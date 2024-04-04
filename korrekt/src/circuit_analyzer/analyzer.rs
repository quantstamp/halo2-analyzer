use super::{analyzable::AnalyzableField, halo2_proofs_libs::*};
use anyhow::{Context, Result};
use log::info;

use std::{
    collections::{HashMap, HashSet},
    fs::{self, File, OpenOptions},
    path::Path,
    process::Command,
};

use crate::io::analyzer_io::{output_result, retrieve_user_input_for_underconstrained};
use crate::io::analyzer_io_type::{
    AnalyzerInput, AnalyzerOutput, AnalyzerOutputStatus, AnalyzerType, VerificationMethod,
};
use crate::smt_solver::{
    smt,
    smt::Printer,
    smt_parser::{self, ModelResult, Satisfiability},
};
use crate::{
    circuit_analyzer::abstract_expr::{self, AbsResult},
    io::analyzer_io_type::LookupMethod,
};

use super::analyzable::Analyzable;

#[derive(Debug)]
pub struct Analyzer<F: AnalyzableField> {
    pub cs: ConstraintSystem<F>,
    /// The regions in the circuit.
    pub regions: Vec<Region>,

    // The fixed cells in the circuit, arranged as [column][row].
    pub fixed: Vec<Vec<CellValue<F>>>,

    pub selectors: Vec<Vec<bool>>,
    pub log: Vec<String>,
    pub permutation: HashMap<String, String>,
    pub instace_cells: HashMap<String, i64>,
    pub cell_to_cycle_head: HashMap<String, String>,
    pub counter: u32,
    pub lookup_mappings: Vec<HashMap<String, usize>>,
}
#[derive(Debug)]
pub enum NodeType {
    Constant,
    Advice,
    Instance,
    Fixed,
    Negated,
    Mult,
    Add,
    Scaled,
    Poly,
    Invalid,
}
#[derive(Debug)]
pub enum Operation {
    Equal,
    NotEqual,
    And,
    Or,
}

#[derive(Debug)]
pub enum IsZeroExpression {
    Zero,
    NonZero,
}

impl<'b, F: AnalyzableField> Analyzer<F> {
    pub fn new<ConcreteCircuit: Circuit<F>>(
        circuit: &ConcreteCircuit,
        k: u32,
    ) -> Result<Self, Error> {
        let analyzable = Analyzable::config_and_synthesize(circuit, k)?;
        let (permutation, instace_cells, cell_to_cycle_head) =
            Analyzer::<F>::extract_permutations(&analyzable.permutation);
        Ok(Analyzer {
            cs: analyzable.cs,
            regions: analyzable.regions,
            fixed: analyzable.fixed,
            selectors: analyzable.selectors,
            log: Vec::new(),
            permutation,
            instace_cells,
            cell_to_cycle_head,
            counter: 0,
            lookup_mappings: Vec::new(),
        })
    }

    /// Detects unused custom gates
    ///
    /// This function iterates through the gates in the constraint system (`self.cs`) and checks if each gate is used.
    /// A gate is considered unused if it evaluates to zero for all regions in the layouter (`self.layouter`).
    /// If an unused gate is found, it is logged in the `self.log` vector along with a suggested action.
    /// Finally, the function prints the total number of unused gates found.
    ///
    pub fn analyze_unused_custom_gates(&mut self) -> Result<AnalyzerOutput> {
        let mut count = 0;
        let mut used;
        for gate in self.cs.gates.iter() {
            used = false;

            // is this gate identically zero over regions?
            'region_search: for region in self
                .regions
                .iter()
                .filter(|reg| reg.enabled_selectors.len() > 0)
            {
                let (region_begin, region_end) = region.rows.unwrap();
                let row_num = (region_end - region_begin + 1) as i32;
                let selectors = region.enabled_selectors.keys().cloned().collect();
                for poly in gate.polynomials() {
                    let res = abstract_expr::eval_abstract(
                        poly,
                        &selectors,
                        region_begin,
                        region_end,
                        row_num,
                        &self.fixed,
                    );
                    if res != AbsResult::Zero {
                        used = true;
                        break 'region_search;
                    }
                }
            }

            if !used {
                count += 1;
                self.log.push(format!("unused gate: \"{}\" (consider removing the gate or checking selectors in regions)", gate.name()));
            }
        }
        println!("Finished analysis: {} unused gates found.", count);
        if count > 0 {
            Ok(AnalyzerOutput {
                output_status: AnalyzerOutputStatus::UnusedCustomGates,
            })
        } else {
            Ok(AnalyzerOutput {
                output_status: AnalyzerOutputStatus::NoUnusedCustomGates,
            })
        }
    }

    /// Detects unused columns
    ///
    /// This function iterates through the advice queries in the constraint system (`self.cs`) and checks if each column is used.
    /// A column is considered unused if it does not appear in any of the polynomials within the gates of the constraint system.
    /// If an unused column is found, it is logged in the `self.log` vector.
    /// Finally, the function prints the total number of unused columns found.
    ///
    pub fn analyze_unused_columns(&mut self) -> Result<AnalyzerOutput> {
        let mut count = 0;
        let mut used;
        for (column, rotation) in self.cs.advice_queries.iter().cloned() {
            used = false;

            for gate in self.cs.gates.iter() {
                for poly in gate.polynomials() {
                    let advices = abstract_expr::extract_columns(poly);
                    if advices.contains(&(column.into(), rotation)) {
                        used = true;
                    }
                }
            }

            if !used {
                count += 1;
                self.log.push(format!("unused column: {:?}", column));
            }
        }
        println!("Finished analysis: {} unused columns found.", count);
        if count > 0 {
            Ok(AnalyzerOutput {
                output_status: AnalyzerOutputStatus::UnusedColumns,
            })
        } else {
            Ok(AnalyzerOutput {
                output_status: AnalyzerOutputStatus::NoUnusedColumns,
            })
        }
    }

    /// Detect assigned but unconstrained cells:
    /// (does it occur in a not-identially zero polynomial in the region?)
    /// (if not almost certainly a bug)
    pub fn analyze_unconstrained_cells(&mut self) -> Result<AnalyzerOutput> {
        let mut count = 0;
        for region in self.regions.iter() {
            let selectors = region.enabled_selectors.keys().cloned().collect();
            let (region_begin, region_end) = region.rows.unwrap();
            let row_num = (region_end - region_begin + 1) as i32;
            let mut used;
            for cell in region.cells.clone() {
                #[cfg(any(
                    feature = "use_pse_halo2_proofs",
                    feature = "use_axiom_halo2_proofs",
                    feature = "use_scroll_halo2_proofs",
                    feature = "use_pse_v1_halo2_proofs"
                ))]
                let (reg_column, rotation) = (cell.0 .0, cell.1);
                #[cfg(feature = "use_zcash_halo2_proofs")]
                let (reg_column, rotation) = (cell.0, cell.1);
                used = false;
                match reg_column.column_type {
                    Any::Fixed => continue,
                    _ => {
                        for gate in self.cs.gates.iter() {
                            for poly in gate.polynomials() {
                                let advices = abstract_expr::extract_columns(poly);
                                let eval = abstract_expr::eval_abstract(
                                    poly,
                                    &selectors,
                                    region_begin,
                                    region_end,
                                    row_num,
                                    &self.fixed,
                                );
                                if eval != AbsResult::Zero
                                    && advices.contains(&(reg_column, Rotation(rotation as i32)))
                                {
                                    used = true;
                                }
                            }
                        }
                    }
                }

                if !used {
                    count += 1;
                    self.log.push(format!("unconstrained cell in \"{}\" region: {:?} (rotation: {:?}) -- very likely a bug.", region.name,  reg_column, rotation));
                }
            }
        }
        println!("Finished analysis: {} unconstrained cells found.", count);
        if count > 0 {
            Ok(AnalyzerOutput {
                output_status: AnalyzerOutputStatus::UnconstrainedCells,
            })
        } else {
            Ok(AnalyzerOutput {
                output_status: AnalyzerOutputStatus::NoUnconstrainedCells,
            })
        }
    }
    // Define a function to extract permutations from the provided permutation assembly.
    // Returns three HashMaps containing pairs, instances, and cell-to-cycle head mappings.

    pub fn extract_permutations(
        permutation: &permutation::keygen::Assembly,
    ) -> (
        HashMap<String, String>,
        HashMap<String, i64>,
        HashMap<String, String>,
    ) {
        let mut pairs = HashMap::<String, String>::new();
        let mut instances = HashMap::<String, i64>::new();
        let mut cycles = Vec::<Vec<String>>::new();
        let mut num_of_cycles = 0;
        let mut cell_to_cycle_head = HashMap::<String, String>::new();

        for col in 0..permutation.sizes.len() {
            for row in 0..permutation.sizes[col].len() {
                if permutation.sizes[col][row] > 1 {
                    let mut cycle = Vec::<String>::new();
                    num_of_cycles = num_of_cycles + 1;
                    let mut cycle_length = permutation.sizes[col][row];
                    let mut cycle_col = col;
                    let mut cycle_row = row;
                    while cycle_length > 1 {
                        let mut is_instance: bool = false;
                        let left_cell = permutation.columns[cycle_col];
                        #[cfg(any(
                            feature = "use_zcash_halo2_proofs",
                            feature = "use_pse_v1_halo2_proofs",
                        ))]
                        let left_column_abr = match left_cell.column_type() {
                            Any::Advice => 'A',
                            Any::Fixed => 'F',
                            Any::Instance => {
                                is_instance = true;
                                'I'
                            }
                        };
                        #[cfg(any(
                            feature = "use_pse_halo2_proofs",
                            feature = "use_axiom_halo2_proofs",
                            feature = "use_scroll_halo2_proofs"
                        ))]
                        let left_column_abr = match left_cell.column_type() {
                            Any::Advice(_) => 'A',
                            Any::Fixed => 'F',
                            Any::Instance => {
                                is_instance = true;
                                'I'
                            }
                        };

                        let left_column_index = left_cell.index;
                        let left =
                            format!("{}-{}-{}", left_column_abr, left_column_index, cycle_row);
                        if is_instance {
                            instances.insert(left.clone(), 0);
                        }
                        is_instance = false;
                        let (right_cell_col, right_cell_row) =
                            permutation.mapping[cycle_col][cycle_row];
                        let right_cell = permutation.columns[right_cell_col];
                        #[cfg(any(
                            feature = "use_zcash_halo2_proofs",
                            feature = "use_pse_v1_halo2_proofs",
                        ))]
                        let right_column_abr = match right_cell.column_type() {
                            Any::Advice => 'A',
                            Any::Fixed => 'F',
                            Any::Instance => {
                                is_instance = true;
                                'I'
                            }
                        };
                        #[cfg(any(
                            feature = "use_pse_halo2_proofs",
                            feature = "use_axiom_halo2_proofs",
                            feature = "use_scroll_halo2_proofs"
                        ))]
                        let right_column_abr = match right_cell.column_type() {
                            Any::Advice(_) => 'A',
                            Any::Fixed => 'F',
                            Any::Instance => {
                                is_instance = true;
                                'I'
                            }
                        };
                        let right_column_index = right_cell.index;
                        let right = format!(
                            "{}-{}-{}",
                            right_column_abr, right_column_index, right_cell_row
                        );
                        if is_instance {
                            instances.insert(right.clone(), 0);
                        }
                        pairs.insert(left.clone(), right.clone());

                        if cycle.is_empty() {
                            cycle.push(left.clone());
                        }
                        cycle.push(right.clone());
                        if is_instance {
                            cell_to_cycle_head.insert(left.clone(), right);
                        } else {
                            cell_to_cycle_head.insert(right, left);
                        }
                        cycle_col = right_cell_col;
                        cycle_row = right_cell_row;
                        cycle_length -= 1;
                    }
                    cycles.push(cycle);
                }
            }
        }
        (pairs, instances, cell_to_cycle_head)
    }

    /// Analyzes underconstrained circuits and generates an analyzer output.
    ///
    /// This function performs the analysis of underconstrained circuits. It takes as input an `analyzer_input` struct
    /// containing the required information for the analysis, and a `fixed` vector representing the vallues of fixed columns.
    /// The function creates an SMT file, decomposes the polynomials, writes the necessary variables and assertions, and runs
    /// the control uniqueness function to determine the `output_status` of the analysis.
    /// The analyzer output is returned as a `Result` indicating success or an error if the analysis fails.
    pub fn analyze_underconstrained(
        &mut self,
        analyzer_input: AnalyzerInput,
        base_field_prime: &str,
    ) -> Result<AnalyzerOutput> {
        fs::create_dir_all("src/output/").unwrap();
        let smt_file_path = "src/output/out.smt2";
        let mut smt_file =
            std::fs::File::create(smt_file_path).context("Failed to create file!")?;
        let mut printer = smt::write_start(&mut smt_file, base_field_prime.to_owned());

        let _ = Self::decompose_polynomial(self, &mut printer, &analyzer_input);

        let instance_string = analyzer_input.verification_input.instances_string.clone();

        let mut analyzer_output: AnalyzerOutput = AnalyzerOutput {
            output_status: AnalyzerOutputStatus::Invalid,
        };

        for permutation in &self.permutation {
            let mut permutation_r = permutation.0.to_owned();
            let mut permutation_l = permutation.1.to_owned();
            if self
                .cell_to_cycle_head
                .contains_key(&permutation.0.to_owned())
            {
                permutation_r = self.cell_to_cycle_head[permutation.0].to_owned();
            }

            smt::write_var(&mut printer, permutation_r.to_owned());
            if self
                .cell_to_cycle_head
                .contains_key(&permutation.1.to_owned())
            {
                permutation_l = self.cell_to_cycle_head[permutation.1].to_owned();
            }

            if !permutation_l.eq(&permutation_r) {
                smt::write_var(&mut printer, permutation_l.to_owned());

                let neg = format!("(ff.neg {})", permutation_l);
                let term = smt::write_term(
                    &mut printer,
                    "add".to_owned(),
                    permutation_r.to_owned(),
                    NodeType::Advice,
                    neg,
                    NodeType::Advice,
                );
                smt::write_assert(
                    &mut printer,
                    term,
                    "0".to_owned(),
                    NodeType::Poly,
                    Operation::Equal,
                );
            }
        }

        let output_status: AnalyzerOutputStatus = Self::uniqueness_assertion(
            self,
            smt_file_path.to_owned(),
            &instance_string,
            &analyzer_input,
            &mut printer,
        )
        .context("Failed to run control uniqueness function!")?;

        analyzer_output.output_status = output_status;
        output_result(analyzer_input, &analyzer_output);

        Ok(analyzer_output)
    }

    #[cfg(test)]
    pub fn log(&self) -> &[String] {
        &self.log
    }
    /**
     * Decomposes an `Expression` into its corresponding SMT-LIB format (`String`) and its type (`NodeType`).
     *
     * # Arguments
     *
     * * `poly` - A reference to an `Expression` instance that is to be decomposed into SMT-LIB v2 format.
     * * `printer` - A mutable reference to a `Printer` instance which is used for writing the decomposed expression.
     * * `region_no` - An integer that represents the region number.
     * * `row_num` - An integer that represents the row number in region.
     * * `es` - A reference to a `HashSet` of Strings representing enabled selectors. These selectors are checked during the decomposition.
     *
     * # Returns
     *
     * A tuple of two elements:
     * * `String` - The SMT-LIB v2 formatted string representation of the decomposed expression.
     * * `NodeType` - The type of the node that the expression corresponds to.
     *
     * # Behavior
     *
     * The function formats a string representation of the expression in SMT-LIB v2 format and identifies its polynomial type as a NodeType.
     *  The function has a recursive behavior in the cases of `Negated`, `Sum`, `Product`,
     * and `Scaled` variants of `Expression`, where it decomposes the nested expressions by calling itself.
     */
    fn decompose_expression(
        poly: &Expression<F>,
        printer: &mut smt::Printer<File>,
        region_begin: usize,
        region_end: usize,
        row_num: i32,
        es: &HashMap<Selector, Vec<usize>>,
        fixed: &Vec<Vec<CellValue<F>>>,
        cell_to_cycle_head: &HashMap<String, String>,
    ) -> (String, NodeType, IsZeroExpression) {
        let mut is_zero_expression = IsZeroExpression::NonZero;
        match &poly {
            Expression::Constant(a) => {
                let constant_decimal_value =
                    u64::from_str_radix(format!("{:?}", a).strip_prefix("0x").unwrap(), 16)
                        .unwrap();

                if constant_decimal_value == 0 {
                    return (
                        "as ff0 F".to_owned(),
                        NodeType::Constant,
                        IsZeroExpression::Zero,
                    );
                }

                let term = format!("(as ff{:?} F)", constant_decimal_value);
                (term, NodeType::Constant, is_zero_expression)
            }
            Expression::Selector(a) => {
                if es.contains_key(a) {
                    ("(as ff1 F)".to_owned(), NodeType::Fixed, is_zero_expression)
                } else {
                    (
                        "as ff0 F".to_owned(),
                        NodeType::Fixed,
                        IsZeroExpression::Zero,
                    )
                }
            }
            Expression::Fixed(fixed_query) => {
                let col = fixed_query.column_index;
                let row = (fixed_query.rotation.0 + row_num) as usize + region_begin;

                let mut t = 0;
                if let CellValue::Assigned(fixed_val) = fixed[col][row] {
                    t = u64::from_str_radix(
                        format!("{:?}", fixed_val).strip_prefix("0x").unwrap(),
                        16,
                    )
                    .unwrap();
                }
                let term = format!("(as ff{:?} F)", t);

                if t == 0 {
                    is_zero_expression = IsZeroExpression::Zero;
                }

                (term, NodeType::Fixed, is_zero_expression)
            }
            Expression::Advice(advice_query) => {
                let term = format!(
                    "A-{}-{}",
                    advice_query.column_index,
                    advice_query.rotation.0 + row_num + region_begin as i32
                );
                let mut t = term.clone();
                if cell_to_cycle_head.contains_key(&term) {
                    t = cell_to_cycle_head[&term.clone()].to_string();
                }
                smt::write_var(printer, t.to_string());
                (t.to_string(), NodeType::Advice, is_zero_expression)
            }
            Expression::Instance(_instance_query) => {
                ("".to_owned(), NodeType::Instance, is_zero_expression)
            }
            Expression::Negated(poly) => {
                let (node_str, node_type, is_zero_expression) = Self::decompose_expression(
                    poly,
                    printer,
                    region_begin,
                    region_end,
                    row_num,
                    es,
                    fixed,
                    cell_to_cycle_head,
                );
                if matches!(is_zero_expression, IsZeroExpression::Zero) {
                    return (
                        "as ff0 F".to_owned(),
                        NodeType::Fixed,
                        IsZeroExpression::Zero,
                    );
                }
                let term = if (matches!(node_type, NodeType::Advice)
                    || matches!(node_type, NodeType::Instance)
                    || matches!(node_type, NodeType::Fixed)
                    || matches!(node_type, NodeType::Constant))
                {
                    format!("ff.neg {}", node_str)
                } else {
                    format!("ff.neg ({})", node_str)
                };
                (term, NodeType::Negated, is_zero_expression)
            }
            Expression::Sum(a, b) => {
                let (node_str_left, nodet_type_left, left_is_zero) = Self::decompose_expression(
                    a,
                    printer,
                    region_begin,
                    region_end,
                    row_num,
                    es,
                    fixed,
                    cell_to_cycle_head,
                );
                let (node_str_right, nodet_type_right, right_is_zero) = Self::decompose_expression(
                    b,
                    printer,
                    region_begin,
                    region_end,
                    row_num,
                    es,
                    fixed,
                    cell_to_cycle_head,
                );

                if matches!(left_is_zero, IsZeroExpression::Zero)
                    && matches!(right_is_zero, IsZeroExpression::Zero)
                {
                    return (
                        "as ff0 F".to_owned(),
                        NodeType::Fixed,
                        IsZeroExpression::Zero,
                    );
                }

                let term = smt::write_term(
                    printer,
                    "add".to_owned(),
                    node_str_left,
                    nodet_type_left,
                    node_str_right,
                    nodet_type_right,
                );
                (term, NodeType::Add, is_zero_expression)
            }
            Expression::Product(a, b) => {
                let (node_str_left, nodet_type_left, left_is_zero) = Self::decompose_expression(
                    a,
                    printer,
                    region_begin,
                    region_end,
                    row_num,
                    es,
                    fixed,
                    cell_to_cycle_head,
                );
                let (node_str_right, nodet_type_right, right_is_zero) = Self::decompose_expression(
                    b,
                    printer,
                    region_begin,
                    region_end,
                    row_num,
                    es,
                    fixed,
                    cell_to_cycle_head,
                );

                if matches!(left_is_zero, IsZeroExpression::Zero)
                    || matches!(right_is_zero, IsZeroExpression::Zero)
                {
                    return (
                        "as ff0 F".to_owned(),
                        NodeType::Fixed,
                        IsZeroExpression::Zero,
                    );
                }

                let term = smt::write_term(
                    printer,
                    "mul".to_owned(),
                    node_str_left,
                    nodet_type_left,
                    node_str_right,
                    nodet_type_right,
                );
                (term, NodeType::Mult, is_zero_expression)
            }
            Expression::Scaled(_poly, c) => {
                // convering the field element into an expression constant and recurse.
                let (node_str_left, nodet_type_left, lef_is_zero) = Self::decompose_expression(
                    &Expression::Constant(*c),
                    printer,
                    region_begin,
                    region_end,
                    row_num,
                    es,
                    fixed,
                    cell_to_cycle_head,
                );
                let (node_str_right, nodet_type_right, right_is_zero) = Self::decompose_expression(
                    _poly,
                    printer,
                    region_begin,
                    region_end,
                    row_num,
                    es,
                    fixed,
                    cell_to_cycle_head,
                );
                if matches!(lef_is_zero, IsZeroExpression::Zero)
                    || matches!(right_is_zero, IsZeroExpression::Zero)
                {
                    return (
                        "as ff0 F".to_owned(),
                        NodeType::Fixed,
                        IsZeroExpression::Zero,
                    );
                }
                let term = smt::write_term(
                    printer,
                    "mul".to_owned(),
                    node_str_left,
                    nodet_type_left,
                    node_str_right,
                    nodet_type_right,
                );
                (term, NodeType::Scaled, is_zero_expression)
            }
            #[cfg(any(
                feature = "use_pse_halo2_proofs",
                feature = "use_axiom_halo2_proofs",
                feature = "use_scroll_halo2_proofs"
            ))]
            Expression::Challenge(_poly) => ("".to_string(), NodeType::Fixed, is_zero_expression),
        }
    }

    fn decompose_lookup_expression(
        poly: &Expression<F>,
        printer: &mut smt::Printer<File>,
        region_begin: usize,
        region_end: usize,
        row_num: i32,
        es: &HashMap<Selector, Vec<usize>>,
        fixed: &Vec<Vec<CellValue<F>>>,
        cell_to_cycle_head: &HashMap<String, String>,
    ) -> (String, NodeType, String, IsZeroExpression) {
        let is_zero_expression = IsZeroExpression::NonZero;
        match &poly {
            Expression::Constant(_) => (
                String::new(),
                NodeType::Invalid,
                String::new(),
                IsZeroExpression::NonZero,
            ),
            Expression::Selector(a) => {
                if es.contains_key(a) {
                    (
                        "(as ff1 F)".to_owned(),
                        NodeType::Fixed,
                        "1".to_owned(),
                        IsZeroExpression::NonZero,
                    )
                } else {
                    (
                        "as ff0 F".to_owned(),
                        NodeType::Fixed,
                        "0".to_owned(),
                        IsZeroExpression::Zero,
                    )
                }
            }
            Expression::Fixed(fixed_query) => {
                let col = fixed_query.column_index;
                let row = (fixed_query.rotation.0 + row_num) as usize + region_begin;

                let mut t = 0;
                if let CellValue::Assigned(fixed_val) = fixed[col][row] {
                    t = u64::from_str_radix(
                        format!("{:?}", fixed_val).strip_prefix("0x").unwrap(),
                        16,
                    )
                    .unwrap();
                }
                if t == 0 {
                    return (
                        "as ff0 F".to_owned(),
                        NodeType::Fixed,
                        "0".to_owned(),
                        IsZeroExpression::Zero,
                    );
                }
                let term = format!("(as ff{:?} F)", t);

                (term, NodeType::Fixed, t.to_string(), is_zero_expression)
            }
            Expression::Advice(advice_query) => {
                let term = format!(
                    "A-{}-{}",
                    advice_query.column_index,
                    advice_query.rotation.0 + row_num + region_begin as i32
                );
                let mut t = term.clone();
                if cell_to_cycle_head.contains_key(&term) {
                    t = cell_to_cycle_head[&term.clone()].to_string();
                }
                smt::write_var(printer, t.to_string());
                (
                    t.to_string(),
                    NodeType::Advice,
                    t.to_string(),
                    is_zero_expression,
                )
            }
            Expression::Instance(instance_query) => {
                let term = format!(
                    "I-{}-{}",
                    instance_query.column_index,
                    instance_query.rotation.0 + row_num + region_begin as i32
                );
                let mut t = term.clone();
                if cell_to_cycle_head.contains_key(&term) {
                    t = cell_to_cycle_head[&term.clone()].to_string();
                }
                smt::write_var(printer, t.to_string());
                (
                    t.to_string(),
                    NodeType::Advice,
                    t.to_string(),
                    is_zero_expression,
                )
            }
            Expression::Negated(_) => {
                (
                    String::new(),
                    NodeType::Invalid,
                    String::new(),
                    is_zero_expression,
                ) //TODO: add error handling for invalid expressions: ZKR-3331
            }
            Expression::Sum(_, _) => (
                String::new(),
                NodeType::Invalid,
                String::new(),
                is_zero_expression,
            ),
            Expression::Product(a, b) => {
                let (node_str_left, nodet_type_left, variable_left, left_is_zero) =
                    Self::decompose_lookup_expression(
                        a,
                        printer,
                        region_begin,
                        region_end,
                        row_num,
                        es,
                        fixed,
                        cell_to_cycle_head,
                    );
                let (node_str_right, nodet_type_right, variable_right, right_is_zero) =
                    Self::decompose_lookup_expression(
                        b,
                        printer,
                        region_begin,
                        region_end,
                        row_num,
                        es,
                        fixed,
                        cell_to_cycle_head,
                    );
                if matches!(left_is_zero, IsZeroExpression::Zero)
                    || matches!(right_is_zero, IsZeroExpression::Zero)
                {
                    return (
                        "as ff0 F".to_owned(),
                        NodeType::Fixed,
                        "0".to_owned(),
                        IsZeroExpression::Zero,
                    );
                }
                let term = smt::write_term(
                    printer,
                    "mul".to_owned(),
                    node_str_left,
                    nodet_type_left,
                    node_str_right,
                    nodet_type_right,
                );
                let mut var = String::from("");
                if variable_left == "1" || variable_right == "1" {
                    if variable_left == "1" {
                        var = variable_right;
                    } else {
                        var = variable_left;
                    }
                }
                (term, NodeType::Mult, var, is_zero_expression)
            }
            Expression::Scaled(_poly, _) => (
                String::new(),
                NodeType::Invalid,
                String::new(),
                is_zero_expression,
            ),
            #[cfg(any(
                feature = "use_pse_halo2_proofs",
                feature = "use_axiom_halo2_proofs",
                feature = "use_scroll_halo2_proofs"
            ))]
            Expression::Challenge(_poly) => (
                String::new(),
                NodeType::Invalid,
                String::new(),
                is_zero_expression,
            ),
        }
    }

    /// Decomposes polynomials and writes assertions using an SMT printer.
    ///
    /// This function iterates over the regions and rows of a layouter and decomposes the polynomials
    /// associated with gates and lookups. It writes assertions using an SMT printer based on the decomposed expressions.
    ///
    pub fn decompose_polynomial(
        &'b mut self,
        printer: &mut smt::Printer<File>,
        analyzer_input: &AnalyzerInput,
    ) -> Result<(), anyhow::Error> {
        // Extract all gates
        if !self.regions.is_empty() {
            for region in &self.regions {
                if !region.enabled_selectors.is_empty() {
                    let (region_begin, region_end) = region.rows.unwrap();
                    for row_num in 0..region_end - region_begin + 1 {
                        for gate in self.cs.gates.iter() {
                            for poly in &gate.polys {
                                let (node_str, _, _) = Self::decompose_expression(
                                    poly,
                                    printer,
                                    region_begin,
                                    region_end,
                                    i32::try_from(row_num).ok().unwrap(),
                                    &region.enabled_selectors,
                                    &self.fixed,
                                    &self.cell_to_cycle_head,
                                );

                                smt::write_assert(
                                    printer,
                                    node_str,
                                    "0".to_owned(),
                                    NodeType::Poly,
                                    Operation::Equal,
                                );
                            }
                        }
                    }
                }
            }
        }
        // Extract all lookups
        if (matches!(analyzer_input.lookup_method, LookupMethod::Uninterpreted)
            || matches!(analyzer_input.lookup_method, LookupMethod::Interpreted))
        {
            // Extract all lookups as uninterpreted functions and stores all lookup structure to be use for post-processing
            self.decompose_lookups_as_uniterpreted(printer, analyzer_input)?;
        } else {
            // Extract all lookup constraints
            self.decompose_lookups(printer)?;
        }
        Ok(())
    }

    #[cfg(any(
        feature = "use_zcash_halo2_proofs",
        feature = "use_pse_halo2_proofs",
        feature = "use_axiom_halo2_proofs",
        feature = "use_pse_v1_halo2_proofs",
    ))]
    // Extracts the lookup constraints and writes assertions using an SMT printer.
    fn decompose_lookups(&self, printer: &mut smt::Printer<File>) -> Result<(), anyhow::Error> {
        for region in &self.regions {
            if !region.enabled_selectors.is_empty() {
                let (region_begin, region_end) = region.rows.unwrap();
                for row_num in 0..region_end - region_begin + 1 {
                    for lookup in self.cs.lookups.iter() {
                        let mut zero_lookup_expressions = Vec::new();
                        let mut cons_str_vec = Vec::new();
                        for poly in &lookup.input_expressions {
                            let (node_str, _, is_zero) = Self::decompose_expression(
                                poly,
                                printer,
                                region_begin,
                                region_end,
                                i32::try_from(row_num).ok().unwrap(),
                                &region.enabled_selectors,
                                &self.fixed,
                                &self.cell_to_cycle_head,
                            );
                            if matches!(is_zero, IsZeroExpression::NonZero) {
                                cons_str_vec.push(node_str);
                                zero_lookup_expressions.push(true);
                            } else {
                                zero_lookup_expressions.push(false);
                            }
                        }
                        let mut col_indices = Vec::new();
                        for col in lookup.table_expressions.clone() {
                            if let Expression::Fixed(fixed_query) = col {
                                col_indices.push(fixed_query.column_index);
                            }
                        }

                        let big_cons_str = Self::extract_lookup_constraints(
                            self,
                            col_indices,
                            cons_str_vec,
                            printer,
                            zero_lookup_expressions,
                        )?;
                        if big_cons_str.is_empty() {
                            continue;
                        }
                        smt::write_assert_bool(printer, big_cons_str, Operation::Or);
                    }
                }
            }
        }
        Ok(())
    }

    fn extract_lookup_constraints(
        &self,
        col_indices: Vec<usize>,
        cons_str_vec: Vec<String>,
        printer: &mut smt::Printer<File>,
        zero_lookup_expressions: Vec<bool>,
    ) -> Result<String, anyhow::Error> {
        let mut exit = false;
        let mut big_cons_str = "".to_owned();
        let mut big_cons = vec![];
        for row in 0..self.fixed[0].len() {
            //*** Iterate over look up table rows */
            if exit {
                break;
            }
            let mut equalities = vec![];
            let mut eq_str = String::new();
            for col in 0..col_indices.len() {
                if !zero_lookup_expressions[col] {
                    continue;
                }
                //*** Iterate over fixed cols */
                let mut t = String::new();
                match self.fixed[col_indices[col]][row] {
                    CellValue::Unassigned => {
                        exit = true;
                        break;
                    }
                    CellValue::Assigned(f) => {
                        t = format!("{:?}", f);
                    }
                    CellValue::Poison(_) => {}
                }
                if let CellValue::Assigned(value) = self.fixed[col_indices[col]][row] {
                    t = u64::from_str_radix(format!("{:?}", value).strip_prefix("0x").unwrap(), 16)
                        .unwrap()
                        .to_string();
                }
                let sa = smt::get_assert(
                    printer,
                    cons_str_vec[col].clone(),
                    t,
                    NodeType::Mult,
                    Operation::Equal,
                )
                .context("Failled to generate assert!")?;
                equalities.push(sa);
            }
            if exit {
                break;
            }
            for var in equalities.iter() {
                eq_str.push_str(var);
            }
            if eq_str.is_empty() {
                continue;
            }
            let and_eqs = smt::get_and(printer, eq_str);
            if and_eqs.is_empty() {
                continue;
            }
            big_cons.push(and_eqs);
        }
        for var in big_cons.iter() {
            big_cons_str.push_str(var);
        }
        Ok(big_cons_str)
    }
    fn extract_lookup_constraints_unint(
        &self,
        col_indices: Vec<usize>,
        printer: &mut smt::Printer<File>,
    ) -> Result<String, anyhow::Error> {
        let mut exit = false;
        let mut big_cons_str = "".to_owned();
        let mut big_cons = vec![];
        for row in 0..self.fixed[0].len() {
            //*** Iterate over look up table rows */
            if exit {
                break;
            }
            let mut equalities = vec![];
            let mut eq_str = String::new();
            for col in 0..col_indices.len() {
                let input = format!("x_{} ", col);
                //*** Iterate over fixed cols */
                let mut t = String::new();
                match self.fixed[col_indices[col]][row] {
                    CellValue::Unassigned => {
                        exit = true;
                        break;
                    }
                    CellValue::Assigned(f) => {
                        t = format!("{:?}", f);
                    }
                    CellValue::Poison(_) => {}
                }
                if let CellValue::Assigned(value) = self.fixed[col_indices[col]][row] {
                    t = u64::from_str_radix(format!("{:?}", value).strip_prefix("0x").unwrap(), 16)
                        .unwrap()
                        .to_string();
                }
                let sa = smt::get_assert(printer, input, t, NodeType::Advice, Operation::Equal)
                    .context("Failled to generate assert!")?;
                equalities.push(sa);
            }
            if exit {
                break;
            }
            for var in equalities.iter() {
                eq_str.push_str(var);
            }
            let and_eqs = smt::get_and(printer, eq_str);

            big_cons.push(and_eqs);
        }
        for var in big_cons.iter() {
            big_cons_str.push_str(var);
        }
        Ok(big_cons_str)
    }
    // Extracts the lookup dependant cells and writes assertions of an uninterpreted function using an SMT printer.
    // Also extract the list of all lookup dependant cells and their corresponding lookup mappings. These data will be used for checking if a under-constrained circuit is false positive.
    #[cfg(any(
        feature = "use_zcash_halo2_proofs",
        feature = "use_pse_halo2_proofs",
        feature = "use_axiom_halo2_proofs",
        feature = "use_pse_v1_halo2_proofs",
    ))]
    fn decompose_lookups_as_uniterpreted(
        &mut self,
        printer: &mut smt::Printer<File>,
        analyzer_input: &AnalyzerInput,
    ) -> Result<(), anyhow::Error> {
        let mut lookup_func_map = HashMap::new();
        for region in &self.regions {
            if !region.enabled_selectors.is_empty() {
                let (region_begin, region_end) = region.rows.unwrap();
                for row_num in 0..region_end - region_begin + 1 {
                    let mut lookup_index = 0;
                    for lookup in self.cs.lookups.iter() {
                        let mut non_zero_expression = vec![false; lookup.input_expressions.len()];
                        let mut cons_str_vec = Vec::new();
                        let mut lookup_arg_cells = Vec::new();
                        // Decompose the lookup input expressions and store the result in cons_str_vec.
                        for poly in &lookup.input_expressions {
                            // Decompose the lookup input expressions and return the SMT compatible decomposed expression and the variable name.
                            let (node_str, _, var, is_zero) = Self::decompose_lookup_expression(
                                poly,
                                printer,
                                region_begin,
                                region_end,
                                i32::try_from(row_num).ok().unwrap(),
                                &region.enabled_selectors,
                                &self.fixed,
                                &self.cell_to_cycle_head,
                            );
                            if matches!(is_zero, IsZeroExpression::NonZero) {
                                cons_str_vec.push(node_str);
                                if !var.is_empty() {
                                    non_zero_expression.push(true);
                                    lookup_arg_cells.push(var);
                                }
                            }
                        }

                        let mut col_indices = Vec::new();
                        for col in lookup.table_expressions.clone() {
                            if let Expression::Fixed(fixed_query) = col {
                                col_indices.push(fixed_query.column_index);
                            }
                        }
                        let mut function_input = String::new();
                        let mut function_body = String::new();
                        if matches!(analyzer_input.lookup_method, LookupMethod::Interpreted) {
                            // Extract the lookup dependant cells and write assertions of an uninterpreted function using an SMT printer.
                            let big_cons_str = Self::extract_lookup_constraints_unint(
                                self,
                                col_indices.clone(),
                                printer,
                            )?;

                            function_body = smt::get_or(printer, big_cons_str);
                        }
                        let mut lookup_mapping = HashMap::new();
                        let mut input_index = 0;
                        // Using decomposed lookup input expressions and column indexes of the lookup table, we can have the whole structure of each lookup as elements of lookup_mappings

                        for (index, var) in lookup_arg_cells.iter().enumerate() {
                            if var.is_empty() {
                                continue;
                            }
                            if let Some(col_index) = col_indices.get(index).cloned() {
                                // Keeping track of in the current lookup, which cell is mapped to which column in the lookup table.
                                lookup_mapping.insert(var.clone(), col_index);
                                // Conncatinate function_input with format!("(x_{} ", col_index)
                                if matches!(analyzer_input.lookup_method, LookupMethod::Interpreted)
                                {
                                    function_input.push_str(&format!("(x_{} F)", input_index));
                                    input_index += 1;
                                }
                            }
                        }
                        if !lookup_mapping.is_empty() {
                            self.lookup_mappings.push(lookup_mapping.clone());
                        }

                        if !cons_str_vec.is_empty() && !lookup_mapping.is_empty() {
                            let funcion_name =
                                format!("isInLookupTable{}", lookup_index);
                            if !lookup_func_map.contains_key(&lookup_index) {
                                lookup_func_map.insert(lookup_index, true);
                                if matches!(analyzer_input.lookup_method, LookupMethod::Interpreted)
                                {
                                    // lookup_interpreted_func {
                                    smt::write_define_fn(
                                        printer,
                                        funcion_name.clone(),
                                        function_input,
                                        "Bool".to_owned(),
                                        function_body,
                                    );
                                } else {
                                    smt::write_declare_fn(
                                        printer,
                                        funcion_name.clone(),
                                        "F".to_owned(),
                                        "Bool".to_owned(),
                                    );
                                }
                            }
                            if matches!(analyzer_input.lookup_method, LookupMethod::Interpreted) {
                                // Concatenate all lookup input expressions and write assertions of an uninterpreted function using an SMT printer.
                                println!("lookup_arg_cells: {:?}", lookup_arg_cells);
                                let cons_str = lookup_arg_cells
                                    .iter()
                                    .fold(String::new(), |acc, x| acc + x + " ");
                                //remove space from beginning and end
                                let cons_str = cons_str.trim();
                                smt::write_assert_boolean_func(
                                    printer,
                                    funcion_name.clone(),
                                    cons_str.to_owned(),
                                );
                            } else {
                                for cons_str in cons_str_vec.iter() {
                                    smt::write_assert_boolean_func(
                                        printer,
                                        funcion_name.clone(),
                                        format!("({})", cons_str).to_owned(),
                                    );
                                }
                            }
                        }
                        lookup_index += 1;
                    }
                }
            }
        }
        Ok(())
    }
    #[cfg(any(feature = "use_scroll_halo2_proofs"))]
    fn decompose_lookups_as_uniterpreted(
        &mut self,
        printer: &mut smt::Printer<File>,
        analyzer_input: &AnalyzerInput,
    ) -> Result<(), anyhow::Error> {
        let mut lookup_func_map = HashMap::new();
        for region in &self.regions {
            if !region.enabled_selectors.is_empty() {
                let (region_begin, region_end) = region.rows.unwrap();
                for row_num in 0..region_end - region_begin + 1 {
                    let mut lookup_index = 0;
                    for lookup in &self.cs.lookups_map {
                        let mut cons_str_vec = Vec::new();
                        let mut lookup_arg_cells = Vec::new();
                        for polys in &lookup.1.inputs {
                            for poly in polys {
                                let (node_str, _, var, is_zero) = Self::decompose_lookup_expression(
                                    poly,
                                    printer,
                                    region_begin,
                                    region_end,
                                    i32::try_from(row_num).ok().unwrap(),
                                    &region.enabled_selectors,
                                    &self.fixed,
                                    &self.cell_to_cycle_head,
                                );
                                cons_str_vec.push(node_str);
                                if !var.is_empty() {
                                    lookup_arg_cells.push(var);
                                }
                            }
                        }

                        let mut col_indices = Vec::new();
                        for col in lookup.1.table.clone() {
                            if let Expression::Fixed(fixed_query) = col {
                                col_indices.push(fixed_query.column_index);
                            }
                        }
                        let mut function_input = String::new();
                        let mut function_body = String::new();
                        if matches!(analyzer_input.lookup_method, LookupMethod::Interpreted) {
                            // Extract the lookup dependant cells and write assertions of an uninterpreted function using an SMT printer.
                            let big_cons_str = Self::extract_lookup_constraints_unint(
                                self,
                                col_indices.clone(),
                                printer,
                            )?;

                            function_body = smt::get_or(printer, big_cons_str);
                        }
                        let mut lookup_mapping = HashMap::new();
                        let mut input_index = 0;
                        for (index, var) in lookup_arg_cells.iter().enumerate() {
                            if var.is_empty() {
                                continue;
                            }
                            if let Some(&col_index) = col_indices.get(index) {
                                lookup_mapping.insert(var.clone(), col_index);
                                if matches!(analyzer_input.lookup_method, LookupMethod::Interpreted)
                                {
                                    function_input.push_str(&format!("(x_{} F)", input_index));
                                    input_index += 1;
                                }
                            }
                        }
                        if !lookup_mapping.is_empty() {
                            &self.lookup_mappings.push(lookup_mapping.clone());
                        }
                        if !cons_str_vec.is_empty() && !lookup_mapping.is_empty() {
                            let function_name =
                                format!("isInLookupTable{}", lookup_index);
                            if !lookup_func_map.contains_key(&lookup_index) {
                                lookup_func_map.insert(lookup_index, true);
                                if matches!(analyzer_input.lookup_method, LookupMethod::Interpreted)
                                {
                                    // lookup_interpreted_func {
                                    smt::write_define_fn(
                                        printer,
                                        function_name.clone(),
                                        function_input,
                                        "Bool".to_owned(),
                                        function_body,
                                    );
                                } else {
                                    smt::write_declare_fn(
                                        printer,
                                        function_name.clone(),
                                        "F".to_owned(),
                                        "Bool".to_owned(),
                                    );
                                }
                            }
                            if matches!(analyzer_input.lookup_method, LookupMethod::Interpreted) {
                                // Concatenate all lookup input expressions and write assertions of an uninterpreted function using an SMT printer.
                                let cons_str = lookup_arg_cells
                                    .iter()
                                    .fold(String::new(), |acc, x| acc + x + " ");
                                //remove space from beginning and end
                                let cons_str = cons_str.trim();
                                smt::write_assert_boolean_func(
                                    printer,
                                    function_name.clone(),
                                    cons_str.to_owned(),
                                );
                            } else {
                                for cons_str in cons_str_vec.iter() {
                                    smt::write_assert_boolean_func(
                                        printer,
                                        function_name.clone(),
                                        format!("({})", cons_str).to_owned(),
                                    );
                                }
                            }
                        }
                        lookup_index += 1;
                    }
                }
            }
        }
        Ok(())
    }
    #[cfg(any(feature = "use_scroll_halo2_proofs"))]
    fn decompose_lookups(&self, printer: &mut smt::Printer<File>) -> Result<(), anyhow::Error> {
        for region in &self.regions {
            if !region.enabled_selectors.is_empty() {
                let (region_begin, region_end) = region.rows.unwrap();
                for row_num in 0..region_end - region_begin + 1 {
                    for lookup in &self.cs.lookups_map {
                        let mut zero_lookup_expressions = Vec::new();
                        let mut cons_str_vec = Vec::new();
                        for polys in &lookup.1.inputs {
                            
                            for poly in polys {
                                let (node_str, _, is_zero) = Self::decompose_expression(
                                    &poly,
                                    printer,
                                    region_begin,
                                    region_end,
                                    i32::try_from(row_num).ok().unwrap(),
                                    &region.enabled_selectors,
                                    &self.fixed,
                                    &self.cell_to_cycle_head,
                                );
                                if matches!(is_zero, IsZeroExpression::NonZero) {
                                    cons_str_vec.push(node_str.clone());
                                    zero_lookup_expressions.push(true);
                                } else {
                                    zero_lookup_expressions.push(false);
                                }
                            }
                        }
                        let mut exit = false;
                        let mut col_indices = Vec::new();
                        for col in lookup.1.table.clone() {
                            if exit {
                                break;
                            }
                            if let Expression::Fixed(fixed_query) = col {
                                col_indices.push(fixed_query.column_index);
                            }
                        }
                        let big_cons_str = Self::extract_lookup_constraints(
                            self,
                            col_indices,
                            cons_str_vec,
                            printer,
                            zero_lookup_expressions,
                        )?;
                        if big_cons_str.is_empty() {
                            continue;
                        }

                        smt::write_assert_bool(printer, big_cons_str, Operation::Or);
                    }
                }
            }
        }
        Ok(())
    }
    /// Checks the uniqueness inputs and returns the analysis result.
    ///
    /// This function checks the uniqueness by solving SMT formulas with various assignments
    /// and constraints. It iterates over the variables and applies different rules based on the verification method
    /// specified in the `analyzer_input`. The function writes assertions using an SMT printer and returns the
    /// analysis result as `AnalyzerOutputStatus`.
    ///
    pub fn uniqueness_assertion(
        &mut self,
        smt_file_path: String,
        instance_cols_string: &HashMap<String, i64>,
        analyzer_input: &AnalyzerInput,
        printer: &mut smt::Printer<File>,
    ) -> Result<AnalyzerOutputStatus> {
        let mut result: AnalyzerOutputStatus = AnalyzerOutputStatus::NotUnderconstrainedLocal;
        let mut variables: HashSet<String> = HashSet::new();
        for variable in printer.vars.keys() {
            variables.insert(variable.clone());
        }

        let mut max_iterations: u128 = 1;

        // Determine the verification method and configure the analysis accordingly.
        match analyzer_input.verification_method {
            // For specific public input, directly write assertions for each variable.
            VerificationMethod::Specific => {
                for var in instance_cols_string {
                    // Declare the variables in the SMT formula.
                    smt::write_var(printer, var.0.to_owned());
                    // Write an assertion that each veriables equals the given value.
                    smt::write_assert(
                        printer,
                        var.0.clone(),
                        (*var.1).to_string(),
                        NodeType::Instance,
                        Operation::Equal,
                    );
                }
            }
            // For random verification, set the number of iterations as specified.
            VerificationMethod::Random => {
                max_iterations = analyzer_input.verification_input.iterations;
            }
        }
        let model = Self::solve_and_get_model(smt_file_path.clone(), &variables)
            .context("Failed to solve and get model!")?;
        // With uninterpreted function, the model might be invalid due to the lookup constraints. We will ignore these models.
        let mut valid_model_lookeded_up = false;
        if matches!(model.sat, Satisfiability::Unsatisfiable) {
            result = AnalyzerOutputStatus::Overconstrained;
            return Ok(result); // We can just break here.
        }
        let mut uc_lookup_dependency_fp = false;
        let mut uc_lookup_dependency: bool = false;
        for i in 1..=max_iterations {
            // Attempt to solve the SMT problem and obtain a model.
            let model = Self::solve_and_get_model(smt_file_path.clone(), &variables)
                .context("Failed to solve and get model!")?;
            if matches!(model.sat, Satisfiability::Unsatisfiable) {
                result = AnalyzerOutputStatus::NotUnderconstrained;
                return Ok(result); // We can just break here.
            }
            // No need to do the lookup as they are already constrained in SMT solver where uninterpreted functions are not used for lookups.
            if !matches!(analyzer_input.lookup_method, LookupMethod::Uninterpreted) {
                info!("Model {} to be checked:", i);
                for r in &model.result {
                    info!("{} : {}", r.1.name, r.1.value.element)
                }
                valid_model_lookeded_up = true;
            }
            // if using uninterpreted function, we need to check if the model is valid by performing the lookup.
            else {
                uc_lookup_dependency = false;
                // Lookup search to make sure all values in the model are valid.
                for index in 0..self.lookup_mappings.len() {
                    // Perform the lookup
                    let lookup_sucessful = self
                        .lookup(&model, index)
                        .context("Failed to perform lookup")?;

                    if lookup_sucessful {
                        valid_model_lookeded_up = true;
                    }
                }
            }
            // If the model is not valid, we ignore it and continue to the next iteration.
            if valid_model_lookeded_up {
                println!("Model {} is valid!", i);
                info!("Model {} to be checked:", i);
                for r in &model.result {
                    info!("{} : {}", r.1.name, r.1.value.element)
                }
                // Imitate the creation of a new solver by utilizing the stack functionality of solver
                smt::write_push(printer, 1);

                //*** To check the model is under-constrained we need to:
                //      1. Fix the public input
                //      2. Change the other vars
                //      3. add these rules to the current solver and,
                //      4. find a model that satisfies these rules

                let mut same_assignments = vec![];
                let mut diff_assignments = vec![];
                for var in variables.iter() {
                    // The second condition is needed because the following constraints would've been added already to the solver in the beginning.
                    // It is not strictly necessary, but there is no point in adding redundant constraints to the solver.
                    if instance_cols_string.contains_key(var)
                        && !matches!(
                            analyzer_input.verification_method,
                            VerificationMethod::Specific
                        )
                    {
                        // 1. Fix the public input
                        let result_from_model = &model.result[var];
                        let sa = smt::get_assert(
                            printer,
                            result_from_model.name.clone(),
                            result_from_model.value.element.clone(),
                            NodeType::Instance,
                            Operation::Equal,
                        )
                        .context("Failled to generate assert!")?;
                        same_assignments.push(sa);
                    } else {
                        //2. Change the other vars
                        let result_from_model = &model.result[var];
                        let sa = smt::get_assert(
                            printer,
                            result_from_model.name.clone(),
                            result_from_model.value.element.clone(),
                            NodeType::Instance,
                            Operation::NotEqual,
                        )
                        .context("Failled to generate assert!")?;
                        diff_assignments.push(sa);
                    }
                }

                let mut same_str = "".to_owned();
                for var in same_assignments.iter() {
                    same_str.push_str(var);
                }
                let mut diff_str = "".to_owned();
                for var in diff_assignments.iter() {
                    diff_str.push_str(var);
                }

                // 3. add these rules to the current solver,
                let or_diff_assignments = smt::get_or(printer, diff_str);
                same_str.push_str(&or_diff_assignments);
                let and_all = smt::get_and(printer, same_str);
                smt::write_assert_bool(printer, and_all, Operation::And);

                // 4. find a model that satisfies these rules
                let model_with_constraint =
                    Self::solve_and_get_model(smt_file_path.clone(), &variables)
                        .context("Failed to solve and get model!")?;

                // If using uninterpreted function, we need to check if the model is valid by performing the lookup.
                if matches!(analyzer_input.lookup_method, LookupMethod::Uninterpreted) {
                    info!("Equivalent model for the same public input!(No Lookup Constraint):");
                    for r in &model_with_constraint.result {
                        info!("{} : {}", r.1.name, r.1.value.element)
                    }
                    uc_lookup_dependency = false;
                    for index in 0..self.lookup_mappings.len() {
                        // Lookup search to make sure all values in the model are valid.
                        let lookup_sucessful = self
                            .lookup(&model_with_constraint, index)
                            .context("Failed to perform lookup")?;
                        // if the lookup is not successful, the model found is not valid and the under-constrained flag is a false positive, still we can't say if the circuit is under-constrained or not.
                        if !lookup_sucessful {
                            uc_lookup_dependency = true;
                            uc_lookup_dependency_fp = true;
                            if (matches!(
                                analyzer_input.verification_method,
                                VerificationMethod::Specific
                            ) || (matches!(
                                analyzer_input.verification_method,
                                VerificationMethod::Random
                            ) && i == max_iterations))
                            {
                                info!("Lookup unsuccessful! Probably a false positive!");
                                result = AnalyzerOutputStatus::NotUnderconstrainedLocalUniterpretedLookups;
                                return Ok(result);
                            }
                        }
                    }
                }
                if (matches!(model_with_constraint.sat, Satisfiability::Satisfiable)
                    && !uc_lookup_dependency)
                {
                    info!("Equivalent model for the same public input:");
                    for r in &model_with_constraint.result {
                        info!("{} : {}", r.1.name, r.1.value.element)
                    }
                    result = AnalyzerOutputStatus::Underconstrained;
                    return Ok(result);
                } else {
                    info!("There is no equivalent model with the same public input to prove model {} is under-constrained!", i);
                }
                smt::write_pop(printer, 1);
            }

            // If no model found, add some rules to the initial solver to make sure does not generate the same model again
            let mut negated_model_variable_assignments = vec![];
            for res in &model.result {
                if instance_cols_string.contains_key(&res.1.name) {
                    let sa = smt::get_assert(
                        printer,
                        res.1.name.clone(),
                        res.1.value.element.clone(),
                        NodeType::Instance,
                        Operation::NotEqual,
                    )
                    .context("Failled to generate assert!")?;
                    negated_model_variable_assignments.push(sa);
                }
            }
            let mut neg_model = "".to_owned();
            for var in negated_model_variable_assignments.iter() {
                neg_model.push_str(var);
            }
            smt::write_assert_bool(printer, neg_model, Operation::Or);
        }
        if uc_lookup_dependency_fp
            && matches!(result, AnalyzerOutputStatus::NotUnderconstrainedLocal)
        {
            result = AnalyzerOutputStatus::NotUnderconstrainedLocalUniterpretedLookups;
        }
        Ok(result)
    }
    /// Generates a copy path for the SMT file.
    ///
    /// This function takes the original SMT file path as input and generates a copy path
    /// for the SMT file. The copy path is constructed by appending "_temp.smt2" to the
    /// original file's stem (i.e., file name without extension), and placing it in the
    /// "src/output/" directory. The function then creates a copy of the original file
    /// at the generated copy path.
    ///
    pub fn generate_copy_path(smt_file_path: String) -> Result<String> {
        let smt_path_clone = smt_file_path.clone();
        let smt_path_obj = Path::new(&smt_path_clone);
        let smt_file_stem = smt_path_obj.file_stem().unwrap();
        let smt_file_copy_path = format!(
            "{}{}{}",
            "src/output/",
            smt_file_stem.to_str().unwrap(),
            "_temp.smt2"
        );
        fs::copy(smt_file_path, smt_file_copy_path.clone()).context("Failed to copy file!")?;
        Ok(smt_file_copy_path)
    }
    // Solves the SMT formula in the specified file and retrieves the model result.
    ///
    /// This function solves the SMT formula in the given `smt_file_path` by executing the CVC5 solver.
    /// It appends the necessary commands to the SMT file for checking satisfiability and retrieving values
    /// for the specified variables. The function then runs the CVC5 solver and captures its output.
    /// The output is parsed to extract the model result, which is returned as a `ModelResult`.
    ///
    pub fn solve_and_get_model(
        smt_file_path: String,
        variables: &HashSet<String>,
    ) -> Result<ModelResult> {
        let smt_file_copy_path =
            Self::generate_copy_path(smt_file_path).context("Failed to generate copy path!")?;
        let mut smt_file_copy = OpenOptions::new()
            .append(true)
            .open(smt_file_copy_path.clone())
            .expect("cannot open file");
        let mut copy_printer = Printer::new(&mut smt_file_copy);

        // Add (check-sat) (get-value var) ... here.
        smt::write_end(&mut copy_printer);
        for var in variables.iter() {
            smt::write_get_value(&mut copy_printer, var.clone());
        }
        let output = Command::new("cvc5").arg(smt_file_copy_path).output();
        let term = output.unwrap();
        let output_string = String::from_utf8_lossy(&term.stdout);

        smt_parser::extract_model_response(output_string.to_string())
            .context("Failed to parse smt result!")
    }
    fn lookup(&self, model_with_constraint: &ModelResult, index: usize) -> Option<bool> {
        let lookup_mapping = &self.lookup_mappings[index];

        let variables: Vec<_> = model_with_constraint
            .result
            .iter()
            .filter_map(|(key, var)| {
                if let Some(&col_index) = lookup_mapping.get(key) {
                    Some((col_index, var))
                } else {
                    None
                }
            })
            .collect();

        'outer: for (_, row) in self.fixed.iter().enumerate() {
            for &(column_index, variable) in &variables {
                if let Some(cell) = row.get(column_index) {
                    let mut t = String::new();
                    match cell {
                        CellValue::Unassigned => {
                            break;
                        }
                        CellValue::Assigned(f) => {
                            t = format!("{:?}", f);
                        }
                        CellValue::Poison(_) => {}
                    }
                    if let CellValue::Assigned(value) = cell {
                        t = u64::from_str_radix(
                            format!("{:?}", value).strip_prefix("0x").unwrap(),
                            16,
                        )
                        .unwrap()
                        .to_string();
                    }
                    if t != variable.value.element {
                        continue 'outer;
                    }
                } else {
                    continue 'outer; // Either Unassigned, Poison, or column_index out of bounds
                }
            }
            return Some(true);
        }
        // No row matched all conditions
        Some(false)
    }
    /// Dispatches the analysis based on the specified analyzer type.
    ///
    /// This function takes an `AnalyzerType` enum and performs the corresponding analysis
    /// based on the type. The supported analyzer types include:
    ///
    /// - `UnusedGates`: Analyzes and identifies unused custom gates in the circuit.
    /// - `UnconstrainedCells`: Analyzes and identifies cells with unconstrained values in the circuit.
    /// - `UnusedColumns`: Analyzes and identifies unused columns in the circuit.
    /// - `UnderconstrainedCircuit`: Analyzes the circuit for underconstrained properties by
    ///   retrieving user input for specific instance columns and conducting analysis.
    ///
    /// The function performs the analysis and updates the internal state accordingly.
    ///
    pub fn dispatch_analysis(
        &mut self,
        analyzer_type: AnalyzerType,
        prime: &str,
    ) -> Result<AnalyzerOutput> {
        match analyzer_type {
            AnalyzerType::UnusedGates => self.analyze_unused_custom_gates(),
            AnalyzerType::UnconstrainedCells => self.analyze_unconstrained_cells(),
            AnalyzerType::UnusedColumns => self.analyze_unused_columns(),
            AnalyzerType::UnderconstrainedCircuit => {
                let analyzer_input: AnalyzerInput =
                    retrieve_user_input_for_underconstrained(&self.instace_cells, &self.cs)
                        .context("Failed to retrieve user input!")?;
                self.analyze_underconstrained(analyzer_input, prime)
            }
        }
    }
}
