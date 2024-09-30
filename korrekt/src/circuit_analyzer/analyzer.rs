use super::{analyzable::AnalyzableField, halo2_proofs_libs::*};
use anyhow::{anyhow, Context, Result};
use log::info;
use num::{BigInt, Num};
use num_bigint::Sign;

use std::{
    collections::{HashMap, HashSet},
    fs::{self, File, OpenOptions},
    path::Path,
    process::Command,
};

use lazy_static::lazy_static;

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
    pub fixed: Vec<Vec<BigInt>>,
    pub selectors: Vec<Vec<bool>>,
    pub log: Vec<String>,
    pub permutation: HashMap<String, String>,
    pub instance_cells: HashMap<String, i64>,
    pub cell_to_cycle_head: HashMap<String, String>,
    pub counter: u32,
    pub lookup_mappings: Vec<HashMap<String, usize>>,
    pub lookup_tables: Vec<LookupTable>,
    pub analysis_type: AnalyzerType,
    pub prime: String,
    pub all_variables: HashSet<String>,
    pub smt_file: Option<File>,
    pub cycle_abs_value: HashMap<String, AbsResult>,
    pub cycle_bigint_value: HashMap<String, BigInt>,
    pub selector_indices: HashSet<usize>,
}

#[derive(Debug)]
pub enum NodeCategory {
    Variable,
    Constant,
    Polynomial,
    Invalid,
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

impl NodeType {
    pub fn category(&self) -> NodeCategory {
        match self {
            NodeType::Advice | NodeType::Instance => NodeCategory::Variable,
            NodeType::Fixed | NodeType::Constant => NodeCategory::Constant,
            NodeType::Mult
            | NodeType::Add
            | NodeType::Negated
            | NodeType::Scaled
            | NodeType::Poly => NodeCategory::Polynomial,
            _ => NodeCategory::Invalid,
        }
    }
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
    ZeroSelector,
    Zero,
    One,
    NonZero,
}

#[derive(Debug)]
pub struct LookupTable {
    pub function_name: String,
    pub function_body: String,
    pub column_indices: Vec<usize>,
    pub row_set: HashSet<Vec<BigInt>>,
    pub match_index: usize,
    pub matched_lookup_exists: bool,
}

lazy_static! {
    pub static ref SMT_FILE_PATH: &'static str = "src/output/out.smt2";
}

impl<'b, F: AnalyzableField> Analyzer<F> {
    pub fn new<ConcreteCircuit: Circuit<F>>(
        circuit: &ConcreteCircuit,
        k: u32,
        analysis_type: AnalyzerType,
        analyzer_input: Option<&AnalyzerInput>,
    ) -> Result<Self, anyhow::Error> {
        let modulus = bn256::fr::MODULUS_STR;
        let without_prefix = modulus.trim_start_matches("0x");
        let prime = BigInt::from_str_radix(without_prefix, 16)
            .unwrap()
            .to_string();
        let analyzable = Analyzable::config_and_synthesize(circuit, k)?;

        // Convert fixed to an equivalent matrix with BigInt type instead of CellValue
        let mut fixed = Vec::new();
        for col in analyzable.fixed.iter() {
            let mut new_col = Vec::new();

            for cell in col.iter() {
                match cell {
                    CellValue::Assigned(fixed_val) => {
                        let t = BigInt::from_str_radix(
                            format!("{:?}", fixed_val).strip_prefix("0x").unwrap(),
                            16,
                        )
                        .unwrap();
                        new_col.push(t);
                    }
                    CellValue::Unassigned => {
                        new_col.push(BigInt::from(0));
                    }
                    CellValue::Poison(_) => {
                        new_col.push(BigInt::from(0));
                    }
                }
            }

            fixed.push(new_col);
        }

        let mut selector_indices = HashSet::new();
        for selector in &analyzable.cs.selector_map {
            selector_indices.insert(selector.index);
        }
        let (permutation, instance_cells, cell_to_cycle_head, cycle_abs_value, cycle_bigint_value) =
            Analyzer::<F>::extract_permutations(&analyzable.permutation, &fixed);
        let mut analyzer = Analyzer {
            cs: analyzable.cs,
            regions: analyzable.regions,
            fixed: fixed,
            selectors: analyzable.selectors,
            log: Vec::new(),
            permutation,
            instance_cells,
            cell_to_cycle_head,
            counter: 0,
            lookup_mappings: Vec::new(),
            lookup_tables: Vec::new(),
            analysis_type,
            prime,
            all_variables: HashSet::new(),
            smt_file: None,
            cycle_abs_value: cycle_abs_value,
            cycle_bigint_value,
            selector_indices,
        };

        fs::create_dir_all("src/output/").unwrap();
        let mut smt_file =
            std::fs::File::create(&*SMT_FILE_PATH).context("Failed to create file!")?;
        let mut printer = Printer::new(&mut smt_file);

        if matches!(
            analyzer.analysis_type,
            AnalyzerType::UnderconstrainedCircuit
        ) {
            let input = analyzer_input.unwrap();
            if input.verification_method == VerificationMethod::Specific
                && input.verification_input.instance_cells.len() == 0
            {
                let instance =
                    retrieve_user_input_for_underconstrained::<Fr>(input, &analyzer.instance_cells)
                        .context("Failed to retrieve user input!")?;
                analyzer.instance_cells = instance.clone();
            } else if input.verification_method == VerificationMethod::Specific {
                analyzer.instance_cells = analyzer_input
                    .unwrap()
                    .verification_input
                    .instance_cells
                    .clone();
            }

            printer.write_start(analyzer.prime.to_owned());

            let _ = analyzer.decompose_polynomial(&mut printer, &analyzer_input.unwrap());

            for permutation in &analyzer.permutation {
                let mut permutation_r = permutation.0.to_owned();
                let mut permutation_l = permutation.1.to_owned();
                let mut r_is_fixed = false;
                let mut l_is_fixed = false;
                if analyzer
                    .cell_to_cycle_head
                    .contains_key(&permutation.0.to_owned())
                {
                    if analyzer
                        .cycle_abs_value
                        .contains_key(&analyzer.cell_to_cycle_head[&permutation.0.to_owned()])
                    {
                        r_is_fixed = true;
                        permutation_r = format!(
                            "(as ff{:?} F)",
                            analyzer.cycle_bigint_value
                                [&analyzer.cell_to_cycle_head[permutation.0]]
                                .to_owned()
                        );
                    } else {
                        permutation_r = analyzer.cell_to_cycle_head[permutation.0].to_owned();
                    }
                }

                if !analyzer.all_variables.contains(&permutation_r) && !r_is_fixed {
                    analyzer.all_variables.insert(permutation_r.clone());

                    printer.write_var(permutation_r.to_owned());
                }
                if analyzer
                    .cell_to_cycle_head
                    .contains_key(&permutation.1.to_owned())
                {
                    if analyzer
                        .cycle_abs_value
                        .contains_key(&analyzer.cell_to_cycle_head[&permutation.1.to_owned()])
                    {
                        l_is_fixed = true;
                        permutation_l = format!(
                            "(as ff{:?} F)",
                            analyzer.cycle_bigint_value
                                [&analyzer.cell_to_cycle_head[permutation.1]]
                                .to_owned()
                        );
                    } else {
                        permutation_l = analyzer.cell_to_cycle_head[permutation.1].to_owned();
                    }
                }

                if !permutation_l.eq(&permutation_r) {
                    if !analyzer.all_variables.contains(&permutation_l) && !l_is_fixed {
                        analyzer.all_variables.insert(permutation_l.clone());
                        printer.write_var(permutation_l.to_owned());
                    }

                    let neg = format!("(ff.neg {})", permutation_l);
                    let term = printer.write_term(
                        "add".to_owned(),
                        permutation_r.to_owned(),
                        NodeType::Advice,
                        neg,
                        NodeType::Advice,
                    );
                    printer.write_assert(term, "0".to_owned(), NodeType::Poly, Operation::Equal);
                }
            }
        }

        analyzer.smt_file = Some(smt_file);

        Ok(analyzer)
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
                let selectors = region.enabled_selectors.keys().cloned().collect();
                for row_num in 0..region_end - region_begin + 1 {
                    for poly in gate.polynomials() {
                        let res = abstract_expr::eval_abstract(
                        poly,
                        &selectors,
                        region_begin,
                        region_end,
                        row_num as i32,
                        &self.fixed,
                        &self.cell_to_cycle_head,
                        &self.cycle_abs_value,
                    )
                    .with_context(|| format!(
                        "Failed to run abstract evaluation for polynomial at region from row: {} to {}.",
                        region_begin, region_end
                    ))?;
                        if res != AbsResult::Zero {
                            used = true;
                            break 'region_search;
                        }
                    }
                }
            }

            if !used {
                count += 1;
                self.log.push(format!("unused gate: \"{}\" (consider removing the gate or checking selectors or fixed assignments in regions)", gate.name()));
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
                        for row_num in 0..region_end - region_begin + 1 {
                            for gate in self.cs.gates.iter() {
                                for poly in gate.polynomials() {
                                    let advices = abstract_expr::extract_columns(poly);
                                    let eval = abstract_expr::eval_abstract(
                                    poly,
                                    &selectors,
                                    region_begin,
                                    region_end,
                                    row_num as i32,
                                    &self.fixed,
                                    &self.cell_to_cycle_head,
                                    &self.cycle_abs_value,
                                )
                                .with_context(|| format!(
                                    "Failed to run abstract evaluation for polynomial at region from row: {} to {}.",
                                    region_begin, region_end
                                ))?;
                                    if eval != AbsResult::Zero
                                        && advices
                                            .contains(&(reg_column, Rotation(rotation as i32)))
                                    {
                                        used = true;
                                    }
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
        fixed: &Vec<Vec<BigInt>>,
    ) -> (
        HashMap<String, String>,
        HashMap<String, i64>,
        HashMap<String, String>,
        HashMap<String, AbsResult>,
        HashMap<String, BigInt>,
    ) {
        let mut pairs = HashMap::<String, String>::new();
        let mut instances = HashMap::<String, i64>::new();
        let mut cycles = Vec::<Vec<String>>::new();
        let mut num_of_cycles = 0;
        let mut cell_to_cycle_head = HashMap::<String, String>::new();
        let mut cycle_abs_value: HashMap<String, AbsResult> = HashMap::new();
        let mut cycle_bigint_value: HashMap<String, BigInt> = HashMap::new();

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
                        let mut left_is_fixed: bool = false;
                        let mut left_abs = AbsResult::Variable;
                        let mut left_big_int_val = BigInt::from(0);
                        let mut right_is_fixed: bool = false;
                        let mut right_abs = AbsResult::Variable;
                        let mut right_big_int_val = BigInt::from(0);
                        let left_cell = permutation.columns[cycle_col];

                        #[cfg(any(
                            feature = "use_zcash_halo2_proofs",
                            feature = "use_pse_v1_halo2_proofs",
                        ))]
                        let left_column_abr = match left_cell.column_type() {
                            Any::Advice => 'A',
                            Any::Fixed => {
                                left_is_fixed = true;
                                'F'
                            }
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
                            Any::Fixed => {
                                left_is_fixed = true;
                                'F'
                            }
                            Any::Instance => {
                                is_instance = true;
                                'I'
                            }
                        };
                        let left_column_index = left_cell.index;
                        let left =
                            format!("{}-{}-{}", left_column_abr, left_column_index, cycle_row);
                        if left_is_fixed {
                            left_big_int_val = fixed[left_column_index][cycle_row].clone();
                            if left_big_int_val.sign() == Sign::NoSign {
                                left_abs = AbsResult::Zero;
                            } else {
                                left_abs = AbsResult::NonZero;
                            }
                        }
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
                            Any::Fixed => {
                                right_is_fixed = true;
                                'F'
                            }
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
                            Any::Fixed => {
                                right_is_fixed = true;
                                'F'
                            }
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
                        if right_is_fixed {
                            right_big_int_val = fixed[right_column_index][right_cell_row].clone();
                            if right_big_int_val.sign() == Sign::NoSign {
                                right_abs = AbsResult::Zero;
                            } else {
                                right_abs = AbsResult::NonZero;
                            }
                        }
                        if is_instance {
                            instances.insert(right.clone(), 0);
                        }
                        pairs.insert(left.clone(), right.clone());

                        if cycle.is_empty() {
                            cycle.push(left.clone());
                        }
                        cycle.push(right.clone());
                        if is_instance {
                            cell_to_cycle_head.insert(left.clone(), right.clone());
                            cell_to_cycle_head.insert(right.clone(), right.clone());
                        } else {
                            cell_to_cycle_head.insert(right.clone(), left.clone());
                            cell_to_cycle_head.insert(left.clone(), left.clone());
                        }

                        if right_is_fixed {
                            cycle_abs_value.insert(cell_to_cycle_head[&right].clone(), right_abs);
                            cycle_bigint_value
                                .insert(cell_to_cycle_head[&right].clone(), right_big_int_val);
                        } else if left_is_fixed {
                            cycle_abs_value.insert(cell_to_cycle_head[&left].clone(), left_abs);
                            cycle_bigint_value
                                .insert(cell_to_cycle_head[&left].clone(), left_big_int_val);
                        }
                        cycle_col = right_cell_col;
                        cycle_row = right_cell_row;
                        cycle_length -= 1;
                    }
                    cycles.push(cycle);
                }
            }
        }
        (
            pairs,
            instances,
            cell_to_cycle_head,
            cycle_abs_value,
            cycle_bigint_value,
        )
    }

    pub fn extract_lookups(
        &mut self,
        printer: &mut smt::Printer<File>,
        cons_str_vec: Option<Vec<String>>,
    ) -> Result<()> {
        let mut lookup_index = 0;
        #[cfg(any(
            feature = "use_zcash_halo2_proofs",
            feature = "use_pse_halo2_proofs",
            feature = "use_axiom_halo2_proofs",
            feature = "use_pse_v1_halo2_proofs",
        ))]
        let lookups = self.cs.lookups.clone();
        #[cfg(any(feature = "use_scroll_halo2_proofs",))]
        let lookups = self.cs.lookups_map.clone();
        for lookup in lookups.iter() {
            let mut col_indices = Vec::new();
            #[cfg(any(
                feature = "use_zcash_halo2_proofs",
                feature = "use_pse_halo2_proofs",
                feature = "use_axiom_halo2_proofs",
                feature = "use_pse_v1_halo2_proofs",
            ))]
            let table_expressions = lookup.table_expressions.clone();
            #[cfg(any(feature = "use_scroll_halo2_proofs",))]
            let table_expressions = lookup.1.table.clone();
            for col in table_expressions {
                if let Expression::Fixed(fixed_query) = col {
                    col_indices.push(fixed_query.column_index);
                }
            }

            let row_set = self.extract_lookup_columns(&col_indices);

            let (big_cons_str, matched_lookup_exists, index) =
                Self::extract_lookup_constraints_as_function(
                    self,
                    col_indices.clone(),
                    cons_str_vec.clone(),
                    printer,
                    row_set.clone(),
                )?;

            let function_body = printer.get_or(big_cons_str);

            if matched_lookup_exists {
                self.lookup_tables.push(LookupTable {
                    function_name: String::new(),
                    function_body: String::new(),
                    column_indices: Vec::new(),
                    row_set: HashSet::new(),
                    match_index: index,
                    matched_lookup_exists,
                });
            } else {
                self.lookup_tables.push(LookupTable {
                    function_name: format!("isInLookupTable{}", lookup_index),
                    function_body: function_body,
                    column_indices: col_indices.clone(),
                    row_set,
                    match_index: 0 as usize,
                    matched_lookup_exists,
                });
            }
            lookup_index += 1;
        }
        Ok(())
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
        analyzer_input: &AnalyzerInput,
    ) -> Result<AnalyzerOutput> {
        let mut analyzer_output: AnalyzerOutput = AnalyzerOutput {
            output_status: AnalyzerOutputStatus::Invalid,
        };

        let output_status: AnalyzerOutputStatus = Self::uniqueness_assertion(self, &analyzer_input)
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
        fixed: &Vec<Vec<BigInt>>,
        cell_to_cycle_head: &HashMap<String, String>,
        cycle_bigint_value: &HashMap<String, BigInt>,
        new_variables: &mut HashSet<String>,
        selector_indices: &HashSet<usize>,
    ) -> (String, NodeType, IsZeroExpression) {
        let mut is_zero_expression = IsZeroExpression::NonZero;
        match &poly {
            Expression::Constant(a) => {
                let constant_decimal_value =
                    BigInt::from_str_radix(format!("{:?}", a).strip_prefix("0x").unwrap(), 16)
                        .unwrap();

                if constant_decimal_value.sign() == Sign::NoSign {
                    return (
                        "(as ff0 F)".to_owned(),
                        NodeType::Constant,
                        IsZeroExpression::Zero,
                    );
                } else if constant_decimal_value == BigInt::from(1) {
                    return (
                        "(as ff1 F)".to_owned(),
                        NodeType::Constant,
                        IsZeroExpression::One,
                    );
                }

                let term = format!("(as ff{:?} F)", constant_decimal_value);
                (term, NodeType::Constant, is_zero_expression)
            }
            Expression::Selector(a) => {
                if es.contains_key(a) {
                    (
                        "(as ff1 F)".to_owned(),
                        NodeType::Fixed,
                        IsZeroExpression::One,
                    )
                } else {
                    (
                        "(as ff0 F)".to_owned(),
                        NodeType::Fixed,
                        IsZeroExpression::ZeroSelector,
                    )
                }
            }
            Expression::Fixed(fixed_query) => {
                let col = fixed_query.column_index;
                let row = (fixed_query.rotation.0 + row_num) as usize + region_begin;

                if col < fixed.len() && row < fixed[col].len() {
                    let t = &fixed[col][row];
                    let term = format!("(as ff{:?} F)", t);

                    if t.sign() == Sign::NoSign {
                        if selector_indices.contains(&col) {
                            is_zero_expression = IsZeroExpression::ZeroSelector;
                        } else {
                            is_zero_expression = IsZeroExpression::Zero;
                        }
                    } else if *t == BigInt::from(1) {
                        is_zero_expression = IsZeroExpression::One;
                    }

                    (term, NodeType::Fixed, is_zero_expression)
                } else {
                    (
                        "(as ff0 F)".to_owned(),
                        NodeType::Fixed,
                        IsZeroExpression::Zero,
                    )
                }
            }
            Expression::Advice(advice_query) => {
                let term = format!(
                    "A-{}-{}",
                    advice_query.column_index,
                    advice_query.rotation.0 + row_num + region_begin as i32
                );
                let mut t = term.clone();
                let mut t_is_fixed = false;
                if cell_to_cycle_head.contains_key(&term) {
                    if cycle_bigint_value.contains_key(&cell_to_cycle_head[&term]) {
                        t_is_fixed = true;
                        t = format!(
                            "(as ff{:?} F)",
                            cycle_bigint_value[&cell_to_cycle_head[&term]].to_owned()
                        );
                    } else {
                        t = cell_to_cycle_head[&term.clone()].to_string();
                    }
                }
                if !t_is_fixed {
                    new_variables.insert(t.clone());
                }
                (t.to_string(), NodeType::Advice, is_zero_expression)
            }
            Expression::Instance(instance_query) => {
                let term = format!(
                    "I-{}-{}",
                    instance_query.column_index,
                    instance_query.rotation.0 + row_num + region_begin as i32
                );
                let mut t = term.clone();
                let mut t_is_fixed = false;
                if cell_to_cycle_head.contains_key(&term) {
                    if cycle_bigint_value.contains_key(&cell_to_cycle_head[&term]) {
                        t_is_fixed = true;
                        t = format!(
                            "(as ff{:?} F)",
                            cycle_bigint_value[&cell_to_cycle_head[&term]].to_owned()
                        );
                    } else {
                        t = cell_to_cycle_head[&term.clone()].to_string();
                    }
                }
                if !t_is_fixed {
                    new_variables.insert(t.clone());
                }
                (t.to_string(), NodeType::Instance, is_zero_expression)
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
                    cycle_bigint_value,
                    new_variables,
                    selector_indices,
                );
                if matches!(is_zero_expression, IsZeroExpression::ZeroSelector) {
                    return (
                        "(as ff0 F)".to_owned(),
                        NodeType::Fixed,
                        IsZeroExpression::ZeroSelector,
                    );
                }
                let term = if (matches!(node_type.category(), NodeCategory::Variable)
                    || matches!(node_type.category(), NodeCategory::Constant))
                {
                    format!("ff.neg {}", node_str)
                } else {
                    format!("ff.neg ({})", node_str)
                };
                (term, NodeType::Negated, is_zero_expression)
            }
            Expression::Sum(a, b) => {
                let (node_str_left, node_type_left, left_is_zero) = Self::decompose_expression(
                    a,
                    printer,
                    region_begin,
                    region_end,
                    row_num,
                    es,
                    fixed,
                    cell_to_cycle_head,
                    cycle_bigint_value,
                    new_variables,
                    selector_indices,
                );
                let (node_str_right, node_type_right, right_is_zero) = Self::decompose_expression(
                    b,
                    printer,
                    region_begin,
                    region_end,
                    row_num,
                    es,
                    fixed,
                    cell_to_cycle_head,
                    cycle_bigint_value,
                    new_variables,
                    selector_indices,
                );

                if matches!(left_is_zero, IsZeroExpression::ZeroSelector)
                    && matches!(right_is_zero, IsZeroExpression::ZeroSelector)
                {
                    return (
                        "(as ff0 F)".to_owned(),
                        NodeType::Fixed,
                        IsZeroExpression::ZeroSelector,
                    );
                }

                let term = printer.write_term(
                    "add".to_owned(),
                    node_str_left,
                    node_type_left,
                    node_str_right,
                    node_type_right,
                );
                (term, NodeType::Add, is_zero_expression)
            }
            Expression::Product(a, b) => {
                let (node_str_left, node_type_left, left_is_zero) = Self::decompose_expression(
                    a,
                    printer,
                    region_begin,
                    region_end,
                    row_num,
                    es,
                    fixed,
                    cell_to_cycle_head,
                    cycle_bigint_value,
                    new_variables,
                    selector_indices,
                );
                let (node_str_right, node_type_right, right_is_zero) = Self::decompose_expression(
                    b,
                    printer,
                    region_begin,
                    region_end,
                    row_num,
                    es,
                    fixed,
                    cell_to_cycle_head,
                    cycle_bigint_value,
                    new_variables,
                    selector_indices,
                );

                if matches!(left_is_zero, IsZeroExpression::ZeroSelector)
                    || matches!(right_is_zero, IsZeroExpression::ZeroSelector)
                {
                    return (
                        "(as ff0 F)".to_owned(),
                        NodeType::Fixed,
                        IsZeroExpression::ZeroSelector,
                    );
                } else if matches!(left_is_zero, IsZeroExpression::One)
                    && matches!(right_is_zero, IsZeroExpression::One)
                {
                    return (
                        "(as ff1 F)".to_owned(),
                        NodeType::Fixed,
                        IsZeroExpression::One,
                    );
                } else if matches!(left_is_zero, IsZeroExpression::One) {
                    return (node_str_right, node_type_right, right_is_zero);
                } else if matches!(right_is_zero, IsZeroExpression::One) {
                    return (node_str_left, node_type_left, left_is_zero);
                }

                let term = printer.write_term(
                    "mul".to_owned(),
                    node_str_left,
                    node_type_left,
                    node_str_right,
                    node_type_right,
                );
                (term, NodeType::Mult, is_zero_expression)
            }
            Expression::Scaled(_poly, c) => {
                // convering the field element into an expression constant and recurse.
                let (node_str_left, node_type_left, left_is_zero) = Self::decompose_expression(
                    &Expression::Constant(*c),
                    printer,
                    region_begin,
                    region_end,
                    row_num,
                    es,
                    fixed,
                    cell_to_cycle_head,
                    cycle_bigint_value,
                    new_variables,
                    selector_indices,
                );
                let (node_str_right, node_type_right, right_is_zero) = Self::decompose_expression(
                    _poly,
                    printer,
                    region_begin,
                    region_end,
                    row_num,
                    es,
                    fixed,
                    cell_to_cycle_head,
                    cycle_bigint_value,
                    new_variables,
                    selector_indices,
                );
                if matches!(left_is_zero, IsZeroExpression::ZeroSelector)
                    || matches!(right_is_zero, IsZeroExpression::ZeroSelector)
                {
                    return (
                        "(as ff0 F)".to_owned(),
                        NodeType::Fixed,
                        IsZeroExpression::ZeroSelector,
                    );
                } else if matches!(left_is_zero, IsZeroExpression::One)
                    && matches!(right_is_zero, IsZeroExpression::One)
                {
                    return (
                        "(as ff1 F)".to_owned(),
                        NodeType::Fixed,
                        IsZeroExpression::One,
                    );
                } else if matches!(left_is_zero, IsZeroExpression::One) {
                    return (node_str_right, node_type_right, right_is_zero);
                } else if matches!(right_is_zero, IsZeroExpression::One) {
                    return (node_str_left, node_type_left, left_is_zero);
                }
                let term = printer.write_term(
                    "mul".to_owned(),
                    node_str_left,
                    node_type_left,
                    node_str_right,
                    node_type_right,
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
        fixed: &Vec<Vec<BigInt>>,
        cell_to_cycle_head: &HashMap<String, String>,
        new_variables: &mut HashSet<String>,
    ) -> Result<(String, NodeType, String, IsZeroExpression)> {
        let is_zero_expression = IsZeroExpression::NonZero;
        match &poly {
            Expression::Constant(a) => {
                let constant_decimal_value =
                    BigInt::from_str_radix(format!("{:?}", a).strip_prefix("0x").unwrap(), 16)
                        .unwrap();

                if constant_decimal_value.sign() == Sign::NoSign {
                    return Ok((
                        "(as ff0 F)".to_owned(),
                        NodeType::Constant,
                        constant_decimal_value.to_string(),
                        IsZeroExpression::Zero,
                    ));
                } else if constant_decimal_value == BigInt::from(1) {
                    return Ok((
                        "(as ff1 F)".to_owned(),
                        NodeType::Constant,
                        constant_decimal_value.to_string(),
                        IsZeroExpression::One,
                    ));
                }

                let term = format!("(as ff{:?} F)", constant_decimal_value);
                Ok((
                    term,
                    NodeType::Constant,
                    constant_decimal_value.to_string(),
                    is_zero_expression,
                ))
            }
            Expression::Selector(a) => {
                if es.contains_key(a) {
                    Ok((
                        "(as ff1 F)".to_owned(),
                        NodeType::Fixed,
                        "1".to_owned(),
                        IsZeroExpression::One,
                    ))
                } else {
                    Ok((
                        "(as ff0 F)".to_owned(),
                        NodeType::Fixed,
                        "0".to_owned(),
                        IsZeroExpression::ZeroSelector,
                    ))
                }
            }
            Expression::Fixed(fixed_query) => {
                let col = fixed_query.column_index;
                let row = (fixed_query.rotation.0 + row_num) as usize + region_begin;

                let t = &fixed[col][row];
                if t.sign() == Sign::NoSign {
                    return Ok((
                        "(as ff0 F)".to_owned(),
                        NodeType::Fixed,
                        "0".to_owned(),
                        IsZeroExpression::Zero,
                    ));
                } else if *t == BigInt::from(1) {
                    return Ok((
                        "(as ff1 F)".to_owned(),
                        NodeType::Fixed,
                        "1".to_owned(),
                        IsZeroExpression::One,
                    ));
                }
                let term = format!("(as ff{:?} F)", t);

                Ok((term, NodeType::Fixed, t.to_string(), is_zero_expression))
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

                new_variables.insert(t.clone());
                Ok((
                    t.to_string(),
                    NodeType::Advice,
                    t.to_string(),
                    is_zero_expression,
                ))
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
                new_variables.insert(t.clone());
                Ok((
                    t.to_string(),
                    NodeType::Advice,
                    t.to_string(),
                    is_zero_expression,
                ))
            }
            Expression::Negated(poly) => {
                let (node_str, node_type, _, _) = Self::decompose_lookup_expression(
                    poly,
                    printer,
                    region_begin,
                    region_end,
                    row_num,
                    es,
                    fixed,
                    cell_to_cycle_head,
                    new_variables,
                )
                .with_context(|| {
                    format!(
                        "Failed to decompose negated within region from row: {} to {}, at row: {}",
                        region_begin, region_end, row_num
                    )
                })?;
                if matches!(is_zero_expression, IsZeroExpression::ZeroSelector) {
                    return Ok((
                        "(as ff0 F)".to_owned(),
                        NodeType::Fixed,
                        String::from(""),
                        IsZeroExpression::ZeroSelector,
                    ));
                }
                let term = if (matches!(node_type.category(), NodeCategory::Variable)
                    || matches!(node_type.category(), NodeCategory::Constant))
                {
                    format!("ff.neg {}", node_str)
                } else {
                    format!("ff.neg ({})", node_str)
                };
                Ok((
                    term,
                    NodeType::Negated,
                    String::from(""),
                    is_zero_expression,
                ))
            }

            Expression::Sum(a, b) => {
                let (node_str_left, node_type_left, _, left_is_zero) =
                    Self::decompose_lookup_expression(
                        a,
                        printer,
                        region_begin,
                        region_end,
                        row_num,
                        es,
                        fixed,
                        cell_to_cycle_head,
                        new_variables,
                    ).with_context(|| format!("Failed to decompose the left side of the Sum expression within region from row: {} to {}, at row: {}", region_begin, region_end, row_num))?;
                let (node_str_right, node_type_right, _, right_is_zero) =
                    Self::decompose_lookup_expression(
                        b,
                        printer,
                        region_begin,
                        region_end,
                        row_num,
                        es,
                        fixed,
                        cell_to_cycle_head,
                        new_variables,
                    ).with_context(|| format!("Failed to decompose the right side of the Sum expression within region from row: {} to {}, at row: {}", region_begin, region_end, row_num))?;

                if matches!(left_is_zero, IsZeroExpression::ZeroSelector)
                    && matches!(right_is_zero, IsZeroExpression::ZeroSelector)
                {
                    return Ok((
                        "(as ff0 F)".to_owned(),
                        NodeType::Fixed,
                        "0".to_owned(),
                        IsZeroExpression::ZeroSelector,
                    ));
                }

                let term = printer.write_term(
                    "add".to_owned(),
                    node_str_left,
                    node_type_left,
                    node_str_right,
                    node_type_right,
                );
                Ok((term, NodeType::Add, String::from(""), is_zero_expression))
            }
            Expression::Product(a, b) => {
                let (node_str_left, node_type_left, variable_left, left_is_zero) =
                    Self::decompose_lookup_expression(
                        a,
                        printer,
                        region_begin,
                        region_end,
                        row_num,
                        es,
                        fixed,
                        cell_to_cycle_head,
                        new_variables,
                    ).with_context(|| format!("Failed to decompose the left side of the Product expression within region from row: {} to {}, at row: {}", region_begin, region_end, row_num))?;
                let (node_str_right, node_type_right, variable_right, right_is_zero) =
                    Self::decompose_lookup_expression(
                        b,
                        printer,
                        region_begin,
                        region_end,
                        row_num,
                        es,
                        fixed,
                        cell_to_cycle_head,
                        new_variables,
                    ).with_context(|| format!("Failed to decompose the right side of the Product expression within region from row: {} to {}, at row: {}", region_begin, region_end, row_num))?;
                if matches!(node_type_left, NodeType::Invalid) {
                    return Err(anyhow!("Left side of the Product expression evaluated to an invalid type. Check the expression within region from row: {} to {}, at row: {}", region_begin, region_end, row_num))?;
                } else if matches!(node_type_right, NodeType::Invalid) {
                    return Err(anyhow!("Right side of the Product expression evaluated to an invalid type. Check the expression within region from row: {} to {}, at row: {}", region_begin, region_end, row_num))?;
                }

                let mut var = String::from("");
                if variable_left == "1" || variable_right == "1" {
                    if variable_left == "1" {
                        var = variable_right;
                    } else {
                        var = variable_left;
                    }
                }

                if matches!(left_is_zero, IsZeroExpression::ZeroSelector)
                    || matches!(right_is_zero, IsZeroExpression::ZeroSelector)
                {
                    return Ok((
                        "(as ff0 F)".to_owned(),
                        NodeType::Fixed,
                        "0".to_owned(),
                        IsZeroExpression::ZeroSelector,
                    ));
                } else if matches!(left_is_zero, IsZeroExpression::One)
                    && matches!(right_is_zero, IsZeroExpression::One)
                {
                    return Ok((
                        "(as ff1 F)".to_owned(),
                        NodeType::Fixed,
                        "1".to_owned(),
                        IsZeroExpression::One,
                    ));
                } else if matches!(left_is_zero, IsZeroExpression::One) {
                    return Ok((node_str_right, node_type_right, var, right_is_zero));
                } else if matches!(right_is_zero, IsZeroExpression::One) {
                    return Ok((node_str_left, node_type_left, var, left_is_zero));
                }

                let term = printer.write_term(
                    "mul".to_owned(),
                    node_str_left,
                    node_type_left,
                    node_str_right,
                    node_type_right,
                );

                Ok((term, NodeType::Mult, var, is_zero_expression))
            }
            Expression::Scaled(poly, c) => {
                // convering the field element into an expression constant and recurse.
                let (node_str_left, node_type_left, _, left_is_zero) = Self::decompose_lookup_expression(
                    &Expression::Constant(*c),
                    printer,
                        region_begin,
                        region_end,
                        row_num,
                        es,
                        fixed,
                        cell_to_cycle_head,
                        new_variables,
                    ).with_context(|| format!("Failed to decompose the constant part of the Scaled expression within region from row: {} to {}, at row: {}", region_begin, region_end, row_num))?;
                let (node_str_right, node_type_right, _, right_is_zero) =
                    Self::decompose_lookup_expression(
                        poly,
                        printer,
                        region_begin,
                        region_end,
                        row_num,
                        es,
                        fixed,
                        cell_to_cycle_head,
                        new_variables,
                    ).with_context(|| format!("Failed to decompose the polynomila part of the Scaled expression within region from row: {} to {}, at row: {}", region_begin, region_end, row_num))?;
                if matches!(left_is_zero, IsZeroExpression::ZeroSelector)
                    || matches!(right_is_zero, IsZeroExpression::ZeroSelector)
                {
                    return Ok((
                        "(as ff0 F)".to_owned(),
                        NodeType::Fixed,
                        "0".to_owned(),
                        IsZeroExpression::ZeroSelector,
                    ));
                } else if matches!(left_is_zero, IsZeroExpression::One)
                    && matches!(right_is_zero, IsZeroExpression::One)
                {
                    return Ok((
                        "(as ff1 F)".to_owned(),
                        NodeType::Fixed,
                        String::from(""),
                        IsZeroExpression::One,
                    ));
                } else if matches!(left_is_zero, IsZeroExpression::One) {
                    return Ok((
                        node_str_right,
                        node_type_right,
                        String::from(""),
                        right_is_zero,
                    ));
                } else if matches!(right_is_zero, IsZeroExpression::One) {
                    return Ok((
                        node_str_left,
                        node_type_left,
                        String::from(""),
                        left_is_zero,
                    ));
                }
                let term = printer.write_term(
                    "mul".to_owned(),
                    node_str_left,
                    node_type_left,
                    node_str_right,
                    node_type_right,
                );
                Ok((term, NodeType::Scaled, String::from(""), is_zero_expression))
            }
            #[cfg(any(
                feature = "use_pse_halo2_proofs",
                feature = "use_axiom_halo2_proofs",
                feature = "use_scroll_halo2_proofs"
            ))]
            Expression::Challenge(_poly) => Err(anyhow!(
                "Challenge expression in lookup expression is invalid."
            )),
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
                if self.selectors.is_empty() || !region.enabled_selectors.is_empty() {
                    let (region_begin, region_end) = region.rows.unwrap();
                    for row_num in 0..region_end - region_begin + 1 {
                        let contains_t = region
                            .enabled_selectors
                            .values()
                            .any(|vec| vec.contains(&(row_num + region_begin)));
                        if !contains_t && !self.selectors.is_empty() {
                            continue;
                        }
                        for gate in self.cs.gates.iter() {
                            for poly in &gate.polys {
                                let mut new_variables = HashSet::new();
                                let (node_str, node_type, is_zero) = Self::decompose_expression(
                                    poly,
                                    printer,
                                    region_begin,
                                    region_end,
                                    i32::try_from(row_num).ok().unwrap(),
                                    &region.enabled_selectors,
                                    &self.fixed,
                                    &self.cell_to_cycle_head,
                                    &self.cycle_bigint_value,
                                    &mut new_variables,
                                    &self.selector_indices,
                                );

                                if !matches!(is_zero, IsZeroExpression::ZeroSelector)
                                    && !(matches!(is_zero, IsZeroExpression::Zero)
                                        && (matches!(node_type.category(), NodeCategory::Constant)))
                                {
                                    let diff: HashSet<String> = new_variables
                                        .difference(&self.all_variables)
                                        .cloned()
                                        .collect();
                                    for element in diff {
                                        self.all_variables.insert(element.clone());
                                        printer.write_var(element.to_string());
                                    }

                                    printer.write_assert(
                                        node_str,
                                        "0".to_owned(),
                                        node_type,
                                        Operation::Equal,
                                    );
                                }
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
            self.decompose_lookups_as_function(printer, analyzer_input)?;
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
    fn decompose_lookups(&mut self, printer: &mut smt::Printer<File>) -> Result<(), anyhow::Error> {
        for region in &self.regions {
            if self.selectors.is_empty() || !region.enabled_selectors.is_empty() {
                let (region_begin, region_end) = region.rows.unwrap();
                for row_num in 0..region_end - region_begin + 1 {
                    for lookup in self.cs.lookups.iter() {
                        let mut zero_lookup_expressions = Vec::new();
                        let mut cons_str_vec = Vec::new();
                        for poly in &lookup.input_expressions {
                            let mut new_variables = HashSet::new();
                            let (node_str, node_type, is_zero) = Self::decompose_expression(
                                poly,
                                printer,
                                region_begin,
                                region_end,
                                i32::try_from(row_num).ok().unwrap(),
                                &region.enabled_selectors,
                                &self.fixed,
                                &self.cell_to_cycle_head,
                                &self.cycle_bigint_value,
                                &mut new_variables,
                                &self.selector_indices,
                            );
                            if !matches!(is_zero, IsZeroExpression::ZeroSelector) {
                                let diff: HashSet<String> = new_variables
                                    .difference(&self.all_variables)
                                    .cloned()
                                    .collect();
                                for element in diff {
                                    self.all_variables.insert(element.clone());
                                    printer.write_var(element.to_string());
                                }
                                cons_str_vec.push((node_str, node_type));
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
                            Some(cons_str_vec),
                            printer,
                            Some(zero_lookup_expressions),
                        )?;
                        if big_cons_str.is_empty() {
                            continue;
                        }
                        printer.write_assert_bool(big_cons_str, Operation::Or);
                    }
                }
            }
        }
        Ok(())
    }
    fn extract_lookup_constraints(
        &self,
        col_indices: Vec<usize>,
        cons_str_vec: Option<Vec<(String, NodeType)>>,
        printer: &mut smt::Printer<File>,
        zero_lookup_expressions: Option<Vec<bool>>,
    ) -> Result<String, anyhow::Error> {
        let mut big_cons_str = String::new();
        let mut big_cons = vec![];

        for row in 0..self.fixed[0].len() {
            let mut equalities = vec![];
            let mut eq_str = String::new();
            for col in 0..col_indices.len() {
                if zero_lookup_expressions.as_ref().map_or(false, |z| !z[col]) {
                    continue;
                }
                // Define cons_str outside the match to extend its lifetime
                let default_str = (format!("x_{} ", col), NodeType::Advice);
                let cons_str = match &cons_str_vec {
                    Some(vec) => &vec[col],
                    None => &default_str,
                };

                let t = format!("{:?}", self.fixed[col_indices[col]][row]);
                let mut poly = cons_str.0.clone();
                if !matches!(cons_str.1.category(), NodeCategory::Variable)
                {
                    poly = format!("({})", cons_str.0.clone());
                }
                let sa = printer
                    .get_assert(poly, t, NodeType::Advice, Operation::Equal)
                    .context("Failed to generate assert!")?;
                equalities.push(sa);
            }

            for var in equalities.iter() {
                eq_str.push_str(var);
            }
            if eq_str.is_empty() {
                continue;
            }
            let and_eqs = printer.get_and(eq_str);
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
    fn extract_lookup_constraints_as_function(
        &self,
        col_indices: Vec<usize>,
        cons_str_vec: Option<Vec<String>>,
        printer: &mut smt::Printer<File>,
        row_set: HashSet<Vec<BigInt>>,
    ) -> Result<(String, bool, usize), anyhow::Error> {
        let mut big_cons_str = String::new();
        let mut big_cons = vec![];

        //if matches!(analyzer_input.lookup_method, LookupMethod::Interpreted) {
        // First check if there is an equivalent lookup table in the lookup_tables.
        // If there is, we can use the existing lookup function.
        // Otherwise, we will generate a new lookup function.
        let mut index = 0;
        let mut matched_lookup_exists = false;
        if self.lookup_tables.len() > 0 {
            (matched_lookup_exists, index) = self.match_equivalent_lookup_tables(row_set.clone());
        }
        if matched_lookup_exists {
            Ok((self.lookup_tables[index].function_body.clone(), true, index))
        } else {
            for row in row_set.iter() {
                let mut equalities = vec![];
                let mut eq_str = String::new();
                for col in 0..col_indices.len() {
                    // Define cons_str outside the match to extend its lifetime
                    let default_str = format!("x_{} ", col);
                    let cons_str = match &cons_str_vec {
                        Some(vec) => &vec[col],
                        None => &default_str,
                    };

                    let t = format!("{:?}", row[col]);
                    let sa = printer
                        .get_assert(cons_str.clone(), t, NodeType::Advice, Operation::Equal)
                        .context("Failed to generate assert!")?;
                    equalities.push(sa);
                }

                for var in equalities.iter() {
                    eq_str.push_str(var);
                }
                if eq_str.is_empty() {
                    continue;
                }
                let and_eqs = printer.get_and(eq_str);
                if and_eqs.is_empty() {
                    continue;
                }
                big_cons.push(and_eqs);
            }

            for var in big_cons.iter() {
                big_cons_str.push_str(var);
            }
            Ok((big_cons_str, false, 0))
        }
    }
    // Extracts the lookup dependant cells and writes assertions of an uninterpreted function using an SMT printer.
    // Also extract the list of all lookup dependant cells and their corresponding lookup mappings. These data will be used for checking if a under-constrained circuit is false positive.
    #[cfg(any(
        feature = "use_zcash_halo2_proofs",
        feature = "use_pse_halo2_proofs",
        feature = "use_axiom_halo2_proofs",
        feature = "use_pse_v1_halo2_proofs",
        feature = "use_scroll_halo2_proofs",
    ))]
    fn decompose_lookups_as_function(
        &mut self,
        printer: &mut smt::Printer<File>,
        analyzer_input: &AnalyzerInput,
    ) -> Result<(), anyhow::Error> {
        self.extract_lookups(printer, None)?;
        let mut lookup_func_map = HashMap::new();
        for region in &self.regions {
            if self.selectors.is_empty() || !region.enabled_selectors.is_empty() {
                let (region_begin, region_end) = region.rows.unwrap();
                for row_num in 0..region_end - region_begin + 1 {
                    let mut lookup_index = 0;
                    #[cfg(any(
                        feature = "use_zcash_halo2_proofs",
                        feature = "use_pse_halo2_proofs",
                        feature = "use_axiom_halo2_proofs",
                        feature = "use_pse_v1_halo2_proofs",
                    ))]
                    let lookups = self.cs.lookups.clone();
                    #[cfg(any(feature = "use_scroll_halo2_proofs",))]
                    let lookups = self.cs.lookups_map.clone();
                    for lookup in lookups.iter() {
                        let mut function_name = String::new();
                        let mut function_body = String::new();
                        let lookup_table = &self.lookup_tables[lookup_index];

                        if lookup_table.matched_lookup_exists {
                            function_name = self.lookup_tables[lookup_table.match_index]
                                .function_name
                                .clone();
                            function_body = self.lookup_tables[lookup_table.match_index]
                                .function_body
                                .clone();
                        } else {
                            function_name = lookup_table.function_name.clone();
                            function_body = lookup_table.function_body.clone();
                        }

                        let mut cons_str_vec = Vec::new();
                        let mut lookup_arg_cells = Vec::new();
                        // Decompose the lookup input expressions and store the result in cons_str_vec.
                        #[cfg(any(
                            feature = "use_zcash_halo2_proofs",
                            feature = "use_pse_halo2_proofs",
                            feature = "use_axiom_halo2_proofs",
                            feature = "use_pse_v1_halo2_proofs",
                        ))]
                        for poly in &lookup.input_expressions {
                            let mut new_variables = HashSet::new();
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
                                &mut new_variables,
                            )
                        .with_context(|| format!("Failed to decompose lookup input expression within region from row: {} to {}, at row: {}", region_begin, region_end, row_num))?;
                            if !matches!(is_zero, IsZeroExpression::ZeroSelector) {
                                let diff: HashSet<String> = new_variables
                                    .difference(&self.all_variables)
                                    .cloned()
                                    .collect();
                                for element in diff {
                                    self.all_variables.insert(element.clone());
                                    printer.write_var(element.to_string());
                                }
                                cons_str_vec.push(node_str);
                                if !var.is_empty() {
                                    lookup_arg_cells.push(var);
                                }
                            }
                        }
                        #[cfg(any(feature = "use_scroll_halo2_proofs",))]
                        for polys in &lookup.1.inputs {
                            for poly in polys {
                                let mut new_variables = HashSet::new();
                                let (node_str, _, var, is_zero) =
                                    Self::decompose_lookup_expression(
                                        poly,
                                        printer,
                                        region_begin,
                                        region_end,
                                        i32::try_from(row_num).ok().unwrap(),
                                        &region.enabled_selectors,
                                        &self.fixed,
                                        &self.cell_to_cycle_head,
                                        &mut new_variables,
                                    )
                                    .with_context(|| format!("Failed to decompose lookup input expression within region from row: {} to {}, at row: {}", region_begin, region_end, row_num))?;
                                if !matches!(is_zero, IsZeroExpression::ZeroSelector) {
                                    let diff: HashSet<String> = new_variables
                                        .difference(&self.all_variables)
                                        .cloned()
                                        .collect();
                                    for element in diff {
                                        self.all_variables.insert(element.clone());
                                        printer.write_var(element.to_string());
                                    }
                                    cons_str_vec.push(node_str);
                                    if !var.is_empty() {
                                        lookup_arg_cells.push(var);
                                    }
                                }
                            }
                        }
                        if !cons_str_vec.is_empty() {
                            let col_indices =
                                self.lookup_tables[lookup_index].column_indices.clone();

                            let mut function_input = String::new();

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
                                    // Concatenate function_input with format!("(x_{} ", col_index)
                                    if matches!(
                                        analyzer_input.lookup_method,
                                        LookupMethod::Interpreted
                                    ) {
                                        function_input.push_str(&format!("(x_{} F)", input_index));
                                        input_index += 1;
                                    }
                                }
                            }
                            if !lookup_mapping.is_empty() {
                                self.lookup_mappings.push(lookup_mapping.clone());
                            }

                            if !lookup_mapping.is_empty() {
                                if !lookup_func_map.contains_key(&lookup_index) {
                                    lookup_func_map.insert(lookup_index, true);
                                    if matches!(
                                        analyzer_input.lookup_method,
                                        LookupMethod::Interpreted
                                    ) {
                                        if !self.lookup_tables[lookup_index].matched_lookup_exists {
                                            printer.write_define_fn(
                                                function_name.clone(),
                                                function_input,
                                                "Bool".to_owned(),
                                                function_body,
                                            );
                                        }
                                    } else {
                                        printer.write_declare_fn(
                                            function_name.clone(),
                                            "F".to_owned(),
                                            "Bool".to_owned(),
                                        );
                                    }
                                }
                                if matches!(analyzer_input.lookup_method, LookupMethod::Interpreted)
                                {
                                    // Concatenate all lookup input expressions and write assertions of an interpreted function using an SMT printer.
                                    let cons_str = lookup_arg_cells
                                        .iter()
                                        .fold(String::new(), |acc, x| acc + x + " ");
                                    let cons_str = cons_str.trim();
                                    printer.write_assert_boolean_func(
                                        function_name.clone(),
                                        cons_str.to_owned(),
                                    );
                                } else {
                                    for cons_str in cons_str_vec.iter() {
                                        printer.write_assert_boolean_func(
                                            function_name.clone(),
                                            format!("{}", cons_str).to_owned(),
                                        );
                                    }
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
    fn decompose_lookups(&mut self, printer: &mut smt::Printer<File>) -> Result<(), anyhow::Error> {
        for region in &self.regions {
            if self.selectors.is_empty() || !region.enabled_selectors.is_empty() {
                let (region_begin, region_end) = region.rows.unwrap();
                for row_num in 0..region_end - region_begin + 1 {
                    for lookup in &self.cs.lookups_map {
                        let mut zero_lookup_expressions = Vec::new();
                        let mut cons_str_vec = Vec::new();
                        for polys in &lookup.1.inputs {
                            for poly in polys {
                                let mut new_variables = HashSet::new();
                                let (node_str, node_type, is_zero) = Self::decompose_expression(
                                    &poly,
                                    printer,
                                    region_begin,
                                    region_end,
                                    i32::try_from(row_num).ok().unwrap(),
                                    &region.enabled_selectors,
                                    &self.fixed,
                                    &self.cell_to_cycle_head,
                                    &self.cycle_bigint_value,
                                    &mut new_variables,
                                    &self.selector_indices,
                                );
                                if !matches!(is_zero, IsZeroExpression::ZeroSelector) {
                                    let diff: HashSet<String> = new_variables
                                        .difference(&self.all_variables)
                                        .cloned()
                                        .collect();
                                    for element in diff {
                                        self.all_variables.insert(element.clone());
                                        printer.write_var(element.to_string());
                                    }
                                    cons_str_vec.push((node_str.clone(), node_type));
                                    zero_lookup_expressions.push(true);
                                } else {
                                    zero_lookup_expressions.push(false);
                                }
                            }
                        }
                        let mut col_indices = Vec::new();
                        for col in lookup.1.table.clone() {
                            if let Expression::Fixed(fixed_query) = col {
                                col_indices.push(fixed_query.column_index);
                            }
                        }
                        let big_cons_str = Self::extract_lookup_constraints(
                            self,
                            col_indices,
                            Some(cons_str_vec),
                            printer,
                            Some(zero_lookup_expressions),
                        )?;
                        if big_cons_str.is_empty() {
                            continue;
                        }

                        printer.write_assert_bool(big_cons_str, Operation::Or);
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
        analyzer_input: &AnalyzerInput,
    ) -> Result<AnalyzerOutputStatus> {
        if let Some(smt_file) = self.smt_file.as_mut() {
            let mut printer = Printer::new(smt_file);
            let mut result: AnalyzerOutputStatus = AnalyzerOutputStatus::NotUnderconstrainedLocal;
            let mut variables: HashSet<String> = HashSet::new();
            for variable in &self.all_variables {
                variables.insert(variable.clone());
            }

            let mut max_iterations: u128 = 1;

            // Determine the verification method and configure the analysis accordingly.
            match analyzer_input.verification_method {
                // For specific public input, directly write assertions for each variable.
                VerificationMethod::Specific => {
                    for var in self.instance_cells.iter() {
                        // Declare the variables in the SMT formula.
                        if !self.all_variables.contains(&var.0.to_owned()) {
                            self.all_variables.insert(var.0.clone());
                            printer.write_var(var.0.to_owned());
                        }
                        // Write an assertion that each veriables equals the given value.
                        printer.write_assert(
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
                VerificationMethod::None => {}
            }
            let model = Self::solve_and_get_model(SMT_FILE_PATH.to_string(), &variables)
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
                let model = Self::solve_and_get_model(SMT_FILE_PATH.to_string(), &variables)
                    .context("Failed to solve and get model!")?;
                if matches!(model.sat, Satisfiability::Unsatisfiable) {
                    result = AnalyzerOutputStatus::NotUnderconstrained;
                    return Ok(result); // We can just break here.
                }
                // No need to do the lookup as they are already constrained in SMT solver where uninterpreted functions are not used for lookups.
                if !matches!(analyzer_input.lookup_method, LookupMethod::Uninterpreted) {
                    valid_model_lookeded_up = true;
                }
                // if using uninterpreted function, we need to check if the model is valid by performing the lookup.
                else {
                    uc_lookup_dependency = false;
                    // Lookup search to make sure all values in the model are valid.
                    let num_of_lookup_mappings = self.lookup_mappings.clone().len();
                    for index in 0..num_of_lookup_mappings {
                        // Perform the lookup
                        let lookup_sucessful =
                            Self::lookup(&model, &self.lookup_mappings[index], self.fixed.clone());

                        if lookup_sucessful {
                            valid_model_lookeded_up = true;
                        }
                    }
                }
                // If the model is not valid, we ignore it and continue to the next iteration.
                if valid_model_lookeded_up {
                    info!("Model {} to be checked:", i);
                    for r in &model.result {
                        info!("{} : {}", r.1.name, r.1.value.element)
                    }
                    // Imitate the creation of a new solver by utilizing the stack functionality of solver
                    printer.write_push(1);

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
                        if self.instance_cells.contains_key(var)
                            && !matches!(
                                analyzer_input.verification_method,
                                VerificationMethod::Specific
                            )
                        {
                            // 1. Fix the public input
                            let result_from_model = &model.result[var];
                            let sa = printer
                                .get_assert(
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
                            let sa = printer
                                .get_assert(
                                    result_from_model.name.clone(),
                                    result_from_model.value.element.clone(),
                                    NodeType::Advice,
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
                    let or_diff_assignments = printer.get_or(diff_str);
                    same_str.push_str(&or_diff_assignments);
                    let and_all = printer.get_and(same_str);
                    printer.write_assert_bool(and_all, Operation::And);

                    // 4. find a model that satisfies these rules
                    let model_with_constraint =
                        Self::solve_and_get_model(SMT_FILE_PATH.to_string(), &variables)
                            .context("Failed to solve and get model!")?;

                    // If using uninterpreted function, we need to check if the model is valid by performing the lookup.
                    if matches!(analyzer_input.lookup_method, LookupMethod::Uninterpreted) {
                        info!("Equivalent model for the same public input!(No Lookup Constraint):");
                        for r in &model_with_constraint.result {
                            info!("{} : {}", r.1.name, r.1.value.element)
                        }
                        uc_lookup_dependency = false;
                        let num_of_lookup_mappings = self.lookup_mappings.clone().len();
                        for index in 0..num_of_lookup_mappings {
                            // Lookup search to make sure all values in the model are valid.
                            let lookup_sucessful = Self::lookup(
                                &model_with_constraint,
                                &self.lookup_mappings[index],
                                self.fixed.clone(),
                            );
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
                                    result = AnalyzerOutputStatus::NotUnderconstrainedLocalUninterpretedLookups;
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
                    printer.write_pop(1);
                }

                // If no model found, add some rules to the initial solver to make sure does not generate the same model again
                let mut negated_model_variable_assignments = vec![];
                for res in &model.result {
                    if self.instance_cells.contains_key(&res.1.name) {
                        let sa = printer
                            .get_assert(
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

                if negated_model_variable_assignments.is_empty() {
                    continue;
                }
                for var in negated_model_variable_assignments.iter() {
                    neg_model.push_str(var);
                }
                printer.write_assert_bool(neg_model, Operation::Or);
            }
            if uc_lookup_dependency_fp
                && matches!(result, AnalyzerOutputStatus::NotUnderconstrainedLocal)
            {
                result = AnalyzerOutputStatus::NotUnderconstrainedLocalUninterpretedLookups;
            }
            Ok(result)
        } else {
            Err(anyhow!("Failed to open SMT file!"))
        }
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
        copy_printer.write_end();
        for var in variables.iter() {
            copy_printer.write_get_value(var.clone());
        }
        let output = Command::new("cvc5").arg(smt_file_copy_path).output();
        let term = output.unwrap();
        let output_string = String::from_utf8_lossy(&term.stdout);

        smt_parser::extract_model_response(output_string.to_string())
            .context("Failed to parse smt result!")
    }

    fn lookup(
        model_with_constraint: &ModelResult,
        lookup_mapping: &HashMap<String, usize>,
        fixed: Vec<Vec<BigInt>>,
    ) -> bool {
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

        'outer: for (_, row) in fixed.iter().enumerate() {
            for &(column_index, variable) in &variables {
                if let Some(cell) = row.get(column_index) {
                    let t = format!("{:?}", cell);

                    if t != variable.value.element {
                        continue 'outer;
                    }
                } else {
                    continue 'outer; // Either Unassigned, Poison, or column_index out of bounds
                }
            }
            return true;
        }
        // No row matched all conditions
        false
    }

    fn have_same_rows(matrix1: Vec<Vec<BigInt>>, matrix2: Vec<Vec<BigInt>>) -> bool {
        if matrix1.len() != matrix2.len() {
            return false;
        }
        let num_columns = matrix1[0].len();
        let num_rows = matrix1.len();

        // Transform matrices into sets of column tuples
        let mut set1: HashSet<Vec<BigInt>> = HashSet::new();
        let mut set2: HashSet<Vec<BigInt>> = HashSet::new();

        for col_index in 0..num_columns {
            let mut col_tuple1 = Vec::with_capacity(num_rows);

            let mut col_tuple2 = Vec::with_capacity(num_rows);

            for row_index in 0..num_rows {
                col_tuple1.push(matrix1[row_index][col_index].clone());
                col_tuple2.push(matrix2[row_index][col_index].clone());
            }

            set1.insert(col_tuple1);
            set2.insert(col_tuple2);
        }
        set1 == set2
    }

    fn match_equivalent_lookup_tables(
        &self,
        new_lookup_table: HashSet<Vec<BigInt>>,
    ) -> (bool, usize) {
        for (index, existing_table) in self.lookup_tables.iter().enumerate() {
            let result = existing_table.row_set == new_lookup_table;

            if result {
                return (true, index); // Match found, return true with the index of the existing table
            }
        }

        (false, 0) // No match found, return false with a default index
    }

    fn extract_lookup_columns(&self, col_indices: &[usize]) -> HashSet<Vec<BigInt>> {
        let matrix: Vec<Vec<BigInt>> = col_indices
            .iter()
            .filter_map(|&index| self.fixed.get(index).cloned())
            .collect();
        let num_columns = matrix[0].len();
        let num_rows: usize = matrix.len();

        // Transform matrices into sets of column tuples
        let mut set: HashSet<Vec<BigInt>> = HashSet::new();

        for col_index in 0..num_columns {
            let mut col_tuple = Vec::with_capacity(num_rows);

            for row_index in 0..num_rows {
                col_tuple.push(matrix[row_index][col_index].clone());
            }

            set.insert(col_tuple);
        }
        set
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
        analyzer_input: &mut AnalyzerInput,
    ) -> Result<AnalyzerOutput> {
        match self.analysis_type {
            AnalyzerType::UnusedGates => self.analyze_unused_custom_gates(),
            AnalyzerType::UnconstrainedCells => self.analyze_unconstrained_cells(),
            AnalyzerType::UnusedColumns => self.analyze_unused_columns(),
            AnalyzerType::UnderconstrainedCircuit => self.analyze_underconstrained(analyzer_input),
        }
    }
}
