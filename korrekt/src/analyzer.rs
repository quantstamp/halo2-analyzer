use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::layouter::RegionColumn,
    dev::CellValue,
    plonk::{Circuit, ConstraintSystem, Expression},
};
use std::{
    collections::{HashMap, HashSet},
    fs,
    fs::File,
    fs::OpenOptions,
    path::Path,
    process::Command,
};

use crate::{
    abstract_expr::{self, AbsResult},
    analyzer_io::{output_result, retrieve_user_input_for_underconstrained},
    analyzer_io_type::{
        AnalyzerInput, AnalyzerOutput, AnalyzerOutputStatus, AnalyzerType, VerificationMethod,
    },
    layouter, smt,
    smt::Printer,
    smt_parser::{self, ModelResult, Satisfiability},
};
use layouter::AnalyticLayouter;

#[derive(Debug)]
pub struct Analyzer<F: FieldExt> {
    pub cs: ConstraintSystem<F>,
    pub layouter: layouter::AnalyticLayouter<F>,
    pub log: Vec<String>,
    pub counter: u32,
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
}
#[derive(Debug)]
pub enum Operation {
    Equal,
    NotEqual,
    And,
    Or,
    // Add,
    // Mul,
}

impl<'a, 'b, F: FieldExt> Analyzer<F> {
    pub fn create_with_circuit<C: Circuit<F>>(circuit: &C) -> Self {
        // create constraint system to collect custom gates
        let mut cs: ConstraintSystem<F> = Default::default();
        let config = C::configure(&mut cs);
        // synthesize the circuit with analytic layout
        let mut layouter = AnalyticLayouter::new();
        circuit.synthesize(config, &mut layouter).unwrap();
        Analyzer {
            cs,
            layouter,
            log: vec![],
            counter: 0,
        }
    }

    /// Detects unused custom gates
    pub fn analyze_unused_custom_gates(&mut self) {
        let mut count = 0;
        for gate in self.cs.gates.iter() {
            let mut used = false;

            // is this gate identically zero over regions?
            'region_search: for region in self.layouter.regions.iter() {
                let selectors = HashSet::from_iter(region.selectors().into_iter());
                for poly in gate.polynomials() {
                    let res = abstract_expr::eval_abstract(poly, &selectors);
                    if res != AbsResult::Zero {
                        used = true;
                        break 'region_search;
                    }
                }
            }

            if !used {
                count += 1;
                println!("unused gate: \"{}\" (consider removing the gate or checking selectors in regions)", gate.name());
            }
        }
        println!("Finished analysis: {} unused gates found.", count);
    }

    /// Detects unused columns
    pub fn analyze_unused_columns(&mut self) {
        let mut count = 0;
        for (column, rotation) in self.cs.advice_queries.iter().cloned() {
            let mut used = false;

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
                println!("unused column: {:?}", column);
            }
        }
        println!("Finished analysis: {} unused columns found.", count);
    }

    /// Detect assigned but unconstrained cells:
    /// (does it occur in a not-identially zero polynomial in the region?)
    /// (if not almost certainly a bug)
    pub fn analyze_unconstrained_cells(&mut self) {
        let mut count = 0;
        for region in self.layouter.regions.iter() {
            let selectors = HashSet::from_iter(region.selectors().into_iter());

            for (reg_column, rotation) in region.columns.iter().cloned() {
                let mut used = false;

                match reg_column {
                    RegionColumn::Selector(_) => continue,
                    RegionColumn::Column(column) => {
                        for gate in self.cs.gates.iter() {
                            for poly in gate.polynomials() {
                                let advices = abstract_expr::extract_columns(poly);
                                let eval = abstract_expr::eval_abstract(poly, &selectors);

                                column.index();

                                if eval != AbsResult::Zero
                                    && advices.contains(&(column.into(), rotation))
                                {
                                    used = true;
                                }
                            }
                        }
                    }
                };

                if !used {
                    count += 1;
                    println!("unconstrained cell in \"{}\" region: {:?} (rotation: {:?}) -- very likely a bug.", region.name,  reg_column, rotation);
                }
            }
        }
        println!("Finished analysis: {} unconstrained cells found.", count);
    }

    pub fn extract_instance_cols(
        &mut self,
        eq_table: HashMap<String, String>,
    ) -> HashMap<String, i64> {
        let mut instance_cols_string: HashMap<String, i64> = HashMap::new();
        for cell in eq_table {
            instance_cols_string.insert(format!("{}", cell.0), 0);
        }
        instance_cols_string
    }

    pub fn extract_instance_cols_from_region(&mut self) -> HashMap<String, i64> {
        let mut instance_cols_string: HashMap<String, i64> = HashMap::new();
        for region in self.layouter.regions.iter() {
            for eq_adv in region.__eq_table.iter() {
                instance_cols_string.insert(format!("{}", eq_adv.0), 0);
            }
        }
        instance_cols_string
    }

    /// Linter
    pub fn analyze_underconstrained(
        &mut self,
        analyzer_input: AnalyzerInput,
        fixed: Vec<Vec<CellValue<F>>>,
    ) -> AnalyzerOutput {
        fs::create_dir_all("src/output/").unwrap();
        let smt_file_path = "src/output/out.smt2";
        // TODO: extract the modulus from F
        let base_field_prime = "307";
        let mut smt_file = std::fs::File::create(smt_file_path).unwrap();
        let mut printer = smt::write_start(&mut smt_file, base_field_prime.to_string());

        Self::decompose_polynomial(self, &mut printer, fixed);

        let instance_string = analyzer_input.verification_input.instances_string.clone();

        let mut analyzer_output: AnalyzerOutput = AnalyzerOutput {
            output_status: AnalyzerOutputStatus::Invalid,
        };
        for region in self.layouter.regions.iter() {
            for eq_adv in region.__advice_eq_table.iter() {

                smt::write_var(&mut printer, eq_adv.0.to_string());
                smt::write_var(&mut printer, eq_adv.1.to_string());

                let neg = format!("(ff.neg {})", eq_adv.1.to_string());
                let term = smt::write_term(
                    &mut printer,
                    "add".to_string(),
                    eq_adv.0.to_string(),
                    NodeType::Advice,
                    neg,
                    NodeType::Advice,
                );
                smt::write_assert(
                    &mut printer,
                    term,
                    "0".to_string(),
                    NodeType::Poly,
                    Operation::Equal,
                );
            }
        }

        for region in self.layouter.regions.iter() {
            for eq_adv in region.__eq_table.iter() {
                smt::write_var(&mut printer, eq_adv.0.to_string());
                smt::write_var(&mut printer, eq_adv.1.to_string());

                let neg = format!("(ff.neg {})", eq_adv.1.to_string());
                let term = smt::write_term(
                    &mut printer,
                    "add".to_string(),
                    eq_adv.0.to_string(),
                    NodeType::Advice,
                    neg,
                    NodeType::Advice,
                );
                smt::write_assert(
                    &mut printer,
                    term,
                    "0".to_string(),
                    NodeType::Poly,
                    Operation::Equal,
                );
            }
        }

        let output_status: AnalyzerOutputStatus = Self::control_uniqueness(
            smt_file_path.to_string(),
            &instance_string,
            &analyzer_input,
            &mut printer,
        );

        analyzer_output.output_status = output_status;
        output_result(analyzer_input, &analyzer_output);
        return analyzer_output;
    }

    // pub fn log(&self) -> &[String] {
    //     &self.log
    // }

    fn decompose_expression(
        poly: &Expression<F>,
        printer: &mut smt::Printer<File>,
        region_no: usize,
        row_num: i32,
        es: &HashSet<String>,
    ) -> (String, NodeType) {
        match &poly {
            Expression::Constant(a) => {
                //smt::write_const(p, format!("V-{}", counter),a.get_lower_32());
                let term = format!("(as ff{} F)", a.get_lower_128());
                (term, NodeType::Constant)
            }
            Expression::Selector(a) => {
                let s = format!("S-{:?}-{}-{}", region_no, a.0, row_num);
                if es.contains(&s) {
                    (format!("(as ff1 F)"), NodeType::Fixed)
                } else {
                    (format!("(as ff0 F)"), NodeType::Fixed) //*** Return like the previuus, at the and replace with 1 if enabled, 0 for disabled */
                }
            }
            Expression::Fixed {
                query_index: _,
                column_index,
                rotation,
            } => {
                let term = format!("F-{}-{}-{}", region_no, *column_index, rotation.0 + row_num);
                //let t = format!( "(as ff{} F)",a.get_lower_32());
                //(term, NodeType::Fixed)
                // smt::write_var(printer, term.clone());
                // if es.contains(&term) {
                //     (format!("(as ff1 F)"), NodeType::Fixed)
                // } else {
                //     (format!("(as ff0 F)"), NodeType::Fixed) //*** Return like the previuus, at the and replace with 1 if enabled, 0 for disabled */
                // }
                (term, NodeType::Fixed)
            }
            Expression::Advice {
                query_index: _,
                column_index,
                rotation,
            } => {
                let term = format!("A-{}-{}-{}", region_no, *column_index, rotation.0 + row_num); // ("Advice-{}-{}-{:?}", *query_index, *column_index, *rotation);
                smt::write_var(printer, term.clone());
                (term, NodeType::Advice)
            }
            Expression::Instance {
                query_index: _,
                column_index: _,
                rotation: _,
            } => ("".to_string(), NodeType::Instance),
            Expression::Negated(_poly) => {
                let (node_str, _) =
                    Self::decompose_expression(&_poly, printer, region_no, row_num, es);
                let term = format!("ff.neg {}", node_str);
                (term, NodeType::Negated)
            }
            Expression::Sum(a, b) => {
                let (node_str_left, nodet_type_left) =
                    Self::decompose_expression(a, printer, region_no, row_num, &es);
                let (node_str_right, nodet_type_right) =
                    Self::decompose_expression(b, printer, region_no, row_num, &es);
                let term = smt::write_term(
                    printer,
                    "add".to_string(),
                    node_str_left,
                    nodet_type_left,
                    node_str_right,
                    nodet_type_right,
                );
                (term, NodeType::Add)
            }
            Expression::Product(a, b) => {
                let (node_str_left, nodet_type_left) =
                    Self::decompose_expression(a, printer, region_no, row_num, es);
                let (node_str_right, nodet_type_right) =
                    Self::decompose_expression(b, printer, region_no, row_num, es);
                let term = smt::write_term(
                    printer,
                    "mul".to_string(),
                    node_str_left,
                    nodet_type_left,
                    node_str_right,
                    nodet_type_right,
                );
                (term, NodeType::Mult)
            }
            Expression::Scaled(_poly, c) => {
                // convering the field element into an expression constant and recurse.
                let (node_str_left, nodet_type_left) = Self::decompose_expression(
                    &Expression::Constant(*c),
                    printer,
                    region_no,
                    row_num,
                    es,
                );
                let (node_str_right, nodet_type_right) =
                    Self::decompose_expression(&_poly, printer, region_no, row_num, es);
                let term = smt::write_term(
                    printer,
                    "mul".to_string(),
                    node_str_left,
                    nodet_type_left,
                    node_str_right,
                    nodet_type_right,
                );
                (term, NodeType::Scaled)
            }
        }
    }

    pub fn decompose_polynomial(
        &'b mut self,
        printer: &mut smt::Printer<File>,
        fixed: Vec<Vec<CellValue<F>>>,
    ) {
        if self.layouter.regions.len() > 0 {
            for region_no in 0..self.layouter.regions.len() {
                for row_num in 0..self.layouter.regions[region_no].row_count {
                    for gate in (&self).cs.gates.iter() {
                        for poly in &gate.polys {
                            let (node_str, _) = Self::decompose_expression(
                                poly,
                                printer,
                                region_no,
                                i32::try_from(row_num).ok().unwrap(),
                                &self.layouter.regions[region_no].__enabled_selectors,
                            );

                            smt::write_assert(
                                printer,
                                node_str,
                                "0".to_string(),
                                NodeType::Poly,
                                Operation::Equal,
                            );
                        }
                    }
                }
            }

            for region_no in 0..self.layouter.regions.len() {
                for row_num in 0..self.layouter.regions[region_no].row_count {
                    //println!("lookup: {:?}",self.cs.lookups.clone());
                    for lookup in self.cs.lookups.iter() {
                        //lookups.iter() {
                        //let mut cons_str = "".to_string();
                        let mut cons_str_vec = Vec::new();
                        for poly in &lookup.input_expressions {
                            let (node_str, _) = Self::decompose_expression(
                                poly,
                                printer,
                                region_no,
                                i32::try_from(row_num).ok().unwrap(),
                                &self.layouter.regions[region_no].__enabled_selectors,
                            );
                            cons_str_vec.push(node_str);
                            //cons_str.push_str(&node_str);
                        }
                        let mut exit = false;
                        let mut col_indices = Vec::new();
                        for col in lookup.table_expressions.clone() {
                            if exit {
                                break;
                            }
                            match col {
                                Expression::Fixed {
                                    query_index: _,
                                    column_index,
                                    rotation: _,
                                } => {
                                    col_indices.push(column_index);
                                }
                                _ => {} //extract col index to col_indices
                            }
                        }
                        println!("col_indices: {:?}",col_indices);
                        println!("cons_str_vec: {:?}",cons_str_vec);
                        let mut big_cons_str = "".to_string();
                        let mut big_cons = vec![];
                        for row in 0..fixed[0].len() {//*** Iterate over look up table rows */
                            if exit {
                                break;
                            }
                            //let mut cons_str = "".to_string();
                            let mut equalities = vec![];
                            let mut eq_str = String::new();
                            for col in 0..col_indices.len() {//*** Iterate over fixed cols */
                                let mut t = String::new();
                                match fixed[col_indices[col]][row] {
                                    CellValue::Unassigned => {
                                        exit = true;
                                        break;
                                    }
                                    CellValue::Assigned(f) => {
                                        t = f.get_lower_128().to_string();
                                    }
                                    CellValue::Poison(_) => todo!(),
                                }
                                if let CellValue::Assigned(value) = fixed[col_indices[col]][row] {
                                    t = value.get_lower_128().to_string();
                                }
                                let sa = smt::get_assert(
                                    printer,
                                    cons_str_vec[col].clone(),
                                    t,
                                    NodeType::Mult,
                                    Operation::Equal,
                                );
                                equalities.push(sa);
                                //let t =  cons_str_vec[col] == fixed[col][row];
                                //and with t
                                //cons_str.push_str(t);
                            }
                            if exit{
                                break;
                            }
                            for var in equalities.iter() {
                                eq_str.push_str(var);
                            }
                            let and_eqs = smt::get_and(printer, eq_str);

                            big_cons.push(and_eqs);
                            //big_cons_str Or prev
                        }
                        for var in big_cons.iter() {
                            big_cons_str.push_str(var);
                        }

                        //let or_eqs = smt::get_or(printer, big_cons_str);

                        smt::write_assert_bool(printer, big_cons_str, Operation::Or);
                    }
                }
            }
        }
    }
    pub fn control_uniqueness(
        smt_file_path: String,
        instance_cols_string: &HashMap<String, i64>,
        analyzer_input: &AnalyzerInput,
        printer: &mut smt::Printer<File>,
    ) -> AnalyzerOutputStatus {
        let mut result: AnalyzerOutputStatus = AnalyzerOutputStatus::NotUnderconstrainedLocal;
        let mut variables: HashSet<String> = HashSet::new();
        for variable in printer.vars.keys() {
            variables.insert(variable.clone());
        }

        let mut max_iterations: u128 = 1;

        match analyzer_input.verification_method {
            VerificationMethod::Specific => {
                for var in instance_cols_string {
                    smt::write_var(printer, var.0.to_string());
                    smt::write_assert(
                        printer,
                        var.0.clone(),
                        (*var.1).to_string(),
                        NodeType::Instance,
                        Operation::Equal,
                    );
                }
            }
            VerificationMethod::Random => {
                max_iterations = analyzer_input.verification_input.iterations;
            }
        }
        let model = Self::solve_and_get_model(smt_file_path.clone(), &variables);
        if matches!(model.sat, Satisfiability::UNSATISFIABLE) {
            result = AnalyzerOutputStatus::Overconstrained;
            return result; // We can just break here.
        }
        for i in 1..=max_iterations {
            let model = Self::solve_and_get_model(smt_file_path.clone(), &variables);
            if matches!(model.sat, Satisfiability::UNSATISFIABLE) {
                result = AnalyzerOutputStatus::NotUnderconstrained;
                return result; // We can just break here.
            }

            println!("Model {} to be checked:", i);
            for r in &model.result {
                println!("{} : {}", r.1.name, r.1.value.element)
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
                    );
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
                    );
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
                Self::solve_and_get_model(smt_file_path.clone(), &variables);
            if matches!(model_with_constraint.sat, Satisfiability::SATISFIABLE) {
                println!("Equivalent model for the same public input:");
                for r in &model_with_constraint.result {
                    println!("{} : {}", r.1.name, r.1.value.element)
                }
                result = AnalyzerOutputStatus::Underconstrained;
                return result;
            } else {
                println!("There is no equivalent model with the same public input to prove model {} is under-constrained!", i);
            }
            smt::write_pop(printer, 1);

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
                    );
                    negated_model_variable_assignments.push(sa);
                }
            }
            let mut neg_model = "".to_owned();
            for var in negated_model_variable_assignments.iter() {
                neg_model.push_str(var);
            }
            smt::write_assert_bool(printer, neg_model, Operation::Or);
        }
        result
    }

    pub fn generate_copy_path(smt_file_path: String) -> String {
        let smt_path_clone = smt_file_path.clone();
        let smt_path_obj = Path::new(&smt_path_clone);
        let smt_file_stem = smt_path_obj.file_stem().unwrap();
        let smt_file_copy_path = format!(
            "{}{}{}",
            "src/output/",
            smt_file_stem.to_str().unwrap(),
            "_temp.smt2"
        );
        fs::copy(smt_file_path.clone(), smt_file_copy_path.clone()).unwrap();
        return smt_file_copy_path;
    }

    pub fn solve_and_get_model(smt_file_path: String, variables: &HashSet<String>) -> ModelResult {
        let smt_file_copy_path = Self::generate_copy_path(smt_file_path.clone());
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
        let output = Command::new("cvc5")
            .arg(smt_file_copy_path.clone())
            .output();
        let term = output.unwrap();
        let output_string = String::from_utf8_lossy(&term.stdout);
        let model = smt_parser::extract_model_response(output_string.to_string());
        //fs::remove_file(smt_file_copy_path.clone());
        return model;
    }

    pub fn dispatch_analysis(
        &mut self,
        analyzer_type: AnalyzerType,
        fixed: Vec<Vec<CellValue<F>>>,
    ) -> bool {
        match analyzer_type {
            AnalyzerType::UnusedGates => {
                self.analyze_unused_custom_gates();
            }
            AnalyzerType::UnconstrainedCells => {
                self.analyze_unconstrained_cells();
            }
            AnalyzerType::UnusedColumns => {
                self.analyze_unused_columns();
            }
            AnalyzerType::UnderconstrainedCircuit => {
                let mut instance_cols_string =
                    self.extract_instance_cols(self.layouter.eq_table.clone());
                let instance_cols_string_from_region = self.extract_instance_cols_from_region();
                instance_cols_string.extend(instance_cols_string_from_region);
                let analyzer_input: AnalyzerInput =
                    retrieve_user_input_for_underconstrained(&instance_cols_string);
                self.analyze_underconstrained(analyzer_input, fixed);
            }
        };
        return true;
    }
}
