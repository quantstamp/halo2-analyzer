use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::layouter::RegionColumn,
    plonk::{Circuit, ConstraintSystem, Expression},
};
use std::{
    collections::{HashMap, HashSet},
    fs::File,
    ops::Neg,
    process::Command,
    str,
    fs,
    path::Path,
    fs::OpenOptions,
};

use layouter::AnalyticLayouter;

use crate::analyzer_io::{self};
use crate::analyzer_io_type::{
    AnalyzerInput, AnalyzerOutput, AnalyzerOutputStatus, VerificationMethod,
};
use crate::{
    abstract_expr::{self, AbsResult},
    analyzer_io::output_result,
    analyzer_io_type::VerificationInput,
    layouter, 
    smt,
    smt::Printer,
    smt_parser::{self, Satisfiability, ModelResult, Variable, FieldElement}
};

#[derive(Debug)]
pub struct Analyzer<F: FieldExt> {
    pub cs: ConstraintSystem<F>,
    pub layouter: layouter::AnalyticLayouter<F>,
    pub log: Vec<String>,
    pub counter: u32,
}

pub enum NodeType {
    Constant,
    Advice,
    Instance,
    Negated,
    Mult,
    Add,
    Scaled,
    Poly,
}

pub enum Operation {
    Equal,
    NotEqual,
    And,
    Or,
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
    pub fn analyze_unsed_custom_gates(&mut self) {
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
                self.log.push(format!("unused gate: \"{}\" (consider removing the gate or checking selectors in regions)", gate.name()));
            }
        }
    }

    /// Detects unused columns
    pub fn analyze_unused_columns(&mut self) {
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
                self.log.push(format!("unused column: {:?}", column));
            }
        }
    }

    /// Detect assigned but unconstrained cells:
    /// (does it occur in a not-identially zero polynomial in the region?)
    /// (if not almost certainly a bug)
    pub fn analyze_unconstrained_cells(&mut self) {
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
                    self.log.push(format!("unconstrained cell in \"{}\" region: {:?} (rotation: {:?}) -- very likely a bug.", region.name,  reg_column, rotation));
                }
            }
        }
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

    pub fn analyze_underconstrained(&mut self, analyzer_input: AnalyzerInput) -> AnalyzerOutput {
        //let z3_context = analyzer_input.z3_context;
        let smt_file_path = "output/out.smt2";
        let base_field_prime = "11";
        let mut smt_file = std::fs::File::create(smt_file_path).unwrap();
        let mut printer = smt::write_start(&mut smt_file, base_field_prime.to_string());
              
        Self::decompose_polynomial(self, &mut printer);

        let instance_string = analyzer_input.verification_input.instances_string.clone();

        let mut analyzer_output: AnalyzerOutput = AnalyzerOutput {
            output_status: AnalyzerOutputStatus::Invalid,
        };

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

    pub fn log(&self) -> &[String] {
        &self.log
    }

    fn decompose_expression(
        poly: &Expression<F>,
        printer: &mut smt::Printer<File>,
    ) -> (
        String,
        NodeType,
    ) {
        match &poly {
            Expression::Constant(a) => {
                //smt::write_const(p, format!("V-{}", counter),a.get_lower_32());
                let term = format!("as ff{} F", a.get_lower_32());
                //println!("Constant:{:?}", a.get_lower_32());
                (term, NodeType::Constant)
            }
            Expression::Selector(..) => {
                (format!("as ff1 F"), NodeType::Constant)
            }
            Expression::Fixed {
                query_index,
                column_index,
                rotation,
            } => {
                let n = format!("F-{}-{}", *column_index, rotation.0);
                //let t = format!( "(as ff{} F)",a.get_lower_32());
                ("".to_string(), NodeType::Constant)
            }
            Expression::Advice {
                query_index,
                column_index,
                rotation,
            } => {
                let term = format!("A-{}-{}", *column_index, rotation.0); // ("Advice-{}-{}-{:?}", *query_index, *column_index, *rotation);
                smt::write_var(printer, term.clone());
                (term, NodeType::Advice)
            }
            Expression::Instance {
                query_index,
                column_index,
                rotation,
            } => {
                ("".to_string(), NodeType::Instance)
            }
            Expression::Negated(_poly) => {
                let (node_str, node_type) = Self::decompose_expression(&_poly, printer);
                let term = format!("ff.neg {}", node_str);
                (term, NodeType::Negated)
            }
            Expression::Sum(a, b) => {
                let (node_str_left, nodet_type_left) =
                    Self::decompose_expression(a, printer);
                let (node_str_right, nodet_type_right) =
                   Self::decompose_expression(b, printer);
                let term = smt::write_term(printer, "add".to_string(), node_str_left, nodet_type_left, node_str_right, nodet_type_right);
                (term, NodeType::Add)
            }
            Expression::Product(a, b) => {
                let (node_str_left, nodet_type_left) =
                    Self::decompose_expression(a, printer);
                let (node_str_right, nodet_type_right) =
                    Self::decompose_expression(b, printer);
                let term = smt::write_term(printer, "mul".to_string(), node_str_left, nodet_type_left, node_str_right, nodet_type_right);
                (term, NodeType::Mult)
            }
            Expression::Scaled(_poly, c) => {
                // convering the field element into an expression constant and recurse.
                let (node_str_left, nodet_type_left) =
                    Self::decompose_expression(&Expression::Constant(*c), printer);
                let (node_str_right, nodet_type_right) =
                    Self::decompose_expression(&_poly, printer);
                let term = smt::write_term(printer, "mul".to_string(), node_str_left, nodet_type_left, node_str_right, nodet_type_right);
                (term, NodeType::Scaled)
            }
        }
    }

    pub fn decompose_polynomial(
        &'b mut self,
        printer: &mut smt::Printer<File>,
    ) {
        for gate in (&self).cs.gates.iter() {
            for poly in &gate.polys {
                let (node_str, node_type) =
                    Self::decompose_expression(poly, printer);
                smt::write_assert(printer, node_str, "0".to_string(), NodeType::Poly, Operation::Equal);
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

        //*** Fix Public Input */
        let mut max_iterations: u128 = 1;
        if (matches!(analyzer_input.verification_method, VerificationMethod::Specific)) {
            for var in instance_cols_string {
                smt::write_assert(
                    printer,
                    var.0.clone(),
                    (*var.1.to_string()).to_string(),
                    NodeType::Instance,
                    Operation::Equal,
                );
            }
        } else if (matches!(analyzer_input.verification_method, VerificationMethod::Random)) {
            max_iterations = analyzer_input.verification_input.iterations;
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
                if (instance_cols_string.contains_key(var)
                    && !matches!(analyzer_input.verification_method, VerificationMethod::Specific
                )) {
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
            let model_with_constraint = Self::solve_and_get_model(smt_file_path.clone(), &variables);
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
                let sa = smt::get_assert(
                    printer,
                    res.1.name.clone(),
                    res.1.value.element.clone(),
                    NodeType::Instance,
                    Operation::NotEqual,
                );
                negated_model_variable_assignments.push(sa);
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
        let smt_file_copy_path = format!("output/{}{}", smt_file_stem.to_str().unwrap(), "_temp.smt2");
        fs::copy(smt_file_path.clone(), smt_file_copy_path.clone());
        return smt_file_copy_path
    }

    pub fn solve_and_get_model(smt_file_path: String, variables: &HashSet<String>) -> ModelResult{
        let smt_file_copy_path = Self::generate_copy_path(smt_file_path.clone());
        let mut smt_file_copy = OpenOptions::new().append(true).open(smt_file_copy_path.clone()).expect("cannot open file");
        let mut copy_printer = Printer::new(&mut smt_file_copy);
        
        // Add (check-sat) (get-value var) ... here.
        smt::write_end(&mut copy_printer);
        for mut var in variables.iter() {
            smt::write_get_value(&mut copy_printer, var.clone());
        }
        let output = Command::new("cvc5").arg(smt_file_copy_path.clone()).output();
        let term = output.unwrap();
        let output_string = String::from_utf8_lossy(&term.stdout);
        println!("Output {:?}", output_string);
        let model = smt_parser::extract_model_response(output_string.to_string());
        println!("Model {:?}", model);
        fs::remove_file(smt_file_copy_path.clone());
        return model
    }
}
