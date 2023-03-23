use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::layouter::RegionColumn,
    plonk::{Circuit, ConstraintSystem, Expression},
};
use std::{
    collections::{HashMap, HashSet},
    ops::Neg,
};
use z3::ast::Ast;
use z3::{ast, SatResult, Solver};

use layouter::AnalyticLayouter;

use crate::{abstract_expr::{self, AbsResult}, layouter, analyzer_io_type::VerificationInput, analyzer_io::output_result};
use crate::analyzer_io_type::{AnalyzerInput, AnalyzerOutput, VerificationMethod, AnalyzerOutputStatus};
use crate::analyzer_io::{self};

#[derive(Debug)]
pub struct Analyzer<F: FieldExt> {
    cs: ConstraintSystem<F>,
    pub layouter: layouter::AnalyticLayouter<F>,
    log: Vec<String>,
}

trait FMCheck<'a, 'b, F: FieldExt> {
    fn decompose_expression(
        z3_context: &'a z3::Context,
        poly: &Expression<F>,
    ) -> (Option<ast::Int<'a>>, Vec<ast::Int<'a>>);



    fn decompose_polynomial(
        &'b mut self,
        z3_context: &'b z3::Context,
    ) -> (Vec<Option<z3::ast::Bool<'b>>>, Vec<z3::ast::Int<'b>>);
}

impl<'a, 'b, F: FieldExt> FMCheck<'a, 'b, F> for Analyzer<F> {
    fn decompose_expression(
        z3_context: &'a z3::Context,
        poly: &Expression<F>,
    ) -> (Option<ast::Int<'a>>, Vec<ast::Int<'a>>) {
        match &poly {
            Expression::Constant(a) => {
                let result = Some(ast::Int::from_i64(
                    z3_context,
                    i64::try_from(a.get_lower_128()).ok().unwrap(), //*** Ask Them */
                ));
                (result, vec![])
            }
            Expression::Selector(..) => {
                let result = Some(
                    ast::Int::from_i64(z3_context, i64::from(1)), //*** Ask Them */
                );

                (result, vec![])
            }
            Expression::Fixed {
                query_index,
                column_index,
                rotation,
            } => {
                let n = format!("F-{}-{}", *column_index, rotation.0);
                let result = Some(ast::Int::new_const(z3_context, n.clone()));
                let v = vec![ast::Int::new_const(z3_context, n)];
                (result, v)
            }
            Expression::Advice {
                query_index,
                column_index,
                rotation,
            } => {
                let n = format!("A-{}-{}", *column_index, rotation.0); // ("Advice-{}-{}-{:?}", *query_index, *column_index, *rotation);
                let result = Some(ast::Int::new_const(z3_context, n.clone()));
                let v = vec![ast::Int::new_const(z3_context, n)];
                (result, v)
            }
            Expression::Instance {
                query_index,
                column_index,
                rotation,
            } => {
                let n = format!("I-{}-{}", *column_index, rotation.0);
                let result = Some(ast::Int::new_const(z3_context, n.clone()));
                let v = vec![ast::Int::new_const(z3_context, n)];
                (result, v)
            }
            Expression::Negated(_poly) => {
                let (r, v) = Self::decompose_expression(z3_context, &_poly);
                let result = Some(r.unwrap().neg());
                (Some(result).unwrap(), v)
            }
            Expression::Sum(a, b) => {
                let (a_var, mut a_v) = Self::decompose_expression(z3_context, a);
                let (b_var, mut b_v) = Self::decompose_expression(z3_context, b);
                let result = Some(ast::Int::add(
                    z3_context,
                    &[&a_var.unwrap(), &b_var.unwrap()],
                ));
                a_v.append(&mut b_v);
                (result, a_v)
            }
            Expression::Product(a, b) => {
                let (a_var, mut a_v) = Self::decompose_expression(z3_context, a);
                let (b_var, mut b_v) = Self::decompose_expression(z3_context, b);
                let result = Some(ast::Int::mul(
                    z3_context,
                    &[&a_var.unwrap(), &b_var.unwrap()],
                ));
                a_v.append(&mut b_v);
                (result, a_v)
            }
            Expression::Scaled(_poly, c) => {
                // convering the field element into an expression constant and recurse.
                let (r_const, mut v_const) =
                    Self::decompose_expression(z3_context, &Expression::Constant(*c));

                let (r_poly, mut v_poly) = Self::decompose_expression(z3_context, &_poly);
                let result = Some(ast::Int::mul(
                    z3_context,
                    &[&r_poly.unwrap(), &r_const.unwrap()],
                ));
                v_poly.append(&mut v_const);
                (result, v_poly)
            }
        }
    }

    fn decompose_polynomial(
        &'b mut self,
        z3_context: &'b z3::Context,
    ) -> (Vec<Option<z3::ast::Bool<'b>>>, Vec<z3::ast::Int<'b>>) {
        let mut formula_conj: Vec<Option<z3::ast::Bool>> = vec![];
        let mut vars_list: HashSet<ast::Int> = Default::default();
        let zero = ast::Int::from_i64(&z3_context, 0);
        for gate in self.cs.gates.iter() {
            for poly in &gate.polys {
                let (formula, v) = Self::decompose_expression(&z3_context, poly);
                let v: HashSet<ast::Int> = HashSet::from_iter(v.iter().cloned());
                vars_list.extend(v);
                formula_conj.push(Some(formula.unwrap()._eq(&zero)));
            }
        }
        let v = Vec::from_iter(vars_list);
        (formula_conj, v)
    }
}

impl<'b,F: FieldExt> Analyzer<F> {
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
        z3_context: &'b z3::Context,
    ) -> HashMap<ast::Int<'b>, i64> {
        let mut instance_cols: HashMap<ast::Int, i64> = HashMap::new();

        for cell in eq_table {
            instance_cols.insert(ast::Int::new_const(z3_context, format!("{}", cell.0)), 0);
        }

        instance_cols
    }

    pub fn analyze_underconstrained(&mut self, analyzer_input: AnalyzerInput) -> AnalyzerOutput {
        //let z3_context = analyzer_input.z3_context;
        let (formulas, vars_list) = Self::decompose_polynomial(self, &analyzer_input.z3_context);

        let instance = analyzer_input.verification_input.instances.clone();
 
        //let instance = specificInput.instances;
        let mut analyzer_output: AnalyzerOutput = AnalyzerOutput{output_status:AnalyzerOutputStatus::Invalid};

        let output_status: AnalyzerOutputStatus = Self::control_uniqueness(
            formulas,
            vars_list,
            &instance,
            &analyzer_input
        );

        analyzer_output.output_status = output_status;
        output_result(analyzer_input, &analyzer_output);
        return analyzer_output;
    }

    fn log(&self) -> &[String] {
        &self.log
    }

    fn control_uniqueness(
        formulas: Vec<Option<z3::ast::Bool>>,
        vars_list: Vec<z3::ast::Int>,
        instance_cols: &HashMap<ast::Int, i64>,
        analyzer_input: &AnalyzerInput
    ) -> AnalyzerOutputStatus {
        println!("{:?}",analyzer_input);
        let mut result: AnalyzerOutputStatus = AnalyzerOutputStatus::NotUnderconstrainedLocal;

        // This is the main solver
        let solver = Solver::new(&analyzer_input.z3_context);
        for f in formulas.clone() {
            solver.assert(&f.unwrap().clone());
        }
    
        //*** Add non-negative constraint */
        for var in vars_list.iter() {
            let s1 = var.ge(&ast::Int::from_i64(&analyzer_input.z3_context, 0));
            solver.assert(&s1);
        }
    
        //*** Fix Public Input */
        if (matches!(analyzer_input.verification_method, VerificationMethod::Specific)) {
            for var in instance_cols {
                let s1 = var.0._eq(&ast::Int::from_i64(&analyzer_input.z3_context, *var.1));
                solver.assert(&s1);
            }
        }

        let mut max_iterations: u128 = 1;
        if (matches!(analyzer_input.verification_method, VerificationMethod::Random)) {
            max_iterations = analyzer_input.verification_input.iterations;
        }

        if solver.check() == SatResult::Unsat {
            result = AnalyzerOutputStatus::Overconstrained;
            return result
        }

        for i in 1..=max_iterations {            
            // If there are no more satisfiable model, then we have explored all possible configurations.
            if matches!(solver.check(), SatResult::Unsat) {
                result = AnalyzerOutputStatus::NotUnderconstrained;
                break;
            }

            let model = solver.get_model().unwrap();
            println!("Model {} to be checked:", i);
            println!("{:?}", model);

            // Imitate the creation of a new solver by utilizing the stack functionality of solver
            solver.push();

            //*** To check the model is under-constrained we need to:
            //      1. Fix the public input
            //      2. Change the other vars
            //      3. add these rules to the current solver and,
            //      4. find a model that satisfies these rules
            
            let mut same_assignments = vec![];
            let mut diff_assignments = vec![];
            for var in vars_list.iter() {
                // The second condition is needed because the following constraints would've been added already to the solver in the beginning.
                // It is not strictly necessary, but there is no point in adding redundant constraints to the solver.
                if (instance_cols.contains_key(var) && !matches!(analyzer_input.verification_method, VerificationMethod::Specific)) { 
                    // 1. Fix the public input
                    let var_eval = model.eval(var, true).unwrap().as_i64().unwrap();
                    let var_same_assignment = var._eq(&ast::Int::from_i64(&analyzer_input.z3_context, var_eval));
                    same_assignments.push(var_same_assignment);
                } else {
                    // 2. Change the other vars
                    let var_eval = model.eval(var, true).unwrap().as_i64().unwrap();
                    let var_diff_assignment = !var._eq(&ast::Int::from_i64(&analyzer_input.z3_context, var_eval));
                    diff_assignments.push(var_diff_assignment);
                }
            }

            let mut same_assignments_p = vec![];
            let mut diff_assignments_p = vec![];
            for var in same_assignments.iter() {
                same_assignments_p.push(var);
            }
            for var in diff_assignments.iter() {
                diff_assignments_p.push(var);
            }

            // 3. add these rules to the current solver,
            let or_diff_assignments = z3::ast::Bool::or(&analyzer_input.z3_context, &diff_assignments_p);
            same_assignments_p.push(&or_diff_assignments);
            solver.assert(&z3::ast::Bool::and(&analyzer_input.z3_context, &same_assignments_p));

            // 4. find a model that satisfies these rules
            if matches!(solver.check(), SatResult::Sat) {
                let another_constrained_model = solver.get_model();
                println!("Equivalent model for the same public input:");
                println!("{:?}", another_constrained_model.unwrap());
                result = AnalyzerOutputStatus::Underconstrained;
                break;
            } else {
                println!("There is no equivalent model with the same public input to prove model {} is under-constrained!", i);
            }

            solver.pop(1);

            // If no model found, add some rules to the initial solver to make sure does not generate the same model again
            let mut negated_model_variable_assignments = vec![];
            let mut negated_model_variable_assignments_p = vec![];
            for var in vars_list.iter() {
                let var_eval = model.eval(var, true).unwrap().as_i64().unwrap();
                let var_assignment = !var._eq(&ast::Int::from_i64(&analyzer_input.z3_context, var_eval));
                negated_model_variable_assignments.push(var_assignment);
            }
            for var in negated_model_variable_assignments.iter() {
                negated_model_variable_assignments_p.push(var);
            }
            solver.assert(&z3::ast::Bool::or(&analyzer_input.z3_context, &negated_model_variable_assignments_p));
        }

        result
    }
}
