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
};
use z3::ast::Ast;
use z3::{ast, SatResult, Solver};

use layouter::AnalyticLayouter;

use crate::analyzer_io::{self};
use crate::analyzer_io_type::{
    AnalyzerInput, AnalyzerOutput, AnalyzerOutputStatus, VerificationMethod,
};
use crate::{
    abstract_expr::{self, AbsResult},
    analyzer_io::output_result,
    analyzer_io_type::VerificationInput,
    layouter, smt,
};
use std::str;

#[derive(Debug, PartialEq)]
pub enum Satisfiability {
    SATISFIABLE,
    UNSATISFIABLE,
}

#[derive(Debug, PartialEq)]
pub struct FieldElement {
    pub order: i64,
    pub element: i64,
}

#[derive(Debug, PartialEq)]
pub struct Variable {
    pub name: String,
    pub value: FieldElement,
}

#[derive(Debug, PartialEq)]
pub struct ModelResult {
    pub sat: Satisfiability,
    pub result: HashMap<String, Variable>,
}

fn parse_field_element(value: &str) -> FieldElement {
    // remove #f, split by "m", and then the elements would be (val, prime)
    let mut elements = value[2..].split("m");
    let value_str = elements.next().unwrap();
    let order_str = elements.next().unwrap();
    let field_element = FieldElement {
        order: order_str.parse().unwrap(),
        element: value_str.parse().unwrap(),
    };
    return field_element;
}
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
        z3_context: &'b z3::Context,
    ) -> (HashMap<ast::Int<'b>, i64>, HashMap<String, i64>) {
        let mut instance_cols: HashMap<ast::Int, i64> = HashMap::new();
        let mut instance_cols_string: HashMap<String, i64> = HashMap::new();

        for cell in eq_table {
            instance_cols.insert(ast::Int::new_const(z3_context, format!("{}", cell.0)), 0);
            instance_cols_string.insert(format!("{}", cell.0), 0);
        }

        (instance_cols, instance_cols_string)
    }

    pub fn analyze_underconstrained(&mut self, analyzer_input: AnalyzerInput) -> AnalyzerOutput {
        //let z3_context = analyzer_input.z3_context;
        let mut f = std::fs::File::create("out.smt2").unwrap();
        let mut p = smt::write_start(&mut f);
        let (formulas, vars_list) =
            Self::decompose_polynomial(self, &analyzer_input.z3_context, &mut p);

        //println!("formulas:{:?}",formulas);

        let instance = analyzer_input.verification_input.instances.clone();
        let instance_string = analyzer_input.verification_input.instances_string.clone();

        //let instance = specificInput.instances;
        let mut analyzer_output: AnalyzerOutput = AnalyzerOutput {
            output_status: AnalyzerOutputStatus::Invalid,
        };

        let output_status: AnalyzerOutputStatus = Self::control_uniqueness(
            formulas,
            vars_list,
            &instance,
            &instance_string,
            &analyzer_input,
            &mut p,
        );

        analyzer_output.output_status = output_status;
        output_result(analyzer_input, &analyzer_output);
        return analyzer_output;
    }

    pub fn log(&self) -> &[String] {
        &self.log
    }
    fn decompose_expression(
        counter: u32,
        z3_context: &'a z3::Context,
        poly: &Expression<F>,
        p: &mut smt::Printer<File>,
    ) -> (
        Option<ast::Int<'a>>,
        Vec<ast::Int<'a>>,
        u32,
        String,
        NodeType,
    ) {
        let mut cg = counter;

        match &poly {
            Expression::Constant(a) => {
                let result = Some(ast::Int::from_i64(
                    z3_context,
                    i64::try_from(a.get_lower_128()).ok().unwrap(), //*** Ask Them */
                ));
                //smt::write_const(p, format!("V-{}", counter),a.get_lower_32());
                let t = format!("as ff{} F", a.get_lower_32());
                //cg+=1;
                //println!("Constant:{:?}", a.get_lower_32());
                (result, vec![], counter, t, NodeType::Constant)
            }
            Expression::Selector(..) => {
                let result = Some(
                    ast::Int::from_i64(z3_context, i64::from(1)), //*** Ask Them */
                );

                (
                    result,
                    vec![],
                    counter,
                    format!("as ff1 F"),
                    NodeType::Constant,
                )
            }
            Expression::Fixed {
                query_index,
                column_index,
                rotation,
            } => {
                let n = format!("F-{}-{}", *column_index, rotation.0);
                let result = Some(ast::Int::new_const(z3_context, n.clone()));
                let v = vec![ast::Int::new_const(z3_context, n)];
                //let t = format!( "(as ff{} F)",a.get_lower_32());
                (result, v, counter, "".to_string(), NodeType::Constant)
            }
            Expression::Advice {
                query_index,
                column_index,
                rotation,
            } => {
                let n = format!("A-{}-{}", *column_index, rotation.0); // ("Advice-{}-{}-{:?}", *query_index, *column_index, *rotation);
                let result = Some(ast::Int::new_const(z3_context, n.clone()));
                let v = vec![ast::Int::new_const(z3_context, n.clone())];
                smt::write_var(p, n.clone());
                (result, v, counter, n, NodeType::Advice)
            }
            Expression::Instance {
                query_index,
                column_index,
                rotation,
            } => {
                let n = format!("I-{}-{}", *column_index, rotation.0);
                let result = Some(ast::Int::new_const(z3_context, n.clone()));
                let v = vec![ast::Int::new_const(z3_context, n)];
                (result, v, counter, "".to_string(), NodeType::Instance)
            }
            Expression::Negated(_poly) => {
                let (r, v, c, s, nt) = Self::decompose_expression(counter, z3_context, &_poly, p);
                let result = Some(r.unwrap().neg());
                let t = format!("ff.neg {}", s);
                (Some(result).unwrap(), v, counter, t, NodeType::Negated)
            }
            Expression::Sum(a, b) => {
                let (a_var, mut a_v, c, s1, ntl) =
                    Self::decompose_expression(counter, z3_context, a, p);
                let (b_var, mut b_v, c, s2, ntr) =
                    Self::decompose_expression(counter, z3_context, b, p);
                let result = Some(ast::Int::add(
                    z3_context,
                    &[&a_var.unwrap(), &b_var.unwrap()],
                ));
                let t = smt::write_term(p, "add".to_string(), s1, ntl, s2, ntr);
                a_v.append(&mut b_v);

                (result, a_v, counter, t, NodeType::Add)
            }
            Expression::Product(a, b) => {
                let (a_var, mut a_v, c, s1, ntl) =
                    Self::decompose_expression(counter, z3_context, a, p);
                let (b_var, mut b_v, c, s2, ntr) =
                    Self::decompose_expression(counter, z3_context, b, p);
                let result = Some(ast::Int::mul(
                    z3_context,
                    &[&a_var.unwrap(), &b_var.unwrap()],
                ));
                let t = smt::write_term(p, "mul".to_string(), s1, ntl, s2, ntr);
                a_v.append(&mut b_v);
                (result, a_v, counter, t, NodeType::Mult)
            }
            Expression::Scaled(_poly, c) => {
                // convering the field element into an expression constant and recurse.
                let (r_const, mut v_const, c, s1, ntl) =
                    Self::decompose_expression(counter, z3_context, &Expression::Constant(*c), p);

                let (r_poly, mut v_poly, c, s2, ntr) =
                    Self::decompose_expression(counter, z3_context, &_poly, p);
                let result = Some(ast::Int::mul(
                    z3_context,
                    &[&r_poly.unwrap(), &r_const.unwrap()],
                ));
                let t = smt::write_term(p, "mul".to_string(), s1, ntl, s2, ntr);
                v_poly.append(&mut v_const);
                (result, v_poly, counter, t, NodeType::Scaled)
            }
        }
    }

    pub fn decompose_polynomial(
        &'b mut self,
        z3_context: &'b z3::Context,
        p: &mut smt::Printer<File>,
    ) -> (Vec<Option<z3::ast::Bool<'b>>>, Vec<z3::ast::Int<'b>>) {
        let mut formula_conj: Vec<Option<z3::ast::Bool>> = vec![];
        let mut vars_list: HashSet<ast::Int> = Default::default();
        let zero = ast::Int::from_i64(&z3_context, 0);
        //println!("cs:{:?}",self.cs);
        //println!("regions:{:?}",self.layouter.regions);

        for gate in (&self).cs.gates.iter() {
            for poly in &gate.polys {
                let (formula, v, c, s, nt) =
                    Self::decompose_expression(self.counter, &z3_context, poly, p);
                smt::write_assert(p, s, 0, NodeType::Poly, Operation::Equal);
                let v: HashSet<ast::Int> = HashSet::from_iter(v.iter().cloned());
                vars_list.extend(v);
                formula_conj.push(Some(formula.unwrap()._eq(&zero)));
            }
        }
        let v = Vec::from_iter(vars_list);
        (formula_conj, v)
    }
    pub fn control_uniqueness(
        formulas: Vec<Option<z3::ast::Bool>>,
        vars_list: Vec<z3::ast::Int>,
        instance_cols: &HashMap<ast::Int, i64>,
        instance_cols_string: &HashMap<String, i64>,
        analyzer_input: &AnalyzerInput,
        p: &mut smt::Printer<File>,
    ) -> AnalyzerOutputStatus {
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
        if (matches!(
            analyzer_input.verification_method,
            VerificationMethod::Specific
        )) {
            // for var in instance_cols {
            //     let s1 = var
            //         .0
            //         ._eq(&ast::Int::from_i64(&analyzer_input.z3_context, *var.1));
            //     solver.assert(&s1);
            // }
            for var in instance_cols_string {
                smt::write_assert(
                    p,
                    var.0.clone(),
                    *var.1,
                    NodeType::Instance,
                    Operation::Equal,
                );
            }
        }

        let mut max_iterations: u128 = 1;
        if (matches!(
            analyzer_input.verification_method,
            VerificationMethod::Random
        )) {
            max_iterations = analyzer_input.verification_input.iterations;
        }

        // if solver.check() == SatResult::Unsat {
        //     result = AnalyzerOutputStatus::Overconstrained;
        //     return result;
        // }
        smt::write_end(p);

        for var in &vars_list {
            smt::write_get_value(p, var.to_string());
        }
        let output = Command::new("cvc5").arg("out.smt2").output();
        let t = output.unwrap();
        let str = String::from_utf8_lossy(&t.stdout);
        let model = Self::parse_output(str.to_string());
        if matches!(model.sat, Satisfiability::UNSATISFIABLE) {
            result = AnalyzerOutputStatus::Overconstrained;
        }
        for i in 1..=max_iterations {
            // If there are no more satisfiable model, then we have explored all possible configurations.
            // if matches!(solver.check(), SatResult::Unsat) {
            //     result = AnalyzerOutputStatus::NotUnderconstrained;
            //     break;
            // }
            smt::write_end(p);
            let output = Command::new("cvc5").arg("out.smt2").output();
            let t = output.unwrap();
            let str = String::from_utf8_lossy(&t.stdout);
            let model = Self::parse_output(str.to_string());
 
            if matches!(model.sat, Satisfiability::UNSATISFIABLE) {
                result = AnalyzerOutputStatus::NotUnderconstrained;
                break;
            }
            for var in &vars_list {
                smt::write_get_value(p, var.to_string());
            }
            let output = Command::new("cvc5").arg("out.smt2").output();
            let t = output.unwrap();
            let str = String::from_utf8_lossy(&t.stdout);
            let model = Self::parse_output(str.to_string());

            //let model = solver.get_model().unwrap();
            println!("Model {} to be checked:", i);
            for r in &model.result {
                println!("{} : {}", r.0, r.1.value.element)
            }
            //println!("{:?}", model.result);

            // Imitate the creation of a new solver by utilizing the stack functionality of solver
            //solver.push();
            smt::write_push(p, 1);

            //*** To check the model is under-constrained we need to:
            //      1. Fix the public input
            //      2. Change the other vars
            //      3. add these rules to the current solver and,
            //      4. find a model that satisfies these rules

            let mut same_assignments = vec![];
            let mut diff_assignments = vec![];
            for var in &vars_list {
                // The second condition is needed because the following constraints would've been added already to the solver in the beginning.
                // It is not strictly necessary, but there is no point in adding redundant constraints to the solver.
                if (instance_cols_string.contains_key(&var.to_string())
                    && !matches!(
                        analyzer_input.verification_method,
                        VerificationMethod::Specific
                    ))
                {
                    // 1. Fix the public input
                    // let var_eval = model.eval(var, true).unwrap().as_i64().unwrap();
                    // let var_same_assignment =
                    //     var._eq(&ast::Int::from_i64(&analyzer_input.z3_context, var_eval));
                    let value_from_model = &model.result[&var.to_string()].value;
                    let sa = smt::get_assert(
                        p,
                        var.to_string(),
                        value_from_model.element,
                        NodeType::Instance,
                        Operation::Equal,
                    );
                    same_assignments.push(sa);
                } else {
                    //2. Change the other vars
                    // let var_eval = model.eval(var, true).unwrap().as_i64().unwrap();
                    // let var_diff_assignment =
                    //     !var._eq(&ast::Int::from_i64(&analyzer_input.z3_context, var_eval));
                    //diff_assignments.push(var_diff_assignment);
                    let value_from_model = &model.result[&var.to_string()].value;
                    let sa = smt::get_assert(
                        p,
                        var.to_string(),
                        value_from_model.element,
                        NodeType::Instance,
                        Operation::NotEqual,
                    );
                    diff_assignments.push(sa);
                }
            }

            // let mut same_assignments_p = vec![];
            // let mut diff_assignments_p = vec![];
            let mut same_str = "".to_owned();
            for var in same_assignments.iter() {
                same_str.push_str(var);
            }
            let mut diff_str = "".to_owned();
            for var in diff_assignments.iter() {
                diff_str.push_str(var);
            }

            // 3. add these rules to the current solver,
            // let or_diff_assignments =
            //     z3::ast::Bool::or(&analyzer_input.z3_context, &diff_assignments_p);
            let or_diff_assignments = smt::get_or(p, diff_str);
            same_str.push_str(&or_diff_assignments);
            let and_all = smt::get_and(p, same_str);
            smt::write_assert_bool(p, and_all, Operation::And);
            // same_assignments_p.push(&or_diff_assignments);
            // solver.assert(&z3::ast::Bool::and(
            //     &analyzer_input.z3_context,
            //     &same_assignments_p,
            // ));

            // 4. find a model that satisfies these rules
            smt::write_end(p);

            let output = Command::new("cvc5").arg("out.smt2").output();

            let t = output.unwrap();

            let str = String::from_utf8_lossy(&t.stdout);
            let model1 = Self::parse_output(str.to_string());
            //println!("status: {:?}",str.trim());

            if matches!(model1.sat, Satisfiability::SATISFIABLE) {
                for var in &vars_list {
                    smt::write_get_value(p, var.to_string());
                }
                let output = Command::new("cvc5").arg("out.smt2").output();
                let t = output.unwrap();
                let str = String::from_utf8_lossy(&t.stdout);
                //println!("status: {:?}",str.trim());
                let model1 = Self::parse_output(str.to_string());
                //let another_constrained_model = solver.get_model();
                println!("Equivalent model for the same public input:");
                for r in &model1.result {
                    println!("{} : {}", r.0, r.1.value.element)
                }
                result = AnalyzerOutputStatus::Underconstrained;
                break;
            } else {
                println!("There is no equivalent model with the same public input to prove model {} is under-constrained!", i);
            }
            // if matches!(solver.check(), SatResult::Sat) {
            //     let another_constrained_model = solver.get_model();
            //     println!("Equivalent model for the same public input:");
            //     println!("{:?}", another_constrained_model.unwrap());
            //     result = AnalyzerOutputStatus::Underconstrained;
            //     break;
            // } else {
            //     println!("There is no equivalent model with the same public input to prove model {} is under-constrained!", i);
            // }

            // solver.pop(1);
            smt::write_pop(p, 1);
            // If no model found, add some rules to the initial solver to make sure does not generate the same model again
            let mut negated_model_variable_assignments = vec![];
            //let mut negated_model_variable_assignments_p = vec![];
            for var in vars_list.iter() {
                // let var_eval = model.eval(var, true).unwrap().as_i64().unwrap();
                // let var_assignment =
                //     !var._eq(&ast::Int::from_i64(&analyzer_input.z3_context, var_eval));
                // negated_model_variable_assignments.push(var_assignment);
                let value_from_model = &model.result[&var.to_string()].value;
                    let sa = smt::get_assert(
                        p,
                        var.to_string(),
                        value_from_model.element,
                        NodeType::Instance,
                        Operation::NotEqual,
                    );
                    negated_model_variable_assignments.push(sa);
            }
            let mut neg_model = "".to_owned();
            for var in negated_model_variable_assignments.iter() {
                neg_model.push_str(var);
            }
            //let or_neg = smt::get_or(p, neg_model);
            smt::write_assert_bool(p,neg_model,Operation::Or);
            // for var in negated_model_variable_assignments.iter() {
            //     negated_model_variable_assignments_p.push(var);
            // }
            // solver.assert(&z3::ast::Bool::or(
            //     &analyzer_input.z3_context,
            //     &negated_model_variable_assignments_p,
            // ));
        }

        result
    }

    pub fn parse_output(str: String) -> ModelResult {
        let parts = str.trim().split("\n");
        let mut first_line = true;
        let mut satisfiability: Satisfiability = Satisfiability::UNSATISFIABLE;
        let mut variable_vec: HashMap<String, Variable> = HashMap::new();

        for p in parts {
            if p == "sat" || p == "unsat"{
                //first_line = false;
                if p == "sat" {
                    satisfiability = Satisfiability::SATISFIABLE;
                }
                else {
                    satisfiability = Satisfiability::UNSATISFIABLE;
                }
            } else {
                if (satisfiability == Satisfiability::SATISFIABLE && !p.is_empty()) {
                    let variable_str = p.replace(&['(', ')'][..], "");
                    let mut vss = variable_str.split(" ");
                    let variable_name = vss.next().unwrap();
                    let field_element = parse_field_element(vss.next().unwrap());
                    variable_vec.insert(
                        variable_name.to_string(),
                        Variable {
                            name: variable_name.to_string(),
                            value: field_element,
                        },
                    );
                }
            }
        }

        let mut model = ModelResult {
            sat: satisfiability,
            result: variable_vec,
        };

        // println!("Satisfiability: {:?}", model.sat);
        // for variable in model.result {
        //     let field_element = variable.value;
        //     println!("Variable Name: {}, Variable Value: {:?}", variable.name, field_element);
        // }
        model
    }
}
