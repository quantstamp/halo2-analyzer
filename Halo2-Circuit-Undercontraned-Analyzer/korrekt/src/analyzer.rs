use crate::layouter;
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::layouter::RegionColumn,
    plonk::{Circuit, ConstraintSystem, Expression},
};
use std::{
    collections::{HashMap, HashSet},
    io,
    ops::Neg,
};
use z3::{ast, SatResult, Solver};

use layouter::AnalyticLayouter;
use z3::ast::Ast;

use crate::abstract_expr::{self, AbsResult};

#[derive(Debug)]
pub struct Analyzer<F: FieldExt> {
    cs: ConstraintSystem<F>,
    layouter: layouter::AnalyticLayouter<F>,
    log: Vec<String>,
}
trait FMCheck<'a, 'b, F: FieldExt> {
    fn decompose_expression(
        z3_context: &'a z3::Context,
        poly: &Expression<F>,
    ) -> (Option<ast::Int<'a>>, Vec<ast::Int<'a>>);

    fn extract_instance_colls(
        eq_table: HashMap<String, String>,
        z3_context: &'b z3::Context,
    ) -> HashMap<ast::Int<'b>, i64>;

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
                println!("constant:{}", a.get_lower_128());
                (result, vec![])
            }
            Expression::Selector(..) => {
                //unimplemented!();
                // let result = Some(ast::Int::new_const(z3_context, format!("{:?}", &a)));
                // let v = [ast::Int::new_const(z3_context, format!("{:?}", &a))];
                // (result,v.to_vec())
                let result = Some(
                    ast::Int::from_i64(z3_context, i64::from(1)), //*** Ask Them */
                );

                (result, vec![])
            }
            // Expression::Fixed { .. } => {
            //     println!("fixed {:?}", poly);
            //     unimplemented!("Implement this!");
            // }
            Expression::Fixed {
                query_index,
                column_index,
                rotation,
            } => {
                let n = format!("F-{}-{}", *column_index, rotation.0);
                //let m = format!("F-{}-{:?}", *column_index, rotation.0);
                let result = Some(ast::Int::new_const(z3_context, n.clone()));
                let v = vec![ast::Int::new_const(z3_context, n)];
                (result, v)
            }
            Expression::Advice {
                query_index,
                column_index,
                rotation,
            } => {
                let n = format!("A-{}-{}", *column_index, rotation.0); //("Advice-{}-{}-{:?}", *query_index, *column_index, *rotation);
                                                                       //let m = format!("A-{}-{}", *column_index, rotation.0); //format!("Advice-{}-{}-{:?}", *query_index, *column_index, *rotation);
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
                // let m = format!(
                //     "I-{}-{}",
                //     *column_index,
                //     rotation.0
                // );
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
                // In circuit.rs L492
                // This is a scaled polynomial
                // Scaled(Box<Expression<F>>, F)
                // For example, if we change one of the constraint to be:
                // Expression::Scaled(Box::new(dummy * a.clone() * (Expression::Constant(F::from(1)) - a.clone())), F::from(5))
                // This scales the polynomial by 5 and it will call this path.

                // Method 1: convering the field element into an expression constant and recurse.
                let (r_const, mut v_const) =
                    Self::decompose_expression(z3_context, &Expression::Constant(*c));
                // Method 2: copying code for processing expression constant from above.
                // let r_const = Some(ast::Int::from_i64(
                //     z3_context,
                //     i64::from(c.get_lower_32()),
                // ));

                let (r_poly, mut v_poly) = Self::decompose_expression(z3_context, &_poly);
                let result = Some(ast::Int::mul(
                    z3_context,
                    &[&r_poly.unwrap(), &r_const.unwrap()],
                ));
                v_poly.append(&mut v_const); // Not 100% sure if we need to do this.
                (result, v_poly)
            }
        }
    }
    fn extract_instance_colls(
        eq_table: HashMap<String, String>,
        z3_context: &'b z3::Context,
    ) -> HashMap<ast::Int<'b>, i64> {
        let mut instance_cols: HashMap<ast::Int, i64> = HashMap::new();

        for cell in eq_table {
            instance_cols.insert(ast::Int::new_const(z3_context, format!("{}", cell.0)), 0);
        }

        instance_cols
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

impl<F: FieldExt> Analyzer<F> {
    // fn new<C: Circuit<F> + Default>() -> Self {
    //     Self::new_with(&C::default())
    // }

    pub fn new_with<C: Circuit<F>>(circuit: &C) -> Self {
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

            //
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

    pub fn analyze_underconstrained(&mut self) -> i8{
        let z3_config = z3::Config::new();
        let z3_context = z3::Context::new(&z3_config);
        let instance_cols: HashMap<ast::Int, i64> =
            Self::extract_instance_colls(self.layouter.eq_table.clone(), &z3_context);

        let (formulas, vars_list) = Self::decompose_polynomial(self, &z3_context);
        //
        let mut result = -1;
        let (verification_method, instance_cols_new, iterations) = user_inputs(&instance_cols);

        let t: HashMap<ast::Int, i64>;

        if (verification_method == 1) {
            t = instance_cols_new;
        } else if (verification_method == 2){
            t = instance_cols;
        }
        else {
            return result; 
        }

        let mut result = -1;

        //println!("{:?}{}{}{}{}",formulas,vars_list,t,verification_method)
        result = control_uniqueness(
            &z3_context,
            formulas,
            vars_list,
            &t,
            verification_method,
            iterations,
        );


        output_result(
            result,
            verification_method,
            iterations,
        );

        return result;
    }

    // pub fn analyze_underconstrained(&mut self) {
    //     let z3_config = z3::Config::new();
    //     let z3_context = z3::Context::new(&z3_config);
    //     let mut instance_cols: HashMap<ast::Int, i64> = HashMap::new();

    //     for cell in &self.layouter.eq_table {
    //         instance_cols.insert(ast::Int::new_const(&z3_context, format!("{}", cell.0)), 0);
    //     }

    //     let mut formula_conj: Vec<Option<z3::ast::Bool>> = vec![];
    //     let mut vars_list: HashSet<ast::Int> = Default::default();
    //     let zero = ast::Int::from_i64(&z3_context, 0);
    //     for gate in self.cs.gates.iter() {
    //         for poly in &gate.polys {
    //             let (formula, v) = Self::decompose_expression(&z3_context, poly);
    //             let v: HashSet<ast::Int> = HashSet::from_iter(v.iter().cloned());
    //             vars_list.extend(v);
    //             formula_conj.push(Some(formula.unwrap()._eq(&zero)));
    //         }
    //     }
    //     let v = Vec::from_iter(vars_list);
    //     test_count_models(&z3_context, formula_conj, v, instance_cols);
    // }

    fn log(&self) -> &[String] {
        &self.log
    }
}


fn control_uniqueness(
    ctx: &z3::Context,
    formulas: Vec<Option<z3::ast::Bool>>,
    vars_list: Vec<z3::ast::Int>, //,
    //instance_index: usize,
    instance_cols: &HashMap<ast::Int, i64>,
    verification_method: i64,
    iterations: u128,
) -> i8 {
    let mut result = 0;

    let solver = Solver::new(&ctx);
    for f in formulas.clone() {
        solver.assert(&f.unwrap().clone());
    }

    //*** adding non-negative constraint */
    for var in vars_list.iter() {
        let s1 = var.ge(&ast::Int::from_i64(&ctx, 0));
        solver.assert(&s1);
    }

    let mut count = 0;
    let mut count1 = 0;

    if verification_method == 1 {
        //*** Fixed Public Input */
        for var in instance_cols {
            println!("Here: {:?}", var);
            let s1 = var.0._eq(&ast::Int::from_i64(ctx, *var.1));
            solver.assert(&s1);
        }
    }
    println!("Solver {:?}", solver);
    while result == 0 {
        count += 1;
        if solver.check() == SatResult::Sat {
            count1 += 1;
            let model = solver.get_model().unwrap();
            //*** Create an equivalent local solver to check if it's under-constrained*/
            //*** adding the circuit constraints */
            let solver1 = Solver::new(&ctx);
            for f in formulas.clone() {
                solver1.assert(&f.unwrap().clone());
            }
            //*** adding non-negative constraint */
            for var in vars_list.iter() {
                let s1 = var.ge(&ast::Int::from_i64(&ctx, 0));
                solver1.assert(&s1);
            }

            if (verification_method == 1) {
                //*** Fixed Public Input */
                for var in instance_cols {
                    let s1 = var.0._eq(&ast::Int::from_i64(ctx, *var.1));
                    solver1.assert(&s1);
                }
            }

            let mut nvc10 = vec![];
            //*** Enforcing the solver to generate the same model by having the previous model values in check_assumptions */
            for var in vars_list.iter() {
                let v = model.eval(var, true).unwrap().as_i64().unwrap();
                let s1 = var._eq(&ast::Int::from_i64(ctx, v));
                nvc10.push(s1);
            }
            // for var in nvc10.iter() {
            //     nvcp10.push(var);
            // }
            solver1.check_assumptions(&nvc10);
            let model = solver1.get_model().unwrap();

            println!("Model {} to be checked:", count);
            println!("{:?}", model);

            let mut nvc_p1 = vec![];
            let mut nvc_p2 = vec![];
            let mut nvc1 = vec![];
            let mut nvc2 = vec![];
            //*** To check the model is under-constrained we need to:
            //      1. Fix the public input
            //      2. Change the other vars
            //      3. add these rules to the current solver and,
            //      4. find a model that satisfies these rules
            for i in 0..vars_list.len() {
                let var = &vars_list[i];
                // 1. Fix the public input
                if (instance_cols.contains_key(var) && verification_method != 1) {
                    //if (var.eq(&instance_col)) {
                    let v = model.eval(var, true).unwrap().as_i64().unwrap();
                    let s1 = var._eq(&ast::Int::from_i64(ctx, v));
                    nvc1.push(s1);
                } else {
                    // 2. Change the other vars
                    let v = model.eval(var, true).unwrap().as_i64().unwrap();
                    let s11 = !var._eq(&ast::Int::from_i64(ctx, v));
                    nvc2.push(s11);
                }
            }

            for var in nvc1.iter() {
                nvc_p1.push(var);
            }

            for var in nvc2.iter() {
                nvc_p2.push(var);
            }
            // 3. add these rules to the current solver,
            let or_of_others = z3::ast::Bool::or(&ctx, &nvc_p2);
            nvc_p1.push(&or_of_others);
            solver1.assert(&z3::ast::Bool::and(&ctx, &nvc_p1));

            //println!("solver1: {:?}", solver1);
            //      4. find a model that satisfies these rules
            solver1.check();

            if solver1.check() == SatResult::Sat {
                if (!solver1.get_model().is_none()) {
                    let model1 = solver1.get_model().unwrap();
                    println!("Equivalent model for the same public input:");
                    println!("{:?}", model1);
                }
                result = 1;
                break;
            }
            println!("There is no equivalent model with the  same public input to prove model {} is under-constrained!",count);

            // if no models found, add some rules to the initial solver to make sure does not generate the same model again

            let mut new_var_constraints = vec![];
            let mut new_var_constraints_p = vec![];

            for var in vars_list.iter() {
                let v = model.eval(var, true).unwrap().as_i64().unwrap();
                let s1 = !var._eq(&ast::Int::from_i64(ctx, v));
                new_var_constraints.push(s1);
            }
            for var in new_var_constraints.iter() {
                new_var_constraints_p.push(var);
            }
            solver.assert(&z3::ast::Bool::or(&ctx, &new_var_constraints_p));
        }
        //*** Checking one specific public input */
        if verification_method == 1 {
            break;
        }
        //*** Checking a random number of public inputs */
        if count >= iterations {
            //*** If there have not been any other possible models to be checked we can say that the ciruit is not under-constrained */
            if count > count1 {
                result = 2;
            }
            break;
        }
    }

    result
}
fn user_inputs<'a>(
    instance_cols: &HashMap<ast::Int<'a>, i64>,
) -> (i64, HashMap<ast::Int<'a>, i64>, u128) {
    println!("You can verify the circuit for a specific public input or a random number of public inputs:");
    println!("1. verify the circuit for a specific public input!");
    println!("2. Verify for a random number of public inputs!");

    let mut menu = String::new();

    io::stdin()
        .read_line(&mut menu)
        .expect("Failed to read line");
    let mut instance_cols_new: HashMap<ast::Int, i64> = HashMap::new();
    let mut iterations: u128 = 0;
    match menu.trim() {
        "1" => {
            let mut input_var = String::new();
            for mut _var in instance_cols.iter() {
                println!("Enter value for {} : ", _var.0);
                io::stdin()
                    .read_line(&mut input_var)
                    .expect("Failed to read line");
                instance_cols_new.insert(_var.0.clone(), input_var.trim().parse::<i64>().unwrap());
            }
        }
        "2" => {
            let mut input_var = String::new();
            println!("How many random public inputs you want to verify?");
            io::stdin()
                .read_line(&mut input_var)
                .expect("Failed to read line");

            iterations = input_var.trim().parse::<u128>().unwrap();
        }
        &_ => {}
    };

    let verification_method = menu.trim().parse::<i64>().unwrap();
    (verification_method, instance_cols_new, iterations)
}

fn output_result(
    result: i8,
    verification_method: i64,
    iterations: u128,
) {
    if verification_method == 1 {
        if result == 1 {
            println!("The circuit is under-constrained.");
        } else if result == 0 {
            println!("The circuit is not under-constrained for this specific input.");
        } else if result == 2 {
            println!("The circuit is not under-constrained!");
        }
    } else if verification_method == 2 {
        if result == 1 {
            println!("The circuit is under-constrained.");
        } else if result == 0 {
            if (iterations == 1) {
                println!(
                    "The circuit is not under-constrained for {} random input.",
                    iterations
                );
            } else {
                println!(
                    "The circuit is not under-constrained for {} random inputs.",
                    iterations
                );
            }
        } else if result == 2 {
            println!("The circuit is not under-constrained!");
        }
    }
}
