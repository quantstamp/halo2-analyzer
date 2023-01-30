use std::collections::HashSet;
use std::marker::PhantomData;
use std::ops::Neg;

use halo2_proofs::dev::MockProver;
use halo2_proofs::pasta::Fp as Fr;

use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::circuit::{Layouter, Value};
use halo2_proofs::plonk::Error;
use halo2_proofs::plonk::{
    Advice, Circuit, Column, ConstraintSystem, Expression, Instance, Selector,
};
use halo2_proofs::poly::Rotation;

use halo2_proofs::circuit::layouter::RegionColumn;
use halo2_proofs::circuit::SimpleFloorPlanner;

mod abstract_expr;
mod layouter;
mod shape;

use layouter::AnalyticLayouter;
use z3::ast::Ast;
use z3::{ast, SatResult, Solver};

use crate::abstract_expr::AbsResult;

use log;


struct PlayCircuit<F: FieldExt> {
    _ph: PhantomData<F>,
    b0: F,
    b1: F,
}

#[derive(Clone)]
pub struct PlayCircuitConfig<F: FieldExt> {
    _ph: PhantomData<F>,
    b0: Column<Advice>,
    b1: Column<Advice>,
    x: Column<Advice>,
    i: Column<Instance>,
    s: Selector,
}

impl<F: FieldExt> PlayCircuit<F> {
    fn new(b0: F, b1: F) -> Self {
        PlayCircuit {
            _ph: PhantomData,
            b0,
            b1,
        }
    }
}

impl<F: FieldExt> Default for PlayCircuit<F> {
    fn default() -> Self {
        PlayCircuit {
            _ph: PhantomData,
            b0: F::one(),
            b1: F::one(),
        }
    }
}

impl<F: FieldExt> Circuit<F> for PlayCircuit<F> {
    type Config = PlayCircuitConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let b0 = meta.advice_column();
        let b1 = meta.advice_column();
        let x = meta.advice_column();
        let i = meta.instance_column();
        let s = meta.selector();

        meta.enable_equality(x);
        meta.enable_equality(i);

        // def gates
        meta.create_gate("b0_binary_check", |meta| {
            let a = meta.query_advice(b1, Rotation::cur());
            let dummy = meta.query_selector(s);
            vec![dummy * a.clone() * (Expression::Constant(F::from(1)) - a.clone())]
            // b0 * (1-b0)
        });
        meta.create_gate("b1_binary_check", |meta| {
            let a = meta.query_advice(b1, Rotation::cur());
            let dummy = meta.query_selector(s);
            vec![dummy * a.clone() * (Expression::Constant(F::from(1)) - a.clone())]
            // b1 * (1-b1)
        });
        meta.create_gate("equality", |meta| {
            let a = meta.query_advice(b0, Rotation::cur());
            let b = meta.query_advice(b1, Rotation::cur());
            let c = meta.query_advice(x, Rotation::cur());
            let dummy = meta.query_selector(s);
            vec![dummy * (a + Expression::Constant(F::from(2)) * b - c)]
        });

        let cfg = Self::Config {
            _ph: PhantomData,
            b0,
            b1,
            x,
            i,
            s,
        };

        cfg
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let out = layouter
            .assign_region(
                || "The Region",
                |mut region| {
                    config.s.enable(&mut region, 0)?;

                    region.assign_advice(|| "b0", config.b0, 0, || Value::known(self.b0))?;

                    region.assign_advice(|| "b1", config.b1, 0, || Value::known(self.b1))?;

                    let out = region.assign_advice(
                        || "x",
                        config.x,
                        0,
                        || Value::known(self.b0 + F::from(2) * self.b1),
                    )?;

                    Ok(out)
                },
            )
            .unwrap();
        // println!("out");
        // println!("{:?}",out);
        // expose the public input
        layouter.constrain_instance(out.cell(), config.i, 0)?; //*** what is this? */
        Ok(())
    }
}

struct MultiPlayCircuit<F: FieldExt> {
    _ph: PhantomData<F>,
    b0: F,
    b1: F,
}

#[derive(Clone)]
pub struct MultiPlayCircuitConfig<F: FieldExt> {
    _ph: PhantomData<F>,
    advice: Column<Advice>,
    instance: Column<Instance>,
    s: Selector,
}

impl<F: FieldExt> MultiPlayCircuit<F> {
    fn new(b0: F, b1: F) -> Self {
        MultiPlayCircuit {
            _ph: PhantomData,
            b0,
            b1,
        }
    }
}

impl<F: FieldExt> Default for MultiPlayCircuit<F> {
    fn default() -> Self {
        MultiPlayCircuit {
            _ph: PhantomData,
            b0: F::one(),
            b1: F::one(),
        }
    }
}

impl<F: FieldExt> Circuit<F> for MultiPlayCircuit<F> {
    type Config = MultiPlayCircuitConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let x = meta.advice_column();
        let i = meta.instance_column();
        let s = meta.selector();

        meta.enable_equality(x);
        meta.enable_equality(i);

        // def gates
        meta.create_gate("b0_binary_check", |meta| {
            let a = meta.query_advice(x, Rotation::cur());
            let dummy = meta.query_selector(s);
            vec![dummy * a.clone() * (Expression::Constant(F::from(1)) - a.clone())]
            // b0 * (1-b0)
        });
        meta.create_gate("b1_binary_check", |meta| {
            let a = meta.query_advice(x, Rotation::next());
            let dummy = meta.query_selector(s);
            vec![dummy * a.clone() * (Expression::Constant(F::from(1)) - a.clone())]
            // b1 * (1-b1)
        });
        meta.create_gate("equality", |meta| {
            let a = meta.query_advice(x, Rotation::cur());
            let b = meta.query_advice(x, Rotation::next());
            let c = meta.query_advice(x, Rotation(2));
            let dummy = meta.query_selector(s);
            vec![dummy * (a + Expression::Constant(F::from(2)) * b - c)]
        });

        let cfg = Self::Config {
            _ph: PhantomData,
            advice:x,
            instance:i,
            s,
        };

        cfg
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let out = layouter
            .assign_region(
                || "The Region",
                |mut region| {
                    config.s.enable(&mut region, 0)?;

                    region.assign_advice(|| "b0", config.advice, 0, || Value::known(self.b0))?;

                    region.assign_advice(|| "b1", config.advice, 1, || Value::known(self.b1))?;

                    let out = region.assign_advice(
                        || "x",
                        config.advice,
                        2,
                        || Value::known(self.b0 + F::from(2) * self.b1),
                    )?;

                    Ok(out)
                },
            )
            .unwrap();
            // println!("out");
            // println!("{:?}",out);
        // expose the public input
        layouter.constrain_instance(out.cell(), config.instance, 0)?; //*** what is this? */
        Ok(())
    }
}


#[derive(Debug)]
struct Analyzer<F: FieldExt> {
    cs: ConstraintSystem<F>,
    layouter: AnalyticLayouter<F>,
    log: Vec<String>,
}
trait FMCheck<'a, F: FieldExt> {
    fn decompose_expression(
        z3_context: &'a z3::Context,
        poly: &Expression<F>,
    ) -> (Option<ast::Int<'a>>, Vec<ast::Int<'a>>);
}

impl<'a, F: FieldExt> FMCheck<'a, F> for Analyzer<F> {
    fn decompose_expression(
        z3_context: &'a z3::Context,
        poly: &Expression<F>,
    ) -> (Option<ast::Int<'a>>, Vec<ast::Int<'a>>) {
        match &poly {
            Expression::Constant(a) => {
                let result = Some(ast::Int::from_i64(
                    z3_context,
                    i64::from(a.get_lower_32()), //*** Ask Them */
                ));

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
                let n = format!("Fixed-{}-{}-{:?}", *query_index, *column_index, *rotation);
                let m = format!("Fixed-{}-{}-{:?}", *query_index, *column_index, *rotation);
                let result = Some(ast::Int::new_const(z3_context, n));
                let v = [ast::Int::new_const(z3_context, m)];
                (result, v.to_vec())
            }
            Expression::Advice {
                query_index,
                column_index,
                rotation,
            } => {
                let n = format!("A-{}-{:?}", *column_index,*rotation); //("Advice-{}-{}-{:?}", *query_index, *column_index, *rotation);
                let m = format!("A-{}-{:?}", *column_index,*rotation); //format!("Advice-{}-{}-{:?}", *query_index, *column_index, *rotation);
                let result = Some(ast::Int::new_const(z3_context, n));
                let v = [ast::Int::new_const(z3_context, m)];
                (result, v.to_vec())
            }
            Expression::Instance {
                query_index,
                column_index,
                rotation,
            } => {
                let n = format!(
                    "Instance-{}-{}-{:?}",
                    *query_index, *column_index, *rotation
                );
                let m = format!(
                    "Instance-{}-{}-{:?}",
                    *query_index, *column_index, *rotation
                );
                let result = Some(ast::Int::new_const(z3_context, n));
                let v = [ast::Int::new_const(z3_context, m)];
                (result, v.to_vec())
                // unimplemented!();
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
            Expression::Scaled(_poly, _) => {
                let result = Self::decompose_expression(z3_context, &_poly);
                result
                //TODO: figure out ... this does.
            }
        }
    }
}

impl<F: FieldExt> Analyzer<F> {
    // fn new<C: Circuit<F> + Default>() -> Self {
    //     Self::new_with(&C::default())
    // }

    fn new_with<C: Circuit<F>>(circuit: &C) -> Self {
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
    fn analyze_unsed_custom_gates(&mut self) {
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
    fn analyze_unused_columns(&mut self) {
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
    fn analyze_unconstrained_cells(&mut self) {
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

    fn analyze_underconstrained(&mut self) {
        let z3_config = z3::Config::new();
        let z3_context = z3::Context::new(&z3_config);
        let mut instance_cols_vec = vec![];
        //println!("{:?}",self.cs);
        //let v = [ast::Int::new_const(&z3_context, m)];

        for col in self.cs.permutation.columns.iter() {
            let c_type = format!("{:?}", col.column_type());
            if c_type == "Advice" {
                instance_cols_vec.push(ast::Int::new_const(
                    &z3_context,
                    format!("A{}-Rotation(0)", col.index()),
                ));
            }
        }

        let mut instance_cols = HashSet::from_iter(instance_cols_vec.iter().cloned());

        //let instance_col = ast::Int::new_const(&z3_context, "A2");

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
        test_count_models(&z3_context, formula_conj, v, instance_cols);
    }

    fn log(&self) -> &[String] {
        &self.log
    }
}

fn main() {
    println!("----------------------Circuit----------------------");
    let circuit = PlayCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
    let mut analyzer = Analyzer::new_with(&circuit);
    let k = 5;

    let public_input = Fr::from(3);
    //mockprover verify passes
    let prover = MockProver::<Fr>::run(k, &circuit, vec![vec![public_input]]);
    analyzer.analyze_underconstrained();

    println!("----------------------Multi Circuit----------------------");
    let multi_circuit = MultiPlayCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
    let mut analyzer1 = Analyzer::new_with(&multi_circuit);

    let k = 5;

    let public_input1 = Fr::from(3);
    log::debug!("running mock prover...");
    let prover1 = MockProver::<Fr>::run(k, &multi_circuit, vec![vec![public_input1]]).unwrap();

    prover1.verify().expect("verify should work");
    log::debug!("verified via mock prover...");

    
    analyzer1.analyze_underconstrained();
}

fn test_count_models(
    ctx: &z3::Context,
    formulas: Vec<Option<z3::ast::Bool>>,
    vars_list: Vec<z3::ast::Int>,
    instance_cols: HashSet<ast::Int>,
) {
    println!("instance:");
    println!("{:?}",instance_cols);
    let result = control_uniqueness(&ctx, formulas, vars_list, instance_cols);
    if (!result) {
        println!("The circuit is underConstrained");
    } else {
        println!("The circuit is NOT underConstrained");
    }
}
fn control_uniqueness(
    ctx: &z3::Context,
    formulas: Vec<Option<z3::ast::Bool>>,
    vars_list: Vec<z3::ast::Int>, //,
    //instance_index: usize,
    instance_cols: HashSet<ast::Int>,
) -> bool {
    let mut result = true;

    let solver = Solver::new(&ctx);
    for f in formulas.clone() {
        solver.assert(&f.unwrap().clone());
    }
    println!("solver:");
    println!("{:?}",solver);


    let mut count = 0;
    //* This loop iterates over all the possible,nonrepeated models, it may stop when:
    //       - there is no more new model, or the underconstrained 
    //       - there is a model which prooves the circuit is undercnstrained   
    // it may not stop if there are unlimited models that satisfy the slver and none of them satisfies the underconstrained reqs.
    // (one of the tasks would be finding a solution for this, right now the while is hardcoded to break after 10000 iterations!)
    // */
    while solver.check() == SatResult::Sat {
        count += 1;

        let model = solver.get_model().unwrap();
        //*** Create an equivalent local solver to check if it's underconstrained*/
        //*** adding the circuit constraints */
        let solver1 = Solver::new(&ctx);
        for f in formulas.clone() {
            solver1.assert(&f.unwrap().clone());
        }
        let mut nvc10 = vec![];
        //let mut nvcp10 = vec![];
        //*** Enforcing the solver to generate the same model by having the prev model values in check_assumptions */
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

        println!("Model to be checked:");
        println!("{:?}", model);

        let mut i = 0;
        let mut nvc_p1 = vec![];
        let mut nvc_p2 = vec![];
        let mut nvc1 = vec![];
        let mut nvc2 = vec![];
        //*** To check the model is underconstrained we need to:
        //      1. Fix the instance related
        //      2. Change the other vars
        //      3. add these rules to the current solver and,
        //      4. find a model that satisfies these rules
        for i in 0..vars_list.len() {
            let var = &vars_list[i];
            // 1. Fix the instance related
            if (instance_cols.contains(var)) {
                //if (var.eq(&instance_col)) {
                let v = model.eval(var, true).unwrap().as_i64().unwrap();
                let s1 = var._eq(&ast::Int::from_i64(ctx, v));
                nvc1.push(s1);
            } else {// 2. Change the other vars
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
        // 3. add these rules to the current solver and,
        let or_of_others = z3::ast::Bool::or(&ctx, &nvc_p2);
        nvc_p1.push(&or_of_others);
        solver1.assert(&z3::ast::Bool::and(&ctx, &nvc_p1));

        //      4. find a model that satisfies these rules
        solver1.check();

        // if (!solver1.get_model().is_none()) {
        //     let model1 = solver1.get_model().unwrap();
        //     println!("New Model: {:?}", model1);
        // }

        if solver1.check() == SatResult::Sat {
            if (!solver1.get_model().is_none()) {
                let model1 = solver1.get_model().unwrap();
                println!("equivalent model with same instance column:");
                println!("{:?}", model1);
            }
            result = false;
            break;
        }
        // if no models found, add some rules to the initial solver to make sure does not generate the same model again
        println!("Model:");
        println!("{:?}", model);
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

        println!("count: {}", count);
        if (!result || count > 10000) {
            break;
        }
    }
    result
}
