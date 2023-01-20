use std::collections::HashSet;
use std::fmt::format;
use std::marker::PhantomData;

use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::circuit::{Layouter, Value};
use halo2_proofs::pasta::Fp;
use halo2_proofs::plonk::Error;
use halo2_proofs::plonk::{
    Advice, Circuit, Column, ConstraintSystem, Expression, Instance, Selector,
};
use halo2_proofs::poly::{Rotation};

use halo2_proofs::circuit::layouter::RegionColumn;
use halo2_proofs::circuit::SimpleFloorPlanner;

mod abstract_expr;
mod layouter;
mod shape;

use layouter::AnalyticLayouter;
use z3::ast::Ast;
use z3::{ast, Config, Context, SatResult, Solver};

use crate::abstract_expr::AbsResult;

struct PlayCircuit<F: FieldExt> {
    _ph: PhantomData<F>,
    b0: F,
    b1: F,
}

#[derive(Clone)]
pub struct PlayCircuitConfig<F: FieldExt> {
    _ph: PhantomData<F>,
    // s_mul: Selector,
    // s_add: Selector,
    // columns: [Column<Advice>; 25],
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
        //meta.enable_equality(i);

        // def gates
        meta.create_gate("b0_binary_check", |meta| {
            let a = meta.query_advice(b0, Rotation::cur());
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

        // expose the public input
        layouter.constrain_instance(out.cell(), config.i, 0)?; //*** what is this? */
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
        z3Context: &'a z3::Context,
        poly: &Expression<F>,
    ) -> (Option<ast::Int<'a>>,Vec<ast::Int<'a>>);
}

impl<'a, F: FieldExt> FMCheck<'a, F> for Analyzer<F> {
    fn decompose_expression(
        z3_context: &'a z3::Context,
        poly: &Expression<F>,
    ) -> (Option<ast::Int<'a>>,Vec<ast::Int<'a>>) {
        match &poly {
            Expression::Constant(a) => {
                let result = Some(ast::Int::from_i64(
                    z3_context,
                    i64::from(a.get_lower_32()), //*** Ask Them */
                ));

                (result,vec![])
            }
            Expression::Selector(a) => {
                //unimplemented!();
                let result = Some(ast::Int::new_const(z3_context, format!("{:?}", &a)));
                let v = [ast::Int::new_const(z3_context, format!("{:?}", &a))];
                (result,v.to_vec())
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
                let n = format!("Advic-{}-{}-{:?}",*query_index,*column_index,*rotation);
                let m = format!("Advic-{}-{}-{:?}",*query_index,*column_index,*rotation);
                let result = Some(ast::Int::new_const(z3_context, n));
                let v = [ast::Int::new_const(z3_context, m)];
                (result,v.to_vec())
            },
            Expression::Advice {
                query_index,
                column_index,
                rotation,
            } => {
                let n = format!("Advic-{}-{}-{:?}",*query_index,*column_index,*rotation);
                let m = format!("Advic-{}-{}-{:?}",*query_index,*column_index,*rotation);
                let result = Some(ast::Int::new_const(z3_context, n));
                let v = [ast::Int::new_const(z3_context, m)];
                (result,v.to_vec())
            }
            Expression::Instance {
                query_index,
                column_index,
                rotation,
            } => {
                let n = format!("Advic-{}-{}-{:?}",*query_index,*column_index,*rotation);
                let m = format!("Advic-{}-{}-{:?}",*query_index,*column_index,*rotation);
                let result = Some(ast::Int::new_const(z3_context, n));
                let v = [ast::Int::new_const(z3_context, m)];
                (result,v.to_vec())
                // unimplemented!();
            }
            Expression::Negated(_poly) => {
                let (result,v) = Self::decompose_expression(z3_context, &_poly);
                (Some(result).unwrap(),v)
            }
            Expression::Sum(a, b) => {
                let (a_var,mut a_v) = Self::decompose_expression(z3_context, a);
                let (b_var,mut b_v) = Self::decompose_expression(z3_context, b);
                let result = Some(ast::Int::add(z3_context, &[&a_var.unwrap(), &b_var.unwrap()]));
                a_v.append(&mut b_v);
                (result,a_v)
            }
            Expression::Product(a, b) => {
                let (a_var,mut a_v) = Self::decompose_expression(z3_context, a);
                let (b_var,mut b_v) = Self::decompose_expression(z3_context, b);
                let result = Some(ast::Int::mul(z3_context, &[&a_var.unwrap(), &b_var.unwrap()]));
                a_v.append(&mut b_v);
                (result,a_v)
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
    fn new<C: Circuit<F> + Default>() -> Self {
        Self::new_with(&C::default())
    }

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
            'region_search : for region in self.layouter.regions.iter() { 
                let selectors = HashSet::from_iter(region.selectors().into_iter());
                for poly in gate.polynomials() {
                    let res = abstract_expr::eval_abstract(poly, &selectors);
                    if res != AbsResult::Zero {
                        used = true;
                        break 'region_search
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
                                
                                if eval != AbsResult::Zero && advices.contains(&(column.into(), rotation)) {
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
        let z3Config = z3::Config::new();
        let z3Context = z3::Context::new(&z3Config);
        let mut formula_conj: Vec<Option<z3::ast::Bool>>=vec![];
        let vars_list: Vec<ast::Int<>> = vec![];
        let zero = ast::Int::from_i64(&z3Context, 0);
        for gate in self.cs.gates.iter() {
            for poly in &gate.polys {
                
                // let vars_list: Vec<z3::ast::Int> = [].to_vec();
                let (formula,vars_list) = Self::decompose_expression(&z3Context, poly);
                formula_conj.push(Some(formula.unwrap()._eq(&zero)));
           }
        }
        let mut formula_n: ast::Bool;// = Some(ast::Bool::from_bool(&z3Context, true));
        testCountModels(&z3Context,formula_conj,vars_list);

    }

    fn log(&self) -> &[String] {
        &self.log
    }
}

fn main() {
    let mut analyzer = Analyzer::new::<PlayCircuit<Fp>>();
    //let z3Config = z3::Config::new();
    //let z3Context = z3::Context::new(&z3Config);

    // println!("{:#?}", analyzer);
    analyzer.analyze_unused_columns();
    analyzer.analyze_unsed_custom_gates();
    analyzer.analyze_unconstrained_cells();
    analyzer.analyze_underconstrained();
    //testCountModels(&z3Context);
    //testCountModels1();
}

fn testCountModels(ctx: &z3::Context, formulas: Vec<Option<z3::ast::Bool>>, varsList: Vec<z3::ast::Int>) {
    let solver = Solver::new(&ctx);

    //    h*(a+b)+(1-h)(a*b) - o  = 0

    // solver.assert(&x.gt(&y)); // old; for reference

    let zero = ast::Int::from_i64(&ctx, 0);

    let finalCount = countModels(&ctx, formulas, varsList);
    println!("Final count: {}", finalCount);
}

fn countModels(ctx: &z3::Context, formulas: Vec<Option<z3::ast::Bool>>, varsList: Vec<z3::ast::Int>) -> i32 {
    let mut count = 0;

    let solver = Solver::new(&ctx);
    for f in formulas.clone(){
        solver.assert(&f.unwrap().clone());
    }
    
    println!("Going to check... {:?}", &formulas);

    loop {
        if count > 1 {
            break;
        }

        if solver.check() != SatResult::Sat {
            break;
        }

        assert_eq!(solver.check(), SatResult::Sat);
        println!("Result is SAT");
        let model = solver.get_model().unwrap();
        println!("model: \n{}", model);
        println!("model end");

        // testing only; not needed due to previous line in production?
        for var in varsList.iter() {
            println!("varsList");
            let v = model.eval(var, true).unwrap().as_i64().unwrap();
            println!("{} -> {}", var, v);
        }

        let mut newVarConstraints = vec![];
        let mut newVarConstraintsP = vec![];

        for var in varsList.iter() {
            let v = model.eval(var, true).unwrap().as_i64().unwrap();
            let s1 = var.gt(&ast::Int::from_i64(ctx, v));
            let s2 = var.lt(&ast::Int::from_i64(ctx, v));
            newVarConstraints.push(s1);
            newVarConstraints.push(s2);
        }
        for var in newVarConstraints.iter() {
            newVarConstraintsP.push(var);
        }

        solver.assert(&z3::ast::Bool::or(&ctx, &newVarConstraintsP));

        count = count + 1;
    }

    count
}
fn testCountModels1() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let a = ast::Int::new_const(&ctx, "a");
    let b = ast::Int::new_const(&ctx, "b");
    let h = ast::Int::new_const(&ctx, "h");
    let o = ast::Int::new_const(&ctx, "o");
    let zero = ast::Int::from_i64(&ctx, 0);
    let one = ast::Int::from_i64(&ctx, 1);

    let solver = Solver::new(&ctx);

    //    h*(a+b)+(1-h)(a*b) - o  = 0

    // solver.assert(&x.gt(&y)); // old; for reference

    let firstTerm = ast::Int::mul(&ctx, &[&h, &ast::Int::add(&ctx, &[&a, &b])]);
    let secondTerm = ast::Int::mul(
        &ctx,
        &[
            &ast::Int::sub(&ctx, &[&one, &h]),
            &ast::Int::add(&ctx, &[&a, &b]),
        ],
    );
    let formulaSum = ast::Int::add(&ctx, &[&firstTerm, &secondTerm]);
    let formula = ast::Int::sub(&ctx, &[&formulaSum, &o]);
    let finalCount = countModels1(&ctx, formula._eq(&zero), vec![a, b, h, o]);
    println!("Final count: {}", finalCount);
}

fn countModels1(ctx: &z3::Context, formula: z3::ast::Bool, varsList: Vec<z3::ast::Int>) -> i32 {
    let mut count = 0;

    let solver = Solver::new(&ctx);

    solver.assert(&formula);
    println!("Going to check... {}", &formula);

    loop {
        if count > 1 {
            break;
        }

        if solver.check() != SatResult::Sat {
            break;
        }

        assert_eq!(solver.check(), SatResult::Sat);
        println!("Result is SAT");
        let model = solver.get_model().unwrap();
        println!("model: {:?}", model);
        println!("model end");
        count = 2;
        // testing only; not needed due to previous line in production?
        //  for var in varsList.iter() {
        //      let v = model.eval(var, true).unwrap().as_i64().unwrap();
        //      println!("{} -> {}", var, v);
        //  }

        //  let mut newVarConstraints = vec![];
        //  let mut newVarConstraintsP = vec![];

        //  for var in varsList.iter() {
        //     let v = model.eval(var, true).unwrap().as_i64().unwrap();
        //     let s1 = var.gt( &ast::Int::from_i64(ctx, v));
        //     let s2 = var.lt( &ast::Int::from_i64(ctx, v));
        //     newVarConstraints.push(s1);
        //     newVarConstraints.push(s2);
        //  }
        //  for var in newVarConstraints.iter() {
        //      newVarConstraintsP.push(var);
        //  }

        //  solver.assert(&z3::ast::Bool::or(&ctx, &newVarConstraintsP));

        //  count = count + 1;
    }

    count
}
