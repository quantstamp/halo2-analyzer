use std::marker::PhantomData;

use env_logger;

use halo2_proofs::pasta::group::ff::{PrimeField, PrimeFieldBits};
use log;

use halo2_proofs::arithmetic::Field;
use halo2_proofs::circuit::Value;
use halo2_proofs::dev::MockProver;
use halo2_proofs::pasta::Fp as Fr;
use halo2_proofs::poly::Rotation;
use halo2_proofs::{circuit::Layouter,circuit::SimpleFloorPlanner, plonk::*};

extern crate z3;

use z3::ast::{Ast, Bool};
use z3::*;

// public input x
// prove that I know its bit decomposition b0, b1
struct PlayCircuit<F> {
    _ph: PhantomData<F>,
    b0: F,
    b1: F,
    z3Config: z3::Config,
    z3Context: z3::Context,
}

#[derive(Clone)]
pub struct PlayCircuitConfig<F: Field> {
    _ph: PhantomData<F>,
    b0: Column<Advice>,
    b1: Column<Advice>,
    x: Column<Advice>,
    i: Column<Instance>,
    s: Selector,
}

impl<F: Field> PlayCircuit<F> {
    fn new(b0: F, b1: F) -> Self {
        let z3Config = z3::Config::new();
        let z3Context = z3::Context::new(&z3Config);
        PlayCircuit {
            _ph: PhantomData,
            b0,
            b1,
            z3Config,
            z3Context,
        }
    }
}

impl Default for PlayCircuit<Fr> {
    fn default() -> Self {
        let z3Config = z3::Config::new();
        let z3Context = z3::Context::new(&z3Config);
        PlayCircuit {
            _ph: PhantomData,
            b0: Fr::one(),
            b1: Fr::one(),
            z3Config,
            z3Context,
        }
    }
}

trait FMCheck {
    fn extract_constraints(z3Context: &z3::Context, cs: &ConstraintSystem<Fr>);
    fn decompose_expression<'a>(
        z3Context: &z3::Context,
        poly: &Expression<Fr>,
    ) -> Option<ast::Int<'a>>;
}

impl FMCheck for FMCheckFloorPlanner {
    fn extract_constraints(z3Context: &z3::Context, cs: &ConstraintSystem<Fr>) {
        //adding constraints
        // let cfg = Config::new();
        // let mut ctx = z3::Context::new(&cfg);
        for gate in &cs.gates {
            // println!("All polys in Gate {:?}",gate.polys);
            for poly in &gate.polys {
                // println!("Expression poly {:?}",poly);
                Self::decompose_expression(z3Context, &poly);
            }
        }
        println!("{:?}", z3Context);
    }
    fn decompose_expression<'a>(
        z3Context: &z3::Context,
        poly: &Expression<Fr>,
    ) -> Option<ast::Int<'a>> {
        //TODO: Fix life time error 
        match &poly {
            Expression::Constant(a) => {
                println!("constant {:?}", a);
                // Some(ast::Int::from_i64(
                //     &z3Context,
                //     i64::from(a.clone().to_repr()[0]),
                // ))
                unimplemented!();
            }
            Expression::Selector(a) => {
                println!("selector {:?}", a);
                unimplemented!();
                // Some(ast::Int::new_const(z3Context, format!("{:?}", a)))
            }
            Expression::Fixed { .. } => {
                println!("fixed {:?}", poly);
                unimplemented!("Implement this!");
            }
            Expression::Advice { .. } => {
                println!("advice {:?}", poly);
                // Some(ast::Int::new_const(z3Context, format!("{:?}", poly)))
                unimplemented!();
            }
            Expression::Instance { .. } => {
                println!("instance {:?}", poly);
                // Some(ast::Int::new_const(z3Context, format!("{:?}", poly)))
                unimplemented!();
            }
            Expression::Negated(_poly) => {
                println!("negated");
                println!("decomposing poly:");
                let a = Self::decompose_expression(z3Context, &_poly).unwrap();
                Some(a)
            }
            Expression::Sum(a, b) => {
                println!("sum {:?}, {:?}", a, b);
                println!("decomposing a:");
                let a_var = Self::decompose_expression(z3Context, a).unwrap();
                println!("decomposing b:");
                let b_var = Self::decompose_expression(z3Context, b).unwrap();
                let c_var = ast::Int::add(z3Context, &[&a_var, &b_var]);
                // Some(c_var)
                unimplemented!();
            }
            Expression::Product(a, b) => {
                println!("product {:?}, {:?}", a, b);
                println!("decomposing a:");
                let a_var = Self::decompose_expression(z3Context, a).unwrap();
                println!("decomposing b:");
                let b_var = Self::decompose_expression(z3Context, b).unwrap();
                let c_var = ast::Int::mul(z3Context, &[&a_var, &b_var]);
                // Some(c_var)
                unimplemented!();
            }
            Expression::Scaled(_poly, _) => {
                println!("scaled");
                let a = Self::decompose_expression(z3Context, &_poly);
                a
                //TODO: figure out WTF this does.
            }
        }
    }
}

struct FMCheckFloorPlanner;

impl FloorPlanner for FMCheckFloorPlanner {
    fn synthesize<F: Field, CS: Assignment<F>, C: Circuit<F>>(
        cs: &mut CS,
        circuit: &C,
        config: C::Config,
        constants: Vec<Column<Fixed>>,
    ) -> Result<(), Error> {
        // Do any fancy shit you want
        println!("Custom floor planner engaged!!");
        SimpleFloorPlanner::synthesize(cs, circuit, config, constants)
    }
}

impl Circuit<Fr> for PlayCircuit<Fr> {
    type Config = PlayCircuitConfig<Fr>;
    type FloorPlanner = FMCheckFloorPlanner;
    

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        let b0 = meta.advice_column();
        let b1 = meta.advice_column();
        let x = meta.advice_column();
        let i = meta.instance_column();
        let s = meta.selector();

        meta.enable_equality(x);
        meta.enable_equality(i);

        // def gates
        meta.create_gate("b0_binary_check", |meta| {
            let a = meta.query_advice(b0, Rotation::cur());
            let dummy = meta.query_selector(s);
            vec![dummy * a.clone() * (Expression::Constant(Fr::from(1)) - a.clone())]
            // a * (1-a)
        });
        meta.create_gate("b1_binary_check", |meta| {
            let a = meta.query_advice(b1, Rotation::cur());
            let dummy = meta.query_selector(s);
            vec![dummy * a.clone() * (Expression::Constant(Fr::from(1)) - a.clone())]
            // a * (1-a)
        });
        meta.create_gate("equality", |meta| {
            let a = meta.query_advice(b0, Rotation::cur());
            let b = meta.query_advice(b1, Rotation::cur());
            let c = meta.query_advice(x, Rotation::cur());
            let dummy = meta.query_selector(s);
            vec![dummy * (a + Expression::Constant(Fr::from(2)) * b - c)]
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
        mut layouter: impl Layouter<Fr>,
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
                        || Value::known(self.b0 + Fr::from(2) * self.b1),
                    )?;

                    Ok(out)
                },
            )
            .unwrap();

        // expose the public input
        layouter.constrain_instance(out.cell(), config.i, 0)?;

        Ok(())
    }
}

#[tokio::main]
async fn main() {
    env_logger::init();

    let circuit = PlayCircuit::<Fr>::new(Fr::from(1), Fr::from(1));

    let k = 5;

    let public_input = Fr::from(3);
    //mockprover verify passes
    log::debug!("running mock prover...");
    let prover = MockProver::<Fr>::run(k, &circuit, vec![vec![public_input]]).unwrap();

    prover.verify().expect("verify should work");
    log::debug!("verified via mock prover...");
}
