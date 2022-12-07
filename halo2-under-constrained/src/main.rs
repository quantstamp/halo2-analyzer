use std::marker::PhantomData;

use env_logger;

use log;

use halo2_proofs::{circuit::Layouter, circuit::SimpleFloorPlanner, plonk::*};
use halo2_proofs::dev::MockProver;
use halo2_proofs::arithmetic::Field;
use halo2_proofs::pasta::{Fp as Fr};
use halo2_proofs::circuit::Value;
use halo2_proofs::poly::Rotation;

// public input x
// prove that I know its bit decomposition b0, b1
struct PlayCircuit<F> {
    _ph: PhantomData<F>,
    b0: F,
    b1: F,
}

#[derive(Clone)]
pub struct PlayCircuitConfig<F: Field> {
    _ph: PhantomData<F>,
    b0: Column<Advice>,
    b1: Column<Advice>,
    x: Column<Advice>,
    i: Column<Instance>,
    s: Selector
}

impl <F: Field> PlayCircuit<F> {
    fn new(b0: F, b1: F) -> Self {
        PlayCircuit {
            _ph: PhantomData,
            b0,
            b1, 
        }
    }
}

impl Default for PlayCircuit<Fr> {
    fn default() -> Self {
        PlayCircuit{
            _ph: PhantomData,
            b0: Fr::one(),
            b1: Fr::one(),
        }
    }
}

impl Circuit<Fr> for PlayCircuit<Fr> {
    type Config = PlayCircuitConfig<Fr>;
    type FloorPlanner = SimpleFloorPlanner;

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
            vec![dummy*a.clone()*(Expression::Constant(Fr::from(1))-a.clone())] // a * (1-a)
        });
        meta.create_gate("b1_binary_check", |meta| {
            let a = meta.query_advice(b1, Rotation::cur());
            let dummy = meta.query_selector(s);
            vec![dummy*a.clone()*(Expression::Constant(Fr::from(1))-a.clone())] // a * (1-a)
        });
        meta.create_gate("equality", |meta| {
            let a = meta.query_advice(b0, Rotation::cur());
            let b = meta.query_advice(b1, Rotation::cur());
            let c = meta.query_advice(x, Rotation::cur());
            let dummy = meta.query_selector(s);
            vec![dummy*(a+Expression::Constant(Fr::from(2))*b-c)]
        });

        Self::Config {
            _ph: PhantomData,
            b0,
            b1,
            x,
            i, 
            s
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), Error> {

        let out = layouter.assign_region(
            || "The Region",
            |mut region| {
                config.s.enable(&mut region, 0)?;

                region.assign_advice(
                    || "b0",
                    config.b0,
                    0,
                    || Value::known(self.b0),
                )?;

                region.assign_advice(
                    || "b1",
                    config.b1,
                    0,
                    || Value::known(self.b1),
                )?;

                let out = region.assign_advice(
                    || "x",
                    config.x,
                    0,
                    || Value::known(self.b0+Fr::from(2)*self.b1),
                )?;

                Ok(out)
            }
        ).unwrap();

        // expose the public input
        layouter.constrain_instance(out.cell(), config.i, 0)?;

        Ok(())
    }
}


#[tokio::main]
async fn main() {
    env_logger::init();

    let circuit = PlayCircuit::<Fr>::new(Fr::from(3), Fr::from(1));

    let k = 5;

    let public_input = Fr::from(3);
    //mockprover verify passes
    log::debug!("running mock prover...");
    let prover = MockProver::<Fr>::run(k, &circuit, vec![vec![public_input]]).unwrap();
    
    prover.verify().expect("verify should work");
    log::debug!("verified via mock prover...");
}