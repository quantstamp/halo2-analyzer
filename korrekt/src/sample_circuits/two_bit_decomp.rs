use std::marker::PhantomData;
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::plonk::{
    Advice, Circuit, Column, ConstraintSystem, Expression, Instance, Selector,
};
use halo2_proofs::circuit::{Layouter, Value, SimpleFloorPlanner};
use halo2_proofs::plonk::Error;
use halo2_proofs::poly::Rotation;

pub struct TwoBitDecompCircuit<F: FieldExt> {
    b0: F,
    b1: F,
}

#[derive(Clone)]
pub struct TwoBitDecompCircuitConfig {
    b0: Column<Advice>,
    b1: Column<Advice>,
    x: Column<Advice>,
    i: Column<Instance>,
    s: Selector,
}

impl<F: FieldExt> TwoBitDecompCircuit<F> {
    pub fn new(b0: F, b1: F) -> Self {
        TwoBitDecompCircuit {
            b0,
            b1,
        }
    }
}

impl<F: FieldExt> Default for TwoBitDecompCircuit<F> {
    fn default() -> Self {
        TwoBitDecompCircuit {
            b0: F::one(),
            b1: F::one(),
        }
    }
}

impl<F: FieldExt> Circuit<F> for TwoBitDecompCircuit<F> {
    type Config = TwoBitDecompCircuitConfig;
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

        // define gates
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
            // For example, if we change the constraint to the following, then the circuit is underconstraint,
            // because we have two models with the same public input (i=1, b0=1, b1=0, x=1) and (i=1, b0=0, b1=1, x=1)
            // vec![dummy * (a + b - c)]
            vec![dummy * (a + Expression::Constant(F::from(2)) * b - c)]
        });

        let cfg = Self::Config {
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
        // Is this line just making sure the output "x" (which is private) is same as the instance (public input)?
        // For example, given public input i=3, we want b0 = 1, b1 = 1, x = 3, and make sure x
        layouter.constrain_instance(out.cell(), config.i, 0)?; //*** what is this? */
        Ok(())
    }
}

pub struct TwoBitDecompCircuitUnderConstrained<F: FieldExt> {
    b0: F,
    b1: F,
}

#[derive(Clone)]
pub struct TwoBitDecompCircuitUnderConstrainedConfig<F: FieldExt> {
    _ph: PhantomData<F>,
    // b0: Column<Advice>,
    // b1: Column<Advice>,
    // x: Column<Advice>,
    // i: Column<Instance>,
    // s: Selector,
}

impl<F: FieldExt> TwoBitDecompCircuitUnderConstrained<F> {
    pub fn new(b0: F, b1: F) -> Self {
        TwoBitDecompCircuitUnderConstrained {
            b0,
            b1,
        }
    }
}

impl<F: FieldExt> Default for TwoBitDecompCircuitUnderConstrained<F> {
    fn default() -> Self {
        TwoBitDecompCircuitUnderConstrained {
            b0: F::one(),
            b1: F::one(),
        }
    }
}

impl<F: FieldExt> Circuit<F> for TwoBitDecompCircuitUnderConstrained<F> {
    type Config = TwoBitDecompCircuitConfig;
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

        // define gates
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
            // For example, if we change the constraint to the following, then the circuit is underconstraint,
            // because we have two models with the same public input (i=1, b0=1, b1=0, x=1) and (i=1, b0=0, b1=1, x=1)
            // vec![dummy * (a + b - c)]
            vec![dummy * (a + Expression::Constant(F::from(2)) * b - c)]
        });

        let cfg = Self::Config {
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
        // Is this line just making sure the output "x" (which is private) is same as the instance (public input)?
        // For example, given public input i=3, we want b0 = 1, b1 = 1, x = 3, and make sure x
        layouter.constrain_instance(out.cell(), config.i, 0)?; //*** what is this? */
        Ok(())
    }
}
