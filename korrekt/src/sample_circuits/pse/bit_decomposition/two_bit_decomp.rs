use group::ff::PrimeField;
use pse_halo2_proofs::circuit::*;
use pse_halo2_proofs::plonk::*;
use pse_halo2_proofs::poly::Rotation;
use std::marker::PhantomData;

/// `TwoBitDecompCircuit` is a circuit designed to perform binary decomposition
/// on a two-digit binary number.
///
/// The circuit takes two binary digits, `b0` and `b1`, and forms a two-bit binary number, denoted as x = b0 + 2*b1.
///
/// It uses custom gates to ensure the binarity of `b0` and `b1`, and to enforce the correct formation of the
/// combined binary number, `x`.
///
/// # Constraints
///
/// |   Row   |   b0    |   b1    |   x    |  i  |    s     |
/// |---------|---------|---------|--------|-----|----------|
/// |   0     |   b0    |   b1    |  x     |  i  |    1     |
///
/// Gate: b0_binary_check: s*b0*(1-b0)
/// Gate: b1_binary_check: s*b1*(1-b1)
/// Gate:        equality: s*(2*b1+b0-x)

pub struct TwoBitDecompCircuit<F: PrimeField> {
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

impl<F: PrimeField> Default for TwoBitDecompCircuit<F> {
    fn default() -> Self {
        TwoBitDecompCircuit {
            b0: F::ONE,
            b1: F::ONE,
        }
    }
}

impl<F: PrimeField> Circuit<F> for TwoBitDecompCircuit<F> {
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
            // b0 * (1-b0)
            vec![dummy * a.clone() * (Expression::Constant(F::ONE) - a)]
        });
        meta.create_gate("b1_binary_check", |meta| {
            let a = meta.query_advice(b1, Rotation::cur());
            let dummy = meta.query_selector(s);
            // b1 * (1-b1)
            vec![dummy * a.clone() * (Expression::Constant(F::ONE) - a)]
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

        Self::Config { b0, b1, x, i, s }
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
        layouter.constrain_instance(out.cell(), config.i, 0)?;
        Ok(())
    }
}
/// `TwoBitDecompCircuitUnderConstrained` is a version of the `TwoBitDecompCircuit` that underconstrains
/// the circuit for the sake of showcasing an example of an underconstrained circuit.
///
/// The circuit takes two binary digits, `b0` and `b1`, and forms a two-bit binary number, denoted as x = b0 + 2*b1.
///
/// It uses gates to ensure the binarity of `b0` and `b1`, and to enforce the correct formation of the
/// combined binary number, `x`. But the gate related to `b1` is missing. Which makes this cuircuit underconstrained.
///
/// # Constraints
///
/// |   Row   |   b0    |   b1    |   x    |  i  |    s     | Gate: b0_binary_check | Gate: b1_binary_check | Gate: equality |
/// |---------|---------|---------|--------|-----|----------|-----------------------|-----------------------|----------------|
/// |   0     |   b0    |   b1    |  x     |  i  |    1     |       s*b0*(1-b0)     |       s*b0*(1-b0)     |  s*(2*b1+b0-x) |
///

pub struct TwoBitDecompCircuitUnderConstrained<F: PrimeField> {
    b0: F,
    b1: F,
}

#[derive(Clone)]

pub struct TwoBitDecompCircuitUnderConstrainedConfig<F: PrimeField> {
    _ph: PhantomData<F>,
}

impl<F: PrimeField> Default for TwoBitDecompCircuitUnderConstrained<F> {
    fn default() -> Self {
        TwoBitDecompCircuitUnderConstrained {
            b0: F::ONE,
            b1: F::ONE,
        }
    }
}

impl<F: PrimeField> Circuit<F> for TwoBitDecompCircuitUnderConstrained<F> {
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
            // b0 * (1-b0)
            vec![dummy * a.clone() * (Expression::Constant(F::ONE) - a)]
        });
        meta.create_gate("b1_binary_check", |meta| {
            let a = meta.query_advice(b0, Rotation::cur());
            let dummy = meta.query_selector(s);
            // b1 * (1-b1)
            vec![dummy * a.clone() * (Expression::Constant(F::ONE) - a)]
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

        Self::Config { b0, b1, x, i, s }
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
        layouter.constrain_instance(out.cell(), config.i, 0)?;
        Ok(())
    }
}
