#[cfg(feature = "use_pse_halo2_proofs")]
use group::ff::{Field, PrimeField};
#[cfg(feature = "use_pse_halo2_proofs")]
use pse_halo2_proofs::circuit::*;
#[cfg(feature = "use_pse_halo2_proofs")]
use pse_halo2_proofs::plonk::*;
#[cfg(feature = "use_pse_halo2_proofs")]
use pse_halo2_proofs::poly::Rotation;
use std::marker::PhantomData;

// `MultiRowTwoBitDecompCircuit`: This circuit is designed to perform binary decomposition
// on a two-digit binary number. It receives two field elements, `b0` and `b1`, which
// are intended to be binary digits. These digits are then used to form a two-bit binary
// number. The circuit implements custom gates to ensure the binarity of `b0` and `b1`, 
// and to enforce the correct formation of the combined binary number.
// This implematation uses one advice column which implies access to multiple rows in the table.
/// |   Row   | advice  |instance|    s     |      
/// |---------|---------|--------|----------| 
/// |   0     |   b0    |  x     |    1     | 
/// |   1     |   b1    |        |          |
/// |   2     |   x     |        |          |
/// 
///    Gate: b0_binary_check:  s*b0*(1-b0) 
///    Gate: b0_binary_check:  s*b1*(1-b1)
///    Gate:        equality:  s*(b0+2*b1-x)

#[cfg(feature = "use_pse_halo2_proofs")]
pub struct MultiRowTwoBitDecompCircuit<F: PrimeField> {
    b0: F,
    b1: F,
}

#[derive(Clone)]
#[cfg(feature = "use_pse_halo2_proofs")]
pub struct MultiRowTwoBitDecompCircuitConfig<F: PrimeField> {
    _ph: PhantomData<F>,
    advice: Column<Advice>,
    instance: Column<Instance>,
    s: Selector,
}

#[cfg(feature = "use_pse_halo2_proofs")]
impl<F: PrimeField> Default for MultiRowTwoBitDecompCircuit<F> {
    fn default() -> Self {
        MultiRowTwoBitDecompCircuit {
            b0: F::ONE,
            b1: F::ONE,
        }
    }
}

#[cfg(feature = "use_pse_halo2_proofs")]
impl<F: PrimeField> Circuit<F> for MultiRowTwoBitDecompCircuit<F> {
    type Config = MultiRowTwoBitDecompCircuitConfig<F>;
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

        // define gates
        meta.create_gate("b0_binary_check", |meta| {
            let a = meta.query_advice(x, Rotation::cur());
            let dummy = meta.query_selector(s);
            // b0 * (1-b0)
            vec![dummy * a.clone() * (Expression::Constant(F::ONE) - a)]
        });
        meta.create_gate("b1_binary_check", |meta| {
            let a = meta.query_advice(x, Rotation::next());
            let dummy = meta.query_selector(s);
            // b1 * (1-b1)
            vec![dummy * a.clone() * (Expression::Constant(F::ONE) - a)]
        });
        meta.create_gate("equality", |meta| {
            let a = meta.query_advice(x, Rotation::cur());
            let b = meta.query_advice(x, Rotation::next());
            let c = meta.query_advice(x, Rotation(2));
            let dummy = meta.query_selector(s);
            // The following is equivalent to: vec![dummy * (a + Expression::Constant(F::from(2)) * b - c)]
            // But it uses the Scaled operator.
            vec![dummy * (a + Expression::Scaled(Box::new(b), F::from(2)) - c)]
        });

        Self::Config {
            _ph: PhantomData,
            advice: x,
            instance: i,
            s,
        }
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
        // expose the public input
        layouter.constrain_instance(out.cell(), config.instance, 0)?;
        Ok(())
    }
}
