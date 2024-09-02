use group::ff::PrimeField as Field;
use std::marker::PhantomData;
use zcash_halo2_proofs::circuit::*;
use zcash_halo2_proofs::plonk::*;
use zcash_halo2_proofs::poly::Rotation;

pub struct FixedWithZeroCircuit<F: Field> {
    _ph: PhantomData<F>,
}

#[derive(Clone)]

pub struct FixedWithZeroCircuitConfig {
    a: Column<Advice>,
    f: Column<Fixed>,
    s: Selector,
}

impl<F: Field> Default for FixedWithZeroCircuit<F> {
    fn default() -> Self {
        FixedWithZeroCircuit {
            _ph: PhantomData,
        }
    }
}

impl<F: Field> Circuit<F> for FixedWithZeroCircuit<F> {
    type Config = FixedWithZeroCircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let a = meta.advice_column();
        let f = meta.fixed_column();
        let s = meta.selector();

        meta.enable_equality(a);
        meta.enable_equality(f);

        // define gates
        meta.create_gate("multiplication", |meta| {
            let b1 = meta.query_advice(a, Rotation::cur());
            let f = meta.query_fixed(f);
            let b3 = meta.query_advice(a, Rotation::next());
            let selector = meta.query_selector(s);
            // b0 * (1-b0)
            vec![selector * (b1 * f - b3)]
        });

        Self::Config { a, f, s }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter
            .assign_region(
                || "The Region",
                |mut region| {
                    config.s.enable(&mut region, 0)?;

                    let out = region.assign_fixed(|| "f1", config.f, 0, || Value::known(F::from_u128(2)))?;//Value::known(F::ZERO))?;

                    Ok(out)
                },
            )
            .unwrap();
        Ok(())
    }
}