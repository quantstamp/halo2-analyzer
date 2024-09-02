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
        FixedWithZeroCircuit { _ph: PhantomData }
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
            let b2 = meta.query_advice(a, Rotation::next());
            let b3 = meta.query_advice(a, Rotation(2));
            let selector = meta.query_selector(s);
            // b0 * (1-b0)
            vec![selector * (b1 * b2 - b3)]
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

                    let b1 = region.assign_advice(|| "b0", config.a, 0, || Value::known(F::ONE))?;
                    let b2 = region.assign_advice(|| "b0", config.a, 1, || Value::known(F::ONE))?;
                    let b3 = region.assign_advice(|| "b0", config.a, 2, || Value::known(F::ONE))?;

                    let f1 = region.assign_fixed(|| "c0", config.f, 0, || Value::known(F::ZERO))?;

                    let f2 = region.assign_fixed(|| "c0", config.f, 1, || Value::known(F::ZERO))?;

                    let out = region.constrain_equal(b1.cell(), f1.cell())?;

                    let out = region.constrain_equal(b3.cell(), f2.cell())?;

                    Ok(out)
                },
            )
            .unwrap();
        Ok(())
    }
}
