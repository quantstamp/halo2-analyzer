use group::ff::Field;
use pse_halo2_proofs::circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value};
use pse_halo2_proofs::plonk::{
    Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Instance, Selector,
};
use pse_halo2_proofs::poly::Rotation;
use std::marker::PhantomData;
use std::thread::current;

#[derive(Debug, Clone)]
pub struct SampleConfig {
    pub col_a: Column<Advice>,
    pub col_b: Column<Advice>,
    pub col_c: Column<Advice>,
    pub selector: Selector,
    pub instance: Column<Instance>,
    pub fixed_a: Column<Fixed>,
    pub fixed_b: Column<Fixed>,
}

#[derive(Debug, Clone)]
struct SampleChip<F: Field> {
    config: SampleConfig,
    _marker: PhantomData<F>,
}

impl<F: Field> SampleChip<F> {
    pub fn construct(config: SampleConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> SampleConfig {
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let col_c = meta.advice_column();
        let selector = meta.selector();
        let instance = meta.instance_column();
        let fixed_a = meta.fixed_column();
        let fixed_b = meta.fixed_column();

        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);
        meta.enable_equality(instance);
        meta.enable_equality(fixed_a);
        meta.enable_equality(fixed_b);

        // Initial gate: col_c should be equal to the sum of fixed_a and fixed_b
        meta.create_gate("initial_gate", |meta| {
            let s = meta.query_selector(selector);
            let a = meta.query_fixed(fixed_a, Rotation::cur());
            let b = meta.query_fixed(fixed_b, Rotation::cur());
            let c = meta.query_advice(col_c, Rotation::cur());

            vec![s * (a + b) * c]
        });

        SampleConfig {
            col_a,
            col_b,
            col_c,
            selector,
            instance,
            fixed_a,
            fixed_b,
        }
    }

    #[allow(clippy::type_complexity)]
    pub fn assign_first_row(
        &self,
        mut layouter: impl Layouter<F>,
    ) -> Result<(AssignedCell<F, F>, AssignedCell<F, F>, AssignedCell<F, F>), Error> {
        layouter.assign_region(
            || "first row",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;
                let a_cell = region.assign_fixed(
                    || "fixed value",
                    self.config.fixed_a,
                    0,
                    || Value::known(F::ZERO),
                )?;

                let b_cell = region.assign_fixed(
                    || "fixed value",
                    self.config.fixed_b,
                    0,
                    || Value::known(F::ZERO),
                )?;

                // Copy fixed values to advice columns
                a_cell.copy_advice(|| "a", &mut region, self.config.col_a, 0)?;
                b_cell.copy_advice(|| "b", &mut region, self.config.col_b, 0)?;

                let c_cell = region.assign_advice(
                    || "a + b",
                    self.config.col_c,
                    0,
                    || a_cell.value().copied() + b_cell.value(),
                )?;

                Ok((a_cell, b_cell, c_cell))
            },
        )
    }

    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        cell: &AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.config.instance, row)
    }
}

#[derive(Default)]
pub struct SampleCircuit<F>(pub PhantomData<F>);

impl<F: Field> Circuit<F> for SampleCircuit<F> {
    type Config = SampleConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        SampleChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = SampleChip::construct(config);

        let (_, _, prev_c) = chip.assign_first_row(layouter.namespace(|| "first row"))?;

        chip.expose_public(layouter.namespace(|| "out"), &prev_c, 2)?;
        Ok(())
    }
}
