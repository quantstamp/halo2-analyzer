use axiom_halo2_proofs::arithmetic::Field;
use axiom_halo2_proofs::circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value};
use axiom_halo2_proofs::plonk::{
    Advice, Assigned, Circuit, Column, ConstraintSystem, Error, Instance, Selector,
};
use axiom_halo2_proofs::poly::Rotation;
use std::marker::PhantomData;

#[derive(Debug, Clone)]
pub struct FibonacciConfig {
    pub col_a: Column<Advice>,
    pub col_b: Column<Advice>,
    pub col_c: Column<Advice>,
    pub selector: Selector,
    pub instance: Column<Instance>,
}

#[derive(Debug, Clone)]
struct FibonacciChip<F: Field> {
    config: FibonacciConfig,
    _marker: PhantomData<F>,
}

impl<F: Field> FibonacciChip<F> {
    pub fn construct(config: FibonacciConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> FibonacciConfig {
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let col_c = meta.advice_column();
        let selector = meta.selector();
        let instance = meta.instance_column();

        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);
        meta.enable_equality(instance);

        meta.create_gate("add", |meta| {
            //
            // col_a | col_b | col_c | selector
            //   a      b        c       s
            //
            let s = meta.query_selector(selector);
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let c = meta.query_advice(col_c, Rotation::cur());

            vec![s * (a + b - c)]
        });

        FibonacciConfig {
            col_a,
            col_b,
            col_c,
            selector,
            instance,
        }
    }

    pub fn assign_first_row(
        &self,
        mut layouter: impl Layouter<F>,
    ) -> Result<
        (
            AssignedCell<&Assigned<F>, F>,
            AssignedCell<&Assigned<F>, F>,
            AssignedCell<&Assigned<F>, F>,
        ),
        Error,
    > {
        layouter.assign_region(
            || "first row",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;

                let a_cell = region.assign_advice(self.config.col_a, 0, Value::known(F::ONE));

                let b_cell = region.assign_advice(self.config.col_b, 0, Value::known(F::ONE));

                //let c_value = Value::zip(a_cell.value(), b_cell.value()).map(|(a, b)| *a + *b);
                let c_value = a_cell.value().copied() + b_cell.value().copied();
                let c_cell = region.assign_advice(self.config.col_c, 0, c_value);

                Ok((a_cell, b_cell, c_cell))
            },
        )
    }

    pub fn assign_row(
        &self,
        i: usize, // loop index
        mut layouter: impl Layouter<F>,
        prev_b: &AssignedCell<&Assigned<F>, F>,
        prev_c: &AssignedCell<&Assigned<F>, F>,
    ) -> Result<AssignedCell<&Assigned<F>, F>, Error> {
        layouter.assign_region(
            || "next row",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;
                let row_offset = i;

                // Copy the value from b & c in the previous row to a & b in the current row
                prev_b.copy_advice(&mut region, self.config.col_a, row_offset);
                prev_c.copy_advice(&mut region, self.config.col_b, row_offset);

                // Calculate the value for c_cell
                let c_value = Value::zip(prev_b.value(), prev_c.value()).map(|(b, c)| *b + *c);

                // Assign the value to c_cell
                let c_cell = region.assign_advice(self.config.col_c, row_offset, c_value);

                Ok(c_cell)
            },
        )
    }

    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        cell: &AssignedCell<&Assigned<F>, F>,
        row: usize,
    ) {
        layouter.constrain_instance(cell.cell(), self.config.instance, row)
    }
}

#[derive(Default)]
pub struct FibonacciCircuit<F>(pub PhantomData<F>);

impl<F: Field> Circuit<F> for FibonacciCircuit<F> {
    type Config = FibonacciConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        FibonacciChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = FibonacciChip::construct(config);

        let (_, mut prev_b, mut prev_c) =
            chip.assign_first_row(layouter.namespace(|| "first row"))?;

        for _i in 3..10 {
            let c_cell =
                chip.assign_row(_i, layouter.namespace(|| "next row"), &prev_b, &prev_c)?;
            prev_b = prev_c;
            prev_c = c_cell;
        }

        chip.expose_public(layouter.namespace(|| "out"), &prev_c, 2);
        Ok(())
    }
}
