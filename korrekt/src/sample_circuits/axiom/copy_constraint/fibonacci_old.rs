use axiom_halo2_proofs::arithmetic::Field;
use axiom_halo2_proofs::circuit::{AssignedCell, Cell, Layouter, SimpleFloorPlanner, Value};
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

    // #[allow(clippy::type_complexity)]
    // pub fn assign_first_row(
    //     &self,
    //     mut layouter: impl Layouter<F>,
    // ) -> Result<(Cell, Cell, Cell), Error> {
    //     layouter.assign_region(
    //         || "first row",
    //         |mut region| {
    //             self.config.selector.enable(&mut region, 0)?;

    //             let a_cell = region.assign_advice_from_instance(
    //                 || "f(0)",
    //                 self.config.instance,
    //                 0,
    //                 self.config.col_a,
    //                 0,
    //             )?;

    //             let b_cell = region.assign_advice_from_instance(
    //                 || "f(1)",
    //                 self.config.instance,
    //                 1,
    //                 self.config.col_b,
    //                 0,
    //             )?;

    //             let c_cell = region.assign_advice(
    //                 self.config.col_c,
    //                 0,
    //                 a_cell.value().copied() + b_cell.value(),
    //             );

    //             Ok((a_cell.cell(), b_cell.cell(), c_cell.cell()))
    //         },
    //     )
    // }

    pub fn assign_row(
        &self,
        mut layouter: impl Layouter<F>,
    ) -> Result<AssignedCell<&Assigned<F>, F>, Error> {
        //let mut c_cell;
        //let mut prev_b;
        //let mut prev_c;
        let (mut prev_b, mut prev_c) = layouter
            .assign_region(
                || "first row",
                |mut region| {
                    self.config.selector.enable(&mut region, 0)?;

                    region.assign_advice(self.config.col_a, 0, Value::known(F::ONE));

                    let mut prev_b =
                        region.assign_advice(self.config.col_b, 0, Value::known(F::ONE));
                    let mut prev_c = region.assign_advice(
                        self.config.col_c,
                        0,
                        Value::known(F::ONE) + Value::known(F::ONE),
                    );

                    Ok((prev_b, prev_c))
                },
            )
            .unwrap();
        //for _i in 3..10 {
        let mut c_cell = layouter
            .assign_region(
                || "second row",
                |mut region| {
                    self.config.selector.enable(&mut region, 0)?;

                    // Copy the value from b & c in previous row to a & b in current row
                    prev_b.copy_advice(&mut region, self.config.col_a, 0);
                    prev_c.copy_advice(&mut region, self.config.col_b, 0);

                    let c_cell =
                        region.assign_advice(self.config.col_c, 0, prev_b.value + prev_c.value);

                    Ok(c_cell)
                },
            )
            .unwrap();
        prev_b = prev_c;
        prev_c = c_cell.clone();

        // c_cell = layouter
        //     .assign_region(
        //         || "next row",
        //         |mut region| {
        //             self.config.selector.enable(&mut region, 0)?;

        //             // Copy the value from b & c in previous row to a & b in current row
        //             prev_b.copy_advice(&mut region, self.config.col_a, 0);
        //             prev_c.copy_advice(&mut region, self.config.col_b, 0);

        //             let c_cell =
        //                 region.assign_advice(self.config.col_c, 0, prev_b.value + prev_c.value);

        //             Ok(c_cell)
        //         },
        //     )
        //     .unwrap();
        // prev_b = prev_c;
        // prev_c = c_cell.clone();

        // c_cell = layouter
        //     .assign_region(
        //         || "next row",
        //         |mut region| {
        //             self.config.selector.enable(&mut region, 0)?;

        //             // Copy the value from b & c in previous row to a & b in current row
        //             prev_b.copy_advice(&mut region, self.config.col_a, 0);
        //             prev_c.copy_advice(&mut region, self.config.col_b, 0);

        //             let c_cell =
        //                 region.assign_advice(self.config.col_c, 0, prev_b.value + prev_c.value);

        //             Ok(c_cell)
        //         },
        //     )
        //     .unwrap();

        Ok(prev_c)
    }

    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        cell: Cell,
        row: usize,
    ) -> Result<(), Error> {
        Ok(layouter.constrain_instance(cell, self.config.instance, row))
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
        let chip:FibonacciChip<F> = FibonacciChip::construct(config);

        // let (_, mut prev_b, mut prev_c) =
        //     chip.assign_first_row(layouter.namespace(|| "first row"))?;

        let c_cell: AssignedCell<&Assigned<F>, F> = chip.assign_row(layouter.namespace(|| "next row"))?;
        layouter.constrain_instance(c_cell.cell(), chip.config.instance, 2);
        Ok(())
    }
}
