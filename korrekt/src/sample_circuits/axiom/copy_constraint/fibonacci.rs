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
    // ) -> Result<
    //     (
    //         AssignedCell<&Assigned<F>, F>,
    //         AssignedCell<&Assigned<F>, F>,
    //         AssignedCell<&Assigned<F>, F>,
    //     ),
    //     Error,
    // > {
    //     layouter.assign_region(
    //         || "first row",
    //         |mut region| {
    //             self.config.selector.enable(&mut region, 0)?;

    //             let a_cell = region
    //                 .assign_advice_from_instance(
    //                     || "f(0)",
    //                     self.config.instance,
    //                     0,
    //                     self.config.col_a,
    //                     0,
    //                 )
    //                 .unwrap();
    //             let a_assigned_ref: &Assigned<F> = unsafe { std::mem::transmute(&a_cell.value()) };
    //             let a = AssignedCell {
    //                 value: Value::known(a_assigned_ref),
    //                 cell: a_cell.cell(),
    //                 _marker: PhantomData,
    //             };
    //             let b_cell = region
    //                 .assign_advice_from_instance(
    //                     || "f(1)",
    //                     self.config.instance,
    //                     1,
    //                     self.config.col_b,
    //                     0,
    //                 )
    //                 .unwrap();
    //             let b_assigned_ref: &Assigned<F> = unsafe { std::mem::transmute(&b_cell.value()) };
    //             let b = AssignedCell {
    //                 value: Value::known(b_assigned_ref),
    //                 cell: b_cell.cell(),
    //                 _marker: PhantomData,
    //             };
    //             let c_cell = region.assign_advice(
    //                 self.config.col_c,
    //                 0,
    //                 a_cell.value().copied() + b_cell.value(),
    //             );

    //             Ok((a, b, c_cell))
    //         },
    //     )
    // }

    // pub fn assign_row(
    //     &self,
    //     i: i32,
    //     mut layouter: impl Layouter<F>,
    //     prev_b: &AssignedCell<&Assigned<F>, F>,
    //     prev_c: &AssignedCell<&Assigned<F>, F>,
    // ) -> Result<AssignedCell<&Assigned<F>, F>, Error> {
    //     layouter.assign_region(
    //         || format!("{} row", i),
    //         |mut region| {
    //             self.config.selector.enable(&mut region, 0)?;

    //             // Copy the value from b & c in previous row to a & b in current row
    //             prev_b.copy_advice(&mut region, self.config.col_a, 0);
    //             prev_c.copy_advice(&mut region, self.config.col_b, 0);

    //             let c_cell = region.assign_advice(
    //                 self.config.col_c,
    //                 0,
    //                 prev_b.value().copied() + prev_c.value().copied(),
    //             );

    //             Ok(c_cell)
    //         },
    //     )
    // }

    // pub fn expose_public(
    //     &self,
    //     mut layouter: impl Layouter<F>,
    //     cell: &AssignedCell<&Assigned<F>, F>,
    //     row: usize,
    // ) {
    //     layouter.constrain_instance(cell.cell(), self.config.instance, row)
    // }
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
        let chip:FibonacciChip<F> = FibonacciChip::construct(config.clone());
    
        let mut a_val = F::ONE;
        let mut b_val = F::ONE;
        let mut a_cell_prev: Option<Cell> = None;
        
        for i in 0..10 {
            layouter.assign_region(
                || format!("Fibonacci sequence {}", i),
                |mut region| {
                    // Dynamically calculate the row offset for this region
                    let row_offset = i;
        
                    // If not the first region, link 'b' cell of this region with 'a' cell of the previous region
                    if let Some(prev_a_cell) = a_cell_prev {
                        let b_cell = region.assign_advice(config.col_b, row_offset, Value::known(b_val));
                        region.constrain_equal(prev_a_cell, b_cell.cell());
                    }
        
                    // Assign 'a' value for the current step
                    let a_cell = region.assign_advice(config.col_a, row_offset, Value::known(a_val)).cell();
        
                    // Update the values for the next step
                    let next_val = a_val + b_val;
                    a_val = b_val;
                    b_val = next_val;
        
                    // Store the current 'a' cell to link in the next region
                    a_cell_prev = Some(a_cell);
        
                    Ok(())
                },
            )?;
        }
        Ok(())
    }
}
