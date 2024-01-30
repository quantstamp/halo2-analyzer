use axiom_halo2_proofs::arithmetic::Field as FieldExt;
use axiom_halo2_proofs::circuit::Value;
use axiom_halo2_proofs::{
    circuit::{Cell, Chip, Layouter, Region, SimpleFloorPlanner},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Selector},
    poly::Rotation,
};

use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct FibonacciConfig {
    a: Column<Advice>,
    b: Column<Advice>,
    s: Selector,
}

struct FibonacciChip<F: FieldExt> {
    config: FibonacciConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> FibonacciChip<F> {
    fn new(config: FibonacciConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> FibonacciConfig {
        let a = meta.advice_column();
        let b = meta.advice_column();
        let a_next = meta.advice_column();
        let s = meta.selector();

        meta.enable_equality(a);
        meta.enable_equality(b);

        meta.create_gate("Fibonacci", |cells| {
            let a = cells.query_advice(a, Rotation::cur());
            let b = cells.query_advice(b, Rotation::cur());
            let a_next = cells.query_advice(a_next, Rotation::next());
            let s = cells.query_selector(s);

            vec![s * (a + b - a_next)]
        });

        FibonacciConfig { a, b, s }
    }
    
}

pub struct FibonacciCircuit<F: FieldExt> {
    pub initial: F,
    pub steps: usize,
}

impl<F: FieldExt> Circuit<F> for FibonacciCircuit<F> {
    type Config = FibonacciConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self {
            initial: F::ZERO,
            steps: self.steps,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        FibonacciChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip:FibonacciChip<F> = FibonacciChip::new(config.clone());
    
        let mut a_val = self.initial;
        let mut b_val = F::ONE;
        let mut a_cell_prev: Option<Cell> = None;
    
        for i in 0..self.steps {
            // Assign a region for each step (or group steps as needed)
            layouter.assign_region(
                || format!("Fibonacci sequence {}", i),
                |mut region| {
                    // Assign 'a' value
                    let a_cell = region.assign_advice(config.a, 0, Value::known(a_val));
                    let a_cell = a_cell.cell();
    
                    // Assign 'b' value
                    let b_cell = region.assign_advice(config.b, 0, Value::known(b_val));
                    let b_cell = b_cell.cell();
    
                    // Enforce equality for subsequent cells
                    if let Some(prev_a_cell) = a_cell_prev.take() {
                        region.constrain_equal(prev_a_cell, b_cell);
                    }
    
                    a_cell_prev = Some(a_cell);
                    let next_val = a_val + b_val;
                    a_val = b_val;
                    b_val = next_val;
    
                    Ok(())
                },
            )?;
        }
    
        Ok(())
    }    
}
