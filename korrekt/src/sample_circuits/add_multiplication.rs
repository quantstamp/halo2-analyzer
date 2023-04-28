use std::marker::PhantomData;
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::plonk::{
    Advice, Circuit, Column, ConstraintSystem, Selector,
};
use halo2_proofs::circuit::{Layouter, Value, SimpleFloorPlanner};
use halo2_proofs::plonk::Error;
use halo2_proofs::poly::Rotation;

pub struct AddMultCircuit<F: FieldExt> {
    a: F,
    b: F,
}

#[derive(Clone)]
pub struct AddMultCircuitConfig<F: FieldExt> {
    _ph: PhantomData<F>,
    s_mul: Selector,
    //s_add: Selector,
    columns: [Column<Advice>; 25],
}

impl <F: FieldExt> AddMultCircuit<F> {
    // fn new(a: F, b: F) -> Self {
    //     AddMultCircuit {
    //         a,
    //         b
    //     }
    // }
}

impl <F: FieldExt> Default for AddMultCircuit<F> {
    fn default() -> Self {
        AddMultCircuit{
            a: F::one(),
            b: F::one(),
        }
    }
}

impl <F: FieldExt>  Circuit<F> for AddMultCircuit<F> {
    type Config = AddMultCircuitConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let columns: [Column<Advice>; 25] = (0..25)
        .map(|_| {
            let column = meta.advice_column();
            meta.enable_equality(column);
            column
        })
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();
        
        for column in columns.iter().cloned() {
            meta.enable_equality(column);
        }

        // multiplication selector
        let s_mul = meta.selector();

        // def mul. gate
        meta.create_gate("mul", |meta| {
            let lhs = meta.query_advice(columns[0], Rotation::cur());
            let rhs = meta.query_advice(columns[1], Rotation::cur());
            let out = meta.query_advice(columns[0], Rotation::next());
            let s_mul = meta.query_selector(s_mul);
            vec![s_mul * (lhs * rhs - out)]
        });

        let s_add = meta.selector();

        meta.create_gate("add", |meta| {
            let lhs = meta.query_advice(columns[0], Rotation::cur());
            let rhs = meta.query_advice(columns[1], Rotation::cur());
            let out = meta.query_advice(columns[0], Rotation::next());
            let s_add = meta.query_selector(s_add);
            vec![s_add * (lhs + rhs - out)]
        });

        Self::Config {
            _ph: PhantomData,
            s_mul,
            //s_add,
            columns,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {

        layouter.assign_region(
            || "test 1",
            |mut region| {
                // do mul (into next)
                config.s_mul.enable(&mut region, 0)?;

                region.assign_advice(
                    || "a",
                    config.columns[0],
                    0,
                    || Value::known(self.a),
                )?;

                region.assign_advice(
                    || "b",
                    config.columns[1],
                    0,
                    || Value::known(self.b),
                )?;

                let c = self.a * self.b;

                region.assign_advice(
                    || "c",
                    config.columns[0],
                    1,
                    || Value::known(c),
                )?;

                Ok(())
            }
        ).unwrap();

        layouter.assign_region(
            || "test 2",
            |mut region| {
                // do mul (into next)
                // config.s_mul.enable(&mut region, 0)?;

                region.assign_advice(
                    || "a",
                    config.columns[0],
                    0,
                    || Value::known(self.a),
                )?;

                region.assign_advice(
                    || "b",
                    config.columns[1],
                    0,
                    || Value::known(self.b),
                )?;

                let c = self.a * self.b;

                region.assign_advice(
                    || "c",
                    config.columns[0],
                    1,
                    || Value::known(c),
                )?;

                Ok(())
            }
        ).unwrap();

        Ok(())
    }
}
