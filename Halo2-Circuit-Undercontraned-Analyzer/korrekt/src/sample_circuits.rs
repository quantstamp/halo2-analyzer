use std::marker::PhantomData;
use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::plonk::{
    Advice, Circuit, Column, ConstraintSystem, Expression, Instance, Selector,
};
use halo2_proofs::circuit::{Layouter, Value, SimpleFloorPlanner, AssignedCell};
use halo2_proofs::plonk::Error;
use halo2_proofs::poly::Rotation;

pub struct PlayCircuit<F: FieldExt> {
    _ph: PhantomData<F>,
    b0: F,
    b1: F,
}

#[derive(Clone)]
pub struct PlayCircuitConfig<F: FieldExt> {
    _ph: PhantomData<F>,
    b0: Column<Advice>,
    b1: Column<Advice>,
    x: Column<Advice>,
    i: Column<Instance>,
    s: Selector,
}

impl<F: FieldExt> PlayCircuit<F> {
    pub fn new(b0: F, b1: F) -> Self {
        PlayCircuit {
            _ph: PhantomData,
            b0,
            b1,
        }
    }
}

impl<F: FieldExt> Default for PlayCircuit<F> {
    fn default() -> Self {
        PlayCircuit {
            _ph: PhantomData,
            b0: F::one(),
            b1: F::one(),
        }
    }
}

impl<F: FieldExt> Circuit<F> for PlayCircuit<F> {
    type Config = PlayCircuitConfig<F>;
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
            let a = meta.query_advice(b1, Rotation::cur());
            let dummy = meta.query_selector(s);
            vec![dummy * a.clone() * (Expression::Constant(F::from(1)) - a.clone())]
            // b0 * (1-b0)
        });
        meta.create_gate("b1_binary_check", |meta| {
            let a = meta.query_advice(b1, Rotation::cur());
            let dummy = meta.query_selector(s);
            vec![dummy * a.clone() * (Expression::Constant(F::from(1)) - a.clone())]
            // b1 * (1-b1)
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

        let cfg = Self::Config {
            _ph: PhantomData,
            b0,
            b1,
            x,
            i,
            s,
        };

        cfg
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
        // Is this line just making sure the output "x" (which is private) is same as the instance (public input)?
        // For example, given public input i=3, we want b0 = 1, b1 = 1, x = 3, and make sure x
        layouter.constrain_instance(out.cell(), config.i, 0)?; //*** what is this? */
        Ok(())
    }
}

pub struct PlayCircuitUnderConstrained<F: FieldExt> {
    _ph: PhantomData<F>,
    b0: F,
    b1: F,
}

#[derive(Clone)]
pub struct PlayCircuitUnderConstrainedConfig<F: FieldExt> {
    _ph: PhantomData<F>,
    b0: Column<Advice>,
    b1: Column<Advice>,
    x: Column<Advice>,
    i: Column<Instance>,
    s: Selector,
}

impl<F: FieldExt> PlayCircuitUnderConstrained<F> {
    pub fn new(b0: F, b1: F) -> Self {
        PlayCircuitUnderConstrained {
            _ph: PhantomData,
            b0,
            b1,
        }
    }
}

impl<F: FieldExt> Default for PlayCircuitUnderConstrained<F> {
    fn default() -> Self {
        PlayCircuitUnderConstrained {
            _ph: PhantomData,
            b0: F::one(),
            b1: F::one(),
        }
    }
}

impl<F: FieldExt> Circuit<F> for PlayCircuitUnderConstrained<F> {
    type Config = PlayCircuitConfig<F>;
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
            let a = meta.query_advice(b1, Rotation::cur());
            let dummy = meta.query_selector(s);
            vec![dummy * a.clone() * (Expression::Constant(F::from(1)) - a.clone())]
            // b0 * (1-b0)
        });
        meta.create_gate("b1_binary_check", |meta| {
            let a = meta.query_advice(b1, Rotation::cur());
            let dummy = meta.query_selector(s);
            vec![dummy * a.clone() * (Expression::Constant(F::from(1)) - a.clone())]
            // b1 * (1-b1)
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

        let cfg = Self::Config {
            _ph: PhantomData,
            b0,
            b1,
            x,
            i,
            s,
        };

        cfg
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
        // Is this line just making sure the output "x" (which is private) is same as the instance (public input)?
        // For example, given public input i=3, we want b0 = 1, b1 = 1, x = 3, and make sure x
        layouter.constrain_instance(out.cell(), config.i, 0)?; //*** what is this? */
        Ok(())
    }
}

pub struct MultiPlayCircuit<F: FieldExt> {
    _ph: PhantomData<F>,
    b0: F,
    b1: F,
}

#[derive(Clone)]
pub struct MultiPlayCircuitConfig<F: FieldExt> {
    _ph: PhantomData<F>,
    advice: Column<Advice>,
    instance: Column<Instance>,
    s: Selector,
}

impl<F: FieldExt> MultiPlayCircuit<F> {
    pub fn new(b0: F, b1: F) -> Self {
        MultiPlayCircuit {
            _ph: PhantomData,
            b0,
            b1,
        }
    }
}

impl<F: FieldExt> Default for MultiPlayCircuit<F> {
    fn default() -> Self {
        MultiPlayCircuit {
            _ph: PhantomData,
            b0: F::one(),
            b1: F::one(),
        }
    }
}

impl<F: FieldExt> Circuit<F> for MultiPlayCircuit<F> {
    type Config = MultiPlayCircuitConfig<F>;
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
            vec![dummy * a.clone() * (Expression::Constant(F::from(1)) - a.clone())]
            // b0 * (1-b0)
        });
        meta.create_gate("b1_binary_check", |meta| {
            let a = meta.query_advice(x, Rotation::next());
            let dummy = meta.query_selector(s);
            vec![dummy * a.clone() * (Expression::Constant(F::from(1)) - a.clone())]
            // b1 * (1-b1)
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

        let cfg = Self::Config {
            _ph: PhantomData,
            advice: x,
            instance: i,
            s,
        };

        cfg
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
        layouter.constrain_instance(out.cell(), config.instance, 0)?; //*** what is this? */
        Ok(())
    }
}

pub struct PlayCircuit_M<F: FieldExt> {
    _ph: PhantomData<F>,
    a: F,
    b: F,
}

#[derive(Clone)]
pub struct PlayCircuit_M_Config<F: FieldExt> {
    _ph: PhantomData<F>,
    s_mul: Selector,
    s_add: Selector,
    columns: [Column<Advice>; 25],
}

impl <F: FieldExt> PlayCircuit_M<F> {
    fn new(a: F, b: F) -> Self {
        PlayCircuit_M {
            _ph: PhantomData,
            a,
            b
        }
    }
}

impl <F: FieldExt> Default for PlayCircuit_M<F> {
    fn default() -> Self {
        PlayCircuit_M{
            _ph: PhantomData,
            a: F::one(),
            b: F::one(),
        }
    }
}

impl <F: FieldExt>  Circuit<F> for PlayCircuit_M<F> {
    type Config = PlayCircuit_M_Config<F>;
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
            s_add,
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


#[derive(Debug, Clone)]
pub struct FibonacciConfig {
    pub col_a: Column<Advice>,
    pub col_b: Column<Advice>,
    pub col_c: Column<Advice>,
    pub selector: Selector,
    pub instance: Column<Instance>,
}

#[derive(Debug, Clone)]
struct FibonacciChip<F: FieldExt> {
    config: FibonacciConfig,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> FibonacciChip<F> {
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

            // println!("{:?}", vec![s.clone() * (a.clone() + b.clone() - c.clone())]);
            vec![s * (a + b - c)]
            //[Product(Selector(Selector(0, true)), Sum(Sum(Advice { query_index: 0, column_index: 0, rotation: Rotation(0) }, Advice { query_index: 1, column_index: 1, rotation: Rotation(0) }), Negated(Advice { query_index: 2, column_index: 2, rotation: Rotation(0) })))]
        });

        FibonacciConfig {
            col_a,
            col_b,
            col_c,
            selector,
            instance,
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

                let a_cell = region.assign_advice_from_instance(
                    || "f(0)",
                    self.config.instance,
                    0,
                    self.config.col_a,
                    0)?;

                let b_cell = region.assign_advice_from_instance(
                    || "f(1)",
                    self.config.instance,
                    1,
                    self.config.col_b,
                    0)?;

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

    pub fn assign_row(
        &self,
        mut layouter: impl Layouter<F>,
        prev_b: &AssignedCell<F, F>,
        prev_c: &AssignedCell<F, F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "next row",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;

                // Copy the value from b & c in previous row to a & b in current row
                prev_b.copy_advice(
                    || "a",
                    &mut region,
                    self.config.col_a,
                    0,
                )?;
                prev_c.copy_advice(
                    || "b",
                    &mut region,
                    self.config.col_b,
                    0,
                )?;

                let c_cell = region.assign_advice(
                    || "c",
                    self.config.col_c,
                    0,
                    || prev_b.value().copied() + prev_c.value(),
                )?;

                Ok(c_cell)
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
pub struct MyCircuit<F>(pub PhantomData<F>);

impl<F: FieldExt> Circuit<F> for MyCircuit<F> {
    type Config = FibonacciConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let cfg = FibonacciChip::configure(meta);
        // for gate in &meta.gates{
        //     //println!("{:?}",gate.polys);
        // }
        cfg
        
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
            let c_cell = chip.assign_row(layouter.namespace(|| "next row"), &prev_b, &prev_c)?;
            prev_b = prev_c;
            prev_c = c_cell;
        }

        chip.expose_public(layouter.namespace(|| "out"), &prev_c, 2)?;
        Ok(())
    }
}