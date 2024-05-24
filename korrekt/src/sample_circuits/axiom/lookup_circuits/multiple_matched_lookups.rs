use axiom_halo2_proofs::circuit::*;
use axiom_halo2_proofs::plonk::*;
use axiom_halo2_proofs::poly::Rotation;
use group::ff::PrimeField;
use std::marker::PhantomData;

#[derive(Debug, Clone)]

pub struct FibonacciConfig {
    pub advice: [Column<Advice>; 3],
    pub s_add: Selector,
    pub s_xor: Selector,
    pub s_xor_1: Selector,
    pub s_range: Selector,
    pub s_range_1: Selector,
    pub range_check_table: [TableColumn; 1],
    pub range_check_table_1: [TableColumn; 1],
    pub xor_table: [TableColumn; 3],
    pub xor_table_1: [TableColumn; 3],
    pub instance: Column<Instance>,
}

#[derive(Debug, Clone)]

struct FibonacciChip<F: PrimeField> {
    config: FibonacciConfig,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> FibonacciChip<F> {
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
        let s_add = meta.selector();
        let s_xor: Selector = meta.complex_selector();
        let s_xor_1: Selector = meta.complex_selector();
        let s_range = meta.complex_selector();
        let s_range_1 = meta.complex_selector();
        let instance = meta.instance_column();

        let xor_table = [
            meta.lookup_table_column(),
            meta.lookup_table_column(),
            meta.lookup_table_column(),
        ];

        let xor_table_1 = [
            meta.lookup_table_column(),
            meta.lookup_table_column(),
            meta.lookup_table_column(),
        ];

        let range_check_table = [meta.lookup_table_column()];

        let range_check_table_1 = [meta.lookup_table_column()];

        meta.enable_equality(col_a);
        meta.enable_equality(col_b);
        meta.enable_equality(col_c);
        meta.enable_equality(instance);

        meta.create_gate("add", |meta| {
            //
            // col_a | col_b | col_c | selector
            //   a      b        c       s
            //
            let s = meta.query_selector(s_add);
            let a = meta.query_advice(col_a, Rotation::cur());
            let b = meta.query_advice(col_b, Rotation::cur());
            let c = meta.query_advice(col_c, Rotation::cur());
            vec![s * (a + b - c)]
        });

        meta.lookup("RC_lookup", |meta| {
            let s = meta.query_selector(s_range);
            let value = meta.query_advice(col_a, Rotation::cur());

            vec![(s * value, range_check_table[0])]
        });

        meta.lookup("RC1_lookup", |meta| {
            let s1 = meta.query_selector(s_range_1);
            let value = meta.query_advice(col_b, Rotation::cur());

            vec![(s1 * value, range_check_table_1[0])]
        });

        meta.lookup("XOR_lookup", |meta| {
            let s = meta.query_selector(s_xor);
            let lhs = meta.query_advice(col_a, Rotation::cur());
            let rhs = meta.query_advice(col_b, Rotation::cur());
            let out = meta.query_advice(col_c, Rotation::cur());
            vec![
                (s.clone() * lhs, xor_table[0]),
                (s.clone() * rhs, xor_table[1]),
                (s * out, xor_table[2]),
            ]
        });

        meta.lookup("XOR_lookup_1", |meta| {
            let s = meta.query_selector(s_xor);
            let lhs = meta.query_advice(col_a, Rotation::cur());
            let rhs = meta.query_advice(col_b, Rotation::cur());
            let out = meta.query_advice(col_c, Rotation::cur());
            vec![
                (s.clone() * lhs, xor_table_1[0]),
                (s.clone() * rhs, xor_table_1[1]),
                (s * out, xor_table_1[2]),
            ]
        });

        FibonacciConfig {
            advice: [col_a, col_b, col_c],
            s_add,
            s_xor,
            s_xor_1,
            s_range,
            s_range_1,
            range_check_table,
            range_check_table_1,
            xor_table,
            xor_table_1,
            instance,
        }
    }

    fn load_table_range(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "range_check_table",
            |mut table| {
                for (idx, value) in (0..6).enumerate() {
                    table.assign_cell(
                        || "value",
                        self.config.range_check_table[0],
                        idx,
                        || Value::known(F::from(value)),
                    )?;
                }
                Ok(())
            },
        )
    }

    fn load_table_range_1(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "range_check_table",
            |mut table| {
                for (idx, value) in (0..6).enumerate() {
                    table.assign_cell(
                        || "value",
                        self.config.range_check_table_1[0],
                        idx,
                        || Value::known(F::from(6 - value - 1)),
                    )?;
                }
                Ok(())
            },
        )
    }
    fn load_xor_table(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "xor_table",
            |mut table| {
                let mut idx = 0;
                for lhs in 0..6 {
                    for rhs in 0..6 {
                        table.assign_cell(
                            || "lhs",
                            self.config.xor_table[0],
                            idx,
                            || Value::known(F::from(lhs)),
                        )?;
                        table.assign_cell(
                            || "rhs",
                            self.config.xor_table[1],
                            idx,
                            || Value::known(F::from(rhs)),
                        )?;
                        table.assign_cell(
                            || "lhs ^ rhs",
                            self.config.xor_table[2],
                            idx,
                            || Value::known(F::from(lhs ^ rhs)),
                        )?;
                        idx += 1;
                    }
                }
                Ok(())
            },
        )
    }
    fn load_xor_table_1(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "xor_table_1",
            |mut table| {
                let mut idx = 0;
                for lhs in 0..6 {
                    for rhs in 0..6 {
                        table.assign_cell(
                            || "lhs",
                            self.config.xor_table_1[0],
                            idx,
                            || Value::known(F::from(6 - lhs - 1)),
                        )?;
                        table.assign_cell(
                            || "rhs",
                            self.config.xor_table_1[1],
                            idx,
                            || Value::known(F::from(6 - rhs - 1)),
                        )?;
                        table.assign_cell(
                            || "lhs ^ rhs",
                            self.config.xor_table_1[2],
                            idx,
                            || Value::known(F::from(6 - lhs - 1 ^ 6 - rhs - 1)),
                        )?;
                        idx += 1;
                    }
                }
                Ok(())
            },
        )
    }
    #[allow(clippy::type_complexity)]
    pub fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        nrows: usize,
    ) -> Result<AssignedCell<&Assigned<F>, F>, Error> {
        layouter.assign_region(
            || "entire circuit",
            |mut region| {
                self.config.s_add.enable(&mut region, 0)?;
                self.config.s_range.enable(&mut region, 0)?;
                self.config.s_range_1.enable(&mut region, 0)?;
                // assign first row

                let a_cell = region.assign_advice(self.config.advice[0], 0, Value::known(F::ONE));

                let mut b_cell =
                    region.assign_advice(self.config.advice[1], 0, Value::known(F::ONE));
                let mut c_cell = region.assign_advice(
                    self.config.advice[2],
                    0,
                    a_cell.value().copied() + b_cell.value().copied(),
                );

                // assign the rest of rows
                for row in 1..nrows {
                    b_cell.copy_advice(&mut region, self.config.advice[0], row);
                    c_cell.copy_advice(&mut region, self.config.advice[1], row);

                    let new_c_cell = if row % 2 == 0 {
                        self.config.s_add.enable(&mut region, row)?;
                        self.config.s_range.enable(&mut region, row)?;
                        self.config.s_range_1.enable(&mut region, row)?;
                        region.assign_advice(
                            self.config.advice[2],
                            row,
                            b_cell.value().copied() + c_cell.value().copied(),
                        )
                    } else {
                        self.config.s_xor.enable(&mut region, row)?;
                        self.config.s_range.enable(&mut region, row)?;
                        self.config.s_range_1.enable(&mut region, row)?;
                        let t = (|| {
                            b_cell.value().and_then(|a| {
                                c_cell.value().map(|b| {
                                    let binding = F::ZERO;
                                    let binding1 = F::ZERO;
                                    let a_val = match a {
                                        Assigned::Trivial(f) => f,
                                        Assigned::Zero => &binding,
                                        Assigned::Rational(_, _) => &binding1,
                                    };
                                    let binding2 = F::ZERO;
                                    let binding3 = F::ZERO;
                                    let b_val = match b {
                                        Assigned::Trivial(f) => f,
                                        Assigned::Zero => &binding2,
                                        Assigned::Rational(_, _) => &binding3,
                                    };

                                    let a_val1 = u64::from_str_radix(
                                        format!("{:?}", a_val).strip_prefix("0x").unwrap(),
                                        16,
                                    )
                                    .unwrap();
                                    let b_val1 = u64::from_str_radix(
                                        format!("{:?}", b_val).strip_prefix("0x").unwrap(),
                                        16,
                                    )
                                    .unwrap();
                                    F::from(a_val1 ^ b_val1)
                                })
                            })
                        })();
                        region.assign_advice(self.config.advice[2], row, t)
                    };

                    b_cell = c_cell;
                    c_cell = new_c_cell;
                }

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

pub struct MyCircuit<F>(pub PhantomData<F>);

impl<F: PrimeField> Circuit<F> for MyCircuit<F> {
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
        chip.load_xor_table(layouter.namespace(|| "lookup table"))?;
        chip.load_xor_table_1(layouter.namespace(|| "lookup table 1"))?;
        chip.load_table_range(layouter.namespace(|| "range table"))?;
        chip.load_table_range_1(layouter.namespace(|| "range table 1"))?;
        let out_cell = chip.assign(layouter.namespace(|| "entire table"), 4)?;
        chip.expose_public(layouter.namespace(|| "out"), &out_cell, 2);

        Ok(())
    }
}
