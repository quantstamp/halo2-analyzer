use crate::circuit_analyzer::halo2_proofs_libs::*;
use std::marker::PhantomData;

#[derive(Debug, Clone)]
pub struct FibonacciConfig<const SIZE: usize> {
    pub advice: [Column<Advice>; 3],
    pub s_add: Selector,
    pub s_xor: Selector,
    pub s_xor_1: Selector,
    pub s_xor_2: Selector,
    pub s_xor_3: Selector,
    pub s_xor_4: Selector,
    pub s_xor_5: Selector,
    pub s_xor_6: Selector,
    pub s_xor_7: Selector,
    pub s_xor_8: Selector,
    pub s_xor_9: Selector,
    pub s_xor_10: Selector,
    pub s_xor_11: Selector,
    pub s_xor_12: Selector,
    pub s_xor_13: Selector,
    pub s_xor_14: Selector,
    pub s_range: Selector,
    pub s_range_1: Selector,
    pub range_check_table: [TableColumn; 1],
    pub range_check_table_1: [TableColumn; 1],
    pub xor_table: [TableColumn; 3],
    pub xor_table_1: [TableColumn; 3],
    pub xor_table_2: [TableColumn; 3],
    pub xor_table_3: [TableColumn; 3],
    pub xor_table_4: [TableColumn; 3],
    pub xor_table_5: [TableColumn; 3],
    pub xor_table_6: [TableColumn; 3],
    pub xor_table_7: [TableColumn; 3],
    pub xor_table_8: [TableColumn; 3],
    pub xor_table_9: [TableColumn; 3],
    pub xor_table_10: [TableColumn; 3],
    pub xor_table_11: [TableColumn; 3],
    pub xor_table_12: [TableColumn; 3],
    pub xor_table_13: [TableColumn; 3],
    pub xor_table_14: [TableColumn; 3],
    pub instance: Column<Instance>,
}

#[derive(Debug, Clone)]
struct FibonacciChip<F: FieldExt, const SIZE: usize> {
    config: FibonacciConfig<SIZE>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const SIZE: usize> FibonacciChip<F, SIZE> {
    pub fn construct(config: FibonacciConfig<SIZE>) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> FibonacciConfig<SIZE> {
        let col_a = meta.advice_column();
        let col_b = meta.advice_column();
        let col_c = meta.advice_column();
        let s_add = meta.selector();
        let s_xor: Selector = meta.complex_selector();
        let s_xor_1: Selector = meta.complex_selector();
        let s_xor_2: Selector = meta.complex_selector();
        let s_xor_3: Selector = meta.complex_selector();
        let s_xor_4: Selector = meta.complex_selector();
        let s_xor_5: Selector = meta.complex_selector();
        let s_xor_6: Selector = meta.complex_selector();
        let s_xor_7: Selector = meta.complex_selector();
        let s_xor_8: Selector = meta.complex_selector();
        let s_xor_9: Selector = meta.complex_selector();
        let s_xor_10: Selector = meta.complex_selector();
        let s_xor_11: Selector = meta.complex_selector();
        let s_xor_12: Selector = meta.complex_selector();
        let s_xor_13: Selector = meta.complex_selector();
        let s_xor_14: Selector = meta.complex_selector();
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

        let xor_table_2 = [
            meta.lookup_table_column(),
            meta.lookup_table_column(),
            meta.lookup_table_column(),
        ];

        let xor_table_3 = [
            meta.lookup_table_column(),
            meta.lookup_table_column(),
            meta.lookup_table_column(),
        ];

        let xor_table_4 = [
            meta.lookup_table_column(),
            meta.lookup_table_column(),
            meta.lookup_table_column(),
        ];

        let xor_table_5 = [
            meta.lookup_table_column(),
            meta.lookup_table_column(),
            meta.lookup_table_column(),
        ];

        let xor_table_6 = [
            meta.lookup_table_column(),
            meta.lookup_table_column(),
            meta.lookup_table_column(),
        ];

        let xor_table_7 = [
            meta.lookup_table_column(),
            meta.lookup_table_column(),
            meta.lookup_table_column(),
        ];

        let xor_table_8 = [
            meta.lookup_table_column(),
            meta.lookup_table_column(),
            meta.lookup_table_column(),
        ];

        let xor_table_9 = [
            meta.lookup_table_column(),
            meta.lookup_table_column(),
            meta.lookup_table_column(),
        ];

        let xor_table_10 = [
            meta.lookup_table_column(),
            meta.lookup_table_column(),
            meta.lookup_table_column(),
        ];

        let xor_table_11 = [
            meta.lookup_table_column(),
            meta.lookup_table_column(),
            meta.lookup_table_column(),
        ];

        let xor_table_12 = [
            meta.lookup_table_column(),
            meta.lookup_table_column(),
            meta.lookup_table_column(),
        ];

        let xor_table_13 = [
            meta.lookup_table_column(),
            meta.lookup_table_column(),
            meta.lookup_table_column(),
        ];

        let xor_table_14 = [
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
            let lhs = meta.query_advice(col_a, Rotation::cur());
            vec![(s * lhs, range_check_table[0])]
        });

        meta.lookup("RC1_lookup", |meta| {
            let s1 = meta.query_selector(s_range_1);
            let rhs = meta.query_advice(col_b, Rotation::cur());

            vec![(s1 * rhs, range_check_table_1[0])]
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
            let s = meta.query_selector(s_xor_1);
            let lhs = meta.query_advice(col_a, Rotation::cur());
            let rhs = meta.query_advice(col_b, Rotation::cur());
            let out = meta.query_advice(col_c, Rotation::cur());
            vec![
                (s.clone() * lhs, xor_table_1[0]),
                (s.clone() * rhs, xor_table_1[1]),
                (s * out, xor_table_1[2]),
            ]
        });

        meta.lookup("XOR_lookup_2", |meta| {
            let s = meta.query_selector(s_xor_2);
            let lhs = meta.query_advice(col_a, Rotation::cur());
            let rhs = meta.query_advice(col_b, Rotation::cur());
            let out = meta.query_advice(col_c, Rotation::cur());
            vec![
                (s.clone() * lhs, xor_table_2[0]),
                (s.clone() * rhs, xor_table_2[1]),
                (s * out, xor_table_2[2]),
            ]
        });

        meta.lookup("XOR_lookup_3", |meta| {
            let s = meta.query_selector(s_xor_3);
            let lhs = meta.query_advice(col_a, Rotation::cur());
            let rhs = meta.query_advice(col_b, Rotation::cur());
            let out = meta.query_advice(col_c, Rotation::cur());
            vec![
                (s.clone() * lhs, xor_table_3[0]),
                (s.clone() * rhs, xor_table_3[1]),
                (s * out, xor_table_3[2]),
            ]
        });

        meta.lookup("XOR_lookup_4", |meta| {
            let s = meta.query_selector(s_xor_4);
            let lhs = meta.query_advice(col_a, Rotation::cur());
            let rhs = meta.query_advice(col_b, Rotation::cur());
            let out = meta.query_advice(col_c, Rotation::cur());
            vec![
                (s.clone() * lhs, xor_table_4[0]),
                (s.clone() * rhs, xor_table_4[1]),
                (s * out, xor_table_4[2]),
            ]
        });

        meta.lookup("XOR_lookup_5", |meta| {
            let s = meta.query_selector(s_xor_5);
            let lhs = meta.query_advice(col_a, Rotation::cur());
            let rhs = meta.query_advice(col_b, Rotation::cur());
            let out = meta.query_advice(col_c, Rotation::cur());
            vec![
                (s.clone() * lhs, xor_table_5[0]),
                (s.clone() * rhs, xor_table_5[1]),
                (s * out, xor_table_5[2]),
            ]
        });

        meta.lookup("XOR_lookup_6", |meta| {
            let s = meta.query_selector(s_xor_6);
            let lhs = meta.query_advice(col_a, Rotation::cur());
            let rhs = meta.query_advice(col_b, Rotation::cur());
            let out = meta.query_advice(col_c, Rotation::cur());
            vec![
                (s.clone() * lhs, xor_table_6[0]),
                (s.clone() * rhs, xor_table_6[1]),
                (s * out, xor_table_6[2]),
            ]
        });

        meta.lookup("XOR_lookup_7", |meta| {
            let s = meta.query_selector(s_xor_7);
            let lhs = meta.query_advice(col_a, Rotation::cur());
            let rhs = meta.query_advice(col_b, Rotation::cur());
            let out = meta.query_advice(col_c, Rotation::cur());
            vec![
                (s.clone() * lhs, xor_table_7[0]),
                (s.clone() * rhs, xor_table_7[1]),
                (s * out, xor_table_7[2]),
            ]
        });

        meta.lookup("XOR_lookup_8", |meta| {
            let s = meta.query_selector(s_xor_8);
            let lhs = meta.query_advice(col_a, Rotation::cur());
            let rhs = meta.query_advice(col_b, Rotation::cur());
            let out = meta.query_advice(col_c, Rotation::cur());
            vec![
                (s.clone() * lhs, xor_table_8[0]),
                (s.clone() * rhs, xor_table_8[1]),
                (s * out, xor_table_8[2]),
            ]
        });

        meta.lookup("XOR_lookup_9", |meta| {
            let s = meta.query_selector(s_xor_9);
            let lhs = meta.query_advice(col_a, Rotation::cur());
            let rhs = meta.query_advice(col_b, Rotation::cur());
            let out = meta.query_advice(col_c, Rotation::cur());
            vec![
                (s.clone() * lhs, xor_table_9[0]),
                (s.clone() * rhs, xor_table_9[1]),
                (s * out, xor_table_9[2]),
            ]
        });

        meta.lookup("XOR_lookup_10", |meta| {
            let s = meta.query_selector(s_xor_10);
            let lhs = meta.query_advice(col_a, Rotation::cur());
            let rhs = meta.query_advice(col_b, Rotation::cur());
            let out = meta.query_advice(col_c, Rotation::cur());
            vec![
                (s.clone() * lhs, xor_table_10[0]),
                (s.clone() * rhs, xor_table_10[1]),
                (s * out, xor_table_10[2]),
            ]
        });

        meta.lookup("XOR_lookup_11", |meta| {
            let s = meta.query_selector(s_xor_11);
            let lhs = meta.query_advice(col_a, Rotation::cur());
            let rhs = meta.query_advice(col_b, Rotation::cur());
            let out = meta.query_advice(col_c, Rotation::cur());
            vec![
                (s.clone() * lhs, xor_table_11[0]),
                (s.clone() * rhs, xor_table_11[1]),
                (s * out, xor_table_11[2]),
            ]
        });

        meta.lookup("XOR_lookup_12", |meta| {
            let s = meta.query_selector(s_xor_12);
            let lhs = meta.query_advice(col_a, Rotation::cur());
            let rhs = meta.query_advice(col_b, Rotation::cur());
            let out = meta.query_advice(col_c, Rotation::cur());
            vec![
                (s.clone() * lhs, xor_table_12[0]),
                (s.clone() * rhs, xor_table_12[1]),
                (s * out, xor_table_12[2]),
            ]
        });

        meta.lookup("XOR_lookup_13", |meta| {
            let s = meta.query_selector(s_xor_13);
            let lhs = meta.query_advice(col_a, Rotation::cur());
            let rhs = meta.query_advice(col_b, Rotation::cur());
            let out = meta.query_advice(col_c, Rotation::cur());
            vec![
                (s.clone() * lhs, xor_table_13[0]),
                (s.clone() * rhs, xor_table_13[1]),
                (s * out, xor_table_13[2]),
            ]
        });

        meta.lookup("XOR_lookup_14", |meta| {
            let s = meta.query_selector(s_xor_14);
            let lhs = meta.query_advice(col_a, Rotation::cur());
            let rhs = meta.query_advice(col_b, Rotation::cur());
            let out = meta.query_advice(col_c, Rotation::cur());
            vec![
                (s.clone() * lhs, xor_table_14[0]),
                (s.clone() * rhs, xor_table_14[1]),
                (s * out, xor_table_14[2]),
            ]
        });

        FibonacciConfig {
            advice: [col_a, col_b, col_c],
            s_add,
            s_xor,
            s_xor_1,
            s_xor_2,
            s_xor_3,
            s_xor_4,
            s_xor_5,
            s_xor_6,
            s_xor_7,
            s_xor_8,
            s_xor_9,
            s_xor_10,
            s_xor_11,
            s_xor_12,
            s_xor_13,
            s_xor_14,
            s_range,
            s_range_1,
            range_check_table,
            range_check_table_1,
            xor_table,
            xor_table_1,
            xor_table_2,
            xor_table_3,
            xor_table_4,
            xor_table_5,
            xor_table_6,
            xor_table_7,
            xor_table_8,
            xor_table_9,
            xor_table_10,
            xor_table_11,
            xor_table_12,
            xor_table_13,
            xor_table_14,
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
                            || Value::known(F::from(6 - lhs - 1)),
                        )?;
                        table.assign_cell(
                            || "rhs",
                            self.config.xor_table[1],
                            idx,
                            || Value::known(F::from(6 - rhs - 1)),
                        )?;
                        table.assign_cell(
                            || "lhs ^ rhs",
                            self.config.xor_table[2],
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
                            || Value::known(F::from(lhs)),
                        )?;
                        table.assign_cell(
                            || "rhs",
                            self.config.xor_table_1[1],
                            idx,
                            || Value::known(F::from(rhs)),
                        )?;
                        table.assign_cell(
                            || "lhs ^ rhs",
                            self.config.xor_table_1[2],
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

    fn load_xor_table_2(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "xor_table_2",
            |mut table| {
                let mut idx = 0;
                for lhs in 0..6 {
                    for rhs in 0..6 {
                        table.assign_cell(
                            || "lhs",
                            self.config.xor_table_2[0],
                            idx,
                            || Value::known(F::from(lhs)),
                        )?;
                        table.assign_cell(
                            || "rhs",
                            self.config.xor_table_2[1],
                            idx,
                            || Value::known(F::from(rhs)),
                        )?;
                        table.assign_cell(
                            || "lhs ^ rhs",
                            self.config.xor_table_2[2],
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

    fn load_xor_table_3(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "xor_table_3",
            |mut table| {
                let mut idx = 0;
                for lhs in 0..6 {
                    for rhs in 0..6 {
                        table.assign_cell(
                            || "lhs",
                            self.config.xor_table_3[0],
                            idx,
                            || Value::known(F::from(lhs)),
                        )?;
                        table.assign_cell(
                            || "rhs",
                            self.config.xor_table_3[1],
                            idx,
                            || Value::known(F::from(rhs)),
                        )?;
                        table.assign_cell(
                            || "lhs ^ rhs",
                            self.config.xor_table_3[2],
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

    fn load_xor_table_4(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "xor_table_4",
            |mut table| {
                let mut idx = 0;
                for lhs in 0..6 {
                    for rhs in 0..6 {
                        table.assign_cell(
                            || "lhs",
                            self.config.xor_table_4[0],
                            idx,
                            || Value::known(F::from(lhs)),
                        )?;
                        table.assign_cell(
                            || "rhs",
                            self.config.xor_table_4[1],
                            idx,
                            || Value::known(F::from(rhs)),
                        )?;
                        table.assign_cell(
                            || "lhs ^ rhs",
                            self.config.xor_table_4[2],
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

    fn load_xor_table_5(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "xor_table_5",
            |mut table| {
                let mut idx = 0;
                for lhs in 0..6 {
                    for rhs in 0..6 {
                        table.assign_cell(
                            || "lhs",
                            self.config.xor_table_5[0],
                            idx,
                            || Value::known(F::from(6 - lhs - 1)),
                        )?;
                        table.assign_cell(
                            || "rhs",
                            self.config.xor_table_5[1],
                            idx,
                            || Value::known(F::from(6 - rhs - 1)),
                        )?;
                        table.assign_cell(
                            || "lhs ^ rhs",
                            self.config.xor_table_5[2],
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

    fn load_xor_table_6(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "xor_table_6",
            |mut table| {
                let mut idx = 0;
                for lhs in 0..6 {
                    for rhs in 0..6 {
                        table.assign_cell(
                            || "lhs",
                            self.config.xor_table_6[0],
                            idx,
                            || Value::known(F::from(lhs)),
                        )?;
                        table.assign_cell(
                            || "rhs",
                            self.config.xor_table_6[1],
                            idx,
                            || Value::known(F::from(rhs)),
                        )?;
                        table.assign_cell(
                            || "lhs ^ rhs",
                            self.config.xor_table_6[2],
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

    fn load_xor_table_7(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "xor_table_7",
            |mut table| {
                let mut idx = 0;
                for lhs in 0..6 {
                    for rhs in 0..6 {
                        table.assign_cell(
                            || "lhs",
                            self.config.xor_table_7[0],
                            idx,
                            || Value::known(F::from(lhs)),
                        )?;
                        table.assign_cell(
                            || "rhs",
                            self.config.xor_table_7[1],
                            idx,
                            || Value::known(F::from(rhs)),
                        )?;
                        table.assign_cell(
                            || "lhs ^ rhs",
                            self.config.xor_table_7[2],
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

    fn load_xor_table_8(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "xor_table_8",
            |mut table| {
                let mut idx = 0;
                for lhs in 0..6 {
                    for rhs in 0..6 {
                        table.assign_cell(
                            || "lhs",
                            self.config.xor_table_8[0],
                            idx,
                            || Value::known(F::from(lhs)),
                        )?;
                        table.assign_cell(
                            || "rhs",
                            self.config.xor_table_8[1],
                            idx,
                            || Value::known(F::from(rhs)),
                        )?;
                        table.assign_cell(
                            || "lhs ^ rhs",
                            self.config.xor_table_8[2],
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

    fn load_xor_table_9(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "xor_table_9",
            |mut table| {
                let mut idx = 0;
                for lhs in 0..6 {
                    for rhs in 0..6 {
                        table.assign_cell(
                            || "lhs",
                            self.config.xor_table_9[0],
                            idx,
                            || Value::known(F::from(lhs)),
                        )?;
                        table.assign_cell(
                            || "rhs",
                            self.config.xor_table_9[1],
                            idx,
                            || Value::known(F::from(rhs)),
                        )?;
                        table.assign_cell(
                            || "lhs ^ rhs",
                            self.config.xor_table_9[2],
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

    fn load_xor_table_10(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "xor_table_10",
            |mut table| {
                let mut idx = 0;
                for lhs in 0..6 {
                    for rhs in 0..6 {
                        table.assign_cell(
                            || "lhs",
                            self.config.xor_table_10[0],
                            idx,
                            || Value::known(F::from(6 - lhs - 1)),
                        )?;
                        table.assign_cell(
                            || "rhs",
                            self.config.xor_table_10[1],
                            idx,
                            || Value::known(F::from(6 - rhs - 1)),
                        )?;
                        table.assign_cell(
                            || "lhs ^ rhs",
                            self.config.xor_table_10[2],
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

    fn load_xor_table_11(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "xor_table_11",
            |mut table| {
                let mut idx = 0;
                for lhs in 0..6 {
                    for rhs in 0..6 {
                        table.assign_cell(
                            || "lhs",
                            self.config.xor_table_11[0],
                            idx,
                            || Value::known(F::from(lhs)),
                        )?;
                        table.assign_cell(
                            || "rhs",
                            self.config.xor_table_11[1],
                            idx,
                            || Value::known(F::from(rhs)),
                        )?;
                        table.assign_cell(
                            || "lhs ^ rhs",
                            self.config.xor_table_11[2],
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

    fn load_xor_table_12(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "xor_table_12",
            |mut table| {
                let mut idx = 0;
                for lhs in 0..6 {
                    for rhs in 0..6 {
                        table.assign_cell(
                            || "lhs",
                            self.config.xor_table_12[0],
                            idx,
                            || Value::known(F::from(lhs)),
                        )?;
                        table.assign_cell(
                            || "rhs",
                            self.config.xor_table_12[1],
                            idx,
                            || Value::known(F::from(rhs)),
                        )?;
                        table.assign_cell(
                            || "lhs ^ rhs",
                            self.config.xor_table_12[2],
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

    fn load_xor_table_13(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "xor_table_13",
            |mut table| {
                let mut idx = 0;
                for lhs in 0..6 {
                    for rhs in 0..6 {
                        table.assign_cell(
                            || "lhs",
                            self.config.xor_table_13[0],
                            idx,
                            || Value::known(F::from(lhs)),
                        )?;
                        table.assign_cell(
                            || "rhs",
                            self.config.xor_table_13[1],
                            idx,
                            || Value::known(F::from(rhs)),
                        )?;
                        table.assign_cell(
                            || "lhs ^ rhs",
                            self.config.xor_table_13[2],
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

    fn load_xor_table_14(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "xor_table_14",
            |mut table| {
                let mut idx = 0;
                for lhs in 0..6 {
                    for rhs in 0..6 {
                        table.assign_cell(
                            || "lhs",
                            self.config.xor_table_14[0],
                            idx,
                            || Value::known(F::from(lhs)),
                        )?;
                        table.assign_cell(
                            || "rhs",
                            self.config.xor_table_14[1],
                            idx,
                            || Value::known(F::from(rhs)),
                        )?;
                        table.assign_cell(
                            || "lhs ^ rhs",
                            self.config.xor_table_14[2],
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

    #[allow(clippy::type_complexity)]
    pub fn assign(
        &self,
        mut layouter: impl Layouter<F>,
        nrows: usize,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "entire circuit",
            |mut region| {
                self.config.s_add.enable(&mut region, 0)?;
                self.config.s_range.enable(&mut region, 0)?;
                self.config.s_range_1.enable(&mut region, 0)?;
                // assign first row
                let a_cell = region.assign_advice_from_instance(
                    || "1",
                    self.config.instance,
                    0,
                    self.config.advice[0],
                    0,
                )?;
                let mut b_cell = region.assign_advice_from_instance(
                    || "1",
                    self.config.instance,
                    1,
                    self.config.advice[1],
                    0,
                )?;
                let mut c_cell = region.assign_advice(
                    || "add",
                    self.config.advice[2],
                    0,
                    || a_cell.value().copied() + b_cell.value(),
                )?;

                // assign the rest of rows
                for row in 1..nrows {
                    b_cell.copy_advice(|| "a", &mut region, self.config.advice[0], row)?;
                    c_cell.copy_advice(|| "b", &mut region, self.config.advice[1], row)?;

                    let new_c_cell = if row % 2 == 0 {
                        self.config.s_add.enable(&mut region, row)?;
                        self.config.s_range.enable(&mut region, row)?;
                        self.config.s_range_1.enable(&mut region, row)?;
                        region.assign_advice(
                            || "advice",
                            self.config.advice[2],
                            row,
                            || b_cell.value().copied() + c_cell.value(),
                        )?
                    } else {
                        self.config.s_xor_14.enable(&mut region, row)?;
                        self.config.s_xor_13.enable(&mut region, row)?;
                        self.config.s_xor_12.enable(&mut region, row)?;
                        self.config.s_xor_11.enable(&mut region, row)?;
                        self.config.s_xor_10.enable(&mut region, row)?;
                        self.config.s_xor_9.enable(&mut region, row)?;
                        self.config.s_xor_8.enable(&mut region, row)?;
                        self.config.s_xor_7.enable(&mut region, row)?;
                        self.config.s_xor_6.enable(&mut region, row)?;
                        self.config.s_xor_5.enable(&mut region, row)?;
                        self.config.s_xor_4.enable(&mut region, row)?;
                        self.config.s_xor_3.enable(&mut region, row)?;
                        self.config.s_xor_2.enable(&mut region, row)?;
                        self.config.s_xor_1.enable(&mut region, row)?;
                        self.config.s_xor.enable(&mut region, row)?;
                        self.config.s_range.enable(&mut region, row)?;
                        self.config.s_range_1.enable(&mut region, row)?;
                        region.assign_advice(
                            || "advice",
                            self.config.advice[2],
                            row,
                            || {
                                b_cell.value().and_then(|a| {
                                    c_cell.value().map(|b| {
                                        let a_val = u64::from_str_radix(
                                            format!("{:?}", a).strip_prefix("0x").unwrap(),
                                            16,
                                        )
                                        .unwrap();
                                        let b_val = u64::from_str_radix(
                                            format!("{:?}", b).strip_prefix("0x").unwrap(),
                                            16,
                                        )
                                        .unwrap();
                                        F::from(a_val ^ b_val)
                                    })
                                })
                            },
                        )?
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
        cell: AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.config.instance, row)
    }
}

#[derive(Default)]
pub struct MyCircuit<F: FieldExt, const SIZE: usize>(pub PhantomData<F>);

impl<F: FieldExt, const SIZE: usize> Circuit<F> for MyCircuit<F, SIZE> {
    type Config = FibonacciConfig<SIZE>;
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
        chip.load_xor_table_1(layouter.namespace(|| "lookup table"))?;
        chip.load_xor_table_2(layouter.namespace(|| "lookup table"))?;
        chip.load_xor_table_3(layouter.namespace(|| "lookup table"))?;
        chip.load_xor_table_4(layouter.namespace(|| "lookup table"))?;
        chip.load_xor_table_5(layouter.namespace(|| "lookup table"))?;
        chip.load_xor_table_6(layouter.namespace(|| "lookup table"))?;
        chip.load_xor_table_7(layouter.namespace(|| "lookup table"))?;
        chip.load_xor_table_8(layouter.namespace(|| "lookup table"))?;
        chip.load_xor_table_9(layouter.namespace(|| "lookup table"))?;
        chip.load_xor_table_10(layouter.namespace(|| "lookup table"))?;
        chip.load_xor_table_11(layouter.namespace(|| "lookup table"))?;
        chip.load_xor_table_12(layouter.namespace(|| "lookup table"))?;
        chip.load_xor_table_13(layouter.namespace(|| "lookup table"))?;
        chip.load_xor_table_14(layouter.namespace(|| "lookup table"))?;
        chip.load_table_range(layouter.namespace(|| "range table"))?;
        chip.load_table_range_1(layouter.namespace(|| "range table 1"))?;
        let out_cell = chip.assign(layouter.namespace(|| "entire table"), SIZE)?;
        chip.expose_public(layouter.namespace(|| "out"), out_cell, 2)?;

        Ok(())
    }
}
