use group::ff::PrimeField as Field;
use pse_halo2_proofs::circuit::*;
use pse_halo2_proofs::plonk::*;
use pse_halo2_proofs::poly::Rotation;
use std::marker::PhantomData;

pub struct TwoBitDecompCircuitUnderConstrained<F: Field> {
    b0: F,
    b1: F,
}

#[derive(Debug, Clone)]
pub struct TwoBitDecompCircuitConfig {
    b0: Column<Advice>,
    b1: Column<Advice>,
    x: Column<Advice>,
    i: Column<Instance>,
    s: Selector,
    s_binary_b0: Selector,
    s_binary_b1: Selector,
    binary_check_table: [TableColumn; 1],
}

impl<F: Field> Default for TwoBitDecompCircuitUnderConstrained<F> {
    fn default() -> Self {
        TwoBitDecompCircuitUnderConstrained {
            b0: F::ONE,
            b1: F::ONE,
        }
    }
}

#[derive(Debug, Clone)]

struct TwoBitDecopmChip<F: Field> {
    config: TwoBitDecompCircuitConfig,
    _marker: PhantomData<F>,
}

impl<F: Field> TwoBitDecopmChip<F> {
    pub fn construct(config: TwoBitDecompCircuitConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
    fn configure(meta: &mut ConstraintSystem<F>) -> TwoBitDecompCircuitConfig {
        let b0 = meta.advice_column();
        let b1 = meta.advice_column();
        let x = meta.advice_column();
        let i = meta.instance_column();
        let s = meta.complex_selector();
        let s_binary_b0 = meta.complex_selector();
        let s_binary_b1 = meta.complex_selector();

        meta.enable_equality(x);
        meta.enable_equality(i);

        let binary_check_table = [meta.lookup_table_column()];

        meta.lookup("BINARY_lookup", |meta| {
            let s = meta.query_selector(s);
            let lhs = meta.query_advice(b0, Rotation::cur());
            vec![(s * lhs, binary_check_table[0])]
        });

        meta.lookup("BINARY_lookup", |meta: &mut VirtualCells<'_, F>| {
            let s = meta.query_selector(s);
            let lhs = meta.query_advice(b1, Rotation::cur());
            vec![(s * lhs, binary_check_table[0])]
        });

        // define gates
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

        TwoBitDecompCircuitConfig {
            b0,
            b1,
            x,
            i,
            s,
            s_binary_b0,
            s_binary_b1,
            binary_check_table,
        }
    }
    fn load_table_binary(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_table(
            || "binary_check_table",
            |mut table| {
                for (idx, lhs) in (0..2).enumerate() {
                    table.assign_cell(
                        || "lhs",
                        self.config.binary_check_table[0],
                        idx,
                        || Value::known(F::from(lhs)),
                    )?;
                }
                Ok(())
            },
        )
    }
}

#[derive(Default)]

pub struct TwoBitDecompCircuit<F> {
    b0: F,
    b1: F,
}

impl<F: Field> Circuit<F> for TwoBitDecompCircuit<F> {
    type Config = TwoBitDecompCircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        TwoBitDecopmChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = TwoBitDecopmChip::construct(config.clone());

        chip.load_table_binary(layouter.namespace(|| "lookup table binary"))?;

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
        layouter.constrain_instance(out.cell(), config.i, 0)?;
        Ok(())
    }
}
