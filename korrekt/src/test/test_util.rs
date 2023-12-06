use itertools::Itertools;
use std::marker::PhantomData;
use strum::IntoEnumIterator;

use zkevm_circuits::evm_circuit::{
    param::{MAX_STEP_HEIGHT, STEP_WIDTH},
    step::{ExecutionState, Step},
    table::{FixedTableTag, Table},
    util::{constraint_builder::ConstraintBuilder, rlc, CachedRegion, CellType, StoredExpression},
};

use crate::circuit_analyzer::analyzer::Analyzer;
use crate::io::{
    analyzer_io_type,
    analyzer_io_type::{AnalyzerOutputStatus, VerificationInput, VerificationMethod},
};

use eth_types::{Field, Word, U256};
use halo2_proofs::{
    arithmetic::FieldExt,
    circuit::{Layouter, SimpleFloorPlanner, Value},
    dev::MockProver,
    halo2curves::bn256,
    halo2curves::bn256::Fr as Fp,
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Selector,Expression},
    poly::Rotation,
};

use num::{BigInt, Num};

use zkevm_circuits::table::LookupTable;
use zkevm_circuits::util::power_of_randomness_from_instance;

pub(crate) const WORD_LOW_MAX: Word = U256([u64::MAX, u64::MAX, 0, 0]);
pub(crate) const WORD_HIGH_MAX: Word = U256([0, 0, u64::MAX, u64::MAX]);
// Maximum field value in bn256: bn256::MODULES - 1
pub(crate) const WORD_CELL_MAX: Word = U256([
    0x43e1f593f0000000,
    0x2833e84879b97091,
    0xb85045b68181585d,
    0x30644e72e131a029,
]);

pub(crate) fn generate_power_of_randomness<F: Field>(randomness: F) -> Vec<F> {
    (1..32).map(|exp| randomness.pow(&[exp, 0, 0, 0])).collect()
}

pub(crate) trait MathGadgetContainer<F: Field>: Clone {
    fn configure_gadget_container(cb: &mut ConstraintBuilder<F>) -> Self
    where
        Self: Sized;

    fn assign_gadget_container(
        &self,
        witnesses: &[Word],
        region: &mut CachedRegion<'_, '_, F>,
    ) -> Result<(), Error>;
}

#[derive(Debug, Clone)]
pub(crate) struct UnitTestMathGadgetBaseCircuitConfig<F: Field, G>
where
    G: MathGadgetContainer<F>,
{
    q_usable: Selector,
    fixed_table: [Column<Fixed>; 4],
    advices: [Column<Advice>; STEP_WIDTH],
    step: Step<F>,
    stored_expressions: Vec<StoredExpression<F>>,
    math_gadget_container: G,
    _marker: PhantomData<F>,
    power_of_randomness: [Expression<F>; 31],
}

pub(crate) struct UnitTestMathGadgetBaseCircuit<F, G> {
    size: usize,
    witnesses: Vec<Word>,
    randomness: F,
    _marker: PhantomData<G>,
}

impl<F: Field, G> UnitTestMathGadgetBaseCircuit<F, G> {
    fn new(size: usize, witnesses: Vec<Word>, randomness: F) -> Self {
        UnitTestMathGadgetBaseCircuit {
            size,
            witnesses,
            randomness,
            _marker: PhantomData,
        }
    }
}

impl<F: Field, G: MathGadgetContainer<F>> Circuit<F> for UnitTestMathGadgetBaseCircuit<F, G> {
    type Config = UnitTestMathGadgetBaseCircuitConfig<F, G>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        UnitTestMathGadgetBaseCircuit {
            size: 0,
            witnesses: vec![],
            randomness: F::from(123456u64),
            _marker: PhantomData,
        }
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let q_usable = meta.selector();
        let fixed_table = [(); 4].map(|_| meta.fixed_column());
        let advices = [(); STEP_WIDTH].map(|_| meta.advice_column());
        let step_curr = Step::new(meta, advices, 0);
        let step_next = Step::new(meta, advices, 1);
        let power_of_randomness = power_of_randomness_from_instance(meta);

        let mut cb = ConstraintBuilder::new(
            step_curr.clone(),
            step_next,
            &power_of_randomness,
            ExecutionState::STOP,
        );
        let math_gadget_container = G::configure_gadget_container(&mut cb);
        let (constraints, _, stored_expressions, _) = cb.build();

        if !constraints.is_empty() {
            let step_constraints = constraints;
            meta.create_gate("MathGadgetTestContainer", |meta| {
                let q_usable = meta.query_selector(q_usable);
                step_constraints
                    .into_iter()
                    .map(move |(name, constraint)| (name, q_usable.clone() * constraint))
            });
        }

        let cell_manager = step_curr.cell_manager.clone();
        for column in cell_manager.columns().iter() {
            if let CellType::Lookup(table) = column.cell_type {
                if table == Table::Fixed {
                    let name = format!("{:?}", table);
                    meta.lookup_any(Box::leak(name.into_boxed_str()), |meta| {
                        let table_expressions = fixed_table.table_exprs(meta);
                        vec![(
                            column.expr.clone(),
                            rlc::expr(&table_expressions, &power_of_randomness),
                        )]
                    });
                }
            }
        }

        UnitTestMathGadgetBaseCircuitConfig::<F, G> {
            q_usable,
            fixed_table,
            advices,
            step: step_curr,
            stored_expressions,
            math_gadget_container,
            _marker: PhantomData,
            power_of_randomness,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "assign test container",
            |mut region| {
                let offset = 0;
                config.q_usable.enable(&mut region, offset)?;
                let power_of_randomness = generate_power_of_randomness(self.randomness);
                let cached_region = &mut CachedRegion::<'_, '_, F>::new(
                    &mut region,
                    power_of_randomness.try_into().unwrap(),
                    STEP_WIDTH,
                    MAX_STEP_HEIGHT * 3,
                    config.advices[0].index(), // TODO
                    offset,
                );
                config.step.state.execution_state.assign(
                    cached_region,
                    offset,
                    ExecutionState::STOP as usize,
                )?;
                config
                    .math_gadget_container
                    .assign_gadget_container(&self.witnesses, cached_region)?;
                for stored_expr in &config.stored_expressions {
                    stored_expr.assign(cached_region, offset)?;
                }
                Ok(())
            },
        )?;

        // assign fixed range tables only as they are the only tables referred by a
        // specfic math gadget -- ConstantDivisionGadget.
        layouter.assign_region(
            || "fixed table",
            |mut region| {
                for (offset, row) in std::iter::once([F::zero(); 4])
                    .chain(
                        FixedTableTag::iter()
                            .filter(|t| {
                                matches!(
                                    t,
                                    FixedTableTag::Range5
                                        | FixedTableTag::Range16
                                        | FixedTableTag::Range32
                                        | FixedTableTag::Range64
                                        | FixedTableTag::Range256
                                        | FixedTableTag::Range512
                                        | FixedTableTag::Range1024
                                )
                            })
                            .flat_map(|tag| tag.build()),
                    )
                    .enumerate()
                {
                    for (column, value) in config.fixed_table.iter().zip_eq(row) {
                        region.assign_fixed(|| "", *column, offset, || Value::known(value))?;
                    }
                }

                Ok(())
            },
        )
    }
}

/// This fn test_math_gadget_container takes math gadget container and run a
/// container based circuit. All test logic should be included in the container,
/// and witness words are used for both input & output data. How to deal with
/// the witness words is left to each container.
pub(crate) fn test_math_gadget_container<F: Field, G: MathGadgetContainer<F>>(
    witnesses: Vec<Word>,
    expected_success: bool,
) {
    const K: usize = 12;
    let randomness = F::from(123456u64);
    let power_of_randomness_instances: Vec<Vec<F>> = generate_power_of_randomness(randomness)
        .iter()
        .map(|power_of_randomn: &F| vec![*power_of_randomn; (1 << K) - 64])
        .collect();
    let circuit = UnitTestMathGadgetBaseCircuit::<F, G>::new(K, witnesses, randomness);

    let prover = MockProver::<F>::run(K as u32, &circuit, power_of_randomness_instances).unwrap();
    let modulus = bn256::fr::MODULUS_STR;
    let without_prefix = modulus.trim_start_matches("0x");
    let prime = BigInt::from_str_radix(without_prefix, 16)
        .unwrap()
        .to_string();

    let mut analyzer = Analyzer::from(&circuit);

    let instance_cols = analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
    let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
        verification_method: VerificationMethod::Random,
        verification_input: VerificationInput {
            instances_string: instance_cols,
            iterations: 5,
        },
    };
    println!("Output{:?}","1000000");
    let output_status = analyzer
        .analyze_underconstrained(analyzer_input, prover.fixed, &prime)
        .unwrap()
        .output_status;
    assert!(output_status.eq(&AnalyzerOutputStatus::Underconstrained));
    // if expected_success {
    //     assert_eq!(prover.verify(), Ok(()));
    // } else {
    //     assert_ne!(prover.verify(), Ok(()));
    // }
}

/// A simple macro for less code & better readability
macro_rules! try_test {
    ($base_class:ty, $witnesses:expr, $expect_success:expr $(,)?) => {{
        test_math_gadget_container::<Fr, $base_class>($witnesses.to_vec(), $expect_success)
    }};
}

#[cfg(test)]
pub(crate) use try_test;
