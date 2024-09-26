// // This is just a sample of how to import an external circuit and analyze it using the Analyzer.

// #[cfg(test)]
// #[cfg(feature = "use_pse_v1_halo2_proofs")]
// mod test {
//     use crate::circuit_analyzer::analyzer::Analyzer;
//     use crate::circuit_analyzer::halo2_proofs_libs::*;
//     use crate::io::{
//         analyzer_io_type,
//         analyzer_io_type::{AnalyzerType, LookupMethod, VerificationInput, VerificationMethod},
//     };
//     use gadgets::is_zero::{IsZeroChip, IsZeroConfig, IsZeroInstruction};
//     use std::collections::HashMap;
//     use std::marker::PhantomData;

//     macro_rules! try_test_circuit {
//         ($values:expr, $checks:expr) => {{
//             let k = usize::BITS - $values.len().leading_zeros() + 2;
//             let circuit = TestCircuit::<Fr> {
//                 values: Some($values),
//                 checks: Some($checks),
//                 _marker: PhantomData,
//             };

//             let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
//                 verification_method: VerificationMethod::Random,
//                 verification_input: VerificationInput {
//                     instance_cells: HashMap::new(),
//                     iterations: 5,
//                 },
//                 lookup_method: LookupMethod::InlineConstraints,
//             };

//             let mut analyzer = Analyzer::new(
//                 &circuit,
//                 k,
//                 AnalyzerType::UnderconstrainedCircuit,
//                 Some(&analyzer_input),
//             )
//             .unwrap();

//             let _output_status = analyzer
//                 .analyze_underconstrained(&analyzer_input)
//                 .unwrap()
//                 .output_status;
//         }};
//     }

//     #[test]
//     fn row_diff_is_zero() {
//         #[derive(Clone, Debug)]
//         struct TestCircuitConfig<F> {
//             q_enable: Selector,
//             value: Column<Advice>,
//             check: Column<Advice>,
//             is_zero: IsZeroConfig<F>,
//         }

//         #[derive(Default)]
//         struct TestCircuit<F: FieldExt> {
//             values: Option<Vec<u64>>,
//             // checks[i] = is_zero(values[i + 1] - values[i])
//             checks: Option<Vec<bool>>,
//             _marker: PhantomData<F>,
//         }

//         impl<F: FieldExt> Circuit<F> for TestCircuit<F> {
//             type Config = TestCircuitConfig<F>;
//             type FloorPlanner = SimpleFloorPlanner;

//             fn without_witnesses(&self) -> Self {
//                 Self::default()
//             }

//             fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
//                 let q_enable = meta.complex_selector();
//                 let value = meta.advice_column();
//                 let value_diff_inv = meta.advice_column();
//                 let check = meta.advice_column();

//                 let is_zero = IsZeroChip::configure(
//                     meta,
//                     |meta| meta.query_selector(q_enable),
//                     |meta| {
//                         let value_prev = meta.query_advice(value, Rotation::prev());
//                         let value_cur = meta.query_advice(value, Rotation::cur());
//                         value_cur - value_prev
//                     },
//                     value_diff_inv,
//                 );

//                 let config = Self::Config {
//                     q_enable,
//                     value,
//                     check,
//                     is_zero,
//                 };

//                 meta.create_gate("check is_zero", |meta| {
//                     let q_enable = meta.query_selector(q_enable);

//                     // This verifies is_zero is calculated correctly
//                     let check = meta.query_advice(config.check, Rotation::cur());

//                     vec![q_enable * (config.is_zero.is_zero_expression.clone() - check)]
//                 });

//                 config
//             }

//             fn synthesize(
//                 &self,
//                 config: Self::Config,
//                 mut layouter: impl Layouter<F>,
//             ) -> Result<(), Error> {
//                 let chip = IsZeroChip::construct(config.is_zero.clone());

//                 let values: Vec<_> = self
//                     .values
//                     .as_ref()
//                     .map(|values| values.iter().map(|value| F::from(*value)).collect())
//                     .ok_or(Error::Synthesis)?;
//                 let checks = self.checks.as_ref().ok_or(Error::Synthesis)?;
//                 let (first_value, values) = values.split_at(1);
//                 let first_value = first_value[0];

//                 layouter.assign_region(
//                     || "witness",
//                     |mut region| {
//                         region.assign_advice(
//                             || "first row value",
//                             config.value,
//                             0,
//                             || Value::known(first_value),
//                         )?;

//                         let mut value_prev = first_value;
//                         for (idx, (value, check)) in values.iter().zip(checks).enumerate() {
//                             region.assign_advice(
//                                 || "check",
//                                 config.check,
//                                 idx + 1,
//                                 || Value::known(F::from(*check as u64)),
//                             )?;
//                             region.assign_advice(
//                                 || "value",
//                                 config.value,
//                                 idx + 1,
//                                 || Value::known(*value),
//                             )?;

//                             config.q_enable.enable(&mut region, idx + 1)?;
//                             chip.assign(&mut region, idx + 1, Value::known(*value - value_prev))?;

//                             value_prev = *value;
//                         }

//                         Ok(())
//                     },
//                 )
//             }
//         }

//         try_test_circuit!(vec![1, 2, 3, 4, 5], vec![false, false, false, false]);
//     }
// }
