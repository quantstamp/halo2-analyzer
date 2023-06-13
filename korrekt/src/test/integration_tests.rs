#[cfg(test)]
mod tests {
    use crate::circuit_analyzer::analyzer::Analyzer;
    use crate::io::{
        analyzer_io_type,
        analyzer_io_type::{AnalyzerOutputStatus, VerificationInput, VerificationMethod},
    };
    use crate::sample_circuits;
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::halo2curves::bn256::Fr;
    use std::collections::HashMap;
    use std::marker::PhantomData;

    #[test]
    fn create_two_bit_decomp_circuit() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp::TwoBitDecompCircuit::<Fr>::default(
            );
        let k = 5;

        let public_input = Fr::from(3);
        //mockprover verify passes
        let prover = MockProver::<Fr>::run(k, &circuit, vec![vec![public_input]]).unwrap();
        assert!(prover.verify().eq(&Ok(())));
    }
    #[test]
    fn create_multtrow_two_bit_decomp_circuit() {
        let circuit = sample_circuits::bit_decomposition::two_bit_decomp_multirow::MultiRowTwoBitDecompCircuit::<Fr>::default();
        let k = 5;

        let public_input = Fr::from(3);
        //mockprover verify passes
        let prover = MockProver::<Fr>::run(k, &circuit, vec![vec![public_input]]).unwrap();
        assert!(prover.verify().eq(&Ok(())));
    }

    #[test]
    fn create_analyzer_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp::TwoBitDecompCircuit::<Fr>::default(
            );
        let analyzer = Analyzer::from(&circuit);
        assert!(analyzer.cs.gates.len().eq(&3));
        assert!(analyzer.cs.degree().eq(&3));
        assert!(analyzer.cs.num_advice_columns().eq(&3));
        assert!(analyzer.cs.num_instance_columns().eq(&1));
        assert!(analyzer.cs.num_selectors.eq(&1));
        assert!(analyzer.cs.num_fixed_columns().eq(&0));
    }

    #[test]
    fn extract_instance_cols_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp::TwoBitDecompCircuit::<Fr>::default(
            );
        let mut analyzer = Analyzer::from(&circuit);

        let instance_cols = analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
        assert!(instance_cols.len().eq(&1));
        assert!(instance_cols.iter().next().unwrap().0.eq("A-0-2-0"));
        assert!(instance_cols.iter().next().unwrap().1.eq(&0));
    }

    #[test]
    fn set_user_input_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp::TwoBitDecompCircuit::<Fr>::default(
            );
        let mut analyzer = Analyzer::from(&circuit);
        let instance_cols = analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
        assert!(instance_cols.len().eq(&1));
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string: instance_cols,
                iterations: 5,
            },
        };
        assert!(analyzer_input
            .verification_method
            .eq(&VerificationMethod::Random));
        assert!(analyzer_input.verification_input.iterations.eq(&5));
    }

    #[test]
    fn not_under_constrained_enough_random_input_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp::TwoBitDecompCircuit::<Fr>::default(
            );
        let mut analyzer = Analyzer::from(&circuit);

        let instance_cols = analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
        assert!(instance_cols.len().eq(&1));

        let k: u32 = 11;

        let public_input = vec![Fr::from(3)];

        let prover: MockProver<Fr> = MockProver::run(k, &circuit, vec![public_input]).unwrap();

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string: instance_cols,
                iterations: 5,
            },
        };
        let output_status = analyzer
            .analyze_underconstrained(analyzer_input, prover.fixed)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrained));
    }

    #[test]
    fn not_under_constrained_not_enough_input_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp::TwoBitDecompCircuit::<Fr>::default(
            );
        let mut analyzer = Analyzer::from(&circuit);

        let instance_cols = analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
        assert!(instance_cols.len().eq(&1));
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string: instance_cols,
                iterations: 1,
            },
        };
        let k: u32 = 11;

        let public_input = vec![Fr::from(3)];

        let prover: MockProver<Fr> = MockProver::run(k, &circuit, vec![public_input]).unwrap();

        let output_status = analyzer
            .analyze_underconstrained(analyzer_input, prover.fixed)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }

    #[test]
    fn not_under_constrained_not_enough_input_1_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp::TwoBitDecompCircuit::<Fr>::default(
            );
        let mut analyzer = Analyzer::from(&circuit);

        let instance_cols = analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
        assert!(instance_cols.len().eq(&1));
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string: instance_cols,
                iterations: 4,
            },
        };
        let k: u32 = 11;

        let public_input = vec![Fr::from(3)];

        let prover: MockProver<Fr> = MockProver::run(k, &circuit, vec![public_input]).unwrap();

        let output_status = analyzer
            .analyze_underconstrained(analyzer_input, prover.fixed)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }

    #[test]
    fn not_under_constrained_exact_spec_input_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp::TwoBitDecompCircuit::<Fr>::default(
            );
        let mut analyzer = Analyzer::from(&circuit);

        let instance_cols = analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
        assert!(instance_cols.len().eq(&1));
        let mut specified_instance_cols = HashMap::new();
        for var in instance_cols.iter() {
            specified_instance_cols.insert(var.0.clone(), 3);
        }

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput {
                instances_string: specified_instance_cols,
                iterations: 1,
            },
        };
        let k: u32 = 11;

        let public_input = vec![Fr::from(3)];

        let prover: MockProver<Fr> = MockProver::run(k, &circuit, vec![public_input]).unwrap();

        let output_status = analyzer
            .analyze_underconstrained(analyzer_input, prover.fixed)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }

    #[test]
    fn not_under_constrained_not_exact_spec_input_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp::TwoBitDecompCircuit::<Fr>::default(
            );
        let mut analyzer = Analyzer::from(&circuit);

        let instance_cols = analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
        assert!(instance_cols.len().eq(&1));
        let mut specified_instance_cols = HashMap::new();
        for var in instance_cols.iter() {
            specified_instance_cols.insert(var.0.clone(), 1);
        }

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput {
                instances_string: specified_instance_cols,
                iterations: 1,
            },
        };
        let k: u32 = 11;

        let public_input = vec![Fr::from(3)];

        let prover: MockProver<Fr> = MockProver::run(k, &circuit, vec![public_input]).unwrap();

        let output_status = analyzer
            .analyze_underconstrained(analyzer_input, prover.fixed)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }

    #[test]
    fn under_constrained_enough_random_input_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp::TwoBitDecompCircuitUnderConstrained::<
                Fr,
            >::default();
        let mut analyzer = Analyzer::from(&circuit);

        let instance_cols = analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
        assert!(instance_cols.len().eq(&1));
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string: instance_cols,
                iterations: 5,
            },
        };
        let k: u32 = 11;

        let public_input = vec![Fr::from(3)];

        let prover: MockProver<Fr> = MockProver::run(k, &circuit, vec![public_input]).unwrap();

        let output_status = analyzer
            .analyze_underconstrained(analyzer_input, prover.fixed)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::Underconstrained));
    }

    #[test]
    fn under_constrained_not_enough_random_input_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp::TwoBitDecompCircuitUnderConstrained::<
                Fr,
            >::default();
        let mut analyzer = Analyzer::from(&circuit);

        let instance_cols = analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
        assert!(instance_cols.len().eq(&1));
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string: instance_cols,
                iterations: 1,
            },
        };
        let k: u32 = 11;

        let public_input = vec![Fr::from(3)];

        let prover: MockProver<Fr> = MockProver::run(k, &circuit, vec![public_input]).unwrap();

        let output_status = analyzer
            .analyze_underconstrained(analyzer_input, prover.fixed)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::Underconstrained));
    }

    #[test]
    fn under_constrained_exact_spec_input_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp::TwoBitDecompCircuitUnderConstrained::<
                Fr,
            >::default();
        let mut analyzer = Analyzer::from(&circuit);

        let instance_cols = analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());

        assert!(instance_cols.len().eq(&1));
        let mut specified_instance_cols = HashMap::new();
        for var in instance_cols.iter() {
            specified_instance_cols.insert(var.0.clone(), 3);
        }

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput {
                instances_string: specified_instance_cols,
                iterations: 1,
            },
        };
        let k: u32 = 11;

        let public_input = vec![Fr::from(3)];

        let prover: MockProver<Fr> = MockProver::run(k, &circuit, vec![public_input]).unwrap();

        let output_status = analyzer
            .analyze_underconstrained(analyzer_input, prover.fixed)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::Underconstrained));
    }

    #[test]
    fn under_constrained_not_exact_spec_input_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp::TwoBitDecompCircuitUnderConstrained::<
                Fr,
            >::default();
        let mut analyzer = Analyzer::from(&circuit);

        let instance_cols = analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());

        assert!(instance_cols.len().eq(&1));
        let mut specified_instance_cols = HashMap::new();
        for var in instance_cols.iter() {
            specified_instance_cols.insert(var.0.clone(), 1);
        }

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput {
                instances_string: specified_instance_cols,
                iterations: 1,
            },
        };
        let k: u32 = 11;

        let public_input = vec![Fr::from(3)];

        let prover: MockProver<Fr> = MockProver::run(k, &circuit, vec![public_input]).unwrap();

        let output_status = analyzer
            .analyze_underconstrained(analyzer_input, prover.fixed)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::Underconstrained));
    }

    #[test]
    fn analyze_unused_columns_test() {
        let circuit: sample_circuits::bit_decomposition::add_multiplication::AddMultCircuit<Fr> =
            sample_circuits::bit_decomposition::add_multiplication::AddMultCircuit::default();
        let mut analyzer = Analyzer::from(&circuit);
        let output_status = analyzer.analyze_unused_columns().unwrap().output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::UnusedColumns));
        assert!(analyzer.log().len().gt(&0))
    }

    #[test]
    fn analyze_unused_custom_gates_test() {
        let circuit: sample_circuits::bit_decomposition::add_multiplication::AddMultCircuit<Fr> =
            sample_circuits::bit_decomposition::add_multiplication::AddMultCircuit::default();
        let mut analyzer = Analyzer::from(&circuit);
        let output_status = analyzer
            .analyze_unused_custom_gates()
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::UnusedCustomGates));
        assert!(analyzer.log().len().gt(&0))
    }

    #[test]
    fn analyze_unconstrained_cells() {
        let circuit: sample_circuits::bit_decomposition::add_multiplication::AddMultCircuit<Fr> =
            sample_circuits::bit_decomposition::add_multiplication::AddMultCircuit::default();
        let mut analyzer = Analyzer::from(&circuit);
        let output_status = analyzer
            .analyze_unconstrained_cells()
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::UnconstrainedCells));
        assert!(analyzer.log().len().gt(&0))
    }

    #[test]
    fn analyze_underconstrained_fibonacci_test() {
        let circuit: sample_circuits::copy_constraint::fibonacci::FibonacciCircuit<_> =
            sample_circuits::copy_constraint::fibonacci::FibonacciCircuit::<Fr>(PhantomData);
        let mut analyzer = Analyzer::from(&circuit);

        let instance_cols = analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string: instance_cols,
                iterations: 5,
            },
        };
        let k: u32 = 11;

        let public_input = vec![Fr::from(3)];

        let prover: MockProver<Fr> = MockProver::run(k, &circuit, vec![public_input]).unwrap();

        let output_status = analyzer
            .analyze_underconstrained(analyzer_input, prover.fixed)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::Underconstrained));
    }

    #[test]
    fn analyze_underconstrained_single_lookup_test() {
        let circuit =
            sample_circuits::lookup_circuits::lookup_underconstrained::MyCircuit::<Fr>(PhantomData);
        let mut analyzer = Analyzer::from(&circuit);

        let instance_cols = analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string: instance_cols,
                iterations: 5,
            },
        };
        let k = 11;

        let a = Fr::from(1);
        let b = Fr::from(1);
        let out = Fr::from(21);

        let public_input = vec![a, b, out];
        let prover: MockProver<Fr> = MockProver::run(k, &circuit, vec![public_input]).unwrap();
        let output_status = analyzer
            .analyze_underconstrained(analyzer_input, prover.fixed)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::Underconstrained));
    }

    #[test]
    fn analyze_underconstrained_multiple_lookup_test() {
        let circuit =
            sample_circuits::lookup_circuits::multiple_lookups::MyCircuit::<Fr>(PhantomData);
        let mut analyzer = Analyzer::from(&circuit);

        let instance_cols = analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string: instance_cols,
                iterations: 5,
            },
        };

        let k = 11;

        let a = Fr::from(1);
        let b = Fr::from(1);
        let out = Fr::from(21);

        let public_input = vec![a, b, out];
        let prover: MockProver<Fr> = MockProver::run(k, &circuit, vec![public_input]).unwrap();
        let output_status = analyzer
            .analyze_underconstrained(analyzer_input, prover.fixed)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::Underconstrained));
    }
    #[test]
    fn analyze_not_underconstrained_lookup_test() {
        let circuit =
            sample_circuits::lookup_circuits::multiple_lookups::MyCircuit::<Fr>(PhantomData);
        let mut analyzer = Analyzer::from(&circuit);

        let instance_cols = analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
        assert!(instance_cols.len().eq(&1));
        let mut specified_instance_cols = HashMap::new();
        specified_instance_cols.insert("A-0-2-7".to_owned(), 21);
        specified_instance_cols.insert("I-0-0-1".to_owned(), 1);
        specified_instance_cols.insert("I-0-0-0".to_owned(), 1);

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput {
                instances_string: specified_instance_cols,
                iterations: 1,
            },
        };
        let k = 11;

        let a = Fr::from(1); // F[0]
        let b = Fr::from(1); // F[1]
        let out = Fr::from(21); // F[9]

        let public_input = vec![a, b, out];
        let prover: MockProver<Fr> = MockProver::run(k, &circuit, vec![public_input]).unwrap();
        let output_status = analyzer
            .analyze_underconstrained(analyzer_input, prover.fixed)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }
}
