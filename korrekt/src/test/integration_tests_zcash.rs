#[cfg(test)]
#[cfg(feature = "use_zcash_halo2_proofs")]
mod tests {
    use crate::circuit_analyzer::analyzer::Analyzer;
    use crate::io::{
        analyzer_io_type,
        analyzer_io_type::{AnalyzerOutputStatus, VerificationInput, VerificationMethod},
    };
    use crate::sample_circuits::zcash as sample_circuits;
    use halo2curves::bn256;
    use zcash_halo2_proofs::pasta::Fp as Fr;

    use num::{BigInt, Num};
    use std::collections::HashMap;
    use std::marker::PhantomData;

    #[test]
    fn create_zcash_analyzer_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp_zcash::TwoBitDecompCircuit::<Fr>::default(
            );
        let k: u32 = 11;

        let mut analyzer = Analyzer::new(&circuit, k).unwrap();

        assert!(analyzer.cs.gates.len().eq(&3));
        assert!(analyzer.cs.degree().eq(&3));
        //assert!(analyzer.cs.num_advice_columns().eq(&3));
        //assert!(analyzer.cs.num_instance_columns().eq(&1));
        //assert!(analyzer.cs.num_selectors.eq(&1) || analyzer.cs.num_fixed_columns().eq(&1));
    }

    #[test]
    fn extract_instance_cols_zcash_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp_zcash::TwoBitDecompCircuit::<Fr>::default(
            );
        let k: u32 = 11;

        let mut analyzer = Analyzer::new(&circuit, k).unwrap();
        assert!(analyzer.instace_cells.len().eq(&1));
        assert!(analyzer.instace_cells.contains_key("I-0-0"));
        assert!(analyzer.instace_cells.iter().next().unwrap().1.eq(&0));
    }

    #[test]
    fn set_user_input_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp_zcash::TwoBitDecompCircuit::<Fr>::default(
            );
        let k: u32 = 11;

        let mut analyzer = Analyzer::new(&circuit, k).unwrap();

        assert!(analyzer.instace_cells.len().eq(&1));
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string: analyzer.instace_cells,
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
            sample_circuits::bit_decomposition::two_bit_decomp_zcash::TwoBitDecompCircuit::<Fr>::default(
            );
        let k: u32 = 11;

        let mut analyzer = Analyzer::new(&circuit, k).unwrap();

        assert!(analyzer.instace_cells.clone().len().eq(&1));

        let modulus = bn256::fr::MODULUS_STR;
        let without_prefix = modulus.trim_start_matches("0x");
        let prime = BigInt::from_str_radix(without_prefix, 16)
            .unwrap()
            .to_string();

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string: analyzer.instace_cells.clone(),
                iterations: 5,
            },
        };
        let output_status = analyzer
            .analyze_underconstrained(analyzer_input, &prime)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrained));
    }

    #[test]
    fn not_under_constrained_not_enough_input_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp_zcash::TwoBitDecompCircuit::<Fr>::default(
            );
        let k: u32 = 11;

        let mut analyzer = Analyzer::new(&circuit, k).unwrap();

        assert!(analyzer.instace_cells.clone().len().eq(&1));
        let modulus = bn256::fr::MODULUS_STR;
        let without_prefix = modulus.trim_start_matches("0x");
        let prime = BigInt::from_str_radix(without_prefix, 16)
            .unwrap()
            .to_string();

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string: analyzer.instace_cells.clone(),
                iterations: 1,
            },
        };

        let output_status = analyzer
            .analyze_underconstrained(analyzer_input, &prime)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }

    #[test]
    fn not_under_constrained_not_enough_input_1_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp_zcash::TwoBitDecompCircuit::<Fr>::default(
            );
        let k: u32 = 11;

        let mut analyzer = Analyzer::new(&circuit, k).unwrap();

        assert!(analyzer.instace_cells.clone().len().eq(&1));
        let modulus = bn256::fr::MODULUS_STR;
        let without_prefix = modulus.trim_start_matches("0x");
        let prime = BigInt::from_str_radix(without_prefix, 16)
            .unwrap()
            .to_string();

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string: analyzer.instace_cells.clone(),
                iterations: 4,
            },
        };

        let output_status = analyzer
            .analyze_underconstrained(analyzer_input, &prime)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }

    #[test]
    fn not_under_constrained_exact_spec_input_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp_zcash::TwoBitDecompCircuit::<Fr>::default(
            );
        let k: u32 = 11;

        let mut analyzer = Analyzer::new(&circuit, k).unwrap();

        assert!(analyzer.instace_cells.len().eq(&1));
        let mut specified_instance_cols = HashMap::new();
        for var in analyzer.instace_cells.iter() {
            specified_instance_cols.insert(var.0.clone(), 3);
        }

        let modulus = bn256::fr::MODULUS_STR;
        let without_prefix = modulus.trim_start_matches("0x");
        let prime = BigInt::from_str_radix(without_prefix, 16)
            .unwrap()
            .to_string();

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput {
                instances_string: specified_instance_cols,
                iterations: 1,
            },
        };

        let output_status = analyzer
            .analyze_underconstrained(analyzer_input, &prime)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }

    #[test]
    fn not_under_constrained_not_exact_spec_input_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp_zcash::TwoBitDecompCircuit::<Fr>::default(
            );
        let k: u32 = 11;

        let mut analyzer = Analyzer::new(&circuit, k).unwrap();

        assert!(analyzer.instace_cells.len().eq(&1));
        let mut specified_instance_cols = HashMap::new();
        for var in analyzer.instace_cells.iter() {
            specified_instance_cols.insert(var.0.clone(), 1);
        }

        let modulus = bn256::fr::MODULUS_STR;
        let without_prefix = modulus.trim_start_matches("0x");
        let prime = BigInt::from_str_radix(without_prefix, 16)
            .unwrap()
            .to_string();

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput {
                instances_string: specified_instance_cols,
                iterations: 1,
            },
        };

        let output_status = analyzer
            .analyze_underconstrained(analyzer_input, &prime)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }

    #[test]
    fn under_constrained_enough_random_input_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp_zcash::TwoBitDecompCircuitUnderConstrained::<
                Fr,
            >::default();
        let k: u32 = 11;

        let mut analyzer = Analyzer::new(&circuit, k).unwrap();
        assert!(analyzer.instace_cells.clone().len().eq(&1));
        let modulus = bn256::fr::MODULUS_STR;
        let without_prefix = modulus.trim_start_matches("0x");
        let prime = BigInt::from_str_radix(without_prefix, 16)
            .unwrap()
            .to_string();

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string: analyzer.instace_cells.clone(),
                iterations: 5,
            },
        };

        let output_status = analyzer
            .analyze_underconstrained(analyzer_input, &prime)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::Underconstrained));
    }

    #[test]
    fn under_constrained_not_enough_random_input_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp_zcash::TwoBitDecompCircuitUnderConstrained::<
                Fr,
            >::default();
        let k: u32 = 11;

        let mut analyzer = Analyzer::new(&circuit, k).unwrap();

        assert!(analyzer.instace_cells.clone().len().eq(&1));
        let modulus = bn256::fr::MODULUS_STR;
        let without_prefix = modulus.trim_start_matches("0x");
        let prime = BigInt::from_str_radix(without_prefix, 16)
            .unwrap()
            .to_string();

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string: analyzer.instace_cells.clone(),
                iterations: 1,
            },
        };

        let output_status = analyzer
            .analyze_underconstrained(analyzer_input, &prime)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::Underconstrained));
    }

    #[test]
    fn under_constrained_exact_spec_input_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp_zcash::TwoBitDecompCircuitUnderConstrained::<
                Fr,
            >::default();
        let k: u32 = 11;

        let mut analyzer = Analyzer::new(&circuit, k).unwrap();

        assert!(analyzer.instace_cells.len().eq(&1));
        let mut specified_instance_cols = HashMap::new();
        for var in analyzer.instace_cells.iter() {
            specified_instance_cols.insert(var.0.clone(), 3);
        }

        let modulus = bn256::fr::MODULUS_STR;
        let without_prefix = modulus.trim_start_matches("0x");
        let prime = BigInt::from_str_radix(without_prefix, 16)
            .unwrap()
            .to_string();

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput {
                instances_string: specified_instance_cols,
                iterations: 1,
            },
        };

        let output_status = analyzer
            .analyze_underconstrained(analyzer_input, &prime)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::Underconstrained));
    }

    #[test]
    fn under_constrained_not_exact_spec_input_test() {
        let circuit =
            sample_circuits::bit_decomposition::two_bit_decomp_zcash::TwoBitDecompCircuitUnderConstrained::<
                Fr,
            >::default();
        let k: u32 = 11;

        let mut analyzer = Analyzer::new(&circuit, k).unwrap();

        assert!(analyzer.instace_cells.len().eq(&1));
        let mut specified_instance_cols = HashMap::new();
        for var in analyzer.instace_cells.iter() {
            specified_instance_cols.insert(var.0.clone(), 1);
        }

        let modulus = bn256::fr::MODULUS_STR;
        let without_prefix = modulus.trim_start_matches("0x");
        let prime = BigInt::from_str_radix(without_prefix, 16)
            .unwrap()
            .to_string();

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput {
                instances_string: specified_instance_cols,
                iterations: 1,
            },
        };

        let output_status = analyzer
            .analyze_underconstrained(analyzer_input, &prime)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::Underconstrained));
    }

    #[test]
    fn analyze_unused_columns_test() {
        let circuit: sample_circuits::bit_decomposition::add_multiplication_zcash::AddMultCircuit<Fr> =
            sample_circuits::bit_decomposition::add_multiplication_zcash::AddMultCircuit::default();
        let k = 5;

        //let prover = MockProver::<Fr>::run(k, &circuit, vec![]).unwrap();

        let mut analyzer = Analyzer::new(&circuit, k).unwrap();
        let output_status = analyzer.analyze_unused_columns().unwrap().output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::UnusedColumns));
        assert!(analyzer.log().len().gt(&0))
    }

    #[test]
    fn analyze_unused_custom_gates_test() {
        let circuit: sample_circuits::bit_decomposition::add_multiplication_zcash::AddMultCircuit<Fr> =
            sample_circuits::bit_decomposition::add_multiplication_zcash::AddMultCircuit::default();
        let k = 5;

        //let prover = MockProver::<Fr>::run(k, &circuit, vec![]).unwrap();
        let mut analyzer = Analyzer::new(&circuit, k).unwrap();
        let output_status = analyzer
            .analyze_unused_custom_gates()
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::UnusedCustomGates));
        assert!(analyzer.log().len().gt(&0))
    }

    #[test]
    fn analyze_unconstrained_cells() {
        let circuit: sample_circuits::bit_decomposition::add_multiplication_zcash::AddMultCircuit<Fr> =
            sample_circuits::bit_decomposition::add_multiplication_zcash::AddMultCircuit::default();
        let k = 5;

        //let prover = MockProver::<Fr>::run(k, &circuit, vec![]).unwrap();
        let mut analyzer = Analyzer::new(&circuit, k).unwrap();
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
        let k: u32 = 11;

        let mut analyzer = Analyzer::new(&circuit, k).unwrap();

        let modulus = bn256::fr::MODULUS_STR;
        let without_prefix = modulus.trim_start_matches("0x");
        let prime = BigInt::from_str_radix(without_prefix, 16)
            .unwrap()
            .to_string();

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string: analyzer.instace_cells.clone(),
                iterations: 5,
            },
        };

        let output_status = analyzer
            .analyze_underconstrained(analyzer_input, &prime)
            .unwrap()
            .output_status;
        println!("output_status: {:?}", output_status);
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }

    #[test]
    fn analyze_underconstrained_single_lookup_test() {
        let circuit =
            sample_circuits::lookup_circuits::lookup_underconstrained_zcash::MyCircuit::<Fr>(PhantomData);
        let k = 11;

        let a = Fr::from(1);
        let b = Fr::from(1);
        let out = Fr::from(21);

        let mut analyzer = Analyzer::new(&circuit, k).unwrap();

        let modulus = bn256::fr::MODULUS_STR;
        let without_prefix = modulus.trim_start_matches("0x");
        let prime = BigInt::from_str_radix(without_prefix, 16)
            .unwrap()
            .to_string();

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string: analyzer.instace_cells.clone(),
                iterations: 5,
            },
        };
        let output_status = analyzer
            .analyze_underconstrained(analyzer_input, &prime)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::Underconstrained));
    }

    #[test]
    fn analyze_underconstrained_multiple_lookup_test() {
        let circuit =
            sample_circuits::lookup_circuits::multiple_lookups_zcash::MyCircuit::<Fr>(PhantomData);

        let k = 11;

        let a = Fr::from(1);
        let b = Fr::from(1);
        let out = Fr::from(21);

        let mut analyzer = Analyzer::new(&circuit, k).unwrap();

        let modulus = bn256::fr::MODULUS_STR;
        let without_prefix = modulus.trim_start_matches("0x");
        let prime = BigInt::from_str_radix(without_prefix, 16)
            .unwrap()
            .to_string();

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string: analyzer.instace_cells.clone(),
                iterations: 5,
            },
        };
        let output_status = analyzer
            .analyze_underconstrained(analyzer_input, &prime)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }
    #[test]
    fn analyze_not_underconstrained_lookup_test() {
        let circuit =
            sample_circuits::lookup_circuits::multiple_lookups_zcash::MyCircuit::<Fr>(PhantomData);
        let k = 11;

        let a = Fr::from(1); // F[0]
        let b = Fr::from(1); // F[1]
        let out = Fr::from(21); // F[9]

        let mut analyzer = Analyzer::new(&circuit, k).unwrap();

        assert!(analyzer.instace_cells.len().eq(&3));
        let mut specified_instance_cols = HashMap::new();
        specified_instance_cols.insert("I-2-7".to_owned(), 21);
        specified_instance_cols.insert("I-0-1".to_owned(), 1);
        specified_instance_cols.insert("I-0-0".to_owned(), 1);

        let modulus = bn256::fr::MODULUS_STR;
        let without_prefix = modulus.trim_start_matches("0x");
        let prime = BigInt::from_str_radix(without_prefix, 16)
            .unwrap()
            .to_string();

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput {
                instances_string: specified_instance_cols,
                iterations: 1,
            },
        };
        let output_status = analyzer
            .analyze_underconstrained(analyzer_input, &prime)
            .unwrap()
            .output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }
}