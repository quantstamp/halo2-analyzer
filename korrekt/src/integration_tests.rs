#[cfg(test)]
mod tests {
    use halo2_proofs::pasta::Fp;
    use halo2_proofs::{dev::MockProver, pasta::Fp as Fr};
    use std::collections::HashMap;
    use std::marker::PhantomData;
    use crate::analyzer::Analyzer;
    use crate::analyzer_io_type;
    use crate::analyzer_io_type::AnalyzerOutputStatus;
    use crate::analyzer_io_type::VerificationInput;
    use crate::analyzer_io_type::VerificationMethod;
    use crate::sample_circuits;
    use crate::smt;

    #[test]
    fn create_two_bit_decomp_circuit() {
        let circuit = sample_circuits::two_bit_decomp::TwoBitDecompCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
        let k = 5;

        let public_input = Fr::from(3);
        //mockprover verify passes
        let prover = MockProver::<Fr>::run(k, &circuit, vec![vec![public_input]]).unwrap();
        assert!(prover.verify().eq(&Ok(())));
    }
    #[test]
    fn create_multtrow_two_bit_decomp_circuit() {
        let circuit = sample_circuits::two_bit_decomp_multirow::MultiRowTwoBitDecompCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
        let k = 5;

        let public_input = Fr::from(3);
        //mockprover verify passes
        let prover = MockProver::<Fr>::run(k, &circuit, vec![vec![public_input]]).unwrap();
        assert!(prover.verify().eq(&Ok(())));
    }

    #[test]
    fn create_analyzer_test() {
        let circuit = sample_circuits::two_bit_decomp::TwoBitDecompCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
        let analyzer = Analyzer::create_with_circuit(&circuit);
        assert!(analyzer.cs.gates.len().eq(&3));
        assert!(analyzer.cs.degree().eq(&3));
        assert!(analyzer.cs.num_advice_columns.eq(&3));
        assert!(analyzer.cs.num_instance_columns.eq(&1));
        assert!(analyzer.cs.num_selectors.eq(&1));
        assert!(analyzer.cs.num_fixed_columns.eq(&0));
    }

    #[test]
    fn extract_instance_cols_test() {
        let circuit = sample_circuits::two_bit_decomp::TwoBitDecompCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
        let mut analyzer = Analyzer::create_with_circuit(&circuit);

        let instance_cols =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
        assert!(instance_cols.len().eq(&1));
        for var in instance_cols {
            assert!(var.0.to_string().eq("A-2-0"));
            assert!(var.1.eq(&0));
            break;
        }
    }

    #[test]
    fn set_user_input_test() {
        let circuit = sample_circuits::two_bit_decomp::TwoBitDecompCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
        let mut analyzer = Analyzer::create_with_circuit(&circuit);
        let instance_cols =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
        assert!(instance_cols.len().eq(&1));
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string:instance_cols,
                iterations: 5,
            },
        };
        assert!(analyzer_input
            .verification_method
            .eq(&VerificationMethod::Random));
        assert!(analyzer_input.verification_input.iterations.eq(&5));
    }

    #[test]
    fn decompose_polynomial_test() {
        let circuit = sample_circuits::two_bit_decomp::TwoBitDecompCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
        let mut analyzer = Analyzer::create_with_circuit(&circuit);
        let instance_cols =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
        assert!(instance_cols.len().eq(&1));
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                
                instances_string:instance_cols,
                iterations: 5,
            },
            
        };
        let smt_file_path = "src/output/out.smt2";
        let base_field_prime = "28948022309329048855892746252171976963363056481941560715954676764349967630337";
        let mut smt_file = std::fs::File::create(smt_file_path).unwrap();
        let mut printer = smt::write_start(&mut smt_file, base_field_prime.to_string());
        analyzer.decompose_polynomial(&mut printer);
    }

    #[test]
    fn not_under_constrained_enough_random_input_test() {
        let circuit = sample_circuits::two_bit_decomp::TwoBitDecompCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
        let mut analyzer = Analyzer::create_with_circuit(&circuit);

        let instance_cols =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
        assert!(instance_cols.len().eq(&1));
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string:instance_cols,
                iterations: 5,
            },
        };
        let output_status = analyzer.analyze_underconstrained(analyzer_input).output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrained));
    }

    #[test]
    fn not_under_constrained_not_enough_input_test() {
        let circuit = sample_circuits::two_bit_decomp::TwoBitDecompCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
        let mut analyzer = Analyzer::create_with_circuit(&circuit);

        let (instance_cols) =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
        assert!(instance_cols.len().eq(&1));
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string: instance_cols,
                iterations: 1,
            },
        };
        let output_status = analyzer.analyze_underconstrained(analyzer_input).output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }

    #[test]
    fn not_under_constrained_not_enough_input_1_test() {
        let circuit = sample_circuits::two_bit_decomp::TwoBitDecompCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
        let mut analyzer = Analyzer::create_with_circuit(&circuit);

        let (instance_cols) =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
        assert!(instance_cols.len().eq(&1));
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                
                instances_string:instance_cols,
                iterations: 4,
            },
            
        };
        let output_status = analyzer.analyze_underconstrained(analyzer_input).output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }

    #[test]
    fn not_under_constrained_exact_spec_input_test() {
        let circuit = sample_circuits::two_bit_decomp::TwoBitDecompCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
        let mut analyzer = Analyzer::create_with_circuit(&circuit);

        let (instance_cols) =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
        assert!(instance_cols.len().eq(&1));
        let mut specified_instance_cols = HashMap::new();
        for mut _var in instance_cols.iter() {
            specified_instance_cols.insert(_var.0.clone(), 3);
        }

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput {
                instances_string:specified_instance_cols,
                iterations: 1,
            },  
        };
        let output_status = analyzer.analyze_underconstrained(analyzer_input).output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }

    #[test]
    fn not_under_constrained_not_exact_spec_input_test() {
        let circuit = sample_circuits::two_bit_decomp::TwoBitDecompCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
        let mut analyzer = Analyzer::create_with_circuit(&circuit);

        let instance_cols =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
        assert!(instance_cols.len().eq(&1));
        let mut specified_instance_cols = HashMap::new();
        for mut _var in instance_cols.iter() {
            specified_instance_cols.insert(_var.0.clone(), 1);
        }

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput {
                instances_string:specified_instance_cols,
                iterations: 1,
            }, 
        };
        let output_status = analyzer.analyze_underconstrained(analyzer_input).output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }

    #[test]
    fn under_constrained_enough_random_input_test() {
        let circuit =
            sample_circuits::two_bit_decomp::TwoBitDecompCircuitUnderConstrained::<Fr>::new(Fr::from(1), Fr::from(1));
        let mut analyzer = Analyzer::create_with_circuit(&circuit);

        let instance_cols =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
        assert!(instance_cols.len().eq(&1));
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string:instance_cols,
                iterations: 5,
            },   
        };
        let output_status = analyzer.analyze_underconstrained(analyzer_input).output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::Underconstrained));
    }

    #[test]
    fn under_constrained_not_enough_random_input_test() {
        let circuit =
            sample_circuits::two_bit_decomp::TwoBitDecompCircuitUnderConstrained::<Fr>::new(Fr::from(1), Fr::from(1));
        let mut analyzer = Analyzer::create_with_circuit(&circuit);

        let instance_cols =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
        assert!(instance_cols.len().eq(&1));
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                
                instances_string:instance_cols,
                iterations: 1,
            },
        };
        let output_status = analyzer.analyze_underconstrained(analyzer_input).output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }

    #[test]
    fn under_constrained_exact_spec_input_test() {
        let circuit =
            sample_circuits::two_bit_decomp::TwoBitDecompCircuitUnderConstrained::<Fr>::new(Fr::from(1), Fr::from(1));
        let mut analyzer = Analyzer::create_with_circuit(&circuit);

        let instance_cols =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());

        assert!(instance_cols.len().eq(&1));
        let mut specified_instance_cols = HashMap::new();
        for mut _var in instance_cols.iter() {
            specified_instance_cols.insert(_var.0.clone(), 3);
        }

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput {
                instances_string:specified_instance_cols,
                iterations: 1,
            },
        };
        let output_status = analyzer.analyze_underconstrained(analyzer_input).output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::Underconstrained));
    }

    #[test]
    fn under_constrained_not_exact_spec_input_test() {
        let circuit =
            sample_circuits::two_bit_decomp::TwoBitDecompCircuitUnderConstrained::<Fr>::new(Fr::from(1), Fr::from(1));
        let mut analyzer = Analyzer::create_with_circuit(&circuit);

        let instance_cols =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());

        assert!(instance_cols.len().eq(&1));
        let mut specified_instance_cols = HashMap::new();
        for mut _var in instance_cols.iter() {
            specified_instance_cols.insert(_var.0.clone(), 1);
        }

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput {
                instances_string:specified_instance_cols,
                iterations: 1,
            },
            
        };
        let output_status = analyzer.analyze_underconstrained(analyzer_input).output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }

    #[test]
    fn analyze_underconstrained_test() {
        let circuit : sample_circuits::add_multiplication::AddMultCircuit<Fp> =
        sample_circuits::add_multiplication::AddMultCircuit::default();
        let mut analyzer = Analyzer::create_with_circuit(&circuit);

        let instance_cols =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                
                instances_string:instance_cols,
                iterations: 5,
            },
            
        };
        let output_status = analyzer.analyze_underconstrained(analyzer_input).output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::Underconstrained));
    }

    #[test]
    fn analyze_unused_columns_test() {
        let circuit : sample_circuits::add_multiplication::AddMultCircuit<Fp> =
        sample_circuits::add_multiplication::AddMultCircuit::default();
        let mut analyzer = Analyzer::create_with_circuit(&circuit);
        analyzer.analyze_unused_columns();
        assert!(analyzer.log().len().gt(&0))
    }

    #[test]
    fn analyze_unused_custom_gates_test() {
        let circuit : sample_circuits::add_multiplication::AddMultCircuit<Fp> =
        sample_circuits::add_multiplication::AddMultCircuit::default();
        let mut analyzer = Analyzer::create_with_circuit(&circuit);
        analyzer.analyze_unused_custom_gates();
        assert!(analyzer.log().len().gt(&0))
    }

    #[test]
    fn analyze_unconstrained_cells() {
        let circuit : sample_circuits::add_multiplication::AddMultCircuit<Fp> =
        sample_circuits::add_multiplication::AddMultCircuit::default();
        let mut analyzer = Analyzer::create_with_circuit(&circuit);
        analyzer.analyze_unconstrained_cells();
        assert!(analyzer.log().len().gt(&0))
    }

    #[test]
    fn analyze_underconstrained_fibonacci_test() {
        let a = Fp::from(1); // F[0]
        let b = Fp::from(1); // F[1]
        let out = Fp::from(55); // F[9]

        let circuit:sample_circuits::fibonacci::FibonacciCircuit<_> = sample_circuits::fibonacci::FibonacciCircuit::<Fp>(PhantomData);
        let mut analyzer = Analyzer::create_with_circuit(&circuit);

        let instance_cols =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone());
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances_string:instance_cols,
                iterations: 5,
            },
            
        };
        let output_status = analyzer.analyze_underconstrained(analyzer_input).output_status;
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrained));
    }
}