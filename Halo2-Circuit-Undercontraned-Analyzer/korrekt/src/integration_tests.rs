#[cfg(test)]
mod tests {
    use std::collections::HashMap;
    use std::marker::PhantomData;
    use crate::analyzer::Analyzer;
    //use crate::analyzer::FMCheck;
    use crate::analyzer_io_type;
    use crate::analyzer_io_type::AnalyzerOutputStatus;
    use crate::analyzer_io_type::VerificationInput;
    use crate::analyzer_io_type::VerificationMethod;
    use crate::sample_circuits;
    use crate::smt;
    use halo2_proofs::pasta::Fp;
    use halo2_proofs::{dev::MockProver, pasta::Fp as Fr};
    use z3::ast;
    #[test]
    fn create_play_circuit() {
        let circuit = sample_circuits::PlayCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
        let k = 5;

        let public_input = Fr::from(3);
        //mockprover verify passes
        let prover = MockProver::<Fr>::run(k, &circuit, vec![vec![public_input]]).unwrap();
        assert!(prover.verify().eq(&Ok(())));
    }
    #[test]
    fn create_multi_play_circuit() {
        let circuit = sample_circuits::MultiPlayCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
        let k = 5;

        let public_input = Fr::from(3);
        //mockprover verify passes
        let prover = MockProver::<Fr>::run(k, &circuit, vec![vec![public_input]]).unwrap();
        assert!(prover.verify().eq(&Ok(())));
    }

    #[test]
    fn create_analyzer_test() {
        let circuit = sample_circuits::PlayCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
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
        let circuit = sample_circuits::PlayCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
        let mut analyzer = Analyzer::create_with_circuit(&circuit);
        let z3_context: z3::Context = z3::Context::new(&z3::Config::new());
        let (instance_cols,t) =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone(), &z3_context);
        assert!(instance_cols.len().eq(&1));
        for var in instance_cols {
            assert!(var.0.to_string().eq("A-2-0"));
            assert!(var.1.eq(&0));
            break;
        }
    }

    #[test]
    fn set_user_input_test() {
        let circuit = sample_circuits::PlayCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
        let mut analyzer = Analyzer::create_with_circuit(&circuit);
        let z3_context: z3::Context = z3::Context::new(&z3::Config::new());
        let (instance_cols,t) =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone(), &z3_context);
        assert!(instance_cols.len().eq(&1));
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances: instance_cols,
                instances_string:t,
                iterations: 5,
            },
            z3_context: &z3_context,
        };
        assert!(analyzer_input
            .verification_method
            .eq(&VerificationMethod::Random));
        assert!(analyzer_input.verification_input.iterations.eq(&5));
    }
    #[test]
    fn decompose_polynomial_test() {
        let circuit = sample_circuits::PlayCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
        let mut analyzer = Analyzer::create_with_circuit(&circuit);
        let z3_context: z3::Context = z3::Context::new(&z3::Config::new());
        let (instance_cols,t) =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone(), &z3_context);
        assert!(instance_cols.len().eq(&1));
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances: instance_cols,
                instances_string:t,
                iterations: 5,
            },
            z3_context: &z3_context,
        };
        let mut f = std::fs::File::create("out.smt2").unwrap();
        let mut p = smt::write_start(&mut f);
        let (formulas, vars_list) = analyzer.decompose_polynomial(&analyzer_input.z3_context,&mut p);
        assert!(formulas.len().eq(&3));
        assert!(vars_list.len().eq(&3));
    }
    #[test]
    fn not_under_constrained_enough_random_input_test() {
        let circuit = sample_circuits::PlayCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
        let mut analyzer = Analyzer::create_with_circuit(&circuit);
        let z3_context: z3::Context = z3::Context::new(&z3::Config::new());
        let (instance_cols,t) =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone(), &z3_context);
        assert!(instance_cols.len().eq(&1));
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances: instance_cols,
                instances_string:t,
                iterations: 5,
            },
            z3_context: &z3_context,
        };
        let mut f = std::fs::File::create("out.smt2").unwrap();
        let mut p = smt::write_start(&mut f);
        let (formulas, vars_list) = analyzer.decompose_polynomial(&analyzer_input.z3_context,&mut p);
        let instance = analyzer_input.verification_input.instances.clone();
        let instance_string = analyzer_input.verification_input.instances_string.clone();
        let output_status: AnalyzerOutputStatus =
            Analyzer::<Fp>::control_uniqueness(formulas, vars_list, &instance,&instance_string, &analyzer_input,&mut p);
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrained));
    }

    #[test]
    fn not_under_constrained_not_enough_input_test() {
        let circuit = sample_circuits::PlayCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
        let mut analyzer = Analyzer::create_with_circuit(&circuit);
        let z3_context: z3::Context = z3::Context::new(&z3::Config::new());
        let (instance_cols,t) =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone(), &z3_context);
        assert!(instance_cols.len().eq(&1));
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances: instance_cols,
                instances_string:t,
                iterations: 1,
            },
            z3_context: &z3_context,
        };
        let mut f = std::fs::File::create("out.smt2").unwrap();
        let mut p = smt::write_start(&mut f);
        let (formulas, vars_list) = analyzer.decompose_polynomial(&analyzer_input.z3_context,&mut p);
        let instance = analyzer_input.verification_input.instances.clone();
        let instance_string = analyzer_input.verification_input.instances_string.clone();
        let output_status: AnalyzerOutputStatus =
            Analyzer::<Fp>::control_uniqueness(formulas, vars_list, &instance,&instance_string, &analyzer_input,&mut p);
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }
    #[test]
    fn not_under_constrained_not_enough_input_1_test() {
        let circuit = sample_circuits::PlayCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
        let mut analyzer = Analyzer::create_with_circuit(&circuit);
        let z3_context: z3::Context = z3::Context::new(&z3::Config::new());
        let (instance_cols,t) =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone(), &z3_context);
        assert!(instance_cols.len().eq(&1));
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances: instance_cols,
                instances_string:t,
                iterations: 4,
            },
            z3_context: &z3_context,
        };
        let mut f = std::fs::File::create("out.smt2").unwrap();
        let mut p = smt::write_start(&mut f);
        let (formulas, vars_list) = analyzer.decompose_polynomial(&analyzer_input.z3_context,&mut p);
        let instance = analyzer_input.verification_input.instances.clone();
        let instance_string = analyzer_input.verification_input.instances_string.clone();
        let output_status: AnalyzerOutputStatus =
            Analyzer::<Fp>::control_uniqueness(formulas, vars_list, &instance,&instance_string, &analyzer_input,&mut p);
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }
    #[test]
    fn not_under_constrained_exact_spec_input_test() {
        let circuit = sample_circuits::PlayCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
        let mut analyzer = Analyzer::create_with_circuit(&circuit);
        let z3_context: z3::Context = z3::Context::new(&z3::Config::new());
        let (instance_cols,t) =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone(), &z3_context);
        assert!(instance_cols.len().eq(&1));
        let mut specified_instance_cols = HashMap::new();
        for mut _var in instance_cols.iter() {
            specified_instance_cols.insert(_var.0.clone(), 3);
        }

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput {
                instances: specified_instance_cols,
                instances_string:t,
                iterations: 1,
            },
            z3_context: &z3_context,
        };
        let mut f = std::fs::File::create("out.smt2").unwrap();
        let mut p = smt::write_start(&mut f);
        let (formulas, vars_list) = analyzer.decompose_polynomial(&analyzer_input.z3_context,&mut p);
        let instance = analyzer_input.verification_input.instances.clone();
        let instance_string = analyzer_input.verification_input.instances_string.clone();
        let output_status: AnalyzerOutputStatus =
            Analyzer::<Fp>::control_uniqueness(formulas, vars_list, &instance,&instance_string, &analyzer_input,&mut p);
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }

    #[test]
    fn not_under_constrained_not_exact_spec_input_test() {
        let circuit = sample_circuits::PlayCircuit::<Fr>::new(Fr::from(1), Fr::from(1));
        let mut analyzer = Analyzer::create_with_circuit(&circuit);
        let z3_context: z3::Context = z3::Context::new(&z3::Config::new());
        let (instance_cols,t) =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone(), &z3_context);
        assert!(instance_cols.len().eq(&1));
        let mut specified_instance_cols = HashMap::new();
        for mut _var in instance_cols.iter() {
            specified_instance_cols.insert(_var.0.clone(), 1);
        }

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput {
                instances: specified_instance_cols,
                instances_string:t,
                iterations: 1,
            },
            z3_context: &z3_context,
        };
        let mut f = std::fs::File::create("out.smt2").unwrap();
        let mut p = smt::write_start(&mut f);
        let (formulas, vars_list) = analyzer.decompose_polynomial(&analyzer_input.z3_context,&mut p);
        let instance = analyzer_input.verification_input.instances.clone();
        let instance_string = analyzer_input.verification_input.instances_string.clone();
        let output_status: AnalyzerOutputStatus =
            Analyzer::<Fp>::control_uniqueness(formulas, vars_list, &instance,&instance_string, &analyzer_input,&mut p);
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }

    #[test]
    fn under_constrained_enough_random_input_test() {
        let circuit =
            sample_circuits::PlayCircuitUnderConstrained::<Fr>::new(Fr::from(1), Fr::from(1));
        let mut analyzer = Analyzer::create_with_circuit(&circuit);
        let z3_context: z3::Context = z3::Context::new(&z3::Config::new());
        let (instance_cols,t) =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone(), &z3_context);
        assert!(instance_cols.len().eq(&1));
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances: instance_cols,
                instances_string:t,
                iterations: 5,
            },
            z3_context: &z3_context,
        };
        let mut f = std::fs::File::create("out.smt2").unwrap();
        let mut p = smt::write_start(&mut f);
        let (formulas, vars_list) = analyzer.decompose_polynomial(&analyzer_input.z3_context,&mut p);
        let instance = analyzer_input.verification_input.instances.clone();
        let instance_string = analyzer_input.verification_input.instances_string.clone();
        let output_status: AnalyzerOutputStatus =
            Analyzer::<Fp>::control_uniqueness(formulas, vars_list, &instance,&instance_string, &analyzer_input,&mut p);
        assert!(output_status.eq(&AnalyzerOutputStatus::Underconstrained));
    }

    #[test]
    fn under_constrained_not_enough_random_input_test() {
        let circuit =
            sample_circuits::PlayCircuitUnderConstrained::<Fr>::new(Fr::from(1), Fr::from(1));
        let mut analyzer = Analyzer::create_with_circuit(&circuit);
        let z3_context: z3::Context = z3::Context::new(&z3::Config::new());
        let (instance_cols,t) =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone(), &z3_context);
        assert!(instance_cols.len().eq(&1));
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances: instance_cols,
                instances_string:t,
                iterations: 1,
            },
            z3_context: &z3_context,
        };
        let mut f = std::fs::File::create("out.smt2").unwrap();
        let mut p = smt::write_start(&mut f);
        let (formulas, vars_list) = analyzer.decompose_polynomial(&analyzer_input.z3_context,&mut p);
        let instance = analyzer_input.verification_input.instances.clone();
        let instance_string = analyzer_input.verification_input.instances_string.clone();
        let output_status: AnalyzerOutputStatus =
            Analyzer::<Fp>::control_uniqueness(formulas, vars_list, &instance,&instance_string, &analyzer_input,&mut p);
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }

    #[test]
    fn under_constrained_exact_spec_input_test() {
        let circuit =
            sample_circuits::PlayCircuitUnderConstrained::<Fr>::new(Fr::from(1), Fr::from(1));
        let mut analyzer = Analyzer::create_with_circuit(&circuit);
        let z3_context: z3::Context = z3::Context::new(&z3::Config::new());
        let (instance_cols,t) =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone(), &z3_context);

        assert!(instance_cols.len().eq(&1));
        let mut specified_instance_cols = HashMap::new();
        for mut _var in instance_cols.iter() {
            specified_instance_cols.insert(_var.0.clone(), 3);
        }

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput {
                instances: specified_instance_cols,
                instances_string:t,
                iterations: 1,
            },
            z3_context: &z3_context,
        };
        let mut f = std::fs::File::create("out.smt2").unwrap();
        let mut p = smt::write_start(&mut f);
        let (formulas, vars_list) = analyzer.decompose_polynomial(&analyzer_input.z3_context,&mut p);
        let instance = analyzer_input.verification_input.instances.clone();
        let instance_string = analyzer_input.verification_input.instances_string.clone();
        let output_status: AnalyzerOutputStatus =
            Analyzer::<Fp>::control_uniqueness(formulas, vars_list, &instance,&instance_string, &analyzer_input,&mut p);
        assert!(output_status.eq(&AnalyzerOutputStatus::Underconstrained));
    }
    #[test]
    fn under_constrained_not_exact_spec_input_test() {
        let circuit =
            sample_circuits::PlayCircuitUnderConstrained::<Fr>::new(Fr::from(1), Fr::from(1));
        let mut analyzer = Analyzer::create_with_circuit(&circuit);
        let z3_context: z3::Context = z3::Context::new(&z3::Config::new());
        let (instance_cols,t) =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone(), &z3_context);

        assert!(instance_cols.len().eq(&1));
        let mut specified_instance_cols = HashMap::new();
        for mut _var in instance_cols.iter() {
            specified_instance_cols.insert(_var.0.clone(), 1);
        }

        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Specific,
            verification_input: VerificationInput {
                instances: specified_instance_cols,
                instances_string:t,
                iterations: 1,
            },
            z3_context: &z3_context,
        };
        let mut f = std::fs::File::create("out.smt2").unwrap();
        let mut p = smt::write_start(&mut f);
        let (formulas, vars_list) = analyzer.decompose_polynomial(&analyzer_input.z3_context,&mut p);
        let instance = analyzer_input.verification_input.instances.clone();
        let instance_string = analyzer_input.verification_input.instances_string.clone();
        let output_status: AnalyzerOutputStatus =
            Analyzer::<Fp>::control_uniqueness(formulas, vars_list, &instance,&instance_string, &analyzer_input,&mut p);
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrainedLocal));
    }


    #[test]
    fn analyze_underconstrained_test() {
        let circuit : sample_circuits::PlayCircuit_M<Fp> =
        sample_circuits::PlayCircuit_M::default();
        let mut analyzer = Analyzer::create_with_circuit(&circuit);
        let z3_context: z3::Context = z3::Context::new(&z3::Config::new());
        let (instance_cols,t) =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone(), &z3_context);
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances: instance_cols,
                instances_string:t,
                iterations: 5,
            },
            z3_context: &z3_context,
        };
        let mut f = std::fs::File::create("out.smt2").unwrap();
        let mut p = smt::write_start(&mut f);
        let (formulas, vars_list) = analyzer.decompose_polynomial(&analyzer_input.z3_context,&mut p);
        let instance = analyzer_input.verification_input.instances.clone();
        let instance_string = analyzer_input.verification_input.instances_string.clone();
        let output_status: AnalyzerOutputStatus =
            Analyzer::<Fp>::control_uniqueness(formulas, vars_list, &instance,&instance_string, &analyzer_input,&mut p);
        assert!(output_status.eq(&AnalyzerOutputStatus::Underconstrained));
    }

    #[test]
    fn analyze_unused_columns_test() {
        let circuit : sample_circuits::PlayCircuit_M<Fp> =
        sample_circuits::PlayCircuit_M::default();
        let mut analyzer = Analyzer::create_with_circuit(&circuit);
        // println!("{:#?}", analyzer);

        analyzer.analyze_unused_columns();

        assert!(analyzer.log().len().gt(&0))
    }
    #[test]
    fn analyze_unsed_custom_gates_test() {
        let circuit : sample_circuits::PlayCircuit_M<Fp> =
        sample_circuits::PlayCircuit_M::default();
        let mut analyzer = Analyzer::create_with_circuit(&circuit);
        // println!("{:#?}", analyzer);

        
        analyzer.analyze_unsed_custom_gates();

        assert!(analyzer.log().len().gt(&0))
    }
    #[test]
    fn analyze_unconstrained_cells() {
        let circuit : sample_circuits::PlayCircuit_M<Fp> =
        sample_circuits::PlayCircuit_M::default();
        let mut analyzer = Analyzer::create_with_circuit(&circuit);
        // println!("{:#?}", analyzer);

        analyzer.analyze_unconstrained_cells();

        assert!(analyzer.log().len().gt(&0))
    }

    #[test]
    fn analyze_underconstrained_fibonacci_test() {
        let k = 4;

        let a = Fp::from(1); // F[0]
        let b = Fp::from(1); // F[1]
        let out = Fp::from(55); // F[9]

        let circuit:sample_circuits::MyCircuit<_> = sample_circuits::MyCircuit::<Fp>(PhantomData);

        //let mut public_input = vec![a, b, out];

        let mut analyzer = Analyzer::create_with_circuit(&circuit);
        let z3_context: z3::Context = z3::Context::new(&z3::Config::new());
        let (instance_cols,t) =
            analyzer.extract_instance_cols(analyzer.layouter.eq_table.clone(), &z3_context);
        let analyzer_input: analyzer_io_type::AnalyzerInput = analyzer_io_type::AnalyzerInput {
            verification_method: VerificationMethod::Random,
            verification_input: VerificationInput {
                instances: instance_cols,
                instances_string:t,
                iterations: 5,
            },
            z3_context: &z3_context,
        };
        let mut f = std::fs::File::create("out.smt2").unwrap();
        let mut p = smt::write_start(&mut f);
        let (formulas, vars_list) = analyzer.decompose_polynomial(&analyzer_input.z3_context,&mut p);
        let instance = analyzer_input.verification_input.instances.clone();
        let instance_string = analyzer_input.verification_input.instances_string.clone();
        let output_status: AnalyzerOutputStatus =
            Analyzer::<Fp>::control_uniqueness(formulas, vars_list, &instance,&instance_string, &analyzer_input,&mut p);
        assert!(output_status.eq(&AnalyzerOutputStatus::NotUnderconstrained));
    }
}
