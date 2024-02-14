use crate::circuit_analyzer::halo2_proofs_libs::*;

/// `BitDecompositon`: This circuit is designed to check the binary decomposition
/// of a number. It takes an array `b` of FieldExt elements as input and verifies
/// that each element in `b` is either 0 or 1 (i.e., binary). It then combines
/// the binary elements of `b` into a single FieldExt element `x` in a way that `x`
/// represents the binary number formed by `b`. This combination is achieved by
/// a linear combination where each binary digit is multiplied by the corresponding
/// power of 2. The circuit uses a custom gate to enforce that every element in `b`
/// is binary. This gate creates the constraint `bi * (1 - bi)` for each `bi` in `b`,
/// which is satisfied only when `bi` is 0 or 1. Another gate ensures the correct
/// combination of the binary elements in `b` to form `x`. During the synthesis,
/// actual values are assigned to the elements in `b` and `x`, and the checks are enforced.
/// |   Row   |    bi    |   x    |  i  |    s     |
/// |---------|--------- |------- |---- |--------- |
/// |   0     |   b[0]   |  x     |  i  |    1     |
/// |   1     |   b[1]   |        |     |          |
/// |  ...    |   ...    |        |     |          |
/// |   i     |   b[i]   |        |     |          |
/// |  ...    |   ...    |        |     |          |
/// |   n     |   b[n]   |        |     |          |
/// 
/// Gate: b0_binary_check: s*b[0]*(1-b[0])
/// Gate: b1_binary_check: s*b[1]*(1-b[1])
/// Gate: b2_binary_check: s*b[2]*(1-b[2])
/// .....
/// Gate: bi_binary_check: s*b[i]*(1-b[i])
/// .....
/// Gate: bn_binary_check: s*b[n]*(1-b[n])
/// Gate:        equality: s*((2**n)*b[2]+...+(2**i)*b[i]+...+2*b[1]+b[0]-x)


pub struct BitDecompositon<F: FieldExt, const COUNT: usize> {
    b: [F; COUNT],
}

#[derive(Clone)]
pub struct BitDecompositonConfig<const COUNT: usize> {
    b: [Column<Advice>; COUNT],
    x: Column<Advice>,
    i: Column<Instance>,
    s: Selector,
}

impl<F: FieldExt, const COUNT: usize> Default for BitDecompositon<F, COUNT> {
    fn default() -> Self {
        BitDecompositon {
            b: [F::one(); COUNT],
        }
    }
}

impl<F: FieldExt, const COUNT: usize> Circuit<F> for BitDecompositon<F, COUNT> {
    type Config = BitDecompositonConfig<COUNT>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let mut b: [Column<Advice>; COUNT] = [Column::new(0, Advice); COUNT];
        for item in b.iter_mut().take(COUNT) {
            *item = meta.advice_column();
        }

        let x = meta.advice_column();
        let i = meta.instance_column();
        let s = meta.selector();

        meta.enable_equality(x);
        meta.enable_equality(i);

        // define gates
        for (i, item) in b.iter().enumerate().take(COUNT) {
            let tmp = format!("b{}_binary_check", i).to_owned();
            let name: &'static str = Box::leak(tmp.to_string().into_boxed_str());
            // adds constraint: bi * (1-bi)
            meta.create_gate(name, |meta| {
                let a = meta.query_advice(*item, Rotation::cur());
                let dummy = meta.query_selector(s);
                vec![dummy * a.clone() * (Expression::Constant(F::from(1)) - a)]
            });
        }

        meta.create_gate("equality", |meta| {
            let mut exp = Expression::Constant(F::from(0));
            let mut t = F::from(1);
            for item in b.iter().take(COUNT) {
                let bi = meta.query_advice(*item, Rotation::cur());
                exp = exp + Expression::Constant(t) * bi;
                t *= F::from(2);
            }

            let c = meta.query_advice(x, Rotation::cur());
            let dummy = meta.query_selector(s);
            // For example, if we change the constraint to the following, then the circuit is underconstraint,
            // because we have two models with the same public input (i=1, b0=1, b1=0, x=1) and (i=1, b0=0, b1=1, x=1)
            vec![dummy * (exp - c)]
        });

        Self::Config { b, x, i, s }
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
                    for i in 0..COUNT {
                        region.assign_advice(
                            || "bi",
                            config.b[i],
                            0,
                            || Value::known(self.b[0]),
                        )?;
                    }

                    let mut compose_b = F::from(0);
                    for i in 0..COUNT - 1 {
                        compose_b = F::from(2) * compose_b + self.b[COUNT - 1 - i];
                    }
                    compose_b += self.b[0];

                    let out =
                        region.assign_advice(|| "x", config.x, 0, || Value::known(compose_b))?;

                    Ok(out)
                },
            )
            .unwrap();
        // expose the public input
        layouter.constrain_instance(out.cell(), config.i, 0)?;
        Ok(())
    }
}

// `BitDecompositonUnderConstrained`: This circuit is almost identical to
// `BitDecompositon`, but intentionally introduces an under-constraint bug
// in the bit-checking gate. In the configuration of the circuit, the gate
// that enforces each `bi` in `b` to be binary starts checking from the second
// element in `b` rather than the first. This means that the first binary digit
// isn't properly checked, and the circuit becomes under-constrained. This could
// allow a malicious prover to provide incorrect witnesses that still satisfy
// the circuit's constraints. For example, the prover could provide two different
// decompositions that result in the same `x`, violating the unique representation
// property of the binary numbers.
pub struct BitDecompositonUnderConstrained<F: FieldExt, const COUNT: usize> {
    b: [F; COUNT],
}

#[derive(Clone)]
pub struct BitDecompositonUnderConstrainedConfig<const COUNT: usize> {
    b: [Column<Advice>; COUNT],
    x: Column<Advice>,
    i: Column<Instance>,
    s: Selector,
}

impl<F: FieldExt, const COUNT: usize> Default for BitDecompositonUnderConstrained<F, COUNT> {
    fn default() -> Self {
        BitDecompositonUnderConstrained {
            b: [F::one(); COUNT],
        }
    }
}

impl<F: FieldExt, const COUNT: usize> Circuit<F> for BitDecompositonUnderConstrained<F, COUNT> {
    type Config = BitDecompositonUnderConstrainedConfig<COUNT>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        let mut b: [Column<Advice>; COUNT] = [Column::new(0, Advice); COUNT];
        for item in b.iter_mut().take(COUNT) {
            *item = meta.advice_column();
        }
        let x = meta.advice_column();
        let i = meta.instance_column();
        let s = meta.selector();

        meta.enable_equality(x);
        meta.enable_equality(i);

        // define gates
        // NOTICE: introducing under-constrained bug
        // The for loop has to start from 1, but we introduce the bug by starting from 0
        // hence b[0] will be left not constrained properly.
        for (i, item) in b.iter().enumerate().take(COUNT).skip(1) {
            let tmp = format!("b{}_binary_check", i).to_owned();
            let name: &'static str = Box::leak(tmp.to_string().into_boxed_str());
            //Adds Constraint for: bi * (1-bi)
            meta.create_gate(name, |meta| {
                let a = meta.query_advice(*item, Rotation::cur());
                let dummy = meta.query_selector(s);
                vec![dummy * a.clone() * (Expression::Constant(F::from(1)) - a)]
            });
        }

        meta.create_gate("equality", |meta| {
            let mut exp = Expression::Constant(F::from(0));
            let mut t = F::from(1);
            for item in b.iter().take(COUNT) {
                let bi = meta.query_advice(*item, Rotation::cur());
                exp = exp + Expression::Constant(t) * bi;
                t *= F::from(2);
            }

            let c = meta.query_advice(x, Rotation::cur());
            let dummy = meta.query_selector(s);
            // For example, if we change the constraint to the following, then the circuit is underconstraint,
            // because we have two models with the same public input (i=1, b0=1, b1=0, x=1) and (i=1, b0=0, b1=1, x=1)
            vec![dummy * (exp - c)]
        });

        Self::Config { b, x, i, s }
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
                    for i in 0..COUNT {
                        region.assign_advice(
                            || "bi",
                            config.b[i],
                            0,
                            || Value::known(self.b[0]),
                        )?;
                    }

                    let mut compose_b = F::from(0);
                    for i in 0..COUNT - 1 {
                        compose_b = F::from(2) * compose_b + self.b[COUNT - 1 - i];
                    }
                    compose_b += self.b[0];

                    let out =
                        region.assign_advice(|| "x", config.x, 0, || Value::known(compose_b))?;

                    Ok(out)
                },
            )
            .unwrap();
        // expose the public input
        layouter.constrain_instance(out.cell(), config.i, 0)?;
        Ok(())
    }
}