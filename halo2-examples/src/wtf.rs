use std::marker::PhantomData;
use halo2_examples::fibonacci::example1::MyCircuit;
//use super::MyCircuit;
use halo2_proofs::{dev::MockProver, pasta::Fp};

extern crate z3;
use std::convert::TryInto;
use std::ops::Add;
use std::time::Duration;
use z3::ast::{Ast, Bool};
use z3::*;

fn main() {
    println!("Printing out constraints in Halo2 Constraint format:");

    let k = 4;
    let a = Fp::from(1); // F[0]
    let b = Fp::from(1); // F[1]
    let out = Fp::from(55); // F[9]

    let circuit = MyCircuit(PhantomData);

    let mut public_input = vec![a, b, out];

    let prover = MockProver::run(k, &circuit, vec![public_input.clone()]).unwrap();
    prover.assert_satisfied();

    public_input[2] += Fp::one();
    let _prover = MockProver::run(k, &circuit, vec![public_input]).unwrap();

    exampleZ3();

}

fn exampleZ3() {
    let cfg = Config::new();
    let ctx = Context::new(&cfg);

    let a = ast::Int::new_const(&ctx, "a");
    let b = ast::Int::new_const(&ctx, "b");
    let h = ast::Int::new_const(&ctx, "h");
    let o = ast::Int::new_const(&ctx, "o");
    let zero = ast::Int::from_i64(&ctx, 0);
    let one = ast::Int::from_i64(&ctx, 1);

    let solver = Solver::new(&ctx);


   //    h*(a+b)+(1-h)(a*b) - o  = 0

    // solver.assert(&x.gt(&y)); // old; for reference

    let firstTerm = ast::Int::mul(&ctx, &[&h, &ast::Int::add(&ctx, &[&a, &b])]);
    let secondTerm = ast::Int::mul(&ctx, &[&ast::Int::sub(&ctx, &[&one, &h]), &ast::Int::add(&ctx, &[&a, &b])]);
    let formulaSum = ast::Int::add(&ctx, &[&firstTerm, &secondTerm]);
    let formula = ast::Int::sub(&ctx, &[&formulaSum, &o]);
    solver.assert(&formula._eq(&zero));
    println!("Going to check... {}", &formula._eq(&zero));

    assert_eq!(solver.check(), SatResult::Sat);
    println!("Result is SAT");
    let model = solver.get_model().unwrap();
    let av = model.eval(&a, true).unwrap().as_i64().unwrap();
    let bv = model.eval(&b, true).unwrap().as_i64().unwrap();
    let hv = model.eval(&h, true).unwrap().as_i64().unwrap();
    let ov = model.eval(&o, true).unwrap().as_i64().unwrap();
    println!("model: \n{}", model);

    solver.assert(&h.gt(&zero));
    assert_eq!(solver.check(), SatResult::Sat);
    println!("Result is SAT");
    let model = solver.get_model().unwrap();
    let av = model.eval(&a, true).unwrap().as_i64().unwrap();
    let bv = model.eval(&b, true).unwrap().as_i64().unwrap();
    let hv = model.eval(&h, true).unwrap().as_i64().unwrap();
    let ov = model.eval(&o, true).unwrap().as_i64().unwrap();
    println!("model: \n{}", model);


    solver.assert(&h.gt(&one));
    solver.assert(&b.gt(&zero));
    solver.assert(&a.gt(&zero));
    assert_eq!(solver.check(), SatResult::Sat);
    println!("Result is SAT");
    let model = solver.get_model().unwrap();
    let av = model.eval(&a, true).unwrap().as_i64().unwrap();
    let bv = model.eval(&b, true).unwrap().as_i64().unwrap();
    let hv = model.eval(&h, true).unwrap().as_i64().unwrap();
    let ov = model.eval(&o, true).unwrap().as_i64().unwrap();
    println!("model: \n{}", model);

    //assert!(hv*(av+bv)+(1-hv)(av*bv)-ov == 0);

/*
    let model = solver.get_model().unwrap();
    let xv = model.eval(&x, true).unwrap().as_i64().unwrap();
    let yv = model.eval(&y, true).unwrap().as_i64().unwrap();
    println!("x: {}", xv);
    println!("y: {}", yv);
    assert!(xv > yv);
    assert!(yv % 7 == 2);
    assert!(xv + 2 > 7);
    */
}
