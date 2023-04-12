//! SMT printing without duplication
//!
//! rsmt2 duplicates a ton.

use std::collections::HashMap;
use std::fs::File;
use std::io::Write;

use crate::analyzer::{self, NodeType};

pub struct Printer<'a, W: 'a> {
    //sort_reprs: HashMap<Sort, String>,
    //term_reprs: TermMap<String>,
    writer: &'a mut W,
    n_ff_sorts: usize,
    n_terms: usize,
    pub vars: HashMap<String, bool>,
}

fn get_logic_string() -> String {
    let mut ff = true;
    let mut bv = false;
    let mut nia = false;

    format!(
        "QF_{}{}{}",
        if bv { "BV" } else { "" },
        if ff { "FF" } else { "" },
        if nia { "NIA" } else { "" },
    )
}

impl<'a, W: 'a + Write> Printer<'a, W> {
    pub fn new(writer: &'a mut W) -> Self {
        Self {
            //sort_reprs: Default::default(),
            //term_reprs: Default::default(),
            writer,
            n_ff_sorts: 0,
            n_terms: 0,
            vars: HashMap::new(),
        }
    }

    // fn declare_sorts(&mut self, t: Term) {
    //     for sub_t in PostOrderIter::new(t) {
    //         let s = check(&sub_t);
    //         match &s {
    //             Sort::Field(f) => {
    //                 if !self.sort_reprs.contains_key(&s) {
    //                     let name = format!("FF{}", self.n_ff_sorts);
    //                     writeln!(
    //                         self.writer,
    //                         "(define-sort {} () (_ FiniteField {}))",
    //                         name,
    //                         f.modulus()
    //                     )
    //                     .unwrap();
    //                     self.sort_reprs.insert(s, name);
    //                     self.n_ff_sorts += 1;
    //                 }
    //             }
    //             Sort::BitVector(w) => {
    //                 let name = format!("(_ BitVec {})", w);
    //                 self.sort_reprs.insert(s, name);
    //             }
    //             Sort::Int => {
    //                 self.sort_reprs.insert(s, "Int".into());
    //             }
    //             Sort::Bool => {
    //                 self.sort_reprs.insert(s, "Bool".into());
    //             }
    //             _ => unimplemented!("sort {}", s),
    //         }
    //     }
    // }

    pub fn write_term(
        &mut self,
        op: String,
        left: String,
        ntl: analyzer::NodeType,
        right: String,
        ntr: analyzer::NodeType,
    ) -> String {
        //writeln!(&mut self.writer, "(assert ",).unwrap();
        let l;
        if (matches!(ntl, NodeType::Advice) || matches!(ntl, NodeType::Instance)) {
            l = left;
        } else {
            l = format!("({})", left);
        }

        let r;
        if (matches!(ntr, NodeType::Advice) || matches!(ntr, NodeType::Instance)) {
            r = right;
        } else {
            r = format!("({})", right);
        }

        let t = format!("ff.{} {} {}", op, l, r);
        //writeln!(&mut self.writer,"{}",t).unwrap();
        t
        //writeln!(&mut self.writer, ")").unwrap();
    }

    // fn write_term(&mut self, t: Term) {
    //     let mut close = 0;
    //     for sub_t in PostOrderIter::new(t.clone()) {
    //         let name = format!("let{}", self.n_terms);
    //         self.n_terms += 1;
    //         let op: Option<String> = match sub_t.op() {
    //             &PF_ADD => Some("ff.add".into()),
    //             &PF_MUL => Some("ff.mul".into()),
    //             &PF_NEG => Some("ff.neg".into()),
    //             Op::Const(Value::Field(f)) => {
    //                 let s = check(&sub_t);
    //                 Some(format!(
    //                     "(as ff{} {})",
    //                     f.i(),
    //                     self.sort_reprs.get(&s).unwrap()
    //                 ))
    //             }
    //             &INT_MUL => Some("*".into()),
    //             &INT_ADD => Some("+".into()),
    //             Op::BoolNaryOp(_)
    //             | Op::Const(Value::Bool(_))
    //             | Op::Implies
    //             | Op::Not
    //             | Op::Const(Value::Int(_))
    //             | Op::IntBinPred(_)
    //             | Op::Const(Value::BitVector(_))
    //             | Op::BvBinOp(_)
    //             | Op::BvBinPred(_)
    //             | Op::BvNaryOp(_)
    //             | Op::BvUnOp(_)
    //             | Op::Var(..)
    //             | Op::Ite
    //             | Op::Eq => Some(format!("{}", sub_t.op())),
    //             _ => unimplemented!("op in term: {}", sub_t),
    //         };
    //         if let Some(op) = op {
    //             close += 1;
    //             if sub_t.op().arity() == Some(0) {
    //                 writeln!(&mut self.writer, "  (let (({} {}))", name, op).unwrap();
    //             } else {
    //                 write!(&mut self.writer, "  (let (({} ({}", name, op).unwrap();
    //                 for c in sub_t.cs() {
    //                     write!(&mut self.writer, " {}", self.term_reprs.get(c).unwrap()).unwrap();
    //                 }
    //                 writeln!(&mut self.writer, ")))").unwrap();
    //             }
    //         }
    //         self.term_reprs.insert(sub_t.clone(), name);
    //     }
    //     writeln!(&mut self.writer, "  {}", self.term_reprs.get(&t).unwrap()).unwrap();
    //     for _ in 0..close {
    //         write!(&mut self.writer, ")").unwrap();
    //     }
    //     writeln!(&mut self.writer, "").unwrap();
    // }

    fn write_start(&mut self, prime: String) {
        writeln!(&mut self.writer, "(set-info :smt-lib-version 2.6)").unwrap();
        writeln!(&mut self.writer, "(set-info :category \"crafted\")").unwrap();
        writeln!(&mut self.writer, "(set-option :produce-models true)").unwrap();
        writeln!(&mut self.writer, "(set-option :incremental true)").unwrap();

        writeln!(&mut self.writer, "(set-logic {})", get_logic_string()).unwrap();
        writeln!(&mut self.writer, "(define-sort F () (_ FiniteField 11))").unwrap();
    }
    
    fn write_end(&mut self) {
        writeln!(&mut self.writer, "(check-sat)").unwrap();
    }

    fn write_var(&mut self, name: String) {
        if self.vars.contains_key(&name) {
            return;
        }
        self.vars.insert(name.clone(), true);
        writeln!(&mut self.writer, "(declare-fun {} () {})", name, "F").unwrap();
    }

    fn write_assert(&mut self, poly: String,value: String,nt: analyzer::NodeType,op:analyzer::Operation) {
        let a;
        if (matches!(nt, NodeType::Advice) || matches!(nt, NodeType::Instance)) {
            a = poly;
        } else {
            a = format!("({})", poly);
        }
        if (matches!(op,analyzer::Operation::Equal)) {
            writeln!(&mut self.writer, "(assert ( = {} (as ff{} F)))", a,value).unwrap();
        } else {
            writeln!(&mut self.writer, "(assert (not ( = {} (as ff{} F))))", a,value).unwrap();
        }
    }

    fn write_assert_bool(&mut self, poly: String,op:analyzer::Operation){
        if (matches!(op,analyzer::Operation::Or)) {
            writeln!(&mut self.writer, "(assert (or {}))", poly).unwrap();
        } else if (matches!(op,analyzer::Operation::And)) {
            writeln!(&mut self.writer, "(assert (and {}))", poly).unwrap();
        }
    }

    fn get_assert(&mut self, poly: String, value: String, nt: analyzer::NodeType,op:analyzer::Operation) ->String {
        let a;
        if (matches!(nt, NodeType::Advice) || matches!(nt, NodeType::Instance)) {
            a = poly;
        } else {
            a = format!("({})", poly);
        }
        if (matches!(op,analyzer::Operation::Equal)) {
            format!( "( = {} (as ff{} F))", a,value)
        } else {
            format!( "(not ( = {} (as ff{} F)))", a,value)
        }
    }

    pub fn write_get_value(&mut self, var: String){
        writeln!(&mut self.writer, "(get-value ({}))", var).unwrap();
    }

    pub fn write_get_model(&mut self){
        writeln!(&mut self.writer, "(get-model)").unwrap();
    }
    
    pub fn write_push(&mut self,number:u8){
        if number == 1 {
            writeln!(&mut self.writer, "(push)").unwrap();
        } else {
            writeln!(&mut self.writer, "(push {})", number).unwrap();
        }
    }
    
    pub fn write_pop(&mut self,number:u8){
        if number == 1 {
            writeln!(&mut self.writer, "(pop)").unwrap();
        } else {
            writeln!(&mut self.writer, "(pop {})", number).unwrap();
        }   
    }

    pub fn get_or(&mut self,or_str:String) -> String{
        format!("(or {})", or_str)
    }
    
    pub fn get_and(&mut self,or_str:String) -> String{
        format!("(and {})", or_str)
    }
}

pub fn write_start<W: Write>(w: &mut W, prime: String) -> Printer<W> {
    let mut p = Printer::new(w);
    p.write_start(prime);
    return p;
}

pub fn write_end<W: Write>(p: &mut Printer<W>) {
    p.write_end();
}

pub fn write_var(p: &mut Printer<File>, name: String) {
    p.write_var(name);
}

pub fn write_term<W: Write>(
    p: &mut Printer<W>,
    op: String,
    left: String,
    ntl: analyzer::NodeType,
    right: String,
    ntr: analyzer::NodeType,
) -> String {
    p.write_term(op, left, ntl, right, ntr)
}

pub fn write_assert(p: &mut Printer<File>, poly: String,value: String,nt: analyzer::NodeType,op:analyzer::Operation) {
    p.write_assert(poly,value,nt,op);
}

pub fn write_assert_bool(p: &mut Printer<File>, poly: String,op:analyzer::Operation) {
    p.write_assert_bool(poly,op);
}

pub fn get_assert(p: &mut Printer<File>, poly: String,value: String,nt: analyzer::NodeType,op:analyzer::Operation)->String {
    p.get_assert(poly,value,nt,op)
}

pub fn write_get_value(p: &mut Printer<File>, var: String){
    p.write_get_value(var);
}

pub fn write_get_model(p: &mut Printer<File>){
    p.write_get_model();
}

pub fn write_push(p: &mut Printer<File>,number:u8){
    p.write_push(number);
}

pub fn write_pop(p: &mut Printer<File>,number:u8){
    p.write_pop(number);
}

pub fn get_or(p: &mut Printer<File>,or_str:String)->String{
    p.get_or(or_str)
}

pub fn get_and(p: &mut Printer<File>,or_str:String)->String{
    p.get_and(or_str)
}
