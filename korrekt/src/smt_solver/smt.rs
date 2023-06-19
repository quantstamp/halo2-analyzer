use std::collections::HashMap;
use std::fs::File;
use std::io::Write;

use crate::circuit_analyzer::analyzer::{self, NodeType};

pub struct Printer<'a, W: 'a> {
    writer: &'a mut W,
    pub vars: HashMap<String, bool>,
}

fn get_logic_string() -> String {
    let ff = true;
    let bv = false;
    let nia = false;

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
            writer,
            vars: HashMap::new(),
        }
    }
    /// Constructs a term string based on the provided operator and operands.
    ///
    /// This function constructs a term string by combining the operator and operands,
    /// considering the node types of the operands.
    ///
    pub fn write_term(
        &mut self,
        op: String,
        left: String,
        ntl: analyzer::NodeType,
        right: String,
        ntr: analyzer::NodeType,
    ) -> String {
        let l = if (matches!(ntl, NodeType::Advice)
            || matches!(ntl, NodeType::Instance)
            || matches!(ntl, NodeType::Fixed)
            || matches!(ntl, NodeType::Constant))
        {
            left
        } else {
            format!("({})", left)
        };

        let r = if (matches!(ntr, NodeType::Advice)
            || matches!(ntr, NodeType::Instance)
            || matches!(ntr, NodeType::Fixed)
            || matches!(ntr, NodeType::Constant))
        {
            right
        } else {
            format!("({})", right)
        };
        let t = format!("ff.{} {} {}", op, l, r);
        t
    }
    /// Writes the start of the SMT-LIB file.
    ///
    /// This function writes the initial lines at the start of the SMT-LIB file,
    /// including the SMT-LIB version, category, options, logic, and the definition of the finite field.
    ///
    fn write_start(&mut self, prime: String) {
        writeln!(&mut self.writer, "(set-info :smt-lib-version 2.6)").unwrap();
        writeln!(&mut self.writer, "(set-info :category \"crafted\")").unwrap();
        writeln!(&mut self.writer, "(set-option :produce-models true)").unwrap();
        writeln!(&mut self.writer, "(set-option :incremental true)").unwrap();

        writeln!(&mut self.writer, "(set-logic {})", get_logic_string()).unwrap();
        writeln!(
            &mut self.writer,
            "(define-sort F () (_ FiniteField {}))",
            prime
        )
        .unwrap();
    }
    /// Writes the end of the SMT-LIB file.
    ///
    /// This function writes the `(check-sat)` command at the end of the SMT-LIB file.
    ///
    fn write_end(&mut self) {
        writeln!(&mut self.writer, "(check-sat)").unwrap();
    }
    /// Writes a variable declaration in the SMT-LIB file.
    ///
    /// This function writes a variable declaration for a variable with the given name
    /// in the SMT-LIB file. The variable is declared to be of sort `F` (finite field).
    /// If a variable with the same name has already been declared, this function does nothing.
    ///
    fn write_var(&mut self, name: String) {
        if self.vars.contains_key(&name) {
            return;
        }
        self.vars.insert(name.clone(), true);
        writeln!(&mut self.writer, "(declare-fun {} () F)", name).unwrap();
    }
    /// Writes an assertion in the SMT-LIB file.
    ///
    /// This function writes an assertion in the SMT-LIB file based on the given polynomial, value,
    /// node type, and operation. The polynomial and value are converted to SMT-LIB syntax.
    /// If the node type is advice, instance, or fixed, the polynomial is used directly;
    /// otherwise, it is wrapped in parentheses. The operation determines whether the assertion
    /// is an equality or inequality.
    ///
    fn write_assert(
        &mut self,
        poly: String,
        value: String,
        nt: analyzer::NodeType,
        op: analyzer::Operation,
    ) {
        let a = if (matches!(nt, NodeType::Advice)
            || matches!(nt, NodeType::Instance)
            || matches!(nt, NodeType::Fixed))
        {
            poly
        } else {
            format!("({})", poly)
        };
        if matches!(op, analyzer::Operation::Equal) {
            writeln!(&mut self.writer, "(assert ( = {} (as ff{} F)))", a, value).unwrap();
        } else if matches!(op, analyzer::Operation::NotEqual) {
            writeln!(
                &mut self.writer,
                "(assert (not ( = {} (as ff{} F))))",
                a, value
            )
            .unwrap();
        }
    }
    /// Writes a boolean assertion in the SMT-LIB file.
    ///
    /// This function writes a boolean assertion in the SMT-LIB file based on the given polynomial
    /// and operation. The polynomial represents a boolean expression, and the operation determines
    /// whether it is combined with an OR or an AND operator.
    ///
    fn write_assert_bool(&mut self, poly: String, op: analyzer::Operation) {
        if matches!(op, analyzer::Operation::Or) {
            writeln!(&mut self.writer, "(assert (or {}))", poly).unwrap();
        } else if matches!(op, analyzer::Operation::And) {
            writeln!(&mut self.writer, "(assert (and {}))", poly).unwrap();
        }
    }
    /// Returns a string representing an assertion in the SMT-LIB format.
    ///
    /// This function returns a string representing an assertion in the SMT-LIB format based on the given
    /// polynomial, value, node type, and operation. The polynomial represents an expression, the value is
    /// the target value for the assertion, the node type specifies the type of the expression, and the
    /// operation determines whether it is an equality or inequality assertion.
    ///
    fn get_assert(
        &mut self,
        poly: String,
        value: String,
        nt: analyzer::NodeType,
        op: analyzer::Operation,
    ) -> String {
        let a = if (matches!(nt, NodeType::Advice)
            || matches!(nt, NodeType::Instance)
            || matches!(nt, NodeType::Fixed))
        {
            poly
        } else {
            format!("({})", poly)
        };
        if matches!(op, analyzer::Operation::Equal) {
            format!("( = {} (as ff{} F))", a, value)
        } else if matches!(op, analyzer::Operation::NotEqual) {
            format!("(not ( = {} (as ff{} F)))", a, value)
        } else {
            String::new()
        }
    }
    /// Writes a "get-value" command in the SMT-LIB file to retrieve the value of a variable.
    ///
    /// This function writes a "get-value" command in the SMT-LIB file to retrieve the value of the specified variable.
    /// The variable's value will be included in the model result when solving the SMT problem.
    ///
    pub fn write_get_value(&mut self, var: String) {
        writeln!(&mut self.writer, "(get-value ({}))", var).unwrap();
    }
    /// Writes a "push" command in the SMT-LIB file to create a new scope.
    ///
    /// This function writes a "push" command in the SMT-LIB file to create a new scope. The optional
    /// parameter `number` specifies the number of levels to push. If `number` is 1, a single level
    /// is pushed. Otherwise, the specified number of levels is pushed.
    ///
    pub fn write_push(&mut self, number: u8) {
        if number == 1 {
            writeln!(&mut self.writer, "(push)").unwrap();
        } else {
            writeln!(&mut self.writer, "(push {})", number).unwrap();
        }
    }
    /// Writes a "pop" command in the SMT-LIB file to remove one or more levels from the current scope.
    ///
    /// This function writes a "pop" command in the SMT-LIB file to remove one or more levels from the current scope.
    /// The optional parameter `number` specifies the number of levels to pop. If `number` is 1, a single level is popped.
    /// Otherwise, the specified number of levels is popped.
    ///
    pub fn write_pop(&mut self, number: u8) {
        if number == 1 {
            writeln!(&mut self.writer, "(pop)").unwrap();
        } else {
            writeln!(&mut self.writer, "(pop {})", number).unwrap();
        }
    }
    /// Returns a string representing a logical OR operation in the SMT-LIB format.
    ///
    /// This function takes a string `or_str` representing multiple logical expressions and returns a string
    /// representing their logical OR operation in the SMT-LIB format.
    ///
    pub fn get_or(&mut self, or_str: String) -> String {
        format!("(or {})", or_str)
    }
    /// Returns a string representing a logical AND operation in the SMT-LIB format.
    ///
    /// This function takes a string `and_str` representing multiple logical expressions and returns a string
    /// representing their logical AND operation in the SMT-LIB format.
    ///
    pub fn get_and(&mut self, or_str: String) -> String {
        format!("(and {})", or_str)
    }
}

pub fn write_start<W: Write>(w: &mut W, prime: String) -> Printer<W> {
    let mut p = Printer::new(w);
    p.write_start(prime);
    p
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

pub fn write_assert(
    p: &mut Printer<File>,
    poly: String,
    value: String,
    nt: analyzer::NodeType,
    op: analyzer::Operation,
) {
    p.write_assert(poly, value, nt, op);
}

pub fn write_assert_bool(p: &mut Printer<File>, poly: String, op: analyzer::Operation) {
    p.write_assert_bool(poly, op);
}

pub fn get_assert(
    p: &mut Printer<File>,
    poly: String,
    value: String,
    nt: analyzer::NodeType,
    op: analyzer::Operation,
) -> String {
    p.get_assert(poly, value, nt, op)
}

pub fn write_get_value(p: &mut Printer<File>, var: String) {
    p.write_get_value(var);
}

pub fn write_push(p: &mut Printer<File>, number: u8) {
    p.write_push(number);
}

pub fn write_pop(p: &mut Printer<File>, number: u8) {
    p.write_pop(number);
}

pub fn get_or(p: &mut Printer<File>, or_str: String) -> String {
    p.get_or(or_str)
}

pub fn get_and(p: &mut Printer<File>, and_str: String) -> String {
    p.get_and(and_str)
}
