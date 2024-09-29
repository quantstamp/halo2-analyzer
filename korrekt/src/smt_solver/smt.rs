use anyhow::{anyhow, Result};
use std::io::Write;

use crate::circuit_analyzer::analyzer::{self, NodeCategory, NodeType};

#[derive(Debug)]
pub struct Printer<'a, W: 'a> {
    writer: &'a mut W,
}

fn get_logic_string() -> String {
    String::from("ALL")
}

impl<'a, W: 'a + Write> Printer<'a, W> {
    pub fn new(writer: &'a mut W) -> Self {
        Self { writer }
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
        let l = if (matches!(ntl.category(), NodeCategory::Variable)
            || matches!(ntl.category(), NodeCategory::Constant))
        {
            left
        } else {
            format!("({})", left)
        };

        let r = if (matches!(ntr.category(), NodeCategory::Variable)
            || matches!(ntr.category(), NodeCategory::Constant))
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
    pub fn write_start(&mut self, prime: String) {
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
    pub fn write_end(&mut self) {
        writeln!(&mut self.writer, "(check-sat)").unwrap();
    }
    /// Writes a variable declaration in the SMT-LIB file.
    ///
    /// This function writes a variable declaration for a variable with the given name
    /// in the SMT-LIB file. The variable is declared to be of sort `F` (finite field).
    /// If a variable with the same name has already been declared, this function does nothing.
    ///
    pub fn write_var(&mut self, name: String) {
        writeln!(&mut self.writer, "(declare-fun {} () F)", name).unwrap();
    }
    /// Declares a function in the SMT-LIB file.
    ///
    /// This function declares a new SMT-LIB function with the specified name, input types, and output type.
    /// The `name` parameter specifies the name of the function to be declared.
    /// The `inputs` parameter is a space-separated list of types representing the function's input parameters.
    /// The `outputs` parameter specifies the type of the function's output.
    ///
    ///
    pub fn write_declare_fn(&mut self, name: String, inputs: String, outputs: String) {
        writeln!(
            &mut self.writer,
            "(declare-fun {} ( {} ) {})",
            name, inputs, outputs
        )
        .unwrap();
    }
    pub fn write_define_fn(&mut self, name: String, inputs: String, outputs: String, body: String) {
        writeln!(
            &mut self.writer,
            "(define-fun {} ( {} ) {} {})",
            name, inputs, outputs, body
        )
        .unwrap();
    }

    /// Writes an assertion in the SMT-LIB file.
    ///
    /// This function writes an assertion in the SMT-LIB file based on the given polynomial, value,
    /// node type, and operation. The polynomial and value are converted to SMT-LIB syntax.
    /// If the node type is advice, instance, or fixed, the polynomial is used directly;
    /// otherwise, it is wrapped in parentheses. The operation determines whether the assertion
    /// is an equality or inequality.
    ///
    pub fn write_assert(
        &mut self,
        poly: String,
        value: String,
        nt: analyzer::NodeType,
        op: analyzer::Operation,
    ) {
        let a = if (matches!(nt.category(), NodeCategory::Variable)
            || matches!(nt.category(), NodeCategory::Constant))
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
    pub fn write_assert_bool(&mut self, poly: String, op: analyzer::Operation) {
        if poly.is_empty() {
            return;
        }
        if matches!(op, analyzer::Operation::Or) {
            writeln!(&mut self.writer, "(assert (or {}))", poly).unwrap();
        } else if matches!(op, analyzer::Operation::And) {
            writeln!(&mut self.writer, "(assert (and {}))", poly).unwrap();
        }
    }
    pub fn write_assert_boolean_func(&mut self, func_name: String, inputs: String) {
        writeln!(&mut self.writer, "(assert ({} {}))", func_name, inputs).unwrap();
    }
    /// Returns a string representing an assertion in the SMT-LIB format.
    ///
    /// This function returns a string representing an assertion in the SMT-LIB format based on the given
    /// polynomial, value, node type, and operation. The polynomial represents an expression, the value is
    /// the target value for the assertion, the node type specifies the type of the expression, and the
    /// operation determines whether it is an equality or inequality assertion.
    ///
    pub fn get_assert(
        &mut self,
        poly: String,
        value: String,
        nt: analyzer::NodeType,
        op: analyzer::Operation,
    ) -> Result<String> {
        let a = if (matches!(nt.category(), NodeCategory::Variable)
            || matches!(nt.category(), NodeCategory::Constant))
        {
            poly
        } else {
            format!("({})", poly)
        };
        if matches!(op, analyzer::Operation::Equal) {
            Ok(format!("( = {} (as ff{} F))", a, value))
        } else if matches!(op, analyzer::Operation::NotEqual) {
            Ok(format!("(not ( = {} (as ff{} F)))", a, value))
        } else {
            Err(anyhow!("Invalid Operation: {:?}.", op))
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
        if or_str.is_empty() {
            return String::from("");
        }
        format!("(or {})", or_str)
    }
    /// Returns a string representing a logical AND operation in the SMT-LIB format.
    ///
    /// This function takes a string `and_str` representing multiple logical expressions and returns a string
    /// representing their logical AND operation in the SMT-LIB format.
    ///
    pub fn get_and(&mut self, or_str: String) -> String {
        if or_str.is_empty() {
            return String::from("");
        }
        format!("(and {})", or_str)
    }
}
