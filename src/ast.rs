// Copyright (c) 2019 Georg Brandl.  Licensed under the Apache License,
// Version 2.0 <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0>
// or the MIT license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at
// your option. This file may not be copied, modified, or distributed except
// according to those terms.

//! Data types to represent a parsed G-code program.
//!
//! The syntax and semantics are described on the [G-code reference] page from
//! LinuxCNC.
//!
//! [G-code reference]: http://linuxcnc.org/docs/html/gcode/overview.html

use std::fmt::{self, Display, Formatter};

/// A whole program, consisting of blocks.  Each block corresponds to a line in
/// the source code.
#[derive(Debug, Default)]
pub struct Program {
    /// Original filename of the program, as given to `parse()`.
    pub filename: String,
    /// Blocks of the program.
    pub blocks: Vec<Block>,
}

/// A block (source line), which contains a number of words and parameter
/// assignments.
#[derive(Debug, Default)]
pub struct Block {
    /// Line number in the original file.
    pub lineno: usize,
    /// True if the line was "block deleted"; i.e. starts with a slash.
    ///
    /// Execution of these lines can be switched with a global flag.
    pub blockdel: bool,
    /// Words (e.g. `G0` or `X5.2`) found in the line.  The ordering is
    /// irrelevant to G-code.
    pub words: Vec<Word>,
    /// Assignments (e.g. `#1=4.2`) found in the line.  The ordering, and
    /// ordering with respect to words, are irrelevant to G-code.
    pub assignments: Vec<ParAssign>,
}

/// A parameter assignment.
#[derive(Debug)]
pub struct ParAssign {
    pub id: ParId,
    pub value: Expr,
}

/// A reference to a parameter.
///
/// This can be a numeric parameter, a named parameter, or an indirect
/// reference, where the parameter number is determined from an expression.
#[derive(Debug)]
pub enum ParId {
    Named(String),
    Numeric(u16),
    Indirect(Box<Expr>),
}

/// A G-code expression.
#[derive(Debug)]
pub enum Expr {
    /// A simple number.  G-code only knows floating-point numbers; in any place
    /// that requires integers, a check for an integral value (or something very
    /// close to it) is performed at execution time.
    Num(f64),
    /// A parameter reference.
    Par(ParId),
    /// A function call, with arguments.  There is a small list of built-in
    /// functions, most of which take one argument.  `ATAN` takes two arguments.
    Call(String, Vec<Expr>),
    // TODO: unary ops (+, -) exist although they are not documented.
    /// An operator, with lefthand and righthand expression.
    Op(Op, Box<Expr>, Box<Expr>),
}

/// A G-code "word", i.e. indication letter and value.
///
/// The value can be a complex expression introduced in brackets, even for `G`
/// and `M` words.
#[derive(Debug)]
pub enum Word {
    Gcode(Expr),
    Mcode(Expr),
    Feed(Expr),
    Spindle(Expr),
    Tool(Expr),
    Arg(Arg, Expr),
}

/// The binary operators known to G-code.
///
/// For Boolean inputs, all nonzero numbers are true.  Boolean results are
/// represented as 0.0 and 1.0.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Op {
    Exp,
    Mul,
    Div,
    Mod,
    Add,
    Sub,
    Eq,
    Ne,
    Gt,
    Ge,
    Lt,
    Le,
    And,
    Or,
    Xor,
}

/// The possible argument words (i.e. all words except N, G, M, F, S, T).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Arg {
    // axis words
    AxisA,
    AxisB,
    AxisC,
    AxisU,
    AxisV,
    AxisW,
    AxisX,
    AxisY,
    AxisZ,
    // arc parameters
    ArcI,
    ArcJ,
    ArcK,
    // variable meaning params
    ParamD,
    ParamE,
    ParamH,
    ParamL,
    ParamP,
    ParamQ,
    ParamR,
}

impl Display for Program {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        for block in &self.blocks {
            write!(f, "{}\n", block)?;
        }
        Ok(())
    }
}

impl Display for Block {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        if self.blockdel {
            write!(f, "/ ")?;
        }
        for ass in &self.assignments {
            write!(f, "{} ", ass)?;
        }
        for word in &self.words {
            write!(f, "{} ", word)?;
        }
        Ok(())
    }
}

impl Display for ParAssign {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "#{}={}", self.id, self.value)
    }
}

impl Display for ParId {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            ParId::Numeric(n) => write!(f, "{}", n),
            ParId::Named(n) => write!(f, "<{}>", n),
            ParId::Indirect(ex) => write!(f, "[{}]", ex),
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Expr::Num(n) => write!(f, "{}", n),
            Expr::Par(id) => write!(f, "#{}", id),
            Expr::Call(func, args) => if args.len() == 2 {
                write!(f, "{}[{}]/[{}]", func, args[0], args[1])
            } else {
                write!(f, "{}[{}]", func, args[0])
            },
            Expr::Op(op, lhs, rhs) => {
                match **lhs {
                    Expr::Op(..) => write!(f, "[{}] {} ", lhs, op)?,
                    _ => write!(f, "{} {} ", lhs, op)?,
                }
                match **rhs {
                    Expr::Op(..) => write!(f, "[{}]", rhs),
                    _ => write!(f, "{}", rhs),
                }
            }
        }
    }
}

impl Display for Op {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", match self {
            Op::Exp => "**",
            Op::Mul => "*",
            Op::Div => "/",
            Op::Mod => "MOD",
            Op::Add => "+",
            Op::Sub => "-",
            Op::Eq  => "EQ",
            Op::Ne  => "NE",
            Op::Gt  => "GT",
            Op::Ge  => "GE",
            Op::Lt  => "LT",
            Op::Le  => "LE",
            Op::And => "AND",
            Op::Or  => "OR",
            Op::Xor => "XOR",
        })
    }
}

impl Display for Word {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Word::Gcode(n) => write!(f, "G{}", n),
            Word::Mcode(n) => write!(f, "M{}", n),
            Word::Feed(n) => write!(f, "F{}", n),
            Word::Spindle(n) => write!(f, "S{}", n),
            Word::Tool(n) => write!(f, "T{}", n),
            Word::Arg(a, n) => write!(f, "{}{}", a, n)
        }
    }
}

impl Display for Arg {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", match self {
            Arg::AxisA => "A",
            Arg::AxisB => "B",
            Arg::AxisC => "C",
            Arg::AxisU => "U",
            Arg::AxisV => "V",
            Arg::AxisW => "W",
            Arg::AxisX => "X",
            Arg::AxisY => "Y",
            Arg::AxisZ => "Z",
            Arg::ArcI  => "I",
            Arg::ArcJ  => "J",
            Arg::ArcK  => "K",
            Arg::ParamD => "D",
            Arg::ParamE => "E",
            Arg::ParamH => "H",
            Arg::ParamL => "L",
            Arg::ParamP => "P",
            Arg::ParamQ => "Q",
            Arg::ParamR => "R",
        })
    }
}
