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
    /// A function call, with argument(s).
    Call(Call),
    /// An operator, with lefthand and righthand expression.
    BinOp(Op, Box<Expr>, Box<Expr>),
    /// An unary operator.
    UnOp(UnOp, Box<Expr>),
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

/// The unary operators known to G-code.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Plus,
    Minus,
}

/// A function call, with all functions known to G-code.
#[derive(Debug)]
pub enum Call {
    Exists(ParId),
    Atan(Box<Expr>, Box<Expr>),
    Abs(Box<Expr>),
    Acos(Box<Expr>),
    Asin(Box<Expr>),
    Cos(Box<Expr>),
    Exp(Box<Expr>),
    Fix(Box<Expr>),
    Fup(Box<Expr>),
    Round(Box<Expr>),
    Ln(Box<Expr>),
    Sin(Box<Expr>),
    Sqrt(Box<Expr>),
    Tan(Box<Expr>),
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

fn wrap_op(f: &mut Formatter, ex: &Expr) -> fmt::Result {
    if let Expr::BinOp(..) = ex {
        write!(f, "[{}]", ex)
    } else {
        Display::fmt(&ex, f)
    }
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
        // LinuxCNC requires function calls to be parenthesized here, although
        // it doesn't require it for parameter references elsewhere.
        if let ParId::Indirect(id) = &self.id {
            if let Expr::Call(..) = **id {
                write!(f, "#[{}]=", self.id)?;
                return wrap_op(f, &self.value);
            }
        }
        write!(f, "#{}=", self.id)?;
        wrap_op(f, &self.value)
    }
}

impl Display for ParId {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            ParId::Numeric(n) => Display::fmt(n, f),
            ParId::Named(n) => write!(f, "<{}>", n),
            ParId::Indirect(ex) => wrap_op(f, ex),
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Expr::Num(n) => Display::fmt(n, f),
            Expr::Par(id) => write!(f, "#{}", id),
            Expr::Call(func) => Display::fmt(func, f),
            Expr::BinOp(op, lhs, rhs) => {
                wrap_op(f, lhs)?;
                write!(f, " {} ", op)?;
                wrap_op(f, rhs)
            }
            Expr::UnOp(op, rhs) => {
                Display::fmt(op, f)?;
                wrap_op(f, rhs)
            }
        }
    }
}

impl Display for Op {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str(match self {
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

impl Display for UnOp {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str(match self {
            UnOp::Plus => "+",
            UnOp::Minus => "-",
        })
    }
}

impl Display for Word {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Word::Gcode(n)   => { f.write_str("G")?; wrap_op(f, n) },
            Word::Mcode(n)   => { f.write_str("M")?; wrap_op(f, n) },
            Word::Feed(n)    => { f.write_str("F")?; wrap_op(f, n) },
            Word::Spindle(n) => { f.write_str("S")?; wrap_op(f, n) },
            Word::Tool(n)    => { f.write_str("T")?; wrap_op(f, n) },
            Word::Arg(a, n)  => { Display::fmt(a, f)?; wrap_op(f, n) },
        }
    }
}

impl Display for Arg {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.write_str(match self {
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

impl Display for Call {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Call::Atan(arg1, arg2) => write!(f, "ATAN[{}]/[{}]", arg1, arg2),
            Call::Exists(par)      => write!(f, "EXISTS[#{}]", par),
            Call::Abs(arg)         => write!(f, "ABS[{}]", arg),
            Call::Acos(arg)        => write!(f, "ACOS[{}]", arg),
            Call::Asin(arg)        => write!(f, "ASIN[{}]", arg),
            Call::Cos(arg)         => write!(f, "COS[{}]", arg),
            Call::Exp(arg)         => write!(f, "EXP[{}]", arg),
            Call::Fix(arg)         => write!(f, "FIX[{}]", arg),
            Call::Fup(arg)         => write!(f, "FUP[{}]", arg),
            Call::Round(arg)       => write!(f, "ROUND[{}]", arg),
            Call::Ln(arg)          => write!(f, "LN[{}]", arg),
            Call::Sin(arg)         => write!(f, "SIN[{}]", arg),
            Call::Sqrt(arg)        => write!(f, "SQRT[{}]", arg),
            Call::Tan(arg)         => write!(f, "TAN[{}]", arg),
        }
    }
}
