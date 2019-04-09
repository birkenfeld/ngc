// Copyright (c) 2019 Georg Brandl.  Licensed under the Apache License,
// Version 2.0 <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0>
// or the MIT license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at
// your option. This file may not be copied, modified, or distributed except
// according to those terms.

use std::fmt::{self, Display, Formatter};

#[derive(Debug)]
pub struct Program {
    pub filename: String,
    pub blocks: Vec<Block>,
}

#[derive(Debug)]
pub struct Block {
    pub lineno: usize,
    pub instructions: Vec<Instr>,
    pub assignments: Vec<ParAssign>,
}

#[derive(Debug)]
pub struct ParAssign {
    pub id: ParId,
    pub value: Expr,
}

#[derive(Debug)]
pub enum ParId {
    Named(String),
    Numeric(u16),
    Indirect(Box<Expr>),
}

#[derive(Debug)]
pub enum Expr {
    Num(f64),
    Par(ParId),
    Call(String, Vec<Expr>),
    Op(Op, Box<Expr>, Box<Expr>),
}

#[derive(Debug)]
pub enum Instr {
    Feed(Expr),
    Spindle(Expr),
    Tool(Expr),

    // These should be individual enum values as well...
    Gcode(u16, Vec<(Arg, Expr)>),
    Mcode(u16, Vec<(Arg, Expr)>),
    // This should disappear
    Arg(Arg, Expr),
}

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
        for ass in &self.assignments {
            write!(f, "{} ", ass)?;
        }
        for instr in &self.instructions {
            write!(f, "{} ", instr)?;
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

impl Display for Instr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Instr::Feed(n) => write!(f, "F{}", n),
            Instr::Spindle(n) => write!(f, "S{}", n),
            Instr::Tool(n) => write!(f, "T{}", n),
            // XXX: use arguments
            Instr::Gcode(n, _) => {
                let nf = (*n as f64) / 10.;
                write!(f, "G{}", nf)
            },
            Instr::Mcode(n, _) => write!(f, "M{}", n),
            // This should disappear
            Instr::Arg(a, n) => write!(f, "{}{}", a, n)
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
