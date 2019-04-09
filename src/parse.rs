// Copyright (c) 2019 Georg Brandl.  Licensed under the Apache License,
// Version 2.0 <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0>
// or the MIT license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at
// your option. This file may not be copied, modified, or distributed except
// according to those terms.

use lazy_static::lazy_static;
use pest_derive::Parser;
use pest::{Parser, iterators::{Pair, Pairs}};
use pest::prec_climber::{PrecClimber, Operator, Assoc};

use crate::ast::*;

#[derive(Parser)]
#[grammar = "gcode.pest"]
pub struct GcodeParser;

#[derive(Debug)]
pub enum Error {
    Parse(pest::error::Error<Rule>),
    Other(String),  // XXX flesh out
}

impl From<pest::error::Error<Rule>> for Error {
    fn from(e: pest::error::Error<Rule>) -> Self {
        Error::Parse(e)
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Error::Parse(e) => write!(f, "{}", e),
            Error::Other(e) => write!(f, "{}", e),
        }
    }
}

impl std::error::Error for Error {}

type PR<T> = Result<T, Error>;


lazy_static! {
    static ref PREC_CLIMBER: PrecClimber<Rule> = {
        use Rule::*;
        use Assoc::*;

        PrecClimber::new(vec![
            // lowest
            Operator::new(op_and, Left) | Operator::new(op_or, Left) |
            Operator::new(op_xor, Left),

            Operator::new(op_eq, Left) | Operator::new(op_ne, Left) |
            Operator::new(op_gt, Left) | Operator::new(op_ge, Left) |
            Operator::new(op_lt, Left) | Operator::new(op_le, Left),

            Operator::new(op_add, Left) | Operator::new(op_sub, Left),

            Operator::new(op_mul, Left) | Operator::new(op_div, Left) |
            Operator::new(op_mod, Left),
            // highest
            Operator::new(op_exp, Right),
        ])
    };
}

fn make_num(inp: &str) -> PR<f64> {
    let mut buf = String::with_capacity(inp.len());
    let mut com = false;
    // get rid of spaces and comments
    for ch in inp.chars() {
        match ch {
            ' ' | '\t' => (),
            ')' => com = false,
            '(' => com = true,
            _ if com => (),
            _ => buf.push(ch),
        }
    }
    buf.parse().map_err(|_| Error::Other(format!("invalid number: {:?}", inp)))
}

fn make_int(inp: f64, mul: f64) -> PR<u16> {
    let v = inp * mul;
    if (v.round() - v).abs() < 0.0001 && v >= 0. && v <= 65535. {
        Ok(v.round() as u16)
    } else {
        Err(Error::Other(format!("number invalid here: {:?}", inp)))
    }
}

fn make_expr(expr_pair: Pair<Rule>) -> PR<Expr> {
    let pairs = expr_pair.into_inner();
    PREC_CLIMBER.climb(
        pairs,
        |pair| match pair.as_rule() {
            Rule::num => Ok(Expr::Num(make_num(pair.as_str())?)),
            Rule::expr => make_expr(pair),
            Rule::expr_call => {
                let func = pair.as_str().split("[").next().unwrap();
                let mut inner = pair.into_inner().into_iter();
                let x = make_expr(inner.next().unwrap())?;
                Ok(Expr::Call(func.into(), vec![x]))
            }
            Rule::expr_atan => {
                let mut inner = pair.into_inner().into_iter();
                let x = make_expr(inner.next().unwrap())?;
                let y = make_expr(inner.next().unwrap())?;
                Ok(Expr::Call("ATAN".into(), vec![x, y]))
            }
            Rule::par_ref => Ok(Expr::Par(make_par_ref(pair)?)),
            _ => unreachable!("while climbing, found {:?}", pair.as_rule()),
        },
        |lhs, op, rhs| match op.as_rule() {
            Rule::op_exp => Ok(Expr::Op(Op::Exp, Box::new(lhs?), Box::new(rhs?))),
            Rule::op_mul => Ok(Expr::Op(Op::Mul, Box::new(lhs?), Box::new(rhs?))),
            Rule::op_div => Ok(Expr::Op(Op::Div, Box::new(lhs?), Box::new(rhs?))),
            Rule::op_mod => Ok(Expr::Op(Op::Mod, Box::new(lhs?), Box::new(rhs?))),
            Rule::op_add => Ok(Expr::Op(Op::Add, Box::new(lhs?), Box::new(rhs?))),
            Rule::op_sub => Ok(Expr::Op(Op::Sub, Box::new(lhs?), Box::new(rhs?))),
            Rule::op_eq  => Ok(Expr::Op(Op::Eq,  Box::new(lhs?), Box::new(rhs?))),
            Rule::op_ne  => Ok(Expr::Op(Op::Ne,  Box::new(lhs?), Box::new(rhs?))),
            Rule::op_gt  => Ok(Expr::Op(Op::Gt,  Box::new(lhs?), Box::new(rhs?))),
            Rule::op_ge  => Ok(Expr::Op(Op::Ge,  Box::new(lhs?), Box::new(rhs?))),
            Rule::op_lt  => Ok(Expr::Op(Op::Lt,  Box::new(lhs?), Box::new(rhs?))),
            Rule::op_le  => Ok(Expr::Op(Op::Le,  Box::new(lhs?), Box::new(rhs?))),
            Rule::op_and => Ok(Expr::Op(Op::And, Box::new(lhs?), Box::new(rhs?))),
            Rule::op_or  => Ok(Expr::Op(Op::Or,  Box::new(lhs?), Box::new(rhs?))),
            Rule::op_xor => Ok(Expr::Op(Op::Xor, Box::new(lhs?), Box::new(rhs?))),
            _ => unreachable!(),
        },
    )
}

fn make_instr(pairs: Pairs<Rule>) -> PR<Option<Instr>> {
    let mut pairs = pairs.into_iter();
    let letter = pairs.next().unwrap().as_str();
    let value = make_expr(pairs.next().unwrap())?;
    match letter {
        "o" | "O" => Err(Error::Other("O word control flow is not supported".into())),
        "n" | "N" => Ok(None),  // line numbers are accepted but ignoredxs
        "f" | "F" => Ok(Some(Instr::Feed(value))),
        "s" | "S" => Ok(Some(Instr::Spindle(value))),
        "t" | "T" => Ok(Some(Instr::Tool(value))),
        "g" | "G" => match value {
            Expr::Num(n) => Ok(Some(Instr::Gcode(make_int(n, 10.)?, vec![]))),
            _ => Err(Error::Other("G words must have a constant numeric value".into())),
        },
        "m" | "M" => match value {
            Expr::Num(n) => Ok(Some(Instr::Mcode(make_int(n, 1.)?, vec![]))),
            _ => Err(Error::Other("M words must have a constant numeric value".into())),
        },
        "a" | "A" => Ok(Some(Instr::Arg(Arg::AxisA, value))),
        "b" | "B" => Ok(Some(Instr::Arg(Arg::AxisB, value))),
        "c" | "C" => Ok(Some(Instr::Arg(Arg::AxisC, value))),
        "u" | "U" => Ok(Some(Instr::Arg(Arg::AxisU, value))),
        "v" | "V" => Ok(Some(Instr::Arg(Arg::AxisV, value))),
        "w" | "W" => Ok(Some(Instr::Arg(Arg::AxisW, value))),
        "x" | "X" => Ok(Some(Instr::Arg(Arg::AxisX, value))),
        "y" | "Y" => Ok(Some(Instr::Arg(Arg::AxisY, value))),
        "z" | "Z" => Ok(Some(Instr::Arg(Arg::AxisZ, value))),
        "i" | "I" => Ok(Some(Instr::Arg(Arg::ArcI, value))),
        "j" | "J" => Ok(Some(Instr::Arg(Arg::ArcJ, value))),
        "k" | "K" => Ok(Some(Instr::Arg(Arg::ArcK, value))),
        "d" | "D" => Ok(Some(Instr::Arg(Arg::ParamD, value))),
        "e" | "E" => Ok(Some(Instr::Arg(Arg::ParamE, value))),
        "h" | "H" => Ok(Some(Instr::Arg(Arg::ParamH, value))),
        "l" | "L" => Ok(Some(Instr::Arg(Arg::ParamL, value))),
        "p" | "P" => Ok(Some(Instr::Arg(Arg::ParamP, value))),
        "q" | "Q" => Ok(Some(Instr::Arg(Arg::ParamQ, value))),
        "r" | "R" => Ok(Some(Instr::Arg(Arg::ParamR, value))),
        _ => unreachable!()
    }
}

fn make_par_ref(pair: Pair<Rule>) -> PR<ParId> {
    let pair = pair.into_inner().into_iter().next().unwrap();
    Ok(match pair.as_rule() {
        Rule::num => ParId::Numeric(make_int(make_num(pair.as_str())?, 1.)?),
        Rule::par_name => {
            let name = pair.as_str();
            ParId::Named(name[1..name.len()-1].into())
        },
        Rule::par_ref => ParId::Indirect(Box::new(Expr::Par(make_par_ref(pair)?))),
        Rule::expr => ParId::Indirect(Box::new(make_expr(pair)?)),
        _ => unreachable!()
    })
}

fn make_par_assign(pairs: Pairs<Rule>) -> PR<ParAssign> {
    let mut pairs = pairs.into_iter();
    Ok(ParAssign {
        id: make_par_ref(pairs.next().unwrap())?,
        value: make_expr(pairs.next().unwrap())?,
    })
}

fn make_block(n: usize, pairs: Pairs<Rule>) -> PR<Block> {
    let mut block = Block { assignments: vec![], instructions: vec![], lineno: n };
    for pair in pairs {
        match pair.as_rule() {
            Rule::word => if let Some(instr) = make_instr(pair.into_inner())? {
                block.instructions.push(instr);
            },
            Rule::par_assign => block.assignments.push(make_par_assign(pair.into_inner())?),
            _ => unreachable!()
        }
    }
    Ok(block)
}

pub fn parse(filename: &str, input: &str) -> Result<Program, Error> {
    let lines = GcodeParser::parse(Rule::file, input)?;
    let mut prog = Program { filename: filename.into(), blocks: vec![] };
    for (n, line) in lines.into_iter().enumerate() {
        if line.as_rule() == Rule::line {
            // TODO count empty lines too...
            prog.blocks.push(make_block(n, line.into_inner())?);
        }
    }
    Ok(prog)
}
