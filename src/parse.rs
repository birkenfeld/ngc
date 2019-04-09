// Copyright (c) 2019 Georg Brandl.  Licensed under the Apache License,
// Version 2.0 <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0>
// or the MIT license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at
// your option. This file may not be copied, modified, or distributed except
// according to those terms.

use pest_derive::Parser;
use pest::{Parser, iterators::{Pair, Pairs}};

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


fn make_num(inp: &str) -> PR<f64> {
    inp.parse().map_err(|_| Error::Other(format!("invalid number: {:?}", inp)))
}

fn num_to_int(inp: f64, mul: f64) -> PR<u16> {
    let v = inp * mul;
    if (v.round() - v).abs() < 0.0001 && v >= 0. && v <= 65535. {
        Ok(v.round() as u16)
    } else {
        Err(Error::Other(format!("number invalid here: {:?}", inp)))
    }
}

fn child(pair: Pair<Rule>) -> Pair<Rule> {
    pair.into_inner().next().expect("a child rule is required")
}

fn make_expr(expr_pair: Pair<Rule>) -> PR<Expr> {
    let mut lhs = None;
    let mut op = None;
    for pair in expr_pair.into_inner() {
        match pair.as_rule() {
            // singleton inside "expr_atom" or "value"
            Rule::expr => return make_expr(pair),
            Rule::num => return Ok(Expr::Num(make_num(pair.as_str())?)),
            Rule::expr_call => {
                let mut inner = pair.into_inner();
                let func = inner.next().unwrap().as_str();
                let x = make_expr(inner.next().unwrap())?;
                return Ok(Expr::Call(func.into(), vec![x]));
            }
            Rule::expr_atan => {
                let mut inner = pair.into_inner();
                let x = make_expr(inner.next().unwrap())?;
                let y = make_expr(inner.next().unwrap())?;
                return Ok(Expr::Call("ATAN".into(), vec![x, y]));
            }
            Rule::par_ref => return Ok(Expr::Par(make_par_ref(pair)?)),
            // rules inside (left-associative) binops
            Rule::expr_atom |
            Rule::expr_pow |
            Rule::expr_mul |
            Rule::expr_add |
            Rule::expr_cmp => {
                if let Some(op) = op.take() {
                    let lhs_expr = lhs.take().expect("LHS expected before op");
                    lhs = Some(Expr::Op(op, Box::new(lhs_expr), Box::new(make_expr(pair)?)));
                } else {
                    lhs = Some(make_expr(pair)?);
                }
            }
            // operators inside binops
            Rule::op_pow => op = Some(Op::Exp),
            Rule::op_mul => op = Some(match pair.as_str() {
                "*" => Op::Mul, "/" => Op::Div, _ => Op::Mod,
            }),
            Rule::op_add => op = Some(match pair.as_str() {
                "+" => Op::Add, _ => Op::Sub,
            }),
            Rule::op_cmp => op = Some(match pair.as_str() {
                x if x.eq_ignore_ascii_case("EQ") => Op::Eq,
                x if x.eq_ignore_ascii_case("NE") => Op::Ne,
                x if x.eq_ignore_ascii_case("GT") => Op::Gt,
                x if x.eq_ignore_ascii_case("GE") => Op::Ge,
                x if x.eq_ignore_ascii_case("LT") => Op::Lt,
                _                                 => Op::Le
            }),
            Rule::op_log => op = Some(match pair.as_str() {
                x if x.eq_ignore_ascii_case("AND") => Op::And,
                x if x.eq_ignore_ascii_case("OR")  => Op::Or,
                _                                  => Op::Xor,
            }),
            _ => unreachable!()
        }
    }
    Ok(lhs.expect("no children in expr?"))
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
            Expr::Num(n) => Ok(Some(Instr::Gcode(num_to_int(n, 10.)?, vec![]))),
            _ => Err(Error::Other("G words must have a constant numeric value".into())),
        },
        "m" | "M" => match value {
            Expr::Num(n) => Ok(Some(Instr::Mcode(num_to_int(n, 1.)?, vec![]))),
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
    let pair = child(pair);
    Ok(match pair.as_rule() {
        Rule::par_num => ParId::Numeric(pair.as_str().parse().expect("valid integer")),
        Rule::name => ParId::Named(pair.as_str().into()),
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

fn filter(input: &str) -> String {
    let mut new = String::with_capacity(input.len());
    let mut in_comment = false;
    let mut in_line_comment = false;
    for ch in input.chars() {
        match ch {
            ' ' | '\t' => (),
            '\n' => {
                in_line_comment = false;
                in_comment = false;
                new.push('\n');
            }
            _ if in_line_comment => (),
            ';' => in_line_comment = true,
            ')' if in_comment => in_comment = false,
            '(' => in_comment = true,
            _ if in_comment => (),
            _ => new.push(ch),
        }
    }
    new.push('\n');
    new
}

pub fn parse(filename: &str, input: &str) -> Result<Program, Error> {
    let input = filter(input);
    let lines = GcodeParser::parse(Rule::file, &input)?;
    let mut prog = Program { filename: filename.into(), blocks: vec![] };
    for (n, line) in lines.into_iter().enumerate() {
        if line.as_rule() == Rule::line {
            // TODO count empty lines too...
            prog.blocks.push(make_block(n, line.into_inner())?);
        }
    }
    Ok(prog)
}
