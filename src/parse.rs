// Copyright (c) 2019 Georg Brandl.  Licensed under the Apache License,
// Version 2.0 <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0>
// or the MIT license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at
// your option. This file may not be copied, modified, or distributed except
// according to those terms.

use std::str::FromStr;
use itertools::Itertools;
use pest_derive::Parser;
use pest::{Parser, Span, error::{Error, ErrorVariant}, iterators::{Pair, Pairs}};

use crate::ast::*;

#[derive(Parser)]
#[grammar = "gcode.pest"]
pub struct GcodeParser;

type ParseResult<T> = Result<T, Error<Rule>>;

fn err<T>(span: Span, msg: impl Into<String>) -> ParseResult<T> {
    Err(Error::new_from_span(ErrorVariant::CustomError { message: msg.into() }, span))
}

fn parse_filtered<T: FromStr>(pair: Pair<Rule>) -> T
    where T::Err: std::fmt::Debug
{
    let input = pair.as_str();
    let mut new = String::with_capacity(input.len());
    let mut in_comment = false;
    for ch in input.chars() {
        match ch {
            ' ' | '\t' => (),
            ')' if in_comment => in_comment = false,
            '(' => in_comment = true,
            _ if in_comment => (),
            ';' => break,
            _ => new.push(ch),
        }
    }
    new.parse().expect("valid parse")
}

fn num_to_int(span: Span, inp: f64, figures: i32) -> ParseResult<u16> {
    let v = inp * 10f64.powi(figures);
    if (v.round() - v).abs() < 0.0001 && v >= 0. && v <= 65535. {
        Ok(v.round() as u16)
    } else {
        err(span, format!("number can have at most {} decimal places", figures))
    }
}

fn make_par_ref(pair: Pair<Rule>) -> ParseResult<ParId> {
    let (pair,) = pair.into_inner().collect_tuple().expect("one child");
    Ok(match pair.as_rule() {
        Rule::par_num => ParId::Numeric(parse_filtered(pair)),
        Rule::name => ParId::Named(parse_filtered(pair)),
        Rule::par_ref => ParId::Indirect(Box::new(Expr::Par(make_par_ref(pair)?))),
        Rule::expr => ParId::Indirect(Box::new(make_expr(pair)?)),
        _ => unreachable!()
    })
}

fn make_expr(expr_pair: Pair<Rule>) -> ParseResult<Expr> {
    let mut lhs = None;
    let mut op = None;
    for pair in expr_pair.into_inner() {
        match pair.as_rule() {
            // singleton inside "expr_atom" or "value"
            Rule::expr => return make_expr(pair),
            Rule::num => return Ok(Expr::Num(parse_filtered(pair))),
            Rule::expr_call => {
                let (func, arg) = pair.into_inner().collect_tuple().expect("children");
                return Ok(Expr::Call(parse_filtered(func), vec![make_expr(arg)?]));
            }
            Rule::expr_atan => {
                let (argy, argx) = pair.into_inner().collect_tuple().expect("children");
                return Ok(Expr::Call("ATAN".into(), vec![make_expr(argy)?,
                                                         make_expr(argx)?]));
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
            // XXX: can there be comments *INSIDE* of op names and between **?
            // Also check ATAN.
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

fn make_instr(pairs: Pairs<Rule>) -> ParseResult<Option<Instr>> {
    let (letter, value) = pairs.collect_tuple().expect("children");
    let value_span = value.as_span();
    let value = make_expr(value)?;
    match letter.as_str() {
        "o" | "O" => err(letter.as_span(), "O-word control flow is not supported"),
        "n" | "N" => Ok(None),  // line numbers are accepted but ignoredxs
        "f" | "F" => Ok(Some(Instr::Feed(value))),
        "s" | "S" => Ok(Some(Instr::Spindle(value))),
        "t" | "T" => Ok(Some(Instr::Tool(value))),
        "g" | "G" => match value {
            Expr::Num(n) => Ok(Some(Instr::Gcode(num_to_int(value_span, n, 1)?, vec![]))),
            // XXX this is actually accepted by LinuxCNC, but would require evaluating
            // the program before being able to reorder and check words
            _ => err(value_span, "G words must have a constant numeric value"),
        },
        "m" | "M" => match value {
            Expr::Num(n) => Ok(Some(Instr::Mcode(num_to_int(value_span, n, 0)?, vec![]))),
            _ => err(value_span, "M words must have a constant numeric value"),
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

fn make_block(n: usize, pairs: Pairs<Rule>) -> ParseResult<Block> {
    let mut block = Block::default();
    block.lineno = n;
    for pair in pairs {
        match pair.as_rule() {
            Rule::word => if let Some(instr) = make_instr(pair.into_inner())? {
                block.instructions.push(instr);
            }
            Rule::par_assign => {
                let (id, value) = pair.into_inner().collect_tuple().expect("children");
                block.assignments.push(ParAssign {
                    id: make_par_ref(id)?,
                    value: make_expr(value)?
                });
            }
            Rule::blockdel => block.blockdel = true,
            _ => unreachable!()
        }
    }
    Ok(block)
}

pub fn parse(filename: &str, input: &str) -> ParseResult<Program> {
    let lines = GcodeParser::parse(Rule::file, input).map_err(|e| e.with_path(filename))?;
    let mut prog = Program { filename: filename.into(), blocks: vec![] };
    for (n, line) in lines.enumerate() {
        if line.as_rule() == Rule::line {
            prog.blocks.push(make_block(n, line.into_inner())?);
        }
    }
    Ok(prog)
}
