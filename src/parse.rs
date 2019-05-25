// Copyright (c) 2019 Georg Brandl.  Licensed under the Apache License,
// Version 2.0 <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0>
// or the MIT license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at
// your option. This file may not be copied, modified, or distributed except
// according to those terms.

//! Parser for G-code.

use std::str::FromStr;
use itertools::Itertools;
use pest::{Parser, Span, error::{Error, ErrorVariant}, iterators::{Pair, Pairs}};

use crate::ast::*;
use crate::util::num_to_int;

// Since pest makes Rule "pub", we do this in order to not show it to crate users.
mod parser {
    use pest_derive::Parser;

    #[derive(Parser)]
    #[grammar = "gcode.pest"]
    pub struct GcodeParser;
}

use self::parser::{GcodeParser, Rule};

/// Result of a parsing operation.
pub type ParseResult<T> = Result<T, Error<Rule>>;

fn err(span: Span, msg: impl Into<String>) -> Error<Rule> {
    Error::new_from_span(ErrorVariant::CustomError { message: msg.into() }, span)
}

fn parse_filtered<T: FromStr>(pair: Pair<Rule>) -> T
    where T::Err: std::fmt::Debug
{
    pair.as_str().chars()
                 .filter(|&ch| ch != ' ' && ch != '\t')
                 .collect::<String>()
                 .parse().expect("valid parse")
}

fn make_par_ref(pair: Pair<Rule>) -> ParseResult<ParId> {
    let (pair,) = pair.into_inner().collect_tuple().expect("one child");
    if pair.as_rule() == Rule::par_name {
        Ok(ParId::Named(parse_filtered(pair)))
    } else {
        let expr_span = pair.as_span();
        let expr = make_expr(pair)?;
        if let Expr::Num(f) = expr {
            let n = num_to_int(f, u16::max_value(),
                               |f| err(expr_span, format!("Invalid parameter number {}", f)))?;
            Ok(ParId::Numeric(n as u16))
        } else {
            Ok(ParId::Indirect(Box::new(expr)))
        }
    }
}

fn make_signed(sign: f64, expr: Expr) -> Expr {
    if sign < 0. {
        Expr::UnOp(UnOp::Minus, Box::new(expr))
    } else {
        expr
    }
}

fn make_expr(expr_pair: Pair<Rule>) -> ParseResult<Expr> {
    let mut lhs = None;
    let mut op = None;
    let mut sign = 1.;
    for pair in expr_pair.into_inner() {
        match pair.as_rule() {
            // prefix unary op
            Rule::op_un => if pair.as_str() == "-" { sign = -sign; },
            // singleton inside "expr_atom" or "value"
            Rule::expr => return Ok(make_signed(sign, make_expr(pair)?)),
            Rule::num => return Ok(Expr::Num(sign * parse_filtered::<f64>(pair))),
            Rule::expr_call => {
                let (func, arg) = pair.into_inner().collect_tuple().expect("children");
                let arg = Box::new(make_expr(arg)?);
                let func = match func.as_str() {
                    x if x.eq_ignore_ascii_case("ABS")    => Call::Abs(arg),
                    x if x.eq_ignore_ascii_case("ACOS")   => Call::Acos(arg),
                    x if x.eq_ignore_ascii_case("ASIN")   => Call::Asin(arg),
                    x if x.eq_ignore_ascii_case("COS")    => Call::Cos(arg),
                    x if x.eq_ignore_ascii_case("EXP")    => Call::Exp(arg),
                    x if x.eq_ignore_ascii_case("FIX")    => Call::Fix(arg),
                    x if x.eq_ignore_ascii_case("FUP")    => Call::Fup(arg),
                    x if x.eq_ignore_ascii_case("ROUND")  => Call::Round(arg),
                    x if x.eq_ignore_ascii_case("LN")     => Call::Ln(arg),
                    x if x.eq_ignore_ascii_case("SIN")    => Call::Sin(arg),
                    x if x.eq_ignore_ascii_case("SQRT")   => Call::Sqrt(arg),
                    _                                     => Call::Tan(arg),
                };
                return Ok(make_signed(sign, Expr::Call(func)));
            }
            Rule::expr_exist => {
                let (par_ref,) = pair.into_inner().collect_tuple().expect("one child");
                return Ok(make_signed(sign, Expr::Call(Call::Exists(
                    make_par_ref(par_ref)?
                ))));
            }
            Rule::expr_atan => {
                let (argy, argx) = pair.into_inner().collect_tuple().expect("children");
                return Ok(make_signed(
                    sign, Expr::Call(Call::Atan(Box::new(make_expr(argy)?),
                                                Box::new(make_expr(argx)?)))));
            }
            Rule::par_ref => return Ok(make_signed(sign, Expr::Par(make_par_ref(pair)?))),
            // rules inside (left-associative) binops
            Rule::expr_atom |
            Rule::expr_pow |
            Rule::expr_mul |
            Rule::expr_add |
            Rule::expr_cmp => {
                if let Some(op) = op.take() {
                    let lhs_expr = lhs.take().expect("LHS expected before op");
                    lhs = Some(Expr::BinOp(op, Box::new(lhs_expr), Box::new(make_expr(pair)?)));
                } else {
                    lhs = Some(make_expr(pair)?);
                }
            }
            Rule::expr_unop => {
                let mut inner = pair.into_inner().collect::<Vec<_>>();
                let expr = make_expr(inner.pop().expect("children"))?;
                let full = if inner.is_empty() || inner[0].as_str() == "+" {
                    expr
                } else {
                    Expr::UnOp(UnOp::Minus, Box::new(expr))
                };
                if let Some(op) = op.take() {
                    let lhs_expr = lhs.take().expect("LHS expected before op");
                    lhs = Some(Expr::BinOp(op, Box::new(lhs_expr), Box::new(full)));
                } else {
                    lhs = Some(full);
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

fn make_word(pairs: Pairs<Rule>) -> ParseResult<Option<Word>> {
    let (letter, value) = pairs.collect_tuple().expect("children");
    let value = make_expr(value)?;
    match letter.as_str() {
        "o" | "O" => Err(err(letter.as_span(), "O-word control flow is not supported")),
        "n" | "N" => Ok(None),  // line numbers are accepted but ignoredxs
        "g" | "G" => Ok(Some(Word::Gcode(value))),
        "m" | "M" => Ok(Some(Word::Mcode(value))),
        "f" | "F" => Ok(Some(Word::Feed(value))),
        "s" | "S" => Ok(Some(Word::Spindle(value))),
        "t" | "T" => Ok(Some(Word::Tool(value))),
        "a" | "A" => Ok(Some(Word::Arg(Arg::AxisA, value))),
        "b" | "B" => Ok(Some(Word::Arg(Arg::AxisB, value))),
        "c" | "C" => Ok(Some(Word::Arg(Arg::AxisC, value))),
        "u" | "U" => Ok(Some(Word::Arg(Arg::AxisU, value))),
        "v" | "V" => Ok(Some(Word::Arg(Arg::AxisV, value))),
        "w" | "W" => Ok(Some(Word::Arg(Arg::AxisW, value))),
        "x" | "X" => Ok(Some(Word::Arg(Arg::AxisX, value))),
        "y" | "Y" => Ok(Some(Word::Arg(Arg::AxisY, value))),
        "z" | "Z" => Ok(Some(Word::Arg(Arg::AxisZ, value))),
        "i" | "I" => Ok(Some(Word::Arg(Arg::OffsetI, value))),
        "j" | "J" => Ok(Some(Word::Arg(Arg::OffsetJ, value))),
        "k" | "K" => Ok(Some(Word::Arg(Arg::OffsetK, value))),
        "d" | "D" => Ok(Some(Word::Arg(Arg::ParamD, value))),
        "e" | "E" => Ok(Some(Word::Arg(Arg::ParamE, value))),
        "h" | "H" => Ok(Some(Word::Arg(Arg::ParamH, value))),
        "l" | "L" => Ok(Some(Word::Arg(Arg::ParamL, value))),
        "p" | "P" => Ok(Some(Word::Arg(Arg::ParamP, value))),
        "q" | "Q" => Ok(Some(Word::Arg(Arg::ParamQ, value))),
        "r" | "R" => Ok(Some(Word::Arg(Arg::ParamR, value))),
        _ => unreachable!()
    }
}

fn make_block(lineno: usize, pairs: Pairs<Rule>) -> ParseResult<Option<Block>> {
    let mut block = Block { lineno, ..Block::default() };
    for pair in pairs {
        match pair.as_rule() {
            Rule::word => if let Some(word) = make_word(pair.into_inner())? {
                block.words.push(word);
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
    Ok(if block.words.len() + block.assignments.len() > 0 { Some(block) } else { None })
}

/// Parse a program, coming from *filename*, consisting of the source *text*.
///
/// On parse error, a standard parse error from [pest] is returned.
///
/// [pest]: https://docs.rs/pest
pub fn parse(filename: &str, input: &str) -> ParseResult<Program> {
    let lines = GcodeParser::parse(Rule::file, input).map_err(|e| e.with_path(filename))?;
    let mut prog = Program { filename: filename.into(), blocks: vec![] };
    for (lineno, line) in lines.into_iter().enumerate() {
        if let Some(block) = make_block(lineno + 1, line.into_inner())? {
            prog.blocks.push(block);
        }
    }
    Ok(prog)
}
