// Copyright (c) 2019 Georg Brandl.  Licensed under the Apache License,
// Version 2.0 <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0>
// or the MIT license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at
// your option. This file may not be copied, modified, or distributed except
// according to those terms.

use std::fmt;

use super::enums::*;

pub struct EvalError {
    pub lineno: usize,
    pub errtype: ErrType,
}

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Error in line {}: ", self.lineno)?;
        match &self.errtype {
            ErrType::ConflictingGCodes(s, c1, c2) =>
                write!(f, "G{} and G{} of group {} cannot be used together",
                       *c1 as f64 / 10., *c2 as f64 / 10., s),
            ErrType::ConflictingMCodes(s, c1, c2) =>
                write!(f, "M{} and M{} of group {} cannot be used together",
                       c1, c2, s),
            ErrType::InvalidAxis(ax) =>
                write!(f, "Used nonexisting axis {}", ax),
            ErrType::InvalidArcCoordinate(arc) =>
                write!(f, "Arc coordinate {} is not allowed for this plane", arc),
            ErrType::UnknownParameter(s) =>
                write!(f, "The parameter {} does not exist", s),
            ErrType::InvalidParamNumber(n) =>
                write!(f, "Parameter number {} is out of range or not an integer", n),
            ErrType::InvalidAxisValue(ax, v) =>
                write!(f, "The value {} is out of range for axis {}", v, ax),
            ErrType::InvalidArcValue(ax, v) =>
                write!(f, "The value {} is out of range for arc coord {}", v, ax),
            ErrType::InvalidPlane(p) =>
                write!(f, "Arcs not supported in the  {} plane", p),
            ErrType::InvalidWordValue(w, v) =>
                write!(f, "The value {} is out of range for word {}", v, w),
            ErrType::DivByZero =>
                write!(f, "Division by zero attempted"),
            ErrType::InvalidGCode(c) =>
                write!(f, "The code G{} does not exist", c),
            ErrType::InvalidMCode(c) =>
                write!(f, "The code M{} does not exist", c),
            ErrType::InvalidTool(n) =>
                write!(f, "The tool number {} is invalid", n),
            ErrType::MissingGCodeWord(c, arg) =>
                write!(f, "G{} needs a {} word", *c as f64 / 10., arg),
            ErrType::MissingMCodeWord(c, arg) =>
                write!(f, "M{} needs a {} word", c, arg),
            ErrType::UnsupportedGCode(c) =>
                write!(f, "G{} is unsupported by this library", *c as f64 / 10.),
            ErrType::UnsupportedMCode(c) =>
                write!(f, "M{} is unsupported by this library", c),
            ErrType::CutterCompActive(c) =>
                write!(f, "G{} is invalid when cutter compensation is on", *c as f64 / 10.),
            ErrType::Other(s) =>
                write!(f, "{}", s),
        }
    }
}

pub enum ErrType {
    InvalidGCode(f64),
    InvalidMCode(f64),
    ConflictingGCodes(&'static str, u16, u16),
    ConflictingMCodes(&'static str, u16, u16),
    MissingGCodeWord(u16, GenWord),
    MissingMCodeWord(u16, GenWord),
    InvalidAxis(Axis),
    InvalidArcCoordinate(Arc),
    InvalidPlane(Plane),
    UnknownParameter(Param),
    InvalidParamNumber(f64),
    InvalidAxisValue(Axis, f64),
    InvalidArcValue(Axis, f64),
    InvalidWordValue(GenWord, f64),
    DivByZero,
    InvalidTool(f64),
    UnsupportedGCode(u16),
    UnsupportedMCode(u16),
    CutterCompActive(u16),
    Other(String),
}

impl ErrType {
    pub fn other<T>(s: impl Into<String>) -> Result<T, Self> {
        Err(ErrType::Other(s.into()))
    }
}
