// Copyright (c) 2019 Georg Brandl.  Licensed under the Apache License,
// Version 2.0 <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0>
// or the MIT license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at
// your option. This file may not be copied, modified, or distributed except
// according to those terms.

use std::collections::HashMap;

use crate::ast::*;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Axis {
    A, B, C,
    U, V, W,
    X, Y, Z,
}

/// A collection of axis coordinates.
///
/// All length measures are in millimeters.
/// All angle measures are in degrees.
pub struct Coords {
    map: HashMap<Axis, f64>,
}

pub struct Instruction {
    pub gcode_line: usize,
    pub instr: Instr,
}

pub enum Instr {
    // G codes
    RapidMove(Coords),    // e.g. from G0
    Move(Coords),         // e.g. from G1, but also other gotos
    Helix(Coords, Coords, u32),   // (center, target, turns), from G2, G3
    Dwell(f64),         // from G4
    // todo: Splines (G5)
    // ? LatheMode(bool),    // G7, G8
    // todo: Tool table (G10)
    //  PlaneSelect(), // G17-G19
    // ? UoM(bool)      // G20-G21
    // ? Goto/Set predef // G28, G30
    // todo: spindle sync // G33
    Probe(Coords, u32), // G38
    CutterComp(bool, bool), // G40-42
    // ? ToolLengthOff G43, G49
    // ? MachineCoords G53
    // ? CoordSystem G54-G59
    // ? PathControl G61, G64
    // Cycles G73, G76, G80-89, G98-99
    // ? Distance mode G90,G91
    // ? Offsets G92
    // FeedRateMode(u16), // G93-95
    // SpindleControlMode(u16), // G96-97
    // M codes
    End,         // M2, M30
    Pause(bool), // M0-1
    Spindle(bool, bool), // M3-5
    ToolChange, // M6
    Coolant(bool, bool), // M7-9
    // todo: others
    // Others
    FeedRate(f64),
    SpindleSpeed(f64),
    ToolSelect(u16),
}

/// The Interpreter translates G-code into a series of machine instructions,
/// resolving variable interpolation, modal word state and ordering of words on
/// a line.
pub struct Interpreter {
    program: Program,
    /// Available axes
    axes: Vec<Axis>,
    /// TODO: numeric vars as numbers?
    vars: HashMap<String, f64>,

    // private stuff
    modal_state: 
}

fn num_to_int(inp: f64, figures: i32) -> Result<u16, String> {
    let v = inp * 10f64.powi(figures);
    if (v.round() - v).abs() < 0.0001 && v >= 0. && v <= 65535. {
        Ok(v.round() as u16)
    } else {
        Err(format!("number can have at most {} decimal places", figures))
    }
}

impl Interpreter {
    pub fn new(program: Program, axes: impl Into<Vec<Axis>>, vars: Option<HashMap<String, f64>>) -> Self {
        
    }

    pub fn interpret(&mut self, exec: impl FnMut(Instruction)) -> {
        
    }
}
