// Copyright (c) 2019 Georg Brandl.  Licensed under the Apache License,
// Version 2.0 <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0>
// or the MIT license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at
// your option. This file may not be copied, modified, or distributed except
// according to those terms.

use std::fmt;
use std::borrow::Cow;
use std::hash::Hash;
use std::collections::HashMap;
use strum_macros::Display;
use fixedbitset::FixedBitSet as BitSet;

use crate::ast::*;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Display)]
pub enum Axis {
    A, B, C,
    U, V, W,
    X, Y, Z,
}

impl Axis {
    fn from_arg(arg: &Arg) -> Option<Self> {
        Some(match arg {
            Arg::AxisA => Axis::A,
            Arg::AxisB => Axis::B,
            Arg::AxisC => Axis::C,
            Arg::AxisU => Axis::U,
            Arg::AxisV => Axis::V,
            Arg::AxisW => Axis::W,
            Arg::AxisX => Axis::X,
            Arg::AxisY => Axis::Y,
            Arg::AxisZ => Axis::Z,
            _ => return None
        })
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Display)]
pub enum Arc {
    I, J, K,
}

impl Arc {
    fn from_arg(arg: &Arg) -> Option<Self> {
        Some(match arg {
            Arg::ArcI => Arc::I,
            Arg::ArcJ => Arc::J,
            Arg::ArcK => Arc::K,
            _ => return None
        })
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Display)]
pub enum Param {
    D, E, H, L, P, Q, R,
}

impl Param {
    fn from_arg(arg: &Arg) -> Option<Self> {
        Some(match arg {
            Arg::ParamD => Param::D,
            Arg::ParamE => Param::E,
            Arg::ParamH => Param::H,
            Arg::ParamL => Param::L,
            Arg::ParamP => Param::P,
            Arg::ParamQ => Param::Q,
            Arg::ParamR => Param::R,
            _ => return None
        })
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Plane {
    XY, XZ, YZ, UV, UW, VW,
}

impl Default for Plane {
    fn default() -> Self { Plane::XY }
}

pub struct Params(HashMap<Param, f64>);

impl Params {
    fn get(&mut self, p: Param, def: f64) -> f64 {
        // TODO: is it ok to take them away?
        self.0.remove(&p).unwrap_or(def)
    }
    fn get_int(&mut self, p: Param, def: u16, max: u16) -> Result<u16, ErrType> {
        let f = self.0.remove(&p).unwrap_or(def as f64);
        num_to_int(f, 0, max as f64, |n| ErrType::InvalidWordValue(p, n))
    }
}

/// A collection of axis coordinates.
///
/// All length measures are in millimeters.
/// All angle measures are in degrees.
pub struct Coords<T> {
    pub rel: bool,
    pub map: HashMap<T, f64>,
}

fn coords<T>(map: HashMap<T, f64>, rel: bool) -> Coords<T> {
    Coords { rel, map }
}

impl<T: Hash+Eq+fmt::Display> fmt::Debug for Coords<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut i = 0;
        for (k, v) in self.map.iter() {
            i += 1;
            write!(f, "{}={}", k, v)?;
            if i < self.map.len() {
                write!(f, ", ")?;
            }
        }
        Ok(())
    }
}

pub struct Instruction {
    pub gcode_line: usize,
    pub instr: Instr,
}

#[derive(Debug)]
pub enum Instr {
    // G codes
    RapidMove(Coords<Axis>),    // e.g. from G0
    Move(Coords<Axis>),         // e.g. from G1, but also other gotos
    HelixCW(Coords<Axis>, Coords<Arc>, u16),   // from G2
    HelixCCW(Coords<Axis>, Coords<Arc>, u16),  // from G3
    Dwell(f64),         // from G4
    // todo: Splines (G5)
    // ? LatheMode(bool),    // G7, G8
    // todo: Tool table (G10)
    PlaneSelect(Plane), // G17-G19
    // ? UoM(bool)      // G20-G21
    // ? Goto/Set predef // G28, G30
    // todo: spindle sync // G33
    Probe(Coords<Axis>, u32), // G38
    CutterComp(bool, bool), // G40-42
    LengthComp(bool), // G43, G49
    // ? MachineCoords G53
    // ? CoordSystem G54-G59
    // ? PathControl G61, G64
    // Cycles G73, G76, G80-89, G98-99
    // ? Distance mode G90,G91
    // ? Offsets G92
    // FeedRateMode(u16), // G93-95
    // SpindleControlMode(u16), // G96-97
    // M codes
    End(bool),         // M2, M30
    Pause(bool, bool), // M0-1
    Spindle((bool, bool)), // M3-5
    ToolChange, // M6
    Coolant((bool, bool)), // M7-9
    // todo: others
    // Others
    FeedRate(f64),
    SpindleSpeed(f64),
    ToolSelect(u16),
}

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
            ErrType::UnknownFunction(func) =>
                write!(f, "The function {} does not exist", func),
            ErrType::ExistsNeedsParameterName =>
                write!(f, "The EXISTS function needs a parameter as argument"),
            ErrType::UnknownParameter(s) =>
                write!(f, "The parameter {} does not exist", s),
            ErrType::InvalidParamNumber(n) =>
                write!(f, "Parameter number {} is out of range or not an integer", n),
            ErrType::InvalidAxisValue(ax, v) =>
                write!(f, "The value {} is out of range for axis {}", v, ax),
            ErrType::InvalidArcValue(ax, v) =>
                write!(f, "The value {} is out of range for arc coord {}", v, ax),
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
        }
    }
}

pub enum ErrType {
    ConflictingGCodes(&'static str, u16, u16),
    ConflictingMCodes(&'static str, u16, u16),
    InvalidAxis(Axis),
    InvalidArcCoordinate(Arc),
    ExistsNeedsParameterName,
    UnknownParameter(String),
    InvalidParamNumber(f64),
    InvalidAxisValue(Axis, f64),
    InvalidArcValue(Axis, f64),
    InvalidWordValue(Param, f64),
    UnknownFunction(String),
    DivByZero,
    InvalidGCode(f64),
    InvalidMCode(f64),
    InvalidTool(f64),
    MissingGCodeWord(u16, Param),
    MissingMCodeWord(u16, Param),
    UnsupportedGCode(u16),
    UnsupportedMCode(u16),
}

/// The Evaluator translates G-code into a series of machine instructions,
/// resolving variable interpolation, modal word state and ordering of words on
/// a line.
///
/// It does *not* calculate absolute coordinates for everything, or try to
/// resolve compund G-codes (like drilling cycles) to individual operations.
pub struct Evaluator {
    program: Program,
    /// Available axes
    axes: Vec<Axis>,
    /// TODO: numeric vars as numbers instead of #n?
    vars: HashMap<String, f64>,

    // private stuff
    g_state: GState,
    m_state: MState,
}

#[derive(Default)]
struct GState {
    // TODO: make enums for most of these
    // TODO: find proper defaults, some might be true
    motion_mode: usize,
    lathe_diam: bool,
    inches: bool,
    plane: Plane,
    cutter_comp: bool,
    cutter_side: bool,
    length_comp: bool,
    dist_rel: bool,
    arc_rel: bool,
}

#[derive(Default)]
struct MState {
    spindle: (bool, bool),
    coolant: (bool, bool),
}

fn num_to_int(inp: f64, figures: i32, max: f64, err: impl Fn(f64) -> ErrType) -> Result<u16, ErrType> {
    let v = inp * 10f64.powi(figures);
    if v.round() >= max {
        Err(err(inp))
    } else if (v.round() - v).abs() < 0.0001 && v >= 0. && v <= 65535. {
        Ok(v.round() as u16)
    } else {
        Err(err(inp))
    }
}

impl Evaluator {
    pub fn new(program: Program, axes: impl Into<Vec<Axis>>, vars: Option<HashMap<String, f64>>) -> Self {
        Evaluator {
            program,
            axes: axes.into(),
            vars: vars.unwrap_or_default(),
            g_state: Default::default(),
            m_state: Default::default(),
        }
    }

    pub fn eval<F>(&mut self, eval_blockdel: bool, mut exec: F) -> Result<(), EvalError>
    where F: FnMut(&mut Self, Instruction) -> Result<(), ErrType>
    {
        let blocks = std::mem::replace(&mut self.program.blocks, vec![]);
        for block in &blocks {
            if block.blockdel && !eval_blockdel {
                continue;
            }
            if self.eval_block(block, &mut exec)
                   .map_err(|e| EvalError { lineno: block.lineno, errtype: e })? {
                break;
            }
        }
        Ok(())
    }

    fn eval_block<F>(&mut self, block: &Block, mut exec: F) -> Result<bool, ErrType>
    where F: FnMut(&mut Self, Instruction) -> Result<(), ErrType>
    {
        macro_rules! exec {
            ($($tt:tt)*) => {
                exec(self, Instruction { gcode_line: block.lineno, instr: Instr::$($tt)*})?;
            }
        }

        let mut end_of_program = false;

        // Process words, by evaluating all expressions.
        let mut feed = None;
        let mut spindle = None;
        let mut tool = None;
        let mut gcodes = BitSet::with_capacity(1000); // G0 to G99.9
        let mut mcodes = BitSet::with_capacity(100);  // M0 to M99
        let mut axes = HashMap::new();
        let mut arcs = HashMap::new();
        let mut params = Params(HashMap::new());
        for word in &block.words {
            match word {
                Word::Feed(ex) => feed = Some(self.eval_expr(ex)?),
                Word::Spindle(ex) => spindle = Some(self.eval_expr(ex)?),
                Word::Tool(ex) => {
                    let n = num_to_int(self.eval_expr(ex)?, 0, 100., ErrType::InvalidTool)?;
                    tool = Some(n);
                }
                Word::Gcode(ex) => {
                    let n = num_to_int(self.eval_expr(ex)?, 1, 1000., ErrType::InvalidGCode)?;
                    gcodes.insert(n as usize);
                }
                Word::Mcode(ex) => {
                    let n = num_to_int(self.eval_expr(ex)?, 0, 100., ErrType::InvalidMCode)?;
                    mcodes.insert(n as usize);
                }
                Word::Arg(a, ex) => {
                    if let Some(ax) = Axis::from_arg(a) {
                        if !self.axes.contains(&ax) {
                            return Err(ErrType::InvalidAxis(ax));
                        }
                        axes.insert(ax, self.eval_expr(ex)?);
                    } else if let Some(arc) = Arc::from_arg(a) {
                        arcs.insert(arc, self.eval_expr(ex)?);
                    } else {
                        params.0.insert(Param::from_arg(a).unwrap(), self.eval_expr(ex)?);
                    }
                }
            }
        }

        let has_axis_words = !(axes.is_empty() && arcs.is_empty());

        // Process assignments.  Since parameter assignment only takes place
        // after the whole line has evaluated, including in other assignments,
        // cache new values here and apply at the end.
        let mut new_values = vec![];
        for assign in &block.assignments {
            new_values.push((self.get_par_key(&assign.id)?.into_owned(),
                             self.eval_expr(&assign.value)?));
        }
        for (name, value) in new_values {
            self.vars.insert(name, value);
        }

        // Now execute all collected words. We need to respect the different
        // modal groups, and ensure that there are no conflicting words.
        {
            // Define a helper for determining which code from a modal group is present.

            // TODO: move to a wrapper type over FixedBitSet
            let mut g_modal_group = |name, codes: &[usize]| {
                let mut found = None;
                for &code in codes {
                    if gcodes[code] {
                        if let Some(&other) = codes.iter().find(|&&c| gcodes[c] && c != code) {
                            return Err(ErrType::ConflictingGCodes(name, code as u16, other as u16));
                        }
                        found = Some(code);
                    }
                }
                for &code in codes {
                    gcodes.set(code, false);
                }
                Ok(found)
            };

            let mut m_modal_group = |name, codes: &[usize]| {
                let mut found = None;
                for &code in codes {
                    if mcodes[code] {
                        if let Some(&other) = codes.iter().find(|&&c| mcodes[c] && c != code) {
                            return Err(ErrType::ConflictingMCodes(name, code as u16, other as u16));
                        }
                        found = Some(code);
                    }
                }
                for &code in codes {
                    mcodes.set(code, false);
                }
                Ok(found)
            };

            // #1. Set feed rate mode (G93-G95) and spindle speed mode (G96-G97).
            // All but the default are unsupported.
            match g_modal_group("feed rate mode", &[930, 940, 950])? {
                Some(940) | None => (),
                Some(x) => return Err(ErrType::UnsupportedGCode(x as u16))
            }
            match g_modal_group("spindle speed mode", &[960, 970])? {
                Some(970) | None => (),
                Some(x) => return Err(ErrType::UnsupportedGCode(x as u16))
            }

            // #2. Execute F, S and T codes.
            if let Some(feed) = feed { exec!(FeedRate(feed)); }
            if let Some(speed) = spindle { exec!(SpindleSpeed(speed)); }
            if let Some(tool) = tool { exec!(ToolSelect(tool)); }

            // #3. Execute toolchange (M6 and M61).
            match m_modal_group("toolchange", &[6, 61])? {
                Some(6) => exec!(ToolChange),
                Some(61) => return Err(ErrType::UnsupportedMCode(61)), // TODO
                _ => ()
            }

            // #4. Switch spindle.
            if let Some(x) = m_modal_group("spindle control", &[3, 4, 5])? {
                match x {
                    3 => self.m_state.spindle = (true, true),
                    4 => self.m_state.spindle = (true, false),
                    5 => self.m_state.spindle = (false, false),
                    _ => ()
                }
                exec!(Spindle(self.m_state.spindle));
            }

            // #5. Save or restore state (M70-M73), unsupported.
            if let Some(x) = m_modal_group("save/restore", &[70, 71, 72, 73])? {
                return Err(ErrType::UnsupportedMCode(x as u16));
            }

            // #6. Switch coolant.
            // This group is odd since M7 and M8 may be given together.
            let old_coolant = self.m_state.coolant;
            match m_modal_group("mist coolant", &[7, 9])? {
                Some(7) => self.m_state.coolant.0 = true,
                Some(9) => self.m_state.coolant = (false, false),
                _ => ()
            }
            match m_modal_group("mist coolant", &[8, 9])? {
                Some(8) => self.m_state.coolant.1 = true,
                Some(9) => self.m_state.coolant = (false, false),
                _ => ()
            }
            if self.m_state.coolant != old_coolant {
                exec!(Coolant(self.m_state.coolant));
            }

            // #7. Overrides (M48-M53), currently unsupported.
            if let Some(x) = m_modal_group("overrides", &[48, 49, 50, 51, 52, 53])? {
                return Err(ErrType::UnsupportedMCode(x as u16));
            }

            // #8. Dwell (G4).
            // This isn't a modal group, but we can't access the gcodes set right now.
            if g_modal_group("dwell", &[40])?.is_some() {
                let secs = params.get(Param::P, -1.0);
                if secs >= 0. {
                    exec!(Dwell(secs));
                } else {
                    return Err(ErrType::MissingGCodeWord(40, Param::P));
                }
            }

            // #9. Set active plane (G17-G19).
            if let Some(x) = g_modal_group("active plane", &[170, 171, 180, 181, 190, 191])? {
                match x {
                    170 => self.g_state.plane = Plane::XY,
                    180 => self.g_state.plane = Plane::XZ,
                    190 => self.g_state.plane = Plane::YZ,
                    171 => self.g_state.plane = Plane::UV,
                    181 => self.g_state.plane = Plane::UW,
                    191 => self.g_state.plane = Plane::VW,
                    _ => ()
                }
                exec!(PlaneSelect(self.g_state.plane));
            }

            // #10. Set length units (G20-G21).
            match g_modal_group("length units", &[200, 210])? {
                Some(200) => self.g_state.inches = true,
                Some(210) => self.g_state.inches = false,
                _ => ()
            }

            // #10.1. Set lathe mode (G7-G8).
            match g_modal_group("lathe mode", &[70, 80])? {
                Some(70) => return Err(ErrType::UnsupportedGCode(70)),
                Some(80) => self.g_state.lathe_diam = false,
                _ => ()
            }

            // #11. Set cutter radius compensation (G40-G42).  Only "off" is supported.
            if let Some(x) = g_modal_group("cutter radius compensation", &[400, 410, 411, 420, 421])? {
                match x {
                    400 => self.g_state.cutter_comp = false,
                    _ => return Err(ErrType::UnsupportedGCode(x as u16)),
                }
                exec!(CutterComp(self.g_state.cutter_comp, self.g_state.cutter_side));
            }

            // #12. Set length compensation (G43, G49).
            if let Some(x) = g_modal_group("cutter length compensation", &[430, 431, 432, 490])? {
                match x {
                    490 => self.g_state.length_comp = false,
                    _ => return Err(ErrType::UnsupportedGCode(x as u16)),
                }
                exec!(LengthComp(self.g_state.length_comp));
            }

            // #13. Select coordinate system (G54-G59). Only first one supported.
            match g_modal_group("coordinate system", &[540, 550, 560, 570, 580, 590, 591, 592, 593])? {
                Some(540) | None => (),
                Some(x) => return Err(ErrType::UnsupportedGCode(x as u16))
            }

            // #14. Set path control mode.
            if let Some(_) = g_modal_group("path control", &[610, 611, 640])? {
                // Currently ignored.
            }

            // #15. Set distance mode.
            match g_modal_group("distance mode", &[900, 910])? {
                Some(900) => self.g_state.dist_rel = false,
                Some(910) => self.g_state.dist_rel = true,
                _ => ()
            }
            match g_modal_group("arc distance mode", &[901, 911])? {
                Some(901) => self.g_state.arc_rel = false,
                Some(911) => self.g_state.arc_rel = true,
                _ => ()
            }

            // #16. Set retract mode (G98-G99).  All unsupported.
            if let Some(x) = g_modal_group("retract mode", &[980, 990])? {
                return Err(ErrType::UnsupportedGCode(x as u16));
            }

            // #17. Reference modes and offsets.  All unsupported.
            if let Some(x) = g_modal_group("reference/offsets", &[280, 281, 300, 301, 100,
                                                                  920, 921, 922, 923])? {
                return Err(ErrType::UnsupportedGCode(x as u16));
            }

            // #18. Perform motion.
            let machine_coords = g_modal_group("machine coords", &[530])?.is_some();
            if machine_coords {
                return Err(ErrType::UnsupportedGCode(530));
            }

            let mut mmode = g_modal_group("motion", &[0, 10, 20, 30, 50, 51, 52, 53, 330, 331,
                                                      382, 383, 384, 385, 730, 760, 800, 810,
                                                      820, 830, 840, 850, 860, 870, 880, 890])?;
            // Motion is also performed if there are any axis (or arc) words.
            if mmode.is_none() && has_axis_words {
                mmode = Some(self.g_state.motion_mode);
            }


            /* TODO enforce this
            let plane = self.g_state.plane;
            if (arc == Arc::K && (plane == Plane::XY || plane == Plane::UV)) ||
            (arc == Arc::J && (plane == Plane::XZ || plane == Plane::UW)) ||
            (arc == Arc::I && (plane == Plane::YZ || plane == Plane::VW))
            {
                return Err(ErrType::InvalidArcCoordinate(arc));
            }
            */

            if let Some(x) = mmode {
                match x {
                    0   => exec!(RapidMove(coords(axes, self.g_state.dist_rel))),
                    10  => exec!(Move(coords(axes, self.g_state.dist_rel))),
                    20  => exec!(HelixCW(coords(axes, self.g_state.dist_rel),
                                         coords(arcs, self.g_state.arc_rel),
                                          params.get_int(Param::P, 1, 1000)?)),
                    30  => exec!(HelixCCW(coords(axes, self.g_state.dist_rel),
                                          coords(arcs, self.g_state.arc_rel),
                                          params.get_int(Param::P, 1, 1000)?)),
                    _ => return Err(ErrType::UnsupportedGCode(x as u16))
                }
                self.g_state.motion_mode = x;
            }

            // #19. Stop.
            match m_modal_group("stop", &[0, 1, 2, 30, 60])? {
                Some(0) => exec!(Pause(false, false)),
                Some(1) => exec!(Pause(true, false)),
                Some(60) => exec!(Pause(false, true)),
                Some(2) => { exec!(End(false)); end_of_program = true; }
                Some(30) => { exec!(End(true)); end_of_program = true; }
                _ => ()
            }
        }

        // Check for invalid codes.  All supported ones have been removed as part of
        // the modal group checks, so anything left over is unknown to us.
        if let Some(code) = gcodes.ones().next() {
            return Err(ErrType::InvalidGCode(code as f64));
        }
        if let Some(code) = mcodes.ones().next() {
            return Err(ErrType::InvalidGCode(code as f64));
        }

        Ok(end_of_program)
    }

    fn get_par_key<'a>(&self, id: &'a ParId) -> Result<Cow<'a, str>, ErrType> {
        Ok(match id {
            ParId::Named(s) => s.into(),
            ParId::Numeric(n) => format!("#{}", n).into(),
            ParId::Indirect(expr) => {
                let parnum = self.eval_expr(&expr)?;
                let parnum = num_to_int(parnum, 0, 1000000., ErrType::InvalidParamNumber)?;
                format!("#{}", parnum).into()
            }
        })
    }

    fn eval_expr(&self, expr: &Expr) -> Result<f64, ErrType> {
        Ok(match expr {
            Expr::Num(value) => *value,
            Expr::Par(id) => {
                let key = self.get_par_key(id)?;
                match self.vars.get(&*key) {
                    Some(value) => *value,
                    _ => return Err(ErrType::UnknownParameter(key.into()))
                }
            }
            Expr::Op(op, left, right) => {
                let left = self.eval_expr(left)?;
                let right = self.eval_expr(right)?;
                match op {
                    Op::Exp => left.powf(right),
                    Op::Mul => left * right,
                    Op::Div => if right == 0. {
                        return Err(ErrType::DivByZero)
                    } else { left / right },
                    Op::Mod => if right == 0. {
                        return Err(ErrType::DivByZero)
                    } else { left % right },
                    Op::Add => left + right,
                    Op::Sub => left - right,
                    Op::Eq  => if left == right { 1.0 } else { 0.0 },
                    Op::Ne  => if left != right { 1.0 } else { 0.0 },
                    Op::Gt  => if left >  right { 1.0 } else { 0.0 },
                    Op::Ge  => if left >= right { 1.0 } else { 0.0 },
                    Op::Lt  => if left <  right { 1.0 } else { 0.0 },
                    Op::Le  => if left <= right { 1.0 } else { 0.0 },
                    Op::And => if left != 0. && right != 0. { 1.0 } else { 0.0 },
                    Op::Or  => if left != 0. || right != 0. { 1.0 } else { 0.0 },
                    Op::Xor => if (left != 0.) ^ (right != 0.) { 1.0 } else { 0.0 },
                }
            }
            Expr::Call(name, exprs) => {
                // Invariant: we know that exprs is always length 1, except for ATAN.
                if name == "EXISTS" {
                    // Special case: needs unevaluated parameter as arg
                    if let Expr::Par(id) = &exprs[0] {
                        let key = self.get_par_key(id)?;
                        if self.vars.contains_key(&*key) { 1.0 } else { 0.0 }
                    } else {
                        return Err(ErrType::ExistsNeedsParameterName)
                    }
                } else if name == "ATAN" {
                    let arg_y = self.eval_expr(&exprs[0])?;
                    let arg_x = self.eval_expr(&exprs[1])?;
                    arg_y.atan2(arg_x)
                } else {
                    let arg = self.eval_expr(&exprs[0])?;
                    match &**name {
                        "ABS" => arg.abs(),
                        "ACOS" => arg.acos(),
                        "ASIN" => arg.asin(),
                        "COS" => arg.cos(),
                        "EXP" => arg.exp(),
                        "FIX" => arg.floor(),
                        "FUP" => arg.ceil(),
                        "ROUND" => arg.round(),
                        "LN" => arg.ln(),
                        "SIN" => arg.sin(),
                        "SQRT" => arg.sqrt(),
                        "TAN" => arg.tan(),
                        _ => return Err(ErrType::UnknownFunction(name.into()))
                    }
                }
            }
        })
    }
}
