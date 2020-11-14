// Copyright (c) 2019-2020 Georg Brandl.  Licensed under the Apache License,
// Version 2.0 <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0>
// or the MIT license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at
// your option. This file may not be copied, modified, or distributed except
// according to those terms.

mod enums;
mod error;

use std::collections::HashMap;
use fixedbitset::FixedBitSet as BitSet;

use crate::ast::*;
use crate::util::num_to_int;

pub use self::enums::*;
pub use self::error::*;

const MAX_TOOL: u16 = 100;
const MAX_PARAM: u16 = 10000;

/// A machine instruction collected from G-code.
#[derive(Debug)]
pub struct Instruction {
    pub gcode_line: usize,
    pub instr: Instr,
}

/// Represents all possible machine instructions.
///
/// Each family of G-codes roughly corresponds to one variant of this enum,
/// e.g. G2 and G3 both result in `Helix` or `HelixRadius`.
///
/// Some G-codes are handled completely internally, such as switching
/// units between inches and mm, or lathe mode.
#[derive(Debug)]
pub enum Instr {
    // G codes
    RapidMove(Coords),          // G0
    Move(Coords),               // G1
    Helix(bool, Coords, HelixCenter, u16),  // G2-3
    Dwell(f64),                 // G4
    // todo: Splines (G5)
    // todo: Tool table (G10)
    PlaneSelect(Plane), // G17-G19
    // ? Goto/Set predef // G28, G30
    // todo: spindle sync // G33
    Probe(Coords, u32),         // G38
    CutterComp(CutterComp),     // G40-42
    LengthComp(LengthComp),     // G43, G49
    // ? MachineCoords G53
    // ? CoordSystem G54-G59
    PathControl(PathMode),      // G61, G64
    // Cycles G73, G76, G80-89, G98-99
    // ? Distance mode G90,G91
    // ? Offsets G92
    // FeedRateMode(u16), // G93-95
    // SpindleControlMode(u16), // G96-97

    // M codes
    Pause(bool, bool),          // M0-1, M60
    End(bool),                  // M2, M30
    Spindle(Spindle),           // M3-5
    ToolChange,                 // M6
    Coolant(Coolant),           // M7-9
    UserDefined(u16, Option<f64>, Option<f64>), // M100-199  with P/Q words

    // Others
    FeedRate(f64),              // F
    SpindleSpeed(f64),          // S
    ToolSelect(u16),            // T
}

/// The Evaluator translates G-code into a series of machine instructions,
/// resolving variable interpolation, modal word state and ordering of words on
/// a line.
///
/// It does *not* calculate absolute coordinates for everything, or try to
/// resolve compund G-codes (like drilling cycles) to individual operations.
pub struct Evaluator {
    program: Program,
    // available axes
    axes: Vec<Axis>,
    // current parameter values
    vars: HashMap<Param, f64>,
    // private state tracking
    motion_mode: u16,
    state: State, // state manipulated by M70-73
    saved_state: Option<State>,
}

/*
    TODO: To save for M70:
    ----------------
    feed mode (G93/G94,G95)
    current coordinate system (G54-G59.3)
    retract mode (G98,G99)
    spindle mode (G96-css or G97-RPM)
    speed override (M51) and feed override (M50) settings
    adaptive feed setting (M52)
    feed hold setting (M53)
*/

#[derive(Default, Clone)]
struct State {
    feed_rate: f64,
    spindle_speed: f64,
    dist_rel: bool,
    offset_abs: bool,
    plane: Plane,
    cutter_comp: CutterComp,
    length_comp: LengthComp,
    path_mode: PathMode,
    spindle: Spindle,
    coolant: Coolant,
    lathe_diam: bool,
    inches: bool,
}

impl Evaluator {
    pub fn new(program: Program, axes: impl Into<Vec<Axis>>, vars: Option<HashMap<Param, f64>>) -> Self {
        Evaluator {
            program,
            axes: axes.into(),
            vars: vars.unwrap_or_default(),
            motion_mode: 1,
            state: Default::default(),
            saved_state: None,
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
                return Ok(());
            }
        }
        Err(EvalError { lineno: 0,
                        errtype: ErrType::Other("missing end of program code".into())})
    }

    pub fn set_var(&mut self, param: Param, value: f64) {
        self.vars.insert(param, value);
    }

    pub fn get_var(&mut self, param: Param) -> Option<f64> {
        self.vars.get(&param).cloned()
    }

    // -- private API --

    fn eval_block<F>(&mut self, block: &Block, mut exec: F) -> Result<bool, ErrType>
    where F: FnMut(&mut Self, Instruction) -> Result<(), ErrType>
    {
        macro_rules! exec {
            ($($tt:tt)*) => {
                exec(self, Instruction { gcode_line: block.lineno, instr: Instr::$($tt)*})?;
            }
        }

        // Set when we should return true to indicate one of the "end" words.
        let mut end_of_program = false;

        // Process words, by evaluating all expressions.
        let mut feed = None;
        let mut spindle = None;
        let mut tool = None;
        let mut gcodes = Codes(BitSet::with_capacity(1000), ErrType::ConflictingGCodes);
        let mut mcodes = Codes(BitSet::with_capacity(200), ErrType::ConflictingMCodes);
        let mut gens = GenWords(HashMap::new());
        let mut axes = HashMap::new();
        let mut offsets = HashMap::new();
        for word in &block.words {
            match word {
                Word::Feed(ex) => feed = Some(self.eval_expr(ex)?),
                Word::Spindle(ex) => spindle = Some(self.eval_expr(ex)?),
                Word::Tool(ex) => {
                    let n = num_to_int(self.eval_expr(ex)?, MAX_TOOL, ErrType::InvalidTool)?;
                    tool = Some(n);
                }
                Word::Gcode(ex) => {
                    let n = num_to_int(10. * self.eval_expr(ex)?, 1000, ErrType::InvalidGCode)?;
                    gcodes.insert(n);
                }
                Word::Mcode(ex) => {
                    let n = num_to_int(self.eval_expr(ex)?, 100, ErrType::InvalidMCode)?;
                    mcodes.insert(n);
                }
                Word::Arg(a, ex) => {
                    if let Some(ax) = Axis::from_arg(a) {
                        if !self.axes.contains(&ax) {
                            return Err(ErrType::InvalidAxis(ax));
                        }
                        axes.insert(ax, self.eval_expr(ex)?);
                    } else if let Some(off) = Offset::from_arg(a) {
                        offsets.insert(off, self.eval_expr(ex)?);
                    } else {
                        gens.insert(GenWord::from_arg(a).unwrap(), self.eval_expr(ex)?);
                    }
                }
            }
        }

        let has_axis_words = !(axes.is_empty() && offsets.is_empty());

        // Process assignments.  Since parameter assignment only takes place
        // after the whole line has evaluated, including in other assignments,
        // cache new values here and apply at the end.
        let mut new_values = vec![];
        for assign in &block.assignments {
            new_values.push((self.get_par_key(&assign.id)?,
                             self.eval_expr(&assign.value)?));
        }
        for (name, value) in new_values {
            self.vars.insert(name, value);
        }

        // Now execute all collected words. We need to respect the different
        // modal groups, and ensure that there are no conflicting words.

        // Determine motion mode first, since we need it to check some conflicts.
        let mut motion_mode = gcodes.modal_group("motion", &[
            0, 10, 20, 30, 50, 51, 52, 53, 330, 331, 382, 383, 384, 385,
            730, 760, 800, 810, 820, 830, 840, 850, 860, 870, 880, 890,
        ])?;

        // #1. Set feed rate mode (G93-G95) and spindle speed mode (G96-G97).
        // All but the default are unsupported.
        match gcodes.modal_group("feed rate mode", &[930, 940, 950])? {
            Some(940) | None => (),
            Some(x) => return Err(ErrType::UnsupportedGCode(x as u16))
        }
        match gcodes.modal_group("spindle speed mode", &[960, 970])? {
            Some(970) | None => (),
            Some(x) => return Err(ErrType::UnsupportedGCode(x as u16))
        }

        // #2. Execute F, S and T codes.
        if let Some(feed) = feed {
            self.state.feed_rate = feed;
            exec!(FeedRate(feed));
        }
        if let Some(speed) = spindle {
            self.state.spindle_speed = speed;
            exec!(SpindleSpeed(speed));
        }
        if let Some(tool) = tool { exec!(ToolSelect(tool)); }

        // #3. Execute toolchange (M6 and M61).
        match mcodes.modal_group("toolchange", &[6, 61])? {
            Some(6) => exec!(ToolChange),
            Some(61) => return Err(ErrType::UnsupportedMCode(61)), // TODO
            _ => ()
        }

        // #4. Switch spindle.
        if let Some(x) = mcodes.modal_group("spindle control", &[3, 4, 5])? {
            match x {
                3 => self.state.spindle = Spindle::Cw,
                4 => self.state.spindle = Spindle::Ccw,
                5 => self.state.spindle = Spindle::Off,
                _ => unreachable!()
            }
            exec!(Spindle(self.state.spindle));
        }

        // #5. Save or restore state (M70-M73), unsupported.
        if let Some(x) = mcodes.modal_group("save/restore", &[70, 71, 72, 73])? {
            return Err(ErrType::UnsupportedMCode(x as u16));
        }

        // #6. Switch coolant.
        if let Some(x) = mcodes.modal_group("coolant control", &[7, 8, 9])? {
            match x {
                7 => self.state.coolant.mist = true,
                8 => self.state.coolant.flood = true,
                9 => self.state.coolant = Coolant::default(),
                _ => unreachable!()
            }
            exec!(Coolant(self.state.coolant));
        }

        // #7. Overrides (M48-M53), currently unsupported.
        if let Some(x) = mcodes.modal_group("overrides", &[48, 49, 50, 51, 52, 53])? {
            return Err(ErrType::UnsupportedMCode(x as u16));
        }

        // #7.5. User defined codes.
        if let Some(x) = mcodes.modal_group("user-defined", USER_DEFINED)? {
            exec!(UserDefined(x as u16, gens.get(GenWord::P), gens.get(GenWord::Q)));
        }

        // #8. Dwell (G4).
        if gcodes.modal_group("dwell", &[40])?.is_some() {
            let secs = gens.get_def(GenWord::P, -1.0);
            if secs >= 0. {
                exec!(Dwell(secs));
            } else {
                return Err(ErrType::MissingGCodeWord(40, GenWord::P));
            }
        }

        // #9. Set active plane (G17-G19).
        if let Some(x) = gcodes.modal_group("active plane", &[170, 171, 180, 181, 190, 191])? {
            match x {
                170 => self.state.plane = Plane::XY,
                180 => self.state.plane = Plane::XZ,
                190 => self.state.plane = Plane::YZ,
                171 => self.state.plane = Plane::UV,
                181 => self.state.plane = Plane::UW,
                191 => self.state.plane = Plane::VW,
                _ => ()
            }
            exec!(PlaneSelect(self.state.plane));
        }

        // #10. Set length units (G20-G21).
        match gcodes.modal_group("length units", &[200, 210])? {
            Some(200) => self.state.inches = true,
            Some(210) => self.state.inches = false,
            _ => ()
        }

        // #10.1. Set lathe mode (G7-G8).
        match gcodes.modal_group("lathe mode", &[70, 80])? {
            Some(70) => return Err(ErrType::UnsupportedGCode(70)),
            Some(80) => self.state.lathe_diam = false,
            _ => ()
        }

        // Now fix up axis values to the length and lathe mode.
        if self.state.inches {
            axes.iter_mut().filter(|(&ax, _)| ax.is_linear()).for_each(|(_, v)| *v *= 25.4);
        }
        if self.state.lathe_diam {
            axes.iter_mut().filter(|(&ax, _)| ax == Axis::X).for_each(|(_, v)| *v /= 2.);
        }

        // #11. Set cutter radius compensation (G40-G42).  Only "off" is supported.
        if let Some(x) = gcodes.modal_group("cutter radius compensation", &[400, 410, 411, 420, 421])? {
            if x == 400 {
                self.state.cutter_comp = CutterComp::Off;
            } else {
                if self.state.cutter_comp != CutterComp::Off {
                    return Err(ErrType::CutterCompActive(x))
                }
                self.state.cutter_comp = match x {
                    410 => CutterComp::LeftFromTool(gens.get_int(GenWord::D, MAX_TOOL)?),
                    420 => CutterComp::RightFromTool(gens.get_int(GenWord::D, MAX_TOOL)?),
                    411 => CutterComp::LeftDynamic(
                        gens.get(GenWord::D).ok_or_else(|| ErrType::MissingGCodeWord(411, GenWord::D))?,
                        gens.get_int_def(GenWord::L, 0, 9)?),
                    421 => CutterComp::RightDynamic(
                        gens.get(GenWord::D).ok_or_else(|| ErrType::MissingGCodeWord(411, GenWord::D))?,
                        gens.get_int_def(GenWord::L, 0, 9)?),
                    _ => unreachable!()
                }
            }
            exec!(CutterComp(self.state.cutter_comp.clone()));
        }

        // #12. Set length compensation (G43, G49).
        if let Some(x) = gcodes.modal_group("cutter length compensation", &[430, 431, 432, 490])? {
            match x {
                430 => self.state.length_comp = LengthComp::FromTool(
                    gens.get_int(GenWord::H, MAX_TOOL)?, vec![]),
                432 => {
                    let tool = gens.get_int(GenWord::H, MAX_TOOL)?
                                   .ok_or_else(|| ErrType::MissingGCodeWord(432, GenWord::H))?;
                    match &mut self.state.length_comp {
                        LengthComp::Off => self.state.length_comp = LengthComp::FromTool(Some(tool), vec![]),
                        LengthComp::FromTool(_, vec) => vec.push(tool),
                        LengthComp::Dynamic(_, vec) => vec.push(tool),
                    }
                }
                431 => {
                    if let Some(x) = motion_mode {
                        return Err(ErrType::ConflictingGCodes("motion", 431, x));
                    }
                    let dyn_axes = std::mem::replace(&mut axes, HashMap::new());
                    self.state.length_comp = LengthComp::Dynamic(Coords::new(dyn_axes, true), vec![]);
                }
                490 => self.state.length_comp = LengthComp::Off,
                _ => unreachable!()
            }
            exec!(LengthComp(self.state.length_comp.clone()));
        }

        // #13. Select coordinate system (G54-G59). Only first one supported.
        match gcodes.modal_group("coordinate system", &[540, 550, 560, 570, 580, 590, 591, 592, 593])? {
            Some(540) | None => (),
            Some(x) => return Err(ErrType::UnsupportedGCode(x))
        }

        // #14. Set path control mode.
        if let Some(x) = gcodes.modal_group("path control", &[610, 611, 640])? {
            self.state.path_mode = match x {
                610 => PathMode::Exact,
                611 => PathMode::ExactStop,
                640 => PathMode::Blending(gens.get(GenWord::P), gens.get(GenWord::Q)),
                _ => unreachable!()
            };
            exec!(PathControl(self.state.path_mode));
        }

        // #15. Set distance mode.
        match gcodes.modal_group("distance mode", &[900, 910])? {
            Some(900) => self.state.dist_rel = false,
            Some(910) => self.state.dist_rel = true,
            _ => ()
        }
        match gcodes.modal_group("arc offset distance mode", &[901, 911])? {
            Some(901) => self.state.offset_abs = true,
            Some(911) => self.state.offset_abs = false,
            _ => ()
        }

        // #16. Set retract mode (G98-G99).  All unsupported.
        if let Some(x) = gcodes.modal_group("retract mode", &[980, 990])? {
            return Err(ErrType::UnsupportedGCode(x));
        }

        // #17. Reference modes and offsets.  All unsupported.
        if let Some(x) = gcodes.modal_group("reference/offsets", &[280, 281, 300, 301, 100,
                                                                   920, 921, 922, 923])? {
            return Err(ErrType::UnsupportedGCode(x));
        }

        // #18. Perform motion.
        let machine_coords = gcodes.modal_group("machine coords", &[530])?.is_some();
        if machine_coords {
            return Err(ErrType::UnsupportedGCode(530));
        }

        // Motion is also performed if there are any axis (or offset) words.
        if motion_mode.is_none() && has_axis_words {
            motion_mode = Some(self.motion_mode);
        }

        if let Some(x) = motion_mode {
            match x {
                0   => {
                    exec!(RapidMove(Coords::new(axes, self.state.dist_rel)));
                }
                10  => {
                    exec!(Move(Coords::new(axes, self.state.dist_rel)));
                }
                20 | 30 => {
                    match self.state.plane {
                        Plane::UV | Plane::UW | Plane::VW =>
                            return Err(ErrType::InvalidPlane(self.state.plane)),
                        Plane::XY if offsets.contains_key(&Offset::K) =>
                            return Err(ErrType::InvalidOffsetCoordinate(Offset::K)),
                        Plane::XZ if offsets.contains_key(&Offset::J) =>
                            return Err(ErrType::InvalidOffsetCoordinate(Offset::J)),
                        Plane::YZ if offsets.contains_key(&Offset::I) =>
                            return Err(ErrType::InvalidOffsetCoordinate(Offset::I)),
                        _ => ()
                    }

                    let center = if let Some(value) = gens.get(GenWord::R) {
                        if !offsets.is_empty() {
                            return Err(ErrType::MixedCenterRadiusArc);
                        }
                        if value == 0. {
                            return Err(ErrType::InvalidWordValue(GenWord::R, 0.));
                        }
                        HelixCenter::Radius(value)
                    } else {
                        if offsets.is_empty() {
                            return Err(ErrType::ArcCenterRequired);
                        }
                        HelixCenter::Center(
                            Coords::from_ijk(offsets, !self.state.offset_abs))
                    };

                    exec!(Helix(x == 20, Coords::new(axes, self.state.dist_rel),
                                center, gens.get_int_def(GenWord::P, 1, 1000)?));
                }
                _ => return Err(ErrType::UnsupportedGCode(x))
            }
            self.motion_mode = x;
        }

        // #19. Stop.
        match mcodes.modal_group("stop", &[0, 1, 2, 30, 60])? {
            Some(0) => exec!(Pause(false, false)),
            Some(1) => exec!(Pause(true, false)),
            Some(60) => exec!(Pause(false, true)),
            Some(x) => {
                // TODO: commented ones below
                // Origin offsets are set to the default (like G54).
                self.state.plane = Plane::XY;
                exec!(PlaneSelect(Plane::XY));
                self.state.dist_rel = false;
                // Feed rate mode is set to units per minute (like G94).
                // Feed and speed overrides are set to ON (like M48).
                self.state.cutter_comp = CutterComp::Off;
                exec!(CutterComp(CutterComp::Off));
                self.state.spindle = Spindle::Off;
                exec!(Spindle(Spindle::Off));
                self.state.coolant = Coolant::default();
                exec!(Coolant(self.state.coolant));
                self.motion_mode = 1;

                exec!(End(x == 30));
                end_of_program = true;
            }
            _ => ()
        }

        // Check for invalid codes.  All supported ones have been removed as part of
        // the modal group checks, so anything left over is unknown to us.
        if let Some(code) = gcodes.get_first() {
            return Err(ErrType::InvalidGCode(code as f64));
        }
        if let Some(code) = mcodes.get_first() {
            return Err(ErrType::InvalidGCode(code as f64));
        }

        Ok(end_of_program)
    }

    fn get_par_key<'a>(&self, id: &'a ParId) -> Result<Param, ErrType> {
        Ok(match id {
            ParId::Named(s) => Param::Named(s.clone()),
            ParId::Numeric(n) => Param::Num(*n),
            ParId::Indirect(expr) => {
                let parnum = self.eval_expr(&expr)?;
                Param::Num(num_to_int(parnum, MAX_PARAM, ErrType::InvalidParamNumber)?)
            }
        })
    }

    /// Evaluate a G-code expression.  The only available type is a floating-point number.
    fn eval_expr(&self, expr: &Expr) -> Result<f64, ErrType> {
        Ok(match expr {
            Expr::Num(value) => *value,
            Expr::Par(id) => {
                let key = self.get_par_key(id)?;
                match self.vars.get(&key) {
                    Some(value) => *value,
                    _ => return Err(ErrType::UnknownParameter(key))
                }
            }
            Expr::BinOp(op, left, right) => {
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
            Expr::UnOp(op, arg) => {
                let arg = self.eval_expr(arg)?;
                match op {
                    UnOp::Minus => -arg,
                    UnOp::Plus => arg,
                }
            }
            Expr::Call(func) => {
                match func {
                    Call::Exists(id) => {
                        let key = self.get_par_key(id)?;
                        if self.vars.contains_key(&key) { 1.0 } else { 0.0 }
                    }
                    Call::Atan(arg1, arg2) => {
                        let arg_y = self.eval_expr(arg1)?;
                        let arg_x = self.eval_expr(arg2)?;
                        arg_y.atan2(arg_x)
                    }
                    Call::Abs(arg)   => self.eval_expr(arg)?.abs(),
                    Call::Acos(arg)  => self.eval_expr(arg)?.acos(),
                    Call::Asin(arg)  => self.eval_expr(arg)?.asin(),
                    Call::Cos(arg)   => self.eval_expr(arg)?.cos(),
                    Call::Exp(arg)   => self.eval_expr(arg)?.exp(),
                    Call::Fix(arg)   => self.eval_expr(arg)?.floor(),
                    Call::Fup(arg)   => self.eval_expr(arg)?.ceil(),
                    Call::Round(arg) => self.eval_expr(arg)?.round(),
                    Call::Ln(arg)    => self.eval_expr(arg)?.ln(),
                    Call::Sin(arg)   => self.eval_expr(arg)?.sin(),
                    Call::Sqrt(arg)  => self.eval_expr(arg)?.sqrt(),
                    Call::Tan(arg)   => self.eval_expr(arg)?.tan(),
                }
            }
        })
    }
}


// ----- non-public helper APIs

/// Helper for flagging and retrieving G and M codes on a line.
struct Codes(BitSet, fn(&'static str, u16, u16) -> ErrType);

impl Codes {
    fn insert(&mut self, b: u16) {
        self.0.insert(b as usize);
    }

    fn modal_group(&mut self, name: &'static str, codes: &[usize])
                   -> Result<Option<u16>, ErrType> {
        let mut found = None;
        for &code in codes {
            if self.0[code] {
                if let Some(&other) = codes.iter().find(|&&c| self.0[c] && c != code) {
                    return Err((self.1)(name, code as u16, other as u16));
                }
                found = Some(code as u16);
            }
        }
        for &code in codes {
            self.0.set(code, false);
        }
        Ok(found)
    }

    fn get_first(&self) -> Option<usize> {
        self.0.ones().next()
    }
}


/// Helper for parsing generic argument words out of a G-code line.
struct GenWords(HashMap<GenWord, f64>);

impl GenWords {
    fn insert(&mut self, p: GenWord, v: f64) {
        self.0.insert(p, v);
    }

    fn get(&mut self, p: GenWord) -> Option<f64> {
        self.0.remove(&p)
    }

    fn get_def(&mut self, p: GenWord, def: f64) -> f64 {
        self.0.remove(&p).unwrap_or(def)
    }

    fn get_int(&mut self, p: GenWord, max: u16) -> Result<Option<u16>, ErrType> {
        self.0.remove(&p).map(
            |f| num_to_int(f, max, |n| ErrType::InvalidWordValue(p, n))
        ).transpose()
    }

    fn get_int_def(&mut self, p: GenWord, def: u16, max: u16) -> Result<u16, ErrType> {
        self.get_int(p, max).map(|v| v.unwrap_or(def))
    }
}

const USER_DEFINED: &[usize] = &[
    100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117,
    118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135,
    136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153,
    154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171,
    172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189,
    190, 191, 192, 193, 194, 195, 196, 197, 198, 199];
