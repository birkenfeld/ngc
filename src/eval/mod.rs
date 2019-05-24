// Copyright (c) 2019 Georg Brandl.  Licensed under the Apache License,
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

const MAX_TOOL: u16 = 100; // TODO?
const MAX_PARAM: u16 = 10000;

/// A machine instruction collected from G-code.
pub struct Instruction {
    pub gcode_line: usize,
    pub instr: Instr,
}

/// Represents all possible machine instructions.
///
/// Each family of G-codes roughly corresponds to one variant of this enum,
/// e.g. G2 and G3 both result in `Helix`.
///
/// Some G-codes are handled completely internally, such as switching
/// units between inches and mm, or lathe mode.
#[derive(Debug)]
pub enum Instr {
    // G codes
    RapidMove(Coords<Axis>),    // G0
    Move(Coords<Axis>),         // G1
    Helix(bool, Coords<Axis>,
          Coords<Arc>, u16),    // G2-3
    Dwell(f64),                 // G4
    // todo: Splines (G5)
    // todo: Tool table (G10)
    PlaneSelect(Plane), // G17-G19
    // ? Goto/Set predef // G28, G30
    // todo: spindle sync // G33
    Probe(Coords<Axis>, u32), // G38
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
    // private stuff
    state: State,
}

#[derive(Default)]
struct State {
    motion_mode: u16,
    dist_rel: bool,
    arc_rel: bool,
    plane: Plane,
    cutter_comp: CutterComp,
    length_comp: LengthComp,
    spindle: Spindle,
    coolant: Coolant,
    // TODO: actually use these.
    lathe_diam: bool,
    inches: bool,
}

impl Evaluator {
    pub fn new(program: Program, axes: impl Into<Vec<Axis>>, vars: Option<HashMap<Param, f64>>) -> Self {
        Evaluator {
            program,
            axes: axes.into(),
            vars: vars.unwrap_or_default(),
            state: Default::default(),
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
        let mut mcodes = Codes(BitSet::with_capacity(100), ErrType::ConflictingMCodes);
        let mut gens = GenWords(HashMap::new());
        let mut axes = HashMap::new();
        let mut arcs = HashMap::new();
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
                    } else if let Some(arc) = Arc::from_arg(a) {
                        arcs.insert(arc, self.eval_expr(ex)?);
                    } else {
                        gens.insert(GenWord::from_arg(a).unwrap(), self.eval_expr(ex)?);
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
        if let Some(feed) = feed { exec!(FeedRate(feed)); }
        if let Some(speed) = spindle { exec!(SpindleSpeed(speed)); }
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
            self.state.length_comp = match x {
                430 => LengthComp::FromTool(gens.get_int(GenWord::H, MAX_TOOL)?),
                432 => LengthComp::Additional(gens.get_int(GenWord::H, MAX_TOOL)?
                                              .ok_or_else(|| ErrType::MissingGCodeWord(432, GenWord::H))?),
                431 => {
                    if let Some(x) = motion_mode {
                        return Err(ErrType::ConflictingGCodes("motion", 431, x));
                    }
                    let dyn_axes = std::mem::replace(&mut axes, HashMap::new());
                    LengthComp::Dynamic(coords(dyn_axes, true))
                }
                490 => LengthComp::Off,
                _ => unreachable!()
            };
            exec!(LengthComp(self.state.length_comp.clone()));
        }

        // #13. Select coordinate system (G54-G59). Only first one supported.
        match gcodes.modal_group("coordinate system", &[540, 550, 560, 570, 580, 590, 591, 592, 593])? {
            Some(540) | None => (),
            Some(x) => return Err(ErrType::UnsupportedGCode(x))
        }

        // #14. Set path control mode.
        match gcodes.modal_group("path control", &[610, 611, 640])? {
            Some(610) => exec!(PathControl(PathMode::Exact)),
            Some(611) => exec!(PathControl(PathMode::ExactStop)),
            Some(640) => exec!(PathControl(PathMode::Blending(gens.get(GenWord::P),
                                                              gens.get(GenWord::Q)))),
            _ => ()
        }

        // #15. Set distance mode.
        match gcodes.modal_group("distance mode", &[900, 910])? {
            Some(900) => self.state.dist_rel = false,
            Some(910) => self.state.dist_rel = true,
            _ => ()
        }
        match gcodes.modal_group("arc distance mode", &[901, 911])? {
            Some(901) => self.state.arc_rel = false,
            Some(911) => self.state.arc_rel = true,
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

        // Motion is also performed if there are any axis (or arc) words.
        if motion_mode.is_none() && has_axis_words {
            motion_mode = Some(self.state.motion_mode);
        }

        if let Some(x) = motion_mode {
            match x {
                0   => exec!(RapidMove(coords(axes, self.state.dist_rel))),
                10  => exec!(Move(coords(axes, self.state.dist_rel))),
                20 | 30 => {
                    match self.state.plane {
                        Plane::UV | Plane::UW | Plane::VW =>
                            return Err(ErrType::InvalidPlane(self.state.plane)),
                        Plane::XY if arcs.contains_key(&Arc::K) =>
                            return Err(ErrType::InvalidArcCoordinate(Arc::K)),
                        Plane::XZ if arcs.contains_key(&Arc::J) =>
                            return Err(ErrType::InvalidArcCoordinate(Arc::J)),
                        Plane::YZ if arcs.contains_key(&Arc::I) =>
                            return Err(ErrType::InvalidArcCoordinate(Arc::I)),
                        _ => ()
                    }

                    exec!(Helix(x == 20, coords(axes, self.state.dist_rel),
                                coords(arcs, self.state.arc_rel),
                                gens.get_int_def(GenWord::P, 1, 1000)?));
                }
                _ => return Err(ErrType::UnsupportedGCode(x))
            }
            self.state.motion_mode = x;
        }

        // #19. Stop.
        match mcodes.modal_group("stop", &[0, 1, 2, 30, 60])? {
            Some(0) => exec!(Pause(false, false)),
            Some(1) => exec!(Pause(true, false)),
            Some(60) => exec!(Pause(false, true)),
            Some(2) => { exec!(End(false)); end_of_program = true; }
            Some(30) => { exec!(End(true)); end_of_program = true; }
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

fn coords<T>(map: HashMap<T, f64>, rel: bool) -> Coords<T> {
    Coords { rel, map }
}


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
