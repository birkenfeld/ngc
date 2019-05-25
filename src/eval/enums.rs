// Copyright (c) 2019 Georg Brandl.  Licensed under the Apache License,
// Version 2.0 <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0>
// or the MIT license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at
// your option. This file may not be copied, modified, or distributed except
// according to those terms.

use std::fmt;
use std::collections::HashMap;
use strum_macros::Display;

use crate::ast::*;

/// Identifier for a parameter: either numeric or named.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Param {
    Num(u16),
    Named(String),
}

impl fmt::Display for Param {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Param::Num(n) => write!(f, "#{}", n),
            Param::Named(s) => write!(f, "#<{}>", s),
        }
    }
}

/// An axis supported by G-code.
///
/// Concrete machines usually only support some subset of axes.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Display)]
pub enum Axis {
    A, B, C,
    U, V, W,
    X, Y, Z,
}

impl Axis {
    pub(super) fn from_arg(arg: &Arg) -> Option<Self> {
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

    pub fn is_linear(&self) -> bool {
        match self {
            Axis::A | Axis::B | Axis::C => false,
            _ => true
        }
    }
}

/// An arc center offset or coordinate.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Display)]
pub enum Offset {
    I, J, K,
}

impl Offset {
    pub(super) fn from_arg(arg: &Arg) -> Option<Self> {
        Some(match arg {
            Arg::OffsetI => Offset::I,
            Arg::OffsetJ => Offset::J,
            Arg::OffsetK => Offset::K,
            _ => return None
        })
    }
}

/// A generic argument word, such as `P`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Display)]
pub enum GenWord {
    D, E, H, L,
    P, Q, R,
}

impl GenWord {
    pub(super) fn from_arg(arg: &Arg) -> Option<Self> {
        Some(match arg {
            Arg::ParamD => GenWord::D,
            Arg::ParamE => GenWord::E,
            Arg::ParamH => GenWord::H,
            Arg::ParamL => GenWord::L,
            Arg::ParamP => GenWord::P,
            Arg::ParamQ => GenWord::Q,
            Arg::ParamR => GenWord::R,
            _ => return None
        })
    }
}

/// A plane as selected by G17-G19.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Display)]
pub enum Plane {
    XY, XZ, YZ,
    UV, UW, VW,
}

impl Default for Plane {
    fn default() -> Self { Plane::XY }
}

/// A collection of axis coordinates.
///
/// All length measures are in millimeters.
/// All angle measures are in degrees.
#[derive(Clone, PartialEq)]
pub struct Coords {
    pub rel: bool,
    pub map: HashMap<Axis, f64>,
}

impl Coords {
    pub fn new(map: HashMap<Axis, f64>, rel: bool) -> Self {
        Self { map, rel }
    }

    pub(crate) fn from_ijk(map: HashMap<Offset, f64>, rel: bool) -> Self {
        Self {
            rel: rel,
            map: map.into_iter().map(|(k, v)| (match k {
                Offset::I => Axis::X,
                Offset::J => Axis::Y,
                Offset::K => Axis::Z,
            }, v)).collect()
        }
    }
}

impl fmt::Debug for Coords {
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

/// A spindle state.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Spindle {
    Off, Cw, Ccw,
}

impl Default for Spindle {
    fn default() -> Self { Spindle::Off }
}

/// A coolant state.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
pub struct Coolant {
    pub mist: bool,
    pub flood: bool,
}

/// A cutter compensation state.
///
/// The value in Left/Right variants is the tool number to use.
#[derive(Clone, PartialEq, Debug)]
pub enum CutterComp {
    Off,
    LeftFromTool(Option<u16>),
    RightFromTool(Option<u16>),
    LeftDynamic(f64, u16),
    RightDynamic(f64, u16),
}

impl Default for CutterComp {
    fn default() -> Self { CutterComp::Off }
}

/// A length compensation state.
///
/// The vector member contains additional tool offsets added with G43.2.
#[derive(Clone, PartialEq, Debug)]
pub enum LengthComp {
    Off,
    FromTool(Option<u16>, Vec<u16>),
    Dynamic(Coords, Vec<u16>),
}

impl Default for LengthComp {
    fn default() -> Self { LengthComp::Off }
}

/// A path control mode.
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum PathMode {
    Exact,
    ExactStop,
    Blending(Option<f64>, Option<f64>),
}

impl Default for PathMode {
    fn default() -> Self { PathMode::Exact }
}

/// Center specification for a helix.
#[derive(Clone, Debug)]
pub enum HelixCenter {
    Center(Coords),
    Radius(f64),
}
