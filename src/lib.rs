// Copyright (c) 2019 Georg Brandl.  Licensed under the Apache License,
// Version 2.0 <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0>
// or the MIT license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at
// your option. This file may not be copied, modified, or distributed except
// according to those terms.

//! A G-Code parsing and evaluation library, aiming for compatibility with the
//! [LinuxCNC] dialect of G-Code.
//!
//! Currently, it can parse G-Code into an AST, using the Pest parser library.
//! An evaluator is work in progress and the current state can be enabled with
//! the *eval* feature flag.
//!
//! [LinuxCNC]: http://linuxcnc.org/docs/html/gcode/overview.html
//!
//! ## Basic usage
//!
//! Use `ngc::parse::parse` to get an AST, then work with the abstract syntax
//! tree datastructures from `ngc::ast`.
//!
//! Later, you will be able to feed this into an evaluator from `ngc::eval`,
//! which takes care of evaluating expressions, checking invalid codes and
//! combinations, and yielding a series of more machine-level instructions.
//!
//! The following code (the same as the "ngc-parse" demo binary) takes a file as
//! an argument, parses it and outputs the display form, which is the same
//! G-code, but in a consistent format and cleaned of comments.
//!
//! ```rust,no_run
//! use std::{env, fs};
//! use ngc::parse::parse;
//!
//! fn main() {
//!     let filename = env::args().nth(1).unwrap();
//!     let input = fs::read_to_string(&filename).unwrap();
//!
//!     match parse(&filename, &input) {
//!         Err(e) => eprintln!("Parse error: {}", e),
//!         Ok(prog) => println!("{}", prog),
//!     }
//! }
//! ```
//!
//! ## Unsupported features
//!
//! Currently, LinuxCNC's control flow constructs ("O codes") are completely
//! unsupported.


pub mod ast;
pub mod parse;

#[cfg(feature = "eval")]
pub mod eval;

// internal helpers
pub(crate) mod util;
