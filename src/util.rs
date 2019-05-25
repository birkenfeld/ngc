// Copyright (c) 2019 Georg Brandl.  Licensed under the Apache License,
// Version 2.0 <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0>
// or the MIT license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at
// your option. This file may not be copied, modified, or distributed except
// according to those terms.


/// Helper for converting a floating number to an integer, or a suitable exception.
pub fn num_to_int<T>(inp: f64, figures: i32, max: f64, err: impl FnOnce(f64) -> T) -> Result<u16, T> {
    let v = inp * 10f64.powi(figures);
    if v.round() >= max {
        Err(err(inp))
    } else if (v.round() - v).abs() < 0.0001 && v >= 0. && v <= 65535. {
        Ok(v.round() as u16)
    } else {
        Err(err(inp))
    }
}
