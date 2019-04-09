// Copyright (c) 2019 Georg Brandl.  Licensed under the Apache License,
// Version 2.0 <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0>
// or the MIT license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at
// your option. This file may not be copied, modified, or distributed except
// according to those terms.

use ngc::parse::parse;

fn main() -> Result<(), Box<std::error::Error>> {
    let text = std::fs::read_to_string(std::env::args().nth(1).unwrap()).unwrap();
    match parse("input.ngc", &text) {
        Err(e) => println!("Error: {}", e),
        Ok(prog) => println!("Successful:\n{}", prog),
    }
    Ok(())
}
