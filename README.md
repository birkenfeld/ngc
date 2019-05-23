# ngc - G-Code parser/evaluator for Rust

[![Build Status](https://travis-ci.org/birkenfeld/ngc.svg?branch=master)](https://travis-ci.org/birkenfeld/ngc)
[![Build Status](https://docs.rs/ngc/badge.svg)](https://docs.rs/ngc)
[![crates.io](http://meritbadge.herokuapp.com/ngc)](https://crates.io/crates/ngc)

**Work in progress!**

Currently, only the parser is functional.

## Documentation

[Module documentation](https://docs.rs/ngc) is hosted on docs.rs.

## Examples

The following code (the same as the "ngc-parse" demo binary) takes a file as
an argument, parses it and outputs the display form, which is the same
G-code, but in a consistent format and cleaned of comments.

```rust
use std::{env, fs};
use ngc::parse::parse;

fn main() {
    let filename = env::args().nth(1).unwrap();
    let input = fs::read_to_string(&filename).unwrap();

    match parse(&filename, &input) {
        Err(e) => eprintln!("Parse error: {}", e),
        Ok(prog) => println!("{}", prog),
    }
}
```
