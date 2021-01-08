use std::{env, fs};
use ngc::parse::parse;

fn main() {
    let filename = env::args().nth(1).expect("file name required");
    let input = fs::read_to_string(&filename).unwrap();

    match parse(&filename, &input) {
        Err(e) => eprintln!("Parse error: {}", e),
        Ok(prog) => println!("{}", prog),
    }
}
