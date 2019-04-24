use std::{env, fs};
use ngc::parse::parse;
use ngc::interp::{Interpreter, Axis};

fn main() {
    let filename = env::args().nth(1).unwrap();
    let input = fs::read_to_string(&filename).unwrap();
    match parse(&filename, &input) {
        Err(e) => eprintln!("Parse error: {}", e),
        Ok(prog) => {
            let mut interp = Interpreter::new(prog, vec![Axis::X, Axis::Y, Axis::Z], None);
            match interp.interpret(false, |_, instr| {
                println!("{:?}", instr.instr);
                Ok(())
            }) {
                Err(e) => eprintln!("{}", e),
                Ok(_) => return
            }
        }
    }
}
