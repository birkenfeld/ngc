use std::{env, fs};
use ngc::parse::parse;
use ngc::eval::{Evaluator, Axis};

fn main() {
    let filename = env::args().nth(1).unwrap();
    let input = fs::read_to_string(&filename).unwrap();
    match parse(&filename, &input) {
        Err(e) => eprintln!("Parse error: {}", e),
        Ok(prog) => {
            let axes = vec![Axis::X, Axis::Y, Axis::Z];
            let result = Evaluator::new(prog, axes, None).eval(false, |_, instr| {
                println!("{:?}", instr.instr);
                Ok(())
            });
            if let Err(e) = result {
                eprintln!("{}", e);
            }
        }
    }
}
