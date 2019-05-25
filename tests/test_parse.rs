// Copyright (c) 2019 Georg Brandl.  Licensed under the Apache License,
// Version 2.0 <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0>
// or the MIT license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at
// your option. This file may not be copied, modified, or distributed except
// according to those terms.

use ngc::parse;

#[test]
fn test_parse() {
    let src = r#"; Try to exercise as much of the syntax as possible.

; comments anywhere, line numbers, and block deletion
/G1 X1 0(a)(b) Y2(a);rest
/(a)
(a)N1 G#1 X-[10] (a)

; number formats
#1=+1. (a) #2=1.5 #3=-.5

; expressions
G[[1+ 2]/ 3*4--5]
G+SIN[0]
G[ATAN[1]/[2]]
G[1 LE 2]

; parameter references
#1=[1+2]
#<de pth>=1
#<de(a) pth>=2
#[1 ]=3
#-#2=[+ 5]
#SIN [0]=7 ; LCNC doesn't like this.
# 10 = EXISTS[#<blub>]

"#;

    let parsed = r#"/ G1 X10 Y2
G#1 X-10
#1=1 #2=1.5 #3=-0.5
G[[[[1 + 2] / 3] * 4] - -5]
GSIN[0]
GATAN[1]/[2]
G[1 LE 2]
#1=[1 + 2]
#<depth>=1
#<de(a)pth>=2
#1=3
#-#2=5
#[SIN[0]]=7
#10=EXISTS[#<blub>]
"#;

    let prog = parse::parse("testfile", src).unwrap();

    // make sure we count lines correctly
    assert_eq!(prog.blocks[0].lineno, 4);

    println!("{:#?}", prog);
    assert_eq!(prog.to_string(), parsed.replace("\n", " \n"));
}

#[test]
fn test_invalid() {
    for snippet in &[
        "$",            // invalid characters
        "GG",           // missing values
        "O10",          // O-words are unsupported
        "(",            // unclosed comments
        "(\n)",         // comments spanning lines
        "G(a)1",        // comments between letter/value
        "G1(a)2",       // comments within the value
        "G[1(a)+2]",    // comments within an expression
        "G[1;]",        // line comments within expression
        "G[TEST[x]]",   // invalid function
        "#1.2=5",       // fractional parameter number
        "#1=EXISTS[5]", // invalid EXISTS argument
    ] {
        assert!(parse::parse("testfile", snippet).is_err());
    }
}
