#![feature(rustc_private)]

extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir_build;
extern crate rustc_span;
extern crate rustc_typeck;

use rust_verify::config;
use rust_verify::verifier::Verifier;

struct CompilerCallbacks;

impl rustc_driver::Callbacks for CompilerCallbacks {}

pub fn main() {
    let mut args = std::env::args();
    let program = args.next().unwrap();
    let (our_args, rustc_args) = config::parse_args(&program, args);

    // Run verifier callback to build VIR tree and run verifier
    let mut verifier = Verifier::new(our_args);
    let status = rustc_driver::RunCompiler::new(&rustc_args, &mut verifier).run();
    println!(
        "Verification results:: verified: {} errors: {}",
        verifier.count_verified,
        verifier.errors.len()
    );
    match status {
        Ok(_) => {}
        Err(_) => {
            std::process::exit(1);
        }
    }

    // Run borrow checker and compiler (if enabled)
    let compile = false;
    if compile {
        rustc_driver::RunCompiler::new(&rustc_args, &mut CompilerCallbacks)
            .run()
            .expect("RunCompiler.run() failed");
    }
}
