#![feature(rustc_private)]

mod config;
mod rust_to_vir;
mod util;
mod verifier;

extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir_build;
extern crate rustc_span;
extern crate rustc_typeck;

use config::take_our_args;
use std::env;
use verifier::Verifier;

struct CompilerCallbacks;

impl rustc_driver::Callbacks for CompilerCallbacks {}

pub fn main() {
    let mut args: Vec<String> = env::args().collect();
    let our_args = take_our_args(&mut args);

    // Run verifier callback to build VIR tree and run verifier
    let mut verifier = Verifier::new(our_args);
    let status = rustc_driver::RunCompiler::new(&args, &mut verifier).run();
    println!(
        "Verification results:: verified: {} errors: {}",
        verifier.count_verified, verifier.count_errors
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
        rustc_driver::RunCompiler::new(&args, &mut CompilerCallbacks)
            .run()
            .expect("RunCompiler.run() failed");
    }
}
