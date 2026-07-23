#![feature(rustc_private)]

fn main() {
    rust_verify::cli::run_verifier(std::env::args());
}
