#![feature(rustc_private)]

pub fn main() {
    rust_verify::cli::run_verifier(std::env::args())
}
