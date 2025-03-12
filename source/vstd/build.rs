use std::env;

const RUST_MIN_STACK_ENV: &str = "RUST_MIN_STACK";

const RUST_MIN_STACK_DEFAULT: u64 = 10 * 1024 * 1024;

fn main() {
    let already_specified = match env::var_os(RUST_MIN_STACK_ENV) {
        None => false,
        Some(s) => !s.is_empty(),
    };

    if !already_specified {
        println!("cargo:rustc-env={RUST_MIN_STACK_ENV}={RUST_MIN_STACK_DEFAULT}");
    }

    println!("cargo:rerun-if-env-changed={RUST_MIN_STACK_ENV}");
}
