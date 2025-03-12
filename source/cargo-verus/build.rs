//
// Copyright (c) 2024 The Verus Contributors
//
// SPDX-License-Identifier: MIT
//

fn main() {
    rustc_tools_util::setup_version_info!();

    // See https://doc.rust-lang.org/cargo/reference/build-scripts.html#rerun-if-changed
    println!("cargo:rerun-if-changed=build.rs");
}
