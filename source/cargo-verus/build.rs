//
// Copyright (c) 2024 The Verus Contributors
//
// SPDX-License-Identifier: MIT
//

fn main() {
    rustc_tools_util::setup_version_info!();

    let manifest_dir = std::path::PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let toolchain_manifests_dir = manifest_dir.join("toolchain-manifests");
    let out_dir = std::path::PathBuf::from(std::env::var("OUT_DIR").unwrap());
    let generated_toolchains = out_dir.join("toolchain_list.rs");

    let toolchains =
        cargo_verus_toolchains::ToolchainList::parse_from_dir(&toolchain_manifests_dir);
    let mut generated = String::new();
    toolchains
        .format_code(cargo_verus_toolchains::Indent::default(), &mut generated)
        .expect("format generated toolchains");
    std::fs::write(&generated_toolchains, generated).expect("write generated toolchains");

    // See https://doc.rust-lang.org/cargo/reference/build-scripts.html#rerun-if-changed
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed={}", toolchain_manifests_dir.display());
}
