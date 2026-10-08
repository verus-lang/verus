use std::fs;
use std::process::Command;

fn run(args: &[&std::path::Path]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_verus-exec")).args(args).output().unwrap()
}

#[test]
fn file_stdout_and_output() {
    let temp = tempfile::tempdir().unwrap();
    let input = temp.path().join("input.rs");
    let output = temp.path().join("output.rs");
    fs::write(&input, "verus! {\nfn f() { assert(true); assert!(true); }\n}\n").unwrap();
    let result = run(&[&input]);
    assert!(result.status.success(), "{:?}", result);
    assert_eq!(String::from_utf8(result.stdout).unwrap(), "fn f() {  assert!(true); }\n");
    let result = run(&[&input, std::path::Path::new("-o"), &output]);
    assert!(result.status.success());
    assert_eq!(fs::read_to_string(&output).unwrap(), "fn f() {  assert!(true); }\n");
    assert!(!run(&[&input, std::path::Path::new("-o"), &output]).status.success());
}

#[test]
fn crate_copy_keeps_resources_and_skips_build_output() {
    let temp = tempfile::tempdir().unwrap();
    let input = temp.path().join("crate");
    let output = temp.path().join("snapshot");
    fs::create_dir_all(input.join("src/nested")).unwrap();
    fs::create_dir_all(input.join("target")).unwrap();
    fs::write(input.join("Cargo.toml"), "[package]\nname = \"test\"\nversion = \"0.1.0\"\n")
        .unwrap();
    fs::write(input.join("src/lib.rs"), "#[verus_spec(requires true,)]\npub fn f() {}\n").unwrap();
    fs::write(input.join("src/nested/m.rs"), "verus! {\nproof fn lemma() {}\nfn f() {}\n}\n")
        .unwrap();
    fs::write(input.join("resource.bin"), [0, 255, 0]).unwrap();
    fs::write(input.join("target/broken.rs"), "not valid rust").unwrap();
    let result = run(&[&input.join("Cargo.toml"), std::path::Path::new("-o"), &output]);
    assert!(result.status.success(), "{:?}", result);
    assert_eq!(fs::read_to_string(output.join("src/lib.rs")).unwrap(), "pub fn f() {}\n");
    assert_eq!(fs::read_to_string(output.join("src/nested/m.rs")).unwrap(), "fn f() {}\n");
    assert_eq!(fs::read(output.join("resource.bin")).unwrap(), [0, 255, 0]);
    assert!(!output.join("target").exists());
    assert_eq!(
        fs::read(input.join("Cargo.toml")).unwrap(),
        fs::read(output.join("Cargo.toml")).unwrap()
    );
}

#[test]
fn failed_crate_copy_leaves_no_snapshot() {
    let temp = tempfile::tempdir().unwrap();
    let input = temp.path().join("crate");
    let output = temp.path().join("snapshot");
    fs::create_dir_all(&input).unwrap();
    fs::write(input.join("Cargo.toml"), "").unwrap();
    fs::write(input.join("broken.rs"), "verus! { fn f( }").unwrap();
    assert!(!run(&[&input, std::path::Path::new("-o"), &output]).status.success());
    assert!(!output.exists());
    assert_eq!(fs::read_dir(temp.path()).unwrap().count(), 1);
}

#[test]
fn crate_copy_skips_git_worktree_files_and_nested_git_directories() {
    let temp = tempfile::tempdir().unwrap();
    let input = temp.path().join("crate");
    let output = temp.path().join("snapshot");
    fs::create_dir_all(input.join("nested/.git")).unwrap();
    fs::write(input.join("Cargo.toml"), "").unwrap();
    fs::write(input.join(".git"), "gitdir: /original/repo/.git/worktrees/crate\n").unwrap();
    fs::write(input.join("nested/.git/invalid.rs"), "not valid Rust").unwrap();
    fs::write(input.join("lib.rs"), "fn f() {}\n").unwrap();
    let result = run(&[&input, std::path::Path::new("-o"), &output]);
    assert!(result.status.success(), "{:?}", result);
    assert!(!output.join(".git").exists());
    assert!(!output.join("nested/.git").exists());
    assert_eq!(fs::read_to_string(output.join("lib.rs")).unwrap(), "fn f() {}\n");
}

#[cfg(unix)]
#[test]
fn symlink_inputs_and_entries_are_rejected() {
    use std::os::unix::fs::symlink;

    let temp = tempfile::tempdir().unwrap();
    let input = temp.path().join("crate");
    let output = temp.path().join("snapshot");
    let alias = temp.path().join("alias");
    fs::create_dir(&input).unwrap();
    fs::write(input.join("Cargo.toml"), "").unwrap();
    fs::write(input.join("lib.rs"), "fn f() {}\n").unwrap();
    symlink(&input, &alias).unwrap();
    assert!(!run(&[&alias, std::path::Path::new("-o"), &output]).status.success());
    symlink(input.join("lib.rs"), input.join("alias.rs")).unwrap();
    assert!(!run(&[&input, std::path::Path::new("-o"), &output]).status.success());
    assert!(!output.exists());
}

#[test]
fn crate_output_inside_input_is_rejected() {
    let temp = tempfile::tempdir().unwrap();
    let input = temp.path().join("crate");
    fs::create_dir(&input).unwrap();
    fs::write(input.join("Cargo.toml"), "").unwrap();
    let output = input.join("snapshot");
    assert!(!run(&[&input, std::path::Path::new("-o"), &output]).status.success());
    assert!(!output.exists());
}

#[test]
fn crate_excludes_skip_custom_build_output() {
    let temp = tempfile::tempdir().unwrap();
    let input = temp.path().join("crate");
    let output = temp.path().join("snapshot");
    fs::create_dir_all(input.join("target-custom")).unwrap();
    fs::write(input.join("Cargo.toml"), "").unwrap();
    fs::write(input.join("target-custom/broken.rs"), "not valid Rust").unwrap();
    fs::write(input.join("launcher"), "not needed in the snapshot").unwrap();
    fs::write(input.join("lib.rs"), "fn f() {}\n").unwrap();
    let result = run(&[
        &input,
        std::path::Path::new("-o"),
        &output,
        std::path::Path::new("--exclude"),
        std::path::Path::new("target-custom"),
        std::path::Path::new("--exclude"),
        std::path::Path::new("launcher"),
    ]);
    assert!(result.status.success(), "{:?}", result);
    assert!(!output.join("target-custom").exists());
    assert!(!output.join("launcher").exists());
    assert_eq!(fs::read_to_string(output.join("lib.rs")).unwrap(), "fn f() {}\n");
}

#[test]
fn crate_excludes_reject_parent_paths() {
    let temp = tempfile::tempdir().unwrap();
    let input = temp.path().join("crate");
    let output = temp.path().join("snapshot");
    fs::create_dir(&input).unwrap();
    fs::write(input.join("Cargo.toml"), "").unwrap();
    let result = run(&[
        &input,
        std::path::Path::new("-o"),
        &output,
        std::path::Path::new("--exclude"),
        std::path::Path::new("../crate"),
    ]);
    assert!(!result.status.success());
    assert!(!output.exists());
}

#[test]
fn extracted_expressions_and_constants_compile_and_execute() {
    let temp = tempfile::tempdir().unwrap();
    let input = temp.path().join("input.rs");
    let output = temp.path().join("output.rs");
    let binary = temp.path().join(format!("snapshot{}", std::env::consts::EXE_SUFFIX));
    fs::write(
        &input,
        "verus! {\n#[cfg(verus_keep_ghost)]\nmod ghost { custom! { opaque tokens } }\nexec const C: u32 ensures C == 9 { verus_exec_expr!(1 + 2) * 3 }\nfn value() -> (result: u32) ensures result == C { C }\n}\nfn main() {\n    let unit = proof! { assert(true); };\n    assert_eq!(unit, ());\n    verus_exec_expr!{assert_eq!(C, 9)}\n    let value = verus_exec_expr!{1 + 2} * 3;\n    assert_eq!(value, 9);\n    assert_eq!(crate::value(), 9);\n}\n",
    )
    .unwrap();
    let result = run(&[&input, std::path::Path::new("-o"), &output]);
    assert!(result.status.success(), "{:?}", result);
    let compile = Command::new("rustc")
        .arg("--edition=2021")
        .arg(&output)
        .arg("-o")
        .arg(&binary)
        .output()
        .unwrap();
    assert!(compile.status.success(), "{:?}", compile);
    assert!(Command::new(binary).status().unwrap().success());
}

#[test]
fn macro_expansions_compile_and_match_normal_macro_execution() {
    let temp = tempfile::tempdir().unwrap();
    let source =
        fs::canonicalize(std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")).unwrap();
    let fixture = include_str!("fixtures/macros.rs");
    let src = temp.path().join("src");
    fs::create_dir(&src).unwrap();
    fs::write(
        temp.path().join("Cargo.toml"),
        format!(
            "[package]\nname = \"exec-macro-test\"\nversion = \"0.1.0\"\nedition = \"2021\"\n[workspace]\n[dependencies]\nvstd = {{ path = {:?} }}\nverus_state_machines_macros = {{ path = {:?} }}\n",
            source.join("vstd"), source.join("state_machines_macros"),
        ),
    )
    .unwrap();
    let execute = |text: &str| {
        fs::write(src.join("main.rs"), text).unwrap();
        // Running outside source/ selects normal rustc's ghost-free config.
        let output = Command::new("cargo")
            .current_dir(temp.path())
            .args(["run", "--offline", "--quiet"])
            .env_remove("RUSTFLAGS")
            .env_remove("CARGO_ENCODED_RUSTFLAGS")
            .env_remove("CARGO_BUILD_RUSTFLAGS")
            .env_remove("VSTD_KIND")
            .output()
            .unwrap();
        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr),);
        output.stdout
    };
    let normal = execute(fixture);
    let extracted = verus_exec::strip_source(fixture).unwrap();
    assert!(!extracted.contains("atomic_with_ghost!"));
    assert!(!extracted.contains("struct_with_invariants!"));
    assert!(!extracted.contains("tokenized_state_machine!"));
    assert!(!extracted.contains("tokenized_state_machine_vstd!"));
    assert!(!extracted.contains("state_machine!"));
    assert_eq!(execute(&extracted), normal);
    assert_eq!(verus_exec::strip_source(&extracted).unwrap(), extracted);
}
