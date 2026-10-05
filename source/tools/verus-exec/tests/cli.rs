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
