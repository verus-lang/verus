use rust_verify_test_macros::examples_in_dir;
use std::path::Path;
use std::process::Command;

#[cfg(target_os = "macos")]
const DYN_LIB_VAR: &str = "DYLD_LIBRARY_PATH";

#[cfg(target_os = "linux")]
const DYN_LIB_VAR: &str = "LD_LIBRARY_PATH";

#[cfg(target_os = "macos")]
const DYN_LIB_EXT: &str = "dylib";

#[cfg(target_os = "linux")]
const DYN_LIB_EXT: &str = "so";

#[cfg(all(target_os = "macos", target_arch = "x86_64"))]
const RUST_LIB_TARGET: &str = "x86_64-apple-darwin";

#[cfg(all(target_os = "macos", target_arch = "aarch64"))]
const RUST_LIB_TARGET: &str = "aarch64-apple-darwin";

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
const RUST_LIB_TARGET: &str = "x86_64-unknown-linux-gnu";

#[cfg(all(target_os = "linux", target_arch = "aarch64"))]
const RUST_LIB_TARGET: &str = "aarch64-unknown-linux-gnu";

#[derive(Debug)]
enum Mode {
    ExpectSuccess,
    ExpectErrors,
    ExpectFailures,
}

examples_in_dir!("example");
examples_in_dir!("example/guide");
examples_in_dir!("example/state_machines");
examples_in_dir!("example/summer_school");
examples_in_dir!("example/state_machines/tutorial");

fn run_example_for_file(file_path: &str) {
    let relative_path = Path::new(file_path);

    let mut path = std::path::PathBuf::from("rust_verify");
    path.extend(relative_path);
    let path = path.to_str().expect("invalid example path");

    let mut reader =
        std::io::BufReader::new(std::fs::File::open(relative_path).expect("cannot open file"));
    let mut first_line = String::new();
    let first_line_elements: Vec<_> = {
        use std::io::BufRead;
        reader.read_line(&mut first_line).expect("unable to read first line");
        first_line.split(" ").collect()
    };

    let mut mode = Mode::ExpectSuccess;

    if let ["//", "rust_verify/tests/example.rs", command] = &first_line_elements[..] {
        match command.strip_suffix("\n").unwrap_or("unexpected") {
            "expect-success" => mode = Mode::ExpectSuccess,
            "expect-errors" => mode = Mode::ExpectErrors,
            "expect-failures" => mode = Mode::ExpectFailures,
            "ignore" => {
                return;
            }
            _ => panic!(
                "invalid command for example file test: use one of 'expect-success', 'expect-errors', 'expect-failures' or 'ignore'"
            ),
        }
    }

    #[cfg(target_os = "windows")]
    let script = format!(
        "..\\rust\\install\\bin\\rust_verify --pervasive-path pervasive --extern builtin=../rust/install/bin/libbuiltin.rlib --extern builtin_macros=../rust/install/bin/builtin_macros.dll --extern state_machines_macros=../rust/install/bin/state_machines_macros.dll --edition=2018 {}",
        &path
    );

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    let script = format!(
        "{}=../rust/install/lib/rustlib/{}/lib:../rust/install/lib ../rust/install/bin/rust_verify --pervasive-path pervasive --extern builtin=../rust/install/bin/libbuiltin.rlib --extern builtin_macros=../rust/install/bin/libbuiltin_macros.{} --extern state_machines_macros=../rust/install/bin/libstate_machines_macros.{} --edition=2018 {}",
        DYN_LIB_VAR, RUST_LIB_TARGET, DYN_LIB_EXT, DYN_LIB_EXT, &path
    );

    let output = if cfg!(target_os = "windows") {
        Command::new("cmd")
            .current_dir("..")
            .args(&["/C", &script])
            .output()
            .expect("failed to execute process")
    } else {
        Command::new("sh")
            .current_dir("..")
            .arg("-c")
            .arg(script)
            .output()
            .expect("failed to execute process")
    };

    use regex::Regex;
    let re = Regex::new(r"verification results:: verified: (\d+) errors: (\d+)").unwrap();
    let stdout = std::str::from_utf8(&output.stdout).expect("invalid stdout encoding");
    let verifier_output: Option<(u64, u64)> = re.captures_iter(stdout).next().map(|x| {
        (
            x[1].parse().expect("invalid verifier output"),
            x[2].parse().expect("invalid verifier output"),
        )
    });

    let success = match mode {
        Mode::ExpectSuccess => {
            output.status.success()
                && match verifier_output {
                    Some((_, 0)) => true,
                    _ => false,
                }
        }
        Mode::ExpectErrors => !output.status.success(),
        Mode::ExpectFailures => {
            !output.status.success()
                && match verifier_output {
                    Some((_, failures)) if failures > 0 => true,
                    _ => false,
                }
        }
    };

    if !success {
        eprintln!("- example {} - mode: {:?} - failed -", &path, mode);
        eprintln!(
            "- stderr -\n{}\n",
            std::str::from_utf8(&output.stderr).expect("invalid stderr encoding")
        );
        eprintln!("- stdout -\n{}\n", stdout);
        assert!(false);
    }
}
