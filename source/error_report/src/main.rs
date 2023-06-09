use std::env;
use std::fs::File;
use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::path::Path;
use std::process::{Command, Stdio};
use toml::{map::Map, Value};
use std::str;
// use toml::ser;
// use toml::Value;
 // 0.5.1

// TODO
// use toml::{map::Map, Value};
// https://stackoverflow.com/questions/38405620/how-to-create-a-toml-file-from-rust
// probably only 2/3 fields are necessary, leave for later

// TODO: report the verus version by `git rev-parse HEAD`
// add a --version flag, which replicates F* behavior

// F* version
// > fstar.exe
// F* 0.9.7.9-alpha1
// platform=Linux_x86_64          (use uname)
// compiler=OCaml ...             (jsut use git hash)
// git-hash=""

// LATER: if someone is having an error, you may want to pass a message
//        to the developer

// LATER: deal with flags of a verus command
//

// TODO: needs to be updated when there's a released binary of error_report
const REL_Z3_PATH: &str = "../../../target-verus/release/z3";
const REL_VERUS_PATH: &str = "../../../target-verus/release/verus";

fn main() {
    // path where this piece of code is (then you can talk abt the rel path to z3/verus)
    let mut exe_dir = env::current_exe().expect("invalid directory");
    exe_dir.pop();

    let mut file_path = String::new();
    let args: Vec<String> = env::args().collect();
    if args.len() > 1 {
        file_path = args[1].clone();
    } else {
        println!("Usage: error_report <file_name>");
    }

    println!();

    let z3_path = exe_dir.join(REL_Z3_PATH);
    // exe_dir.push(REL_Z3_PATH);

    let z3_version_output = Command::new(z3_path).arg("--version").output().expect("failed to execute process");

    let msg: &str = file_path.trim();

    let verus_path = exe_dir.join(REL_VERUS_PATH);
    let child = Command::new(verus_path)
        .stdin(Stdio::null())
        .arg(msg)
        .arg("--emit=dep-info")
        // .arg("--color=always") // this preserves color when piped
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to execute process");

    let verus_output: std::process::Output = child.wait_with_output().expect("Failed to read stdout");

    // no color information now (because we are writing in the file)
    println!("{}", String::from_utf8_lossy(&verus_output.stderr));
    println!("{}", String::from_utf8_lossy(&verus_output.stdout));

    // TODO: see above
    // probably change to file name?
    write_toml(z3_version_output, verus_output);

    let d_file_name = create_zip(file_path);

    clean_up(d_file_name);
}

fn create_toml(z3_version: String, verus_version: String, stdout: String, stderr: String) -> Value {

    let mut versions = Map::new();
    versions.insert("z3-version".to_string(), Value::String(z3_version));
    versions.insert("verus-version".to_string(), Value::String(verus_version));

    
    let mut output = Map::new();
    output.insert("stdout".to_string(), Value::String(stdout));
    output.insert("stderr".to_string(),Value::String(stderr));

    let mut map = Map::new();
    map.insert("title".to_string(), Value::String("Error report file - details and dependencies".to_string()));
    map.insert("Versions".into(), Value::Table(versions));
    map.insert("Verus-output".into(), Value::Table(output));

    Value::Table(map)
}

fn write_toml(z3_version_output: std::process::Output, verus_output: std::process::Output)
{
    let mut file = File::create("error_report.toml").expect("Unable to create file");
    
    let mut z3_version = String::new();
    z3_version.push_str(match str::from_utf8(&z3_version_output.stdout) {
        Ok(val) => val,
        Err(_) => panic!("got non UTF-8 data from git"),
    });

    let mut verus_version = "TODO".to_string();

    let mut stdout = String::new();
    stdout.push_str(match str::from_utf8(&verus_output.stdout) {
        Ok(val) => val,
        Err(_) => panic!("got non UTF-8 data from git"),
    });
    
    let mut stderr = String::new();
    stderr.push_str(match str::from_utf8(&verus_output.stderr) {
        Ok(val) => val,
        Err(_) => panic!("got non UTF-8 data from git"),
    });

    let toml_string = toml::to_string(&create_toml(z3_version, verus_version, stdout, stderr)).expect("Could not encode TOML value");
    fs::write("error_report.toml", toml_string).expect("Could not write to file!");

}

pub fn create_zip(file_path: String) -> String
{
    // LATER
    // zip might need to be a higher level rust implementation that is platform independent
    // maybe this library? https://crates.io/crates/zip

    // file path  blabla/bar.rs -> blabla/bar.d
    // let cur_dir = env::current_dir().expect("invalid directory");

    let file_name_path = Path::new(&file_path);

    // dep_file_path.truncate(dep_file_path.len() - 3);
      // v "main.rs"
    let temp_file_name = &file_name_path.file_name().unwrap().to_string_lossy();
    let mut d_file_name = String::new();
    d_file_name.push_str(&temp_file_name.to_string()[..]);
    d_file_name = d_file_name[..d_file_name.len()-2].to_string();
    d_file_name.push_str("d");

    println!("{}", d_file_name);
    let mut deps = d_to_vec(d_file_name.to_string());
    deps.push("error_report.toml".to_string());

    // LATER: might append current directory to the deps
    // this might only happens when their are related files in parent directories
    // accessed by the #[path = ""] attribute
    // let path = env::current_dir().expect("invalid directory");

    Command::new("zip")
                .arg("errorReport.zip")
                .args(deps)
                .output()
                .expect("failed to execute process");

    d_file_name
}

fn d_to_vec(file_name: String) -> Vec<String> {
    let file = File::open(file_name).expect("Couldn't open file!");
    let mut reader = BufReader::new(file);
    let mut dependencies = String::new();
    reader.read_line(&mut dependencies).expect("Could not read the first line");

    let mut deps = Vec::new();
    for dep in dependencies.split_whitespace() {
        if dep.ends_with(".d") {
            continue;
        }
        deps.push(dep.to_string());
    }
    deps
}

fn clean_up(d_file_name: String) {
    fs::remove_file("error_report.toml").expect("failed to delete toml file\n");
    fs::remove_file(d_file_name).expect("failed to delete .d file\n");
}
