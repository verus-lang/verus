use std::env;
use std::fs;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::Path;
use std::process::{Command, Stdio};
use std::str;
use toml::value::Value;
use toml::{map::Map};
use std::io::prelude::*;
use zip::write::FileOptions;
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

   let z3_path = exe_dir.join(REL_Z3_PATH);
    // exe_dir.push(REL_Z3_PATH);
    let verus_path = exe_dir.join(REL_VERUS_PATH);

    let z3_version_output =
        Command::new(z3_path).arg("--version").output().expect("failed to execute process");
    
    let verus_version_output = 
    Command::new(&verus_path).arg("--version").output().expect("failed to execute process");

    let msg: &str = file_path.trim();

    let child = Command::new(verus_path)
        .stdin(Stdio::null())
        .arg(msg)
        .arg("--emit=dep-info")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to execute process");

    let verus_output: std::process::Output =
        child.wait_with_output().expect("Failed to read stdout");

    println!("{}", String::from_utf8_lossy(&verus_output.stderr));
    println!("{}", String::from_utf8_lossy(&verus_output.stdout));

    toml_setup_and_write(args, z3_version_output, verus_version_output, verus_output);

    let d_file_name = zip_setup(file_path);

    clean_up(d_file_name);
}

/* Creates a toml file and writes relevant information to this file, including
 * the command-line arguments, versions, and output.
 * 
 * @params args: The command line arguments given to call the input file
 *         z3_version: Information regarding the user's current z3 version
 *         verus_version: Information regarding the user's current verus version
 *         stdout: The resulting output from the input file to stdout
 *         stderr: The resulting output from the input file to stderr
 * 
 * @returns A Table data structure used to write a toml file
 */
fn create_toml(args: Vec<String>, z3_version: String, verus_version: String, stdout: String, stderr: String) -> Value {
    
   let mut command_line_arguments = Map::new();
   command_line_arguments.insert("args".to_string(), Value::String(args.join(" ")));
   
   let mut versions = Map::new();
    versions.insert("z3-version".to_string(), Value::String(z3_version));
    versions.insert("verus-version".to_string(), Value::String(verus_version));

    let mut output = Map::new();
    output.insert("stdout".to_string(), Value::String(stdout));
    output.insert("stderr".to_string(), Value::String(stderr));

    let mut map = Map::new();
    map.insert(
        "title".to_string(),
        Value::String("Error report file - details and dependencies".to_string()),
    );
    map.insert("Command-Line-Arguments".into(), Value::Table(command_line_arguments));
    map.insert("Versions".into(), Value::Table(versions));
    map.insert("Verus-output".into(), Value::Table(output));

    Value::Table(map)
}

/* Transforms data from the input file into the proper data structure for
 * toml creation, and then calls a function to write the toml
 * 
 * @params args: The command line arguments given to call the input file
 *         z3_version_output: Information regarding the user's current z3 version
 *         verus_version_output: Information regarding the user's current verus version
 *         verus_output: The resulting output from the input file
 */
fn toml_setup_and_write(args: Vec<String>, z3_version_output: std::process::Output, 
    verus_version_output: std::process::Output, 
    verus_output: std::process::Output) {
    //let mut file = File::create("error_report.toml").expect("Unable to create file");

    let mut z3_version = String::new();
    z3_version.push_str(match str::from_utf8(&z3_version_output.stdout) {
        Ok(val) => val,
        Err(_) => panic!("got non UTF-8 data from git"),
    });

    let mut verus_version = String::new();
    verus_version.push_str(match str::from_utf8(&verus_version_output.stdout) {
        Ok(val) => val,
        Err(_) => panic!("got non UTF-8 data from git"),
    });

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

    let toml_string = toml::to_string(&create_toml(args, z3_version, verus_version, stdout, stderr))
        .expect("Could not encode TOML value");
    fs::write("error_report.toml", toml_string).expect("Could not write to file!");
}

/* Uses the user input file to find the .d file, parse the dependencies,
 * and write each dependency to the zip file.
 *
 * @param file_path: a String representation of the path to the input file
 * 
 * @returns the name of the .d file for book-keeping purposes
 */
pub fn zip_setup(file_path: String) -> String {

    let file_name_path = Path::new(&file_path);

    let temp_file_name = &file_name_path.file_name().unwrap().to_string_lossy();
    let mut d_file_name = String::new();
    d_file_name.push_str(&temp_file_name.to_string()[..]);
    d_file_name = d_file_name[..d_file_name.len() - 2].to_string();
    d_file_name.push('d');

    let mut deps = d_to_vec(d_file_name.to_string());
    deps.push("error_report.toml".to_string());

    write_zip_archive(deps);

    d_file_name
}

/* Turns the .d file that lists each of the input files' dependencies
 * and turns them into a vector of Strings for easier data manipulation
 * 
 * @param file_name: The name of the previously generated .d file
 * 
 * @returns: a vector containing each dependency of the input file
 *      as an individual string
 */
fn d_to_vec(file_name: String) -> Vec<String> {
    let file = File::open(file_name).expect("Couldn't open file!");
    let mut reader = BufReader::new(file);
    let mut dependencies = String::new();
    reader.read_line(&mut dependencies).expect("Could not read the first line");

    let mut deps = Vec::new();
    let mut ctr = 0;
    for dep in dependencies.split_whitespace() {
        if ctr >0
        {
            deps.push(dep.to_string());
        }
        ctr+= 1;
    }
    deps
}

/* Deletes the generated toml file and .d file so as to not clutter the user's directory
 *
 * @param d_file_name: The name of the .d file that was created by this process
        and needs to be deleted.
 */
fn clean_up(d_file_name: String) {
    fs::remove_file("error_report.toml").expect("failed to delete toml file\n");
    fs::remove_file(d_file_name).expect("failed to delete .d file\n");
}

/* Creates a zip file from a given list of files to compress
 *
 * @params deps: A vector of strings representing files to be compressed 
 *               (in this context, each file is a dependency of the input)
 */
fn write_zip_archive(deps: Vec<String>)
{
    let path = std::path::Path::new("error-report.zip");
    let file = std::fs::File::create(path).unwrap();
    //let deps = vec!["folder/a.rs", "src/b.rs", "src/c.rs", "src/main.rs"];
    let mut zip = zip::ZipWriter::new(file);

    let options = FileOptions::default()
        .compression_method(zip::CompressionMethod::Stored)
        .unix_permissions(0o755);

    for file in deps
    {
        let path = file;
        let binding = read_file_string(&path).expect("Could not read file");
        let content = binding.as_bytes();
        
        zip.start_file(path, options).expect("Could not start file");
        zip.write_all(content).expect("Could not write file contents to zip");
    }

    zip.finish().expect("Could not finish up zip file");
}

/* Turns a file path into a string
 */
fn read_file_string(filepath: &str) -> Result<String, Box<dyn std::error::Error>> {
    let data = fs::read_to_string(filepath)?;
    Ok(data)
}