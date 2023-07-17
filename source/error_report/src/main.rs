use chrono::{prelude::*, DateTime};
use std::time::{Duration, Instant};
use std::{
    env,
    fs::{self, File},
    io::prelude::*,
    io::{BufRead, BufReader},
    path::Path,
    process::{Command, Stdio},
    str,
};
use toml::{map::Map, value::Value};
use zip::write::FileOptions;

fn main() {
    if cfg!(windows) && !yansi::Paint::enable_windows_ascii() {
        yansi::Paint::disable();
    }
    match run() {
        Ok(()) => (),
        Err(err) => {
            eprintln!("{}", yansi::Paint::red(format!("error: {}", err)));
            std::process::exit(1);
        }
    }
}

fn run() -> Result<(), String> {
    let mut file_path: Option<String> = None;

    let mut our_args = Vec::new();

    let args: Vec<String> = env::args().collect();

    if args.len() > 1 {
        for argument in &args {
            if argument.ends_with(".rs") {
                if file_path.is_some() {
                    Err("multiple .rs files passed, unsupported by the --record flag")?;
                }
                file_path = Some(argument.clone());
            }
            if argument.starts_with("-o") || argument.starts_with("--out-dir") {
                Err("--record does not support `-o` or `--out-dir` flag")?;
            }
        }
        our_args = args[2..].to_vec();
    } else {
        eprintln!("Usage: verus INPUT --record <args..>");
        Err("no arguments provided")?;
    }

    let Some(file_path) = file_path else { return Err("no INPUT provided, Usage: verus INPUT --record [options]")?; };

    // add this error message because verus output is blocked
    // though normally user should make sure simple error like this does not happen
    // since they add record flag after they meet something wierd
    if !Path::new(&file_path).exists() {
        Err(format!("couldn't find crate root: {}", file_path))?;
    }

    // assumption: when verus is invoking error_report, the dir of verus path should be put in the first argument
    let program_dir = args[1].clone();

    let z3_path = if let Ok(z3_path) = env::var("VERUS_Z3_PATH") {
        Path::new(&z3_path).to_path_buf()
    } else {
        Path::new(&program_dir).join(if cfg!(windows) { "z3.exe" } else { "z3" })
    };

    let verus_path = Path::new(&program_dir).join("verus");

    let mut verus_call = our_args.clone();
    verus_call.insert(
        0,
        verus_path
            .file_name()
            .ok_or("Cannot get file name of verus path")?
            .to_string_lossy()
            .to_string(),
    );

    let z3_version_output =
        Command::new(z3_path.clone()).arg("--version").output().map_err(|x| {
            format!("failed to execute z3 with error message {}, path is at {:?}", x, z3_path)
        })?;

    // mandating --time and --output-json flag, we remove both flags here to prevent passing duplicates to verus
    if our_args.contains(&"--time".to_string()) || our_args.contains(&"--output-json".to_string()) {
        our_args.retain(|x| x != "--time" && x != "--output-json");
    }

    let temp_dep_file = Path::new(&file_path)
        .with_extension("d")
        .file_name()
        .unwrap()
        .to_string_lossy()
        .to_string();

    eprintln!(
        "{}",
        yansi::Paint::blue("Rerunning verus to create zip archive (verus outputs are blocked)")
    );
    let start_time = Instant::now();
    let verus_output = match Command::new(verus_path.clone())
        .stdin(Stdio::null())
        .args(our_args.clone())
        .arg("--emit=dep-info")
        .arg("--time")
        .arg("--output-json")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
    {
        Ok(output) => output,
        Err(err) => {
            // remove temp file if created
            fs::remove_file(&temp_dep_file).map_err(|x| {
                format!("failed to delete `.d` file with this error message: {}", x)
            })?;
            Err(format!(
                "failed to execute verus with error message {}, verus path is at {:?}, args are {:?}",
                err, verus_path, our_args
            ))?
        }
    };

    let verus_duration = start_time.elapsed();

    match toml_setup_and_write(verus_call, z3_version_output, verus_output, verus_duration) {
        Ok(()) => (),
        Err(err) => {
            // remove temp file if created
            fs::remove_file(&temp_dep_file).map_err(|x| {
                format!("failed to delete `.d` file with this error message: {}", x)
            })?;
            Err(err)?
        }
    }

    let zip_path = zip_setup(temp_dep_file.clone());

    fs::remove_file("error_report.toml")
        .map_err(|x| format!("failed to delete toml file with this error message: {}", x))?;
    // TODO: in some cases where the main.d file is not created, the following error will be reported, rather than the error of zip_zetup
    fs::remove_file(temp_dep_file.clone()).map_err(|x| format!("failed to delete dependencies file with this error message: {}, path to dependency file is {}", x, temp_dep_file))?;

    println!(
        "Collected dependencies and stored your reproducible crate to zip file: {}\n",
        zip_path?
    );

    Ok(())
}

fn toml_setup_and_write(
    args: Vec<String>,
    z3_version_output: std::process::Output,
    verus_output: std::process::Output,
    verus_duration: Duration,
) -> Result<(), String> {
    let z3_version =
        str::from_utf8(&z3_version_output.stdout).map_err(|x| format!("{}", x))?.to_string();

    let verus_time = verus_duration.as_secs_f64();

    let stdout_json =
        serde_json::from_str::<serde_json::Value>(&String::from_utf8_lossy(&verus_output.stdout))
            .map_err(|x| format!("Could not parse stdout as json with error message: {}", x))?;

    let version_info: toml::Value = serde_json::from_str(&stdout_json["verus"].to_string())
        .map_err(|x| {
            format!("failed to parse version info to toml file with error message {}", x)
        })?;

    let verification_result: toml::map::Map<String, Value> =
        serde_json::from_str(&stdout_json["verification-results"].to_string()).map_err(|x| {
            format!("failed to parse verification results with error message {}", x)
        })?;

    let stdout_toml_text = serde_json::from_str(&stdout_json.to_string())
        .map_err(|x| format!("failed to parse stdout (json) with error message {}", x))?;

    let stderr = String::from_utf8_lossy(&verus_output.stderr).to_string();

    let toml_string = toml::to_string(&create_toml(
        args,
        z3_version,
        version_info,
        verification_result,
        verus_time,
        stdout_toml_text,
        stderr,
    ))
    .map_err(|x| format!("Could not encode TOML value with error message: {}", x))?;

    fs::write("error_report.toml", toml_string)
        .map_err(|x| format!("Could not write to toml file with error message: {}", x))?;

    Ok(())
}

// Creates a toml file and writes relevant information to this file, including
// the command-line arguments, versions, rough time info, and verus output.
fn create_toml(
    args: Vec<String>,
    z3_version: String,
    verus_version: toml::Value,
    verification_result: toml::map::Map<String, Value>,
    verus_time: f64,
    stdout: toml::Value,
    stderr: String,
) -> Value {
    let mut command_line_arguments = Map::new();
    command_line_arguments.insert("args".to_string(), Value::String(args.join(" ")));

    let mut versions = Map::new();
    versions.insert("z3-version".to_string(), Value::String(z3_version));
    versions.insert("verus-version".to_string(), verus_version);

    let mut time = Map::new();
    time.insert("verus-time".to_string(), Value::Float(verus_time));

    let mut output = Map::new();
    output.insert("stdout".to_string(), stdout);
    output.insert("stderr".to_string(), Value::String(stderr));

    let mut map = Map::new();
    map.insert(
        "title".to_string(),
        Value::String("Error report file - details and dependencies".to_string()),
    );
    map.insert("report-schema-version".into(), Value::String("1".to_string()));
    map.insert("command-line-arguments".into(), Value::Table(command_line_arguments));
    map.insert("verus-time".into(), Value::Table(time));
    map.insert("versions".into(), Value::Table(versions));
    map.insert("verus-output".into(), Value::Table(output));
    map.insert("verification-results".into(), Value::Table(verification_result));
    Value::Table(map)
}

// grab all the files (dependencies + toml) to write the zip archive
pub fn zip_setup(dep_file_name: String) -> Result<String, String> {
    let dep_path = Path::new(&dep_file_name);
    if !dep_path.exists() {
        Err(format!(
            "file {} does not exist in zip_zetup, {}",
            dep_file_name,
            yansi::Paint::red("INTERNAL ERROR").bold()
        ))?;
    }

    let mut deps = get_dependencies(dep_path)?;
    deps.push("error_report.toml".to_string());

    let zip_file_name = write_zip_archive(deps)?;

    Ok(zip_file_name)
}

// parse the .d file and returns a vector of files names required to generate the crate
fn get_dependencies(dep_file_path: &std::path::Path) -> Result<Vec<String>, String> {
    // update to better error message
    let file = File::open(dep_file_path)
        .map_err(|x| format!("{}, dependency file name: {:?}", x, dep_file_path))?;
    let mut reader = BufReader::new(file);
    let mut dependencies = String::new();
    reader.read_line(&mut dependencies).map_err(|x| {
        format!("Could not read the first line of the dependency file with message: {}", x)
    })?;
    let result = dependencies.split_whitespace().skip(1).map(|x| x.to_string()).collect();
    Ok(result)
}

// Creates a zip file from a given list of files to compress
//
// Parameters: deps: A vector of strings representing files to be compressed
//                    (in this context, each file is a dependency of the input)
//
// Returns:    The name of the created zip file
fn write_zip_archive(deps: Vec<String>) -> Result<String, String> {
    let local: DateTime<Local> = Local::now();
    let formatted = local.format("%Y-%m-%d-%H-%M-%S");
    let date = formatted.to_string();
    let mut zip_file_name = date;

    zip_file_name.push_str(".zip");

    let path = std::path::Path::new(&zip_file_name);
    let file = std::fs::File::create(path).unwrap();
    let mut zip = zip::ZipWriter::new(file);
    let options = FileOptions::default();

    for file in deps {
        let path = file;
        eprintln!("{}", yansi::Paint::blue(format!("Adding file {} to zip archive", path)));
        let binding = fs::read_to_string(&path).map_err(|x| {
            format!("{}, file name: {}. Check if this file can be opened.", x, path)
        })?;

        let content = binding.as_bytes();

        zip.start_file(path, options).expect("Could not start zip file");
        zip.write_all(content).expect("Could not write file contents to zip");
    }
    zip.finish().expect("Could not finish up zip file");
    Ok(zip_file_name)
}
