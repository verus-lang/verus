use chrono::{prelude::*, DateTime};
use regex::Regex;
use std::path::PathBuf;
use std::time::Duration;
use std::{
    fs::{self, File},
    io::prelude::*,
    io::{BufRead, BufReader},
    process::Command,
    str,
};
use toml::{map::Map, value::Value};
use zip::write::FileOptions;

pub fn get_z3_version(z3_path: &PathBuf) -> Option<std::process::Output> {
    match Command::new(z3_path.clone()).arg("--version").output() {
        Ok(output) => Some(output),
        Err(err) => {
            eprintln!(
                "{}: failed to execute z3 with error message {}, path is at {:?}",
                yansi::Paint::yellow("warning"),
                err,
                z3_path
            );
            None
        }
    }
}

pub fn find_source_file(args: &Vec<String>) -> Result<PathBuf, String> {
    let mut source_file: Option<String> = None;
    for argument in args.iter() {
        if argument.ends_with(".rs") {
            if source_file.is_some() {
                return Err("multiple .rs files passed, unsupported by the --record flag".into());
            }
            source_file = Some(argument.clone());
        }
        if argument.starts_with("-o") || argument.starts_with("--out-dir") {
            return Err("--record does not support `-o` or `--out-dir` flag".into());
        }
    }
    match source_file {
        Some(source_file) => Ok(PathBuf::from(source_file)),
        None => return Err("no .rs files passed, unsupported by the --record flag".into()),
    }
}

pub fn temp_dep_file_from_source_file(file: &PathBuf) -> Result<std::ffi::OsString, String> {
    let dep_file = file.with_extension("d");
    let Some(dep_file) = dep_file.file_name() else {
        return Err("invalid input file name for --record".into());
    };
    Ok(dep_file.to_owned())
}

pub fn error_report_toml_value(
    args: Vec<String>,
    z3_version_output: Option<std::process::Output>,
    verus_stdout: Vec<u8>,
    verus_stderr: Vec<u8>,
    verus_duration: Duration,
    exit_status: Option<i32>,
) -> Result<toml::Value, String> {
    let z3_version: Option<toml::Value> = if let Some(z3_version_output) = z3_version_output {
        let mut z3_version = Map::new();
        let stdout_str = str::from_utf8(&z3_version_output.stdout)
            .map_err(|x| format!("z3 version output is not valid utf8 ({})", x))?
            .to_string();
        let z3_version_re = Regex::new(r"Z3 version (\d+\.\d+\.\d+) - \d+ bit")
            .expect("failed to compile z3 version regex");
        if let Some(captures) = z3_version_re.captures(&stdout_str) {
            z3_version.insert("version".into(), Value::String(captures[1].into()));
        } else {
            eprintln!("{}: failed to parse z3 version stdout", yansi::Paint::yellow("warning"),);
        }
        z3_version.insert("stdout".into(), Value::String(stdout_str));
        Some(Value::Table(z3_version))
    } else {
        None
    };

    let verus_time = verus_duration.as_secs_f64();

    let stdout_string = String::from_utf8_lossy(&verus_stdout).to_string();

    let stdout_json: Option<serde_json::Value> =
        match serde_json::from_str::<serde_json::Value>(&stdout_string) {
            Ok(json) => Some(json),
            Err(err) => {
                eprintln!(
                    "{}: failed to parse stdout to json with error message:\n {}",
                    yansi::Paint::yellow("warning"),
                    err
                );
                None
            }
        };

    let version_info: Option<toml::Value> = stdout_json.as_ref().and_then(|stdout_json| {
        match serde_json::from_value(stdout_json["verus"].clone()) {
            Ok(json) => Some(json),
            Err(err) => {
                eprintln!(
                    "{}: failed to parse version info to toml with error message:\n {}",
                    yansi::Paint::yellow("warning"),
                    err
                );
                None
            }
        }
    });

    let verification_result: Option<toml::Value> = stdout_json.as_ref().and_then(|stdout_json| {
        match serde_json::from_value(stdout_json["verification-results"].clone()) {
            Ok(json) => Some(json),
            Err(err) => {
                eprintln!(
                    "{}: failed to parse verification results to toml with error message:\n {}",
                    yansi::Paint::yellow("warning"),
                    err
                );
                None
            }
        }
    });

    let stdout_toml = stdout_json.and_then(|stdout_json| {
        match serde_json::from_value::<toml::Value>(stdout_json) {
            Ok(json) => Some(json),
            Err(err) => {
                eprintln!(
                    "{}: failed to convert stdout to toml with error message:\n {}",
                    yansi::Paint::yellow("warning"),
                    err
                );
                None
            }
        }
    });

    let stderr = String::from_utf8_lossy(&verus_stderr).to_string();

    Ok(create_toml(
        args,
        z3_version,
        version_info,
        exit_status,
        verification_result,
        verus_time,
        stdout_toml,
        stderr,
    ))
}

// Creates a toml file and writes relevant information to this file, including
// the command-line arguments, versions, rough time info, and verus output.
fn create_toml(
    mut args: Vec<String>,
    z3_version: Option<toml::Value>,
    verus_version: Option<toml::Value>,
    exit_status: Option<i32>,
    verification_results: Option<toml::Value>,
    verus_time: f64,
    stdout: Option<toml::Value>,
    stderr: String,
) -> Value {
    args.insert(0, "verus".into());
    let mut command_line_arguments = Map::new();
    command_line_arguments.insert("args".to_string(), Value::String(args.join(" ")));

    let mut versions = Map::new();
    if let Some(z3_version) = z3_version {
        versions.insert("z3".to_string(), z3_version);
    }
    if let Some(verus_version) = verus_version {
        versions.insert("verus".to_string(), verus_version);
    }

    let mut time = Map::new();
    time.insert("verus-time".to_string(), Value::Float(verus_time));

    let mut output = Map::new();
    if let Some(exit_status) = exit_status {
        output.insert("exit-code".to_owned(), Value::Integer(exit_status as i64));
    }
    if let Some(stdout) = stdout {
        output.insert("stdout".to_string(), stdout);
    }
    output.insert("stderr".to_string(), Value::String(stderr));

    let mut map = Map::new();
    map.insert(
        "title".to_string(),
        Value::String("Error report file - details and dependencies".to_string()),
    );
    map.insert("report-schema-version".into(), Value::String("1.1".to_string()));
    map.insert("command-line-arguments".into(), Value::Table(command_line_arguments));
    map.insert("verus-time".into(), Value::Table(time));
    map.insert("versions".into(), Value::Table(versions));
    map.insert("verus-output".into(), Value::Table(output));
    if let Some(verification_results) = verification_results {
        map.insert("verification-results".into(), verification_results);
    }
    Value::Table(map)
}

// parse the .d file and returns a vector of files names required to generate the crate
pub fn get_dependencies(
    dep_file_name: &std::ffi::OsString,
) -> Result<(PathBuf, Vec<PathBuf>), String> {
    let dep_file_path = PathBuf::from(dep_file_name);
    if !dep_file_path.exists() {
        Err(format!(
            "internal error: file {} does not exist in zip_setup",
            dep_file_name.to_string_lossy(),
        ))?;
    }

    let file = File::open(&dep_file_path)
        .map_err(|x| format!("{}, dependency file name: {:?}", x, dep_file_path))?;
    let mut reader = BufReader::new(file);
    let mut dependencies = String::new();
    reader.read_line(&mut dependencies).map_err(|x| {
        format!("Could not read the first line of the dependency file with message: {}", x)
    })?;
    let result: Vec<_> =
        dependencies.split_whitespace().skip(1).map(|x| PathBuf::from(x)).collect();
    assert!(result.len() > 0);
    let mut path_iters: Vec<_> =
        result.iter().map(|x| x.iter().take(x.iter().count() - 1)).collect();
    let mut chomp_components = 0;
    loop {
        let common = path_iters
            .iter_mut()
            .map(|x| x.next())
            .reduce(|acc, x| acc.and_then(|a| if Some(a) == x { Some(a) } else { None }))
            .flatten();
        if common.is_some() {
            chomp_components += 1;
        } else {
            break;
        }
    }
    let result_chomped: Vec<PathBuf> =
        result.iter().map(|p| PathBuf::from_iter(p.components().skip(chomp_components))).collect();
    let chomped = PathBuf::from_iter(result[0].iter().take(chomp_components));

    Ok((chomped, result_chomped))
}

// Creates a zip file from a given list of files to compress
//
// Parameters: deps: A vector of strings representing files to be compressed
//                    (in this context, each file is a dependency of the input)
//
// Returns:    The name of the created zip file
pub fn write_zip_archive(
    prefix: PathBuf,
    deps: Vec<PathBuf>,
    error_report_contents: String,
) -> Result<String, String> {
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
        eprintln!(
            "{}",
            yansi::Paint::blue(format!("Adding file {} to zip archive", path.display()))
        );
        let binding = fs::read_to_string(&prefix.join(&path)).map_err(|x| {
            format!("{}, file name: {}. Check if this file can be opened.", x, path.display())
        })?;

        let content = binding.as_bytes();

        zip.start_file(path.as_os_str().to_string_lossy(), options)
            .expect("Could not start zip file");
        zip.write_all(content).expect("Could not write file contents to zip");
    }
    zip.start_file("error_report.toml", options).expect("Could not start zip file");
    zip.write_all(error_report_contents.as_bytes()).expect("Could not write toml contents to zip");
    zip.finish().expect("Could not finish up zip file");
    Ok(zip_file_name)
}
