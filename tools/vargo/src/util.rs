// Some of the code in this file is copied from https://github.com/rust-lang/cargo/blob/cee088b0db01076deb11c037fe8b64b238b005a2/src/cargo/util/paths.rs#L183-L217
// Cargo is primarily distributed under the terms of both the MIT license and the Apache License (Version 2.0).
// See https://github.com/rust-lang/cargo/blob/cee088b0db01076deb11c037fe8b64b238b005a2/LICENSE-APACHE
// and https://github.com/rust-lang/cargo/blob/cee088b0db01076deb11c037fe8b64b238b005a2/LICENSE-MIT
// for details.

// MIT License text:
// Permission is hereby granted, free of charge, to any
// person obtaining a copy of this software and associated
// documentation files (the "Software"), to deal in the
// Software without restriction, including without
// limitation the rights to use, copy, modify, merge,
// publish, distribute, sublicense, and/or sell copies of
// the Software, and to permit persons to whom the Software
// is furnished to do so, subject to the following
// conditions:
//
// The above copyright notice and this permission notice
// shall be included in all copies or substantial portions
// of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF
// ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED
// TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
// PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT
// SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
// CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
// OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR
// IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
// DEALINGS IN THE SOFTWARE.

use filetime::FileTime;
use std::fs;
use std::path::Path;

pub fn mtime_recursive(path: &Path) -> Result<FileTime, String> {
    let meta = fs::metadata(path).map_err(|_| format!("failed to stat `{}`", path.display()))?;
    if !meta.is_dir() {
        return Ok(FileTime::from_last_modification_time(&meta));
    }
    let max_meta = walkdir::WalkDir::new(path)
        .follow_links(true)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter_map(|e| {
            if e.path_is_symlink() {
                // Use the mtime of both the symlink and its target, to
                // handle the case where the symlink is modified to a
                // different target.
                let sym_meta = std::fs::symlink_metadata(e.path()).ok()?;
                let sym_mtime = FileTime::from_last_modification_time(&sym_meta);
                // Walkdir follows symlinks.
                match e.metadata() {
                    Ok(target_meta) => {
                        let target_mtime = FileTime::from_last_modification_time(&target_meta);
                        Some(sym_mtime.max(target_mtime))
                    }
                    Err(_) => Some(sym_mtime),
                }
            } else {
                let meta = e.metadata().ok()?;
                Some(FileTime::from_last_modification_time(&meta))
            }
        })
        .max()
        .unwrap_or_else(|| FileTime::from_last_modification_time(&meta));
    Ok(max_meta)
}

// ============================================================================

pub struct VersionInfo {
    pub version: String,
    pub sha: String,
}

pub fn version_info(root: &std::path::PathBuf) -> Result<VersionInfo, String> {
    fn io_err_to_string(err: std::io::Error) -> String {
        format!("cannot obtain version info from git ({})", err)
    }

    // assumes the verus executable gets the .git file for verus repo
    fn rev_parse(root: &std::path::PathBuf, short: bool) -> Result<String, String> {
        let mut rev_parse_cmd = std::process::Command::new("git");
        rev_parse_cmd.current_dir(root).args(&["rev-parse"]);
        if short {
            rev_parse_cmd.args(&["--short=7"]);
        }
        rev_parse_cmd.args(&["HEAD"]);
        let rev_parse_output = rev_parse_cmd
            .stdout(std::process::Stdio::piped())
            .spawn()
            .map_err(io_err_to_string)?
            .wait_with_output()
            .map_err(io_err_to_string)?;
        rev_parse_output
            .status
            .success()
            .then(|| ())
            .ok_or(format!("git returned error code"))?;
        let sha = String::from_utf8(rev_parse_output.stdout)
            .map_err(|x| format!("commit sha is invalid utf8, {}", x))?;
        Ok(sha.trim().to_owned())
    }
    let sha_short = rev_parse(&root, true)?;
    let sha_full = rev_parse(&root, false)?;

    let date_info_output = std::process::Command::new("git")
        .current_dir(&root)
        .args(&["show", "-s", "--format=%cs", "HEAD"])
        .stdout(std::process::Stdio::piped())
        .spawn()
        .map_err(io_err_to_string)?
        .wait_with_output()
        .map_err(io_err_to_string)?;

    date_info_output
        .status
        .success()
        .then(|| ())
        .ok_or(format!("git returned error code"))?;
    let date_str = String::from_utf8(date_info_output.stdout)
        .map_err(|x| format!("commit date is invalid utf8, {}", x))?;
    let date_re = regex::Regex::new(r"^(\d{4})-(\d{2})-(\d{2})$").unwrap();
    let date_captures = date_re
        .captures(date_str.trim())
        .ok_or(format!("unexpected date string \"{}\"", date_str))?;
    let year = &date_captures[1];
    let month = &date_captures[2];
    let day = &date_captures[3];

    let dirty_output = std::process::Command::new("git")
        .current_dir(&root)
        .args(&["diff", "--exit-code", "HEAD"])
        .stdout(std::process::Stdio::null())
        .spawn()
        .map_err(io_err_to_string)?
        .wait_with_output()
        .map_err(io_err_to_string)?;

    let dirty = if dirty_output.status.success() {
        ""
    } else {
        ".dirty"
    };
    Ok(VersionInfo {
        version: format!("0.{year}.{month}.{day}.{sha_short}{dirty}"),
        sha: sha_full,
    })
}

// ============================================================================

pub fn vargo_file_contents(vargo_dir: &std::path::Path) -> Vec<(String, Box<[u8]>)> {
    use std::io::Read;

    fn add_file(files: &mut Vec<(String, Box<[u8]>)>, path: &Path, relative: &Path) {
        let mut file = std::fs::File::open(path.join(relative))
            .expect(&format!("cannot read file {}", relative.display()));
        let mut buffer = Vec::new();
        file.read_to_end(&mut buffer)
            .expect(&format!("cannot read file {}", relative.display()));
        let path_str = relative
            .components()
            .map(|x| x.as_os_str().to_str().unwrap().to_owned())
            .collect::<Vec<_>>()
            .join("/");
        files.push((path_str, buffer.into_boxed_slice()));
    }

    fn add_dir(files: &mut Vec<(String, Box<[u8]>)>, path: &Path, relative: &Path) {
        for entry in fs::read_dir(path.join(relative))
            .expect(&format!("cannot read dir {}", relative.display()))
        {
            let entry = entry.unwrap();
            if entry.file_type().unwrap().is_dir() {
                add_dir(files, path, &relative.join(entry.file_name()));
            } else if entry.path().extension() == Some(std::ffi::OsStr::new("rs")) {
                add_file(files, path, &relative.join(entry.file_name()));
            }
        }
    }

    let mut entries = Vec::new();
    add_dir(&mut entries, &vargo_dir, Path::new("src"));
    entries
}

pub fn hash_file_contents<'a>(mut files: Vec<(&'a str, &'a [u8])>) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    files.sort_by_key(|&(n, _)| n);
    for (n, b) in files {
        n.hash(&mut hasher);
        b.hash(&mut hasher);
    }
    hasher.finish()
}
