// The code in this file is copied from https://github.com/rust-lang/cargo/blob/cee088b0db01076deb11c037fe8b64b238b005a2/src/cargo/util/paths.rs#L183-L217
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

pub fn store_commit_info() {
    // assumes the verus executable gets the .git file for verus repo
    let mut exe_dir = std::env::current_exe().expect("invalid directory");
    exe_dir.pop();

    let sha = std::process::Command::new("git")
        .current_dir(&exe_dir)
        .args(&["rev-parse", "--short", "HEAD"])
        .stdout(std::process::Stdio::piped())
        .spawn()
        .expect("failed to execute git rev-parse HEAD");

    let mut sha_msg = sha
        .wait_with_output()
        .expect("failed to execute git rev-parse HEAD")
        .stdout;
    sha_msg.pop();

    let date_info = std::process::Command::new("git")
        .current_dir(&exe_dir)
        .args(&["show", "-s", "--format=%ci", "HEAD"])
        .stdout(std::process::Stdio::piped())
        .spawn()
        .expect("failed to execute git show -s --format=%ci HEAD");

    let date_msg = date_info
        .wait_with_output()
        .expect("failed to execute git show -s --format=%ci HEAD")
        .stdout;

    let year = String::from_utf8(date_msg[0..4].to_vec()).unwrap();
    let month = String::from_utf8(date_msg[5..7].to_vec()).unwrap();
    let day = String::from_utf8(date_msg[8..10].to_vec()).unwrap();

    let child = std::process::Command::new("git")
        .current_dir(&exe_dir)
        .args(&["diff", "--exit-code", "HEAD"])
        .stdout(std::process::Stdio::null())
        .spawn()
        .expect("failed to execute git diff --exit-code HEAD");

    let status = child
        .wait_with_output()
        .expect("failed to execute git diff --exit-code HEAD")
        .status;

    if status.success() {
        let msg = format!("0.{}.{}.{}-{}", year, month, day, String::from_utf8(sha_msg).unwrap());
        std::env::set_var("VERUS_BUILD_VERSION", msg);
    } else {
        let msg = format!("0.{}.{}.{}-{} (dirty)", year, month, day, String::from_utf8(sha_msg).unwrap());
        std::env::set_var("VERUS_BUILD_VERSION", msg);
    }
}
