## Usage

Warning: this is a super prototype that only restricts on Unix platforms

run `cargo build`, which should generate the `error_report` executable in 
`./target/debug/`. Then you can run error_report on any directory that you
run `verus`. This should generate a `errorReport.zip` that contains the
necessary files to replicate the error, and a `output.toml` file that have 
error message and version info.

## Attempt for Error Reporting

(mostly me playing around with rust)

Goal:

Error Reporting: Verus is still under development, when you get into an error
it is frustrating to manually record the versions of your z3, rustc, rustup, 
etc. This tool attempts to record these data automatically.

Implementation plan:
1. pack everything into a metadata file (toml)
