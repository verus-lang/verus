## Usage

Warning: this is a super prototype that only restricts on Unix platforms.

Run `cargo build`, which should generate the `error_report` executable in 
`./target/debug/`. Then you can run error_report on any directory that you
run `verus`. This should generate an `errorReport.zip` that contains the
necessary files to replicate the error, and an `error_report.toml` file that has 
the error message and version info.

## Attempt for Error Reporting

(mostly me playing around with rust)

Goal:

Error Reporting: Verus is still under development, so when you get into an error
it can be quite frustrating to manually record the versions of your z3, rustc, rustup, 
etc. This tool attempts to record this data automatically.

Implementation plan:
1. pack everything into a metadata file (toml)
