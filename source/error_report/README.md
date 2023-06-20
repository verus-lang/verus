# Error Reporting

## Overview

Warning: This is an experimental prototype.

Error Reporting: Verus is still under development, so when you get into an error
it can be quite frustrating to manually record the versions of your z3, verus,
etc. This tool attempts to record this data automatically.

## Usage
 Run `cargo build --release`, which should generate the `error_report` executable in 
 `./target/release/`. Then you can run error_report on any directory that you
 run `verus`, or use the `--error-report` flag in verus. This generates a
 zip file that contains both the necessary files to replicate the error  
 and an `error_report.toml` file tracking other useful information,
 such as version info, and output from Verus.