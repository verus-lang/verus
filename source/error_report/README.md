# Error Reporting

## Overview

Warning: This is an experimental prototype.

Error Reporting: Verus is still under development, so when you get into an error
it can be quite frustrating to manually record the versions of your z3, verus,
etc. This tool attempts to record this data automatically.

## Usage
 add `--error-report` flag to whatever file you call `verus` on.
 This will generates a
 zip file (`YYYY-MM-DD-HH-MM-SS.zip`) that contains both the necessary files to replicate the error  
 and an `error_report.toml` file tracking other useful information,
 such as version info, and output from Verus.