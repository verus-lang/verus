# Record flag

Verus is still under development, so when you get into an error
it can be quite frustrating to manually record the versions of your z3 and verus to reproduce the error. This tool attempts to record this data automatically.

The `--record` flag will rerun verus and package source files of the current crate to the current directory, alongside with output and version information. The file will be named YYYY-MM-DD-HH-MM-SS.zip. If you are reporting an error, please keep the original arguments in addition to this flag 

