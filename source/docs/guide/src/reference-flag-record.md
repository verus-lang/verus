# Record flag

Sometimes, you might wish to record an execution trace of Verus to share, along with all the necessary dependencies to reproduce an execution.
This might be useful for either packaging up your verified project, or to report a Verus bug to the [issue tracker](https://github.com/verus-lang/verus/issues).

The `--record` flag will do precisely this.  In particular, to record an execution of Verus (say, `verus foo --bar --baz`), simply add the `--record` flag (for example, `verus foo --bar --baz --record`).  This will re-run Verus, and package all the relevant source files, along with the execution output and version information into a zip file (`yyyy-mm-dd-hh-mm-ss.zip`) in your current directory.
