NOTE: Veritas is highly experimental at this stage. It should already be useful,
but it is likely to break when encountering unexpected situations.

Veritas is a rust crater-alike tool to run a version of verus on a number of projects,
generating a report of verification success/failures and verification performance data.

Running veritas requires docker (or another container runtime). 
You can start a run with `bash run.sh path_to_run_configuration.toml`.
There is an example run configuration in this directory.
Running that command will start an ephemeral container and will create four
permanent docker volumes: `verus-veritas-cargo-cache`, `verus-veritas-repo-cache`,
`verus-veritas-rustup`, `verus-veritas-z3-cache`. These volumes cache dowloaded repositories,
binaries, and other files, to reduce unnecessary traffic when performing multiple runs.