This directory contains various example files of programs to verify.

There is a test in `rust_verify_test/tests/examples.rs` that attempts to run the verify on all .rs files in `example`, unless tagged as "ignore".
The test will check the verification outcome based on the mode specified in the tag.
The tag is specified by adding the following as the *first line*:

```
// rust_verify/tests/example.rs <mode> [---] [optional comment]
```

where `<mode>` is one of:
* `expect-success` (default) expects the verification to succeed, reporting zero verification failures,
* `expect-errors` expects the compiler to fail, without reporting verification successes and failures,
* `expect-failures` expects the compiler and verifier to run successfully, but reporting one or more verification failures,
* `ignore` causes the test to skip this file.

These checks are implemented with a regular expression that matches the expected verifier output.

If no tag is specified on the first line, `expect-success` is assumed.

The "optional comment" field is _required_ if `ignore` is used.

It is recommended to include the optional comment if `expect-failures` is used.

## State-machine examples and the checked macro

An example that selects its state-machine macro with `cfg(verus_verified_tsm)` (see
`source/rust_verify_test/README.md`) is also verified with
`verified_tokenized_state_machine!`/`verified_state_machine_model!`. A header line
`// verified-tsm: <mode> [--- comment]` sets the mode of that run.

The examples in `verified_tsm/` run with `--no-cheating`, unless a header line
`// no-cheating: off --- <reason>` says otherwise. A header line `// EXPECTED-ERROR: <text>`
expects verification to fail with an error containing `<text>` (or with that error code).
