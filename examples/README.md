This directory contains various example files of programs to verify.

There is a test in `rust_verify/tests/examples.rs` that attempts to run the verify on all .rs files in `example`, unless tagged as "ignore".
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
