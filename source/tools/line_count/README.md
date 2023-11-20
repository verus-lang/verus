# Trusted / Proof / Code line accounting

This accounts Verus lines in a project by whether they are
* part of the trusted system specification,
* executable code, or
* proof text.

## Known issues

* `#[verus::trusted]` is ignored on macros
* `macro_rules!` are accounted as directives, or ignored
* `#[verifier::verify]` is ignored

To run this, first run `verus` on a project with `--emit=dep-info`. This will output a `.d` file in the
current working directory. Then run this tool with
```
cargo run --release -- path_to.d -p
```
You will need a shell not configured for `vargo` to be able to run cargo directly.

With the `-p` option you can inspect the project source to see how each line is accounted.
`Spec`, `Proof`, `Exec` are lines with that mode (with some imprecision due to the fact that
this accounting is purely syntactic and some lines aren't purely one mode). Lines that contain
both `Exec` and `Proof` code are accounted separately.
`Trusted` are all the lines in files, modules, items marked with `#[verus::trusted]` and should be
the system and environment specification (i.e. what needs to be manually inspected by an auditor).
Other lines are other definitions and directives, whitespace and mostly-whitespace lines (`Layout`)
and `Comment`s.

At the end of the output, there is a table with a summary per-file and totals. To only print the table
remove the `-p` option.
