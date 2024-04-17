# Trusted / Proof / Code line accounting

This accounts Verus lines in a project by whether they are
* part of the trusted system specification,
* executable code, or
* proof text.

## Known issues

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

By default we only count items inside the `verus!` macro, and items marked `#[verified::verify]`.
You can set `--no-external-by-default` to count everything in the crate. There are also local overrides:

* `#[verus::line_count::ignore]` ignores an item in the line count (it becomes unaccounted);
* `#[verus::line_count::consider]` enables counting for an item that would otherwise be ignored.

Finally even more manual overrides are available:

* you can mark a single line with a comment containing the string `$line_count$<list of categories>$` where `<list of categories>` is a comma separated list of categories to apply to that line (which is typically only one), for example `$line_count$Proof$` marks a line as Proof'
* you can mark a block using `$line_count$<list of categories>${$` (at the start of the block) and
`$line_count$}$` at the end of the block; if the list of categories is empty, the line will be ignored.

By default lines that only contain delimiters are accounted as the enclosing context. If you would like to consider them as layout lines instead, use `--delimiters-are-layout`.

Please use `-p` to check that the overrides are being applied correctly.
