# Trusted / Proof / Code line accounting

This accounts Verus lines in a project by whether they are
* part of the trusted system specification,
* executable code, or
* proof text.

## Usage

```
Usage: line_count [OPTIONS] [PATHS]...

Arguments:
  [PATHS]...  Paths to be counted. Can only be 1 in `--deps` mode

Options:
  -p, --print-all               Print all the annotated files
      --no-external-by-default  Do not ignore items outside of `verus!` by default
      --json                    Output as machine-readable json
      --delimiters-are-layout   Consider delimiter-only lines as layout
      --proofs-arent-trusted    Do not apply _trusted_ to proofs
      --deps                    Parse the DEPS_FILE.d file produced by rustc, finding the crate's paths from that source
  -h, --help                    Print help
```

To use the line counter, you can point it at a set of paths. `line_count` searches recursively any directories passed on:

```bash
$ line_count crate_a/src crate_b/src
```

An alternative way to run the tool is by leveraging the cargo emitted dependency file.
If you first run `cargo verus verify -- --emit=dep-info` on your project, a `.d` file in that project's `target/debug/` directory will be generated.
Then, you can run line_count with that file only:
```
line_count --deps DEPS_FILE.d
```

### Options

With the `--print-all/-p` option you can inspect the project source to see how each line is accounted.
`Spec`, `Proof`, `Exec` are lines with that mode (with some imprecision due to the fact that
this accounting is purely syntactic and some lines aren't purely one mode). Lines that contain
both `Exec` and `Proof` code are accounted separately.
`Trusted` are all the lines in files, modules, items marked with `#[verus::trusted]` and should be
the system and environment specification (i.e. what needs to be manually inspected by an auditor).
Other lines are other definitions and directives, whitespace and mostly-whitespace lines (`Layout`)
and `Comment`s.

Please use `-p` to check that the overrides are being applied correctly.
Report any bugs in the verus repository.

### Accounting

By default we only count items inside the `verus!` macro, and items marked `#[verified::verify]`.
You can set `--no-external-by-default` to count everything in the crate. There are also local overrides:

* `#[verus::line_count::ignore]` ignores an item in the line count (it becomes unaccounted);
* `#[verus::line_count::consider]` enables counting for an item that would otherwise be ignored.

Finally even more manual overrides are available:

* you can mark a single line with a comment containing the string `$line_count$<list of categories>$` where `<list of categories>` is a comma separated list of categories to apply to that line (which is typically only one), for example `$line_count$Proof$` marks a line as Proof'
* you can mark a block using `$line_count$<list of categories>${$` (at the start of the block) and
`$line_count$}$` at the end of the block; if the list of categories is empty, the line will be ignored.

By default lines that only contain delimiters are accounted as the enclosing context. If you would like to consider them as layout lines instead, use `--delimiters-are-layout`.
