# `verita`

Verita is a [crater](https://github.com/rust-lang/crater)-inspired benchmarking tool for [Verus](https://github.com/verus-lang/verus), a Rust verification framework. Given a configuration file listing Verus projects, `verita` clones each project, runs Verus verification on it, and saves the results — including per-function verification timing — to a timestamped output directory. The goal is to make it easy to compare verification performance and correctness across different Verus versions or solver configurations.

Derived in part from an earlier [veritas tool](https://github.com/verus-lang/verus/tree/main/tools/veritas).

## Building and running

```bash
cargo build --release
```

For full usage information, run:

```bash
cargo run -- --help
```

A typical invocation looks like:

```bash
cargo run -- --verus-repo /path/to/verus --label my-experiment run_configuration_all.toml 
```

## Output

Each run produces a directory under `output/` named by timestamp and label:

```
output/YYYY-MM-DD-HH-MM-SS-msec-LABEL/
```

Inside that directory there is one JSON file per project (or per crate root, for projects with multiple crate roots). Each JSON file contains the raw Verus verification output augmented with a `runner` object that records metadata such as:

- Whether the run succeeded
- `stderr` output from Verus
- Verus and solver versions
- Per-function verification timing
- The label and date of the run

If a project has verification errors, `verita` also preserves a copy of the cloned repository in a temporary directory for debugging purposes.

## Summarizing results

The `scripts/summarize.py` script provides a quick overview of a run's outcome.

**Single run summary** — prints per-project status, verified/error counts, total time, and the top-5 slowest functions per project:

```bash
python scripts/summarize.py output/2026-01-10-baseline/
```

**Comparing two runs** — shows how each project's status, counts, and timing changed between an old and a new run:

```bash
python scripts/summarize.py output/2026-01-10-baseline/ output/2026-02-15-experiment/
```

## Configuration file format

Configuration files are TOML. The top-level section configures run-wide options, and each `[[project]]` section describes one project to verify.  At present, the only relevant top-level key is `verus_extra_args`, which is an optional list of string arguments to be passed to every Verus invocation.

NOTE: At present, when running with `cargo verus`, we use `cargo verus focus` to avoid re-verifying dependencies, such as `vstd`.

### Per-project keys (`[[project]]`)

| Key | Type | Default | Description |
|-----|------|---------|-------------|
| `name` | string | required | Display name; also used as the output filename stem |
| `git_url` | string | required | Git URL of the project repository |
| `refspec` | string | required | Git refspec (branch, tag, or commit) to check out |
| `crate_roots` | list of strings | required | Paths to crate root files or directories, relative to the repo root. For projects using `cargo verus` these are subdirectory paths; for projects that directly invoke `verus` these are paths to `.rs` files. Multiple entries cause `verita` to run `verus` (or `cargo verus`) separately on each root. |
| `extra_args` | list of strings | `[]` | Additional arguments appended to the Verus command for this project |
| `prepare_script` | string | none | Shell script (bash/sh) run inside the cloned repo before verification. Useful for building dependencies. |
| `prepare_script_windows` | string | none | PowerShell equivalent of `prepare_script` used on Windows. If omitted on Windows and `prepare_script` is set, the prepare step is skipped with a warning. |
| `cargo_verus` | boolean | `false` | When `true`, use `cargo verus focus` instead of invoking `verus` directly. The crate roots are treated as package directories rather than `.rs` file paths. |
| `requires_singular` | boolean | `false` | Indicates whether this project depends on Singular functionality in Verus. When `true`, `verita` requires `--singular` (or `VERUS_SINGULAR_PATH`) to be set; the run is aborted early if neither is provided. |
| `ignore` | boolean | `false` | When `true`, the project is skipped unless `--run-ignored` is passed on the command line. Useful for projects that are known to be broken. |

