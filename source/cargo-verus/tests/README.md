# Package-Level Tests for `cargo verus`

The tests in this directory validate `cargo-verus` command planning directly.
They use `MockPackage`/`MockWorkspace` fixtures and assert against the
`ExecutionPlan::RunCargo` output: CLI args and environment variable bindings.

## How to Run

```bash
cargo test -p cargo-verus
```
