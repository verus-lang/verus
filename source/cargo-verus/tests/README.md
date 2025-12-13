# Integration Tests for `cargo verus`

These tests are meant to confirm integration between `cargo-verus` and `cargo` itself, without actually running any of the heavy machinery. This is where the helper `fake-cargo` binary comes in: it allows capturing the args and env vars that `cargo-verus` passes to `cargo`, but without actually running `cargo` or `verus` in any serious capacity. It only ever invokes `cargo metadata` which does not need network access, because the test fixtures are set up to be entirely local using `path` deps, etc.

## How to Run

```
cargo test -p cargo-verus --features integration-tests
```
