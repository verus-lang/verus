# Testing `vstd` with Verus SpecCheck

[Verus SpecCheck](https://github.com/verus-lang/verus-spec-check) turns Verus contracts into
 executable tests. vstd can carry its labels directly in its source:

```rust
verus! {

#[vcheck]
#[verifier::external_body]
pub exec fn u16_from_le_bytes(s: &[u8]) -> (x: u16)
    requires s@.len() == 2,
    ensures x == spec_u16_from_le_bytes(s@),
{ ... }

#[vcheck(T = u32)]
#[verifier::external_body]
pub exec fn slice_to_vec<T: Copy>(slice: &[T]) -> (out: alloc::vec::Vec<T>)
    ensures out@ == slice@,
{ ... }

}
```

The labels are `#[vcheck]`, `#[vcheck_provide]`, `#[vcheck_axiom]`, `#[vcheck_view]`,
`#[vcheck_cov_mutate]`, `#[vcheck_cov_fuzz]`, `#[vcheck] assert(...)` and
`external_vcheck_provide! { ... }`, as described in the
[Verus SpecCheck usage guide](https://github.com/verus-lang/verus-spec-check/blob/main/USAGE.md).
Labels must be inside `verus!`.

## Running the tests

From `source/vstd`:

```sh
cargo test --features spec-check --lib
```

or from outside `source/`, e.g. the repository root:

```sh
cargo test --manifest-path source/vstd/Cargo.toml --features spec-check --lib
```

Use `--lib`. vstd's doctests are Verus examples that don't compile as plain Rust, with or
without this feature. The usual vcheck knobs apply (`PROPTEST_CASES=10000`,
`VERUS_SPEC_CHECK_PRINT_EXPANSION=1`, ...).

Without passing in `--features spec-check`, no verification changes. `vstd` lists
Verus SpecCheck as a dev dependency, so `cargo publish` will drop them.

## Updating verus-spec-check

Bump the `tag` in both `source/vstd/Cargo.toml` (the `verus_spec_check` dev-dependency) and
`Cargo.toml` here (`verus_spec_check_engine`), and set `verus_syn` here to the version that tag
pins in its `[workspace.dependencies]`.

## Known gaps

- `vstd::contrib::spec_check` doesn't provide `verus_spec_check_vstd_ext::resource`, so
  harnesses over tracked permissions (`Tracked<PointsTo<_>>` parameters) don't compile yet.
- Labels in `verus_impl!` / `verus_trait_impl!` are stripped, not tested (the engine has no
  pass for bare impl item lists)
- verus-spec-check can't yet generate a harness for some contract shapes, e.g. a returned
  slice reference compared against a subrange (`slice_subrange`).
