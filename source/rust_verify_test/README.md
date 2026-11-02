# rust_verify_test

Run with `vargo test -p rust_verify_test --test <file>` (add `--release` for a release build).

## State-machine tests: trusted and checked macro

Tests of `tokenized_state_machine!` and `state_machine!` also check the proof-producing
`verified_tokenized_state_machine!` and `verified_state_machine_model!`.

### Tests that run with both macros

`test_verify_tsm!` takes the syntax of `test_verify_one_file!` (and
`test_verify_tsm_with_options!` that of `test_verify_one_file_with_options!`) and generates
two tests, `<name>::trusted` and `<name>::verified`. The verified run passes
`--cfg verus_verified_tsm`, under which the `IMPORTS` prelude of `tests/state_machines.rs`
imports `verified_tokenized_state_machine as tokenized_state_machine` and
`verified_state_machine_model as state_machine`. The test body is the trusted test,
unchanged.

If the checked macro is expected to behave differently, add a per-macro expectation after
the trusted one:

```rust
test_verify_tsm! {
    #[test] set_codegen IMPORTS.to_string() + verus_code_str! { .. }
        => Err(e) => assert_fails(e, 2)
    // short reason
    ; verified => Err(e) => assert_fails_anywhere(e, 1)
}
```

* `; verified => <pattern> [=> <assertion>]`: a diagnostic difference, for example a
  different message, span or number of errors. `assert_fails_anywhere(e, n)` counts
  verification failures without requiring them on a `// FAILS` line.
* `; verified ignore "<reason>"`: a checked-macro bug or an unsupported form. The verified
  test is reported as ignored with the reason, and it can be enabled once the macro is fixed
  (`cargo test -- --ignored`).
* `; trusted_only "<reason>"`: no verified test is generated.

#### `--no-cheating` in the verified run

The verified run passes `--no-cheating` (the trusted run does not), so a verified test also
checks that the checked macro introduces no `assume`, `admit`, `external_body` or
`assume_specification`. A test whose own source contains such an assumption (for example
`by { assume(false); }`) opts out:

```rust
test_verify_tsm! {
    #[test] name IMPORTS.to_string() + verus_code_str! { .. } => Ok(())
    ; verified cheating "test source contains assume(false) in a by block"
}
```

* `; verified cheating "<reason>"`: the verified run is without `--no-cheating`. A second
  verified run with `--no-cheating` must be rejected, and each `--no-cheating` error must point
  at a user-written assumption (its highlighted source, or an attribute line directly above it,
  contains `assume`, `admit` or `external_body`), not into macro-generated code. Verus reports
  the first `--no-cheating` error of each function, so a macro-introduced assumption in a
  function that also contains a user assumption is not caught. The reason says which
  assumption of the test's source needs it. The clause combines with the others (in any
  order), for example `; verified cheating "..." ; verified => Err(e) => assert_fails(e, 1)`.

`VERUS_TSM=verified` passes `--cfg verus_verified_tsm` to every verifier run of a test
process. This runs the plain `test_verify_one_file!` tests with the checked macro too (without
`--no-cheating`).

### Tests that need a source change for the checked macro

If the checked macro needs an interface change, the trusted test stays as it is (a plain
`test_verify_one_file!`). Examples are the `Unit` argument of a token-less operation in a
machine with storage, or a body that imports the trusted macro by name. Next to it, add a
separate `<name>_verified` test that uses the checked macro directly and contains the
adapted code. Unless its source contains an assumption (as the `by { assume(false); }` of the
example below), make it a `test_verify_one_file_with_options!` with `["--no-cheating"]`, like
the verified run of `test_verify_tsm!` (for example `step_is_variant_verified`). Start it with
a one-line comment naming the difference:

```rust
// Checked-macro version of test_use_pre_no_field_withdraw_kv_key. API difference: in a machine
// with storage, an operation that consumes no token takes a `Unit` (here from
// `<init>_with_unit`, as the machine has no field token).
test_verify_one_file! {
    #[test] test_use_pre_no_field_withdraw_kv_key_verified IMPORTS.to_string() + verus_code_str! {
        verified_tokenized_state_machine!{ X { .. } }
        ..
            let tracked (Tracked(inst), Tracked(unit)) = X::Instance::initialize_with_unit(m);
            let tracked t = (inst).tr(unit);
        ..
    } => Ok(())
}
```

Don't put `#[cfg(verus_verified_tsm)]` shims in the original test.

### Examples

`tests/examples.rs` gives an example an extra `<example>_verified_tsm` test if the file
contains `cfg(verus_verified_tsm)`, which is how the example selects its macro in its import
lines:

```rust
#[cfg(not(verus_verified_tsm))]
use verus_state_machines_macros::tokenized_state_machine;
#[cfg(verus_verified_tsm)]
use verus_state_machines_macros::verified_tokenized_state_machine as tokenized_state_machine;
```

A header line `// verified-tsm: <mode> [--- reason]` (the modes of the first line, see
`examples/README.md`) overrides the expectation of the verified run. The verified run uses
`--no-cheating`; an example whose own source contains an assumption opts out with a header
line `// no-cheating: off --- <reason>`, and then a second verified run with `--no-cheating`
checks that every `--no-cheating` error points at the example's own assumptions. An example that needs
an interface change keeps only the trusted macro (for example
`examples/cuckoo_hash_table/cuckoo.rs`, which names `IMapToken`); the interface difference
itself is tested in `examples/verified_tsm/` (here `generic_tokens_imap.rs`).

`examples/verified_tsm/` (with `negative/`) holds the tests that only make sense for the
checked macro: the raw interface, local readiness, the generic interface's differences from
the trusted one, checked diagnostics, soundness negatives the trusted macro does not catch,
and regression tests for bugs of the checked macro. Its `README.md` lists every file with the
reason it is kept; add a test there only if it covers something the dual-run tests in
`tests/state_machines.rs` and the trusted examples do not. They run with `--no-cheating`. A file can
opt out with a header line `// no-cheating: off --- <reason>`. A negative test states a
substring of its expected error with `// EXPECTED-ERROR: <text>`, matched against the
rendered errors and the error codes.
