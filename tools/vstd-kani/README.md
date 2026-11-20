# vstd-kani: checking vstd's std specifications against std

vstd's `assume_specification`s of the Rust standard library are trusted: Verus never checks
them against what std does, and a wrong one lets verified code prove false facts. Two such
bugs have been found in the field: #2674 (`RangeInclusive::end_bound` after iteration) and
#2603 (signed `checked_rem`/`checked_rem_euclid` at `MIN % -1`).

This crate checks specifications mechanically. Each harness restates a specification's
postcondition as plain Rust and asserts that it agrees with the std function it describes.
[Kani](https://github.com/model-checking/kani) checks each harness for all inputs, or for
all inputs up to a bound stated in the harness. A failing harness is a specification that
disagrees with std.

## Contents

- `src/generated.rs`: harnesses that `generate.py` derives from `std_specs/num.rs`, for
  specifications whose postcondition is a single scalar expression (`checked_*`,
  `saturating_*`, `is_multiple_of`). `GENERATED_REPORT.md` lists every specification the
  generator skipped, with the reason. Regenerate with `python3 generate.py`; CI checks that
  `src/generated.rs` is up to date.
- `src/bits.rs`: `trailing_zeros`, `leading_zeros`, `trailing_ones`, `leading_ones` and
  `count_ones` for all unsigned types that vstd specifies them for (`std_specs/bits.rs`).
- `src/chars.rs`: the `char` predicates and ASCII conversions (`std_specs/char.rs`),
  `char::is_whitespace`, and `char::len_utf8` together with std's UTF-8 encoding against
  `encode_scalar` (`utf8.rs`).
- `src/lib.rs`: signed `/` and `%` (`rust_div`/`rust_rem`), hand-written `checked_*` and
  `wrapping_*` harnesses, `Option::is_some`/`is_none`/`unwrap_or`,
  `Result::is_ok`/`is_err`, `RangeInclusive` bounds and emptiness on fresh and iterated
  ranges, `enumerate`, and the regression harnesses for #2603.

The regression harnesses encode the specification as it was before the fix, and are marked
`#[kani::should_panic]`: they pass only if Kani finds the counterexample. #2674 has no such
harness: std changed in Rust 1.99, and the old specification happens to be right for the
current std (see the comment in `src/lib.rs`). The current specification leaves the bounds
of an empty range unspecified, which is right for both.

Each harness predicate is also an ordinary Rust function, so `cargo test` checks the
predicates exhaustively on small domains (all `char`s, all `u8`/`u16`, all `i8` pairs, ...)
under the toolchain Verus pins.

## Which std is checked

Kani uses its own nightly toolchain (Kani 0.68.0: nightly-2026-08-21), so the harnesses
check Kani's std, not necessarily the std of the toolchain Verus pins
(`rust-toolchain.toml`). A specification that describes std behaviour that changed between
the two can pass under one and fail under the other. `cargo test` covers the pinned
toolchain for the harness predicates.

## Running

```
# the harness predicates under the pinned toolchain
cargo test --release

# all Kani harnesses (bound memory as well as time)
cargo install --locked kani-verifier --version 0.68.0 && cargo kani setup
( ulimit -v 12582912; timeout 4800 cargo kani --output-format terse )

# one harness
cargo kani --harness chars::char_specs
```

The nightly workflow `.github/workflows/nightly-vstd-kani.yml` runs both, and checks that
`generate.py` reproduces the checked-in `src/generated.rs`.

## Adding harnesses

A new or changed vstd specification whose postcondition can be computed in Rust can get a
harness here: transcribe the spec functions it uses, call the std function on `kani::any()`
inputs, and assert that the two agree. Keep the predicate a plain function that `cargo test`
can also run. For loops (iterators, slices), bound the input size and give the harness a
`#[kani::unwind(n)]` large enough that Kani's unwinding assertions pass.

`survey.py` classifies the `assume_specification`s of a `std_specs` directory by how
directly they translate into such checks.
