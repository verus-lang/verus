# Design: `Tracked<&T>` in place of `&PointsTo<T>`

Goal: raw-pointer APIs that take a shared `&PointsTo<T>` (`[T]`, `str`) take a `Tracked<&T>` instead,
with the reference's pointer given by its shadow data (`shared_ref_ptr(shadow_data(r))`).
`&PointsToUntyped` and `&PointsToUnaligned<T>` parameters don't change.
`SharedReference` is no longer needed.

A scratch prototype (over the previous `PointsTo` API) verifies:
`get(i)` on a slice through raw pointers, a read through a pointer from a `&mut`,
and B rejecting a reference made in ghost code.

## Shadow data

**Used, now on this branch** (cherry-picked `10dd2cdd1`):
`#[verifier::shadow_data]` on proof functions and axioms,
`shadow_data(x)` on tracked variables (spec variables are rejected) and on a tracked return value in `ensures`,
and `let tracked t = x;` keeping `x`'s shadow data.

**Restrictions the design works around:**

1. **A caller relating two calls through `shadow_data(x)` needs `#[verifier::shadow_data]` itself.**
   Otherwise each call gets its own unknown shadow value for `x`.
   This affects `<[T]>::get_unchecked_verus`, `str::get_unchecked` (add the attribute),
   and the `SliceIndex` `get` / `index` impls, where the attribute goes on the trait:
   for core's `SliceIndex`, that's the `ExSliceIndex` external trait specification (untested).
   Fallback: keep one tuple-returning cast for those impls (as `as_slice_ptr_verus` is now).
2. **The attribute goes on trait methods only, and drops their `call_requires` / `call_ensures` axioms.**
   Affects `SliceIndexVerus` (and `SliceIndex` under 1).
3. **Reborrows, `&mut` → `&` coercions, tuple destructuring and struct fields give fresh shadow data.**
   C covers `&mut` → `&`.
   Exec conversions between reference types (`str::as_bytes`, `from_utf8_unchecked`, ...)
   need shadow-data ensures wherever a pointer has to flow across them.
4. **A reference made in ghost code has an unknown shadow pointer.**
   So a function that gives permission parts for a reference (B) is exec, with the exec pointer as a witness.

**Extensions to Verus:** none needed.
Optional, if the restrictions get in the way:
`shadow_data` on `external_trait_specification` methods (if 1 turns out unsupported),
precise shadow data through `&*x` reborrows,
and shadow-data projections for tuple and struct fields.

## New trusted items

11 trusted functions in place of the current 16 (see [Trusted items removed](#trusted-items-removed)):

| Function | Kind | Versions |
|---|---|---|
| `ptr_shr_ref` | exec | 1, generic over `T: ?Sized` |
| C `mut_ref_as_shr_ref` | axiom | 1, generic over `T: ?Sized` |
| A `untyped_with_typed_value_ref` | axiom | 3: `T`, slice, `str` |
| B `ref_untyped_with_typed_value` | exec | 3: `T`, slice, `str` |
| `borrow_mut_untyped_with_typed_value` | axiom | 3: `T`, slice, `str` (unchanged) |

`ptr_shr_ref` and C only relate a reference to a pointer, so one generic version covers `T`, `[T]` and `str`
(like the existing `ptr_mut_ref_join` for `&mut`).
A and B relate a reference to permission parts, in the parts form of `TRUSTED_POINTS_TO_APPROVED.md`,
so they need one version per `pt_parts_wf` variant:
the slice versions use `pt_parts_wf_slice` and `value_ref()@`,
and rustlib's `proofs/str.rs` has the `str` versions (`pt_parts_wf_str`, with the `inv()` conditions).

`ptr_shr_ref`, A, B, C and rustlib's `as_slice_ptr` / `as_str_ptr` casts (which give only the pointer)
are approved, in [TRACKED_REF_APPROVED.md](TRACKED_REF_APPROVED.md).

Why each is sound:
- **`ptr_shr_ref`, B:** the reference is live for `'a` at a pointer equal to an exec value,
  which rules out references made in ghost code (restriction 4).
- **A:** the reference is built from real, well-formed permission parts.
- **C:** the same trust as the existing `mut_ref_ptr`.

## Trusted items removed

Approved trusted items this replaces (changes to `TRUSTED_POINTS_TO_APPROVED.md`):

| Approved | Count | Replaced by | Count |
|---|---|---|---|
| `ptr_ref_untyped_with_typed_value` (+ slice, `str`) | 3 | A, then `ptr_shr_ref` (verified) | 0 |
| `ptr_ref2_untyped_with_typed_value` | 1 | A, then `ptr_shr_ref` (verified) | 0 |
| | | generic `ptr_shr_ref` | 1 |
| `ptr_ref2_ghost_untyped_with_typed_value` (+ slice, `str`) | 3 | A (+ slice, `str`) | 3 |
| `SharedReference::untyped_with_typed_value` (+ slice, `str`) | 3 | B (+ slice, `str`) | 3 |
| `mut_ref_to_shr_untyped_with_typed_value` (+ slice, `str`) | 3 | generic C | 1 |
| `borrow_mut_*_untyped_with_typed_value` (+ slice, `str`) | 3 | unchanged | 3 |
| **total** | **16** | | **11** |
| rustlib `as_slice_ptr_untyped_with_typed_value`, `as_str_ptr_untyped_with_typed_value` | 2 | `as_slice_ptr` / `as_str_ptr` (the cast only), then B | 2 |

Also removed: `SharedReference` and all its trusted items
(`external_body` struct, `uninterp` `value` / `ptr`, `ptr_nonnull`, `axiom_shared_ref_value_view`).

Unchanged: `pt_parts_wf*`, the structural axioms, `Box`.

## Verified wrappers (`ptr_verified_specs.rs`)

| Current verified wrapper | Becomes |
|---|---|
| `ptr_ref`, `ptr_ref_slice` (over `&PointsTo`) | kept, names and specs unchanged: A, then `ptr_shr_ref` (decided 2026-11-02) |
| `ptr_ref2` | removed (returns a `SharedReference`); callers use `ptr_ref` or `ptr_shr_ref` |
| `ptr_ref2_ghost`, `ptr_ref2_slice_ghost` | a verified `&PointsTo` → tracked `&T` wrapper over A, with the same shadow-data ensures |
| `SharedReference::points_to` (+ slice; rustlib `str`) | removed, with `SharedReference` |
| `mut_ref_to_shr_points_to` (+ slice; rustlib `str`) | removed: as a proof function it can't call B; callers use C, then B in exec code if they need a permission |
| `ptr_mut_ref`, `ptr_mut_ref_slice`, `PointsTo::borrow_mut` | unchanged |

## Files

- **`ptr_specs.rs` (trusted):** the generic `ptr_shr_ref` and C, and the `T` and slice versions of A and B,
  in place of the trusted `ptr_ref_*`, `mut_ref_to_shr_*` functions it has now.
- **`shared_reference.rs`:** removed. Its trusted `ptr_ref2_*` and `untyped_with_typed_value` functions are replaced by `ptr_shr_ref`, A and B.
- **`ptr_verified_specs.rs` (verified):** the wrappers above.
- **rustlib `proofs/str.rs` (approved file):** the `str` versions of A and B, and `ptr_ref_str` as a verified wrapper,
  in place of its `str` trusted functions and wrappers
  (the generic `ptr_shr_ref` and C cover `str`).

## Decided

- **B is exec** (2026-11-02), so ghost code can't get permission parts from a reference;
  it calls B in exec code first.
  Nothing needs a proof-mode B today: every current use of `as_*_ptr_verus`, `SharedReference::points_to`
  and `mut_ref_to_shr_points_to*` (vstd and rustlib) is in exec code,
  apart from the verified wrappers this removes.
  Replacing `mut_ref_to_shr_untyped_with_typed_value` with C (and B in exec code)
  also stops proof code from getting parts for a `&mut` made in ghost code.
- **`ptr_ref` / `ptr_ref_slice` over `&PointsTo` stay as verified wrappers** (2026-11-02);
  the `Tracked<&T>` version is `ptr_shr_ref`.

## For review

Nothing open: all new trusted items are approved, in [TRACKED_REF_APPROVED.md](TRACKED_REF_APPROVED.md).
