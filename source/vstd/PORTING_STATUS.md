# Status: porting `raw_ptr_dup.rs` to `points_to_permissions.rs`

## Goal

`raw_ptr_dup.rs` is a reference snapshot of the old, axiom-heavy `PointsTo` /
`PointsToUnaligned` / `SeqPointsTo` API (originally from `raw_ptr.rs`). It is **not**
part of the build — it's not listed as a module in `vstd.rs` — so it's just there to make porting
easier without scrolling through the much larger `raw_ptr.rs`.

We're porting its contents, piece by piece, into the new, compositionally-built model in
`points_to_permissions.rs`, proving what were previously axioms wherever the new concrete
representation makes that possible. The new model builds `PointsTo<T>` on top of
`PointsToUnaligned<T>` (which now directly holds a `TypedValue<T>` — a real `Box<T>` when valid —
plus a `Tracked<PointsToUntyped>`), which is built on `PointsToUntyped = SeqPointsTo<[u8],
PointsToSingleton>`, bottoming out at `PointsToSingleton` (the one remaining
`#[verifier::external_body]` primitive, in `points_to.rs`). Because `PointsToUnaligned<T>` is no
longer opaque, a lot of what used to require an axiom can now be proved by directly manipulating
its fields.

This file tracks what's been ported so far and what's left in `raw_ptr_dup.rs`.

## Done

`impl<T> PointsTo<T>` (`raw_ptr_dup.rs` lines 12-183) — fully ported to `points_to_permissions.rs`.

Originally `proof fn` (ported/adapted to new naming, not axioms either before or after):
- `into_unaligned`
- `as_unaligned`
- `bytes_decode` (was `abstract_bytes_decode`)
- `cast_to_untyped` — now returns `(PointsToUntyped, Option<T>)` instead of
  `(PointsTo<[u8]>, Option<T>)`, since `PointsTo<[u8]>` doesn't exist in the new model.

Originally `axiom fn`, now proved:
- `from_untyped`
- `into_untyped`
- `as_untyped`
- `as_untyped_mut`
- `borrow`
- `take`
- `put`

Still an axiom, expected to stay that way:
- `borrow_mut` — its contract requires `mut_ref_ptr(val) == old(self).ptr()`, linking a real Rust
  reference to the raw pointer it was derived from. That link can only be established by an
  actual unsafe dereference of `self.ptr()` (as `ptr_mut_ref` in `raw_ptr.rs` does), not by
  borrowing out of a ghost `Box<T>` — a genuine trust boundary, not just a gap in the current
  representation.

Verified via `tools/build-expand-errors.sh`: baseline before this work was 1965 verified / 0
errors; currently 1976 verified / 0 errors.

## Not yet ported (remaining `raw_ptr_dup.rs` contents)

The old slice/`str` permissions (`PointsTo<[T]>`, `PointsTo<[u8]>`, `PointsToUnaligned<[T]>`,
`PointsTo<str>`) will be ported as impls on `SeqPointsTo` rather than as separate types, so this
section lists only what has no equivalent in `SeqPointsTo<T, PointsTo<T>>` yet. (The alignment type
invariant on `impl<T: ?Sized> PointsTo<T>` is just there for reference and won't be ported.)

### Already covered by `SeqPointsTo<T, PointsTo<T>>` (no porting needed)

- `mem_contents_seq`/`len`/`spec_index`, `is_init`/`is_uninit`/`is_fully_uninit`, `value` →
  `typed_value`/`len`/`spec_index`, `is_valid`/`is_empty`/`is_fully_empty`, `value`.
- `is_nonnull`/`ptr_bounds`/`provenance_non_null` → the `PointsToProperties` trait methods;
  `is_aligned` → `wf()` includes alignment; `is_disjoint` → `is_disjoint_seqpt` / trait
  `is_disjoint`.
- `abstract_bytes_decode` → `bytes_decode`/`bytes_equiv`/`bytes_len`.
- `into_seq_pt*` and the `seq_into_slice*` free functions disappear once slices are `SeqPointsTo`.
  Seq access is via `into_seq`/`tracked_seq_pt`/`tracked_seq_pt_mut`/`index_mut`.
- `as_untyped` → `as_untyped` (axiom); `from_untyped` (all uninitialized) →
  `PointsToUntyped::cast_to_seq_pt` with an empty `typed_value`;
  `PointsTo<[u8]>::cast_to_typed_uninit` → `PointsTo::from_untyped`.

### Ported from the remaining slice functions

- `is_init_subrange`/`value_subrange` → `is_valid_subrange`/`value_subrange` (specs).
- Subrange content operations. **Proved** (by induction over the range, using `index_mut`
  and the concrete `TypedValue` representation): `put_subrange`, `put_typed_value_subrange`,
  `take_typed_value_subrange`, `copy_typed_value_subrange` (`T: Copy`). `PointsTo::put`/`take` now
  also ensure `ptrs_len_same_valid_decode`, which these proofs need.
  Note: the old `take_mem_contents_subrange` filled the range with `Seq::new(end, ...)` (length
  `end`); the port uses `end - start`.
- **Axioms** (they return a reference to something the `SeqPointsTo` doesn't store, so there is
  nothing to borrow): shared-borrow `subrange`, `borrow_typed_value_subrange`, and `as_untyped_mut`
  for sequences.
- Integer casts `cast_points_to`/`cast_points_to_unaligned` were drafted as axioms on
  `SeqPointsTo<T, PointsTo<T>>` and then removed, since that isn't their final home (see the
  TODOs). The old contracts are in `raw_ptr_dup.rs` (`impl<T> PointsTo<[T]>`).
- Single-value `PointsTo<[u8]>::cast_to_typed` → `PointsToUntyped::cast_to_typed` (proved from
  `PointsTo::from_untyped` + `put`).

### `PointsTo<str>` → `SeqPointsTo<str, PointsTo<u8>>`: drafted, removed from the build

A `str` permission as a `SeqPointsTo<str, PointsTo<u8>>` (one `PointsTo<u8>` per byte, a `*mut str`
pointer whose metadata is the length, no stored `str`; the value is derived from the `u8` values via
`str::spec_bytes()`) was drafted and verified, including the `[u8]` to `str` cast, but is **not**
in `points_to_permissions.rs` right now (it is excluded because of the `spec_bytes` cfg issue
below). The complete code and its design notes are saved in
[points_to_str_wip.rs](points_to_str_wip.rs), a reference snapshot that is not part of the build.
It has the build at 2009 verified, 0 errors (2005 without it).

What the snapshot contains:
- Specs `bytes`, `value_bytes`, `is_valid`, `is_empty`, `value`, `wf`. `is_valid()` = every byte
  valid and some `&str` has exactly those bytes and the abstract bytes decode into it; `wf()` =
  `wf_basic()` and `ptr()@.metadata == len()`. Decodability is in `is_valid()` rather than `wf()`
  because there is no `str` extensionality axiom (two `&str`s with the same `spec_bytes()` aren't
  known to be equal), so a `choose`-based `value()` couldn't otherwise be shown to decode.
- Proved: `is_aligned`, `bytes_decode`, `cast_to_u8_seq_pt` (replaces `cast_to_u8_shared`/`_inner`),
  and `cast_to_str` on `SeqPointsTo<u8, PointsTo<u8>>` (replaces `cast_to_str_shared`/`_inner`;
  ensures `out.value().spec_bytes() == value@` rather than `out.value() == target`, for the same
  extensionality reason).
- Axioms: `as_untyped` and `as_u8_seq_pt` (nothing is stored to borrow).

Reason it was taken out: `StringSliceAdditionalSpecFns::spec_bytes` is
`cfg(not(verus_verify_core))` in `string.rs`, so the `str` code would need a cfg guard if
`points_to_permissions.rs` is ever built under `verus_verify_core`. To restore: see the header of
the snapshot file (paste the block back and re-add two imports).

### Not yet covered (on hold)

- All of `PointsTo<str>` and the `[u8]` to `str` casts (`cast_to_str_shared`/`_inner`): see above
  (drafted, saved in `points_to_str_wip.rs`).
- `tracked_borrow` (`&[T]`) and `tracked_borrow_mut` (`&mut [T]`): real slice references, so the
  same trust boundary as `PointsTo::borrow_mut`; would be axioms.
- `cast_points_to` and `cast_points_to_unaligned` (a `[T]` permission to a `V` permission, for
  integer `T`, `V`): they belong in an `impl` block on `PointsTo<[T]>`, not on `SeqPointsTo`, so
  they are on hold until `PointsTo<[T]>` is implemented (see the TODOs; they were drafted on
  `SeqPointsTo<T, PointsTo<T>>` and removed).
- **Unaligned slices** (`impl<T> PointsToUnaligned<[T]>`): the unaligned-specific functions
  (`into_aligned`/`as_aligned`/`as_aligned_mut`, `subrange`, the `cast_points_to` pair) assume a
  `SeqPointsTo<T, PointsToUnaligned<T>>`, which has no impl yet (the current impl is only for
  `PointsTo<T>`). On hold until needed. The trait methods (`is_nonnull`, `ptr_bounds`,
  `is_disjoint`) already work for it generically.

## Done: old `SeqPointsTo<T>` and `SeqPointsTo<u8>` impls

The old `impl<T> SeqPointsTo<T>` (`raw_ptr_dup.rs` lines 1144-1398) is the old one-type-param
`SeqPointsTo<T>`, distinct from the new `SeqPointsTo<T, PointsToPerm>`; it is now ported to
`SeqPointsTo<T, PointsTo<T>>`:
- `from_seq`, `split`, `join`, and `cast_to_untyped` (returns a `PointsToUntyped`) are proved.
- `subrange_mut` and `as_untyped` are axioms. `subrange_mut` hands out a `&mut` sub-permission
  whose final state flows back into `self`. `as_untyped` is an axiom returning `&PointsToUntyped`
  because the new type stores no `PointsToUntyped` to borrow.
- Added `PointsToUntyped::split`/`join`, which `cast_to_untyped` needed.

The old `impl SeqPointsTo<u8>` is ported as `PointsToUntyped::cast_to_seq_pt`, which returns a
`SeqPointsTo<T, PointsTo<T>>` (proved by induction using `split`/`join`, `PointsTo::from_untyped`
and `PointsTo::put`).

## TODO

- [x] Audit `as_untyped_mut` and `borrow_mut`: `as_untyped_mut` now guarantees `final(self).wf()`
  under `PointsToUntyped::ptrs_len_same` (replacing the bare pointer-equality condition);
  `borrow_mut` requires `old(self).wf()` and ensures
  `ptrs_len_same_valid_decode(old, final) ==> final(self).wf()`.
- [x] `take` and `put` now require `old(self).wf()` and ensure `final(self).wf()`. `borrow` takes
  `&self` so has no `final` state to guarantee.
- [x] Audited every proof fn in `points_to_permissions.rs` for `wf()` requires/ensures. Added
  `requires self.wf()` / `ensures perm.wf()` to `PointsToUnaligned::into_aligned`/`as_aligned` and
  `PointsTo::into_unaligned`/`as_unaligned`, and `requires self.wf()` plus
  `ensures forall|i| r[i].wf()` to `SeqPointsTo::into_seq`. `tracked_pt_untyped` and
  `tracked_pt_unaligned` intentionally have no `wf` clauses (they live in `?Sized` impl blocks,
  where `wf` isn't defined); each has a comment explaining this. Follow-up: `PointsTo::borrow` now
  requires `self.wf()` for consistency, and `SeqPointsTo::tracked_seq_pt` now ensures every element
  is `wf()` (like `into_seq`). The `PointsToProperties` trait contracts in `points_to.rs` were
  checked and already require `wf_basic()`; note `is_disjoint` puts no `wf` requirement on `other`
  (its bound is only `PointsToPhys`).
- [ ] Keep applying the same wf requires/ensures audit to every proof fn ported from here on.
- [ ] Audit whether the `Tracked<...>` wrappers around the permissions held by the various
  `PointsTo*` structs (e.g. `PointsTo::pt_unaligned: Tracked<PointsToUnaligned<T>>`,
  `PointsToUnaligned::pt_untyped: Tracked<PointsToUntyped>`) are actually needed, or whether they
  can be removed since the structs holding them are themselves `tracked`.
  - Status: on hold, no edits made. Likely feasible and a simplification: bare fields already work
    in tracked structs (`val: TypedValue<T>`, `SeqPointsTo::seq_pt`), so removal would drop
    `.get()`/`.borrow()`/`.borrow_mut()`, `Tracked(...)` in constructors, and the `@` in the closed
    specs `pt_untyped()`/`pt_unaligned()`. The fields are private, so there's no external API change.
  - Known risk: the commented-out body of the `PointsToUnaligned::as_aligned` axiom uses
    `shr_ref_struct_wrap(self, &PointsTo { pt_unaligned: Tracked(self) }, "", "pt_unaligned")` (from
    `main`, not on this branch). If that helper needs a `Tracked` field, removing it from
    `PointsTo::pt_unaligned` would block proving `as_aligned`. Investigate `shr_ref_struct_wrap`
    before removing that wrapper. The `PointsToUnaligned::pt_untyped` wrapper doesn't have this concern.
- [ ] Continue porting the remaining impl blocks listed above — `impl<T> PointsTo<[T]>` is
  probably next, since it's the biggest and most load-bearing.
- [ ] (Lower priority) Fill out `SeqPointsTo<T, PointsTo<T>>` and `PointsTo<T>` for completeness
  with respect to each other. The up-to-date list of what is missing is in the TODOs section of
  [POINTS_TO_COMPARISON.md](POINTS_TO_COMPARISON.md) (e.g. the
  `Seq<T>` subrange versions, the single-value `TypedValue<T>` operations on `PointsTo`). The
  unaligned conversions (`as_unaligned`, `into_unaligned`, ...) can wait until there is a
  `SeqPointsTo<T, PointsToUnaligned<T>>`.
- [ ] Add `cast_points_to` and `cast_points_to_unaligned` in an `impl` block on `PointsTo<[T]>`,
  where they make more sense than on `SeqPointsTo`. They were drafted as axioms on
  `SeqPointsTo<T, PointsTo<T>>` and removed; the draft contract (requires `wf()`, all elements
  valid, `len * size_of::<T>() == size_of::<V>()`, plus alignment to `V` for the aligned version;
  ensures `points_to.wf()`, the same address/provenance, same bytes, and
  `value() as int == to_big_from_digits::<V, T>(value()).index(0)`) is straightforward to redo.
  They would also need the `endian` imports (`CompatibleSmallerBaseFor`, `BasePow2`,
  `to_big_from_digits`). On hold until `PointsTo<[T]>` is implemented.
