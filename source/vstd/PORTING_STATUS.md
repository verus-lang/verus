# Status: porting `raw_ptr_dup.rs` to `points_to_permissions.rs`

## Goal

`raw_ptr_dup.rs` is a reference snapshot of the old, axiom-heavy `PointsTo` /
`PointsToUnaligned` / `SeqPointsTo` / `Dealloc` API (originally from `raw_ptr.rs`). It is **not**
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

(Line numbers are as of the current `raw_ptr_dup.rs`; treat as approximate pointers, not stable
IDs — they'll drift as the file changes.)

- `impl<T: ?Sized> PointsTo<T>` (lines 1-10) — just the alignment type invariant. Worth checking
  this is equivalent to the new file's own `?Sized` impl block / `inv`, but low priority.
- `impl<T> PointsTo<[T]>` (lines 185-768) — the slice-typed permission API: `mem_contents_seq`,
  `is_init`/`is_uninit`, `subrange`, `cast_points_to`/`cast_points_to_unaligned`, `is_disjoint`,
  `into_unaligned`/`as_unaligned`, `abstract_bytes_decode`, `into_seq_pt`/`into_seq_pt_shared`,
  `tracked_borrow`/`tracked_borrow_mut`, `from_untyped`/`as_untyped`/`as_untyped_mut`,
  `borrow_mem_contents_subrange`/`copy_mem_contents_subrange`/`take_mem_contents_subrange`/
  `put_subrange`/`put_mem_contents_subrange`. Biggest remaining chunk, mostly axioms.
- `impl PointsTo<[u8]>` (lines 770-874) — `cast_to_typed`, `cast_to_typed_uninit`,
  `cast_to_str_shared`/`cast_to_str_shared_inner`.
- `impl<T> PointsToUnaligned<[T]>` (lines 877-1156) — the unaligned slice permission:
  `is_nonnull`, `ptr_bounds`, `provenance_non_null`, `is_disjoint`,
  `into_aligned`/`as_aligned`/`as_aligned_mut`, `cast_points_to`/`cast_points_to_unaligned`,
  `subrange`, `into_seq_pt`/`into_seq_pt_shared`.
- `impl PointsTo<str>` (lines 1158-1258) — `is_nonnull`, `is_aligned`, `abstract_bytes_decode`,
  `cast_to_u8_shared`/`cast_to_u8_shared_inner`, `as_untyped`.
- Free functions `seq_into_slice`/`seq_into_slice_shared`/`seq_into_slice_mut` (lines 1259-1316).
- `impl<T> SeqPointsTo<T>` (lines 1317-1572-ish) — note: this is the *old* `SeqPointsTo<T>` (one
  type param), distinct from the new file's `SeqPointsTo<T, PointsToPerm>` (two type params) /
  `SeqPointsTo<T, PointsTo<T>>` impl that's already been ported. Includes `subrange_mut` etc. —
  need to work out the mapping to the new two-param type before porting.
- `impl SeqPointsTo<u8>` (lines 1573-1757-ish).
- `impl Dealloc` (lines 1758-1837) — `empty`, `provenance_non_null`, `in_bounds`, `is_disjoint`.

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
  requires `self.wf()` for consistency, and `SeqPointsTo::tracked_pt_seq` now ensures every element
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
