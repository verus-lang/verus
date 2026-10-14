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
plus a `PointsToUntyped`), which is built on `PointsToUntyped = SeqPointsTo<[u8],
PointsToSingleton>`, bottoming out at `PointsToSingleton` (the one remaining
`#[verifier::external_body]` primitive, in `points_to.rs`). Because `PointsToUnaligned<T>` is no
longer opaque, a lot of what used to require an axiom can now be proved by directly manipulating
its fields.

This file tracks what's been ported so far and what's left in `raw_ptr_dup.rs`.

## Done

### `impl<T> PointsTo<T>` (`raw_ptr_dup.rs` lines 12-183)

Fully ported to `points_to_permissions.rs`.

Originally `proof fn` (ported/adapted to new naming, not axioms either before or after):
- `into_unaligned`
- `as_unaligned`
- `bytes_decode` (was `abstract_bytes_decode`)
- `cast_to_untyped` → `into_untyped_with_typed_value` — now returns
  `(PointsToUntyped, TypedValue<T>)` instead of `(PointsTo<[u8]>, Option<T>)`, since
  `PointsTo<[u8]>` doesn't exist in the new model.

Originally `axiom fn`, now proved:
- `from_untyped`
- `into_untyped`
- `as_untyped`
- `as_untyped_mut` (its flow-back clause also ensures `ptrs_len_same_valid_decode(old, final)`)
- `borrow` (now `borrow_value`)
- `take`
- `put`

Commented out (not essential for now):
- `borrow_mut`. A version proved from a `TypedValue` mutable-borrow axiom could only keep the bytes
  unchanged, so callers could never restore `wf()` after writing a new value. It was then made an
  axiom whose final permission is `wf()` unconditionally (the bytes change along with the value),
  and later commented out. Its old `mut_ref_ptr(val) == old(self).ptr()` postcondition is also
  commented out (Travis: not necessarily true because of `Box`/enum, and not obviously needed).

New (no counterpart in `raw_ptr_dup.rs`), all proved:
- `copy` (`T: Copy`, taking `&T`)
- `borrow_typed_value`, `take_typed_value`, `put_typed_value` and `copy_typed_value` (the
  `TypedValue<T>` versions of `borrow`/`take`/`put`/`copy`)

All of `take`, `put`, `copy` and the three mutating `*_typed_value` functions ensure
`ptrs_len_same_valid_decode(old, final)`, so they can be used through `SeqPointsTo::index_mut`.

### `impl<T> PointsToUnaligned<T>`

- `as_aligned` is now proved with `shr_ref_struct_wrap` (it was an axiom waiting on that builtin).

The current list of axioms is in [POINTS_TO_AXIOMS.md](POINTS_TO_AXIOMS.md).

## Not yet ported (remaining `raw_ptr_dup.rs` contents)

The old slice/`str` permissions (`PointsTo<[T]>`, `PointsTo<[u8]>`, `PointsToUnaligned<[T]>`,
`PointsTo<str>`) will be ported as impls on `SeqPointsTo` rather than as separate types, so this
section lists only what has no equivalent in `SeqPointsTo<T, PointsTo<T>>` yet. (The alignment type
invariant on `impl<T: ?Sized> PointsTo<T>` is just there for reference and won't be ported.)

### Already covered by `SeqPointsTo<T, PointsTo<T>>` (no porting needed)

- `mem_contents_seq`/`len`/`spec_index`, `is_init`/`is_uninit`/`is_fully_uninit`, `value` →
  `seq_typed_value`/`len`/`spec_index`, `is_valid`/`is_empty`/`is_fully_empty`, `seq_value`.
- `is_nonnull`/`ptr_bounds`/`provenance_non_null` → the `PointsToProperties` trait methods;
  `is_aligned` → `wf()` includes alignment; `is_disjoint` → `is_disjoint_seqpt` / trait
  `is_disjoint`.
- `abstract_bytes_decode` → `bytes_decode`/`bytes_equiv`/`bytes_len`.
- `into_seq_pt*` and the `seq_into_slice*` free functions disappear once slices are `SeqPointsTo`.
  Seq access is via `into_seq`/`tracked_seq_pt`/`tracked_seq_pt_mut`/`index_mut`.
- `as_untyped` → `as_untyped` (proved from the `PointsToUntyped::join_ref` axiom); `from_untyped` (all uninitialized) →
  `from_untyped` (proved from `from_untyped_with_typed_value` with an empty `typed_value`);
  `PointsTo<[u8]>::cast_to_typed_uninit` → `PointsTo::from_untyped`.

### Ported from the remaining slice functions

- `is_init_subrange`/`value_subrange` → `is_valid_subrange`/`value_subrange` (specs).
- Subrange content operations, all **proved** (by induction over the range, using `index_mut`
  and the concrete `TypedValue` representation): `put_subrange`, `take_subrange`, `copy_subrange`
  (`T: Copy`), and the `TypedValue<T>` versions `put_typed_value_subrange`,
  `take_typed_value_subrange` and `copy_typed_value_subrange`. They rely on `PointsTo::put`/`take`
  ensuring `ptrs_len_same_valid_decode`.
  Note: the old `take_mem_contents_subrange` filled the range with `Seq::new(end, ...)` (length
  `end`); the port uses `end - start`.
- **Borrows of things the `SeqPointsTo` doesn't store** are all proved:
  - `borrow_value_subrange` returns a `Seq<&T>` and `borrow_typed_value_subrange` a
    `Seq<&TypedValue<T>>`, built element by element from `PointsTo::borrow_value` /
    `borrow_typed_value`.
  - The shared-borrow `subrange` borrows the `seq_pt` subrange (`Seq::tracked_borrow_subrange`) and
    wraps it with `shr_ref_struct_wrap`. `bytes_subrange_equiv` relates its bytes to a subrange of
    `self.bytes()`.
  - `as_untyped`/`as_untyped_mut` join per-element borrows with the binary
    `PointsToUntyped::join_ref`/`join_mut` axioms (`as_untyped_mut` splits the `&mut Seq` with
    `Seq::tracked_split_borrow_mut`).
  - `borrow_mut_subrange` (a `Seq<&mut T>`) was proved from `PointsTo::borrow_mut` and is
    commented out along with it.
- Integer casts `cast_points_to`/`cast_points_to_unaligned` were drafted as axioms on
  `SeqPointsTo<T, PointsTo<T>>` and then removed, since that isn't their final home (see the
  TODOs). The old contracts are in `raw_ptr_dup.rs` (`impl<T> PointsTo<[T]>`).
- Single-value `PointsTo<[u8]>::cast_to_typed` → `PointsTo::from_untyped_with_value` (proved from
  `PointsTo::from_untyped` + `put`).

### `PointsTo<str>` → `SeqPointsTo<str, PointsTo<u8>>`: drafted, removed from the build

A `str` permission as a `SeqPointsTo<str, PointsTo<u8>>` (one `PointsTo<u8>` per byte, a `*mut str`
pointer whose metadata is the length, no stored `str`; the value is derived from the `u8` values via
`str::spec_bytes()`) was drafted and verified, including the `[u8]` to `str` cast, but is **not**
in `points_to_permissions.rs` right now (it is excluded because of the `spec_bytes` cfg issue
below). The complete code and its design notes are saved in
[points_to_str_wip.rs](points_to_str_wip.rs), a reference snapshot that is not part of the build.

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
- `tracked_borrow` (`&[T]`) and `tracked_borrow_mut` (`&mut [T]`): real slice references, so they
  would need axioms, like the (commented-out) `PointsTo::borrow_mut`.
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
- `from_seq`, `split`, `join`, `into_untyped_with_typed_value` (was `cast_to_untyped`; returns a
  `PointsToUntyped` and the `Seq<TypedValue<T>>`), `into_untyped` and `from_untyped` are proved.
- `subrange_mut` is an axiom: it hands out a `&mut` sub-permission whose final state flows back
  into `self`. (A proof from a generic `&mut` struct-wrapping axiom, `wrap_mut`, was drafted and
  reverted pending a soundness review; see [wrap_mut_wip.rs](wrap_mut_wip.rs).)
- `as_untyped` and `as_untyped_mut` are proved: they borrow each element's `PointsToUntyped` and
  join the borrows two at a time with the `PointsToUntyped::join_ref` / `join_mut` axioms, since the
  new type stores no single `PointsToUntyped` to borrow. The empty case uses
  `PointsToUntyped::zero_sized` with `tracked_static_ref` / `tracked_static_mut_ref`.
- Added `PointsToUntyped::split`/`join`, which `into_untyped_with_typed_value` needed, plus the borrowed versions:
  `split_ref` (proved), `join_ref` / `join_mut` (axioms, the inverses), and `split_mut` (proved
  from `wrap_mut`, so commented out with it).
- `seq.rs` changes: added `Seq::tracked_borrow_subrange` and `Seq::tracked_split_borrow_mut`
  (`external_body`, used above); renamed `tracked_mut_borrow_subrange` to
  `tracked_borrow_subrange_mut`; removed `tracked_mut_borrow` as a duplicate of
  `tracked_borrow_mut` (see [POINTS_TO_MIGRATION.md](POINTS_TO_MIGRATION.md)).

The old `impl SeqPointsTo<u8>` is ported as `SeqPointsTo<T, PointsTo<T>>::from_untyped_with_typed_value`
(proved by induction using `split`/`join`, `PointsTo::from_untyped` and
`PointsTo::put_typed_value`).

## TODO

- [x] Audit `as_untyped_mut` and `borrow_mut`: `as_untyped_mut` now guarantees `final(self).wf()`
  under `PointsToUntyped::ptrs_len_same` (replacing the bare pointer-equality condition);
  `borrow_mut` requires `old(self).wf()` and ensures
  `ptrs_len_same_valid_decode(old, final) ==> final(self).wf()`. (Superseded: `borrow_mut` has
  since been commented out; see the `PointsTo<T>` notes above.)
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
- [x] Removed the `Tracked<...>` wrappers around `PointsTo::pt_unaligned` and
  `PointsToUnaligned::pt_untyped`, since the structs holding them are themselves `tracked`. This
  dropped the `.get()`/`.borrow()`/`.borrow_mut()` calls, the `Tracked(...)` in constructors, and the
  `@` in the closed specs `pt_untyped()`/`pt_unaligned()`. The fields are private, so there's no
  external API change. `shr_ref_struct_wrap` (now used for the `as_aligned` body) was checked
  and doesn't need a `Tracked` field.
- [ ] Port `impl<T> PointsTo<[T]>` from `raw_ptr_old.rs` (line ~754).
- [ ] Add `cast_points_to` and `cast_points_to_unaligned` in an `impl` block on `PointsTo<[T]>`,
  where they make more sense than on `SeqPointsTo`. They were drafted as axioms on
  `SeqPointsTo<T, PointsTo<T>>` and removed; the draft contract (requires `wf()`, all elements
  valid, `len * size_of::<T>() == size_of::<V>()`, plus alignment to `V` for the aligned version;
  ensures `points_to.wf()`, the same address/provenance, same bytes, and
  `value() as int == to_big_from_digits::<V, T>(value()).index(0)`) is straightforward to redo.
  They would also need the `endian` imports (`CompatibleSmallerBaseFor`, `BasePow2`,
  `to_big_from_digits`). On hold until `PointsTo<[T]>` is implemented.
- [ ] Port `PointsToRaw` (and its `impl PointsToRaw`) from `raw_ptr_old.rs` (line ~3245).
- [x] Implemented `View` for `SeqPointsTo<T, PointsTo<T>>`: it views as
  `SeqPointsToData { ptr, seq_pt }`.
- [x] Renamed `SeqPointsTo<T, PointsTo<T>>`'s `typed_value()` / `value()` to
  `seq_typed_value()` / `seq_value()`. Related names (`typed_value_equiv`, `value_subrange`,
  `is_valid_subrange`) are unchanged, and element-level calls (`self[i].value()`,
  `self[i].typed_value()`) are `PointsTo`'s and keep their names.
- [x] Renamed `PointsTo::borrow` to `borrow_value` and `SeqPointsTo::borrow_subrange` to
  `borrow_value_subrange`, paralleling `borrow_typed_value` / `borrow_typed_value_subrange`. If
  `borrow_mut` / `borrow_mut_subrange` are restored, rename them the same way
  (`borrow_value_mut` / `borrow_value_subrange_mut`).
- [ ] Possibly rename `SeqPointsTo::subrange` to `borrow_subrange` (and `subrange_mut` to
  `borrow_subrange_mut`), since they borrow a sub-permission rather than return an owned one,
  matching the `Seq::tracked_borrow_subrange` / `tracked_borrow_subrange_mut` names. The name
  `borrow_subrange` is now free (the value-borrowing function became `borrow_value_subrange`).
- [x] Renamed the `cast_to_*` typed/untyped conversions. The `into_untyped` / `from_untyped` /
  `as_untyped` / `as_untyped_mut` names already follow Rust/vstd conventions (`into_*` consumes
  `self`, `from_*` constructs `Self`, `as_*` borrows, `_mut` for the mutable version) and stay as
  they are. "Cast" is reserved for conversions that change the type of the value (like
  `cast_points_to`); converting to/from `PointsToUntyped` keeps the same bytes and only decides
  whether the typed value comes along. The new names follow the existing `value` (a guaranteed-valid
  `T`) vs `typed_value` (a possibly-empty `TypedValue<T>`) split:

  | Old | New | Carries |
  |---|---|---|
  | `PointsTo::cast_to_untyped(self)` | `PointsTo::into_untyped_with_typed_value(self)` | `TypedValue<T>` (instead of `Option<T>`) |
  | `SeqPointsTo::cast_to_untyped(self)` | `SeqPointsTo::into_untyped_with_typed_value(self)` | `Seq<TypedValue<T>>` (instead of `Seq<Option<T>>`) |
  | `PointsToUntyped::cast_to_typed(self, value)` | `PointsTo::from_untyped_with_value(untyped, value)` | `T`, always valid |
  | `PointsToUntyped::cast_to_seq_pt(self, capacity, values)` | `SeqPointsTo::from_untyped_with_typed_value(untyped, capacity, values)` | `Seq<TypedValue<T>>` for a prefix (instead of `Seq<Option<T>>`) |

  The `from_*` functions moved from `PointsToUntyped` to the type being built, like `from_untyped`.
  The asymmetry is deliberate. There is no `PointsTo::from_untyped_with_typed_value`, because
  `from_untyped` (empty) and `from_untyped_with_value` (valid) already cover both cases for a single
  value. `PointsTo::into_untyped_with_typed_value` returns a `TypedValue<T>`, so it can be called
  whether or not the permission is valid. The sequence versions use `TypedValue<T>` both ways, so
  each element can independently be valid or not.
- [ ] Move `ptrs_len_same` / `ptrs_len_same_valid_decode` and `stays_wf` into the
  `PointsToProperties` trait. What it takes:
  - Merge the two predicates under one trait name (each impl keeps its own body), and declare
    `spec fn ptrs_len_same(old: Self, new: Self) -> bool` and
    `proof fn stays_wf(old: Self, new: Self)` in the trait. Take spec arguments rather than
    `tracked` ones, so `stays_wf` can be applied to `old(..)` / `final(..)` values.
  - Implement it for `PointsToSingleton` (`new.ptr() == old.ptr()`; `stays_wf` is trivial), the
    generic `SeqPointsTo<T, P>` (same pointer and length, plus per-element `P::ptrs_len_same` and
    element pointers; `stays_wf` calls `P::stays_wf` per element), `PointsToUnaligned<T>` and
    `PointsTo<T>` (move the existing bodies). The generic `SeqPointsTo` definition subsumes both
    `PointsToUntyped::ptrs_len_same` and `SeqPointsTo<T, PointsTo<T>>::ptrs_len_same_valid_decode`.
  - The trait-level `stays_wf` can only talk about `wf_basic` (a single generic `SeqPointsTo` impl
    can't define the per-instantiation `wf`). `wf` only adds pointer conditions beyond `wf_basic`
    (metadata for `PointsToUntyped`, alignment for `SeqPointsTo<T, PointsTo<T>>`), which
    `ptrs_len_same` preserves, so keep short inherent `wf`-level `stays_wf` lemmas on those two
    types to state the full `wf` condition.
  - Remove the inherent versions and update the ~20 call sites in `points_to_permissions.rs`;
    expect some proof/trigger fixups inside the generic `SeqPointsTo` impl, where
    `P::ptrs_len_same` is opaque. Update the docs.
- [ ] Consider replacing the `ptrs_len_same_valid_decode(*old(self), *final(self))` postconditions
  on `PointsTo`'s `take`, `put`, `copy`, `take_typed_value`, `put_typed_value`,
  `copy_typed_value` and `as_untyped_mut` with a public lemma. The fact follows from `old.wf()`,
  `new.wf()` and `new.ptr() == old.ptr()`, which those functions already ensure; it is stated
  today only because it unfolds through the closed `pt_unaligned()` / `pt_untyped()`, so outside
  callers can't derive it (they need it to restore `wf()` after `SeqPointsTo::index_mut`). A lemma
  that was checked to verify:

  ```rust
  pub proof fn lemma_ptrs_len_same_valid_decode(old: Self, new: Self)
      requires old.wf(), new.wf(), new.ptr() == old.ptr(),
      ensures Self::ptrs_len_same_valid_decode(old, new),
  {
      broadcast use raw_ptr_new::group_raw_ptr_axioms;
      let ghost old_u = old.pt_unaligned().pt_untyped();
      let ghost new_u = new.pt_unaligned().pt_untyped();
      assert forall|j: int| 0 <= j < new_u.len() implies #[trigger] new_u[j].ptr() == old_u[j].ptr()
          by {
          assert(new_u[j].ptr()@.addr == old_u[j].ptr()@.addr);
          assert(new_u[j].ptr()@.provenance == old_u[j].ptr()@.provenance);
      }
  }
  ```

  The cost is that callers relying on the postcondition (inside the module: `put_subrange`,
  `put_typed_value_subrange`, `take_subrange`, `take_typed_value_subrange` and the
  `as_untyped_mut` helper; outside: anyone doing `index_mut` followed by `take`/`put`/`copy`) must
  call the lemma, with ghost snapshots of the references to name `final(..)`.
- [ ] Assess whether all the copy functions are necessary: `PointsTo::copy` / `copy_typed_value`
  and `SeqPointsTo::copy_subrange` / `copy_typed_value_subrange` (with their private helpers
  `copy_values` / `copy_typed_values`). Each is just the corresponding `put` operation applied to a
  `T: Copy` copy of a borrowed value, so callers could copy the value themselves and call `put` /
  `put_typed_value` / `put_subrange` / `put_typed_value_subrange` directly.
- [ ] Revisit `wrap_mut`, the generic `&mut` struct-wrapping axiom on `SeqPointsTo` (the `&mut`
  analogue of `shr_ref_struct_wrap`). It made `SeqPointsTo::subrange_mut` provable and gave
  `PointsToUntyped::split_mut`, but was reverted pending a soundness review. The verified code and
  restore steps are in [wrap_mut_wip.rs](wrap_mut_wip.rs); `split_mut` is commented out in place
  in `points_to_permissions.rs`.
- [ ] (On hold, if `borrow_mut` comes back) Check whether the
  `ptrs_len_same_valid_decode ==> wf()` postcondition on `PointsTo::borrow_mut` and
  `SeqPointsTo::borrow_mut_subrange` is sound and usable, since callers cannot see the inner
  pointers they would need to establish it.
- [ ] (Lower priority) Add the unaligned conversions (`as_unaligned`, `into_unaligned`, ...) to
  `SeqPointsTo<T, PointsTo<T>>`, the counterparts of the ones on `PointsTo<T>`. These can wait until
  there is a `SeqPointsTo<T, PointsToUnaligned<T>>`.
