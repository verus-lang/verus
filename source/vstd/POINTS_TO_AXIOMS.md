# Axioms in `points_to_permissions.rs`

All `axiom fn`s in [points_to_permissions.rs](points_to_permissions.rs), split by whether they
convert a shared (`&`) or mutable (`&mut`) borrow, then grouped by impl block.

## `&` conversions

### `PointsToUntyped`

1. `join_ref`: joins shared borrows `self` and `other` into a single `&'a PointsToUntyped`, under
   the same conditions as `join` (both `wf()`, same provenance, `other` starting where `self`
   ends). Ensures the result holds `self.seq_pt() + other.seq_pt()` (so its bytes are
   `self.bytes() + other.bytes()`), starts at `self`'s address with length
   `self.len() + other.len()`, and is `wf()`. It's the shared-borrow analogue of `join`, and an axiom
   because the joined permission isn't stored anywhere to borrow. `SeqPointsTo::as_untyped` is
   proved from it.

### `PointsTo<[T]>`

These are on hold and not currently in the file. They will land here once `PointsTo<[T]>` exists.

2. `cast_points_to<V>`: reinterprets a valid sequence of a
   smaller integer type `T` as a `&PointsTo<V>` for a larger power-of-2 integer type `V`. Requires
   alignment to `V` and total size equal to `size_of::<V>()`. The value is given by
   `to_big_from_digits`; bytes are unchanged. TODO to prove it later.
3. `cast_points_to_unaligned<V>`: same as `cast_points_to`, but
   with no alignment requirement, returning a `&PointsToUnaligned<V>`. TODO to prove it later.

## `&mut` conversions

### `PointsToUntyped`

4. `join_mut`: the mutable-borrow analogue of `join_ref`, with the same requires and the same
   ensures about the joined permission. In addition, if the joined permission keeps its pointers
   and length, then so do `self` and `other` (and both are `wf()`), and their final `seq_pt`s
   (and bytes) concatenate to the joined permission's final ones. `SeqPointsTo::as_untyped_mut` is proved from it.

### `PointsTo<T>`

5. `borrow_mut` (**commented out** for now, as not essential; `borrow_mut_subrange` and its
   helper are commented out with it): mutably borrows the `T` held by a valid
   permission. The final permission is valid with the value written through the reference, keeps
   its pointer, satisfies `ptrs_len_same_valid` and is `wf()` unconditionally. So the
   final bytes are whatever encoding of the new value is in memory. It's an axiom because the
   bytes live in separate ghost state from the `TypedValue<T>`, so a borrow of the value alone
   can't update them. The `mut_ref_ptr(val) == self.ptr()` postcondition is commented out
   (Travis: not necessarily true because of `Box`/enum, and not obviously needed).

### `SeqPointsTo<T, PointsTo<T>>`

6. `subrange_mut`: mutably borrows the sub-permission for indices `[i, j)`, with the pointer
   offset by `i * size_of::<T>()`. If the sub-permission stays well-formed with the same pointer
   and length, `self` stays well-formed with that slice replaced by the final sub-permission.
   (It could be proved from a generic `&mut` struct-wrapping axiom on `SeqPointsTo`, the `&mut`
   analogue of `shr_ref_struct_wrap`; that was tried and reverted pending a soundness review.
   `PointsToUntyped::split_mut`, which used the same axiom, is commented out.)

## Axioms outside this file that proofs here rely on

- `Seq::tracked_borrow_subrange` in [seq.rs](seq.rs) (`external_body`): shared-borrows
  `self.subrange(i, j)` as a `&Seq`. It's the shared counterpart of the existing
  `Seq::tracked_borrow_subrange_mut`. `PointsToUntyped::split_ref` and `SeqPointsTo::subrange` are proved from it plus the
  `shr_ref_struct_wrap` builtin, which wraps the borrowed `&Seq<PointsTo<T>>` in a `&SeqPointsTo`
  (its other field, `ptr`, is a `Ghost`).
- `Seq::tracked_split_borrow_mut` in [seq.rs](seq.rs) (`external_body`): splits a `&mut Seq` into
  `&mut` borrows of `take(mid)` and `skip(mid)`, with `final(self)` equal to the concatenation of
  their finals. It's the `Seq` analogue of `Map::tracked_borrow_mut_split`. Used by
  `SeqPointsTo::as_untyped_mut` (and by the commented-out `borrow_mut_subrange` and
  `PointsToUntyped::split_mut`).
- `tracked_static_mut_ref` in [modes.rs](modes.rs) (existing vstd axiom; `tracked_static_ref` is
  proved from it): turns an owned tracked value into a `'static` reference. `as_untyped` and
  `as_untyped_mut` use it for the empty case, wrapping a `PointsToUntyped::zero_sized` permission,
  since there's no element borrow to start the joins from.
