# Axioms in `points_to_permissions.rs`

All `axiom fn`s in [points_to_permissions.rs](points_to_permissions.rs), split by whether they
convert a shared (`&`) or mutable (`&mut`) borrow, then grouped by impl block.

## `&` conversions

### `PointsToUnaligned<T>`

1. [`as_aligned`](points_to_permissions.rs#L809): if the pointer address is aligned for `T`,
   borrows `&self` as a `&PointsTo<T>` with the same view. There's a commented-out body
   (`shr_ref_struct_wrap`) waiting on a merge from main, so this is only temporarily an axiom.

### `SeqPointsTo<T, PointsTo<T>>`

2. [`as_untyped`](points_to_permissions.rs#L1996): shared-borrows the sequence as a
   `&PointsToUntyped`. Same address and provenance, length `len * size_of::<T>()`, same bytes.
3. [`subrange`](points_to_permissions.rs#L2051): shared-borrows the sub-permission for `len`
   elements starting at `start_index`. The pointer is offset by `start_index * size_of::<T>()`, and
   the sequence of permissions is restricted to that range (so the bytes are too, since `bytes` is
   defined from `seq_pt`; `bytes_subrange_equiv` relates them to a subrange of `self.bytes()`).
4. [`borrow_typed_value_subrange`](points_to_permissions.rs#L2070): shared-borrows
   `typed_value().subrange(start, end)` as a `&Seq<TypedValue<T>>`.
5. [`borrow_subrange`](points_to_permissions.rs#L2352): shared-borrows the values in `[start, end)`
   as a `&Seq<T>`. Requires the range to be valid; the result is
   `value_subrange(start, end - start)`.

### `PointsTo<[T]>`

These are on hold and not currently in the file. They will land here once `PointsTo<[T]>` exists.

6. `cast_points_to<V>`: reinterprets a valid sequence of a
   smaller integer type `T` as a `&PointsTo<V>` for a larger power-of-2 integer type `V`. Requires
   alignment to `V` and total size equal to `size_of::<V>()`. The value is given by
   `to_big_from_digits`; bytes are unchanged. TODO to prove it later.
7. `cast_points_to_unaligned<V>`: same as `cast_points_to`, but
   with no alignment requirement, returning a `&PointsToUnaligned<V>`. TODO to prove it later.

## `&mut` conversions

### `PointsTo<T>`

8. [`borrow_mut`](points_to_permissions.rs#L1291): mutably borrows the `T` held by a valid
   permission. `mut_ref_ptr(val) == self.ptr()` connects the reference to the raw pointer, and the
   final value matches what's written through `val`. It's an axiom because that pointer connection
   can't be built by borrowing from a ghost value. Has a `// TODO: is this right/sound?` on the
   line that says when `wf` is restored.

### `SeqPointsTo<T, PointsTo<T>>`

9. [`as_untyped_mut`](points_to_permissions.rs#L2025): mutable version of `as_untyped`. Any typed
   values are dropped. If the raw permission's pointer and length are unchanged, `self` comes back
   fully empty and well-formed, with the raw permission's final bytes.
10. [`borrow_mut_subrange`](points_to_permissions.rs#L2365): mutable version of `borrow_subrange`,
    borrowing the values in a valid range `[start, end)` as a `&mut Seq<T>`. The pointer, length
    and per-element pointers of `self` stay the same. If the borrowed `Seq<T>` keeps its length,
    the final `typed_value()` has that range replaced by the final values. Unlike `borrow_mut`, it
    has no `mut_ref_ptr` postcondition. Like `borrow_mut`, `wf` is restored only under
    `ptrs_len_same_valid_decode`, with the same `// TODO: is this right/sound?`.
11. [`subrange_mut`](points_to_permissions.rs#L2522): mutably borrows the sub-permission for
    indices `[i, j)`, with the pointer offset by `i * size_of::<T>()`. If the sub-permission stays
    well-formed with the same pointer and length, `self` stays well-formed with that slice replaced
    by the final sub-permission.
