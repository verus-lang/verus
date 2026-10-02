# Axioms in `points_to_permissions.rs`

All `axiom fn`s in [points_to_permissions.rs](points_to_permissions.rs), split by whether they
convert a shared (`&`) or mutable (`&mut`) borrow, then grouped by impl block.

## `&` conversions

### `PointsToUnaligned<T>`

1. [`as_aligned`](points_to_permissions.rs#L810): if the pointer address is aligned for `T`,
   borrows `&self` as a `&PointsTo<T>` with the same view. There's a commented-out body
   (`shr_ref_struct_wrap`) waiting on a merge from main, so this is only temporarily an axiom.

### `SeqPointsTo<T, PointsTo<T>>`

2. [`as_untyped`](points_to_permissions.rs#L1875): shared-borrows the sequence as a
   `&PointsToUntyped`. Same address and provenance, length `len * size_of::<T>()`, same bytes.
3. [`subrange`](points_to_permissions.rs#L1920): shared-borrows the sub-permission for `len`
   elements starting at `start_index`. The pointer is offset by `start_index * size_of::<T>()`, and
   the sequence of permissions and the bytes are restricted to that range.
4. [`borrow_typed_value_subrange`](points_to_permissions.rs#L1941): shared-borrows
   `typed_value().subrange(start, end)` as a `&Seq<TypedValue<T>>`.
5. [`cast_points_to<V>`](points_to_permissions.rs#L2152): reinterprets a valid sequence of a
   smaller integer type `T` as a `&PointsTo<V>` for a larger power-of-2 integer type `V`. Requires
   alignment to `V` and total size equal to `size_of::<V>()`. The value is given by
   `to_big_from_digits`; bytes are unchanged. TODO to prove it later.
6. [`cast_points_to_unaligned<V>`](points_to_permissions.rs#L2180): same as `cast_points_to`, but
   with no alignment requirement, returning a `&PointsToUnaligned<V>`. TODO to prove it later.

## `&mut` conversions

### `PointsTo<T>`

7. [`borrow_mut`](points_to_permissions.rs#L1296): mutably borrows the `T` held by a valid
   permission. `mut_ref_ptr(val) == self.ptr()` connects the reference to the raw pointer, and the
   final value matches what's written through `val`. It's an axiom because that pointer connection
   can't be built by borrowing from a ghost value. Has a `// TODO: is this right/sound?` on the
   line that says when `wf` is restored.

### `SeqPointsTo<T, PointsTo<T>>`

8. [`as_untyped_mut`](points_to_permissions.rs#L1895): mutable version of `as_untyped`. Any typed
   values are dropped. If the raw permission's pointer and length are unchanged, `self` comes back
   fully empty and well-formed, with the raw permission's final bytes.
9. [`subrange_mut`](points_to_permissions.rs#L2330): mutably borrows the sub-permission for
   indices `[i, j)`, with the pointer offset by `i * size_of::<T>()`. If the sub-permission stays
   well-formed with the same pointer and length, `self` stays well-formed with that slice replaced
   by the final sub-permission.
