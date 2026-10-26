# Migrating `PointsToRaw` and allocation

For code that used `PointsToRaw`, `Dealloc`, `allocate` or `deallocate` from vstd's original `raw_ptr.rs`
(kept as `raw_ptr_old.rs`).
The rest of the permission API is covered in [POINTS_TO_MIGRATION.md](POINTS_TO_MIGRATION.md).
Everything here is in `vstd::raw_ptr_final` (`PointsToRaw` in `points_to_collections`, `allocate` / `deallocate` in `ptr_specs`).

## `PointsToRaw`

Still a permission to an arbitrary set of addresses with one provenance.
It was an `external_body` struct; it's now a map from addresses to `PointsToByte` permissions,
and everything except the byte primitive is proved.
It doesn't implement the permission traits (it has no single pointer).

| Old | New |
|---|---|
| `provenance()`, `dom()`, `is_range`, `contains_range` | unchanged |
| (new) | `byte(a)`, `bytes_range(start, len)`: the abstract bytes are now visible |
| `empty(provenance)` | unchanged |
| `split(range)`, `join(other)` | unchanged; now also ensure each part keeps its bytes |
| `ptr_bounds` | no longer requires `provenance().is_some()`; the upper bound is now strict (`a < start_addr() + alloc_len()`) |
| `provenance_non_null` | `provenance_not_none` |
| `is_disjoint` | unchanged |
| `into_typed::<V>(start)` | `into_untyped(start, size_of::<V>())`, then `PointsTo::<V>::from_untyped(pt_untyped, ())` |
| `into_typed_slice::<V>(start, length)` | `into_untyped(start, length * size_of::<V>())`, then `PointsTo::<[V]>::from_untyped(pt_untyped, length)` |
| `into_typed_seq::<V>(start, length)` | `into_untyped(start, length * size_of::<V>())`, then `SeqPointsTo::<V, PointsTo<V>>::from_untyped(pt_untyped, length)` |
| `PointsTo<V>::into_raw`, `PointsTo<[V]>::into_raw`, `SeqPointsTo<V>::into_raw` | `into_untyped()`, then `PointsToRaw::from_untyped(pt_untyped)`. The typed value, if any, is dropped (the old `PointsTo<V>::into_raw` required it to be empty). |
| `PointsToRaw::empty(p).into_typed::<V>(addr)` for a ZST | `PointsTo::<V>::zero_sized(ptr)` (or `PointsToUntyped::zero_sized`) |

`into_untyped(start, len)` requires `is_range(start, len)` and `start != 0`
(the old `into_typed` also accepted `start == 0` for non-zero sizes;
a non-empty `PointsToRaw`'s addresses are non-zero, by `ptr_bounds` and `provenance_properties`).
For `len == 0` with a `Some` provenance, `start` must also be in bounds of the provenance.
The typed constructors then require the address to be aligned to `V`.

## Allocation

| Old | New |
|---|---|
| `allocate(size, align) -> (*mut u8, Tracked<PointsToRaw>, Tracked<Dealloc>)` | `allocate(size, align) -> (*mut u8, Tracked<PointsToUntyped>)`. Use `PointsToRaw::from_untyped` if you want a `PointsToRaw`. |
| `deallocate(p, size, align, Tracked<PointsToRaw>, Tracked<Dealloc>)` | `deallocate(ptr, size, align, Tracked<PointsToUntyped>)`. Use `PointsToRaw::into_untyped(start, len)` to get one back. |
| `Dealloc` | removed; its facts are on the pointer's provenance (`orig_size()`, `start_addr()`, `alignment()`); see [`Dealloc` → provenance](POINTS_TO_MIGRATION.md#dealloc--provenance) |

`allocate` ensures the allocation's provenance has `alloc_id() == global_alloc_id()`,
`orig_size() == alloc_len() == size` and `alignment() == align`,
and that the pointer is at its `start_addr()`.
`deallocate` requires a `PointsToUntyped` covering the whole allocation, with matching `size` (`orig_size()`) and `align`.
