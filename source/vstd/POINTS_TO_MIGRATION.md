# Migrating from `raw_ptr.rs`

Reference for updating code that used `vstd::raw_ptr` (the `verify-rustlib` branch's `raw_ptr.rs`)
to the new `vstd::raw_ptr_final`.
It covers the permissions (`PointsTo`, `PointsToUnaligned`, `SeqPointsTo`, `MemContents`, ...)
and the rest of `raw_ptr.rs`: the pointer and provenance model, and the trusted specs for exec pointer operations.

The design is in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md).
This doc is about what changes for callers.
`PointsToRaw` and allocation are in [POINTS_TO_RAW_MIGRATION.md](POINTS_TO_RAW_MIGRATION.md).

## 1. Where things live

`vstd::raw_ptr` is no longer built.
**Replace each `use vstd::raw_ptr::*;` (or `use crate::vstd::raw_ptr::...`) with `use vstd::raw_ptr_final::*;`**.
`raw_ptr_final/mod.rs` re-exports every module:

| What the import was for | Module |
|---|---|
| The permission types and traits: `PointsTo<T>`, `PointsToUnaligned<T>`, `SeqPointsTo<T, P>`, `PointsToUntyped`, `PointsToByte`, `TypedValue<T>`; the traits `PTPhys`, `PTProperties`, `PTTypedValue`, `PTValueOps`, `PTSizedValue` | `points_to_model` (definitions and axioms), `points_to_model::points_to_ops` (proofs) |
| The typed sequence `SeqPointsTo<T, PointsTo<T>>` | `points_to_collections` |
| The pointer and provenance model: `PtrData`, `Provenance`, `ProvenanceData`, `AllocId`, `global_alloc_id`, `ptr_addr_in_bounds`, `ptr_mut_from_data`, `ptr_from_data`, `Metadata`, `group_raw_ptr_axioms` | `ptr_model` |
| `ptr_null*`, the pointer casts, `ptr_ref` / `ptr_mut_ref` and their slice versions, `ptr_mut_ref_join`, `mut_ref_to_shr_points_to(_slice)`, `tracked_mut_ref_slice_subrange` / `_idx`, `cast_mut_ref_to_ptr` (and the slice and `str` versions), `allocate`, `deallocate` | `ptr_specs` |
| `SharedReference`, `ptr_ref2`, `ptr_ref2_ghost`, `ptr_ref2_slice_ghost` | `shared_reference` |
| `Dealloc` / `DeallocData` | removed; see [`Dealloc` → provenance](#dealloc--provenance) |
| Everything for `PointsTo<str>` | rustlib (see [section 8](#8-str)) |

`mut_ref_ptr` is a builtin and comes from the prelude.

`ptr()`, `wf()`, `typed_value()`, `bytes()`, the pointer lemmas, and most operations are **trait methods**,
so the traits must be in scope; `use vstd::raw_ptr_final::*;` brings them in.
Without them, calls like `perm.ptr()` won't resolve.

## 2. Representation

Old: `PointsToUnaligned<T>` was an `external_body` struct, and all facts about its contents came from axioms.

New: the permissions are tracked structs built on top of each other, over one primitive:

```
PointsTo<T: ?Sized>          { pt_unaligned: PointsToUnaligned<T> }                     // + aligned to T
PointsToUnaligned<T: ?Sized> { val: TypedValue<T>, pt_untyped: PointsToUntyped, metadata }
PointsToUntyped              = SeqPointsTo<u8, PointsToByte>                            // the bytes
SeqPointsTo<T, P>            { seq_pt: Seq<P>, ptr: *mut [T] }
PointsToByte                 // external_body: one byte
TypedValue<T: ?Sized>        = Empty | Valid(Tracked<T>)
```

Consequences:

* `PointsTo<T>` and `PointsToUnaligned<T>` work for `T`, `[T]` and (in rustlib) `str`.
  `T`'s pointer metadata is `()`; `[T]`'s and `str`'s is the length.
* A `PointsTo<[T]>` holds **one** `TypedValue<[T]>`: the whole slice is valid or the whole slice is empty.
  This differs from the old `PointsTo<[T]>`, which tracked each element separately.
  A sequence of independently valid-or-empty elements is a `SeqPointsTo<T, PointsTo<T>>`
  (see [section 7](#7-pointstot-or-seqpointstot-pointstot)).
* `SeqPointsTo` has two type parameters: `SeqPointsTo<T, P>`, where `P` is the element permission.
  The old `SeqPointsTo<T>` is `SeqPointsTo<T, PointsTo<T>>`.
* The untyped bytes are `PointsToUntyped`.
  It replaces `PointsToUnaligned<[u8]>` and `PointsTo<[u8]>` wherever those were used as raw bytes.
* Most operations that were axioms (`take`, `put`, `borrow`, the untyped conversions, `as_aligned`, `subrange`, ...)
  are now proofs over these fields.

## 3. Explicit `wf()` instead of a type invariant

Old permissions had a type invariant (`use_type_invariant`), so many lemmas had no precondition.
New permissions have **no type invariant**.
Well-formedness is an explicit predicate:

* `PTPhys::wf_basic()`: the pointer-level conditions (non-null, in bounds of the provenance,
  the bytes cover `Self::size(metadata)` bytes).
  The pointer lemmas (`is_nonnull`, `ptr_bounds`, `provenance_not_none`, `is_disjoint`) need only this.
* `PTTypedValue::wf()` (on `PointsTo` and `PointsToUnaligned`):
  `wf_basic()`, the alignment requirement (`satisfies_alignment`: aligned to `T` for `PointsTo`, nothing for `PointsToUnaligned`),
  and `valid_value()`: if the typed value is valid, the bytes decode to it
  and it satisfies `additional_validity_constraints` (for a slice, that its length is the metadata; for `str`, that it is valid UTF-8).
* `PointsToUntyped::wf()` is `wf_basic()`.
* `SeqPointsTo<T, PointsTo<T>>::wf()`: `wf_basic()`, aligned to `T`, and every element `wf()`.

Practical rules:

1. Functions that relied on the invariant now `require` `wf()`
   (`is_aligned`, `bytes_decode`, the untyped conversions, `borrow`, `take`, `put`, `is_disjoint_*`, ...).
2. Constructors and mutators `ensure` `wf()`.
3. Functions that hand out `&mut` to a part (`as_untyped_mut`, `as_unaligned_mut`, `as_aligned_mut`, `SeqPointsTo::index_mut`,
   `tracked_seq_pt_mut`, `subrange_mut`, `split_mut`, `as_slice_pt_mut`) ensure `final(self).wf()` only **conditionally**:
   on the part keeping its pointers and length (`ptrs_len_same`)
   and, for typed values, still satisfying its validity constraints (`ptrs_len_same_valid_value`).
   Often Verus proves the condition automatically; otherwise establish it on the `final(...)` of the borrowed part.
4. To establish the condition, use the lemmas for two well-formed permissions with the same pointer:
   `PTTypedValue::lemma_ptrs_len_same_valid_value` (for `PointsTo` / `PointsToUnaligned`),
   `PointsToUntyped::lemma_ptrs_len_same_untyped`,
   and `SeqPointsTo<T, PointsTo<T>>::lemma_ptrs_len_same_valid_value`.
   The first two are broadcast in `group_vstd_default` (through `group_points_to_lemmas`).
   **The sequence lemma is not**: add `broadcast use group_points_to_collections_lemmas;` where needed.
5. `stays_wf(old, new)` turns `old.wf()` plus `ptrs_len_same_valid_value(old, new)` into `new.wf()`.
6. Carry `perm.wf()` through your own specs and invariants where you relied on the type invariant.

## 4. Renames

### Types and variants

| Old | New |
|---|---|
| `MemContents<T>` | `TypedValue<T>` |
| `MemContents::Init(v)` | `TypedValue::Valid(Tracked(v))` (in specs, write `x.is_valid() && x.value() == v`, since `Tracked(v)` can't be built in spec code) |
| `MemContents::Uninit` | `TypedValue::Empty` |
| `PointsToUnaligned<[u8]>` / `PointsTo<[u8]>` as raw bytes | `PointsToUntyped` |
| `SeqPointsTo<T>` | `SeqPointsTo<T, PointsTo<T>>` |
| `PointsToData { ptr, mem_contents, abstract_bytes }` | `PointsToData { ptr, value, bytes }` |
| `Provenance` (enum) | `Provenance = Option<ProvenanceData>` |

### Spec functions and lemmas

| Old | New |
|---|---|
| `mem_contents()` | `typed_value()` |
| `is_init()` / `is_uninit()` | `is_valid()` / `is_empty()` |
| `abstract_bytes()` | `bytes()` |
| `abstract_bytes_decode` | `bytes_decode` (requires `wf()`) |
| `provenance_non_null` | `provenance_not_none` (requires `Self::size(metadata) != 0`) |
| `value()` | unchanged for `Sized` `T`; for `[T]` and `str`, `typed_value().value_ref()` (a `&[T]` / `&str`; use `@` for the `Seq<T>`) |
| `ptr()` | unchanged, now `PTPhys::ptr` |
| `Provenance::data()` | `Option::unwrap()` |
| `Provenance::is_some()` / `is_none()` | the `Option` methods |
| `alloc_bound`, `prov_alignment`, `start_addr_aligned`, `is_nonnull` (provenance axioms) | all in the broadcast axiom `provenance_properties` |

`value` means a valid value and `typed_value` a possibly-empty `TypedValue`
(for example `take` vs `take_typed_value`).

### `SeqPointsTo`

| Old | New |
|---|---|
| `seq_perm()` | `seq_pt()` |
| `ptr()` (`*mut T`) | `thin_ptr()` (`*mut T`); `ptr()` is now the `*mut [T]` with the length as metadata |
| `mem_contents()` | `seq_typed_value()` |
| `value()` | `seq_value()` |
| `abstract_bytes()` / `abstract_bytes_inner` | `bytes()` / `bytes_inner` |
| `tracked_perm_seq` / `tracked_perm_seq_mut` | `tracked_seq_pt` / `tracked_seq_pt_mut` |
| `borrow_mut(i)` | `index_mut(i)` |
| `mem_contents_equiv` | `typed_value_equiv` |
| `abstract_bytes_len` / `abstract_bytes_equiv` / `abstract_bytes_decode` | `bytes_len` / `bytes_equiv` / `bytes_decode` |
| `is_init`, `is_uninit`, `is_fully_uninit` | `is_valid`, `is_empty` ("not all valid"), `is_fully_empty` |
| `cast_to_untyped` | `into_untyped_with_typed_value` |
| `SeqPointsTo<u8>::cast_to_typed` | `SeqPointsTo<T, PointsTo<T>>::from_untyped_with_typed_value` |
| `constants` (broadcast) | no equivalent |

**Ranges are `(start, end)`, not `(start, len)`**:
`is_valid_subrange(start, end)`, `value_subrange(start, end)`, `subrange(start, end)`, `subrange_mut(i, j)`,
and the `borrow_*` / `take_*` subrange operations below
(`put_*` and `copy_*` take a start index and the values).

### `Seq` tracked borrows (`seq.rs`)

| Old | New |
|---|---|
| `tracked_mut_borrow(i)` | `tracked_borrow_mut(i)` (same facts, stated with `update`) |
| `tracked_mut_borrow_subrange(i, j)` | `tracked_borrow_subrange_mut(i, j)` |
| (new) | `tracked_borrow_subrange(i, j)`: borrows a subrange of a borrowed `Seq` |
| (new) | `tracked_split_borrow_mut(mid)`: splits a `&mut Seq` in two at `mid` |

### `Dealloc` → provenance

`Dealloc` and `DeallocData` are gone: they're folded into the provenance model.
`ProvenanceData` records the originally requested size as `orig_size()`.
Read the facts off the pointer's provenance (`ptr@.provenance.unwrap()`):

| Old (`Dealloc`) | New (`ProvenanceData`) |
|---|---|
| `size()` | `orig_size()` |
| `addr()` | `start_addr()` |
| `align()` | `alignment()` |
| `provenance()` | the pointer's own `ptr@.provenance` |
| `in_bounds` (`size <= alloc_len`) | `provenance_properties` (`orig_size() <= alloc_len()`) |
| `empty()` | not needed: `None` provenance carries no allocation |
| `provenance_non_null` | not needed: `orig_size()` is only defined on a `Some` provenance |
| `is_disjoint` | dropped (no callers) |

## 5. `PointsTo` and `PointsToUnaligned`

These hold for `T`, `[T]` and `str` unless the table says otherwise.
"Proved" means it was an `axiom fn` in `raw_ptr.rs` and is a `proof fn` now.

### The pointer lemmas (`PTProperties`)

| Old | New |
|---|---|
| `is_nonnull`, `ptr_bounds`, `provenance_non_null` | trait methods `is_nonnull`, `ptr_bounds`, `provenance_not_none`; require `wf_basic()`. `ptr_bounds` is stated with `Self::size(metadata)`. |
| `is_disjoint<S>` | trait method `is_disjoint` against any permission (`PTPhys`); or the specialized `is_disjoint_pointsto<S>` / `is_disjoint_unaligned<S>` (sized `T`). Requires `wf_basic()` (the specialized ones `wf()`). |
| `is_aligned` | `PointsTo<T>::is_aligned` (sized `T`); requires `wf()` |

### Values (`PTValueOps`, `PTSizedValue`)

| Old | New |
|---|---|
| `borrow` | `borrow` (proved); requires `wf()` and validity |
| `take`, `put` | `take`, `put` (proved, sized `T` only); require and ensure `wf()` |
| `borrow_mut` (`&mut T`) | `PointsTo<T>::borrow_mut` (axiom, sized `T`); requires `wf()` and validity, ensures `final(self).wf()` |
| (new) | `borrow_typed_value`, `take_typed_value`, `put_typed_value`: the `TypedValue` versions; don't require validity |
| (new) | `copy`, `copy_typed_value` (sized `T: Copy`) |
| `zero_sized(ptr)` | `zero_sized(ptr)`: a trait method now, for any `T` whose `Self::size(metadata)` is 0. Requires `ptr_addr_in_bounds(ptr)` and alignment. |

### Untyped conversions (`PTValueOps`)

All take or produce a `PointsToUntyped` and require `wf()`.
The untyped permission's pointer is a `*mut [u8]` with the address and provenance of `self.ptr()`
and metadata `Self::size(self.ptr()@.metadata)`.

| Old | New |
|---|---|
| `cast_to_untyped` | `into_untyped_with_typed_value`, returning `(PointsToUntyped, TypedValue<T>)` |
| `from_untyped(raw)` | `from_untyped(pt_untyped, metadata)` (proved); `metadata` is `()` for sized `T`. Requires `pt_untyped.len() == Self::size(metadata)` and alignment. Ensures an empty, `wf()` permission. |
| `PointsTo<[u8]>::cast_to_typed<T>(value)` | `PointsTo::<T>::from_untyped_with_value(pt_untyped, value)` (sized `T`) |
| `PointsTo<[u8]>::cast_to_typed_uninit<T>` | `PointsTo::<T>::from_untyped(pt_untyped, ())` |
| (new) | `from_untyped_with_typed_value(pt_untyped, typed_value, metadata)`: the inverse of `into_untyped_with_typed_value` |
| `into_untyped`, `as_untyped` | `into_untyped`, `as_untyped` (proved) |
| `as_untyped_mut` | `as_untyped_mut` (proved). Drops the typed value; `final(self)` is empty, with the borrow's final bytes. `final(self).wf()` holds if the borrow keeps its pointers and length. |

### Aligned ↔ unaligned

| Old | New |
|---|---|
| `into_unaligned`, `as_unaligned` | same names; require `wf()`, ensure the result's `wf()` |
| (new) | `as_unaligned_mut` |
| `into_aligned` | `into_aligned`; requires `wf()` and `PointsTo::<T>::satisfies_alignment(addr)` |
| `as_aligned` | `as_aligned` (proved) |
| `PointsToUnaligned<[T]>::as_aligned_mut` | `as_aligned_mut` (for any `T`) |

### Accessors

`tracked_pt_unaligned` (on `PointsTo`), `tracked_pt_untyped` and `tracked_typed_value` (on `PointsToUnaligned`)
expose the inner parts without `wf()` clauses;
`self.wf()` implies the inner part's `wf()`.
`into_raw_parts`, `from_raw_parts` and `as_raw_parts_mut` take a `PointsToUnaligned` apart and rebuild it;
they say nothing about `wf()`.

### `PointsToUntyped`

| Function | Notes |
|---|---|
| `bytes()`, `len()`, `wf()` | `wf()` is `wf_basic()`, which includes `ptr()@.metadata == len()` |
| `zero_sized<T>(ptr)` | replaces `PointsToUnaligned<[u8]>::zero_sized<T>` |
| `split(mid)`, `join(other)` | in bytes |
| `split_ref(mid)`, `split_mut(mid)` | the borrowed versions of `split` |
| `join_ref(other)`, `join_mut(other)` | axioms; join two borrowed halves into one borrow |
| `is_disjoint_untyped`, `stays_wf`, `lemma_ptrs_len_same_untyped` | see [section 3](#3-explicit-wf-instead-of-a-type-invariant) |

## 6. `SeqPointsTo`

`SeqPointsTo<T, P>` is generic over the element permission `P`:
`PointsToUntyped` (elements `PointsToByte`) and the typed sequence `SeqPointsTo<T, PointsTo<T>>` share one definition.

### `wf()`

The old `wf()` demanded per-element provenance and address, `Some` provenance when non-empty,
the whole range in bounds, non-null, and aligned.
The new `wf()` demands per-element provenance and address, each element `wf()`,
`ptr()@.metadata == len()`, non-null, the base address in bounds, and aligned.
"Provenance is `Some`" and "the whole range is in bounds" are no longer part of `wf()`:
call `provenance_not_none` and `ptr_bounds` for them.

### Functions on `SeqPointsTo<T, PointsTo<T>>`

| Function | Notes |
|---|---|
| `from_seq(perms, ptr)`, `into_seq`, `empty(ptr)` | `from_seq` takes the base `*mut T` and ensures `wf_basic()`; requires `ptr_addr_in_bounds(ptr)` |
| `tracked_seq_pt`, `tracked_seq_pt_mut`, `index_mut(i)` | the `&mut` ones give `final(self).wf_basic()` conditionally (not `wf()`): re-establish each element's `wf()` with `stays_wf` |
| `zero_sized(ptr, length)` | ensures `wf()` |
| `split(mid)`, `join(other)` | ensure `wf()` and relate the bytes |
| `subrange(start, end)` | proved (shared); `(start, end)` instead of `(start, len)` |
| `subrange_mut(i, j)` | proved; `final(self).wf()` if the sub-permission satisfies `ptrs_len_same_valid_value` |
| `borrow_typed_value_subrange`, `take_typed_value_subrange`, `put_typed_value_subrange`, `copy_typed_value_subrange` | replace the `*_mem_contents_subrange` functions; use `Seq<TypedValue<T>>` (`borrow` and `copy` use `Seq<&TypedValue<T>>`) |
| `borrow_subrange`, `take_subrange`, `put_subrange`, `copy_subrange` | the `T` versions (the range must be valid); `Seq<&T>` / `Seq<T>` |
| `borrow_mut_subrange(start, end)` | a `Seq<&mut T>` of a valid range |
| `into_untyped_with_typed_value` | replaces `cast_to_untyped`; returns the `PointsToUntyped` and `seq_typed_value()` |
| `from_untyped_with_typed_value(pt_untyped, capacity, typed_value)` | replaces `SeqPointsTo<u8>::cast_to_typed`; `typed_value` may be a prefix |
| `into_untyped`, `from_untyped(pt_untyped, len)`, `as_untyped`, `as_untyped_mut` | proved |
| `as_slice_pt`, `as_slice_pt_mut` | borrow as a `PointsTo<[T]>`; see [section 7](#7-pointstot-or-seqpointstot-pointstot) |
| `bytes_decode`, `is_aligned`, `is_disjoint_seqpt<S>`, `stays_wf`, `lemma_ptrs_len_same_valid_value` | require `wf()` |

## 7. `PointsTo<[T]>` or `SeqPointsTo<T, PointsTo<T>>`

Both exist. Pick by what the code needs:

| | `PointsTo<[T]>` | `SeqPointsTo<T, PointsTo<T>>` |
|---|---|---|
| Validity | all valid or all empty | each element independently |
| Real `&[T]` / `&mut [T]` | yes: `ptr_ref_slice`, `ptr_mut_ref_slice`, `borrow` (ghost `&[T]`) | no |
| From a `&[T]` / `&mut [T]` | yes: `SharedReference<[T]>::points_to`, `mut_ref_to_shr_points_to_slice` | no |
| Element access | `borrow_index(i)` (shared) | `self[i]`, `index_mut(i)`, the `*_subrange` operations |
| Subranges, split, join | no | yes |
| Pointer | `*mut [T]`; `len()` is the metadata | `ptr()` is `*mut [T]`, `thin_ptr()` the base |
| Typical use | slices that came from Rust references, and values read through them | buffers being filled or partly initialized (for example `Vec`'s spare capacity) |

**Converting.** `SeqPointsTo::as_slice_pt` / `as_slice_pt_mut` borrow a sequence as a `PointsTo<[T]>`.
If any element is empty, the slice permission is empty.
When the `&mut` borrow ends, a valid slice value of the same length goes back to the elements;
otherwise every element ends empty.
There is **no slice → sequence conversion**; use `borrow_index` for one element.
A `PointsTo<[T]>` can also be borrowed from a `&PointsToUntyped` with
`PointsTo::<[T]>::from_untyped_ref(pt_untyped, len)` (empty) or `from_untyped_with_value_ref(pt_untyped, value)` (valid).

### Old `PointsTo<[T]>` functions

| Old | New |
|---|---|
| `mem_contents_seq()`, `self[i]` (a `MemContents<T>`) | none on `PointsTo<[T]>` (one `TypedValue<[T]>`); use `typed_value().value_ref()@[i]` when valid, or a `SeqPointsTo` |
| `len()` | `len()` |
| `is_init()`, `is_uninit()` | `is_valid()`, `is_empty()` |
| `is_init_subrange`, `is_fully_uninit`, `value_subrange` | on `SeqPointsTo` only |
| `value()` | `typed_value().value_ref()@` |
| `abstract_bytes()`, `abstract_bytes_decode` | `bytes()`, `bytes_decode` |
| `is_nonnull`, `ptr_bounds`, `provenance_non_null`, `is_disjoint` | the `PTProperties` methods |
| `into_unaligned`, `as_unaligned` | same names (generic) |
| `from_untyped(raw, len)`, `as_untyped`, `as_untyped_mut` | `from_untyped(pt_untyped, len)`, `as_untyped`, `as_untyped_mut` (generic) |
| `tracked_borrow` (`&[T]`) | `borrow` |
| `tracked_borrow_mut` (`&mut [T]`) | none in ghost code; in exec code, `ptr_mut_ref_slice` |
| `subrange(start, len)` | none on `PointsTo<[T]>`; `SeqPointsTo::subrange(start, end)` |
| `into_seq_pt`, `into_seq_pt_shared` | none (no slice → sequence conversion) |
| `cast_points_to<V>`, `cast_points_to_unaligned<V>` | none |
| `*_mem_contents_subrange`, `put_subrange` | on `SeqPointsTo` only |
| `seq_into_slice_shared`, `seq_into_slice_mut` | `SeqPointsTo::as_slice_pt`, `as_slice_pt_mut` |
| `seq_into_slice` (owned) | none |

### `PointsToUnaligned<[T]>`

The generic operations (untyped conversions, `as_aligned(_mut)`, `into_aligned`) and `borrow_index`,
`from_untyped_ref`, `from_untyped_with_value_ref` exist.
`subrange`, `cast_points_to*` and `into_seq_pt*` have no replacement.

## 8. `str`

`PointsTo<str>` and `PointsToUnaligned<str>` are written in **rustlib**, not vstd
(rustlib's `str` view is its bytes).
Their specs are in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#rustlib-str).

* The metadata is the byte length, and the value is `typed_value().value_ref()` (a `&str`).
* `wf()` includes UTF-8 validity (`str::inv`).
* The shared casts are `PointsTo<str>::as_bytes` (to `&PointsTo<[u8]>`)
  and `PointsTo<str>::from_bytes_ref` (from `&PointsTo<[u8]>`, given valid UTF-8);
  they replace `cast_to_u8_shared` and `cast_to_str_shared`.
  There are no owned or `&mut` casts.
* The reference helpers (`ptr_ref_str`, `ptr_mut_ref_str`, `ptr_ref2_str_ghost`, `SharedReference<str>::points_to`,
  `mut_ref_to_shr_points_to_str`) are rustlib axioms with the new API.
* The old `PointsTo<str>` methods (`ptr_bounds`, `is_disjoint`, ...) are the trait methods.
  `subrange` and `axiom_pt_str_len` have no replacement.

## 9. Allocation

`allocate(size, align)` returns a `PointsToUntyped` for the new allocation, with a global-allocator provenance
(`alloc_id() == global_alloc_id()`, `orig_size() == alloc_len() == size`).
`deallocate(ptr, size, align, perm)` takes back a `PointsToUntyped` covering the whole allocation.
See [POINTS_TO_RAW_MIGRATION.md](POINTS_TO_RAW_MIGRATION.md).

## 10. What is not available

* On `PointsTo<[T]>`: per-element validity, `subrange`, `cast_points_to` / `cast_points_to_unaligned`,
  a ghost `&mut [T]`, and conversion to a `SeqPointsTo` (see [section 7](#7-pointstot-or-seqpointstot-pointstot)).
* `seq_into_slice` (owned) and `SeqPointsTo<T, PointsToUnaligned<T>>`.
* Owned or `&mut` `str` ↔ `[u8]` permission casts.

## 11. Checklist

1. Replace `use vstd::raw_ptr::*;` with `use vstd::raw_ptr_final::*;` ([section 1](#1-where-things-live)).
2. Rename per [section 4](#4-renames).
   Ranges change from `(start, len)` to `(start, end)`, and `SeqPointsTo::ptr()` is now a `*mut [T]` (use `thin_ptr()` for the base).
3. Replace raw-byte uses of `PointsToUnaligned<[u8]>` / `PointsTo<[u8]>` with `PointsToUntyped`,
   and update the untyped conversions ([section 5](#untyped-conversions-ptvalueops)).
4. For each `PointsTo<[T]>` and `SeqPointsTo<T>`, decide which of the two the code needs ([section 7](#7-pointstot-or-seqpointstot-pointstot)).
5. Add `wf()` to specs and invariants that relied on the type invariant,
   and discharge the conditional `final(...).wf()` after `&mut` borrows ([section 3](#3-explicit-wf-instead-of-a-type-invariant)).
6. Where code used `SeqPointsTo::wf()` for "provenance is `Some`" or "the whole range is in bounds",
   call `provenance_not_none` / `ptr_bounds`.
7. Replace `Dealloc` with the provenance's `orig_size()` and friends.
