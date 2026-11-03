# Approved: `PTValueOps` trait and typed `SeqPointsTo` (level 3)

Designs and specifications that have been reviewed and approved.
Any change here, including to documentation, needs to be flagged for re-approval.
What is still under review is in [TYPED_POINTS_TO_PLAN.md](TYPED_POINTS_TO_PLAN.md).

## Permission types after all phases

| Type | `A` | Pointer metadata | `size(metadata)` | Traits | Holds |
|---|---|---|---|---|---|
| `PointsToByte` (renamed from `PointsToSingleton`) | `u8` | `()` | `1` | `PTPhys`, `PTProperties` | one abstract byte (axiomatized, as today) |
| `PointsToUntyped` = `SeqPointsTo<u8, PointsToByte>` | `[u8]` | length | `len` | `PTPhys`, `PTProperties` | a sequence of byte permissions |
| `PointsToUnaligned<T>` | `T` | `()` | `size_of::<T>()` | the above + `PTTypedValue` + `PTValueOps` + `PTSizedValue` | untyped bytes, a `TypedValue<T>`, and the ghost metadata |
| `PointsToUnaligned<[T]>` | `[T]` | length | `len * size_of::<T>()` | the above, without `PTSizedValue` | the same, with a `TypedValue<[T]>` |
| `PointsToUnaligned<str>` (rustlib) | `str` | byte length | `len` | as for `[T]` | the same, with a `TypedValue<str>` |
| `PointsTo<X>` (for each `X` above) | `X` | as above | as above | as for `PointsToUnaligned<X>` | a `PointsToUnaligned<X>` at an aligned address |
| `SeqPointsTo<T, P>`, `P: PTProperties<A = T>` | `[T]` | length | `len * P::size(())` | `PTPhys`, `PTProperties` | one element permission `P` per element |
| `PointsToRaw` | — | — | — | none (no single pointer) | a map from addresses to `PointsToByte`s, one provenance |

## Trait impls

`T` is `Sized` (in `[T]`, it is the element type).
"Generic" means one `impl<T: ?Sized> ... for PointsTo<T> where PointsToUnaligned<T>: PTValueOps<A = T>`.

| Type | `PTPhys`, `PTProperties`, `View` | `PTTypedValue`, `PTValueOps` | `PTSizedValue` | Where | When |
|---|---|---|---|---|---|
| `PointsToUnaligned<T>` | `PTPhys`, `PTProperties`: per type (phase 2) | yes | yes | vstd | phase 2 |
| `PointsToUnaligned<[T]>` | `PTPhys`: per type (done); `PTProperties`: per type (phase 2) | yes | no | vstd | phase 2b |
| `PointsToUnaligned<str>` | `PTPhys`, `PTProperties`: per type | yes | no | rustlib | after phase 3b ([specs](#rustlib-str)) |
| `PointsTo<T>` | yes, generic | yes, generic | yes | vstd | phase 2 (generic from phase 2b) |
| `PointsTo<[T]>` | yes, generic | yes, generic | no | vstd, nothing slice-specific | phase 2b |
| `PointsTo<str>` | yes, generic | yes, generic | no | vstd, nothing `str`-specific | once rustlib adds `PointsToUnaligned<str>` |
| `SeqPointsTo<T, P>` (`A = [T]`) | yes (exists, generic) | no | no | vstd | pointer becomes `*mut [T]` in phase 1b |
| `PointsToByte` (`A = u8`) | yes (exists) | no | no | vstd | — |
| `PointsToRaw` | no (no single pointer) | no | no | vstd | phase 2c |

There is no `SeqPointsTo<str, _>`.
There is no `SeqPointsTo<T, PointsToUnaligned<T>>`:
the only typed sequences are `SeqPointsTo<T, PointsTo<T>>`
(unaligned memory is a `PointsToUnaligned<T>` or `PointsToUnaligned<[T]>`).

## Written once vs per type

Single-value permissions:

| Code | Written | What it contains |
|---|---|---|
| `PTPhys for PointsToUnaligned<_>` | per type | `ptr` (same shape each time), the `size` formula, `wf_basic` (the untyped permission is well-formed and has `size` bytes; same shape each time), and `ptrs_len_same` / `stays_wf_basic` (delegating to the untyped bytes) |
| `PTProperties for PointsToUnaligned<_>` | per type (same body each time) | the pointer-level lemmas, all delegating to the untyped bytes |
| `PTTypedValue for PointsToUnaligned<_>` | per type | `typed_value`, `bytes`, `additional_validity_constraints`, `satisfies_alignment` (`true`); the lemmas `bytes_decode`, `satisfies_alignment_of_wf`, `lemma_wf_basic` (empty proofs), `lemma_ptrs_len_same_valid_value`, `stays_wf` |
| `PTValueOps for PointsToUnaligned<_>` | per type | the operations that touch the fields (`borrow_typed_value`, `take_typed_value`, `put_typed_value`, `into_untyped_with_typed_value`, `from_untyped_with_typed_value`, `as_untyped`, `as_untyped_mut`) |
| `PTSizedValue for PointsToUnaligned<T>` | once (Sized `T` only) | the two lemmas |
| `PTPhys`, `PTProperties`, `View`, `PTTypedValue`, `PTValueOps` for `PointsTo<T: ?Sized>` | once (generic) | delegation to `self.pt_unaligned`, except `satisfies_alignment` (adds alignment) and `from_untyped_with_typed_value` (wraps the result) |
| `PTSizedValue for PointsTo<T>` | once (Sized `T` only) | the two lemmas (`lemma_satisfies_alignment_offset` has the real alignment proof) |
| trait default bodies | once (in the traits) | `PTTypedValue::wf`, `valid_value`, `ptrs_len_same_valid_value`; `PTValueOps::borrow`, `into_untyped`, `from_untyped`, `zero_sized`; `PTSizedValue::take`, `put`, `copy`, `copy_typed_value`, `from_untyped_with_value` |
| `impl<T: ?Sized> PointsToUnaligned<T> where PointsToUnaligned<T>: PTValueOps<A = T>` | once (generic) | `into_aligned`, `as_aligned`, `as_aligned_mut` |
| `impl<T: ?Sized> PointsTo<T> where PointsToUnaligned<T>: PTValueOps<A = T>` | once (generic) | `into_unaligned`, `as_unaligned`, `as_unaligned_mut` |
| `impl<T> PointsToUnaligned<[T]>` | once (slices) | `borrow_index`, `subrange` and the borrowed constructors (`from_untyped_ref`, `from_untyped_with_value_ref`): the primary implementations |
| `impl<T> PointsTo<[T]>` | once (slices) | the same functions, as compositions over the `PointsToUnaligned<[T]>` versions and the aligned/unaligned conversions |

Sequences:

| Impl | Applies to | What it contains |
|---|---|---|
| structural `impl<T, P: PTProperties<A = T>>` (`points_to_model.rs` for the specs, the field primitives and M5, `points_to_ops.rs` for the rest) | every sequence, untyped or typed | the only code touching the fields: accessors, constructors, borrows, `split_basic`, `join_basic`, `subrange_basic` |
| `PointsToUntyped` (`points_to_model.rs` for `View`, `bytes`, `wf` and the axioms; `points_to_ops.rs` for the proofs) | `SeqPointsTo<u8, PointsToByte>` | its `View`, `bytes`, `wf`, `split` / `join` / `split_ref` wrappers, and its axioms |
| typed `impl<T> SeqPointsTo<T, PointsTo<T>>` (`points_to_collections.rs`) | sequences of `PointsTo<T>` (the only typed sequences) | `View`, `thin_ptr` (`self.ptr() as *mut T`), `wf`, bytes and values, the typed `split` / `join` / `subrange` wrappers, `subrange_mut`, untyped conversions, value operations, `is_aligned`, `is_disjoint_seqpt`, and the sequence → slice conversions (`as_slice_pt`, `as_slice_pt_mut`) |

## Conversions

| From ↔ to | Owned | `&` | `&mut` | Where | When |
|---|---|---|---|---|---|
| `PointsTo<T>` ↔ `PointsToUnaligned<T>` | yes | yes | yes (to unaligned: field borrow; to aligned: M4) | vstd, generic aligned/unaligned impl | phase 2; `as_aligned_mut` in phase 3b |
| `PointsTo<[T]>` ↔ `PointsToUnaligned<[T]>` | yes | yes | yes (same) | vstd, same generic impl | phase 2b; `as_aligned_mut` in phase 3b |
| `PointsTo<str>` ↔ `PointsToUnaligned<str>` | yes | yes | yes (same) | vstd, same generic impl, no `str`-specific code | once rustlib adds `PointsToUnaligned<str>` |
| `SeqPointsTo<T, PointsTo<T>>` → `PointsTo<[T]>` | no | yes | yes | vstd | phase 4 |
| `PointsTo<[T]>` → `PointsTo<T>` at an index (`borrow_index`) | no | yes | no | vstd, composed from the unaligned version and the aligned/unaligned conversions | phase 4 |
| `PointsToUnaligned<[T]>` → `PointsToUnaligned<T>` at an index (`borrow_index`) | no | yes | no | vstd | phase 4 |
| `PointsTo<[T]>` → `PointsTo<[T]>` for a subrange (`subrange`) | no | yes | no | vstd, composed from the unaligned version and the aligned/unaligned conversions | rustlib port |
| `PointsToUnaligned<[T]>` → `PointsToUnaligned<[T]>` for a subrange (`subrange`) | no | yes | no | vstd (`points_to_ops.rs`) | rustlib port |
| `PointsToUnaligned<str>` ↔ `PointsToUnaligned<[u8]>` | no | yes | no | rustlib | after phase 3b ([specs](#rustlib-str)) |
| `PointsTo<str>` ↔ `PointsTo<[u8]>` | no | yes | no | rustlib, via the unaligned versions and the aligned/unaligned conversions | after phase 3b |
| `PointsToRaw` ↔ `PointsToUntyped` (a contiguous range) | yes | no | no | vstd | phase 2c |

## API changes not visible in the specs

Renames: `PointsToSingleton` → `PointsToByte`, `borrow_value` → `borrow`,
`borrow_value_subrange` → `borrow_subrange`,
`PTProperties::ptrs_len_same_valid` → `PTPhys::ptrs_len_same`.
Removed: `FixedSize`, `Dealloc`, and the inherent `PointsTo<T>` versions of the trait methods
(the five traits are re-exported instead; the prelude is unchanged).
Split: `PTValueOps`'s spec items and the lemmas that unfold `wf` move into a new supertrait,
`PTTypedValue`, and `PTProperties`'s `ptrs_len_same` and `stays_wf_basic` move into `PTPhys`
(see [Trait definitions](#trait-definitions)).
`group_points_to_permissions_lemmas` is split into `group_points_to_lemmas` and `group_points_to_collections_lemmas`
(see [Module layout](#module-layout)).

## Module layout

All of these are in a `raw_ptr` directory, which replaces the old `raw_ptr.rs`;
`mod.rs` only declares the modules and re-exports them, so importers use `vstd::raw_ptr::*`.

```
vstd/raw_ptr/
  mod.rs                       module declarations and re-exports only
  ptr_model.rs                 trusted
  ptr_specs.rs                 trusted
  shared_reference.rs          trusted
  points_to_model.rs           trusted
  points_to_structs.rs         trusted
  points_to_ops.rs             verified
  ptr_verified_specs.rs        verified
  points_to_collections.rs     verified
```

The trusted files hold the closed accessors and field primitives,
and every spec fn that an axiom depends on
(directly or through the spec fns it unfolds to).
The verified files only use the structs through those,
and nothing in the trusted files depends on them.

| File | Contents |
|---|---|
| `ptr_model.rs` | the module docs and model notes, `AllocId` and `global_alloc_id`, `ProvenanceData`, `provenance_properties`, `ptr_addr_in_bounds`, `Metadata`, `CovariantMetadata`, `PtrData`, the `View` impls for `*mut T` / `*const T`; the inverse functions (`ptr_mut_from_data`, `tracked_ptr_mut_from_data`, `ptr_from_data`, `axiom_ptr_mut_from_data`, `view_reverse_for_eq`, `ptrs_mut_eq`, `ptrs_mut_eq_sized`); `group_raw_ptr_axioms` |
| `ptr_specs.rs` | the pointer `==` `assume_specification`s, null pointers, casts, `addr` / `with_addr`; the reference specs (`ptr_shr_ref`, `ref_to_parts*`, `ref_from_parts*`, `mut_ref_as_shr_ref`, `mut_ref_from_parts*`, `ptr_mut_ref_join`, …); `cast_mut_ref_*`; `allocate` / `deallocate` |
| `shared_reference.rs` | `SharedReference` and its items over a permission's parts (`pt_untyped_and_typed_value`, `ptr_ref2*_untyped_with_typed_value`) |
| `points_to_model.rs` | the `PTPhys` and `PTProperties` traits (`PTPhys` sealed by `PTPhysSealed`); `PointsToByte` with its `PTPhys` / `PTProperties` impls (its axioms) and `View`; `SeqPointsTo`: the struct, its `PTPhys` impl, closed accessors, field primitives (`tracked_seq_pt`, `tracked_seq_pt_mut`, `into_seq`, `from_seq`, `from_seq_ref`) and M5; `PointsToUntyped`'s `View`, `bytes` and `wf`; `TypedValue`, with `tracked_copy`, `valid_ref`, `from_elems_ref` and M1; `pt_unaligned_parts_wf`, `pt_parts_wf`, `pt_parts_wf_slice` |
| `points_to_structs.rs` | the `PointsToUnaligned` and `PointsTo` structs: their `PTPhysSealed` impls, closed accessors, field primitives, which say nothing about `wf` (`tracked_pt_untyped`, `tracked_typed_value`, `tracked_pt_unaligned`, `into_raw_parts`, `from_raw_parts`, `from_raw_parts_ref`, `as_raw_parts_mut`, `lemma_ext`), and M3, M4 |
| `points_to_ops.rs` | the `PTTypedValue`, `PTValueOps` and `PTSizedValue` traits, with their default bodies; `SeqPointsTo`'s `PTProperties` impl and structural operations (`index_mut`, `from_seq_pt`, `empty`, `split_basic`, `join_basic`, `subrange_basic`); `PointsToUntyped`'s proofs; `PointsToUnaligned`'s and `PointsTo`'s `View`, inherent spec fns (`bytes`, `is_valid`, `value`, …) and all their trait impls; the aligned/unaligned conversions; the slice permissions' `len`, `borrow_index`, `subrange` and borrowed constructors (`from_untyped_ref`, `from_untyped_with_value_ref`); `is_aligned`, `is_disjoint_pointsto`, `is_disjoint_unaligned`, `lemma_pt_parts_wf`, `borrow_mut`; `group_points_to_lemmas` |
| `ptr_verified_specs.rs` | the `PointsTo` versions of the trusted functions over a permission's parts: `ptr_ref`, `ptr_ref_slice`, `ptr_mut_ref`, `ptr_mut_ref_slice`, `ptr_ref2`, `ptr_ref2_ghost`, `ptr_ref2_slice_ghost`, `SharedReference::points_to`, `shr_ref_points_to*`, `mut_ref_to_shr_points_to*` |
| `points_to_collections.rs` | `PointsToRaw` (all of it); the typed `SeqPointsTo` impl (`impl<T> SeqPointsTo<T, PointsTo<T>>`), including its `wf`, and its `View`; the sequence → slice conversions (`as_slice_pt`, `as_slice_pt_mut`); `group_points_to_collections_lemmas`. Nothing else depends on it. |

`group_points_to_lemmas` (in `group_vstd_default`) holds the broadcast lemmas of `points_to_ops.rs`:

```rust
pub broadcast group group_points_to_lemmas {
    SeqPointsTo::lemma_ptrs_len_same_untyped,
    PTTypedValue::lemma_ptrs_len_same_valid_value,
}
```

## Trusted functions

The trusted items (axioms, `external_body` functions and structs, `uninterp` spec fns, `assume_specification`s)
that the permissions rely on.
Their specs are in the code and aren't repeated here;
the ones added or changed by the trusted `PointsTo` refactor and `Tracked<&T>` are reviewed in [TRUSTED_REVIEW.md](TRUSTED_REVIEW.md).

**vstd `raw_ptr/ptr_model.rs`:**
`AllocationData`; `Tag`; `ProvenanceData` (`spatial_data`, `tag`); `provenance_properties`; `global_alloc_id`;
`View for *mut T`; `ptr_mut_from_data`, `tracked_ptr_mut_from_data`, `axiom_ptr_mut_from_data`, `ptrs_mut_eq`;
`CovariantMetadata`, `axiom_covariant_metadata_from_metadata`, `axiom_covariant_metadata_eq`.

**vstd `raw_ptr/ptr_specs.rs`:**
the pointer `==` and `addr` `assume_specification`s and the `cast_*` functions;
`shared_ref_ptr`; `ptr_shr_ref`; `ref_to_parts`, `ref_to_parts_slice`; `ref_from_parts`, `ref_from_parts_slice`;
`mut_ref_as_shr_ref`; `mut_ref_from_parts`, `mut_ref_from_parts_slice`;
`mut_ref_slice_len`, `ptr_mut_ref_join`, `tracked_mut_ref_slice_subrange`, `tracked_mut_ref_slice_idx`;
`cast_mut_ref_to_ptr`, `cast_mut_ref_slice_to_ptr`, `cast_mut_ref_str_to_ptr`;
`allocate`, `deallocate`.

**vstd `raw_ptr/shared_reference.rs`:**
`SharedReference` (`value`, `ptr` and its exec methods), `ptr_nonnull`, `axiom_shared_ref_value_view`;
`pt_untyped_and_typed_value` (`T` and `[T]`);
`ptr_ref2_untyped_with_typed_value`, `ptr_ref2_ghost_untyped_with_typed_value`, `ptr_ref2_slice_ghost_untyped_with_typed_value`.

**vstd `raw_ptr/points_to_model.rs`:**
`PointsToByte` (`byte_ptr`, `byte`) and its `is_nonnull`, `ptr_bounds`, `provenance_not_none`, `is_disjoint_byte`;
`SeqPointsTo::from_seq_mut` (M5);
`TypedValue::<[T]>::from_elems_ref`, `from_elems_mut` (M1);
`pt_unaligned_parts_wf`, `pt_parts_wf`, `pt_parts_wf_slice`.

**vstd `raw_ptr/points_to_structs.rs`:**
`PointsToUnaligned::from_raw_parts_ref`, `from_raw_parts_mut` (M3); `PointsTo::from_raw_parts_mut` (M4).

**Elsewhere in vstd:**
`seq.rs`: the `Seq` tracked operations, including `tracked_borrow_subrange`, `tracked_split_borrow_mut`, `tracked_add_borrow`, `tracked_add_borrow_mut`;
`slice.rs`: `tracked_slice_index`, `tracked_slice_subrange`;
`modes.rs`: `tracked_swap`, `tracked_static_mut_ref`, `tracked_ref`, `TrivialOwnership` (`u32` and `usize`);
`map.rs`: the `Map` tracked operations;
`type_representation.rs`: `abs_encode`, `abs_decode`, `abs_can_be_encoded`, `encode_decode_len`, `encode_decode_inverse`, `shared_ref_cannot_be_encoded`, `abs_decode_slice`, the per-type encoding impls;
`layout.rs`: the layout axioms;
builtin: `shr_ref_struct_wrap`.

**rustlib:**
`proofs/str.rs`: `spec_size_of_val_str`, `mut_ref_str_len`, `tracked_mut_ref_str_subrange`,
`SharedReference<str>::as_str_ptr`, `pt_untyped_and_typed_value` (`str`), `ptr_ref2_str_ghost_untyped_with_typed_value`,
`ref_to_parts_str`, `ref_from_parts_str`, `mut_ref_from_parts_str`, `pt_parts_wf_str`, and `EncodingStr`'s encoding axioms;
`core/src/str/mod.rs`: `str::as_str_ptr`, `as_bytes_tracked`, `from_bytes_tracked`;
`core/src/slice/mod.rs`: `<[T]>::as_slice_ptr`;
`core/src/ptr/mod.rs`: `read_unaligned_verus`;
`alloc/src/boxed.rs`: `from_raw_in_untyped_with_typed_value`, `into_non_null_with_allocator_untyped_with_typed_value`;
`specs/slice_index.rs`: the definitional axioms, including those over `&PointsTo`
(`def_valid_indices_slice_points_to`, `def_valid_indices_str_points_to`, `def_perm_ptr_*`, `def_perm_wf_*`, `def_perm_value_eq_*`).

**`str` decoding** (rustlib).
`abs_decode::<str>` comes from rustlib's existing `EncodingStr` (with `abs_encode_impl_unsized`):
the bytes' length and each byte's `u8` decoding. UTF-8 validity is not part of decoding.

## Trait definitions

| Trait | Contents | Impls in |
|---|---|---|
| `PTPhys` | the pointer and size; pointer-level well-formedness (`wf_basic`) and its preservation (`ptrs_len_same`, `stays_wf_basic`) | `points_to_model.rs` |
| `PTProperties` | the pointer lemmas (`is_nonnull`, `ptr_bounds`, `provenance_not_none`, `is_disjoint`) | `points_to_ops.rs` (`PointsToByte`'s, which are axioms: `points_to_model.rs`) |
| `PTTypedValue` | the typed value and bytes; well-formedness (`wf`, `valid_value`) and its preservation (`ptrs_len_same_valid_value`, `lemma_ptrs_len_same_valid_value`, `stays_wf`) | `points_to_model.rs` |
| `PTValueOps` | the operations: borrowing, taking and putting the typed value, the untyped conversions, `zero_sized` | `points_to_ops.rs` |
| `PTSizedValue` | the operations on `Sized` values | `points_to_ops.rs` |

The trait definitions, with their default bodies, are approved;
their code is in `points_to_model.rs`.

## Impls

The `points_to_model.rs`, `points_to_ops.rs` and `points_to_collections.rs` impls are approved and not repeated here;
their code is in those files.
Each `points_to_model.rs` section names its axioms,
which are listed in [Trusted functions](#trusted-functions).
`points_to_ops.rs` and `points_to_collections.rs` have no axioms.

### `PointsToByte` (phase 1)

Approved; the code is in `points_to_model.rs`.
`PointsToByte` is an `external_body` struct with uninterp `byte_ptr` and `byte` functions.
Axioms: `is_nonnull`, `ptr_bounds`, `provenance_not_none`, `is_disjoint_byte`.

### `SeqPointsTo` and `PointsToUntyped`: specs (phase 1b)

Approved; the code is in `points_to_model.rs`.
Axioms: `SeqPointsTo::from_seq_mut` (M5).

### `TypedValue` (phase 2)

Approved; the code is in `points_to_model.rs`.
`value_ref` and `valid_ref` are new; the rest exists today.
Axioms: `TypedValue::<[T]>::from_elems_mut` (M1), `from_elems_ref`.

### `PointsToUnaligned`: specs (phases 2, 2b; `str` in rustlib)

rustlib writes the `PTPhys`, `PTProperties` and `PTTypedValue` impls for `PointsToUnaligned<str>`
in the same shape as the `[T]` ones (`size(len) = len`; `additional_validity_constraints` is UTF-8 validity, `str::inv`, since `str` decoding is `EncodingStr`'s, which doesn't include it);
see [rustlib: `str`](#rustlib-str).
`PTPhys` is sealed by the crate-private `PTPhysSealed`,
but vstd's `impl<T: ?Sized> PTPhysSealed for PointsToUnaligned<T>` already covers `str`,
and vstd is a module of rustlib's `core`, so rustlib can write these impls.

Approved; the code is in `points_to_model.rs`.
Axioms: `PointsToUnaligned::from_raw_parts_ref`, `from_raw_parts_mut` (M3).

### `PointsTo`: specs (generic; phase 2, widened in phase 2b)

The generic impls name the `PointsToUnaligned` trait functions (`<PointsToUnaligned<T> as PTTypedValue>::...`),
since the inherent accessors don't unfold to them for a generic `T`.
`wf` is overridden: the trait's default body doesn't unfold at `PointsToUnaligned<T>` for a generic `T`,
so with the default, `self.wf()` doesn't give `pt_unaligned.wf()`, which every delegation needs
([phase 0, item 17](TYPED_POINTS_TO_IMPL_PLAN.md#phase-0-pending-checks)).

Approved; the code is in `points_to_model.rs`.
Axioms: `PointsTo::from_raw_parts_mut` (M4).

### `points_to_ops.rs`: `SeqPointsTo`'s `PTProperties` and structural operations (phase 1b)

`points_to_ops.rs` is a child module of `points_to_model.rs`, so it can use the structs' private fields
([phase 0, item 15](TYPED_POINTS_TO_IMPL_PLAN.md#phase-0-pending-checks)).

Approved; the code is in `points_to_ops.rs`.

### `points_to_ops.rs`: `PointsToUntyped`'s proofs (phase 1b)

Approved; the code is in `points_to_ops.rs`.
`join_ref` / `join_mut` are proved from the `Seq` join axioms
(`Seq::tracked_add_borrow` / `tracked_add_borrow_mut`).

### `points_to_ops.rs`: `PointsToUnaligned`'s proofs

`PTProperties` and `PTValueOps` are one impl per type (`T` and `[T]`; rustlib writes the `str` ones),
with the same bodies each time.
They aren't generic: the delegations need `wf_basic` and `ptr` to unfold,
and the per-type `PTPhys` bodies don't unfold in generic code.

Approved; the code is in `points_to_ops.rs`.

### `points_to_ops.rs`: `PointsTo`'s proofs and the aligned/unaligned conversions

Approved; the code is in `points_to_ops.rs`.

### `points_to_ops.rs`: slice indexing and borrowed constructors (phase 4)

There are no slice → sequence conversions (`as_seq_pt`, `as_seq_pt_mut`);
`borrow_index` borrows one element of a slice permission instead.
The borrowed constructors are the borrowed counterparts of the owned `from_untyped` / `from_untyped_with_typed_value`.

Approved; the code is in `points_to_ops.rs`.

### `points_to_collections.rs`: `PointsToRaw` (phase 2c)

Typed permissions convert through `PointsToUntyped`:
`into_untyped` followed by `PTValueOps::from_untyped` / `SeqPointsTo::from_untyped`, and back.

Approved; the code is in `points_to_collections.rs`.

### `points_to_collections.rs`: typed `SeqPointsTo` (phase 1b)

`from_seq_pt`, `empty`, `into_seq`, `tracked_seq_pt(_mut)` and `index_mut` have no typed versions.
There is no `SeqPointsTo<T, PointsToUnaligned<T>>`,
so there are no sequence aligned/unaligned conversions.

Approved; the code is in `points_to_collections.rs`.

### `points_to_collections.rs`: sequence → slice conversions (phase 4)

There are no slice → sequence conversions
(`borrow_index` borrows one element of a slice permission instead),
and no borrowed constructors for sequences.

Approved; the code is in `points_to_collections.rs`.

### rustlib: `str`

Approved; the code is in rustlib's `proofs/str.rs`.
rustlib writes `PTPhys`, `PTTypedValue`, `PTProperties` and `PTValueOps` for `PointsToUnaligned<str>`,
`value()` (the string's bytes), the shared `str` ↔ `[u8]` casts (`as_bytes`, `from_bytes_ref`) and `PointsTo<str>::subrange`;
its `View` and the rest of `PointsTo<str>` come from the generic impls (alignment 1, from `layout_of_str`).
These are proved, with no new axioms.

### rustlib: `slice_index.rs` wrappers

`specs/slice_index.rs`.
The defining axioms for `[T]` and `str` are restated on the new API;
`perm_ptr`, `perm_wf` and their defining axioms are new and in `group_slice_index_specs`.
`SliceIndexVerus`'s requires (`output_ptr_ref`, `get_unchecked_verus`, `get_unchecked_mut_verus`) use `perm_ptr(perm)` in place of `perm.ptr()`,
and `get_unchecked_verus` / `get_unchecked_mut_verus` also require `perm_wf(perm)`;
their comments "(1) follows from the below condition and `PointsTo<T>::{ptr_bounds, axiom_pt_slice_len}`" become "... `perm_wf(perm)` and `PointsTo<T>::ptr_bounds`".
`perm_init` is an open spec fn (`is_valid()` and `perm_wf`); its defining axioms are removed.
`valid_indices_slice_points_to` bounds the indices by `slice.len()` (the pointer's metadata).
`valid_indices_str_points_to` bounds the indices by `slice.ptr()@.metadata` and, when the value is valid, requires them to be on its char boundaries.
Everything else in the file is unchanged.
The axioms are listed in [Trusted functions](#trusted-functions).
