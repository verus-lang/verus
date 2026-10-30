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

`points_to.rs` and `points_to_permissions.rs` become three files.
`points_to_model.rs` and `points_to_ops.rs` are trusted (reviewed),
and `points_to_ops` is a child module of `points_to_model`.
`points_to_model.rs` holds the closed accessors,
and every spec fn that an axiom depends on
(directly or through the spec fns it unfolds to).
Other open spec fns, such as `len`, may live with the proofs that use them.
`points_to_collections.rs` is verified, and nothing else depends on it.

| `points_to_model.rs` (trusted) | `points_to_ops.rs` (trusted) | `points_to_collections.rs` (verified) |
|---|---|---|
| the five trait definitions, with their default bodies | the `PTProperties` impls of `SeqPointsTo`, `PointsToUnaligned` and `PointsTo` | `PointsToRaw` (all of it) |
| the struct definitions: `PointsToByte`, `TypedValue`, `SeqPointsTo`, `PointsToUntyped`, `PointsToUnaligned`, `PointsTo`; their closed accessors and the inherent spec fns (`typed_value`, `bytes`, `metadata`, `is_valid`, `value`, `value_ref`, `SeqPointsTo::len`, …); their `View` impls | the `PTValueOps` impls (per type for `PointsToUnaligned`, generic for `PointsTo`) and the `PTSizedValue` impls | the typed `SeqPointsTo` impl (`impl<T> SeqPointsTo<T, PointsTo<T>>`), including its `wf`, and its `View` |
| well-formedness: every `PTPhys` impl (`ptr`, `size`, `wf_basic`, `ptrs_len_same`, `stays_wf_basic`), every `PTTypedValue` impl (`typed_value`, `bytes`, `additional_validity_constraints`, `satisfies_alignment`, `valid_value`, `ptrs_len_same_valid_value`, and the lemmas `bytes_decode`, `satisfies_alignment_of_wf`, `lemma_wf_basic`, `lemma_ptrs_len_same_valid_value`, `stays_wf`), `PointsToUntyped::wf` and `bytes` | the structural `SeqPointsTo` impl (except the field primitives and M5) and `PointsToUntyped`'s proofs | |
| the axioms: `PointsToByte`'s `PTProperties` impl, `from_raw_parts_ref`, `TypedValue::from_elems_ref`, M1, M3–M5, `PointsTo::borrow_mut` | the aligned/unaligned conversions | the sequence → slice conversions (`as_slice_pt`, `as_slice_pt_mut`) |
| the tracked getters and byte disjointness: `TypedValue::tracked_copy`, `valid_ref`; `PointsToByte::is_disjoint_byte`; the field primitives, which say nothing about `wf`: `SeqPointsTo::tracked_seq_pt`, `tracked_seq_pt_mut`, `into_seq`, `PointsToUnaligned::tracked_pt_untyped`, `tracked_typed_value`, `into_raw_parts`, `from_raw_parts`, `as_raw_parts_mut`, `PointsTo::tracked_pt_unaligned` | the slice permissions' `len`, `borrow_index`, `subrange` and borrowed constructors (`from_untyped_ref`, `from_untyped_with_value_ref`); `is_aligned`, `is_disjoint_pointsto`, `is_disjoint_unaligned`; `group_points_to_lemmas` | `group_points_to_collections_lemmas` |

`group_points_to_lemmas` (in `group_vstd_default`) holds the broadcast lemmas of `points_to_model.rs` and `points_to_ops.rs`:

```rust
pub broadcast group group_points_to_lemmas {
    SeqPointsTo::lemma_ptrs_len_same_untyped,
    PTTypedValue::lemma_ptrs_len_same_valid_value,
}
```

`raw_ptr_new.rs` becomes two files:

| `ptr_model.rs` | `ptr_specs.rs` |
|---|---|
| the module docs and model notes, `AllocId` and `global_alloc_id`, `ProvenanceData`, `provenance_properties`, `ptr_addr_in_bounds`, `Metadata`, `PtrData`, the `View` impls for `*mut T` / `*const T` | the pointer `==` `assume_specification`s |
| the inverse functions: `ptr_mut_from_data`, `tracked_ptr_mut_from_data`, `ptr_from_data`, `axiom_ptr_mut_from_data`, `view_reverse_for_eq`, `ptrs_mut_eq`, `ptrs_mut_eq_sized` | null pointers, casts, `ptr_ref` / `ptr_mut_ref` (and the slice versions), `addr` / `with_addr`, the reference specs, `mut_ref_to_shr_points_to` (and the slice version), `cast_mut_ref_*`, `allocate` / `deallocate` |
| `group_raw_ptr_axioms` (all four members are here) | |

All of these are in a `raw_ptr` directory, which replaces the old `raw_ptr.rs`;
`mod.rs` only declares the modules and re-exports them, so importers use `vstd::raw_ptr::*`.

```
vstd/raw_ptr/
  mod.rs                       module declarations and re-exports only
  ptr_model.rs
  ptr_specs.rs
  shared_reference.rs
  points_to_model.rs
  points_to_model/
    points_to_ops.rs
  points_to_collections.rs
```

## Existing, unchanged trusted specs

Trusted items the permissions rely on that exist today and don't change.
"Uses" names the main dependents.
Existing axioms with minor contract changes on this branch are in
[Minor changes to existing trusted specs](#minor-changes-to-existing-trusted-specs).

| Item | File | What it states | Uses |
|---|---|---|---|
| `PointsToByte` (`external_body` struct; `uninterp` `ptr`, `byte`) | `points_to_model.rs` | A permission to one byte, with its address and abstract byte. | everything byte-level |
| `PointsToByte`'s `is_nonnull`, `ptr_bounds`, `provenance_not_none`, `is_disjoint` | `points_to_model.rs` | A byte permission's pointer is non-null, within its allocation, has non-null provenance; two byte permissions are at different addresses. | `PointsToUntyped`'s and `PointsToRaw`'s pointer-level lemmas |
| `AllocationData` (`start_addr`, `alloc_len`, `alignment`, `orig_size`, `alloc_id`); `Tag` (`external_body`); `ProvenanceData` (`external_body`; `uninterp` `spatial_data`, `tag`; `open` accessors for each `AllocationData` field); `provenance_properties` (triggered on `spatial_data`); `provenance_eq_up_to_tag` | `ptr_model.rs` | The allocation model, plus a tag that tracks reborrows. `orig_size` replaces `Dealloc`'s size tracking. | pointer bounds, `allocate` / `deallocate`, `ptr_eq_up_to_tag` |
| pointer model: `View for *mut T` (`uninterp`), `ptr_mut_from_data` (`uninterp`), `axiom_ptr_mut_from_data`, `ptrs_mut_eq`, `tracked_ptr_mut_from_data` | `ptr_model.rs` | A pointer is its `PtrData` (address, provenance, metadata). | every pointer spec (e.g. the generic `PointsToUnaligned` pointer built from its metadata) |
| `assume_specification`s for pointer `==`, `null`, `null_mut`, `addr`, `with_addr`; the `cast_*` `external_body` functions | `ptr_specs.rs` | The exec pointer operations match the model. | exec code |
| `SharedReference` (`external_body`; `uninterp` `value`, `ptr`), `ptr_nonnull`, `axiom_shared_ref_value_view` | `shared_reference.rs` | A shared reference with its pointer. | exec code; the source of valid shared permissions |
| `shared_ref_ptr` (`uninterp`), `mut_ref_slice_len`, `ptr_mut_ref_join`, `tracked_mut_ref_slice_subrange`, `tracked_mut_ref_slice_idx`, `cast_mut_ref_to_ptr`, `cast_mut_ref_slice_to_ptr`, `cast_mut_ref_str_to_ptr` | `ptr_specs.rs` | Reference ↔ pointer and permission boundary. | exec code; the source of valid permissions |
| `abs_encode`, `abs_decode`, `abs_can_be_encoded` (`uninterp`); `encode_decode_len`, `encode_decode_inverse`, `shared_ref_cannot_be_encoded`; the per-type encoding impls | `type_representation.rs` | The abstract-byte encoding of values. | every decode clause |
| layout axioms (`layout_of_sized`, `layout_of_slices`, `layout_of_str`, `layout_of_unit_tuple`, `align_properties`, …) | `layout.rs` | Sizes and alignments of types and values. | sizes, `satisfies_alignment`, `lemma_satisfies_alignment_offset`, the `zero_sized` default |
| `tracked_swap`, `tracked_static_mut_ref` | `modes.rs` | Swapping tracked values; a `'static` borrow of an owned value. | `take_typed_value` |
| `Seq` tracked operations (`tracked_borrow`, `tracked_borrow_mut`, `tracked_borrow_subrange_mut`, …) | `seq.rs` | Borrowing parts of a tracked `Seq`. | `as_untyped_mut`, `index_mut` |
| `Map` tracked operations (`tracked_empty`, `tracked_remove_keys`, `tracked_union_prefer_right`, …) | `map.rs` | Building and splitting a tracked `Map`. | `PointsToRaw` |
| `shr_ref_struct_wrap` | builtin | Borrowing a struct from a borrow of its only tracked field. | `as_aligned`, `subrange_basic`, `split_ref`, `join_ref` |

## Minor changes to existing trusted specs

The Sized ones are already in the code on this branch;
the slice versions are restored in phase 4b, and the `str` versions move to rustlib.
`ptr_mut_ref`'s change (it now also ensures `final(perm).wf()`) is a bigger change;
it's in [New axioms and axioms with bigger changes](#new-axioms-and-axioms-with-bigger-changes).

| Item | File | Change | Uses |
|---|---|---|---|
| `ptr_ref` (`external_body`) | `ptr_specs.rs` | Now requires `perm.wf()`. | exec reads |
| `mut_ref_to_shr_points_to` | `ptr_specs.rs` | Now ensures `pt.wf()`. | the source of valid permissions from `&mut T` |
| `SharedReference::points_to` | `shared_reference.rs` | Now ensures `pt.wf()`. | the source of valid shared permissions |
| `ptr_ref2` (`external_body`), `ptr_ref2_ghost` | `shared_reference.rs` | Now require `perm.wf()`. | exec code; `SharedReference` from a permission |
| `ptr_ref_slice` (`external_body`; restored, phase 4b) | `ptr_specs.rs` | Restored from commented-out code; now requires `perm.wf()`. | exec slice reads |
| `mut_ref_to_shr_points_to_slice` (restored, phase 4b) | `ptr_specs.rs` | Restored from commented-out code; now ensures `pt.wf()`. | the source of valid slice permissions from `&mut [T]` |
| `SharedReference<[T]>::points_to` (restored, phase 4b) | `shared_reference.rs` | Restored from commented-out code; now ensures `pt.wf()`. | the source of valid shared slice permissions |
| `ptr_ref2_slice_ghost` (restored, phase 4b) | `shared_reference.rs` | Restored from commented-out code; now requires `perm.wf()`. | `SharedReference<[T]>` from a slice permission |
| `ptr_ref_str` (`external_body`; rustlib) | rustlib | Moved from vstd's commented-out code; now requires `perm.wf()`. | exec `str` reads |
| `mut_ref_to_shr_points_to_str` (rustlib) | rustlib | Moved from vstd's commented-out code; now ensures `pt.wf()`, and requires the `str`'s `inv()`. | the source of valid `str` permissions from `&mut str` |
| `SharedReference<str>::points_to` (rustlib) | rustlib | Moved from vstd's commented-out code; now ensures `pt.wf()`, and requires the `str`'s `inv()`. | the source of valid shared `str` permissions |
| `str::as_str_ptr_verus` (`external_body`; rustlib) | rustlib | Existing; now states the permission through `typed_value()` and `is_valid()`, ensures `perm@.wf()`, and requires `self.inv()`. | exec `str` pointers with permissions |
| `ptr_ref2_str_ghost` (rustlib) | rustlib | Moved from vstd's commented-out code; now requires `perm.wf()`. | `SharedReference<str>` from a `str` permission |
| `SharedReference<str>::as_str_ptr` (`external_body`; rustlib) | rustlib | Moved from vstd's commented-out code; the body uses `as_ref()` (the field is private to vstd); requires the `str`'s `inv()`. | exec `str` pointers (`as_ptr`) |

The restored slice and `str` versions also state the value through `typed_value().value_ref()`
(with `@` for slices) in place of the old `value()`, which the planned `PointsTo<[T]>` / `PointsTo<str>` don't have.

`ptr_specs.rs`:

```rust
/// Equivalent to `&*ptr`, passing in a permission `perm` to ensure safety.
/// The memory pointed to by `ptr` must be initialized.
#[inline(always)]
#[verifier::external_body]
pub const fn ptr_ref<T>(ptr: *const T, Tracked(perm): Tracked<&PointsTo<T>>) -> (v: &T)
    requires
        perm.ptr() == ptr,
        perm.is_valid(),
        perm.wf(),
    ensures
        v == perm.value(),
    opens_invariants none
    no_unwind
{
    unsafe { &*ptr }
}

/// Convert from a shared reference to a `&'a mut T` to a `&'a PointsTo<T>`.
pub axiom fn mut_ref_to_shr_points_to<'a, T>(tracked mut_ref: &'a &'a mut T) -> (tracked pt:
    &'a PointsTo<T>)
    ensures
        pt.ptr() == mut_ref_ptr(*mut_ref),
        pt.is_valid(),
        pt.value() == *old(*mut_ref),
        pt.wf(),
        *final(*mut_ref) == *old(*mut_ref),
;
```

`ptr_specs.rs`, the restored slice versions (phase 4b):

```rust
/// Equivalent to `&*ptr`, passing in a permission `perm` to ensure safety.
/// The memory pointed to by `ptr` must be initialized.
#[inline(always)]
#[verifier::external_body]
pub const fn ptr_ref_slice<T>(ptr: *const [T], Tracked(perm): Tracked<&PointsTo<[T]>>) -> (v: &[T])
    requires
        perm.ptr() == ptr,
        perm.is_valid(),
        perm.wf(),
    ensures
        v@ == perm.value(),
    opens_invariants none
    no_unwind
{
    unsafe { &*ptr }
}

/// Convert from a shared reference to a `&'a mut [T]` to a `&'a PointsTo<[T]>`.
pub axiom fn mut_ref_to_shr_points_to_slice<'a, T>(tracked mut_ref: &'a &'a mut [T])
    -> (tracked pt: &'a PointsTo<[T]>)
    ensures
        pt.ptr() == mut_ref_ptr(*mut_ref),
        pt.is_valid(),
        pt.value() == (*old(*mut_ref))@,
        pt.wf(),
        &*final(*mut_ref) == &*old(*mut_ref),
;
```

`shared_reference.rs`:

```rust
impl<'a, T> SharedReference<'a, T> {
    // NOTE: there does not exist a points_to_unaligned function because SharedReference
    // by definition gives you an _aligned_ PointsTo.
    // https://doc.rust-lang.org/std/primitive.reference.html
    pub axiom fn points_to(tracked self) -> (tracked pt: &'a PointsTo<T>)
        ensures
            pt.ptr() == self.ptr(),
            pt.is_valid(),
            pt.value() == self.value(),
            pt.wf(),
    ;
}

/// Like [`ptr_ref`] but returns a `SharedReference` so it keeps track of the relationship
/// between the pointers.
/// Note the resulting reference's pointers does NOT have the same provenance.
/// This is because in Rust models like Stacked Borrows / Tree Borrows, the pointer
/// gets a new tag.
#[inline(always)]
#[verifier::external_body]
pub fn ptr_ref2<'a, T>(ptr: *const T, Tracked(perm): Tracked<&PointsTo<T>>) -> (v: SharedReference<
    'a,
    T,
>)
    requires
        perm.ptr() == ptr,
        perm.is_valid(),
        perm.wf(),
    ensures
        v.value() == perm.value(),
        v.ptr().addr() == ptr.addr(),
        v.ptr()@.metadata == ptr@.metadata,
    opens_invariants none
    no_unwind
{
    SharedReference(unsafe { &*ptr })
}

/// Same as [`ptr_ref2`], but operates on ghost values.
/// Because this doesn't constitute a retag, the returned value's pointer has the same provenance as the original pointer.
pub axiom fn ptr_ref2_ghost<'a, T>(ptr: *const T, tracked perm: &PointsTo<T>) -> (tracked v:
    SharedReference<'a, T>)
    requires
        perm.ptr() == ptr,
        perm.is_valid(),
        perm.wf(),
    ensures
        v.value() == perm.value(),
        v.ptr() == ptr,
;
```

`shared_reference.rs`, the restored slice versions (phase 4b):

```rust
impl<'a, T> SharedReference<'a, [T]> {
    /// A shared slice reference gives a shared, valid slice permission.
    pub axiom fn points_to(tracked self) -> (tracked pt: &'a PointsTo<[T]>)
        ensures
            pt.ptr() == self.ptr(),
            pt.is_valid(),
            pt.value() == self.value()@,
            pt.wf(),
    ;
}

/// The ghost version of `ptr_ref2` for slices.
/// Because this doesn't constitute a retag,
/// the returned value's pointer has the same provenance as the original pointer.
pub axiom fn ptr_ref2_slice_ghost<'a, T>(ptr: *const [T], tracked perm: &PointsTo<[T]>)
    -> (tracked v: SharedReference<'a, [T]>)
    requires
        perm.ptr() == ptr,
        perm.is_valid(),
        perm.wf(),
    ensures
        v.value()@ == perm.value(),
        v.ptr() == ptr,
;
```

rustlib, the `str` versions (moved from vstd's commented-out code):

```rust
impl<'a> SharedReference<'a, str> {
    #[verifier::external_body]
    pub const fn as_str_ptr(self) -> (ptr: *const str)
        requires
            self.value().inv(),
        ensures
            ptr == self.ptr(),
    {
        self.as_ref() as *const str
    }

    // commonly used operation: this function's signature corresponds to Rust's `str::as_ptr`
    pub const fn as_ptr(self) -> (ptr: *const u8)
        requires
            self.value().inv(),
        ensures
            ptr == self.ptr() as *const u8,
    {
        self.as_str_ptr() as *const u8
    }

    pub axiom fn points_to(tracked self) -> (tracked pt: &'a PointsTo<str>)
        requires
            self.value().inv(),
        ensures
            pt.ptr() == self.ptr(),
            pt.is_valid(),
            pt.typed_value().value_ref() == self.value(),
            pt.wf(),
    ;
}

/// The ghost version of `ptr_ref2` for `str`.
/// Because this doesn't constitute a retag,
/// the returned value's pointer has the same provenance as the original pointer.
pub axiom fn ptr_ref2_str_ghost<'a>(ptr: *const str, tracked perm: &PointsTo<str>) -> (tracked v: SharedReference<'a, str>)
    requires
        perm.ptr() == ptr,
        perm.is_valid(),
        perm.wf(),
    ensures
        v.value() == perm.typed_value().value_ref(),
        v.ptr() == ptr,
;

/// Equivalent to `&*ptr`, passing in a permission `perm` to ensure safety.
/// The memory pointed to by `ptr` must be initialized.
#[inline(always)]
#[verifier::external_body]
pub const fn ptr_ref_str(ptr: *const str, Tracked(perm): Tracked<&PointsTo<str>>) -> (v: &str)
    requires
        perm.ptr() == ptr,
        perm.is_valid(),
        perm.wf(),
    ensures
        v == perm.typed_value().value_ref(),
    opens_invariants none
    no_unwind
{
    unsafe { &*ptr }
}

/// Convert from a shared reference to a `&'a mut str` to a `&'a PointsTo<str>`.
pub axiom fn mut_ref_to_shr_points_to_str<'a>(tracked mut_ref: &'a &'a mut str) -> (tracked pt: &'a PointsTo<str>)
    requires
        mut_ref.inv(),
    ensures
        pt.ptr() == mut_ref_ptr(*mut_ref),
        pt.is_valid(),
        pt.typed_value().value_ref() == &*old(*mut_ref),
        pt.wf(),
        &*final(*mut_ref) == &*old(*mut_ref),
;

// In `impl str` (`str/mod.rs`).
#[verifier::shadow_data]
#[verifier::external_body] // Ok - cast from `&self` to `*const str`
// Axiomatizes cast from `&self` to `*const str`, since Verus doesn't support it.
pub const fn as_str_ptr_verus(&self) -> ((ptr, perm): (*const str, Tracked<&PointsTo<str>>))
    requires
        self.inv(),
    ensures
        ptr == shared_ref_ptr(shadow_data(self)),
        perm@.ptr() == shared_ref_ptr(shadow_data(self)),
        perm@.is_valid(),
        perm@.typed_value().value_ref() == self,
        perm@.wf(),
{
    (self as *const str, Tracked::assume_new())
}
```

## New axioms and axioms with bigger changes

Every new trusted item, relative to the `verify-rustlib` branch.
Includes all `points_to_model` axiomatized code.
`PointsToByte` (`external_body` struct; `uninterp` `ptr`, `byte`)
and its `PTProperties` impl (`is_nonnull`, `ptr_bounds`, `provenance_not_none`, `is_disjoint`)
are also trusted (axioms in `points_to_model.rs`), but unchanged
(see [Existing, unchanged trusted specs](#existing-unchanged-trusted-specs)).

| Item | File | What it states | Uses | Approved by Travis/Natalie |
|---|---|---|---|---|
| `ptr_mut_ref` (`external_body`; existing, strengthened, already in the code) | `ptr_specs.rs` | Now also ensures `final(perm).wf()`: the final bytes decode to the final value (and requires `old(perm).wf()`). | exec writes through `&mut T` | yes |
| `ptr_mut_ref_slice` (`external_body`; restored, phase 4b) | `ptr_specs.rs` | Restored from commented-out code, strengthened the same way as `ptr_mut_ref`. | exec writes through `&mut [T]` | yes |
| `ptr_mut_ref_str` (`external_body`; rustlib) | rustlib | Moved from vstd's commented-out code, strengthened the same way as `ptr_mut_ref`, with the final `wf()` only if the final `str` is valid UTF-8. | exec writes through `&mut str` | yes |
| `Seq::tracked_borrow_subrange` (`external_body`; already in the code) | `seq.rs` | Borrows a subrange of a borrowed tracked `Seq`. | `subrange_basic`, `split_ref` | yes |
| `Seq::tracked_split_borrow_mut` (`external_body`; already in the code) | `seq.rs` | Splits a mutable borrow of a tracked `Seq` in two. | `subrange_mut`, the `&mut` conversions | yes |
| `Seq::tracked_add_borrow` | `seq.rs` | Two borrowed tracked `Seq`s act as one borrowed concatenation. | `PointsToUntyped::join_ref` | yes |
| `Seq::tracked_add_borrow_mut` | `seq.rs` | The same for mutable borrows; the parts' final values are tied back if the concatenation keeps its length. | `PointsToUntyped::join_mut` | yes |
| `tracked_slice_index` (phase 3b) | `slice.rs` | Borrows an element of a borrowed slice. | `borrow_index` | yes |
| `tracked_slice_subrange` (rustlib port) | `slice.rs` | Borrows a subrange of a borrowed slice. | other users (slice `subrange` uses `from_elems_ref`) | yes |
| `TrivialOwnership` and its `u32` / `usize` impls (rustlib port) | `modes.rs` | A spec value of a type that owns no resources can be made tracked. | rustlib's `u32` / `usize` casts of `[u8]` permissions (G3) | yes |
| `TypedValue::<[T]>::from_elems_ref` (phase 3b) | `points_to_model.rs` | Per-element shared typed values act as one shared slice typed value (the shared counterpart of M1). Replaces the generic `tracked_slice_from_refs`, so it only covers `TypedValue`s, which have no physical memory. | shared sequence → slice | yes |
| `tracked_ref` (phase 3b) | `modes.rs` | A borrow is a borrowed `Tracked` of itself. | `TypedValue::valid_ref` | yes |
| `PointsToUnaligned::from_raw_parts_ref` (phase 3b) | `points_to_model.rs` | Borrowed bytes and typed value act as one borrowed permission. | borrowed constructors, `borrow_index`, sequence → slice, `str` ↔ `[u8]` | yes |
| M1 `TypedValue::<[T]>::from_elems_mut` (phase 3b) | `points_to_model.rs` | Per-element `&mut` typed values act as one `&mut` slice typed value. | `&mut` sequence → slice | yes |
| M3 `PointsToUnaligned::from_raw_parts_mut` (phase 3b) | `points_to_model.rs` | `&mut` bytes and typed value act as one `&mut` permission. | `&mut` conversions | yes |
| M4 `PointsTo::from_unaligned_mut` (phase 3b) | `points_to_model.rs` | A `&mut PointsToUnaligned` acts as a `&mut PointsTo`. | `as_aligned_mut`, aligned `&mut` conversions | yes |
| M5 `SeqPointsTo::from_seq_mut` (phase 3b) | `points_to_model.rs` | A `&mut Seq<P>` acts as a `&mut SeqPointsTo`. | `subrange_mut`, `split_mut` | yes |
| `PointsTo::borrow_mut` (already in the code) | `points_to_model.rs` | A mutable borrow of a valid permission's value; writing through it updates the value and the bytes together, keeping `wf()`. | ghost writes through a permission | yes |
| `global_alloc_id` (`uninterp`) | `ptr_model.rs` | The id of the global allocator's allocations. | `allocate` / `deallocate` | yes |
| `allocate`, `deallocate` (`external_body`; ported from `raw_ptr_old.rs`, without `Dealloc`) | `ptr_specs.rs` | Allocation gives a well-formed `PointsToUntyped` for the new range with a global-allocator provenance; deallocation consumes one covering the whole allocation. | heap allocation | yes |
| `abs_decode_slice` (already in the code) | `type_representation.rs` | A slice decodes exactly when each element's slot does. Its definition is in the code and isn't repeated here. | slice `wf` | yes |

**`ptr_mut_ref`** (`ptr_specs.rs`; existing, strengthened, already in the code).
It now requires and ensures `wf()`.
It doesn't say the bytes stay the same,
so `final(perm).wf()` is what tells callers the final bytes decode to the final value.

```rust
/// Equivalent to `&mut *ptr`, passing in a permission `perm` to ensure safety.
/// The memory pointed to by `ptr` must be initialized.
#[inline(always)]
#[verifier::external_body]
pub const fn ptr_mut_ref<T>(ptr: *mut T, Tracked(perm): Tracked<&mut PointsTo<T>>) -> (v: &mut T)
    requires
        old(perm).ptr() == ptr,
        old(perm).is_valid(),
        old(perm).wf(),
    ensures
        final(perm).ptr() == ptr,
        final(perm).is_valid(),
        // The final bytes decode to the final value.
        final(perm).wf(),
        old(perm).value() == *v,
        final(perm).value() == *final(v),
    opens_invariants none
    no_unwind
{
    unsafe { &mut *ptr }
}
```

The restored slice version (phase 4b),
with the value stated through `PointsTo<[T]>::value()` (the elements, `typed_value().value_ref()@`):

```rust
/// Equivalent to `&mut *ptr`, passing in a permission `perm` to ensure safety.
/// The memory pointed to by `ptr` must be initialized.
#[inline(always)]
#[verifier::external_body]
pub const fn ptr_mut_ref_slice<T>(ptr: *mut [T], Tracked(perm): Tracked<&mut PointsTo<[T]>>) -> (v: &mut [T])
    requires
        old(perm).ptr() == ptr,
        old(perm).is_valid(),
        old(perm).wf(),
    ensures
        final(perm).ptr() == ptr,
        final(perm).is_valid(),
        // The final bytes decode to the final value.
        final(perm).wf(),
        old(perm).value() == v@,
        final(perm).value() == final(v)@,
    opens_invariants none
    no_unwind
{
    unsafe { &mut *ptr }
}
```

rustlib, the `str` version (moved from vstd's commented-out code):

```rust
/// Equivalent to `&mut *ptr`, passing in a permission `perm` to ensure safety.
/// The memory pointed to by `ptr` must be initialized.
#[inline(always)]
#[verifier::external_body]
pub const fn ptr_mut_ref_str(ptr: *mut str, Tracked(perm): Tracked<&mut PointsTo<str>>) -> (v: &mut str)
    requires
        old(perm).ptr() == ptr,
        old(perm).is_valid(),
        old(perm).wf(),
    ensures
        final(perm).ptr() == ptr,
        final(perm).is_valid(),
        // The final permission is well-formed if the final str is valid UTF-8.
        final(v).inv() ==> final(perm).wf(),
        old(perm).typed_value().value_ref() == &*v,
        final(perm).typed_value().value_ref() == &*final(v),
    opens_invariants none
    no_unwind
{
    unsafe { &mut *ptr }
}
```

**`Seq` tracked operations** (`seq.rs`, in `impl<A> Seq<A>`; new relative to `verify-rustlib`, already in the code).

```rust
/// Take a tracked subrange of a sequence.
#[verifier(external_body)]
pub proof fn tracked_borrow_subrange(tracked &self, i: int, j: int) -> (tracked ret: &Self)
    requires
        0 <= i <= j <= self.len(),
    ensures
        *ret == self.subrange(i, j),
{
    unimplemented!()
}

/// Split a tracked mutable borrow of a sequence into two at index `mid`.
#[verifier(external_body)]
pub proof fn tracked_split_borrow_mut(tracked &mut self, mid: int) -> (tracked (s1, s2): (
    &mut Self,
    &mut Self,
))
    requires
        0 <= mid <= self.len(),
    ensures
        *s1 == old(self).take(mid),
        *s2 == old(self).skip(mid),
        *final(self) == *final(s1) + *final(s2),
{
    unimplemented!()
}

/// Combine tracked borrows of two sequences into one borrow of their concatenation.
pub axiom fn tracked_add_borrow<'a>(tracked &'a self, tracked other: &'a Self) -> (tracked ret:
    &'a Self)
    ensures
        *ret == *self + *other,
;

/// Combine tracked mutable borrows of two sequences into one mutable borrow of their concatenation
/// (the inverse of `tracked_split_borrow_mut`).
/// If the concatenation keeps its length,
/// its final value splits back into `self`'s and `other`'s at `self`'s length.
pub axiom fn tracked_add_borrow_mut<'a>(tracked &'a mut self, tracked other: &'a mut Self) -> (tracked ret:
    &'a mut Self)
    ensures
        *ret == *old(self) + *old(other),
        final(ret).len() == ret.len() ==> {
            &&& *final(self) == final(ret).take(old(self).len() as int)
            &&& *final(other) == final(ret).skip(old(self).len() as int)
        },
;
```

**Borrowed slices and `Tracked`** (new, phase 3b).

`slice.rs` (no permissions involved):

```rust
/// Borrows the element at index `i` of a borrowed slice.
pub axiom fn tracked_slice_index<'a, T>(tracked s: &'a [T], i: int) -> (tracked e: &'a T)
    requires
        0 <= i < s@.len(),
    ensures
        *e == s@[i],
;

/// Borrows elements `[i, j)` of a borrowed slice.
pub axiom fn tracked_slice_subrange<'a, T>(tracked s: &'a [T], i: int, j: int) -> (tracked out: &'a [T])
    requires
        0 <= i <= j <= s@.len(),
    ensures
        out@ == s@.subrange(i, j),
;
```

`modes.rs`, next to `tracked_swap`:

```rust
/// Converts a borrowed value to a borrowed `Tracked` of that value.
pub axiom fn tracked_ref<'a, T: ?Sized>(tracked t: &'a T) -> (tracked out: &'a Tracked<T>)
    ensures
        &**out == t,
;
```

**Tracked values of trivial-ownership types** (rustlib port).
`modes.rs`, next to `tracked_static_mut_ref`.
Implemented only for `u32` and `usize`,
each impl's `tracked_from_spec` an `axiom fn`.

```rust
/// Types whose values own no resources (no permissions, tokens or other tracked data),
/// so any spec value can be used as a tracked one.
pub trait TrivialOwnership: Sized {
    /// Makes a spec value tracked.
    proof fn tracked_from_spec(v: Self) -> (tracked out: Self)
        ensures
            out == v,
    ;
}
```

**Borrowed permission assembly** (new, phase 3b).
It says nothing about `wf()`: callers prove it from the parts.

`points_to_model.rs`, with `PointsToUnaligned`:

```rust
impl<T: ?Sized> PointsToUnaligned<T> {
    /// Converts a borrowed untyped permission and a borrowed typed value, with the given pointer metadata,
    /// into one borrowed `PointsToUnaligned` permission.
    /// This is the borrowed version of building the permission from its parts.
    /// It says nothing about `wf()`: callers prove it from the parts.
    pub axiom fn from_raw_parts_ref<'a>(
        tracked pt_untyped: &'a PointsToUntyped,
        tracked typed_value: &'a TypedValue<T>,
        metadata: Metadata<T>,
    ) -> (tracked out: &'a Self)
        ensures
            out.pt_untyped() == *pt_untyped,
            out.typed_value() == *typed_value,
            out.metadata() == metadata,
    ;
}
```

`points_to_model.rs`, with `TypedValue` (the shared counterpart of M1):

```rust
impl<T> TypedValue<[T]> {
    /// A sequence of borrows of typed values acts as one borrow of a slice typed value.
    /// If any element is empty, the slice is empty.
    pub axiom fn from_elems_ref<'a>(tracked elems: Seq<&'a TypedValue<T>>)
        -> (tracked out: &'a TypedValue<[T]>)
        ensures
            // Valid with the elements' values if every element is valid
            // (a zero-length Seq counts as valid); otherwise empty.
            (forall|i: int| #![trigger elems[i]] 0 <= i < elems.len() ==> elems[i].is_valid()) ==> {
                &&& out.is_valid()
                &&& out.value_ref()@ == Seq::new(elems.len(), |i: int| elems[i].value())
            },
            !(forall|i: int| #![trigger elems[i]] 0 <= i < elems.len() ==> elems[i].is_valid()) ==> out.is_empty(),
    ;
}
```

**Mutable borrowed assembly (M1, M3–M5)** (new, phase 3b; there is no M2 or M6).
Each follows `PointsToUntyped::join_mut`'s pattern:
the borrowed parts' final values are tied to the result's final value,
conditionally where the structure could change.

`points_to_model.rs`, with `TypedValue` (M1):

```rust
impl<T> TypedValue<[T]> {
    /// A sequence of mutable borrows of typed values acts as one mutable borrow of a slice typed value.
    /// If any element is empty, the slice starts empty.
    pub axiom fn from_elems_mut<'a>(tracked elems: Seq<&'a mut TypedValue<T>>)
        -> (tracked out: &'a mut TypedValue<[T]>)
        ensures
            // Initially: valid with the elements' values if every element is valid
            // (a zero-length Seq counts as valid); otherwise empty.
            (forall|i: int| #![trigger elems[i]] 0 <= i < elems.len() ==> elems[i].is_valid()) ==> {
                &&& out.is_valid()
                &&& out.value_ref()@ == Seq::new(elems.len(), |i: int| elems[i].value())
            },
            !(forall|i: int| #![trigger elems[i]] 0 <= i < elems.len() ==> elems[i].is_valid()) ==> out.is_empty(),
            // Finally: a valid slice of the same length is distributed back to the elements;
            // anything else leaves every element empty.
            final(out).is_valid() && final(out).value_ref()@.len() == elems.len() ==> forall|i: int|
                #![trigger elems[i]]
                0 <= i < elems.len() ==> {
                    &&& final(elems[i]).is_valid()
                    &&& final(elems[i]).value() == final(out).value_ref()@[i]
                },
            !(final(out).is_valid() && final(out).value_ref()@.len() == elems.len()) ==> forall|i: int|
                #![trigger elems[i]]
                0 <= i < elems.len() ==> final(elems[i]).is_empty(),
    ;
}
```

`points_to_model.rs`, with `PointsToUnaligned` (M3):

```rust
impl<T: ?Sized> PointsToUnaligned<T> {
    /// Converts a mutable borrow of an untyped permission and a mutable borrow of a typed value, with the given pointer metadata,
    /// into one mutably borrowed `PointsToUnaligned` permission.
    /// The borrowed parts' final values are the final permission's parts.
    /// It says nothing about `wf()`: callers prove it from the parts.
    pub axiom fn from_raw_parts_mut<'a>(
        tracked pt_untyped: &'a mut PointsToUntyped,
        tracked typed_value: &'a mut TypedValue<T>,
        metadata: Metadata<T>,
    ) -> (tracked out: &'a mut Self)
        ensures
            out.pt_untyped() == *old(pt_untyped),
            out.typed_value() == *old(typed_value),
            out.metadata() == metadata,
            *final(pt_untyped) == final(out).pt_untyped(),
            *final(typed_value) == final(out).typed_value(),
    ;
}
```

`points_to_model.rs`, with `PointsTo` (M4):

```rust
impl<T: ?Sized> PointsTo<T> {
    /// A mutably borrowed `PointsToUnaligned<T>` acts as a mutably borrowed `PointsTo<T>`
    /// (the `&mut` counterpart of the `shr_ref_struct_wrap` in `as_aligned`).
    pub axiom fn from_unaligned_mut<'a>(tracked u: &'a mut PointsToUnaligned<T>)
        -> (tracked out: &'a mut Self)
        ensures
            out.pt_unaligned() == *old(u),
            *final(u) == final(out).pt_unaligned(),
    ;
}
```

`points_to_model.rs`, with `SeqPointsTo` (M5):

```rust
impl<T, P: PTProperties<A = T>> SeqPointsTo<T, P> {
    /// A mutably borrowed `Seq<P>` acts as a mutably borrowed `SeqPointsTo<T, P>` with the given pointer.
    pub axiom fn from_seq_mut<'a>(tracked s: &'a mut Seq<P>, ptr: *mut [T]) -> (tracked out: &'a mut Self)
        ensures
            out.seq_pt() == *old(s),
            out.ptr() == ptr,
            *final(s) == final(out).seq_pt(),
    ;
}
```

**Mutable value borrow** (`points_to_model.rs`; already in the code).

```rust
impl<T> PointsTo<T> {
    /// This takes a mutable borrow of the `T` from a mutable borrow of a `PointsTo<T>`.
    /// The pointer of this borrow matches the permission's pointer.
    ///
    /// Writing through the reference updates both the value and the underlying bytes,
    /// so `final(self)` is well-formed with bytes that decode to the final value.
    /// This is an axiom because the bytes live in separate ghost state from the `TypedValue<T>`,
    /// so they can't be updated through a borrow of the value alone.
    pub axiom fn borrow_mut(tracked &mut self) -> (tracked val: &mut T)
        requires
            self.wf(),
            self.is_valid(),
        ensures
            *val == old(self).value(),
            mut_ref_ptr(val) == old(self).ptr(),
            final(self).is_valid(),
            final(self).ptr() == old(self).ptr(),
            final(self).value() == *final(val),
            final(self).wf(),
    ;
}
```

**Allocation** (phase 2c; `global_alloc_id` in `ptr_model.rs` next to `AllocId`, `allocate` / `deallocate` in `ptr_specs.rs`).

`ptr_model.rs`, next to `AllocId`:

```rust
/// The `AllocId` of allocations made by the global allocator.
pub uninterp spec fn global_alloc_id() -> AllocId;
```

`ptr_specs.rs`:

```rust
/// Allocate with the global allocator.
/// The precondition should be consistent with the
/// [documented safety conditions on `alloc`](https://doc.rust-lang.org/alloc/alloc/trait.GlobalAlloc.html#tymethod.alloc).
/// Returns a pointer with a corresponding [`PointsToUntyped`] permission.
/// The byte contents are arbitrary (uninitialized).
///
/// Here we allocate exactly the size of memory requested
/// (shown by having both the `Provenance` `orig_size` and `alloc_len` be the provided `size`).
/// This is a stronger guarantee than `Allocator::allocate`, which may allocate a larger block of memory.
#[cfg(feature = "std")]
#[verifier::external_body]
pub fn allocate(size: usize, align: usize) -> ((ptr, perm): (*mut u8, Tracked<PointsToUntyped>))
    requires
        valid_layout(size, align),
        size != 0,
    ensures
        perm@.ptr() == ptr_mut_from_data::<[u8]>(
            PtrData { addr: ptr@.addr, provenance: ptr@.provenance, metadata: size },
        ),
        perm@.wf(),
        ptr@.provenance is Some,
        ptr@.addr == ptr@.provenance.unwrap().start_addr(),
        ptr@.provenance.unwrap().alloc_len() == size,
        ptr@.provenance.unwrap().orig_size() == size,
        ptr@.provenance.unwrap().alignment() == align,
        ptr@.provenance.unwrap().alloc_id() == global_alloc_id(),
        // ptr@.addr % align == 0 and ptr@.addr + size <= usize::MAX follow from provenance_properties.
    opens_invariants none
{
    // SAFETY: valid_layout is a precondition
    let layout = unsafe { alloc::alloc::Layout::from_size_align_unchecked(size, align) };
    // SAFETY: size != 0
    let ptr = unsafe { ::alloc::alloc::alloc(layout) };
    if ptr == core::ptr::null_mut() {
        std::process::abort();
    }
    (ptr, Tracked::assume_new())
}

/// Deallocate with the global allocator.
///
/// The provenance ensures that the
/// [documented safety conditions on `dealloc`](https://doc.rust-lang.org/1.82.0/core/alloc/trait.GlobalAlloc.html#tymethod.dealloc)
/// are satisfied; by also giving up the [`PointsToUntyped`] permission for the whole allocation,
/// we ensure there can be no use-after-free bug as a result of this deallocation.
/// In order to do so, the parameters of the provenance and the [`PointsToUntyped`] permission
/// must match the parameters of the deallocation.
///
/// We have two different ways to track size within the provenance:
/// `orig_size`, the original requested size, and `alloc_len`, the size of memory actually allocated.
/// According to the `Allocator` documentation, it's possible to have `orig_size <= alloc_len`.
/// Here, we restrict them to be the same.
#[cfg(feature = "alloc")]
#[verifier::external_body]
pub fn deallocate(ptr: *mut u8, size: usize, align: usize, Tracked(perm): Tracked<PointsToUntyped>)
    requires
        perm.wf(),
        ptr@.provenance == perm.ptr()@.provenance,
        ptr@.addr == perm.ptr()@.addr,
        ptr@.provenance is Some,
        ptr@.provenance.unwrap().alloc_id() == global_alloc_id(),
        ptr@.addr == ptr@.provenance.unwrap().start_addr(),
        perm.len() == ptr@.provenance.unwrap().alloc_len(),
        size == ptr@.provenance.unwrap().orig_size(),
        align == ptr@.provenance.unwrap().alignment(),
    opens_invariants none
{
    // SAFETY: ensured by the provenance and the PointsToUntyped
    let layout = unsafe { alloc::alloc::Layout::from_size_align_unchecked(size, align) };
    unsafe {
        ::alloc::alloc::dealloc(ptr, layout);
    }
}
```

**`str` decoding** (rustlib).
`abs_decode::<str>` comes from rustlib's existing `EncodingStr` (with `abs_encode_impl_unsized`):
the bytes' length and each byte's `u8` decoding. UTF-8 validity is not part of decoding.

Not trusted: the shared `&TypedValue<str>` ↔ `&TypedValue<[u8]>` casts
(from rustlib's existing `str::as_bytes_tracked` / `str::from_bytes_tracked` axioms and `valid_ref`).
There are no owned or `&mut` `str` ↔ `[u8]` casts.
rustlib's existing `str` permission axioms (`perm_init`, `perm_value_eq`, `perm_ptr`)
are temporary stand-ins until `PointsTo<str>` is ported;
they're replaced by the above and not part of this design.

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
which are in [New axioms and axioms with bigger changes](#new-axioms-and-axioms-with-bigger-changes)
(`PointsToByte`'s, which are unchanged, are in `points_to_model.rs`).
`points_to_ops.rs` and `points_to_collections.rs` have no axioms.

### `PointsToByte` (phase 1)

Approved; the code is in `points_to_model.rs`.
`PointsToByte` is an `external_body` struct with uninterp `ptr` and `byte` functions.
Axioms: the `PTProperties` impl (`is_nonnull`, `ptr_bounds`, `provenance_not_none`, `is_disjoint`).

### `SeqPointsTo` and `PointsToUntyped`: specs (phase 1b)

Approved; the code is in `points_to_model.rs`.
Axioms: `SeqPointsTo::from_seq_mut` (M5)
(in [New axioms and axioms with bigger changes](#new-axioms-and-axioms-with-bigger-changes)).

### `TypedValue` (phase 2)

Approved; the code is in `points_to_model.rs`.
`value_ref` and `valid_ref` are new; the rest exists today.
Axioms: `TypedValue::<[T]>::from_elems_mut` (M1), `from_elems_ref`
(in [New axioms and axioms with bigger changes](#new-axioms-and-axioms-with-bigger-changes)).

### `PointsToUnaligned`: specs (phases 2, 2b; `str` in rustlib)

rustlib writes the `PTPhys`, `PTProperties` and `PTTypedValue` impls for `PointsToUnaligned<str>`
in the same shape as the `[T]` ones (`size(len) = len`; `additional_validity_constraints` is UTF-8 validity, `str::inv`, since `str` decoding is `EncodingStr`'s, which doesn't include it);
see [rustlib: `str`](#rustlib-str).
`PTPhys` is sealed by the crate-private `PTPhysSealed`,
but vstd's `impl<T: ?Sized> PTPhysSealed for PointsToUnaligned<T>` already covers `str`,
and vstd is a module of rustlib's `core`, so rustlib can write these impls.

Approved; the code is in `points_to_model.rs`.
Axioms: `PointsToUnaligned::from_raw_parts_ref`, `from_raw_parts_mut` (M3)
(in [New axioms and axioms with bigger changes](#new-axioms-and-axioms-with-bigger-changes)).

### `PointsTo`: specs (generic; phase 2, widened in phase 2b)

The generic impls name the `PointsToUnaligned` trait functions (`<PointsToUnaligned<T> as PTTypedValue>::...`),
since the inherent accessors don't unfold to them for a generic `T`.
`wf` is overridden: the trait's default body doesn't unfold at `PointsToUnaligned<T>` for a generic `T`,
so with the default, `self.wf()` doesn't give `pt_unaligned.wf()`, which every delegation needs
([phase 0, item 17](TYPED_POINTS_TO_IMPL_PLAN.md#phase-0-pending-checks)).

Approved; the code is in `points_to_model.rs`.
Axioms: `PointsTo::from_unaligned_mut` (M4), `borrow_mut`
(in [New axioms and axioms with bigger changes](#new-axioms-and-axioms-with-bigger-changes)).

### `points_to_ops.rs`: `SeqPointsTo`'s `PTProperties` and structural operations (phase 1b)

`points_to_ops.rs` is a child module of `points_to_model.rs`, so it can use the structs' private fields
([phase 0, item 15](TYPED_POINTS_TO_IMPL_PLAN.md#phase-0-pending-checks)).

Approved; the code is in `points_to_ops.rs`.

### `points_to_ops.rs`: `PointsToUntyped`'s proofs (phase 1b)

Approved; the code is in `points_to_ops.rs`.
`join_ref` / `join_mut` are proved from the `Seq` join axioms
(`Seq::tracked_add_borrow` / `tracked_add_borrow_mut`, in [New axioms and axioms with bigger changes](#new-axioms-and-axioms-with-bigger-changes)).

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

`from_seq`, `empty`, `into_seq`, `tracked_seq_pt(_mut)` and `index_mut` have no typed versions.
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

```rust
/// The pointer of the given permission.
pub uninterp spec fn perm_ptr<T: ?Sized>(perm: &PointsTo<T>) -> *mut T;

pub open spec fn valid_indices_slice_points_to<T>(start: int, end: int, slice: &PointsTo<[T]>) -> bool {
    0 <= start <= end <= slice.len()
}

/// For a `str` permission, the indices must be within the pointer's metadata,
/// and, if the permission holds a value, on char boundaries of the value.
pub open spec fn valid_indices_str_points_to(start: int, end: int, slice: &PointsTo<str>) -> bool {
    &&& 0 <= start <= end <= slice.ptr()@.metadata
    &&& slice.typed_value().is_valid() ==> {
        &&& is_char_boundary(slice.value(), start)
        &&& is_char_boundary(slice.value(), end)
    }
}

pub broadcast axiom fn def_valid_indices_str_points_to(start: int, end: int, slice: &PointsTo<str>)
    ensures
        valid_indices_str_points_to(start, end, slice) <==> #[trigger] valid_indices(
            start,
            end,
            slice,
        ),
;

pub broadcast axiom fn def_perm_ptr_slice<T>(perm: &PointsTo<[T]>)
    ensures
        #[trigger] perm_ptr(perm) == perm.ptr(),
;

pub broadcast axiom fn def_perm_ptr_str(perm: &PointsTo<str>)
    ensures
        #[trigger] perm_ptr(perm) == perm.ptr(),
;

/// True when the given permission is well-formed.
pub uninterp spec fn perm_wf<T: ?Sized>(perm: &PointsTo<T>) -> bool;

pub broadcast axiom fn def_perm_wf_slice<T>(perm: &PointsTo<[T]>)
    ensures
        #[trigger] perm_wf(perm) <==> perm.wf(),
;

pub broadcast axiom fn def_perm_wf_str(perm: &PointsTo<str>)
    ensures
        #[trigger] perm_wf(perm) <==> perm.wf(),
;

/// True when the given permission is (fully) initialized and well-formed.
pub open spec fn perm_init<T: ?Sized>(perm: &PointsTo<T>) -> bool {
    perm.is_valid() && perm_wf(perm)
}

pub broadcast axiom fn def_perm_value_eq_slice<T>(perm: &PointsTo<[T]>, val: &[T])
    ensures
        #[trigger] perm_value_eq(perm, val) <==> perm.value() == val@,
;

pub broadcast axiom fn def_perm_value_eq_str(perm: &PointsTo<str>, val: &str)
    ensures
        #[trigger] perm_value_eq(perm, val) <==> perm.typed_value().value_ref() == val,
;
```
