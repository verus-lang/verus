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
| `PointsToUnaligned<str>` | `PTPhys`, `PTProperties`: per type | yes | no | rustlib | after phase 3b ([specs](TYPED_POINTS_TO_PLAN.md#str-rustlib)) |
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
| `PTPhys for PointsToUnaligned<_>` | per type | `ptr` (same shape each time), the `size` formula, `wf_basic` (one call to the generic `wf_basic_unaligned`), and `ptrs_len_same` / `stays_wf_basic` (delegating to the untyped bytes) |
| `PTProperties for PointsToUnaligned<_>` | per type (same body each time) | the pointer-level lemmas, all delegating to the untyped bytes |
| `PTTypedValue for PointsToUnaligned<_>` | per type | `typed_value`, `bytes`, `metadata_matches`, `satisfies_alignment` (`true`); the lemmas `bytes_decode`, `satisfies_alignment_of_wf`, `lemma_wf_basic` (empty proofs), `lemma_ptrs_len_same_valid`, `stays_wf` |
| `PTValueOps for PointsToUnaligned<_>` | per type | the operations that touch the fields (`borrow_typed_value`, `take_typed_value`, `put_typed_value`, `into_untyped_with_typed_value`, `from_untyped_with_typed_value`, `as_untyped`, `as_untyped_mut`) |
| `PTSizedValue for PointsToUnaligned<T>` | once (Sized `T` only) | the two lemmas |
| `PTPhys`, `PTProperties`, `View`, `PTTypedValue`, `PTValueOps` for `PointsTo<T: ?Sized>` | once (generic) | delegation to `self.pt_unaligned`, except `satisfies_alignment` (adds alignment) and `from_untyped_with_typed_value` (wraps the result) |
| `PTSizedValue for PointsTo<T>` | once (Sized `T` only) | the two lemmas (`lemma_satisfies_alignment_offset` has the real alignment proof) |
| trait default bodies | once (in the traits) | `PTTypedValue::wf`, `ptrs_len_same_valid`; `PTValueOps::borrow`, `into_untyped`, `from_untyped`, `zero_sized`; `PTSizedValue::take`, `put`, `copy`, `copy_typed_value`, `from_untyped_with_value` |
| `impl<T: ?Sized> PointsToUnaligned<T> where PointsToUnaligned<T>: PTValueOps<A = T>` | once (generic) | `into_aligned`, `as_aligned`, `as_aligned_mut` |
| `impl<T: ?Sized> PointsTo<T> where PointsToUnaligned<T>: PTValueOps<A = T>` | once (generic) | `into_unaligned`, `as_unaligned`, `as_unaligned_mut` |
| `impl<T> PointsToUnaligned<[T]>` | once (slices) | `borrow_index` and the borrowed constructors (`from_untyped_ref`, `from_untyped_with_value_ref`): the primary implementations |
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
| `PointsToUnaligned<str>` ↔ `PointsToUnaligned<[u8]>` | no | yes | no | rustlib | after phase 3b ([specs](TYPED_POINTS_TO_PLAN.md#str-rustlib)) |
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
| well-formedness: every `PTPhys` impl (`ptr`, `size`, `wf_basic`, `ptrs_len_same`, `stays_wf_basic`), every `PTTypedValue` impl (`typed_value`, `bytes`, `metadata_matches`, `satisfies_alignment`, `ptrs_len_same_valid`, and the lemmas `bytes_decode`, `satisfies_alignment_of_wf`, `lemma_wf_basic`, `lemma_ptrs_len_same_valid`, `stays_wf`), `wf_basic_unaligned`, `PointsToUntyped::wf` and `bytes` | the structural `SeqPointsTo` impl (except the field primitives and M5) and `PointsToUntyped`'s proofs | |
| the axioms: `PointsToByte`'s `PTProperties` impl, `PointsToUntyped::join_ref` / `join_mut`, `from_raw_parts_ref`, `TypedValue::from_elems_ref`, M1, M3–M5, `PointsTo::borrow_mut` | the aligned/unaligned conversions | the sequence → slice conversions (`as_slice_pt`, `as_slice_pt_mut`) |
| the tracked getters and byte disjointness: `TypedValue::tracked_copy`, `valid_ref`; `PointsToByte::is_disjoint_byte`; the field primitives, which say nothing about `wf`: `SeqPointsTo::tracked_seq_pt`, `tracked_seq_pt_mut`, `into_seq`, `PointsToUnaligned::tracked_pt_untyped`, `tracked_typed_value`, `into_raw_parts`, `from_raw_parts`, `as_raw_parts_mut`, `PointsTo::tracked_pt_unaligned` | the slice permissions' `len`, `borrow_index` and borrowed constructors (`from_untyped_ref`, `from_untyped_with_value_ref`); `is_aligned`, `is_disjoint_pointsto`, `is_disjoint_unaligned`; `group_points_to_lemmas` | `group_points_to_collections_lemmas` |

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
| `PointsToByte`'s `is_nonnull`, `ptr_bounds`, `provenance_not_none`, `is_disjoint` | `points_to_model.rs` | A byte permission's pointer is non-null, within its allocation, has non-null provenance; two byte permissions are at different addresses. | `PointsToUntyped`'s and `PointsToRaw`'s pointer-level lemmas || `ProvenanceData` (`external_body`; `uninterp` `start_addr`, `alloc_len`, `alignment`, `orig_size`, `alloc_id`), `provenance_properties` | `ptr_model.rs` | The allocation model. `orig_size` replaces `Dealloc`'s size tracking. | pointer bounds, `allocate` / `deallocate` |
| pointer model: `View for *mut T` (`uninterp`), `ptr_mut_from_data` (`uninterp`), `axiom_ptr_mut_from_data`, `ptrs_mut_eq`, `tracked_ptr_mut_from_data` | `ptr_model.rs` | A pointer is its `PtrData` (address, provenance, metadata). | every pointer spec (e.g. the generic `PointsToUnaligned` pointer built from its metadata) |
| `assume_specification`s for pointer `==`, `null`, `null_mut`, `addr`, `with_addr`; the `cast_*` `external_body` functions | `ptr_specs.rs` | The exec pointer operations match the model. | exec code |
| `SharedReference` (`external_body`; `uninterp` `value`, `ptr`), `ptr_nonnull`, `axiom_shared_ref_value_view` | `shared_reference.rs` | A shared reference with its pointer. | exec code; the source of valid shared permissions |
| `shared_ref_ptr` (`uninterp`), `mut_ref_slice_len`, `ptr_mut_ref_join`, `tracked_mut_ref_slice_subrange`, `tracked_mut_ref_slice_idx`, `cast_mut_ref_to_ptr`, `cast_mut_ref_slice_to_ptr`, `cast_mut_ref_str_to_ptr` | `ptr_specs.rs` | Reference ↔ pointer and permission boundary. | exec code; the source of valid permissions |
| `abs_encode`, `abs_decode`, `abs_can_be_encoded` (`uninterp`); `encode_decode_len`, `encode_decode_inverse`, `shared_ref_cannot_be_encoded`; the per-type encoding impls | `type_representation.rs` | The abstract-byte encoding of values. | every decode clause |
| layout axioms (`layout_of_sized`, `layout_of_slices`, `layout_of_str`, `layout_of_unit_tuple`, `align_properties`, …) | `layout.rs` | Sizes and alignments of types and values. | sizes, `satisfies_alignment`, `lemma_satisfies_alignment_offset`, the `zero_sized` default |
| `tracked_swap`, `tracked_static_mut_ref` | `modes.rs` | Swapping tracked values; a `'static` borrow of an owned value. | `take_typed_value`, empty cases of borrowed conversions |
| `Seq` tracked operations (`tracked_borrow`, `tracked_borrow_mut`, `tracked_borrow_subrange_mut`, …) | `seq.rs` | Borrowing parts of a tracked `Seq`. | `as_untyped_mut`, `index_mut` |
| `Map` tracked operations (`tracked_empty`, `tracked_remove_keys`, `tracked_union_prefer_right`, …) | `map.rs` | Building and splitting a tracked `Map`. | `PointsToRaw` |
| `shr_ref_struct_wrap` | builtin | Borrowing a struct from a borrow of its only tracked field. | `as_aligned`, `subrange_basic`, `split_ref` |

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
| `mut_ref_to_shr_points_to_str` (rustlib) | rustlib | Moved from vstd's commented-out code; now ensures `pt.wf()`. | the source of valid `str` permissions from `&mut str` |
| `SharedReference<str>::points_to` (rustlib) | rustlib | Moved from vstd's commented-out code; now ensures `pt.wf()`. | the source of valid shared `str` permissions |
| `ptr_ref2_str_ghost` (rustlib) | rustlib | Moved from vstd's commented-out code; now requires `perm.wf()`. | `SharedReference<str>` from a `str` permission |

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
        v@ == perm.typed_value().value_ref()@,
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
        pt.typed_value().value_ref()@ == (*old(*mut_ref))@,
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
            pt.typed_value().value_ref()@ == self.value()@,
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
        v.value()@ == perm.typed_value().value_ref()@,
        v.ptr() == ptr,
;
```

rustlib, the `str` versions (moved from vstd's commented-out code):

```rust
impl<'a> SharedReference<'a, str> {
    pub axiom fn points_to(tracked self) -> (tracked pt: &'a PointsTo<str>)
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
    ensures
        pt.ptr() == mut_ref_ptr(*mut_ref),
        pt.is_valid(),
        pt.typed_value().value_ref() == &*old(*mut_ref),
        pt.wf(),
        &*final(*mut_ref) == &*old(*mut_ref),
;
```

## New axioms and axioms with bigger changes

Every new trusted item, relative to the `verify-rustlib` branch.

| Item | File | What it states | Uses | Approved by Travis/Natalie |
|---|---|---|---|---|
| `ptr_mut_ref` (`external_body`; existing, strengthened, already in the code) | `ptr_specs.rs` | Now also ensures `final(perm).wf()`: the final bytes decode to the final value (and requires `old(perm).wf()`). | exec writes through `&mut T` | yes |
| `ptr_mut_ref_slice` (`external_body`; restored, phase 4b) | `ptr_specs.rs` | Restored from commented-out code, strengthened the same way as `ptr_mut_ref`. | exec writes through `&mut [T]` | yes |
| `ptr_mut_ref_str` (`external_body`; rustlib) | rustlib | Moved from vstd's commented-out code, strengthened the same way as `ptr_mut_ref`. | exec writes through `&mut str` | yes |
| `Seq::tracked_borrow_subrange` (`external_body`; already in the code) | `seq.rs` | Borrows a subrange of a borrowed tracked `Seq`. | `subrange_basic`, `split_ref` | yes |
| `Seq::tracked_split_borrow_mut` (`external_body`; already in the code) | `seq.rs` | Splits a mutable borrow of a tracked `Seq` in two. | `subrange_mut`, the `&mut` conversions | yes |
| `tracked_slice_index` (phase 3b) | `slice.rs` | Borrows an element of a borrowed slice. | `borrow_index` | yes |
| `TypedValue::<[T]>::from_elems_ref` (phase 3b) | `points_to_model.rs` | Per-element shared typed values act as one shared slice typed value (the shared counterpart of M1). Replaces the generic `tracked_slice_from_refs`, so it only covers `TypedValue`s, which have no physical memory. | shared sequence → slice | |
| `tracked_ref` (phase 3b) | `modes.rs` | A borrow is a borrowed `Tracked` of itself. | `TypedValue::valid_ref` | yes |
| `PointsToUnaligned::from_raw_parts_ref` (phase 3b) | `points_to_model.rs` | Borrowed bytes and typed value act as one borrowed permission. | borrowed constructors, `borrow_index`, sequence → slice, `str` ↔ `[u8]` | yes |
| M1 `TypedValue::<[T]>::from_elems_mut` (phase 3b) | `points_to_model.rs` | Per-element `&mut` typed values act as one `&mut` slice typed value. | `&mut` sequence → slice | yes |
| M3 `PointsToUnaligned::from_raw_parts_mut` (phase 3b) | `points_to_model.rs` | `&mut` bytes and typed value act as one `&mut` permission. | `&mut` conversions | yes |
| M4 `PointsTo::from_unaligned_mut` (phase 3b) | `points_to_model.rs` | A `&mut PointsToUnaligned` acts as a `&mut PointsTo`. | `as_aligned_mut`, aligned `&mut` conversions | yes |
| M5 `SeqPointsTo::from_seq_mut` (phase 3b) | `points_to_model.rs` | A `&mut Seq<P>` acts as a `&mut SeqPointsTo`. | `subrange_mut`, `split_mut` | yes |
| `PointsToUntyped::join_ref` (already in the code) | `points_to_model.rs` | Two borrowed untyped permissions, the second starting where the first ends, act as one borrowed permission. | the typed sequences' `as_untyped`, shared sequence → slice | |
| `PointsToUntyped::join_mut` (already in the code) | `points_to_model.rs` | The same for mutable borrows; the parts' final values are tied back if the joined permission keeps its pointers and length. | the typed sequences' `as_untyped_mut`, `&mut` sequence → slice | |
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
with the value stated as `typed_value().value_ref()@` in place of the old `value()` (a `Seq<T>`):

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
        old(perm).typed_value().value_ref()@ == v@,
        final(perm).typed_value().value_ref()@ == final(v)@,
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
        // The final bytes decode to the final value.
        final(perm).wf(),
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
```

`modes.rs`, next to `tracked_swap`:

```rust
/// Converts a borrowed value to a borrowed `Tracked` of that value.
pub axiom fn tracked_ref<'a, T: ?Sized>(tracked t: &'a T) -> (tracked out: &'a Tracked<T>)
    ensures
        &**out == t,
;
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
                &&& out.value()@ == Seq::new(elems.len(), |i: int| elems[i].value())
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
                &&& out.value()@ == Seq::new(elems.len(), |i: int| elems[i].value())
            },
            !(forall|i: int| #![trigger elems[i]] 0 <= i < elems.len() ==> elems[i].is_valid()) ==> out.is_empty(),
            // Finally: a valid slice of the same length is distributed back to the elements;
            // anything else leaves every element empty.
            final(out).is_valid() && final(out).value()@.len() == elems.len() ==> forall|i: int|
                #![trigger elems[i]]
                0 <= i < elems.len() ==> {
                    &&& final(elems[i]).is_valid()
                    &&& final(elems[i]).value() == final(out).value()@[i]
                },
            !(final(out).is_valid() && final(out).value()@.len() == elems.len()) ==> forall|i: int|
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

**Untyped joins** (`points_to_model.rs`; new relative to `verify-rustlib`, already in the code).
The contracts are the code's,
with `ptrs_len_same_valid` renamed `ptrs_len_same` and "singleton" renamed "byte" in the docs.

```rust
impl PointsToUntyped {
    /// Joins shared borrows of two `PointsToUntyped` permissions into a shared borrow of a
    /// single `PointsToUntyped`, under the same conditions as `join`.
    ///
    /// This is the shared-borrow analogue of `join`. It's an axiom because the joined permission
    /// isn't stored anywhere that could be borrowed.
    pub axiom fn join_ref<'a>(tracked &'a self, tracked other: &'a Self) -> (tracked joined: &'a Self)
        requires
            self.wf(),
            other.wf(),
            self.ptr()@.provenance == other.ptr()@.provenance,
            other.ptr()@.addr == self.ptr()@.addr + self.len(),
        ensures
            joined.seq_pt() == self.seq_pt() + other.seq_pt(),
            joined.bytes() == self.bytes() + other.bytes(),
            joined.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: self.ptr()@.addr,
                    provenance: self.ptr()@.provenance,
                    metadata: (self.len() + other.len()) as usize,
                },
            ),
            joined.wf(),
    ;

    /// Joins mutable borrows of two `PointsToUntyped` permissions into a mutable borrow of a
    /// single `PointsToUntyped`, under the same conditions as `join`.
    ///
    /// If the joined permission keeps its pointers and length, then so do `self` and `other`, and
    /// their final byte permissions concatenate to the joined permission's final ones.
    ///
    /// This is the mutable-borrow analogue of `join`. It's an axiom because the joined permission
    /// isn't stored anywhere that could be borrowed.
    pub axiom fn join_mut<'a>(tracked &'a mut self, tracked other: &'a mut Self) -> (tracked joined:
        &'a mut Self)
        requires
            self.wf(),
            other.wf(),
            self.ptr()@.provenance == other.ptr()@.provenance,
            other.ptr()@.addr == self.ptr()@.addr + self.len(),
        ensures
            joined.seq_pt() == old(self).seq_pt() + old(other).seq_pt(),
            joined.bytes() == old(self).bytes() + old(other).bytes(),
            joined.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: old(self).ptr()@.addr,
                    provenance: old(self).ptr()@.provenance,
                    metadata: (old(self).len() + old(other).len()) as usize,
                },
            ),
            joined.wf(),
            Self::ptrs_len_same(*joined, *final(joined)) ==> {
                &&& final(self).ptr() == old(self).ptr()
                &&& final(other).ptr() == old(other).ptr()
                &&& final(self).wf()
                &&& final(other).wf()
                &&& final(joined).seq_pt() == final(self).seq_pt() + final(other).seq_pt()
                &&& final(joined).bytes() == final(self).bytes() + final(other).bytes()
            },
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
rustlib's existing `str` permission axioms (`as_str_ptr_verus`, `perm_init`, `perm_value_eq`, `perm_ptr`)
are temporary stand-ins until `PointsTo<str>` is ported;
they're replaced by the above and not part of this design.

## Trait definitions

| Trait | Contents | Impls in |
|---|---|---|
| `PTPhys` | the pointer and size; pointer-level well-formedness (`wf_basic`) and its preservation (`ptrs_len_same`, `stays_wf_basic`) | `points_to_model.rs` |
| `PTProperties` | the pointer lemmas (`is_nonnull`, `ptr_bounds`, `provenance_not_none`, `is_disjoint`) | `points_to_ops.rs` (`PointsToByte`'s, which are axioms: `points_to_model.rs`) |
| `PTTypedValue` | the typed value and bytes; well-formedness (`wf`) and its preservation (`ptrs_len_same_valid`, `lemma_ptrs_len_same_valid`, `stays_wf`) | `points_to_model.rs` |
| `PTValueOps` | the operations: borrowing, taking and putting the typed value, the untyped conversions, `zero_sized` | `points_to_ops.rs` |
| `PTSizedValue` | the operations on `Sized` values | `points_to_ops.rs` |

```rust
// A private seal trait to prevent `PTPhys` from being implemented outside of vstd.
pub(crate) trait PTPhysSealed {}

/// Defines the physical memory region that a `PointsTo` permission covers,
/// by specifying the pointer to memory and the size of the pointed-to region.
/// Additionally defines pointer-level well-formedness which is required 
/// for proving properties that hold for any `PointsTo` permission, 
/// along with the conditions that preserve well-formedness.
#[allow(private_bounds)]
pub trait PTPhys: Sized + PTPhysSealed {
    type A: ?Sized;

    /// The pointer that this permission is associated with.
    spec fn ptr(self) -> *mut Self::A;

    /// The size, in bytes, of the memory region tracked by a permission
    /// whose pointer has the given metadata.
    /// A permission `p` tracks `Self::size(p.ptr()@.metadata)` bytes.
    spec fn size(metadata: Metadata<Self::A>) -> nat;

    /// Define basic well-formedness conditions on the permission's pointer
    /// which are necessary to ensure all of the `PTProperties` requirements.
    /// `PTTypedValue::wf` builds on this to add conditions on the bytes and typed value,
    /// as well as adding pointer conditions specific to a given permission type.
    spec fn wf_basic(self) -> bool;

    /// Specifies necessary conditions for ensuring that `new` and `old` are permissions 
    /// to the same region of memory and that `wf_basic` carries over from `old`: 
    /// `new` must keep `old`'s pointers and length.
    /// Each implementation defines what this means for its permission type.
    spec fn ptrs_len_same(old: Self, new: Self) -> bool;

    /// If `old` satisfies `wf_basic` and `new` satisfies `ptrs_len_same` with respect to it,
    /// then `new` satisfies `wf_basic`.
    proof fn stays_wf_basic(old: Self, new: Self)
        requires
            old.wf_basic(),
            Self::ptrs_len_same(old, new),
        ensures
            new.wf_basic(),
    ;
}

/// Defines properties which should hold of any `PointsTo` permission.
pub trait PTProperties: PTPhys {
    /// Guarantee that the pointer is non-null.
    ///
    /// See <https://doc.rust-lang.org/std/ptr/#safety>
    proof fn is_nonnull(tracked &self)
        requires
            self.wf_basic(),
        ensures
            self.ptr()@.addr != 0,
    ;

    /// The memory associated with a pointer should always be within bounds of its spatial provenance.
    proof fn ptr_bounds(tracked &self)
        requires
            self.ptr()@.provenance.is_some(),
            self.wf_basic(),
        ensures
            self.ptr()@.addr as int >= self.ptr()@.provenance.unwrap().start_addr(),
            self.ptr()@.addr + Self::size(self.ptr()@.metadata)
                <= self.ptr()@.provenance.unwrap().start_addr() + self.ptr()@.provenance.unwrap().alloc_len(),
    ;

    /// If the size of the pointed-to region is nonzero,
    /// then the pointer's provenance is non-null.
    proof fn provenance_not_none(tracked &self)
        requires
            Self::size(self.ptr()@.metadata) != 0,
            self.wf_basic(),
        ensures
            self.ptr()@.provenance != Provenance::None,
    ;

    /// Guarantees that the memory ranges associated with two distinct, non-ZST permissions will not overlap,
    /// since you cannot have two permissions to the same memory.
    /// (`self` is an &mut reference to enforce distinctness,
    /// so you cannot pass the same PointsTo as both arguments.)
    /// Since both memory regions are non-zero-sized, this implies the pointers have distinct addresses.
    ///
    /// Note: If either memory region is zero-sized, we get disjointness "for free" without having to call this axiom,
    /// since the empty memory range corresponding to a ZST cannot possibly intersect with any other memory.
    /// However, note that if one type is a ZST and the other is a non-ZST,
    /// the disjointness definition as stated here does not hold,
    /// since the ZST pointer could be in the middle of the non-ZST's range.
    ///
    /// Both permissions must be `wf_basic`, since that is what ties `size` to the memory actually held.
    proof fn is_disjoint<OtherPointsToPerm: PTPhys>(
        tracked &mut self,
        tracked other: &OtherPointsToPerm,
    )
        requires
            Self::size(self.ptr()@.metadata) != 0,
            OtherPointsToPerm::size(other.ptr()@.metadata) != 0,
            self.wf_basic(),
            other.wf_basic(),
        ensures
            *old(self) == *final(self),
            final(self).ptr()@.addr + Self::size(final(self).ptr()@.metadata) <= other.ptr()@.addr
                || other.ptr()@.addr + OtherPointsToPerm::size(other.ptr()@.metadata) <= final(self).ptr()@.addr,
    ;
}

/// Defines the typed data tracked by a `PointsTo` permission
/// to a single, possibly-valid value of type `Self::A`,
/// along with well-formedness conditions and the conditions that preserve them.
pub trait PTTypedValue: PTPhys {
    /// The (possibly-valid) typed value that this permission tracks.
    spec fn typed_value(self) -> TypedValue<Self::A>;

    /// The abstract bytes of the memory that this permission tracks.
    spec fn bytes(self) -> Seq<AbstractByte>;

    /// Well-formedness: the pointer-level conditions (`wf_basic`),
    /// the alignment requirement for this permission type,
    /// and validity constraints.
    open spec fn wf(self) -> bool {
        &&& self.wf_basic()
        &&& Self::satisfies_alignment(self.ptr()@.addr)
        &&& self.typed_value().is_valid() ==> {
            &&& abs_decode(self.bytes(), self.typed_value().value_ref())
            &&& Self::metadata_matches(self.typed_value().value_ref(), self.ptr()@.metadata)
        }
    }

    /// Whether the pointer metadata `metadata` is consistent with `value`.
    /// For a slice, this means the slice has `metadata` elements;
    /// for other types, it is always `true`.
    spec fn metadata_matches(value: &Self::A, metadata: Metadata<Self::A>) -> bool;

    /// Whether `addr` satisfies this permission type's alignment requirement:
    /// alignment to `Self::A` for `PointsTo`,
    /// and no requirement (`true`) for `PointsToUnaligned`.
    spec fn satisfies_alignment(addr: usize) -> bool;

    /// Specifies conditions which must hold on the bytes and typed value if the permission is well-formed.
    proof fn bytes_decode(&self)
        requires
            self.wf(),
        ensures
            self.bytes().len() == Self::size(self.ptr()@.metadata),
            self.typed_value().is_valid() ==> {
                &&& abs_decode(self.bytes(), self.typed_value().value_ref())
                &&& Self::metadata_matches(self.typed_value().value_ref(), self.ptr()@.metadata)
            },
    ;

    /// A well-formed permission's address satisfies the alignment requirement.
    proof fn satisfies_alignment_of_wf(&self)
        requires
            self.wf(),
        ensures
            Self::satisfies_alignment(self.ptr()@.addr),
    ;

    /// Well-formedness implies the pointer-level well-formedness.
    proof fn lemma_wf_basic(&self)
        requires
            self.wf(),
        ensures
            self.wf_basic(),
    ;

    /// Invariants which must hold between `old` and `new` to preserve well-formedness (see `stays_wf`).
    open spec fn ptrs_len_same_valid(old: Self, new: Self) -> bool {
        &&& Self::ptrs_len_same(old, new)
        &&& new.typed_value().is_valid() ==> {
            &&& abs_decode(new.bytes(), new.typed_value().value_ref())
            &&& Self::metadata_matches(new.typed_value().value_ref(), new.ptr()@.metadata)
        }
    }

    /// Two well-formed permissions with the same pointer satisfy `ptrs_len_same_valid`.
    broadcast proof fn lemma_ptrs_len_same_valid(old: Self, new: Self)
        requires
            old.wf(),
            new.wf(),
            new.ptr() == old.ptr(),
        ensures
            #[trigger] Self::ptrs_len_same_valid(old, new),
    ;

    /// If `old` is well-formed and `new` satisfies `ptrs_len_same_valid`,
    /// then `new` is well-formed.
    proof fn stays_wf(old: Self, new: Self)
        requires
            old.wf(),
            Self::ptrs_len_same_valid(old, new),
        ensures
            new.wf(),
    ;
}

/// Defines constructors and conversions
/// for a `PointsTo` permission to a single, possibly-valid value of type `Self::A`.
pub trait PTValueOps: PTTypedValue + PTProperties {
    /// Creates an empty permission to a zero-sized region,
    /// at any non-null, in-bounds pointer that satisfies the alignment requirement.
    proof fn zero_sized(ptr: *mut Self::A) -> (tracked out: Self)
        requires
            ptr@.addr != 0,
            ptr_addr_in_bounds(ptr),
            Self::size(ptr@.metadata) == 0,
            Self::satisfies_alignment(ptr@.addr),
        ensures
            out.ptr() == ptr,
            out.bytes().len() == 0,
            out.typed_value().is_empty(),
            out.wf(),
    {
        broadcast use axiom_ptr_mut_from_data, ptrs_mut_eq, layout_of_unit_tuple;

        // PointsToUntyped::zero_sized needs a pointer to a zero-sized type.
        let tracked pt_untyped = PointsToUntyped::zero_sized(ptr_mut_from_data::<()>(
            PtrData { addr: ptr@.addr, provenance: ptr@.provenance, metadata: () },
        ));
        Self::from_untyped(pt_untyped, ptr@.metadata)
    }

    /// Borrows the typed value.
    proof fn borrow_typed_value(tracked &self) -> tracked &TypedValue<Self::A>
        requires
            self.wf(),
        returns
            self.typed_value(),
    ;

    /// Moves the typed value out, leaving `self` empty.
    proof fn take_typed_value(tracked &mut self) -> (tracked v: TypedValue<Self::A>)
        requires
            self.wf(),
        ensures
            v == old(self).typed_value(),
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).typed_value().is_empty(),
            final(self).wf(),
    ;

    /// Replaces the typed value with `v`.
    /// If `v` is valid, the bytes must decode to its value and the metadata must match it.
    proof fn put_typed_value(tracked &mut self, tracked v: TypedValue<Self::A>)
        requires
            self.wf(),
            v.is_valid() ==> {
                &&& abs_decode(self.bytes(), v.value_ref())
                &&& Self::metadata_matches(v.value_ref(), self.ptr()@.metadata)
            },
        ensures
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).typed_value() == v,
            final(self).wf(),
    ;

    /// Borrows the value, which must be valid.
    proof fn borrow(tracked &self) -> tracked &Self::A
        requires
            self.wf(),
            self.typed_value().is_valid(),
        returns
            self.typed_value().value_ref(),
    {
        match self.borrow_typed_value() {
            TypedValue::Valid(b) => b,
            TypedValue::Empty => proof_from_false(),
        }
    }

    /// Splits the permission into an untyped permission to the same bytes and the typed value.
    proof fn into_untyped_with_typed_value(tracked self) -> (tracked (pt_untyped, v): (PointsToUntyped, TypedValue<Self::A>))
        requires
            self.wf(),
        ensures
            pt_untyped.ptr() == ptr_mut_from_data::<[u8]>(PtrData {
                addr: self.ptr()@.addr,
                provenance: self.ptr()@.provenance,
                metadata: Self::size(self.ptr()@.metadata) as usize,
            }),
            pt_untyped.bytes() == self.bytes(),
            pt_untyped.wf(),
            v == self.typed_value(),
    ;

    /// Creates a permission from an untyped permission, a typed value and pointer metadata.
    /// The inverse of `into_untyped_with_typed_value`.
    /// If `typed_value` is valid, the bytes must decode to its value and the metadata must match it.
    proof fn from_untyped_with_typed_value(
        tracked pt_untyped: PointsToUntyped,
        tracked typed_value: TypedValue<Self::A>,
        metadata: Metadata<Self::A>,
    ) -> (tracked out: Self)
        requires
            pt_untyped.wf(),
            pt_untyped.len() == Self::size(metadata),
            Self::satisfies_alignment(pt_untyped.ptr()@.addr),
            typed_value.is_valid() ==> {
                &&& abs_decode(pt_untyped.bytes(), typed_value.value_ref())
                &&& Self::metadata_matches(typed_value.value_ref(), metadata)
            },
        ensures
            out.ptr() == ptr_mut_from_data::<Self::A>(PtrData {
                addr: pt_untyped.ptr()@.addr,
                provenance: pt_untyped.ptr()@.provenance,
                metadata,
            }),
            out.bytes() == pt_untyped.bytes(),
            out.typed_value() == typed_value,
            out.wf(),
    ;

    /// Converts to an untyped permission for the same bytes,
    /// dropping the typed value, if any.
    proof fn into_untyped(tracked self) -> (tracked pt_untyped: PointsToUntyped)
        requires
            self.wf(),
        ensures
            pt_untyped.ptr() == ptr_mut_from_data::<[u8]>(PtrData {
                addr: self.ptr()@.addr,
                provenance: self.ptr()@.provenance,
                metadata: Self::size(self.ptr()@.metadata) as usize,
            }),
            pt_untyped.bytes() == self.bytes(),
            pt_untyped.wf(),
    {
        let tracked (pt_untyped, _) = self.into_untyped_with_typed_value();
        pt_untyped
    }

    /// Borrows the underlying untyped permission.
    proof fn as_untyped(tracked &self) -> (tracked pt_untyped: &PointsToUntyped)
        requires
            self.wf(),
        ensures
            pt_untyped.ptr() == ptr_mut_from_data::<[u8]>(PtrData {
                addr: self.ptr()@.addr,
                provenance: self.ptr()@.provenance,
                metadata: Self::size(self.ptr()@.metadata) as usize,
            }),
            pt_untyped.bytes() == self.bytes(),
            pt_untyped.wf(),
    ;

    /// Mutably borrows the underlying untyped permission.
    /// The typed value, if any, is dropped (call `take_typed_value` first to keep it).
    /// 
    /// `final(self)` is empty
    /// and has the final untyped permission's bytes, address, and provenance,
    /// but keeps its original pointer metadata (since this is a separate field).
    /// If the final untyped permission has the same pointers and length as the original,
    /// `self` is well-formed afterwards 
    /// (including that the metadata still defines the size of bytes).
    proof fn as_untyped_mut(tracked &mut self) -> (tracked pt_untyped: &mut PointsToUntyped)
        requires
            self.wf(),
        ensures
            pt_untyped.ptr() == ptr_mut_from_data::<[u8]>(PtrData {
                addr: old(self).ptr()@.addr,
                provenance: old(self).ptr()@.provenance,
                metadata: Self::size(old(self).ptr()@.metadata) as usize,
            }),
            pt_untyped.bytes() == old(self).bytes(),
            pt_untyped.wf(),
            final(self).ptr() == ptr_mut_from_data::<Self::A>(PtrData {
                addr: final(pt_untyped).ptr()@.addr,
                provenance: final(pt_untyped).ptr()@.provenance,
                metadata: old(self).ptr()@.metadata,
            }),
            final(self).bytes() == final(pt_untyped).bytes(),
            final(self).typed_value().is_empty(),
            PointsToUntyped::ptrs_len_same(*pt_untyped, *final(pt_untyped)) ==> final(self).wf(),
    ;

    /// Creates an empty permission to `pt_untyped`'s bytes, with the given pointer metadata.
    proof fn from_untyped(tracked pt_untyped: PointsToUntyped, metadata: Metadata<Self::A>) -> (tracked out: Self)
        requires
            pt_untyped.wf(),
            pt_untyped.len() == Self::size(metadata),
            Self::satisfies_alignment(pt_untyped.ptr()@.addr),
        ensures
            out.ptr() == ptr_mut_from_data::<Self::A>(PtrData {
                addr: pt_untyped.ptr()@.addr,
                provenance: pt_untyped.ptr()@.provenance,
                metadata,
            }),
            out.bytes() == pt_untyped.bytes(),
            out.typed_value().is_empty(),
            out.wf(),
    {
        Self::from_untyped_with_typed_value(pt_untyped, TypedValue::Empty, metadata)
    }
}

/// Restricts `PTValueOps` to permissions whose value type is `Sized`,
/// so its value can be moved in and out of the permission.
/// `PointsTo<T>` permissions are the element permissions of a typed `SeqPointsTo`.
pub trait PTSizedValue: PTValueOps<A: Sized> {
    /// The alignment requirement is preserved by offsets that are multiples of the size.
    proof fn lemma_satisfies_alignment_offset(addr: usize, i: nat)
        requires
            Self::satisfies_alignment(addr),
            addr + i * Self::size(()) <= usize::MAX,
        ensures
            Self::satisfies_alignment((addr + i * Self::size(())) as usize),
    ;

    /// The pointer metadata of a `Sized` value always matches `()`.
    proof fn lemma_metadata_matches(value: &Self::A)
        ensures
            Self::metadata_matches(value, ()),
    ;

    /// Moves the value out, leaving `self` empty.
    proof fn take(tracked &mut self) -> (tracked v: Self::A)
        requires
            self.wf(),
            self.typed_value().is_valid(),
        ensures
            v == old(self).typed_value().value(),
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).typed_value().is_empty(),
            final(self).wf(),
    {
        match self.take_typed_value() {
            TypedValue::Valid(b) => b.get(),
            TypedValue::Empty => proof_from_false(),
        }
    }

    /// Puts `v` in the permission. The bytes must decode to `v`.
    proof fn put(tracked &mut self, tracked v: Self::A)
        requires
            self.wf(),
            abs_decode(self.bytes(), &v),
        ensures
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).typed_value().is_valid(),
            final(self).typed_value().value() == v,
            final(self).wf(),
    {
        Self::lemma_metadata_matches(&v);
        self.put_typed_value(TypedValue::Valid(Tracked(v)));
    }

    /// Copies `*v` into the permission. The bytes must decode to `*v`.
    proof fn copy(tracked &mut self, tracked v: &Self::A) where Self::A: Copy
        requires
            self.wf(),
            abs_decode(self.bytes(), v),
        ensures
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).typed_value().is_valid(),
            final(self).typed_value().value() == *v,
            final(self).wf(),
    {
        self.put(*v);
    }

    /// Copies `*v` into the permission as its typed value.
    /// If `*v` is valid, the bytes must decode to its value.
    proof fn copy_typed_value(tracked &mut self, tracked v: &TypedValue<Self::A>) where Self::A: Copy
        requires
            self.wf(),
            v.is_valid() ==> abs_decode(self.bytes(), &v.value()),
        ensures
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).typed_value() == *v,
            final(self).wf(),
    {
        if v.is_valid() {
            Self::lemma_metadata_matches(&v.value());
        }
        self.put_typed_value(v.tracked_copy());
    }

    /// Creates a valid permission holding `value` from an untyped permission
    /// whose bytes decode to `value`.
    proof fn from_untyped_with_value(tracked pt_untyped: PointsToUntyped, tracked value: Self::A) -> (tracked out: Self)
        requires
            pt_untyped.wf(),
            pt_untyped.len() == Self::size(()),
            Self::satisfies_alignment(pt_untyped.ptr()@.addr),
            abs_decode(pt_untyped.bytes(), &value),
        ensures
            out.ptr() == ptr_mut_from_data::<Self::A>(PtrData {
                addr: pt_untyped.ptr()@.addr,
                provenance: pt_untyped.ptr()@.provenance,
                metadata: (),
            }),
            out.bytes() == pt_untyped.bytes(),
            out.typed_value().is_valid(),
            out.typed_value().value() == value,
            out.wf(),
    {
        Self::lemma_metadata_matches(&value);
        Self::from_untyped_with_typed_value(pt_untyped, TypedValue::Valid(Tracked(value)), ())
    }
}
```

## Impls

The `points_to_model.rs` impls are written out as the final code.
The `points_to_ops.rs` impls are written out without their proof bodies;
trait impl methods there don't restate their contracts, which are the trait's.
Axioms are named in a comment, not repeated;
their code is in [New axioms and axioms with bigger changes](#new-axioms-and-axioms-with-bigger-changes).

### `PointsToByte` (phase 1)

```rust
/// Permission to access a byte of memory.
#[verifier::external_body]
pub tracked struct PointsToByte {
    no_copy: NoCopy,
}

impl PTPhysSealed for PointsToByte {}

impl PTPhys for PointsToByte {
    type A = u8;

    /// This permission points to a single byte of memory.
    uninterp spec fn ptr(self) -> *mut u8;

    /// This permission tracks a single byte of memory.
    open spec fn size(metadata: ()) -> nat {
        1
    }

    /// A `PointsToByte` is always well-formed.
    open spec fn wf_basic(self) -> bool {
        true
    }

    /// If the pointer stays the same, `old` and `new` are permissions to the same memory.
    open spec fn ptrs_len_same(old: Self, new: Self) -> bool {
        new.ptr() == old.ptr()
    }

    /// Trivial, since a `PointsToByte` is always well-formed.
    proof fn stays_wf_basic(old: Self, new: Self) {
    }
}

impl PTProperties for PointsToByte {
    /// Guarantee that the `PointsToByte` points to a non-null address.
    ///
    /// See <https://doc.rust-lang.org/std/ptr/#safety>.
    axiom fn is_nonnull(tracked &self);

    /// The memory associated with a pointer should always be within bounds of its spatial provenance.
    axiom fn ptr_bounds(tracked &self);

    /// Since `u8` is not a ZST, the pointer's provenance is non-null.
    /// <https://doc.rust-lang.org/std/ptr/index.html#provenance>
    axiom fn provenance_not_none(tracked &self);

    /// Guarantees that the memory ranges associated with two distinct, non-ZST permissions will not overlap,
    /// since you cannot have two permissions to the same memory.
    /// (`self` is an &mut reference to enforce distinctness,
    /// so you cannot pass the same PointsTo as both arguments.)
    /// Since `u8` is not a ZST, this implies the pointers have distinct addresses.
    axiom fn is_disjoint<OtherPointsToPerm: PTPhys>(
        tracked &mut self,
        tracked other: &OtherPointsToPerm,
    );
}

impl PointsToByte {
    /// The byte that this permission tracks.
    pub uninterp spec fn byte(self) -> AbstractByte;

    /// Specializes `is_disjoint` to the case when the other permission is a `PointsToByte`.
    pub proof fn is_disjoint_byte(tracked &mut self, tracked other: &Self)
        requires
            self.wf_basic(),
            other.wf_basic(),
        ensures
            *old(self) == *final(self),
            final(self).ptr()@.addr + size_of::<u8>() <= other.ptr()@.addr
                || other.ptr()@.addr + size_of::<u8>() <= final(self).ptr()@.addr,
    {
        broadcast use group_vstd_default;

        self.is_disjoint(other);
    }
}

/// The interface for a `PointsToByte` permission,
/// which represents permission to access a single byte in memory.
/// We track the pointer to that memory as well as
/// the abstract byte corresponding to Rust's abstract machine.
#[cfg(verus_keep_ghost)]
pub ghost struct PointsToByteData {
    pub ptr: *mut u8,
    pub byte: AbstractByte,
}

#[cfg(verus_keep_ghost)]
impl View for PointsToByte {
    type V = PointsToByteData;

    open spec fn view(&self) -> Self::V {
        PointsToByteData { ptr: self.ptr(), byte: self.byte() }
    }
}
```

### `SeqPointsTo` and `PointsToUntyped`: specs (phase 1b)

```rust
/// Permission to access a contiguous sequence of values of type `T` in memory.
/// Internally represented as a sequence of permissions `P`,
/// along with a `*mut [T]` pointer to the whole region.
// We expect the associated type `A` from `PTProperties` to be the same as `T`,
// but `A = T` is bound on the impls
// so that recursive types like `struct Tree { children: Vec<Tree> }` are allowed.
#[verifier::accept_recursive_types(T)]
pub tracked struct SeqPointsTo<T, P: PTProperties> {
    seq_pt: Seq<P>,
    ptr: Ghost<*mut [T]>,
}

impl<T, P: PTProperties> PTPhysSealed for SeqPointsTo<T, P> {}

impl<T, P: PTProperties<A = T>> PTPhys for SeqPointsTo<T, P> {
    type A = [T];

    /// The pointer to the whole region; its metadata is the number of elements.
    closed spec fn ptr(self) -> *mut [T] {
        self.ptr@
    }

    /// The size of the pointed-to region is given by the length of the sequence (the pointer's metadata)
    /// times the size of the permission type in the sequence.
    ///
    /// Note that since this impl block restricts `P` to permissions satisfying `PTProperties`
    /// with the associated type set to `T` (which is implicitly `Sized`),
    /// `P` is a permission whose pointer has `()` metadata.
    open spec fn size(metadata: usize) -> nat {
        metadata as nat * P::size(())
    }

    open spec fn wf_basic(self) -> bool {
        // The pointer's metadata is the number of permissions
        &&& self.ptr()@.metadata == self.len()
        // Defining the provenance and address for the individual permissions
        &&& forall|i|
            #![trigger self[i].ptr()@.provenance]
            #![trigger self[i].ptr()@.addr]
            #![trigger self[i].wf_basic()]
            0 <= i < self.len() ==> {
                &&& self[i].ptr()@.provenance == self.ptr()@.provenance
                &&& self[i].ptr()@.addr == self.ptr()@.addr + i * P::size(())
                &&& self[i].wf_basic()
            }
        // The ptr is non-null
        &&& self.ptr()@.addr != 0
        // If ptr's provenance is Some, the address is in bounds of the provenance
        &&& self.ptr()@.provenance.is_some() ==> {
            &&& self.ptr()@.provenance.unwrap().start_addr() <= self.ptr()@.addr
            &&& self.ptr()@.addr <= self.ptr()@.provenance.unwrap().start_addr()
                + self.ptr()@.provenance.unwrap().alloc_len()
        }
    }

    /// `new` has the same pointer and length as `old`, and each element of `new` keeps the
    /// corresponding element of `old`'s pointer and satisfies its `ptrs_len_same`.
    open spec fn ptrs_len_same(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& new.len() == old.len()
        &&& forall|i: int|
            #![trigger new[i]]
            0 <= i < new.len() ==> P::ptrs_len_same(old[i], new[i]) && new[i].ptr() == old[i].ptr()
    }

    proof fn stays_wf_basic(old: Self, new: Self);
}

impl<T, P: PTProperties<A = T>> SeqPointsTo<T, P> {
    /// The sequence of permissions that the `SeqPointsTo` contains.
    pub closed spec fn seq_pt(self) -> Seq<P> {
        self.seq_pt
    }

    /// The length of the sequence of `P` permissions.
    #[verifier::inline]
    pub open spec fn len(self) -> nat {
        self.seq_pt().len()
    }

    /// `[]` operator, synonymous with `index`.
    #[verifier::inline]
    pub open spec fn spec_index(self, index: int) -> P
        recommends
            0 <= index < self.len(),
    {
        self.seq_pt()[index]
    }

    /// Borrows the sequence of permissions.
    pub proof fn tracked_seq_pt(tracked &self) -> tracked &Seq<P>
        returns
            self.seq_pt(),
    ;

    /// Mutably borrows the sequence of permissions, leaving the pointer unchanged.
    /// If the final permissions keep their original pointers and lengths,
    /// `self` satisfies `wf_basic` afterwards.
    pub proof fn tracked_seq_pt_mut(tracked &mut self) -> (tracked ret: &mut Seq<P>)
        ensures
            *ret == old(self).seq_pt(),
            final(self).seq_pt() == *final(ret),
            final(self).ptr() == old(self).ptr(),
            old(self).wf_basic() && Self::ptrs_len_same(*old(self), *final(self)) ==> final(self).wf_basic(),
    ;

    /// Consumes this `SeqPointsTo`, returning the underlying `Seq<P>`.
    pub proof fn into_seq(tracked self) -> (tracked perms: Seq<P>)
        returns
            self.seq_pt(),
    ;

    // Axiom: from_seq_mut (M5).
}

/// Permission to access an (untyped) contiguous sequence of bytes in memory.
/// Internally represented as a sequence of `PointsToByte` permissions,
/// along with a `*mut [u8]` pointer to the region of bytes.
pub type PointsToUntyped = SeqPointsTo<u8, PointsToByte>;

/// The interface for a `PointsToUntyped` permission,
/// which represents permission to access an (untyped) contiguous sequence of bytes in memory.
/// We track the pointer to that memory as well as
/// the abstract bytes corresponding to Rust's abstract machine.
#[cfg(verus_keep_ghost)]
pub ghost struct PointsToUntypedData {
    pub ptr: *mut [u8],
    pub bytes: Seq<AbstractByte>,
}

#[cfg(verus_keep_ghost)]
impl View for PointsToUntyped {
    type V = PointsToUntypedData;

    open spec fn view(&self) -> Self::V {
        PointsToUntypedData { ptr: self.ptr(), bytes: self.bytes() }
    }
}

impl PointsToUntyped {
    /// The contiguous sequence of bytes that this permission tracks.
    pub open spec fn bytes(self) -> Seq<AbstractByte> {
        self.seq_pt().map(|i: int, pt_byte: PointsToByte| pt_byte.byte())
    }

    /// The well-formed-ness properties which must hold of every `SeqPointsTo` (`wf_basic`),
    /// which include that the `*mut [u8]` pointer's metadata matches the number of `PointsToByte` permissions.
    pub open spec fn wf(self) -> bool {
        self.wf_basic()
    }

    // Axioms: join_ref, join_mut.
}
```

### `TypedValue` (phase 2)

`value_ref` and `valid_ref` are new; the rest exists today.

```rust
/// Represents (typed) contents of memory.
// Don't use std Option here in order to avoid circular dependency issues
// with verifying the standard library.
// (Also, using our own enum here lets us have more meaningful
// variant names like Empty/Valid.)
#[verifier::accept_recursive_types(T)]
pub tracked enum TypedValue<T: ?Sized> {
    /// Represents uninitialized memory.
    Empty,
    /// Represents initialized memory with the given value of type `T`.
    Valid(Tracked<T>),
}

impl<T: ?Sized> TypedValue<T> {
    /// Returns `true` if it is a [`TypedValue::Valid`] value.
    #[verifier::inline]
    pub open spec fn is_valid(&self) -> bool {
        self is Valid
    }

    /// Returns `true` if it is a [`TypedValue::Empty`] value.
    #[verifier::inline]
    pub open spec fn is_empty(&self) -> bool {
        self is Empty
    }

    /// If valid, a reference to the value; otherwise meaningless.
    pub open spec fn value_ref(&self) -> &T
        recommends
            self.is_valid(),
    {
        &*self->0
    }

    /// Borrows a value as a valid typed value.
    pub proof fn valid_ref<'a>(tracked v: &'a T) -> (tracked out: &'a Self)
        ensures
            out.is_valid(),
            out.value_ref() == v,
    {
        let tracked t = tracked_ref(v);
        shr_ref_struct_wrap(t, &TypedValue::Valid(*t), "Valid", "0")
    }
}

impl<T> TypedValue<T> {
    /// If it is a [`TypedValue::Valid`] value, returns the value.
    /// Otherwise, the return value is meaningless.
    #[verifier::inline]
    pub open spec fn value(&self) -> T
        recommends
            self is Valid,
    {
        *self->0
    }

    /// Copies a `TypedValue<T>` out of a shared reference, given that `T` is `Copy`.
    pub proof fn tracked_copy(tracked &self) -> (tracked out: TypedValue<T>) where T: Copy
        ensures
            out == *self,
    {
        match self {
            TypedValue::Valid(b) => TypedValue::Valid(Tracked(**b)),
            TypedValue::Empty => TypedValue::Empty,
        }
    }
}

impl<T> TypedValue<[T]> {
    /// If it is a [`TypedValue::Valid`] value, returns the value.
    /// Otherwise, the return value is meaningless.
    #[verifier::inline]
    pub open spec fn value(&self) -> &[T]
        recommends
            self is Valid,
    {
        &*self->0
    }

    // Axioms: from_elems_mut (M1), from_elems_ref.
}
```

### `PointsToUnaligned`: specs (phases 2, 2b; `str` in rustlib)

rustlib writes the `PTPhys`, `PTProperties` and `PTTypedValue` impls for `PointsToUnaligned<str>`
in the same shape as the `[T]` ones (`size(len) = len`; `metadata_matches` is `true`, since `str` decoding is `EncodingStr`'s).
`PTPhys` is sealed by the crate-private `PTPhysSealed`,
but vstd's `impl<T: ?Sized> PTPhysSealed for PointsToUnaligned<T>` already covers `str`,
and vstd is a module of rustlib's `core`, so rustlib can write these impls.

```rust
/// Permission to access memory which may decode to a valid value of type `T`;
/// this memory is not guaranteed to be aligned to `T`.
/// Internally represented as a possibly-valid value of type `T`,
/// along with a `PointsToUntyped` permission to the underlying bytes,
/// and the (ghost) metadata of the `*mut T` pointer.
pub tracked struct PointsToUnaligned<T: ?Sized> {
    val: TypedValue<T>,
    pt_untyped: PointsToUntyped,
    metadata: Ghost<Metadata<T>>,
}

/// The interface for a `PointsToUnaligned` or `PointsTo` permission,
/// which represents permission to access memory
/// whose bytes may decode to a valid value of type `T`.
/// We track the pointer to that memory,
/// the (possibly-valid) typed value, and its abstract bytes.
///
/// If `value` is `Valid(v)`, this signifies that `ptr` points to initialized memory,
/// and `v` is consistent with the bytes `ptr` points to.
/// We also have all the ghost state associated with type `T`.
///
/// If `value` is `Empty`, then we have no knowledge about what's in memory,
/// and we assume `ptr` points to uninitialized memory.
/// (To be pedantic, the bytes might be initialized in Rust's abstract machine,
///  but we don't know, so we have to pretend they're uninitialized.)
#[cfg(verus_keep_ghost)]
pub ghost struct PointsToData<T: ?Sized> {
    pub ptr: *mut T,
    pub value: TypedValue<T>,
    pub bytes: Seq<AbstractByte>,
}

#[cfg(verus_keep_ghost)]
impl<T: ?Sized> View for PointsToUnaligned<T> where PointsToUnaligned<T>: PTTypedValue<A = T> {
    type V = PointsToData<T>;

    open spec fn view(&self) -> Self::V {
        PointsToData {
            ptr: self.ptr(),
            value: <Self as PTTypedValue>::typed_value(*self),
            bytes: <Self as PTTypedValue>::bytes(*self),
        }
    }
}

impl<T: ?Sized> PointsToUnaligned<T> {
    /// The (possibly-valid) typed value that this permission tracks.
    pub closed spec fn typed_value(self) -> TypedValue<T> {
        self.val
    }

    /// The underlying `PointsToUntyped` permission to the pointed-to bytes.
    pub closed spec fn pt_untyped(self) -> PointsToUntyped {
        self.pt_untyped
    }

    /// The metadata of the `*mut T` pointer this permission is for.
    pub closed spec fn metadata(self) -> Metadata<T> {
        self.metadata@
    }

    /// The contiguous sequence of bytes that this permission tracks.
    #[verifier::inline]
    pub open spec fn bytes(self) -> Seq<AbstractByte> {
        self.pt_untyped().bytes()
    }

    /// Returns `true` if the permission's associated memory is valid for the type `T`.
    #[verifier::inline]
    pub open spec fn is_valid(&self) -> bool {
        self.typed_value().is_valid()
    }

    /// Returns `true` if the permission's associated memory is not valid for the type `T`.
    #[verifier::inline]
    pub open spec fn is_empty(&self) -> bool {
        self.typed_value().is_empty()
    }

    /// Returns a tracked reference to the underlying `PointsToUntyped` permission.
    ///
    /// This has no `wf()` requires/ensures,
    /// which gives flexibility for getting the underlying `PointsToUntyped`
    /// when the permission is not well-formed.
    /// However, the `wf()` conditions on `self` should imply that `pt_untyped` is `wf()`.
    // This is implemented by making `PTTypedValue::wf` on `self` include `wf_basic_unaligned`,
    // which includes `self.pt_untyped().wf()`.
    pub proof fn tracked_pt_untyped(tracked &self) -> tracked &PointsToUntyped
        returns
            self.pt_untyped(),
    {
        &self.pt_untyped
    }

    /// Returns a tracked reference to the typed value.
    pub proof fn tracked_typed_value(tracked &self) -> tracked &TypedValue<T>
        returns
            self.typed_value(),
    {
        &self.val
    }

    /// Splits the permission into an untyped permission to the same bytes and the typed value.
    /// It says nothing about `wf()`.
    pub proof fn into_raw_parts(tracked self) -> (tracked (pt_untyped, typed_value): (PointsToUntyped, TypedValue<T>))
        ensures
            pt_untyped == self.pt_untyped(),
            typed_value == self.typed_value(),
    {
        (self.pt_untyped, self.val)
    }

    /// Creates a permission from an untyped permission, a typed value and pointer metadata.
    /// The inverse of `into_raw_parts`.
    /// It says nothing about `wf()`: callers prove it from the parts.
    pub proof fn from_raw_parts(
        tracked pt_untyped: PointsToUntyped,
        tracked typed_value: TypedValue<T>,
        metadata: Metadata<T>,
    ) -> (tracked out: Self)
        ensures
            out.pt_untyped() == pt_untyped,
            out.typed_value() == typed_value,
            out.metadata() == metadata,
    {
        PointsToUnaligned { val: typed_value, pt_untyped, metadata: Ghost(metadata) }
    }

    /// Mutably borrows the untyped bytes and the typed value separately
    /// (the inverse of `from_raw_parts_mut`).
    /// The metadata is unchanged.
    pub proof fn as_raw_parts_mut(tracked &mut self)
        -> (tracked (pt_untyped, typed_value): (&mut PointsToUntyped, &mut TypedValue<T>))
        ensures
            *pt_untyped == old(self).pt_untyped(),
            *typed_value == old(self).typed_value(),
            final(self).pt_untyped() == *final(pt_untyped),
            final(self).typed_value() == *final(typed_value),
            final(self).metadata() == old(self).metadata(),
    {
        (&mut self.pt_untyped, &mut self.val)
    }

    // Axioms: from_raw_parts_ref, from_raw_parts_mut (M3).
}

impl<T: ?Sized> PointsToUnaligned<T> where PointsToUnaligned<T>: PTPhys<A = T> {
    /// A `PointsToUnaligned` is well-formed at the pointer level (`wf_basic`)
    /// if its memory region is `Self::size(self.ptr()@.metadata)` bytes,
    /// and the underlying `PointsToUntyped` is well-formed.
    /// Every `PTPhys` impl for `PointsToUnaligned` uses this as its `wf_basic`.
    pub open spec fn wf_basic_unaligned(self) -> bool {
        &&& self.pt_untyped().wf()
        &&& self.pt_untyped().len() == Self::size(self.ptr()@.metadata)
    }
}

impl<T> PointsToUnaligned<T> {
    /// If the permission's associated memory is valid,
    /// returns the value that the pointer points to.
    /// Otherwise, the result is meaningless.
    #[verifier::inline]
    pub open spec fn value(&self) -> T
        recommends
            self.is_valid(),
    {
        self.typed_value().value()
    }
}

impl<T: ?Sized> PTPhysSealed for PointsToUnaligned<T> {}

impl<T> PTPhys for PointsToUnaligned<T> {
    type A = T;

    /// Builds the `*mut T` from the underlying untyped pointer's address and provenance
    /// and the stored metadata.
    closed spec fn ptr(self) -> *mut T {
        ptr_mut_from_data::<T>(
            PtrData {
                addr: self.pt_untyped().ptr()@.addr,
                provenance: self.pt_untyped().ptr()@.provenance,
                metadata: self.metadata(),
            },
        )
    }

    /// The size of the pointed-to region is the size of `T`.
    open spec fn size(metadata: ()) -> nat {
        size_of::<T>()
    }

    /// A `PointsToUnaligned` is well-formed at the pointer level
    /// if its memory region is `size_of::<T>()` bytes,
    /// and the underlying `PointsToUntyped` is well-formed.
    open spec fn wf_basic(self) -> bool {
        self.wf_basic_unaligned()
    }

    /// `new` has the same pointer
    /// and the same underlying `PointsToUntyped` pointers and length as `old`.
    open spec fn ptrs_len_same(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& PointsToUntyped::ptrs_len_same(old.pt_untyped(), new.pt_untyped())
    }

    /// Delegates to `PointsToUntyped::stays_wf`.
    proof fn stays_wf_basic(old: Self, new: Self);
}

impl<T> PTPhys for PointsToUnaligned<[T]> {
    type A = [T];

    /// Builds the `*mut [T]` from the underlying untyped pointer's address and provenance
    /// and the stored metadata.
    closed spec fn ptr(self) -> *mut [T] {
        ptr_mut_from_data::<[T]>(
            PtrData {
                addr: self.pt_untyped().ptr()@.addr,
                provenance: self.pt_untyped().ptr()@.provenance,
                metadata: self.metadata(),
            },
        )
    }

    /// The size of the pointed-to region is the number of elements times the size of `T`.
    open spec fn size(metadata: usize) -> nat {
        metadata as nat * size_of::<T>()
    }

    /// A `PointsToUnaligned<[T]>` is well-formed at the pointer level
    /// if its memory region is `Self::size(self.ptr()@.metadata)` bytes,
    /// and the underlying `PointsToUntyped` is well-formed.
    open spec fn wf_basic(self) -> bool {
        self.wf_basic_unaligned()
    }

    /// `new` has the same pointer
    /// and the same underlying `PointsToUntyped` pointers and length as `old`.
    open spec fn ptrs_len_same(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& PointsToUntyped::ptrs_len_same(old.pt_untyped(), new.pt_untyped())
    }

    /// Delegates to `PointsToUntyped::stays_wf`.
    proof fn stays_wf_basic(old: Self, new: Self);
}

impl<T> PTTypedValue for PointsToUnaligned<T> {
    /// The inherent `typed_value` accessor.
    open spec fn typed_value(self) -> TypedValue<T> {
        PointsToUnaligned::<T>::typed_value(self)
    }

    /// The underlying untyped permission's bytes.
    open spec fn bytes(self) -> Seq<AbstractByte> {
        self.pt_untyped().bytes()
    }

    /// Always `true`: a `Sized` value has no pointer metadata.
    open spec fn metadata_matches(value: &T, metadata: ()) -> bool {
        true
    }

    /// Always `true`: a `PointsToUnaligned` has no alignment requirement.
    open spec fn satisfies_alignment(addr: usize) -> bool {
        true
    }

    proof fn bytes_decode(&self) {
    }

    proof fn satisfies_alignment_of_wf(&self) {
    }

    proof fn lemma_wf_basic(&self) {
    }

    // ptrs_len_same_valid: the trait's default body.

    /// From `PointsToUntyped::lemma_ptrs_len_same_untyped` on the underlying permissions.
    broadcast proof fn lemma_ptrs_len_same_valid(old: Self, new: Self);

    /// From `PointsToUntyped::stays_wf` on the underlying permissions.
    proof fn stays_wf(old: Self, new: Self);
}

impl<T> PTTypedValue for PointsToUnaligned<[T]> {
    /// The inherent `typed_value` accessor.
    open spec fn typed_value(self) -> TypedValue<[T]> {
        PointsToUnaligned::<[T]>::typed_value(self)
    }

    /// The underlying untyped permission's bytes.
    open spec fn bytes(self) -> Seq<AbstractByte> {
        self.pt_untyped().bytes()
    }

    /// The slice has `metadata` elements.
    open spec fn metadata_matches(value: &[T], metadata: usize) -> bool {
        value@.len() == metadata
    }

    /// Always `true`: a `PointsToUnaligned` has no alignment requirement.
    open spec fn satisfies_alignment(addr: usize) -> bool {
        true
    }

    proof fn bytes_decode(&self) {
    }

    proof fn satisfies_alignment_of_wf(&self) {
    }

    proof fn lemma_wf_basic(&self) {
    }

    // ptrs_len_same_valid: the trait's default body.

    /// From `PointsToUntyped::lemma_ptrs_len_same_untyped` on the underlying permissions.
    broadcast proof fn lemma_ptrs_len_same_valid(old: Self, new: Self);

    /// From `PointsToUntyped::stays_wf` on the underlying permissions.
    proof fn stays_wf(old: Self, new: Self);
}
```

### `PointsTo`: specs (generic; phase 2, widened in phase 2b)

The generic impls name the `PointsToUnaligned` trait functions (`<PointsToUnaligned<T> as PTTypedValue>::...`),
since the inherent accessors don't unfold to them for a generic `T`.
`wf` is overridden: the trait's default body doesn't unfold at `PointsToUnaligned<T>` for a generic `T`,
so with the default, `self.wf()` doesn't give `pt_unaligned.wf()`, which every delegation needs
([phase 0, item 17](TYPED_POINTS_TO_IMPL_PLAN.md#phase-0-pending-checks)).

````rust
/**
Permission to access possibly-initialized, _typed_ memory.

The associated pointer ([`points_to.ptr()`](PTPhys::ptr)) is always a valid pointer for constructing
a reference to the underlying data. That means it's always aligned to its type
([`is_aligned`](PointsTo::is_aligned)) and is non-null ([`is_nonnull`](PTProperties::is_nonnull)).

### Notes

The invariants on a `PointsTo` are a little more restrictive than is necessary for all
Rust operations you might want to do. For example:

1. With a null pointer to a ZST, Rust lets you read and write (though not take a reference).

```
#[derive(Copy, Clone)]
#[repr(align(64))]
struct X { }

fn zst_test() {
    let x_ptr: *mut X = std::ptr::null_mut();

    let x = unsafe { *x_ptr };  // allowed

    let x = X { };
    unsafe { *x_ptr = x; }      // allowed

    let j = unsafe { &*x_ptr }; // not allowed because ptr is null
}
```

2. The [`std::ptr::read_unaligned`] and [`std::ptr::write_unaligned`] don't require the pointer
   to be aligned.

Currently, the first use-case isn't supported because `PointsTo` enforces non-nullness.
For the second, use `PointsToUnaligned`, which doesn't enforce alignment.
*/
pub tracked struct PointsTo<T: ?Sized> {
    pt_unaligned: PointsToUnaligned<T>,
}

#[cfg(verus_keep_ghost)]
impl<T: ?Sized> View for PointsTo<T> where PointsToUnaligned<T>: PTValueOps<A = T> {
    type V = PointsToData<T>;

    open spec fn view(&self) -> Self::V {
        PointsToData {
            ptr: self.ptr(),
            value: <Self as PTTypedValue>::typed_value(*self),
            bytes: <Self as PTTypedValue>::bytes(*self),
        }
    }
}

impl<T: ?Sized> PointsTo<T> {
    /// The underlying `PointsToUnaligned` permission to the pointed-to memory.
    pub closed spec fn pt_unaligned(self) -> PointsToUnaligned<T> {
        self.pt_unaligned
    }

    /// The (possibly-valid) typed value that this permission tracks.
    pub open spec fn typed_value(self) -> TypedValue<T> {
        self.pt_unaligned().typed_value()
    }

    /// The metadata of the `*mut T` pointer this permission is for.
    pub open spec fn metadata(self) -> Metadata<T> {
        self.pt_unaligned().metadata()
    }

    /// The contiguous sequence of bytes that this permission tracks.
    #[verifier::inline]
    pub open spec fn bytes(self) -> Seq<AbstractByte> {
        self.pt_unaligned().bytes()
    }

    /// Returns `true` if the permission's associated memory is valid for the type `T`.
    #[verifier::inline]
    pub open spec fn is_valid(&self) -> bool {
        self.typed_value().is_valid()
    }

    /// Returns `true` if the permission's associated memory is not valid for the type `T`.
    #[verifier::inline]
    pub open spec fn is_empty(&self) -> bool {
        self.typed_value().is_empty()
    }

    /// Returns a tracked reference to the underlying `PointsToUnaligned` permission.
    ///
    /// This has no `wf()` requires/ensures,
    /// which gives flexibility for getting the underlying `PointsToUnaligned`
    /// when the permission is not well-formed.
    /// However, the `wf()` conditions on `self` should imply that `pt_unaligned` is `wf()`.
    // This is implemented by making `PTTypedValue::wf` on `self` include `self.pt_unaligned().wf()`.
    pub proof fn tracked_pt_unaligned(tracked &self) -> tracked &PointsToUnaligned<T>
        returns
            self.pt_unaligned(),
    {
        &self.pt_unaligned
    }

    // Axiom: from_unaligned_mut (M4).
}

impl<T> PointsTo<T> {
    /// If the permission's associated memory is valid,
    /// returns the value that the pointer points to.
    /// Otherwise, the result is meaningless.
    #[verifier::inline]
    pub open spec fn value(&self) -> T
        recommends
            self.is_valid(),
    {
        self.typed_value().value()
    }

    // Axiom: borrow_mut.
}

impl<T: ?Sized> PTPhysSealed for PointsTo<T> {}

impl<T: ?Sized> PTPhys for PointsTo<T> where PointsToUnaligned<T>: PTValueOps<A = T> {
    type A = T;

    /// Delegates to the underlying `PointsToUnaligned`'s pointer.
    open spec fn ptr(self) -> *mut T {
        self.pt_unaligned().ptr()
    }

    /// Delegates to the underlying `PointsToUnaligned`'s size.
    open spec fn size(metadata: Metadata<T>) -> nat {
        <PointsToUnaligned<T> as PTPhys>::size(metadata)
    }

    /// Delegates to the underlying `PointsToUnaligned`'s `wf_basic`.
    /// This does not capture all well-formedness conditions:
    /// pointer alignment is specified in `PTTypedValue::wf`.
    open spec fn wf_basic(self) -> bool {
        self.pt_unaligned().wf_basic()
    }

    /// `new` has the same pointer as `old`,
    /// and they satisfy the `PointsToUnaligned` requirements
    /// for preserving pointer-level well-formed-ness.
    open spec fn ptrs_len_same(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& <PointsToUnaligned<T> as PTPhys>::ptrs_len_same(old.pt_unaligned(), new.pt_unaligned())
    }

    /// Delegates to `PointsToUnaligned`'s `stays_wf_basic`.
    proof fn stays_wf_basic(old: Self, new: Self);
}

impl<T: ?Sized> PTTypedValue for PointsTo<T> where PointsToUnaligned<T>: PTValueOps<A = T> {
    /// Delegates to the underlying `PointsToUnaligned`'s typed value.
    open spec fn typed_value(self) -> TypedValue<T> {
        <PointsToUnaligned<T> as PTTypedValue>::typed_value(self.pt_unaligned())
    }

    /// Delegates to the underlying `PointsToUnaligned`'s bytes.
    open spec fn bytes(self) -> Seq<AbstractByte> {
        <PointsToUnaligned<T> as PTTypedValue>::bytes(self.pt_unaligned())
    }

    /// A `PointsTo` is well-formed if its pointer is aligned to `T`,
    /// and the underlying `PointsToUnaligned` is well-formed.
    open spec fn wf(self) -> bool {
        &&& self.pt_unaligned().wf()
        &&& Self::satisfies_alignment(self.ptr()@.addr)
    }

    /// Delegates to `PointsToUnaligned::metadata_matches`.
    open spec fn metadata_matches(value: &T, metadata: Metadata<T>) -> bool {
        <PointsToUnaligned<T> as PTTypedValue>::metadata_matches(value, metadata)
    }

    /// The pointer's address is aligned to `T`.
    /// Includes the (trivial) `PointsToUnaligned` requirement
    /// to satisfy generic preconditions defined over the trait `PTValueOps`.
    open spec fn satisfies_alignment(addr: usize) -> bool {
        &&& <PointsToUnaligned<T> as PTTypedValue>::satisfies_alignment(addr)
        &&& addr as nat % spec_align_of_val::<T>(arbitrary()) == 0
    }

    proof fn bytes_decode(&self) {
        self.pt_unaligned().bytes_decode();
    }

    proof fn satisfies_alignment_of_wf(&self) {
    }

    proof fn lemma_wf_basic(&self) {
        self.pt_unaligned().lemma_wf_basic();
    }

    /// `new` has the same pointer as `old`,
    /// and they satisfy the `PointsToUnaligned` requirements
    /// for preserving well-formed-ness.
    open spec fn ptrs_len_same_valid(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& <PointsToUnaligned<T> as PTTypedValue>::ptrs_len_same_valid(old.pt_unaligned(), new.pt_unaligned())
    }

    /// Delegates to the underlying `PointsToUnaligned`.
    broadcast proof fn lemma_ptrs_len_same_valid(old: Self, new: Self);

    /// Delegates to the underlying `PointsToUnaligned`.
    proof fn stays_wf(old: Self, new: Self);
}
````

### `points_to_ops.rs`: `SeqPointsTo`'s `PTProperties` and structural operations (phase 1b)

`points_to_ops.rs` is a child module of `points_to_model.rs`, so it can use the structs' private fields
([phase 0, item 15](TYPED_POINTS_TO_IMPL_PLAN.md#phase-0-pending-checks)).

```rust
impl<T, P: PTProperties<A = T>> PTProperties for SeqPointsTo<T, P> {
    /// Non-nullness is guaranteed by the invariant.
    proof fn is_nonnull(tracked &self);

    /// If the sequence is nonempty, this follows from the last element's `ptr_bounds`.
    /// Otherwise, `wf_basic`'s provenance clause guarantees it.
    proof fn ptr_bounds(tracked &self);

    /// If the size is non-zero, the length must be nonzero.
    /// Then this follows from the `provenance_not_none` property of an individual `P`.
    proof fn provenance_not_none(tracked &self);

    /// Finds the element whose range contains `other`'s start address
    /// (or the first or last element, if `other` starts outside `self`'s range),
    /// and uses that element's `is_disjoint`.
    proof fn is_disjoint<OtherPointsToPerm: PTPhys>(
        tracked &mut self,
        tracked other: &OtherPointsToPerm,
    );
}

impl<T, P: PTProperties<A = T>> SeqPointsTo<T, P> {
    /// Mutably borrows the permission at index `i`, leaving the pointer unchanged.
    pub proof fn index_mut(tracked &mut self, i: int) -> (tracked ret: &mut P)
        requires
            0 <= i < self.len(),
        ensures
            *ret == old(self)[i],
            final(self).seq_pt() == old(self).seq_pt().update(i, *final(ret)),
            final(self).ptr() == old(self).ptr(),
            old(self).wf_basic() && P::ptrs_len_same(*ret, *final(ret)) && final(ret).ptr() == ret.ptr() ==> final(self).wf_basic(),
    ;

    /// Creates a `SeqPointsTo` from a sequence of permissions at consecutive offsets from `ptr`.
    pub proof fn from_seq(tracked perms: Seq<P>, ptr: *mut T) -> (tracked out: Self)
        requires
            forall|i: int| 0 <= i < perms.len() ==> #[trigger] perms[i].wf_basic(),
            forall|i: int| 0 <= i < perms.len() ==> {
                &&& (#[trigger] perms[i]).ptr()@.provenance == ptr@.provenance
                &&& perms[i].ptr()@.addr == ptr@.addr + i * P::size(())
            },
            ptr@.addr != 0,
            ptr_addr_in_bounds(ptr),
            perms.len() <= usize::MAX,
        ensures
            out.seq_pt() == perms,
            out.ptr() as *mut T == ptr,
            out.wf_basic(),
    ;

    /// Creates an empty sequence at `ptr`.
    pub proof fn empty(ptr: *mut T) -> (tracked out: Self)
        requires
            ptr@.addr != 0,
            ptr_addr_in_bounds(ptr),
        ensures
            out.seq_pt() == Seq::<P>::empty(),
            out.ptr() as *mut T == ptr,
            out.wf_basic(),
    ;

    /// Splits into the first `mid` permissions and the rest.
    pub proof fn split_basic(tracked self, mid: nat) -> (tracked (first, second): (Self, Self))
        requires
            self.wf_basic(),
            mid <= self.len(),
        ensures
            first.seq_pt() == self.seq_pt().take(mid as int),
            second.seq_pt() == self.seq_pt().skip(mid as int),
            first.ptr() == ptr_mut_from_data::<[T]>(PtrData {
                addr: self.ptr()@.addr,
                provenance: self.ptr()@.provenance,
                metadata: mid as usize,
            }),
            second.ptr() == ptr_mut_from_data::<[T]>(PtrData {
                addr: (self.ptr()@.addr + mid * P::size(())) as usize,
                provenance: self.ptr()@.provenance,
                metadata: (self.len() - mid) as usize,
            }),
            first.wf_basic(),
            second.wf_basic(),
    ;

    /// Concatenates two sequences, provided that `other` starts where `self` ends
    /// and they have the same provenance.
    pub proof fn join_basic(tracked self, tracked other: Self) -> (tracked joined: Self)
        requires
            self.wf_basic(),
            other.wf_basic(),
            self.ptr()@.provenance == other.ptr()@.provenance,
            other.ptr()@.addr == self.ptr()@.addr + self.len() * P::size(()),
            P::size(()) == 0 ==> self.len() + other.len() <= usize::MAX,
        ensures
            joined.seq_pt() == self.seq_pt() + other.seq_pt(),
            joined.ptr() == ptr_mut_from_data::<[T]>(PtrData {
                addr: self.ptr()@.addr,
                provenance: self.ptr()@.provenance,
                metadata: (self.len() + other.len()) as usize,
            }),
            joined.wf_basic(),
    ;

    /// Borrows the sub-sequence of `len` permissions starting at `start`.
    pub proof fn subrange_basic(tracked &self, start: nat, len: nat) -> (tracked sub: &Self)
        requires
            self.wf_basic(),
            start + len <= self.len(),
        ensures
            sub.seq_pt() == self.seq_pt().subrange(start as int, (start + len) as int),
            sub.ptr() == ptr_mut_from_data::<[T]>(PtrData {
                addr: (self.ptr()@.addr + start * P::size(())) as usize,
                provenance: self.ptr()@.provenance,
                metadata: len as usize,
            }),
            sub.wf_basic(),
    ;
}
```

### `points_to_ops.rs`: `PointsToUntyped`'s proofs (phase 1b)

```rust
impl PointsToUntyped {
    /// If `old` is well-formed
    /// and `new` has the same pointers and length (`ptrs_len_same`),
    /// then `new` is well-formed.
    pub proof fn stays_wf(old: Self, new: Self)
        requires
            old.wf(),
            Self::ptrs_len_same(old, new),
        ensures
            new.wf(),
    ;

    /// If `old` and `new` are both well-formed with the same pointer,
    /// then `new` keeps `old`'s pointers and length.
    pub broadcast proof fn lemma_ptrs_len_same_untyped(old: Self, new: Self)
        requires
            old.wf(),
            new.wf(),
            new.ptr() == old.ptr(),
        ensures
            #[trigger] Self::ptrs_len_same(old, new),
    ;

    /// If `T` is zero sized,
    /// then we can construct a `PointsToUntyped` from any non-null `*mut T`
    /// whose address is within bounds of its provenance.
    /// The range of memory pointed to by this permission will be empty.
    pub proof fn zero_sized<T>(ptr: *mut T) -> (tracked perm: Self)
        requires
            ptr@.addr != 0,
            size_of::<T>() == 0,
            ptr_addr_in_bounds(ptr),
        ensures
            perm.ptr()@.addr == ptr@.addr,
            perm.ptr()@.provenance == ptr@.provenance,
            perm.bytes().len() == size_of::<T>(),
            perm.wf(),
    ;

    /// Specializes `is_disjoint` to the case when the other permission is a `PointsToUntyped`.
    pub proof fn is_disjoint_untyped(tracked &mut self, tracked other: &PointsToUntyped)
        requires
            self.len() != 0,
            other.len() != 0,
            self.wf(),
            other.wf(),
        ensures
            *old(self) == *final(self),
            final(self).ptr()@.addr + final(self).len() <= other.ptr()@.addr
                || other.ptr()@.addr + other.len() <= final(self).ptr()@.addr,
    ;

    /// Splits the `PointsToUntyped` into two permissions at the index boundary `mid`.
    /// The first covers bytes `[0, mid)` and the second covers bytes `[mid, len)`.
    pub proof fn split(tracked self, mid: nat) -> (tracked (first, second): (Self, Self))
        requires
            0 <= mid <= self.len(),
            self.wf(),
        ensures
            first.seq_pt() == self.seq_pt().take(mid as int),
            second.seq_pt() == self.seq_pt().skip(mid as int),
            first.bytes() == self.bytes().take(mid as int),
            second.bytes() == self.bytes().skip(mid as int),
            first.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: self.ptr()@.addr,
                    provenance: self.ptr()@.provenance,
                    metadata: mid as usize,
                },
            ),
            second.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: (self.ptr()@.addr + mid) as usize,
                    provenance: self.ptr()@.provenance,
                    metadata: (self.len() - mid) as usize,
                },
            ),
            first.wf(),
            second.wf(),
    ;

    /// Splits a shared borrow of a `PointsToUntyped`
    /// into shared borrows of bytes `[0, mid)` and `[mid, len)`.
    /// This is the shared-borrow analogue of `split`.
    pub proof fn split_ref(tracked &self, mid: nat) -> (tracked (first, second): (&Self, &Self))
        requires
            0 <= mid <= self.len(),
            self.wf(),
        ensures
            first.seq_pt() == self.seq_pt().take(mid as int),
            second.seq_pt() == self.seq_pt().skip(mid as int),
            first.bytes() == self.bytes().take(mid as int),
            second.bytes() == self.bytes().skip(mid as int),
            first.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: self.ptr()@.addr,
                    provenance: self.ptr()@.provenance,
                    metadata: mid as usize,
                },
            ),
            second.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: (self.ptr()@.addr + mid) as usize,
                    provenance: self.ptr()@.provenance,
                    metadata: (self.len() - mid) as usize,
                },
            ),
            first.wf(),
            second.wf(),
    ;

    /// Splits a mutable borrow of a `PointsToUntyped`
    /// into mutable borrows of bytes `[0, mid)` and `[mid, len)`.
    /// This is the mutable-borrow analogue of `split`.
    ///
    /// The final pointer stays the same, 
    /// and `self`'s final bytes and `seq_pt` are the concatenation 
    /// of `first` and `second`'s final bytes and `seq_pt`.
    /// If both halves keep their pointers and lengths (`ptrs_len_same`),
    /// then `final(self)` is also still well-formed.
    pub proof fn split_mut(tracked &mut self, mid: nat) -> (tracked (first, second): (
        &mut Self,
        &mut Self,
    ))
        requires
            0 <= mid <= self.len(),
            self.wf(),
        ensures
            first.seq_pt() == old(self).seq_pt().take(mid as int),
            second.seq_pt() == old(self).seq_pt().skip(mid as int),
            first.bytes() == old(self).bytes().take(mid as int),
            second.bytes() == old(self).bytes().skip(mid as int),
            first.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: old(self).ptr()@.addr,
                    provenance: old(self).ptr()@.provenance,
                    metadata: mid as usize,
                },
            ),
            second.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: (old(self).ptr()@.addr + mid) as usize,
                    provenance: old(self).ptr()@.provenance,
                    metadata: (old(self).len() - mid) as usize,
                },
            ),
            first.wf(),
            second.wf(),
            final(self).ptr() == old(self).ptr(),
            final(self).seq_pt() == final(first).seq_pt() + final(second).seq_pt(),
            final(self).bytes() == final(first).bytes() + final(second).bytes(),
            // Criteria necessary for re-establishing invariants
            Self::ptrs_len_same(*first, *final(first)) && Self::ptrs_len_same(*second, *final(second))
                ==> final(self).wf(),
    ;

    /// Concatenates `PointsToUntyped` permissions `self` and `other`,
    /// provided their pointers have the same provenance
    /// and `other`'s pointer starts at the end of `self`'s range.
    pub proof fn join(tracked self, tracked other: Self) -> (tracked joined: Self)
        requires
            self.wf(),
            other.wf(),
            self.ptr()@.provenance == other.ptr()@.provenance,
            other.ptr()@.addr == self.ptr()@.addr + self.len(),
        ensures
            joined.seq_pt() == self.seq_pt() + other.seq_pt(),
            joined.bytes() == self.bytes() + other.bytes(),
            joined.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: self.ptr()@.addr,
                    provenance: self.ptr()@.provenance,
                    metadata: (self.len() + other.len()) as usize,
                },
            ),
            joined.wf(),
    ;
}
```

### `points_to_ops.rs`: `PointsToUnaligned`'s proofs

`PTProperties` and `PTValueOps` are one impl per type (`T` and `[T]`; rustlib writes the `str` ones),
with the same bodies each time.
They aren't generic: the delegations need `wf_basic` and `ptr` to unfold,
and the per-type `PTPhys` bodies don't unfold in generic code.

```rust
impl<T> PTProperties for PointsToUnaligned<T> {
    /// Non-nullness follows from the underlying `PointsToUntyped`'s invariant,
    /// since `self.ptr()` and `self.pt_untyped().ptr()` have the same address.
    proof fn is_nonnull(tracked &self);

    /// Delegates to the underlying `PointsToUntyped`'s `ptr_bounds`,
    /// since `self.ptr()` and `self.pt_untyped().ptr()` have the same address.
    proof fn ptr_bounds(tracked &self);

    /// Delegates to the underlying `PointsToUntyped`'s `provenance_not_none`,
    /// since `self.ptr()` and `self.pt_untyped().ptr()` have the same address.
    proof fn provenance_not_none(tracked &self);

    /// Delegates to the underlying `PointsToUntyped`'s `is_disjoint`,
    /// since the two permissions track the same memory range.
    proof fn is_disjoint<OtherPointsToPerm: PTPhys>(
        tracked &mut self,
        tracked other: &OtherPointsToPerm,
    );
}

impl<T> PTProperties for PointsToUnaligned<[T]> {
    /// Non-nullness follows from the underlying `PointsToUntyped`'s invariant,
    /// since `self.ptr()` and `self.pt_untyped().ptr()` have the same address.
    proof fn is_nonnull(tracked &self);

    /// Delegates to the underlying `PointsToUntyped`'s `ptr_bounds`,
    /// since `self.ptr()` and `self.pt_untyped().ptr()` have the same address.
    proof fn ptr_bounds(tracked &self);

    /// Delegates to the underlying `PointsToUntyped`'s `provenance_not_none`,
    /// since `self.ptr()` and `self.pt_untyped().ptr()` have the same address.
    proof fn provenance_not_none(tracked &self);

    /// Delegates to the underlying `PointsToUntyped`'s `is_disjoint`,
    /// since the two permissions track the same memory range.
    proof fn is_disjoint<OtherPointsToPerm: PTPhys>(
        tracked &mut self,
        tracked other: &OtherPointsToPerm,
    );
}

impl<T> PTValueOps for PointsToUnaligned<T> {
    // zero_sized, borrow, into_untyped, from_untyped: the trait's default bodies.

    /// Borrows the `val` field.
    proof fn borrow_typed_value(tracked &self) -> tracked &TypedValue<T>;

    /// Swaps `Empty` into the `val` field.
    proof fn take_typed_value(tracked &mut self) -> (tracked v: TypedValue<T>);

    /// Replaces the `val` field.
    proof fn put_typed_value(tracked &mut self, tracked v: TypedValue<T>);

    /// Splits into well-formed `pt_untyped` and `val` fields.
    proof fn into_untyped_with_typed_value(tracked self) -> (tracked (pt_untyped, v): (PointsToUntyped, TypedValue<T>));

    /// Builds the struct from its well-formed fields.
    proof fn from_untyped_with_typed_value(
        tracked pt_untyped: PointsToUntyped,
        tracked typed_value: TypedValue<T>,
        metadata: (),
    ) -> (tracked out: Self);

    /// Borrows the `pt_untyped` field.
    proof fn as_untyped(tracked &self) -> (tracked pt_untyped: &PointsToUntyped);

    /// Mutably borrows the `pt_untyped` field, setting the `val` field to `Empty`.
    proof fn as_untyped_mut(tracked &mut self) -> (tracked pt_untyped: &mut PointsToUntyped);
}

impl<T> PTValueOps for PointsToUnaligned<[T]> {
    // zero_sized, borrow, into_untyped, from_untyped: the trait's default bodies.

    /// Borrows the `val` field.
    proof fn borrow_typed_value(tracked &self) -> tracked &TypedValue<[T]>;

    /// Swaps `Empty` into the `val` field.
    proof fn take_typed_value(tracked &mut self) -> (tracked v: TypedValue<[T]>);

    /// Replaces the `val` field.
    proof fn put_typed_value(tracked &mut self, tracked v: TypedValue<[T]>);

    /// Splits into well-formed `pt_untyped` and `val` fields.
    proof fn into_untyped_with_typed_value(tracked self) -> (tracked (pt_untyped, v): (PointsToUntyped, TypedValue<[T]>));

    /// Builds the struct from its well-formed fields.
    proof fn from_untyped_with_typed_value(
        tracked pt_untyped: PointsToUntyped,
        tracked typed_value: TypedValue<[T]>,
        metadata: usize,
    ) -> (tracked out: Self);

    /// Borrows the `pt_untyped` field.
    proof fn as_untyped(tracked &self) -> (tracked pt_untyped: &PointsToUntyped);

    /// Mutably borrows the `pt_untyped` field, setting the `val` field to `Empty`.
    proof fn as_untyped_mut(tracked &mut self) -> (tracked pt_untyped: &mut PointsToUntyped);
}

impl<T> PTSizedValue for PointsToUnaligned<T> {
    // take, put, copy, copy_typed_value, from_untyped_with_value: the trait's default bodies.

    /// Trivial, since a `PointsToUnaligned` has no alignment requirement.
    proof fn lemma_satisfies_alignment_offset(addr: usize, i: nat);

    /// Trivial, since `metadata_matches` is always `true` for a `Sized` value.
    proof fn lemma_metadata_matches(value: &T);
}

impl<T> PointsToUnaligned<T> {
    /// Specializes `is_disjoint` to the case when the other permission is a `PointsToUnaligned<S>`.
    pub proof fn is_disjoint_unaligned<S>(tracked &mut self, tracked other: &PointsToUnaligned<S>)
        requires
            size_of::<T>() != 0,
            size_of::<S>() != 0,
            self.wf(),
            other.wf(),
        ensures
            *old(self) == *final(self),
            final(self).ptr()@.addr + size_of::<T>() <= other.ptr()@.addr
                || other.ptr()@.addr + size_of::<S>() <= final(self).ptr()@.addr,
    ;
}
```

### `points_to_ops.rs`: `PointsTo`'s proofs and the aligned/unaligned conversions

```rust
impl<T: ?Sized> PTProperties for PointsTo<T> where PointsToUnaligned<T>: PTValueOps<A = T> {
    /// Non-nullness follows from the underlying `PointsToUnaligned`'s invariant,
    /// since `self.ptr()` is `self.pt_unaligned().ptr()`.
    proof fn is_nonnull(tracked &self);

    /// Delegates to the underlying `PointsToUnaligned`'s `ptr_bounds`,
    /// since `self.ptr()` is `self.pt_unaligned().ptr()`.
    proof fn ptr_bounds(tracked &self);

    /// Delegates to the underlying `PointsToUnaligned`'s `provenance_not_none`.
    proof fn provenance_not_none(tracked &self);

    /// Delegates to the underlying `PointsToUnaligned`'s `is_disjoint`,
    /// since the two permissions track the same memory range.
    proof fn is_disjoint<OtherPointsToPerm: PTPhys>(
        tracked &mut self,
        tracked other: &OtherPointsToPerm,
    );
}

impl<T: ?Sized> PTValueOps for PointsTo<T> where PointsToUnaligned<T>: PTValueOps<A = T> {
    // zero_sized, borrow, into_untyped, from_untyped: the trait's default bodies.

    /// Delegates to the underlying `PointsToUnaligned`.
    proof fn borrow_typed_value(tracked &self) -> tracked &TypedValue<T>;

    /// Delegates to the underlying `PointsToUnaligned`.
    proof fn take_typed_value(tracked &mut self) -> (tracked v: TypedValue<T>);

    /// Delegates to the underlying `PointsToUnaligned`.
    proof fn put_typed_value(tracked &mut self, tracked v: TypedValue<T>);

    /// Delegates to the underlying `PointsToUnaligned`.
    proof fn into_untyped_with_typed_value(tracked self) -> (tracked (pt_untyped, v): (PointsToUntyped, TypedValue<T>));

    /// Wraps the `PointsToUnaligned` built from the same parts.
    /// (`satisfies_alignment` includes `PointsToUnaligned`'s, which its `from_untyped_with_typed_value` requires.)
    proof fn from_untyped_with_typed_value(
        tracked pt_untyped: PointsToUntyped,
        tracked typed_value: TypedValue<T>,
        metadata: Metadata<T>,
    ) -> (tracked out: Self);

    /// Delegates to the underlying `PointsToUnaligned`.
    proof fn as_untyped(tracked &self) -> (tracked pt_untyped: &PointsToUntyped);

    /// Delegates to the underlying `PointsToUnaligned`.
    proof fn as_untyped_mut(tracked &mut self) -> (tracked pt_untyped: &mut PointsToUntyped);
}

impl<T> PTSizedValue for PointsTo<T> {
    // take, put, copy, copy_typed_value, from_untyped_with_value: the trait's default bodies.

    /// Offsetting a pointer by multiples of `size_of::<T>()` preserves its alignment to `T`,
    /// since `size_of::<T>()` is a multiple of `align_of::<T>()`.
    proof fn lemma_satisfies_alignment_offset(addr: usize, i: nat);

    /// Trivial, since `metadata_matches` is `PointsToUnaligned<T>`'s, which is always `true`.
    proof fn lemma_metadata_matches(value: &T);
}

impl<T> PointsTo<T> {
    /// A `PointsTo<T>` is always aligned.
    pub proof fn is_aligned(tracked &self)
        requires
            self.wf(),
        ensures
            self.ptr()@.addr as nat % align_of::<T>() == 0,
    ;

    /// Specializes `is_disjoint` to the case when the other permission is a `PointsTo<S>`.
    pub proof fn is_disjoint_pointsto<S>(tracked &mut self, tracked other: &PointsTo<S>)
        requires
            size_of::<T>() != 0,
            size_of::<S>() != 0,
            self.wf(),
            other.wf(),
        ensures
            *old(self) == *final(self),
            final(self).ptr()@.addr + size_of::<T>() <= other.ptr()@.addr
                || other.ptr()@.addr + size_of::<S>() <= final(self).ptr()@.addr,
    ;
}

impl<T: ?Sized> PointsToUnaligned<T> where PointsToUnaligned<T>: PTValueOps<A = T> {
    /// Converts to a `PointsTo<T>`, given that the address is aligned.
    pub proof fn into_aligned(tracked self) -> (tracked out: PointsTo<T>)
        requires
            self.wf(),
            <PointsTo<T> as PTTypedValue>::satisfies_alignment(self.ptr()@.addr),
        ensures
            out.pt_unaligned() == self,
            out.wf(),
    ;

    /// Borrows as a `PointsTo<T>`, given that the address is aligned.
    pub proof fn as_aligned(tracked &self) -> (tracked out: &PointsTo<T>)
        requires
            self.wf(),
            <PointsTo<T> as PTTypedValue>::satisfies_alignment(self.ptr()@.addr),
        ensures
            out.pt_unaligned() == *self,
            out.wf(),
    ;

    /// Mutably borrows as a `PointsTo<T>`, given that the address is aligned.
    /// `final(self)` is the final `PointsTo<T>`'s underlying `PointsToUnaligned<T>`.
    /// If the final `PointsTo<T>` satisfies `ptrs_len_same_valid` with the original,
    /// `self` is well-formed afterwards.
    pub proof fn as_aligned_mut(tracked &mut self) -> (tracked out: &mut PointsTo<T>)
        requires
            self.wf(),
            <PointsTo<T> as PTTypedValue>::satisfies_alignment(self.ptr()@.addr),
        ensures
            out.pt_unaligned() == *old(self),
            out.wf(),
            *final(self) == final(out).pt_unaligned(),
            <PointsTo<T> as PTTypedValue>::ptrs_len_same_valid(*out, *final(out)) ==> final(self).wf(),
    ;
}

impl<T: ?Sized> PointsTo<T> where PointsToUnaligned<T>: PTValueOps<A = T> {
    /// Converts to a `PointsToUnaligned<T>`.
    pub proof fn into_unaligned(tracked self) -> (tracked out: PointsToUnaligned<T>)
        requires
            self.wf(),
        ensures
            out == self.pt_unaligned(),
            out.wf(),
    ;

    /// Borrows as a `PointsToUnaligned<T>`.
    pub proof fn as_unaligned(tracked &self) -> (tracked out: &PointsToUnaligned<T>)
        requires
            self.wf(),
        ensures
            *out == self.pt_unaligned(),
            out.wf(),
    ;

    /// Mutably borrows the underlying `PointsToUnaligned<T>`.
    /// `final(self)` holds the final `PointsToUnaligned<T>`.
    /// If the final unaligned permission satisfies `ptrs_len_same_valid`
    /// with the initial unaligned permission (so it keeps the same aligned address),
    /// `self` is well-formed afterwards.
    pub proof fn as_unaligned_mut(tracked &mut self) -> (tracked out: &mut PointsToUnaligned<T>)
        requires
            self.wf(),
        ensures
            *out == old(self).pt_unaligned(),
            out.wf(),
            final(self).pt_unaligned() == *final(out),
            PointsToUnaligned::<T>::ptrs_len_same_valid(*out, *final(out)) ==> final(self).wf(),
    ;
}
```

### `points_to_ops.rs`: slice indexing and borrowed constructors (phase 4)

There are no slice → sequence conversions (`as_seq_pt`, `as_seq_pt_mut`);
`borrow_index` borrows one element of a slice permission instead.
The borrowed constructors are the borrowed counterparts of the owned `from_untyped` / `from_untyped_with_typed_value`.

```rust
impl<T> PointsToUnaligned<[T]> {
    /// The number of elements in the slice (the pointer's metadata).
    #[verifier::inline]
    pub open spec fn len(self) -> nat {
        self.ptr()@.metadata as nat
    }

    /// Borrows the permission to the element at index `i`.
    /// If the slice permission is empty, so is the element's.
    pub proof fn borrow_index(tracked &self, i: int) -> (tracked out: &PointsToUnaligned<T>)
        requires
            self.wf(),
            0 <= i < self.len(),
        ensures
            out.ptr() == ptr_mut_from_data::<T>(PtrData {
                addr: (self.ptr()@.addr + i * size_of::<T>()) as usize,
                provenance: self.ptr()@.provenance,
                metadata: (),
            }),
            out.bytes() == self.bytes().subrange(i * size_of::<T>(), (i + 1) * size_of::<T>()),
            self.typed_value().is_valid() ==> {
                &&& out.typed_value().is_valid()
                &&& out.typed_value().value() == self.typed_value().value_ref()@[i]
            },
            self.typed_value().is_empty() ==> out.typed_value().is_empty(),
            out.wf(),
    ;

    /// Borrows a `&PointsToUntyped` as a `&PointsToUnaligned<[T]>`
    /// with an empty typed value of length `len`,
    /// provided that the length matches the bytes.
    pub proof fn from_untyped_ref<'a>(tracked pt_untyped: &'a PointsToUntyped, len: usize) -> (tracked out: &'a Self)
        requires
            pt_untyped.wf(),
            pt_untyped.len() == len * size_of::<T>(),
        ensures
            out.ptr()@ == (PtrData { addr: pt_untyped.ptr()@.addr, provenance: pt_untyped.ptr()@.provenance, metadata: len }),
            out.bytes() == pt_untyped.bytes(),
            out.typed_value().is_empty(),
            out.wf(),
    ;

    /// Borrows a `&PointsToUntyped` and `tracked &[T]` as a `&PointsToUnaligned<[T]>`
    /// with a valid typed value set to `value`,
    /// provided that the bytes decode to the value.
    pub proof fn from_untyped_with_value_ref<'a>(tracked pt_untyped: &'a PointsToUntyped, tracked value: &'a [T])
        -> (tracked out: &'a Self)
        requires
            pt_untyped.wf(),
            abs_decode::<[T]>(pt_untyped.bytes(), value),
        ensures
            out.ptr()@ == (PtrData { addr: pt_untyped.ptr()@.addr, provenance: pt_untyped.ptr()@.provenance, metadata: value@.len() as usize }),
            out.bytes() == pt_untyped.bytes(),
            out.typed_value().is_valid(),
            out.typed_value().value_ref() == value,
            out.wf(),
    ;
}

impl<T> PointsTo<[T]> {
    /// The number of elements in the slice (the pointer's metadata).
    #[verifier::inline]
    pub open spec fn len(self) -> nat {
        self.ptr()@.metadata as nat
    }

    /// Borrows the permission to the element at index `i`.
    /// If the slice permission is empty, so is the element's.
    pub proof fn borrow_index(tracked &self, i: int) -> (tracked out: &PointsTo<T>)
        requires
            self.wf(),
            0 <= i < self.len(),
        ensures
            out.ptr() == ptr_mut_from_data::<T>(PtrData {
                addr: (self.ptr()@.addr + i * size_of::<T>()) as usize,
                provenance: self.ptr()@.provenance,
                metadata: (),
            }),
            out.bytes() == self.bytes().subrange(i * size_of::<T>(), (i + 1) * size_of::<T>()),
            self.typed_value().is_valid() ==> {
                &&& out.typed_value().is_valid()
                &&& out.typed_value().value() == self.typed_value().value_ref()@[i]
            },
            self.typed_value().is_empty() ==> out.typed_value().is_empty(),
            out.wf(),
    ;

    /// Borrows a `&PointsToUntyped` as a `&PointsTo<[T]>`
    /// with an empty typed value of length `len`,
    /// provided that the length matches the bytes and the `PointsToUntyped`'s pointer is aligned.
    pub proof fn from_untyped_ref<'a>(tracked pt_untyped: &'a PointsToUntyped, len: usize) -> (tracked out: &'a Self)
        requires
            pt_untyped.wf(),
            pt_untyped.len() == len * size_of::<T>(),
            Self::satisfies_alignment(pt_untyped.ptr()@.addr),
        ensures
            out.ptr()@ == (PtrData { addr: pt_untyped.ptr()@.addr, provenance: pt_untyped.ptr()@.provenance, metadata: len }),
            out.bytes() == pt_untyped.bytes(),
            out.typed_value().is_empty(),
            out.wf(),
    ;

    /// Borrows a `&PointsToUntyped` and `tracked &[T]` as a `&PointsTo<[T]>`
    /// with a valid typed value set to `value`,
    /// provided that the bytes decode to the value and the `PointsToUntyped`'s pointer is aligned.
    pub proof fn from_untyped_with_value_ref<'a>(tracked pt_untyped: &'a PointsToUntyped, tracked value: &'a [T])
        -> (tracked out: &'a Self)
        requires
            pt_untyped.wf(),
            abs_decode::<[T]>(pt_untyped.bytes(), value),
            Self::satisfies_alignment(pt_untyped.ptr()@.addr),
        ensures
            out.ptr()@ == (PtrData { addr: pt_untyped.ptr()@.addr, provenance: pt_untyped.ptr()@.provenance, metadata: value@.len() as usize }),
            out.bytes() == pt_untyped.bytes(),
            out.typed_value().is_valid(),
            out.typed_value().value_ref() == value,
            out.wf(),
    ;
}
```
