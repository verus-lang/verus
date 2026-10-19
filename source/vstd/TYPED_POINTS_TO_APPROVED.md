# Approved: `PointsToSingleValue` trait and typed `SeqPointsTo` (level 3)

Designs and specifications that have been reviewed and approved.
Any change here, including to documentation, needs to be flagged for re-approval.
What is still under review is in [TYPED_POINTS_TO_PLAN.md](TYPED_POINTS_TO_PLAN.md).

## Permission types after all phases

| Type | `A` | Pointer metadata | `size(metadata)` | Traits | Holds |
|---|---|---|---|---|---|
| `PointsToByte` (renamed from `PointsToSingleton`) | `u8` | `()` | `1` | `PointsToPhys`, `PointsToProperties` | one abstract byte (axiomatized, as today) |
| `PointsToUntyped` = `SeqPointsTo<u8, PointsToByte>` | `[u8]` | length | `len` | `PointsToPhys`, `PointsToProperties` | a sequence of byte permissions |
| `PointsToUnaligned<T>` | `T` | `()` | `size_of::<T>()` | the above + `PointsToSingleValueSpec` + `PointsToSingleValue` + `PointsToSingleValueSized` | untyped bytes, a `TypedValue<T>`, and the ghost metadata |
| `PointsToUnaligned<[T]>` | `[T]` | length | `len * size_of::<T>()` | the above, without `PointsToSingleValueSized` | the same, with a `TypedValue<[T]>` |
| `PointsToUnaligned<str>` (rustlib) | `str` | byte length | `len` | as for `[T]` | the same, with a `TypedValue<str>` |
| `PointsTo<X>` (for each `X` above) | `X` | as above | as above | as for `PointsToUnaligned<X>` | a `PointsToUnaligned<X>` at an aligned address |
| `SeqPointsTo<T, P>`, `P: PointsToProperties<A = T>` | `[T]` | length | `len * P::size(())` | `PointsToPhys`, `PointsToProperties` | one element permission `P` per element |
| `PointsToRaw` | — | — | — | none (no single pointer) | a map from addresses to `PointsToByte`s, one provenance |

## Trait impls

`T` is `Sized` (in `[T]`, it is the element type).
"Generic" means one `impl<T: ?Sized> ... for PointsTo<T> where PointsToUnaligned<T>: PointsToSingleValue<A = T>`.

| Type | `PointsToPhys`, `PointsToProperties`, `View` | `PointsToSingleValueSpec`, `PointsToSingleValue` | `PointsToSingleValueSized` | Where | When |
|---|---|---|---|---|---|
| `PointsToUnaligned<T>` | `PointsToPhys`: per type; `PointsToProperties`: generic (phase 2) | yes | yes | vstd | phase 2 |
| `PointsToUnaligned<[T]>` | `PointsToPhys`: per type (done); `PointsToProperties`: generic (phase 2) | yes | no | vstd | phase 2b |
| `PointsToUnaligned<str>` | `PointsToPhys`: per type; `PointsToProperties`: generic | yes | no | rustlib | after phase 3b ([specs](TYPED_POINTS_TO_PLAN.md#str-rustlib)) |
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

## API changes not visible in the specs

Renames: `PointsToSingleton` → `PointsToByte`, `borrow_value` → `borrow`,
`into_untyped_with_typed_value` → `into_raw_parts` (single permissions only),
`borrow_value_subrange` → `borrow_subrange`,
`PointsToProperties::ptrs_len_same_valid` → `ptrs_len_same`.
Removed: `FixedSize`, `Dealloc`, and the inherent `PointsTo<T>` versions of the trait methods
(the five traits are re-exported instead; the prelude is unchanged).
Split: `PointsToSingleValue`'s spec items and the lemmas that unfold `wf` move into a new supertrait,
`PointsToSingleValueSpec` (see [Trait definitions](#trait-definitions)).
`group_points_to_permissions_lemmas` is split into `group_points_to_lemmas` and `group_points_to_collections_lemmas`
(see [Module layout](#module-layout)).

## Module layout

`points_to.rs` and `points_to_permissions.rs` become three files.
`points_to_model.rs` and `points_to_ops.rs` are trusted (reviewed);
`points_to_collections.rs` is verified, and nothing else depends on it:
removing it leaves a complete single-value and untyped API.

| `points_to_model.rs` (trusted) | `points_to_ops.rs` (trusted) | `points_to_collections.rs` (verified) |
|---|---|---|
| the five trait definitions, with their default bodies | the `PointsToProperties` impls of `SeqPointsTo`, `PointsToUnaligned` and `PointsTo` | `PointsToRaw` (all of it) |
| the struct definitions: `PointsToByte`, `TypedValue`, `SeqPointsTo`, `PointsToUntyped`, `PointsToUnaligned`, `PointsTo`; their closed accessors and the inherent spec fns (`typed_value`, `bytes`, `metadata`, `is_valid`, `value`, `value_ref`, `len`, `thin_ptr`, …); their `View` impls | the `PointsToSingleValue` impls (per type for `PointsToUnaligned`, generic for `PointsTo`) and the `PointsToSingleValueSized` impls | the typed `SeqPointsTo` impl (`impl<T> SeqPointsTo<T, PointsTo<T>>`), including its `wf`, and its `View` |
| well-formedness: every `PointsToPhys` impl (`ptr`, `size`, `wf_basic`), every `PointsToSingleValueSpec` impl (`typed_value`, `bytes`, `metadata_matches`, `satisfies_alignment`, and the lemmas `bytes_decode`, `satisfies_alignment_of_wf`, `lemma_wf_basic`), `wf_basic_unaligned`, `PointsToUntyped::wf` and `bytes` | the structural `SeqPointsTo` impl (except M5) and `PointsToUntyped`'s proofs | |
| the axioms: `PointsToByte`'s `PointsToProperties` impl, `PointsToUntyped::join_ref` / `join_mut`, `from_raw_parts_ref`, M1, M3–M5 | the aligned/unaligned conversions | the sequence → slice conversions (`as_slice_pt`, `as_slice_pt_mut`) |
| the tracked getters and byte disjointness: `TypedValue::tracked_copy`, `valid_ref`; `PointsToByte::is_disjoint_byte` | the slice permissions' borrowed constructors (`from_untyped_ref`, `from_untyped_with_value_ref`) and `borrow_index`; `is_aligned`, `is_disjoint_pointsto`, `is_disjoint_unaligned`; `group_points_to_lemmas` | `group_points_to_collections_lemmas` |

- **Field access.** Private fields are visible only in the defining module and its descendants.
  So `points_to_ops` is a child module of `points_to_model`, and can touch the fields.
  `points_to_collections` is not a descendant of `points_to_model`, so the compiler guarantees it never does.
  Field privacy isn't what makes the axioms sound
  (Verus derives nothing from privacy, and checks `PointsToRaw`'s type invariant everywhere);
  it keeps the field-touching code in the trusted files.
- **Spec and proof traits.** A trait impl can't be split across files,
  so `PointsToSingleValue`'s spec items are in their own trait, `PointsToSingleValueSpec`.
  Its impls (the spec items and the lemmas that unfold `wf`) and the `PointsToPhys` impls
  are in `points_to_model.rs`, so all of `wf`'s meaning is there;
  the `PointsToSingleValue` impls are in `points_to_ops.rs`.
  The exception is `ptrs_len_same`, a spec fn in the `PointsToProperties` impls (in `points_to_ops.rs`).
- **Dependencies.** `points_to_model` and `points_to_ops` use `raw_ptr_model`,
  `layout` and `type_representation`, never `points_to_collections` or `raw_ptr_specs`.
  `points_to_collections` uses both trusted files.
  `raw_ptr_specs` and `shared_reference.rs` use the two trusted files, never `points_to_collections`.
  `points_to_model` calls into `points_to_ops` in one place:
  the default body of `PointsToSingleValue::zero_sized` calls `PointsToUntyped::zero_sized`.
- **`allocate` / `deallocate`** go in `raw_ptr_specs.rs`.
  They take and return a `PointsToUntyped` for the whole allocation,
  so nothing trusted mentions `PointsToRaw`.
  `PointsToRaw::from_untyped` / `into_untyped` convert.
- **Typed sequence `wf`.** It is a well-formedness condition,
  but nothing trusted uses it, so it stays with the typed impl in `points_to_collections.rs`.
- **Lemma groups.** `group_points_to_permissions_lemmas` is split in two, one per file,
  so `points_to_collections` can be removed without losing anything the other files provide:
  `group_points_to_lemmas` (`points_to_ops.rs`) contains `PointsToSingleValue::lemma_ptrs_len_same_valid`
  (in place of `PointsTo::lemma_ptrs_len_same_valid`)
  and `PointsToUntyped`'s lemma (renamed `lemma_ptrs_len_same_untyped`);
  `group_points_to_collections_lemmas` (`points_to_collections.rs`) contains
  the typed `SeqPointsTo::lemma_ptrs_len_same_valid`.
  Both are in vstd's default group.

`raw_ptr_new.rs` becomes two files:

| `raw_ptr_model.rs` | `raw_ptr_specs.rs` |
|---|---|
| the module docs and model notes, `AllocId`, `ProvenanceData`, `provenance_properties`, `ptr_addr_in_bounds`, `Metadata`, `PtrData`, the `View` impls for `*mut T` / `*const T` | the pointer `==` `assume_specification`s |
| the inverse functions: `ptr_mut_from_data`, `tracked_ptr_mut_from_data`, `ptr_from_data`, `axiom_ptr_mut_from_data`, `view_reverse_for_eq`, `ptrs_mut_eq`, `ptrs_mut_eq_sized` | null pointers, casts, `ptr_ref` / `ptr_mut_ref` (and the slice versions), `addr` / `with_addr`, the reference specs, `mut_ref_to_shr_points_to` (and the slice version), `cast_mut_ref_*`, `allocate` / `deallocate` |
| `group_raw_ptr_axioms` (all four members are here) | |

The cast functions' `rustc_diagnostic_item`s are string names, so moving them doesn't affect `as`-casts.

## Existing, unchanged trusted specs

Trusted items the permissions rely on that exist today and don't change.
"Uses" names the main dependents.
Existing axioms with minor contract changes on this branch are in
[Minor changes to existing trusted specs](#minor-changes-to-existing-trusted-specs).

| Item | File | What it states | Uses |
|---|---|---|---|
| `PointsToByte` (`external_body` struct; `uninterp` `ptr`, `byte`) | `points_to_model.rs` | A permission to one byte, with its address and abstract byte. | everything byte-level |
| `PointsToByte`'s `is_nonnull`, `ptr_bounds`, `provenance_not_none`, `is_disjoint` | `points_to_model.rs` | A byte permission's pointer is non-null, within its allocation, has non-null provenance; two byte permissions are at different addresses. | `PointsToUntyped`'s and `PointsToRaw`'s pointer-level lemmas || `ProvenanceData` (`external_body`; `uninterp` `start_addr`, `alloc_len`, `alignment`, `orig_size`, `alloc_id`), `provenance_properties` | `raw_ptr_model.rs` | The allocation model. `orig_size` replaces `Dealloc`'s size tracking. | pointer bounds, `allocate` / `deallocate` |
| pointer model: `View for *mut T` (`uninterp`), `ptr_mut_from_data` (`uninterp`), `axiom_ptr_mut_from_data`, `ptrs_mut_eq`, `tracked_ptr_mut_from_data` | `raw_ptr_model.rs` | A pointer is its `PtrData` (address, provenance, metadata). | every pointer spec (e.g. the generic `PointsToUnaligned` pointer built from its metadata) |
| `assume_specification`s for pointer `==`, `null`, `null_mut`, `addr`, `with_addr`; the `cast_*` `external_body` functions | `raw_ptr_specs.rs` | The exec pointer operations match the model. | exec code |
| `SharedReference` (`external_body`; `uninterp` `value`, `ptr`), `ptr_nonnull`, `axiom_shared_ref_value_view` | `shared_reference.rs` | A shared reference with its pointer. | exec code; the source of valid shared permissions |
| `shared_ref_ptr` (`uninterp`), `mut_ref_slice_len`, `ptr_mut_ref_join`, `tracked_mut_ref_slice_subrange`, `tracked_mut_ref_slice_idx`, `cast_mut_ref_to_ptr`, `cast_mut_ref_slice_to_ptr`, `cast_mut_ref_str_to_ptr` | `raw_ptr_specs.rs` | Reference ↔ pointer and permission boundary. | exec code; the source of valid permissions |
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
| `ptr_ref` (`external_body`) | `raw_ptr_specs.rs` | Now requires `perm.wf()`. | exec reads |
| `mut_ref_to_shr_points_to` | `raw_ptr_specs.rs` | Now ensures `pt.wf()`. | the source of valid permissions from `&mut T` |
| `SharedReference::points_to` | `shared_reference.rs` | Now ensures `pt.wf()`. | the source of valid shared permissions |
| `ptr_ref2` (`external_body`), `ptr_ref2_ghost` | `shared_reference.rs` | Now require `perm.wf()`. | exec code; `SharedReference` from a permission |
| `ptr_ref_slice` (`external_body`; restored, phase 4b) | `raw_ptr_specs.rs` | Restored from commented-out code; now requires `perm.wf()`. | exec slice reads |
| `mut_ref_to_shr_points_to_slice` (restored, phase 4b) | `raw_ptr_specs.rs` | Restored from commented-out code; now ensures `pt.wf()`. | the source of valid slice permissions from `&mut [T]` |
| `SharedReference<[T]>::points_to` (restored, phase 4b) | `shared_reference.rs` | Restored from commented-out code; now ensures `pt.wf()`. | the source of valid shared slice permissions |
| `ptr_ref2_slice_ghost` (restored, phase 4b) | `shared_reference.rs` | Restored from commented-out code; now requires `perm.wf()`. | `SharedReference<[T]>` from a slice permission |
| `ptr_ref_str` (`external_body`; rustlib) | rustlib | Moved from vstd's commented-out code; now requires `perm.wf()`. | exec `str` reads |
| `mut_ref_to_shr_points_to_str` (rustlib) | rustlib | Moved from vstd's commented-out code; now ensures `pt.wf()`. | the source of valid `str` permissions from `&mut str` |
| `SharedReference<str>::points_to` (rustlib) | rustlib | Moved from vstd's commented-out code; now ensures `pt.wf()`. | the source of valid shared `str` permissions |
| `ptr_ref2_str_ghost` (rustlib) | rustlib | Moved from vstd's commented-out code; now requires `perm.wf()`. | `SharedReference<str>` from a `str` permission |

The restored slice and `str` versions also state the value through `typed_value().value_ref()`
(with `@` for slices) in place of the old `value()`, which the planned `PointsTo<[T]>` / `PointsTo<str>` don't have.

```rust
// raw_ptr_specs.rs

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

// raw_ptr_specs.rs, restored slice versions (phase 4b; from raw_ptr_new.rs lines 524 and 683)

/// Equivalent to `&*ptr`, passing in a permission `perm` to ensure safety.
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

// shared_reference.rs

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

// shared_reference.rs, restored slice versions (phase 4b; from lines 126 and 221)

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

```rust
// rustlib: the str versions, moved from vstd's commented-out code.

impl<'a> SharedReference<'a, str> {
    pub axiom fn points_to(tracked self) -> (tracked pt: &'a PointsTo<str>)
        ensures
            pt.ptr() == self.ptr(),
            pt.is_valid(),
            pt.typed_value().value_ref() == self.value(),
            pt.wf(),
    ;
}

pub axiom fn ptr_ref2_str_ghost<'a>(ptr: *const str, tracked perm: &PointsTo<str>) -> (tracked v: SharedReference<'a, str>)
    requires
        perm.ptr() == ptr,
        perm.is_valid(),
        perm.wf(),
    ensures
        v.value() == perm.typed_value().value_ref(),
        v.ptr() == ptr,
;

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

Specs approved so far; the full list of new trusted items is in
[TYPED_POINTS_TO_PLAN.md](TYPED_POINTS_TO_PLAN.md#new-axioms).

| Item | File | What it states | Uses |
|---|---|---|---|
| `ptr_mut_ref` (`external_body`; existing, strengthened, already in the code) | `raw_ptr_specs.rs` | Now also ensures `final(perm).wf()`: the final bytes decode to the final value (and requires `old(perm).wf()`). | exec writes through `&mut T` |
| `ptr_mut_ref_slice` (`external_body`; restored, phase 4b) | `raw_ptr_specs.rs` | Restored from commented-out code, strengthened the same way as `ptr_mut_ref`. | exec writes through `&mut [T]` |
| `ptr_mut_ref_str` (`external_body`; rustlib) | rustlib | Moved from vstd's commented-out code, strengthened the same way as `ptr_mut_ref`. | exec writes through `&mut str` |
| `Seq::tracked_borrow_subrange` (`external_body`; already in the code) | `seq.rs` | Borrows a subrange of a borrowed tracked `Seq`. | `subrange_basic`, `split_ref` |
| `Seq::tracked_split_borrow_mut` (`external_body`; already in the code) | `seq.rs` | Splits a mutable borrow of a tracked `Seq` in two. | `subrange_mut`, the `&mut` conversions |
| `tracked_slice_index` (phase 3b) | `slice.rs` | Borrows an element of a borrowed slice. | `borrow_index` |
| `tracked_slice_from_refs` (phase 3b) | `slice.rs` | Borrowed elements act as one borrowed slice. | shared sequence → slice |
| `tracked_ref` (phase 3b) | `modes.rs` | A borrow is a borrowed `Tracked` of itself. | `TypedValue::valid_ref` |
| `PointsToUnaligned::from_raw_parts_ref` (phase 3b) | `points_to_model.rs` | Borrowed bytes and typed value act as one borrowed permission. | borrowed constructors, `borrow_index`, sequence → slice, `str` ↔ `[u8]` |
| M1 `TypedValue::<[T]>::from_elems_mut` (phase 3b) | `points_to_model.rs` | Per-element `&mut` typed values act as one `&mut` slice typed value. | `&mut` sequence → slice |
| M3 `PointsToUnaligned::from_raw_parts_mut` (phase 3b) | `points_to_model.rs` | `&mut` bytes and typed value act as one `&mut` permission. | `&mut` conversions |
| M4 `PointsTo::from_unaligned_mut` (phase 3b) | `points_to_model.rs` | A `&mut PointsToUnaligned` acts as a `&mut PointsTo`. | `as_aligned_mut`, aligned `&mut` conversions |
| M5 `SeqPointsTo::from_seq_mut` (phase 3b) | `points_to_model.rs` | A `&mut Seq<P>` acts as a `&mut SeqPointsTo`. | `subrange_mut`, `split_mut` |
| `PointsToUntyped::join_ref` (already in the code) | `points_to_model.rs` | Two borrowed untyped permissions, the second starting where the first ends, act as one borrowed permission. | the typed sequences' `as_untyped`, shared sequence → slice |
| `PointsToUntyped::join_mut` (already in the code) | `points_to_model.rs` | The same for mutable borrows; the parts' final values are tied back if the joined permission keeps its pointers and length. | the typed sequences' `as_untyped_mut`, `&mut` sequence → slice |
| `abs_decode_slice` (already in the code) | `type_representation.rs` | A slice decodes exactly when each element's slot does. Its definition is in the code and isn't repeated here. | slice `wf` |
| `abs_decode_str` (rustlib) | rustlib (`type_representation`) | A `str` decodes exactly when its bytes are valid UTF-8 and each decodes as a `u8`. | `str` `wf`, `str` ↔ `[u8]` |
**`ptr_mut_ref`** (`raw_ptr_specs.rs`; existing, strengthened, already in the code).
It now requires and ensures `wf()`.
It doesn't say the bytes stay the same,
so `final(perm).wf()` is what tells callers the final bytes decode to the final value.

```rust
/// Equivalent to `&mut *X`, passing in a permission `perm` to ensure safety.
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

// Restored slice version (phase 4b; from raw_ptr_new.rs line 559).
// The value is stated as typed_value().value_ref()@ in place of the old value() (a Seq<T>).
/// Equivalent to `&mut *ptr`, passing in a permission `perm` to ensure safety.
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

// rustlib: the str version, moved from vstd's commented-out code.
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

**`Seq` tracked operations** (`seq.rs`; new relative to `verify-rustlib`, already in the code).

```rust
// seq.rs, impl<A> Seq<A>
#[verifier(external_body)]
pub proof fn tracked_borrow_subrange(tracked &self, i: int, j: int) -> (tracked ret: &Self)
    requires
        0 <= i <= j <= self.len(),
    ensures
        *ret == self.subrange(i, j),
{
    unimplemented!()
}

/// Split a mutable borrow of a sequence into two at index `mid`.
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

```rust
// slice.rs: no permissions involved
pub axiom fn tracked_slice_index<'a, T>(tracked s: &'a [T], i: int) -> (tracked e: &'a T)
    requires
        0 <= i < s@.len(),
    ensures
        *e == s@[i],
;

pub axiom fn tracked_slice_from_refs<'a, T>(tracked refs: Seq<&'a T>) -> (tracked s: &'a [T])
    ensures
        s@ == refs.map_values(|r: &T| *r),
;
```

```rust
// modes.rs, next to tracked_swap
pub axiom fn tracked_ref<'a, T: ?Sized>(tracked t: &'a T) -> (tracked out: &'a Tracked<T>)
    ensures
        &**out == t,
;
```

**Borrowed permission assembly** (new, phase 3b).
It says nothing about `wf()`: callers prove it from the parts.

```rust
// points_to_model.rs, with PointsToUnaligned.
// The borrowed version of the struct literal; no wf.
impl<T: ?Sized> PointsToUnaligned<T> {
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

**Mutable borrowed assembly (M1, M3–M5)** (new, phase 3b; there is no M2 or M6).
Each follows `PointsToUntyped::join_mut`'s pattern:
the borrowed parts' final values are tied to the result's final value,
conditionally where the structure could change.

```rust
// points_to_model.rs, with TypedValue.
impl<T> TypedValue<[T]> {
    /// M1: per-element typed values -> one slice typed value.
    /// If any element is empty, the slice starts empty.
    pub axiom fn from_elems_mut<'a>(tracked elems: Seq<&'a mut TypedValue<T>>)
        -> (tracked out: &'a mut TypedValue<[T]>)
        ensures
            // Initially: valid with the elements' values if every element is valid
            // (a zero-length Seq counts as valid); otherwise empty.
            (forall|i: int| 0 <= i < elems.len() ==> (#[trigger] *elems[i]).is_valid()) ==> {
                &&& out.is_valid()
                &&& out.value()@ == Seq::new(elems.len(), |i: int| (*elems[i]).value())
            },
            !(forall|i: int| 0 <= i < elems.len() ==> (#[trigger] *elems[i]).is_valid()) ==> out.is_empty(),
            // Finally: a valid slice of the same length is distributed back to the elements;
            // anything else leaves every element empty.
            final(out).is_valid() && final(out).value()@.len() == elems.len() ==> forall|i: int|
                0 <= i < elems.len() ==> {
                    &&& (#[trigger] *final(elems[i])).is_valid()
                    &&& (*final(elems[i])).value() == final(out).value()@[i]
                },
            !(final(out).is_valid() && final(out).value()@.len() == elems.len()) ==> forall|i: int|
                0 <= i < elems.len() ==> (#[trigger] *final(elems[i])).is_empty(),
    ;
}
```

```rust
// points_to_model.rs, with PointsToUnaligned.
impl<T: ?Sized> PointsToUnaligned<T> {
    /// M3: the `&mut` version of `from_raw_parts_ref`.
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

```rust
// points_to_model.rs, with PointsTo.
impl<T: ?Sized> PointsTo<T> {
    /// M4: a mutably borrowed `PointsToUnaligned<T>` acts as a mutably borrowed `PointsTo<T>`
    /// (the `&mut` counterpart of the `shr_ref_struct_wrap` in `as_aligned`).
    pub axiom fn from_unaligned_mut<'a>(tracked u: &'a mut PointsToUnaligned<T>)
        -> (tracked out: &'a mut Self)
        ensures
            out.pt_unaligned() == *old(u),
            *final(u) == final(out).pt_unaligned(),
    ;
}
```

```rust
// points_to_model.rs, with SeqPointsTo.
impl<T, P: PointsToProperties<A = T>> SeqPointsTo<T, P> {
    /// M5: a mutably borrowed `Seq<P>` acts as a mutably borrowed sequence with the given (ghost) pointer.
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
                &&& Self::ptrs_len_same(*old(self), *final(self))
                &&& Self::ptrs_len_same(*old(other), *final(other))
                &&& final(self).wf()
                &&& final(other).wf()
                &&& final(joined).seq_pt() == final(self).seq_pt() + final(other).seq_pt()
                &&& final(joined).bytes() == final(self).bytes() + final(other).bytes()
            },
    ;
}
```

**`str` decoding** (new, rustlib).
In rustlib a `str`'s view `s@` is its bytes (`Seq<u8>`).

```rust
// type_representation (rustlib): the str counterpart of abs_decode_slice
/// The bytes decode to a `str` exactly when its bytes are valid UTF-8
/// and each abstract byte decodes to the corresponding `u8`.
/// The byte condition is `EncodingU8Slice::decode`'s, with `s@` for the slice's view,
/// so `abs_decode::<str>(b, s) <==> valid_utf8(s@) && abs_decode::<[u8]>(b, v)` for any `v` with `v@ == s@`
/// (by the existing `[u8]` axiom).
pub broadcast axiom fn abs_decode_str(bytes: Seq<AbstractByte>, s: &str)
    ensures
        #[trigger] abs_decode::<str>(bytes, s) <==> {
            &&& valid_utf8(s@)
            &&& s@.len() == bytes.len()
            &&& forall|i| 0 <= i < s@.len() ==> u8::decode(seq![bytes[i]], #[trigger] s@[i])
        },
;
```

Not trusted: the shared `&TypedValue<str>` ↔ `&TypedValue<[u8]>` casts
(from rustlib's existing `str::as_bytes_tracked` / `str::from_bytes_tracked` axioms and `valid_ref`).
There are no owned or `&mut` `str` ↔ `[u8]` casts.
rustlib's existing `str` permission axioms (`as_str_ptr_verus`, `perm_init`, `perm_value_eq`, `perm_ptr`)
are temporary stand-ins until `PointsTo<str>` is ported;
they're replaced by the above and not part of this design.

## Slice indexing

Borrows one element of a slice permission (phase 4; in `points_to_ops.rs`).
There are no slice → sequence conversions.
Needs no new axioms:
the bytes come from `split_ref` on the untyped permission,
a valid element's typed value from `tracked_slice_index` and `TypedValue::valid_ref`
(an empty one from `tracked_static_mut_ref`, as in the other borrowed conversions),
and the permission from `from_raw_parts_ref`.

```rust
impl<T> PointsToUnaligned<[T]> {
    /// Borrows the permission to the element at index `i`.
    /// If the slice permission is empty, so is the element's.
    pub proof fn borrow_index(tracked &self, i: int) -> (tracked out: &PointsToUnaligned<T>)
        requires
            self.wf(),
            0 <= i < self.ptr()@.metadata,
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
}
// impl<T> PointsTo<[T]>: borrow_index(&self, i) -> &PointsTo<T>, the same contract;
//   composed from as_unaligned, PointsToUnaligned::<[T]>::borrow_index and as_aligned
//   (each element's address is aligned because the slice's is,
//   and size_of::<T>() is a multiple of align_of::<T>()).
```

## Trait definitions

```rust
// A private seal trait to prevent `PointsToPhys` from being implemented outside of vstd.
pub(crate) trait PointsToPhysSealed {}

/// Defines the physical memory region that a `PointsTo` permission covers,
/// by specifying the pointer to memory and the size of the pointed-to region.
#[allow(private_bounds)]
pub trait PointsToPhys: Sized + PointsToPhysSealed {
    type A: ?Sized;

    /// The pointer that this permission is associated with.
    spec fn ptr(self) -> *mut Self::A;

    /// The size, in bytes, of the memory region tracked by a permission
    /// whose pointer has the given metadata.
    /// A permission `p` tracks `Self::size(p.ptr()@.metadata)` bytes.
    spec fn size(metadata: Metadata<Self::A>) -> nat;

    /// Define basic well-formedness conditions on the permission's pointer,
    /// including that the permission holds `Self::size(self.ptr()@.metadata)` bytes.
    /// `PointsToSingleValue::wf` builds on this to add conditions on the bytes and typed value.
    spec fn wf_basic(self) -> bool;
}

/// Defines properties which should hold of any `PointsTo` permission.
pub trait PointsToProperties: PointsToPhys {
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
    proof fn is_disjoint<OtherPointsToPerm: PointsToPhys>(
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

    /// Specifies that `new` keeps `old`'s pointers and length,
    /// which is what `wf_basic` needs to carry over from `old`.
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

/// Defines the typed data tracked by a `PointsTo` permission
/// to a single, possibly-valid value of type `Self::A`,
/// along with well-formedness conditions.
pub trait PointsToSingleValueSpec: PointsToPhys {
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
}

/// Defines constructors and conversions
/// for a `PointsTo` permission to a single, possibly-valid value of type `Self::A`.
pub trait PointsToSingleValue: PointsToSingleValueSpec + PointsToProperties {
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
    proof fn into_raw_parts(tracked self) -> (tracked (pt_untyped, v): (PointsToUntyped, TypedValue<Self::A>))
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
        let tracked (pt_untyped, _) = self.into_raw_parts();
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
        Self::from_raw_parts(pt_untyped, TypedValue::Empty, metadata)
    }

    /// Creates a permission from an untyped permission, a typed value and pointer metadata.
    /// The inverse of `into_raw_parts`.
    /// If `typed_value` is valid, the bytes must decode to its value and the metadata must match it.
    proof fn from_raw_parts(
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
}

/// Restricts `PointsToSingleValue` to permissions whose value type is `Sized`,
/// so its value can be moved in and out of the permission.
/// `PointsTo<T>` permissions are the element permissions of a typed `SeqPointsTo`.
pub trait PointsToSingleValueSized: PointsToSingleValue<A: Sized> {
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
        Self::from_raw_parts(pt_untyped, TypedValue::Valid(Tracked(value)), ())
    }
}
```
