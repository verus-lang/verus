# Approved: `PointsToSingleValue` trait and a generic typed `SeqPointsTo` (level 3)

Designs and specifications that have been reviewed and approved.
Any change here, including to documentation, needs to be flagged for re-approval.
What is still under review is in [TYPED_POINTS_TO_PLAN.md](TYPED_POINTS_TO_PLAN.md).

## Permission types after all phases

| Type | `A` | Pointer metadata | `size(metadata)` | Traits | Holds |
|---|---|---|---|---|---|
| `PointsToByte` (renamed from `PointsToSingleton`) | `u8` | `()` | `1` | `PointsToPhys`, `PointsToProperties` | one abstract byte (axiomatized, as today) |
| `PointsToUntyped` = `SeqPointsTo<u8, PointsToByte>` | `[u8]` | length | `len` | `PointsToPhys`, `PointsToProperties` | a sequence of byte permissions |
| `PointsToUnaligned<T>` | `T` | `()` | `size_of::<T>()` | the above + `PointsToSingleValue` + `PointsToSingleValueSized` | untyped bytes, a `TypedValue<T>`, and the ghost metadata |
| `PointsToUnaligned<[T]>` | `[T]` | length | `len * size_of::<T>()` | the above, without `PointsToSingleValueSized` | the same, with a `TypedValue<[T]>` |
| `PointsToUnaligned<str>` (rustlib) | `str` | byte length | `len` | as for `[T]` | the same, with a `TypedValue<str>` |
| `PointsTo<X>` (for each `X` above) | `X` | as above | as above | as for `PointsToUnaligned<X>` | a `PointsToUnaligned<X>` at an aligned address |
| `SeqPointsTo<T, P>`, `P: PointsToProperties<A = T>` | `[T]` | length | `len * P::size(())` | `PointsToPhys`, `PointsToProperties` | one element permission `P` per element |
| `PointsToRaw` | — | — | — | none (no single pointer) | a map from addresses to `PointsToByte`s, one provenance |

## Trait impls

`T` is `Sized` (in `[T]`, it is the element type).
"Generic" means one `impl<T: ?Sized> ... for PointsTo<T> where PointsToUnaligned<T>: PointsToSingleValue<A = T>`.

| Type | `PointsToPhys`, `PointsToProperties`, `View` | `PointsToSingleValue` | `PointsToSingleValueSized` | Where | When |
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

## API changes not visible in the specs

Renames: `PointsToSingleton` → `PointsToByte`, `borrow_value` → `borrow`,
`into_untyped_with_typed_value` → `into_raw_parts` (single permissions only),
`borrow_value_subrange` → `borrow_subrange`,
`PointsToProperties::ptrs_len_same_valid` → `ptrs_len_same`.
Removed: `FixedSize`, `Dealloc`, and the inherent `PointsTo<T>` versions of the trait methods
(`points_to_permissions.rs` re-exports the four traits instead; the prelude is unchanged).

## Existing, unchanged trusted specs

Trusted items the permissions rely on that exist today and don't change.
"Uses" names the main dependents.
Existing axioms with minor contract changes on this branch are in
[Minor changes to existing trusted specs](#minor-changes-to-existing-trusted-specs).

| Item | File | What it states | Uses |
|---|---|---|---|
| `PointsToByte` (`external_body` struct; `uninterp` `ptr`, `byte`) | `points_to.rs` | A permission to one byte, with its address and abstract byte. | everything byte-level |
| `PointsToByte`'s `is_nonnull`, `ptr_bounds`, `provenance_not_none`, `is_disjoint` | `points_to.rs` | A byte permission's pointer is non-null, within its allocation, has non-null provenance; two byte permissions are at different addresses. | `PointsToUntyped`'s and `PointsToRaw`'s pointer-level lemmas |
| `ProvenanceData` (`external_body`; `uninterp` `start_addr`, `alloc_len`, `alignment`, `orig_size`, `alloc_id`), `provenance_properties` | `raw_ptr_new.rs` | The allocation model. `orig_size` replaces `Dealloc`'s size tracking. | pointer bounds, `allocate` / `deallocate` |
| pointer model: `View for *mut T` (`uninterp`), `ptr_mut_from_data` (`uninterp`), `axiom_ptr_mut_from_data`, `ptrs_mut_eq`, `tracked_ptr_mut_from_data` | `raw_ptr_new.rs` | A pointer is its `PtrData` (address, provenance, metadata). | every pointer spec (e.g. the generic `PointsToUnaligned` pointer built from its metadata) |
| `assume_specification`s for pointer `==`, `null`, `null_mut`, `addr`, `with_addr`; the `cast_*` `external_body` functions | `raw_ptr_new.rs` | The exec pointer operations match the model. | exec code |
| `SharedReference` (`external_body`; `uninterp` `value`, `ptr`), `ptr_nonnull`, `axiom_shared_ref_value_view` | `shared_reference.rs` | A shared reference with its pointer. | exec code; the source of valid shared permissions |
| `shared_ref_ptr` (`uninterp`), `mut_ref_slice_len`, `ptr_mut_ref_join`, `tracked_mut_ref_slice_subrange`, `tracked_mut_ref_slice_idx`, `cast_mut_ref_to_ptr`, `cast_mut_ref_slice_to_ptr`, `cast_mut_ref_str_to_ptr` | `raw_ptr_new.rs` | Reference ↔ pointer and permission boundary. | exec code; the source of valid permissions |
| `abs_encode`, `abs_decode`, `abs_can_be_encoded` (`uninterp`); `encode_decode_len`, `encode_decode_inverse`, `shared_ref_cannot_be_encoded`; the per-type encoding impls | `type_representation.rs` | The abstract-byte encoding of values. | every decode clause |
| layout axioms (`layout_of_sized`, `layout_of_slices`, `layout_of_str`, `layout_of_unit_tuple`, `align_properties`, …) | `layout.rs` | Sizes and alignments of types and values. | sizes, `satisfies_alignment`, `lemma_satisfies_alignment_offset`, the `zero_sized` default |
| `tracked_swap`, `tracked_static_mut_ref` | `modes.rs` | Swapping tracked values; a `'static` borrow of an owned value. | `take_typed_value`, empty cases of borrowed conversions |
| `Seq` tracked operations (`tracked_borrow`, `tracked_borrow_mut`, `tracked_borrow_subrange_mut`, …) | `seq.rs` | Borrowing parts of a tracked `Seq`. | `as_untyped_mut`, `index_mut` |
| `Map` tracked operations (`tracked_empty`, `tracked_remove_keys`, `tracked_union_prefer_right`, …) | `map.rs` | Building and splitting a tracked `Map`. | `PointsToRaw` |
| `shr_ref_struct_wrap` | builtin | Borrowing a struct from a borrow of its only tracked field. | `as_aligned`, `subrange_basic`, `split_ref`, `from_refs` |

## Minor changes to existing trusted specs

Already in the code on this branch.
`ptr_mut_ref`'s change (it now also ensures `final(perm).wf()`) is a bigger change;
it's in [New axioms and axioms with bigger changes](#new-axioms-and-axioms-with-bigger-changes).

| Item | File | Change | Uses |
|---|---|---|---|
| `ptr_ref` (`external_body`) | `raw_ptr_new.rs` | Now requires `perm.wf()`. | exec reads |
| `mut_ref_to_shr_points_to` | `raw_ptr_new.rs` | Now ensures `pt.wf()`. | the source of valid permissions from `&mut T` |
| `SharedReference::points_to` | `shared_reference.rs` | Now ensures `pt.wf()`. | the source of valid shared permissions |
| `ptr_ref2` (`external_body`), `ptr_ref2_ghost` | `shared_reference.rs` | Now require `perm.wf()`. | exec code; `SharedReference` from a permission |

```rust
// raw_ptr_new.rs

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
```

## New axioms and axioms with bigger changes

Specs approved so far; the full list of new trusted items is in
[TYPED_POINTS_TO_PLAN.md](TYPED_POINTS_TO_PLAN.md#new-axioms).

| Item | File | What it states | Uses |
|---|---|---|---|
| `ptr_mut_ref` (`external_body`; existing, strengthened, already in the code) | `raw_ptr_new.rs` | Now also ensures `final(perm).wf()`: the final bytes decode to the final value (and requires `old(perm).wf()`). | exec writes through `&mut T` |
| `Seq::tracked_borrow_subrange` (`external_body`; already in the code) | `seq.rs` | Borrows a subrange of a borrowed tracked `Seq`. | `subrange_basic`, `split_ref` |
| `Seq::tracked_split_borrow_mut` (`external_body`; already in the code) | `seq.rs` | Splits a mutable borrow of a tracked `Seq` in two. | `subrange_mut`, the `&mut` conversions |
| `tracked_slice_index` (phase 3b) | `slice.rs` | Borrows an element of a borrowed slice. | shared slice → sequence |
| `tracked_slice_from_refs` (phase 3b) | `slice.rs` | Borrowed elements act as one borrowed slice. | shared sequence → slice |
| `tracked_ref` (phase 3b) | `modes.rs` | A borrow is a borrowed `Tracked` of itself. | `TypedValue::valid_ref` |

**`ptr_mut_ref`** (`raw_ptr_new.rs`; existing, strengthened, already in the code).
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
/// along with well-formedness properties, constructors, and conversions.
pub trait PointsToSingleValue: PointsToProperties {
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

    /// Invariants which must hold between `old` and `new` to preserve well-formedness (see `stays_wf`).
    open spec fn ptrs_len_same_valid(old: Self, new: Self) -> bool {
        &&& Self::ptrs_len_same(old, new)
        &&& new.typed_value().is_valid() ==> {
            &&& abs_decode(new.bytes(), new.typed_value().value_ref())
            &&& Self::metadata_matches(new.typed_value().value_ref(), new.ptr()@.metadata)
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
/// These are the element permissions of a typed `SeqPointsTo`.
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
