# Design: `PointsToSingleValue` trait and a generic typed `SeqPointsTo` (level 3)

The specifications and trusted code to review:
a `PointsToSingleValue` trait implemented by `PointsTo` and `PointsToUnaligned` (for `T`, `[T]`, and `str` in rustlib),
one generic typed `SeqPointsTo` impl,
the slice ↔ sequence conversions,
and every new trusted item in vstd and rustlib.

The rationale, background and decisions are in [TYPED_POINTS_TO_NOTES.md](TYPED_POINTS_TO_NOTES.md);
the phases, spike results and risks in [TYPED_POINTS_TO_IMPL_PLAN.md](TYPED_POINTS_TO_IMPL_PLAN.md)
("phase N" below points there).

## Overview

**Permission types after all phases.**

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

**Written once vs per type.**

Single-value permissions:

| Code | Written | What it contains |
|---|---|---|
| `PointsToPhys for PointsToUnaligned<_>` | per type | `ptr` (same shape each time) and the `size` formula |
| `PointsToProperties for PointsToUnaligned<T: ?Sized>` | once (generic) | `wf_basic`, `ptrs_len_same`, and the pointer-level lemmas, all delegating to the untyped bytes |
| `PointsToSingleValue for PointsToUnaligned<_>` | per type | `typed_value`, `bytes`, `metadata_matches`, `satisfies_alignment` (`true`); the lemmas (empty proofs); and the operations that touch the fields (`borrow_typed_value`, `take_typed_value`, `put_typed_value`, `into_raw_parts`, `from_raw_parts`, `as_untyped`, `as_untyped_mut`) |
| `PointsToSingleValueSized for PointsToUnaligned<T>` | once (Sized `T` only) | the two lemmas |
| `PointsToPhys`, `PointsToProperties`, `View`, `PointsToSingleValue` for `PointsTo<T: ?Sized>` | once (generic) | delegation to `self.pt_unaligned`, except `satisfies_alignment` (adds alignment) and `from_raw_parts` (wraps the result) |
| `PointsToSingleValueSized for PointsTo<T>` | once (Sized `T` only) | the two lemmas (`lemma_satisfies_alignment_offset` has the real alignment proof) |
| trait default bodies | once (in the traits) | `wf`, `ptrs_len_same_valid`, `borrow`, `into_untyped`, `from_untyped`, `zero_sized`, `take`, `put`, `copy`, `copy_typed_value`, `from_untyped_with_value` |
| `impl<T: ?Sized> PointsToUnaligned<T> where PointsToUnaligned<T>: PointsToSingleValue<A = T>` | once (generic) | `into_aligned`, `as_aligned`, `as_aligned_mut` |
| `impl<T: ?Sized> PointsTo<T> where PointsToUnaligned<T>: PointsToSingleValue<A = T>` | once (generic) | `into_unaligned`, `as_unaligned`, `as_unaligned_mut` |
| `impl<T> PointsToUnaligned<[T]>` | once (slices) | the slice side of the slice ↔ sequence conversions (`as_seq_pt`, `as_seq_pt_mut`) and the borrowed constructors (`from_untyped_ref`, `from_untyped_with_value_ref`): the primary implementations |
| `impl<T> PointsTo<[T]>` | once (slices) | the same functions, as compositions over the `PointsToUnaligned<[T]>` versions and the aligned/unaligned conversions |

Sequences:

| Impl | Applies to | What it contains |
|---|---|---|
| structural `impl<T, P: PointsToProperties<A = T>>` (`points_to.rs`) | every sequence, untyped or typed | the only code touching the fields: accessors, `thin_ptr`, constructors, borrows, `split_basic`, `join_basic`, `subrange_basic` |
| `PointsToUntyped` (`points_to.rs`) | `SeqPointsTo<u8, PointsToByte>` | its `View`, `bytes`, `wf`, `split` / `join` / `split_ref` wrappers, and its axioms |
| typed `impl<T, P: PointsToSingleValueSized<A = T>>` (`points_to_permissions.rs`) | sequences of `PointsTo<T>` or `PointsToUnaligned<T>` | the generic `View`, `wf`, bytes and values, the typed `split` / `join` / `subrange` wrappers, `subrange_mut`, untyped conversions, value operations, `is_disjoint_seqpt`; so `SeqPointsTo<T, PointsToUnaligned<T>>` gets the whole typed API |
| `PointsToUnaligned<T>`-specific (`points_to_permissions.rs`) | `SeqPointsTo<T, PointsToUnaligned<T>>` | the sequence side of the slice ↔ sequence conversions (`as_slice_pt`, `as_slice_pt_mut`) and the borrowed constructors (the primary implementations); `into_aligned`, `as_aligned`, `as_aligned_mut` |
| `PointsTo<T>`-specific (`points_to_permissions.rs`) | `SeqPointsTo<T, PointsTo<T>>` | `is_aligned`; the slice ↔ sequence conversions and borrowed constructors as compositions over the `PointsToUnaligned<T>` versions; `into_unaligned`, `as_unaligned`, `as_unaligned_mut` |

**API changes not visible in the specs.**
Renames: `PointsToSingleton` → `PointsToByte`, `borrow_value` → `borrow`,
`into_untyped_with_typed_value` → `into_raw_parts` (single permissions only),
`borrow_value_subrange` → `borrow_subrange`,
`PointsToProperties::ptrs_len_same_valid` → `ptrs_len_same`.
Removed: `FixedSize`, `Dealloc`, and the inherent `PointsTo<T>` versions of the trait methods
(`points_to_permissions.rs` re-exports the four traits instead; the prelude is unchanged).

**Trait impls.** `T` is `Sized` (in `[T]`, it is the element type).
"Generic" means one `impl<T: ?Sized> ... for PointsTo<T> where PointsToUnaligned<T>: PointsToSingleValue<A = T>`.

| Type | `PointsToPhys`, `PointsToProperties`, `View` | `PointsToSingleValue` | `PointsToSingleValueSized` | Where | When |
|---|---|---|---|---|---|
| `PointsToUnaligned<T>` | `PointsToPhys`: per type; `PointsToProperties`: generic (phase 2) | yes | yes | vstd | phase 2 |
| `PointsToUnaligned<[T]>` | `PointsToPhys`: per type (done); `PointsToProperties`: generic (phase 2) | yes | no | vstd | phase 2b |
| `PointsToUnaligned<str>` | `PointsToPhys`: per type; `PointsToProperties`: generic | yes | no | rustlib | after phase 3b ([specs](#str-rustlib)) |
| `PointsTo<T>` | yes, generic | yes, generic | yes | vstd | phase 2 (generic from phase 2b) |
| `PointsTo<[T]>` | yes, generic | yes, generic | no | vstd, nothing slice-specific | phase 2b |
| `PointsTo<str>` | yes, generic | yes, generic | no | vstd, nothing `str`-specific | once rustlib adds `PointsToUnaligned<str>` |
| `SeqPointsTo<T, P>` (`A = [T]`) | yes (exists, generic) | no | no | vstd | pointer becomes `*mut [T]` in phase 1b |
| `PointsToByte` (`A = u8`) | yes (exists) | no | no | vstd | — |
| `PointsToRaw` | no (no single pointer) | no | no | vstd | phase 2c |

There is no `SeqPointsTo<str, _>`.

**Conversions.**

| From ↔ to | Owned | `&` | `&mut` | Where | When |
|---|---|---|---|---|---|
| `PointsTo<T>` ↔ `PointsToUnaligned<T>` | yes | yes | yes (to unaligned: field borrow; to aligned: M4) | vstd, generic aligned/unaligned impl | phase 2; `as_aligned_mut` in phase 3b |
| `PointsTo<[T]>` ↔ `PointsToUnaligned<[T]>` | yes | yes | yes (same) | vstd, same generic impl | phase 2b; `as_aligned_mut` in phase 3b |
| `PointsTo<str>` ↔ `PointsToUnaligned<str>` | yes | yes | yes (same) | vstd, same generic impl, no `str`-specific code | once rustlib adds `PointsToUnaligned<str>` |
| `SeqPointsTo<T, PointsTo<T>>` ↔ `SeqPointsTo<T, PointsToUnaligned<T>>` | yes | yes | yes | vstd | phase 4 |
| `PointsTo<[T]>` ↔ `SeqPointsTo<T, PointsTo<T>>` | no | yes | yes | vstd, composed from the unaligned version and the aligned/unaligned conversions | phase 4 |
| `PointsToUnaligned<[T]>` ↔ `SeqPointsTo<T, PointsToUnaligned<T>>` | no | yes | yes | vstd | phase 4 |
| `PointsToUnaligned<str>` ↔ `PointsToUnaligned<[u8]>` | yes | yes | yes | rustlib | after phase 3b ([specs](#str-rustlib)) |
| `PointsTo<str>` ↔ `PointsTo<[u8]>` | yes | yes | yes | rustlib, via the unaligned versions and the aligned/unaligned conversions | after phase 3b |
| `PointsToRaw` ↔ `PointsToUntyped` (a contiguous range) | yes | no | no | vstd | phase 2c |
| `PointsToRaw` ↔ any `PointsToSingleValue` / `SeqPointsTo`, through `PointsToUntyped` | yes (into typed: empty value) | no | no | vstd | phase 2c |

**Module layout** (on hold until the trusted axioms are reviewed):

| `points_to.rs` | `points_to_permissions.rs` |
|---|---|
| the traits `PointsToPhys`, `PointsToProperties` (and wherever `PointsToSingleValue(Sized)` is declared) | `TypedValue` |
| `PointsToByte` (axiomatized) | `PointsToUnaligned`, `PointsTo`, and their trait impls |
| `struct SeqPointsTo`, its generic `PointsToPhys` / `PointsToProperties` impls | the typed `SeqPointsTo` impl and its generic `View` |
| the structural `impl<T, P: PointsToProperties<A = T>> SeqPointsTo<T, P>` | the `PointsTo<T>`- and `PointsToUnaligned<T>`-specific `SeqPointsTo` impls |
| `PointsToUntyped`'s impl and its axioms (`join_ref`, `join_mut`) | re-exports of the four traits |
| | `PointsToRaw` |

**Still open.**

- The module split (trusted in `points_to.rs`, verified in `points_to_permissions.rs`):
  on hold until the trusted axioms are reviewed.
  In particular, whether the verified `SeqPointsTo` struct, structural impl and `PointsToUntyped` proofs
  stay in `points_to.rs`, and where phase 3b's new axioms go.
- Where the trusted functions that use verified permission types go, decided together:
  `allocate` / `deallocate` (use `PointsToRaw`),
  `ptr_ref`, `ptr_mut_ref`, `mut_ref_to_shr_points_to` (use `PointsTo<T>`),
  and the restored slice versions (`PointsTo<[T]>`).
  Trusted code shouldn't depend on verified code
  (see the dependency note in [Trusted surface](#trusted-surface)).
- Whether the reference helpers should ensure `wf()` (see the review notes in [Trusted surface](#trusted-surface)).

## Specifications

Bodies are omitted except for spec fns and trusted code.
"Unchanged" means the contract is today's, apart from `size()` → `Self::size(self.ptr()@.metadata)`.

### Traits

```rust
/// Defines the physical memory region that a `PointsTo` permission covers,
/// by specifying the pointer to memory and the size of the pointed-to region.
pub trait PointsToPhys: Sized {
    type A: ?Sized;

    /// The pointer that this permission is associated with.
    spec fn ptr(self) -> *mut Self::A;

    /// The size, in bytes, of the memory region tracked by a permission
    /// whose pointer has the given metadata.
    /// A permission `p` tracks `Self::size(p.ptr()@.metadata)` bytes.
    spec fn size(metadata: Metadata<Self::A>) -> nat;
}

/// Defines properties which should hold of any `PointsTo` permission.
pub trait PointsToProperties: PointsToPhys {
    /// Define basic well-formedness conditions on the permission's pointer.
    /// `PointsToSingleValue::wf` builds on this to add conditions on the bytes and typed value.
    spec fn wf_basic(self) -> bool;

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
    proof fn is_disjoint<OtherPointsToPerm: PointsToPhys>(
        tracked &mut self,
        tracked other: &OtherPointsToPerm,
    )
        requires
            Self::size(self.ptr()@.metadata) != 0,
            OtherPointsToPerm::size(other.ptr()@.metadata) != 0,
            self.wf_basic(),
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

impl<T: ?Sized> PointsToSingleValue for PointsTo<T> where PointsToUnaligned<T>: PointsToSingleValue<A = T> {
    // Everything delegates to self.pt_unaligned, except:
    open spec fn satisfies_alignment(addr: usize) -> bool {
        &&& PointsToUnaligned::<T>::satisfies_alignment(addr)
        &&& addr as nat % spec_align_of_val::<T>(arbitrary()) == 0
    }
    // from_raw_parts: wraps the PointsToUnaligned result.
    // wf, ptrs_len_same_valid, borrow, into_untyped, from_untyped, zero_sized: the trait's default bodies.
}

impl<T> PointsToSingleValueSized for PointsTo<T> {
    // lemma_satisfies_alignment_offset: the alignment arithmetic; lemma_metadata_matches: empty.
    // take, put, copy, copy_typed_value, from_untyped_with_value: the trait's default bodies.
}

impl<T: ?Sized> PointsToUnaligned<T> where PointsToUnaligned<T>: PointsToSingleValue<A = T> {
    /// Converts to a `PointsTo<T>`, given that the address is aligned.
    pub proof fn into_aligned(tracked self) -> (tracked out: PointsTo<T>)
        requires
            self.wf(),
            <PointsTo<T> as PointsToSingleValue>::satisfies_alignment(self.ptr()@.addr),
        ensures
            out.pt_unaligned() == self,
            out.wf(),
    ;

    /// Borrows as a `PointsTo<T>`, given that the address is aligned.
    pub proof fn as_aligned(tracked &self) -> (tracked out: &PointsTo<T>)
        requires
            self.wf(),
            <PointsTo<T> as PointsToSingleValue>::satisfies_alignment(self.ptr()@.addr),
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
            <PointsTo<T> as PointsToSingleValue>::satisfies_alignment(self.ptr()@.addr),
        ensures
            out.pt_unaligned() == *old(self),
            out.wf(),
            *final(self) == final(out).pt_unaligned(),
            <PointsTo<T> as PointsToSingleValue>::ptrs_len_same_valid(*out, *final(out)) ==> final(self).wf(),
    ;
}
impl<T: ?Sized> PointsTo<T> where PointsToUnaligned<T>: PointsToSingleValue<A = T> {
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

### `TypedValue` (phase 2)

```rust
impl<T: ?Sized> TypedValue<T> {
    /// If valid, a reference to the value; otherwise meaningless.
    /// Generalizes `TypedValue<T>::value()` (Sized, by value) and `TypedValue<[T]>::value()` (-> &[T]),
    /// which both stay.
    pub open spec fn value_ref(&self) -> &T
        recommends
            self is Valid,
    {
        &*self->0
    }
}
```

### `PointsToProperties` (changed in phase 1b)

The trait is in [Traits](#traits). Compared with today's:
contracts use `Self::size(self.ptr()@.metadata)` instead of `self.size()`;
`is_disjoint` compares `ptr()@.addr` instead of `ptr() as int`;
and `ptrs_len_same_valid` is renamed `ptrs_len_same` (pointer-level; the decoding version is
`PointsToSingleValue::ptrs_len_same_valid`), which `stays_wf_basic` now uses.

`group_points_to_permissions_lemmas` contains `PointsToSingleValue::lemma_ptrs_len_same_valid`
(in place of `PointsTo::lemma_ptrs_len_same_valid`),
the typed `SeqPointsTo::lemma_ptrs_len_same_valid`,
and `PointsToUntyped`'s lemma (renamed `lemma_ptrs_len_same_untyped`).

### `PointsToUnaligned` (phases 2, 2b; `str` in rustlib)

```rust
// One per type; only `size` differs.
impl<T> PointsToPhys for PointsToUnaligned<T> {
    type A = T;
    closed spec fn ptr(self) -> *mut T {
        ptr_mut_from_data::<T>(PtrData {
            addr: self.pt_untyped().ptr()@.addr,
            provenance: self.pt_untyped().ptr()@.provenance,
            metadata: self.metadata(),   // closed inherent accessor for the ghost field
        })
    }
    open spec fn size(metadata: ()) -> nat { size_of::<T>() }
}
impl<T> PointsToPhys for PointsToUnaligned<[T]> {
    type A = [T];
    closed spec fn ptr(self) -> *mut [T] { /* same as above */ }
    open spec fn size(metadata: usize) -> nat { metadata as nat * size_of::<T>() }
}
// rustlib: impl PointsToPhys for PointsToUnaligned<str> { type A = str; ptr: same; size(len) = len }

// One generic impl.
impl<T: ?Sized> PointsToProperties for PointsToUnaligned<T> where PointsToUnaligned<T>: PointsToPhys<A = T> {
    open spec fn wf_basic(self) -> bool {
        &&& self.pt_untyped().wf()
        &&& self.pt_untyped().len() == Self::size(self.ptr()@.metadata)
    }
    open spec fn ptrs_len_same(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& PointsToUntyped::ptrs_len_same(old.pt_untyped(), new.pt_untyped())
    }
    // is_nonnull, ptr_bounds, provenance_not_none, is_disjoint, stays_wf_basic: delegate to pt_untyped.
}

// PointsToSingleValue spec items per impl (the operations' contracts are the trait's):
//                     typed_value          bytes                     metadata_matches(v, m)   satisfies_alignment(a)
// PointsToUnaligned<T>    self.typed_value()   self.pt_untyped().bytes()  true                true
// PointsToUnaligned<[T]>  (same)               (same)                    v@.len() == m       true
// PointsToUnaligned<str>  (same)               (same)                    true                true   (rustlib; UTF-8 is in abs_decode::<str>)
// wf: the trait's default body. For T and [T], this replaces today's per-type wf_basic clauses.
```

### `PointsTo` (generic; phase 2, widened in phase 2b)

```rust
impl<T: ?Sized> PointsToPhys for PointsTo<T> where PointsToUnaligned<T>: PointsToSingleValue<A = T> {
    type A = T;
    open spec fn ptr(self) -> *mut T { self.pt_unaligned().ptr() }
    open spec fn size(metadata: Metadata<T>) -> nat { <PointsToUnaligned<T> as PointsToPhys>::size(metadata) }
}
impl<T: ?Sized> PointsToProperties for PointsTo<T> where PointsToUnaligned<T>: PointsToSingleValue<A = T> {
    open spec fn wf_basic(self) -> bool { self.pt_unaligned().wf_basic() }
    open spec fn ptrs_len_same(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& <PointsToUnaligned<T> as PointsToProperties>::ptrs_len_same(old.pt_unaligned(), new.pt_unaligned())
    }
    // proof fns delegate to pt_unaligned.
}
impl<T: ?Sized> View for PointsTo<T> where PointsToUnaligned<T>: PointsToSingleValue<A = T> {
    type V = PointsToData<T>;
    open spec fn view(&self) -> PointsToData<T> {
        PointsToData { ptr: self.ptr(), value: self.typed_value(), bytes: self.bytes() }
    }
}
// PointsToSingleValue: typed_value, bytes, metadata_matches delegate (naming the trait fns, phase 0 item 5);
//   satisfies_alignment(a) = PointsToUnaligned::<T>::satisfies_alignment(a) && a as nat % spec_align_of_val::<T>(arbitrary()) == 0;
//   wf: default body. (Sketch in Traits.)
```

### `SeqPointsTo` (phase 1b; typed impl generalized in phase 3)

In `points_to.rs`: the struct, its generic trait impls, the structural impl, and `PointsToUntyped`.

```rust
#[verifier::reject_recursive_types(T)]
pub tracked struct SeqPointsTo<T, P: PointsToProperties<A = T>> {
    seq_pt: Seq<P>,
    ptr: Ghost<*mut [T]>,
}

impl<T, P: PointsToProperties<A = T>> PointsToPhys for SeqPointsTo<T, P> {
    type A = [T];
    closed spec fn ptr(self) -> *mut [T] { self.ptr@ }
    open spec fn size(metadata: usize) -> nat { metadata as nat * P::size(()) }
}

impl<T, P: PointsToProperties<A = T>> PointsToProperties for SeqPointsTo<T, P> {
    open spec fn wf_basic(self) -> bool {
        &&& self.ptr()@.metadata == self.len()   // new (was only in PointsToUntyped::wf)
        &&& forall|i| 0 <= i < self.len() ==> {
            &&& self[i].ptr()@.provenance == self.ptr()@.provenance
            &&& self[i].ptr()@.addr == self.ptr()@.addr + i * P::size(())
            &&& self[i].wf_basic()
        }
        &&& self.ptr()@.addr != 0
        &&& /* provenance bounds: unchanged */
    }
    // ptrs_len_same (renamed from ptrs_len_same_valid; elements' ptrs_len_same), proof fns: unchanged.
}

/// Structural operations for a sequence of any element permission, stated with `wf_basic`.
impl<T, P: PointsToProperties<A = T>> SeqPointsTo<T, P> {
    /// The element permissions.
    pub closed spec fn seq_pt(self) -> Seq<P> {
        self.seq_pt
    }

    /// The number of element permissions.
    pub open spec fn len(self) -> nat {
        self.seq_pt().len()
    }

    pub open spec fn spec_index(self, index: int) -> P
        recommends
            0 <= index < self.len(),
    {
        self.seq_pt()[index]
    }

    /// The pointer to the first element, without the length.
    /// For code that doesn't care about the slice metadata.
    pub open spec fn thin_ptr(self) -> *mut T {
        ptr_mut_from_data::<T>(PtrData { addr: self.ptr()@.addr, provenance: self.ptr()@.provenance, metadata: () })
    }

    /// Borrows the element permissions.
    pub proof fn tracked_seq_pt(tracked &self) -> tracked &Seq<P>
        returns
            self.seq_pt(),
    ;

    /// Mutably borrows the element permissions; the pointer is unchanged.
    /// If the final permissions keep the original pointers and lengths,
    /// `self` is pointer-level well-formed (`wf_basic`) afterwards.
    pub proof fn tracked_seq_pt_mut(tracked &mut self) -> (tracked ret: &mut Seq<P>)
        ensures
            *ret == old(self).seq_pt(),
            final(self).seq_pt() == *final(ret),
            final(self).ptr() == old(self).ptr(),
            old(self).wf_basic() && Self::ptrs_len_same(*old(self), *final(self)) ==> final(self).wf_basic(),
    ;

    /// Mutably borrows the element permission at index `i`; the pointer is unchanged.
    pub proof fn index_mut(tracked &mut self, i: int) -> (tracked ret: &mut P)
        requires
            0 <= i < self.len(),
        ensures
            *ret == old(self)[i],
            final(self).seq_pt() == old(self).seq_pt().update(i, *final(ret)),
            final(self).ptr() == old(self).ptr(),
            old(self).wf_basic() && P::ptrs_len_same(*ret, *final(ret)) ==> final(self).wf_basic(),
    ;

    /// Creates a sequence from element permissions at consecutive offsets from `ptr`.
    pub proof fn from_seq(tracked r: Seq<P>, ptr: *mut T) -> (tracked s: Self)
        requires
            forall|i: int| 0 <= i < r.len() ==> #[trigger] r[i].wf_basic(),
            forall|i: int| 0 <= i < r.len() ==> {
                &&& (#[trigger] r[i]).ptr()@.provenance == ptr@.provenance
                &&& r[i].ptr()@.addr == ptr@.addr + i * P::size(())
            },
            ptr@.addr != 0,
            ptr_addr_in_bounds(ptr),
            r.len() <= usize::MAX,
        ensures
            s.seq_pt() == r,
            s.thin_ptr() == ptr,
            s.wf_basic(),
    ;

    /// Creates an empty sequence at `ptr`.
    pub proof fn empty(ptr: *mut T) -> (tracked s: Self)
        requires
            ptr@.addr != 0,
            ptr_addr_in_bounds(ptr),
        ensures
            s.seq_pt() == Seq::<P>::empty(),
            s.thin_ptr() == ptr,
            s.wf_basic(),
    ;

    /// Returns the element permissions.
    pub proof fn into_seq(tracked self) -> (tracked r: Seq<P>)
        returns
            self.seq_pt(),
    ;

    /// Splits into the first `mid` element permissions and the rest.
    pub proof fn split_basic(tracked self, mid: nat) -> (tracked (first, second): (Self, Self))
        requires
            self.wf_basic(),
            mid <= self.len(),
        ensures
            first.seq_pt() == self.seq_pt().take(mid as int),
            second.seq_pt() == self.seq_pt().skip(mid as int),
            first.thin_ptr() == self.thin_ptr(),
            second.thin_ptr() == ptr_mut_from_data::<T>(PtrData {
                addr: (self.ptr()@.addr + mid * P::size(())) as usize,
                provenance: self.ptr()@.provenance,
                metadata: (),
            }),
            first.wf_basic(),
            second.wf_basic(),
    ;

    /// Concatenates two sequences, where `other` starts where `self` ends.
    pub proof fn join_basic(tracked self, tracked other: Self) -> (tracked joined: Self)
        requires
            self.wf_basic(),
            other.wf_basic(),
            self.ptr()@.provenance == other.ptr()@.provenance,
            other.ptr()@.addr == self.ptr()@.addr + self.len() * P::size(()),
        ensures
            joined.seq_pt() == self.seq_pt() + other.seq_pt(),
            joined.thin_ptr() == self.thin_ptr(),
            joined.wf_basic(),
    ;

    /// Borrows the sub-sequence of `len` element permissions starting at `start`.
    pub proof fn subrange_basic(tracked &self, start: nat, len: nat) -> (tracked sub: &Self)
        requires
            self.wf_basic(),
            start + len <= self.len(),
        ensures
            sub.seq_pt() == self.seq_pt().subrange(start as int, (start + len) as int),
            sub.thin_ptr() == ptr_mut_from_data::<T>(PtrData {
                addr: (self.ptr()@.addr + start * P::size(())) as usize,
                provenance: self.ptr()@.provenance,
                metadata: (),
            }),
            sub.wf_basic(),
    ;

    /// Borrows element permissions at consecutive offsets from `ptr` as one borrowed sequence
    /// (the borrowed counterpart of `from_seq`).
    /// Says nothing about `wf_basic`: callers prove it from the elements, as for `from_seq`.
    /// Phase 3b; proved from `tracked_collect_perm_refs`
    /// (see [Borrowed-assembly axioms](#borrowed-assembly-axioms-phase-3b)).
    pub proof fn from_refs<'a>(tracked perms: Seq<&'a P>, ptr: *mut T) -> (tracked out: &'a Self)
        requires
            perms.len() <= usize::MAX,
            forall|i: int| 0 <= i < perms.len() ==> {
                &&& (#[trigger] perms[i]).ptr()@.provenance == ptr@.provenance
                &&& perms[i].ptr()@.addr == ptr@.addr + i * P::size(())
            },
        ensures
            out.seq_pt() == perms.map_values(|r: &P| *r),
            out.thin_ptr() == ptr,
            out.len() == perms.len(),
    {
        let tracked s = tracked_collect_perm_refs(perms);
        let ghost slice_ptr = ptr_mut_from_data::<[T]>(
            PtrData { addr: ptr@.addr, provenance: ptr@.provenance, metadata: perms.len() as usize });
        shr_ref_struct_wrap(s, &SeqPointsTo { seq_pt: *s, ptr: Ghost(slice_ptr) }, "", "seq_pt")
    }

    /// M5: a mutably borrowed `Seq<P>` acts as a mutably borrowed sequence with the given (ghost) pointer.
    /// Phase 3b (new axiom).
    pub axiom fn from_seq_mut<'a>(tracked s: &'a mut Seq<P>, ptr: *mut [T]) -> (tracked out: &'a mut Self)
        ensures
            out.seq_pt() == *old(s),
            out.ptr() == ptr,
            *final(s) == final(out).seq_pt(),
    ;
}

impl SeqPointsTo<u8, PointsToByte> {   // PointsToUntyped
    pub open spec fn wf(self) -> bool { self.wf_basic() }   // the metadata clause moved to wf_basic
    // split, join, split_ref: wrappers over split_basic / join_basic / subrange_basic (same contracts as today).
    // View, bytes, stays_wf, lemma_ptrs_len_same_untyped, zero_sized, is_disjoint_untyped,
    // join_ref, join_mut, split_mut: today's contracts, proved in phase 3b
    //   (join_ref from from_refs; join_mut and split_mut from M5 + M6).
    //   Until then join_ref / join_mut stay axioms and split_mut stays commented out.
}
```

In `points_to_permissions.rs`: the typed sequence.
`from_seq`, `empty`, `into_seq`, `tracked_seq_pt(_mut)` and `index_mut` have no typed versions.

```rust
// Phase 1b: on SeqPointsTo<T, PointsTo<T>>.
// Phase 3: moved to impl<T, P: PointsToSingleValueSized<A = T>>, with PointsTo<T> -> P,
//          size_of::<T>() -> P::size(()), PointsTo::<T>::satisfies_alignment -> P::satisfies_alignment.
impl<T> SeqPointsTo<T, PointsTo<T>> {
    pub open spec fn wf(self) -> bool {
        &&& self.wf_basic()
        &&& PointsTo::<T>::satisfies_alignment(self.ptr()@.addr)
        &&& forall|i| 0 <= i < self.len() ==> #[trigger] self[i].wf()
    }

    /// The pointer-level `ptrs_len_same`, plus each element's `PointsToSingleValue::ptrs_len_same_valid`.
    /// Used by `stays_wf` and by the re-establishing clauses of `tracked_seq_pt_mut` / `index_mut` (unchanged).
    pub open spec fn ptrs_len_same_valid(old: Self, new: Self) -> bool {
        &&& Self::ptrs_len_same(old, new)
        &&& forall|i| 0 <= i < new.len() ==> PointsTo::<T>::ptrs_len_same_valid(old[i], #[trigger] new[i])
    }

    pub proof fn stays_wf(old: Self, new: Self)
        requires
            old.wf(),
            Self::ptrs_len_same_valid(old, new),
        ensures
            new.wf(),
    ;

    /// Same pointer means same length (the pointer carries it), so no separate length condition.
    pub broadcast proof fn lemma_ptrs_len_same_valid(old: Self, new: Self)
        requires
            old.wf(),
            new.wf(),
            new.ptr() == old.ptr(),
        ensures
            #[trigger] Self::ptrs_len_same_valid(old, new),
    ;

    /// Built by collecting `length` zero-sized element permissions and calling `from_seq`.
    pub proof fn zero_sized(ptr: *mut T, length: nat) -> (tracked s: Self)
        requires
            ptr@.addr != 0,
            PointsTo::<T>::satisfies_alignment(ptr@.addr),
            ptr_addr_in_bounds(ptr),
            size_of::<T>() == 0,
            length <= usize::MAX,    // new
        ensures
            forall|i| 0 <= i < s.len() ==> (#[trigger] s[i]).is_empty(),
            s.thin_ptr() == ptr,
            s.len() == length,
            s.wf(),
    ;

    /// Built on `split_basic`, adding the bytes, alignment and element `wf` facts.
    pub proof fn split(tracked self, mid: nat) -> (tracked (first, second): (Self, Self))
        requires
            mid <= self.len(),
            self.wf(),
        ensures
            first.seq_pt() == self.seq_pt().take(mid as int),
            second.seq_pt() == self.seq_pt().skip(mid as int),
            first.bytes() == self.bytes().take(mid as int * size_of::<T>()),
            second.bytes() == self.bytes().skip(mid as int * size_of::<T>()),
            first.thin_ptr() == self.thin_ptr(),   // was first.ptr() == self.ptr()
            second.thin_ptr() == ptr_mut_from_data::<T>(PtrData {
                addr: (self.ptr()@.addr + mid * size_of::<T>()) as usize,
                provenance: self.ptr()@.provenance,
                metadata: (),
            }),
            first.wf(),
            second.wf(),
    ;

    /// Built on `join_basic`, adding the bytes and `wf` facts.
    pub proof fn join(tracked self, tracked other: Self) -> (tracked joined: Self)
        requires
            self.wf(),
            other.wf(),
            self.ptr()@.provenance == other.ptr()@.provenance,
            other.ptr()@.addr == self.ptr()@.addr + self.len() * size_of::<T>(),
        ensures
            joined.thin_ptr() == self.thin_ptr(),  // was joined.ptr() == self.ptr()
            joined.seq_pt() == self.seq_pt() + other.seq_pt(),
            joined.bytes() == self.bytes() + other.bytes(),
            joined.wf(),
    ;

    /// Built on `subrange_basic`, adding the alignment and `wf` facts.
    pub proof fn subrange(tracked &self, start_index: nat, len: nat) -> (tracked sub: &Self)
        requires
            self.wf(),
            start_index + len <= self.len(),
        ensures
            sub.wf(),
            sub.thin_ptr() == ptr_mut_from_data::<T>(PtrData {
                addr: (self.ptr()@.addr + start_index * size_of::<T>()) as usize,
                provenance: self.ptr()@.provenance,
                metadata: (),
            }),
            sub.seq_pt() == self.seq_pt().subrange(start_index as int, (start_index + len) as int),
    ;

    /// Proved from M5 (`from_seq_mut`) in phase 3b;
    /// until then, an axiom on `SeqPointsTo<T, PointsTo<T>>` only.
    pub proof fn subrange_mut(tracked &mut self, i: nat, j: nat) -> (tracked r: &mut Self)
        requires
            self.wf(),
            i <= j <= self.len(),
        ensures
            r.wf(),
            r.thin_ptr() == ptr_mut_from_data::<T>(PtrData {
                addr: (old(self).ptr()@.addr + i * size_of::<T>()) as usize,
                provenance: old(self).ptr()@.provenance,
                metadata: (),
            }),
            r.seq_pt() == old(self).seq_pt().subrange(i as int, j as int),
            final(r).wf() && final(r).ptr() == r.ptr() ==> {   // same ptr: same thin_ptr and length
                &&& final(self).wf()
                &&& final(self).ptr() == old(self).ptr()
                &&& final(self).seq_pt() == old(self).seq_pt().subrange(0, i as int) + final(r).seq_pt()
                    + old(self).seq_pt().subrange(j as int, old(self).len() as int)
            },
    ;

    pub proof fn from_untyped(tracked pt_untyped: PointsToUntyped, len: usize) -> (tracked out: Self)
        requires
            pt_untyped.wf(),
            PointsTo::<T>::satisfies_alignment(pt_untyped.ptr()@.addr),
            pt_untyped.len() == len * size_of::<T>(),
        ensures
            out.ptr()@.addr == pt_untyped.ptr()@.addr,          // was out.ptr() == pt_untyped.ptr() as *mut T
            out.ptr()@.provenance == pt_untyped.ptr()@.provenance,
            out.len() == len,
            out.bytes() == pt_untyped.bytes(),
            out.is_fully_empty(),
            out.wf(),
    ;

    pub proof fn from_untyped_with_typed_value(
        tracked pt_untyped: PointsToUntyped,
        capacity: usize,
        tracked typed_value: Seq<TypedValue<T>>,
    ) -> (tracked out: Self)
        requires
            pt_untyped.wf(),
            PointsTo::<T>::satisfies_alignment(pt_untyped.ptr()@.addr),
            pt_untyped.len() == capacity * size_of::<T>(),
            typed_value.len() <= capacity,
            forall|i: int| 0 <= i < typed_value.len() && typed_value[i].is_valid() ==> #[trigger] abs_decode::<T>(
                pt_untyped.bytes().subrange(i * size_of::<T>(), (i + 1) * size_of::<T>()),
                &typed_value[i].value(),
            ),
        ensures
            out.ptr()@.addr == pt_untyped.ptr()@.addr,
            out.ptr()@.provenance == pt_untyped.ptr()@.provenance,
            out.len() == capacity,
            out.bytes() == pt_untyped.bytes(),
            forall|i: int| 0 <= i < typed_value.len() ==> (#[trigger] out[i]).typed_value() == typed_value[i],
            out.wf(),
    ;

    // `untyped_mut_join(perms, base: *mut T)`: `base` stays a thin pointer.
    // `View` moves to the generic impl below.
    // into_untyped*, as_untyped*, the value operations, the byte lemmas: unchanged,
    // except `borrow_value_subrange` is renamed `borrow_subrange`
    // (matching `take_subrange` / `put_subrange` / `copy_subrange` and `PointsToSingleValue::borrow`).

    /// Specializes `is_disjoint` to another typed sequence.
    /// Moves to the generic typed impl in phase 3 with everything else here
    /// (so `PointsToUnaligned` sequences get it too), with `other` generalized to any typed sequence.
    /// (`PointsToUntyped::is_disjoint_untyped` stays as it is.)
    pub proof fn is_disjoint_seqpt<S, Q: PointsToSingleValueSized<A = S>>(
        tracked &mut self,
        tracked other: &SeqPointsTo<S, Q>,
    )
        requires
            self.wf(),
            self.len() != 0,
            other.len() != 0,
            size_of::<T>() != 0,
            Q::size(()) != 0,
        ensures
            *old(self) == *final(self),
            final(self).ptr()@.addr + final(self).len() * size_of::<T>() <= other.ptr()@.addr
                || other.ptr()@.addr + other.len() * Q::size(()) <= final(self).ptr()@.addr,
    ;
}

/// The interface for a sequence of single-value permissions:
/// the pointer to the whole range and the element permissions.
#[cfg(verus_keep_ghost)]
pub ghost struct SeqPointsToData<T, P> {
    pub ptr: *mut [T],
    pub seq_pt: Seq<P>,
}

// One View for every typed sequence (generalized from `SeqPointsTo<T, PointsTo<T>>`).
// `PointsToUntyped` keeps its own `View` (`PointsToUntypedData`);
// the two impls don't overlap, since `PointsToByte` doesn't implement `PointsToSingleValueSized`.
#[cfg(verus_keep_ghost)]
impl<T, P: PointsToSingleValueSized<A = T>> View for SeqPointsTo<T, P> {
    type V = SeqPointsToData<T, P>;

    open spec fn view(&self) -> SeqPointsToData<T, P> {
        SeqPointsToData { ptr: self.ptr(), seq_pt: self.seq_pt() }
    }
}
```

### Borrowed-assembly axioms (phase 3b)

Trusted. M5 (`from_seq_mut`) is in the structural `SeqPointsTo` impl above.

**Shared.**

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

// modes.rs, next to tracked_swap
pub axiom fn tracked_ref<'a, T: ?Sized>(tracked t: &'a T) -> (tracked out: &'a Tracked<T>)
    ensures
        &**out == t,
;

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

// Collects borrowed permissions (not arbitrary values) into a borrowed Seq.
// Makes SeqPointsTo::from_refs provable (see the structural impl above).
pub axiom fn tracked_collect_perm_refs<'a, P: PointsToProperties>(tracked perms: Seq<&'a P>)
    -> (tracked out: &'a Seq<P>)
    ensures
        *out == perms.map_values(|r: &P| *r),
;

impl<T: ?Sized> TypedValue<T> {
    /// Borrows a value as a valid typed value.
    pub proof fn valid_ref<'a>(tracked v: &'a T) -> (tracked out: &'a TypedValue<T>)
        ensures
            out.is_valid(),
            out.value_ref() == v,
    {
        let tracked t = tracked_ref(v);
        shr_ref_struct_wrap(t, &TypedValue::Valid(*t), "Valid", "0")
    }
}
```

**`&mut`.**

```rust
impl<T> TypedValue<[T]> {
    /// M1: per-element typed values -> one slice typed value.
    pub axiom fn from_elems_mut<'a>(tracked elems: Seq<&'a mut TypedValue<T>>)
        -> (tracked out: &'a mut TypedValue<[T]>)
        requires
            (forall|i: int| 0 <= i < elems.len() ==> (#[trigger] *elems[i]).is_valid())
                || (forall|i: int| 0 <= i < elems.len() ==> (#[trigger] *elems[i]).is_empty()),
        ensures
            // Initially: valid with the elements' values (a zero-length Seq counts as valid), or empty.
            (forall|i: int| 0 <= i < elems.len() ==> (#[trigger] *elems[i]).is_valid()) ==> {
                &&& out.is_valid()
                &&& out.value()@ == Seq::new(elems.len(), |i: int| (*elems[i]).value())
            },
            elems.len() > 0 && (*elems[0]).is_empty() ==> out.is_empty(),
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

    /// M2: one slice typed value -> per-element typed values (the inverse of M1).
    pub axiom fn into_elems_mut<'a>(tracked &'a mut self, len: nat)
        -> (tracked elems: Seq<&'a mut TypedValue<T>>)
        requires
            old(self).is_valid() ==> old(self).value()@.len() == len,
        ensures
            // Initially: one element per slice element, each valid with its value, or each empty.
            elems.len() == len,
            old(self).is_valid() ==> forall|i: int| 0 <= i < len ==> {
                &&& (#[trigger] *elems[i]).is_valid()
                &&& (*elems[i]).value() == old(self).value()@[i]
            },
            old(self).is_empty() ==> forall|i: int| 0 <= i < len ==> (#[trigger] *elems[i]).is_empty(),
            // Finally: if every element ends valid, the slice holds them;
            // otherwise it ends empty (any remaining values are dropped).
            (forall|i: int| 0 <= i < len ==> (#[trigger] *final(elems[i])).is_valid()) ==> {
                &&& final(self).is_valid()
                &&& final(self).value()@ == Seq::new(len, |i: int| (*final(elems[i])).value())
            },
            !(forall|i: int| 0 <= i < len ==> (#[trigger] *final(elems[i])).is_valid())
                ==> final(self).is_empty(),
    ;
}

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

// M5 (SeqPointsTo::from_seq_mut) is in the structural SeqPointsTo impl above.

/// M6: the `&mut` version of `tracked_collect_perm_refs`.
pub axiom fn tracked_collect_perm_muts<'a, P: PointsToProperties>(tracked perms: Seq<&'a mut P>)
    -> (tracked out: &'a mut Seq<P>)
    ensures
        *out == Seq::new(perms.len(), |i: int| *perms[i]),
        // Finally: the permissions are tied back only if the length is unchanged.
        final(out).len() == perms.len() ==> forall|i: int|
            0 <= i < perms.len() ==> *final(perms[i]) == #[trigger] final(out)[i],
;
```

### Unaligned sequence conversions (phase 4)

```rust
impl<T> SeqPointsTo<T, PointsTo<T>> {
    pub proof fn into_unaligned(tracked self) -> (tracked out: SeqPointsTo<T, PointsToUnaligned<T>>)
        requires
            self.wf(),
        ensures
            out.ptr() == self.ptr(),
            out.len() == self.len(),
            forall|i| 0 <= i < out.len() ==> #[trigger] out[i] == self[i].pt_unaligned(),
            out.wf(),
    ;
    // as_unaligned(&self) -> &SeqPointsTo<T, PointsToUnaligned<T>>: same ensures (via from_refs).
    // as_unaligned_mut(&mut self): initially the same; finally, if final(out).wf() and
    //   final(out).ptr() == out.ptr(), then final(self).wf(), final(self).ptr() == old(self).ptr(),
    //   and final(self)[i].pt_unaligned() == final(out)[i] (via M4-M6).
}

impl<T> SeqPointsTo<T, PointsToUnaligned<T>> {
    pub proof fn into_aligned(tracked self) -> (tracked out: SeqPointsTo<T, PointsTo<T>>)
        requires
            self.wf(),
            PointsTo::<T>::satisfies_alignment(self.ptr()@.addr),
        ensures
            out.ptr() == self.ptr(),
            out.len() == self.len(),
            forall|i| 0 <= i < out.len() ==> (#[trigger] out[i]).pt_unaligned() == self[i],
            out.wf(),
    ;
    // as_aligned(&self), as_aligned_mut(&mut self): as for as_unaligned(_mut), with the alignment precondition.
}
```

### Slice ↔ sequence conversions (phase 4)

The `PointsTo<[T]>` / `SeqPointsTo<T, PointsTo<T>>` versions have the same contracts
with `PointsTo` in place of `PointsToUnaligned`, plus alignment where the result is aligned.

```rust
impl<T> SeqPointsTo<T, PointsToUnaligned<T>> {
    /// A `PointsToUnaligned<[T]>` is all valid or all empty.
    pub proof fn as_slice_pt(tracked &self) -> (tracked out: &PointsToUnaligned<[T]>)
        requires
            self.wf(),
            self.is_valid() || self.is_fully_empty(),
        ensures
            out.ptr() == self.ptr(),
            out.bytes() == self.bytes(),
            self.is_valid() ==> out.typed_value().is_valid() && out.typed_value().value_ref()@ == self.seq_value(),
            !self.is_valid() ==> out.typed_value().is_empty(),
            out.wf(),
    ;

    pub proof fn as_slice_pt_mut(tracked &mut self) -> (tracked out: &mut PointsToUnaligned<[T]>)
        requires
            self.wf(),
            self.is_valid() || self.is_fully_empty(),
        ensures
            // initially: as for as_slice_pt, with old(self)
            final(out).wf() && final(out).ptr() == out.ptr() ==> {
                &&& final(self).wf()
                &&& final(self).ptr() == old(self).ptr()
                &&& final(self).bytes() == final(out).bytes()
                &&& final(out).typed_value().is_valid() ==> final(self).is_valid()
                    && final(self).seq_value() == final(out).typed_value().value_ref()@
                &&& final(out).typed_value().is_empty() ==> final(self).is_fully_empty()
            },
    ;
}

impl<T> PointsToUnaligned<[T]> {
    pub proof fn as_seq_pt(tracked &self) -> (tracked out: &SeqPointsTo<T, PointsToUnaligned<T>>)
        requires
            self.wf(),
        ensures
            out.ptr() == self.ptr(),
            out.bytes() == self.bytes(),
            self.typed_value().is_valid() ==> out.is_valid() && out.seq_value() == self.typed_value().value_ref()@,
            self.typed_value().is_empty() ==> out.is_fully_empty(),
            out.wf(),
    ;

    pub proof fn as_seq_pt_mut(tracked &mut self) -> (tracked out: &mut SeqPointsTo<T, PointsToUnaligned<T>>)
        requires
            self.wf(),
        ensures
            // initially: as for as_seq_pt, with old(self)
            final(out).wf() && final(out).ptr() == out.ptr() ==> {
                &&& final(self).wf()
                &&& final(self).ptr() == old(self).ptr()
                &&& final(self).bytes() == final(out).bytes()
                &&& final(out).is_valid() ==> final(self).typed_value().is_valid()
                    && final(self).typed_value().value_ref()@ == final(out).seq_value()
                &&& !final(out).is_valid() ==> final(self).typed_value().is_empty()   // partial validity is dropped
            },
    ;
}
```

The borrowed constructors are the borrowed counterparts of the owned `from_untyped` / `from_untyped_with_typed_value`:

```rust
impl<T> PointsToUnaligned<[T]> {
    /// An empty slice permission of `len` elements borrowed from untyped bytes.
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

    /// A valid slice permission holding `value`, borrowed from untyped bytes that decode to it.
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

impl<T> SeqPointsTo<T, PointsToUnaligned<T>> {
    // from_untyped_ref(&'a PointsToUntyped, len) -> &'a Self:
    //   as PointsToUnaligned::<[T]>::from_untyped_ref, with out.thin_ptr() at pt_untyped's address
    //   and provenance, out.len() == len, and out.is_fully_empty().
    // from_untyped_with_value_ref(&'a PointsToUntyped, &'a [T]) -> &'a Self:
    //   as PointsToUnaligned::<[T]>::from_untyped_with_value_ref, with out.len() == value@.len(),
    //   out.is_valid(), and out.seq_value() == value@.
}
// PointsTo<[T]> and SeqPointsTo<T, PointsTo<T>> versions: the same, plus alignment
// (PointsTo::<T>::satisfies_alignment of the address) as a precondition.
```

### Slice reference helpers (phase 4b)

Trusted. Restored from commented-out code, each mirroring an existing Sized version.

```rust
// shared_reference.rs (restored from lines 126 and 221)
impl<'a, T> SharedReference<'a, [T]> {
    /// A shared slice reference gives a shared, valid slice permission.
    pub axiom fn points_to(tracked self) -> (tracked pt: &'a PointsTo<[T]>)
        ensures
            pt.ptr() == self.ptr(),
            pt.is_valid(),
            pt.typed_value().value_ref()@ == self.value()@,
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
    ensures
        v.value()@ == perm.typed_value().value_ref()@,
        v.ptr() == ptr,
;

// raw_ptr_new.rs (restored from lines 524, 559 and 683)
/// Equivalent to `&*ptr`, passing in a permission `perm` to ensure safety.
#[verifier::external_body]
pub const fn ptr_ref_slice<T>(ptr: *const [T], Tracked(perm): Tracked<&PointsTo<[T]>>) -> (v: &[T])
    requires
        perm.ptr() == ptr,
        perm.is_valid(),
    ensures
        v@ == perm.typed_value().value_ref()@,
    opens_invariants none
    no_unwind
{
    unsafe { &*ptr }
}

/// Equivalent to `&mut *ptr`, passing in a permission `perm` to ensure safety.
#[verifier::external_body]
pub const fn ptr_mut_ref_slice<T>(ptr: *mut [T], Tracked(perm): Tracked<&mut PointsTo<[T]>>) -> (v: &mut [T])
    requires
        old(perm).ptr() == ptr,
        old(perm).is_valid(),
    ensures
        final(perm).ptr() == ptr,
        final(perm).is_valid(),
        old(perm).typed_value().value_ref()@ == v@,
        final(perm).typed_value().value_ref()@ == final(v)@,
    opens_invariants none
    no_unwind
{
    unsafe { &mut *ptr }
}

/// Convert from a shared reference to a `&'a mut [T]` to a `&'a PointsTo<[T]>`.
pub axiom fn mut_ref_to_shr_points_to_slice<'a, T>(tracked mut_ref: &'a &'a mut [T])
    -> (tracked pt: &'a PointsTo<[T]>)
    ensures
        pt.ptr() == mut_ref_ptr(*mut_ref),
        pt.is_valid(),
        pt.typed_value().value_ref()@ == (*old(*mut_ref))@,
        &*final(*mut_ref) == &*old(*mut_ref),
;
```

### `PointsToRaw` (phase 2c)

```rust
pub tracked struct PointsToRaw {
    bytes: Map<int, PointsToByte>,
    provenance: Ghost<Provenance>,
}

impl PointsToRaw {
    #[verifier::type_invariant]
    spec fn inv(self) -> bool {
        &&& self.bytes.dom().finite()
        &&& forall|a: int| #[trigger] self.bytes.dom().contains(a) ==> {
            &&& self.bytes[a].ptr()@.addr == a
            &&& self.bytes[a].ptr()@.provenance == self.provenance@
            &&& self.provenance@ != Provenance::None
            &&& self.provenance@.start_addr() <= a < self.provenance@.start_addr() + self.provenance@.alloc_len()
        }
    }

    pub closed spec fn provenance(self) -> Provenance { self.provenance@ }
    pub closed spec fn dom(self) -> Set<int> { self.bytes.dom() }
    /// The abstract byte at `a` (new: the old PointsToRaw had no contents).
    pub closed spec fn byte(self, a: int) -> AbstractByte recommends self.dom().contains(a) { self.bytes[a].byte() }
    pub open spec fn is_range(self, start: int, len: int) -> bool { set_int_range(start, start + len) =~= self.dom() }
    pub open spec fn contains_range(self, start: int, len: int) -> bool { set_int_range(start, start + len) <= self.dom() }
    /// The contents of `[start, start + len)` as a sequence.
    pub open spec fn bytes_range(self, start: int, len: nat) -> Seq<AbstractByte> { Seq::new(len, |i: int| self.byte(start + i)) }

    pub proof fn empty(provenance: Provenance) -> (tracked out: Self)
        ensures
            out.dom() == Set::<int>::empty(),
            out.provenance() == provenance,
    ;

    pub proof fn split(tracked self, range: Set<int>) -> (tracked res: (Self, Self))
        requires
            range.subset_of(self.dom()),
        ensures
            res.0.provenance() == self.provenance(),
            res.1.provenance() == self.provenance(),
            res.0.dom() == range,
            res.1.dom() == self.dom().difference(range),
            forall|a| res.0.dom().contains(a) ==> #[trigger] res.0.byte(a) == self.byte(a),
            forall|a| res.1.dom().contains(a) ==> #[trigger] res.1.byte(a) == self.byte(a),
    ;

    pub proof fn join(tracked self, tracked other: Self) -> (tracked joined: Self)
        requires
            self.provenance() == other.provenance(),
        ensures
            joined.provenance() == self.provenance(),
            joined.dom() == self.dom() + other.dom(),
            forall|a| self.dom().contains(a) ==> #[trigger] joined.byte(a) == self.byte(a),
            forall|a| other.dom().contains(a) ==> #[trigger] joined.byte(a) == other.byte(a),
            // (the domains are disjoint by is_disjoint, so these don't conflict)
    ;

    /// Stronger than the old axiom (`<` instead of `<=` at the end).
    pub proof fn ptr_bounds(tracked &self)
        requires
            self.provenance().is_some(),
        ensures
            forall|a| self.dom().contains(a) ==> self.provenance().start_addr() <= a
                < self.provenance().start_addr() + self.provenance().alloc_len(),
    ;

    pub proof fn provenance_non_null(tracked &self)
        requires
            self.dom() != Set::<int>::empty(),
        ensures
            self.provenance() != Provenance::None,
    ;

    pub proof fn is_disjoint(tracked &mut self, tracked other: &PointsToRaw)
        requires
            self.dom() != Set::<int>::empty(),
            other.dom() != Set::<int>::empty(),
        ensures
            *old(self) == *final(self),
            final(self).dom().intersect(other.dom()).is_empty(),
    ;

    pub proof fn from_untyped(tracked pt_untyped: PointsToUntyped) -> (tracked out: Self)
        requires
            pt_untyped.wf(),
        ensures
            out.provenance() == pt_untyped.ptr()@.provenance,
            out.is_range(pt_untyped.ptr()@.addr as int, pt_untyped.len() as int),
            out.bytes_range(pt_untyped.ptr()@.addr as int, pt_untyped.len()) == pt_untyped.bytes(),
    ;

    pub proof fn into_untyped(tracked self, start: usize, len: nat) -> (tracked out: PointsToUntyped)
        requires
            self.is_range(start as int, len as int),
            len <= usize::MAX,
            start != 0,
            len == 0 ==> ptr_addr_in_bounds(ptr_mut_from_data::<[u8]>(
                PtrData { addr: start, provenance: self.provenance(), metadata: 0 })),
        ensures
            out.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData { addr: start, provenance: self.provenance(), metadata: len as usize }),
            out.bytes() == self.bytes_range(start as int, len),
            out.wf(),
    ;

    /// Replaces into_typed<V> and into_typed_slice<V>: an empty permission of any PointsToSingleValue type.
    pub proof fn into_typed<P: PointsToSingleValue>(tracked self, start: usize, metadata: Metadata<P::A>) -> (tracked out: P)
        requires
            self.is_range(start as int, P::size(metadata) as int),
            P::satisfies_alignment(start),
            start != 0,
            P::size(metadata) == 0 ==> ptr_addr_in_bounds(ptr_mut_from_data::<P::A>(
                PtrData { addr: start, provenance: self.provenance(), metadata })),
        ensures
            out.ptr() == ptr_mut_from_data::<P::A>(PtrData { addr: start, provenance: self.provenance(), metadata }),
            out.bytes() == self.bytes_range(start as int, P::size(metadata)),
            out.typed_value().is_empty(),
            out.wf(),
    ;

    /// Replaces PointsTo<V>::into_raw and PointsTo<[V]>::into_raw; no is_uninit() requirement.
    pub proof fn from_typed<P: PointsToSingleValue>(tracked p: P) -> (tracked out: Self)
        requires
            p.wf(),
        ensures
            out.provenance() == p.ptr()@.provenance,
            out.is_range(p.ptr()@.addr as int, P::size(p.ptr()@.metadata) as int),
            out.bytes_range(p.ptr()@.addr as int, P::size(p.ptr()@.metadata)) == p.bytes(),
    ;

    /// Replaces into_typed_seq<V>.
    pub proof fn into_typed_seq<T>(tracked self, start: usize, len: nat) -> (tracked out: SeqPointsTo<T, PointsTo<T>>)
        requires
            self.is_range(start as int, (len * size_of::<T>()) as int),
            len <= usize::MAX,
            PointsTo::<T>::satisfies_alignment(start),
            start != 0,
            len * size_of::<T>() == 0 ==> ptr_addr_in_bounds(ptr_mut_from_data::<T>(
                PtrData { addr: start, provenance: self.provenance(), metadata: () })),
        ensures
            out.thin_ptr() == ptr_mut_from_data::<T>(PtrData { addr: start, provenance: self.provenance(), metadata: () }),
            out.len() == len,
            out.bytes() == self.bytes_range(start as int, len * size_of::<T>()),
            out.is_fully_empty(),
            out.wf(),
    ;

    /// Replaces SeqPointsTo<V>::into_raw.
    pub proof fn from_typed_seq<T>(tracked s: SeqPointsTo<T, PointsTo<T>>) -> (tracked out: Self)
        requires
            s.wf(),
        ensures
            out.provenance() == s.ptr()@.provenance,
            out.is_range(s.ptr()@.addr as int, (s.len() * size_of::<T>()) as int),
            out.bytes_range(s.ptr()@.addr as int, s.len() * size_of::<T>()) == s.bytes(),
    ;
}

```

Trusted: `allocate`, `deallocate` (ported from `raw_ptr_old.rs`, without `Dealloc`; placement open)
and `global_alloc_id`.

```rust
/// The `AllocId` of allocations made by the global allocator.
/// Only `allocate` produces provenances with this id,
/// so no other allocation (e.g. a stack variable's) can be shown to have it.
pub uninterp spec fn global_alloc_id() -> AllocId;

/// Allocate with the global allocator.
/// The precondition should be consistent with the
/// [documented safety conditions on `alloc`](https://doc.rust-lang.org/alloc/alloc/trait.GlobalAlloc.html#tymethod.alloc).
/// Allocates exactly the requested size (`alloc_len == orig_size == size`),
/// a stronger guarantee than `Allocator::allocate`, which may allocate a larger block.
/// The byte contents are arbitrary (uninitialized).
#[cfg(feature = "std")]
#[verifier::external_body]
pub fn allocate(size: usize, align: usize) -> (pt: (*mut u8, Tracked<PointsToRaw>))
    requires
        valid_layout(size, align),
        size != 0,
    ensures
        pt.1@.provenance() is Some,
        pt.0@.provenance == pt.1@.provenance(),
        pt.0@.addr == pt.1@.provenance().unwrap().start_addr(),
        pt.1@.provenance().unwrap().alloc_len() == size,
        pt.1@.provenance().unwrap().orig_size() == size,
        pt.1@.provenance().unwrap().alignment() == align,
        pt.1@.provenance().unwrap().alloc_id() == global_alloc_id(),
        pt.1@.is_range(pt.0@.addr as int, size as int),
        // pt.0@.addr % align == 0 and pt.0@.addr + size <= usize::MAX follow from provenance_properties.
    opens_invariants none
{
    // SAFETY: valid_layout is a precondition
    let layout = unsafe { alloc::alloc::Layout::from_size_align_unchecked(size, align) };
    // SAFETY: size != 0
    let p = unsafe { ::alloc::alloc::alloc(layout) };
    if p == core::ptr::null_mut() {
        std::process::abort();
    }
    (p, Tracked::assume_new())
}

/// Deallocate with the global allocator.
/// The provenance gives the
/// [documented safety conditions on `dealloc`](https://doc.rust-lang.org/core/alloc/trait.GlobalAlloc.html#tymethod.dealloc)
/// (same allocator, same layout);
/// giving up the `PointsToRaw` for the whole allocation rules out use-after-free and double free.
#[cfg(feature = "alloc")]
#[verifier::external_body]
pub fn deallocate(p: *mut u8, size: usize, align: usize, Tracked(pt): Tracked<PointsToRaw>)
    requires
        pt.provenance() is Some,
        p@.provenance == pt.provenance(),
        pt.provenance().unwrap().alloc_id() == global_alloc_id(),
        p@.addr == pt.provenance().unwrap().start_addr(),
        size == pt.provenance().unwrap().orig_size(),
        align == pt.provenance().unwrap().alignment(),
        pt.is_range(p@.addr as int, pt.provenance().unwrap().alloc_len() as int),
    opens_invariants none
{
    // SAFETY: ensured by the provenance and the PointsToRaw
    let layout = unsafe { alloc::alloc::Layout::from_size_align_unchecked(size, align) };
    unsafe {
        ::alloc::alloc::dealloc(p, layout);
    }
}
```

### `str` (rustlib)

Signatures only; rustlib fixes the details.
rustlib writes `PointsToPhys` (`Metadata<str>` is the byte length; `size(len) = len`), `View`
and `PointsToSingleValue` for `PointsToUnaligned<str>`;
`PointsTo<str>` comes from the generic impls (alignment 1, from `layout_of_str`).

```rust
impl PointsToUnaligned<str> {
    /// The same bytes and metadata as a byte slice; the value becomes the string's bytes.
    pub proof fn into_bytes(tracked self) -> (tracked out: PointsToUnaligned<[u8]>)
        requires
            self.wf(),
        ensures
            out.ptr()@.addr == self.ptr()@.addr,
            out.ptr()@.provenance == self.ptr()@.provenance,
            out.ptr()@.metadata == self.ptr()@.metadata,
            out.bytes() == self.bytes(),
            out.typed_value().is_valid() == self.typed_value().is_valid(),
            self.typed_value().is_valid() ==> out.typed_value().value_ref()@ == self.typed_value().value_ref()@,
            out.wf(),
    ;

    /// Valid only if the value is valid UTF-8; otherwise empty.
    pub proof fn from_bytes(tracked p: PointsToUnaligned<[u8]>) -> (tracked out: PointsToUnaligned<str>)
        requires
            p.wf(),
        ensures
            out.ptr()@.addr == p.ptr()@.addr,
            out.ptr()@.provenance == p.ptr()@.provenance,
            out.ptr()@.metadata == p.ptr()@.metadata,
            out.bytes() == p.bytes(),
            out.typed_value().is_valid() <==> p.typed_value().is_valid() && valid_utf8(p.typed_value().value_ref()@),
            out.typed_value().is_valid() ==> out.typed_value().value_ref()@ == p.typed_value().value_ref()@,
            out.wf(),
    ;

    // as_bytes(&self) -> &PointsToUnaligned<[u8]>: as into_bytes
    //   (the value from str::as_bytes_tracked + TypedValue::valid_ref, then from_raw_parts_ref).
    // as_bytes_mut(&mut self) -> &mut PointsToUnaligned<[u8]>: initially as into_bytes; finally,
    //   if final(out).wf() and final(out).ptr() == out.ptr(), then final(self) is as from_bytes(final(out))
    //   (the value from TypedValue::<str>::as_bytes_mut, then M3).
    // PointsTo<str> versions: through the aligned/unaligned conversions (alignment 1).
}
```

In rustlib a `str`'s view `s@` is its bytes (`Seq<u8>`). The trusted pieces, all in rustlib:

```rust
// type_representation (rustlib): the str counterpart of abs_decode_slice
/// The bytes decode to a `str` exactly when its bytes are valid UTF-8
/// and each byte decodes to the corresponding `u8`
/// (so `abs_decode::<str>(b, s) <==> valid_utf8(s@) && abs_decode::<[u8]>(b, v)` for any `v` with `v@ == s@`,
/// by `abs_decode_slice` with `size_of::<u8>() == 1`).
pub broadcast axiom fn abs_decode_str(bytes: Seq<AbstractByte>, s: &str)
    ensures
        #[trigger] abs_decode::<str>(bytes, s) <==> {
            &&& valid_utf8(s@)
            &&& bytes.len() == s@.len()
            &&& forall|i: int|
                #![trigger s@[i]]
                0 <= i < s@.len() ==> abs_decode::<u8>(bytes.subrange(i, i + 1), &s@[i])
        },
;

impl TypedValue<str> {
    /// A mutably borrowed `str` typed value acts as a mutably borrowed byte-slice typed value.
    /// If the final bytes aren't valid UTF-8, the final `str` value is empty (the bytes are dropped).
    pub axiom fn as_bytes_mut<'a>(tracked &'a mut self) -> (tracked out: &'a mut TypedValue<[u8]>)
        ensures
            out.is_valid() == old(self).is_valid(),
            old(self).is_valid() ==> out.value()@ == old(self).value_ref()@,
            final(self).is_valid() <==> final(out).is_valid() && valid_utf8(final(out).value()@),
            final(self).is_valid() ==> final(self).value_ref()@ == final(out).value()@,
    ;
}
```

Not trusted: the shared `&TypedValue<str>` → `&TypedValue<[u8]>` cast
(from rustlib's existing `str::as_bytes_tracked` and `valid_ref`)
and both owned casts (from `as_bytes_mut` and `tracked_swap`).

The `str` reference helpers (trusted), moved from vstd's commented-out code:

```rust
impl<'a> SharedReference<'a, str> {
    pub axiom fn points_to(tracked self) -> (tracked pt: &'a PointsTo<str>)
        ensures
            pt.ptr() == self.ptr(),
            pt.is_valid(),
            pt.typed_value().value_ref() == self.value(),
    ;
}

pub axiom fn ptr_ref2_str_ghost<'a>(ptr: *const str, tracked perm: &PointsTo<str>) -> (tracked v: SharedReference<'a, str>)
    requires
        perm.ptr() == ptr,
        perm.is_valid(),
    ensures
        v.value() == perm.typed_value().value_ref(),
        v.ptr() == ptr,
;

#[verifier::external_body]
pub const fn ptr_ref_str(ptr: *const str, Tracked(perm): Tracked<&PointsTo<str>>) -> (v: &str)
    requires
        perm.ptr() == ptr,
        perm.is_valid(),
    ensures
        v == perm.typed_value().value_ref(),
    opens_invariants none
    no_unwind
{
    unsafe { &*ptr }
}

#[verifier::external_body]
pub const fn ptr_mut_ref_str(ptr: *mut str, Tracked(perm): Tracked<&mut PointsTo<str>>) -> (v: &mut str)
    requires
        old(perm).ptr() == ptr,
        old(perm).is_valid(),
    ensures
        final(perm).ptr() == ptr,
        final(perm).is_valid(),
        old(perm).typed_value().value_ref() == &*v,
        final(perm).typed_value().value_ref() == &*final(v),
    opens_invariants none
    no_unwind
{
    unsafe { &mut *ptr }
}

pub axiom fn mut_ref_to_shr_points_to_str<'a>(tracked mut_ref: &'a &'a mut str) -> (tracked pt: &'a PointsTo<str>)
    ensures
        pt.ptr() == mut_ref_ptr(*mut_ref),
        pt.is_valid(),
        pt.typed_value().value_ref() == &*old(*mut_ref),
        &*final(*mut_ref) == &*old(*mut_ref),
;
```

rustlib's existing `str` permission axioms (`as_str_ptr_verus`, `perm_init`, `perm_value_eq`, `perm_ptr`)
are temporary stand-ins until `PointsTo<str>` is ported;
they're replaced by the above and not part of this design.

## Inherent impls

What stays outside the traits, by impl block, after all phases.
"(new)" is added by this design; "(removed)" lists what moves into a trait;
everything else exists today.

| Impl block | Functions | Notes |
|---|---|---|
| `impl<T: ?Sized> TypedValue<T>` | `is_valid`, `is_empty`; `value_ref` (new); `valid_ref` (new, phase 3b) | |
| `impl<T> TypedValue<T>` | `value`, `tracked_copy` | Sized: by-value access |
| `impl<T> TypedValue<[T]>` | `value` (-> `&[T]`); `from_elems_mut`, `into_elems_mut` (new axioms M1/M2, phase 3b) | |
| `impl<T: ?Sized> PointsToUnaligned<T>` | closed accessors `typed_value`, `pt_untyped`, `metadata`; `bytes`, `is_valid`, `is_empty` (inline); `tracked_pt_untyped`; `from_raw_parts_ref` (new axiom, phase 3b), `from_raw_parts_mut` (new axiom M3, phase 3b) | The inherent `typed_value`/`bytes` coexist with the trait's (phase 0, item 5). |
| `impl<T: ?Sized> PointsToUnaligned<T> where PointsToUnaligned<T>: PointsToSingleValue<A = T>` | `into_aligned`, `as_aligned` (new, generic); `as_aligned_mut` (new, generic, phase 3b: needs M4) | Contracts in [Traits](#traits). |
| `impl<T> PointsToUnaligned<T>` | `value`; `is_disjoint_unaligned<S>`. (removed: `wf`, `stays_wf`, `zero_sized`) | |
| `impl<T> PointsToUnaligned<[T]>` | `from_untyped_ref`, `from_untyped_with_value_ref`, `as_seq_pt`, `as_seq_pt_mut` (new, phase 4; the primary implementations). (removed in 2b: inherent `wf`) | |
| `impl<T: ?Sized> PointsTo<T>` | closed `pt_unaligned`; `typed_value`, `metadata`, `bytes`, `is_valid`, `is_empty` (open, delegating); `tracked_pt_unaligned`; `from_unaligned_mut` (new axiom M4) | |
| `impl<T: ?Sized> PointsTo<T> where PointsToUnaligned<T>: PointsToSingleValue<A = T>` | `into_unaligned`, `as_unaligned`, `as_unaligned_mut` (new, generic) | Contracts in [Traits](#traits). |
| `impl<T> PointsTo<T>` | `value`, `is_aligned`, `is_disjoint_pointsto<S>`. (removed: `wf`, `stays_wf`, `lemma_ptrs_len_same_valid`, `zero_sized`, `bytes_decode`, the untyped conversions, the value operations) | Removed ones are `PointsToSingleValue` / `PointsToSingleValueSized` methods. |
| `impl<T> PointsTo<[T]>` | `from_untyped_ref`, `from_untyped_with_value_ref`, `as_seq_pt`, `as_seq_pt_mut` (new, phase 4; compositions over the `PointsToUnaligned` versions). (removed: inherent `wf`) | |
| `impl<T, P: PointsToProperties<A = T>> SeqPointsTo<T, P>` (`points_to.rs`) | `seq_pt`, `len`, `spec_index`, `thin_ptr`; `tracked_seq_pt`, `tracked_seq_pt_mut`, `index_mut`, `from_seq`, `empty`, `into_seq` (moved here in phase 1); `split_basic`, `join_basic`, `subrange_basic` (new); `from_refs` (new), `from_seq_mut` (new axiom M5) | Structural; stated with `wf_basic`. The only code touching the fields. |
| `impl<T, P: PointsToSingleValueSized<A = T>> SeqPointsTo<T, P>` | `View` (generalized; `SeqPointsToData<T, P>`); `wf`, `bytes`, `bytes_inner`, `seq_typed_value`, `is_valid`, `is_empty`, `is_fully_empty`, `seq_value`, `is_valid_subrange`, `value_subrange`, `ptrs_len_same_valid`, `stays_wf`, `lemma_ptrs_len_same_valid`, `typed_value_equiv`, the byte lemmas, `split`, `join`, `subrange`, `subrange_mut` (proved in phase 3b), `zero_sized`, the untyped conversions, the value operations, `is_disjoint_seqpt` | Moved from `impl<T> SeqPointsTo<T, PointsTo<T>>` in phase 3. |
| `impl<T> SeqPointsTo<T, PointsTo<T>>` | `is_aligned`; `from_untyped_ref`, `from_untyped_with_value_ref`, `as_slice_pt`, `as_slice_pt_mut` (new, phase 4; compositions); `into_unaligned`, `as_unaligned`, `as_unaligned_mut` (new, phase 4) | |
| `impl<T> SeqPointsTo<T, PointsToUnaligned<T>>` | `into_aligned`, `as_aligned`, `as_aligned_mut`, `from_untyped_ref`, `from_untyped_with_value_ref`, `as_slice_pt`, `as_slice_pt_mut` (new, phase 4; the primary implementations) | |
| `impl SeqPointsTo<u8, PointsToByte>` (`PointsToUntyped`, `points_to.rs`) | `View`, `bytes`, `wf`, `stays_wf`, `lemma_ptrs_len_same_untyped` (renamed), `zero_sized<T>`, `split`, `split_ref`, `join` (wrappers over the `_basic` primitives); `join_ref`, `join_mut`, `split_mut` (proved in phase 3b); `is_disjoint_untyped` | |
| `impl PointsToByte` (renamed from `PointsToSingleton`) | `byte`, `is_disjoint_singleton` | |
| `impl PointsToRaw` | everything in [`PointsToRaw` (phase 2c)](#pointstoraw-phase-2c) above (new) | Not a `PointsToPhys`. |
| free functions | `tracked_slice_index`, `tracked_slice_from_refs`, `tracked_collect_perm_refs`, `tracked_collect_perm_muts` (M6), `tracked_ref` (new axioms, phase 3b); `allocate`, `deallocate` (ported, phase 2c; placement open; `Dealloc` dropped) | |
| rustlib: `impl PointsToUnaligned<str>` | `into_bytes`, `from_bytes`, `as_bytes`, `as_bytes_mut` | |

## Trusted surface

Every trusted item the permissions rely on, after all phases:
`axiom fn`s, `external_body` functions and types, `assume_specification`s,
and `uninterp` specs that axioms constrain.
"Uses" names the main dependents.

**Existing, unchanged.**

| Item | File | What it states | Uses |
|---|---|---|---|
| `PointsToByte` (`external_body` struct; `uninterp` `ptr`, `byte`) | `points_to.rs` | A permission to one byte, with its address and abstract byte. | everything byte-level |
| `PointsToByte`'s `is_nonnull`, `ptr_bounds`, `provenance_not_none`, `is_disjoint` | `points_to.rs` | A byte permission's pointer is non-null, within its allocation, has non-null provenance; two byte permissions are at different addresses. | `PointsToUntyped`'s and `PointsToRaw`'s pointer-level lemmas |
| `ProvenanceData` (`external_body`; `uninterp` `start_addr`, `alloc_len`, `alignment`, `orig_size`, `alloc_id`), `provenance_properties` | `raw_ptr_new.rs` | The allocation model. `orig_size` replaces `Dealloc`'s size tracking. | pointer bounds, `allocate` / `deallocate` |
| pointer model: `View for *mut T` (`uninterp`), `ptr_mut_from_data` (`uninterp`), `axiom_ptr_mut_from_data`, `ptrs_mut_eq`, `tracked_ptr_mut_from_data` | `raw_ptr_new.rs` | A pointer is its `PtrData` (address, provenance, metadata). | every pointer spec (e.g. the generic `PointsToUnaligned` pointer built from its metadata) |
| `assume_specification`s for pointer `==`, `null`, `null_mut`, `addr`, `with_addr`; the `cast_*` `external_body` functions | `raw_ptr_new.rs` | The exec pointer operations match the model. | exec code |
| `ptr_ref`, `ptr_mut_ref` (`external_body`) | `raw_ptr_new.rs` | Dereferencing a pointer with a valid `PointsTo<T>` gives its value (`&` / `&mut`). | exec reads and writes |
| `SharedReference` (`external_body`; `uninterp` `value`, `ptr`), `SharedReference::points_to`, `ptr_nonnull`, `ptr_ref2`, `ptr_ref2_ghost`, `axiom_shared_ref_value_view` | `shared_reference.rs` | A shared reference with its pointer; it gives a valid `PointsTo<T>` and back. | exec code; the source of valid shared permissions |
| `shared_ref_ptr` (`uninterp`), `mut_ref_slice_len`, `ptr_mut_ref_join`, `mut_ref_to_shr_points_to`, `tracked_mut_ref_slice_subrange`, `tracked_mut_ref_slice_idx`, `cast_mut_ref_to_ptr`, `cast_mut_ref_slice_to_ptr`, `cast_mut_ref_str_to_ptr` | `raw_ptr_new.rs` | Reference ↔ pointer and permission boundary. | exec code; the source of valid permissions |
| `abs_encode`, `abs_decode`, `abs_can_be_encoded` (`uninterp`); `encode_decode_len`, `encode_decode_inverse`, `shared_ref_cannot_be_encoded`; the per-type encoding impls | `type_representation.rs` | The abstract-byte encoding of values. | every decode clause |
| layout axioms (`layout_of_sized`, `layout_of_slices`, `layout_of_str`, `layout_of_unit_tuple`, `align_properties`, …) | `layout.rs` | Sizes and alignments of types and values. | sizes, `satisfies_alignment`, `lemma_satisfies_alignment_offset`, the `zero_sized` default |
| `tracked_swap`, `tracked_static_mut_ref` | `modes.rs` | Swapping tracked values; a `'static` borrow of an owned value. | `take_typed_value`, empty cases of borrowed conversions |
| `Seq` tracked operations (`tracked_borrow`, `tracked_borrow_subrange`, `tracked_borrow_subrange_mut`, `tracked_split_borrow_mut`, …) | `seq.rs` | Borrowing parts of a tracked `Seq`. | `subrange_basic`, `split_ref`, `as_untyped_mut` |
| `Map` tracked operations (`tracked_empty`, `tracked_remove_keys`, `tracked_union_prefer_right`, …) | `map.rs` | Building and splitting a tracked `Map`. | `PointsToRaw` |
| `shr_ref_struct_wrap` | builtin | Borrowing a struct from a borrow of its only tracked field. | `as_aligned`, `subrange_basic`, `split_ref`, `from_refs` |

**Existing, removed (become proofs).**

| Item | File | Proved from |
|---|---|---|
| `PointsToUntyped::join_ref` | `points_to_permissions.rs` today (`points_to.rs` after the move) | `tracked_collect_perm_refs` (via `from_refs`), phase 3b |
| `PointsToUntyped::join_mut` | same | M5 + M6, phase 3b |
| `SeqPointsTo::subrange_mut` (on `SeqPointsTo<T, PointsTo<T>>`) | `points_to_permissions.rs` | M5, phase 3b; the proof is in the typed generic impl, so it covers every typed sequence |
| `PointsToRaw`'s axioms (`empty`, `split`, `join`, `ptr_bounds`, `provenance_non_null`, `is_disjoint`, `into_typed*`, `into_raw`) | `raw_ptr_old.rs` (not in the current vstd) | `PointsToByte`'s axioms and `Map`'s tracked operations |

**New in vstd.**

| Item | Planned file | What it states | Uses |
|---|---|---|---|
| `abs_decode_slice` (already added) | `type_representation.rs` | A slice decodes exactly when each element's slot does. | slice `wf` |
| `tracked_slice_index` | `slice.rs` | Borrows an element of a borrowed slice. | shared slice → sequence |
| `tracked_slice_from_refs` | `slice.rs` | Borrowed elements act as one borrowed slice. | shared sequence → slice |
| `tracked_ref` | `modes.rs` | A borrow is a borrowed `Tracked` of itself. | `TypedValue::valid_ref` |
| `PointsToUnaligned::from_raw_parts_ref` | with `PointsToUnaligned` (placement open) | Borrowed bytes and typed value act as one borrowed permission. | borrowed constructors, slice ↔ sequence, `str` ↔ `[u8]` |
| `tracked_collect_perm_refs` | with `SeqPointsTo` (placement open) | Borrowed permissions act as one borrowed `Seq`. | `from_refs`, `join_ref` |
| M1 `TypedValue::<[T]>::from_elems_mut`, M2 `into_elems_mut` | with `TypedValue` (placement open) | Per-element `&mut` typed values ↔ one `&mut` slice typed value. | `&mut` slice ↔ sequence |
| M3 `PointsToUnaligned::from_raw_parts_mut` | with `PointsToUnaligned` (placement open) | `&mut` bytes and typed value act as one `&mut` permission. | `&mut` conversions |
| M4 `PointsTo::from_unaligned_mut` | with `PointsTo` (placement open) | A `&mut PointsToUnaligned` acts as a `&mut PointsTo`. | `as_aligned_mut`, aligned `&mut` conversions |
| M5 `SeqPointsTo::from_seq_mut` | with `SeqPointsTo` (placement open) | A `&mut Seq<P>` acts as a `&mut SeqPointsTo`. | `subrange_mut`, `join_mut`, `&mut` conversions |
| M6 `tracked_collect_perm_muts` | with `SeqPointsTo` (placement open) | `&mut` permissions act as one `&mut Seq`. | `join_mut`, `&mut` conversions |
| `SharedReference<[T]>::points_to`, `ptr_ref2_slice_ghost` | `shared_reference.rs` (restored) | A shared slice reference gives a valid `PointsTo<[T]>`, and back. | sources of valid slice permissions (phase 4b) |
| `ptr_ref_slice`, `ptr_mut_ref_slice` (`external_body`), `mut_ref_to_shr_points_to_slice` | `raw_ptr_new.rs` (restored) | Dereferencing a pointer with a valid `PointsTo<[T]>`; a `&&mut [T]` gives a shared `PointsTo<[T]>`. | exec slice reads and writes (phase 4b) |
| `global_alloc_id` (`uninterp`) | with `allocate` (placement open) | The id of the global allocator's allocations. | `allocate` / `deallocate` |
| `allocate`, `deallocate` (`external_body`) | open | Allocation gives a `PointsToRaw` for the new range with a global-allocator provenance; deallocation consumes one covering the whole allocation. | heap allocation |

Full definitions: [Borrowed-assembly axioms](#borrowed-assembly-axioms-phase-3b) and the structural `SeqPointsTo` impl (M5),
[Slice reference helpers](#slice-reference-helpers-phase-4b), and [`PointsToRaw`](#pointstoraw-phase-2c) (`allocate` / `deallocate`).

**New in rustlib.** Full definitions in [`str` (rustlib)](#str-rustlib).

| Item | What it states | Uses |
|---|---|---|
| `abs_decode_str` | A `str` decodes exactly when its bytes are valid UTF-8 and each decodes as a `u8`. | `str` `wf`, `str` ↔ `[u8]` |
| `TypedValue::<str>::as_bytes_mut` | A `&mut` `str` typed value acts as a `&mut` byte-slice typed value; non-UTF-8 final bytes leave the `str` empty. | `as_bytes_mut`; the owned casts (`into_bytes`, `from_bytes`) |
| `SharedReference<str>::points_to`, `ptr_ref2_str_ghost`, `ptr_ref_str`, `ptr_mut_ref_str`, `mut_ref_to_shr_points_to_str` | The `str` versions of the reference helpers (moved from vstd's commented-out code). | exec `str` code |

Existing rustlib axioms the `str` conversions use: `str::as_bytes_tracked` (for the shared cast).

**Dependency direction (for the module split).**
Trusted code already depends on verified code in one place:
`ptr_ref`, `ptr_mut_ref` and `mut_ref_to_shr_points_to` in `raw_ptr_new.rs` take or produce `PointsTo<T>`,
and the restored slice versions would produce `PointsTo<[T]>`.
`allocate` / `deallocate` would add `PointsToRaw`.
The phase 3b axioms are stated on the verified types (`PointsToUnaligned`, `PointsTo`, `SeqPointsTo`, `TypedValue`),
though they only use their (closed) specs, not their fields.

**Not trusted.**

- No axiom turns an owned `SeqPointsTo<T, PointsTo<T>>` into an owned `PointsTo<[T]>`.
- No new axiom mentions `wf()`, alignment or decoding, except `abs_decode_slice` and `abs_decode_str`.
- Proved: `TypedValue::valid_ref`, `SeqPointsTo::from_refs`, the borrowed constructors,
  all four slice ↔ sequence conversions (`as_slice_pt`, `as_seq_pt`, `as_slice_pt_mut`, `as_seq_pt_mut`),
  `borrow` for slices, and the empty slice functions.
- Not needed at all: `PointsTo::borrow_mut`, `borrow_mut_subrange`, the reverted generic `wrap_mut`,
  and any `&mut [T]` / `&mut T` slice axioms.

**Review notes.**

- **Duplicate references.** `tracked_slice_from_refs` and `tracked_collect_perm_refs`
  can be given the same reference more than once,
  producing a borrowed slice or `Seq` with repeated elements.
  This is harmless: a shared reference never guarantees uniqueness
  (several `&PointsTo<T>` to one permission can already exist),
  so distinctness is only derived through `&mut`,
  which is why `is_disjoint` takes `&mut` even though it doesn't modify anything.
  All disjointness lemmas on points-to permissions require `&mut`,
  so none can conclude distinctness from the collected shared borrow.
  M6 can't receive duplicates at all: a `Seq<&mut P>` can't hold the same mutable borrow twice.
- **The `&mut` axioms (M1–M6)** are accepted.
  Like `join_mut`, each hands out a `&mut` to something that isn't stored.
  Each is sound because every final state of the result maps to a consistent final state of the borrowed parts
  without duplicating a tracked value:
  M1/M2 drop values rather than duplicate them when the final state can't be distributed,
  and M6's finals are only tied when the length is unchanged.
- **The reference helpers don't state `wf()`.**
  The existing Sized ones (`SharedReference::points_to`, `mut_ref_to_shr_points_to`, `ptr_mut_ref`)
  give a valid permission with the right pointer and value, but say nothing about its bytes or alignment,
  and `ptr_mut_ref` says nothing about the final bytes.
  The restored slice and `str` versions copy that.
  A real reference does satisfy `wf()` (aligned, bytes decode to the value),
  so `pt.wf()` / `final(perm).wf()` could be added to all of them together; to decide when reviewing.
- **`global_alloc_id`.** It replaces what `Dealloc` guaranteed implicitly:
  that the memory being freed came from the global allocator.
  Only `allocate` ensures a provenance has this id,
  so a `PointsToRaw` covering a stack variable's whole allocation can't be passed to `deallocate`.
