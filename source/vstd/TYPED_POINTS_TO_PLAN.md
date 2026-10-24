# Design: `PTValueOps` trait and typed `SeqPointsTo` (level 3)

The specifications and trusted code to review:
a `PTValueOps` trait implemented by `PointsTo` and `PointsToUnaligned` (for `T`, `[T]`, and `str` in rustlib),
the typed `SeqPointsTo<T, PointsTo<T>>` impl,
the sequence → slice conversions and slice indexing,
and every new trusted item in vstd and rustlib.

Approved designs and specs are in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md).
The rationale, background and decisions are in [TYPED_POINTS_TO_NOTES.md](TYPED_POINTS_TO_NOTES.md);
the phases, spike results and risks in [TYPED_POINTS_TO_IMPL_PLAN.md](TYPED_POINTS_TO_IMPL_PLAN.md)
("phase N" below points there).

## Overview

The permission types table, the trait impls table, the written once vs per type tables, the conversions table,
the API changes not visible in the specs, the existing (unchanged) trusted specs, the five trait definitions,
the module layout, and all of `points_to_model.rs`'s impl blocks are approved
and are in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md).

## Specifications

Every module is written out item by item, with its documentation and contract.
Approved axioms are named in a comment, not repeated; their code is in TYPED_POINTS_TO_APPROVED.md.
Spec fn bodies are written out; proof bodies are omitted.
Trait impl methods don't restate their contracts, which are the trait's
([Trait definitions](TYPED_POINTS_TO_APPROVED.md#trait-definitions)).

Grouped by module ([layout](TYPED_POINTS_TO_APPROVED.md#module-layout)), from low-level to high-level permissions.
An impl block with both spec fns and proofs is split as in the layout:
`points_to_model.rs` holds the closed accessors,
and every spec fn that an axiom depends on
(directly or through the spec fns it unfolds to).
Other open spec fns, such as `len`, may live with the proofs that use them.
The trait definitions are in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#trait-definitions).

### `points_to_model.rs` (trusted)

The five trait definitions, with their default bodies, are approved
([TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#trait-definitions)).
The lemma groups (`group_points_to_lemmas`, `group_points_to_collections_lemmas`) are in
[Module layout](TYPED_POINTS_TO_APPROVED.md#module-layout).

All of `points_to_model.rs`'s impl blocks
(`PointsToByte`, `SeqPointsTo` / `PointsToUntyped`, `TypedValue`, `PointsToUnaligned` and `PointsTo`) are approved
([Impls](TYPED_POINTS_TO_APPROVED.md#impls)).

### `points_to_ops.rs` (trusted)

A child module of `points_to_model.rs`, so it can use the structs' private fields
([phase 0, item 15](TYPED_POINTS_TO_IMPL_PLAN.md#phase-0-pending-checks)).

#### `SeqPointsTo` and `PointsToUntyped`: proofs (phase 1b)

`SeqPointsTo`'s `PTProperties` impl, the structural `impl<T, P: PTProperties<A = T>> SeqPointsTo<T, P>`,
and the `impl PointsToUntyped` proofs are approved
([`points_to_ops.rs`: `SeqPointsTo`](TYPED_POINTS_TO_APPROVED.md#points_to_opsrs-seqpointstos-ptproperties-and-structural-operations-phase-1b),
[`points_to_ops.rs`: `PointsToUntyped`](TYPED_POINTS_TO_APPROVED.md#points_to_opsrs-pointstountypeds-proofs-phase-1b)).

#### `PointsToUnaligned`: proofs

`PointsToUnaligned`'s `PTProperties`, `PTValueOps` and `PTSizedValue` impls and `is_disjoint_unaligned` are approved
([`points_to_ops.rs`: `PointsToUnaligned`](TYPED_POINTS_TO_APPROVED.md#points_to_opsrs-pointstounaligneds-proofs)),
and so are the field primitives `tracked_typed_value`, `into_raw_parts`, `from_raw_parts` and `as_raw_parts_mut`
([`PointsToUnaligned`: specs](TYPED_POINTS_TO_APPROVED.md#pointstounaligned-specs-phases-2-2b-str-in-rustlib)).

#### `PointsTo`: proofs and aligned/unaligned conversions

Approved ([`points_to_ops.rs`: `PointsTo`](TYPED_POINTS_TO_APPROVED.md#points_to_opsrs-pointstos-proofs-and-the-alignedunaligned-conversions)).

#### Slices: indexing and borrowed constructors (phase 4)

Approved ([`points_to_ops.rs`: slices](TYPED_POINTS_TO_APPROVED.md#points_to_opsrs-slice-indexing-and-borrowed-constructors-phase-4)).
They need no new axioms:
for `borrow_index`, the bytes come from `split_ref` on the untyped permission,
a valid element's typed value from `tracked_slice_index` and `TypedValue::valid_ref`
(an empty one from `&TypedValue::Empty`, a promoted constant),
and the permission from `from_raw_parts_ref`.

### `points_to_collections.rs` (verified)

#### `PointsToRaw` (phase 2c)

```rust
/// Variable-sized uninitialized memory.
///
/// Permission is for an arbitrary set of addresses, not necessarily contiguous,
/// and with a given provenance.
/// Internally represented as a map from addresses to `PointsToByte` permissions.
/// Not a `PTPhys`, since it has no single pointer.
// Note reading from uninitialized memory is UB, so we shouldn't give any
// reading capabilities to PointsToRaw. Turning a PointsToRaw into a PointsTo
// should always leave it as 'uninitialized'.
pub tracked struct PointsToRaw {
    bytes: Map<int, PointsToByte>,
    provenance: Ghost<Provenance>,
}

impl PointsToRaw {
    /// The domain is finite, and each byte permission is at its key's address,
    /// with this permission's provenance, which is non-null and contains that address.
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

    /// Provenance of the `PointsToRaw` permission;
    /// this corresponds to the original allocation and does not change.
    pub closed spec fn provenance(self) -> Provenance {
        self.provenance@
    }

    /// Memory addresses (domain) that the `PointsToRaw` permission gives access to.
    /// This set may be split apart and/or recombined, in order to create permissions to smaller pieces of the allocation.
    pub closed spec fn dom(self) -> Set<int> {
        self.bytes.dom()
    }

    /// The abstract byte at `a` (new: the old PointsToRaw had no contents).
    pub closed spec fn byte(self, a: int) -> AbstractByte
        recommends
            self.dom().contains(a),
    {
        self.bytes[a].byte()
    }

    /// Returns `true` if the domain of this permission is exactly the range `[start, start + len)`.
    pub open spec fn is_range(self, start: int, len: int) -> bool {
        set_int_range(start, start + len) =~= self.dom()
    }

    /// Returns `true` if the domain of this permission contains the range `[start, start + len)`.
    pub open spec fn contains_range(self, start: int, len: int) -> bool {
        set_int_range(start, start + len) <= self.dom()
    }

    /// The contents of `[start, start + len)` as a sequence.
    pub open spec fn bytes_range(self, start: int, len: nat) -> Seq<AbstractByte> {
        Seq::new(len, |i: int| self.byte(start + i))
    }

    /// Constructs a `PointsToRaw` permission over an empty domain with the given provenance.
    pub proof fn empty(provenance: Provenance) -> (tracked out: Self)
        ensures
            out.dom() == Set::<int>::empty(),
            out.provenance() == provenance,
    ;

    /// Splits the current `PointsToRaw` permission into a permission with domain `range`
    /// and a permission containing the rest of the domain,
    /// provided that `range` is contained in the domain of the current permission.
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

    /// Joins two `PointsToRaw` permissions into one,
    /// provided that they have the same provenance.
    /// The memory addresses of the new permission is the union of the domains of `self` and `other`.
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

    /// The memory associated with a pointer should always be within bounds of its spatial provenance.
    /// Stronger than the old axiom (`<` instead of `<=` at the end).
    pub proof fn ptr_bounds(tracked &self)
        requires
            self.provenance().is_some(),
        ensures
            forall|a| self.dom().contains(a) ==> self.provenance().start_addr() <= a
                < self.provenance().start_addr() + self.provenance().alloc_len(),
    ;

    /// If the address domain is non-empty, then the provenance is non-null.
    /// <https://doc.rust-lang.org/std/ptr/index.html#provenance>
    /// Renamed from `provenance_non_null`, matching `PTProperties::provenance_not_none`.
    pub proof fn provenance_not_none(tracked &self)
        requires
            self.dom() != Set::<int>::empty(),
        ensures
            self.provenance() != Provenance::None,
    ;

    /// Guarantees that the memory ranges associated with two distinct, non-empty permissions will not overlap,
    /// since you cannot have two permissions to the same memory.
    /// (`self` is an &mut reference to enforce distinctness,
    /// so you cannot pass the same PointsToRaw as both arguments.)
    pub proof fn is_disjoint(tracked &mut self, tracked other: &PointsToRaw)
        requires
            self.dom() != Set::<int>::empty(),
            other.dom() != Set::<int>::empty(),
        ensures
            *old(self) == *final(self),
            final(self).dom().intersect(other.dom()).is_empty(),
    ;

    /// Converts a `PointsToUntyped` into a `PointsToRaw` holding the same bytes.
    pub proof fn from_untyped(tracked pt_untyped: PointsToUntyped) -> (tracked out: Self)
        requires
            pt_untyped.wf(),
        ensures
            out.provenance() == pt_untyped.ptr()@.provenance,
            out.is_range(pt_untyped.ptr()@.addr as int, pt_untyped.len() as int),
            out.bytes_range(pt_untyped.ptr()@.addr as int, pt_untyped.len()) == pt_untyped.bytes(),
    ;

    /// Converts a `PointsToRaw` holding exactly the bytes in `[start, start + len)`
    /// into a `PointsToUntyped` for that range.
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
}
```

Typed permissions convert through `PointsToUntyped`:
`into_untyped` followed by `PTValueOps::from_untyped` / `SeqPointsTo::from_untyped`, and back.

#### Typed `SeqPointsTo` (phase 1b)

`from_seq`, `empty`, `into_seq`, `tracked_seq_pt(_mut)` and `index_mut` have no typed versions.

```rust
/// The interface for a `SeqPointsTo<T, PointsTo<T>>` permission,
/// which represents permission to access a contiguous sequence of memory locations,
/// each aligned to `T` and possibly holding a valid value of type `T`.
/// We track the pointer to the start of that memory, along with the
/// `PointsTo<T>` permission for each element.
#[cfg(verus_keep_ghost)]
pub ghost struct SeqPointsToData<T> {
    pub ptr: *mut T,
    pub seq_pt: Seq<PointsTo<T>>,
}

#[cfg(verus_keep_ghost)]
impl<T> View for SeqPointsTo<T, PointsTo<T>> {
    type V = SeqPointsToData<T>;

    open spec fn view(&self) -> Self::V {
        SeqPointsToData { ptr: self.thin_ptr(), seq_pt: self.seq_pt() }
    }
}

// The only typed sequence impl (there is no generic typed impl).
impl<T> SeqPointsTo<T, PointsTo<T>> {
    /// The pointer to the first element, without the length.
    pub open spec fn thin_ptr(self) -> *mut T {
        self.ptr() as *mut T
    }

    /// In addition to the well-formed-ness properties which must hold of every `SeqPointsTo` (`wf_basic`),
    /// the pointer must be aligned to `T`, and each element must be well-formed.
    pub open spec fn wf(self) -> bool {
        &&& self.wf_basic()
        &&& PointsTo::<T>::satisfies_alignment(self.ptr()@.addr)
        &&& forall|i| 0 <= i < self.len() ==> #[trigger] self[i].wf()
    }

    /// A "flattened" view of the abstract bytes.
    /// Because the abstract bytes do not change across casting/transmuting, it is often more
    /// convenient to have a single flattened view of the bytes that is the same as for `PointsTo<[T]>`.
    pub open spec fn bytes(self) -> Seq<AbstractByte> {
        Self::bytes_inner(self.seq_pt())
    }

    /// The concatenation of the abstract bytes of each permission in `perms`.
    pub open spec fn bytes_inner(perms: Seq<PointsTo<T>>) -> Seq<AbstractByte> {
        perms.fold_left(Seq::empty(), |acc: Seq<AbstractByte>, elt: PointsTo<T>| acc + elt.bytes())
    }

    /// The (possibly-valid) typed value of each element, as a sequence.
    pub open spec fn seq_typed_value(self) -> Seq<TypedValue<T>> {
        self.seq_pt().map(|i: int, pt: PointsTo<T>| pt.typed_value())
    }

    /// Returns `true` if all of the permission's associated memory is valid for the type `T`.
    #[verifier::inline]
    pub open spec fn is_valid(&self) -> bool {
        forall|i| 0 <= i < self.len() ==> #[trigger] self[i].is_valid()
    }

    /// Returns `true` if any part of the permission's associated memory is not valid for the type `T`.
    #[verifier::inline]
    pub open spec fn is_empty(&self) -> bool {
        !self.is_valid()
    }

    /// Returns `true` if all of the permission's associated memory is not valid for the type `T`.
    #[verifier::inline]
    pub open spec fn is_fully_empty(&self) -> bool {
        forall|i| 0 <= i < self.len() ==> #[trigger] self[i].is_empty()
    }

    /// Given that all of the permission's associated memory is initialized,
    /// returns the underlying values as a sequence.
    #[verifier::inline]
    pub open spec fn seq_value(&self) -> Seq<T>
        recommends
            self.is_valid(),
    {
        Seq::new(self.len(), |i| self[i].value())
    }

    /// Returns `true` if all of the permission's associated memory in the given subrange is valid for the type `T`.
    #[verifier::inline]
    pub open spec fn is_valid_subrange(&self, start_index: int, len: nat) -> bool {
        &&& 0 <= start_index <= start_index + len <= self.len()
        &&& forall|i: int| start_index <= i < start_index + len ==> #[trigger] self[i].is_valid()
    }

    /// Given that the subrange is valid, returns the underlying values in that subrange as a sequence.
    #[verifier::inline]
    pub open spec fn value_subrange(&self, start_index: int, len: nat) -> Seq<T>
        recommends
            self.is_valid_subrange(start_index, len),
    {
        Seq::new(len, |i: int| self[start_index + i].value())
    }

    /// The pointer-level `ptrs_len_same`, plus each element's `PTTypedValue::ptrs_len_same_valid`.
    /// Used by `stays_wf`.
    pub open spec fn ptrs_len_same_valid(old: Self, new: Self) -> bool {
        &&& Self::ptrs_len_same(old, new)
        &&& forall|i| 0 <= i < new.len() ==> PointsTo::<T>::ptrs_len_same_valid(old[i], #[trigger] new[i])
    }

    /// If `old` is well-formed and `new` has the same pointers and length, with each element
    /// still satisfying decode validity (`ptrs_len_same_valid`), then `new` is well-formed.
    pub proof fn stays_wf(old: Self, new: Self)
        requires
            old.wf(),
            Self::ptrs_len_same_valid(old, new),
        ensures
            new.wf(),
    ;

    /// If `old` and `new` are both well-formed with the same pointer, then each element
    /// of `new` keeps the corresponding element of `old`'s pointers and length, and still
    /// satisfies decode validity.
    /// Same pointer means same length (the pointer carries it), so no separate length condition.
    pub broadcast proof fn lemma_ptrs_len_same_valid(old: Self, new: Self)
        requires
            old.wf(),
            new.wf(),
            new.ptr() == old.ptr(),
        ensures
            #[trigger] Self::ptrs_len_same_valid(old, new),
    ;

    /// A `SeqPointsTo<T, PointsTo<T>>` is always aligned to `T`.
    pub proof fn is_aligned(tracked &self)
        requires
            self.wf(),
        ensures
            self.ptr()@.addr as nat % align_of::<T>() == 0,
    ;

    /// Proof of equivalence for two different ways to get the `TypedValue<T>` at a given index `i`.
    pub broadcast proof fn typed_value_equiv(self, i: int)
        requires
            0 <= i < self.len(),
        ensures
            #![trigger self.seq_typed_value()[i]]
            #![trigger self.seq_pt()[i]]
            self.seq_typed_value()[i] == self.seq_pt()[i].typed_value(),
    ;

    /// We can construct a `SeqPointsTo` with `length`-many `PointsTo` permissions,
    /// provided that `T` is zero-sized and that the pointer is non-null and aligned.
    pub proof fn zero_sized(ptr: *mut T, length: nat) -> (tracked out: Self)
        requires
            ptr@.addr != 0,
            PointsTo::<T>::satisfies_alignment(ptr@.addr),
            ptr_addr_in_bounds(ptr),
            size_of::<T>() == 0,
            length <= usize::MAX,    // new
        ensures
            forall|i| 0 <= i < out.len() ==> (#[trigger] out[i]).is_empty(),
            out.thin_ptr() == ptr,
            out.len() == length,
            out.wf(),
    ;

    /// The length of the abstract bytes matches the size of this type multiplied by the number of elements this permission represents.
    pub broadcast proof fn bytes_len(&self)
        requires
            self.wf(),
        ensures
            #[trigger] self.bytes().len() == self.len() * size_of::<T>(),
    ;

    /// The abstract bytes of an individual permission in a sequence corresponds to a subrange of length `size_of::<T>()`
    /// from the entire abstract bytes.
    pub broadcast proof fn bytes_equiv(&self, i: int)
        requires
            self.wf(),
            0 <= i < self.len(),
        ensures
            #[trigger] self.seq_pt()[i].bytes() == self.bytes().subrange(
                i * size_of::<T>(),
                (i + 1) * size_of::<T>(),
            ),
    ;

    /// If `sub` holds the permissions in `[start, end)` of `self`,
    /// then its abstract bytes are the subrange `[start * size_of::<T>(), end * size_of::<T>())`
    /// of `self`'s abstract bytes.
    pub proof fn bytes_subrange_equiv(&self, sub: Self, start: int, end: int)
        requires
            self.wf(),
            0 <= start <= end <= self.len(),
            sub.seq_pt() == self.seq_pt().subrange(start, end),
        ensures
            sub.bytes() == self.bytes().subrange(start * size_of::<T>(), end * size_of::<T>()),
    ;

    /// For all positions in this sequence,
    /// the abstract bytes for that position can be decoded into the value in memory at that position.
    pub proof fn bytes_decode(&self)
        requires
            self.wf(),
        ensures
            forall|i: int|
                0 <= i < self.len() ==> {
                    &&& (#[trigger] self.seq_typed_value()[i]).is_valid() ==> abs_decode::<T>(
                        self.bytes().subrange(i * size_of::<T>(), (i + 1) * size_of::<T>()),
                        &self.seq_typed_value()[i].value(),
                    )
                    &&& self.seq_pt()[i].bytes().len() == size_of::<T>()
                },
    ;

    /// Converts a `SeqPointsTo<T, PointsTo<T>>` into a `PointsToUntyped` covering the same bytes,
    /// together with the `TypedValue<T>` of each element.
    /// (Use `into_untyped` instead if you don't need the typed values.)
    ///
    /// The resulting `PointsToUntyped` has the same address and provenance
    /// and a length of `self.len() * size_of::<T>()`,
    /// and preserves the abstract bytes.
    /// The returned `tracked typed_value` holds the typed contents from this memory,
    /// which can later be used to convert the `pt_untyped` permission back to a typed permission
    /// (see `SeqPointsTo::from_untyped_with_typed_value`).
    pub proof fn into_untyped_with_typed_value(tracked self) -> (tracked (pt_untyped, typed_value): (
        PointsToUntyped,
        Seq<TypedValue<T>>,
    ))
        requires
            self.wf(),
        ensures
            pt_untyped.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: self.ptr()@.addr,
                    provenance: self.ptr()@.provenance,
                    metadata: (self.len() * size_of::<T>()) as usize,
                },
            ),
            pt_untyped.bytes() == self.bytes(),
            typed_value == self.seq_typed_value(),
            pt_untyped.wf(),
    ;

    /// Creates a `PointsToUntyped` from a `SeqPointsTo<T, PointsTo<T>>`
    /// with the same address and provenance
    /// and a length of `self.len() * size_of::<T>()`.
    /// If there are any typed values stored in memory, they are dropped here.
    /// (Use `into_untyped_with_typed_value` instead if you want to keep them.)
    pub proof fn into_untyped(tracked self) -> (tracked pt_untyped: PointsToUntyped)
        requires
            self.wf(),
        ensures
            pt_untyped.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: self.ptr()@.addr,
                    provenance: self.ptr()@.provenance,
                    metadata: (self.len() * size_of::<T>()) as usize,
                },
            ),
            pt_untyped.bytes() == self.bytes(),
            pt_untyped.wf(),
    ;

    /// Splits the `SeqPointsTo` into two permissions at the index boundary `mid`.
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
            first.ptr() == ptr_mut_from_data::<[T]>(PtrData {
                addr: self.ptr()@.addr,
                provenance: self.ptr()@.provenance,
                metadata: mid as usize,
            }),
            second.ptr() == ptr_mut_from_data::<[T]>(PtrData {
                addr: (self.ptr()@.addr + mid * size_of::<T>()) as usize,
                provenance: self.ptr()@.provenance,
                metadata: (self.len() - mid) as usize,
            }),
            first.wf(),
            second.wf(),
    ;

    /// Concatenates `SeqPointsTo` permissions `self` and `other`,
    /// provided their pointers have the same provenance
    /// and `other`'s pointer starts at the end of `self`'s range.
    /// Built on `join_basic`, adding the bytes and `wf` facts.
    pub proof fn join(tracked self, tracked other: Self) -> (tracked joined: Self)
        requires
            self.wf(),
            other.wf(),
            self.ptr()@.provenance == other.ptr()@.provenance,
            other.ptr()@.addr == self.ptr()@.addr + self.len() * size_of::<T>(),
            size_of::<T>() == 0 ==> self.len() + other.len() <= usize::MAX,    // new: needed by `join_basic`
        ensures
            joined.ptr() == ptr_mut_from_data::<[T]>(PtrData {
                addr: self.ptr()@.addr,
                provenance: self.ptr()@.provenance,
                metadata: (self.len() + other.len()) as usize,
            }),
            joined.seq_pt() == self.seq_pt() + other.seq_pt(),
            joined.bytes() == self.bytes() + other.bytes(),
            joined.wf(),
    ;

    /// Given that the subrange is within bounds,
    /// it is always possible to borrow a permission to just that subrange.
    /// Built on `subrange_basic`, adding the alignment and `wf` facts.
    pub proof fn subrange(tracked &self, start_index: nat, len: nat) -> (tracked sub: &Self)
        requires
            self.wf(),
            start_index + len <= self.len(),
        ensures
            sub.wf(),
            sub.ptr() == ptr_mut_from_data::<[T]>(PtrData {
                addr: (self.ptr()@.addr + start_index * size_of::<T>()) as usize,
                provenance: self.ptr()@.provenance,
                metadata: len as usize,
            }),
            sub.seq_pt() == self.seq_pt().subrange(start_index as int, (start_index + len) as int),
    ;

    /// Returns a mutable reference to the sub-permission covering indices `[i, j)`.
    /// The sub-permission has the same provenance,
    /// and its pointer is offset from `self.ptr()` by `i * size_of::<T>()`.
    ///
    /// `self` keeps its pointer,
    /// with the sub-sequence of permissions replaced by the final sub-permission's.
    /// Provided that the sub-permission keeps its pointers and length,
    /// with each element still satisfying decode validity (`ptrs_len_same_valid`),
    /// `self` is also still well-formed.
    ///
    /// Proved from M5 (`from_seq_mut`) in phase 3b;
    /// until then, an axiom on `SeqPointsTo<T, PointsTo<T>>` only.
    pub proof fn subrange_mut(tracked &mut self, i: nat, j: nat) -> (tracked r: &mut Self)
        requires
            self.wf(),
            i <= j <= self.len(),
        ensures
            r.wf(),
            r.ptr() == ptr_mut_from_data::<[T]>(PtrData {
                addr: (old(self).ptr()@.addr + i * size_of::<T>()) as usize,
                provenance: old(self).ptr()@.provenance,
                metadata: (j - i) as usize,
            }),
            r.seq_pt() == old(self).seq_pt().subrange(i as int, j as int),
            final(self).ptr() == old(self).ptr(),
            final(self).seq_pt() == old(self).seq_pt().subrange(0, i as int) + final(r).seq_pt()
                + old(self).seq_pt().subrange(j as int, old(self).len() as int),
            // Criteria necessary for re-establishing invariants
            Self::ptrs_len_same_valid(*r, *final(r)) ==> final(self).wf(),
    ;

    /// Creates a `SeqPointsTo<T, PointsTo<T>>` of length `len`
    /// from a `PointsToUntyped` with the same address and provenance.
    /// The resulting permission will be empty (uninitialized).
    /// (Use `from_untyped_with_typed_value` instead if you want to supply typed values.)
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

    /// Creates a `SeqPointsTo<T, PointsTo<T>>` of length `capacity` from a `PointsToUntyped`,
    /// with the first `typed_value.len()` elements holding the given typed values,
    /// under the following conditions:
    ///
    /// (1) The pointer's address is aligned to `T`.
    ///
    /// (2) The length is exactly `capacity * size_of::<T>()`.
    ///
    /// (3) For each valid element in `typed_value`,
    ///     the corresponding abstract bytes for the `PointsToUntyped` can be decoded into its value.
    ///     `typed_value` may contain empty elements (these are ignored for purposes of decoding)
    ///     and can be a prefix of the total `capacity`
    ///     (in which case, the remaining memory is all logically uninitialized).
    ///
    /// The abstract bytes remain the same.
    /// This preserves the typed contents in memory on a roundtrip
    /// (see `SeqPointsTo::into_untyped_with_typed_value`).
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

    /// Creates a reference to a `PointsToUntyped`
    /// from a reference to a `SeqPointsTo<T, PointsTo<T>>`,
    /// with the same address and provenance, a length of `self.len() * size_of::<T>()`,
    /// and the same abstract bytes.
    pub proof fn as_untyped(tracked &self) -> (tracked raw: &PointsToUntyped)
        requires
            self.wf(),
        ensures
            raw.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: self.ptr()@.addr,
                    provenance: self.ptr()@.provenance,
                    metadata: (self.len() * size_of::<T>()) as usize,
                },
            ),
            raw.bytes() == self.bytes(),
            raw.wf(),
    ;

    /// Creates a mutable reference to a `PointsToUntyped`
    /// from a mutable reference to a `SeqPointsTo<T, PointsTo<T>>`,
    /// with the same address and provenance and a length of `self.len() * size_of::<T>()`.
    /// If this permission carries any typed values, they are dropped here.
    pub proof fn as_untyped_mut(tracked &mut self) -> (tracked raw: &mut PointsToUntyped)
        requires
            self.wf(),
        ensures
            raw.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: old(self).ptr()@.addr,
                    provenance: old(self).ptr()@.provenance,
                    metadata: (old(self).len() * size_of::<T>()) as usize,
                },
            ),
            raw.bytes() == old(self).bytes(),
            raw.wf(),
            final(self).ptr() == old(self).ptr(),
            final(self).len() == old(self).len(),
            final(self).is_fully_empty(),
            // Criteria necessary for re-establishing invariants
            PointsToUntyped::ptrs_len_same(*raw, *final(raw)) ==> ({
                &&& final(self).bytes() == final(raw).bytes()
                &&& final(self).wf()
            }),
    ;

    /// This takes a borrow of each of the `TypedValue<T>`s in a subrange of `self`.
    pub proof fn borrow_typed_value_subrange(tracked &self, start: int, end: int) -> (tracked val:
        Seq<&TypedValue<T>>)
        requires
            self.wf(),
            0 <= start <= end <= self.len(),
        ensures
            val.map_values(|r: &TypedValue<T>| *r) == self.seq_typed_value().subrange(start, end),
    ;

    /// Copies the given `TypedValue<T>`s into the subrange starting at `start`.
    pub proof fn copy_typed_value_subrange(
        tracked &mut self,
        start: int,
        tracked val: Seq<&TypedValue<T>>,
    ) where T: Copy
        requires
            self.wf(),
            0 <= start <= start + val.len() <= self.len(),
            forall|i: int|
                0 <= i < val.len() ==> {
                    (#[trigger] val[i]).is_valid() ==> abs_decode::<T>(
                        self.bytes().subrange(
                            (start + i) * size_of::<T>(),
                            (start + i + 1) * size_of::<T>(),
                        ),
                        &val[i].value(),
                    )
                },
        ensures
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).seq_typed_value() == old(self).seq_typed_value().update_subrange_with(
                start,
                val.map_values(|r: &TypedValue<T>| *r),
            ),
            final(self).wf(),
    ;

    /// This moves a subrange of the `TypedValue<T>`s out from `self`,
    /// leaving that subrange empty.
    pub proof fn take_typed_value_subrange(tracked &mut self, start: int, end: int) -> (tracked val:
        Seq<TypedValue<T>>)
        requires
            self.wf(),
            0 <= start <= end <= self.len(),
        ensures
            val == old(self).seq_typed_value().subrange(start, end),
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).seq_typed_value() == old(self).seq_typed_value().update_subrange_with(
                start,
                Seq::new((end - start) as nat, |i: int| TypedValue::Empty),
            ),
            final(self).wf(),
    ;

    /// Consumes the `Seq<T>`
    /// and puts it in the specified subrange of the `TypedValue<T>`s for `self`.
    pub proof fn put_subrange(tracked &mut self, start: int, tracked val: Seq<T>)
        requires
            self.wf(),
            0 <= start <= start + val.len() <= self.len(),
            forall|i: int|
                0 <= i < val.len() ==> {
                    abs_decode::<T>(
                        self.bytes().subrange(
                            (start + i) * size_of::<T>(),
                            (start + i + 1) * size_of::<T>(),
                        ),
                        &val[i],
                    )
                },
        ensures
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).len() == old(self).len(),
            final(self).is_valid_subrange(start, val.len()),
            final(self).value_subrange(start, val.len()) == val,
            forall|i: int|
                0 <= i < old(self).len() && !(start <= i < start + val.len())
                    ==> #[trigger] final(self).seq_typed_value()[i] == old(self).seq_typed_value()[i],
            final(self).wf(),
    ;

    /// Consumes the `Seq<TypedValue<T>>`
    /// and puts it in the specified subrange of the `TypedValue<T>`s for `self`.
    pub proof fn put_typed_value_subrange(
        tracked &mut self,
        start: int,
        tracked val: Seq<TypedValue<T>>,
    )
        requires
            self.wf(),
            0 <= start <= start + val.len() <= self.len(),
            forall|i: int|
                0 <= i < val.len() ==> {
                    (#[trigger] val[i]).is_valid() ==> abs_decode::<T>(
                        self.bytes().subrange(
                            (start + i) * size_of::<T>(),
                            (start + i + 1) * size_of::<T>(),
                        ),
                        &val[i].value(),
                    )
                },
        ensures
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).seq_typed_value() == old(self).seq_typed_value().update_subrange_with(start, val),
            final(self).wf(),
    ;

    /// Copies the given values into the subrange starting at `start`.
    pub proof fn copy_subrange(tracked &mut self, start: int, tracked val: &Seq<T>) where T: Copy
        requires
            self.wf(),
            0 <= start <= start + val.len() <= self.len(),
            forall|i: int|
                0 <= i < val.len() ==> {
                    abs_decode::<T>(
                        self.bytes().subrange(
                            (start + i) * size_of::<T>(),
                            (start + i + 1) * size_of::<T>(),
                        ),
                        &val[i],
                    )
                },
        ensures
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).len() == old(self).len(),
            final(self).is_valid_subrange(start, val.len()),
            final(self).value_subrange(start, val.len()) == val,
            forall|i: int|
                0 <= i < old(self).len() && !(start <= i < start + val.len())
                    ==> #[trigger] final(self).seq_typed_value()[i] == old(self).seq_typed_value()[i],
            final(self).wf(),
    ;

    /// This moves a subrange of the values out from `self`,
    /// leaving that subrange empty.
    pub proof fn take_subrange(tracked &mut self, start: int, end: int) -> (tracked val: Seq<T>)
        requires
            self.wf(),
            0 <= start <= end <= self.len(),
            self.is_valid_subrange(start, (end - start) as nat),
        ensures
            val == old(self).value_subrange(start, (end - start) as nat),
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).seq_typed_value() == old(self).seq_typed_value().update_subrange_with(
                start,
                Seq::new((end - start) as nat, |i: int| TypedValue::Empty),
            ),
            final(self).wf(),
    ;

    /// This takes a borrow of each of the values in a subrange of `self`.
    /// Renamed from `borrow_value_subrange`
    /// (matching `take_subrange` / `put_subrange` / `copy_subrange` and `PTValueOps::borrow`).
    pub proof fn borrow_subrange(tracked &self, start: int, end: int) -> (tracked val: Seq<&T>)
        requires
            self.wf(),
            0 <= start <= end <= self.len(),
            self.is_valid_subrange(start, (end - start) as nat),
        ensures
            val.map_values(|r: &T| *r) == self.value_subrange(start, (end - start) as nat),
    ;

    /// Specializes `is_disjoint` to the case
    /// when the other permission is a `SeqPointsTo<S, PointsTo<S>>`.
    pub proof fn is_disjoint_seqpt<S>(
        tracked &mut self,
        tracked other: &SeqPointsTo<S, PointsTo<S>>,
    )
        requires
            self.len() != 0,
            other.len() != 0,
            size_of::<T>() != 0,
            size_of::<S>() != 0,
            self.wf(),
            other.wf(),
        ensures
            *old(self) == *final(self),
            final(self).ptr()@.addr + final(self).len() * size_of::<T>() <= other.ptr()@.addr
                || other.ptr()@.addr + other.len() * size_of::<S>() <= final(self).ptr()@.addr,
    ;

    // Private helpers, as today:
    // `bytes_len_helper`, `bytes_subrange`, `bytes_decode_helper`, `bytes_inner_ext`
    // (the byte lemmas);
    // `untyped_ref_join`, `untyped_mut_join` (`as_untyped`, `as_untyped_mut`);
    // `borrow_typed_values`, `copy_typed_values`, `copy_values`, `borrow_values` (the value operations).
}
```

There is no `SeqPointsTo<T, PointsToUnaligned<T>>`,
so there are no sequence aligned/unaligned conversions.

#### Sequence → slice conversions (phase 4)

There are no slice → sequence conversions;
see [Slices](#slices-indexing-and-borrowed-constructors-phase-4) for `borrow_index`.

```rust
impl<T> SeqPointsTo<T, PointsTo<T>> {
    /// A `PointsTo<[T]>` is all valid or all empty,
    /// so a sequence with any empty element gives an empty slice permission.
    pub proof fn as_slice_pt(tracked &self) -> (tracked out: &PointsTo<[T]>)
        requires
            self.wf(),
        ensures
            out.ptr() == self.ptr(),
            out.bytes() == self.bytes(),
            self.is_valid() ==> out.typed_value().is_valid() && out.typed_value().value_ref()@ == self.seq_value(),
            !self.is_valid() ==> out.typed_value().is_empty(),
            out.wf(),
    ;

    /// As for `as_slice_pt`, a sequence with any empty element gives an empty slice permission.
    /// When the borrow ends,
    /// a valid slice value of the same length is distributed back to the elements;
    /// otherwise every element ends empty
    /// (the values of any valid elements are dropped).
    /// If the slice permission keeps its pointers and length,
    /// with its value still satisfying decode validity (`ptrs_len_same_valid`),
    /// the sequence holds its bytes and is well-formed.
    pub proof fn as_slice_pt_mut(tracked &mut self) -> (tracked out: &mut PointsTo<[T]>)
        requires
            self.wf(),
        ensures
            // Initially: as for `as_slice_pt`.
            out.ptr() == old(self).ptr(),
            out.bytes() == old(self).bytes(),
            old(self).is_valid() ==> out.typed_value().is_valid()
                && out.typed_value().value_ref()@ == old(self).seq_value(),
            !old(self).is_valid() ==> out.typed_value().is_empty(),
            out.wf(),
            // Finally: the pointer, length and typed values, unconditionally.
            final(self).ptr() == old(self).ptr(),
            final(self).len() == old(self).len(),
            final(out).typed_value().is_valid() && final(out).typed_value().value_ref()@.len() == old(self).len()
                ==> final(self).is_valid() && final(self).seq_value() == final(out).typed_value().value_ref()@,
            !(final(out).typed_value().is_valid() && final(out).typed_value().value_ref()@.len() == old(self).len())
                ==> final(self).is_fully_empty(),
            // Criteria necessary for re-establishing invariants
            // (the bytes too, since `join_mut` ties them back only under `ptrs_len_same`).
            <PointsTo<[T]> as PTTypedValue>::ptrs_len_same_valid(*out, *final(out)) ==> {
                &&& final(self).bytes() == final(out).bytes()
                &&& final(self).wf()
            },
    ;
}
```

How they're built (without field access):

- `as_slice_pt`: the bytes from the sequence's `as_untyped` (`join_ref`),
  the typed value from `from_elems_ref` on the elements' typed values
  (empty when any element is empty),
  then `from_raw_parts_ref` gives a `&PointsToUnaligned<[T]>` and `as_aligned` the `&PointsTo<[T]>`.
- `as_slice_pt_mut`: each element through `as_unaligned_mut`, then `as_raw_parts_mut` (in `points_to_model.rs`)
  for its bytes and typed value; the bytes merged with `join_mut`, the typed values with M1,
  the permission assembled with M3, and `as_aligned_mut` (M4) for the `&mut PointsTo<[T]>`.

There are no borrowed constructors for sequences
(they would need to collect borrowed permissions into a borrowed `Seq`).

### `ptr_specs.rs` (trusted)

`allocate` and `deallocate` (`global_alloc_id` is in `ptr_model.rs`): approved; see [Allocation](#allocation-phase-2c).

### rustlib

#### `str` (rustlib)

Signatures only; rustlib fixes the details.
rustlib writes `PTPhys`, `PTTypedValue`, `PTProperties` and `PTValueOps` for `PointsToUnaligned<str>`;
its `View` and everything for `PointsTo<str>` come from the generic impls (alignment 1, from `layout_of_str`).
These impls are trusted code in rustlib (see [Trusted surface](#trusted-surface)).

`PTPhys` and `PTTypedValue` are written out from the approved description
([`PointsToUnaligned`: specs](TYPED_POINTS_TO_APPROVED.md#pointstounaligned-specs-phases-2-2b-str-in-rustlib)),
in the same shape as the `[T]` ones:

```rust
impl PTPhys for PointsToUnaligned<str> {
    type A = str;

    /// Builds the `*mut str` from the underlying untyped pointer's address and provenance
    /// and the stored metadata.
    closed spec fn ptr(self) -> *mut str {
        ptr_mut_from_data::<str>(
            PtrData {
                addr: self.pt_untyped().ptr()@.addr,
                provenance: self.pt_untyped().ptr()@.provenance,
                metadata: self.metadata(),
            },
        )
    }

    /// The size of the pointed-to region is the length in bytes.
    open spec fn size(metadata: usize) -> nat {
        metadata as nat
    }

    /// A `PointsToUnaligned<str>` is well-formed at the pointer level
    /// if its memory region is `Self::size(self.ptr()@.metadata)` bytes,
    /// and the underlying `PointsToUntyped` is well-formed.
    open spec fn wf_basic(self) -> bool {
        &&& self.pt_untyped().wf()
        &&& self.pt_untyped().len() == Self::size(self.ptr()@.metadata)
    }

    /// `new` has the same pointer
    /// and the same underlying `PointsToUntyped` pointers and length as `old`.
    open spec fn ptrs_len_same(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& PointsToUntyped::ptrs_len_same(old.pt_untyped(), new.pt_untyped())
    }

    proof fn stays_wf_basic(old: Self, new: Self) {
    }
}

impl PTTypedValue for PointsToUnaligned<str> {
    /// The inherent `typed_value` accessor.
    open spec fn typed_value(self) -> TypedValue<str> {
        PointsToUnaligned::<str>::typed_value(self)
    }

    /// The underlying untyped permission's bytes.
    open spec fn bytes(self) -> Seq<AbstractByte> {
        self.pt_untyped().bytes()
    }

    /// Always `true`:
    /// decoding (`EncodingStr`) makes the `str`'s length its number of bytes,
    /// which `wf_basic` makes the metadata.
    open spec fn metadata_matches(value: &str, metadata: usize) -> bool {
        true
    }

    /// Always `true`: a `PointsToUnaligned` has no alignment requirement.
    open spec fn satisfies_alignment(addr: usize) -> bool {
        true
    }

    proof fn bytes_decode(&self);

    proof fn satisfies_alignment_of_wf(&self);

    proof fn lemma_wf_basic(&self);

    // ptrs_len_same_valid: the trait's default body.

    /// From `PointsToUntyped::lemma_ptrs_len_same_untyped` on the underlying permissions.
    broadcast proof fn lemma_ptrs_len_same_valid(old: Self, new: Self);

    /// From `PointsToUntyped::stays_wf` on the underlying permissions.
    proof fn stays_wf(old: Self, new: Self);
}
```

`PTProperties` and `PTValueOps` are the same as for `T` and `[T]`,
except that `PTValueOps` goes through the generic field helpers
(`tracked_typed_value`, `into_raw_parts`, `from_raw_parts`, `as_raw_parts_mut`, `tracked_pt_untyped`),
since rustlib can't touch the fields.

```rust
impl PTProperties for PointsToUnaligned<str> {
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

impl PTValueOps for PointsToUnaligned<str> {
    // zero_sized, borrow, into_untyped, from_untyped: the trait's default bodies.

    /// Delegates to `tracked_typed_value`.
    proof fn borrow_typed_value(tracked &self) -> tracked &TypedValue<str>;

    /// Swaps `Empty` into the typed value,
    /// through `as_raw_parts_mut`.
    proof fn take_typed_value(tracked &mut self) -> (tracked v: TypedValue<str>);

    /// Replaces the typed value,
    /// through `as_raw_parts_mut`.
    proof fn put_typed_value(tracked &mut self, tracked v: TypedValue<str>);

    /// Delegates to `into_raw_parts`.
    proof fn into_untyped_with_typed_value(tracked self) -> (tracked (pt_untyped, v): (PointsToUntyped, TypedValue<str>));

    /// Delegates to `from_raw_parts`.
    proof fn from_untyped_with_typed_value(
        tracked pt_untyped: PointsToUntyped,
        tracked typed_value: TypedValue<str>,
        metadata: usize,
    ) -> (tracked out: Self);

    /// Delegates to `tracked_pt_untyped`.
    proof fn as_untyped(tracked &self) -> (tracked pt_untyped: &PointsToUntyped);

    /// Empties the typed value, then mutably borrows the untyped bytes,
    /// through `as_raw_parts_mut`.
    proof fn as_untyped_mut(tracked &mut self) -> (tracked pt_untyped: &mut PointsToUntyped);
}
```

Only shared casts: there are no owned or `&mut` `str` ↔ `[u8]` permission casts.
Both are proved, with no new axioms:
the value from rustlib's existing `str::as_bytes_tracked` / `str::from_bytes_tracked` and `TypedValue::valid_ref`
(an empty value from `&TypedValue::Empty`, a promoted constant),
and the permission from `from_raw_parts_ref` with the same untyped bytes and metadata.

```rust
impl PointsToUnaligned<str> {
    /// Borrows as a byte-slice permission to the same bytes, with the same metadata;
    /// the value becomes the string's bytes.
    pub proof fn as_bytes(tracked &self) -> (tracked out: &PointsToUnaligned<[u8]>)
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

    /// Borrows a byte-slice permission as a `str` permission to the same bytes,
    /// with the same metadata.
    /// Valid only if the value is valid UTF-8; otherwise empty.
    pub proof fn from_bytes_ref(tracked p: &PointsToUnaligned<[u8]>) -> (tracked out: &PointsToUnaligned<str>)
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
}

impl PointsTo<str> {
    /// Borrows as a byte-slice permission to the same bytes, with the same metadata;
    /// the value becomes the string's bytes.
    /// Through `as_unaligned`, `PointsToUnaligned::<str>::as_bytes` and `as_aligned`
    /// (alignment 1 for both `str` and `[u8]`).
    pub proof fn as_bytes(tracked &self) -> (tracked out: &PointsTo<[u8]>)
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

    /// Borrows a byte-slice permission as a `str` permission to the same bytes,
    /// with the same metadata.
    /// Valid only if the value is valid UTF-8; otherwise empty.
    /// Through `as_unaligned`, `PointsToUnaligned::<str>::from_bytes_ref` and `as_aligned`
    /// (alignment 1 for both `str` and `[u8]`).
    pub proof fn from_bytes_ref(tracked p: &PointsTo<[u8]>) -> (tracked out: &PointsTo<str>)
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
}
```

On hold (asking Natalie): `as_bytes_tracked` requires a UTF-8 value (`self.inv()`), which `self.wf()` doesn't give,
since UTF-8 isn't part of decoding.
Options: drop `as_bytes_tracked`'s `requires self.inv()` in rustlib,
or have `as_bytes` require `self.typed_value().is_valid() ==> valid_utf8(self.typed_value().value_ref()@)`.

Open (to revisit when reviewing `str`): UTF-8 validity might also need to be added to the `str` permissions themselves,
for example as part of a valid `PointsToUnaligned<str>`'s well-formedness,
since decoding (`EncodingStr`) doesn't include it.
Planned approach: generalize `PTTypedValue::metadata_matches`
to cover validity requirements beyond decoding (such as UTF-8 for `str`),
not just the value matching the pointer metadata.

The other rustlib axioms (the `str` reference helpers):
see [New rustlib axioms](#new-rustlib-axioms).

## Inherent impls

What stays outside the traits, by impl block, after all phases.
"(new)" is added by this design; "(removed)" lists what moves into a trait;
everything else exists today.

| Impl block | Functions | Notes |
|---|---|---|
| `impl<T: ?Sized> TypedValue<T>` | `is_valid`, `is_empty`; `value_ref` (new); `valid_ref` (new, phase 3b) | |
| `impl<T> TypedValue<T>` | `value`, `tracked_copy` | Sized: by-value access |
| `impl<T> TypedValue<[T]>` | `value` (-> `&[T]`); `from_elems_ref` (new axiom, phase 3b); `from_elems_mut` (new axiom M1, phase 3b) | |
| `impl<T: ?Sized> PointsToUnaligned<T>` | closed accessors `typed_value`, `pt_untyped`, `metadata`; `bytes`, `is_valid`, `is_empty` (inline); `tracked_pt_untyped`; `as_raw_parts_mut` (new, phase 4); `tracked_typed_value`, `into_raw_parts`, `from_raw_parts` (new; for rustlib's `str`); `from_raw_parts_ref` (new axiom, phase 3b), `from_raw_parts_mut` (new axiom M3, phase 3b) | The inherent `typed_value`/`bytes` coexist with the trait's (phase 0, item 5). |
| `impl<T: ?Sized> PointsToUnaligned<T> where PointsToUnaligned<T>: PTValueOps<A = T>` | `into_aligned`, `as_aligned` (new, generic); `as_aligned_mut` (new, generic, phase 3b: needs M4) | Contracts in [`PointsTo`: proofs and aligned/unaligned conversions](#pointsto-proofs-and-alignedunaligned-conversions). |
| `impl<T> PointsToUnaligned<T>` | `value`; `is_disjoint_unaligned<S>`. (removed: `wf`, `stays_wf`, `zero_sized`) | |
| `impl<T> PointsToUnaligned<[T]>` | `len` (new, inline); `from_untyped_ref`, `from_untyped_with_value_ref`, `borrow_index` (new, phase 4; the primary implementations). (removed in 2b: inherent `wf`) | |
| `impl<T: ?Sized> PointsTo<T>` | closed `pt_unaligned`; `typed_value`, `metadata`, `bytes`, `is_valid`, `is_empty` (open, delegating); `tracked_pt_unaligned`; `from_unaligned_mut` (new axiom M4) | |
| `impl<T: ?Sized> PointsTo<T> where PointsToUnaligned<T>: PTValueOps<A = T>` | `into_unaligned`, `as_unaligned`, `as_unaligned_mut` (new, generic) | Contracts in [`PointsTo`: proofs and aligned/unaligned conversions](#pointsto-proofs-and-alignedunaligned-conversions). |
| `impl<T> PointsTo<T>` | `value`, `is_aligned`, `is_disjoint_pointsto<S>`; `borrow_mut` (axiom). (removed: `wf`, `stays_wf`, `lemma_ptrs_len_same_valid`, `zero_sized`, `bytes_decode`, the untyped conversions, the value operations) | Removed ones are `PTValueOps` / `PTSizedValue` methods. |
| `impl<T> PointsTo<[T]>` | `len` (new, inline); `from_untyped_ref`, `from_untyped_with_value_ref`, `borrow_index` (new, phase 4; compositions over the `PointsToUnaligned` versions). (removed: inherent `wf`) | |
| `impl<T, P: PTProperties<A = T>> SeqPointsTo<T, P>` (`points_to_model.rs` / `points_to_ops.rs`) | `seq_pt`, `len`, `spec_index`; `tracked_seq_pt`, `tracked_seq_pt_mut`, `index_mut`, `from_seq`, `empty`, `into_seq` (moved here in phase 1); `split_basic`, `join_basic`, `subrange_basic` (new); `from_seq_mut` (new axiom M5) | Structural; stated with `wf_basic`. The only code touching the fields. |
| `impl<T> SeqPointsTo<T, PointsTo<T>>` | `View` (`SeqPointsToData<T>`); `thin_ptr`, `wf`, `bytes`, `bytes_inner`, `seq_typed_value`, `is_valid`, `is_empty`, `is_fully_empty`, `seq_value`, `is_valid_subrange`, `value_subrange`, `ptrs_len_same_valid`, `stays_wf`, `lemma_ptrs_len_same_valid`, `typed_value_equiv`, the byte lemmas, `split`, `join`, `subrange`, `subrange_mut` (proved in phase 3b), `zero_sized`, the untyped conversions, the value operations, `is_aligned`, `is_disjoint_seqpt`; `as_slice_pt`, `as_slice_pt_mut` (new, phase 4) | The only typed sequence impl. |
| `impl SeqPointsTo<u8, PointsToByte>` (`PointsToUntyped`, `points_to_model.rs` / `points_to_ops.rs`) | `View`, `bytes`, `wf`, `stays_wf`, `lemma_ptrs_len_same_untyped` (renamed), `zero_sized<T>`, `split`, `split_ref`, `join` (wrappers over the `_basic` primitives); `join_ref`, `join_mut` (axioms); `split_mut` (proved in phase 3b); `is_disjoint_untyped` | |
| `impl PointsToByte` (renamed from `PointsToSingleton`) | `byte`, `is_disjoint_byte` (renamed from `is_disjoint_singleton`, in phase 1 with the type) | |
| `impl PointsToRaw` | everything in [`PointsToRaw` (phase 2c)](#pointstoraw-phase-2c) above (new) | Not a `PTPhys`. |
| free functions | `tracked_slice_index`, `tracked_ref` (new axioms, phase 3b); `allocate`, `deallocate` (ported, phase 2c, with `PointsToUntyped` in place of `PointsToRaw`; in `ptr_specs.rs`; `Dealloc` dropped) | |
| rustlib: `impl PointsToUnaligned<str>` | `as_bytes`, `from_bytes_ref` | |
| rustlib: `impl PointsTo<str>` | `as_bytes`, `from_bytes_ref` (through the aligned/unaligned conversions) | |

## Trusted surface

Every trusted item the permissions rely on, after all phases:
`axiom fn`s, `external_body` functions and types, `assume_specification`s,
and `uninterp` specs that axioms constrain.
"Uses" names the main dependents.

**Existing, unchanged.** Approved; see [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#existing-unchanged-trusted-specs).

**New.** See [New axioms](#new-axioms).

**Dependency direction.**
`ptr_ref`, `ptr_mut_ref` and `mut_ref_to_shr_points_to` (in `ptr_specs.rs`) take or produce `PointsTo<T>`,
and the restored slice versions `PointsTo<[T]>`;
`allocate` / `deallocate` use `PointsToUntyped`.
The phase 3b axioms are stated on `PointsToUnaligned`, `PointsTo`, `SeqPointsTo` and `TypedValue`.
All of these are in the two trusted files (see [Module layout](TYPED_POINTS_TO_APPROVED.md#module-layout)),
so no trusted code depends on `points_to_collections.rs`.

**rustlib.** rustlib also holds trusted code for `str`:
its axioms (`ptr_mut_ref_str`, the other `str` reference helpers, `spec_size_of_val_str`),
and the `PTPhys`, `PTTypedValue`, `PTProperties` and `PTValueOps` impls for `PointsToUnaligned<str>`.
The impls aren't axioms, but they're trusted in effect:
`PTPhys::size` and `wf_basic` fix what memory a `PointsToUnaligned<str>` claims,
which the `str` reference axioms rely on,
and `PTTypedValue`'s `metadata_matches` and `satisfies_alignment` feed into `wf`.
Sealing doesn't keep them in vstd:
vstd's `impl<T: ?Sized> PTPhysSealed for PointsToUnaligned<T>` covers every `PointsToUnaligned<_>`,
so rustlib can write `PTPhys` for any of them, not just `str`.

## New axioms

All in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#new-axioms-and-axioms-with-bigger-changes)
and approved, including `allocate`, `deallocate`, `global_alloc_id` and `PointsTo::borrow_mut`,
except `TypedValue::<[T]>::from_elems_ref` and the untyped joins `join_ref` / `join_mut` (waiting on Travis).

Minor changes to existing axioms (`ptr_ref`, `ptr_ref2`, `ptr_ref2_ghost`, `mut_ref_to_shr_points_to`, `SharedReference::points_to`,
and the restored slice versions `ptr_ref_slice`, `ptr_ref2_slice_ghost`, `mut_ref_to_shr_points_to_slice`, `SharedReference<[T]>::points_to`)
are approved and in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#minor-changes-to-existing-trusted-specs),
and so are the strengthened `ptr_mut_ref`, `ptr_mut_ref_slice` and `ptr_mut_ref_str`,
the other `str` reference helpers (minor changes), the new `Seq` tracked operations
(`tracked_borrow_subrange`, `tracked_split_borrow_mut`),
and the borrowed-assembly axioms (`tracked_slice_index`, `tracked_ref`,
`PointsToUnaligned::from_raw_parts_ref`, M1, M3–M5)
([TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#new-axioms-and-axioms-with-bigger-changes)).

**rustlib.** All new rustlib axioms are approved
([TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#new-axioms-and-axioms-with-bigger-changes)).

"New" means new relative to the `verify-rustlib` branch.
`abs_decode_slice` (already in `type_representation.rs`) is approved and listed in
[TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#new-axioms-and-axioms-with-bigger-changes).

### Borrowed-assembly axioms (phase 3b)

All in
[TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#new-axioms-and-axioms-with-bigger-changes):
the shared ones (`tracked_slice_index`, `tracked_ref`, `PointsToUnaligned::from_raw_parts_ref`,
and `TypedValue::<[T]>::from_elems_ref`, which is waiting on Travis) and the `&mut` ones (M1, M3–M5).

### Slice reference helpers (phase 4b)

Approved and in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md):
`ptr_mut_ref_slice` with `ptr_mut_ref` in
[New axioms and axioms with bigger changes](TYPED_POINTS_TO_APPROVED.md#new-axioms-and-axioms-with-bigger-changes),
and the rest in [Minor changes to existing trusted specs](TYPED_POINTS_TO_APPROVED.md#minor-changes-to-existing-trusted-specs).

### Allocation (phase 2c)

Approved; see [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#new-axioms-and-axioms-with-bigger-changes).

### New rustlib axioms

All approved and in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md):
`ptr_mut_ref_str` in
[New axioms and axioms with bigger changes](TYPED_POINTS_TO_APPROVED.md#new-axioms-and-axioms-with-bigger-changes),
and the other `str` reference helpers in [Minor changes to existing trusted specs](TYPED_POINTS_TO_APPROVED.md#minor-changes-to-existing-trusted-specs).
