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
the module layout, and the `TypedValue` impl are approved
and are in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md).


## Specifications

Bodies are omitted except for spec fns and trusted code.
"Unchanged" means the contract is today's, apart from `size()` → `Self::size(self.ptr()@.metadata)`.

Grouped by module ([layout](TYPED_POINTS_TO_APPROVED.md#module-layout)), from low-level to high-level permissions.
An impl block with both spec fns and proofs is split as in the layout:
the spec fns and axioms are under `points_to_model.rs`, the proofs under `points_to_ops.rs`.
The trait definitions are in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#trait-definitions).

### `points_to_model.rs` (trusted)

#### `PTProperties` (changed in phase 1b)

The trait is in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#trait-definitions). Compared with today's:
contracts use `Self::size(self.ptr()@.metadata)` instead of `self.size()`;
`is_disjoint` compares `ptr()@.addr` instead of `ptr() as int`;
and `ptrs_len_same_valid` is renamed `ptrs_len_same` (pointer-level; the decoding version is
`PTValueOps::ptrs_len_same_valid`), which `stays_wf_basic` now uses.

The lemma groups (`group_points_to_lemmas`, `group_points_to_collections_lemmas`) are in
[Module layout](TYPED_POINTS_TO_APPROVED.md#module-layout).

#### `SeqPointsTo` and `PointsToUntyped`: specs (phase 1b)

```rust
// `A = T` is bound on the impls, not here,
// so recursive types like `struct Tree { children: Vec<Tree> }` are allowed.
#[verifier::accept_recursive_types(T)]
pub tracked struct SeqPointsTo<T, P: PTProperties> {
    seq_pt: Seq<P>,
    ptr: Ghost<*mut [T]>,
}

impl<T, P: PTProperties<A = T>> PTPhys for SeqPointsTo<T, P> {
    type A = [T];
    closed spec fn ptr(self) -> *mut [T] { self.ptr@ }
    open spec fn size(metadata: usize) -> nat { metadata as nat * P::size(()) }
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
}

/// Structural specs for a sequence of any element permission.
impl<T, P: PTProperties<A = T>> SeqPointsTo<T, P> {
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

    // from_seq_mut (M5, axiom): see [Borrowed-assembly axioms](#borrowed-assembly-axioms-phase-3b).
}

impl SeqPointsTo<u8, PointsToByte> {   // PointsToUntyped
    pub open spec fn wf(self) -> bool { self.wf_basic() }   // the metadata clause moved to wf_basic
    // View, bytes: today's.
    // join_ref, join_mut: axioms (see TYPED_POINTS_TO_APPROVED.md, Untyped joins).
}
```

#### `TypedValue` (phase 2)

Approved; see [`TypedValue`](TYPED_POINTS_TO_APPROVED.md#typedvalue-phase-2).

#### `PointsToUnaligned`: specs (phases 2, 2b; `str` in rustlib)

```rust
// The shared `wf_basic` body, written once.
impl<T: ?Sized> PointsToUnaligned<T> where PointsToUnaligned<T>: PTPhys<A = T> {
    pub open spec fn wf_basic_unaligned(self) -> bool {
        &&& self.pt_untyped().wf()
        &&& self.pt_untyped().len() == Self::size(self.ptr()@.metadata)
    }
}

// One per type; only `size` differs.
// `wf_basic` is in `PTPhys` so that `is_disjoint` can require it of `other`
// (a generic `other` bounded by `PTProperties` would be a trait cycle).
impl<T> PTPhys for PointsToUnaligned<T> {
    type A = T;
    closed spec fn ptr(self) -> *mut T {
        ptr_mut_from_data::<T>(PtrData {
            addr: self.pt_untyped().ptr()@.addr,
            provenance: self.pt_untyped().ptr()@.provenance,
            metadata: self.metadata(),   // closed inherent accessor for the ghost field
        })
    }
    open spec fn size(metadata: ()) -> nat { size_of::<T>() }
    open spec fn wf_basic(self) -> bool { self.wf_basic_unaligned() }
}
impl<T> PTPhys for PointsToUnaligned<[T]> {
    type A = [T];
    closed spec fn ptr(self) -> *mut [T] { /* same as above */ }
    open spec fn size(metadata: usize) -> nat { metadata as nat * size_of::<T>() }
    open spec fn wf_basic(self) -> bool { self.wf_basic_unaligned() }
}
// rustlib: impl PTPhys for PointsToUnaligned<str> { type A = str; ptr: same; size(len) = len; wf_basic: same }
// (Needs no `str` view. `PTPhys` is sealed by the crate-private `PTPhysSealed`;
// vstd's generic `impl<T: ?Sized> PTPhysSealed for PointsToUnaligned<T>` already covers `str`,
// and vstd is a module of rustlib's `core`, so rustlib can still write this impl.)

// PTTypedValue items per impl (the operations' contracts are PTValueOps's):
//                     typed_value          bytes                     metadata_matches(v, m)   satisfies_alignment(a)
// PointsToUnaligned<T>    self.typed_value()   self.pt_untyped().bytes()  true                true
// PointsToUnaligned<[T]>  (same)               (same)                    v@.len() == m       true
// PointsToUnaligned<str>  (same)               (same)                    true                true   (rustlib; decoding is EncodingStr's, without UTF-8)
// wf: the trait's default body. For T and [T], this replaces today's per-type wf_basic clauses.
```

#### `PointsTo`: specs (generic; phase 2, widened in phase 2b)

```rust
impl<T: ?Sized> PTPhys for PointsTo<T> where PointsToUnaligned<T>: PTValueOps<A = T> {
    type A = T;
    open spec fn ptr(self) -> *mut T { self.pt_unaligned().ptr() }
    open spec fn size(metadata: Metadata<T>) -> nat { <PointsToUnaligned<T> as PTPhys>::size(metadata) }
    open spec fn wf_basic(self) -> bool { self.pt_unaligned().wf_basic() }
}

impl<T: ?Sized> View for PointsTo<T> where PointsToUnaligned<T>: PTValueOps<A = T> {
    type V = PointsToData<T>;
    open spec fn view(&self) -> PointsToData<T> {
        PointsToData { ptr: self.ptr(), value: self.typed_value(), bytes: self.bytes() }
    }
}

impl<T: ?Sized> PTTypedValue for PointsTo<T> where PointsToUnaligned<T>: PTValueOps<A = T> {
    // typed_value, bytes, metadata_matches delegate to self.pt_unaligned;
    open spec fn satisfies_alignment(addr: usize) -> bool {
        &&& PointsToUnaligned::<T>::satisfies_alignment(addr)
        &&& addr as nat % spec_align_of_val::<T>(arbitrary()) == 0
    }
    // wf: the trait's default body; the lemmas delegate.
}
```

### `points_to_ops.rs` (trusted)

#### `SeqPointsTo` and `PointsToUntyped`: proofs (phase 1b)

```rust
impl<T, P: PTProperties<A = T>> PTProperties for SeqPointsTo<T, P> {
    // ptrs_len_same (renamed from ptrs_len_same_valid; elements' ptrs_len_same), proof fns: unchanged.
}

/// Structural operations for a sequence of any element permission, stated with `wf_basic`.
impl<T, P: PTProperties<A = T>> SeqPointsTo<T, P> {
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
}

impl SeqPointsTo<u8, PointsToByte> {   // PointsToUntyped
    // split, join, split_ref: wrappers over split_basic / join_basic / subrange_basic (same contracts as today).
    // stays_wf, lemma_ptrs_len_same_untyped, zero_sized, is_disjoint_untyped: today's contracts.
    // split_mut: today's (commented-out) contract, proved in phase 3b
    //   from M5 and Seq::tracked_split_borrow_mut.
}
```

#### `PointsToUnaligned`: proofs

```rust
// One per type (T and [T]; rustlib writes the str one), the same body each time.
// Not generic: the delegations need `wf_basic` and `ptr` to unfold,
// and the per-type `PTPhys` bodies don't unfold in generic code.
impl<T> PTProperties for PointsToUnaligned<T> {
    open spec fn ptrs_len_same(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& PointsToUntyped::ptrs_len_same(old.pt_untyped(), new.pt_untyped())
    }
    // is_nonnull, ptr_bounds, provenance_not_none, is_disjoint, stays_wf_basic: delegate to pt_untyped.
}
// impl<T> PTProperties for PointsToUnaligned<[T]>: the same.
// rustlib: impl PTProperties for PointsToUnaligned<str>: the same.

// PTValueOps (per type) and PTSizedValue (for T): the traits' contracts.
```

**Proposed: `as_raw_parts_mut`** (proved; inherent, so no change to the approved traits).
It borrows the two fields separately: the inverse of M3.
Generic over `T: ?Sized`, so it covers `T`, `[T]` and rustlib's `str` without rustlib touching the fields.

```rust
impl<T: ?Sized> PointsToUnaligned<T> {
    /// Mutably borrows the untyped bytes and the typed value separately
    /// (the inverse of `from_raw_parts_mut`). The metadata is unchanged.
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
}
```

#### `PointsTo`: proofs and aligned/unaligned conversions

```rust
impl<T: ?Sized> PTProperties for PointsTo<T> where PointsToUnaligned<T>: PTValueOps<A = T> {
    open spec fn ptrs_len_same(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& <PointsToUnaligned<T> as PTProperties>::ptrs_len_same(old.pt_unaligned(), new.pt_unaligned())
    }
    // proof fns delegate to pt_unaligned.
}

impl<T: ?Sized> PTValueOps for PointsTo<T> where PointsToUnaligned<T>: PTValueOps<A = T> {
    // Everything delegates to self.pt_unaligned, except:
    // from_raw_parts: wraps the PointsToUnaligned result.
    // ptrs_len_same_valid, borrow, into_untyped, from_untyped, zero_sized: the trait's default bodies.
}

impl<T> PTSizedValue for PointsTo<T> {
    // lemma_satisfies_alignment_offset: the alignment arithmetic; lemma_metadata_matches: empty.
    // take, put, copy, copy_typed_value, from_untyped_with_value: the trait's default bodies.
}

impl<T: ?Sized> PointsToUnaligned<T> where PointsToUnaligned<T>: PTValueOps<A = T> {
    /// Converts to a `PointsTo<T>`, given that the address is aligned.
    pub proof fn into_aligned(tracked self) -> (tracked out: PointsTo<T>)
        requires
            self.wf(),
            <PointsTo<T> as PTValueOps>::satisfies_alignment(self.ptr()@.addr),
        ensures
            out.pt_unaligned() == self,
            out.wf(),
    ;

    /// Borrows as a `PointsTo<T>`, given that the address is aligned.
    pub proof fn as_aligned(tracked &self) -> (tracked out: &PointsTo<T>)
        requires
            self.wf(),
            <PointsTo<T> as PTValueOps>::satisfies_alignment(self.ptr()@.addr),
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
            <PointsTo<T> as PTValueOps>::satisfies_alignment(self.ptr()@.addr),
        ensures
            out.pt_unaligned() == *old(self),
            out.wf(),
            *final(self) == final(out).pt_unaligned(),
            <PointsTo<T> as PTValueOps>::ptrs_len_same_valid(*out, *final(out)) ==> final(self).wf(),
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

#### Slices: indexing and borrowed constructors (phase 4)

There are no slice → sequence conversions (`as_seq_pt`, `as_seq_pt_mut`);
`borrow_index` borrows one element of a slice permission instead
(spec okayed, to be approved with its impl block).
It needs no new axioms:
the bytes come from `split_ref` on the untyped permission,
a valid element's typed value from `tracked_slice_index` and `TypedValue::valid_ref`
(an empty one from `tracked_static_mut_ref`, as in the other borrowed conversions),
and the permission from `from_raw_parts_ref`.

The borrowed constructors are the borrowed counterparts of the owned `from_untyped` / `from_untyped_with_typed_value`.

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
// impl<T> PointsTo<[T]>: borrow_index(&self, i) -> &PointsTo<T>, the same contract;
//   composed from as_unaligned, PointsToUnaligned::<[T]>::borrow_index and as_aligned
//   (each element's address is aligned because the slice's is,
//   and size_of::<T>() is a multiple of align_of::<T>()).
// PointsTo<[T]> borrowed constructors: the same, plus alignment
// (PointsTo::<T>::satisfies_alignment of the address) as a precondition.
```

### `points_to_collections.rs` (verified)

#### `PointsToRaw` (phase 2c)

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
}
```

Typed permissions convert through `PointsToUntyped`:
`into_untyped` followed by `PTValueOps::from_untyped` / `SeqPointsTo::from_untyped`, and back.

#### Typed `SeqPointsTo` (phase 1b)

`from_seq`, `empty`, `into_seq`, `tracked_seq_pt(_mut)` and `index_mut` have no typed versions.

```rust
// The only typed sequence impl (there is no generic typed impl).
impl<T> SeqPointsTo<T, PointsTo<T>> {
    pub open spec fn wf(self) -> bool {
        &&& self.wf_basic()
        &&& PointsTo::<T>::satisfies_alignment(self.ptr()@.addr)
        &&& forall|i| 0 <= i < self.len() ==> #[trigger] self[i].wf()
    }

    /// The pointer-level `ptrs_len_same`, plus each element's `PTValueOps::ptrs_len_same_valid`.
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
    // into_untyped*, as_untyped*, the value operations, the byte lemmas: unchanged,
    // except `borrow_value_subrange` is renamed `borrow_subrange`
    // (matching `take_subrange` / `put_subrange` / `copy_subrange` and `PTValueOps::borrow`).
    // `is_disjoint_seqpt` (other: &SeqPointsTo<S, PointsTo<S>>): unchanged.
}

// View (SeqPointsToData<T>, with seq_pt: Seq<PointsTo<T>>): unchanged.
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
    /// If the slice is still empty when the borrow ends, every element ends empty
    /// (the values of any valid elements are dropped).
    pub proof fn as_slice_pt_mut(tracked &mut self) -> (tracked out: &mut PointsTo<[T]>)
        requires
            self.wf(),
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
```

How they're built (without field access):

- `as_slice_pt`: the bytes from the sequence's `as_untyped` (`join_ref`),
  the typed value from `tracked_slice_from_refs` and `valid_ref`
  (or an empty one when any element is empty),
  then `from_raw_parts_ref` gives a `&PointsToUnaligned<[T]>` and `as_aligned` the `&PointsTo<[T]>`.
- `as_slice_pt_mut`: each element through `as_unaligned_mut`, then `as_raw_parts_mut` (in `points_to_ops.rs`)
  for its bytes and typed value; the bytes merged with `join_mut`, the typed values with M1,
  the permission assembled with M3, and `as_aligned_mut` (M4) for the `&mut PointsTo<[T]>`.

There are no borrowed constructors for sequences
(they would need to collect borrowed element permissions into a borrowed `Seq`).

### `ptr_specs.rs` (trusted)

`allocate` and `deallocate` (`global_alloc_id` is in `ptr_model.rs`): approved; see [Allocation](#allocation-phase-2c).

### rustlib

#### `str` (rustlib)

Signatures only; rustlib fixes the details.
rustlib writes `PTPhys` (`Metadata<str>` is the byte length; `size(len) = len`;
`wf_basic` is `self.wf_basic_unaligned()`), `PTProperties` (the same delegations as for `T` and `[T]`), `View`,
`PTTypedValue` and `PTValueOps` for `PointsToUnaligned<str>`;
`PointsTo<str>` comes from the generic impls (alignment 1, from `layout_of_str`).

Only shared casts: there are no owned or `&mut` `str` ↔ `[u8]` permission casts.
Both are proved, with no new axioms:
the value from rustlib's existing `str::as_bytes_tracked` / `str::from_bytes_tracked` and `TypedValue::valid_ref`
(an empty value from `tracked_static_mut_ref`),
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

    /// Borrows a byte-slice permission as a `str` permission to the same bytes, with the same metadata.
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
// impl PointsTo<str>: as_bytes(&self) -> &PointsTo<[u8]> and from_bytes_ref(&PointsTo<[u8]>) -> &PointsTo<str>,
//   the same contracts, through the aligned/unaligned conversions (alignment 1 for both).
```

On hold (asking Natalie): `as_bytes_tracked` requires a UTF-8 value (`self.inv()`), which `self.wf()` doesn't give,
since UTF-8 isn't part of decoding.
Options: drop `as_bytes_tracked`'s `requires self.inv()` in rustlib,
or have `as_bytes` require `self.typed_value().is_valid() ==> valid_utf8(self.typed_value().value_ref()@)`.

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
| `impl<T> TypedValue<[T]>` | `value` (-> `&[T]`); `from_elems_mut` (new axiom M1, phase 3b) | |
| `impl<T: ?Sized> PointsToUnaligned<T>` | closed accessors `typed_value`, `pt_untyped`, `metadata`; `bytes`, `is_valid`, `is_empty` (inline); `tracked_pt_untyped`; `as_raw_parts_mut` (new, proposed, phase 4); `from_raw_parts_ref` (new axiom, phase 3b), `from_raw_parts_mut` (new axiom M3, phase 3b) | The inherent `typed_value`/`bytes` coexist with the trait's (phase 0, item 5). |
| `impl<T: ?Sized> PointsToUnaligned<T> where PointsToUnaligned<T>: PTValueOps<A = T>` | `into_aligned`, `as_aligned` (new, generic); `as_aligned_mut` (new, generic, phase 3b: needs M4) | Contracts in [`PointsTo`: proofs and aligned/unaligned conversions](#pointsto-proofs-and-alignedunaligned-conversions). |
| `impl<T> PointsToUnaligned<T>` | `value`; `is_disjoint_unaligned<S>`. (removed: `wf`, `stays_wf`, `zero_sized`) | |
| `impl<T> PointsToUnaligned<[T]>` | `from_untyped_ref`, `from_untyped_with_value_ref`, `borrow_index` (new, phase 4; the primary implementations). (removed in 2b: inherent `wf`) | |
| `impl<T: ?Sized> PointsTo<T>` | closed `pt_unaligned`; `typed_value`, `metadata`, `bytes`, `is_valid`, `is_empty` (open, delegating); `tracked_pt_unaligned`; `from_unaligned_mut` (new axiom M4) | |
| `impl<T: ?Sized> PointsTo<T> where PointsToUnaligned<T>: PTValueOps<A = T>` | `into_unaligned`, `as_unaligned`, `as_unaligned_mut` (new, generic) | Contracts in [`PointsTo`: proofs and aligned/unaligned conversions](#pointsto-proofs-and-alignedunaligned-conversions). |
| `impl<T> PointsTo<T>` | `value`, `is_aligned`, `is_disjoint_pointsto<S>`; `borrow_mut` (axiom). (removed: `wf`, `stays_wf`, `lemma_ptrs_len_same_valid`, `zero_sized`, `bytes_decode`, the untyped conversions, the value operations) | Removed ones are `PTValueOps` / `PTSizedValue` methods. |
| `impl<T> PointsTo<[T]>` | `from_untyped_ref`, `from_untyped_with_value_ref`, `borrow_index` (new, phase 4; compositions over the `PointsToUnaligned` versions). (removed: inherent `wf`) | |
| `impl<T, P: PTProperties<A = T>> SeqPointsTo<T, P>` (`points_to_model.rs` / `points_to_ops.rs`) | `seq_pt`, `len`, `spec_index`, `thin_ptr`; `tracked_seq_pt`, `tracked_seq_pt_mut`, `index_mut`, `from_seq`, `empty`, `into_seq` (moved here in phase 1); `split_basic`, `join_basic`, `subrange_basic` (new); `from_seq_mut` (new axiom M5) | Structural; stated with `wf_basic`. The only code touching the fields. |
| `impl<T> SeqPointsTo<T, PointsTo<T>>` | `View` (`SeqPointsToData<T>`); `wf`, `bytes`, `bytes_inner`, `seq_typed_value`, `is_valid`, `is_empty`, `is_fully_empty`, `seq_value`, `is_valid_subrange`, `value_subrange`, `ptrs_len_same_valid`, `stays_wf`, `lemma_ptrs_len_same_valid`, `typed_value_equiv`, the byte lemmas, `split`, `join`, `subrange`, `subrange_mut` (proved in phase 3b), `zero_sized`, the untyped conversions, the value operations, `is_aligned`, `is_disjoint_seqpt`; `as_slice_pt`, `as_slice_pt_mut` (new, phase 4) | The only typed sequence impl. |
| `impl SeqPointsTo<u8, PointsToByte>` (`PointsToUntyped`, `points_to_model.rs` / `points_to_ops.rs`) | `View`, `bytes`, `wf`, `stays_wf`, `lemma_ptrs_len_same_untyped` (renamed), `zero_sized<T>`, `split`, `split_ref`, `join` (wrappers over the `_basic` primitives); `join_ref`, `join_mut` (axioms); `split_mut` (proved in phase 3b); `is_disjoint_untyped` | |
| `impl PointsToByte` (renamed from `PointsToSingleton`) | `byte`, `is_disjoint_byte` (renamed from `is_disjoint_singleton`, in phase 1 with the type) | |
| `impl PointsToRaw` | everything in [`PointsToRaw` (phase 2c)](#pointstoraw-phase-2c) above (new) | Not a `PTPhys`. |
| free functions | `tracked_slice_index`, `tracked_slice_from_refs`, `tracked_ref` (new axioms, phase 3b); `allocate`, `deallocate` (ported, phase 2c, with `PointsToUntyped` in place of `PointsToRaw`; in `ptr_specs.rs`; `Dealloc` dropped) | |
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

## New axioms

All approved, including `allocate`, `deallocate` and `global_alloc_id`
([TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#new-axioms-and-axioms-with-bigger-changes)),
including `PointsTo::borrow_mut`.

Minor changes to existing axioms (`ptr_ref`, `ptr_ref2`, `ptr_ref2_ghost`, `mut_ref_to_shr_points_to`, `SharedReference::points_to`,
and the restored slice versions `ptr_ref_slice`, `ptr_ref2_slice_ghost`, `mut_ref_to_shr_points_to_slice`, `SharedReference<[T]>::points_to`)
are approved and in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#minor-changes-to-existing-trusted-specs),
and so are the strengthened `ptr_mut_ref`, `ptr_mut_ref_slice` and `ptr_mut_ref_str`,
the other `str` reference helpers (minor changes), the new `Seq` tracked operations
(`tracked_borrow_subrange`, `tracked_split_borrow_mut`),
and the borrowed-assembly axioms (`tracked_slice_index`, `tracked_slice_from_refs`, `tracked_ref`,
`PointsToUnaligned::from_raw_parts_ref`, M1, M3–M5, and the untyped joins `join_ref` / `join_mut`)
([TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#new-axioms-and-axioms-with-bigger-changes)).

**rustlib.** All new rustlib axioms are approved
([TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#new-axioms-and-axioms-with-bigger-changes)).

"New" means new relative to the `verify-rustlib` branch.
`abs_decode_slice` (already in `type_representation.rs`) is approved and listed in
[TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#new-axioms-and-axioms-with-bigger-changes).

### Borrowed-assembly axioms (phase 3b)

All approved and in
[TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#new-axioms-and-axioms-with-bigger-changes):
the shared ones (`tracked_slice_index`, `tracked_slice_from_refs`, `tracked_ref`,
`PointsToUnaligned::from_raw_parts_ref`) and the `&mut` ones (M1, M3–M5).

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
