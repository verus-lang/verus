# Design: `PointsToSingleValue` trait and a generic typed `SeqPointsTo` (level 3)

The specifications and trusted code to review:
a `PointsToSingleValue` trait implemented by `PointsTo` and `PointsToUnaligned` (for `T`, `[T]`, and `str` in rustlib),
one generic typed `SeqPointsTo` impl,
the slice ↔ sequence conversions,
and every new trusted item in vstd and rustlib.

Approved designs and specs are in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md).
The rationale, background and decisions are in [TYPED_POINTS_TO_NOTES.md](TYPED_POINTS_TO_NOTES.md);
the phases, spike results and risks in [TYPED_POINTS_TO_IMPL_PLAN.md](TYPED_POINTS_TO_IMPL_PLAN.md)
("phase N" below points there).

## Overview

The permission types table, the trait impls table, the API changes not visible in the specs,
the existing (unchanged) trusted specs, the five trait definitions, and the module layout are approved
and are in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md).

**Written once vs per type.**

Single-value permissions:

| Code | Written | What it contains |
|---|---|---|
| `PointsToPhys for PointsToUnaligned<_>` | per type | `ptr` (same shape each time), the `size` formula, and `wf_basic` (one call to the generic `wf_basic_unaligned`) |
| `PointsToProperties for PointsToUnaligned<T: ?Sized>` | once (generic) | `ptrs_len_same`, and the pointer-level lemmas, all delegating to the untyped bytes |
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
| structural `impl<T, P: PointsToProperties<A = T>>` (`points_to_model.rs` for the specs and M5, `points_to_ops.rs` for the rest) | every sequence, untyped or typed | the only code touching the fields: accessors, `thin_ptr`, constructors, borrows, `split_basic`, `join_basic`, `subrange_basic` |
| `PointsToUntyped` (`points_to_model.rs` for `View`, `bytes`, `wf` and the axioms; `points_to_ops.rs` for the proofs) | `SeqPointsTo<u8, PointsToByte>` | its `View`, `bytes`, `wf`, `split` / `join` / `split_ref` wrappers, and its axioms |
| typed `impl<T, P: PointsToSingleValueSized<A = T>>` (`points_to_collections.rs`) | sequences of `PointsTo<T>` or `PointsToUnaligned<T>` | the generic `View`, `wf`, bytes and values, the typed `split` / `join` / `subrange` wrappers, `subrange_mut`, untyped conversions, value operations, `is_disjoint_seqpt`; so `SeqPointsTo<T, PointsToUnaligned<T>>` gets the whole typed API |
| `PointsToUnaligned<T>`-specific (`points_to_collections.rs`) | `SeqPointsTo<T, PointsToUnaligned<T>>` | the sequence side of the slice ↔ sequence conversions (`as_slice_pt`, `as_slice_pt_mut`) and the borrowed constructors (the primary implementations); `into_aligned`, `as_aligned`, `as_aligned_mut` |
| `PointsTo<T>`-specific (`points_to_collections.rs`) | `SeqPointsTo<T, PointsTo<T>>` | `is_aligned`; the slice ↔ sequence conversions and borrowed constructors as compositions over the `PointsToUnaligned<T>` versions; `into_unaligned`, `as_unaligned`, `as_unaligned_mut` |


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

**Module layout.** Approved; see [Module layout](TYPED_POINTS_TO_APPROVED.md#module-layout).

**Still open.**

- Imports: likely a `raw_ptr` directory that re-exports everything
  (about 30 files import `raw_ptr_new` / `points_to_permissions` today, many in rustlib),
  with `points_to_collections` outside `points_to_model`'s subtree.
- Spike: Verus accepts private-field and `closed` spec access from the child module.
- The `allocate` / `deallocate` specs with `PointsToUntyped` (below, still with `PointsToRaw`).

## Specifications

Bodies are omitted except for spec fns and trusted code.
"Unchanged" means the contract is today's, apart from `size()` → `Self::size(self.ptr()@.metadata)`.

### Generic `PointsTo` trait impls and aligned/unaligned conversions

The trait definitions are in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#trait-definitions).

```rust
impl<T: ?Sized> PointsToSingleValueSpec for PointsTo<T> where PointsToUnaligned<T>: PointsToSingleValue<A = T> {
    // typed_value, bytes, metadata_matches delegate to self.pt_unaligned;
    open spec fn satisfies_alignment(addr: usize) -> bool {
        &&& PointsToUnaligned::<T>::satisfies_alignment(addr)
        &&& addr as nat % spec_align_of_val::<T>(arbitrary()) == 0
    }
    // wf: the trait's default body; the lemmas delegate.
}

impl<T: ?Sized> PointsToSingleValue for PointsTo<T> where PointsToUnaligned<T>: PointsToSingleValue<A = T> {
    // Everything delegates to self.pt_unaligned, except:
    // from_raw_parts: wraps the PointsToUnaligned result.
    // ptrs_len_same_valid, borrow, into_untyped, from_untyped, zero_sized: the trait's default bodies.
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

    /// Borrows a value as a valid typed value (phase 3b; proved from the `tracked_ref` axiom).
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

### `PointsToProperties` (changed in phase 1b)

The trait is in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#trait-definitions). Compared with today's:
contracts use `Self::size(self.ptr()@.metadata)` instead of `self.size()`;
`is_disjoint` compares `ptr()@.addr` instead of `ptr() as int`;
and `ptrs_len_same_valid` is renamed `ptrs_len_same` (pointer-level; the decoding version is
`PointsToSingleValue::ptrs_len_same_valid`), which `stays_wf_basic` now uses.

The lemma groups (`group_points_to_lemmas`, `group_points_to_collections_lemmas`) are in
[Module layout](TYPED_POINTS_TO_APPROVED.md#module-layout).

### `PointsToUnaligned` (phases 2, 2b; `str` in rustlib)

```rust
// The shared `wf_basic` body, written once.
impl<T: ?Sized> PointsToUnaligned<T> where PointsToUnaligned<T>: PointsToPhys<A = T> {
    pub open spec fn wf_basic_unaligned(self) -> bool {
        &&& self.pt_untyped().wf()
        &&& self.pt_untyped().len() == Self::size(self.ptr()@.metadata)
    }
}

// One per type; only `size` differs.
// `wf_basic` is in `PointsToPhys` so that `is_disjoint` can require it of `other`
// (a generic `other` bounded by `PointsToProperties` would be a trait cycle).
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
    open spec fn wf_basic(self) -> bool { self.wf_basic_unaligned() }
}
impl<T> PointsToPhys for PointsToUnaligned<[T]> {
    type A = [T];
    closed spec fn ptr(self) -> *mut [T] { /* same as above */ }
    open spec fn size(metadata: usize) -> nat { metadata as nat * size_of::<T>() }
    open spec fn wf_basic(self) -> bool { self.wf_basic_unaligned() }
}
// rustlib: impl PointsToPhys for PointsToUnaligned<str> { type A = str; ptr: same; size(len) = len; wf_basic: same }
// (Needs no `str` view. `PointsToPhys` is sealed by the crate-private `PointsToPhysSealed`;
// vstd's generic `impl<T: ?Sized> PointsToPhysSealed for PointsToUnaligned<T>` already covers `str`,
// and vstd is a module of rustlib's `core`, so rustlib can still write this impl.)

// One generic impl.
impl<T: ?Sized> PointsToProperties for PointsToUnaligned<T> where PointsToUnaligned<T>: PointsToPhys<A = T> {
    open spec fn ptrs_len_same(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& PointsToUntyped::ptrs_len_same(old.pt_untyped(), new.pt_untyped())
    }
    // is_nonnull, ptr_bounds, provenance_not_none, is_disjoint, stays_wf_basic: delegate to pt_untyped.
}

// PointsToSingleValueSpec items per impl (the operations' contracts are PointsToSingleValue's):
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
    open spec fn wf_basic(self) -> bool { self.pt_unaligned().wf_basic() }
}
impl<T: ?Sized> PointsToProperties for PointsTo<T> where PointsToUnaligned<T>: PointsToSingleValue<A = T> {
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
//   wf: default body. (Sketch in the generic PointsTo trait impls section.)
```

### `SeqPointsTo` (phase 1b; typed impl generalized in phase 3)

In `points_to_model.rs` and `points_to_ops.rs` (see [Module layout](TYPED_POINTS_TO_APPROVED.md#module-layout)):
the struct, its generic trait impls, the structural impl, and `PointsToUntyped`.

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

impl<T, P: PointsToProperties<A = T>> PointsToProperties for SeqPointsTo<T, P> {
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

    // from_seq_mut (M5, axiom): see [Borrowed-assembly axioms](#borrowed-assembly-axioms-phase-3b).
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

In `points_to_collections.rs`: the typed sequence.
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
    /// A `PointsToUnaligned<[T]>` is all valid or all empty,
    /// so a sequence with any empty element gives an empty slice permission.
    pub proof fn as_slice_pt(tracked &self) -> (tracked out: &PointsToUnaligned<[T]>)
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
    pub proof fn as_slice_pt_mut(tracked &mut self) -> (tracked out: &mut PointsToUnaligned<[T]>)
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

`allocate`, `deallocate` and `global_alloc_id` (trusted): see [Allocation](#allocation-phase-2c).

### `str` (rustlib)

Signatures only; rustlib fixes the details.
rustlib writes `PointsToPhys` (`Metadata<str>` is the byte length; `size(len) = len`;
`wf_basic` is `self.wf_basic_unaligned()`), `View`
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

The rustlib axioms (`abs_decode_str`, `TypedValue::<str>::as_bytes_mut`, the `str` reference helpers):
see [New rustlib axioms](#new-rustlib-axioms).

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
| `impl<T: ?Sized> PointsToUnaligned<T> where PointsToUnaligned<T>: PointsToSingleValue<A = T>` | `into_aligned`, `as_aligned` (new, generic); `as_aligned_mut` (new, generic, phase 3b: needs M4) | Contracts in [Generic `PointsTo` trait impls and aligned/unaligned conversions](#generic-pointsto-trait-impls-and-alignedunaligned-conversions). |
| `impl<T> PointsToUnaligned<T>` | `value`; `is_disjoint_unaligned<S>`. (removed: `wf`, `stays_wf`, `zero_sized`) | |
| `impl<T> PointsToUnaligned<[T]>` | `from_untyped_ref`, `from_untyped_with_value_ref`, `as_seq_pt`, `as_seq_pt_mut` (new, phase 4; the primary implementations). (removed in 2b: inherent `wf`) | |
| `impl<T: ?Sized> PointsTo<T>` | closed `pt_unaligned`; `typed_value`, `metadata`, `bytes`, `is_valid`, `is_empty` (open, delegating); `tracked_pt_unaligned`; `from_unaligned_mut` (new axiom M4) | |
| `impl<T: ?Sized> PointsTo<T> where PointsToUnaligned<T>: PointsToSingleValue<A = T>` | `into_unaligned`, `as_unaligned`, `as_unaligned_mut` (new, generic) | Contracts in [Generic `PointsTo` trait impls and aligned/unaligned conversions](#generic-pointsto-trait-impls-and-alignedunaligned-conversions). |
| `impl<T> PointsTo<T>` | `value`, `is_aligned`, `is_disjoint_pointsto<S>`. (removed: `wf`, `stays_wf`, `lemma_ptrs_len_same_valid`, `zero_sized`, `bytes_decode`, the untyped conversions, the value operations) | Removed ones are `PointsToSingleValue` / `PointsToSingleValueSized` methods. |
| `impl<T> PointsTo<[T]>` | `from_untyped_ref`, `from_untyped_with_value_ref`, `as_seq_pt`, `as_seq_pt_mut` (new, phase 4; compositions over the `PointsToUnaligned` versions). (removed: inherent `wf`) | |
| `impl<T, P: PointsToProperties<A = T>> SeqPointsTo<T, P>` (`points_to_model.rs` / `points_to_ops.rs`) | `seq_pt`, `len`, `spec_index`, `thin_ptr`; `tracked_seq_pt`, `tracked_seq_pt_mut`, `index_mut`, `from_seq`, `empty`, `into_seq` (moved here in phase 1); `split_basic`, `join_basic`, `subrange_basic` (new); `from_refs` (new), `from_seq_mut` (new axiom M5) | Structural; stated with `wf_basic`. The only code touching the fields. |
| `impl<T, P: PointsToSingleValueSized<A = T>> SeqPointsTo<T, P>` | `View` (generalized; `SeqPointsToData<T, P>`); `wf`, `bytes`, `bytes_inner`, `seq_typed_value`, `is_valid`, `is_empty`, `is_fully_empty`, `seq_value`, `is_valid_subrange`, `value_subrange`, `ptrs_len_same_valid`, `stays_wf`, `lemma_ptrs_len_same_valid`, `typed_value_equiv`, the byte lemmas, `split`, `join`, `subrange`, `subrange_mut` (proved in phase 3b), `zero_sized`, the untyped conversions, the value operations, `is_disjoint_seqpt` | Moved from `impl<T> SeqPointsTo<T, PointsTo<T>>` in phase 3. |
| `impl<T> SeqPointsTo<T, PointsTo<T>>` | `is_aligned`; `from_untyped_ref`, `from_untyped_with_value_ref`, `as_slice_pt`, `as_slice_pt_mut` (new, phase 4; compositions); `into_unaligned`, `as_unaligned`, `as_unaligned_mut` (new, phase 4) | |
| `impl<T> SeqPointsTo<T, PointsToUnaligned<T>>` | `into_aligned`, `as_aligned`, `as_aligned_mut`, `from_untyped_ref`, `from_untyped_with_value_ref`, `as_slice_pt`, `as_slice_pt_mut` (new, phase 4; the primary implementations) | |
| `impl SeqPointsTo<u8, PointsToByte>` (`PointsToUntyped`, `points_to_model.rs` / `points_to_ops.rs`) | `View`, `bytes`, `wf`, `stays_wf`, `lemma_ptrs_len_same_untyped` (renamed), `zero_sized<T>`, `split`, `split_ref`, `join` (wrappers over the `_basic` primitives); `join_ref`, `join_mut`, `split_mut` (proved in phase 3b); `is_disjoint_untyped` | |
| `impl PointsToByte` (renamed from `PointsToSingleton`) | `byte`, `is_disjoint_byte` (renamed from `is_disjoint_singleton`, in phase 1 with the type) | |
| `impl PointsToRaw` | everything in [`PointsToRaw` (phase 2c)](#pointstoraw-phase-2c) above (new) | Not a `PointsToPhys`. |
| free functions | `tracked_slice_index`, `tracked_slice_from_refs`, `tracked_collect_perm_refs`, `tracked_collect_perm_muts` (M6), `tracked_ref` (new axioms, phase 3b); `allocate`, `deallocate` (ported, phase 2c, with `PointsToUntyped` in place of `PointsToRaw`; placement open; `Dealloc` dropped) | |
| rustlib: `impl PointsToUnaligned<str>` | `into_bytes`, `from_bytes`, `as_bytes`, `as_bytes_mut` | |

## Trusted surface

Every trusted item the permissions rely on, after all phases:
`axiom fn`s, `external_body` functions and types, `assume_specification`s,
and `uninterp` specs that axioms constrain.
"Uses" names the main dependents.

**Existing, unchanged.** Approved; see [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#existing-unchanged-trusted-specs).

**Existing, removed (become proofs).**

| Item | File | Proved from |
|---|---|---|
| `PointsToUntyped::join_ref` | `points_to_permissions.rs` today (`points_to_model.rs` after the move) | `tracked_collect_perm_refs` (via `from_refs`), phase 3b |
| `PointsToUntyped::join_mut` | same | M5 + M6, phase 3b |
| `SeqPointsTo::subrange_mut` (on `SeqPointsTo<T, PointsTo<T>>`) | `points_to_permissions.rs` today (`points_to_collections.rs` after the move) | M5, phase 3b; the proof is in the typed generic impl, so it covers every typed sequence |
| `PointsToRaw`'s axioms (`empty`, `split`, `join`, `ptr_bounds`, `provenance_non_null`, `is_disjoint`, `into_typed*`, `into_raw`) | `raw_ptr_old.rs` (not in the current vstd) | `PointsToByte`'s axioms and `Map`'s tracked operations |

**New.** See [New axioms](#new-axioms).

**Dependency direction.**
`ptr_ref`, `ptr_mut_ref` and `mut_ref_to_shr_points_to` (in `raw_ptr_specs.rs`) take or produce `PointsTo<T>`,
and the restored slice versions `PointsTo<[T]>`;
`allocate` / `deallocate` use `PointsToUntyped`.
The phase 3b axioms are stated on `PointsToUnaligned`, `PointsTo`, `SeqPointsTo` and `TypedValue`.
All of these are in the two trusted files (see [Module layout](TYPED_POINTS_TO_APPROVED.md#module-layout)),
so no trusted code depends on `points_to_collections.rs`.

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
  M1/M2 drop values rather than duplicate them when the final state can't be distributed
  (and M1 starts empty when the elements are mixed, so their values are hidden, then dropped unless the slice ends valid),
  and M6's finals are only tied when the length is unchanged.
- **The reference helpers that produce a `PointsTo` ensure `wf()`**
  (`SharedReference::points_to`, `mut_ref_to_shr_points_to`, and their slice and `str` versions):
  a real reference is aligned and its bytes decode to its value.
  The Sized ones already do in the code.
- **The `ptr_ref` family requires `wf()`** (`ptr_ref`, `ptr_mut_ref`, `ptr_ref2`, `ptr_ref2_ghost`,
  and their slice and `str` versions; the Sized ones already in the code).
  `ptr_mut_ref` and its slice / `str` versions also ensure `final(perm).wf()`:
  they don't say the bytes stay the same, so this is what ties the final bytes to the final value.
- **`global_alloc_id`.** It replaces what `Dealloc` guaranteed implicitly:
  that the memory being freed came from the global allocator.
  Only `allocate` ensures a provenance has this id,
  so a `PointsToRaw` covering a stack variable's whole allocation can't be passed to `deallocate`.

## New axioms

Every new trusted item: the summary, then the full definitions.

**vstd.**

| Item | Planned file | What it states | Uses |
|---|---|---|---|
| `global_alloc_id` (`uninterp`) | with `allocate` (placement open) | The id of the global allocator's allocations. | `allocate` / `deallocate` |
| `allocate`, `deallocate` (`external_body`) | open | Allocation gives a `PointsToRaw` for the new range with a global-allocator provenance; deallocation consumes one covering the whole allocation. | heap allocation |

Minor changes to existing axioms (`ptr_ref`, `ptr_ref2`, `ptr_ref2_ghost`, `mut_ref_to_shr_points_to`, `SharedReference::points_to`,
and the restored slice versions `ptr_ref_slice`, `ptr_ref2_slice_ghost`, `mut_ref_to_shr_points_to_slice`, `SharedReference<[T]>::points_to`)
are approved and in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#minor-changes-to-existing-trusted-specs),
and so are the strengthened `ptr_mut_ref`, `ptr_mut_ref_slice` and `ptr_mut_ref_str`,
the other `str` reference helpers (minor changes), the new `Seq` tracked operations
(`tracked_borrow_subrange`, `tracked_split_borrow_mut`),
and the borrowed-assembly axioms (`tracked_slice_index`, `tracked_slice_from_refs`, `tracked_ref`,
`PointsToUnaligned::from_raw_parts_ref`, `tracked_collect_perm_refs`, and M1–M6)
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
`PointsToUnaligned::from_raw_parts_ref`, `tracked_collect_perm_refs`) and the `&mut` ones (M1–M6).

### Slice reference helpers (phase 4b)

Approved and in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md):
`ptr_mut_ref_slice` with `ptr_mut_ref` in
[New axioms and axioms with bigger changes](TYPED_POINTS_TO_APPROVED.md#new-axioms-and-axioms-with-bigger-changes),
and the rest in [Minor changes to existing trusted specs](TYPED_POINTS_TO_APPROVED.md#minor-changes-to-existing-trusted-specs).

### Allocation (phase 2c)

Ported from `raw_ptr_old.rs`, without `Dealloc`; placement open.

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

### New rustlib axioms

All approved and in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md):
`abs_decode_str`, `TypedValue::<str>::as_bytes_mut` and `ptr_mut_ref_str` in
[New axioms and axioms with bigger changes](TYPED_POINTS_TO_APPROVED.md#new-axioms-and-axioms-with-bigger-changes),
and the other `str` reference helpers in [Minor changes to existing trusted specs](TYPED_POINTS_TO_APPROVED.md#minor-changes-to-existing-trusted-specs).
