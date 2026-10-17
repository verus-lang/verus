# Plan: `PointsToSingleValue` trait and a generic typed `SeqPointsTo` (level 3)

This is the implementation plan for "level 3" from
[GENERALIZATION_ASSESSMENT.md](GENERALIZATION_ASSESSMENT.md#4-a-typedpointsto-trait-for-typed-permissions):
a `PointsToSingleValue` trait implemented by `PointsTo<T>` and `PointsToUnaligned<T>`, and one generic
`impl<T, P: PointsToSingleValueSized<A = T>> SeqPointsTo<T, P>` replacing most of today's
`impl<T> SeqPointsTo<T, PointsTo<T>>`. As a result, `SeqPointsTo<T, PointsToUnaligned<T>>` gets the
full typed API without duplicating the ~1000-line impl.

It is designed to fit together with [GHOST_METADATA_PLAN.md](GHOST_METADATA_PLAN.md), which adds
`metadata: Ghost<Metadata<T>>` to `PointsToUnaligned<T>` and gives `PointsTo<[E]>` /
`PointsToUnaligned<[E]>` their own trait impls. The trait is split so that those slice impls can
implement it too. See [Interaction with the ghost metadata plan](#interaction-with-the-ghost-metadata-plan)
for what changes in each plan and a combined order.

**Status.** Ghost metadata steps 1, 2 and 4 are done
(the `metadata` field,
the slice `PointsToPhys`/`PointsToProperties`/`View` impls,
and `abs_decode_slice`).
Ghost step 3 (empty slice permissions) was written as inherent functions,
then reverted and saved in [step3_slice_wip.patch](step3_slice_wip.patch).
This plan now comes before the rest of the ghost metadata plan,
so that the slice functions are trait impls with shared contracts,
and there are fewer separate specs to review.
Step 3's bodies move into the trait impls in phase 2b.
Phase 0 (the spike) is done; see [Phase 0 results](#phase-0-results).
See [Combined order](#combined-order).

Level 3 builds on level 1 (each contract written once in the trait). Level 2 (default method bodies)
is not needed and is left out for now; see [Deferred](#deferred).

Each phase ends with both builds green (`source/tools/build-expand-errors.sh` and
`source/tools/build-verify-core.sh`) and is meant to be a separate commit, so the work can stop after
any phase with the tree in a good state.

## Target design

### Impls and conversions

These are the permission types and conversions the design has to support.
Everything below is either already in, planned here or in the ghost metadata plan,
or (for `str`) done in rustlib after both plans.

**Trait impls.** `T` and `E` are `Sized`.

| Type | `PointsToPhys`, `PointsToProperties`, `View` | `PointsToSingleValue` | `PointsToSingleValueSized` | Where | When |
|---|---|---|---|---|---|
| `PointsToUnaligned<T>` | `PointsToPhys`: per type; `PointsToProperties`: generic (phase 2) | yes | yes | vstd | phase 2 |
| `PointsToUnaligned<[E]>` | `PointsToPhys`: per type (ghost step 2, done); `PointsToProperties`: generic (phase 2) | yes | no | vstd | phase 2b |
| `PointsToUnaligned<str>` | `PointsToPhys`: per type; `PointsToProperties`: generic | yes | no | rustlib | [after both plans](#str-in-rustlib) |
| `PointsTo<T>` | yes, generic | yes, generic | yes | vstd | phase 2 (generic from phase 2b) |
| `PointsTo<[E]>` | yes, generic | yes, generic | no | vstd, nothing slice-specific | phase 2b |
| `PointsTo<str>` | yes, generic | yes, generic | no | vstd, nothing `str`-specific | once rustlib adds `PointsToUnaligned<str>` |
| `SeqPointsTo<T, P>` (`A = [T]`) | yes (exists, generic) | no | no | vstd | pointer becomes `*mut [T]` in phase 1b |
| `PointsToByte` (`A = u8`) | yes (exists) | no | no | vstd | — |
| `PointsToRaw` | no (no single pointer) | no | no | vstd | phase 2c ([`PointsToRaw`](#pointstoraw)) |

`FixedSize` is removed in phase 1b
(see [`SeqPointsTo`'s pointer and sizes](#seqpointstos-pointer-and-sizes)).

"Generic" means the impl is one
`impl<T: ?Sized> ... for PointsTo<T> where PointsToUnaligned<T>: PointsToSingleValue<A = T>`
that delegates to `self.pt_unaligned`
(see [The generic `PointsTo` impl](#the-generic-pointsto-impl)).
For `PointsToUnaligned`, only `PointsToPhys` (which has the size formula) is per type;
`PointsToProperties` is one generic impl
(see [`wf_basic` and `wf`](#wf_basic-and-wf)).
So `PointsToSingleValue` has four written impls:
three real ones for `PointsToUnaligned` (`T` and `[E]` in vstd, `str` in rustlib)
and one generic delegating one for `PointsTo`.
`PointsToSingleValueSized` has two, both for Sized `T`.

`SeqPointsTo` doesn't implement the typed traits;
it is generic over its element permission `P` instead.
The typed sequence API comes from these inherent impls:

| Sequence type | Inherent impl | When |
|---|---|---|
| `SeqPointsTo<T, PointsTo<T>>` | generic `impl<T, P: PointsToSingleValueSized<A = T>> SeqPointsTo<T, P>`, plus a small `PointsTo<T>`-specific impl (`is_aligned`, slice conversions) | phase 3 |
| `SeqPointsTo<T, PointsToUnaligned<T>>` | the same generic impl | phase 3 (it exists from then on) |
| `PointsToUntyped` = `SeqPointsTo<u8, PointsToByte>` (was `SeqPointsTo<[u8], PointsToSingleton>`) | its own impl | — |

There is no `SeqPointsTo<str, _>`.
A `str` permission is indexed by converting it to `PointsTo<[u8]>`
and then to `SeqPointsTo<u8, PointsTo<u8>>`.
This supersedes [points_to_str_wip.rs](points_to_str_wip.rs).

**Conversions.**

| From ↔ to | Owned | `&` | `&mut` | Where | When |
|---|---|---|---|---|---|
| `PointsTo<T>` ↔ `PointsToUnaligned<T>` | yes | yes | yes (to unaligned: field borrow; to aligned: M4) | vstd, generic aligned/unaligned impl | phase 2; `as_aligned_mut` in ghost step 6 |
| `PointsTo<[E]>` ↔ `PointsToUnaligned<[E]>` | yes | yes | yes (same) | vstd, same generic impl | phase 2b; `as_aligned_mut` in ghost step 6 |
| `PointsTo<str>` ↔ `PointsToUnaligned<str>` | yes | yes | yes (same) | vstd, same generic impl, no `str`-specific code | once rustlib adds `PointsToUnaligned<str>` |
| `SeqPointsTo<T, PointsTo<T>>` ↔ `SeqPointsTo<T, PointsToUnaligned<T>>` | yes | yes | yes | vstd | phase 4 |
| `PointsTo<[E]>` ↔ `SeqPointsTo<E, PointsTo<E>>` | no | yes | yes | vstd | ghost step 6 |
| `PointsToUnaligned<[E]>` ↔ `SeqPointsTo<E, PointsToUnaligned<E>>` | no | yes | yes | vstd | phase 4 |
| `PointsToUnaligned<str>` ↔ `PointsToUnaligned<[u8]>` | yes | yes | yes | rustlib | [after both plans](#str-in-rustlib) |
| `PointsTo<str>` ↔ `PointsTo<[u8]>` | yes | yes | yes | rustlib, via the unaligned versions and the aligned/unaligned conversions | [after both plans](#str-in-rustlib) |
| `PointsToRaw` ↔ `PointsToUntyped` (a contiguous range) | yes | no | no | vstd | phase 2c |
| `PointsToRaw` ↔ any `PointsToSingleValue` / `SeqPointsTo`, through `PointsToUntyped` | yes (into typed: empty value) | no | no | vstd | phase 2c |

Owned conversions between a slice permission and a `SeqPointsTo` are left out on purpose:
valid slice permissions come from real `&[E]` / `&mut [E]` references
(see the ghost metadata plan, step 6).

### Two traits

`PointsToSingleValue` is implemented by every `PointsTo` and `PointsToUnaligned` impl
(`T`, `[E]`, and `str` in rustlib).
Each of these holds a single typed value, one `TypedValue<A>` for the whole region,
in contrast to `SeqPointsTo`, which holds one element permission (and value) per element.
`PointsToSingleValueSized` adds what only fixed-size, `Sized` permissions can provide,
and is what typed `SeqPointsTo` elements need.

There is no `FixedSize` supertrait:
with `PointsToPhys::size` taking the metadata, a permission with `A: Sized` has constant size `size(())`,
so "fixed size" is just `PointsToPhys<A: Sized>`
(see [`SeqPointsTo`'s pointer and sizes](#seqpointstos-pointer-and-sizes)).
That is also all `SeqPointsTo` needs of its elements, so `PointsToByte` needs no extra trait.

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

/// Defines the typed data tracked by a `PointsTo` permission
/// to a single, possibly-valid value of type `Self::A`,
/// along with well-formedness properties, constructors, and conversions.
pub trait PointsToSingleValue: PointsToProperties {
    /// The (possibly-valid) typed value that this permission tracks.
    spec fn typed_value(self) -> TypedValue<Self::A>;

    /// The abstract bytes of the memory that this permission tracks.
    spec fn bytes(self) -> Seq<AbstractByte>;

    /// Well-formedness: the ptr-level conditions (`wf_basic`),
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

    /// Well-formedness implies the ptr-level well-formedness.
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

Notes on the block above (plan context, not code documentation):

- `PointsToPhys::size` takes the metadata instead of `self` from phase 1b on.
- There is no `PointsToSingleValue::metadata()`: it is always `self.ptr()@.metadata`
  (see [`wf_basic` and `wf`](#wf_basic-and-wf)).
- Default bodies, written once in the trait:
  `wf` and `ptrs_len_same_valid` (spec);
  `borrow`, `into_untyped`, `from_untyped`, `zero_sized`,
  and in `PointsToSingleValueSized` `take`, `put`, `copy`, `copy_typed_value`, `from_untyped_with_value` (proof).
  The proof defaults only call other trait methods and follow from their contracts
  ([phase 0, item 13](#phase-0-pending-checks)).
  Each impl writes the rest:
  the lemmas (they need `wf` to unfold, which a default spec body only does at concrete types; phase 0, item 12),
  and the operations that touch the fields
  (`borrow_typed_value`, `take_typed_value`, `put_typed_value`, `into_raw_parts`, `from_raw_parts`,
  `as_untyped`, `as_untyped_mut`).
- `PointsToProperties` has only the byte-level `ptrs_len_same`;
  using one name in both traits would make method calls ambiguous.
- `metadata_matches`: decoding doesn't fix a slice's length when `size_of::<E>() == 0`;
  for `str`, UTF-8 validity is part of `abs_decode::<str>`.
- `satisfies_alignment` for `PointsTo` uses `spec_align_of_val::<T>(arbitrary())`:
  it takes `T: ?Sized`, and for every supported type the alignment doesn't depend on the value
  (`layout_of_sized`, `layout_of_slices`, `layout_of_str`; not true for `dyn`, which is out of scope).
  It includes the unaligned `satisfies_alignment`, which the generic impl can't see is `true`,
  so that `from_untyped` / `zero_sized` are provable by delegation.
- `lemma_metadata_matches` is for generic code over `P: PointsToSingleValueSized`,
  which can't unfold `metadata_matches` but has to establish it
  when calling `put_typed_value`, `from_raw_parts`, or anything relying on `ptrs_len_same_valid`
  (e.g. the typed `SeqPointsTo`'s `put_typed_value_subrange` and `from_untyped_with_typed_value`).
  The impls don't need it: `metadata_matches` unfolds to `true` at the concrete type.
- `A: Sized` in `PointsToSingleValueSized` is an associated type bound,
  so it is implied wherever `P: PointsToSingleValueSized` (phase 0, item 3).
- `lemma_ptrs_len_same_valid` is broadcast through a group naming
  `PointsToSingleValue::lemma_ptrs_len_same_valid` (phase 0, item 6).
- `as_aligned` is proved with `shr_ref_struct_wrap` (phase 0, item 8);
  `as_aligned_mut` is M4 (`PointsTo::from_unaligned_mut`, ghost step 6) plus the `wf` facts;
  `as_unaligned_mut` is a plain field borrow (`&mut self.pt_unaligned`), so it is provable now.
- Renamed from today's names: `borrow` (was `borrow_value`),
  `into_raw_parts` (was `into_untyped_with_typed_value`).
  `from_raw_parts` is new; `from_untyped` and `from_untyped_with_value` are special cases of it.

With the stored metadata, every constructor and conversion in ghost step 3 has one contract
for both `T` and `[E]`.
The only per-type pieces are `PointsToPhys::size` and the `PointsToUnaligned` bodies.
Sized callers pass `()` as the metadata to `from_untyped`.
If phase 0 shows that `Metadata<Self::A>` doesn't normalize to `()` for Sized `A` in generic code,
the fallback is the earlier split:
`from_untyped(pt_untyped)` and `zero_sized` in `PointsToSingleValueSized`,
and inherent slice versions taking `len`.

Why the split falls here:

- **By value vs by reference.** `take`, `put`, `copy` and `from_untyped_with_value` move an `A`, which
  needs `A: Sized`. Everything on `TypedValue<A>` and `&A` works for unsized `A`.
- **Size.** Contracts in `PointsToSingleValue` use `Self::size(self.ptr()@.metadata)`,
  since a slice's size depends on its metadata.
  Only `PointsToSingleValueSized` uses the constant `Self::size(())`.
- **Constructors.** `from_untyped` and `zero_sized` need to know the size before a permission exists.
  The metadata argument (or the pointer's metadata) gives it through `PointsToPhys::size`,
  so they can be in `PointsToSingleValue` rather than split by sizedness.

Contract conventions:

- `PointsToSingleValue` contracts say `wf()` (the trait's), not `wf_basic()`:
  decoding, `metadata_matches` and alignment are in `wf`, not `wf_basic`
  (see [`wf_basic` and `wf`](#wf_basic-and-wf)).
  `wf_basic()` is for `PointsToProperties`' own byte-level lemmas and `SeqPointsTo`'s structural functions.
- Decoding is stated with a new `?Sized` spec `TypedValue::value_ref(&self) -> &T` (`&*self->0`),
  so `abs_decode(bytes, tv.value_ref())` reads the same for `T` and `[E]`. This generalizes the
  existing `TypedValue<[T]>::value() -> &[T]`.
- Pointer facts between a permission and its `PointsToUntyped` are stated on `@.addr` and
  `@.provenance`, not with an `as *mut T` cast, so they read the same for every impl.
- Otherwise the contracts are today's `PointsTo<T>` contracts, with `size_of::<T>()` replaced by
  `Self::size(self.ptr()@.metadata)` / `Self::size(())` and alignment replaced by `Self::satisfies_alignment`.

### `wf_basic` and `wf`

With the ghost `metadata` field, everything about a `PointsToUnaligned<T>` except its size formula
can be written once for any `T: ?Sized`.
So `wf_basic` keeps only the type-independent, byte-level conditions,
and the type-dependent ones move to `PointsToSingleValue::wf`.

**The pointer, generically.** `PointsToUnaligned<T>`'s pointer is built from the stored metadata:

```rust
spec fn ptr(self) -> *mut T {
    ptr_mut_from_data::<T>(PtrData {
        addr: self.pt_untyped().ptr()@.addr,
        provenance: self.pt_untyped().ptr()@.provenance,
        metadata: self.metadata(),
    })
}
```

The slice impl already does this ([points_to_permissions.rs:922](points_to_permissions.rs));
the Sized impl currently uses `pt_untyped().ptr() as *mut T`.
Then `self.ptr()@.metadata == self.metadata()` holds by `axiom_ptr_mut_from_data`
(`ptr_mut_from_data(data)@ == data`),
so the `metadata() == ptr()@.metadata` clause leaves `wf_basic`,
and `PointsToSingleValue` has no `metadata()` (contracts use `ptr()@.metadata`).
The closed inherent `PointsToUnaligned::metadata()` stays as the field accessor.

`PointsToPhys` stays one small impl per type (`A`, this `ptr`, and the `size` formula),
since a generic `size` would need the `?Sized` size-from-metadata spec
that the ghost metadata plan's decision 3 avoids.

**`wf_basic`, generically.** One `impl<T: ?Sized> PointsToProperties for PointsToUnaligned<T>
where PointsToUnaligned<T>: PointsToPhys<A = T>`:

```
wf_basic() = pt_untyped().wf() && pt_untyped().len() == Self::size(self.ptr()@.metadata)
```

The byte count stays in `wf_basic`,
since the generic `ptr_bounds` / `provenance_not_none` / `is_disjoint` delegate to `pt_untyped`
and need it to equal the permission's size.
`PointsToProperties`' byte-level `ptrs_len_same` (renamed from `ptrs_len_same_valid`)
is "same pointer, and `pt_untyped`'s `ptrs_len_same`",
and `stays_wf_basic` follows from `PointsToUntyped::stays_wf`.
The decode part moves to `PointsToSingleValue::ptrs_len_same_valid`, which `stays_wf` uses.
This impl calls only `PointsToPhys` (a supertrait), never `PointsToSingleValue`:
a supertrait impl calling a subtrait impl is rejected as recursion
(phase 0 follow-up, `size_cycle.rs`),
which is why decoding can't stay in `wf_basic` once the impl is generic.

**`wf`.** In `PointsToSingleValue`, for every `PointsToUnaligned` impl:

```
wf() = wf_basic()
    && Self::satisfies_alignment(self.ptr()@.addr)
    && (self.is_valid() ==> abs_decode(self.bytes(), self.typed_value().value_ref())
                         && Self::metadata_matches(self.typed_value().value_ref(), self.ptr()@.metadata))
```

The two hooks differ in when they're used:

- `satisfies_alignment(addr)` depends only on the address,
  so constructors (`from_untyped`, `zero_sized`) can require it before a permission exists,
  and `lemma_satisfies_alignment_offset` can reason about sequence element addresses.
  `true` for `PointsToUnaligned`; alignment for `PointsTo`.
- `metadata_matches(value, metadata)` constrains only valid permissions:
  `true` for Sized `T`;
  `value@.len() == metadata` for `[E]`
  (needed explicitly, since decoding doesn't fix the length when `size_of::<E>() == 0`);
  `true` for `str`, since UTF-8 validity is part of `abs_decode::<str>`.
  So for the planned impls, only slices use it.

`wf() ==> satisfies_alignment(ptr()@.addr)` and `wf() ==> wf_basic()` hold by definition
(`satisfies_alignment_of_wf`, `lemma_wf_basic`).
The generic `PointsTo` uses the same default body;
since it delegates `wf_basic`, `bytes`, `typed_value` and `metadata_matches`,
that amounts to `pt_unaligned.wf()` plus `PointsTo`'s alignment.
`wf` can be written once as a trait default body,
but it doesn't unfold in generic code,
so generic code uses the trait lemmas, proved per impl
([phase 0, item 12](#phase-0-pending-checks)).

**Consequences:**

- The contract convention flips to `wf()` (see [Contract conventions](#two-traits)).
- The generic typed `SeqPointsTo` requires its elements' `P::wf()`,
  since its byte lemmas need decoding.
  The structural phase 1 functions keep `wf_basic`.
- This revisits the ghost metadata plan's decision 2 ("leave the Sized impls alone"):
  the Sized pointer changes from a cast to `ptr_mut_from_data`.
  Contracts like `out.ptr() == pt_untyped.ptr() as *mut T` stay true,
  but proving them goes through `axiom_ptr_mut_from_data` and `ptrs_mut_eq_sized`.
  Restating them on `@.addr` / `@.provenance` (the convention above) avoids most of that.
- Existing per-type `wf_basic` clauses move:
  for Sized `T`, the decode clause and the metadata clause;
  for `[E]` (ghost step 2), the decode clause, the length clause (now `metadata_matches`)
  and the metadata clause.

### `SeqPointsTo`'s pointer and sizes

**The pointer.** `SeqPointsTo<T, P>`'s pointer becomes `*mut [T]` (so `A = [T]`),
with `T` always the element type and `P: PointsToProperties<A = T>`:

| Sequence | Before | After |
|---|---|---|
| typed | `SeqPointsTo<T, PointsTo<T>>`, `ptr: *mut T` (first element) | same type, `ptr: *mut [T]` |
| untyped | `PointsToUntyped = SeqPointsTo<[u8], PointsToSingleton>`, `ptr: *mut [u8]` | `PointsToUntyped = SeqPointsTo<u8, PointsToByte>`, same pointer |

`wf_basic` gains `self.ptr()@.metadata == self.len()`
(today only `PointsToUntyped::wf()` has it).
Element addresses are still `self.ptr()@.addr + i * P::size(())`.

**Sizes.** With the length in every permission's pointer,
size is a function of the pointer's metadata for every permission,
so `PointsToPhys::size` takes the metadata instead of `self`,
and it is the only size function:

- `PointsToPhys::size(metadata: Metadata<Self::A>) -> nat`, the only per-type formula:
  `size_of::<T>()`, `len * size_of::<E>()`, `len` (`str`), `1` (`PointsToByte`),
  and `len * P::size(())` for `SeqPointsTo<T, P>`.
- A permission's own size is written `Self::size(p.ptr()@.metadata)`
  (`Self::size(())` for Sized `A`).
  There is no `size(self)`, so nothing to keep in sync and no lemma relating them.
  Existing `self.size()` / `other.size()` uses change to this form,
  including in `PointsToProperties`' contracts (`ptr_bounds`, `provenance_not_none`, `is_disjoint`).
- `FixedSize` is removed: `const_size()` was always `size(())`,
  which is well-defined exactly when `A: Sized` (the only metadata is `()`).
  Bounds `P: PointsToProperties + FixedSize` become `P: PointsToProperties<A: Sized>`
  (or `<A = T>` with Sized `T`), `P::const_size()` becomes `P::size(())`,
  and `size_eq_const_size` calls go away.
- `PointsToSingleValue` has no size function of its own,
  and the inherent `size_of_metadata` helper from the earlier version isn't needed.

For a `SeqPointsTo`, the size is `metadata * P::size(())`, which equals `len() * P::size(())`
under `wf_basic`.
Today `size` is `len() * const_size()` unconditionally,
so proofs that use it without `wf_basic` (if any) need the metadata clause.

**The thin pointer.** `SeqPointsTo<T, PointsTo<T>>` gets

```rust
/// The pointer to the first element, without the length.
/// For code that doesn't care about the slice metadata.
pub open spec fn thin_ptr(self) -> *mut T {
    ptr_mut_from_data::<T>(PtrData { addr: self.ptr()@.addr, provenance: self.ptr()@.provenance, metadata: () })
}
```

(moved to the generic typed impl in phase 3 with everything else).
Contracts that today use the `*mut T` pointer can mostly use `thin_ptr` instead,
which keeps them as short as they are now:

- `from_seq(r, ptr: *mut T)`, `empty(ptr: *mut T)`, `zero_sized(ptr: *mut T, len)`
  keep taking a thin pointer, build the slice pointer inside,
  and ensure `out.thin_ptr() == ptr` (plus `out.len()`, which they already state).
- `split` / `join`: `first.thin_ptr() == self.thin_ptr()`, `joined.thin_ptr() == self.thin_ptr()`;
  `subrange` / `subrange_mut`: `sub.thin_ptr()` at the offset address.
  With `wf_basic`'s metadata clause, `thin_ptr()` and `len()` determine `ptr()`.
- `from_untyped(pt_untyped, len)`: `out.thin_ptr()` has `pt_untyped`'s address and provenance
  (this replaces `out.ptr() == pt_untyped.ptr() as *mut T`,
  which would be wrong for `*mut [T]`, since an `as` cast keeps the element count, not the byte count).
- Element facts: `self[i].ptr()@.addr == self.thin_ptr()@.addr + i * size_of::<T>()`.

**Where it pays off.** The slice ↔ sequence conversions (ghost step 6)
can state `out.ptr() == self.ptr()`, since both sides now have a `*mut [E]`;
`FixedSize` and two of the three size functions are gone;
and `SeqPointsTo`'s `T` means the element type everywhere.

**Unchanged:** the byte and value specs and lemmas, the value operations,
`wf`/`is_aligned`/`stays_wf` (address-only), the `as_untyped`/`into_untyped` family
(already builds a `*mut [u8]` with metadata `len * size_of::<T>()`),
and every `final(self).ptr() == old(self).ptr()` clause.

### `PointsToRaw`

Ported from `raw_ptr_old.rs` (line 3245),
where it is an `external_body` struct with uninterpreted `provenance()` / `dom()` and every operation an axiom.
Here it is built from byte permissions,
so its operations are proved from `PointsToByte`'s axioms.
It is the permission `allocate` returns and `deallocate` consumes,
for an arbitrary (not necessarily contiguous) set of addresses with one provenance.

```rust
pub tracked struct PointsToRaw {
    bytes: Map<int, PointsToByte>,
    provenance: Ghost<Provenance>,
}
// #[verifier::type_invariant]:
//   bytes.dom().finite(),
//   forall a in bytes.dom(): bytes[a].ptr()@.addr == a && bytes[a].ptr()@.provenance == provenance,
//   plus the per-byte bounds facts (start_addr <= a < start_addr + alloc_len, provenance != None),
//   established when bytes are added (from PointsToByte::ptr_bounds / provenance_not_none).
```

The public specs stay as in `raw_ptr_old.rs`:
`provenance()`, `dom() = bytes.dom()`, `is_range`, `contains_range`.
`PointsToRaw` doesn't implement `PointsToPhys`: it has no single pointer.

| Old axiom | New proof |
|---|---|
| `empty(provenance)` | `Map::tracked_empty()` |
| `split(range)` | `tracked_remove_keys(range)` |
| `join(other)` (same provenance) | `tracked_union_prefer_right` (the domain is the union either way) |
| `ptr_bounds`, `provenance_non_null` | from the type invariant. (The old `ptr_bounds` allowed `a == start + alloc_len`; the new one gives `a < start + alloc_len`.) |
| `is_disjoint(other)` | if some `a` is in both domains, borrow both bytes at `a` and use `PointsToByte::is_disjoint_singleton` for a contradiction. One address, so no quantified tracked calls. |
| `into_typed<V>`, `into_typed_slice<V>`, `into_typed_seq<V>` | `into_untyped(start, len) -> PointsToUntyped` (remove the range's bytes in address order into a `Seq`, then `from_seq` with a thin pointer), then `from_untyped`. One generic `into_typed::<P: PointsToSingleValue>(start, metadata)` covers `T`, `[E]` and `str`; `SeqPointsTo` uses its own `from_untyped`. |
| `PointsTo<V>::into_raw`, `PointsTo<[V]>::into_raw`, `SeqPointsTo::into_raw` | `p.into_untyped()`, then `PointsToRaw::from_untyped` (insert each byte at its address). One generic `from_typed::<P: PointsToSingleValue>(p)`. |

Differences from the old version:

- **Byte contents are kept.**
  Each `PointsToByte` has its `AbstractByte`,
  so `into_typed` gives a permission whose typed value is empty but whose bytes are the real ones,
  and `PointsTo<V>::into_raw` no longer needs `is_uninit()` (the old version asked "Do we need memory to be uninitialized?").
  `PointsToRaw` itself still gives no read access.
- **Still trusted:** `PointsToByte`'s axioms,
  and `allocate` / `deallocate` / `Dealloc` (also not in the current vstd; ported from `raw_ptr_old.rs` 3683-3809 unchanged),
  which create and consume the permission.

### The generic `PointsTo` impl

`PointsTo<X>` is a `PointsToUnaligned<X>` plus an alignment requirement,
so its trait impls are pure delegation to `self.pt_unaligned`,
apart from alignment (`align_of::<T>()` vs `align_of::<E>()`).
The existing `PointsToPhys`/`PointsToProperties` impls for `PointsTo<T>` and `PointsTo<[T]>`
are already line-for-line the same apart from that and `size`.
Rather than one copy per type (three, one of them in rustlib),
`PointsTo` gets one generic impl of each trait,
bounded by `PointsToUnaligned<T>: PointsToSingleValue<A = T>`,
with the alignment written as `spec_align_of_val::<T>(arbitrary())`
(see `satisfies_alignment` in [Two traits](#two-traits)).
Proofs that need the concrete alignment use the existing layout axioms.

- `PointsToPhys`: `ptr` and `size` delegate.
- `PointsToProperties`: `wf_basic` is `pt_unaligned().wf_basic()`; the rest delegates.
  Alignment is in `PointsToSingleValue::wf` (see [`wf_basic` and `wf`](#wf_basic-and-wf)).
- `View`: `PointsToData` is already `?Sized`.
- `PointsToSingleValue`: delegates, except `satisfies_alignment` and the constructors, which wrap the
  `PointsToUnaligned` result.
  Spec delegations must name the trait function
  (`<PointsToUnaligned<T> as PointsToSingleValue>::typed_value(self.pt_unaligned)`),
  not the inherent `?Sized` one of the same name:
  in generic code the inherent and trait versions aren't known to be equal,
  so the trait lemmas' postconditions wouldn't connect (phase 0, item 5).
- `PointsToSingleValueSized` stays a per-`T` impl (only Sized `T` has it).

This does not conflict with the ghost metadata plan's decision 3
(one `PointsToUnaligned` impl per unsized type):
that decision avoids a `?Sized` size-from-metadata spec,
and the generic `PointsTo` impl never computes a size itself.

The fallback, if phase 0, item 9, fails, is one delegating impl per type,
as for `PointsToPhys`/`PointsToProperties` today.

### The generic `SeqPointsTo`

- `wf()` becomes generic:
  `self.wf_basic() && P::satisfies_alignment(self.ptr()@.addr) && forall i. self[i].wf()`
  (elements' `PointsToSingleValue::wf` includes decoding and their own alignment;
  the base pointer's alignment is kept separately, since an empty sequence has no elements to carry it).
  For `PointsTo<T>` this unfolds to today's definition plus the element `wf`.
  `SeqPointsTo::wf_basic` (its generic `PointsToProperties` impl, which also covers `PointsToByte`)
  stays on the elements' `wf_basic`, since `PointsToByte` has no `PointsToSingleValue::wf`;
  its byte-level lemmas (`ptr_bounds`, `is_disjoint`, ...) only need that.
  So element `wf` comes with the sequence's `wf()`, not its `wf_basic()`.
- `PointsToUntyped = SeqPointsTo<u8, PointsToByte>` keeps its own
  impl: `PointsToByte` doesn't implement `PointsToSingleValueSized`, so the impls don't overlap
  (confirmed in [phase 0, item 10](#phase-0-pending-checks)).
  `wf` and `bytes` stay inherent in both impls, not `PointsToProperties` methods.
- Everything in today's `impl<T> SeqPointsTo<T, PointsTo<T>>` moves into the generic impl, with
  `size_of::<T>()` → `P::size(())`, alignment arithmetic → `P::lemma_satisfies_alignment_offset`, and direct
  field access (`elt.pt_unaligned.val`) → trait calls (`elt.take_typed_value()`).
- What stays specific to `PointsTo<T>`: `is_aligned` (unfolds `satisfies_alignment`), possibly `View` (see
  [Open decisions](#open-decisions)), and the slice conversions from the ghost metadata plan's step 6
  (see below).

### Specifications

Every new or changed specification, for review.
`PointsToSingleValue`, `PointsToSingleValueSized`, `PointsToPhys` and the generic aligned/unaligned conversions
are in [Two traits](#two-traits) and aren't repeated here.
The borrowed slice ↔ sequence conversions for `PointsTo` and their axioms (M1-M6 and the rest)
are specified in the ghost metadata plan, step 6;
after phase 1b their pointer clauses become `out.ptr() == self.ptr()`.
Bodies are omitted except for spec fns.
"Unchanged" means the contract is today's, apart from `size()` → `Self::size(self.ptr()@.metadata)`.

#### `TypedValue` (phase 2)

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

#### `PointsToProperties` (changed in phase 1b)

`size()` takes the metadata, and pointer comparisons use `@.addr` instead of `ptr() as int`.

```rust
pub trait PointsToProperties: PointsToPhys {
    spec fn wf_basic(self) -> bool;

    proof fn is_nonnull(tracked &self)
        requires
            self.wf_basic(),
        ensures
            self.ptr()@.addr != 0,
    ;

    proof fn ptr_bounds(tracked &self)
        requires
            self.ptr()@.provenance.is_some(),
            self.wf_basic(),
        ensures
            self.ptr()@.addr as int >= self.ptr()@.provenance.unwrap().start_addr(),
            self.ptr()@.addr + Self::size(self.ptr()@.metadata)
                <= self.ptr()@.provenance.unwrap().start_addr() + self.ptr()@.provenance.unwrap().alloc_len(),
    ;

    proof fn provenance_not_none(tracked &self)
        requires
            Self::size(self.ptr()@.metadata) != 0,
            self.wf_basic(),
        ensures
            self.ptr()@.provenance != Provenance::None,
    ;

    proof fn is_disjoint<OtherPointsToPerm: PointsToPhys>(tracked &mut self, tracked other: &OtherPointsToPerm)
        requires
            Self::size(self.ptr()@.metadata) != 0,
            OtherPointsToPerm::size(other.ptr()@.metadata) != 0,
            self.wf_basic(),
        ensures
            *old(self) == *final(self),
            final(self).ptr()@.addr + Self::size(final(self).ptr()@.metadata) <= other.ptr()@.addr
                || other.ptr()@.addr + OtherPointsToPerm::size(other.ptr()@.metadata) <= final(self).ptr()@.addr,
    ;

    /// Renamed from `ptrs_len_same_valid`, which moves to `PointsToSingleValue` (with decoding).
    /// Byte-level: same pointer, and same underlying pointers and length.
    spec fn ptrs_len_same(old: Self, new: Self) -> bool;

    proof fn stays_wf_basic(old: Self, new: Self)
        requires
            old.wf_basic(),
            Self::ptrs_len_same(old, new),
        ensures
            new.wf_basic(),
    ;
}
```

`group_points_to_permissions_lemmas` contains `PointsToSingleValue::lemma_ptrs_len_same_valid`
(in place of `PointsTo::lemma_ptrs_len_same_valid`),
the typed `SeqPointsTo::lemma_ptrs_len_same_valid`,
and `PointsToUntyped`'s lemma (renamed `lemma_ptrs_len_same_untyped`).

#### `PointsToUnaligned` (phases 2, 2b; `str` in rustlib)

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
impl<E> PointsToPhys for PointsToUnaligned<[E]> {
    type A = [E];
    closed spec fn ptr(self) -> *mut [E] { /* same as above */ }
    open spec fn size(metadata: usize) -> nat { metadata as nat * size_of::<E>() }
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
// PointsToUnaligned<[E]>  (same)               (same)                    v@.len() == m       true
// PointsToUnaligned<str>  (same)               (same)                    true                true   (rustlib; UTF-8 is in abs_decode::<str>)
// wf: the trait's default body. For T and [E], this replaces today's per-type wf_basic clauses.
```

#### `PointsTo` (generic; phase 2, widened in phase 2b)

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
//   wf: default body. (Sketch in Two traits.)
```

#### `SeqPointsTo` (phase 1b; typed impl generalized in phase 3)

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

impl SeqPointsTo<u8, PointsToByte> {   // PointsToUntyped
    pub open spec fn wf(self) -> bool { self.wf_basic() }   // the metadata clause moved to wf_basic
    // everything else unchanged
}

// Typed sequence. Phase 1b: on SeqPointsTo<T, PointsTo<T>>.
// Phase 3: moved to impl<T, P: PointsToSingleValueSized<A = T>>, with PointsTo<T> -> P,
//          size_of::<T>() -> P::size(()), PointsTo::<T>::satisfies_alignment -> P::satisfies_alignment.
impl<T> SeqPointsTo<T, PointsTo<T>> {
    pub open spec fn wf(self) -> bool {
        &&& self.wf_basic()
        &&& PointsTo::<T>::satisfies_alignment(self.ptr()@.addr)
        &&& forall|i| 0 <= i < self.len() ==> #[trigger] self[i].wf()
    }

    /// The pointer to the first element, without the length.
    /// For code that doesn't care about the slice metadata.
    pub open spec fn thin_ptr(self) -> *mut T {
        ptr_mut_from_data::<T>(PtrData { addr: self.ptr()@.addr, provenance: self.ptr()@.provenance, metadata: () })
    }

    /// The byte-level `ptrs_len_same`, plus each element's `PointsToSingleValue::ptrs_len_same_valid`.
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

    pub proof fn from_seq(tracked r: Seq<PointsTo<T>>, ptr: *mut T) -> (tracked s: Self)
        requires
            forall|i: int| 0 <= i < r.len() ==> #[trigger] r[i].wf(),
            forall|i: int| 0 <= i < r.len() ==> {
                &&& (#[trigger] r[i]).ptr()@.provenance == ptr@.provenance
                &&& r[i].ptr()@.addr == ptr@.addr + i * size_of::<T>()
            },
            ptr@.addr != 0,
            PointsTo::<T>::satisfies_alignment(ptr@.addr),
            ptr_addr_in_bounds(ptr),
            r.len() <= usize::MAX,   // new: the length is now pointer metadata
        ensures
            s.seq_pt() == r,
            s.thin_ptr() == ptr,     // was s.ptr() == ptr
            s.wf(),
    ;

    pub proof fn empty(ptr: *mut T) -> (tracked s: Self)
        requires
            ptr@.addr != 0,
            PointsTo::<T>::satisfies_alignment(ptr@.addr),
            ptr_addr_in_bounds(ptr),
        ensures
            s.seq_pt() == Seq::<PointsTo<T>>::empty(),
            s.thin_ptr() == ptr,
            s.wf(),
    ;

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

    /// Still an axiom until ghost step 6 (then proved from M5).
    pub axiom fn subrange_mut(tracked &mut self, i: nat, j: nat) -> (tracked r: &mut Self)
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
    // `SeqPointsToData::ptr` becomes `*mut [T]` (open decision 1 on generalizing `View`).
    // into_untyped*, as_untyped*, the value operations, the byte lemmas: unchanged,
    // except `borrow_value_subrange` is renamed `borrow_subrange`
    // (matching `take_subrange` / `put_subrange` / `copy_subrange` and `PointsToSingleValue::borrow`).
}

// Phase 1, generic over both sequences (replaces is_disjoint_seqpt and is_disjoint_untyped).
impl<T, P: PointsToProperties<A = T>> SeqPointsTo<T, P> {
    pub proof fn is_disjoint_seq<S, Q: PointsToProperties<A = S>>(tracked &mut self, tracked other: &SeqPointsTo<S, Q>)
        requires
            self.wf_basic(),
            self.len() != 0,
            other.len() != 0,
            P::size(()) != 0,
            Q::size(()) != 0,
        ensures
            *old(self) == *final(self),
            final(self).ptr()@.addr + final(self).len() * P::size(()) <= other.ptr()@.addr
                || other.ptr()@.addr + other.len() * Q::size(()) <= final(self).ptr()@.addr,
    ;
}
```

#### Unaligned sequence conversions (phase 4)

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

#### Unaligned slice ↔ sequence conversions (phase 4)

The aligned versions (ghost step 6) have the same contracts with `PointsTo`.

```rust
impl<E> SeqPointsTo<E, PointsToUnaligned<E>> {
    /// A `PointsToUnaligned<[E]>` is all valid or all empty.
    pub proof fn as_slice_pt(tracked &self) -> (tracked out: &PointsToUnaligned<[E]>)
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

    pub proof fn as_slice_pt_mut(tracked &mut self) -> (tracked out: &mut PointsToUnaligned<[E]>)
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

impl<E> PointsToUnaligned<[E]> {
    pub proof fn as_seq_pt(tracked &self) -> (tracked out: &SeqPointsTo<E, PointsToUnaligned<E>>)
        requires
            self.wf(),
        ensures
            out.ptr() == self.ptr(),
            out.bytes() == self.bytes(),
            self.typed_value().is_valid() ==> out.is_valid() && out.seq_value() == self.typed_value().value_ref()@,
            self.typed_value().is_empty() ==> out.is_fully_empty(),
            out.wf(),
    ;

    pub proof fn as_seq_pt_mut(tracked &mut self) -> (tracked out: &mut SeqPointsTo<E, PointsToUnaligned<E>>)
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

// Dealloc, allocate, deallocate: ported unchanged from raw_ptr_old.rs (trusted).
```

#### `str` (rustlib)

Signatures only; rustlib fixes the details.
UTF-8 validity is part of `abs_decode::<str>`, so "the bytes decode as a `str`" is the UTF-8 condition.

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
            self.typed_value().is_valid() ==> out.typed_value().value_ref()@ == self.typed_value().value_ref().spec_bytes(),
            out.wf(),
    ;

    /// Valid only if the bytes decode as a `str` (i.e. are valid UTF-8); otherwise empty.
    pub proof fn from_bytes(tracked p: PointsToUnaligned<[u8]>) -> (tracked out: PointsToUnaligned<str>)
        requires
            p.wf(),
        ensures
            out.ptr()@.addr == p.ptr()@.addr,
            out.ptr()@.provenance == p.ptr()@.provenance,
            out.ptr()@.metadata == p.ptr()@.metadata,
            out.bytes() == p.bytes(),
            out.typed_value().is_valid() <==> p.typed_value().is_valid() && exists|s: &str| abs_decode::<str>(p.bytes(), s),
            out.typed_value().is_valid() ==> out.typed_value().value_ref().spec_bytes() == p.typed_value().value_ref()@,
            out.wf(),
    ;

    // as_bytes(&self) -> &PointsToUnaligned<[u8]>: as into_bytes (new axiom: &TypedValue<str> -> &TypedValue<[u8]>).
    // as_bytes_mut(&mut self) -> &mut PointsToUnaligned<[u8]>: initially as into_bytes; finally,
    //   if final(out).wf() and final(out).ptr() == out.ptr(), then final(self) is as from_bytes(final(out)).
    // PointsTo<str> versions: through the aligned/unaligned conversions (alignment 1).
}
```

### Type-specific inherent impls

What stays outside the traits, by impl block, after all phases.
"(new)" is added by this plan or the ghost metadata plan; "(removed)" lists what moves into a trait;
everything else exists today.

| Impl block | Functions | Notes |
|---|---|---|
| `impl<T: ?Sized> TypedValue<T>` | `is_valid`, `is_empty`; `value_ref` (new); `valid_ref` (new, ghost step 6) | |
| `impl<T> TypedValue<T>` | `value`, `tracked_copy` | Sized: by-value access |
| `impl<T> TypedValue<[T]>` | `value` (-> `&[T]`); `from_elems_mut`, `into_elems_mut` (new axioms M1/M2, ghost step 6) | |
| `impl<T: ?Sized> PointsToUnaligned<T>` | closed accessors `typed_value`, `pt_untyped`, `metadata`; `bytes`, `is_valid`, `is_empty` (inline); `tracked_pt_untyped`; `from_raw_parts_ref` (new axiom, ghost step 6), `from_raw_parts_mut` (new axiom M3) | The inherent `typed_value`/`bytes` coexist with the trait's (phase 0, item 5). |
| `impl<T: ?Sized> PointsToUnaligned<T> where PointsToUnaligned<T>: PointsToSingleValue<A = T>` | `into_aligned`, `as_aligned` (new, generic); `as_aligned_mut` (new, generic, ghost step 6: needs M4) | Contracts in [Two traits](#two-traits). |
| `impl<T> PointsToUnaligned<T>` | `value`; `is_disjoint_unaligned<S>`. (removed: `wf`, `stays_wf`, `zero_sized`) | |
| `impl<E> PointsToUnaligned<[E]>` | `as_seq_pt`, `as_seq_pt_mut` (new, phase 4). (removed in 2b: inherent `wf`) | |
| `impl<T: ?Sized> PointsTo<T>` | closed `pt_unaligned`; `typed_value`, `metadata`, `bytes`, `is_valid`, `is_empty` (open, delegating); `tracked_pt_unaligned`; `from_unaligned_mut` (new axiom M4) | |
| `impl<T: ?Sized> PointsTo<T> where PointsToUnaligned<T>: PointsToSingleValue<A = T>` | `into_unaligned`, `as_unaligned`, `as_unaligned_mut` (new, generic) | Contracts in [Two traits](#two-traits). |
| `impl<T> PointsTo<T>` | `value`, `is_aligned`, `is_disjoint_pointsto<S>`. (removed: `wf`, `stays_wf`, `lemma_ptrs_len_same_valid`, `zero_sized`, `bytes_decode`, the untyped conversions, the value operations) | Removed ones are `PointsToSingleValue` / `PointsToSingleValueSized` methods. |
| `impl<E> PointsTo<[E]>` | `from_untyped_ref`, `from_untyped_with_value_ref`, `as_seq_pt`, `as_seq_pt_mut` (new, ghost step 6). (removed: inherent `wf`) | |
| `impl<T, P: PointsToProperties<A = T>> SeqPointsTo<T, P>` | `seq_pt`, `len`, `spec_index`; `tracked_seq_pt`, `tracked_seq_pt_mut`, `index_mut`, `from_seq`, `empty`, `into_seq` (moved here in phase 1); `is_disjoint_seq` (new, phase 1); `from_refs` (new), `from_seq_mut` (new axiom M5) | Structural; stated with `wf_basic`. |
| `impl<T, P: PointsToSingleValueSized<A = T>> SeqPointsTo<T, P>` | `wf`, `thin_ptr`, `bytes`, `bytes_inner`, `seq_typed_value`, `is_valid`, `is_empty`, `is_fully_empty`, `seq_value`, `is_valid_subrange`, `value_subrange`, `ptrs_len_same_valid`, `stays_wf`, `lemma_ptrs_len_same_valid`, `typed_value_equiv`, the byte lemmas, `split`, `join`, `subrange`, `zero_sized`, the untyped conversions, the value operations | Moved from `impl<T> SeqPointsTo<T, PointsTo<T>>` in phase 3. |
| `impl<T> SeqPointsTo<T, PointsTo<T>>` | `is_aligned`; `subrange_mut` (axiom until ghost step 6); `View` (open decision 1); `from_untyped_ref`, `from_untyped_with_value_ref`, `as_slice_pt`, `as_slice_pt_mut` (new, ghost step 6); `into_unaligned`, `as_unaligned`, `as_unaligned_mut` (new, phase 4) | |
| `impl<T> SeqPointsTo<T, PointsToUnaligned<T>>` | `into_aligned`, `as_aligned`, `as_aligned_mut`, `as_slice_pt`, `as_slice_pt_mut` (new, phase 4) | |
| `impl SeqPointsTo<u8, PointsToByte>` (`PointsToUntyped`) | `View`, `bytes`, `wf`, `stays_wf`, `lemma_ptrs_len_same_untyped` (renamed), `zero_sized<T>`, `split`, `split_ref`, `join`; `join_ref`, `join_mut` (axioms today, proved in ghost step 6); `split_mut` (commented out, proved from M5/M6) | `is_disjoint_untyped` replaced by `is_disjoint_seq`. |
| `impl PointsToByte` (renamed from `PointsToSingleton`) | `byte`, `is_disjoint_singleton` | |
| `impl PointsToRaw` | everything in [`PointsToRaw` (phase 2c)](#pointstoraw-phase-2c) above (new) | Not a `PointsToPhys`. |
| free functions | `tracked_slice_from_refs`, `tracked_collect_perm_refs`, `tracked_collect_perm_muts` (M6), `tracked_ref` (new, ghost step 6); `allocate`, `deallocate`, `Dealloc` (ported, phase 2c) | |
| rustlib: `impl PointsToUnaligned<str>` | `into_bytes`, `from_bytes`, `as_bytes`, `as_bytes_mut` | |

## Phases

### Phase 0: spike the risky Verus features

In a scratch file, not `points_to_permissions.rs`, check the things this plan relies on but hasn't
verified:

1. A trait `proof fn` taking `tracked &mut self`, implemented on one type with a real body and on a
   wrapper type by delegating to a field (`self.pt_unaligned.take()`), with `final(self)` contracts.
   No existing test covers `tracked &mut self` in traits.
2. A generic impl bounded by an associated-type equality, `P: PointsToSingleValueSized<A = T>` (where `A`
   comes from `PointsToPhys`), and that `P::A` and `T` are interchangeable in specs.
3. How to say `Self::A: Sized` for `PointsToSingleValueSized`'s by-value methods: a trait-level
   `where Self::A: Sized` (may not be implied at use sites), per-method `where Self::A: Sized`, or
   relying on the generic `SeqPointsTo` impl's `T` being `Sized` together with `A = T`.
4. A trait method with a `where Self::A: Copy` bound.
5. Name resolution when a trait spec fn (`bytes`, `typed_value`) has the same name as the existing
   inherent `?Sized` spec fn on `PointsTo`/`PointsToUnaligned`. The inherent one should win in
   method syntax on concrete types and the trait one in generic code. If that causes trouble, rename
   the trait methods (e.g. `tp_bytes`).
6. Whether a trait `proof fn` can be `broadcast`. `PointsTo::lemma_ptrs_len_same_valid` is in
   `group_points_to_permissions_lemmas` today. If trait methods can't be broadcast, keep a small
   inherent broadcast wrapper per type that calls the trait lemma.

7. `Metadata<Self::A>` in trait signatures:
   that it normalizes to `()` in the `PointsTo<T>` impl and to `usize` in the `PointsTo<[E]>` impl,
   and that a generic caller with `P: PointsToSingleValueSized<A = T>` can pass `()`.
   (Generic Sized code already writes `metadata: ()` in `PtrData<T>`, e.g. `view_reverse_for_eq_sized`.)
   Also check the non-ghost build, where `Metadata<T>` is `FakeMetadata<T>`.
8. A generic inherent impl `impl<T: ?Sized> PointsToUnaligned<T> where PointsToUnaligned<T>:
   PointsToSingleValue<A = T>` for the aligned/unaligned conversions,
   including `shr_ref_struct_wrap` in `as_aligned` with generic `T`.
9. Generic trait impls `impl<T: ?Sized> Trait for PointsTo<T> where PointsToUnaligned<T>:
   PointsToSingleValue<A = T>` (for `PointsToPhys`, `PointsToProperties`, `View` and `PointsToSingleValue`),
   instantiated at a Sized `T` and at `[E]`.
   Check that Verus accepts the `where` clause on a trait impl,
   that the alignment resolves correctly for each instantiation,
   and that a constructor (`from_untyped`) can call `into_aligned` from inside the impl
   without a recursion or cycle error.
   Also check that `FixedSize for PointsTo<T>` (Sized only) can sit next to the generic impls.

If (1) or (2) fails, stop and revisit the design before continuing.
If (7) or (8) fails, use the fallbacks in [Two traits](#two-traits).
If (9) fails, use the fallback in [The generic `PointsTo` impl](#the-generic-pointsto-impl).

#### Phase 0 results

The spike is in [source/phase0_spike/](../phase0_spike/),
run with `source/tools/verify-spike-all.sh` (each file separately, against the built vstd).
It uses mock `PointsToUnaligned`/`PointsTo`/`SeqPointsTo` types
that implement vstd's real `PointsToPhys`, `PointsToProperties` and `FixedSize`,
with a Sized and a slice `PointsToUnaligned` impl,
and `PointsToSingleValue`/`PointsToSingleValueSized` as in [Two traits](#two-traits).
A deliberately wrong call (aligned slice `zero_sized` without the alignment precondition)
was checked to fail, so the passing results aren't vacuous.

| Item | Result | File | Notes |
|---|---|---|---|
| 1. `tracked &mut self` trait methods, delegation to a field, `final(self)` | works | `main.rs` | `take_typed_value`, `take` delegate through `self.pt_unaligned`. |
| 2. `P: PointsToSingleValueSized<A = T>`, `P::A` and `T` interchangeable | works | `main.rs` | Generic `take_at`/`copy_at` on the mock sequence, instantiated with aligned and unaligned elements. |
| 3. Expressing `Self::A: Sized` | use the associated type bound | `item3_assoc_bound.rs`, `item3_trait_where.rs` | `PointsToSingleValueSized: PointsToSingleValue<A: Sized> + FixedSize` works and is implied at use sites, even with only `P: PointsToSingleValueSized`. A trait-level `where Self::A: Sized` is not implied (E0277) unless the use site states `A = T`. Per-method `where` also works but is noisier. |
| 4. `where Self::A: Copy` on a trait method | works | `main.rs` | `copy_typed_value`, called from generic code with `T: Copy`. |
| 5. Trait spec fn with the same name as an inherent `?Sized` one | works, with a caveat | `main.rs` | In an impl, `self.typed_value()` resolves to the inherent fn (no recursion), and on concrete types the two are provably equal. In generic code they aren't known equal, so generic delegations must name the trait fn. No rename needed. |
| 6. Broadcast trait lemmas | works, through the trait path | `item6_*.rs` | A trait can declare a `broadcast proof fn`. A broadcast group must name the trait method (`Lemmas::lemma_good`); it then fires for every impl, in generic and concrete code. Naming the impl path (`Mock::lemma_good`) is "not found", and `broadcast use P::lemma` / `<P as Lemmas>::lemma` in a generic fn is E0401. The inherent-wrapper fallback also works. Impl-side broadcast fns warn about missing triggers (harmless; the trigger is on the declaration). |
| 7. `Metadata<Self::A>` in trait signatures | works (ghost build) | `main.rs` | Impls can write `()` (Sized) and `usize` (slices) directly; a generic Sized caller passes `()` (`P::size_for(())`). The non-ghost build (`FakeMetadata`) wasn't tested here; these are all spec/proof signatures, which the existing `?Sized` `PointsToUnaligned::metadata` already has. |
| 8. Generic aligned/unaligned impl, incl. `shr_ref_struct_wrap` | works | `main.rs` | Bounded only by `PointsToUnaligned<T>: PointsToSingleValue<A = T>`; checked at a Sized type and a slice. |
| 9. Generic trait impls for `PointsTo` | works | `main.rs` | Generic `PointsToPhys`/`PointsToProperties`/`PointsToSingleValue` for `PointsTo<T: ?Sized>`, next to Sized-only `FixedSize`/`PointsToSingleValueSized`. The alignment, `spec_align_of_val::<T>(arbitrary())`, reduces to `align_of::<u32>()` / `align_of::<u16>()` at `u32` / `[u16]` via `layout_of_sized` / `layout_of_slices` (and to 1 for `str` via `layout_of_str`, `align_unsized.rs`), so no `align()` hook is needed. `zero_sized` calls `into_aligned` inside the impl without a cycle error. Requires `satisfies_alignment` to include the unaligned `satisfies_alignment` (see [Two traits](#two-traits)). |

Follow-up checks:

| Check | Result | File | Notes |
|---|---|---|---|
| Alignment without an `align()` hook | works | `align_unsized.rs`, `main.rs` | `spec_align_of_val::<T>(arbitrary())` reduces to `align_of::<T>()`, `align_of::<E>()`, 1 for `str` via the existing layout axioms. |
| `size` defined as `Self::size_for(..)` (cross-trait) | rejected | `size_cycle.rs` | "recursive function must have a decreases clause" on `size`. |
| `size`/`const_size`/`size_for` through an inherent `size_of_metadata` | works | `size_inherent.rs` | `lemma_size` and `lemma_const_size` have empty proofs, and generic code gets `x.size() == P::const_size()` from them. |

Other findings:

- **Impl type-parameter names must match the trait's.**
  Renaming `is_disjoint<OtherPointsToPerm>` to `is_disjoint<O>` in an impl
  crashes Verus ("generated ill-typed AIR code": undeclared `OtherPointsToPerm`).
  The existing impls already use the trait's names; keep doing so.
- **Not covered by the spike:**
  verification time and trigger behavior at real scale (phase 3's risk),
  broadcast cyclicity with `group_vstd_default`,
  and the non-ghost build.
- The spike was written before the [`SeqPointsTo` pointer change](#seqpointstos-pointer-and-sizes),
  so it still uses `FixedSize`, `size(self)` and a per-trait `size_for`.
  The size rows above are superseded by that design; the other results don't depend on it.

#### Phase 0 pending checks

These cover the [`SeqPointsTo` pointer change](#seqpointstos-pointer-and-sizes),
[`PointsToRaw`](#pointstoraw) and [`wf_basic` and `wf`](#wf_basic-and-wf).

10. **The new `SeqPointsTo` shape.**
    - *Done:* a generic inherent impl `impl<T, P: Typed<A = T>> Seq2<T, P>`
      next to `impl Seq2<u8, Byte>` (where `Byte` doesn't implement `Typed`),
      both defining `wf`, is accepted, with no E0592 (`seq_overlap.rs`).
      The struct needs `#[verifier::reject_recursive_types(T)]`
      once `T` appears in the bound `P: Phys<A = T>`;
      the real `SeqPointsTo` will need it too.
    - *Not run (routine):* the full struct with `ptr: Ghost<*mut [T]>`,
      `PointsToPhys::size(len) = len * P::size(())`, and the `thin_ptr` contracts.
11. **`PointsToRaw`'s representation.**
    - *Known:* `#[verifier::type_invariant]` works on tracked structs
      (`raw_ptr.rs` line 370, with `use_type_invariant` in proof fns).
    - *Not run (routine):* the recursive helper that removes a contiguous range's bytes,
      in address order, into a `Seq`.
12. **Generic `PointsToProperties` and `wf` for `PointsToUnaligned`.**
    - *Done:* trait default bodies for `spec` and `proof` fns are accepted on this branch
      (the trait needs `Sized`, which `PointsToPhys` has),
      and a concrete type that doesn't override sees the default.
      But a default spec body does **not** unfold in generic code,
      nor inside a default proof body (`default_methods.rs`),
      presumably because an impl may override it.
      So `PointsToSingleValue::wf` may be a default body (written once),
      but generic code gets its facts only from the trait lemmas
      (`bytes_decode`, `satisfies_alignment_of_wf`, `lemma_wf_basic`),
      which need per-impl proofs (empty, since `wf` unfolds at the concrete type).
    - *Not run (low risk, same pattern as item 9):*
      `impl<T: ?Sized> PointsToProperties for PointsToUnaligned<T> where PointsToUnaligned<T>: PointsToPhys<A = T>`
      next to per-type `PointsToPhys` impls with the `ptr_mut_from_data` pointer.
13. **Default proof bodies that call other trait methods.**
    *Known (no spike needed):* default proof bodies that only call other trait methods
    and use their contracts are fine. This covers the proof defaults in the trait
    (`borrow`, `into_untyped`, `from_untyped`, `zero_sized`, `take`, `put`, `copy`, `copy_typed_value`,
    `from_untyped_with_value`). It differs from what `default_methods.rs` tested,
    a default proof body that needed a default *spec* body to unfold (which fails).

### Phase 1: structural generalization (assessment section 1, groups 1 and 3)

Independent of the trait, and the generic typed impl needs these.

- Move `tracked_seq_pt`, `tracked_seq_pt_mut`, `index_mut`, `from_seq`, `empty`, `into_seq` into the
  generic `impl<T, P> SeqPointsTo<T, P>`, stated with `wf_basic()` and `P::size(())`
  (after phase 1b; `P::const_size()` if phase 1 lands first).
  Keep thin `wf()` wrappers on `SeqPointsTo<T, PointsTo<T>>` for now; phase 3 removes them.
- Replace `is_disjoint_seqpt` and `PointsToUntyped::is_disjoint_untyped` with one generic
  `is_disjoint_seq<S: ?Sized, Q>`.
- Rename `PointsToSingleton` to `PointsToByte` (and `PointsToSingletonData` to `PointsToByteData`),
  so it isn't confused with `PointsToSingleValue`.
  Purely mechanical; also update the docs that mention it
  (`PORTING_STATUS.md`, `POINTS_TO_MIGRATION.md`, `GENERALIZATION_ASSESSMENT.md`).
- Update call sites and verify.

### Phase 1b: `SeqPointsTo`'s slice pointer, `size(metadata)`, no `FixedSize`

The design is in [`SeqPointsTo`'s pointer and sizes](#seqpointstos-pointer-and-sizes).
Run [phase 0 check 10](#phase-0-pending-checks) first.
Independent of the new traits; it changes existing ones.

1. `PointsToPhys::size(self)` becomes `size(metadata: Metadata<Self::A>)` in every existing impl:
   `PointsToSingleton`/`PointsToByte` (`1`), `PointsToUnaligned<T>` / `PointsTo<T>` (`size_of::<T>()`),
   `PointsToUnaligned<[T]>` / `PointsTo<[T]>` (`len * size_of::<T>()`),
   `SeqPointsTo` (`len * P::size(())`).
   Rewrite `x.size()` uses as `X::size(x.ptr()@.metadata)`,
   starting with `PointsToProperties`' own contracts.
2. `SeqPointsTo`: `ptr: Ghost<*mut [T]>`, bound `P: PointsToProperties<A = T>`
   (with `#[verifier::reject_recursive_types(T)]`),
   `wf_basic` gains `ptr()@.metadata == len()`;
   `PointsToUntyped = SeqPointsTo<u8, PointsToByte>`, and its `wf()` loses the clause that moved.
3. Remove `FixedSize`: `P::const_size()` → `P::size(())`; drop the `size_eq_const_size` calls.
4. Add `thin_ptr` to `SeqPointsTo<T, PointsTo<T>>`,
   and restate the typed impl's pointer contracts with it
   (list in [`SeqPointsTo`'s pointer and sizes](#seqpointstos-pointer-and-sizes)):
   `from_seq`, `empty`, `zero_sized`/`zero_sized_helper`, `split`, `join`,
   `subrange`, `subrange_mut`, `from_untyped`, `from_untyped_with_typed_value`, `untyped_mut_join`,
   and the `View` / `SeqPointsToData` `ptr` field.
5. Update the plan's ghost step 6 contracts and `from_refs`
   (see [What this plan changes in the ghost metadata plan](#what-this-plan-changes-in-the-ghost-metadata-plan)).
6. rustlib uses these types; update its call sites in the same change (not visible from this repo).
7. Verify both builds.

### Phase 2: introduce the traits and the Sized impls

Assumes ghost metadata step 1 (the field) is already in, so moved bodies include `metadata` from the
start (see the combined order).

1. Add `TypedValue::value_ref` (`?Sized`). Restate the existing decode clauses with it where that
   simplifies things. `TypedValue<T>::value()` and `TypedValue<[T]>::value()` can stay as they are.
2. Add `PointsToSingleValue` and `PointsToSingleValueSized` (next to `PointsToProperties` in `points_to.rs`, or at
   the top of `points_to_permissions.rs`).
3. `PointsToUnaligned`'s pointer and `PointsToProperties` ([`wf_basic` and `wf`](#wf_basic-and-wf)):
   build `ptr` from the stored metadata in both `PointsToPhys` impls (Sized and slice),
   and replace the two `PointsToProperties` impls with one generic impl
   whose `wf_basic` is only `pt_untyped().wf()` and the byte count.
   The decode, length and metadata clauses leave `wf_basic`:
   for Sized `T` into `PointsToSingleValue::wf` (next step);
   for slices into the existing inherent `PointsToUnaligned<[T]>::wf` until phase 2b.
   Restate Sized pointer contracts on `@.addr` / `@.provenance` where the cast-based proofs break.
   Rename `PointsToProperties::ptrs_len_same_valid` to `ptrs_len_same` (byte-level, no decoding)
   in every impl, including `SeqPointsTo`'s and `PointsToUntyped`'s
   (whose lemma becomes `lemma_ptrs_len_same_untyped`);
   the decoding version becomes `PointsToSingleValue::ptrs_len_same_valid` in the next step,
   and the typed `SeqPointsTo` gets an inherent `ptrs_len_same_valid` over its elements'.
4. `impl<T> PointsToSingleValue + PointsToSingleValueSized for PointsToUnaligned<T>`: real bodies. Most are today's
   `PointsTo<T>` bodies with `self.pt_unaligned.` removed.
   `wf` is the formula in [`wf_basic` and `wf`](#wf_basic-and-wf), `metadata_matches` is `true`,
   `satisfies_alignment` is `true`, and `from_untyped` loses its alignment precondition.
5. `impl<T> PointsToSingleValue for PointsTo<T>` (Sized only for now):
   one-line delegations to `self.pt_unaligned`,
   except `satisfies_alignment(addr)` (`PointsToUnaligned::<T>::satisfies_alignment(addr) && addr as nat % spec_align_of_val::<T>(arbitrary()) == 0`)
   and `from_untyped` (`PointsToUnaligned::from_untyped(u, m).into_aligned()`).
   Write it in the shape of [the generic impl](#the-generic-pointsto-impl),
   so phase 2b only has to widen `impl<T>` to `impl<T: ?Sized> ... where ...`.
   It can't be generic yet: a `?Sized` `PointsToSingleValue` impl needs `?Sized` supertrait impls,
   and those would drop `PointsTo<[T]>`'s existing ones until `PointsToUnaligned<[E]>` has the trait.
6. `impl<T> PointsToSingleValueSized for PointsTo<T>`: delegations, plus `lemma_satisfies_alignment_offset`,
   which is the `lemma_mul_mod_noop_right`/`lemma_add_mod_noop`/`layout_of_sized` argument
   currently inlined in `split`/`subrange`/`from_untyped_with_typed_value`.
7. Remove the inherent `PointsTo<T>` / `PointsToUnaligned<T>` versions of the moved functions,
   including the inherent `wf` and `stays_wf`:
   inherent fns win over trait fns at concrete types (phase 0, item 5),
   and the old inherent `wf` (= `wf_basic`) would shadow the trait's `wf` with a different meaning.
   Keep `is_aligned`, `value`, `is_disjoint_pointsto`
   (`into_unaligned`/`as_unaligned` move to the generic conversion impl).
8. Callers outside the module need the traits in scope for method syntax. Grep for uses of the moved
   methods (`raw_ptr_new.rs`, `shared_reference.rs`, ...), and either import the traits there or
   export them through the prelude.
9. If any trait method ends up on the dependency path of a broadcast group, its proofs use the
   specific groups `{group_raw_ptr_axioms, group_layout_axioms, group_seq_axioms}`, never
   `group_vstd_default`, to avoid cyclicity errors (as the existing trait impls already do).
10. Verify. At this point `SeqPointsTo<T, PointsTo<T>>` is unchanged and just calls trait methods on
   its elements.

### Phase 2b: slice impls (ghost steps 3 and 5)

1. `impl<E> PointsToSingleValue for PointsToUnaligned<[E]>`,
   reusing the bodies from the ghost step 3 code,
   which was reverted and saved in [step3_slice_wip.patch](step3_slice_wip.patch).
   Its `size(len)` (`len * size_of::<E>()`) is already there from phase 1b,
   `satisfies_alignment` is `true`, and `metadata_matches(v, len)` is `v@.len() == len`.
   The inherent `PointsToUnaligned<[T]>::wf` from phase 2, step 3, is replaced by the trait's `wf`.
2. Make the `PointsTo` impls generic ([The generic `PointsTo` impl](#the-generic-pointsto-impl)):
   widen phase 2's `PointsToSingleValue for PointsTo<T>` to `T: ?Sized`,
   and replace the per-type `PointsToPhys`/`PointsToProperties`/`View` impls
   for `PointsTo<T>` and `PointsTo<[T]>` with one generic impl each.
   `PointsTo<[E]>` then has the trait with no slice-specific code.

`borrow` (ghost step 5's `borrow_value`, renamed) is a trait method, so it comes with this phase.
The inherent slice functions and the `_slice`-suffixed lemmas from step 3 are dropped,
and so is the `PointsTo::<T>::zero_sized` turbofish it needed.

### Phase 2c: `PointsToRaw`

The design is in [`PointsToRaw`](#pointstoraw). Run [phase 0 check 11](#phase-0-pending-checks) first.

1. The struct, its type invariant, and the specs `provenance`, `dom`, `is_range`, `contains_range`.
2. `empty`, `split`, `join`, `ptr_bounds`, `provenance_non_null`, `is_disjoint`.
3. `from_untyped(PointsToUntyped) -> PointsToRaw` and `into_untyped(start, len) -> PointsToUntyped`.
   These only need phase 1b, so 1-3 can land earlier.
4. The generic `into_typed::<P: PointsToSingleValue>` / `from_typed::<P: PointsToSingleValue>`,
   and `SeqPointsTo` versions (needs phases 2 and 2b).
5. Port `Dealloc`, `allocate` and `deallocate` (trusted, unchanged).
6. Add the trusted items to `POINTS_TO_AXIOMS.md` and note the removed `PointsToRaw` axioms.

### Phase 3: generic typed `SeqPointsTo`

Move the `SeqPointsTo<T, PointsTo<T>>` impl to `impl<T, P: PointsToSingleValueSized<A = T>>
SeqPointsTo<T, P>`, in this order (each step depends on the previous ones):

1. **Specs:** `wf` (generic definition above), `bytes`/`bytes_inner`, `seq_typed_value`, `is_valid*`,
   `is_empty`, `is_fully_empty`, `seq_value`, `value_subrange`, `stays_wf`. Drop the phase 1 `wf()`
   wrappers.
2. **Byte lemmas:** `typed_value_equiv`, `bytes_len_helper`/`bytes_len`, `bytes_subrange`,
   `bytes_equiv`, `bytes_subrange_equiv`, `bytes_decode_helper`/`bytes_decode`, `bytes_inner_ext`.
   These need `P::bytes_decode` plus `P::size(())` for each element's byte length. Expect most
   of the trigger fixup work here, since `P::bytes()` is opaque in generic code.
3. **Structure with alignment:** `split`, `join`, `subrange`, `zero_sized`/`zero_sized_helper`,
   `ptrs_len_same_valid`/`lemma_ptrs_len_same_valid`,
   using `P::lemma_satisfies_alignment_offset` and `P::satisfies_alignment_of_wf`.
4. **Untyped conversions:** `into_untyped_with_typed_value`, `into_untyped`, `from_untyped`,
   `from_untyped_with_typed_value`, `untyped_ref_join`/`as_untyped`, `untyped_mut_join`/
   `as_untyped_mut`.
5. **Value operations:** the borrow/take/put/copy subrange functions and their helpers
   (renaming `borrow_value_subrange` to `borrow_subrange`).
6. **`subrange_mut`:** keep it as an axiom on `SeqPointsTo<T, PointsTo<T>>` for now. With the ghost
   metadata plan's M5 it becomes provable for any `P` (see below), so don't generalize the axiom.
7. Leave in `impl<T> SeqPointsTo<T, PointsTo<T>>` only `is_aligned`, `subrange_mut` (until proved),
   and `View` if it isn't generalized.

The recursive helpers are fine here because they're inherent methods. Only trait default methods
can't recurse.

### Phase 4: `SeqPointsTo<T, PointsToUnaligned<T>>` conversions

With the generic impl in place, the unaligned sequence exists. Add the conversions between the two
sequence types (the "(Lower priority) add the unaligned conversions" TODO):

- `into_unaligned` / `into_aligned` (by value): convert each element and rebuild with `from_seq`.
- `as_unaligned` / `as_aligned` (by reference): the element type changes, so this isn't a
  `shr_ref_struct_wrap`. With the ghost metadata plan's `tracked_collect_perm_refs` and `from_refs`,
  it is provable: borrow each element, convert it (`as_unaligned` / `as_aligned`), collect, wrap.
  Without them it would need an axiom; leave it out until then.
- `&mut` versions: provable the same way from M4-M6 once those exist.

Also add the unaligned slice conversions,
`PointsToUnaligned<[E]>` ↔ `SeqPointsTo<E, PointsToUnaligned<E>>` (`&` and `&mut`),
in a `PointsToUnaligned<E>`-specific sequence impl.
They follow ghost step 6's aligned versions without the M4 wrap:
each element is assembled directly with `from_raw_parts_ref` (shared) or M3 (`&mut`).
Optionally, the aligned versions could then be proved from these
plus the aligned/unaligned conversions, instead of separately.

### Phase 5: docs

Update `PORTING_STATUS.md`, `GENERALIZATION_ASSESSMENT.md` (mark level 3 done), and
`POINTS_TO_AXIOMS.md` if any axiom's scope changed.

## Interaction with the ghost metadata plan

The two plans touch the same types, but neither depends on the other being finished. These are the
points where they meet.

### What the ghost metadata plan changes here

- **The new field (ghost step 1).** `PointsToUnaligned` construction and destructuring sites get
  `metadata: Ghost(())` / `metadata: _`. Phase 2 moves most of those sites from `PointsTo` into the
  `PointsToUnaligned` impl, so doing ghost step 1 first means they're edited once.
- **Trait shape.** The slice impls are why `PointsToSingleValue` doesn't require `A: Sized`, states
  sizes with `Self::size(self.ptr()@.metadata)`, decodes through `value_ref`, and keeps by-value methods and constructors
  in `PointsToSingleValueSized`.
- **`subrange_mut` becomes provable.** M5 (`SeqPointsTo::from_seq_mut`) plus the existing
  `tracked_seq_pt_mut` and `Seq::tracked_split_borrow_mut` give a proof of `subrange_mut` for any
  `P`: borrow the sequence, split off the middle, wrap it with M5 at the offset pointer. This replaces
  open decision 2 of the earlier version of this plan (whether to generalize the axiom). It is the
  same result the reverted `wrap_mut` gave, but from a type-specific axiom.
- **`join_ref`/`join_mut` become provable** (ghost plan, "Existing" trusted items), so the
  assessment's section 1, group 2 idea of generalizing those axioms is no longer needed.
- **`SeqPointsTo<T, PointsToUnaligned<T>>` borrowed conversions** (phase 4) become provable from
  `from_refs` and M4-M6 instead of needing new axioms.

### What this plan changes in the ghost metadata plan

- **Steps 3 and 5 implement `PointsToSingleValue`** for `PointsToUnaligned<[E]>`
  (phase 2b) instead of adding inherent functions;
  `PointsTo<[E]>` gets it from the generic `PointsTo` impl.
  Everything in step 3 is a trait method or part of the generic aligned/unaligned impl,
  so no slice-only contracts remain (unless phase 0, items 7 or 8, fail).
  Step 2's impls for `PointsToUnaligned<[E]>` stay as they are;
  its `PointsTo<[E]>` impls are folded into the generic `PointsTo` impls in phase 2b.
- **The `lemma_ptrs_len_same_valid` naming problem goes away.** The uncommitted step 3 code
  used `_slice`-suffixed lemma names, because the broadcast group names lemmas by type,
  and inherent functions with the same name on `PointsTo<T>` and `PointsTo<[T]>`
  also made path calls like `PointsTo::zero_sized(p)` ambiguous.
  As trait methods, each impl has its own `lemma_ptrs_len_same_valid` with no clash
  (subject to phase 0, item 6, for broadcasting).
- **Step 6's sequence-side functions** (`SeqPointsTo::<E, PointsTo<E>>::from_untyped_ref`,
  `from_untyped_with_value_ref`, `as_slice_pt(_mut)`, and the `SeqPointsTo` side of `as_seq_pt(_mut)`)
  go in the `PointsTo<E>`-specific impl, not the generic one: they produce or consume `PointsTo<[E]>`
  and use M4. The unaligned counterparts (`SeqPointsTo<E, PointsToUnaligned<E>>` ↔
  `PointsToUnaligned<[E]>`) are simpler (no M4 needed) and are added in phase 4.
- **`from_refs` and M5** are already in the generic `SeqPointsTo<T, P>` impl in the ghost plan, which
  matches phase 1.
  After phase 1b their bound is `P: PointsToProperties<A = T>` (not `+ FixedSize`),
  element offsets use `P::size(())`,
  and their pointer argument is a thin `*mut T`, with `out.thin_ptr() == ptr` and `out.len() == perms.len()`.
- **Step 6's conversions can state `out.ptr() == self.ptr()`** after phase 1b,
  since `PointsTo<[E]>` and `SeqPointsTo<E, _>` then both have a `*mut [E]`,
  instead of restating address, provenance and `len() == metadata`.

### Combined order

| # | Step | Status | Why here |
|---|---|---|---|
| 1 | Ghost step 1: add the `metadata` field | done | Small; lets phase 2 move bodies once. |
| 2 | Ghost steps 2 and 4: slice `PointsToPhys`/`PointsToProperties`/`View` impls, `abs_decode_slice` | done | Don't depend on the trait. |
| 3 | Phase 0: spike | done ([results](#phase-0-results)) | Settles the trait mechanics before either plan commits to them. |
| 4 | Phase 1: structural generic `SeqPointsTo` | next | Independent; small. |
| 4b | Phase 0 check 10, then phase 1b: `SeqPointsTo` slice pointer, `size(metadata)`, no `FixedSize` | | Before phase 2, which writes the new traits against `PointsToPhys::size(metadata)`. |
| 5 | Phase 2: traits + Sized impls | | Fixes the API the slice impls implement. |
| 6 | Phase 2b: slice impls (ghost steps 3 and 5) | step 3 bodies in `step3_slice_wip.patch` | Uses the trait from row 5. |
| 6b | Phase 0 check 11, then phase 2c: `PointsToRaw` | | Its generic typed conversions use rows 5-6; its untyped part only needs row 4b. |
| 7 | Phase 3: generic typed `SeqPointsTo` | | Before ghost step 6, so step 6's code lands in the final impl structure. |
| 8 | Ghost step 6: borrowed conversions and new axioms; then prove `subrange_mut`, `join_ref`, `join_mut` | | Needs rows 6-7. |
| 9 | Phase 4 and ghost step 7 | | Both build on row 8. |
| 10 | Phase 5 and ghost step 8: docs | | |
| 11 | rustlib: `str` impls and conversions | | See [`str` in rustlib](#str-in-rustlib). Needs rows 6 and 8. |

Row 4 can move later without affecting the slice work.
Row 7 can also move after row 8,
at the cost of moving step 6's sequence-side functions again in phase 3
(they stay `PointsTo<E>`-specific, so that's mostly a relocation).

## `str` in rustlib

`PointsToUnaligned<str>` is written in rustlib,
where the view of a `str` is its bytes.
vstd is compiled as a module of rustlib's `core`,
so these impls are in the same crate as the traits and types,
and the orphan and inherent-impl rules don't get in the way.

rustlib writes impls for `PointsToUnaligned<str>` only.
Not `PointsToSingleValueSized`: like slices, `str` is unsized.
Per-impl pieces: `Metadata<str>` is the byte length (`usize`),
`PointsToPhys::size(len)` is `len`,
`satisfies_alignment` is `true`,
and `metadata_matches` is `true` (UTF-8 validity is part of `abs_decode::<str>`).
`PointsToProperties` comes from the generic `PointsToUnaligned` impl,
so rustlib writes only `PointsToPhys` (with the `ptr_mut_from_data` pointer), `View` and `PointsToSingleValue`.
`PointsTo<str>`'s alignment comes from `layout_of_str` (`align_of::<u8>()`, i.e. 1).
`layout_of_str` is `cfg`'d separately for `verus_verify_core`, but both versions state the alignment.
`PointsTo<str>` then gets all its trait impls from the generic `PointsTo` impls,
and the aligned/unaligned conversions from the generic conversion impl,
with no `str`-specific code.

The only other conversion is to and from `[u8]`,
written on `PointsToUnaligned<str>` ↔ `PointsToUnaligned<[u8]>`
and lifted to `PointsTo` through the aligned/unaligned conversions.
The untyped bytes and the metadata are unchanged
(pointer casts: `cast_str_ptr_to_slice_ptr` / `cast_slice_ptr_to_str_ptr` in `raw_ptr.rs`).
Only the typed value changes:

- **Owned.** `Valid(s)` becomes `Valid(s.as_bytes())`.
  The other direction requires valid UTF-8, or produces `Empty`.
- **`&`.** `shr_ref_struct_wrap` can't do it, since `val` is tracked.
  A `&TypedValue<str>` ↔ `&TypedValue<[u8]>` cast (a new rustlib axiom),
  then `from_raw_parts_ref`, assembles the result.
- **`&mut`.** The same, with a `&mut` value cast and M3 (and M4 for the aligned version).
  If non-UTF-8 bytes are written through a `&mut PointsTo<[u8]>` borrowed from a `PointsTo<str>`,
  the final `str` value is `Empty`.
- **Decoding.** `abs_decode` is uninterpreted and has no `str` axiom today,
  so this needs a new one, the `str` counterpart of `abs_decode_slice` (ghost step 4):

  ```rust
  /// The bytes decode to a `str` exactly when they decode to its UTF-8 bytes as a `[u8]`.
  pub broadcast axiom fn abs_decode_str(bytes: Seq<AbstractByte>, s: &str)
      ensures
          #[trigger] abs_decode::<str>(bytes, s) <==> abs_decode::<[u8]>(bytes, s.as_bytes()),
  ;
  ```

  UTF-8 validity is implicit (the bytes of any `&str` are valid UTF-8).
  `from_bytes` also needs the converse direction:
  every valid UTF-8 byte sequence is the bytes of some `str`
  (`valid_utf8(v) ==> exists|s: &str| s.as_bytes()@ == v`).
  If rustlib's `from_utf8` spec doesn't already give that, it's a second axiom.
  Both go in rustlib, where a `str`'s view is its bytes
  (vstd could state the first with `spec_bytes()`, which is `cfg(not(verus_verify_core))`, like `layout_of_str`).
  There's no `str` extensionality axiom (two `&str`s with the same bytes aren't known equal);
  the conversions don't need one, since they only promise equal bytes.
  The decoding proofs in [points_to_str_wip.rs](points_to_str_wip.rs) may be reusable here.

New trusted items, all in rustlib:
`abs_decode_str`; the "valid UTF-8 bytes are some `str`'s bytes" fact (unless `from_utf8`'s spec gives it);
and the `&TypedValue<str>` ↔ `&TypedValue<[u8]>` casts (shared and `&mut`).

What this requires of vstd:
`PointsToSingleValue`, the generic `PointsTo` impls, the generic aligned/unaligned impl,
`from_raw_parts_ref`, M3 and M4
stay public and generic over `T: ?Sized`,
not narrowed to slices.

## Open decisions

1. **`View` for `SeqPointsTo`.** `SeqPointsToData<T>` holds a `Seq<PointsTo<T>>`. Either generalize
   it to `SeqPointsToData<T, P>` (one generic `View`) or keep `View` only for the `PointsTo<T>`
   instantiation. (The matching question for `PointsToData<T>` is settled:
   ghost step 2 made it `?Sized` and gave the slice permissions a `View`.)
2. **Inherent wrappers on `PointsTo<T>`.** Removing the inherent methods (phase 2, step 7) means
   callers need the traits in scope. Keeping inherent one-line wrappers avoids that but brings back
   the duplication, now per type, since the trait side of `PointsTo` is one generic impl.
   Recommendation: remove them and export the traits.

## Deferred

- **Level 2 (default bodies).** Done where possible: the derived operations have default bodies
  (see the notes under [Two traits](#two-traits)).
  The rest touch the fields or need `wf` to unfold, so they stay per impl.
- **`str`.** Done in rustlib; see [`str` in rustlib](#str-in-rustlib).
- **Other unsized types.** `dyn` and custom DSTs are out of scope.
- **Generalizing `split`/`join`/`subrange` across `PointsToUntyped`** (assessment section 1, group 2).
  Orthogonal and still optional.

## Risks

- **Phase 0 failures.** `tracked &mut self` in trait methods, associated-type equality bounds, and
  expressing `Self::A: Sized` are the load-bearing assumptions.
  The generic `PointsTo` impl (item 9) is not load-bearing:
  its fallback is per-type delegating impls, at the cost of the duplication it avoids.
- **Proof fixups in phase 3.** Every fact about element bytes and values goes through opaque trait
  specs, so proofs that currently unfold `PointsTo` definitions will need trait lemma calls. This is
  likely the bulk of the effort.
- **Broadcast cyclicity.** Moving lemmas into traits can change which functions are on a broadcast
  group's dependency path. The latest commit (`cd02a6bae`) already had to fix cyclicity errors of
  this kind.
- **Verification time.** Generic proofs with trait-bounded quantifiers can be slower; watch for
  timeouts in the byte lemmas.
