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

`points_to_model.rs` is written out as the final code: every item, with its documentation and body.
Approved axioms are named in a comment, not repeated; their code is in TYPED_POINTS_TO_APPROVED.md.
In the other modules, bodies are omitted except for spec fns and trusted code,
and "unchanged" means the contract is today's, apart from `size()` → `Self::size(self.ptr()@.metadata)`.

Grouped by module ([layout](TYPED_POINTS_TO_APPROVED.md#module-layout)), from low-level to high-level permissions.
An impl block with both spec fns and proofs is split as in the layout:
the spec fns and axioms are under `points_to_model.rs`, the proofs under `points_to_ops.rs`.
The trait definitions are in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#trait-definitions).

### `points_to_model.rs` (trusted)

The five trait definitions, with their default bodies, are approved
([TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#trait-definitions)).
The lemma groups (`group_points_to_lemmas`, `group_points_to_collections_lemmas`) are in
[Module layout](TYPED_POINTS_TO_APPROVED.md#module-layout).

#### `PointsToByte` (phase 1)

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

    /// If the pointer stays the same, `old` and `new` are permissions to the same memory.
    open spec fn ptrs_len_same(old: Self, new: Self) -> bool {
        new.ptr() == old.ptr()
    }

    /// Trivial, since a `PointsToByte` is always well-formed.
    proof fn stays_wf_basic(old: Self, new: Self) {
    }
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

#### `SeqPointsTo` and `PointsToUntyped`: specs (phase 1b)

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

    // Approved axiom: from_seq_mut (M5).
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

    // Approved axioms: join_ref, join_mut.
}
```

#### `TypedValue` (phase 2)

`value_ref` and `valid_ref` are approved
([`TypedValue`](TYPED_POINTS_TO_APPROVED.md#typedvalue-phase-2)); the rest exists today.

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

    // Approved: value_ref, valid_ref.
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

    // Approved axiom: from_elems_mut (M1).
    // Axiom (in APPROVED.md, awaiting approval): from_elems_ref.
}
```

#### `PointsToUnaligned`: specs (phases 2, 2b; `str` in rustlib)

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
/// and the metadata of the `*mut T` pointer.
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
    /// If `self.wf()`, then the returned permission is `wf()`.
    pub proof fn tracked_pt_untyped(tracked &self) -> tracked &PointsToUntyped
        returns
            self.pt_untyped(),
    {
        &self.pt_untyped
    }

    // Approved axioms: from_raw_parts_ref, from_raw_parts_mut (M3).
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
}
```

#### `PointsTo`: specs (generic; phase 2, widened in phase 2b)

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

// ptr |--> Valid(v) means:
//   bytes in this memory are consistent with value v
//   and we have all the ghost state associated with type V
//
// ptr |--> Empty means:
//   no knowledge about what's in memory
//   (to be pedantic, the bytes might be initialized in rust's abstract machine,
//   but we don't know so we have to pretend they're uninitialized)
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
    /// If `self.wf()`, then the returned permission is `wf()`.
    pub proof fn tracked_pt_unaligned(tracked &self) -> tracked &PointsToUnaligned<T>
        returns
            self.pt_unaligned(),
    {
        &self.pt_unaligned
    }

    // Approved axiom: from_unaligned_mut (M4).
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

    // Approved axiom: borrow_mut.
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
    /// Alignment is part of `wf`, through `satisfies_alignment`.
    open spec fn wf_basic(self) -> bool {
        self.pt_unaligned().wf_basic()
    }
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

    /// The same as for `PointsToUnaligned`.
    open spec fn metadata_matches(value: &T, metadata: Metadata<T>) -> bool {
        <PointsToUnaligned<T> as PTTypedValue>::metadata_matches(value, metadata)
    }

    /// The `PointsToUnaligned` requirement, plus alignment to `T`.
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
}
````

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
            s.ptr() as *mut T == ptr,
            s.wf_basic(),
    ;

    /// Creates an empty sequence at `ptr`.
    pub proof fn empty(ptr: *mut T) -> (tracked s: Self)
        requires
            ptr@.addr != 0,
            ptr_addr_in_bounds(ptr),
        ensures
            s.seq_pt() == Seq::<P>::empty(),
            s.ptr() as *mut T == ptr,
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
            first.ptr() as *mut T == self.ptr() as *mut T,
            second.ptr() as *mut T == ptr_mut_from_data::<T>(PtrData {
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
            joined.ptr() as *mut T == self.ptr() as *mut T,
            joined.wf_basic(),
    ;

    /// Borrows the sub-sequence of `len` element permissions starting at `start`.
    pub proof fn subrange_basic(tracked &self, start: nat, len: nat) -> (tracked sub: &Self)
        requires
            self.wf_basic(),
            start + len <= self.len(),
        ensures
            sub.seq_pt() == self.seq_pt().subrange(start as int, (start + len) as int),
            sub.ptr() as *mut T == ptr_mut_from_data::<T>(PtrData {
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
    // borrow, into_untyped, from_untyped, zero_sized: the trait's default bodies.
    // ptrs_len_same_valid is overridden, for the same reason as `wf`:
    //   new.ptr() == old.ptr()
    //   && <PointsToUnaligned<T> as PTValueOps>::ptrs_len_same_valid(old.pt_unaligned(), new.pt_unaligned())
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
    /// The pointer to the first element, without the length.
    pub open spec fn thin_ptr(self) -> *mut T {
        self.ptr() as *mut T
    }

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
  the typed value from `from_elems_ref` on the elements' typed values
  (empty when any element is empty),
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
`wf_basic` is `self.wf_basic_unaligned()`), `PTProperties` (the same delegations as for `T` and `[T]`),
`PTTypedValue` and `PTValueOps` for `PointsToUnaligned<str>`;
its `View` and everything for `PointsTo<str>` come from the generic impls (alignment 1, from `layout_of_str`).

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
| `impl<T> TypedValue<[T]>` | `value` (-> `&[T]`); `from_elems_ref` (new axiom, phase 3b); `from_elems_mut` (new axiom M1, phase 3b) | |
| `impl<T: ?Sized> PointsToUnaligned<T>` | closed accessors `typed_value`, `pt_untyped`, `metadata`; `bytes`, `is_valid`, `is_empty` (inline); `tracked_pt_untyped`; `as_raw_parts_mut` (new, proposed, phase 4); `from_raw_parts_ref` (new axiom, phase 3b), `from_raw_parts_mut` (new axiom M3, phase 3b) | The inherent `typed_value`/`bytes` coexist with the trait's (phase 0, item 5). |
| `impl<T: ?Sized> PointsToUnaligned<T> where PointsToUnaligned<T>: PTValueOps<A = T>` | `into_aligned`, `as_aligned` (new, generic); `as_aligned_mut` (new, generic, phase 3b: needs M4) | Contracts in [`PointsTo`: proofs and aligned/unaligned conversions](#pointsto-proofs-and-alignedunaligned-conversions). |
| `impl<T> PointsToUnaligned<T>` | `value`; `is_disjoint_unaligned<S>`. (removed: `wf`, `stays_wf`, `zero_sized`) | |
| `impl<T> PointsToUnaligned<[T]>` | `from_untyped_ref`, `from_untyped_with_value_ref`, `borrow_index` (new, phase 4; the primary implementations). (removed in 2b: inherent `wf`) | |
| `impl<T: ?Sized> PointsTo<T>` | closed `pt_unaligned`; `typed_value`, `metadata`, `bytes`, `is_valid`, `is_empty` (open, delegating); `tracked_pt_unaligned`; `from_unaligned_mut` (new axiom M4) | |
| `impl<T: ?Sized> PointsTo<T> where PointsToUnaligned<T>: PTValueOps<A = T>` | `into_unaligned`, `as_unaligned`, `as_unaligned_mut` (new, generic) | Contracts in [`PointsTo`: proofs and aligned/unaligned conversions](#pointsto-proofs-and-alignedunaligned-conversions). |
| `impl<T> PointsTo<T>` | `value`, `is_aligned`, `is_disjoint_pointsto<S>`; `borrow_mut` (axiom). (removed: `wf`, `stays_wf`, `lemma_ptrs_len_same_valid`, `zero_sized`, `bytes_decode`, the untyped conversions, the value operations) | Removed ones are `PTValueOps` / `PTSizedValue` methods. |
| `impl<T> PointsTo<[T]>` | `from_untyped_ref`, `from_untyped_with_value_ref`, `borrow_index` (new, phase 4; compositions over the `PointsToUnaligned` versions). (removed: inherent `wf`) | |
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
