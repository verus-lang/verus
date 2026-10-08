use super::group_vstd_default;
use super::layout::{self, *};
use super::points_to::*;
use super::prelude::*;
use super::raw_ptr;
use super::raw_ptr::*;
#[cfg(verus_keep_ghost)]
use super::type_representation::*;

verus! {

broadcast use group_vstd_default;

/// Specifies that the pointer's address is within the bounds of its provenance.
// TODO: move to ptr file
pub open spec fn ptr_addr_in_bounds<T: ?Sized>(ptr: *mut T) -> bool {
    ptr@.provenance.is_some() ==> {
        &&& ptr@.addr as int >= ptr@.provenance.data().start_addr()
        &&& ptr@.addr <= ptr@.provenance.data().start_addr() + ptr@.provenance.data().alloc_len()
    }
}

pub tracked struct SeqPointsTo<T: ?Sized, PointsToPerm: PointsToProperties + FixedSize> {
    seq_pt: Seq<PointsToPerm>,
    ptr: Ghost<*mut T>,
}

impl<T, PointsToPerm> PointsToPhys for SeqPointsTo<T, PointsToPerm> where
    T: ?Sized,
    PointsToPerm: PointsToProperties + FixedSize,
 {
    type A = T;

    closed spec fn ptr(self) -> *mut T {
        self.ptr@
    }

    /// The size of the pointed-to region is given by the length of the sequence
    /// times the (constant) size of the permission type in the sequence.
    open spec fn size(self) -> nat {
        self.seq_pt().len() * PointsToPerm::const_size()
    }
}

impl<T, PointsToPerm> PointsToProperties for SeqPointsTo<T, PointsToPerm> where
    T: ?Sized,
    PointsToPerm: PointsToProperties + FixedSize,
 {
    open spec fn wf_basic(self) -> bool {
        // Defining the provenance and address for the individual PointsToPerms
        &&& forall|i|
            #![trigger self[i].ptr()@.provenance]
            #![trigger self[i].ptr()@.addr]
            #![trigger self[i].wf_basic()]
            0 <= i < self.len() ==> {
                &&& self[i].ptr()@.provenance == self.ptr()@.provenance
                &&& self[i].ptr()@.addr == self.ptr()@.addr + i * PointsToPerm::const_size()
                &&& self[i].wf_basic()
            }
            // The ptr is non-null
        &&& self.ptr()@.addr
            != 0
        // If ptr's provenance is Some, the address is in bounds of the provenance
        &&& self.ptr()@.provenance.is_some() ==> {
            &&& self.ptr()@.provenance.data().start_addr() <= self.ptr()@.addr
            &&& self.ptr()@.addr <= self.ptr()@.provenance.data().start_addr()
                + self.ptr()@.provenance.data().alloc_len()
        }
    }

    /// Non-nullness is guaranteed by the invariant.
    proof fn is_nonnull(tracked &self) {
    }

    /// If the size is non-zero, the length must be nonzero.
    /// Then this follows from the `provenance_not_none` property of an individual `PointsToPerm`.
    proof fn provenance_not_none(tracked &self) {
        self.seq_pt.tracked_borrow(0).size_eq_const_size();
        self.seq_pt.tracked_borrow(0).provenance_not_none();
    }

    proof fn ptr_bounds(tracked &self) {
        if self.len() > 0 {
            self.seq_pt.tracked_borrow(self.len() - 1).ptr_bounds();
            self.seq_pt.tracked_borrow(self.len() - 1).size_eq_const_size();
            super::arithmetic::mul::lemma_mul_is_distributive_add_other_way(
                PointsToPerm::const_size() as int,
                (self.len() - 1) as int,
                1,
            );
        }
    }

    proof fn is_disjoint<OtherPointsToPerm: PointsToPhys>(
        tracked &mut self,
        tracked other: &OtherPointsToPerm,
    ) {
        let self_addr = self.ptr()@.addr as int;
        let other_addr = other.ptr()@.addr as int;
        let csize = PointsToPerm::const_size() as int;
        let len = self.len() as int;

        if other_addr < self_addr {
            // `other` starts strictly before `self`'s whole range: since element 0
            // starts exactly where `self` does, its disjointness from `other` is
            // exactly the disjointness we need for the whole array.
            self.seq_pt.tracked_borrow_mut(0).size_eq_const_size();
            self.seq_pt.tracked_borrow_mut(0).is_disjoint(other);
            assert(self.seq_pt =~= old(self).seq_pt);
        } else if other_addr >= self_addr + len * csize {
            // `other` starts at or after `self`'s whole range ends: the last
            // element ends exactly where `self` does, so its disjointness from
            // `other` gives us what we need.
            self.seq_pt.tracked_borrow_mut(len - 1).size_eq_const_size();
            self.seq_pt.tracked_borrow_mut(len - 1).is_disjoint(other);
            assert(self.seq_pt =~= old(self).seq_pt);
            super::arithmetic::mul::lemma_mul_is_distributive_add_other_way(csize, len - 1, 1);
        } else {
            // `other` starts strictly inside `self`'s range: find the element `k`
            // whose byte range contains `other`'s start address, and derive a
            // contradiction from the fact that it can't possibly be disjoint from
            // `other` (since `other`'s own start address lies within it).
            let k = (other_addr - self_addr) / csize;
            super::arithmetic::div_mod::lemma_fundamental_div_mod(other_addr - self_addr, csize);
            super::arithmetic::div_mod::lemma_remainder(other_addr - self_addr, csize);
            super::arithmetic::div_mod::lemma_multiply_divide_lt(
                other_addr - self_addr,
                csize,
                len,
            );
            super::arithmetic::div_mod::lemma_div_pos_is_pos(other_addr - self_addr, csize);
            self.seq_pt.tracked_borrow_mut(k).size_eq_const_size();
            self.seq_pt.tracked_borrow_mut(k).is_disjoint(other);
        }
    }
}

impl<T, PointsToPerm> SeqPointsTo<T, PointsToPerm> where
    T: ?Sized,
    PointsToPerm: PointsToProperties + FixedSize,
 {
    /// The sequence of permissions that the `SeqPointsTo` contains.
    pub closed spec fn seq_pt(self) -> Seq<PointsToPerm> {
        self.seq_pt
    }

    /// The length of the sequence of `PointsToPerm`.
    #[verifier::inline]
    pub open spec fn len(self) -> nat {
        self.seq_pt().len()
    }

    /// `[]` operator, synonymous with `index`.
    #[verifier::inline]
    pub open spec fn spec_index(self, index: int) -> PointsToPerm
        recommends
            0 <= index < self.len(),
    {
        self.seq_pt()[index]
    }
}

/// Permission to access an (untyped) contiguous sequence of bytes in memory.
/// Internally represented as a sequence of `PointsToSingleton` permissions,
/// along with a `*mut [u8]` pointer to the region of bytes.
pub type PointsToUntyped = SeqPointsTo<[u8], PointsToSingleton>;

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
        self.seq_pt().map(|i: int, pt_singleton: PointsToSingleton| pt_singleton.byte())
    }

    /// In addition to the well-formed-ness properties which must hold of every `SeqPointsTo`,
    /// the `*mut [u8]` pointer's metadata must match the number of `PointsToSingleton` permissions.
    pub open spec fn wf(self) -> bool {
        self.wf_basic() && self.ptr()@.metadata == self.len()
    }

    /// Specifies that `old` and `new` have the same pointer, length, and underlying `PointsToSingleton` pointers.
    pub open spec fn ptrs_len_same(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& new.len() == old.len()
        &&& forall|j: int| #![trigger new[j]] 0 <= j < new.len() ==> new[j].ptr() == old[j].ptr()
    }

    /// Ensures that if `self` is well-formed, and `other` has the same pointers and length,
    /// then `other` is well-formed.
    pub proof fn stays_wf(tracked self, tracked other: Self)
        requires
            self.wf(),
            Self::ptrs_len_same(self, other),
        ensures
            other.wf(),
    {
    }

    /// If `T` is zero sized, then we can construct a `PointsToUntyped` from any non-null pointer.
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
    {
        broadcast use raw_ptr::group_raw_ptr_axioms;

        let byte_ptr: *mut [u8] = ptr_mut_from_data(
            PtrData::<[u8]> { addr: ptr@.addr, provenance: ptr@.provenance, metadata: 0 },
        );
        SeqPointsTo { seq_pt: Seq::tracked_empty(), ptr: Ghost(byte_ptr) }
    }

    /// Specializes `is_disjoint` to the case when the other permission is a `PointsToUntyped`.
    pub proof fn is_disjoint_untyped(tracked &mut self, tracked other: &PointsToUntyped)
        requires
            self.len() != 0,
            other.len() != 0,
            self.wf(),
        ensures
            *old(self) == *final(self),
            final(self).ptr() as int + final(self).len() <= other.ptr() as int || other.ptr() as int
                + other.len() <= final(self).ptr() as int,
    {
        assert(self.len() == self.size());
        assert(other.size() == other.len() * other.seq_pt()[0].size());
        self.is_disjoint(other);
    }

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
    {
        if self.len() != 0 {
            self.provenance_not_none();
            self.ptr_bounds();
        }

        let tracked mut seq_pt = self.seq_pt;
        let tracked other = seq_pt.tracked_skip(mid as int);

        let tracked first = SeqPointsTo {
            seq_pt: seq_pt,
            ptr: Ghost(
                ptr_mut_from_data::<[u8]>(
                    PtrData {
                        addr: self.ptr()@.addr,
                        provenance: self.ptr()@.provenance,
                        metadata: mid as usize,
                    },
                ),
            ),
        };
        let tracked second = SeqPointsTo {
            seq_pt: other,
            ptr: Ghost(
                ptr_mut_from_data::<[u8]>(
                    PtrData {
                        addr: (self.ptr()@.addr + mid) as usize,
                        provenance: self.ptr()@.provenance,
                        metadata: (self.len() - mid) as usize,
                    },
                ),
            ),
        };
        (first, second)
    }

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
    {
        if self.len() != 0 {
            self.provenance_not_none();
            self.ptr_bounds();
        }
        if other.len() != 0 {
            other.provenance_not_none();
            other.ptr_bounds();
        }
        let tracked mut seq_pt = self.seq_pt;
        seq_pt.tracked_add(other.seq_pt);

        let tracked joined = SeqPointsTo {
            seq_pt: seq_pt,
            ptr: Ghost(
                ptr_mut_from_data::<[u8]>(
                    PtrData {
                        addr: self.ptr()@.addr,
                        provenance: self.ptr()@.provenance,
                        metadata: (self.len() + other.len()) as usize,
                    },
                ),
            ),
        };
        joined
    }

    /// We can cast a `PointsToUntyped` to a `SeqPointsTo<T, PointsTo<T>>` of length `capacity`
    /// under the following conditions:
    ///
    /// (1) The pointer's address is aligned to `T`.
    ///
    /// (2) The length is exactly `capacity * size_of::<T>()`.
    ///
    /// (3) For each non-None element in `typed_value`, the corresponding abstract bytes for the
    ///     `PointsToUntyped` can be decoded into the given value. Note that `typed_value` is allowed
    ///     to contain None items (these are ignored for purposes of decoding)
    ///     and can be a prefix of the total `capacity` (in which case, the remaining memory is
    ///     all logically uninitialized).
    ///
    /// The resulting `SeqPointsTo<T, PointsTo<T>>` will have a prefix of memory corresponding to
    /// `typed_value`. The rest of the memory will be logically uninitialized.
    /// The abstract bytes will also remain the same.
    pub proof fn cast_to_seq_pt<T>(
        tracked self,
        capacity: usize,
        tracked typed_value: Seq<Option<T>>,
    ) -> (tracked out: SeqPointsTo<T, PointsTo<T>>)
        requires
            self.wf(),
            self.ptr()@.addr as nat % align_of::<T>() == 0,
            self.len() == capacity * size_of::<T>(),
            typed_value.len() <= capacity,
            forall|i: int|
                0 <= i < typed_value.len() && typed_value[i].is_some() ==> #[trigger] abs_decode::<
                    T,
                >(
                    self.bytes().subrange(i * size_of::<T>(), (i + 1) * size_of::<T>()),
                    &typed_value[i].unwrap(),
                ),
        ensures
            out.ptr() == self.ptr() as *mut T,
            out.len() == capacity,
            out.bytes() == self.bytes(),
            forall|i: int|
                0 <= i < typed_value.len() ==> {
                    &&& (#[trigger] out[i]).is_valid() <==> typed_value[i].is_some()
                    &&& typed_value[i].is_some() ==> typed_value[i].unwrap() == out[i].value()
                },
            out.wf(),
        decreases capacity,
    {
        let ghost ghost_self = self;

        if capacity == 0 {
            assert(capacity * size_of::<T>() == 0) by (nonlinear_arith)
                requires
                    capacity == 0,
            ;
            let tracked out = SeqPointsTo::<T, PointsTo<T>>::empty(self.ptr() as *mut T);
            assert(out.bytes() =~= self.bytes());
            out
        } else {
            if size_of::<T>() != 0 {
                assert(capacity * size_of::<T>() != 0) by (nonlinear_arith)
                    requires
                        capacity != 0,
                        size_of::<T>() != 0,
                ;
                self.provenance_not_none();
                self.ptr_bounds();
            }
            assert(0 <= (capacity - 1) as nat * size_of::<T>() <= capacity * size_of::<T>())
                by (nonlinear_arith)
                requires
                    capacity > 0,
            ;
            assert(((self.ptr()@.addr + (capacity - 1) as nat * size_of::<T>()) as nat
                % align_of::<T>() == 0)) by {
                broadcast use
                    crate::vstd::arithmetic::div_mod::lemma_mul_mod_noop_right,
                    crate::vstd::arithmetic::div_mod::lemma_add_mod_noop,
                    layout_of_sized,
                ;

            }
            // Split into "head" and "tail", where tail is the last element's bytes
            let tracked (head, tail) = self.split(((capacity - 1) as nat * size_of::<T>()) as nat);
            assert(tail.len() + (capacity - 1) as nat * size_of::<T>() == capacity
                * size_of::<T>());
            assert(tail.len() == size_of::<T>()) by (nonlinear_arith)
                requires
                    tail.len() + (capacity - 1) as nat * size_of::<T>() == capacity * size_of::<T>(),
                    capacity > 0,
            ;
            if size_of::<T>() == 0 {
                assert((capacity - 1) as nat * size_of::<T>() == 0) by (nonlinear_arith)
                    requires
                        size_of::<T>() == 0,
                ;
            }
            assert(tail.ptr()@.addr == ghost_self.ptr()@.addr + (capacity - 1) as nat * size_of::<
                T,
            >());

            // Cast the tail into either a valid or empty permission, depending on `typed_value`
            let ghost ghost_tail = tail;
            let tracked mut tail_pt = PointsTo::<T>::from_untyped(tail);
            let tracked mut head_typed_value = typed_value;
            if typed_value.len() == capacity {
                let tracked last = head_typed_value.tracked_pop();
                match last {
                    Some(v) => {
                        let i = (capacity - 1) as int;
                        assert(typed_value[i].is_some());
                        assert(tail_pt.bytes() =~= ghost_self.bytes().subrange(
                            i * size_of::<T>(),
                            (i + 1) * size_of::<T>(),
                        ));
                        tail_pt.put(v);
                    },
                    None => {},
                }
            }
            let ghost tail_ptr = tail_pt.ptr();
            let ghost tail_bytes = tail_pt.bytes();
            assert(tail_bytes == ghost_tail.bytes());
            let tracked mut tail_seq = Seq::tracked_empty();
            tail_seq.tracked_push(tail_pt);
            assert forall|i: int| 0 <= i < tail_seq.len() implies #[trigger] tail_seq[i].ptr()@.addr
                == tail_ptr@.addr + i * size_of::<T>() by {
                assert(i == 0);
                assert(0 * size_of::<T>() == 0) by (nonlinear_arith);
            }
            let tracked tail_typed = SeqPointsTo::<T, PointsTo<T>>::from_seq(tail_seq, tail_ptr);

            // Invoke the inductive hypothesis on the head
            assert forall|i: int|
                0 <= i < head_typed_value.len() && head_typed_value[i].is_some() implies #[trigger] abs_decode::<
                T,
            >(
                head.bytes().subrange(i * size_of::<T>(), (i + 1) * size_of::<T>()),
                &head_typed_value[i].unwrap(),
            ) by {
                assert(0 <= i * size_of::<T>() <= (i + 1) * size_of::<T>() <= (capacity
                    - 1) as nat * size_of::<T>()) by (nonlinear_arith)
                    requires
                        0 <= i < capacity - 1,
                ;
                ghost_self.bytes().lemma_slice_of_slice(
                    0,
                    ((capacity - 1) as nat * size_of::<T>()) as int,
                    i * size_of::<T>(),
                    (i + 1) * size_of::<T>(),
                );
            }
            let tracked head_typed = head.cast_to_seq_pt((capacity - 1) as usize, head_typed_value);

            // Join head and tail
            assert(tail_typed.bytes() =~= tail_bytes) by {
                reveal_with_fuel(Seq::fold_left, 2);
            }
            let tracked out = head_typed.join(tail_typed);
            assert(ghost_self.bytes().take(
                ((capacity - 1) as nat * size_of::<T>()) as int,
            ) + ghost_self.bytes().skip(((capacity - 1) as nat * size_of::<T>()) as int)
                =~= ghost_self.bytes());
            out
        }
    }

    /// A `PointsToUntyped` can be cast to a valid `PointsTo<T>` when the abstract bytes can be
    /// decoded into the given `tracked typed_value`, the length is `size_of::<T>()`,
    /// and the pointer is aligned to `T`.
    /// The resulting permission will take on the value in memory given by `typed_value`.
    ///
    /// The abstract bytes remain the same. This preserves the typed contents in memory on a
    /// roundtrip cast (see `PointsTo::cast_to_untyped`).
    /// Note that this means provenance is not lost, which matches Rust's semantics for
    /// casting/transmuting in-memory values.
    ///
    /// The inclusion of `tracked typed_value` prohibits creating permission-carrying types out of
    /// thin air, in the case where `T` is a type that stores/represents a permission
    /// (e.g., shared references).
    pub proof fn cast_to_typed<T>(tracked self, tracked typed_value: T) -> (tracked dst: PointsTo<T>)
        requires
            self.wf(),
            self.len() == size_of::<T>(),
            self.ptr()@.addr as nat % align_of::<T>() == 0,
            abs_decode::<T>(self.bytes(), &typed_value),
        ensures
            dst.bytes() == self.bytes(),
            dst.is_valid(),
            dst.value() == typed_value,
            dst.ptr() == self.ptr() as *mut T,
            dst.wf(),
    {
        let tracked mut perm = PointsTo::<T>::from_untyped(self);
        perm.put(typed_value);
        perm
    }
}

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
    Valid(Box<T>),
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
            TypedValue::Valid(b) => TypedValue::Valid(Box::new(**b)),
            TypedValue::Empty => TypedValue::Empty,
        }
    }
}

impl<T> TypedValue<[T]> {
    /// If it is a [`TypedValue::Valid`] value, returns the value.
    /// Otherwise, the return value is meaningless.
    // Does this make sense as the return value? Returning [T] doesn't work bc it's not Sized.
    #[verifier::inline]
    pub open spec fn value(&self) -> &[T]
        recommends
            self is Valid,
    {
        &*self->0
    }
}

/// Permission to access memory which may decode to a valid value of type `T`;
/// this memory is not guaranteed to be aligned to `T`.
/// Internally represented as a possibly-valid value of type `T`,
/// along with a `PointsToUntyped` permission to the underlying bytes.
pub tracked struct PointsToUnaligned<T: ?Sized> {
    val: TypedValue<T>,
    pt_untyped: Tracked<PointsToUntyped>,
}

/// The interface for a `PointsToUnaligned` permission,
/// which represents permission to access possibly-unaligned memory
/// which may decode to a valid value of type `T`.
/// We track the pointer to that memory,
/// the (possibly-valid) typed value, and its abstract bytes.
#[cfg(verus_keep_ghost)]
impl<T> View for PointsToUnaligned<T> {
    type V = PointsToData<T>;

    open spec fn view(&self) -> Self::V {
        PointsToData { ptr: self.ptr(), value: self.typed_value(), bytes: self.bytes() }
    }
}

impl<T: ?Sized> PointsToUnaligned<T> {
    /// The (possibly-valid) typed value that this permission tracks.
    pub closed spec fn typed_value(self) -> TypedValue<T> {
        self.val
    }

    /// The underlying `PointsToUntyped` permission to the pointed-to bytes.
    pub closed spec fn pt_untyped(self) -> PointsToUntyped {
        self.pt_untyped@
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
    /// This has no `wf()` requires/ensures because `wf` is only defined for `Sized` `T`, 
    /// and this impl block is `?Sized`. 
    /// This also gives flexibility for getting the underlying `PointsToUntyped` 
    /// when the permission is not well-formed.
    /// For `Sized` `T`, if `self.wf()`, then the returned permission is `wf()`. 
    pub proof fn tracked_pt_untyped(tracked &self) -> tracked &PointsToUntyped
        returns
            self.pt_untyped(),
    {
        &self.pt_untyped
    }
}

impl<T> PointsToPhys for PointsToUnaligned<T> {
    type A = T;

    /// Casts the underlying untyped pointer to a `*mut T`.
    closed spec fn ptr(self) -> *mut T {
        self.pt_untyped().ptr() as *mut T
    }

    /// The size of the pointed-to region is the size of `T`.
    open spec fn size(self) -> nat {
        size_of::<T>()
    }
}

impl<T> FixedSize for PointsToUnaligned<T> {
    /// A `PointsToUnaligned<T>` always tracks `size_of::<T>()` bytes of memory.
    open spec fn const_size() -> nat {
        size_of::<T>()
    }

    proof fn size_eq_const_size(tracked &self) {
    }
}

impl<T> PointsToProperties for PointsToUnaligned<T> {
    /// A `PointsToUnaligned` is well-formed if its memory region is `size_of::<T>()`,
    /// validity of the typed memory implies that the bytes decode to its value,
    /// and the underlying `PointsToUntyped` is well-formed.
    open spec fn wf_basic(self) -> bool {
        &&& self.bytes().len() == size_of::<T>()
        &&& self.is_valid() ==> #[trigger] abs_decode::<T>(self.bytes(), &self.value())
        &&& self.pt_untyped().wf()
    }

    /// Non-nullness follows from the underlying `PointsToUntyped`'s invariant,
    /// since `self.ptr()` and `self.pt_untyped().ptr()` have the same address.
    proof fn is_nonnull(tracked &self) {
    }

    /// Delegates to the underlying `PointsToUntyped`'s `ptr_bounds`,
    /// since `self.ptr()` and `self.pt_untyped().ptr()` have the same address.
    proof fn ptr_bounds(tracked &self) {
        self.pt_untyped.ptr_bounds();
    }

    /// Delegates to the underlying `PointsToUntyped`'s `provenance_not_none`.
    proof fn provenance_not_none(tracked &self) {
        self.pt_untyped.provenance_not_none();
    }

    /// Delegates to the underlying `PointsToUntyped`'s `is_disjoint`,
    /// since the two permissions track the same memory range.
    proof fn is_disjoint<OtherPointsToPerm: PointsToPhys>(
        tracked &mut self,
        tracked other: &OtherPointsToPerm,
    ) {
        self.pt_untyped.is_disjoint(other);
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

    /// Well-formedness is defined in the `PointsToProperties` trait function `wf_basic`.
    pub open spec fn wf(&self) -> bool {
        self.wf_basic()
    }

    /// Specifies that `old` and `new` have the same underlying `PointsToUntyped` pointers and length,
    /// and `new`'s bytes still decode to `new`'s value if `new` has a valid `TypedValue`.
    pub open spec fn ptrs_len_same_valid_decode(old: Self, new: Self) -> bool {
        &&& PointsToUntyped::ptrs_len_same(old.pt_untyped(), new.pt_untyped())
        &&& new.is_valid() ==> abs_decode::<T>(new.bytes(), &new.value())
    }

    /// Ensures that if `self` is well-formed, and `other` has the same pointers and length
    /// and still satisfies decode validity,
    /// then `other` is well-formed.
    pub proof fn stays_wf(tracked self, tracked other: Self)
        requires
            self.wf(),
            Self::ptrs_len_same_valid_decode(self, other),
        ensures
            other.wf(),
    {
    }

    /// Convert PointsToUnaligned to an aligned PointsTo.
    /// Requires the pointer address to be properly aligned.
    ///
    /// Ensures pointer locations remain the same, and memory
    /// initializations states remain the same.
    pub proof fn into_aligned(tracked self) -> (tracked perm: PointsTo<T>)
        requires
            self.wf(),
            self.ptr()@.addr as int % align_of::<T>() as int == 0,
        ensures
            perm@ == self@,
            perm.wf(),
    {
        broadcast use layout_of_sized;

        PointsTo { pt_unaligned: Tracked(self) }
    }

    /// Borrow an unaligned PointsToUnaligned as an aligned PointsTo.
    /// Requires the pointer address to be properly aligned.
    ///
    /// Ensures pointer locations remain the same, and memory
    /// initializations states remain the same.
    pub axiom fn as_aligned(tracked &self) -> (tracked perm: &PointsTo<T>)
        requires
            self.wf(),
            self.ptr()@.addr as int % align_of::<T>() as int == 0,
        ensures
            perm@ == self@,
            perm.wf(),
    // TODO: uncomment when main is merged in
    // { shr_ref_struct_wrap(self, &PointsTo { pt_unaligned: Tracked(self) }, "", "pt_unaligned") }

    ;

    /// If `T` is zero sized, then we can construct an uninitialized `PointsToUnaligned<T>`
    /// from any non-null pointer whose address (and, if known, provenance) is otherwise valid.
    /// The range of memory pointed to by this permission will be empty.
    pub proof fn zero_sized(ptr: *mut T) -> (tracked perm: Self)
        requires
            ptr@.addr != 0,
            size_of::<T>() == 0,
            ptr_addr_in_bounds(ptr),
        ensures
            perm.ptr()@.addr == ptr@.addr,
            perm.ptr()@.provenance == ptr@.provenance,
            perm.is_empty(),
            perm.bytes().len() == size_of::<T>(),
            perm.wf(),
    {
        broadcast use raw_ptr::group_raw_ptr_axioms;

        let tracked untyped: PointsToUntyped = PointsToUntyped::zero_sized(ptr);
        PointsToUnaligned { val: TypedValue::Empty, pt_untyped: Tracked(untyped) }
    }

    /// Specializes `is_disjoint` to the case when the other permission is a `PointsToUnaligned<S>`.
    pub proof fn is_disjoint_unaligned<S>(tracked &mut self, tracked other: &PointsToUnaligned<S>)
        requires
            size_of::<T>() != 0,
            size_of::<S>() != 0,
            self.wf(),
        ensures
            *old(self) == *final(self),
            final(self).ptr() as int + size_of::<T>() <= other.ptr() as int || other.ptr() as int
                + size_of::<S>() <= final(self).ptr() as int,
    {
        self.size_eq_const_size();
        other.size_eq_const_size();
        self.is_disjoint(other);
    }
}

/**
Permission to access possibly-initialized, _typed_ memory.

The associated pointer ([`points_to.ptr()`](PointsTo::ptr)) is always a valid pointer for constructing
a reference to the underlying data. That means it's always aligned to its type
([`is_aligned`](PointsTo::is_aligned)) and is non-null ([`is_nonnull`](PointsTo::is_nonnull)).

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

Currently, these use-cases aren't supported because `PointsTo` enforces both non-nullness
and alignment.
*/

// ptr |--> Init(v) means:
//   bytes in this memory are consistent with value v
//   and we have all the ghost state associated with type V
//
// ptr |--> Uninit means:
//   no knowledge about what's in memory
//   (to be pedantic, the bytes might be initialized in rust's abstract machine,
//   but we don't know so we have to pretend they're uninitialized)
pub tracked struct PointsTo<T: ?Sized> {
    pt_unaligned: Tracked<PointsToUnaligned<T>>,
}

/// The interface for a `PointsTo` permission,
/// which represents permission to access memory which is aligned to `T`,
/// whose bytes may decode to a valid value of type `T`.
/// We track the pointer to that memory,
/// the (possibly-valid) typed value, and its abstract bytes.
///
/// Data associated with a `PointsTo` permission.
/// We keep track of both the pointer, the (potentially uninitialized) value
/// it points to, and the abstract bytes in memory corresponding to Rust's abstract machine.
///
/// If `mem_contents` is `Init(T)`, this signifies that `ptr` points to initialized memory,
/// and the value of `mem_contents` is consistent with the bytes `ptr` points to,
/// We also have all the ghost state associated with type `T`.
///
/// If `mem_contents` is `Uninit`, then we have no knowledge about what's in memory,
/// and we assume `ptr` points to uninitialized memory.
/// (To be pedantic, the bytes might be initialized in Rust's abstract machine,
///  but we don't know, so we have to pretend they're uninitialized.)
#[cfg(verus_keep_ghost)]
pub ghost struct PointsToData<T> {
    pub ptr: *mut T,
    pub value: TypedValue<T>,
    pub bytes: Seq<AbstractByte>,
}

#[cfg(verus_keep_ghost)]
impl<T> View for PointsTo<T> {
    type V = PointsToData<T>;

    open spec fn view(&self) -> Self::V {
        PointsToData { ptr: self.ptr(), value: self.typed_value(), bytes: self.bytes() }
    }
}

impl<T: ?Sized> PointsTo<T> {
    /// The underlying `PointsToUnaligned` permission to the pointed-to memory.
    pub closed spec fn pt_unaligned(self) -> PointsToUnaligned<T> {
        self.pt_unaligned@
    }

    /// The (possibly-valid) typed value that this permission tracks.
    pub open spec fn typed_value(self) -> TypedValue<T> {
        self.pt_unaligned().typed_value()
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
    /// This has no `wf()` requires/ensures because `wf` is only defined for `Sized` `T`,
    /// and this impl block is `?Sized`.
    /// This also gives flexibility for getting the underlying `PointsToUnaligned`
    /// when the permission is not well-formed.
    /// For `Sized` `T`, if `self.wf()`, then the returned permission is `wf()`.
    pub proof fn tracked_pt_unaligned(tracked &self) -> tracked &PointsToUnaligned<T>
        returns
            self.pt_unaligned(),
    {
        &self.pt_unaligned
    }
}

impl<T> PointsToPhys for PointsTo<T> {
    type A = T;

    /// Delegates to the underlying `PointsToUnaligned`'s pointer.
    open spec fn ptr(self) -> *mut T {
        self.pt_unaligned().ptr()
    }

    /// The size of the pointed-to region is the size of `T`.
    open spec fn size(self) -> nat {
        size_of::<T>()
    }
}

impl<T> FixedSize for PointsTo<T> {
    /// A `PointsTo<T>` always tracks `size_of::<T>()` bytes of memory.
    open spec fn const_size() -> nat {
        size_of::<T>()
    }

    proof fn size_eq_const_size(tracked &self) {
    }
}

impl<T> PointsToProperties for PointsTo<T> {
    /// A `PointsTo` is well-formed if its pointer is aligned to `T`,
    /// and the underlying `PointsToUnaligned` is well-formed.
    open spec fn wf_basic(self) -> bool {
        &&& self.ptr()@.addr as nat % align_of::<T>() == 0
        &&& self.pt_unaligned().wf()
    }

    /// Non-nullness follows from the underlying `PointsToUnaligned`'s invariant,
    /// since `self.ptr()` and `self.pt_unaligned().ptr()` are the same pointer.
    proof fn is_nonnull(tracked &self) {
    }

    /// Delegates to the underlying `PointsToUnaligned`'s `ptr_bounds`,
    /// since `self.ptr()` and `self.pt_unaligned().ptr()` are the same pointer.
    proof fn ptr_bounds(tracked &self) {
        self.pt_unaligned.ptr_bounds();
    }

    /// Delegates to the underlying `PointsToUnaligned`'s `provenance_not_none`.
    proof fn provenance_not_none(tracked &self) {
        self.pt_unaligned.provenance_not_none();
    }

    /// Delegates to the underlying `PointsToUnaligned`'s `is_disjoint`,
    /// since the two permissions track the same memory range.
    proof fn is_disjoint<OtherPointsToPerm: PointsToPhys>(
        tracked &mut self,
        tracked other: &OtherPointsToPerm,
    ) {
        self.pt_unaligned.is_disjoint(other);
    }
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

    /// Well-formedness is defined in the `PointsToProperties` trait function `wf_basic`.
    pub open spec fn wf(&self) -> bool {
        self.wf_basic()
    }

    /// Specifies that `old` and `new` both satisfy the `PointsToUnaligned` requirements for preserving well-formed-ness.
    pub open spec fn ptrs_len_same_valid_decode(old: Self, new: Self) -> bool {
        PointsToUnaligned::<T>::ptrs_len_same_valid_decode(old.pt_unaligned(), new.pt_unaligned())
    }

    /// Ensures that if `self` is well-formed, and `other` has the same pointers and length
    /// and still satisfies decode validity,
    /// then `other` is well-formed.
    pub proof fn stays_wf(tracked self, tracked other: Self)
        requires
            self.wf(),
            Self::ptrs_len_same_valid_decode(self, other),
        ensures
            other.wf(),
    {
    }

    /// A `PointsTo<T>` is always aligned.
    pub proof fn is_aligned(tracked &self)
        requires
            self.wf(),
        ensures
            self.ptr()@.addr as nat % align_of::<T>() == 0,
    {
    }

    /// From a non-null, aligned pointer to a zero-sized type, we can construct an
    /// uninitialized `PointsTo<T>`. The memory range pointed to by this pointer will be empty.
    pub proof fn zero_sized(ptr: *mut T) -> (tracked perm: PointsTo<T>)
        requires
            ptr@.addr != 0,
            ptr@.addr as nat % align_of::<T>() == 0,
            ptr_addr_in_bounds(ptr),
            size_of::<T>() == 0,
        ensures
            perm.ptr() == ptr,
            perm.is_empty(),
            perm.bytes().len() == size_of::<T>(),
            perm.wf(),
    {
        broadcast use raw_ptr::group_raw_ptr_axioms;

        let tracked pt_unaligned = PointsToUnaligned::<T>::zero_sized(ptr);
        PointsTo { pt_unaligned: Tracked(pt_unaligned) }
    }

    /// Specializes `is_disjoint` to the case when the other permission is a `PointsTo<S>`.
    pub proof fn is_disjoint_pointsto<S>(tracked &mut self, tracked other: &PointsTo<S>)
        requires
            size_of::<T>() != 0,
            size_of::<S>() != 0,
            self.wf(),
        ensures
            *old(self) == *final(self),
            final(self).ptr() as int + size_of::<T>() <= other.ptr() as int || other.ptr() as int
                + size_of::<S>() <= final(self).ptr() as int,
    {
        self.size_eq_const_size();
        other.size_eq_const_size();
        self.is_disjoint(other);
    }

    /// Convert an aligned `PointsTo` to an unaligned `PointsToUnaligned`.
    /// This is always safe since aligned is stricter than unaligned.
    ///
    /// Ensures pointer locations remain the same, and memory
    /// initializations states remain the same.
    pub proof fn into_unaligned(tracked self) -> (tracked perm: PointsToUnaligned<T>)
        requires
            self.wf(),
        ensures
            perm@ == self@,
            perm.wf(),
    {
        self.pt_unaligned.get()
    }

    /// Borrow an aligned `PointsTo` as an unaligned `PointsToUnaligned`.
    /// This is always safe since aligned is stricter than unaligned.
    ///
    /// Ensures pointer locations remain the same, and memory
    /// initializations states remain the same.
    pub proof fn as_unaligned(tracked &self) -> (tracked perm: &PointsToUnaligned<T>)
        requires
            self.wf(),
        ensures
            perm@ == self@,
            perm.wf(),
    {
        &self.pt_unaligned
    }

    /// If the memory is valid, then the bytes must decode into the given value in memory.
    pub broadcast proof fn bytes_decode(&self)
        requires
            self.wf(),
        ensures
            self.is_valid() ==> #[trigger] abs_decode::<T>(self.bytes(), &self.value()),
            self.bytes().len() == size_of::<T>(),
    {
    }

    /// A `PointsTo<T>` can always be cast to a `PointsToUntyped`, an untyped permission to the
    /// same underlying bytes. The resulting permission carries no information about validity.
    ///
    /// The abstract bytes remain the same. This preserves the typed contents in memory on a
    /// roundtrip cast (see `PointsToUntyped::cast_to_seq_pt`).
    /// Note that this means provenance is not lost, which matches Rust's semantics for
    /// casting/transmuting in-memory values.
    ///
    /// This function also returns a `tracked Option<T>` corresponding to the `TypedValue<T>` on
    /// `self`. The use of `tracked Option<T>` prohibits creating permission-carrying types out of
    /// thin air, i.e. in the case where `T` is a type that stores/represents a permission
    /// (e.g., shared references).
    pub proof fn cast_to_untyped(tracked self) -> (tracked (dst, typed_value): (
        PointsToUntyped,
        Option<T>,
    ))
        requires
            self.wf(),
        ensures
            self.bytes() == dst.bytes(),
            self.ptr()@.addr == dst.ptr()@.addr,
            self.ptr()@.provenance == dst.ptr()@.provenance,
            dst.wf(),
            dst.len() == size_of::<T>(),
            typed_value.is_some() <==> self.is_valid(),
            typed_value.is_some() ==> typed_value.unwrap() == self.value(),
    {
        let tracked PointsTo { pt_unaligned } = self;
        let tracked PointsToUnaligned { val, pt_untyped } = pt_unaligned.get();
        let tracked typed_value = match val {
            TypedValue::Valid(b) => Some(*b),
            TypedValue::Empty => None,
        };
        (pt_untyped.get(), typed_value)
    }

    /// Creates a `PointsTo<T>` from a `PointsToUntyped` with the same provenance
    /// and a ptr corresponding to the range of the `PointsToUntyped`.
    /// The resulting `PointsTo<T>` will be empty (uninitialized).
    pub proof fn from_untyped(tracked pt_untyped: PointsToUntyped) -> (tracked out: Self)
        requires
            pt_untyped.wf(),
            pt_untyped.ptr()@.addr as int % align_of::<T>() as int == 0,
            pt_untyped.len() == size_of::<T>(),
        ensures
            out.ptr() == pt_untyped.ptr() as *mut T,
            out.bytes() == pt_untyped.bytes(),
            out.is_empty(),
            out.wf(),
    {
        PointsTo {
            pt_unaligned: Tracked(
                PointsToUnaligned { val: TypedValue::Empty, pt_untyped: Tracked(pt_untyped) },
            ),
        }
    }

    /// Creates a `PointsToUntyped` from a `PointsTo<T>` with the same provenance
    /// and a range corresponding to the address of the `PointsTo<T>` and size of `T`.
    /// If there is any value stored in memory, it is dropped.
    pub proof fn into_untyped(tracked self) -> (tracked pt_untyped: PointsToUntyped)
        requires
            self.wf(),
        ensures
            pt_untyped.ptr() as *mut T == self.ptr(),
            pt_untyped.len() == size_of::<T>(),
            pt_untyped.bytes() == self.bytes(),
            pt_untyped.wf(),
    {
        let tracked PointsTo { pt_unaligned } = self;
        let tracked PointsToUnaligned { val: _, pt_untyped } = pt_unaligned.get();
        pt_untyped.get()
    }

    /// Creates a reference to a `PointsToUntyped` from a reference to a `PointsTo<T>` with the same
    /// provenance and a range corresponding to the address of the `PointsTo<T>` and size of `T`.
    pub proof fn as_untyped(tracked &self) -> (tracked pt_untyped: &PointsToUntyped)
        requires
            self.wf(),
        ensures
            pt_untyped.ptr() as *mut T == self.ptr(),
            pt_untyped.len() == size_of::<T>(),
            pt_untyped.bytes() == self.bytes(),
            pt_untyped.wf(),
    {
        self.pt_unaligned.tracked_pt_untyped()
    }

    /// Creates a mutable reference to a `PointsToUntyped` from a mutable reference to a `PointsTo<T>`
    /// with the same provenance and a range corresponding to the address of the `PointsTo<T>` and
    /// size of `T`. If this permission carries any typed value, it is dropped here.
    /// (call `take` first if you want to save the value.)
    pub proof fn as_untyped_mut(tracked &mut self) -> (tracked pt_untyped: &mut PointsToUntyped)
        requires
            self.wf(),
        ensures
            pt_untyped.ptr() as *mut T == old(self).ptr(),
            pt_untyped.len() == size_of::<T>(),
            pt_untyped.bytes() == old(self).bytes(),
            pt_untyped.wf(),
            PointsToUntyped::ptrs_len_same(*pt_untyped, *final(pt_untyped)) ==> ({
                &&& final(self).ptr() == old(self).ptr()
                &&& final(self).bytes() == final(pt_untyped).bytes()
                &&& final(self).is_empty()
                &&& final(self).wf()
            }),
    {
        self.pt_unaligned.borrow_mut().val = TypedValue::Empty;
        &mut self.pt_unaligned.borrow_mut().pt_untyped
    }

    /// This takes a borrow of the `T` from the `TypedValue<T>` on `self`.
    pub proof fn borrow(tracked &self) -> tracked &T
        requires
            self.wf(),
            self.is_valid(),
        returns
            self.value(),
    {
        match &self.pt_unaligned.borrow().val {
            TypedValue::Valid(b) => b,
            TypedValue::Empty => proof_from_false(),
        }
    }

    /// This takes a mutable borrow of the `T` from the `TypedValue<T>` on `self`.
    ///
    /// Note: unlike `borrow`/`take`/`put`, this cannot be proven from the `TypedValue<T>`
    /// representation alone: `mut_ref_ptr` links a real Rust reference to the raw pointer it was
    /// derived from, and that linkage can only be established by an actual unsafe dereference of
    /// `self.ptr()` (as in, e.g., `ptr_mut_ref`), not by borrowing out of a ghost `Box<T>`.
    pub axiom fn borrow_mut(tracked &mut self) -> (tracked val: &mut T)
        requires
            self.wf(),
            self.is_valid(),
        ensures
            *val == old(self).value(),
            mut_ref_ptr(val) == old(self).ptr(), // Travis: not necessarily true bc Box/enum, also odd thing to want, or necessary
            final(self).is_valid(),
            final(self).ptr() == old(self).ptr(),
            final(self).value() == *final(val),
            // TODO: is this right/sound?
            Self::ptrs_len_same_valid_decode(*old(self), *final(self)) ==> final(self).wf(),
    ;
    // match

    /// This moves the `T` out from the `TypedValue<T>` on `self`, leaving `self` empty.
    pub proof fn take(tracked &mut self) -> (tracked val: T)
        requires
            self.wf(),
            self.is_valid(),
        ensures
            val == old(self).value(),
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).is_empty(),
            final(self).wf(),
            Self::ptrs_len_same_valid_decode(*old(self), *final(self)),
    {
        let tracked mut tmp = TypedValue::Empty;
        super::modes::tracked_swap(&mut tmp, &mut self.pt_unaligned.borrow_mut().val);
        match tmp {
            TypedValue::Valid(b) => *b,
            TypedValue::Empty => proof_from_false(),
        }
    }

    /// Consumes the `T` and puts it in the `TypedValue<T>` for `self`.
    pub proof fn put(tracked &mut self, tracked val: T)
        requires
            self.wf(),
            abs_decode::<T>(self.bytes(), &val),
        ensures
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).is_valid(),
            final(self).value() == val,
            final(self).wf(),
            Self::ptrs_len_same_valid_decode(*old(self), *final(self)),
    {
        self.pt_unaligned.borrow_mut().val = TypedValue::Valid(Box::new(val));
    }
}

impl<T> SeqPointsTo<T, PointsTo<T>> {
    /// In addition to the well-formed-ness properties which must hold of every `SeqPointsTo`,
    /// the `*mut T` pointer must be aligned to `T`.
    pub open spec fn wf(self) -> bool {
        &&& self.wf_basic()
        &&& self.ptr()@.addr as nat % align_of::<T>() == 0
    }

    /// A "flattened" view of the abstract bytes.
    /// Because the abstract bytes do not change across casting/transmuting, it is often more
    /// convenient to have a single flattened view of the bytes that is the same as for `PointsTo<[T]>`.
    pub open spec fn bytes(self) -> Seq<AbstractByte> {
        Self::bytes_inner(self.seq_pt())
    }

    pub open spec fn bytes_inner(perms: Seq<PointsTo<T>>) -> Seq<AbstractByte> {
        perms.fold_left(Seq::empty(), |acc: Seq<AbstractByte>, elt: PointsTo<T>| acc + elt.bytes())
    }

    pub open spec fn typed_value(self) -> Seq<TypedValue<T>> {
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
    pub open spec fn value(&self) -> Seq<T>
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

    /// Specifies that `old` and `new` have the same pointer and length,
    /// and the underlying `PointsTo<T>` permissions have the same pointer
    /// and satisfy the `PointsTo` requirements for preserving well-formed-ness.
    pub open spec fn ptrs_len_same_valid_decode(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& new.len() == old.len()
        &&& forall|i: int|
            #![trigger new[i]]
            0 <= i < new.len() ==> PointsTo::<T>::ptrs_len_same_valid_decode(old[i], new[i])
                && new[i].ptr() == old[i].ptr()
    }

    /// Ensures that if `self` is well-formed, and `other` has the same pointers and length
    /// and still satisfies decode validity,
    /// then `other` is well-formed.
    pub proof fn stays_wf(tracked self, tracked other: Self)
        requires
            self.wf(),
            Self::ptrs_len_same_valid_decode(self, other),
        ensures
            other.wf(),
    {
    }

    /// A `SeqPointsTo<T, PointsTo<T>>` is always aligned to `T`.
    pub proof fn is_aligned(tracked &self)
        requires
            self.wf(),
        ensures
            self.ptr()@.addr as nat % align_of::<T>() == 0,
    {
    }

    /// Returns a `tracked` reference to the underlying `Seq<PointsTo<T>>`,
    /// given `tracked &self`.
    pub proof fn tracked_seq_pt(tracked &self) -> (tracked ret: &Seq<PointsTo<T>>)
        requires
            self.wf(),
        ensures
            ret == self.seq_pt(),
            forall|i: int| 0 <= i < ret.len() ==> #[trigger] ret[i].wf(),
    {
        assert forall|i: int| 0 <= i < self.seq_pt().len() implies #[trigger] self.seq_pt()[i].wf() by {
            assert(self[i].wf_basic());
        }
        &self.seq_pt
    }

    /// Returns a `tracked` mutable reference to the underlying `Seq<PointsTo<T>>`,
    /// given `tracked &mut self`. `self.ptr` will remain unchanged.
    ///
    /// Provided that this mutable reference is not used to change the sequence length
    /// or any of the `PointsTo<T>` pointers, the invariant will be preserved.
    pub proof fn tracked_seq_pt_mut(tracked &mut self) -> (tracked ret: &mut Seq<PointsTo<T>>)
        requires
            self.wf(),
        ensures
            *ret == old(self).seq_pt(),
            final(self).seq_pt() == *final(ret),
            old(self).ptr() == final(self).ptr(),
            // Criteria necessary for re-establishing invariants
            Self::ptrs_len_same_valid_decode(*old(self), *final(self)) ==> final(self).wf(),
    {
        &mut self.seq_pt
    }

    /// Returns a `tracked` mutable reference to the `PointsTo<T>` permission at index `i`,
    /// given `tracked &mut self`. `self.ptr()` will remain unchanged.
    ///
    /// Provided that this mutable reference is not used to change the pointer at index `i`,
    /// the invariant will be preserved.
    pub proof fn index_mut(tracked &mut self, i: int) -> (tracked ret: &mut PointsTo<T>)
        requires
            self.wf(),
            0 <= i < self.len(),
        ensures
            final(self).ptr() == old(self).ptr(),
            *ret == old(self).seq_pt()[i],
            final(self).seq_pt() == old(self).seq_pt().update(i, *final(ret)),
            // Criteria necessary for re-establishing invariants
            ({
                &&& final(ret).ptr() == ret.ptr()
                &&& PointsTo::<T>::ptrs_len_same_valid_decode(*ret, *final(ret))
            }) ==> final(self).wf(),
    {
        broadcast use crate::vstd::seq::group_seq_axioms;

        self.seq_pt.tracked_borrow_mut(i)
    }

    /// Proof of equivalence for two different ways to get the `TypedValue<T>` at a given index `i`.
    pub broadcast proof fn typed_value_equiv(self, i: int)
        requires
            0 <= i < self.len(),
        ensures
            #![trigger self.typed_value()[i]]
            #![trigger self.seq_pt()[i]]
            self.typed_value()[i] == self.seq_pt()[i].typed_value(),
    {
        broadcast use group_vstd_default;

    }

    /// Constructs a `SeqPointsTo` from a sequence of well-formed `PointsTo<T>` permissions and a pointer,
    /// provided that the pointer is aligned, non-null, and in bounds of its provenance,
    /// and the pointer of each permission is at the expected offset from the given pointer.
    pub proof fn from_seq(tracked r: Seq<PointsTo<T>>, ptr: *mut T) -> (tracked s: Self)
        requires
            forall|i: int| 0 <= i < r.len() ==> #[trigger] r[i].wf(),
            forall|i: int|
                #![trigger r[i].ptr()@.provenance]
                #![trigger r[i].ptr()@.addr]
                0 <= i < r.len() ==> {
                    &&& r[i].ptr()@.provenance == ptr@.provenance
                    &&& r[i].ptr()@.addr == ptr@.addr + i * size_of::<T>()
                },
            ptr@.addr != 0,
            ptr@.addr as nat % align_of::<T>() == 0,
            ptr_addr_in_bounds(ptr),
        ensures
            s.seq_pt() == r,
            s.ptr() == ptr,
            s.wf(),
    {
        let tracked s = SeqPointsTo { seq_pt: r, ptr: Ghost(ptr) };
        assert forall|i: int| 0 <= i < s.len() implies #[trigger] s[i].wf_basic() by {
            assert(r[i].wf());
        }
        s
    }

    /// Given an aligned and non-null pointer,
    /// it is always possible to construct a `SeqPointsTo` with an empty sequence of permissions.
    pub proof fn empty(ptr: *mut T) -> (tracked spt: Self)
        requires
            ptr@.addr != 0,
            ptr@.addr as nat % align_of::<T>() == 0,
            ptr_addr_in_bounds(ptr),
        ensures
            spt.seq_pt() == Seq::<PointsTo<T>>::empty(),
            spt.ptr() == ptr,
            spt.len() == 0,
            spt.wf(),
    {
        broadcast use group_vstd_default;

        SeqPointsTo { seq_pt: Seq::tracked_empty(), ptr: Ghost(ptr) }
    }

    /// We can construct a `SeqPointsTo` with `length`-many `PointsTo` permissions,
    /// provided that `T` is zero-sized and that the pointer is non-null and aligned.
    pub proof fn zero_sized(ptr: *mut T, length: nat) -> (tracked spt: Self)
        requires
            ptr@.addr != 0,
            ptr@.addr as nat % align_of::<T>() == 0,
            ptr_addr_in_bounds(ptr),
            size_of::<T>() == 0,
        ensures
            forall|i| #![auto] 0 <= i < spt.len() ==> spt[i].is_empty(),
            spt.ptr() == ptr,
            spt.len() == length,
            spt.wf(),
    {
        Self::empty(ptr).zero_sized_helper(length, length)
    }

    proof fn zero_sized_helper(tracked self, remaining: nat, total: nat) -> (tracked spt: Self)
        requires
            self.ptr()@.addr != 0,
            self.ptr()@.addr as nat % align_of::<T>() == 0,
            size_of::<T>() == 0,
            self.len() + remaining == total,
            forall|i| #![auto] 0 <= i < self.len() ==> self[i].is_empty(),
            self.wf(),
            self.ptr()@.provenance.is_some() ==> {
                &&& self.ptr()@.addr as int >= self.ptr()@.provenance.data().start_addr()
                &&& self.ptr()@.addr <= self.ptr()@.provenance.data().start_addr()
                    + self.ptr()@.provenance.data().alloc_len()
            },
        ensures
            spt.ptr() == self.ptr(),
            spt.len() == total,
            forall|i| #![auto] 0 <= i < spt.len() ==> spt[i].is_empty(),
            spt.wf(),
        decreases remaining,
    {
        broadcast use group_vstd_default;

        if remaining == 0 {
            self
        } else {
            let tracked zs_pt = PointsTo::zero_sized(self.ptr());
            let tracked mut mut_spt = self;
            mut_spt.seq_pt.tracked_push(zs_pt);
            Self::bytes_len_helper(mut_spt.seq_pt());

            assert(PointsTo::<T>::const_size() == 0);
            assert(mut_spt.wf_basic());
            assert(mut_spt.wf());

            mut_spt.zero_sized_helper((remaining - 1) as nat, total)
        }
    }

    /// The length of the flattened abstract bytes for a sequence of well-formed permissions
    /// matches the size of this type multiplied by the number of elements in the sequence.
    proof fn bytes_len_helper(perms: Seq<PointsTo<T>>)
        requires
            forall|i: int| 0 <= i < perms.len() ==> #[trigger] perms[i].wf(),
        ensures
            Self::bytes_inner(perms).len() == perms.len() * size_of::<T>(),
        decreases perms.len(),
    {
        broadcast use
            crate::vstd::seq::group_seq_axioms,
            crate::vstd::type_representation::encode_decode_len,
        ;

        if perms.len() > 0 {
            Self::bytes_len_helper(perms.drop_last());
            assert(perms.last() == perms[perms.len() - 1]);
            assert(perms[perms.len() - 1].wf());
            assert(perms.last().wf());
            assert(perms.last().wf_basic());
            assert(perms.last().pt_unaligned().wf());
            assert(perms.last().pt_unaligned().wf_basic());
            assert(perms.last().bytes().len() == size_of::<T>());
            assert((perms.len() - 1) * size_of::<T>() + size_of::<T>() == perms.len() * size_of::<
                T,
            >()) by (nonlinear_arith);
        }
    }

    /// The length of the abstract bytes matches the size of this type multiplied by the number of elements this permission represents.
    pub broadcast proof fn bytes_len(&self)
        requires
            self.wf(),
        ensures
            #[trigger] self.bytes().len() == self.len() * size_of::<T>(),
    {
        Self::bytes_len_helper(self.seq_pt());
    }

    // Relates the abstract bytes for a sequence of permissions to subranges of those permissions and subranges of the abstract bytes.
    // Useful for avoiding reasoning about fold_left directly.
    proof fn bytes_subrange(perms: Seq<PointsTo<T>>, split: int)
        requires
            0 <= split <= perms.len(),
            forall|i: int| 0 <= i < perms.len() ==> #[trigger] perms[i].wf(),
        ensures
    // abstract bytes can be split by subranges of the permissions themselves

            Self::bytes_inner(perms) == Self::bytes_inner(perms.subrange(0, split))
                + Self::bytes_inner(perms.subrange(split, perms.len() as int)),
            // abstract bytes of a prefix of permssions correspond to a prefix of the entire abstract bytes
            Self::bytes_inner(perms.subrange(0, split)) == Self::bytes_inner(perms).subrange(
                0,
                split * size_of::<T>(),
            ),
            // abstract bytes of a suffix of permissions correspond to suffix of the entire abstract bytes
            Self::bytes_inner(perms.subrange(split, perms.len() as int)) == Self::bytes_inner(
                perms,
            ).subrange(split * size_of::<T>(), perms.len() as int * size_of::<T>()),
            // the abstract bytes of a prefix of permissions has the expected length
            Self::bytes_inner(perms.subrange(0, split)).len() == split * size_of::<T>(),
            // the abstract bytes of a suffix of permissions has the expected length
            Self::bytes_inner(perms.subrange(split, perms.len() as int)).len() == (perms.len()
                - split) * size_of::<T>(),
        decreases perms.len() - split,
    {
        broadcast use group_vstd_default, crate::vstd::arithmetic::mul::group_mul_basics;

        if perms.len() > split {
            Self::bytes_subrange(perms.subrange(0, perms.len() - 1), split);
            perms.lemma_slice_of_slice(0, perms.len() - 1, 0, split);
            perms.lemma_slice_of_slice(0, perms.len() - 1, split, perms.len() - 1);
            assert(Self::bytes_inner(perms.subrange(0, perms.len() - 1)) == Self::bytes_inner(
                perms.subrange(0, split),
            ) + Self::bytes_inner(perms.subrange(split, perms.len() - 1)));

            assert(perms.last() == perms[perms.len() - 1]);
            assert(perms.drop_last() == perms.subrange(0, perms.len() - 1));
            assert(Self::bytes_inner(perms) == Self::bytes_inner(perms.subrange(0, perms.len() - 1))
                + perms[perms.len() - 1].bytes());
            assert(perms.subrange(split, perms.len() as int).last() == perms[perms.len() - 1]);
            assert(perms.subrange(split, perms.len() as int).drop_last() == perms.subrange(
                split,
                perms.len() - 1,
            ));
            assert(Self::bytes_inner(perms.subrange(split, perms.len() as int))
                == Self::bytes_inner(perms.subrange(split, perms.len() - 1)) + perms[perms.len()
                - 1].bytes());

            Self::bytes_len_helper(perms.subrange(0, split));
            Self::bytes_len_helper(perms.subrange(split, perms.len() as int));
            assert(perms.subrange(split, perms.len() as int).len() == perms.len() - split);
            assert(Self::bytes_inner(perms.subrange(0, perms.len() - 1).subrange(0, split)).len()
                == Self::bytes_inner(perms.subrange(0, split)).len());
            assert(Self::bytes_inner(perms).len() - Self::bytes_inner(
                perms.subrange(0, split),
            ).len() == Self::bytes_inner(perms.subrange(split, perms.len() as int)).len());
            assert(perms.len() * size_of::<T>() - split * size_of::<T>() == (perms.len() - split)
                * size_of::<T>()) by (nonlinear_arith);
        } else {
            Self::bytes_len_helper(perms);
        }
    }

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
    {
        broadcast use group_vstd_default;

        Self::bytes_len_helper(self.seq_pt());

        Self::bytes_subrange(self.seq_pt(), i + 1);
        Self::bytes_subrange(self.seq_pt().subrange(0, i + 1), i);
        assert(self.seq_pt()[i] == self.seq_pt().subrange(0, i + 1).subrange(i, i + 1)[0]);
        self.bytes().lemma_slice_of_slice(
            0,
            (i + 1) * size_of::<T>(),
            i * size_of::<T>(),
            (i + 1) * size_of::<T>(),
        );
    }

    /// For all positions in this sequence, the bytes for that position (given `self.wf()`)
    /// can be decoded into the value in memory at that position.
    proof fn bytes_decode_helper(&self, len: int)
        requires
            0 <= len <= self.len(),
            self.wf(),
        ensures
            forall|i: int|
                0 <= i < len ==> {
                    &&& (#[trigger] self.typed_value()[i]).is_valid() ==> abs_decode::<T>(
                        self.seq_pt()[i].bytes(),
                        &self.typed_value()[i].value(),
                    )
                    &&& self.seq_pt()[i].bytes().len() == size_of::<T>()
                },
        decreases len,
    {
        if len > 0 {
            self.bytes_decode_helper(len - 1);
            assert(self.seq_pt()[len - 1].wf());
            self.typed_value_equiv(len - 1);
        }
    }

    /// For all positions in this sequence, the abstract bytes for that position can be decoded into the value in memory at that position.
    pub proof fn bytes_decode(&self)
        requires
            self.wf(),
        ensures
            forall|i: int|
                0 <= i < self.len() ==> {
                    &&& (#[trigger] self.typed_value()[i]).is_valid() ==> abs_decode::<T>(
                        self.bytes().subrange(i * size_of::<T>(), (i + 1) * size_of::<T>()),
                        &self.typed_value()[i].value(),
                    )
                    &&& self.seq_pt()[i].bytes().len() == size_of::<T>()
                },
    {
        broadcast use SeqPointsTo::bytes_equiv;

        self.bytes_decode_helper(self.len() as int);
    }

    /// Casts a `SeqPointsTo<T, PointsTo<T>>` to a `PointsToUntyped` covering the same bytes.
    /// The resulting `PointsToUntyped` has the same address and provenance and a length of
    /// `self.len() * size_of::<T>()`, and preserves the abstract bytes.
    /// It carries no information about validity, so it cannot be read from as a `T`.
    /// The returned `tracked typed_value` holds the typed contents from this memory,
    /// which can later be used to cast the `dst` permission back to a typed permission.
    pub proof fn cast_to_untyped(tracked self) -> (tracked (dst, typed_value): (
        PointsToUntyped,
        Seq<Option<T>>,
    ))
        requires
            self.wf(),
        ensures
            dst.ptr() == ptr_mut_from_data::<[u8]>(
                PtrData {
                    addr: self.ptr()@.addr,
                    provenance: self.ptr()@.provenance,
                    metadata: (self.len() * size_of::<T>()) as usize,
                },
            ),
            dst.bytes() == self.bytes(),
            forall|i: int|
                0 <= i < self.len() ==> {
                    &&& typed_value[i].is_some() <==> (#[trigger] self[i]).is_valid()
                    &&& typed_value[i].is_some() ==> typed_value[i].unwrap() == self[i].value()
                },
            typed_value.len() == self.len(),
            dst.wf(),
        decreases self.len(),
    {
        let ghost ghost_self = self;
        if self.len() == 0 {
            assert(self.len() * size_of::<T>() == 0) by (nonlinear_arith)
                requires
                    self.len() == 0,
            ;
            let tracked dst = SeqPointsTo {
                seq_pt: Seq::tracked_empty(),
                ptr: Ghost(
                    ptr_mut_from_data::<[u8]>(
                        PtrData {
                            addr: self.ptr()@.addr,
                            provenance: self.ptr()@.provenance,
                            metadata: 0,
                        },
                    ),
                ),
            };
            (dst, Seq::tracked_empty())
        } else {
            let tracked mut seq_pt = self.seq_pt;
            let tracked last = seq_pt.tracked_pop();
            let tracked head = SeqPointsTo { seq_pt: seq_pt, ptr: self.ptr };
            let ghost ghost_head = head;
            let ghost ghost_last = last;
            let tracked (head_u8, mut head_typed_value) = head.cast_to_untyped();
            let tracked (last_u8, last_typed_value) = last.cast_to_untyped();
            head_typed_value.tracked_push(last_typed_value);
            let tracked dst = head_u8.join(last_u8);

            ghost_self.bytes_len();

            assert forall|i: int| 0 <= i < ghost_self.len() implies {
                &&& head_typed_value[i].is_some() <==> (#[trigger] ghost_self[i]).is_valid()
                &&& head_typed_value[i].is_some() ==> head_typed_value[i].unwrap()
                    == ghost_self[i].value()
            } by {
                if i < ghost_self.len() - 1 {
                    assert(ghost_head[i] == ghost_self[i]);
                } else {
                    assert(ghost_last == ghost_self[i]);
                }
            }
            (dst, head_typed_value)
        }
    }

    /// Creates a `PointsToUntyped` from a `SeqPointsTo<T, PointsTo<T>>` with the same address and
    /// provenance and a length of `self.len() * size_of::<T>()`.
    /// If there are any typed values stored in memory, they are dropped here.
    /// (Use `cast_to_untyped` instead if you want to keep them.)
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
    {
        let tracked (pt_untyped, _) = self.cast_to_untyped();
        pt_untyped
    }

    /// Creates a `SeqPointsTo<T, PointsTo<T>>` of length `len` from a `PointsToUntyped` with the
    /// same provenance and a ptr corresponding to the range of the `PointsToUntyped`.
    /// The resulting permission will be empty (uninitialized).
    /// (Use `PointsToUntyped::cast_to_seq_pt` instead if you want to supply typed values.)
    pub proof fn from_untyped(tracked pt_untyped: PointsToUntyped, len: usize) -> (tracked out: Self)
        requires
            pt_untyped.wf(),
            pt_untyped.ptr()@.addr as nat % align_of::<T>() == 0,
            pt_untyped.len() == len * size_of::<T>(),
        ensures
            out.ptr() == pt_untyped.ptr() as *mut T,
            out.len() == len,
            out.bytes() == pt_untyped.bytes(),
            out.is_fully_empty(),
            out.wf(),
    {
        let tracked mut out = pt_untyped.cast_to_seq_pt::<T>(len, Seq::tracked_empty());
        // `cast_to_seq_pt` says nothing about the validity of elements past the supplied
        // `typed_value`, so empty all of them.
        let ghost before = out;
        let tracked _taken = out.take_typed_value_subrange(0, len as int);
        assert(out.typed_value().len() == before.typed_value().len());
        assert(out.len() == len);
        assert forall|i: int| 0 <= i < out.len() implies #[trigger] out[i].is_empty() by {
            out.typed_value_equiv(i);
            assert(out.typed_value()[i] == TypedValue::<T>::Empty);
        }
        out
    }

    // May need axiom for taking &Seq<PointsToUntyped> -> &PointsToUntyped
    /// Creates a reference to a `PointsToUntyped` from a reference to a `SeqPointsTo<T, PointsTo<T>>`,
    /// with the same address and provenance, a length of `self.len() * size_of::<T>()`,
    /// and the same abstract bytes.
    ///
    /// This is an axiom because the `SeqPointsTo` does not store a `PointsToUntyped` that can be borrowed.
    pub axiom fn as_untyped(tracked &self) -> (tracked raw: &PointsToUntyped)
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

    // axiom for &mut Seq<PointsToUntyped> -> &mut PointsToUntyped
    // Need way to combine two PointsToUptyped.
    // Can merge maps, so can merge maps of PointsToSingleton.
    // Either axiomatize PointsToUntyped combo or axiomatize conversion to PointsToRaw

    // PointToSingleton - single byte
    // PointsToUntyped - Seq<PointsToSingleton>
    // PointsToRaw - Map/Set<PointsToSingleton>

    /// Creates a mutable reference to a `PointsToUntyped` from a mutable reference to a
    /// `SeqPointsTo<T, PointsTo<T>>`, with the same address and provenance and a length of
    /// `self.len() * size_of::<T>()`. If this permission carries any typed values, they are dropped here.
    ///
    /// This is an axiom because the `SeqPointsTo` does not store a `PointsToUntyped` that can be borrowed.
    pub axiom fn as_untyped_mut(tracked &mut self) -> (tracked raw: &mut PointsToUntyped)
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
            // Criteria necessary for re-establishing invariants
            PointsToUntyped::ptrs_len_same(*raw, *final(raw)) ==> ({
                &&& final(self).ptr() == old(self).ptr()
                &&& final(self).len() == old(self).len()
                &&& final(self).bytes() == final(raw).bytes()
                &&& final(self).is_fully_empty()
                &&& final(self).wf()
            }),
    ;

    // Use shr_ref_wrapper
    /// Given that the subrange is within bounds, it is always possible to borrow a permission
    /// to just that subrange.
    pub axiom fn subrange(tracked &self, start_index: nat, len: nat) -> (tracked sub: &Self)
        requires
            self.wf(),
            start_index + len <= self.len(),
        ensures
            sub.wf(),
            sub.ptr() == ptr_mut_from_data::<T>(
                PtrData {
                    addr: ((self.ptr()@.addr + start_index * size_of::<T>()) as usize),
                    provenance: self.ptr()@.provenance,
                    metadata: (),
                },
            ),
            sub.seq_pt() == self.seq_pt().subrange(start_index as int, (start_index + len) as int),
    ;

    // &Seq<PointsTo<T>> -> &Seq<TypedValue<T>> where PointsTo<T> holds a TypedValue<T>
    // Seq<&TypedValue<T>> - try to make this the return type instead
    /// This takes a borrow of a subrange of the `TypedValue<T>`s from `self`.
    pub axiom fn borrow_typed_value_subrange(tracked &self, start: int, end: int) -> (tracked val:
        &Seq<TypedValue<T>>)
        requires
            self.wf(),
            0 <= start <= end <= self.len(),
        ensures
            val == self.typed_value().subrange(start, end),
    ;

    /// Copies the first `n` `TypedValue<T>`s out of a shared reference to a sequence, given that `T` is `Copy`.
    proof fn copy_typed_values(tracked val: &Seq<TypedValue<T>>, n: nat) -> (tracked out: Seq<
        TypedValue<T>,
    >) where T: Copy
        requires
            n <= val.len(),
        ensures
            out == val.take(n as int),
        decreases n,
    {
        if n == 0 {
            Seq::tracked_empty()
        } else {
            let tracked mut out = Self::copy_typed_values(val, (n - 1) as nat);
            let tracked last = val.tracked_borrow((n - 1) as int).tracked_copy();
            out.tracked_push(last);
            out
        }
    }

    /// Copies the given `TypedValue<T>`s into the subrange starting at `start`.
    pub proof fn copy_typed_value_subrange(
        tracked &mut self,
        start: int,
        tracked val: &Seq<TypedValue<T>>,
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
            final(self).typed_value() == old(self).typed_value().update_subrange_with(start, *val),
            final(self).wf(),
    {
        let tracked copied = Self::copy_typed_values(val, val.len());
        self.put_typed_value_subrange(start, copied);
    }

    /// This moves a subrange of the `TypedValue<T>`s out from `self`, leaving that subrange empty.
    pub proof fn take_typed_value_subrange(tracked &mut self, start: int, end: int) -> (tracked val:
        Seq<TypedValue<T>>)
        requires
            self.wf(),
            0 <= start <= end <= self.len(),
        ensures
            val == old(self).typed_value().subrange(start, end),
            final(self).ptr() == old(self).ptr(),
            final(self).bytes() == old(self).bytes(),
            final(self).typed_value() == old(self).typed_value().update_subrange_with(
                start,
                Seq::new((end - start) as nat, |i: int| TypedValue::Empty),
            ),
            final(self).wf(),
        decreases end - start,
    {
        if start == end {
            Seq::tracked_empty()
        } else {
            let ghost old_self = *self;

            // Take the last value in the range out of the element at `end - 1`
            let tracked elt = self.index_mut(end - 1);
            let tracked mut taken = TypedValue::Empty;
            super::modes::tracked_swap(&mut taken, &mut elt.pt_unaligned.borrow_mut().val);

            // The bytes of the whole sequence are unchanged
            Self::bytes_inner_ext(old_self.seq_pt(), self.seq_pt());

            // Take the rest of the range out of the preceding elements
            let tracked mut val = self.take_typed_value_subrange(start, end - 1);
            val.tracked_push(taken);

            val
        }
    }

    /// The flattened abstract bytes depend only on the abstract bytes of each individual permission.
    proof fn bytes_inner_ext(a: Seq<PointsTo<T>>, b: Seq<PointsTo<T>>)
        requires
            a.len() == b.len(),
            forall|i: int| 0 <= i < a.len() ==> #[trigger] a[i].bytes() == b[i].bytes(),
        ensures
            Self::bytes_inner(a) == Self::bytes_inner(b),
        decreases a.len(),
    {
        if a.len() > 0 {
            Self::bytes_inner_ext(a.drop_last(), b.drop_last());
        }
    }

    /// Consumes the `Seq<T>` and puts it in the specified subrange of the `TypedValue<T>`s for `self`.
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
            final(self).typed_value() == old(self).typed_value().update_subrange_with(
                start,
                Seq::new(val.len(), |i: int| TypedValue::Valid(Box::new(val[i]))),
            ),
            final(self).wf(),
        decreases val.len(),
    {
        if val.len() > 0 {
            let ghost old_self = *self;
            let tracked mut rest = val;
            let tracked first = rest.tracked_pop_front();

            // Put the first value into the element at `start`
            old_self.bytes_equiv(start);
            let tracked elt = self.index_mut(start);
            elt.put(first);

            // The bytes of the whole sequence are unchanged
            Self::bytes_inner_ext(old_self.seq_pt(), self.seq_pt());

            // Put the rest of the values into the following elements
            self.put_subrange(start + 1, rest);
        }
    }

    /// Consumes the `Seq<TypedValue<T>>` and puts it in the specified subrange of the
    /// `TypedValue<T>`s for `self`.
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
            final(self).typed_value() == old(self).typed_value().update_subrange_with(start, val),
            final(self).wf(),
        decreases val.len(),
    {
        if val.len() > 0 {
            let ghost old_self = *self;
            let tracked mut rest = val;
            let tracked first = rest.tracked_pop_front();

            // Put the first value into the element at `start`
            old_self.bytes_equiv(start);
            let tracked elt = self.index_mut(start);
            elt.pt_unaligned.borrow_mut().val = first;

            // The bytes of the whole sequence are unchanged
            Self::bytes_inner_ext(old_self.seq_pt(), self.seq_pt());

            // Put the rest of the values into the following elements
            self.put_typed_value_subrange(start + 1, rest);
        }
    }

    /// Splits the `SeqPointsTo` into two permissions at the index boundary `mid`.
    pub proof fn split(tracked self, mid: nat) -> (tracked (first, second): (Self, Self))
        requires
            0 <= mid <= self.len(),
            self.wf(),
        ensures
            first.seq_pt() == self.seq_pt().take(mid as int),
            second.seq_pt() == self.seq_pt().skip(mid as int),
            first.bytes() == self.bytes().take(mid as int * size_of::<T>()),
            second.bytes() == self.bytes().skip(mid as int * size_of::<T>()),
            first.ptr() == self.ptr(),
            second.ptr() == ptr_mut_from_data(
                PtrData::<T> {
                    addr: (self.ptr()@.addr + mid * size_of::<T>()) as usize,
                    provenance: self.ptr()@.provenance,
                    metadata: self.ptr()@.metadata,
                },
            ),
            first.wf(),
            second.wf(),
    {
        if self.len() != 0 && size_of::<T>() != 0 {
            assert(size_of::<T>() * self.len() != 0) by (nonlinear_arith)
                requires
                    self.len() != 0,
                    size_of::<T>() != 0,
            ;
            self.provenance_not_none();
            self.ptr_bounds();
        }
        let ghost ghost_self = self;

        let tracked mut seq_pt = self.seq_pt;
        let tracked other = seq_pt.tracked_skip(mid as int);

        let tracked first = SeqPointsTo { seq_pt: seq_pt, ptr: self.ptr };
        let tracked second = SeqPointsTo {
            seq_pt: other,
            ptr: Ghost(
                ptr_mut_from_data(
                    PtrData::<T> {
                        addr: (self.ptr()@.addr + mid * size_of::<T>()) as usize,
                        provenance: self.ptr()@.provenance,
                        metadata: self.ptr()@.metadata,
                    },
                ),
            ),
        };
        Self::bytes_subrange(ghost_self.seq_pt(), mid as int);

        if ghost_self.len() == 0 || size_of::<T>() == 0 {
            assert(mid * size_of::<T>() == 0) by (nonlinear_arith)
                requires
                    mid == 0 || size_of::<T>() == 0,
            ;
        } else {
            assert(mid * size_of::<T>() <= ghost_self.len() * size_of::<T>()) by (nonlinear_arith)
                requires
                    mid <= ghost_self.len(),
            ;
            assert((ghost_self.ptr()@.addr + mid * size_of::<T>()) as nat % align_of::<T>() == 0)
                by {
                broadcast use
                    crate::vstd::arithmetic::div_mod::lemma_mul_mod_noop_right,
                    crate::vstd::arithmetic::div_mod::lemma_add_mod_noop,
                    layout_of_sized,
                ;

            }
        }
        assert forall|i: int| 0 <= i < second.len() implies #[trigger] second[i].ptr()@.addr
            == second.ptr()@.addr + i * size_of::<T>() by {
            assert(ghost_self.ptr()@.addr + (i + mid) * size_of::<T>() == ghost_self.ptr()@.addr
                + mid * size_of::<T>() + i * size_of::<T>()) by (nonlinear_arith);
        }
        (first, second)
    }

    /// Concatenates `SeqPointsTo` permissions `self` and `other`,
    /// provided their pointers have the same provenance
    /// and `other`'s pointer starts at the end of `self`'s range.
    pub proof fn join(tracked self, tracked other: Self) -> (tracked joined: Self)
        requires
            self.wf(),
            other.wf(),
            self.ptr()@.provenance == other.ptr()@.provenance,
            other.ptr()@.addr == self.ptr()@.addr + self.len() * size_of::<T>(),
        ensures
            joined.ptr() == self.ptr(),
            joined.seq_pt() == self.seq_pt() + other.seq_pt(),
            joined.bytes() == self.bytes() + other.bytes(),
            joined.wf(),
    {
        let ghost ghost_self = self;
        let ghost ghost_other = other;

        let tracked mut seq_pt = self.seq_pt;
        seq_pt.tracked_add(other.seq_pt);
        let tracked joined = SeqPointsTo { seq_pt: seq_pt, ptr: self.ptr };

        assert forall|i: int| 0 <= i < joined.len() implies #[trigger] joined.seq_pt()[i].wf() by {
            if i < ghost_self.len() {
                assert(ghost_self[i].wf_basic());
            } else {
                assert(ghost_other[i - ghost_self.len()].wf_basic());
            }
        }
        Self::bytes_subrange(joined.seq_pt(), ghost_self.len() as int);
        assert(joined.seq_pt().subrange(0, ghost_self.len() as int) =~= ghost_self.seq_pt());
        assert(joined.seq_pt().subrange(ghost_self.len() as int, joined.len() as int)
            =~= ghost_other.seq_pt());

        assert forall|i: int| 0 <= i < joined.len() implies #[trigger] joined[i].ptr()@.addr
            == joined.ptr()@.addr + i * size_of::<T>() by {
            if i >= ghost_self.len() {
                assert(ghost_self.ptr()@.addr + ghost_self.len() * size_of::<T>() + (i
                    - ghost_self.len()) * size_of::<T>() == ghost_self.ptr()@.addr + i
                    * size_of::<T>()) by (nonlinear_arith);
            }
        }
        joined
    }

    // cam probably have axiom splitting mutable reference in two and . 
    // would need general-purpose way to prove &mut transmutes
    // &mut Seq<PointsTo<T>> -> (&mut Seq<PointsToUntyped>, &mut Seq<TypedValue<T>>)
    // -> (&mut PointsToUntyped, &mut Seq<TypedValue<T>>)

    /// Returns a mutable reference to the sub-permission covering indices `[i, j)`.
    /// The sub-permission has the same provenance, and its pointer is offset from `self.ptr()`
    /// by `i * size_of::<T>()`.
    ///
    /// Provided that the mutable reference is not used to change the pointer or length of the
    /// sub-permission, and that it is still well-formed, `self` is also still well-formed,
    /// with the sub-sequence of permissions replaced by the final sub-permission's.
    pub axiom fn subrange_mut(tracked &mut self, i: nat, j: nat) -> (tracked r: &mut Self)
        requires
            self.wf(),
            0 <= i <= j <= self.len(),
        ensures
            r.wf(),
            r.ptr() == ptr_mut_from_data::<T>(
                PtrData {
                    addr: ((old(self).ptr()@.addr + i * size_of::<T>()) as usize),
                    provenance: old(self).ptr()@.provenance,
                    metadata: (),
                },
            ),
            r.seq_pt() == old(self).seq_pt().subrange(i as int, j as int),
            // Criteria necessary for re-establishing invariants
            final(r).wf() && final(r).ptr() == r.ptr() && final(r).len() == r.len() ==> {
                &&& final(self).wf()
                &&& final(self).ptr() == old(self).ptr()
                &&& final(self).seq_pt() == old(self).seq_pt().subrange(0, i as int)
                    + final(r).seq_pt() + old(self).seq_pt().subrange(
                    j as int,
                    old(self).len() as int,
                )
            },
    ;

    /// Consumes this `SeqPointsTo`, returning the underlying `Seq<PointsTo<T>>`.
    pub proof fn into_seq(tracked self) -> (tracked r: Seq<PointsTo<T>>)
        requires
            self.wf(),
        ensures
            r == self.seq_pt(),
            forall|i: int| 0 <= i < r.len() ==> #[trigger] r[i].wf(),
    {
        assert forall|i: int| 0 <= i < self.seq_pt().len() implies #[trigger] self.seq_pt()[i].wf() by {
            assert(self[i].wf_basic());
        }
        self.seq_pt
    }

    /// Specializes `is_disjoint` to the case when the other permission is a `SeqPointsTo<S, PointsTo<S>>`.
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
        ensures
            *old(self) == *final(self),
            final(self).ptr() as int + final(self).len() * size_of::<T>() <= other.ptr() as int
                || other.ptr() as int + other.len() * size_of::<S>() <= final(self).ptr() as int,
    {
        broadcast use crate::vstd::arithmetic::mul::lemma_mul_nonzero;

        assert(self.size() == self.len() * size_of::<T>());
        assert(other.size() == other.len() * size_of::<S>());
        self.is_disjoint(other);
    }
}

} // verus!
