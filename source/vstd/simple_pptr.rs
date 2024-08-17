use super::layout::*;
use super::prelude::*;
use super::raw_ptr;
use super::raw_ptr::*;

verus! {

/// `PPtr` (which stands for "permissioned pointer")
/// is a wrapper around a raw pointer to a heap-allocated `V`.
/// This is designed to be simpler to use that Verus's
/// [more general pointer support](`vstd::raw_ptr`),
/// but also to serve as a better introductory point.
///
/// Technically, it is a wrapper around `*mut mem::MaybeUninit<V>`, that is, the object
/// it points to may be uninitialized.
///
/// In order to access (read or write) the value behind the pointer, the user needs
/// a special _ghost permission token_, [`PointsTo<V>`](PointsTo). This object is `tracked`,
/// which means that it is "only a proof construct" that does not appear in code,
/// but its uses _are_ checked by the borrow-checker. This ensures memory safety,
/// data-race-freedom, prohibits use-after-free, etc.
///
/// ### PointsTo objects.
///
/// The [`PointsTo`] object represents both the ability to access the data behind the
/// pointer _and_ the ability to free it (return it to the memory allocator).
///
/// In particular:
///  * When the user owns a `PointsTo<V>` object associated to a given pointer,
///    they can either read or write its contents, or deallocate ("free") it.
///  * When the user has a shared borrow, `&PointsTo<.>`, they can read
///    the contents (i.e., obtained a shared borrow `&V`).
///
/// The `perm: PointsTo<V>` object tracks two pieces of data:
///  * `perm.addr()` is the address that the permission is associated to, given
///      as a `usize`
///  * `perm.value()` tracks the data that is behind the pointer. Thereby:
///      * When the user uses the permission to _read_ a value, they always
///        read the value as given by the `perm.value`.
///      * When the user uses the permission to _write_ a value, the `perm.value`
///        data is updated.
///  * `perm.is_init()` tracks whether the memory is initialized. (`perm.is_init()` and `perm.value()` can be replaced by `perm.opt_value()`).
///
/// For those familiar with separation logic, the `PointsTo` object plays a role
/// similar to that of the "points-to" operator, _ptr_ ↦ _value_.
///
/// ### Differences from `PCell`.
///
/// `PPtr` is similar to [`cell::PCell`], but has a few key differences:
///  * In `PCell<V>`, the type `V` is placed internally to the `PCell`, whereas with `PPtr`,
///    the type `V` is placed at some location on the heap.
///  * Since `PPtr` is just a pointer (represented by an integer), it can be `Copy`.
///  * The `ptr::PointsTo` token represents not just the permission to read/write
///    the contents, but also to deallocate.
///
/// ### Simplifications relative to more general pointer API
///
///  * Pointers are only represented by addresses and don't have a general notion of provenance
///  * Pointers are untyped (only `PointsTo` is typed).
///  * The `PointsTo` also encapsulates the permission to free a pointer.
///  * `PointsTo` tokens are non-fungible. They can't be broken up or made variable-sized.
///
/// ### Example (TODO)
pub struct PPtr(pub usize);

/// A `tracked` ghost object that gives the user permission to dereference a pointer
/// for reading or writing, or to free the memory at that pointer.
///
/// The meaning of a `PointsTo` object is given by the data in its
/// `View` object, [`PointsToData`].
///
/// See the [`PPtr`] documentation for more details.
pub tracked struct PointsTo<V> {
    points_to: raw_ptr::PointsTo<V>,
    exposed: raw_ptr::IsExposed,
    dealloc: Option<raw_ptr::Dealloc>,
}

#[verusfmt::skip]
broadcast use
    super::raw_ptr::group_raw_ptr_axioms,
    super::set_lib::group_set_lib_axioms,
    super::set::group_set_axioms;

impl PPtr {
    /// Use `addr` instead
    #[verifier::inline]
    pub open spec fn spec_addr(p: PPtr) -> usize {
        p.0
    }

    /// Cast a pointer to an integer.
    #[inline(always)]
    #[verifier::when_used_as_spec(spec_addr)]
    pub fn addr(self) -> (u: usize)
        ensures
            u == self.addr(),
    {
        self.0
    }

    /// Cast an integer to a pointer.
    ///
    /// Note that this does _not_ require or ensure that the pointer is valid.
    /// Of course, if the user creates an invalid pointer, they would still not be able to
    /// create a valid [`PointsTo`] token for it, and thus they would never
    /// be able to access the data behind the pointer.
    ///
    /// This is analogous to normal Rust, where casting to a pointer is always possible,
    /// but dereferencing a pointer is an `unsafe` operation.
    /// With PPtr, casting to a pointer is likewise always possible,
    /// while dereferencing it is only allowed when the right preconditions are met.
    #[inline(always)]
    pub fn from_addr(u: usize) -> (s: Self)
        ensures
            u == s.addr(),
    {
        PPtr(u)
    }
}

impl<V> PointsTo<V> {
    #[verifier::inline]
    pub open spec fn pptr(&self) -> PPtr {
        PPtr(self.addr())
    }

    pub closed spec fn addr(self) -> usize {
        self.points_to.ptr().addr()
    }

    // TODO make this a user-defined type invariant
    #[verifier::type_invariant]
    closed spec fn wf(self) -> bool {
        &&& self.points_to.ptr()@.metadata == Metadata::Thin
        &&& self.points_to.ptr()@.provenance == self.exposed.provenance()
        &&& match self.dealloc {
            Some(dealloc) => {
                &&& dealloc.addr() == self.points_to.ptr().addr()
                &&& dealloc.size() == size_of::<V>()
                &&& dealloc.align() == align_of::<V>()
                &&& dealloc.provenance() == self.points_to.ptr()@.provenance
                &&& size_of::<V>() > 0
            },
            None => { size_of::<V>() == 0 },
        }
        &&& self.points_to.ptr().addr() != 0
    }

    pub closed spec fn opt_value(&self) -> MemContents<V> {
        self.points_to.opt_value()
    }

    #[verifier::inline]
    pub open spec fn is_init(&self) -> bool {
        self.opt_value().is_init()
    }

    #[verifier::inline]
    pub open spec fn is_uninit(&self) -> bool {
        self.opt_value().is_uninit()
    }

    #[verifier::inline]
    pub open spec fn value(&self) -> V
        recommends
            self.is_init(),
    {
        self.opt_value().value()
    }

    pub proof fn is_nonnull(tracked &self)
        ensures
            self.addr() != 0,
    {
        use_type_invariant(self);
    }

    pub proof fn leak_contents(tracked &mut self)
        ensures
            self.pptr() == old(self).pptr(),
            self.is_uninit(),
    {
        use_type_invariant(&*self);
        self.points_to.leak_contents();
    }

    /// Note: If both S and V are non-zero-sized, then this implies the pointers
    /// have distinct addresses.
    pub proof fn is_disjoint<S>(&mut self, other: &PointsTo<S>)
        ensures
            *old(self) == *self,
            self.addr() + size_of::<V>() <= other.addr() || other.addr() + size_of::<S>()
                <= self.addr(),
    {
        self.points_to.is_disjoint(&other.points_to);
    }

    pub proof fn is_distinct<S>(&mut self, other: &PointsTo<S>)
        requires
            size_of::<V>() != 0,
            size_of::<S>() != 0,
        ensures
            *old(self) == *self,
            self.addr() != other.addr(),
    {
        self.points_to.is_disjoint(&other.points_to);
    }
}

impl Clone for PPtr {
    fn clone(&self) -> (res: Self)
        ensures
            res == *self,
    {
        PPtr(self.0)
    }
}

impl Copy for PPtr {

}

impl PPtr {
    /// Allocates heap memory for type `V`, leaving it uninitialized.
    pub fn empty<V>() -> (pt: (PPtr, Tracked<PointsTo<V>>))
        ensures
            pt.1@.pptr() == pt.0,
            pt.1@.is_uninit(),
        opens_invariants none
    {
        layout_for_type_is_valid::<V>();
        if core::mem::size_of::<V>() != 0 {
            let (p, Tracked(points_to_raw), Tracked(dealloc)) = allocate(
                core::mem::size_of::<V>(),
                core::mem::align_of::<V>(),
            );
            let Tracked(exposed) = expose_provenance(p);
            let tracked points_to = points_to_raw.into_typed::<V>(p.addr());
            proof {
                points_to.is_nonnull();
            }
            let tracked pt = PointsTo { points_to, exposed, dealloc: Some(dealloc) };
            let pptr = PPtr(p as usize);

            return (pptr, Tracked(pt));
        } else {
            let p = core::mem::align_of::<V>();
            assert(p % p == 0) by (nonlinear_arith)
                requires
                    p != 0,
            ;
            let tracked emp = PointsToRaw::empty(Provenance::null());
            let tracked points_to = emp.into_typed(p);
            let tracked pt = PointsTo { points_to, exposed: IsExposed::null(), dealloc: None };
            let pptr = PPtr(p);

            return (pptr, Tracked(pt));
        }
    }

    /// Allocates heap memory for type `V`, leaving it initialized
    /// with the given value `v`.
    pub fn new<V>(v: V) -> (pt: (PPtr, Tracked<PointsTo<V>>))
        ensures
            pt.1@.pptr() == pt.0,
            pt.1@.opt_value() == MemContents::Init(v),
        opens_invariants none
    {
        let (p, Tracked(mut pt)) = PPtr::empty::<V>();
        p.put(Tracked(&mut pt), v);
        (p, Tracked(pt))
    }

    /// Free the memory pointed to be `perm`.
    /// Requires the memory to be uninitialized.
    ///
    /// This consumes `perm`, since it will no longer be safe to access
    /// that memory location.
    #[verifier::external_body]
    pub fn free<V>(self, Tracked(perm): Tracked<PointsTo<V>>)
        requires
            perm.pptr() == self,
            perm.is_uninit(),
        opens_invariants none
    {
        if core::mem::size_of::<V>() != 0 {
            let ptr: *mut u8 = with_exposed_provenance(self.0, Tracked(perm.exposed));
            let tracked PointsTo { points_to, dealloc: dea, exposed } = perm;
            let tracked points_to_raw = points_to.into_raw();
            deallocate(
                ptr,
                core::mem::size_of::<V>(),
                core::mem::align_of::<V>(),
                Tracked(points_to_raw),
                Tracked(dea.tracked_unwrap()),
            );
        }
    }

    /// Free the memory pointed to be `perm` and return the
    /// value that was previously there.
    /// Requires the memory to be initialized.
    /// This consumes the [`PointsTo`] token, since the user is giving up
    /// access to the memory by freeing it.
    #[inline(always)]
    pub fn into_inner<V>(self, Tracked(perm): Tracked<PointsTo<V>>) -> (v: V)
        requires
            perm.pptr() == self,
            perm.is_init(),
        ensures
            v == perm.value(),
        opens_invariants none
    {
        let tracked mut perm = perm;
        let v = self.take(Tracked(&mut perm));
        self.free::<V>(Tracked(perm));
        v
    }

    /// Moves `v` into the location pointed to by the pointer `self`.
    /// Requires the memory to be uninitialized, and leaves it initialized.
    ///
    /// In the ghost perspective, this updates `perm.value`
    /// from `None` to `Some(v)`.
    #[inline(always)]
    pub fn put<V>(self, Tracked(perm): Tracked<&mut PointsTo<V>>, v: V)
        requires
            old(perm).pptr() == self,
            old(perm).opt_value() == MemContents::Uninit::<V>,
        ensures
            perm.pptr() == old(perm).pptr(),
            perm.opt_value() == MemContents::Init(v),
        opens_invariants none
        no_unwind
    {
        proof {
            use_type_invariant(&*perm);
        }
        let ptr: *mut V = with_exposed_provenance(self.0, Tracked(perm.exposed));
        ptr_mut_write(ptr, Tracked(&mut perm.points_to), v);
    }

    /// Moves `v` out of the location pointed to by the pointer `self`
    /// and returns it.
    /// Requires the memory to be initialized, and leaves it uninitialized.
    ///
    /// In the ghost perspective, this updates `perm.value`
    /// from `Some(v)` to `None`,
    /// while returning the `v` as an `exec` value.
    #[inline(always)]
    pub fn take<V>(self, Tracked(perm): Tracked<&mut PointsTo<V>>) -> (v: V)
        requires
            old(perm).pptr() == self,
            old(perm).is_init(),
        ensures
            perm.pptr() == old(perm).pptr(),
            perm.opt_value() == MemContents::Uninit::<V>,
            v == old(perm).value(),
        opens_invariants none
        no_unwind
    {
        proof {
            use_type_invariant(&*perm);
        }
        let ptr: *mut V = with_exposed_provenance(self.0, Tracked(perm.exposed));
        ptr_mut_read(ptr, Tracked(&mut perm.points_to))
    }

    /// Swaps the `in_v: V` passed in as an argument with the value in memory.
    /// Requires the memory to be initialized, and leaves it initialized with the new value.
    #[inline(always)]
    pub fn replace<V>(self, Tracked(perm): Tracked<&mut PointsTo<V>>, in_v: V) -> (out_v: V)
        requires
            old(perm).pptr() == self,
            old(perm).is_init(),
        ensures
            perm.pptr() == old(perm).pptr(),
            perm.opt_value() == MemContents::Init(in_v),
            out_v == old(perm).value(),
        opens_invariants none
        no_unwind
    {
        proof {
            use_type_invariant(&*perm);
        }
        let ptr: *mut V = with_exposed_provenance(self.0, Tracked(perm.exposed));
        let out_v = ptr_mut_read(ptr, Tracked(&mut perm.points_to));
        ptr_mut_write(ptr, Tracked(&mut perm.points_to), in_v);
        out_v
    }

    /// Given a shared borrow of the `PointsTo<V>`, obtain a shared borrow of `V`.
    #[inline(always)]
    #[verifier::external_body]
    pub fn borrow<'a, V>(self, Tracked(perm): Tracked<&'a PointsTo<V>>) -> (v: &'a V)
        requires
            perm.pptr() == self,
            perm.is_init(),
        ensures
            *v === perm.value(),
        opens_invariants none
        no_unwind
    {
        proof {
            use_type_invariant(&*perm);
        }
        let ptr: *mut V = with_exposed_provenance(self.0, Tracked(perm.exposed));
        ptr_ref(ptr, Tracked(&perm.points_to))
    }

    #[inline(always)]
    pub fn write<V: Copy>(self, Tracked(perm): Tracked<&mut PointsTo<V>>, in_v: V)
        requires
            old(perm).pptr() == self,
        ensures
            perm.pptr() === old(perm).pptr(),
            perm.opt_value() === MemContents::Init(in_v),
        opens_invariants none
        no_unwind
    {
        proof {
            use_type_invariant(&*perm);
            perm.leak_contents();
        }
        self.put(Tracked(&mut *perm), in_v);
    }

    #[inline(always)]
    pub fn read<V: Copy>(self, Tracked(perm): Tracked<&PointsTo<V>>) -> (out_v: V)
        requires
            perm.pptr() == self,
            perm.is_init(),
        ensures
            out_v == perm.value(),
        opens_invariants none
        no_unwind
    {
        *self.borrow(Tracked(&*perm))
    }
}

} // verus!
