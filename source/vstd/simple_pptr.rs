use super::layout::*;
use super::prelude::*;
use super::raw_ptr;
use super::raw_ptr::*;
use core::marker::PhantomData;

verus! {

/// `PPtr` (which stands for "permissioned pointer")
/// is a wrapper around a raw pointer to a heap-allocated `V`.
/// This is designed to be simpler to use that Verus's
/// [more general pointer support](`crate::raw_ptr`),
/// but also to serve as a better introductory point.
/// Historically, `PPtr` was positioned as a "trusted primitive" of Verus,
/// but now, it is implemented and verified from the more general pointer support,
/// which operates on similar principles, but which is much precise to Rust's
/// pointer semantics.
///
/// A `PPtr` is equvialent to its `usize`-based address. The type paramter `V` technically
/// doesn't matter, and you can freely convert between `PPtr<V>` and `PPtr<W>` by casting
/// to and from the `usize` address. What _really_ matters is the type paramter of the
/// `PointsTo<V>`.
///
/// In order to access (read or write) the value behind the pointer, the user needs
/// a special _ghost permission token_, [`PointsTo<V>`](PointsTo). This object is `tracked`,
/// which means that it is "only a proof construct" that does not appear in compiled code,
/// but its uses _are_ checked by the borrow-checker. This ensures memory safety,
/// data-race-freedom, prohibits use-after-free, etc.
///
/// ### PointsTo objects.
///
/// The [`PointsTo`] object represents both the ability to access (read or write)
/// the data behind the pointer _and_ the ability to free it
/// (return it to the memory allocator).
///
/// The `perm: PointsTo<V>` object tracks two pieces of data:
///  * [`perm.pptr()`](PointsTo::pptr) is the pointer that the permission is associated to.
///  * [`perm.mem_contents()`](PointsTo::mem_contents) is the memory contents, which is one of either:
///     * [`MemContents::Uninit`](raw_ptr::MemContents::Uninit) if the memory pointed-to by
///       by the pointer is uninitialized.
///     * [`MemContents::Init(v)`](raw_ptr::MemContents::Init) if the memory points-to the
///       the value `v`.
///
/// Your access to the `PointsTo` object determines what operations you can safely perform
/// with the pointer:
///  * You can _read_ from the pointer as long as you have read access to the `PointsTo` object,
///     e.g., `&PointsTo<V>`.
///  * You can _write_ to the pointer as long as you have mutable access to the `PointsTo` object,
///     e.g., `&mut PointsTo<V>`
///  * You can call `free` to deallocate the memory as long as you have full onwership
///     of the `PointsTo` object (i.e., the ability to move it).
///
/// For those familiar with separation logic, the `PointsTo` object plays a role
/// similar to that of the "points-to" operator, _ptr_ ↦ _value_.
///
/// ### Example
///
/// ```rust,ignored
/// fn main() {
///     unsafe {
///         // ALLOCATE
///         // p: PPtr<u64>, points_to: PointsTo<u64>
///         let (p, Tracked(mut points_to)) = PPtr::<u64>::empty();
///
///         assert(points_to.mem_contents() === MemContents::Uninit);
///         assert(points_to.pptr() == p);
///
///         // unsafe { *p = 5; }
///         p.write(Tracked(&mut points_to), 5);
///
///         assert(points_to.mem_contents() === MemContents::Init(5));
///         assert(points_to.pptr() == p);
///
///         // let x = unsafe { *p };
///         let x = p.read(Tracked(&points_to));
///
///         assert(x == 5);
///
///         // DEALLOCATE
///         let y = p.into_inner(Tracked(points_to));
///
///         assert(y == 5);
///     }
/// }
/// ```
///
/// ### Examples of incorrect usage
///
/// The following code has a use-after-free bug, and it is rejected by Verus because
/// it fails to satisfy Rust's ownership-checker.
///
/// ```rust,ignored
/// fn main() {
///     unsafe {
///         // ALLOCATE
///         // p: PPtr<u64>, points_to: PointsTo<u64>
///         let (p, Tracked(mut points_to)) = PPtr::<u64>::empty();
///
///         // unsafe { *p = 5; }
///         p.write(Tracked(&mut points_to), 5);
///
///         // let x = unsafe { *p };
///         let x = p.read(Tracked(&points_to));
///
///         // DEALLOCATE
///         p.free(Tracked(points_to));                 // `points_to` is moved here
///
///         // READ-AFTER-FREE
///         let x2 = p.read(Tracked(&mut points_to));   // so it can't be used here
///     }
/// }
/// ```
///
/// The following doesn't violate Rust's ownership-checking, but it "mixes up" the `PointsTo`
/// objects, attempting to use the wrong `PointsTo` for the given pointer.
/// This violates the precondition on [`p.read()`](PPtr::read).
///
/// ```rust,ignored
/// fn main() {
///     unsafe {
///         // ALLOCATE p
///         let (p, Tracked(mut perm_p)) = PPtr::<u64>::empty();
///
///         // ALLOCATE q
///         let (q, Tracked(mut perm_q)) = PPtr::<u64>::empty();
///
///         // DEALLOCATE p
///         p.free(Tracked(perm_p));
///
///         // READ-AFTER-FREE (read from p, try to use q's permission object)
///         let x = p.read(Tracked(&mut perm_q));
///     }
/// }
/// ```
///
/// ### Differences from `PCell`.
///
/// `PPtr` is similar to [`cell::PCell`](crate::cell::PCell), but has a few key differences:
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
// We want PPtr's fields to be public so the solver knows that equality of addresses
// implies equality of PPtrs
pub struct PPtr<V>(pub usize, pub PhantomData<V>);

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

impl<V> PPtr<V> {
    /// Use `addr()` instead
    #[verifier::inline]
    pub open spec fn spec_addr(p: PPtr<V>) -> usize {
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
        PPtr(u, PhantomData)
    }

    #[doc(hidden)]
    #[inline(always)]
    pub fn from_usize(u: usize) -> (s: Self)
        ensures
            u == s.addr(),
    {
        PPtr(u, PhantomData)
    }
}

impl<V> PointsTo<V> {
    #[verifier::inline]
    pub open spec fn pptr(&self) -> PPtr<V> {
        PPtr(self.addr(), PhantomData)
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

    pub closed spec fn mem_contents(&self) -> MemContents<V> {
        self.points_to.opt_value()
    }

    #[doc(hidden)]
    #[verifier::inline]
    pub open spec fn opt_value(&self) -> MemContents<V> {
        self.mem_contents()
    }

    #[doc(verus_show_body)]
    #[verifier::inline]
    pub open spec fn is_init(&self) -> bool {
        self.mem_contents().is_init()
    }

    #[doc(verus_show_body)]
    #[verifier::inline]
    pub open spec fn is_uninit(&self) -> bool {
        self.mem_contents().is_uninit()
    }

    #[doc(verus_show_body)]
    #[verifier::inline]
    pub open spec fn value(&self) -> V
        recommends
            self.is_init(),
    {
        self.mem_contents().value()
    }

    /// Guarantee that the `PointsTo` points to a non-null address.
    pub proof fn is_nonnull(tracked &self)
        ensures
            self.addr() != 0,
    {
        use_type_invariant(self);
    }

    /// "Forgets" about the value stored behind the pointer.
    /// Updates the `PointsTo` value to [`MemContents::Uninit`](MemContents::Uninit).
    /// Note that this is a `proof` function, i.e., it is operationally a no-op in executable code.
    pub proof fn leak_contents(tracked &mut self)
        ensures
            self.pptr() == old(self).pptr(),
            self.is_uninit(),
    {
        use_type_invariant(&*self);
        self.points_to.leak_contents();
    }

    /// Guarantees that two distinct `PointsTo<V>` objects point to disjoint ranges of memory.
    /// If both S and V are non-zero-sized, then this also implies the pointers
    /// have distinct addresses.
    pub proof fn is_disjoint<S>(&mut self, other: &PointsTo<S>)
        ensures
            *old(self) == *self,
            self.addr() + size_of::<V>() <= other.addr() || other.addr() + size_of::<S>()
                <= self.addr(),
    {
        self.points_to.is_disjoint(&other.points_to);
    }

    /// Guarantees that two distinct, non-ZST `PointsTo<V>` objects point to different
    /// addresses. This is a corollary of [`PointsTo::is_disjoint`].
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

impl<V> Clone for PPtr<V> {
    fn clone(&self) -> (res: Self)
        ensures
            res == *self,
    {
        PPtr(self.0, PhantomData)
    }
}

impl<V> Copy for PPtr<V> {

}

impl<V> PPtr<V> {
    /// Allocates heap memory for type `V`, leaving it uninitialized.
    pub fn empty() -> (pt: (PPtr<V>, Tracked<PointsTo<V>>))
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
            let pptr = PPtr(p as usize, PhantomData);

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
            let pptr = PPtr(p, PhantomData);

            return (pptr, Tracked(pt));
        }
    }

    /// Allocates heap memory for type `V`, leaving it initialized
    /// with the given value `v`.
    pub fn new(v: V) -> (pt: (PPtr<V>, Tracked<PointsTo<V>>))
        ensures
            pt.1@.pptr() == pt.0,
            pt.1@.mem_contents() == MemContents::Init(v),
        opens_invariants none
    {
        let (p, Tracked(mut pt)) = PPtr::<V>::empty();
        p.put(Tracked(&mut pt), v);
        (p, Tracked(pt))
    }

    /// Free the memory pointed to be `perm`.
    /// Requires the memory to be uninitialized.
    ///
    /// This consumes `perm`, since it will no longer be safe to access
    /// that memory location.
    #[verifier::external_body]
    pub fn free(self, Tracked(perm): Tracked<PointsTo<V>>)
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
    pub fn into_inner(self, Tracked(perm): Tracked<PointsTo<V>>) -> (v: V)
        requires
            perm.pptr() == self,
            perm.is_init(),
        ensures
            v == perm.value(),
        opens_invariants none
    {
        let tracked mut perm = perm;
        let v = self.take(Tracked(&mut perm));
        self.free(Tracked(perm));
        v
    }

    /// Moves `v` into the location pointed to by the pointer `self`.
    /// Requires the memory to be uninitialized, and leaves it initialized.
    ///
    /// In the ghost perspective, this updates `perm.mem_contents()`
    /// from `MemContents::Uninit` to `MemContents::Init(v)`.
    #[inline(always)]
    pub fn put(self, Tracked(perm): Tracked<&mut PointsTo<V>>, v: V)
        requires
            old(perm).pptr() == self,
            old(perm).mem_contents() == MemContents::Uninit::<V>,
        ensures
            perm.pptr() == old(perm).pptr(),
            perm.mem_contents() == MemContents::Init(v),
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
    pub fn take(self, Tracked(perm): Tracked<&mut PointsTo<V>>) -> (v: V)
        requires
            old(perm).pptr() == self,
            old(perm).is_init(),
        ensures
            perm.pptr() == old(perm).pptr(),
            perm.mem_contents() == MemContents::Uninit::<V>,
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
    pub fn replace(self, Tracked(perm): Tracked<&mut PointsTo<V>>, in_v: V) -> (out_v: V)
        requires
            old(perm).pptr() == self,
            old(perm).is_init(),
        ensures
            perm.pptr() == old(perm).pptr(),
            perm.mem_contents() == MemContents::Init(in_v),
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
    pub fn borrow<'a>(self, Tracked(perm): Tracked<&'a PointsTo<V>>) -> (v: &'a V)
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
    pub fn write(self, Tracked(perm): Tracked<&mut PointsTo<V>>, in_v: V) where V: Copy
        requires
            old(perm).pptr() == self,
        ensures
            perm.pptr() === old(perm).pptr(),
            perm.mem_contents() === MemContents::Init(in_v),
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
    pub fn read(self, Tracked(perm): Tracked<&PointsTo<V>>) -> (out_v: V) where V: Copy
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

pub use raw_ptr::MemContents;

} // verus!
