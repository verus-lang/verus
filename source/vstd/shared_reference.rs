verus! {

/// This is meant to be a replacement for `&'a T` that allows Verus to keep track of
/// not just the `T` value but the pointer as well.
/// It would be better to get rid of this and use normal reference types `&'a T`,
/// but there are a lot of unsolved implementation questions.
/// The existence of `SharedReference<'a, T>` is a stop-gap.
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::raw_ptr::SharedReference")]
#[repr(transparent)]
pub struct SharedReference<'a, T: ?Sized>(&'a T);

impl<'a, T: ?Sized> Clone for SharedReference<'a, T> {
    #[verifier::external_body]
    fn clone(&self) -> (ret: Self)
        ensures
            ret == *self,
    {
        SharedReference(self.0)
    }
}

impl<'a, T: ?Sized> Copy for SharedReference<'a, T> {

}

impl<'a, T> SharedReference<'a, T> {
    #[verifier::external_body]
    pub const fn as_ptr(self) -> (ptr: *const T)
        ensures
            ptr == self.ptr() as *const T,
    {
        &*self.0
    }

    // NOTE: there does not exist a points_to_unaligned function because SharedReference
    // by definition gives you an _aligned_ PointsTo.
    // https://doc.rust-lang.org/std/primitive.reference.html
    pub axiom fn points_to(tracked self) -> (tracked pt: &'a PointsTo<T>)
        ensures
            pt.ptr() == self.ptr(),
            pt.is_init(),
            pt.value() == self.value(),
    ;
}

impl<'a, T: ?Sized> SharedReference<'a, T> {
    pub uninterp spec fn value(self) -> &'a T;

    pub uninterp spec fn ptr(self) -> *const T;

    #[verifier::external_body]
    pub const fn new(t: &'a T) -> (s: Self)
        ensures
            s.value() == t,
    {
        SharedReference(t)
    }

    #[verifier::external_body]
    pub const fn as_ref(self) -> (t: &'a T)
        ensures
            t == self.value(),
    {
        self.0
    }

    #[verifier::external_body]
    pub proof fn as_ref_tracked(tracked &self) -> (tracked t: &'a T)
        ensures
            t == self.value(),
    {
        self.0
    }

    // References must be nonnull - https://doc.rust-lang.org/reference/behavior-considered-undefined.html#r-undefined.validity.reference-box
    pub axiom fn ptr_nonnull(tracked self)
        ensures
            self.ptr()@.addr != 0,
    ;
}

/// Extracts the pointer from the shadow data of a shared reference.
pub uninterp spec fn shared_ref_ptr<T: ?Sized>(s: ShadowData<&T>) -> *const T;

impl<'a, T> SharedReference<'a, [T]> {
    #[verifier::external_body]
    pub const fn as_slice_ptr(self) -> (ptr: *const [T])
        ensures
            ptr == self.ptr(),
    {
        self.0 as *const [T]
    }

    // commonly used operation: this function's signature corresponds to Rust's `slice::as_ptr`
    pub const fn as_ptr(self) -> (ptr: *const T)
        ensures
            ptr == self.ptr() as *const T,
    {
        self.as_slice_ptr() as *const T
    }

    pub const fn len(self) -> (output: usize)
        ensures
            output == self.value()@.len(),
    {
        broadcast use super::slice::group_slice_axioms;

        self.as_ref().len()
    }

    pub const fn index(self, idx: usize) -> (out: &'a T)
        requires
            0 <= idx < self.value()@.len(),
        ensures
            *out == self.value()@.index(idx as int),
    {
        broadcast use group_vstd_default;

        &(self.as_ref())[idx]
    }

    pub axiom fn points_to(tracked self) -> (tracked pt: &'a PointsTo<[T]>)
        ensures
            pt.ptr() == self.ptr(),
            pt.is_init(),
            pt.value() == self.value()@,
    ;
}

impl<'a> SharedReference<'a, str> {
    #[verifier::external_body]
    pub const fn as_str_ptr(self) -> (ptr: *const str)
        ensures
            ptr == self.ptr(),
    {
        self.0 as *const str
    }

    // commonly used operation: this function's signature corresponds to Rust's `str::as_ptr`
    pub const fn as_ptr(self) -> (ptr: *const u8)
        ensures
            ptr == self.ptr() as *const u8,
    {
        self.as_str_ptr() as *const u8
    }

    pub axiom fn points_to(tracked self) -> (tracked pt: &'a PointsTo<str>)
        ensures
            pt.ptr() == self.ptr(),
            pt.is_init(),
            pt.value() == self.value(),
    ;
}

impl<'a, T> View for SharedReference<'a, [T]> {
    type V = Seq<T>;

    uninterp spec fn view(&self) -> Seq<T>;
}

#[verifier::external_body]
pub broadcast axiom fn axiom_shared_ref_value_view<'a, T>(shared_ref: SharedReference<'a, [T]>)
    ensures
        shared_ref.value()@ == #[trigger] shared_ref@,
;

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
        perm.is_init(),
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
        perm.is_init(),
    ensures
        v.value() == perm.value(),
        v.ptr() == ptr,
;

/// Same as [`ptr_ref2`], but operates on ghost values.
/// Because this doesn't constitute a retag, the returned value's pointer has the same provenance as the original pointer.
pub axiom fn ptr_ref2_str_ghost<'a>(ptr: *const str, tracked perm: &PointsTo<str>) -> (tracked v:
    SharedReference<'a, str>)
    requires
        perm.ptr() == ptr,
        perm.is_init(),
    ensures
        v.value() == perm.value(),
        v.ptr() == ptr,
;

/// Same as [`ptr_ref2`], but operates on ghost values.
/// Because this doesn't constitute a retag, the returned value's pointer has the same provenance as the original pointer.
pub axiom fn ptr_ref2_slice_ghost<'a, T>(
    ptr: *const [T],
    tracked perm: &PointsTo<[T]>,
) -> (tracked v: SharedReference<'a, [T]>)
    requires
        perm.ptr() == ptr,
        perm.is_init(),
    ensures
        v.value()@ == perm.value(),
        v.ptr() == ptr,
;

}