#![allow(unused_imports)]

use super::super::prelude::*;
use super::points_to_model::*;
use super::ptr_model;
use super::ptr_model::*;

verus! {

broadcast use ptr_model::group_raw_ptr_axioms;

/// Permission to access memory which may decode to a valid value of type `T`;
/// this memory is not guaranteed to be aligned to `T`.
/// Internally represented as a possibly-valid value of type `T`,
/// along with a `PointsToUntyped` permission to the underlying bytes,
/// and the (ghost) metadata of the `*mut T` pointer.
pub tracked struct PointsToUnaligned<T: ?Sized> {
    val: TypedValue<T>,
    pt_untyped: PointsToUntyped,
    metadata: Ghost<CovariantMetadata<T>>,
}

impl<T: ?Sized> PTPhysSealed for PointsToUnaligned<T> {

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
        self.metadata@.metadata()
    }

    /// Returns a tracked reference to the underlying `PointsToUntyped` permission.
    ///
    /// This has no `wf()` requires/ensures,
    /// which gives flexibility for getting the underlying `PointsToUntyped`
    /// when the permission is not well-formed.
    /// However, the `wf()` conditions on `self` should imply that `pt_untyped` is `wf()`.
    // This is implemented by making `PTTypedValue::wf` on `self` include `wf_basic`,
    // which includes `self.pt_untyped().wf()`.
    pub proof fn tracked_pt_untyped(tracked &self) -> tracked &PointsToUntyped
        returns
            self.pt_untyped(),
    {
        &self.pt_untyped
    }

    /// Returns a tracked reference to the typed value.
    pub proof fn tracked_typed_value(tracked &self) -> tracked &TypedValue<T>
        returns
            self.typed_value(),
    {
        &self.val
    }

    /// Splits the permission into an untyped permission to the same bytes and the typed value.
    /// It says nothing about `wf()`.
    pub proof fn into_raw_parts(tracked self) -> (tracked (pt_untyped, typed_value): (
        PointsToUntyped,
        TypedValue<T>,
    ))
        ensures
            pt_untyped == self.pt_untyped(),
            typed_value == self.typed_value(),
    {
        (self.pt_untyped, self.val)
    }

    /// Creates a permission from an untyped permission, a typed value and pointer metadata.
    /// The inverse of `into_raw_parts`.
    /// It says nothing about `wf()`: callers prove it from the parts.
    pub proof fn from_raw_parts(
        tracked pt_untyped: PointsToUntyped,
        tracked typed_value: TypedValue<T>,
        metadata: Metadata<T>,
    ) -> (tracked out: Self)
        ensures
            out.pt_untyped() == pt_untyped,
            out.typed_value() == typed_value,
            out.metadata() == metadata,
    {
        PointsToUnaligned {
            val: typed_value,
            pt_untyped,
            metadata: Ghost(CovariantMetadata::from_metadata(metadata)),
        }
    }

    /// Mutably borrows the untyped bytes and the typed value separately
    /// (the inverse of `from_raw_parts_mut`).
    /// The metadata is unchanged.
    pub proof fn as_raw_parts_mut(tracked &mut self) -> (tracked (pt_untyped, typed_value): (
        &mut PointsToUntyped,
        &mut TypedValue<T>,
    ))
        ensures
            *pt_untyped == old(self).pt_untyped(),
            *typed_value == old(self).typed_value(),
            final(self).pt_untyped() == *final(pt_untyped),
            final(self).typed_value() == *final(typed_value),
            final(self).metadata() == old(self).metadata(),
    {
        (&mut self.pt_untyped, &mut self.val)
    }

    /// Converts a borrowed untyped permission and a borrowed typed value, with the given pointer metadata,
    /// into one borrowed `PointsToUnaligned` permission.
    /// This is the borrowed version of building the permission from its parts.
    /// It says nothing about `wf()`: callers prove it from the parts.
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

    /// Converts a mutable borrow of an untyped permission and a mutable borrow of a typed value, with the given pointer metadata,
    /// into one mutably borrowed `PointsToUnaligned` permission.
    /// The borrowed parts' final values are the final permission's parts.
    /// It says nothing about `wf()`: callers prove it from the parts.
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

    /// Permissions with the same untyped permission, typed value and metadata are equal.
    pub proof fn lemma_ext(a: Self, b: Self)
        requires
            a.typed_value() == b.typed_value(),
            a.pt_untyped() == b.pt_untyped(),
            a.metadata() == b.metadata(),
        ensures
            a == b,
    {
    }
}

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

pub tracked struct PointsTo<T: ?Sized> {
    pt_unaligned: PointsToUnaligned<T>,
}

impl<T: ?Sized> PTPhysSealed for PointsTo<T> {

}

impl<T: ?Sized> PointsTo<T> {
    /// The underlying `PointsToUnaligned` permission to the pointed-to memory.
    pub closed spec fn pt_unaligned(self) -> PointsToUnaligned<T> {
        self.pt_unaligned
    }

    /// Returns a tracked reference to the underlying `PointsToUnaligned` permission.
    ///
    /// This has no `wf()` requires/ensures,
    /// which gives flexibility for getting the underlying `PointsToUnaligned`
    /// when the permission is not well-formed.
    /// However, the `wf()` conditions on `self` should imply that `pt_unaligned` is `wf()`.
    // This is implemented by making `PTTypedValue::wf` on `self` include `self.pt_unaligned().wf()`.
    pub proof fn tracked_pt_unaligned(tracked &self) -> tracked &PointsToUnaligned<T>
        returns
            self.pt_unaligned(),
    {
        &self.pt_unaligned
    }

    /// Converts to the underlying `PointsToUnaligned` permission.
    /// It says nothing about `wf()`.
    pub proof fn into_raw_parts(tracked self) -> (tracked out: PointsToUnaligned<T>)
        returns
            self.pt_unaligned(),
    {
        self.pt_unaligned
    }

    /// Creates a permission from its underlying `PointsToUnaligned` permission.
    /// The inverse of `into_raw_parts`.
    /// It says nothing about `wf()`: callers prove it from `pt_unaligned`.
    pub proof fn from_raw_parts(tracked pt_unaligned: PointsToUnaligned<T>) -> (tracked out: Self)
        ensures
            out.pt_unaligned() == pt_unaligned,
    {
        PointsTo { pt_unaligned }
    }

    /// A borrowed `PointsToUnaligned<T>` acts as a borrowed `PointsTo<T>`.
    /// It says nothing about `wf()`: callers prove it from `pt_unaligned`.
    pub proof fn from_raw_parts_ref(tracked pt_unaligned: &PointsToUnaligned<T>) -> (tracked out:
        &Self)
        ensures
            out.pt_unaligned() == *pt_unaligned,
    {
        shr_ref_struct_wrap(
            pt_unaligned,
            &PointsTo { pt_unaligned: *pt_unaligned },
            "",
            "pt_unaligned",
        )
    }

    /// Mutably borrows the underlying `PointsToUnaligned` permission.
    /// `final(self)` holds its final value.
    /// It says nothing about `wf()`.
    pub proof fn as_raw_parts_mut(tracked &mut self) -> (tracked out: &mut PointsToUnaligned<T>)
        ensures
            *out == old(self).pt_unaligned(),
            final(self).pt_unaligned() == *final(out),
    {
        &mut self.pt_unaligned
    }

    /// A mutably borrowed `PointsToUnaligned<T>` acts as a mutably borrowed `PointsTo<T>`
    /// (the `&mut` counterpart of `from_raw_parts_ref`).
    pub axiom fn from_unaligned_mut<'a>(tracked pt_unaligned: &'a mut PointsToUnaligned<T>) -> (tracked out:
        &'a mut Self)
        ensures
            out.pt_unaligned() == *old(pt_unaligned),
            *final(pt_unaligned) == final(out).pt_unaligned(),
    ;

    /// Permissions with the same underlying `PointsToUnaligned` permission are equal.
    pub proof fn lemma_ext(a: Self, b: Self)
        requires
            a.pt_unaligned() == b.pt_unaligned(),
        ensures
            a == b,
    {
    }
}

} // verus!
