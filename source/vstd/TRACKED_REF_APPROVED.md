# Approved: `Tracked<&T>` in place of `&PointsTo<T>`

Approved specs from [TRACKED_REF_PLAN.md](TRACKED_REF_PLAN.md).

## `ptr_shr_ref` (approved 2026-11-02)

Trusted, in `ptr_specs.rs`. One generic version covers `T`, `[T]` and `str`.
The `&PointsTo` versions `ptr_ref` / `ptr_ref_slice` stay, as verified wrappers.

```rust
/// Equivalent to `&*ptr`, given a shared reference `r` at `ptr`.
#[verifier::shadow_data]
#[verifier::external_body]
pub const fn ptr_shr_ref<'a, T: ?Sized>(ptr: *const T, Tracked(r): Tracked<&'a T>) -> (v: &'a T)
    requires
        shared_ref_ptr(shadow_data(r)) == ptr,
    ensures
        v == r,
        ptr_eq_up_to_tag(ptr as *mut T, shared_ref_ptr(shadow_data(v)) as *mut T),
    opens_invariants none
    no_unwind
;
```

## A, B, C (approved 2026-11-02)

Trusted, in `ptr_specs.rs`.
A and B have slice versions (with `pt_parts_wf_slice`),
and rustlib's `proofs/str.rs` has their `str` versions (with `pt_parts_wf_str`; B's `str` version requires `r.inv()`).
C is generic and covers `T`, `[T]` and `str`.

```rust
/// (B) A live shared reference at `ptr` gives the parts of a shared permission for its memory.
#[verifier::shadow_data]
#[verifier::external_body]
pub fn ref_untyped_with_typed_value<'a, T>(ptr: *const T, Tracked(r): Tracked<&'a T>) -> ((pt_untyped, typed_value): (
    Tracked<&'a PointsToUntyped>,
    Tracked<&'a TypedValue<T>>,
))
    requires
        shared_ref_ptr(shadow_data(r)) == ptr,
    ensures
        pt_parts_wf(ptr@, *pt_untyped@, *typed_value@),
        typed_value@.is_valid(),
        typed_value@.value_ref() == r,
;

/// (A) The valid value of a permission's parts, borrowed as a `&T` at `ptr`.
#[verifier::shadow_data]
pub axiom fn untyped_with_typed_value_ref<'a, T>(
    ptr: *const T,
    tracked pt_untyped: &'a PointsToUntyped,
    tracked typed_value: &'a TypedValue<T>,
) -> (tracked r: &'a T)
    requires
        pt_parts_wf(ptr@, *pt_untyped, *typed_value),
        typed_value.is_valid(),
    ensures
        r == typed_value.value_ref(),
        shared_ref_ptr(shadow_data(r)) == ptr,
;

/// (C) Borrows a `&'a mut T` as a `&'a T` at the same pointer.
#[verifier::shadow_data]
pub axiom fn mut_ref_as_shr_ref<'a, T: ?Sized>(tracked mut_ref: &'a &'a mut T) -> (tracked r: &'a T)
    ensures
        r == &*old(*mut_ref),
        &*final(*mut_ref) == &*old(*mut_ref),
        shared_ref_ptr(shadow_data(r)) == mut_ref_ptr(*mut_ref),
;
```

## rustlib casts (approved 2026-11-02)

Trusted. They give only the pointer; B gives the parts.

```rust
// core/src/slice/mod.rs, impl<T> [T]
#[verifier::shadow_data]
#[verifier::external_body]
pub const fn as_slice_ptr(&self) -> *const [T]
    returns
        shared_ref_ptr(shadow_data(self)),

// core/src/str/mod.rs, impl str
#[verifier::shadow_data]
#[verifier::external_body]
pub const fn as_str_ptr(&self) -> *const str
    requires
        self.inv(),
    returns
        shared_ref_ptr(shadow_data(self)),
```

## Supersedes

These replace, in [TRUSTED_POINTS_TO_APPROVED.md](TRUSTED_POINTS_TO_APPROVED.md),
the trusted `ptr_ref*`, `ptr_ref2*`, `SharedReference::untyped_with_typed_value` and `mut_ref_to_shr_untyped_with_typed_value*` functions,
and rustlib's `as_slice_ptr_untyped_with_typed_value` / `as_str_ptr_untyped_with_typed_value`.
`SharedReference` and its trusted items are removed.
