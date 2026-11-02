# Trusted-code changes: `Tracked<&T>` with shadow data in place of `&PointsTo<T>`

All the specs below are approved (2026-11-02; B as a proof axiom).

## New trusted items

### vstd, `source/vstd/raw_ptr/ptr_specs.rs`

**`ptr_shr_ref`** (line 245): the counterpart of `ptr_mut_ref_join`.

```rust
/// Equivalent to `&*ptr`, given a shared reference `r` at `ptr`.
#[inline(always)]
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
{
    unsafe { &*ptr }
}
```

#### Trusted specs
```rust
/// `pt_untyped` and `typed_value` are the parts of a well-formed `PointsToUnaligned<T>` for a pointer with view `ptr`.
pub open spec fn pt_unaligned_parts_wf<T>(ptr: PtrData<T>, pt_untyped: PointsToUntyped, typed_value: TypedValue<T>) -> bool {
    &&& pt_untyped.wf()
    &&& pt_untyped.ptr()@.addr == ptr.addr
    &&& pt_untyped.ptr()@.provenance == ptr.provenance
    &&& pt_untyped.len() == size_of::<T>()
    &&& typed_value.is_valid() ==> abs_decode(pt_untyped.bytes(), typed_value.value_ref())
}

/// `pt_untyped` and `typed_value` are the parts of a well-formed `PointsTo<T>` for a pointer with view `ptr`.
pub open spec fn pt_parts_wf<T>(ptr: PtrData<T>, pt_untyped: PointsToUntyped, typed_value: TypedValue<T>) -> bool {
    &&& pt_unaligned_parts_wf(ptr, pt_untyped, typed_value)
    &&& ptr.addr as nat % align_of::<T>() == 0
}
```

**`ref_untyped_with_typed_value`** (line 259) and `_slice` (line 271, with `pt_parts_wf_slice`):
a reference gives the parts of a shared permission, at its shadow pointer (see [Soundness](#soundness)).

```rust
/// A shared reference gives the parts of a shared permission for its memory, at its pointer.
#[verifier::shadow_data]
pub axiom fn ref_untyped_with_typed_value<'a, T>(tracked r: &'a T) -> (tracked (
    pt_untyped,
    typed_value,
): (&'a PointsToUntyped, &'a TypedValue<T>))
    ensures
        pt_parts_wf(shared_ref_ptr(shadow_data(r))@, *pt_untyped, *typed_value),
        typed_value.is_valid(),
        typed_value.value_ref() == r,
;
```

**`untyped_with_typed_value_ref`** (line 283) and `_slice` (line 298): permission parts give a reference at their pointer.
The shared counterpart of `borrow_mut_untyped_with_typed_value`.

```rust
/// The valid value of a permission's parts, borrowed as a `&T` at `ptr`.
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
```

**`mut_ref_as_shr_ref`** (line 425): a shared reborrow of a `&mut`, keeping its pointer.

```rust
/// Borrows a `&'a mut T` as a `&'a T` at the same pointer.
#[verifier::shadow_data]
pub axiom fn mut_ref_as_shr_ref<'a, T: ?Sized>(tracked mut_ref: &'a &'a mut T) -> (tracked r: &'a T)
    ensures
        r == &*old(*mut_ref),
        &*final(*mut_ref) == &*old(*mut_ref),
        shared_ref_ptr(shadow_data(r)) == mut_ref_ptr(*mut_ref),
;
```

### rustlib, `proofs/str.rs` (`str` depends on rustlib's UTF-8 encoding)

- **`ref_untyped_with_typed_value_str`** (line 572): as above, with `pt_parts_wf_str`, and also `requires r.inv()`
  (`inv()` stands in for `str`'s UTF-8 type invariant, and `pt_parts_wf_str` includes UTF-8 for a valid value).
- **`untyped_with_typed_value_ref_str`** (line 586): as above, with `pt_parts_wf_str`.

### rustlib, the reference-to-pointer casts

`<[T]>::as_slice_ptr` (`core/src/slice/mod.rs:833`) and `str::as_str_ptr` (`core/src/str/mod.rs:692`)
are now `external_body` (they were verified from the removed `as_*_ptr_untyped_with_typed_value`).
Specs unchanged; they give only the pointer:

```rust
#[verifier::shadow_data]
#[verifier::external_body] // Ok - cast from `&self` to `*const [T]`
pub const fn as_slice_ptr(&self) -> *const [T]
    returns
        shared_ref_ptr(shadow_data(self)),
{
    self as *const [T]
}
// str::as_str_ptr: the same, with `requires self.inv()`
```

## Soundness

- **`untyped_with_typed_value_ref`:** the reference is built from real, well-formed permission parts, at their pointer.
- **`mut_ref_as_shr_ref`:** the same trust as the existing uses of `mut_ref_ptr`.
- **References made in ghost code.**
  A `&T` made in ghost code (e.g. `&g` for a tracked local `g`) refers to a ghost value,
  and its shadow data is an unknown value: the shadow-data pass gives a fresh unknown value to every reference
  that isn't a parameter, a copy of a variable, or the result of a `shadow_data` function whose spec constrains it
  (a reborrow `&*x` also gets a fresh value).
  - **`ptr_shr_ref`** is exec and requires `shared_ref_ptr(shadow_data(r)) == ptr` for an exec `ptr`,
    which can't be proven for an unknown shadow pointer, so it only turns real references into exec references.
  - **`ref_untyped_with_typed_value`** is a proof axiom, so it also gives a reference made in ghost code permission parts,
    at its unknown shadow pointer.
    No runtime pointer can be proven equal to that pointer
    (runtime pointers' provenance comes from real allocations, or is `None`),
    so these parts can be modeled as a ghost allocation that exec code can never reach, disjoint from every real one.
    This is the argument the previous `mut_ref_to_shr_untyped_with_typed_value` (a proof axiom, which you've reviewed)
    already relied on for a `&mut` made in ghost code.
- **The invariant this relies on:** only trusted specs about real references pin a shadow pointer to a known value:
  the casts (an exec `&self`), `ptr_shr_ref` (a real reborrow), `untyped_with_typed_value_ref` (real permission parts),
  and `mut_ref_as_shr_ref` (a `&mut`'s `mut_ref_ptr`, which only the trusted `&mut` specs about real `&mut`s pin to a runtime pointer).
  Verified `shadow_data` functions can only pass shadow data along.
  Any new trusted spec has to keep this, and must not make a ghost reference's shadow pointer or provenance reachable from exec code
  (e.g. an axiom that every `Some` provenance is a real allocation, or an exposed-provenance API returning arbitrary provenances).

Tested (scratch files, with `10dd2cdd1`): `ptr_shr_ref` on a ghost `&g` fails as expected;
a reborrow `&*x` gets fresh shadow data;
`let tracked t = x;`, proof functions and axioms with shadow-data ensures, and `proof` blocks in exec code all keep it.

## Question

Is the argument for references made in ghost code sound:
that `ref_untyped_with_typed_value` can give them permission parts, because their shadow pointers can never be proven equal to a runtime pointer?
