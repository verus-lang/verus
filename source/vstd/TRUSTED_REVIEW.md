# Trusted specs: permission parts and `Tracked<&T>` references

Two changes to the trusted code of vstd's `raw_ptr` and rustlib, relative to `verify-rustlib` (vstd) and rustlib's `port-raw-ptr-final`:

1. **`PointsTo` and `PointsToUnaligned` are verified code.**
   Each trusted function that took or gave a `PointsTo` is stated over its parts,
   a `PointsToUntyped` (the bytes) and a `TypedValue<T>` (the possibly-valid value),
   related by the trusted spec fns `pt_parts_wf*`.
   The `PointsTo` versions keep their names and specs, as verified wrappers.
2. **Shared references are `Tracked<&T>`, with their pointer as shadow data** (`shared_ref_ptr(shadow_data(r))`),
   in place of `&PointsTo<T>` and `SharedReference`.
   `SharedReference` stays for now (see [`SharedReference`](#sharedreference-kept-for-now)).

Open items and later work are in [TODO.md](TODO.md).

## Trusted files

- **vstd `raw_ptr/`:**
  `ptr_model.rs` (unchanged), `ptr_specs.rs`, `shared_reference.rs`,
  `points_to_model.rs` (the `PTPhys` / `PTProperties` traits, `PointsToByte`, `SeqPointsTo`, `PointsToUntyped`, `TypedValue`, `pt_parts_wf*`),
  and `points_to_structs.rs` (new: the `PointsToUnaligned` and `PointsTo` structs, their closed field accessors and structural axioms).
- **rustlib:** `proofs/str.rs` (the `str` versions), the reference-to-pointer casts in `core/src/slice/mod.rs` and `core/src/str/mod.rs`,
  and `Box` in `alloc/src/boxed.rs`.

## Well-formed parts

`pt_unaligned_parts_wf`, `pt_parts_wf` and `pt_parts_wf_slice` are in `points_to_model.rs`;
`pt_parts_wf_str` is in rustlib's `proofs/str.rs`.
Verified lemmas (`PointsTo<T>` / `<[T]>` / `<str>::lemma_pt_parts_wf`) show that `p.wf()` is `pt_parts_wf*(p.ptr()@, ..)` of `p`'s parts.

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

/// `pt_untyped` and `typed_value` are the parts of a well-formed `PointsTo<[T]>` for a pointer with view `ptr`.
pub open spec fn pt_parts_wf_slice<T>(ptr: PtrData<[T]>, pt_untyped: PointsToUntyped, typed_value: TypedValue<[T]>) -> bool {
    &&& pt_untyped.wf()
    &&& pt_untyped.ptr()@.addr == ptr.addr
    &&& pt_untyped.ptr()@.provenance == ptr.provenance
    &&& pt_untyped.len() == ptr.metadata * size_of::<T>()
    &&& ptr.addr as nat % align_of::<T>() == 0
    &&& typed_value.is_valid() ==> {
        &&& abs_decode(pt_untyped.bytes(), typed_value.value_ref())
        &&& typed_value.value_ref()@.len() == ptr.metadata
    }
}

/// `pt_untyped` and `typed_value` are the parts of a well-formed `PointsTo<str>` for a pointer with view `ptr`.
pub open spec fn pt_parts_wf_str(ptr: PtrData<str>, pt_untyped: PointsToUntyped, typed_value: TypedValue<str>) -> bool {
    &&& pt_untyped.wf()
    &&& pt_untyped.ptr()@.addr == ptr.addr
    &&& pt_untyped.ptr()@.provenance == ptr.provenance
    &&& pt_untyped.len() == ptr.metadata
    &&& typed_value.is_valid() ==> {
        &&& abs_decode(pt_untyped.bytes(), typed_value.value_ref())
        &&& typed_value.value_ref().inv()
    }
}
```

`str::inv()` (valid UTF-8) stands in for `str`'s type invariant, which Verus can't express yet.

## Shared references (`ptr_specs.rs`)

**`ptr_shr_ref`:** `&*ptr`, given a shared reference at `ptr`; replaces the trusted exec `ptr_ref` / `ptr_ref_slice`.

```rust
/// Equivalent to `&*ptr`, given a tracked shared reference `r` with the pointer `ptr`.
#[inline(always)]
#[verifier::shadow_data]
#[verifier::external_body]
pub const fn ptr_shr_ref<'a, T: ?Sized>(ptr: *const T, Tracked(r): Tracked<&'a T>) -> (v: &'a T)
    requires
        shared_ref_ptr(shadow_data(r)) == ptr,
    ensures
        v == r,
        ptr_eq_up_to_tag(ptr, shared_ref_ptr(shadow_data(v))),
    opens_invariants none
    no_unwind
{
    unsafe { &*ptr }
}

// `ptr_eq_up_to_tag(p, q)` (`*const`) is `ptr_mut_eq_up_to_tag(p as *mut T, q as *mut T)` (`#[verifier::inline]`):
// the same address, metadata, and provenance apart from the tag.
// They were `const_ptr_eq_up_to_tag` and `ptr_eq_up_to_tag`, renamed to follow `ptr_null` / `ptr_null_mut`.
```

**`ref_to_parts`** and `ref_to_parts_slice` (with `pt_parts_wf_slice`):
a reference gives the parts of a shared permission, at its shadow pointer (see [Soundness](#soundness)).

```rust
/// A shared reference gives the parts of a shared permission for its memory, at its pointer.
#[verifier::shadow_data]
pub axiom fn ref_to_parts<'a, T>(tracked r: &'a T) -> (tracked (
    pt_untyped,
    typed_value,
): (&'a PointsToUntyped, &'a TypedValue<T>))
    ensures
        pt_parts_wf(shared_ref_ptr(shadow_data(r))@, *pt_untyped, *typed_value),
        typed_value.is_valid(),
        typed_value.value_ref() == r,
;
```

**`ref_from_parts`** and `ref_from_parts_slice` (with `pt_parts_wf_slice`): permission parts give a reference at their pointer.

```rust
/// The valid value of a permission's parts, borrowed as a `&T` at `ptr`.
#[verifier::shadow_data]
pub axiom fn ref_from_parts<'a, T>(
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

**`mut_ref_as_shr_ref`:** a shared reborrow of a `&mut`, keeping its pointer;
replaces the axioms `mut_ref_to_shr_points_to` / `_slice`.

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

`ptr_shr_ref` and `mut_ref_as_shr_ref` only relate a reference to a pointer, so one generic version covers `T`, `[T]` and `str`
(like the existing `ptr_mut_ref_join` for `&mut`).
`ref_to_parts` and `ref_from_parts` need one version per `pt_parts_wf*` variant.

## Mutable borrows (`ptr_specs.rs`)

**`mut_ref_from_parts`** and **`mut_ref_from_parts_slice`**: mutable borrows of a permission's parts give a `&mut` at their pointer.
They are `PointsTo<T>::borrow_mut` (an axiom in `verify-rustlib`) and `PointsTo<[T]>::borrow_mut`
(an axiom added in this work, so that the trusted exec `ptr_mut_ref_slice` could be verified), stated over the parts.
Both `borrow_mut`s are now verified wrappers, with their specs unchanged.

```rust
/// This takes a mutable borrow of the `T` at `ptr`
/// from mutable borrows of the parts of a `PointsTo<T>` (`pt_untyped` and `typed_value`).
///
/// Writing through the reference updates both the value and the underlying bytes,
/// so the final parts are well-formed with bytes that decode to the final value.
pub axiom fn mut_ref_from_parts<'a, T>(
    ptr: *mut T,
    tracked pt_untyped: &'a mut PointsToUntyped,
    tracked typed_value: &'a mut TypedValue<T>,
) -> (tracked val: &'a mut T)
    requires
        pt_parts_wf(ptr@, *old(pt_untyped), *old(typed_value)),
        old(typed_value).is_valid(),
    ensures
        &*val == old(typed_value).value_ref(),
        mut_ref_ptr(val) == ptr,
        final(pt_untyped).ptr() == old(pt_untyped).ptr(),
        final(typed_value).is_valid(),
        final(typed_value).value_ref() == &*final(val),
        pt_parts_wf(ptr@, *final(pt_untyped), *final(typed_value)),
;

// mut_ref_from_parts_slice: the same, with `ptr: *mut [T]`, `TypedValue<[T]>`, `&'a mut [T]` and `pt_parts_wf_slice`.
```

The previous axiom's spec, for comparison:

```rust
// verify-rustlib: impl<T> PointsTo<T>
pub axiom fn borrow_mut(tracked &mut self) -> (tracked val: &mut T)
    requires
        self.wf(),
        self.is_valid(),
    ensures
        *val == old(self).value(),
        mut_ref_ptr(val) == old(self).ptr(),
        final(self).is_valid(),
        final(self).ptr() == old(self).ptr(),
        final(self).value() == *final(val),
        final(self).wf(),
;
```

For `T`, `value_ref()` is `&value()`; for slices, `==` on `&[T]` is equality of views (`axiom_slice_ext_equal`).
The final `pt_parts_wf_slice` holds unconditionally because a `&mut [T]`'s length can't change.

## Permission model (`points_to_model.rs`, `points_to_structs.rs`)

**`is_disjoint`:** `PointsToByte`'s generic `is_disjoint` (an axiom in `verify-rustlib`) is verified, with its spec unchanged,
from a new `PTPhys` method `borrow_byte` and an axiom `is_disjoint_byte` for two `PointsToByte`s.
Each `borrow_byte` impl is verified; `PTPhys` stays sealed.

```rust
// PTPhys
/// Borrows the byte permission at address `addr`, which is in this permission's memory range.
proof fn borrow_byte(tracked &self, addr: int) -> (tracked b: &PointsToByte)
    requires
        self.wf_basic(),
        self.ptr()@.addr <= addr < self.ptr()@.addr + Self::size(self.ptr()@.metadata),
    ensures
        b.byte_ptr()@.addr == addr,
        b.byte_ptr()@.provenance == self.ptr()@.provenance,
;

// impl PointsToByte
/// The pointer to the single byte of memory this permission is for (its `PTPhys::ptr`).
pub uninterp spec fn byte_ptr(self) -> *mut u8;

/// Specializes `is_disjoint` to the case when the other permission is a `PointsToByte`.
pub axiom fn is_disjoint_byte(tracked &mut self, tracked other: &Self)
    requires
        self.wf_basic(),
        other.wf_basic(),
    ensures
        *old(self) == *final(self),
        final(self).ptr()@.addr + size_of::<u8>() <= other.ptr()@.addr || other.ptr()@.addr
            + size_of::<u8>() <= final(self).ptr()@.addr,
;
```

`PointsToByte`'s `PTPhys::ptr` is now `open`, defined as `byte_ptr` (it was `uninterp`).

**Structural axioms**, specs unchanged, moved to `points_to_structs.rs`:
`PointsToUnaligned::from_raw_parts_ref`, `PointsToUnaligned::from_raw_parts_mut`,
`PointsTo::from_raw_parts_mut` (renamed from `from_unaligned_mut`, to match the other field primitives).
None requires or ensures `wf()`.
`SeqPointsTo::from_seq_mut` and `TypedValue::from_elems_ref` / `from_elems_mut` are unchanged.

## `SharedReference` (kept for now)

`SharedReference` is kept for rustlib's `str::as_bytes` / `from_utf8_unchecked`, which transmute `SharedReference<str>` ↔ `SharedReference<[u8]>`.
Its trusted items are stated over the parts, and the `PointsTo` versions are verified wrappers.

```rust
// vstd shared_reference.rs; impl<'a, T> SharedReference<'a, T>
/// A shared reference gives the parts of a shared, valid permission (`pt_untyped` and `typed_value`).
pub axiom fn pt_untyped_and_typed_value(tracked self) -> (tracked (pt_untyped, typed_value): (
    &'a PointsToUntyped,
    &'a TypedValue<T>,
))
    ensures
        pt_parts_wf(self.ptr()@, *pt_untyped, *typed_value),
        typed_value.is_valid(),
        typed_value.value() == self.value(),
;
// <[T]>: with pt_parts_wf_slice and `typed_value.value_ref()@ == self.value()@`.
// rustlib <str>: with pt_parts_wf_str, `typed_value.value_ref() == self.value()`, and `requires self.value().inv()`.

#[inline(always)]
#[verifier::external_body]
pub fn ptr_ref2_untyped_with_typed_value<'a, T>(
    ptr: *const T,
    Tracked(pt_untyped): Tracked<&PointsToUntyped>,
    Tracked(typed_value): Tracked<&TypedValue<T>>,
) -> (v: SharedReference<'a, T>)
    requires
        pt_parts_wf(ptr@, *pt_untyped, *typed_value),
        typed_value.is_valid(),
    ensures
        v.value() == typed_value.value(),
        ptr_eq_up_to_tag(v.ptr(), ptr),
    opens_invariants none
    no_unwind
{
    SharedReference(unsafe { &*ptr })
}

/// Same as [`ptr_ref2_untyped_with_typed_value`], but operates on ghost values.
/// Because this doesn't constitute a retag, the returned value's pointer has the same provenance as the original pointer.
pub axiom fn ptr_ref2_ghost_untyped_with_typed_value<'a, T>(
    ptr: *const T,
    tracked pt_untyped: &PointsToUntyped,
    tracked typed_value: &TypedValue<T>,
) -> (tracked v: SharedReference<'a, T>)
    requires
        pt_parts_wf(ptr@, *pt_untyped, *typed_value),
        typed_value.is_valid(),
    ensures
        v.value() == typed_value.value(),
        v.ptr() == ptr,
;
// ptr_ref2_slice_ghost_untyped_with_typed_value: with pt_parts_wf_slice and `v.value()@ == typed_value.value_ref()@`.
// rustlib ptr_ref2_str_ghost_untyped_with_typed_value: with pt_parts_wf_str and `v.value() == typed_value.value_ref()`.
```

**Spec change:** `ptr_ref2`'s ensures was `v.ptr().addr() == ptr.addr()` and `v.ptr()@.metadata == ptr@.metadata`;
it is now `ptr_eq_up_to_tag(v.ptr(), ptr)`, which also gives the provenance apart from the tag, as `ptr_shr_ref` does.

## rustlib

**`str` versions** (`proofs/str.rs`), as in vstd, with `pt_parts_wf_str`:

- `ref_to_parts_str`: also `requires r.inv()`.
- `ref_from_parts_str`.
- `mut_ref_from_parts_str` (was the axiom `PointsTo<str>::borrow_mut`, now a verified wrapper):
  as `mut_ref_from_parts`, but the final parts are well-formed only if the final string is valid UTF-8,
  since `unsafe` code can make a `&mut str` invalid (e.g. through `as_bytes_mut`):

  ```rust
  final(val).inv() ==> pt_parts_wf_str(ptr@, *final(pt_untyped), *final(typed_value)),
  ```

**Reference-to-pointer casts:** `<[T]>::as_slice_ptr` (`core/src/slice/mod.rs`) and `str::as_str_ptr` (`core/src/str/mod.rs`)
are `external_body`, giving only the pointer.
They replace `as_slice_ptr_verus` / `as_str_ptr_verus`, which also gave a `&PointsTo`; callers get it with `ref_to_parts*`.

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

**`Box`** (`alloc/src/boxed.rs`): `from_raw_in_verus` and `into_non_null_with_allocator_verus` are verified wrappers over:

```rust
#[verifier::external_body] // axiomatized
pub unsafe fn from_raw_in_untyped_with_typed_value(
    raw: *mut T,
    alloc: A,
    Tracked(pt_untyped): Tracked<PointsToUntyped>,
    Tracked(typed_value): Tracked<TypedValue<T>>,
) -> (out: Self)
    where T: Sized
    requires
        pt_parts_wf(raw@, pt_untyped, typed_value),
        typed_value.is_valid(),
        raw@.provenance.unwrap().alloc_id() == alloc.alloc_id(),
    ensures
        typed_value.value() == *out,
        out.alloc_id() == raw@.provenance.unwrap().alloc_id()
    no_unwind

#[verifier::external_body] // axiomatized
pub fn into_non_null_with_allocator_untyped_with_typed_value(b: Self) -> ((ptr, alloc, pt_untyped, typed_value): (
    NonNull<T>,
    A,
    Tracked<PointsToUntyped>,
    Tracked<TypedValue<T>>,
))
    where T: Sized
    ensures
        pt_parts_wf(ptr@@, pt_untyped@, typed_value@),
        typed_value@.is_valid(),
        typed_value@.value() == *b,
        alloc.alloc_id() == b.alloc_id(),
        ptr@@.provenance.unwrap().alloc_id() == alloc.alloc_id()
```

**Not changed:**
`ptr::read_unaligned_verus` stays trusted over a `PointsToUnalignedArg` (to be verified later, see [TODO.md](TODO.md));
the 8 definitional axioms in `specs/slice_index.rs` stay
(each defines an `uninterp` spec fn at `[T]` or `str` as an existing open spec fn of `&PointsTo`, and none claims a permission exists or is `wf`).

## Trusted items now verified

| Previously trusted | Now |
|---|---|
| `ptr_ref`, `ptr_ref_slice`, rustlib `ptr_ref_str` (exec) | `PointsTo::borrow_ref` (`ref_from_parts*`), then `ptr_shr_ref` |
| `ptr_mut_ref`, `ptr_mut_ref_slice` (exec) | `PointsTo::borrow_mut`, then `ptr_mut_ref_join` |
| `PointsTo<T>` / `<[T]>` / rustlib `<str>::borrow_mut` | `mut_ref_from_parts*` |
| `mut_ref_to_shr_points_to` (+ `_slice`, rustlib `_str`) | `mut_ref_as_shr_ref`, then `ref_to_parts*` |
| `SharedReference<T>` / `<[T]>` / rustlib `<str>::points_to` | `pt_untyped_and_typed_value` |
| `ptr_ref2`, `ptr_ref2_ghost`, `ptr_ref2_slice_ghost`, rustlib `ptr_ref2_str_ghost` | the `*_untyped_with_typed_value` versions |
| `PointsToByte::is_disjoint` | `borrow_byte` and `is_disjoint_byte` |
| `Box::from_raw_in_verus`, `into_non_null_with_allocator_verus` | the `*_untyped_with_typed_value` versions |
| rustlib `as_slice_ptr_verus`, `as_str_ptr_verus` | removed: the casts, then `ref_to_parts*` (verified `shr_ref_points_to*`) |
| everything in `PointsTo` / `PointsToUnaligned`'s trait impls (`wf`, alignment, decoding, ...) | verified, in `points_to_ops.rs` |
| `mut_ref_slice_len` | `mut_ref_as_shr_ref`, then the new verified `shr_ref_slice_len` (`ref_to_parts_slice`) |

rustlib's `mut_ref_str_len` stays an axiom:
the pointer's metadata is the length even for a `&mut str` that isn't valid UTF-8,
but `ref_to_parts_str`, the only trusted route from a `str` reference to its pointer, requires `inv()`.

Also verified: `ExSliceIndex::get` / `index` (rustlib `core/src/slice/index.rs`) get `#[verifier::shadow_data]`,
so they lose their `call_requires` / `call_ensures` axioms; nothing uses them.
