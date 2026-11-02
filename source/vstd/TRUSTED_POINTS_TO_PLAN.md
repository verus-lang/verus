# Design: no trusted specs over `PointsTo` / `PointsToUnaligned`

Goal: `PointsTo` and `PointsToUnaligned` are verified code.
No trusted item in vstd or rustlib depends on their `wf`, alignment, decoding or trait impls.
Each trusted function that takes or gives a `PointsTo` today is restated over a `PointsToUntyped` and a `TypedValue`,
and the current `PointsTo` version is kept, under the same name, as a verified wrapper.
Users keep calling the `PointsTo` versions.

Approved specs that this changes: every function in [Trusted permission functions](#trusted-permission-functions) (its `PointsTo` version keeps its spec),
and rustlib's approved `proofs/str.rs`.
The approved `SeqPointsTo` / `PointsToByte` / `PointsToUnaligned` / `PointsTo` impls move to one verified sibling module and their proof bodies change,
but their specs don't (see [Module layout](#module-layout)).

## Names

Provisional, to revisit during review:
the trusted versions are `*_untyped_with_typed_value` (the convention for `wf`'d constructors and destructors),
and the spec fns are `pt_parts_wf` / `pt_parts_wf_slice` (and `pt_parts_wf_str` in rustlib).

## Well-formed parts

Trusted specs state well-formedness with these open spec fns, defined in the trusted file.
`PtrData` is the pointer's view, so both `*const` and `*mut` pointers can be passed in.

```rust
/// `pt_untyped` and `typed_value` are the parts of a well-formed `PointsTo<T>` for a pointer with view `ptr`.
pub open spec fn pt_parts_wf<T>(ptr: PtrData<T>, pt_untyped: PointsToUntyped, typed_value: TypedValue<T>) -> bool {
    &&& pt_untyped.wf()
    &&& pt_untyped.ptr()@.addr == ptr.addr
    &&& pt_untyped.ptr()@.provenance == ptr.provenance
    &&& pt_untyped.len() == size_of::<T>()
    &&& ptr.addr as nat % align_of::<T>() == 0
    &&& typed_value.is_valid() ==> abs_decode(pt_untyped.bytes(), typed_value.value_ref())
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

// In rustlib's `proofs/str.rs`, where a `str`'s view is its bytes.
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

`pt_parts_wf_str` has no alignment condition (a `str`'s alignment is 1)
and no length condition on the value: decoding gives the length, as in `PointsTo<str>`'s `additional_validity_constraints`.

Verified lemmas then show that `p.wf()` is `pt_parts_wf(p.ptr()@, ..)` of `p`'s parts (and the same for slices and `str`).
The wrappers use these lemmas.

These spec fns are trusted, because the trusted specs' meaning depends on them:
- **Trusted functions require them** (e.g. `ptr_ref_untyped_with_typed_value`).
  If they were too weak, a caller could get a `&T` from memory that doesn't hold one.
- **Trusted axioms ensure them** (e.g. `SharedReference::untyped_with_typed_value`).
  If they were too strong, the axiom would promise something Rust doesn't guarantee.

The lemmas only relate them to `PointsTo::wf`.
That is what makes `PointsTo::wf` untrusted: the wrappers verify against `pt_parts_wf`, whatever `wf` says.

## Approved

The `is_disjoint` change (`PTPhys::borrow_byte`) and keeping the three structural axioms trusted
are approved and in [TRUSTED_POINTS_TO_APPROVED.md](TRUSTED_POINTS_TO_APPROVED.md).

## Trusted permission functions

Each row's trusted version replaces the `PointsTo` permission with `pt_untyped` and `typed_value`.
Its requires and ensures are the current ones,
with `perm.ptr() == ptr` and `perm.wf()` replaced by `pt_parts_wf(ptr@, ..)`,
and `perm.value()` replaced by `typed_value.value()` (slices: `typed_value.value_ref()@`).

| Current (stays, verified) | Trusted version | Kind |
|---|---|---|
| `ptr_ref` | `ptr_ref_untyped_with_typed_value` | exec |
| `ptr_ref_slice` | `ptr_ref_slice_untyped_with_typed_value` | exec |
| `ptr_ref2` | `ptr_ref2_untyped_with_typed_value` | exec |
| `ptr_ref2_ghost` | `ptr_ref2_ghost_untyped_with_typed_value` | axiom |
| `ptr_ref2_slice_ghost` | `ptr_ref2_slice_ghost_untyped_with_typed_value` | axiom |
| `SharedReference<T>::points_to` | `SharedReference<T>::untyped_with_typed_value` | axiom |
| `SharedReference<[T]>::points_to` | `SharedReference<[T]>::untyped_with_typed_value` | axiom |
| `mut_ref_to_shr_points_to` | `mut_ref_to_shr_untyped_with_typed_value` | axiom |
| `mut_ref_to_shr_points_to_slice` | `mut_ref_to_shr_untyped_with_typed_value_slice` | axiom |
| `PointsTo<T>::borrow_mut` | `borrow_mut_untyped_with_typed_value` | axiom |
| `PointsTo<[T]>::borrow_mut` (in `points_to_ops.rs`) | `borrow_mut_slice_untyped_with_typed_value` | axiom |
| rustlib `ptr_ref_str` | `ptr_ref_str_untyped_with_typed_value` | exec |
| rustlib `ptr_ref2_str_ghost` | `ptr_ref2_str_ghost_untyped_with_typed_value` | axiom |
| rustlib `SharedReference<str>::points_to` | `SharedReference<str>::untyped_with_typed_value` | axiom |
| rustlib `mut_ref_to_shr_points_to_str` | `mut_ref_to_shr_untyped_with_typed_value_str` | axiom |
| rustlib `PointsTo<str>::borrow_mut` | `borrow_mut_str_untyped_with_typed_value` | axiom |

`ptr_mut_ref`, `ptr_mut_ref_slice` and rustlib's `ptr_mut_ref_str` are already verified (from `borrow_mut` and `ptr_mut_ref_join`), and are unchanged.

The `str` rows are in rustlib's `proofs/str.rs` (an approved file) and use `pt_parts_wf_str` and `typed_value.value_ref()`.
Their approved `inv()` conditions carry over unchanged:
`SharedReference<str>::untyped_with_typed_value` requires `self.value().inv()`,
`mut_ref_to_shr_untyped_with_typed_value_str` requires `mut_ref.inv()`,
and `borrow_mut_str_untyped_with_typed_value` ensures the final `pt_parts_wf_str` under `final(val).inv()`.

### Sample specs, one per family

Each sample shows the `T` version; the `[T]` version uses `pt_parts_wf_slice`
and `typed_value.value_ref()@` in place of `typed_value.value()` (shown once, for `borrow_mut`).
Doc comments are the current ones, with "permission" read as "the parts of a permission".

**Exec shared borrow** (`ptr_ref`, `ptr_ref_slice`):

```rust
pub const fn ptr_ref_untyped_with_typed_value<T>(
    ptr: *const T,
    Tracked(pt_untyped): Tracked<&PointsToUntyped>,
    Tracked(typed_value): Tracked<&TypedValue<T>>,
) -> (v: &T)
    requires
        pt_parts_wf(ptr@, *pt_untyped, *typed_value),
        typed_value.is_valid(),
    ensures
        v == typed_value.value(),
    opens_invariants none
    no_unwind
;
```

**Exec `SharedReference`** (`ptr_ref2`):

```rust
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
        v.ptr().addr() == ptr.addr(),
        v.ptr()@.metadata == ptr@.metadata,
    opens_invariants none
    no_unwind
;
```

**Ghost `SharedReference`** (`ptr_ref2_ghost`, `ptr_ref2_slice_ghost`):

```rust
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
```

**Permission from a `SharedReference`** (`SharedReference<T>::points_to`, `SharedReference<[T]>::points_to`):

```rust
impl<'a, T> SharedReference<'a, T> {
    pub axiom fn untyped_with_typed_value(tracked self) -> (tracked (pt_untyped, typed_value): (
        &'a PointsToUntyped,
        &'a TypedValue<T>,
    ))
        ensures
            pt_parts_wf(self.ptr()@, *pt_untyped, *typed_value),
            typed_value.is_valid(),
            typed_value.value() == self.value(),
    ;
}
```

`pt.ptr() == self.ptr()` and `pt.wf()` both become `pt_parts_wf(self.ptr()@, ..)`.
The current `points_to` becomes a verified `proof fn` with the same spec, in `ptr_verified_specs.rs`:

```rust
impl<'a, T> SharedReference<'a, T> {
    pub proof fn points_to(tracked self) -> (tracked pt: &'a PointsTo<T>)
        ensures
            pt.ptr() == self.ptr(),
            pt.is_valid(),
            pt.value() == self.value(),
            pt.wf(),
    {
        let tracked (pt_untyped, typed_value) = self.untyped_with_typed_value();
        let tracked u = PointsToUnaligned::from_raw_parts_ref(pt_untyped, typed_value, ());
        // the parts lemma: `pt_parts_wf` of `u`'s parts gives `u.wf()` and alignment
        u.as_aligned()
    }
}
```

**Permission from a `&&mut`** (`mut_ref_to_shr_points_to`, `mut_ref_to_shr_points_to_slice`):

```rust
pub axiom fn mut_ref_to_shr_untyped_with_typed_value<'a, T>(tracked mut_ref: &'a &'a mut T) -> (tracked (
    pt_untyped,
    typed_value,
): (&'a PointsToUntyped, &'a TypedValue<T>))
    ensures
        pt_parts_wf(mut_ref_ptr(*mut_ref)@, *pt_untyped, *typed_value),
        typed_value.is_valid(),
        typed_value.value() == *old(*mut_ref),
        *final(*mut_ref) == *old(*mut_ref),
;
```

**Mutable borrow** (`PointsTo<T>::borrow_mut`, `PointsTo<[T]>::borrow_mut`).
The current ones are methods on the permission;
the parts don't carry the pointer's metadata, so the trusted versions take `ptr`.

```rust
pub axiom fn borrow_mut_untyped_with_typed_value<T>(
    ptr: *mut T,
    tracked pt_untyped: &mut PointsToUntyped,
    tracked typed_value: &mut TypedValue<T>,
) -> (tracked val: &mut T)
    requires
        pt_parts_wf(ptr@, *old(pt_untyped), *old(typed_value)),
        old(typed_value).is_valid(),
    ensures
        *val == old(typed_value).value(),
        mut_ref_ptr(val) == ptr,
        final(pt_untyped).ptr() == old(pt_untyped).ptr(),
        final(typed_value).is_valid(),
        final(typed_value).value() == *final(val),
        pt_parts_wf(ptr@, *final(pt_untyped), *final(typed_value)),
;

pub axiom fn borrow_mut_slice_untyped_with_typed_value<T>(
    ptr: *mut [T],
    tracked pt_untyped: &mut PointsToUntyped,
    tracked typed_value: &mut TypedValue<[T]>,
) -> (tracked val: &mut [T])
    requires
        pt_parts_wf_slice(ptr@, *old(pt_untyped), *old(typed_value)),
        old(typed_value).is_valid(),
    ensures
        val@ == old(typed_value).value_ref()@,
        mut_ref_ptr(val) == ptr,
        final(pt_untyped).ptr() == old(pt_untyped).ptr(),
        final(typed_value).is_valid(),
        final(typed_value).value_ref()@ == final(val)@,
        pt_parts_wf_slice(ptr@, *final(pt_untyped), *final(typed_value)),
;
```

## Field-access primitives

The two trusted modules export these, and `points_to_ops.rs` uses only these to reach the fields.
None of them requires or ensures `wf()` (hence `raw_parts`).
The verified ones are short proof fns over the fields.

`PointsToUnaligned<T>`: unchanged, existing.

| Function | Status |
|---|---|
| `tracked_pt_untyped`, `tracked_typed_value` (`&self` → `&` field) | existing, verified |
| `into_raw_parts` / `from_raw_parts` (owned) | existing, verified |
| `as_raw_parts_mut` (`&mut self` → `&mut` fields) | existing, verified |
| `from_raw_parts_ref` / `from_raw_parts_mut` | existing, approved axioms |

`PointsTo<T>`: one existing, the rest new.

| Function | Status |
|---|---|
| `tracked_pt_unaligned` (`&self` → `&PointsToUnaligned<T>`) | existing, verified |
| `from_unaligned_mut` | existing, approved axiom |
| `into_raw_parts(tracked self) -> PointsToUnaligned<T>`, ensures `out == self.pt_unaligned()` | new, verified |
| `from_raw_parts(tracked u: PointsToUnaligned<T>) -> Self`, ensures `out.pt_unaligned() == u` | new, verified |
| `from_raw_parts_ref(tracked u: &PointsToUnaligned<T>) -> &Self`, ensures `out.pt_unaligned() == *u` | new, verified (`shr_ref_struct_wrap`, as `as_aligned` does now) |
| `as_raw_parts_mut(tracked &mut self) -> &mut PointsToUnaligned<T>`, ensures `*out == old(self).pt_unaligned()`, `final(self).pt_unaligned() == *final(out)` | new, verified |

Extensionality, since the accessors are closed in `points_to_ops.rs` (new, verified):

| Function | Ensures |
|---|---|
| `PointsToUnaligned::lemma_ext(a, b)` | equal `typed_value()`, `pt_untyped()` and `metadata()` ==> `a == b` |
| `PointsTo::lemma_ext(a, b)` | equal `pt_unaligned()` ==> `a == b` |

The current `wf`'d conversions (`into_aligned`, `as_aligned`, `as_aligned_mut`, `into_unaligned`, `as_unaligned`, `as_unaligned_mut`)
move to `points_to_ops.rs` with their specs unchanged, built on these primitives.

`SeqPointsTo` (in the trusted core) gets the same treatment:

| Function | Status |
|---|---|
| `tracked_seq_pt`, `tracked_seq_pt_mut`, `into_seq` | existing, verified |
| `from_seq_mut` | existing, axiom |
| `from_seq(tracked s: Seq<P>, ptr: *mut [T]) -> Self`, ensures `out.seq_pt() == s`, `out.ptr() == ptr` | new, verified |
| `lemma_ext(a, b)`: equal `seq_pt()` and `ptr()` ==> `a == b` | new, verified |

(`PointsToByte` is `external_body`, so it has no fields to reach.)

## Module layout

- **Trusted core** (`points_to_model.rs`):
  the `PTPhys` and `PTProperties` traits, `PointsToByte`, `SeqPointsTo`, `PointsToUntyped`, `TypedValue`, `pt_parts_wf(_slice)`,
  and the `SeqPointsTo` [field-access primitives](#field-access-primitives).
  It is the only code that touches `SeqPointsTo`'s fields.
- **Trusted struct module** (new, `points_to_structs.rs`):
  the `PointsToUnaligned` and `PointsTo` struct definitions, their closed field accessors,
  the three approved structural axioms,
  and their [field-access primitives](#field-access-primitives).
  It is the only code that touches these structs' fields.
- **Verified sibling module** `points_to_ops.rs` (no longer a child of the core):
  the `PTTypedValue` / `PTValueOps` / `PTSizedValue` traits,
  and every `SeqPointsTo` / `PointsToByte` / `PointsToUnaligned` / `PointsTo` impl outside the two trusted modules,
  rewritten to go through the primitives.
  Their specs are unchanged; only proof bodies change.
- **Trusted only:** `ptr_specs.rs` and `shared_reference.rs`.
- **Verified:** a new `ptr_verified_specs.rs` with the `PointsTo` versions of every function in the table.
  `SharedReference::points_to` moves there too.
  `mod.rs` re-exports everything with globs, so callers don't change.
- **Unchanged:** `points_to_collections.rs`, which has no trusted items.

## rustlib

The other trusted items in rustlib that use `PointsTo` / `PointsToUnaligned`
(the `proofs/str.rs` permission functions are in [Trusted permission functions](#trusted-permission-functions)).

| Item | Kind | Change |
|---|---|---|
| `alloc/src/boxed.rs`: `Box::from_raw_in_verus` | exec | takes `PointsToUntyped` + `TypedValue<T>` with `pt_parts_wf` |
| `alloc/src/boxed.rs`: `Box::into_non_null_with_allocator_verus` | exec | returns them |
| `core/src/slice/mod.rs`: `<[T]>::as_slice_ptr_verus` | exec | returns `Tracked<(&PointsToUntyped, &TypedValue<[T]>)>` |
| `core/src/str/mod.rs`: `str::as_str_ptr_verus` | exec | same, for `str` |
| `core/src/ptr/mod.rs`: `ptr::read_unaligned_verus` | exec | takes the parts; `Move` takes `&mut` parts and ensures `final(typed_value) == Empty` |
| `specs/slice_index.rs`: 8 axioms | definitional axioms | kept (decided 2026-11-02) |

- **The verified wrappers** for `Box`, `as_slice_ptr_verus`, `as_str_ptr_verus` and `read_unaligned_verus`
  keep their current names and specs, so callers don't change.
- **`borrow_byte`.** `PointsToUnaligned<str>`'s `PTPhys` impl in `proofs/str.rs` gets a (verified) `borrow_byte`.
  This also takes the impl out of the trusted base.
- **The `slice_index.rs` axioms** are `def_valid_indices_slice_points_to`, `def_valid_indices_str_points_to`,
  and the `[T]` / `str` definitions of the `uninterp` `perm_ptr`, `perm_wf` and `perm_value_eq`.
  Each defines an `uninterp` spec fn at one type as an existing open spec fn (e.g. `perm_ptr(p) == p.ptr()` for `p: &PointsTo<[T]>`).
  This is the file's existing pattern for `&[T]` and `&str`.
  - **They're consistent whatever `PointsTo` means.**
    Each only names an existing spec fn, and no two of them constrain the same type
    (`[T]` and `str` are distinct).
    Unlike `SharedReference::points_to`, none of them claims that a permission exists or is `wf`.
  - **What they're used in.** Their only uses are the `SliceIndexVerus` method specs (`core/src/slice/index.rs`),
    which are trait declarations with verified impls, not trusted specs.
    They would only make `PointsTo`'s definitions trusted if a trusted function's spec used them.

  Decided: keep them.
  The alternative is a sealed helper trait implemented for `[T]` and `str`,
  but the `SliceIndex` specs would then need that bound on a generic `T: ?Sized`.
