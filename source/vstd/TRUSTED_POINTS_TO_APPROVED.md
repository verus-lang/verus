# Approved: no trusted specs over `PointsTo` / `PointsToUnaligned`

Approved specs from [TRUSTED_POINTS_TO_PLAN.md](TRUSTED_POINTS_TO_PLAN.md).
Names are provisional ([Names](TRUSTED_POINTS_TO_PLAN.md#names)).

## `is_disjoint` (approved 2026-11-02)

`PTPhys` gets a new method:

```rust
/// Borrows the byte permission at address `addr`, which is in this permission's memory range.
proof fn borrow_byte(tracked &self, addr: int) -> (tracked b: &PointsToByte)
    requires
        self.wf_basic(),
        self.ptr()@.addr <= addr < self.ptr()@.addr + Self::size(self.ptr()@.metadata),
    ensures
        b.ptr()@.addr == addr,
;
```

- `PointsToByte::is_disjoint_byte` becomes the axiom, with its current spec.
- `PointsToByte`'s generic `is_disjoint` is verified from `other.borrow_byte` and `is_disjoint_byte`, with its spec unchanged.
- `PTPhys` stays sealed.
- rustlib's `PointsToUnaligned<str>` implements `borrow_byte` (verified).

## Structural axioms (approved 2026-11-02)

These stay trusted, with their specs unchanged:
`PointsToUnaligned::from_raw_parts_ref`, `PointsToUnaligned::from_raw_parts_mut`, `PointsTo::from_unaligned_mut`.

## Well-formed parts (approved 2026-11-02)

Trusted spec fns. `pt_unaligned_parts_wf`, `pt_parts_wf` and `pt_parts_wf_slice` are in vstd's trusted core;
`pt_parts_wf_str` is in rustlib's `proofs/str.rs`.

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

Verified lemmas show that `p.wf()` is `pt_parts_wf(p.ptr()@, ..)` (or `_slice` / `_str`) of `p`'s parts.

## Trusted permission functions (approved 2026-11-02)

Each trusted version takes or gives `pt_untyped: PointsToUntyped` and `typed_value: TypedValue<T>` in place of the permission.
Its requires and ensures are the current ones,
with `perm.ptr() == ptr` and `perm.wf()` replaced by `pt_parts_wf(ptr@, ..)` (`_slice` / `_str`),
and `perm.value()` replaced by `typed_value.value()` (slices: `typed_value.value_ref()@`; `str`: `typed_value.value_ref()`).
Functions that give a permission return `(&'a PointsToUntyped, &'a TypedValue<T>)`.
The `borrow_mut` versions are free functions that take `ptr`.
The current `PointsTo` versions keep their names and specs, as verified wrappers.

The shared-reference rows are superseded (2026-11-02) by [TRACKED_REF_TRUSTED_REVIEW.md](TRACKED_REF_TRUSTED_REVIEW.md):
their trusted versions are replaced by `ptr_shr_ref`, A (`untyped_with_typed_value_ref`), B (`ref_untyped_with_typed_value`) and C (`mut_ref_as_shr_ref`),
and `SharedReference` is removed.

| Current (verified wrapper) | Trusted version | Kind |
|---|---|---|
| `ptr_ref` | ~~`ptr_ref_untyped_with_typed_value`~~ superseded: wrapper over A and `ptr_shr_ref` | exec |
| `ptr_ref_slice` | ~~`ptr_ref_slice_untyped_with_typed_value`~~ superseded: wrapper over A and `ptr_shr_ref` | exec |
| ~~`ptr_ref2`~~ | ~~`ptr_ref2_untyped_with_typed_value`~~ superseded: removed (`SharedReference`) | exec |
| `ptr_ref2_ghost` | ~~`ptr_ref2_ghost_untyped_with_typed_value`~~ superseded: wrapper over A | axiom |
| `ptr_ref2_slice_ghost` | ~~`ptr_ref2_slice_ghost_untyped_with_typed_value`~~ superseded: wrapper over A | axiom |
| ~~`SharedReference<T>::points_to`~~ | ~~`SharedReference<T>::untyped_with_typed_value`~~ superseded: B | axiom |
| ~~`SharedReference<[T]>::points_to`~~ | ~~`SharedReference<[T]>::untyped_with_typed_value`~~ superseded: B | axiom |
| ~~`mut_ref_to_shr_points_to`~~ | ~~`mut_ref_to_shr_untyped_with_typed_value`~~ superseded: C | axiom |
| ~~`mut_ref_to_shr_points_to_slice`~~ | ~~`mut_ref_to_shr_untyped_with_typed_value_slice`~~ superseded: C | axiom |
| `PointsTo<T>::borrow_mut` | `borrow_mut_untyped_with_typed_value` | axiom |
| `PointsTo<[T]>::borrow_mut` | `borrow_mut_slice_untyped_with_typed_value` | axiom |
| rustlib `ptr_ref_str` | ~~`ptr_ref_str_untyped_with_typed_value`~~ superseded: wrapper over A and `ptr_shr_ref` | exec |
| rustlib `ptr_ref2_str_ghost` | ~~`ptr_ref2_str_ghost_untyped_with_typed_value`~~ superseded: wrapper over A | axiom |
| ~~rustlib `SharedReference<str>::points_to`~~ | ~~`SharedReference<str>::untyped_with_typed_value`~~ superseded: B | axiom |
| ~~rustlib `mut_ref_to_shr_points_to_str`~~ | ~~`mut_ref_to_shr_untyped_with_typed_value_str`~~ superseded: C | axiom |
| rustlib `PointsTo<str>::borrow_mut` | `borrow_mut_str_untyped_with_typed_value` | axiom |

`borrow_mut_str_untyped_with_typed_value` keeps its `inv()` condition:
it ensures the final `pt_parts_wf_str` under `final(val).inv()`.

Specs of the remaining trusted versions:

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

## rustlib `Box` and casts (approved 2026-11-02)

Attributes and bodies are the current ones.
The current functions keep their names and specs, as verified wrappers.

```rust
// alloc/src/boxed.rs
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

The casts `as_slice_ptr_untyped_with_typed_value` / `as_str_ptr_untyped_with_typed_value` are superseded (2026-11-02)
by the `as_slice_ptr` / `as_str_ptr` casts and B in [TRACKED_REF_TRUSTED_REVIEW.md](TRACKED_REF_TRUSTED_REVIEW.md).

## Field-access primitives (approved 2026-11-02)

None of them requires or ensures `wf()`.
`points_to_ops.rs` reaches the structs' fields only through these.

`PointsToUnaligned<T>` (existing, unchanged):
`tracked_pt_untyped`, `tracked_typed_value`, `into_raw_parts`, `from_raw_parts`, `as_raw_parts_mut` (verified);
`from_raw_parts_ref`, `from_raw_parts_mut` (axioms).

`PointsTo<T>`:

| Function | Status |
|---|---|
| `tracked_pt_unaligned` | existing, verified |
| `from_unaligned_mut` | existing, axiom |
| `into_raw_parts(tracked self) -> PointsToUnaligned<T>`, ensures `out == self.pt_unaligned()` | new, verified |
| `from_raw_parts(tracked u: PointsToUnaligned<T>) -> Self`, ensures `out.pt_unaligned() == u` | new, verified |
| `from_raw_parts_ref(tracked u: &PointsToUnaligned<T>) -> &Self`, ensures `out.pt_unaligned() == *u` | new, verified |
| `as_raw_parts_mut(tracked &mut self) -> &mut PointsToUnaligned<T>`, ensures `*out == old(self).pt_unaligned()`, `final(self).pt_unaligned() == *final(out)` | new, verified |

`SeqPointsTo<T, P>`:

| Function | Status |
|---|---|
| `tracked_seq_pt`, `tracked_seq_pt_mut`, `into_seq` | existing, verified |
| `from_seq_mut` | existing, axiom |
| `from_seq(tracked s: Seq<P>, ptr: *mut [T]) -> Self`, ensures `out.seq_pt() == s`, `out.ptr() == ptr` | new, verified |

Extensionality lemmas (new, verified):

| Function | Ensures |
|---|---|
| `SeqPointsTo::lemma_ext(a, b)` | equal `seq_pt()` and `ptr()` ==> `a == b` |
| `PointsToUnaligned::lemma_ext(a, b)` | equal `typed_value()`, `pt_untyped()` and `metadata()` ==> `a == b` |
| `PointsTo::lemma_ext(a, b)` | equal `pt_unaligned()` ==> `a == b` |

The `wf`'d conversions (`into_aligned`, `as_aligned`, `as_aligned_mut`, `into_unaligned`, `as_unaligned`, `as_unaligned_mut`)
keep their specs and move to `points_to_ops.rs`.

## Module layout (approved 2026-11-02)

- **`points_to_model.rs` (trusted):**
  the `PTPhys` and `PTProperties` traits, `PointsToByte`, `SeqPointsTo`, `PointsToUntyped`, `TypedValue`,
  `pt_parts_wf` / `pt_parts_wf_slice`, and `SeqPointsTo`'s field-access primitives.
- **`points_to_structs.rs` (new, trusted):**
  the `PointsToUnaligned` and `PointsTo` struct definitions, their closed field accessors,
  the three structural axioms, and their field-access primitives.
- **`points_to_ops.rs` (verified, a sibling, not a child of either):**
  the `PTTypedValue` / `PTValueOps` / `PTSizedValue` traits,
  and every other `SeqPointsTo` / `PointsToByte` / `PointsToUnaligned` / `PointsTo` impl, with specs unchanged.
- **`ptr_specs.rs` (trusted only):** the trusted permission functions and the other existing trusted specs.
  (`shared_reference.rs`'s trusted items are superseded by [TRACKED_REF_TRUSTED_REVIEW.md](TRACKED_REF_TRUSTED_REVIEW.md),
  except `SharedReference` itself, which stays for now.)
- **`ptr_verified_specs.rs` (new, verified):** the `PointsTo` versions of the trusted permission functions.
- **`points_to_collections.rs`:** unchanged.

`mod.rs` re-exports everything with globs.
