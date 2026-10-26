# Design: `PTValueOps` trait and typed `SeqPointsTo` (level 3)

The specifications and trusted code to review:
a `PTValueOps` trait implemented by `PointsTo` and `PointsToUnaligned` (for `T`, `[T]`, and `str` in rustlib),
the typed `SeqPointsTo<T, PointsTo<T>>` impl,
the sequence → slice conversions and slice indexing,
and every new trusted item in vstd and rustlib.

Approved designs and specs are in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md).
The rationale, background and decisions are in [TYPED_POINTS_TO_NOTES.md](TYPED_POINTS_TO_NOTES.md);
the phases, spike results and risks in [TYPED_POINTS_TO_IMPL_PLAN.md](TYPED_POINTS_TO_IMPL_PLAN.md)
("phase N" below points there).

## Overview

The permission types table, the trait impls table, the written once vs per type tables, the conversions table,
the API changes not visible in the specs, the existing (unchanged) trusted specs, the five trait definitions,
the module layout, all of `points_to_model.rs`'s and `points_to_ops.rs`'s impl blocks,
and all of `points_to_collections.rs` (`PointsToRaw`, the typed `SeqPointsTo`, and the sequence → slice conversions),
and rustlib's `str` impls and casts
are approved and are in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md).
The modified rustlib specs are provisionally accepted.
The `Seq` join axioms (`tracked_add_borrow` / `tracked_add_borrow_mut`, approved by Travis),
and `PointsToUntyped::join_ref` / `join_mut` proved from them, are approved and in TYPED_POINTS_TO_APPROVED.md.
Whether to [remove UTF-8 from `PointsTo<str>`](#plan-remove-utf-8-from-pointstostr) is on hold;
the approved specs still include it.

## Plan: remove UTF-8 from `PointsTo<str>`

**On hold.** The approved specs (TYPED_POINTS_TO_APPROVED.md, "rustlib: `str`") still include UTF-8 in `wf`,
and the rustlib port's other work goes ahead without waiting on this.
A copy of the current UTF-8 specs is in [POINTS_TO_STR_UTF8_SNAPSHOT.md](POINTS_TO_STR_UTF8_SNAPSHOT.md).

Per Travis, a `PointsTo<str>` should guarantee only what a `&str` / `&mut str` does,
and UTF-8 is a library (safety) invariant of `str`, not a validity invariant,
so `wf` shouldn't include it.
UTF-8 would then come only from rustlib's `str::inv()` preconditions on `&str`s, as it does for code that doesn't use permissions.

**Spec changes** (all to approved rustlib specs in TYPED_POINTS_TO_APPROVED.md, "rustlib: `str`"):

1. `PTTypedValue for PointsToUnaligned<str>`: `additional_validity_constraints` becomes `true`,
   with the doc "No constraints beyond decoding: UTF-8 is a library invariant of `str`, not part of the permission."
   (Its length already matches the metadata, as now.)
   `wf` then means the same for `str` as for `[u8]`.
2. `from_bytes_ref` (`PointsToUnaligned<str>` and `PointsTo<str>`):
   drop the requires `pt_slice.typed_value().is_valid() ==> valid_utf8(...)`,
   and "provided that the byte slice is valid UTF-8" from the doc.
   It was only there to establish `out.wf()`.
3. `PointsTo<str>::subrange`: drop the requires `... ==> valid_utf8(...subrange(start, end))`,
   and "provided that they're valid UTF-8 when the permission is valid" from the doc;
   its requires become `self.wf()` and `start <= end <= self.ptr()@.metadata`.
   (It needn't fall on char boundaries either.)

Keeping 2 and 3 instead would break the `SliceIndex<str>` methods in `str/traits.rs` (G2's sites):
they have no `inv()` requires, so they get the sub-bytes' UTF-8 only from the parent permission's `wf`.

**No longer trusted assumptions.**
The [trusted UTF-8 assumptions](#trusted-utf-8-assumptions) go away with no text change:
`SharedReference<str>::points_to`, `mut_ref_to_shr_points_to_str`, `ptr_mut_ref_str` and `str::as_str_ptr_verus`
still ensure `wf()`, which no longer says anything about UTF-8.

**Callers to update** (rustlib; found by rebuilding after 1–3):
proofs that read UTF-8 off a permission's `wf`
(e.g. `split_at_unchecked` calls `valid_utf8_split(perm.value(), mid)`)
get it from the `&str`'s `inv()` requires instead,
through the permission's `typed_value().value_ref() == self`.
Where a function has no `inv()` requires and ensures nothing about UTF-8 (the `SliceIndex<str>` methods),
nothing replaces it.
The transmute proofs (`transmute_shared_ref_u8_slice_str`) keep their `valid_utf8` requires, which `from_bytes_ref` no longer needs.

**Docs.** TYPED_POINTS_TO_APPROVED.md's "rustlib: `str`" section and its summary of `str`'s
`additional_validity_constraints` (in "`PointsToUnaligned`: specs");
this file's [UTF-8 assumptions](#utf-8-assumptions) and [trusted UTF-8 assumptions](#trusted-utf-8-assumptions) sections (deleted);
rustlib's RUSTLIB_PORT_PLAN.md, G2 ("The sites check char boundaries, which give the sub-bytes' `valid_utf8`").

Rustlib is the only user of `PointsTo<str>` (the definitions are moving to rustlib),
so nothing outside rustlib's `str` code is affected.

## TODO: ask Travis

- The [trusted UTF-8 assumptions](#trusted-utf-8-assumptions):
  `SharedReference<str>::points_to`, `mut_ref_to_shr_points_to_str`, `ptr_mut_ref_str` and `str::as_str_ptr_verus`
  now also assert that the `str` is valid UTF-8, through `wf`.
  - We cannot enforce UTF-8 as an invariant of `PointsTo<str>` - it should only guarantee as much as a `&str` or `&mut str` would guarantee, which doesn't guarantee UTF-8.
  - On hold: see [Plan: remove UTF-8 from `PointsTo<str>`](#plan-remove-utf-8-from-pointstostr).
- The [trusted `wf` of a `Box`'s permission](#trusted-wf-of-a-boxs-permission):
  rustlib's `Box::into_non_null_with_allocator_verus` now also ensures the permission it returns is `wf`.
  - Yes - a `Box<T>` is just a pointer and `PointsTo<T>`.
  - Done: approved.
- `TypedValue::<[T]>::from_elems_ref` ([New axioms](#new-axioms)).
  - Yes, but this is a change from the current VerusBelt model. 
    The current VerusBelt model enforces multiple shared references in a struct are distinct.
    This is probably a problem with the VerusBelt model, because Rust semantics do allow duplicate shared references in a struct.
    We can allow this axiom, but we MUST ensure that we don't do things which contradict it:
    e.g., a slice with two shared references cannot assume that they are distinct. 
- `PointsToUntyped::join_ref` / `join_mut` ([New axioms](#new-axioms)).
   - These axioms should be defined on `Seq` instead,
    and then prove `join_ref` and `join_mut` from the `Seq` axioms.
   - Done: `Seq::tracked_add_borrow` / `tracked_add_borrow_mut`, approved by Travis; in TYPED_POINTS_TO_APPROVED.md.
- `tracked_slice_subrange` ([For the rustlib port](#tracked_slice_subrange-trusted-alternative-to-from_elems_ref-for-subrange)):
  an alternative to building slice subranges with `from_elems_ref`.
   - Seems fine to add. With additional slice (or maybe it was pattern?) support the axiom will be proved, but that's not in place yet.
- `TrivialOwnershipData` ([For the rustlib port](#tracked-values-of-trivial-ownership-types-trusted)):
  spec integers can be made tracked.
  - Yes this is fine. Note that another user also needs this, so for now only make minimal changes since we will probably each add some version of it.

The specs, written out in full
(copies of the ones in TYPED_POINTS_TO_APPROVED.md, the code, and [Modified rustlib specs](#modified-rustlib-specs)).

### UTF-8 assumptions

A `str` permission's `wf` includes UTF-8 validity,
through `PointsToUnaligned<str>`'s `additional_validity_constraints`
([approved](TYPED_POINTS_TO_APPROVED.md#rustlib-str)):

```rust
    /// The value is valid UTF-8 (`str::inv`).
    /// Its length already matches the metadata:
    /// the `str`'s length is equal to the number of bytes by decoding (`EncodingStr`),
    /// which is equal to the metadata by `wf_basic`.
    open spec fn additional_validity_constraints(value: &str, metadata: usize) -> bool {
        value.inv()
    }
```

So each `wf()` in these ensures asserts that the `str` is valid UTF-8.
All four are in rustlib.

```rust
impl<'a> SharedReference<'a, str> {
    pub axiom fn points_to(tracked self) -> (tracked pt: &'a PointsTo<str>)
        ensures
            pt.ptr() == self.ptr(),
            pt.is_valid(),
            pt.typed_value().value_ref() == self.value(),
            pt.wf(),
    ;
}

/// Convert from a shared reference to a `&'a mut str` to a `&'a PointsTo<str>`.
pub axiom fn mut_ref_to_shr_points_to_str<'a>(tracked mut_ref: &'a &'a mut str) -> (tracked pt: &'a PointsTo<str>)
    ensures
        pt.ptr() == mut_ref_ptr(*mut_ref),
        pt.is_valid(),
        pt.typed_value().value_ref() == &*old(*mut_ref),
        pt.wf(),
        &*final(*mut_ref) == &*old(*mut_ref),
;

/// Equivalent to `&mut *ptr`, passing in a permission `perm` to ensure safety.
/// The memory pointed to by `ptr` must be initialized.
#[inline(always)]
#[verifier::external_body]
pub const fn ptr_mut_ref_str(ptr: *mut str, Tracked(perm): Tracked<&mut PointsTo<str>>) -> (v: &mut str)
    requires
        old(perm).ptr() == ptr,
        old(perm).is_valid(),
        old(perm).wf(),
    ensures
        final(perm).ptr() == ptr,
        final(perm).is_valid(),
        // The final bytes decode to the final value.
        final(perm).wf(),
        old(perm).typed_value().value_ref() == &*v,
        final(perm).typed_value().value_ref() == &*final(v),
    opens_invariants none
    no_unwind
{
    unsafe { &mut *ptr }
}

// In `impl str` (`str/mod.rs`).
#[verifier::shadow_data]
#[verifier::external_body] // Ok - cast from `&self` to `*const str`
// Axiomatizes cast from `&self` to `*const str`, since Verus doesn't support it.
pub const fn as_str_ptr_verus(&self) -> ((ptr, perm): (*const str, Tracked<&PointsTo<str>>))
    ensures
        ptr == shared_ref_ptr(shadow_data(self)),
        perm@.ptr() == shared_ref_ptr(shadow_data(self)),
        perm@.is_valid(),
        perm@.typed_value().value_ref() == self,
        perm@.wf(),
{
    (self as *const str, Tracked::assume_new())
}
```

### `TypedValue::<[T]>::from_elems_ref`

`points_to_model.rs`; the shared counterpart of M1 (`from_elems_mut`, approved).
It replaces the generic `tracked_slice_from_refs`,
so it only covers `TypedValue`s, which have no physical memory.

```rust
impl<T> TypedValue<[T]> {
    /// A sequence of borrows of typed values acts as one borrow of a slice typed value.
    /// If any element is empty, the slice is empty.
    pub axiom fn from_elems_ref<'a>(tracked elems: Seq<&'a TypedValue<T>>)
        -> (tracked out: &'a TypedValue<[T]>)
        ensures
            // Valid with the elements' values if every element is valid
            // (a zero-length Seq counts as valid); otherwise empty.
            (forall|i: int| #![trigger elems[i]] 0 <= i < elems.len() ==> elems[i].is_valid()) ==> {
                &&& out.is_valid()
                &&& out.value_ref()@ == Seq::new(elems.len(), |i: int| elems[i].value())
            },
            !(forall|i: int| #![trigger elems[i]] 0 <= i < elems.len() ==> elems[i].is_valid()) ==> out.is_empty(),
    ;
}
```

## For the rustlib port: slice subranges and integer casts

Proposed for the gaps flagged in rustlib's `RUSTLIB_PORT_PLAN.md` (G1–G4).

### `subrange` on slice permissions (verified)

Approved and implemented in `points_to_ops.rs`.
G1, and through it G2 and G4.

### `tracked_slice_subrange` (trusted)

Accepted (Travis; added for other users, since `subrange` uses `from_elems_ref`).
`slice.rs`, next to `tracked_slice_index`:

```rust
/// Borrows elements `[i, j)` of a borrowed slice.
pub axiom fn tracked_slice_subrange<'a, T>(tracked s: &'a [T], i: int, j: int) -> (tracked out: &'a [T])
    requires
        0 <= i <= j <= s@.len(),
    ensures
        out@ == s@.subrange(i, j),
;
```

### Tracked values of trivial-ownership types (trusted)

Accepted (Travis), kept minimal since another user needs something similar.
G3. `modes.rs`, next to `tracked_static_mut_ref`:

```rust
/// Types whose values own no resources (no permissions, tokens or other tracked data),
/// so any spec value can be used as a tracked one.
pub trait TrivialOwnership: Sized {
    /// Makes a spec value tracked.
    proof fn tracked_from_spec(v: Self) -> (tracked out: Self)
        ensures
            out == v,
    ;
}
```

Implemented only for `u32` and `usize` (what rustlib's G3 uses),
each impl's `tracked_from_spec` an `axiom fn`, so every impl is visibly trusted
(as with the `AbstractByteRepresentation` impls' `abs_encode_impl`).

### Decoding integers from smaller integers' bytes (verified)

G3. Approved and implemented in `type_representation.rs` (no new axioms):
the trait `DecodesToNat`, implemented for every unsigned integer type
(`u16` and `u128` gained `Base` / `BasePow2` impls in `endian.rs` for this),
and the general `lemma_abs_decode_to_big`.
The cast helpers `PointsTo<[T]>::as_big_aligned` / `as_big_unaligned` (verified) are in `points_to_ops.rs`,
with the bound `V: TrivialOwnership + DecodesToNat + 'static`.

## Specifications

Every module is written out item by item, with its documentation and contract.
Approved axioms are named in a comment, not repeated; their code is in TYPED_POINTS_TO_APPROVED.md.
Spec fn bodies are written out; proof bodies are omitted.
Trait impl methods don't restate their contracts, which are the trait's
([Trait definitions](TYPED_POINTS_TO_APPROVED.md#trait-definitions)).

Grouped by module ([layout](TYPED_POINTS_TO_APPROVED.md#module-layout)), from low-level to high-level permissions.
An impl block with both spec fns and proofs is split as in the layout:
`points_to_model.rs` holds the closed accessors,
and every spec fn that an axiom depends on
(directly or through the spec fns it unfolds to).
Other open spec fns, such as `len`, may live with the proofs that use them.
The trait definitions are in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#trait-definitions).

### `points_to_model.rs` (trusted)

The five trait definitions, with their default bodies, are approved
([TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#trait-definitions)).
The lemma groups (`group_points_to_lemmas`, `group_points_to_collections_lemmas`) are in
[Module layout](TYPED_POINTS_TO_APPROVED.md#module-layout).

All of `points_to_model.rs`'s impl blocks
(`PointsToByte`, `SeqPointsTo` / `PointsToUntyped`, `TypedValue`, `PointsToUnaligned` and `PointsTo`) are approved
([Impls](TYPED_POINTS_TO_APPROVED.md#impls)).

### `points_to_ops.rs` (trusted)

A child module of `points_to_model.rs`, so it can use the structs' private fields
([phase 0, item 15](TYPED_POINTS_TO_IMPL_PLAN.md#phase-0-pending-checks)).

#### `SeqPointsTo` and `PointsToUntyped`: proofs (phase 1b)

`SeqPointsTo`'s `PTProperties` impl, the structural `impl<T, P: PTProperties<A = T>> SeqPointsTo<T, P>`,
and the `impl PointsToUntyped` proofs are approved
([`points_to_ops.rs`: `SeqPointsTo`](TYPED_POINTS_TO_APPROVED.md#points_to_opsrs-seqpointstos-ptproperties-and-structural-operations-phase-1b),
[`points_to_ops.rs`: `PointsToUntyped`](TYPED_POINTS_TO_APPROVED.md#points_to_opsrs-pointstountypeds-proofs-phase-1b)).

#### `PointsToUnaligned`: proofs

`PointsToUnaligned`'s `PTProperties`, `PTValueOps` and `PTSizedValue` impls and `is_disjoint_unaligned` are approved
([`points_to_ops.rs`: `PointsToUnaligned`](TYPED_POINTS_TO_APPROVED.md#points_to_opsrs-pointstounaligneds-proofs)),
and so are the field primitives `tracked_typed_value`, `into_raw_parts`, `from_raw_parts` and `as_raw_parts_mut`
([`PointsToUnaligned`: specs](TYPED_POINTS_TO_APPROVED.md#pointstounaligned-specs-phases-2-2b-str-in-rustlib)).

#### `PointsTo`: proofs and aligned/unaligned conversions

Approved ([`points_to_ops.rs`: `PointsTo`](TYPED_POINTS_TO_APPROVED.md#points_to_opsrs-pointstos-proofs-and-the-alignedunaligned-conversions)).

#### Slices: indexing and borrowed constructors (phase 4)

Approved ([`points_to_ops.rs`: slices](TYPED_POINTS_TO_APPROVED.md#points_to_opsrs-slice-indexing-and-borrowed-constructors-phase-4)).
They need no new axioms:
for `borrow_index`, the bytes come from `split_ref` on the untyped permission,
a valid element's typed value from `tracked_slice_index` and `TypedValue::valid_ref`
(an empty one from `&TypedValue::Empty`, a promoted constant),
and the permission from `from_raw_parts_ref`.

### `points_to_collections.rs` (verified)

#### `PointsToRaw` (phase 2c)

Approved ([`points_to_collections.rs`: `PointsToRaw`](TYPED_POINTS_TO_APPROVED.md#points_to_collectionsrs-pointstoraw-phase-2c)).

#### Typed `SeqPointsTo` (phase 1b)

Approved ([`points_to_collections.rs`: typed `SeqPointsTo`](TYPED_POINTS_TO_APPROVED.md#points_to_collectionsrs-typed-seqpointsto-phase-1b)).

#### Sequence → slice conversions (phase 4)

Approved ([`points_to_collections.rs`: sequence → slice conversions](TYPED_POINTS_TO_APPROVED.md#points_to_collectionsrs-sequence--slice-conversions-phase-4)).

### `ptr_specs.rs` (trusted)

`allocate` and `deallocate` (`global_alloc_id` is in `ptr_model.rs`): approved; see [Allocation](#allocation-phase-2c).

### rustlib

#### `str` (rustlib)

The `PTPhys`, `PTTypedValue`, `PTProperties` and `PTValueOps` impls for `PointsToUnaligned<str>`,
and the `str` ↔ `[u8]` casts (`as_bytes`, `from_bytes_ref`):
approved; see [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#rustlib-str).

The other rustlib axioms (the `str` reference helpers):
see [New rustlib axioms](#new-rustlib-axioms).

#### Trusted UTF-8 assumptions

To review: since UTF-8 validity is now part of a valid `str` permission's `wf`,
these trusted items now also assert that the `str` is valid UTF-8:

- `SharedReference<str>::points_to` (axiom): ensures `pt.wf()`,
  so the referenced `str` is valid UTF-8.
- `mut_ref_to_shr_points_to_str` (axiom): ensures `pt.wf()`,
  so the current value of the `&mut str` is valid UTF-8.
- `ptr_mut_ref_str` (`external_body`): ensures `final(perm).wf()`,
  so writes through the returned `&mut str` keep it valid UTF-8.
- `str::as_str_ptr_verus` (`external_body`, restated in [Modified rustlib specs](#modified-rustlib-specs)):
  ensures `perm@.wf()`, so `self` is valid UTF-8.
  (`as_ptr_verus` ensures the same, but is verified from `as_str_ptr_verus`.)

These are the only ones:
the other `str` reference helpers (`ptr_ref_str`, `ptr_ref2_str_ghost`) only require `wf`,
`def_perm_init_str` is a definition,
and the generic `?Sized` axioms (`from_raw_parts_ref`, `from_raw_parts_mut`, `from_unaligned_mut`) say nothing about `wf`.
This should be sound, since UTF-8 validity is a library invariant of every `&str` / `&mut str`
that safe code can't break, but these axioms now state more than before.

#### Trusted `wf` of a `Box`'s permission

Approved (2026-10-26). rustlib's `Box::into_non_null_with_allocator_verus` (`alloc/src/boxed.rs`, `external_body`)
now also ensures `out.2@.wf()` for the `PointsTo<T>` it returns (sized `T`),
since `linked_list` passes that permission to `ptr_mut_ref`, which requires `wf`.
`Box` has no spec of its own about its memory (it's an opaque `external_body` struct with only `alloc_id`),
so this is a new trusted fact.
It should be sound, since a `Box`'s pointer is aligned and points to an initialized `T`:
`wf` asks for `size_of::<T>()` consecutive bytes at the pointer, alignment to `T`,
and that a valid value's bytes decode to it,
but not that the provenance is `Some` or the range in bounds, so a zero-sized `T`'s dangling pointer is covered.
(Its counterpart `from_raw_in_verus` now requires `perm.wf()` and `perm.is_valid()`.)

```rust
pub fn into_non_null_with_allocator_verus(b: Self) -> (out: (NonNull<T>, A, Tracked<PointsTo<T>>))
    where T: Sized
    ensures
        out.0@ == out.2@.ptr(),
        *b == out.2@.value(),
        out.2@.is_valid(),
        out.2@.wf(),
        b.alloc_id() == out.1.alloc_id(),
        out.0@@.provenance.unwrap().alloc_id() == out.1.alloc_id()
```

#### Modified rustlib specs

Provisionally accepted (2026-10-25): used for the rustlib port, and revisited if the port needs changes.

Existing rustlib specs that mention `PointsTo<str>` or `PointsTo<[T]>`,
restated for the new API
(`typed_value().value_ref()`, `is_valid()` and `wf()` in place of `value()` and `is_init()`).
The functions that are `external_body` only because these were missing
(`str::get_unchecked`, `get_unchecked_mut`, `split_at_unchecked`,
and the `SliceIndex<str>` / `SliceIndexVerus<str>` methods in `str/traits.rs`)
get their verified bodies back, with unchanged specs.

**`str::as_str_ptr_verus` / `as_ptr_verus`** (`str/mod.rs`; `as_ptr_verus` calls `as_str_ptr_verus`).
Still `external_body`, since Verus doesn't support the `&str` → `*const str` cast.
The ensures state the permission directly, and add `wf`,
which `ptr_ref_str` and `ptr_ref2_str_ghost` now require.
`as_ptr_tracked` stays commented out.

```rust
#[verifier::shadow_data]
#[verifier::external_body] // Ok - cast from `&self` to `*const str`
// Axiomatizes cast from `&self` to `*const str`, since Verus doesn't support it.
pub const fn as_str_ptr_verus(&self) -> ((ptr, perm): (*const str, Tracked<&PointsTo<str>>))
    ensures
        ptr == shared_ref_ptr(shadow_data(self)),
        perm@.ptr() == shared_ref_ptr(shadow_data(self)),
        perm@.is_valid(),
        perm@.typed_value().value_ref() == self,
        perm@.wf(),
{
    (self as *const str, Tracked::assume_new())
}

#[verifier::shadow_data]
pub const fn as_ptr_verus(&self) -> ((ptr, perm): (*const u8, Tracked<&PointsTo<str>>))
    ensures
        ptr == shared_ref_ptr(shadow_data(self)) as *const u8,
        perm@.ptr() == shared_ref_ptr(shadow_data(self)),
        perm@.is_valid(),
        perm@.typed_value().value_ref() == self,
        perm@.wf(),
{
    let (ptr, perm) = self.as_str_ptr_verus();
    (ptr as *const u8, perm)
}
```

**`slice_index.rs` wrappers.**
Approved (2026-10-26); in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#rustlib-slice_indexrs-wrappers).

**Shared-reference transmutes** (`proofs/str.rs`).
`transmute_shared_ref_str_u8_slice` and `transmute_shared_ref_u8_slice_str` go back from axioms to proofs, with unchanged specs:
`SharedReference<str>::points_to`, then `PointsTo<str>::as_bytes`, then `ptr_ref2_slice_ghost`;
and `SharedReference<[u8]>::points_to`, then `PointsTo<str>::from_bytes_ref`, then `ptr_ref2_str_ghost`
(`valid_utf8(src.value()@)` satisfies `from_bytes_ref`'s requires).

## Inherent impls

What stays outside the traits, by impl block, after all phases.
"(new)" is added by this design; "(removed)" lists what moves into a trait;
everything else exists today.

| Impl block | Functions | Notes |
|---|---|---|
| `impl<T: ?Sized> TypedValue<T>` | `is_valid`, `is_empty`; `value_ref` (new); `valid_ref` (new, phase 3b) | |
| `impl<T> TypedValue<T>` | `value`, `tracked_copy` | Sized: by-value access |
| `impl<T> TypedValue<[T]>` | `value` (-> `&[T]`); `from_elems_ref` (new axiom, phase 3b); `from_elems_mut` (new axiom M1, phase 3b) | |
| `impl<T: ?Sized> PointsToUnaligned<T>` | closed accessors `typed_value`, `pt_untyped`, `metadata`; `bytes`, `is_valid`, `is_empty` (inline); `tracked_pt_untyped`; `as_raw_parts_mut` (new, phase 4); `tracked_typed_value`, `into_raw_parts`, `from_raw_parts` (new; for rustlib's `str`); `from_raw_parts_ref` (new axiom, phase 3b), `from_raw_parts_mut` (new axiom M3, phase 3b) | The inherent `typed_value`/`bytes` coexist with the trait's (phase 0, item 5). |
| `impl<T: ?Sized> PointsToUnaligned<T> where PointsToUnaligned<T>: PTValueOps<A = T>` | `into_aligned`, `as_aligned` (new, generic); `as_aligned_mut` (new, generic, phase 3b: needs M4) | Contracts in [`PointsTo`: proofs and aligned/unaligned conversions](#pointsto-proofs-and-alignedunaligned-conversions). |
| `impl<T> PointsToUnaligned<T>` | `value`; `is_disjoint_unaligned<S>`. (removed: `wf`, `stays_wf`, `zero_sized`) | |
| `impl<T> PointsToUnaligned<[T]>` | `len` (new, inline); `from_untyped_ref`, `from_untyped_with_value_ref`, `borrow_index` (new, phase 4; the primary implementations); `subrange` (new, rustlib port). (removed in 2b: inherent `wf`) | |
| `impl<T: ?Sized> PointsTo<T>` | closed `pt_unaligned`; `typed_value`, `metadata`, `bytes`, `is_valid`, `is_empty` (open, delegating); `tracked_pt_unaligned`; `from_unaligned_mut` (new axiom M4) | |
| `impl<T: ?Sized> PointsTo<T> where PointsToUnaligned<T>: PTValueOps<A = T>` | `into_unaligned`, `as_unaligned`, `as_unaligned_mut` (new, generic) | Contracts in [`PointsTo`: proofs and aligned/unaligned conversions](#pointsto-proofs-and-alignedunaligned-conversions). |
| `impl<T> PointsTo<T>` | `value`, `is_aligned`, `is_disjoint_pointsto<S>`; `borrow_mut` (axiom). (removed: `wf`, `stays_wf`, `lemma_ptrs_len_same_valid_value`, `zero_sized`, `bytes_decode`, the untyped conversions, the value operations) | Removed ones are `PTValueOps` / `PTSizedValue` methods. |
| `impl<T> PointsTo<[T]>` | `len` (new, inline); `from_untyped_ref`, `from_untyped_with_value_ref`, `borrow_index` (new, phase 4; compositions over the `PointsToUnaligned` versions); `subrange` (new, rustlib port). (removed: inherent `wf`) | |
| `impl<T, P: PTProperties<A = T>> SeqPointsTo<T, P>` (`points_to_model.rs` / `points_to_ops.rs`) | `seq_pt`, `len`, `spec_index`; `tracked_seq_pt`, `tracked_seq_pt_mut`, `index_mut`, `from_seq`, `empty`, `into_seq` (moved here in phase 1); `split_basic`, `join_basic`, `subrange_basic` (new); `from_seq_mut` (new axiom M5) | Structural; stated with `wf_basic`. The only code touching the fields. |
| `impl<T> SeqPointsTo<T, PointsTo<T>>` | `View` (`SeqPointsToData<T>`); `thin_ptr`, `wf`, `bytes`, `bytes_inner`, `seq_typed_value`, `is_valid`, `is_empty`, `is_fully_empty`, `seq_value`, `is_valid_subrange`, `value_subrange`, `ptrs_len_same_valid_value`, `stays_wf`, `lemma_ptrs_len_same_valid_value`, `typed_value_equiv`, the byte lemmas, `split`, `join`, `subrange`, `subrange_mut` (proved in phase 3b), `zero_sized`, the untyped conversions, the value operations, `is_aligned`, `is_disjoint_seqpt`; `as_slice_pt`, `as_slice_pt_mut` (new, phase 4) | The only typed sequence impl. |
| `impl SeqPointsTo<u8, PointsToByte>` (`PointsToUntyped`, `points_to_model.rs` / `points_to_ops.rs`) | `View`, `bytes`, `wf`, `stays_wf`, `lemma_ptrs_len_same_untyped` (renamed), `zero_sized<T>`, `split`, `split_ref`, `join` (wrappers over the `_basic` primitives); `join_ref`, `join_mut` (proved from the `Seq` join axioms); `split_mut` (proved in phase 3b); `is_disjoint_untyped` | |
| `impl PointsToByte` (renamed from `PointsToSingleton`) | `byte`, `is_disjoint_byte` (renamed from `is_disjoint_singleton`, in phase 1 with the type) | |
| `impl PointsToRaw` | everything in [`PointsToRaw` (phase 2c)](#pointstoraw-phase-2c) above (new) | Not a `PTPhys`. |
| free functions | `tracked_slice_index`, `tracked_ref` (new axioms, phase 3b); `allocate`, `deallocate` (ported, phase 2c, with `PointsToUntyped` in place of `PointsToRaw`; in `ptr_specs.rs`; `Dealloc` dropped) | |
| rustlib: `impl PointsToUnaligned<str>` | `as_bytes`, `from_bytes_ref` | |
| rustlib: `impl PointsTo<str>` | `as_bytes`, `from_bytes_ref` (through the aligned/unaligned conversions) | |

## Trusted surface

Every trusted item the permissions rely on, after all phases:
`axiom fn`s, `external_body` functions and types, `assume_specification`s,
and `uninterp` specs that axioms constrain.
"Uses" names the main dependents.

**Existing, unchanged.** Approved; see [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#existing-unchanged-trusted-specs).

**New.** See [New axioms](#new-axioms).

**Dependency direction.**
`ptr_ref`, `ptr_mut_ref` and `mut_ref_to_shr_points_to` (in `ptr_specs.rs`) take or produce `PointsTo<T>`,
and the restored slice versions `PointsTo<[T]>`;
`allocate` / `deallocate` use `PointsToUntyped`.
The phase 3b axioms are stated on `PointsToUnaligned`, `PointsTo`, `SeqPointsTo` and `TypedValue`.
All of these are in the two trusted files (see [Module layout](TYPED_POINTS_TO_APPROVED.md#module-layout)),
so no trusted code depends on `points_to_collections.rs`.

**rustlib.** rustlib also holds trusted code for `str`:
its axioms (`ptr_mut_ref_str`, the other `str` reference helpers, `spec_size_of_val_str`),
and the `PTPhys`, `PTTypedValue`, `PTProperties` and `PTValueOps` impls for `PointsToUnaligned<str>`.
The impls aren't axioms, but they're trusted in effect:
`PTPhys::size` and `wf_basic` fix what memory a `PointsToUnaligned<str>` claims,
which the `str` reference axioms rely on,
and `PTTypedValue`'s `additional_validity_constraints` and `satisfies_alignment` feed into `wf`.
Sealing doesn't keep them in vstd:
vstd's `impl<T: ?Sized> PTPhysSealed for PointsToUnaligned<T>` covers every `PointsToUnaligned<_>`,
so rustlib can write `PTPhys` for any of them, not just `str`.

## New axioms

All in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#new-axioms-and-axioms-with-bigger-changes)
and approved, including `allocate`, `deallocate`, `global_alloc_id`, `PointsTo::borrow_mut`
and `TypedValue::<[T]>::from_elems_ref` (approved by Travis).

Minor changes to existing axioms (`ptr_ref`, `ptr_ref2`, `ptr_ref2_ghost`, `mut_ref_to_shr_points_to`, `SharedReference::points_to`,
and the restored slice versions `ptr_ref_slice`, `ptr_ref2_slice_ghost`, `mut_ref_to_shr_points_to_slice`, `SharedReference<[T]>::points_to`)
are approved and in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#minor-changes-to-existing-trusted-specs),
and so are the strengthened `ptr_mut_ref`, `ptr_mut_ref_slice` and `ptr_mut_ref_str`,
the other `str` reference helpers (minor changes), the new `Seq` tracked operations
(`tracked_borrow_subrange`, `tracked_split_borrow_mut`, `tracked_add_borrow`, `tracked_add_borrow_mut`),
and the borrowed-assembly axioms (`tracked_slice_index`, `tracked_ref`,
`PointsToUnaligned::from_raw_parts_ref`, M1, M3–M5)
([TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#new-axioms-and-axioms-with-bigger-changes)).

**rustlib.** All new rustlib axioms are approved
([TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#new-axioms-and-axioms-with-bigger-changes)).

"New" means new relative to the `verify-rustlib` branch.
`abs_decode_slice` (already in `type_representation.rs`) is approved and listed in
[TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#new-axioms-and-axioms-with-bigger-changes).

### Borrowed-assembly axioms (phase 3b)

All in
[TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#new-axioms-and-axioms-with-bigger-changes):
the shared ones (`tracked_slice_index`, `tracked_ref`, `PointsToUnaligned::from_raw_parts_ref`,
and `TypedValue::<[T]>::from_elems_ref`, which is waiting on Travis) and the `&mut` ones (M1, M3–M5).

### Slice reference helpers (phase 4b)

Approved and in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md):
`ptr_mut_ref_slice` with `ptr_mut_ref` in
[New axioms and axioms with bigger changes](TYPED_POINTS_TO_APPROVED.md#new-axioms-and-axioms-with-bigger-changes),
and the rest in [Minor changes to existing trusted specs](TYPED_POINTS_TO_APPROVED.md#minor-changes-to-existing-trusted-specs).

### Allocation (phase 2c)

Approved; see [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#new-axioms-and-axioms-with-bigger-changes).

### New rustlib axioms

All approved and in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md):
`ptr_mut_ref_str` in
[New axioms and axioms with bigger changes](TYPED_POINTS_TO_APPROVED.md#new-axioms-and-axioms-with-bigger-changes),
and the other `str` reference helpers in [Minor changes to existing trusted specs](TYPED_POINTS_TO_APPROVED.md#minor-changes-to-existing-trusted-specs).
