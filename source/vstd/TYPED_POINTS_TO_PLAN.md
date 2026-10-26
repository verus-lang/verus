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
and all of `points_to_collections.rs` (`PointsToRaw`, the typed `SeqPointsTo`, and the sequence → slice conversions)
are approved and are in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md).
What remains to review is rustlib's `str` and the modified rustlib specs.

## To run by Travis

- The [trusted UTF-8 assumptions](#trusted-utf-8-assumptions):
  `SharedReference<str>::points_to`, `mut_ref_to_shr_points_to_str`, `ptr_mut_ref_str` and `str::as_str_ptr_verus`
  now also assert that the `str` is valid UTF-8, through `wf`.
- `TypedValue::<[T]>::from_elems_ref` ([New axioms](#new-axioms)).
- `PointsToUntyped::join_ref` / `join_mut` ([New axioms](#new-axioms)).

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

Signatures only; rustlib fixes the details.
rustlib writes `PTPhys`, `PTTypedValue`, `PTProperties` and `PTValueOps` for `PointsToUnaligned<str>`;
its `View` and everything for `PointsTo<str>` come from the generic impls (alignment 1, from `layout_of_str`).
These impls are trusted code in rustlib (see [Trusted surface](#trusted-surface)).

`PTPhys` and `PTTypedValue` are written out from the approved description
([`PointsToUnaligned`: specs](TYPED_POINTS_TO_APPROVED.md#pointstounaligned-specs-phases-2-2b-str-in-rustlib)),
in the same shape as the `[T]` ones:

```rust
impl PTPhys for PointsToUnaligned<str> {
    type A = str;

    /// Builds the `*mut str` from the underlying untyped pointer's address and provenance
    /// and the stored metadata.
    open spec fn ptr(self) -> *mut str {
        ptr_mut_from_data::<str>(
            PtrData {
                addr: self.pt_untyped().ptr()@.addr,
                provenance: self.pt_untyped().ptr()@.provenance,
                metadata: self.metadata(),
            },
        )
    }

    /// The size of the pointed-to region is the length in bytes.
    open spec fn size(metadata: usize) -> nat {
        metadata as nat
    }

    /// A `PointsToUnaligned<str>` is well-formed at the pointer level
    /// if its memory region is `Self::size(self.ptr()@.metadata)` bytes,
    /// and the underlying `PointsToUntyped` is well-formed.
    open spec fn wf_basic(self) -> bool {
        &&& self.pt_untyped().wf()
        &&& self.pt_untyped().len() == Self::size(self.ptr()@.metadata)
    }

    /// `new` has the same pointer
    /// and the same underlying `PointsToUntyped` pointers and length as `old`.
    open spec fn ptrs_len_same(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()
        &&& PointsToUntyped::ptrs_len_same(old.pt_untyped(), new.pt_untyped())
    }

    proof fn stays_wf_basic(old: Self, new: Self) {
    }
}

impl PTTypedValue for PointsToUnaligned<str> {
    /// The inherent `typed_value` accessor.
    open spec fn typed_value(self) -> TypedValue<str> {
        PointsToUnaligned::<str>::typed_value(self)
    }

    /// The underlying untyped permission's bytes.
    open spec fn bytes(self) -> Seq<AbstractByte> {
        self.pt_untyped().bytes()
    }

    /// The value is valid UTF-8 (`str::inv`).
    /// Its length already matches the metadata:
    /// the `str`'s length is equal to the number of bytes by decoding (`EncodingStr`),
    /// which is equal to the metadata by `wf_basic`.
    open spec fn additional_validity_constraints(value: &str, metadata: usize) -> bool {
        value.inv()
    }

    /// Always `true`: a `PointsToUnaligned` has no alignment requirement.
    open spec fn satisfies_alignment(addr: usize) -> bool {
        true
    }

    proof fn bytes_decode(&self);

    proof fn satisfies_alignment_of_wf(&self);

    proof fn lemma_wf_basic(&self);

    // ptrs_len_same_valid_value: the trait's default body.

    /// From `PointsToUntyped::lemma_ptrs_len_same_untyped` on the underlying permissions.
    proof fn lemma_ptrs_len_same_valid_value(old: Self, new: Self);

    /// From `PointsToUntyped::stays_wf` on the underlying permissions.
    proof fn stays_wf(old: Self, new: Self);
}
```

`PTProperties` and `PTValueOps` are the same as for `T` and `[T]`,
except that `PTValueOps` goes through the generic field helpers
(`tracked_typed_value`, `into_raw_parts`, `from_raw_parts`, `as_raw_parts_mut`, `tracked_pt_untyped`),
since rustlib can't touch the fields.

```rust
impl PTProperties for PointsToUnaligned<str> {
    /// Non-nullness follows from the underlying `PointsToUntyped`'s invariant,
    /// since `self.ptr()` and `self.pt_untyped().ptr()` have the same address.
    proof fn is_nonnull(tracked &self);

    /// Delegates to the underlying `PointsToUntyped`'s `ptr_bounds`,
    /// since `self.ptr()` and `self.pt_untyped().ptr()` have the same address.
    proof fn ptr_bounds(tracked &self);

    /// Delegates to the underlying `PointsToUntyped`'s `provenance_not_none`,
    /// since `self.ptr()` and `self.pt_untyped().ptr()` have the same address.
    proof fn provenance_not_none(tracked &self);

    /// Delegates to the underlying `PointsToUntyped`'s `is_disjoint`,
    /// since the two permissions track the same memory range.
    proof fn is_disjoint<OtherPointsToPerm: PTPhys>(
        tracked &mut self,
        tracked other: &OtherPointsToPerm,
    );
}

impl PTValueOps for PointsToUnaligned<str> {
    // zero_sized, borrow, into_untyped, from_untyped: the trait's default bodies.

    /// Delegates to `tracked_typed_value`.
    proof fn borrow_typed_value(tracked &self) -> tracked &TypedValue<str>;

    /// Swaps `Empty` into the typed value,
    /// through `as_raw_parts_mut`.
    proof fn take_typed_value(tracked &mut self) -> (tracked v: TypedValue<str>);

    /// Replaces the typed value,
    /// through `as_raw_parts_mut`.
    proof fn put_typed_value(tracked &mut self, tracked v: TypedValue<str>);

    /// Delegates to `into_raw_parts`.
    proof fn into_untyped_with_typed_value(tracked self) -> (tracked (pt_untyped, v): (PointsToUntyped, TypedValue<str>));

    /// Delegates to `from_raw_parts`.
    proof fn from_untyped_with_typed_value(
        tracked pt_untyped: PointsToUntyped,
        tracked typed_value: TypedValue<str>,
        metadata: usize,
    ) -> (tracked out: Self);

    /// Delegates to `tracked_pt_untyped`.
    proof fn as_untyped(tracked &self) -> (tracked pt_untyped: &PointsToUntyped);

    /// Empties the typed value, then mutably borrows the untyped bytes,
    /// through `as_raw_parts_mut`.
    proof fn as_untyped_mut(tracked &mut self) -> (tracked pt_untyped: &mut PointsToUntyped);
}
```

Only shared casts: there are no owned or `&mut` `str` ↔ `[u8]` permission casts.
Both are proved, with no new axioms:
the value from rustlib's existing `str::as_bytes_tracked` / `str::from_bytes_tracked` and `TypedValue::valid_ref`
(an empty value from `&TypedValue::Empty`, a promoted constant),
and the permission from `from_raw_parts_ref` with the same untyped bytes and metadata.

```rust
impl PointsToUnaligned<str> {
    /// Borrows as a `PointsToUnaligned<[u8]>` to the same bytes, with the same metadata;
    /// the value becomes the string's bytes.
    pub proof fn as_bytes(tracked &self) -> (tracked out: &PointsToUnaligned<[u8]>)
        requires
            self.wf(),
        ensures
            out.ptr()@.addr == self.ptr()@.addr,
            out.ptr()@.provenance == self.ptr()@.provenance,
            out.ptr()@.metadata == self.ptr()@.metadata,
            out.bytes() == self.bytes(),
            out.typed_value().is_valid() == self.typed_value().is_valid(),
            self.typed_value().is_valid() ==> out.typed_value().value_ref()@ == self.typed_value().value_ref()@,
            out.wf(),
    ;

    /// Borrows a `&PointsToUnaligned<[u8]>` as a `str` permission to the same bytes,
    /// with the same metadata, provided that the byte slice is valid UTF-8.
    pub proof fn from_bytes_ref(tracked pt_slice: &PointsToUnaligned<[u8]>) -> (tracked out: &PointsToUnaligned<str>)
        requires
            pt_slice.wf(),
            pt_slice.typed_value().is_valid() ==> valid_utf8(pt_slice.typed_value().value_ref()@),
        ensures
            out.ptr()@.addr == pt_slice.ptr()@.addr,
            out.ptr()@.provenance == pt_slice.ptr()@.provenance,
            out.ptr()@.metadata == pt_slice.ptr()@.metadata,
            out.bytes() == pt_slice.bytes(),
            out.typed_value().is_valid() == pt_slice.typed_value().is_valid(),
            pt_slice.typed_value().is_valid() ==> out.typed_value().value_ref()@ == pt_slice.typed_value().value_ref()@,
            out.wf(),
    ;
}

impl PointsTo<str> {
    /// Borrows as a `PointsTo<[u8]>` to the same bytes, with the same metadata;
    /// the value becomes the string's bytes.
    pub proof fn as_bytes(tracked &self) -> (tracked out: &PointsTo<[u8]>)
        requires
            self.wf(),
        ensures
            out.ptr()@.addr == self.ptr()@.addr,
            out.ptr()@.provenance == self.ptr()@.provenance,
            out.ptr()@.metadata == self.ptr()@.metadata,
            out.bytes() == self.bytes(),
            out.typed_value().is_valid() == self.typed_value().is_valid(),
            self.typed_value().is_valid() ==> out.typed_value().value_ref()@ == self.typed_value().value_ref()@,
            out.wf(),
    ;

    /// Borrows a `&PointsTo<[u8]>` as a `str` permission to the same bytes,
    /// with the same metadata, provided that the byte slice is valid UTF-8.
    pub proof fn from_bytes_ref(tracked pt_slice: &PointsTo<[u8]>) -> (tracked out: &PointsTo<str>)
        requires
            pt_slice.wf(),
            pt_slice.typed_value().is_valid() ==> valid_utf8(pt_slice.typed_value().value_ref()@),
        ensures
            out.ptr()@.addr == pt_slice.ptr()@.addr,
            out.ptr()@.provenance == pt_slice.ptr()@.provenance,
            out.ptr()@.metadata == pt_slice.ptr()@.metadata,
            out.bytes() == pt_slice.bytes(),
            out.typed_value().is_valid() == pt_slice.typed_value().is_valid(),
            pt_slice.typed_value().is_valid() ==> out.typed_value().value_ref()@ == pt_slice.typed_value().value_ref()@,
            out.wf(),
    ;
}
```

`as_bytes` gets the UTF-8 value that `as_bytes_tracked` requires (`self.inv()`) from `self.wf()`,
through `additional_validity_constraints`.
`from_bytes_ref`'s output is well-formed because its value, if valid, is required to be valid UTF-8.

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

#### Modified rustlib specs

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
The `perm_ptr` / `perm_init` / `perm_value_eq` / `valid_indices` wrappers stay,
since `SliceIndexVerus` is generic over `T: ?Sized`.
Their defining axioms for `[T]` and `str` are restored on the new API and added back to `group_slice_index_specs`.
`perm_init` includes `wf`:
`SliceIndexVerus::output_ptr_ref` only requires `perm_init(perm)`,
and the `ptr_ref_slice` / `ptr_ref_str` it calls now require `perm.wf()`.
`valid_indices_slice_points_to` (currently uninterpreted) gets a definition.

```rust
pub open spec fn valid_indices_slice_points_to<T>(start: int, end: int, slice: &PointsTo<[T]>) -> bool {
    0 <= start <= end <= slice.len()
}

pub broadcast axiom fn def_valid_indices_str_points_to(start: int, end: int, slice: &PointsTo<str>)
    ensures
        valid_indices_str(start, end, slice.typed_value().value_ref()) <==> #[trigger] valid_indices(
            start,
            end,
            slice,
        ),
;

pub broadcast axiom fn def_perm_ptr_slice<T>(perm: &PointsTo<[T]>)
    ensures
        #[trigger] perm_ptr(perm) == perm.ptr(),
;

pub broadcast axiom fn def_perm_ptr_str(perm: &PointsTo<str>)
    ensures
        #[trigger] perm_ptr(perm) == perm.ptr(),
;

pub broadcast axiom fn def_perm_init_slice<T>(perm: &PointsTo<[T]>)
    ensures
        #[trigger] perm_init(perm) <==> perm.is_valid() && perm.wf(),
;

pub broadcast axiom fn def_perm_init_str(perm: &PointsTo<str>)
    ensures
        #[trigger] perm_init(perm) <==> perm.is_valid() && perm.wf(),
;

pub broadcast axiom fn def_perm_value_eq_slice<T>(perm: &PointsTo<[T]>, val: &[T])
    ensures
        #[trigger] perm_value_eq(perm, val) <==> perm.typed_value().value_ref()@ == val@,
;

pub broadcast axiom fn def_perm_value_eq_str(perm: &PointsTo<str>, val: &str)
    ensures
        #[trigger] perm_value_eq(perm, val) <==> perm.typed_value().value_ref() == val,
;
```

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
| `impl<T> PointsToUnaligned<[T]>` | `len` (new, inline); `from_untyped_ref`, `from_untyped_with_value_ref`, `borrow_index` (new, phase 4; the primary implementations). (removed in 2b: inherent `wf`) | |
| `impl<T: ?Sized> PointsTo<T>` | closed `pt_unaligned`; `typed_value`, `metadata`, `bytes`, `is_valid`, `is_empty` (open, delegating); `tracked_pt_unaligned`; `from_unaligned_mut` (new axiom M4) | |
| `impl<T: ?Sized> PointsTo<T> where PointsToUnaligned<T>: PTValueOps<A = T>` | `into_unaligned`, `as_unaligned`, `as_unaligned_mut` (new, generic) | Contracts in [`PointsTo`: proofs and aligned/unaligned conversions](#pointsto-proofs-and-alignedunaligned-conversions). |
| `impl<T> PointsTo<T>` | `value`, `is_aligned`, `is_disjoint_pointsto<S>`; `borrow_mut` (axiom). (removed: `wf`, `stays_wf`, `lemma_ptrs_len_same_valid_value`, `zero_sized`, `bytes_decode`, the untyped conversions, the value operations) | Removed ones are `PTValueOps` / `PTSizedValue` methods. |
| `impl<T> PointsTo<[T]>` | `len` (new, inline); `from_untyped_ref`, `from_untyped_with_value_ref`, `borrow_index` (new, phase 4; compositions over the `PointsToUnaligned` versions). (removed: inherent `wf`) | |
| `impl<T, P: PTProperties<A = T>> SeqPointsTo<T, P>` (`points_to_model.rs` / `points_to_ops.rs`) | `seq_pt`, `len`, `spec_index`; `tracked_seq_pt`, `tracked_seq_pt_mut`, `index_mut`, `from_seq`, `empty`, `into_seq` (moved here in phase 1); `split_basic`, `join_basic`, `subrange_basic` (new); `from_seq_mut` (new axiom M5) | Structural; stated with `wf_basic`. The only code touching the fields. |
| `impl<T> SeqPointsTo<T, PointsTo<T>>` | `View` (`SeqPointsToData<T>`); `thin_ptr`, `wf`, `bytes`, `bytes_inner`, `seq_typed_value`, `is_valid`, `is_empty`, `is_fully_empty`, `seq_value`, `is_valid_subrange`, `value_subrange`, `ptrs_len_same_valid_value`, `stays_wf`, `lemma_ptrs_len_same_valid_value`, `typed_value_equiv`, the byte lemmas, `split`, `join`, `subrange`, `subrange_mut` (proved in phase 3b), `zero_sized`, the untyped conversions, the value operations, `is_aligned`, `is_disjoint_seqpt`; `as_slice_pt`, `as_slice_pt_mut` (new, phase 4) | The only typed sequence impl. |
| `impl SeqPointsTo<u8, PointsToByte>` (`PointsToUntyped`, `points_to_model.rs` / `points_to_ops.rs`) | `View`, `bytes`, `wf`, `stays_wf`, `lemma_ptrs_len_same_untyped` (renamed), `zero_sized<T>`, `split`, `split_ref`, `join` (wrappers over the `_basic` primitives); `join_ref`, `join_mut` (axioms); `split_mut` (proved in phase 3b); `is_disjoint_untyped` | |
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
and approved, including `allocate`, `deallocate`, `global_alloc_id` and `PointsTo::borrow_mut`,
except `TypedValue::<[T]>::from_elems_ref` and the untyped joins `join_ref` / `join_mut` (waiting on Travis).

Minor changes to existing axioms (`ptr_ref`, `ptr_ref2`, `ptr_ref2_ghost`, `mut_ref_to_shr_points_to`, `SharedReference::points_to`,
and the restored slice versions `ptr_ref_slice`, `ptr_ref2_slice_ghost`, `mut_ref_to_shr_points_to_slice`, `SharedReference<[T]>::points_to`)
are approved and in [TYPED_POINTS_TO_APPROVED.md](TYPED_POINTS_TO_APPROVED.md#minor-changes-to-existing-trusted-specs),
and so are the strengthened `ptr_mut_ref`, `ptr_mut_ref_slice` and `ptr_mut_ref_str`,
the other `str` reference helpers (minor changes), the new `Seq` tracked operations
(`tracked_borrow_subrange`, `tracked_split_borrow_mut`),
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
