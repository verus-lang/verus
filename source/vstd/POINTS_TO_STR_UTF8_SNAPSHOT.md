# Snapshot: `PointsTo<str>` with UTF-8 in `wf`

The approved `str` permission specs that put UTF-8 in `wf`,
saved in case UTF-8 is removed from `wf` (see "Plan: remove UTF-8 from `PointsTo<str>`" in [TYPED_POINTS_TO_PLAN.md](TYPED_POINTS_TO_PLAN.md), on hold)
and later needs to come back.
Only the parts that change are here;
the full documents are at commit `ecfeeb2e6`
(`git show ecfeeb2e6:source/vstd/TYPED_POINTS_TO_APPROVED.md`, section "rustlib: `str`",
and `git show ecfeeb2e6:source/vstd/TYPED_POINTS_TO_PLAN.md`, sections "UTF-8 assumptions" and "Trusted UTF-8 assumptions").
None of this was in rustlib's code yet.

## `additional_validity_constraints`

In `impl PTTypedValue for PointsToUnaligned<str>` (rustlib):

```rust
    /// The value is valid UTF-8 (`str::inv`).
    /// Its length already matches the metadata:
    /// the `str`'s length is equal to the number of bytes by decoding (`EncodingStr`),
    /// which is equal to the metadata by `wf_basic`.
    open spec fn additional_validity_constraints(value: &str, metadata: usize) -> bool {
        value.inv()
    }
```

Summary in "`PointsToUnaligned`: specs":
`additional_validity_constraints` is UTF-8 validity, `str::inv`, since `str` decoding is `EncodingStr`'s, which doesn't include it.

## Casts and `subrange`

Each required UTF-8 so that its output is `wf`:

```rust
impl PointsToUnaligned<str> {
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

    /// Borrows the permission to bytes `[start, end)`,
    /// provided that they're valid UTF-8 when the permission is valid.
    pub proof fn subrange(tracked &self, start: nat, end: nat) -> (tracked out: &PointsTo<str>)
        requires
            self.wf(),
            start <= end <= self.ptr()@.metadata,
            self.typed_value().is_valid()
                ==> valid_utf8(self.typed_value().value_ref()@.subrange(start as int, end as int)),
        ensures
            out.ptr() == ptr_mut_from_data::<str>(PtrData {
                addr: (self.ptr()@.addr + start) as usize,
                provenance: self.ptr()@.provenance,
                metadata: (end - start) as usize,
            }),
            out.bytes() == self.bytes().subrange(start as int, end as int),
            self.typed_value().is_valid() ==> {
                &&& out.typed_value().is_valid()
                &&& out.typed_value().value_ref()@ == self.typed_value().value_ref()@.subrange(start as int, end as int)
            },
            self.typed_value().is_empty() ==> out.typed_value().is_empty(),
            out.wf(),
    ;
}
```

`PointsTo<str>::as_bytes` / `PointsToUnaligned<str>::as_bytes` don't change.

## Trusted UTF-8 assumptions

With UTF-8 in `wf`, these trusted items (all in rustlib) also asserted that the `str` is valid UTF-8, through `wf`:

- `SharedReference<str>::points_to` (axiom): ensures `pt.wf()`, so the referenced `str` is valid UTF-8.
- `mut_ref_to_shr_points_to_str` (axiom): ensures `pt.wf()`, so the current value of the `&mut str` is valid UTF-8.
- `ptr_mut_ref_str` (`external_body`): ensures `final(perm).wf()`, so writes through the returned `&mut str` keep it valid UTF-8.
- `str::as_str_ptr_verus` (`external_body`): ensures `perm@.wf()`, so `self` is valid UTF-8.
  (`as_ptr_verus` ensures the same, but is verified from `as_str_ptr_verus`.)

The other `str` reference helpers (`ptr_ref_str`, `ptr_ref2_str_ghost`) only require `wf`,
`def_perm_init_str` is a definition,
and the generic `?Sized` axioms (`from_raw_parts_ref`, `from_raw_parts_mut`, `from_unaligned_mut`) say nothing about `wf`.
The argument for soundness was that UTF-8 validity is a library invariant of every `&str` / `&mut str`
that safe code can't break.
Travis's objection: a `PointsTo<str>` should guarantee only what a `&str` / `&mut str` does,
and that doesn't include UTF-8.

## rustlib callers

rustlib's `RUSTLIB_PORT_PLAN.md`, G2 (`PointsTo<str>::subrange`):
"The sites check char boundaries, which give the sub-bytes' `valid_utf8` (`valid_utf8_split`)."
The `SliceIndex<str>` methods in `str/traits.rs` have no `inv()` requires,
so with UTF-8 in `wf` they got the parent's UTF-8 from the permission.
