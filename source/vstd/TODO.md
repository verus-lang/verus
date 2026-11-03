# To do: trusted `PointsTo` refactor and `Tracked<&T>`

The trusted specs are in [TRUSTED_REVIEW.md](TRUSTED_REVIEW.md).

## For review

Implemented in vstd and rustlib (both build with 0 errors); not yet reviewed:

1. `SeqPointsTo::from_seq` is named `from_raw_parts`.
2. New verified primitive `SeqPointsTo::from_seq_ref`.
3. The verified lemmas are `PointsTo<T>` / `PointsTo<[T]>` / `PointsTo<str>::lemma_pt_parts_wf`.
4. `PointsTo::from_unaligned_mut`'s doc comment wording.
5. rustlib's `proofs/str.rs` (approved file) gains `PointsToUnaligned<str>::borrow_byte`, `pt_parts_wf_str` and `lemma_pt_parts_wf`,
   and `PointsTo<str>::borrow_mut` becomes a verified wrapper.
6. Names: `*_untyped_with_typed_value` (the `SharedReference` and `Box` items),
   and `pt_unaligned_parts_wf` / `pt_parts_wf` / `pt_parts_wf_slice` / `pt_parts_wf_str`.
7. `mut_ref_to_shr_points_to` (+ slice, `str`) are kept as verified proof wrappers (`mut_ref_as_shr_ref`, then `ref_to_parts*`), specs unchanged.
8. `as_slice_ptr_verus`, `as_str_ptr_verus` and the two `as_ptr_verus` are deleted;
   callers use the casts and the new verified `shr_ref_points_to` (+ slice, `str`).
9. `#[verifier::shadow_data]` is added to `ptr_ref` / `ptr_ref_slice` / `ptr_ref_str`, `<[T]>::get_unchecked_verus`, `str::get_unchecked`,
   and `ExSliceIndex::get` / `index` (so they lose their `call_requires` / `call_ensures` axioms).

## After review

- **Rename `ptr_eq_up_to_tag`** (`*mut`) to `ptr_mut_eq_up_to_tag`
  (4 uses: `ptr_mut_ref_join` and the three `cast_mut_ref*_to_ptr`),
  and `const_ptr_eq_up_to_tag` (`*const`) to `ptr_eq_up_to_tag`, still defined through the `*mut` one.
  This follows `ptr_null` / `ptr_null_mut` and `ptr_from_data` / `ptr_mut_from_data` (plain is `*const`, `_mut` is `*mut`).
- **Rename `SeqPointsTo::from_raw_parts`** (`*mut [T]`, no `wf_basic()`) to `from_seq`,
  and the existing `from_seq` (thin `*mut T`, ensures `wf_basic()`) to `from_seq_pt`
  (5 uses of `from_raw_parts` in `points_to_ops.rs`, besides `from_seq`'s own body;
  `from_seq` is used by `empty` and 4 times in `points_to_collections.rs`, not in rustlib).
  `TYPED_POINTS_TO_APPROVED.md` and `POINTS_TO_MIGRATION.md` mention the current `from_seq`.
- **Consistent names in `points_to_structs.rs`:** the field primitives use `raw_parts`
  (`into_raw_parts`, `from_raw_parts`, `from_raw_parts_ref`, `as_raw_parts_mut`, and `PointsToUnaligned::from_raw_parts_mut`),
  except the axiom `PointsTo::from_unaligned_mut`, which is the `&mut` counterpart of `PointsTo::from_raw_parts_ref`.
  Rename it to `PointsTo::from_raw_parts_mut` (1 use, in `as_aligned_mut` in `points_to_ops.rs`;
  also in `TRUSTED_REVIEW.md`, `TYPED_POINTS_TO_APPROVED.md`, and item 4 under "For review").
- **Merge duplicate inherent impls in `points_to_ops.rs`** (no spec changes):
  the spec-only blocks moved from `points_to_model.rs` repeat the headers of later proof blocks.
  Merge each pair into one block: `impl<T: ?Sized> PointsToUnaligned<T>` (`bytes`, `is_valid`, `is_empty` / `lemma_eq_from_raw_parts`),
  `impl<T> PointsToUnaligned<T>` (`value` / `is_disjoint_unaligned`),
  `impl<T> PointsTo<T>` (`value` / `is_aligned`, `is_disjoint_pointsto`, `lemma_pt_parts_wf`, `borrow_mut`),
  `impl<T> PointsTo<[T]>` (`value` / `len`, `borrow_index`, `subrange`, ...).
  `PointsToUnaligned<[T]>` already has `value` with `len` and `borrow_index`.
- **Stale doc link** in `shared_reference.rs` (on `ptr_ref2_untyped_with_typed_value`):
  it links to `ptr_ref_untyped_with_typed_value`, which no longer exists.

## Later

- **Remove `SharedReference`** and its trusted items once the `str` ↔ `[u8]` reference transmutes
  (`str::as_bytes`, `from_utf8_unchecked`) no longer need it; a collaborator is working on those.
- **Merge `mut_ref_from_parts` and `mut_ref_from_parts_slice`** into one axiom over `T: ?Sized`
  (bound `PointsToUnaligned<T>: PTValueOps<A = T>`), with the `value_ref()` ensures they already share
  and a generic `pt_parts_wf` (the requires of `PTValueOps::from_untyped_with_typed_value`).
  `str` would also get the generic axiom, so its final wf would be under `additional_validity_constraints(&*final(val), metadata)`
  (`inv()` for `str`, as `mut_ref_from_parts_str` has now).
  Blocked: for slices, that antecedent needs `final(val)@.len() == ptr@.metadata`,
  and Verus doesn't yet know that a `&mut [T]`'s final length equals its current length
  (Rust guarantees it; see the TODO in `std_specs/option.rs`).
  The same generic `pt_parts_wf` would also merge `ref_from_parts` / `ref_to_parts` with their `_slice` versions.
- **Shadow-data extensions to Verus**, optional, if the current restrictions get in the way:
  precise shadow data through `&*x` reborrows, and shadow-data projections for tuple and struct fields.
  The restrictions the design works around:
  a caller relating two calls through `shadow_data(x)` needs `#[verifier::shadow_data]` itself;
  the attribute goes on trait methods only, and drops their `call_requires` / `call_ensures` axioms;
  reborrows, `&mut` → `&` coercions, tuple destructuring and struct fields give fresh shadow data
  (`mut_ref_as_shr_ref` covers `&mut` → `&`; exec conversions between reference types such as `str::as_bytes`
  need shadow-data ensures wherever a pointer has to flow across them).

## Proposal: rustlib's verified APIs over `Tracked<&T>`

This proposes moving rustlib's verified functions that still take a shared `&PointsTo` to `Tracked<&T>`.
These are spec changes to verified functions; no new trusted items.

Not changed:
the verified wrappers `ptr_ref`, `ptr_ref_slice`, `ptr_ref_str`;
`ptr_ref2*` (go with `SharedReference`);
`CopyPointsTo::new` (`specs/ptr.rs`), which stores the borrow in a struct field, where shadow data isn't tracked.

**Callers.** A caller that relates a pointer to `shadow_data(r)` needs `#[verifier::shadow_data]` itself.
For trait methods the attribute goes on the trait declaration, and every impl gets it.
This works for an `external_trait_specification` too (tested: `#[verifier::shadow_data]` on an `ExSliceIndex`-style method
makes its impls shadow-data functions; without it, the impl's precondition fails).
Shadow-data functions lose their `call_requires` / `call_ensures` axioms; nothing in rustlib uses them for these methods.

### `SliceIndexVerus` (`core/src/slice/index.rs:443`) and its 21 impls

`perm: &PointsTo<T>` becomes `r: &T` (`T` is `[U]` or `str`), with `#[verifier::shadow_data]` on the three trait methods:

```rust
#[verifier::shadow_data]
fn output_ptr_ref<'a>(
    ptr: *const <Self as SliceIndex<T>>::Output,
    Tracked(r): Tracked<&'a T>,
    Ghost(ghost_self): Ghost<&Self>,
    Ghost(orig_ptr): Ghost<*const T>,
) -> (out: &'a <Self as SliceIndex<T>>::Output)
    requires
        shared_ref_ptr(shadow_data(r)) == orig_ptr,
        valid_indices(ghost_self.spec_start(slice_len(orig_ptr)), ghost_self.spec_end(slice_len(orig_ptr)), r),
        ptr == ptr_from_data(get_unchecked_result::<T, <Self as SliceIndex<T>>::Output>(
            orig_ptr, ghost_self.spec_start(slice_len(orig_ptr)), ghost_self.spec_end(slice_len(orig_ptr)), item_size::<T>(),
        )),
    ensures
        index_result(ghost_self.spec_start(slice_len(orig_ptr)), ghost_self.spec_end(slice_len(orig_ptr)), r, out),
;

#[verifier::shadow_data]
unsafe fn get_unchecked_verus(self, slice: *const T, Tracked(r): Tracked<&T>) -> (out: *const <Self as SliceIndex<T>>::Output)
    requires
        shared_ref_ptr(shadow_data(r)) == slice,
        valid_indices(self.spec_start(slice_len(slice)), self.spec_end(slice_len(slice)), r),
    returns
        // unchanged
;

// get_unchecked_mut_verus: the same, with `slice: *mut T` and `shared_ref_ptr(shadow_data(r)) == slice as *const T`.
```

- **`perm_wf(perm)` goes:** a reference is always valid.
- **`forall|v| perm_value_eq(perm, v) ==> index_result(.., v, out)` becomes `index_result(.., r, out)`.**
- **Bodies:** `ref_to_parts*` on `r` (a proof call; no exec code added), then the existing proofs
  (`borrow_index` / `subrange`, then `as_aligned` and `ref_from_parts*`, then `ptr_shr_ref`; `ptr_bounds` and `as_untyped()` for `get_unchecked*`).
- **Callers:** `<[T]>::get_unchecked_verus` / `get_unchecked_mut_verus` and `str::get_unchecked` / `get_unchecked_mut` get the attribute
  and pass `Tracked(self)` with `self.as_slice_ptr()` / `as_str_ptr()`;
  the `_mut` callers pass `Tracked(mut_ref_as_shr_ref(&slice))` in place of `mut_ref_to_shr_points_to*`.
- **Trusted code removed:** the 8 definitional axioms in `specs/slice_index.rs` that exist only for `&PointsTo`:
  `def_perm_ptr_*`, `def_perm_wf_*`, `def_perm_value_eq_*` (`[T]` and `str`), `def_valid_indices_slice_points_to`, `def_valid_indices_str_points_to`,
  with the `uninterp` `perm_ptr` / `perm_wf` / `perm_value_eq` and the `valid_indices_*_points_to` spec fns.
  `valid_indices` on `&[T]` / `&str` already has its definitions.

### `from_raw_parts_verus` (`core/src/slice/raw.rs:160`)

```rust
#[verifier::shadow_data]
pub const unsafe fn from_raw_parts_verus<'a, T>(data: *const T, len: usize, Tracked(r): Tracked<&'a [T]>) -> (out: &'a [T])
    requires
        shared_ref_ptr(shadow_data(r)) == ptr_from_data(PtrData::<[T]> { addr: data@.addr, provenance: data@.provenance, metadata: len }),
    ensures
        out@ == r@,
```

- The body builds the slice pointer from `data` and `len`, then calls `ptr_shr_ref`; no `ref_to_parts` needed.
- The safety conditions (1a)–(1c) (non-null, in bounds, aligned) follow from `r` being a reference at that pointer,
  so the requires don't need them; they can stay as comments.
- **Caller:** `str::split_at_unchecked` gets the attribute, and gets its two `&[u8]` halves with `ref_from_parts_slice`
  on the parts of `perm.subrange(0, mid)` / `perm.subrange(mid, len)`.

### `read_copy_verus` (`core/src/ptr/mod.rs:1893`)

```rust
#[verifier::shadow_data]
pub const unsafe fn read_copy_verus<T: Copy>(src: *const T, Tracked(r): Tracked<&T>) -> (out: T)
    requires
        shared_ref_ptr(shadow_data(r)) == src,
    ensures
        out == *r,
```

- The body gets the parts with `ref_to_parts` on `r` (a proof call), then runs the current proof (`bytes_decode`, `is_aligned`, `as_untyped()` for `read_via_copy_verus`).
- No callers in verified code.

### `get_offset_len_noubcheck_verus` / `get_offset_len_mut_noubcheck_verus` (`core/src/slice/index.rs:147, 218`)

```rust
#[verifier::shadow_data]
const unsafe fn get_offset_len_noubcheck_verus<T>(ptr: *const [T], offset: usize, len: usize, Tracked(r): Tracked<&[T]>) -> *const [T]
    requires
        shared_ref_ptr(shadow_data(r)) == ptr,
        offset <= r@.len(),
    returns
        // unchanged
;
// _mut_: the same, with `ptr: *mut [T]` and `shared_ref_ptr(shadow_data(r)) == ptr as *const [T]`.
```

- The body gets the parts with `ref_to_parts_slice` on `r` (a proof call) for `ptr_bounds`, `provenance_not_none`, `is_nonnull` and `as_untyped()`.
- **Callers:** the `get_unchecked*_verus` impls above (already shadow-data functions under `SliceIndexVerus`),
  and the `get` / `get_mut` / `index` / `index_mut` impls of core's `SliceIndex` for `Range` / `RangeFrom`
  (`index.rs:985, 1011, 1088, 1113, 1435, 1456`).
  Those need the attribute on `ExSliceIndex`'s `get_mut` and `index_mut` too (`get` and `index` have it),
  which makes every core `SliceIndex` impl of those methods a shadow-data function
  (`[T]` and `str`, including `IndexRange`, `RangeInclusive`, the `Bound` pairs, ...).
- This is possible (tested, above); the cost is the attribute on core trait methods and their impls,
  for two private helpers. Alternatively, keep them taking `&PointsTo`, with their callers building it with `ref_to_parts_slice`.

**Suggested:** `SliceIndexVerus`, `from_raw_parts_verus` and `read_copy_verus`;
`get_offset_len_*` either way.

## On hold: verifying `read_unaligned` and `MaybeUninit`

**On hold (2026-11-02), to come back to after the rest is implemented.**
Until then, `read_unaligned_verus` stays as it is now:
trusted (`external_body`), taking a `PointsToUnalignedArg`, so it is the one remaining trusted spec over `PointsToUnaligned`.
`MaybeUninit`, `CopyPointsToUnaligned` and vstd's `std_specs/maybe_uninit.rs` are unchanged.

To check when this resumes:
whether Verus accepts an exec union field read under an `is_variant` precondition (`assume_init_verus`),
and whether anything else depends on `CopyPointsToUnaligned`'s layout.

**`read_unaligned`** (`core/src/ptr/mod.rs`): verified, following Rust's own body.

```rust
let mut tmp = MaybeUninit::<T>::uninit();
copy_nonoverlapping(src as *const u8, tmp.as_mut_ptr() as *mut u8, size_of::<T>());
tmp.assume_init()
```

`read_unaligned_verus` keeps its name and spec (taking a `PointsToUnalignedArg`) and loses `external_body`.
Its body is the above, with `copy_nonoverlapping_verus` (trusted, over `PointsToUntyped`, already exists)
and rustlib's own `MaybeUninit`, verified (below).

**`MaybeUninit`** (`core/src/mem/maybe_uninit.rs`): verified, only what `read_unaligned` reaches.

- **The union** moves into `verus!` as is (Verus supports unions, modelled with `is_variant` / `get_union_field`):
  ```rust
  pub union MaybeUninit<T> {
      uninit: (),
      value: ManuallyDrop<T>,
  }
  ```
  vstd's axiomatized `std_specs/maybe_uninit.rs` (`mem_contents`, and `assume_specification`s for `new`, `uninit`, `assume_init`, ...)
  is left out of the rustlib build (`#[cfg(not(verus_verify_core))]`); nothing in rustlib uses it.
- **`uninit`**: verified with its current body (`MaybeUninit { uninit: () }`).
  ```rust
  pub const fn uninit() -> (res: MaybeUninit<T>)
      ensures
          is_variant(res, "uninit"),
  ```
- **`as_mut_ptr_verus`** (new, trusted): `as_mut_ptr`'s body (`self as *mut _ as *mut T`), with the parts of a permission for `self`'s memory.
  This is the one new trusted function: it ties the bytes written through the pointer to the union's typed value.
  ```rust
  /// Returns a pointer to the contained value,
  /// with the parts of a permission for its memory.
  /// If the final parts are well-formed for the same pointer and valid,
  /// `self` finally holds the final value.
  #[verifier::external_body]
  pub const fn as_mut_ptr_verus(&mut self) -> ((ptr, pt_untyped, typed_value): (
      *mut T,
      Tracked<&mut PointsToUntyped>,
      Tracked<&mut TypedValue<T>>,
  ))
      ensures
          pt_parts_wf(ptr@, *pt_untyped@, *typed_value@),
          is_variant(*old(self), "value") ==> {
              &&& typed_value@.is_valid()
              &&& typed_value@.value() == get_union_field::<_, ManuallyDrop<T>>(*old(self), "value")@
          },
          !is_variant(*old(self), "value") ==> typed_value@.is_empty(),
          final(pt_untyped@).ptr() == pt_untyped@.ptr()
              && pt_parts_wf(ptr@, *final(pt_untyped@), *final(typed_value@))
              && final(typed_value@).is_valid() ==> {
              &&& is_variant(*final(self), "value")
              &&& get_union_field::<_, ManuallyDrop<T>>(*final(self), "value")@ == final(typed_value@).value()
          },
  ```
- **`assume_init_verus`** (new, verified):
  ```rust
  pub const unsafe fn assume_init_verus(self) -> (out: T)
      requires
          is_variant(self, "value"),
      ensures
          out == get_union_field::<_, ManuallyDrop<T>>(self, "value")@,
  {
      ManuallyDrop::into_inner(unsafe { self.value })
  }
  ```
  The original body reads `self.value` through a raw pointer (`(&raw const self.value).cast::<T>().read()`),
  which would need a permission for `self`'s own memory;
  reading the union field instead is equivalent (the original does it the raw way only for Miri's error messages).
  `ManuallyDrop::into_inner` uses vstd's existing `ManuallyDrop` specs.
  `intrinsics::assert_inhabited::<T>()` is left out: it only panics for an uninhabited `T`,
  and the precondition (a `value` variant, so a value of type `T` exists) rules that out.

The proof:
1. **Get the value.** `Move`: take the `TypedValue` out of the permission (`as_raw_parts_mut`), leaving `Empty`.
   `Copy`: a ghost copy of it (below).
2. **Borrow `tmp`'s memory** with `as_mut_ptr_verus`; it starts `Empty`, since `tmp` is `uninit`.
3. **Copy the bytes.** `copy_nonoverlapping_verus::<u8>` from the source's `PointsToUntyped` into `tmp`'s,
   so `tmp`'s bytes equal the source's, which decode to the value.
4. **Put the value** into `tmp`'s `TypedValue`, so the final parts are well-formed and valid,
   and `tmp` holds the value (variant `value`) once the borrow ends.
5. **`assume_init_verus`** returns it.

**`CopyPointsToUnaligned`** (`specs/ptr.rs`) needs to give the `Copy` case an owned copy of the value,
since `read_unaligned_verus` has no `T: Copy` bound.
Its `new` (which has `T: Copy`) stores a ghost copy (`TypedValue::tracked_copy`),
and it gets two verified functions (spec of `new` unchanged):

| Function | Ensures |
|---|---|
| `tracked_pt_untyped(tracked &self) -> &PointsToUntyped` | `*out == ` the permission's `pt_untyped()` |
| `into_typed_value(tracked self) -> TypedValue<T>` | `out == self.typed_value()` |

`pt_unaligned_parts_wf` then has no trusted users of its own; it's only part of `pt_parts_wf`'s definition.
