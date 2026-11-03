# To do: trusted `PointsTo` refactor and `Tracked<&T>`

The trusted specs are in [TRUSTED_REVIEW.md](TRUSTED_REVIEW.md).

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

## For review (uncommitted, rustlib)

- **`SliceIndexVerus`** (its three methods and 21 impls) and **`get_offset_len_noubcheck_verus` / `get_offset_len_mut_noubcheck_verus`**
  (`slice/index.rs`) take a `Tracked(r): Tracked<&T>` in place of a `&PointsTo<T>`,
  with `shared_ref_ptr(shadow_data(r)) == <the pointer>` in place of the permission's `ptr`, `wf` and value requires.
  `output_ptr_ref`, `get_unchecked_verus` and `get_unchecked_mut_verus` also require `valid_slice(r)`
  (for `str`, `r.inv()`, which `ref_to_parts_str` needs; always true for `&[T]`).
- **`#[verifier::shadow_data]` on `ExSliceIndex::get_mut` and `index_mut`**,
  so every core `SliceIndex` impl of those methods is a shadow-data function
  (`str`'s `Range`, `RangeTo` and `RangeFrom` impls relate a pointer to `shadow_data(r)`).
- **`NonNull::as_mut_verus`** takes a `Tracked<&'a mut T>` in place of a `&'a mut PointsTo<T>`,
  and its bound is `T: MetaSized` (was `T: Sized`):
  ```rust
  pub const unsafe fn as_mut_verus<'a>(&mut self, Tracked(perm): Tracked<&'a mut T>) -> (v: &'a mut T)
      where T: MetaSized
      requires
          mut_ref_ptr(perm) == old(self)@,
      ensures
          old(self)@ == final(self)@,
          &*v == &*old(perm),
          &*final(v) == &*final(perm),
  ```

## Remaining `PointsTo` uses

**Trusted specs over `PointsTo` / `PointsToUnaligned`:**

- vstd's structural axioms (`points_to_structs.rs`):
  `PointsToUnaligned::from_raw_parts_ref` / `from_raw_parts_mut` and `PointsTo::from_raw_parts_mut`.
  They are field primitives of the structs, so they can't be stated over the parts.
- rustlib's `ptr::read_unaligned_verus` (`core/src/ptr/mod.rs`), over a `PointsToUnalignedArg`; on hold (below).

**Specs taking a `&mut PointsTo`:** none that could take a `Tracked<&mut T>`.
These change the value's validity, so they need the permission:

- `ptr::read_verus` and `NonNull::read_verus` move the value out, leaving the permission empty.
- `ptr::write_verus` writes to memory that may not hold a valid value.
- `PointsToUnalignedArg::Move` and `PointsToArg::Move` (`specs/ptr.rs`) move the value out.

vstd keeps `ptr_mut_ref` and `ptr_mut_ref_slice` for code outside rustlib.

**Specs taking or giving a shared `&PointsTo`:**

- `shr_ref_points_to`, `shr_ref_points_to_slice` (vstd) and `shr_ref_points_to_str` (rustlib) give a `&PointsTo` for a reference.
  About 25 rustlib proof bodies use them to reach the permission API (`subrange`, `borrow_index`, `as_big_*`, `ptr_bounds`, ...).
- `SharedReference`'s items, kept until it is removed:
  `ptr_ref2`, `ptr_ref2_ghost`, `ptr_ref2_slice_ghost` (vstd), `ptr_ref2_str_ghost` (rustlib),
  and `SharedReference<T>` / `<[T]>` / `<str>::points_to`.
- `CopyPointsTo`, `CopyPointsToUnaligned` and `PointsToArg` (`specs/ptr.rs`); on hold (below).
- vstd keeps `ptr_ref`, `ptr_ref_slice`, `mut_ref_to_shr_points_to` and `mut_ref_to_shr_points_to_slice` for code outside rustlib.

The permission types' own methods (`as_aligned`, `borrow_index`, `subrange`, `as_big_*`, `as_bytes`, `is_disjoint_*`, ...)
are left out of these lists.

## On hold: verifying `read_unaligned` and `MaybeUninit`

**On hold (2026-11-02), to come back to after the rest is implemented.**
Until then, `read_unaligned_verus` stays as it is now:
trusted (`external_body`), taking a `PointsToUnalignedArg`, so it is the one remaining trusted spec over `PointsToUnaligned`.
`MaybeUninit`, `CopyPointsToUnaligned` and vstd's `std_specs/maybe_uninit.rs` are unchanged.
So are their aligned counterparts in rustlib's `specs/ptr.rs`, `CopyPointsTo` and `PointsToArg`,
which still hold a `&PointsTo` (and, for `PointsToArg::Move`, a `&mut PointsTo`)
and have no users;
`CopyPointsTo::new` can't take a `Tracked<&T>` in their place,
since it stores the borrow in a struct field, where shadow data isn't tracked.

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
