# Design: no trusted specs over `PointsTo` / `PointsToUnaligned`

Goal: `PointsTo` and `PointsToUnaligned` are verified code.
No trusted item in vstd or rustlib depends on their `wf`, alignment, decoding or trait impls.
Each trusted function that takes or gives a `PointsTo` today is restated over a `PointsToUntyped` and a `TypedValue`,
and the current `PointsTo` version is kept, under the same name, as a verified wrapper.
Users keep calling the `PointsTo` versions.

## Approved

The `is_disjoint` change, the structural axioms, the well-formed parts spec fns,
the trusted permission functions (vstd and rustlib's `proofs/str.rs`), the field-access primitives and the module layout
are approved and in [TRUSTED_POINTS_TO_APPROVED.md](TRUSTED_POINTS_TO_APPROVED.md).

## Names

Provisional, to revisit during review:
the trusted versions are `*_untyped_with_typed_value` (the convention for `wf`'d constructors and destructors),
and the spec fns are `pt_unaligned_parts_wf` / `pt_parts_wf` / `pt_parts_wf_slice` / `pt_parts_wf_str`.

## rustlib

The other trusted items in rustlib that use `PointsTo` / `PointsToUnaligned`.

| Item | Kind | Change |
|---|---|---|
| `alloc/src/boxed.rs`: `Box::from_raw_in_verus` | exec | takes `PointsToUntyped` + `TypedValue<T>` with `pt_parts_wf` |
| `alloc/src/boxed.rs`: `Box::into_non_null_with_allocator_verus` | exec | returns them |
| `core/src/slice/mod.rs`: `<[T]>::as_slice_ptr_verus` | exec | returns `Tracked<&PointsToUntyped>` and `Tracked<&TypedValue<[T]>>` |
| `core/src/str/mod.rs`: `str::as_str_ptr_verus` | exec | same, for `str` |
| `core/src/ptr/mod.rs`: `ptr::read_unaligned_verus` | exec | on hold: unchanged for now; later verified, with rustlib's `MaybeUninit` (see [below](#on-hold-verifying-read_unaligned-and-maybeuninit)) |
| `specs/slice_index.rs`: 8 axioms | definitional axioms | kept (decided 2026-11-02) |

- **The verified wrappers** for `Box`, `as_slice_ptr_verus` and `as_str_ptr_verus`
  keep their current names and specs, so callers don't change.
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

### New trusted specs

The `Box` and cast specs are approved and in [TRUSTED_POINTS_TO_APPROVED.md](TRUSTED_POINTS_TO_APPROVED.md#rustlib-box-and-casts-approved-2026-11-02).
Attributes (`#[verifier::external_body]`, `const`, ...) and bodies are the current ones.

### On hold: verifying `read_unaligned` and `MaybeUninit`

**On hold (2026-11-02), to come back to after the rest of this plan is implemented.**
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

`pt_unaligned_parts_wf` (approved) then has no trusted users of its own; it's only part of `pt_parts_wf`'s definition.
