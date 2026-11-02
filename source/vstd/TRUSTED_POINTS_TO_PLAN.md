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
| `core/src/ptr/mod.rs`: `ptr::read_unaligned_verus` | exec | takes the parts; `Move` takes `&mut` parts and ensures `final(typed_value) == Empty` |
| `specs/slice_index.rs`: 8 axioms | definitional axioms | kept (decided 2026-11-02) |

- **The verified wrappers** for `Box`, `as_slice_ptr_verus`, `as_str_ptr_verus` and `read_unaligned_verus`
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

Attributes (`#[verifier::external_body]`, `#[verifier::shadow_data]`, `const`, `no_unwind`, ...) and bodies are the current ones.

**`Box`** (`alloc/src/boxed.rs`):

```rust
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

**Casts from `&self`** (`core/src/slice/mod.rs`, `core/src/str/mod.rs`):

```rust
// impl<T> [T]
pub const fn as_slice_ptr_untyped_with_typed_value(&self) -> ((ptr, pt_untyped, typed_value): (
    *const [T],
    Tracked<&PointsToUntyped>,
    Tracked<&TypedValue<[T]>>,
))
    ensures
        ptr == shared_ref_ptr(shadow_data(self)),
        pt_parts_wf_slice(ptr@, *pt_untyped@, *typed_value@),
        typed_value@.is_valid(),
        typed_value@.value_ref() == self,

// impl str
pub const fn as_str_ptr_untyped_with_typed_value(&self) -> ((ptr, pt_untyped, typed_value): (
    *const str,
    Tracked<&PointsToUntyped>,
    Tracked<&TypedValue<str>>,
))
    requires
        self.inv(),
    ensures
        ptr == shared_ref_ptr(shadow_data(self)),
        pt_parts_wf_str(ptr@, *pt_untyped@, *typed_value@),
        typed_value@.is_valid(),
        typed_value@.value_ref() == self,
```

`perm@.ptr() == shared_ref_ptr(..)` and `perm@.wf()` become `pt_parts_wf_*(ptr@, ..)`, since `ptr` is that pointer.

**`read_unaligned`** (`core/src/ptr/mod.rs`).
Exec code can't branch on which variant a tracked argument is,
so this stays one function taking an argument enum, now over the parts (in `specs/ptr.rs`):

```rust
/// A borrowed, copyable view of a `TypedValue<T>`, provided that `T` is `Copy`.
pub tracked struct CopyTypedValue<'a, T> {
    tracked inner: &'a TypedValue<T>,
}

/// The parts of a `PointsToUnaligned<T>` permission for reading from memory,
/// covering both cases for whether this read copies or moves the underlying data.
pub tracked enum UntypedWithTypedValueArg<'a, T> {
    Copy(&'a PointsToUntyped, CopyTypedValue<'a, T>),
    Move(&'a mut PointsToUntyped, &'a mut TypedValue<T>),
}

pub const unsafe fn read_unaligned_untyped_with_typed_value<T>(
    src: *const T,
    Tracked(arg): Tracked<UntypedWithTypedValueArg<'_, T>>,
) -> (out: T)
    requires
        pt_unaligned_parts_wf(src@, arg.pt_untyped(), arg.typed_value()),
        arg.typed_value().is_valid(),
    ensures
        out == arg.typed_value().value(),
        match arg {
            UntypedWithTypedValueArg::Copy(..) => true,
            UntypedWithTypedValueArg::Move(pt_untyped, typed_value) => {
                &&& final(pt_untyped).wf()
                &&& final(pt_untyped).ptr() == pt_untyped.ptr()
                &&& *final(typed_value) == TypedValue::<T>::Empty
            },
        },
```

- **`CopyTypedValue`** is built only by verified constructors:
  `new(&'a TypedValue<T>)` with `T: Copy`,
  and `from_copy_points_to_unaligned(CopyPointsToUnaligned<'a, T>)` (in the same module, so it can reach `inner`) for any `T`,
  since a `CopyPointsToUnaligned` already shows `T: Copy`.
  The verified `read_unaligned_verus` uses the latter to convert its `PointsToUnalignedArg::Copy`,
  and `as_raw_parts_mut` to convert `Move`.
- **`arg.pt_untyped()` / `arg.typed_value()`** are open spec fns matching on the variant, like `PointsToUnalignedArg::ptr()` now.
- **`pt_unaligned_parts_wf`** (approved, in [TRUSTED_POINTS_TO_APPROVED.md](TRUSTED_POINTS_TO_APPROVED.md#well-formed-parts-approved-2026-11-02)):
  `pt_parts_wf` without the alignment condition, since the read is unaligned.
