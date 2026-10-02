# Migrating from `raw_ptr.rs` permissions to `points_to_permissions.rs`

Reference for updating code that used the `PointsTo` / `PointsToUnaligned` / `SeqPointsTo` /
`MemContents` API from `raw_ptr.rs`. It describes the API as of this branch
(`verify-rustlib-refactor`); the port is not finished (see
[What is not available yet](#what-is-not-available-yet)), and
[PORTING_STATUS.md](PORTING_STATUS.md) tracks progress.

Everything below was written by comparing the signatures in `raw_ptr.rs` against
`points_to_permissions.rs` and `points_to.rs`. The new file verifies in vstd.

## 1. Where things live

| What | Old | New |
|---|---|---|
| `PointsTo<T>`, `PointsToUnaligned<T>`, `SeqPointsTo<T, P>`, `PointsToUntyped`, `TypedValue<T>`, `ptr_addr_in_bounds` | `vstd::raw_ptr` | `vstd::points_to_permissions` |
| Traits `PointsToPhys`, `PointsToProperties`, `FixedSize`; `PointsToSingleton` | (did not exist) | `vstd::points_to` |
| Pointer/provenance model (`PtrData`, `Provenance`, `ptr_mut_from_data`, `mut_ref_ptr`, ...) | `vstd::raw_ptr` | unchanged, still `vstd::raw_ptr` |

`ptr()` and `size()` on the new types are **trait methods** (`PointsToPhys`), and `wf_basic` and
the `is_nonnull` / `ptr_bounds` / `provenance_not_none` / `is_disjoint` lemmas come from
`PointsToProperties`. Bring the traits into scope (`use vstd::points_to::*;`) or calls like
`perm.ptr()` will not resolve.

The new and old types have the same names, so a file that imports both modules with a glob will
get ambiguity errors. Import one or the other (or qualify).

## 2. Representation: from opaque to concrete

Old: `PointsToUnaligned<T>` was an `external_body` struct, and `PointsTo<T>` was a thin wrapper
around it. All facts about contents came from axioms.

New: the permissions are ordinary tracked structs built on top of each other:

```
PointsTo<T>            { pt_unaligned: PointsToUnaligned<T> }          // + aligned to T
PointsToUnaligned<T>   { val: TypedValue<T>, pt_untyped: PointsToUntyped }
PointsToUntyped        = SeqPointsTo<[u8], PointsToSingleton>
PointsToSingleton      // external_body: the single remaining primitive (one byte)
TypedValue<T>          = Empty | Valid(Box<T>)
```

Consequences:

* A valid permission holds a real `Box<T>`; an empty one holds nothing. Most operations that
  were axioms (`take`, `put`, `borrow`, `from_untyped`, `into_untyped`, `as_untyped`,
  `as_untyped_mut`) are now proved by manipulating these fields.
* `SeqPointsTo` has **two** type parameters now: `SeqPointsTo<T, PointsToPerm>`. The old
  one-parameter `SeqPointsTo<T>` corresponds to `SeqPointsTo<T, PointsTo<T>>`.
* The raw/untyped byte permission is `PointsToUntyped`. It replaces the uses of
  `PointsToUnaligned<[u8]>` (and `PointsTo<[u8]>` where it was used as "the untyped view").

## 3. The biggest behavioral change: explicit `wf()` instead of a type invariant

Old permissions carried an implicit invariant (`#[verifier::type_invariant]`, used via
`use_type_invariant`), so e.g. `is_aligned` had no precondition.

New permissions have **no type invariant**. Well-formedness is an explicit predicate:

* `PointsToUnaligned<T>::wf()`: bytes length is `size_of::<T>()`, valid value decodes from the
  bytes, and the underlying `PointsToUntyped` is `wf()`.
* `PointsTo<T>::wf()`: the above plus the address is aligned to `T`.
* `SeqPointsTo<T, P>::wf()`: see [section 6](#6-seqpointsto).

Practical rules when migrating:

1. Functions that used the invariant now `requires self.wf()` (e.g. `is_aligned`,
   `bytes_decode`, `cast_to_untyped`, `into_untyped`, `as_untyped`, `borrow`, `take`, `put`,
   `is_disjoint_*`).
2. Constructors and mutators `ensure` `wf()` where they can: `from_untyped`, `zero_sized`,
   `take`, `put`, `into_unaligned`, `as_unaligned`, `into_aligned`, `as_aligned`.
3. Mutators that hand out `&mut` to a sub-part (`as_untyped_mut`, `borrow_mut`, the `SeqPointsTo`
   `&mut` accessors) ensure `final(self).wf()` only *conditionally*, on the part still having the
   same pointers/length (and, for typed values, still decoding). You must establish that
   condition on the `final(...)` of the borrowed part to get `wf()` back on the parent.
4. In practice you carry `perm.wf()` through your own specs/invariants the way you previously
   relied on the type invariant. Constructing a `wf` permission then flows from the functions in
   [section 5](#5-function-by-function-pointsto-and-pointstounaligned).

## 4. Renames

### Types and variants

| Old | New |
|---|---|
| `MemContents<T>` | `TypedValue<T>` |
| `MemContents::Init(T)` | `TypedValue::Valid(Box<T>)` |
| `MemContents::Uninit` | `TypedValue::Empty` |
| `PointsToUnaligned<[u8]>` (raw bytes) | `PointsToUntyped` |
| `SeqPointsTo<T>` | `SeqPointsTo<T, PointsTo<T>>` |
| `PointsToData { ptr, mem_contents, abstract_bytes }` | `PointsToData { ptr, value, bytes }` |

### Spec functions and lemmas

| Old | New |
|---|---|
| `mem_contents()` | `typed_value()` |
| `is_init()` / `is_uninit()` | `is_valid()` / `is_empty()` |
| `abstract_bytes()` | `bytes()` |
| `abstract_bytes_decode` | `bytes_decode` |
| `provenance_non_null` | `provenance_not_none` (trait method; requires `self.size() != 0`) |
| `value()`, `ptr()` | unchanged (`ptr()` is now a trait method) |

### `SeqPointsTo`

| Old | New |
|---|---|
| `seq_perm()` | `seq_pt()` |
| `mem_contents()` | `typed_value()` |
| `abstract_bytes()` / `abstract_bytes_inner` | `bytes()` / `bytes_inner` |
| `tracked_perm_seq` | `tracked_seq_pt` |
| `tracked_perm_seq_mut` | `tracked_seq_pt_mut` |
| `mem_contents_equiv` | `typed_value_equiv` |
| `abstract_bytes_len` / `abstract_bytes_equiv` / `abstract_bytes_decode` | `bytes_len` / `bytes_equiv` / `bytes_decode` |
| `provenance_non_null` | trait method `provenance_not_none` |
| `SeqPointsTo<u8>::cast_to_typed` | `PointsToUntyped::cast_to_seq_pt` |
| `constants` (broadcast) | no equivalent in the new file |

## 5. Function by function: `PointsTo` and `PointsToUnaligned`

"Proved" means it was an `axiom fn` in `raw_ptr.rs` and is a `proof fn` now.

### `PointsTo<T>`

| Function | Change |
|---|---|
| `zero_sized(ptr)` | Same idea. The inline provenance-bounds requirement is now `ptr_addr_in_bounds(ptr)`. Ensures `wf()`, `is_empty()`, `bytes().len() == size_of::<T>()`. |
| `is_nonnull`, `ptr_bounds`, `provenance_not_none` | Now `PointsToProperties` trait methods; require `wf_basic()`. `ptr_bounds` is stated with `self.size()`. |
| `is_aligned` | Requires `wf()` (no type invariant). |
| `is_disjoint<S>` | Now `is_disjoint_pointsto<S>`; additionally requires `self.wf()`. The generic trait method `is_disjoint` works against any `PointsToPhys`. |
| `into_unaligned`, `as_unaligned` | Require `wf()`, ensure `perm.wf()`, `perm@ == self@`. |
| `abstract_bytes_decode` | `bytes_decode`, requires `wf()`. |
| `cast_to_untyped` | Returns `(PointsToUntyped, Option<T>)` instead of `(PointsTo<[u8]>, Option<T>)`. Requires `wf()`. Ensures `dst.wf()` and `dst.len() == size_of::<T>()`; no `is_fully_uninit` (untyped has no validity). |
| `from_untyped` | Proved. Takes a `PointsToUntyped`; requires `wf()`, aligned address, `len() == size_of::<T>()` (was: metadata equals size). Ensures `out.wf()`, `out.is_empty()`, same bytes. |
| `into_untyped`, `as_untyped` | Proved. Require `wf()`. Return `PointsToUntyped` / `&PointsToUntyped`. |
| `as_untyped_mut` | Proved. Requires `old(self).wf()`. After the call `self`'s typed value is dropped; `final(self)` is empty and `wf()` provided the untyped part keeps its pointers/length (`PointsToUntyped::ptrs_len_same`). |
| `borrow` | Proved. Now also requires `wf()`. |
| `take`, `put` | Proved. Require `old(self).wf()`, ensure `final(self).wf()`. |
| `borrow_mut` | **Still an axiom** (it ties a real Rust reference to the raw pointer, which cannot be done from a ghost `Box<T>`). Now requires `old(self).wf()`; ensures `ptrs_len_same_valid_decode(old, final) ==> final.wf()`. |

### `PointsToUnaligned<T>`

| Function | Change |
|---|---|
| `is_nonnull`, `ptr_bounds`, `provenance_not_none`, `is_disjoint` | `PointsToProperties` trait methods, delegating to the underlying `PointsToUntyped`. `is_disjoint_unaligned<S>` is the specialized form. |
| `into_aligned` | Now requires `wf()` and aligned address; ensures `perm.wf()`. |
| `as_aligned` | Still an axiom; requires `wf()` and aligned address, ensures `perm.wf()`. |
| `zero_sized` | Now defined on `PointsToUnaligned<T>` (generic in `T`); the old one was `PointsToUnaligned<[u8]>::zero_sized<T>`. Ensures `wf()`. The untyped equivalent is `PointsToUntyped::zero_sized<T>`. |

Accessors that expose inner permissions: `tracked_pt_unaligned` (on `PointsTo`) and
`tracked_pt_untyped` (on `PointsToUnaligned`). They have no `wf()` clauses because they live in
`?Sized` impl blocks where `wf` is not defined. For sized `T`, `self.wf()` implies the inner
permission's `wf()`.

## 6. `SeqPointsTo`

The old `SeqPointsTo<T>` wrapped a `Seq<PointsTo<T>>` and a pointer. The new
`SeqPointsTo<T, PointsToPerm>` is generic over the element permission, which is how
`PointsToUntyped` (elements are `PointsToSingleton`) and the typed sequence
(`SeqPointsTo<T, PointsTo<T>>`) share one definition.

### `wf()` is different (weaker in some places, with derived consequences)

Old `wf()` directly demanded: per-element provenance and address offset; provenance `Some` for
non-empty, non-zero-size sequences; the whole range `addr + len * size` within the provenance;
non-null; aligned.

New `wf()` demands: per-element provenance, address offset and **element `wf_basic`**; non-null;
base address within the provenance bounds (`start <= addr <= start + alloc_len`); aligned
(for `SeqPointsTo<T, PointsTo<T>>`; for `PointsToUntyped`, also `ptr()@.metadata == len()`).

The "provenance is `Some`" and "whole range in bounds" facts are no longer part of `wf()`; they
are **derived** by the trait lemmas `provenance_not_none` and `ptr_bounds`. If your code used
those facts straight from `wf()`, call the lemmas.

### Functions

| Function | Notes |
|---|---|
| `from_seq(r, ptr)` | Requires each `r[i].wf()`, the per-element pointer/provenance conditions, non-null, aligned, and `ptr_addr_in_bounds(ptr)` (replaces the old larger bounds condition). Ensures `wf()`. |
| `into_seq` | Requires `wf()`; ensures every element is `wf()`. |
| `tracked_seq_pt` (was `tracked_perm_seq`), `tracked_seq_pt_mut` (was `tracked_perm_seq_mut`), `index_mut(i)` (was `borrow_mut(i)`) | As before, renamed; `&mut` accessors give `final.wf()` conditionally (same `ptrs_len_same_valid_decode` criterion). |
| `is_init_subrange`, `value_subrange` | `is_valid_subrange`, `value_subrange`. |
| `put_subrange`, `put_mem_contents_subrange`, `take_mem_contents_subrange`, `copy_mem_contents_subrange` | `put_subrange`, `put_typed_value_subrange`, `take_typed_value_subrange`, `copy_typed_value_subrange`. Proved; all require `old(self).wf()` and ensure `final(self).wf()`. Replacement sequences are `Seq<TypedValue<T>>` rather than `Seq<MemContents<T>>`. |
| `borrow_mem_contents_subrange` | `borrow_typed_value_subrange` (axiom; requires `wf()`). |
| `PointsTo<[T]>::subrange` (shared borrow) | `subrange(start_index, len) -> &Self` (axiom; requires `wf()`). |
| `PointsTo<[T]>::into_untyped`, `from_untyped(raw, len)` | `into_untyped` (proved; drops any typed values) and `from_untyped(pt_untyped, len)` (proved; requires `wf()`, alignment, `len() == len * size_of::<T>()`; ensures an all-empty, `wf()` permission). Use `PointsToUntyped::cast_to_seq_pt` to supply typed values. |
| `PointsTo<[T]>::as_untyped_mut` | `as_untyped_mut` on `SeqPointsTo<T, PointsTo<T>>` (axiom). |
| `PointsTo<[T]>::cast_points_to`, `cast_points_to_unaligned` | Not available yet; planned as an `impl` on `PointsTo<[T]>`. Keep using the old API for now. |
| `PointsTo<[u8]>::cast_to_typed` | `PointsToUntyped::cast_to_typed` (proved; requires `wf()`, `len() == size_of::<T>()`, alignment, decodability). |
| `empty(ptr)`, `zero_sized(ptr, length)` | Same idea; ensure `wf()`. |
| `split(mid)`, `join(other)` | Same contracts. Also available on `PointsToUntyped` (the untyped `split`/`join` handle the slice-pointer metadata, `metadata == len`). |
| `cast_to_untyped` | Returns a `PointsToUntyped` (plus the `Seq<Option<T>>` of typed values). Proved. The pointer is fully specified: same address/provenance, metadata `len * size_of::<T>()`. |
| `as_untyped` | Axiom returning `&PointsToUntyped` (the new `SeqPointsTo<T, PointsTo<T>>` does not store one to borrow). Requires `wf()`. |
| `subrange_mut(i, j)` | Axiom, same shape as before; `final(self).wf()` conditional on the sub-permission staying `wf()` with the same pointer and length. |
| `PointsToUntyped::cast_to_seq_pt(capacity, typed_value)` | Replaces `SeqPointsTo<u8>::cast_to_typed`. Requires `wf()`, alignment, `len == capacity * size_of::<T>()`, and decodability of each `Some`. |
| `is_disjoint_seqpt<S>` | Specialization of the trait `is_disjoint` (requires `wf()` and non-empty/non-ZST). |

## 7. What is not available yet

The new model only covers sized `T` so far. These still exist **only** in `raw_ptr.rs`, so code
using them must keep using the old API for now:

* `PointsTo<[T]>`, `PointsToUnaligned<[T]>`, `PointsTo<[u8]>` as types. Most of their *methods* now
  exist on `SeqPointsTo<T, PointsTo<T>>` (see the tables above). The ones that do not yet are
  `tracked_borrow` / `tracked_borrow_mut` (real `&[T]` / `&mut [T]`) and the unaligned slice
  methods (`PointsToUnaligned<[T]>`: `as_aligned_mut`, ...), which are on hold until needed.
* `PointsTo<str>` and the `[u8]` to `str` casts (`cast_to_str_shared`, `cast_to_u8_shared`, ...).
  These are planned as a `SeqPointsTo<str, PointsTo<u8>>` impl; a verified draft exists but is
  currently out of the build (see [PORTING_STATUS.md](PORTING_STATUS.md)), so keep using the old
  `PointsTo<str>` for now.
* `seq_into_slice`, `seq_into_slice_shared`, `seq_into_slice_mut`.
* Everything built on the old permissions: `SharedReference::points_to`,
  `mut_ref_to_shr_points_to*`, `ptr_ref2*`, `tracked_mut_ref_slice_*`.
* `Dealloc` is not part of the new model's scope and stays as defined in `raw_ptr.rs`.

The plan is for the slice and `str` permissions to become `SeqPointsTo` impls rather than separate
types. [PORTING_STATUS.md](PORTING_STATUS.md) lists which old functions have no equivalent yet.
Because the two models use the same type names, mixing them in one function is not currently
supported; convert at module boundaries.

## 8. Migration checklist

1. Switch imports to `points_to_permissions` / `points_to`, and bring the traits into scope.
2. Rename per [section 4](#4-renames) (`is_init` → `is_valid`, `mem_contents` → `typed_value`,
   `abstract_bytes` → `bytes`, `MemContents` → `TypedValue`, ...).
3. Replace uses of `PointsToUnaligned<[u8]>` / `PointsTo<[u8]>` as raw bytes with
   `PointsToUntyped`; update `cast_to_untyped` / `from_untyped` call sites and their `ensures`
   (metadata-equals-size becomes `len() == size_of::<T>()`).
4. Add `wf()` to your specs and invariants where you previously relied on the type invariant, and
   discharge the conditional `final(...).wf()` guarantees after `&mut` borrows.
5. Where you used `wf()`-derived facts of `SeqPointsTo` (provenance `Some`, whole-range bound), call
   `provenance_not_none` / `ptr_bounds`.
6. Leave slice/`str` permission code on `raw_ptr.rs` until it is ported.
