# Migrating from `raw_ptr.rs`

Reference for updating code that used anything from `raw_ptr.rs`. This is not only about the
`PointsTo` / `PointsToUnaligned` / `SeqPointsTo` / `MemContents` permission structs. It also
covers the rest of `raw_ptr.rs`:

* **The raw pointer model:** `PtrData`, `Provenance` / `ProvenanceData`, `ptr_mut_from_data`, and
  the axioms about them. These now live in `raw_ptr_new.rs`, and `Dealloc` is folded into
  `ProvenanceData`.
* **The trusted specs** for exec pointer operations: pointer casts, `ptr_ref` / `ptr_mut_ref`,
  `ptr_mut_ref_join`, `SharedReference`, and so on. These now live in `raw_ptr_new.rs` and
  `shared_reference.rs`, stated against the new permissions.

It describes the API as of this branch (`verify-rustlib-refactor`). The port is not finished (see
[What is not available yet](#8-what-is-not-available-yet)), and
[PORTING_STATUS.md](PORTING_STATUS.md) tracks progress.

Everything below was written by comparing the signatures in `raw_ptr.rs` against
`points_to_permissions.rs`, `points_to.rs`, `raw_ptr_new.rs` and `shared_reference.rs`. The new
files verify in vstd.

## 1. Where things live

`vstd::raw_ptr` is no longer compiled into vstd (it is commented out in `vstd.rs`). Its contents
were split across three modules, so **replace each `use vstd::raw_ptr::*;` (or `use
crate::vstd::raw_ptr::...`) with imports of whichever of these modules the code actually needs**:

| What the import was for | New module |
|---|---|
| The permissions: `PointsTo<T>`, `PointsToUnaligned<T>`, `SeqPointsTo<T, P>`, `PointsToUntyped`, `TypedValue<T>` | `vstd::points_to_permissions`, together with `vstd::points_to` (see below) |
| The pointer/provenance model: `PtrData`, `Provenance`, `ProvenanceData`, `AllocId`, `ptr_addr_in_bounds`, `ptr_mut_from_data`, `ptr_from_data`, `ptr_null*`, the pointer casts (`cast_ptr_to_thin_ptr`, `cast_slice_ptr_to_slice_ptr`, ...), `group_raw_ptr_axioms` | `vstd::raw_ptr_new` |
| Exec/proof functions that turn pointers and permissions into references: `ptr_ref`, `ptr_mut_ref`, `ptr_mut_ref_join`, `mut_ref_to_shr_points_to`, `tracked_mut_ref_slice_subrange`/`_idx`, `cast_mut_ref_to_ptr` (and the slice/`str` versions) | `vstd::raw_ptr_new` |
| `SharedReference`, `ptr_ref2`, `ptr_ref2_ghost` | `vstd::shared_reference` |
| `Dealloc` / `DeallocData` | removed; folded into `ProvenanceData` (see [`Dealloc` → provenance](#dealloc--provenance)) |

`mut_ref_ptr` is a builtin and comes from the prelude, so it needs no `raw_ptr` import.

`vstd::points_to` holds the permission traits (`PointsToPhys`, `PointsToProperties`, `FixedSize`)
and `PointsToSingleton`. These are new and have no `raw_ptr` counterpart, so `points_to` never
replaces a `raw_ptr` import on its own. It is needed alongside `points_to_permissions` because
`ptr()` and `size()` on the new types are **trait methods** (`PointsToPhys`), and `wf_basic` and
the `is_nonnull` / `ptr_bounds` / `provenance_not_none` / `is_disjoint` lemmas come from
`PointsToProperties`. Without `use vstd::points_to::*;`, calls like `perm.ptr()` will not resolve.

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
* Typed slices are `SeqPointsTo<T, PointsTo<T>>`, not `PointsTo<[T]>`; see
  [section 7](#7-slices-use-seqpointstot-pointstot-instead-of-pointstot).

## 3. The biggest behavioral change: explicit `wf()` instead of a type invariant

Old permissions carried an implicit invariant (`#[verifier::type_invariant]`, used via
`use_type_invariant`), so e.g. `is_aligned` had no precondition.

New permissions have **no type invariant**. Well-formedness is an explicit predicate:

* `PointsToUnaligned<T>::wf()`: bytes length is `size_of::<T>()`, valid value decodes from the
  bytes, and the underlying `PointsToUntyped` is `wf()`.
* `PointsTo<T>::wf()`: the above plus the address is aligned to `T`.
* `SeqPointsTo<T, P>::wf()`: see [section 6](#6-seqpointsto).

Each type also has a predicate `ptrs_len_same_valid(old, new)` (a `PointsToProperties` trait
method): `new` keeps `old`'s pointers and length and, for typed values, still decodes. The inherent
`stays_wf(old, new)` lemma turns `old.wf()` plus that predicate into `new.wf()`.

Practical rules when migrating:

1. Functions that used the invariant now `requires self.wf()` (e.g. `is_aligned`,
   `bytes_decode`, `into_untyped_with_typed_value`, `into_untyped`, `as_untyped`, `borrow_value`,
   `take`, `put`, `is_disjoint_*`).
2. Constructors and mutators `ensure` `wf()` where they can: `from_untyped`, `zero_sized`,
   `take`, `put`, `copy`, the `*_typed_value` functions, `into_unaligned`, `as_unaligned`,
   `into_aligned`, `as_aligned`.
3. Functions that hand out `&mut` to a sub-part (`as_untyped_mut`, `SeqPointsTo::index_mut`,
   `tracked_seq_pt_mut`, `subrange_mut`) ensure `final(self).wf()` only *conditionally*, on the
   part still having the same pointers/length (and, for typed values, still decoding). In many
   cases Verus establishes that condition, and so `wf()` on the parent, automatically. When it
   doesn't, establish the condition on the `final(...)` of the borrowed part yourself (see rule 4).
4. To establish `ptrs_len_same_valid(old, new)` from outside the module, call
   `PointsTo::lemma_ptrs_len_same_valid(old, new)` (both `wf()`, same `ptr()`) or
   `SeqPointsTo::lemma_ptrs_len_same_valid(old, new)` (both `wf()`, same `ptr()` and `len()`). The
   predicate unfolds through closed specs, so it is not provable directly.
5. In practice you carry `perm.wf()` through your own specs/invariants the way you previously
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
| `PointsTo<[T]>` | `SeqPointsTo<T, PointsTo<T>>` (see [section 7](#7-slices-use-seqpointstot-pointstot-instead-of-pointstot)) |
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

The `TypedValue` naming convention: `value` means a guaranteed-valid `T`, and `typed_value` means a
possibly-empty `TypedValue<T>` (e.g. `borrow_value` vs `borrow_typed_value`).

### `SeqPointsTo`

| Old | New |
|---|---|
| `seq_perm()` | `seq_pt()` |
| `mem_contents()` | `seq_typed_value()` |
| `value()` | `seq_value()` |
| `abstract_bytes()` / `abstract_bytes_inner` | `bytes()` / `bytes_inner` |
| `tracked_perm_seq` | `tracked_seq_pt` |
| `tracked_perm_seq_mut` | `tracked_seq_pt_mut` |
| `borrow_mut(i)` | `index_mut(i)` |
| `mem_contents_equiv` | `typed_value_equiv` |
| `abstract_bytes_len` / `abstract_bytes_equiv` / `abstract_bytes_decode` | `bytes_len` / `bytes_equiv` / `bytes_decode` |
| `provenance_non_null` | trait method `provenance_not_none` |
| `SeqPointsTo<u8>::cast_to_typed` | `SeqPointsTo<T, PointsTo<T>>::from_untyped_with_typed_value` |
| `cast_to_untyped` | `into_untyped_with_typed_value` (returns `Seq<TypedValue<T>>` instead of `Seq<MemContents<T>>`) |
| `*_mem_contents_subrange` | `*_typed_value_subrange` |
| `constants` (broadcast) | no equivalent in the new file |

### `Seq` tracked borrows (`seq.rs`)

| Old | New |
|---|---|
| `tracked_mut_borrow(i)` | `tracked_borrow_mut(i)`. The old function was removed as a duplicate: it had the same spec, stated element by element instead of with `update`, so `final(self) == old(self).update(i, *final(ret))` gives the same facts. |
| `tracked_mut_borrow_subrange(i, j)` | `tracked_borrow_subrange_mut(i, j)` (renamed; same spec). It now sits next to the shared version, `tracked_borrow_subrange(i, j)`. |
| (new) | `tracked_split_borrow_mut(mid)`: splits a `&mut Seq` into two `&mut Seq`s at `mid`. |

### `Dealloc` → provenance

The `Dealloc` permission (and `DeallocData`) no longer exists: it was folded into the provenance
model in `raw_ptr_new.rs`. Its main purpose was `Dealloc::size`, the originally requested
allocation size, and `ProvenanceData` now records that as `orig_size()`. Everything else `Dealloc`
exposed was already derived from its provenance, so read these facts off the pointer's provenance
(`ptr@.provenance.unwrap()`, for an allocation with `Some` provenance):

| Old (`Dealloc`) | New (`ProvenanceData`) |
|---|---|
| `size()` / `@.size` | `orig_size()` |
| `addr()` | `start_addr()` |
| `align()` | `alignment()` |
| `provenance()` / `@.provenance` | the pointer's own `ptr@.provenance` |
| `in_bounds` (`size <= alloc_len`) | part of the `provenance_properties` broadcast axiom (`orig_size() <= alloc_len()`) |
| `empty()` (size 0, `Provenance::None`) | no permission needed; `None` provenance carries no allocation |
| `provenance_non_null` (size ≠ 0 ⟹ `Some` provenance) | not needed: `orig_size()` is only defined on a `Some` provenance's `ProvenanceData` |
| `is_disjoint` (two `Dealloc`s have disjoint allocations) | dropped: it was only a sanity check and has no callers |

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
| `cast_to_untyped` | Renamed to `into_untyped_with_typed_value`. Returns `(PointsToUntyped, TypedValue<T>)` instead of `(PointsTo<[u8]>, Option<T>)`, with `typed_value == self.typed_value()`. Requires `wf()`. Ensures `pt_untyped.wf()` and `pt_untyped.len() == size_of::<T>()`; no `is_fully_uninit` (untyped has no validity). |
| `from_untyped` | Proved. Takes a `PointsToUntyped`; requires `wf()`, aligned address, `len() == size_of::<T>()` (was: metadata equals size). Ensures `out.wf()`, `out.is_empty()`, same bytes. |
| `PointsTo<[u8]>::cast_to_typed` | `from_untyped_with_value(pt_untyped, value)` (proved from `from_untyped` + `put`; requires `wf()`, `len() == size_of::<T>()`, alignment, decodability). |
| `into_untyped`, `as_untyped` | Proved. Require `wf()`. Return `PointsToUntyped` / `&PointsToUntyped`. |
| `as_untyped_mut` | Proved. Requires `old(self).wf()`. Drops `self`'s typed value. Unconditionally, `final(self)` is empty, has the borrow's final bytes, and `final(self).ptr()` is the borrow's final pointer (cast to `*mut T`). `final(self).wf()` holds if the untyped part keeps its pointers/length (`PointsToUntyped::ptrs_len_same_valid`); then `lemma_ptrs_len_same_valid(old, final)` gives `PointsTo::ptrs_len_same_valid`. |
| `borrow` | Renamed to `borrow_value` (to parallel `borrow_typed_value`). Proved. Now also requires `wf()`. |
| `take`, `put` | Proved. Require `old(self).wf()`, ensure `final(self).wf()`. They no longer ensure `ptrs_len_same_valid(old, final)`; use the lemma (rule 4 in [section 3](#3-the-biggest-behavioral-change-explicit-wf-instead-of-a-type-invariant)) if you need it, e.g. after `index_mut`. |
| `borrow_mut` | **Not available for now** (commented out in `points_to_permissions.rs`). Code that called `borrow_mut` and then passed the resulting `&mut T` to `ptr_mut_ref_join(ptr, Tracked(r))` should instead call `ptr_mut_ref(ptr, Tracked(perm))` directly with the `&mut PointsTo<T>`. It requires `perm.ptr() == ptr` and `perm.is_valid()`, and ensures `final(perm)` keeps the pointer, stays valid, and holds `*final(v)`. In ghost code, use `take` and `put` instead. |
| (new) `copy` | `T: Copy`; puts a copy of `*val`. Proved from `put`. |
| (new) `borrow_typed_value`, `take_typed_value`, `put_typed_value`, `copy_typed_value` | `TypedValue<T>` versions of `borrow_value`/`take`/`put`/`copy`; they don't require validity. All proved. |
| (new) `stays_wf`, `lemma_ptrs_len_same_valid` | See [section 3](#3-the-biggest-behavioral-change-explicit-wf-instead-of-a-type-invariant). |

### `PointsToUnaligned<T>`

| Function | Change |
|---|---|
| `is_nonnull`, `ptr_bounds`, `provenance_not_none`, `is_disjoint` | `PointsToProperties` trait methods, delegating to the underlying `PointsToUntyped`. `is_disjoint_unaligned<S>` is the specialized form. |
| `into_aligned` | Now requires `wf()` and aligned address; ensures `perm.wf()`. |
| `as_aligned` | Proved with `shr_ref_struct_wrap` (was an axiom); requires `wf()` and aligned address, ensures `perm.wf()`. |
| `zero_sized` | Now defined on `PointsToUnaligned<T>` (generic in `T`); the old one was `PointsToUnaligned<[u8]>::zero_sized<T>`. Ensures `wf()`. The untyped equivalent is `PointsToUntyped::zero_sized<T>`. |

Accessors that expose inner permissions: `tracked_pt_unaligned` (on `PointsTo`) and
`tracked_pt_untyped` (on `PointsToUnaligned`). They have no `wf()` clauses because they live in
`?Sized` impl blocks where `wf` is not defined. For sized `T`, `self.wf()` implies the inner
permission's `wf()`.

### `PointsToUntyped`

| Function | Notes |
|---|---|
| `bytes()`, `wf()` | `wf()` is the generic `wf_basic()` plus `ptr()@.metadata == len()`. |
| `zero_sized<T>(ptr)` | Replaces `PointsToUnaligned<[u8]>::zero_sized<T>`. |
| `split(mid)`, `join(other)` | Proved; index in bytes and keep `metadata == len`. |
| `split_ref(mid)` | Proved; splits a `&Self` into two halves. |
| `join_ref(other)`, `join_mut(other)` | Axioms; join two borrowed halves into one borrow. |
| `split_mut(mid)` | **Not available for now** (commented out, pending a soundness review of the axiom it was proved from). |
| `is_disjoint_untyped`, `stays_wf` | Specialized `is_disjoint`; `stays_wf` as in [section 3](#3-the-biggest-behavioral-change-explicit-wf-instead-of-a-type-invariant). |

## 6. `SeqPointsTo`

The old `SeqPointsTo<T>` wrapped a `Seq<PointsTo<T>>` and a pointer. The new
`SeqPointsTo<T, PointsToPerm>` is generic over the element permission, which is how
`PointsToUntyped` (elements are `PointsToSingleton`) and the typed sequence
(`SeqPointsTo<T, PointsTo<T>>`) share one definition. `SeqPointsTo<T, PointsTo<T>>` has a `View`
(`SeqPointsToData { ptr, seq_pt }`).

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

### Functions on `SeqPointsTo<T, PointsTo<T>>`

| Function | Notes |
|---|---|
| `from_seq(r, ptr)` | Requires each `r[i].wf()`, the per-element pointer/provenance conditions, non-null, aligned, and `ptr_addr_in_bounds(ptr)` (replaces the old larger bounds condition). Ensures `wf()`. |
| `into_seq` | Requires `wf()`; ensures every element is `wf()`. |
| `tracked_seq_pt`, `tracked_seq_pt_mut`, `index_mut(i)` | Renamed (see [section 4](#4-renames)). The `&mut` ones give `final(self).wf()` conditionally: `tracked_seq_pt_mut` on `SeqPointsTo::ptrs_len_same_valid(old, final)`, `index_mut` on `PointsTo::ptrs_len_same_valid(*ret, *final(ret))`. Establish these with the lemmas (rule 4 in [section 3](#3-the-biggest-behavioral-change-explicit-wf-instead-of-a-type-invariant)). |
| `is_init_subrange`, `value_subrange` | `is_valid_subrange`, `value_subrange`. |
| `is_valid`, `is_empty`, `is_fully_empty` | Note that `is_empty()` means "not all valid", not "all empty"; use `is_fully_empty()` for the latter. |
| `put_subrange`, `put_mem_contents_subrange`, `take_mem_contents_subrange`, `copy_mem_contents_subrange` | `put_subrange`, `put_typed_value_subrange`, `take_typed_value_subrange`, `copy_typed_value_subrange`. Proved; all require `old(self).wf()` and ensure `final(self).wf()`. Replacement sequences are `Seq<TypedValue<T>>` rather than `Seq<MemContents<T>>`. |
| `borrow_mem_contents_subrange` | `borrow_typed_value_subrange` (proved; requires `wf()`; returns a `Seq<&TypedValue<T>>` rather than a `&Seq`). |
| (new) `borrow_value_subrange`, `take_subrange`, `copy_subrange` | The `T` versions (range must be valid for `borrow`/`take`); return `Seq<&T>` / `Seq<T>`. Proved. |
| `empty(ptr)`, `zero_sized(ptr, length)` | Same idea; ensure `wf()`. |
| `split(mid)`, `join(other)` | Same contracts. Also available on `PointsToUntyped` (see [section 5](#pointstountyped)). |
| `cast_to_untyped` | Renamed to `into_untyped_with_typed_value`. Returns a `PointsToUntyped` plus the `Seq<TypedValue<T>>` of typed values (equal to `seq_typed_value()`). Proved. The pointer is fully specified: same address/provenance, metadata `len * size_of::<T>()`. |
| `into_untyped`, `from_untyped(pt_untyped, len)` | `into_untyped` (proved; drops any typed values) and `from_untyped` (proved; requires `wf()`, alignment, `len() == len * size_of::<T>()`; ensures an all-empty, `wf()` permission). |
| `from_untyped_with_typed_value(pt_untyped, capacity, typed_value)` | Replaces `SeqPointsTo<u8>::cast_to_typed`. Takes a `Seq<TypedValue<T>>` (a prefix of the elements). Requires `wf()`, alignment, `len == capacity * size_of::<T>()`, and decodability of each valid element. |
| `as_untyped` | Proved, returning `&PointsToUntyped`. The new `SeqPointsTo<T, PointsTo<T>>` does not store one to borrow, so it joins each element's borrowed `PointsToUntyped`, two at a time, with the `PointsToUntyped::join_ref` axiom. Requires `wf()`. |
| `as_untyped_mut` | Proved from the `PointsToUntyped::join_mut` axiom. Unconditionally, `final(self)` keeps `self`'s pointer and length and is `is_fully_empty()`. If the borrow keeps its pointers/length, `final(self)` is `wf()` with the borrow's final bytes; then `lemma_ptrs_len_same_valid(old, final)` gives `ptrs_len_same_valid`. |
| `subrange(start_index, len)` | Proved (shared borrow, via `shr_ref_struct_wrap`); requires `wf()`. `bytes_subrange_equiv` relates its bytes to the matching subrange of `self.bytes()`. |
| `subrange_mut(i, j)` | Axiom; `final(self).wf()` conditional on the sub-permission staying `wf()` with the same pointer and length. |
| `bytes_decode` | Requires `wf()`; each valid element's `size_of::<T>()`-byte chunk decodes to its value. |
| `is_aligned` | Requires `wf()`. |
| `is_disjoint_seqpt<S>` | Specialization of the trait `is_disjoint` (requires `wf()` and non-empty/non-ZST). |
| `stays_wf`, `lemma_ptrs_len_same_valid` | See [section 3](#3-the-biggest-behavioral-change-explicit-wf-instead-of-a-type-invariant). |

## 7. Slices: use `SeqPointsTo<T, PointsTo<T>>` instead of `PointsTo<[T]>`

The new model has no `PointsTo<[T]>` (or `PointsToUnaligned<[T]>`) impl. **Where possible, code
that used `PointsTo<[T]>` should use `SeqPointsTo<T, PointsTo<T>>`**, and code that used
`PointsTo<[u8]>` / `PointsToUnaligned<[u8]>` as raw bytes should use `PointsToUntyped`.

Two differences to keep in mind:

* **Pointer type.** `PointsTo<[T]>::ptr()` was a `*mut [T]` whose metadata was the length.
  `SeqPointsTo<T, PointsTo<T>>::ptr()` is a `*mut T` (the base), and the length is `len()`. Code
  holding a `*mut [T]` relates the two with `p as *mut T` and `p@.metadata == perm.len()`.
* **Per-element validity.** As before, each element is valid or empty independently
  (`self[i]` is now the element's `PointsTo<T>` permission rather than a `MemContents<T>`).

### `PointsTo<[T]>`

| Old | New on `SeqPointsTo<T, PointsTo<T>>` |
|---|---|
| `mem_contents_seq()` | `seq_typed_value()` (`Seq<TypedValue<T>>`) |
| `len()` | `len()` |
| `self[i]` (a `MemContents<T>`) | `self[i].typed_value()` or `seq_typed_value()[i]` (`self[i]` is the element's `PointsTo<T>`) |
| `is_init()`, `is_init_subrange(start, len)` | `is_valid()`, `is_valid_subrange(start, len)` |
| `is_uninit()`, `is_fully_uninit()` | `is_empty()`, `is_fully_empty()` |
| `value()`, `value_subrange(start, len)` | `seq_value()`, `value_subrange(start, len)` |
| `abstract_bytes()`, `abstract_bytes_decode` | `bytes()`, `bytes_decode` (requires `wf()`) |
| `is_nonnull`, `ptr_bounds`, `provenance_non_null` | Trait methods `is_nonnull`, `ptr_bounds`, `provenance_not_none` (require `wf_basic()`) |
| `is_aligned` | `is_aligned` (requires `wf()`) |
| `is_disjoint<S>` | `is_disjoint_seqpt<S>` |
| `subrange(start, len)` | `subrange(start_index, len)` (proved). The result's pointer is the `*mut T` at the start of the range. |
| `into_seq_pt`, `into_seq_pt_shared` | Not needed: the permission already is a `SeqPointsTo`. Use `into_seq` / `tracked_seq_pt` to get at the `Seq<PointsTo<T>>`. |
| `from_untyped`, `as_untyped`, `as_untyped_mut` | Same names (all proved); see [section 6](#functions-on-seqpointstot-pointstot). |
| `borrow_mem_contents_subrange`, `copy_mem_contents_subrange`, `take_mem_contents_subrange`, `put_mem_contents_subrange`, `put_subrange` | `borrow_typed_value_subrange`, `copy_typed_value_subrange`, `take_typed_value_subrange`, `put_typed_value_subrange`, `put_subrange` |
| `tracked_borrow` (`&[T]`) | **Not possible:** `SeqPointsTo` cannot produce a real `&[T]`. The closest is `borrow_value_subrange(0, len())`, which returns a `Seq<&T>`. |
| `tracked_borrow_mut` (`&mut [T]`) | **Not possible:** no `&mut [T]`, and the per-element `Seq<&mut T>` version (`borrow_mut_subrange`) is commented out along with `PointsTo::borrow_mut`. Use `take_subrange` / `put_subrange`. |
| `into_unaligned`, `as_unaligned` | **Not possible yet:** there is no `SeqPointsTo<T, PointsToUnaligned<T>>` impl. |
| `cast_points_to`, `cast_points_to_unaligned` | **Not possible yet:** planned as an `impl` on `PointsTo<[T]>` (see [PORTING_STATUS.md](PORTING_STATUS.md)). |

### `PointsTo<[u8]>`

| Old | New |
|---|---|
| Used as raw bytes | `PointsToUntyped` |
| `cast_to_typed<T>` | `PointsTo::<T>::from_untyped_with_value(pt_untyped, value)` |
| `cast_to_typed_uninit<T>` | `PointsTo::<T>::from_untyped(pt_untyped)` |
| `cast_to_str_shared` | **Not possible yet:** `str` permissions are on hold (see [section 8](#8-what-is-not-available-yet)). |

### `PointsToUnaligned<[T]>` and `PointsToUnaligned<[u8]>`

| Old | New |
|---|---|
| `PointsToUnaligned<[u8]>::zero_sized<T>` | `PointsToUntyped::zero_sized<T>` |
| Everything else on `PointsToUnaligned<[T]>` (`into_aligned`, `as_aligned`, `as_aligned_mut`, `subrange`, `cast_points_to*`, `into_seq_pt*`, ...) | **Not possible yet:** no unaligned sequence permission exists. |

## 8. What is not available yet

The new model only covers sized `T` so far. These have no equivalent yet. Since `raw_ptr` is no
longer compiled into vstd, code that depends on them can't be migrated until they are ported:

* The `PointsTo<[T]>` / `PointsToUnaligned<[T]>` functions marked "not possible" in
  [section 7](#7-slices-use-seqpointstot-pointstot-instead-of-pointstot): real `&[T]` / `&mut [T]`
  borrows, the unaligned slice methods, and `cast_points_to` / `cast_points_to_unaligned`.
* `PointsTo::borrow_mut` (`&mut T`) and `SeqPointsTo::borrow_mut_subrange`: commented out pending
  a soundness check. For the `borrow_mut` + `ptr_mut_ref_join` pattern, call `ptr_mut_ref` with
  the `&mut PointsTo<T>` instead (see [section 5](#pointstot)); otherwise use `take` / `put`.
* `PointsTo<str>` and the `[u8]` to `str` casts (`cast_to_str_shared`, `cast_to_u8_shared`, ...).
  These are planned as a `SeqPointsTo<str, PointsTo<u8>>` impl; a verified draft exists but is
  currently out of the build (see [PORTING_STATUS.md](PORTING_STATUS.md)).
* `seq_into_slice`, `seq_into_slice_shared`, `seq_into_slice_mut`.
* The slice and `str` versions of the reference helpers: `SharedReference<[T]>` /
  `SharedReference<str>` methods (`points_to`, `as_slice_ptr`, `as_str_ptr`, ...),
  `ptr_ref2_slice_ghost`, `ptr_ref2_str_ghost`, and `mut_ref_to_shr_points_to_slice`/`_str` (all
  commented out). The sized versions (`SharedReference<T>::points_to`, `ptr_ref2`,
  `ptr_ref2_ghost`, `mut_ref_to_shr_points_to`) are ported and use the new `PointsTo<T>`.
[PORTING_STATUS.md](PORTING_STATUS.md) lists which old functions have no equivalent yet.

## 9. Migration checklist

1. Replace `raw_ptr` imports with `points_to_permissions`, `raw_ptr_new` and/or
   `shared_reference`, depending on what each import was for (see [section 1](#1-where-things-live)).
   Wherever you import `points_to_permissions`, also import `points_to` to bring the traits into
   scope.
2. Rename per [section 4](#4-renames) (`is_init` → `is_valid`, `mem_contents` → `typed_value`,
   `abstract_bytes` → `bytes`, `MemContents` → `TypedValue`, ...). On sequences, `mem_contents` →
   `seq_typed_value` and `value` → `seq_value`. `PointsTo::borrow` → `borrow_value`.
   `borrow_mut` followed by `ptr_mut_ref_join` → `ptr_mut_ref` on the `&mut PointsTo<T>`. Also the `Seq`
   tracked borrows: `tracked_mut_borrow` → `tracked_borrow_mut` and `tracked_mut_borrow_subrange` →
   `tracked_borrow_subrange_mut`.
3. Replace uses of `PointsToUnaligned<[u8]>` / `PointsTo<[u8]>` as raw bytes with
   `PointsToUntyped`; update `cast_to_untyped` (now `into_untyped_with_typed_value`), `cast_to_typed`
   (now `PointsTo::from_untyped_with_value` / `SeqPointsTo::from_untyped_with_typed_value`) and
   `from_untyped` call sites and their `ensures`
   (metadata-equals-size becomes `len() == size_of::<T>()`).
4. Replace `PointsTo<[T]>` with `SeqPointsTo<T, PointsTo<T>>` per
   [section 7](#7-slices-use-seqpointstot-pointstot-instead-of-pointstot), including the switch
   from a `*mut [T]` pointer to a `*mut T` base plus `len()`. The "not possible" uses have no
   replacement yet.
5. Add `wf()` to your specs and invariants where you previously relied on the type invariant, and
   discharge the conditional `final(...).wf()` guarantees after `&mut` borrows (using the
   `lemma_ptrs_len_same_valid` lemmas where needed).
6. Where you used `wf()`-derived facts of `SeqPointsTo` (provenance `Some`, whole-range bound), call
   `provenance_not_none` / `ptr_bounds`.
7. `str` permission code has no replacement until `PointsTo<str>` is ported.
