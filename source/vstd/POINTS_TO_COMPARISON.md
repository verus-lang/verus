# `SeqPointsTo<T, PointsTo<T>>` vs the typed-value traits

`SeqPointsTo<T, P>` implements only the pointer-level traits,
`PTPhys` (`raw_ptr/points_to_model.rs`) and `PTProperties` (`raw_ptr/points_to_model/points_to_ops.rs`).
It does not implement the typed-value traits in `raw_ptr/points_to_model.rs`:

- `PTTypedValue`: typed value, bytes, `wf` and the lemmas that preserve `wf`
- `PTValueOps`: constructors, borrowing and moving the typed value, and untyped conversions
- `PTSizedValue`: the same for a `Sized` value (`take`, `put`, `copy`, ...)

Instead, the only typed instance, `SeqPointsTo<T, PointsTo<T>>`,
has inherent counterparts in `raw_ptr/points_to_collections.rs` (`impl<T> SeqPointsTo<T, PointsTo<T>>`).
This doc compares those counterparts with the trait items.

## Why `SeqPointsTo` can't implement the traits

- `PTTypedValue::typed_value` is a single `TypedValue<Self::A>`.
  For a `SeqPointsTo`, `Self::A` is `[T]`, and a `TypedValue<[T]>` is either all valid or all empty.
  A `SeqPointsTo` tracks validity per element, so most of its states can't be written as one `TypedValue<[T]>`.
  Each trait operation is therefore replaced by a subrange version over `Seq<TypedValue<T>>` or `Seq<T>`.
- `PTSizedValue` needs `Self::A: Sized`, which `[T]` is not.
- `PointsTo<[T]>` implements all three traits.
  `as_slice_pt` / `as_slice_pt_mut` borrow a `SeqPointsTo<T, PointsTo<T>>` as a `PointsTo<[T]>`.
  The slice permission is valid only if every element is valid;
  otherwise it is empty.

## `PTTypedValue`

| Trait item | `SeqPointsTo<T, PointsTo<T>>` | Difference |
|---|---|---|
| `typed_value()`: `TypedValue<A>` | `seq_typed_value()`: `Seq<TypedValue<T>>` | One typed value per element. `typed_value_equiv(i)` (broadcast) relates `seq_typed_value()[i]` to `self[i].typed_value()`. |
| (`TypedValue` helpers) `is_valid()`, `is_empty()`, `value()` | `is_valid()`, `is_empty()`, `is_fully_empty()`, `seq_value()`, plus `is_valid_subrange(start, end)` and `value_subrange(start, end)` | `is_empty()` here is `!is_valid()` ("some element is empty"), not "every element is empty", so it isn't the per-element analogue of `TypedValue::is_empty`. `is_fully_empty()` is "every element is empty". |
| `bytes()` | `bytes()`: the elements' bytes, concatenated (`bytes_inner`, a `fold_left`) | Reasoning about the fold goes through `bytes_len` (broadcast), `bytes_equiv(i)` (broadcast) and `bytes_subrange_equiv`. |
| `wf()` = `wf_basic()` + `satisfies_alignment(addr)` + `valid_value()` | `wf()` = `wf_basic()` + `PointsTo::<T>::satisfies_alignment(addr)` + every element `wf()` | Validity is per element (each element's `wf()` includes its `valid_value()`); there is no sequence-level `valid_value`. |
| `valid_value()` | none | Per element: `self[i].valid_value()`. |
| `additional_validity_constraints(value, metadata)` | none | Always `true` for the `Sized` elements. |
| `satisfies_alignment(addr)` | none | Uses `PointsTo::<T>::satisfies_alignment` on the base address. |
| `bytes_decode()`: `bytes().len() == size(metadata)`, and if valid, `bytes()` decodes to the value | `bytes_decode()`: for each `i`, if element `i` is valid, `bytes()[i * size, (i + 1) * size)` decodes to its value, and `self[i].bytes().len() == size_of::<T>()` | The total length is a separate lemma, `bytes_len()`. |
| `satisfies_alignment_of_wf()` | `is_aligned()`: `addr % align_of::<T>() == 0` | Different name and conclusion (`PointsTo<T>` has both). |
| `lemma_wf_basic()` | none | Not needed: `wf()` is open and includes `wf_basic()` directly. |
| `ptrs_len_same_valid_value(old, new)` | same name, inherent | `ptrs_len_same` plus every element's `valid_value()`. |
| `lemma_ptrs_len_same_valid_value(old, new)` (broadcast) | same name, inherent, broadcast | Same requires (both `wf()`, same `ptr()`). It is in `group_points_to_collections_lemmas`, which isn't in `group_vstd_default`. |
| `stays_wf(old, new)` | same name, inherent | Same statement. |

## `PTValueOps`

| Trait item | `SeqPointsTo<T, PointsTo<T>>` | Difference |
|---|---|---|
| `zero_sized(ptr)`: requires `size(metadata) == 0` | `zero_sized(ptr: *mut T, length)`: requires `size_of::<T>() == 0` | Covers a ZST `T` with any length. For length 0 with any `T`, use `empty(ptr)` (generic block), which ensures only `wf_basic()`. Ensures every element is empty, not `bytes().len() == 0` (that follows from `bytes_len`). |
| `borrow_typed_value()`: `&TypedValue<A>` | `borrow_typed_value_subrange(start, end)`: `Seq<&TypedValue<T>>` | Subrange of element borrows. |
| `take_typed_value()` | `take_typed_value_subrange(start, end)`: `Seq<TypedValue<T>>` | Empties the subrange; the rest of `seq_typed_value()` is unchanged (`update_subrange_with`). |
| `put_typed_value(v)` | `put_typed_value_subrange(start, Seq<TypedValue<T>>)` | Each valid value must decode from its element's byte subrange. |
| `borrow()`: `&A`, requires valid | `borrow_subrange(start, end)`: `Seq<&T>`, requires the subrange valid | |
| `into_untyped_with_typed_value()`: `(PointsToUntyped, TypedValue<A>)` | same name: `(PointsToUntyped, Seq<TypedValue<T>>)` | The untyped length is `len() * size_of::<T>()`. |
| `from_untyped_with_typed_value(pt_untyped, typed_value, metadata)` | `from_untyped_with_typed_value(pt_untyped, capacity, Seq<TypedValue<T>>)` | `typed_value` may be a prefix of `capacity`. It ensures nothing about the elements past the prefix (`from_untyped` empties them). It ensures `ptr()`'s address and provenance, plus `len() == capacity`, instead of the whole pointer (the metadata follows from `wf()`). |
| `into_untyped()` | same name | Same shape. |
| `as_untyped()` | same name | Same specs. It is proved by joining the elements' untyped borrows with `PointsToUntyped::join_ref`. |
| `as_untyped_mut()` | same name | Unconditionally, `final(self)` keeps `old(self)`'s pointer and length and is fully empty. Its bytes are the final untyped bytes only when the untyped permission keeps its pointers and length (`ptrs_len_same`), and `final(self).wf()` holds under that same condition. The trait instead gives `final(self)`'s address, provenance and bytes from the final untyped permission unconditionally, and only `wf()` under that condition. |
| `from_untyped(pt_untyped, metadata)` | `from_untyped(pt_untyped, len: usize)` | Ensures `is_fully_empty()`. |

## `PTSizedValue`

| Trait item | `SeqPointsTo<T, PointsTo<T>>` | Difference |
|---|---|---|
| `lemma_satisfies_alignment_offset(addr, i)` | none | Used internally (e.g. by `subrange`) through `PointsTo::<T>`'s version. |
| `lemma_additional_validity_constraints(value)` | none | Not needed (see `PTTypedValue`). |
| `take()`: `A` | `take_subrange(start, end)`: `Seq<T>`, requires the subrange valid | Same postcondition shape as `take_typed_value_subrange`. |
| `put(v)` | `put_subrange(start, Seq<T>)` | It ensures the subrange is valid with the given values and every other element's typed value is unchanged, rather than an `update_subrange_with` equation. |
| `copy(&v)` | `copy_subrange(start, &Seq<T>)` | Same ensures as `put_subrange`. |
| `copy_typed_value(&v)` | `copy_typed_value_subrange(start, Seq<&TypedValue<T>>)` | Takes a sequence of references, whereas `copy_subrange` takes a reference to a sequence. |
| `from_untyped_with_value(pt_untyped, value)` | none | Use `from_untyped_with_typed_value` with `Valid` values. |

## Only on `SeqPointsTo<T, PointsTo<T>>`

- `borrow_mut_subrange(start, end)`: `Seq<&mut T>`, from `PointsTo<T>::borrow_mut` (inherent, not in a trait) on each element.
- `split` / `join`, `subrange` / `subrange_mut`: typed (`wf()`) versions of the generic block's `split_basic`, `join_basic` and `subrange_basic`.
- `as_slice_pt` / `as_slice_pt_mut`: borrow as a `PointsTo<[T]>`.
- `is_disjoint_seqpt<S>`: `PTProperties::is_disjoint` specialized to another `SeqPointsTo<S, PointsTo<S>>`.
- `thin_ptr()`: `ptr()` without the metadata.

## Observations

- Every per-value trait operation has a subrange counterpart except `from_untyped_with_value`.
  Single-element operations go through `index_mut(i)` (generic block) followed by the element's own trait method.
- The postconditions of the range operations come in two styles:
  the `TypedValue` ones and `take_subrange` use `update_subrange_with`,
  while `put_subrange` and `copy_subrange` state validity, `value_subrange` and "other elements unchanged".
- Their arguments are inconsistent too:
  `copy_typed_value_subrange` takes `Seq<&TypedValue<T>>`, but `copy_subrange` takes `&Seq<T>`.
- `is_empty()` means something different here than in `TypedValue::is_empty` (see `PTTypedValue`).
- `satisfies_alignment_of_wf` is named `is_aligned` here, and `lemma_ptrs_len_same_valid_value` is in a separate broadcast group.
