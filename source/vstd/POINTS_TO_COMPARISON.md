# `PointsTo<T>` vs `SeqPointsTo<T, PointsTo<T>>`

Comparison of the inherent impl blocks in `source/vstd/points_to_permissions.rs`:

- `impl<T: ?Sized> PointsTo<T>` (~line 944)
- `impl<T> PointsTo<T>` (~line 1046)
- `impl<T> SeqPointsTo<T, PointsTo<T>>` (~line 1348)
- the generic `impl<T: ?Sized, P> SeqPointsTo<T, P>` (~line 139), since some of the "missing" functions live there
- `impl PointsToUntyped` (~line 188), since a few sequence-side counterparts (`cast_to_seq_pt`, `cast_to_typed`) live there

## Counterparts

| Concept | `PointsTo<T>` | `SeqPointsTo<T, PointsTo<T>>` | Difference |
|---|---|---|---|
| Underlying data | `pt_unaligned()` (closed) | `seq_pt()` (closed, in the generic block) | A `PointsTo` wraps one `PointsToUnaligned`. A `SeqPointsTo` wraps a `Seq<PointsTo<T>>` plus a ghost `*mut T`. |
| `wf` | `wf_basic()`, which checks alignment and `pt_unaligned().wf()` | `wf_basic()` plus alignment of the base pointer | `SeqPointsTo::wf_basic` is the trait impl. It checks that each element's ptr and provenance line up at `addr + i*size` and that each element is wf_basic. It also checks non-null and bounds. |
| `typed_value` | `TypedValue<T>` | `Seq<TypedValue<T>>` (via `map`) | The Seq version adds the broadcast lemma `typed_value_equiv`. |
| `bytes` | `pt_unaligned().bytes()` | `bytes_inner(seq_pt())`, a `fold_left` that concatenates the elements' bytes | The Seq version needs `bytes_len`, `bytes_len_helper`, `bytes_subrange` and `bytes_equiv` to reason about the fold. |
| `value` | `T` (recommends valid) | `Seq<T>` (recommends valid) | |
| `is_valid` | the single value is valid | all elements valid | |
| `is_empty` | `typed_value().is_empty()` | `!is_valid()`, meaning any element is invalid | Semantic mismatch. For `PointsTo`, `is_empty` is the exact complement of `is_valid`. For `SeqPointsTo`, `is_empty` means "not all valid", so it is not "all empty". |
| `is_fully_empty` | none | all elements empty | Needed because of the `is_empty` point above. |
| `ptrs_len_same_valid_decode` | delegates to `PointsToUnaligned` | same ptr and len, plus a per-element `PointsTo::ptrs_len_same_valid_decode` and the same per-element ptr | |
| `stays_wf` | identical statement | identical statement | Both have an empty proof body. |
| `is_aligned` | `is_aligned(&self)`, requires `wf()`, ensures `ptr().addr % align_of::<T>() == 0` | identical statement | Both have an empty proof body, since `wf()` already includes the alignment condition. |
| `zero_sized` | `(ptr)`, requires non-null, aligned, in-bounds and ZST, ensures empty and wf | `(ptr, length)`, same requires, ensures all elements empty and wf | The Seq version builds the result recursively with `empty` and `zero_sized_helper`. |
| `is_disjoint_*` | `is_disjoint_pointsto<S>` | `is_disjoint_seqpt<S>` | Both specialize the trait's `is_disjoint`. The Seq version additionally requires `len != 0` and uses `len * size`. |
| `cast_to_untyped` | returns `(PointsToUntyped, Option<T>)` | returns `(PointsToUntyped, Seq<Option<T>>)` | The Seq version recurses with `pop` and `join`. |
| `as_untyped` | proof fn, returns the `&PointsToUntyped` stored inside | axiom, returns a `&PointsToUntyped` with the same address, provenance and bytes and length `len * size_of::<T>()` | The Seq version is an axiom because a `SeqPointsTo` doesn't store a `PointsToUntyped` to borrow. |
| `as_untyped_mut` | proof fn, returns `&mut` to the `PointsToUntyped` inside, drops the typed value | axiom, returns `&mut PointsToUntyped` with the same address, provenance, bytes and length `len * size_of::<T>()`; ensures `final(self)` is `is_fully_empty()` and `wf()` if the untyped part keeps its pointers and length | Axiom on the Seq side for the same reason as `as_untyped`. |
| `into_untyped` | present | `into_untyped`, proved as `cast_to_untyped` with the typed values dropped | Same contract shape: same address and provenance, length `len * size_of::<T>()`, same bytes, `wf()`. |
| `from_untyped` | `from_untyped(pt_untyped)`, builds an empty `PointsTo<T>` | `from_untyped(pt_untyped, len)`, builds an all-empty `SeqPointsTo<T, PointsTo<T>>` of length `len` | Proved from `PointsToUntyped::cast_to_seq_pt` followed by `take_typed_value_subrange(0, len)` to empty every element. `cast_to_seq_pt(capacity, typed_value)` is the version that also takes a prefix of typed values. |
| `cast_to_typed` (from untyped bytes plus a value) | `PointsToUntyped::cast_to_typed(typed_value)`, proved from `from_untyped` + `put` | `PointsToUntyped::cast_to_seq_pt` | Both are on `PointsToUntyped`. |
| `as_unaligned` / `into_unaligned` | present | none | No `SeqPointsTo<T, PointsToUnaligned<T>>` impl yet (on hold). |
| `borrow` / `take` / `put` | present (single value); `put`/`take` also ensure `ptrs_len_same_valid_decode` | none for single elements; range versions instead: `take_typed_value_subrange`, `put_subrange`, `put_typed_value_subrange`, `copy_typed_value_subrange` (proved), `borrow_typed_value_subrange` (axiom) | The range versions are built by induction on `index_mut` and the `TypedValue` fields; they use the `ptrs_len_same_valid_decode` guarantee on `put`/`take`. |
| `borrow_mut` | axiom, borrows the `&mut T` | `index_mut(i)`, borrows the `&mut PointsTo<T>` at index `i` | Different semantics, so the Seq version was renamed from `borrow_mut` to `index_mut` (the name then matches `subrange_mut`). |
| `bytes_decode` | broadcast, with `wf` as requires | not broadcast, ensures a per-index subrange decode | |

## Only on `SeqPointsTo`

- **Length and indexing** (generic block): `len` and `spec_index`.
- **Subrange specs:** `is_valid_subrange(start_index, len)` (all elements in the range are valid) and `value_subrange(start_index, len)` (the values in the range).
- **Sequence access:** `tracked_seq_pt`, `tracked_seq_pt_mut` and `into_seq`. `into_seq` and `tracked_seq_pt` ensure each element is `wf`.
- **Construction:**
  - `empty(ptr)` builds an empty sequence at an aligned, non-null, in-bounds pointer.
  - `from_seq(r, ptr)` builds a `SeqPointsTo` from a `Seq<PointsTo<T>>` whose elements are all `wf` and sit at `ptr.addr + i * size_of::<T>()` with the same provenance. It requires the same pointer conditions as `empty`, and ensures `seq_pt() == r`, `ptr() == ptr` and `wf()`.
- **Splitting and joining:**
  - `split(mid)` splits into `[0, mid)` and `[mid, len)`. The first keeps `self.ptr()`, the second's pointer is offset by `mid * size_of::<T>()`. It ensures the `seq_pt` and `bytes` are split to match, and both halves are `wf`.
  - `join(other)` concatenates two `SeqPointsTo`. It requires the same provenance and `other` starting exactly at the end of `self`. It ensures the `seq_pt` and `bytes` are concatenated and the result is `wf`.
- **Sub-range borrowing** (both axioms): `subrange_mut(i, j)` returns `&mut Self` for indices `[i, j)`, with the pointer offset by `i * size_of::<T>()`. If the final sub-permission stays `wf` with the same ptr and len, then `self` is `wf` again with that range replaced. `subrange(start_index, len)` is the shared-borrow version, returning `&Self`; it also ensures the matching `bytes` subrange.
- **Sub-range contents:**
  - Proved: `put_subrange` (put a `Seq<T>`), `put_typed_value_subrange` (put a `Seq<TypedValue<T>>`), `take_typed_value_subrange` (move the values out, leaving that range empty) and `copy_typed_value_subrange` (`T: Copy`). Each requires `wf()` and ensures `wf()`, the same `ptr()` and `bytes()`, and the `update_subrange_with` result for `typed_value()`.
  - Axiom: `borrow_typed_value_subrange` (borrow the `Seq<TypedValue<T>>` for a range).
- **Byte reasoning lemmas:** `bytes_len`, `bytes_equiv`, `bytes_decode` and the private helpers (`bytes_len_helper`, `bytes_subrange`, `bytes_inner_ext`).

## `PointsToUntyped` counterparts

- `split(mid)` / `join(other)`: same shape as the `SeqPointsTo<T, PointsTo<T>>` versions, but index in bytes and keep the slice-pointer metadata equal to the length.
- `cast_to_seq_pt(capacity, typed_value)`: inverse of `SeqPointsTo::cast_to_untyped`. Builds a `SeqPointsTo<T, PointsTo<T>>` with the first `typed_value.len()` entries valid and the rest empty.
- `cast_to_typed(typed_value)`: single value, builds a valid `PointsTo<T>` from a `PointsToUntyped` of length `size_of::<T>()`.

## Only on `PointsTo`

- **Field access:** `tracked_pt_unaligned`.
- **Conversions and value access:** the aligned/unaligned and untyped conversions listed in the table, plus `borrow`, `take` and `put`.

## Observations

- `split` and `join` on `SeqPointsTo<T, PointsTo<T>>` follow the same shape as `PointsToUntyped::split` and `join`, but split at element indices (scaled by `size_of::<T>()`) rather than byte indices.
- `PointsTo` has no analogue of `split`, `join`, `subrange`, `subrange_mut`, the subrange content operations or `from_seq`, since those only make sense for a sequence.
- The single-element `borrow`, `take` and `put` are not missing on the Seq side: they are subsumed by the subrange versions (a single element is a subrange of length 1). What is still missing are the `Seq<T>` subrange operations `take_subrange`, `borrow_subrange` and `borrow_mut_subrange` (see the TODOs), and potentially `copy_subrange` (taking in `&Seq<T>`).
- Potentially missing on the `PointsTo` side: `copy` (taking in `&T`) and `copy_typed_value` (taking in `&TypedValue<T>`). The Seq side already has `copy_typed_value_subrange`, and `PointsTo` has no copy operation at all.
- Also still missing on the Seq side compared to `PointsTo`: `as_unaligned` and `into_unaligned`. `index_mut` and `tracked_seq_pt_mut` cover element mutation, but only through `PointsTo`.
- The `is_empty` semantics above are the main inconsistency.
- `PointsTo::bytes_decode` is `broadcast` and the Seq one isn't, even though `bytes_equiv` and `bytes_len` on the Seq side are.
- `as_untyped` and `as_untyped_mut` are axioms on the Seq side but proof fns on `PointsTo`: a `SeqPointsTo` stores no `PointsToUntyped` to borrow, whereas `PointsTo` holds one inside its `PointsToUnaligned`.
- The sequence-only range operations (`put_subrange`, `take_typed_value_subrange`, ...) are proved, not axioms. They rely on `PointsTo::put` / `take` ensuring `ptrs_len_same_valid_decode`, so `index_mut` can re-establish `wf()`.
- The axioms on the Seq side are the ones that return a reference to something not stored (`as_untyped`, `as_untyped_mut`, `subrange`, `borrow_typed_value_subrange`), and `subrange_mut` (needs a `&mut` sub-permission whose final state flows back into `self`).
- The `str` permission (`SeqPointsTo<str, PointsTo<u8>>`) is drafted in `points_to_str_wip.rs` and is not part of this comparison.

## TODOs

Based on the comparison above:

- `SeqPointsTo::take_subrange`, `SeqPointsTo::borrow_subrange` and `SeqPointsTo::borrow_mut_subrange` (with `Seq<T>`).
- `PointsTo::borrow_typed_value`, `PointsTo::take_typed_value` and `PointsTo::put_typed_value` (with `TypedValue<T>`).
- Potentially: `SeqPointsTo::copy_subrange` (taking in `&Seq<T>`), `PointsTo::copy` (taking in `&T`) and `PointsTo::copy_typed_value` (taking in `&TypedValue<T>`).
- `PointsTo::cast_points_to` and `PointsTo::cast_points_to_unaligned`: possibly in the future, if we implement `PointsTo<[T]>`. On hold for now.
