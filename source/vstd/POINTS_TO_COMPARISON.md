# `PointsTo<T>` vs `SeqPointsTo<T, PointsTo<T>>`

Comparison of the inherent impl blocks in `source/vstd/points_to_permissions.rs`:

- `impl<T: ?Sized> PointsTo<T>` (~line 944)
- `impl<T> PointsTo<T>` (~line 1046)
- `impl<T> SeqPointsTo<T, PointsTo<T>>` (~line 1348)
- the generic `impl<T: ?Sized, P> SeqPointsTo<T, P>` (~line 139), since some of the "missing" functions live there
- `impl PointsToUntyped` (~line 188), for `split` / `join` and their borrowed versions

## Counterparts

| Concept | `PointsTo<T>` | `SeqPointsTo<T, PointsTo<T>>` | Difference |
|---|---|---|---|
| Underlying data | `pt_unaligned()` (closed) | `seq_pt()` (closed, in the generic block) | A `PointsTo` wraps one `PointsToUnaligned`. A `SeqPointsTo` wraps a `Seq<PointsTo<T>>` plus a ghost `*mut T`. |
| `View` | `PointsToData { ptr, value, bytes }` | `SeqPointsToData { ptr, seq_pt }` | The Seq view exposes the per-element `PointsTo<T>` permissions, rather than a flattened value or bytes. |
| `wf` | `wf_basic()`, which checks alignment and `pt_unaligned().wf()` | `wf_basic()` plus alignment of the base pointer | `SeqPointsTo::wf_basic` is the trait impl. It checks that each element's ptr and provenance line up at `addr + i*size` and that each element is wf_basic. It also checks non-null and bounds. |
| `typed_value` | `typed_value()`: `TypedValue<T>` | `seq_typed_value()`: `Seq<TypedValue<T>>` (via `map`) | The Seq version adds the broadcast lemma `typed_value_equiv`. |
| `bytes` | `pt_unaligned().bytes()` | `bytes_inner(seq_pt())`, a `fold_left` that concatenates the elements' bytes | The Seq version needs `bytes_len`, `bytes_len_helper`, `bytes_subrange`, `bytes_equiv` and `bytes_subrange_equiv` to reason about the fold. |
| `value` | `value()`: `T` (recommends valid) | `seq_value()`: `Seq<T>` (recommends valid); `value_subrange(start_index, len)` gives the values in a range (recommends that range valid) | |
| `is_valid` | the single value is valid | all elements valid; `is_valid_subrange(start_index, len)` says all elements in a range are valid | |
| `is_empty` | `typed_value().is_empty()` | `!is_valid()`, meaning any element is invalid | Semantic mismatch. For `PointsTo`, `is_empty` is the exact complement of `is_valid`. For `SeqPointsTo`, `is_empty` means "not all valid", so it is not "all empty". |
| `is_fully_empty` | none | all elements empty | Needed because of the `is_empty` point above. |
| `ptrs_len_same_valid` | same `ptr()`, plus `PointsToUnaligned`'s (which also states the same `ptr()` explicitly) | same ptr and len, plus a per-element `PointsTo::ptrs_len_same_valid` and the same per-element ptr | A `PointsToProperties` trait method, along with `stays_wf_basic` (`old.wf_basic()` and `ptrs_len_same_valid` imply `new.wf_basic()`). The Seq definition is the generic one for every `SeqPointsTo<T, P>`, so `PointsToUntyped` shares it. |
| `stays_wf` | `old.wf()` and `ptrs_len_same_valid(old, new)` imply `new.wf()` | identical statement | Inherent, with spec arguments (so it applies to `old(..)` / `final(..)` values). Both are proved from the trait's `stays_wf_basic`; the Seq `wf()`'s extra alignment condition carries over because the pointer is unchanged. |
| `lemma_ptrs_len_same_valid` | `(old, new)`: both `wf()` with the same `ptr()` imply `ptrs_len_same_valid(old, new)` | `(old, new)`: both `wf()` with the same `ptr()` and `len()` imply `ptrs_len_same_valid(old, new)` | Public, with spec arguments. Outside the module, callers need these to restore `wf()` (e.g. after `index_mut` or `as_untyped_mut`), since the predicate unfolds through closed specs. The Seq version calls the `PointsTo` one per element, after `wf()` lines the elements up at the same addresses. |
| `is_aligned` | `is_aligned(&self)`, requires `wf()`, ensures `ptr().addr % align_of::<T>() == 0` | identical statement | Both have an empty proof body, since `wf()` already includes the alignment condition. |
| `zero_sized` | `(ptr)`, requires non-null, aligned, in-bounds and ZST, ensures empty and wf | `(ptr, length)`, same requires, ensures all elements empty and wf | The Seq version builds the result recursively with `empty` and `zero_sized_helper`. |
| `is_disjoint_*` | `is_disjoint_pointsto<S>` | `is_disjoint_seqpt<S>` | Both specialize the trait's `is_disjoint`. The Seq version additionally requires `len != 0` and uses `len * size`. |
| `into_untyped_with_typed_value` | returns `(PointsToUntyped, TypedValue<T>)` | returns `(PointsToUntyped, Seq<TypedValue<T>>)` | Both return exactly `self`'s typed value(s), so they can be called whether or not `self` is valid. The Seq version recurses with `pop` and `join`. |
| `as_untyped` | proof fn, returns the `&PointsToUntyped` stored inside | proved, returns a `&PointsToUntyped` with the same address, provenance and bytes and length `len * size_of::<T>()` | A `SeqPointsTo` doesn't store a single `PointsToUntyped` to borrow, so the Seq version borrows each element's (`PointsTo::as_untyped`) and joins the borrows two at a time with the `PointsToUntyped::join_ref` axiom. The empty case uses `PointsToUntyped::zero_sized` and `tracked_static_ref`. |
| `as_untyped_mut` | proof fn, returns `&mut` to the `PointsToUntyped` inside, drops the typed value | proved, returns `&mut PointsToUntyped` with the same address, provenance, bytes and length `len * size_of::<T>()`; ensures `final(self)` keeps `self`'s pointer and length and is `is_fully_empty()` unconditionally, and is `wf()` with the borrow's final bytes if the untyped part keeps its pointers and length (the `PointsTo` version ensures only `final(self).wf()` under that condition; `is_empty()`, the bytes and the link between `final(self).ptr()` and the borrow's pointer hold unconditionally). In both, callers get `ptrs_len_same_valid(old(self), final(self))` from `lemma_ptrs_len_same_valid` | Same approach as `as_untyped`, with `&mut` borrows: it splits the `&mut Seq<PointsTo<T>>` (`Seq::tracked_split_borrow_mut`), borrows each element's with `PointsTo::as_untyped_mut`, and joins them with the `PointsToUntyped::join_mut` axiom. The empty case uses `zero_sized` and `tracked_static_mut_ref`. |
| `into_untyped` | present | `into_untyped`, proved as `into_untyped_with_typed_value` with the typed values dropped | Same contract shape: same address and provenance, length `len * size_of::<T>()`, same bytes, `wf()`. |
| `from_untyped` | `from_untyped(pt_untyped)`, builds an empty `PointsTo<T>` | `from_untyped(pt_untyped, len)`, builds an all-empty `SeqPointsTo<T, PointsTo<T>>` of length `len` | Proved from `from_untyped_with_typed_value` (with no typed values) followed by `take_typed_value_subrange(0, len)` to empty every element. |
| `from_untyped_with_value` / `from_untyped_with_typed_value` | `from_untyped_with_value(pt_untyped, value)`, builds a valid `PointsTo<T>` holding `value`; proved from `from_untyped` + `put` | `from_untyped_with_typed_value(pt_untyped, capacity, typed_value)`, builds a `SeqPointsTo<T, PointsTo<T>>` whose first `typed_value.len()` elements hold the given typed values | The asymmetry is deliberate: for a single value, `from_untyped` (empty) and `from_untyped_with_value` (valid) cover both cases, while the Seq version takes `TypedValue`s so each element can independently be valid or not. Both are the inverses of `into_untyped_with_typed_value`. |
| `as_unaligned` / `into_unaligned` | present | none | No `SeqPointsTo<T, PointsToUnaligned<T>>` impl yet (on hold). |
| `borrow_value` / `take` / `put` / `copy` (with `T`) | `borrow_value`, `take`, `put` and `copy` (`T: Copy`, taking `&T`) | none for single elements; range versions instead: `borrow_value_subrange` (returns `Seq<&T>`), `take_subrange`, `put_subrange` and `copy_subrange`, all proved | `take_subrange` requires the range to be valid and returns `value_subrange`. The `take`/`put`/`copy` range versions each require `wf()` and ensure `wf()`, the same `ptr()` and `bytes()`, and the `update_subrange_with` result for `seq_typed_value()`. They are built by induction on `index_mut`. `copy` is proved from `put`; `copy_subrange` from `put_subrange`. |
| `borrow_typed_value` / `take_typed_value` / `put_typed_value` / `copy_typed_value` | `borrow_typed_value`, `take_typed_value`, `put_typed_value` and `copy_typed_value` (`T: Copy`), all proved | `borrow_typed_value_subrange` (returns `Seq<&TypedValue<T>>`), `take_typed_value_subrange`, `put_typed_value_subrange` and `copy_typed_value_subrange`, all proved | Unlike the `T` versions, these don't require validity. `take_typed_value` leaves `self` empty; `put_typed_value` requires decoding only if the value is valid. The `take`/`put`/`copy` range versions have the same contract shape as the `T` ones. |
| `borrow_mut` (commented out) | axiom, borrows the `&mut T` | `borrow_mut_subrange(start, end)` (commented out), proved, returns a `Seq<&mut T>` for a valid range | The Seq version is proved by splitting the `&mut Seq<PointsTo<T>>` (`Seq::tracked_split_borrow_mut`) and calling `borrow_mut` on each element. Both ensure `ptrs_len_same_valid` and `wf()` unconditionally (the bytes may change along with the value). |
| `bytes_decode` | broadcast, with `wf` as requires | not broadcast, ensures a per-index subrange decode | |

## Only on `SeqPointsTo`

- **Length and indexing** (generic block): `len` and `spec_index`.
- **Sequence access:** `tracked_seq_pt`, `tracked_seq_pt_mut`, `index_mut` and `into_seq`. `into_seq` and `tracked_seq_pt` ensure each element is `wf`. `index_mut(i)` borrows the `&mut PointsTo<T>` at index `i`.
- **Construction:**
  - `empty(ptr)` builds an empty sequence at an aligned, non-null, in-bounds pointer.
  - `from_seq(r, ptr)` builds a `SeqPointsTo` from a `Seq<PointsTo<T>>` whose elements are all `wf` and sit at `ptr.addr + i * size_of::<T>()` with the same provenance. It requires the same pointer conditions as `empty`, and ensures `seq_pt() == r`, `ptr() == ptr` and `wf()`.
- **Splitting and joining:**
  - `split(mid)` splits into `[0, mid)` and `[mid, len)`. The first keeps `self.ptr()`, the second's pointer is offset by `mid * size_of::<T>()`. It ensures the `seq_pt` and `bytes` are split to match, and both halves are `wf`.
  - `join(other)` concatenates two `SeqPointsTo`. It requires the same provenance and `other` starting exactly at the end of `self`. It ensures the `seq_pt` and `bytes` are concatenated and the result is `wf`.
- **Sub-range borrowing:** `subrange_mut(i, j)` (axiom) returns `&mut Self` for indices `[i, j)`, with the pointer offset by `i * size_of::<T>()`. If the final sub-permission stays `wf` with the same ptr and len, then `self` is `wf` again with that range replaced. `subrange(start_index, len)` (proved) is the shared-borrow version, returning `&Self`: it borrows the `seq_pt` subrange (`Seq::tracked_borrow_subrange`) and wraps it with `shr_ref_struct_wrap`. Its `bytes` are the matching subrange of `self.bytes()`, which follows from `bytes_subrange_equiv`.
- **Byte reasoning lemmas:** `bytes_len`, `bytes_equiv`, `bytes_subrange_equiv` (public wrapper around `bytes_subrange` for `[start, end)`) and the private helpers (`bytes_len_helper`, `bytes_subrange`, `bytes_inner_ext`).

## `PointsToUntyped` counterparts

- `split(mid)` / `join(other)`: same shape as the `SeqPointsTo<T, PointsTo<T>>` versions, but index in bytes and keep the slice-pointer metadata equal to the length.
- Borrowed versions: `split_ref(mid)` (proved) splits a `&Self` into two halves with the same specs as `split`. `split_mut(mid)` is commented out (it was proved from a `&mut` struct-wrapping axiom that is pending a soundness review). `join_ref(other)` / `join_mut(other)` (axioms) join borrowed halves.

## Only on `PointsTo`

- **Field access:** `tracked_pt_unaligned`.

## Observations

- `split` and `join` on `SeqPointsTo<T, PointsTo<T>>` follow the same shape as `PointsToUntyped::split` and `join`, but split at element indices (scaled by `size_of::<T>()`) rather than byte indices.
- Still missing on the Seq side compared to `PointsTo`: `as_unaligned` and `into_unaligned`.
- The `is_empty` semantics above are the main inconsistency.
- `PointsTo::bytes_decode` is `broadcast` and the Seq one isn't, even though `bytes_equiv` and `bytes_len` on the Seq side are.
- A `SeqPointsTo` stores no single `PointsToUntyped` to borrow, whereas `PointsTo` holds one inside its `PointsToUnaligned`. `as_untyped` and `as_untyped_mut` work around this by joining per-element borrows with the binary `PointsToUntyped::join_ref` / `join_mut` axioms.
- To re-establish `wf()` after mutating an element borrowed with `index_mut`, callers need `PointsTo::ptrs_len_same_valid` for that element. Outside the module this comes from `PointsTo::lemma_ptrs_len_same_valid` (both versions `wf()`, same `ptr()`); the range operations inside the module get it by unfolding the predicate.
- The only axiom left on the Seq side is `subrange_mut` (needs a `&mut` sub-permission whose final state flows back into `self`).
- The `str` permission (`SeqPointsTo<str, PointsTo<u8>>`) is drafted in `points_to_str_wip.rs` and is not part of this comparison.

## TODOs

All TODOs, including those that come out of this comparison, are tracked in the TODO section of [PORTING_STATUS.md](PORTING_STATUS.md#todo).
