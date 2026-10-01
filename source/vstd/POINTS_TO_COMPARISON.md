# `PointsTo<T>` vs `SeqPointsTo<T, PointsTo<T>>`

Comparison of the inherent impl blocks in `source/vstd/points_to_permissions.rs`:

- `impl<T: ?Sized> PointsTo<T>` (~line 901)
- `impl<T> PointsTo<T>` (~line 1003)
- `impl<T> SeqPointsTo<T, PointsTo<T>>` (~line 1302)
- the generic `impl<T: ?Sized, P> SeqPointsTo<T, P>` (~line 138), since some of the "missing" functions live there

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
| `as_untyped_mut` / `into_untyped` / `from_untyped` | present | none | Only `cast_to_untyped` and `as_untyped` exist on the Seq side. |
| `as_unaligned` / `into_unaligned` | present | none | |
| `borrow` / `take` / `put` | present | none | |
| `borrow_mut` | axiom, borrows the `&mut T` | `borrow_index_mut(i)`, borrows the `&mut PointsTo<T>` at index `i` | Different semantics, so the Seq version was renamed from `borrow_mut` to `borrow_index_mut`. |
| `bytes_decode` | broadcast, with `wf` as requires | not broadcast, ensures a per-index subrange decode | |

## Only on `SeqPointsTo`

- **Length and indexing** (generic block): `len` and `spec_index`.
- **Sequence access:** `tracked_seq_pt`, `tracked_seq_pt_mut` and `into_seq`. `into_seq` and `tracked_seq_pt` ensure each element is `wf`.
- **Construction:**
  - `empty(ptr)` builds an empty sequence at an aligned, non-null, in-bounds pointer.
  - `from_seq(r, ptr)` builds a `SeqPointsTo` from a `Seq<PointsTo<T>>` whose elements are all `wf` and sit at `ptr.addr + i * size_of::<T>()` with the same provenance. It requires the same pointer conditions as `empty`, and ensures `seq_pt() == r`, `ptr() == ptr` and `wf()`.
- **Splitting and joining:**
  - `split(mid)` splits into `[0, mid)` and `[mid, len)`. The first keeps `self.ptr()`, the second's pointer is offset by `mid * size_of::<T>()`. It ensures the `seq_pt` and `bytes` are split to match, and both halves are `wf`.
  - `join(other)` concatenates two `SeqPointsTo`. It requires the same provenance and `other` starting exactly at the end of `self`. It ensures the `seq_pt` and `bytes` are concatenated and the result is `wf`.
- **Sub-range borrowing:** `subrange_mut(i, j)` is an axiom returning `&mut Self` for indices `[i, j)`, with the pointer offset by `i * size_of::<T>()`. If the final sub-permission stays `wf` with the same ptr and len, then `self` is `wf` again with that range replaced.
- **Byte reasoning lemmas:** `bytes_len`, `bytes_equiv`, `bytes_decode` and the private helpers.

## Only on `PointsTo`

- **Field access:** `tracked_pt_unaligned`.
- **Conversions and value access:** the aligned/unaligned and untyped conversions listed in the table, plus `borrow`, `take` and `put`.

## Observations

- `split` and `join` on `SeqPointsTo<T, PointsTo<T>>` follow the same shape as `PointsToUntyped::split` and `join`, but split at element indices (scaled by `size_of::<T>()`) rather than byte indices.
- `PointsTo` has no analogue of `split`, `join`, `subrange_mut` or `from_seq`, since those only make sense for a sequence.
- Still missing on the Seq side compared to `PointsTo`: `as_untyped_mut`, `into_untyped`, `from_untyped`, `as_unaligned`, `into_unaligned`, `borrow`, `take` and `put`. `borrow_index_mut` and `tracked_seq_pt_mut` cover mutation, but only through `PointsTo`.
- The `is_empty` semantics above are the main inconsistency.
- `PointsTo::bytes_decode` is `broadcast` and the Seq one isn't, even though `bytes_equiv` and `bytes_len` on the Seq side are.
- `as_untyped` is an axiom on the Seq side but a proof fn on `PointsTo`.
