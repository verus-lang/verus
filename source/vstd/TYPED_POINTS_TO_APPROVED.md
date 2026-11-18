# Approved: vstd `raw_ptr` permissions

The approved design of vstd's `raw_ptr` permissions and their trusted code.
Any change here needs to be flagged for re-approval.
Specs live in the code and aren't repeated here.

## Permission types

- `PointsToByte`: permission for one byte (axiomatized).
- `SeqPointsTo<T, P>`: a sequence of element permissions `P` with a `*mut [T]` pointer to the whole region.
  `PointsToUntyped` is `SeqPointsTo<u8, PointsToByte>`;
  the only typed sequences are `SeqPointsTo<T, PointsTo<T>>`.
- `PointsToUnaligned<X>` (`X` is `T`, `[T]`, or `str` in rustlib): a `PointsToUntyped` (the bytes) and a `TypedValue<X>` (the possibly-valid value).
- `PointsTo<X>`: a `PointsToUnaligned<X>` at an aligned address.
- `PointsToRaw`: a map from addresses to `PointsToByte`s with one provenance.

Well-formedness is an explicit `wf()`, not a type invariant.
Every well-formed permission is for a real pointer (`ptr@.is_real`).
`str::inv()` (valid UTF-8) stands in for `str`'s type invariant and is part of a `PointsTo<str>`'s `wf()`.

## Trusted design

1. **`PointsTo` and `PointsToUnaligned` are verified code.**
   Trusted functions are stated over a permission's parts (`PointsToUntyped`, `TypedValue<T>`),
   related by the trusted spec fns `pt_parts_wf*`;
   the `PointsTo` versions are verified wrappers.
2. **Shared references are `Tracked<&T>`**, with their pointer as shadow data (`shared_ref_ptr(shadow_data(r))`),
   in place of `&PointsTo<T>`.

## Trusted files

- **vstd `raw_ptr/`:** `ptr_model.rs`, `ptr_specs.rs`, `abstract_bytes.rs`, `points_to_model.rs`, `points_to_structs.rs`.
  The verified files are `points_to_ops.rs`, `ptr_verified_specs.rs` and `points_to_collections.rs`;
  they use the structs only through the trusted files' accessors and field primitives,
  and nothing in the trusted files depends on them.
- **vstd, elsewhere:** the tracked operations in `seq.rs`, `slice.rs`, `map.rs` and `modes.rs`;
  `type_representation.rs`; `layout.rs`; builtin's `shr_ref_struct_wrap`.
- **rustlib:** `proofs/str.rs` (the `str` versions);
  the reference-to-pointer casts in `core/src/ptr/mod.rs`, `core/src/slice/mod.rs` and `core/src/str/mod.rs`;
  `Box` in `alloc/src/boxed.rs`; `specs/slice_index.rs` (definitional axioms); `read_unaligned_verus`.
