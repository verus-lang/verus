Update other vstd files from raw ptr overhaul (e.g., `MemContents` -> `TypedValue`):
- `examples/cells.rs`
- `examples/doubly_linked.rs`
- `examples/even_cell.rs`
- `examples/rfmig_script.rs`
- `examples/state_machines/tutorial/pcell_example.rs`
- `examples/statics.rs`
- `source/rust_verify_test/tests/cell_lib.rs`
- `source/rust_verify_test/tests/raw_ptrs.rs`
- `source/rust_verify_test/tests/syntax_attr.rs`
- `source/vstd/cell.rs`
- `source/vstd/cell/pcell.rs`
- `source/vstd/cell/pcell_maybe_uninit.rs`
- `source/vstd/invariant.rs`
- `source/vstd/simple_pptr.rs`
- `source/vstd/vstd.rs`
- `source/vstd/std_specs/alloc.rs`
- `source/vstd/std_specs/maybe_uninit.rs`

New iterator examples/support:
- `examples/hillel.rs`
- `examples/iterator-clients.rs`
- `examples/knights_tour.rs`
- `source/rust_verify_test/tests/iterators.rs`
- `source/rust_verify_test/tests/loops.rs`
- `source/rust_verify_test/tests/seqs.rs`

Miscellaneous:
- `source/builtin/src/lib.rs`:
  - Rearrange cfgs to apply `not(verus_verify_core)` to some of them.
  - Make `Tracked` and `Ghost` `?Sized`.
- `source/rust_verify_test/tests/core_special_setup.rs`
  - Add assume_specs in test for cfg'd out definitions
  - TODO: make sure they match rustlib defs

Extend cheat-checking support:
- `source/builtin_macros/src/enum_synthesize.rs`
- `source/builtin_macros/src/syntax.rs` (plus fixing bare `vstd` emitted by loop desugaring)

Shadow data
(original PR, PR adding proof support, my soundness fixes):
- `source/builtin/src/lib.rs`:
- `source/rust_verify/src/attributes.rs`
- `source/rust_verify/src/fn_call_to_vir.rs`
- `source/rust_verify/src/rust_to_vir_base.rs`
- `source/rust_verify/src/rust_to_vir_expr.rs`
- `source/rust_verify/src/rust_to_vir_func.rs`
- `source/rust_verify/src/trait_conflicts.rs`
- `source/rust_verify/src/verus_items.rs` (`ShadowData`)
- `source/rust_verify_test/tests/shadow_data.rs`
- `source/vir/src/ast.rs`
- `source/vir/src/ast_to_sst.rs`
- `source/vir/src/ast_to_sst_crate.rs`
- `source/vir/src/ast_to_sst_func.rs`
- `source/vir/src/ast_util.rs`
- `source/vir/src/bitvector_to_air.rs`
- `source/vir/src/context.rs`
- `source/vir/src/datatype_to_air.rs`
- `source/vir/src/def.rs`
- `source/vir/src/expand_errors.rs`
- `source/vir/src/heuristics.rs`
- `source/vir/src/interpreter.rs`
- `source/vir/src/lib.rs`
- `source/vir/src/modes.rs`
- `source/vir/src/patterns.rs`
- `source/vir/src/poly.rs`
- `source/vir/src/prelude.rs`
- `source/vir/src/printer.rs`
- `source/vir/src/prune.rs`
- `source/vir/src/recursion.rs`
- `source/vir/src/resolution_types.rs`
- `source/vir/src/resolve_axioms.rs`
- `source/vir/src/shadow_data.rs`
- `source/vir/src/sst.rs`
- `source/vir/src/sst_elaborate.rs`
- `source/vir/src/sst_to_air.rs`
- `source/vir/src/sst_to_air_func.rs`
- `source/vir/src/sst_util.rs`
- `source/vir/src/sst_vars.rs`
- `source/vir/src/sst_visitor.rs`
- `source/vir/src/triggers.rs`
- `source/vir/src/triggers_auto.rs`

Support for `mut_ref_ptr` and fix mut ref permissions
(should just be from those two commits):
- `source/builtin/src/lib.rs`
- `source/rust_verify/src/fn_call_to_vir.rs`
- `source/rust_verify/src/rust_to_vir_expr.rs`
- `source/rust_verify/src/verus_items.rs` (`SpecPtrAddr`, `MutRefPtr`)
- `source/rust_verify_test/tests/mut_refs_ptrs.rs`
- `source/vir/src/ast.rs`
- `source/vir/src/ast_simplify.rs`
- `source/vir/src/ast_to_sst.rs`
- `source/vir/src/ast_visitor.rs`
- `source/vir/src/bitvector_to_air.rs`
- `source/vir/src/closures.rs`
- `source/vir/src/def.rs`
- `source/vir/src/early_exit_cf.rs`
- `source/vir/src/heuristics.rs`
- `source/vir/src/interpreter.rs`
- `source/vir/src/modes.rs`
- `source/vir/src/patterns.rs`
- `source/vir/src/poly.rs`
- `source/vir/src/prelude.rs`
- `source/vir/src/prune.rs`
- `source/vir/src/resolution_inference.rs`
- `source/vir/src/sst_to_air.rs`
- `source/vir/src/sst_util.rs`
- `source/vir/src/triggers.rs`
- `source/vir/src/triggers_auto.rs`

Workaround (do NOT add to main):
- `source/rust_verify/src/attributes.rs`, allow unsafe attributes

Delete `SharedReference`:
- `source/rust_verify/src/verus_items.rs`

TODO: update tests to match new raw_ptr

Already on main, as far as I can tell: 
- `source/rust_verify_test/tests/traits.rs`
- `source/vir/src/traits.rs`

Unsure:
- `source/vstd/Cargo.lock`

Arithmetic:
- `source/vstd/arithmetic/div_mod.rs`
- `source/vstd/arithmetic/power2.rs`

Endian:
- `source/vstd/endian.rs`

Add cfg:
- `source/vstd/laws_cmp.rs`
- `source/vstd/laws_eq.rs`
- `source/vstd/layout.rs`

Delete before merge:
- `raw_ptr_old.rs`
- `raw_ptr_popl.rs`

# Proposed PR series into main (preliminary)

Based on the pre-merge diff; redo the split after merging main
(some categories may turn out to be drift, e.g. iterators, parts of `seq.rs`).
Build each PR branch from post-merge verify-rustlib (file subsets / cherry-picks).
`builtin/src/lib.rs` hunks are split by hand across PRs 2, 3, 4 and 5.

Out of this series:
- Cheat-checking: cherry-picked from a separate, unmerged PR.
  Push the follow-up changes made here (incl. the bare-`vstd` loop-desugaring fix?) back to that PR.
- Iterator examples/tests: probably already on main; check after the merge.
- Workaround, delete-before-merge files, `traits.rs` (already on main), `Cargo.lock` (probably drop).

1. Arithmetic + endian (`div_mod.rs`, `power2.rs`, `endian.rs`). Independent.
2. `verus_verify_core` cfgs: `builtin` cfg rearrangement, `laws_cmp.rs`, `laws_eq.rs`, `layout.rs`, `core_special_setup.rs`.
   Independent. Resolve the "match rustlib defs" TODO first.
3. Shadow data (compiler). Original PR + proof support + soundness fixes as one PR, separate commits.
   If too big, split into syntax/attributes/`rust_to_vir` and `vir` AST → SST → AIR.
4. `mut_ref_ptr` + mut ref permission fix (compiler). Independent of 3; both branch from main, in parallel.
   - Includes `spec_ptr_addr` in main's `raw_ptr.rs` (the compiler looks it up as `vstd::raw_ptr::spec_ptr_addr`; the new `raw_ptr` keeps that path).
     The vstd API changes from "mut ref issues" (`cast_mut_ref_to_ptr` returning `Tracked<&mut T>`, etc.) go in 7, not here.
   - Whichever of 3/4 lands second rebases: both add a `UnaryOp` variant to the same match arms
     (`interpreter.rs`, `triggers.rs`, `triggers_auto.rs`), plus possibly adjacent items in `builtin`, `verus_items.rs`, `ast.rs`.
PRs 1–6 can run in parallel.

5. `Tracked`/`Ghost: ?Sized` (`builtin`) + `modes.rs`: `tracked_ref`, `TrivialOwnership` + impls, `tracked_from_spec`
   (the new axioms take `T: ?Sized`, so they need the `builtin` change).
6. Tracked `Seq` and slice operations:
   - `seq.rs`: `tracked_borrow_mut`, `tracked_borrow_subrange(_mut)`, `tracked_split_borrow_mut` (`external_body`),
     `tracked_add_borrow(_mut)` (axioms), `tracked_skip`, `tracked_add` (proved).
   - `slice.rs`: `tracked_slice_index`, `tracked_slice_subrange`.
   - Overlap with main (since the branch point): main added `Seq::tracked_borrow_mut` and slice `tracked_borrow`/`tracked_borrow_mut`;
     dedupe against them after the merge (`tracked_slice_index` ≈ main's slice `tracked_borrow`).
   - Not here: `slice.rs` cfgs (→ 2); `slice_index_get`'s commented-out diagnostic item and `const` (from the shadow data commit; check why).
7. Raw pointers, as one PR with two commits so tests never break (squash-merged, so commit 1 needn't build alone). After 3, 4, 5, 6.
   - Commit 1 (the one reviewers look at): `raw_ptr/`, `SharedReference` deletion.
     - Excludes `type_representation_implements_encode_decode` and the two
       "borrow `[T]` as one bigger integer" functions in `points_to_ops.rs` (move to 8),
       so `abstract_bytes_encode`/`decode` are uninterpreted here.
     - Prerequisite on verify-rustlib: move `AbstractByte` (+ methods) from `type_representation.rs` to `raw_ptr/abstract_bytes.rs`,
       with `pub use` in `type_representation.rs` so rustlib imports keep working.
   - Commit 2: downstream updates (`MemContents` → `TypedValue` list above: cells, `simple_pptr`, `invariant.rs`,
     `std_specs`, examples, tests).
8. Type representation + transmute: `type_representation.rs`, `transmute.rs`, the bridging axiom,
   the two bigger-integer borrow functions (which also use `TrivialOwnership` from 5). After 7.
   rustlib needs this before building against main.