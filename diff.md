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