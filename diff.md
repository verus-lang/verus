Categories are from `git diff main...HEAD` after merging main at 6760bfc46 (2026-11-21).
Main has since moved on (to cc615f27c); see "Before building PR branches" below.

Update other vstd files from raw ptr overhaul (e.g., `MemContents` -> `TypedValue`):
- `examples/cells.rs`
- `examples/doubly_linked.rs`
- `examples/even_cell.rs`
- `examples/rfmig_script.rs`
- `examples/state_machines/tutorial/pcell_example.rs`
- `examples/statics.rs`
- `source/rust_verify_test/tests/cell_lib.rs`
- `source/rust_verify_test/tests/exec_spec_unverified.rs` (1 test `#[ignore]`d)
- `source/rust_verify_test/tests/exec_spec_verified.rs` (2 tests `#[ignore]`d)
- `source/rust_verify_test/tests/raw_ptrs.rs`
- `source/rust_verify_test/tests/syntax_attr.rs`
- `source/vstd/atomic.rs` (`from_ptr_*` specs: `is_init` -> `is_valid` + `wf()`; the cfgs go in "Add cfg")
- `source/vstd/cell.rs`
- `source/vstd/cell/pcell_maybe_uninit.rs`
- `source/vstd/contrib/exec_spec/mod.rs` (`mem_contents.rs` commented out)
- `source/vstd/simple_pptr.rs`
- `source/vstd/std_specs/alloc.rs`
- `source/vstd/std_specs/maybe_uninit.rs`

New iterator examples/support (commit 37cd71da7; the rest of the iterator work is on main):
- `examples/hillel.rs`
- `examples/iterator-clients.rs`
- `examples/knights_tour.rs`
- `source/vstd/std_specs/option.rs`: `ExIntoIter`, `into_iter_opt`, `Option::into_iter` spec

Miscellaneous:
- `source/builtin/src/lib.rs`:
  - Rearrange cfgs to apply `not(verus_verify_core)` to some of them.
  - Make `Tracked` and `Ghost` `?Sized`.
- `source/rust_verify_test/tests/core_special_setup.rs`
  - Add assume_specs in test for cfg'd out definitions
  - TODO: make sure they match rustlib defs

Cheat-checking:
- On main as of cc615f27c ("Add support for nuanced no-cheating policies", #2568),
  including `enum_synthesize.rs`, `syntax.rs` (with the bare-`vstd` loop-desugaring fix),
  `no_cheating.rs` and `assumptions_allowed` in `well_formed.rs`.
- At the next merge, take main's version of `well_formed.rs`'s cheat-checking code.
  This drops the branch-only exemption letting `assumptions_allowed` functions use
  `#[verifier::assume_compatibility_with_trait_spec]` under `--no-cheating` (unused in vstd and rustlib).

Shadow data
(original PR, PR adding proof support, my soundness fixes):
- `source/builtin/src/lib.rs`:
- `source/rust_verify/src/attributes.rs`
- `source/rust_verify/src/automatic_derive.rs` (`has_shadow_data`)
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
- `source/vir/src/recursive_types.rs` (`Primitive::ShadowData`)
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
- `source/vstd/std_specs/iter.rs` (`cfg_attr(verus_verify_core, verifier::shadow_data)` on `next`)

Support for `mut_ref_ptr` and fix mut ref permissions
(should just be from those two commits):
- `source/builtin/src/lib.rs`
- `source/rust_verify/src/erase.rs` (`MutRefPtr`)
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
- `source/rust_verify/src/attributes.rs`: `rustc_nonnull_optimization_guaranteed`
  and `rustc_layout_scalar_valid_range_start/end` in `RUSTC_ATTRS_OK_TO_IGNORE`

Delete `SharedReference`:
- `source/rust_verify/src/verus_items.rs`

TODO: update tests to match new raw_ptr
(mostly done in #3577; left: `mem_contents.rs` and the 3 ignored `exec_spec` tests)

Already on main after the merge:
- `source/rust_verify_test/tests/traits.rs`, `source/vir/src/traits.rs`
- iterator tests (`iterators.rs`, `loops.rs`, `seqs.rs`)
- `source/vstd/invariant.rs`, `source/vstd/cell/pcell.rs`
- `Seq::tracked_borrow_mut`

Unsure:
- `source/vstd/Cargo.lock`

Arithmetic:
- `source/vstd/arithmetic/div_mod.rs`
- `source/vstd/arithmetic/power2.rs`

Endian:
- `source/vstd/endian.rs`

Other proved lemmas:
- `source/vstd/wrapping.rs`: `count_ones`, `lemma_count_ones_is_pow2` (+ group)
- `source/vstd/utf8.rs`: `is_char_boundary_split`, `valid_utf8_subrange`
- `source/vstd/map.rs`: stronger ensures (`final(self).dom() == key_map.dom()`)
- `source/vstd/resource/impls/map.rs`: two asserts in a proof

Add cfg:
- `source/vstd/atomic.rs`
- `source/vstd/laws_cmp.rs`
- `source/vstd/laws_eq.rs`
- `source/vstd/layout.rs` (only the cfgs; see "Layout axioms")
- `source/vstd/slice.rs` (cfgs, plus `axiom_slice_ext_equal` using `@.len()`)
- `source/vstd/std_specs/core.rs` (`Deref`, `Index`, `Option`, `Result`)
- `source/vstd/std_specs/option.rs`
- `source/vstd/std_specs/result.rs`
- `source/vstd/std_specs/slice.rs`
- `source/vstd/std_specs/vec.rs`
- `source/vstd/std_specs/vecdeque.rs`
- `source/vstd/vstd.rs` (`simple_pptr`)

Layout axioms (`source/vstd/layout.rs`, beyond the cfgs):
- `layout_for_val_is_valid` takes `&V` instead of `Tracked<&V>` (API change)
- new axiom `layout_of_sized`
- `layout_of_str` (non-core) specifies `spec_size_of_val` from the bytes
- new axiom: a pointer to an unsized type is its metadata plus a `usize` ("unstable assumption")

New axioms outside raw_ptr:
- `source/vstd/std_specs/control_flow.rs`: `spec_from_from_spec` (`admit()`, in `group_control_flow_axioms`)
- `source/vstd/std_specs/option.rs`: `Option::tracked_mut_borrow`
- `source/vstd/modes.rs`, `seq.rs`, `slice.rs`, `type_representation.rs`, `transmute.rs`, layout (above)
Delete before merge:
- `raw_ptr_old.rs`
- `raw_ptr_popl.rs`

# Proposed PR series into main (preliminary)

Build each PR branch from post-merge verify-rustlib (file subsets / cherry-picks).
`builtin/src/lib.rs` hunks are split by hand across PRs 2, 3, 4 and 5.

Before building PR branches: merge main again (cc615f27c or later).
Main's new commits include the no-cheating PR (#2568),
a shadow-variable closure fix (#3585), `CrateId`s robust to phony vstd/core/alloc (#3574)
and the `rustc_hir_typeck` fork, which may touch PRs 2 and 3.

Out of this series:
- Cheat-checking: on main (#2568); the branch-only exemption is dropped at the next merge.
- Iterator examples + `Option::into_iter` spec (37cd71da7): a small standalone PR, or drop.
- Workaround, delete-before-merge files, `Cargo.lock` (probably drop).

1. Arithmetic, endian and other proved lemmas (`div_mod.rs`, `power2.rs`, `endian.rs`,
   `wrapping.rs` `count_ones`, `utf8.rs`, `map.rs`, `resource/impls/map.rs`). Independent.
   `endian.rs` includes `digit_to_int`, the workaround for the `CastToInteger` bug (main's #2908);
   it can be removed once upstream fixes the bug (not urgent).
2. `verus_verify_core` cfgs: `builtin` cfg rearrangement and the "Add cfg" list, `core_special_setup.rs`.
   Independent. Resolve the "match rustlib defs" TODO first.
3. Shadow data (compiler). Original PR + proof support + soundness fixes as one PR, separate commits.
   If too big, split into syntax/attributes/`rust_to_vir` and `vir` AST → SST → AIR.
   Includes `iter.rs`'s `cfg_attr(verus_verify_core, verifier::shadow_data)` on `Iterator::next`.
4. `mut_ref_ptr` + mut ref permission fix (compiler). Independent of 3; both branch from main, in parallel.
   - Includes `spec_ptr_addr` in main's `raw_ptr.rs` (the compiler looks it up as `vstd::raw_ptr::spec_ptr_addr`; the new `raw_ptr` keeps that path).
     The vstd API changes from "mut ref issues" (`cast_mut_ref_to_ptr` returning `Tracked<&mut T>`, etc.) go in 7, not here.
   - Whichever of 3/4 lands second rebases: both add a `UnaryOp` variant to the same match arms
     (`interpreter.rs`, `triggers.rs`, `triggers_auto.rs`), plus possibly adjacent items in `builtin`, `verus_items.rs`, `ast.rs`.
PRs 1–7 can run in parallel.

5. `Tracked`/`Ghost: ?Sized` (`builtin`) + `modes.rs`: `tracked_ref`, `TrivialOwnership` + impls, `tracked_from_spec`
   (the new axioms take `T: ?Sized`, so they need the `builtin` change).
6. Tracked `Seq`, slice and `Option` operations:
   - `seq.rs`: `tracked_borrow_subrange(_mut)`, `tracked_split_borrow_mut` (`external_body`),
     `tracked_add_borrow(_mut)` (axioms), `tracked_skip`, `tracked_add` made `pub` (proved).
   - `slice.rs`: `tracked_slice_index`, `tracked_slice_subrange`.
   - `option.rs`: `Option::tracked_mut_borrow` (axiom).
   - Dedupe against main's slice `tracked_borrow`/`tracked_borrow_mut` (`tracked_slice_index` ≈ `tracked_borrow`).
   - Not here: `slice.rs` cfgs (→ 2); `slice_index_get`'s commented-out diagnostic item and `const` (from the shadow data commit; check why).
7. Other vstd specs and axioms (none depend on raw_ptr). Independent.
   - `layout.rs` ("Layout axioms" above): `layout_for_val_is_valid` takes `&V` (no users in vstd),
     `layout_of_sized`, `layout_of_str`'s size, the pointer-metadata axiom
     (the last two axioms are used by `type_representation.rs`, in 9).
   - `control_flow.rs`: `spec_from_from_spec` (axiom via `admit()`).
   - `std_specs/core.rs`: `ExThin` (used by `raw_ptr/ptr_specs.rs`, in 8).
8. Raw pointer overhaul, as one PR with two commits so tests never break (squash-merged, so commit 1 needn't build alone). After 3, 4, 5, 6, 7.
   - Commit 1 (the one reviewers look at): `raw_ptr/`, `SharedReference` deletion, `group_points_to_lemmas` in `vstd.rs`.
     - Excludes `type_representation_implements_encode_decode` and the two
       "borrow `[T]` as one bigger integer" functions in `points_to_ops.rs` (move to 9),
       so `abstract_bytes_encode`/`decode` are uninterpreted here.
     - Prerequisite on verify-rustlib: move `AbstractByte` (+ methods) from `type_representation.rs` to `raw_ptr/abstract_bytes.rs`,
       with `pub use` in `type_representation.rs` so rustlib imports keep working.
   - Commit 2: downstream updates (`MemContents` → `TypedValue` list above: cells, `simple_pptr`, `atomic.rs`,
     `std_specs`, `exec_spec`, examples, tests).
     Port `exec_spec/mem_contents.rs` to `TypedValue` and un-ignore its 3 tests, or call them out in the PR description.
9. Type representation + transmute: `type_representation.rs`, `transmute.rs` (+ their `vstd.rs` modules), the bridging axiom,
   the two bigger-integer borrow functions (which also use `TrivialOwnership` from 5). After 8.
   rustlib needs this before building against main.
