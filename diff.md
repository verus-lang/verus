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
- `source/vstd/bits.rs`: `nat_count_ones` (moved from `std_specs/bits.rs`; no re-export), `lemma_nat_count_ones_pos`, `lemma_nat_count_ones_is_pow2`
  (replaces verify-rustlib's per-type `count_ones` / `lemma_count_ones_is_pow2` / `group_count_ones_is_pow2` in `wrapping.rs`, which duplicated main's `nat_count_ones` from #3513)
- `source/vstd/utf8.rs`: `is_char_boundary_split`, `valid_utf8_subrange`
- `source/vstd/map.rs`: stronger ensures (`final(self).dom() == key_map.dom()`)
- `source/vstd/resource/impls/map.rs`: two asserts in a proof (from `mut_ref_ptr`, #2518; in PR 4, not 1)

Add cfg:
- `source/vstd/atomic.rs`
- `source/vstd/laws_cmp.rs`
- `source/vstd/laws_eq.rs`
- `source/vstd/layout.rs` (only the cfgs; see "Layout axioms")
- `source/vstd/slice.rs` (cfgs, plus `axiom_slice_ext_equal` using `@.len()`)
- `source/vstd/seq.rs`, `source/vstd/set.rs` (`#[deprecated]` → `cfg_attr(not(verus_verify_core), deprecated(..))`; Rust 1.100 update)
- `source/vstd/std_specs/cmp.rs` (`min`, `max`, `min_by`, `max_by`, `min_by_key`, `max_by_key`; Rust 1.100 update)
- `source/vstd/std_specs/core.rs` (`Deref`, `Index`, `Option`, `Result`)
- `source/vstd/std_specs/mod.rs` (`char`, `ptr`, `nonzero`; `bits` is in PR 1c; Rust 1.100 update)
- `source/vstd/std_specs/option.rs`
- `source/vstd/std_specs/result.rs`
- `source/vstd/std_specs/slice.rs`
- `source/vstd/std_specs/vec.rs`
- `source/vstd/std_specs/vecdeque.rs`
- `source/vstd/vstd.rs` (`simple_pptr`, `group_nonzero_axioms`, `group_iter_axioms`; `group_bits_axioms` is in PR 1c)

`--is-core` compiler fixes (Rust 1.100 update, uncommitted):
- `source/rust_verify/src/rust_to_vir.rs`: allow `extern crate self as core;` in core (main's #3574 reserves `core` as an `extern crate` alias)
- `source/rust_verify/src/rust_to_vir_expr.rs`: allow `enum as usize` discriminants above `u32::MAX` (MERGE_TODO verus item 8)
- `source/rust_verify/src/config.rs`: allow `--no-cheating` with `--is-core` / `--is-stdlib-outside-of-core` (disallowed by #2568)

Layout axioms (`source/vstd/layout.rs`, beyond the cfgs):
- `layout_for_val_is_valid` takes `&V` instead of `Tracked<&V>` (API change)
- new axiom `layout_of_sized`
- `layout_of_str` (non-core) specifies `spec_size_of_val` from the bytes
- new axiom: a pointer to an unsized type is its metadata plus a `usize` ("unstable assumption")

New axioms outside raw_ptr:
- `source/vstd/std_specs/control_flow.rs`: `spec_from_from_spec` (`admit()`, in `group_control_flow_axioms`)
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

**Opened as PRs:** 1a, 1b, 1c, 3, 4, 5, 6a, 6b, 6c (all reviewable except 1b, a draft).
Still to open: 2, 7, 8, 9.
3, 4, 5 and 6a–c stay as they are; differences with verify-rustlib are fixed on verify-rustlib and in rustlib
(see "Bring verify-rustlib in line with the opened PRs" below).

1. Proved lemmas (three independent PRs):
   - 1a. Small lemmas (`pr-vstd-misc-lemmas`): `div_mod.rs`, `power2.rs`, `utf8.rs`, `map.rs`.
   - 1b. Endian (`pr-vstd-endian`, draft): `endian.rs`.
   - 1c. `count_ones` (`pr-vstd-count-ones`): `nat_count_ones` moves to `bits.rs` (breaking path change), plus two lemmas.
     Also cfgs out `std_specs::bits` and `group_bits_axioms` under `verus_verify_core`,
     which the move makes possible, so PR 2 doesn't depend on 1c
     (uncommitted, in worktree `.claude/worktrees/pr-count-ones`).
   - Delete the superseded `pr-vstd-arithmetic` remote branch.
2. `verus_verify_core` cfgs: `builtin` crate-level feature cfg rearrangement and the "Add cfg" list,
   `core_special_setup.rs` (its `Option`/`Result`/`unwrap`/`len` specs, not its `Tracked` `Deref` impls).
   Also takes `option.rs`'s `#[cfg(not(verus_verify_core))]` on `Option::as_mut` (the other half of #2609; see 1a).
   Independent. Resolve the "match rustlib defs" TODO first.
   `Tracked`'s `Deref`/`DerefMut` cfgs and the test's matching impls go in 5, so 2 and 5 can merge in either order.
   Includes the Rust 1.100 update's cfgs (marked in the "Add cfg" list).
   Also resolve `slice_index_get`'s diagnostic item (commented out in #2634, reason unknown; `SliceIndexGet` is registered but unused):
   it's still commented out on verify-rustlib-update-1.100.0.
   Uncomment it there; if vstd and rustlib core build, PR 2 leaves it as on main, otherwise PR 2 carries the comment-out with a reason.
3. Shadow data (compiler): original PR + proof support + soundness fixes, plus `Iterator::next`'s `shadow_data` cfg_attr.
4. `mut_ref_ptr` + mut ref permission fix (compiler), plus `spec_ptr_addr` in main's `raw_ptr.rs`.
   Whichever of 3/4 lands second rebases (both add a `UnaryOp` variant to the same match arms).
5. `Tracked`/`Ghost: ?Sized` + `modes.rs` axioms (`tracked_ref`, `TrivialOwnership`, `tracked_from_spec`) + `Tracked`'s `Deref` cfgs.
6. vstd specs and axioms needed by 8 (three independent PRs):
   - 6a. Layout axioms (`pr-vstd-layout`): `layout.rs`.
   - 6b. Miscellaneous specs (`pr-vstd-misc-specs`): `control_flow.rs`, `std_specs/core.rs`, `option.rs`, `slice.rs`.
   - 6c. `Seq` borrows (`pr-vstd-seq-borrows`): `seq.rs`.
   Callers of 6b's and 6c's renamed and dropped functions are listed under 8 and 9.
7. `--is-core` compiler fixes (the list above), one commit each. Independent.
   Before opening: resolve MERGE_TODO verus item 8 (check the target's pointer width, not just `--is-core`),
   and state why rustlib needs `--no-cheating` with `--is-core` (it loosens #2568's rule;
   could be a separate PR if it should go to #2568's reviewers on its own).
8. Raw pointer overhaul, as one PR with two commits so tests never break (squash-merged, so commit 1 needn't build alone). After 3, 4, 5, 6a–c.
   - Commit 1 (the one reviewers look at): `raw_ptr/`, `SharedReference` deletion, `group_points_to_lemmas` in `vstd.rs`.
     - Excludes `type_representation_implements_encode_decode` and the two
       "borrow `[T]` as one bigger integer" functions in `points_to_ops.rs` (move to 9),
       so `abstract_bytes_encode`/`decode` are uninterpreted here.
     - Prerequisite on verify-rustlib: move `AbstractByte` (+ methods) from `type_representation.rs` to `raw_ptr/abstract_bytes.rs`,
       with `pub use` in `type_representation.rs` so rustlib imports keep working.
   - Commit 2: downstream updates (`MemContents` → `TypedValue` list above: cells, `simple_pptr`, `atomic.rs`,
     `std_specs`, `exec_spec`, examples, tests),
     including main's tests ported to the new API (`atomic_lib.rs`, `std.rs`, `raw_ptrs.rs` `ptr_ref2_lifetime`)
     and the `examples/state_machines/dist_rwlock.rs` proof fix (fragile with the new `group_raw_ptr_axioms`).
     Port `exec_spec/mem_contents.rs` to `TypedValue` and un-ignore its 3 tests, or call them out in the PR description.
   - Callers to update for 6b's and 6c's renames and removals (do this on verify-rustlib first):
     - `tracked_slice_index` (dropped) → main's `slice::tracked_borrow`: `raw_ptr/points_to_ops.rs` (2 calls).
     - `Seq::tracked_skip` (dropped; duplicates `tracked_split_at`) → `tracked_split_at`: `raw_ptr/points_to_ops.rs` (1 call).
     - `Seq::tracked_split_borrow_mut` → `tracked_borrow_mut_split` (matches `Map`/`IMap`):
       `raw_ptr/points_to_collections.rs` (3 calls), `raw_ptr/points_to_ops.rs` (1 call).
9. Type representation + transmute: `type_representation.rs`, `transmute.rs` (+ their `vstd.rs` modules), the bridging axiom,
   the two bigger-integer borrow functions (which also use `TrivialOwnership` from 5). After 8.
   rustlib needs this before building against main.
   - Callers to update for 6b's renames and removals:
     - `tracked_slice_index` (dropped) → main's `slice::tracked_borrow`: `type_representation.rs` (1 call).
     - rustlib: `Option::tracked_mut_borrow` → `tracked_borrow_mut` in `alloc/src/raw_vec/mod.rs` (1 call).

# Bring verify-rustlib in line with the opened PRs (not done yet)

Checked 2026-11-25 against verify-rustlib-update-1.100.0.
1a and 1c match; 3, 4 and 5 differ only by each other's hunks, PR 2's and the workaround.
Take each PR's version of its files, then:
- 6b, `spec_from_from_spec` is weaker: it now also requires `<S as FromSpec<T>>::obeys_from_spec()`.
  rustlib's `grow_amortized` (`alloc/src/raw_vec/mod.rs`) uses it,
  and `obeys_from_spec` for `FromSpecImpl<TryReserveErrorKind> for TryReserveError` (`alloc/src/collections/mod.rs`) is `closed`,
  so rustlib probably needs it `open` or a lemma (a rustlib spec change: propose it first).
- 6b, `Option::tracked_borrow_mut` (renamed, now proved), `slice::tracked_borrow_subrange` (renamed, no callers),
  `tracked_slice_index` dropped: callers under 8 and 9.
- 6c, `seq.rs`: `tracked_borrow_subrange` becomes an axiom and `tracked_borrow_subrange_mut` is proved
  (both `external_body` here), plus the renames and removal under 8.
- 6a, `layout.rs`: the `StringSliceAdditionalSpecFns` import's cfg is `all(verus_keep_ghost, not(verus_verify_core))`,
  and `layout_of_sized` and some comments moved. No callers affected.
- Doc comments only: `endian.rs` (1b: `digit_to_int`, `to_big_from_digits_single`), `modes.rs` (5: `tracked_ref`).
