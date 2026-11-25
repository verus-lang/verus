# Merge decisions: `main` (6760bfc46) into `verify-rustlib-update-1.100.0`

Merge base: 455695049 ("Remaining uninhab issues (#2501)").
**Ours** = HEAD (verify-rustlib side), **main** = MERGE_HEAD.
Each conflict hunk shows ours, main and the final text.
Judgment calls are marked **[decision]**; the rest are unions of independent changes.

## Status (resume here)

As of 2026-11-20.

**Where it stands**
- All conflicts are resolved in the working tree, and the compiler builds.
- vstd verification has 5 failures, which are deliberately left out of the merge commit
  (see [vstd verification status](#vstd-verification-status-at-the-merge-commit-5-failures-to-fix-in-follow-up-commits)).
- Nothing has been committed.
  Resolved files are still unmerged (`UU`) in git, except `source/vstd/raw_ptr.rs`, which is staged as deleted.
  The merge is still in progress (`MERGE_HEAD` = 6760bfc46).
- This file is untracked.

**Environment**
- z3 is now 4.16.0 (`source/tools/get-z3.sh`), because main requires it.
- `source/target-verus` holds a vstd built with `--vstd-no-verify` (from the cast-bug experiments).
  `source/tools/build-expand-errors.sh` rebuilds and verifies it.

**Next steps, in order**
1. Review: the merge decisions (the conflict sections) were approved on 2026-11-20.
   **Next: review the [build fixes](#build-fixes-auto-merged-code-that-no-longer-compiles-against-main) section.**
   The approved **[decision]** items, for reference:
   - `extra_rets` in SST, for shadow-data returns.
   - `builtin/src/lib.rs` crate attributes.
   - `SpecItem::AtomicSpec` in `no_cheating.rs`'s header list.
   - The `assumptions_allowed` gate on `assume_compatibility_with_trait_spec` (`well_formed.rs`).
   - Dropped iterator tests (`iterators.rs`, main's version).
   - The `std_specs/iter.rs` shadow_data attribute.
   - SliceIndex: main's design, with our `verus_verify_core` guards (also on main's new `[T]` method specs).
   - The ported trusted specs in `atomic.rs`.
   - `seq.rs`: main's `tracked_add` made `pub`.
   - `MemContents` exec_spec taken out of the build.
2. After approval, `git add` the resolved files.
   The user commits the merge.
3. Work through [Follow-ups after the merge commit](#follow-ups-after-the-merge-commit).

## Follow-ups after the merge commit

This is the only list of follow-ups; the sections below point here.

**Verification failures (fix in commits on this branch)**

1. **[done: vstd workaround]** `CastToInteger` bug from main's #2908: 4 vstd failures, also in `test_is_core`
   (details in [vstd verification status](#vstd-verification-status-at-the-merge-commit-5-failures-to-fix-in-follow-up-commits)).
   Not limited to closures: any `d as int` (generic `d: B`) used as a boxed `int` loses its `int` facts.
   Repro (`B: Integer`): `assert(s.map(|i, d: B| d as int).len() == s.len())` fails,
   and so do `let t = s.push(d as int); assert(t.len() == s.len() + 1)` and `assert(t.last() == d as int)` (`s: Seq<int>`);
   `(d as int) + 0` and `Some(d as int)` verify.
   Workaround: new `pub open spec fn digit_to_int<B: Integer>(d: B) -> int { d as int }` in `endian.rs`,
   called in the 4 closures instead of `d as int`
   (`to_endian_from_digits`, `to_big_from_digits`, `to_big_from_digits_single`'s requires, `lemma_bytes_to_endian_digits`' ensures).
   main's `poly.rs` is unchanged. Report upstream (item 6).
2. **[done]** Flaky `GhostSubseq::agree_map` (`resource/impls/seq.rs:243`, main's code).
   Fixed in the proof: the `assert forall` now states the postcondition itself
   (`self@.len()`, `self.off()`, `self@[i]`) and asserts `self@[i] == self.frac@[self.off + i]`,
   so it no longer depends on Z3 unfolding `view`'s `Seq::new`.
   Upstream could take the same change.
3. **[done]** `test_is_core`: core-only failure at `std_specs/iter.rs:1349`,
   main's `exists |m: &mut I| (I::next).ensures((m,), ret) && ...`,
   with our `#[cfg_attr(verus_verify_core, verifier::shadow_data)]` on `Iterator::next`.
   Cause (a bug in our shadow-data code that main's new spec exposed): in `sst_util.rs` `sst_call_requires` / `sst_call_ensures`,
   the tuple *type* was built from all of `func.x.pars` (including shadow parameters),
   but the argument tuple from only the first `n_orig_params` arguments,
   so a call to a `shadow_data` function assumed `call_ensures` at the wrong tuple type.
   Fix: build the tuple type from the first `n_orig_params` parameters too, in both functions.
   Kept the `no_extra_parameters` guard on the generic requires in `sst_to_air.rs`:
   the `call_requires` / `call_ensures` axioms are disabled for functions with extra parameters (`sst_to_air_func.rs`),
   so without the guard a caller could meet the precondition with an unrelated `call_requires`.
   New test `shadow_data.rs` `test_call_ensures_after_call` (`let r = f(a); assert(call_ensures(f, (a,), r))`);
   without the fix, Verus panics on it (`sst_to_air.rs:516`, the 2-tuple type is undeclared).
   `test_is_core` and all `shadow_data.rs` tests pass.

**Testing**

4. **[done, after merging main at cc615f27c]** Ran all of `rust_verify_test` (`vargo test --release -p rust_verify_test --no-fail-fast`).
   Everything passes except:
   - Fixed: main's tests on the old `raw_ptr` API, ported to the new one (`is_init` → `is_valid`, `is_uninit` → `is_empty`, plus `wf()`):
     `atomic_lib.rs` (4 `from_ptr_*` tests), `std.rs` (`maybe_uninit_write`, `maybe_uninit_array_assume_init`),
     `raw_ptrs.rs` `ptr_ref2_lifetime` (now `ptr_ref` + `ptr_mut_write`; same two lifetime errors).
   - Fixed: `examples/state_machines/dist_rwlock.rs` `RwLock::new` (`s.wf()` failed although every conjunct proved).
     Caused by our vstd, not the compiler: it verifies with main's vstd and our compiler,
     and with our vstd minus `raw_ptr::group_raw_ptr_axioms` in `group_vstd_default`;
     no single axiom of the group is responsible, so the proof is just fragile.
     Fix (main's example, goes with the raw_ptr PR): an `assert forall` before `s` stating the `ref_counts` conjuncts of `wf()`
     in both forms (`constant() == (s.inst, j)` and `.0` / `.1`), and an assert of the `exc_locked` conjuncts.
   - Left: `examples/hillel.rs`, `examples/iterator-clients.rs` (follow-up 10).
   - Environment only (not checked on main): `observer.rs` cvc5 tests (no cvc5 installed),
     `cargo.rs` `cargo_new_*` (no toolchain manifest for the local dev version).
5. Build rustlib against the merged vstd, and port it:
   - main's iterator API: `will_return_none` / `initial_value_relation` → `produces`,
     in `core/src/str/validations.rs`, `alloc/src/vec/into_iter.rs` and `alloc/src/collections/linked_list.rs`.
   - Check that main's unguarded slice `IterMut` / `iter_mut` specs don't clash with rustlib's.
   - Check that rustlib's core builds with the new `builtin/src/lib.rs` attributes
     (it includes `builtin/src/lib.rs` as a module, like `test_is_core`).

   Changes made to this branch while building rustlib's core (Rust 1.100 update) **[decisions]**:
   - `rust_verify/src/config.rs`: `--no-cheating` no longer rejects `--is-core` / `--is-stdlib-outside-of-core`.
     Main's #3392 (8bf68ee74) disallows them on purpose; rustlib verifies core and alloc with `--no-cheating`.
   - `rust_verify/src/rust_to_vir.rs` (`check_extern_crate_alias`, from main's #3279):
     `extern crate self as core;` is allowed under `--is-core` (core's `lib.rs` has it; the macros' `::core::` paths need it).
   - `rust_verify/src/rust_to_vir_expr.rs` (`expr_cast_enum_int_to_vir`, from main's #2770):
     `usize` discriminants above `u32::MAX` are allowed under `--is-core` (rustlib's 64-bit `AlignmentEnum`).
     Checking the target width is `MERGE_TODO.md` verus item 10.
   - vstd `#[deprecated]` attributes in `seq.rs` / `set.rs` → `#[cfg_attr(not(verus_verify_core), deprecated(...))]`
     (core's `staged_api` requires a `since`).
   - `#[cfg(not(verus_verify_core))]` on main-added specs that duplicate rustlib's own:
     the `std_specs::{nonzero, bits, char, ptr}` modules (and the nonzero / bits groups in `group_vstd_default`),
     and the `core::cmp::{min, max, min_by, max_by, min_by_key, max_by_key}` assume_specs in `std_specs/cmp.rs`.
     The goal of gating all of them is rustlib item 5 in `MERGE_TODO.md`.
   - `std_specs::iter::group_iter_axioms` is not in `group_vstd_default` under `verus_verify_core`:
     main's `ExIterator::advance_by` spec uses `NonZero`'s view, which in core reaches modules that `broadcast use group_vstd_default`,
     so the iterator axioms close a cycle; rustlib modules that need them `broadcast use` the group explicitly.

**Upstream reports** (optional; drafts for 6 and 7 in `UPSTREAM_REPORTS.md`, not filed)

6. `CastToInteger` (item 1), with the `s.push(d as int)` repro; once fixed, `digit_to_int` can go.
7. `external_trait_extension` (`builtin_macros/src/syntax_trait.rs`) doesn't copy the trait's `cfg` attributes
   to the generated traits and blanket impl (see the SliceIndex section).
   Possible fix: copy `cfg` / `cfg_attr` attributes to the generated items.
8. `Seq::tracked_add` is private on main; we made it `pub` (used by `raw_ptr/points_to_ops.rs`).
   No separate report: it goes in PR 6, and the reviewer can raise it there.

**Later (candidates for `MERGE_TODO.md`, docs branch `verify-rustlib-refactor`)**

9. Port `contrib/exec_spec/mem_contents.rs` to `TypedValue`, and un-ignore its 3 tests
   (`test_exec_spec_mem_contents`, `test_exec_spec_pptr_permissions`, `test_exec_spec_unverified_misc_forms`).
   The `MemContents` case in `builtin_macros/src/contrib/exec_spec.rs` is left as is.
10. Port the iterator examples `examples/hillel.rs` and `examples/iterator-clients.rs` (commit 37cd71da7) to main's iterator API
    (they use `zip_iterators`, `group_slice_axioms` and `option::axiom_spec_into_iter`; they fail in `examples.rs`).
    Port the 5 dropped iterator tests to main's API
    (`map_`, `filter_`, `take_`, `skip_`, `iter_mut_can_be_implemented`; `git show HEAD:source/rust_verify_test/tests/iterators.rs`).
11. Reconcile vstd's SliceIndex spec with rustlib's, and decide which parts of our design to add back
    (ours is described in `source/vstd/SOUNDNESS_AUDIT.md`).
12. `slice.rs`: our `tracked_slice_index` duplicates main's `tracked_borrow`; switch callers
    (`type_representation.rs`, `raw_ptr/points_to_ops.rs`) and remove it.
13. `SOUNDNESS_AUDIT_ITER.md`: the "Checked and believed fine" list still has
    "`Vec`'s `IterMut` specs and `iter_mut_next_postcondition`", which the merge removed (main's `IterMut` spec replaces them).
14. The deprecated `.finite()` in `raw_ptr/points_to_collections.rs:42` (warning only).

---

## `.gitignore`

Ours:
```
/.vscode/tasks.json
```
Main:
```
/.vscode/tasks.json

source/vstd/Cargo.lock
```
Final: main's (ours made no change here).

## `source/docs/guide/src/tcb.md`

Ours:
```
 * As [`assume`](./requires_ensures.md) statement
 * An axiom - any function introduced with [`#[verifier::external_body]`](./calling-unverified-from-verified.md) or declared as an `axiom fn`
```
Main:
```
 * An [`assume`](./requires_ensures.md) statement
 * An axiom - any proof function introduced with `#[verifier::external_body]`
```
Final (main's first line, our second):
```
 * An [`assume`](./requires_ensures.md) statement
 * An axiom - any function introduced with [`#[verifier::external_body]`](./calling-unverified-from-verified.md) or declared as an `axiom fn`
```

## `source/builtin/src/lib.rs`: crate attributes **[decision]**

Base:
```rust
#![cfg_attr(
    verus_keep_ghost,
    feature(rustc_attrs), feature(negative_impls), feature(unboxed_closures), feature(fn_traits),
    feature(register_tool),
    feature(tuple_trait),
    register_tool(verus),
    register_tool(verifier)
)]
```
Ours:
```rust
#![cfg_attr(
    all(verus_keep_ghost, not(verus_verify_core)),
    feature(rustc_attrs), feature(negative_impls), feature(unboxed_closures), feature(fn_traits),
    feature(register_tool),
    feature(tuple_trait)
)]
#![cfg_attr(verus_keep_ghost, register_tool(verus), register_tool(verifier))]
```
Main:
```rust
#![cfg_attr(
    verus_keep_ghost,
    feature(rustc_attrs), feature(negative_impls), feature(unboxed_closures), feature(fn_traits),
    feature(tuple_trait)
)]
#![cfg_attr(
    // register_tool is only allowed at crate root. Disable this trait during `test_is_core`:
    all(verus_keep_ghost, not(verus_verify_core)),
    feature(register_tool),
    register_tool(verus),
    register_tool(verifier)
)]
```
Both sides handle `verus_verify_core` but in opposite ways:
ours turns the *features* off under `verus_verify_core` and keeps `register_tool(...)` on;
main keeps the features on and turns `register_tool` off.

Final (revised after running `test_is_core`): **both guards**, in one block
(ours turns the features off under `verus_verify_core`, and main's turns `register_tool` off):
```rust
#![cfg_attr(
    all(verus_keep_ghost, not(verus_verify_core)),
    feature(rustc_attrs), feature(negative_impls), feature(unboxed_closures), feature(fn_traits),
    feature(register_tool),
    feature(tuple_trait),
    // register_tool is only allowed at crate root. Disable this trait during `test_is_core`:
    register_tool(verus),
    register_tool(verifier)
)]
```
This is the base version with `all(verus_keep_ghost, not(verus_verify_core))` as the condition.
Why: with ours, `test_is_core` fails with `the #![register_tool] attribute can only be used at the crate root`
(rustc 1.100 rejects it in a non-root module; `builtin/src/lib.rs` is a module in `--is-core` mode).
It isn't needed there anyway: rust_verify adds `-Zcrate-attr=register_tool(verus)` / `(verifier)` itself (`rust_verify/src/config.rs`).
rustlib's core also includes `builtin/src/lib.rs` as a module, so it would hit the same error on 1.100.

`test_is_core` status with this (run with `vargo test --release --vstd-no-verify -p rust_verify_test --test core_special_setup`):
- `register_tool` error: fixed by the above.
- `trait core::slice::index::SliceIndex not declared to Verus` in `vstd/slice.rs`:
  fixed (see the SliceIndex section: `ExSliceIndex` moved into its own `#[cfg(not(verus_verify_core))] verus! { ... }` block).
- Still failing:
  - the 4 known `CastToInteger` failures (follow-up 1);
  - **new, core mode only:** `std_specs/iter.rs:1349` (follow-up 3).
  - `agree_map` did not fail in this run.
  - Also unchanged after guarding main's new `[T]` method specs.

## `source/rust_verify/src/lib.rs`

Ours adds `mod no_cheating;`; main adds `mod observers; mod pre_header;`.
Final: all three.

## `source/rust_verify/src/fn_call_to_vir.rs`

Ours: `BuiltinFunctionItem::ShadowData => unreachable!(),`
Main: `BuiltinFunctionItem::ProofWithCallee => unreachable!(),`
Final: both arms.

---

## `source/vir/src/ast.rs`

### `ExprX::BorrowMut` / `TwoPhaseBorrowMut`
Ours:
```rust
    /// Used only when new-mut-refs is enabled.
    BorrowMut(Place, bool),
    ...
    ///
    /// Used only when new-mut-refs is enabled.
    TwoPhaseBorrowMut(Place, bool),
```
Main (removed the doc lines, since new-mut-refs is always on now):
```rust
    BorrowMut(Place),
    ...
    TwoPhaseBorrowMut(Place),
```
Final: main's docs with our `bool`:
```rust
    BorrowMut(Place, bool),
    ...
    TwoPhaseBorrowMut(Place, bool),
```

### `FunctionAttrsX`
Ours adds `has_shadow_data: bool`; main adds `is_drop: bool` and `has_trivial_clone: bool`.
Final: all three (ours first).

## `source/vir/src/closures.rs`, `source/vir/src/ast_simplify.rs`

Ours: `ExprX::AssignToPlace { place, .. } | ExprX::BorrowMut(place, _)` (and `TwoPhaseBorrowMut(place, _)` in ast_simplify)
Main: `ExprX::Assign { place, .. } | ExprX::BorrowMut(place)` (main renamed `AssignToPlace` → `Assign`)
Final: `ExprX::Assign { place, .. } | ExprX::BorrowMut(place, _)` (plus `TwoPhaseBorrowMut(place, _)`)

## `source/vir/src/heuristics.rs`

Ours:
```rust
            UnaryOp::StrLen | UnaryOp::Length(_) => exp.clone(),
            UnaryOp::ShadowData => exp.clone(),
            UnaryOp::ShadowAddrOf => panic!("unexpected ShadowAddrOf"),
            UnaryOp::InferSpecForLoopIter { .. } => exp.clone(),
```
Main:
```rust
            UnaryOp::NewStrLit | UnaryOp::StrLen | UnaryOp::Length(_) => exp.clone(),
```
(main removed `InferSpecForLoopIter` from `UnaryOp`.)
Final:
```rust
            UnaryOp::NewStrLit | UnaryOp::StrLen | UnaryOp::Length(_) => exp.clone(),
            UnaryOp::ShadowData => exp.clone(),
            UnaryOp::ShadowAddrOf => panic!("unexpected ShadowAddrOf"),
```

## `source/vir/src/triggers_auto.rs`

Ours:
```rust
        ExpX::Unary(UnaryOp::CastToInteger, _) => {
            panic!("internal error: CastToInteger should have been removed before here")
        }
        ExpX::Unary(
            op @ (UnaryOp::MutRefCurrent | UnaryOp::MutRefFuture(_) | UnaryOp::MutRefPtr),
            e1,
        ) => {
```
Main (removed the `CastToInteger` panic; it is now handled later in the same function, `UnaryOp::CastToInteger => 1`):
```rust
        ExpX::Unary(op @ (UnaryOp::MutRefCurrent | UnaryOp::MutRefFuture(_)), e1) => {
```
Final: main's removal plus our `MutRefPtr`:
```rust
        ExpX::Unary(
            op @ (UnaryOp::MutRefCurrent | UnaryOp::MutRefFuture(_) | UnaryOp::MutRefPtr),
            e1,
        ) => {
```

## `source/vir/src/sst_util.rs` (imports)

Ours adds `CrateId` (used by our `sst_ptr_addr`).
Main drops `ArithOp`, `BinaryOp`, `Mode` (`ArithOp`/`BinaryOp` moved to `sst`) and adds `VarIdent`, `VarIdentDisambiguate`.
Final: main's list plus `CrateId`.

## `source/vir/src/printer.rs`

Ours adds `impl<A: ToDebugSNode> ToDebugSNode for Box<A>`; main adds `?Sized` to the `Arc<A>` impl.
Final: both.

---

## Return values in SST: `ret: Pars` vs `outer_ret` / `inner_ret` **[decision]**

This is the main structural conflict, in `sst.rs`, `ast_to_sst_func.rs`, `sst_visitor.rs`, `poly.rs`,
`sst_to_air_func.rs`, `sst_to_air.rs` and `shadow_data.rs`.

Ours (`FunctionSstX`):
```rust
    // For unit-value returning functions, ret includes the unit value,
    // so it's always the case that ret.len() >= 1
    // For exec/proof functions that are not const/static values,
    // ret may contain arbitrarily many extra return values after the original one Rust return value
    pub ret: Pars,
```
Main (`FunctionSstX`; main also removed `async_ret`):
```rust
    /// Return value from the external perspective.
    /// Callers of this function see this as the return value, and should apply it as the
    /// last argument to ensures.
    pub outer_ret: Par,
    /// Return value from the internal perspective, used primarily by the `FuncCheckSst`.
    pub inner_ret: Par,
```
Final: main's two fields plus a separate list for ours:
```rust
    pub outer_ret: Par,
    pub inner_ret: Par,
    // For exec/proof functions that are not const/static values,
    // there may be arbitrarily many extra return values after the original one Rust return value
    // (e.g. shadow data for the return value).
    // These are the same from the external and internal perspectives.
    pub extra_rets: Pars,
```
Why: main's code uses `outer_ret` / `inner_ret` in many places (modes, well_formed, ast_simplify, traits, safe_api, ...);
ours only appends shadow-data returns after the original one.
A separate `extra_rets` leaves main's code untouched.
Where ours used `ret[0]`, the final uses `outer_ret` (or `inner_ret` inside the function body);
where ours iterated over `ret`, the final iterates over the original return followed by `extra_rets`.

### `sst.rs`: `StmX` derive
Ours `#[derive(Clone, Debug, ToDebugSNode)]`, main `#[derive(Debug, ToDebugSNode, Clone)]`. Final: main's.

### `ast_to_sst_func.rs`: building `FunctionSstX`
Ours:
```rust
        ret: Arc::new(vec![param_to_par(&function.x.ret)]),
        ens_has_return: function.x.ens_has_return,
```
Main:
```rust
        outer_ret: param_to_par(&function.x.outer_ret),
        inner_ret: param_to_par(&function.x.inner_ret),
        ens_has_return: ens_has_return,
```
Final:
```rust
        outer_ret: param_to_par(&function.x.outer_ret),
        inner_ret: param_to_par(&function.x.inner_ret),
        extra_rets: Arc::new(vec![]),
        ens_has_return: ens_has_return,
```

### `sst_visitor.rs`
- `StmX::Call`: ours made `dest` a `Vec` (`R::map_vec`); main added a `body: Option<Stm>` field.
  Final: `R::map_vec` for `dest` plus main's `body` visit.
- `visit_function`: ours `let ret = self.visit_pars(&f.x.ret)?;` / `ret: R::get_vec_a(ret)`;
  main visits `inner_ret` and `outer_ret`.
  Final: main's two, plus `let extra_rets = self.visit_pars(&f.x.extra_rets)?;` / `extra_rets: R::get_vec_a(extra_rets)`.

### `sst_vars.rs`
- Ours replaced `stm_get_assignment_shallow -> Option<&Exp>` with `stm_get_dest_shallow -> Arc<Vec<Dest>>`
  (and a `Vec<Exp>`-returning `stm_get_assignment_shallow` below it);
  main only reworded its doc ("calls" → "call arguments").
  Final: ours, with main's wording applied to the doc comment on our `stm_get_assignment_shallow`.
- `stm_assign` and `stm_mutations`, `StmX::Call` arm:
  ours loops over the dests (`for dest in dest.iter()`); main destructures every field to rebuild the call with its new `body`.
  Final: main's destructuring and rebuild, with our loop over the dests.

### `poly.rs`
- `State`:
  ours replaced `is_ret_opaque: bool` with `ret: Option<Pars>`;
  main renamed it to `is_poly_ret_with_opaque: bool` (now "contains an opaque type and is Poly", computed from `inner_ret`).
  Final: **per return value**, with main's test applied to each:
  ```rust
  // for each return value (inner_ret, then extra_rets):
  // does its type contain an opaque type encoded as Poly?
  // (empty outside a function)
  rets_poly_with_opaque: Vec<bool>,
  ...
  rets_poly_with_opaque: std::iter::once(inner_ret)
      .chain(extra_rets.iter())
      .map(|r| typ_contains_opaque(&r.x.typ) && typ_is_poly(ctx, &r.x.typ))
      .collect(),
  ```
  (`vec![]` in the expression-only `State`, where ours had `ret: None`.)
  Why per index: a shadow-data extra return `ShadowData<T>` with an opaque type inside `T` passes main's test
  (`typ_contains_opaque` looks inside, and `typ_is_poly` on a `Primitive` is `typ_as_mono(..).is_none()`),
  so it needs the coercion too.
  Both ours (top-level `TypX::Opaque` only) and an `i == 0`-only version would miss it.
  Nothing uses shadow data with opaque return types today.
- `return_typ`: ours added an index `i` into `ret`; main switched `ret` → `outer_ret`.
  Final:
  ```rust
  // i == 0 is the original return value; i > 0 is extra_rets[i - 1]
  fn return_typ(ctx: &Ctx, function: &FunctionSstX, is_trait: bool, typ: &Typ, i: usize) -> Typ {
      let ret = if i == 0 { &function.outer_ret } else { &function.extra_rets[i - 1] };
      if (is_trait || typ_is_poly(ctx, &ret.x.typ))
  ```
- `UnaryOp::CastToInteger`: main rewrote it (rewraps a type-param operand as boxed int instead of unboxing); ours added `MutRefPtr` to the next arm.
  Final: main's `CastToInteger` arm, then `MutRefCurrent | MutRefFuture(_) | MutRefPtr`.
- `StmX::Call`: ours collects `dests: Vec<Dest>`; main visits the new `body`.
  Final: both.
- `StmX::Return`:
  ours:
  ```rust
                let mut is_ret_opaque = false;
                if let Some(ret) = &state.ret {
                    assert!(ret_exp.len() == ret.len());
                    is_ret_opaque = matches!(*ret[i].x.typ, TypX::Opaque { .. });
                }
  ```
  main:
  ```rust
                if state.is_poly_ret_with_opaque {
                    Some(crate::poly::coerce_exp_to_poly(ctx, &e1))
                } else {
                    Some(e1)
                }
  ```
  Final (inside our loop over `ret_exp`; keeps our length assertion, skipped outside a function as ours was):
  ```rust
                let is_ret_opaque = if state.rets_poly_with_opaque.is_empty() {
                    false
                } else {
                    assert!(ret_exp.len() == state.rets_poly_with_opaque.len());
                    state.rets_poly_with_opaque[i]
                };
                let r = if is_ret_opaque { crate::poly::coerce_exp_to_poly(ctx, &e1) } else { e1 };
  ```
- `visit_func_check_sst`: last parameter was `ret: &Pars` in ours (to type every post-condition dest)
  and `ret_typ: &Typ` in main (`&inner_ret.x.typ`).
  Final: `ret_typs: &[Typ]`, built in `visit_function` as
  `once(inner_ret.x.typ).chain(extra_rets types)` (after the poly/native coercion), and passed at all four call sites.
- `visit_function`, coercing the return types:
  ours looped over every `ret` entry; main coerces `outer_ret` and `inner_ret` separately.
  Final: main's code for `outer_ret` / `inner_ret`, then our loop over `extra_rets`.
- `visit_function`, `State` init: main's `is_poly_ret_with_opaque: typ_contains_opaque(&inner_ret.x.typ) && typ_is_poly(ctx, &inner_ret.x.typ)` (ours had `ret: Some(ret.clone())`).

### `sst_to_air_func.rs`
- Five spots where ours had `assert!(function.x.ret.len() == 1)` (or `<= 1`) followed by `function.x.ret[0]`,
  and main had `function.x.outer_ret`:
  final is `assert!(function.x.extra_rets.is_empty())` + `function.x.outer_ret`.
  (spec rec decl, spec fn symbol decl, `static%` const decl, spec-fn ensures error, spec axiom typ_invariant,
  and the `fndef_axioms` check)
- Spec-function error message: main's backticked "`` `ensures` clause unsupported on spec function ``".
- `func_decl_to_air` ensures typing:
  ours:
  ```rust
            let ret = if function.x.attrs.is_async {
                let r = function.x.async_ret.clone().expect("Async function has no return type");
                Arc::new(vec![r])
            } else {
                function.x.ret.clone()
            };
            for r in ret.iter() { /* push typ + typ_invariant */ }
  ```
  main (no more `async_ret`; `outer_ret` is already the future type for async fns):
  ```rust
            let ParX { name, typ, .. } = &function.x.outer_ret.x;
            /* push typ + typ_invariant */
  ```
  Final:
  ```rust
            let rets = std::iter::once(&function.x.outer_ret).chain(function.x.extra_rets.iter());
            for r in rets { /* push typ + typ_invariant */ }
  ```

### `sst_to_air.rs`
- `call_args_to_air` signature:
  - Ours: `dest: &Vec<Dest>`, plus the old unused `state` and `stm`.
  - Main: dropped `state` and `stm`.
  - Final: main's parameter list with our `dest: &Vec<Dest>`.
- `StmX::Call` (function target), before the ensures:
  - Ours: built `ens_args_dests` = args + every dest (when `func.x.ens_has_return`) and passed that to `call_args_to_air`.
  - Main: calls `call_args_to_air(..., args, ...)`, then emits the new call `body`.
    Also removed `FunctionX::ens_has_return` in favor of `crate::ast_to_sst::ens_has_return(ctx, func)`.
  - Final: our `ens_args_dests` approach, using main's `ens_has_return(ctx, func)` (moved up so it is computed first),
    followed by main's `body` emission.
- `StmX::Call`, havoc of the dests:
  - Ours: looped over the dests to havoc them, then took a `ctx.debug` snapshot.
  - Main: havocs the single dest, calls `ctx.notify(|obs| obs.on_havoc(...))`,
    and **removed the `ctx.debug` snapshot feature entirely**.
  - Final: our loop, with main's `notify` after each havoc, and no debug snapshot.
- `emit_generic_conditions`:
  - Ours: `Some(dest)` (all dests).
  - Main: `Some(dest.clone().unwrap().dest)`.
  - Final: `if ens_has_return { Some(dest) } else { None }` (our multi-dest `sst_call_ensures`, main's `ens_has_return`).
    Possible tuple-type mismatch for `shadow_data` functions here (follow-up 3).
- `StmX::Call` (`AssumeExternal`):
  - Ours: `for Dest {..} in dest.iter()`.
  - Main: shorter `call_args_to_air` call.
  - Final: both.
- `StmX::Return`:
  - Ours: looped over `ret_exp` / `dest` and, per return value, emitted `opaque_ty_additional_stmts(...)` using `fun.x.ret[i]`.
  - Main: keeps the single `assume_var` and **removed the `opaque_ty_additional_stmts` call** here
    (opaque return types are now handled via `return_opaque_type_eqs` on `FuncCheckSst`).
  - Final: our loop over the return values, without the opaque-type statements.

### `ast_to_sst.rs`
- `sst_util` imports:
  - Ours: added `sst_mut_ref_ptr`, `sst_ptr_addr`.
  - Main: added `sst_disjoin`, `sst_mut_ref_future`, `subst_typ`.
  - Final: union.
- Call-argument loop:
  - Ours: `TwoPhaseBorrowMut(_)` → `TwoPhaseBorrowMut(..)`.
  - Main: added an `ExprX::AtomicUpdateInitDummy` arm before `TwoPhaseBorrowMut`.
  - Final: both.
- `stm_call` signature:
  - Ours: `dest: Vec<Dest>`.
  - Main: `dest: Option<Dest>`, then a new `body: Option<Stm>`.
  - Final: `dest: Vec<Dest>, body: Option<Stm>`.
- Three `stm_call(...)` call sites:
  - Ours: `vec![dest]` / `vec![]`.
  - Main: `Some(dest), body` / `None, body`.
  - Final: `vec![dest], body` / `vec![], body`.

---

## Other VIR files

### `triggers.rs` (two hunks)
Ours kept `InferSpecForLoopIter` arms and added `ShadowData` / `ShadowAddrOf`; main removed `InferSpecForLoopIter`.
Final: our `ShadowData` / `ShadowAddrOf` arms, without `InferSpecForLoopIter`.

### `resolution_inference.rs` (three hunks)
Ours: `TwoPhaseBorrowMut(p, _)` / `BorrowMut(p, _)` with `self.build_place_and_intern(...)?`;
main: `TwoPhaseBorrowMut(p)` / `BorrowMut(p)` with `unwrap!(self.build_place_and_intern(...))` (the function's return type changed on main).
Final: our patterns, main's `unwrap!(...)`.

### `interpreter.rs` (four hunks)
- Two "ok" arm lists: ours added `MutRefPtr | ShadowData` and kept `InferSpecForLoopIter`; main removed `InferSpecForLoopIter`.
  Final: `| MutRefFinal(_) | MutRefPtr | ShadowData => ok`.
- Two `CastToInteger` arms: ours kept `panic!("CastToInteger should have been removed by poly!")` and added a `ShadowAddrOf` panic.
  Main removed the panic in the first match (now covered by the `ok` list) and changed the second to `CastToInteger => Ok(e.clone())`.
  Final: main's `CastToInteger` handling, plus our `ShadowAddrOf` panic in both places.

### `modes.rs`
- `State::get`:
  ours replaced it with `get_inner(x, span, for_shadow_data)` (and `VarMode::Mode` has a third field, the shadow mode), keeping a `get` wrapper;
  main rewrote `get` with a `let ... else { eprintln!("{x:#?}"); panic!(...) }` and a `match`.
  Final: our `get_inner` (plus the wrapper), in main's `let-else` / `match` style.
- Ensures typing of the return variable:
  ours: `if function.x.ens_has_return { insert_var_mode(&ret.name, VarMode::Mode(Spec, Some(ret.mode), No)) }`;
  main: `ens_typing.insert(&function.x.inner_ret.x.name, Mode::Spec, Some(ProphVar::No));` unconditionally (no more `ens_has_return` field).
  Final: unconditional, on `inner_ret`, with our shadow mode:
  ```rust
    let var_mode = VarMode::Mode(Mode::Spec, Some(function.x.inner_ret.x.mode), ProphVar::No);
    ens_typing.insert_var_mode(&function.x.inner_ret.x.name, var_mode);
  ```
- Body rewrite after mode checking (large hunk):
  ours = base + our `BorrowMut(_, _)` / `BorrowMut(inner, _)` / `TwoPhaseBorrowMut(deref_e, true)` / `BorrowMut(deref_e, true)`;
  main removed the `InferSpecForLoopIter` arm, switched to `map_expr_stmt_visitor`, and added `assert_irrefutable` handling for `Match` and `StmtX::Decl`.
  Final: main's version with our four borrow changes.

### `well_formed.rs` (`--no-cheating`) **[decision]**
- Ours added `Ctxt::assumptions_allowed(function)`
  (`no_cheating_trusted` attribute, vstd, or vstd/verus_builtin embedded in core) and kept `CheckDetails`;
  main replaced `CheckDetails` with `DynCompatabilityChecks` / `InitialWfResults` (`PerFunctionCheckResults` is below).
  Final: our `assumptions_allowed`, then main's new types.
  Main changed `PathX::segments` from `Idents` to `Segments`, so the first-segment check is now
  `path.segments.first().and_then(|s| s.name()).map(|s| s.as_str())`.
- `assume`/`admit`, `assume_termination`, `external_body`/`assume_specification` checks:
  ours added `&& !ctxt.assumptions_allowed(function)` (and for `external_body` replaced the `is_vstd_path` match with it);
  main backticked the messages and switched `emit.emit(None, VirErrAs::NonFatalError(msg, None))` → `emit.emit_deferred_err(msg)`.
  Final: our conditions with main's messages and `emit_deferred_err`.
- New on main: an `assume_compatibility_with_trait_spec` check under `--no-cheating`.
  **I also gated it with `!ctxt.assumptions_allowed(function)`**, for consistency with the other checks.
  Revert that if you want it unconditional.

---

## rust_verify (continued)

### `verus_items.rs`
- `VstdItem`: ours replaced `SharedReference` with `SpecPtrAddr` (old `raw_ptr::SharedReference` is gone);
  main kept `SharedReference` and added `RustDiv`, `RustRem`, `StrictlyCloned`.
  Final: `SpecPtrAddr, RustDiv, RustRem, StrictlyCloned` (no `SharedReference`; nothing else referenced it).
- Item table: likewise, our `raw_ptr::spec_ptr_addr` entry plus main's `pervasive::strictly_cloned` entry, no `raw_ptr::SharedReference` entry.
- `BuiltinFunctionItem`: union (`ShadowData`, `ProofWithCallee`), and both table entries
  (with main's column alignment for `get_future_output_type`).

### `attributes.rs` (five hunks)
Union everywhere: ours added `Attr::ShadowData` / `shadow_data`;
main added `Attr::AssumeUnsupportedAttributes` and `Attr::CreateOpenInvariantCredit` / `create_open_invariant_credit`.

### `rust_to_vir_func.rs` (two hunks)
Union of `FunctionAttrsX` fields: our `has_shadow_data`, main's `is_drop` and `has_trivial_clone`.

## builtin_macros

### `syntax.rs` (four hunks, for-loop desugaring)
Ours only changed bare `vstd::` / `::vstd::` paths to `#vstd::` (commit cc4a1b0b5).
Main rewrote this code (removed `infer_spec_for_loop_iter` and the `ghost_inv`, changed `peek(&#x_iter_name.snapshot.view(), ...)` to `peek(#x_iter_snapshot_arg, ...)`, and `VerusForLoopWrapper::new(#x_exec_iter_arg)`), already using `#vstd::`.
Final: main's in all four. No bare `vstd::` paths remain outside comments.

---

## Tests (`source/rust_verify_test/tests/`)

### `raw_ptrs.rs`
Ours: `token.split(4)` + `PointsTo::<u32>::from_untyped(token1, ())` (new raw-pointer API);
main: `token.split(Set::range(...))` + `token1.into_typed::<u32>(...)` (old API, adjusted for finite `Set`).
Final: ours.

### `seqs.rs`
Both sides added the same four `filter_index` tests (ours cherry-picked them); main also adds a `range_syntax` test.
Final: main's.

### `traits.rs`
Both sides added `direct_concrete_call_trait_spec_only` and `direct_concrete_call_with_assume_specification` (ours from the #2540 cherry-pick);
main's side also has a dozen more tests after them.
Final: main's.

### `iterators.rs` **[decision — please check]**
Ours = cherry-picked early versions of upstream iterator PRs; main has the upstream versions plus many more tests.
Final: **main's whole file**.
Our file had five tests that are not on main (anywhere):
`map_can_be_implemented`, `filter_can_be_implemented`, `take_can_be_implemented`, `skip_can_be_implemented`, `iter_mut_can_be_implemented`.
They are written against our pre-upstream iterator API (`will_return_none`, `initial_value_relation`, `into_map_spec`, ...), which main replaced, so I **dropped** them.
They can be recovered with `git show HEAD:source/rust_verify_test/tests/iterators.rs` (follow-up 10).

---

## vstd

### `std_specs/iter.rs` **[decision]**
Our changes were (a) cherry-picks of upstream iterator PRs (`find`, `all`/`any`, `map`, `filter`, `take`/`skip`, `zip`, `&mut` blanket impl, `collect`/`FromIterator`),
all of which main now has in their final upstream form, and (b) three rustlib-specific changes.
Final: **main's whole file**, plus the rustlib change that still applies:
- kept: `#[cfg_attr(verus_verify_core, verifier::shadow_data)]` (with its comment) on `ExIterator::next`.
- not re-added: our `size_hint` spec (main has its own `size_hint` spec on `ExIterator`).
- not re-added: our `iter_len_exact` extra `requires` (main has no `iter_len` / `iter_len_exact`; it specs `ExactSizeIterator::len` instead).

**Consequence for rustlib:** main removed `will_return_none` and `initial_value_relation` (replaced by `produces`),
so rustlib's `core/src/str/validations.rs`, `alloc/src/vec/into_iter.rs` and `alloc/src/collections/linked_list.rs` need porting to main's `IteratorSpec` (follow-up 5).

### `std_specs/range.rs`
Ours added `ExRangeFrom` / `ExRangeFull` / `ExRangeTo` / `ExRangeToInclusive` type specs, moved the `View for RangeInclusive` impl up,
and added an `assume_specification` for `<Range<A> as Iterator>::size_hint`.
Main independently added the same four type specs (with `reject_recursive_types(Idx)`), plus `Bound`, `RangeBounds` specs and more.
Final: main's whole file (our `size_hint` spec dropped).
Ours added the `size_hint` spec only because Verus required one once `Range::next` had a spec;
the soundness fix itself was the trait-level `ensures` on `Iterator::size_hint`, which main also has (`std_specs/iter.rs`).
Checked: with and without our spec, `(0u8..5u8).size_hint()` can't be proved `== (0, None)` (main's `default_ensures` isn't assumed for `Range`),
and `h.0 <= 5` verifies.

### `std_specs/core.rs`, `std_specs/vec.rs`
Ours only added `#[cfg(not(verus_verify_core))]` to `IndexSetTrustedSpec` / `index_set` and their `Vec` impls; main deleted them all (and `TrustedSpecSealed`).
Final: deleted; main added `assume_specification [core::hint::must_use]` in their place.

### `std_specs/control_flow.rs`
Union of the broadcast group: our `spec_from_from_spec`, main's three `*_try_laws` lemmas.

### `cell.rs`
Ours: `pub use super::raw_ptr::TypedValue;` + `use super::set::*;`; main: `MemContents` and dropped the `set` import (now uses `ISet`).
Final: `pub use super::raw_ptr::TypedValue;` without the `set` import (nothing uses `Set` there any more).

### `modes.rs`
Ours added `TrivialOwnership` / `tracked_from_spec` / `impl_trivial_ownership!`; main added `forget`.
Final: both (ours first).

### `seq_lib.rs`
Both added `zip_truncate`; ours with `.take(...)`, main with `[..n]` range syntax.
Final: main's.

### `wrapping.rs`
Main added `rotate_left` / `rotate_right` specs; ours only removed a blank line.
Final: main's.

### `seq.rs` (tracked `Seq` operations)
- Ours:
  - `external_body` versions of `tracked_insert` / `tracked_borrow_mut`.
  - New `tracked_borrow_subrange`, `tracked_borrow_subrange_mut`, `tracked_split_borrow_mut`, `tracked_add_borrow`, `tracked_add_borrow_mut`.
  - (Auto-merged) `tracked_skip` and a `pub` recursive `tracked_add`.
- Main:
  - Re-implemented the tracked ops on top of an `inner` field (no more `external_body`),
    including `tracked_insert` and `tracked_borrow_mut`.
  - A private, `inner`-based `tracked_add`.
- Final:
  - Main's implementations of `tracked_insert` / `tracked_borrow` / `tracked_borrow_mut` (and their doc comments).
  - All our new functions.
  - The auto-merge produced two `tracked_add`s:
    **kept main's implementation and made it `pub`**, removing ours.

### `simple_pptr.rs`
- Doc link: ours `[`TypedValue::Empty`](TypedValue::Empty)`, main changed the old `MemContents::Uninit` link to the short `[`...`]` form.
  Final: `[`TypedValue::Empty`]`.
- Zero-sized allocation: ours uses the new API (`IsExposed::null()`, `with_exposed_provenance`, `PointsTo::zero_sized`);
  main adjusted the old `PointsToRaw::empty(...).into_typed(p)` code for finite `Set`.
  Final: ours.

### `string.rs` (`group_string_axioms`)
Ours kept `axiom_spec_iter` (dropped `next_postcondition`); main dropped both, and `axiom_spec_iter` no longer exists.
Final: neither.

### SliceIndex specs: `slice.rs`, `std_specs/slice.rs`, `std_specs/vec.rs`, `string.rs` **[decision: main's design]**
Ours (#2532 on our branch): `ExSliceIndex` moved into `std_specs/slice.rs` with `spec_start` / `spec_end`
and uninterpreted `valid_indices` / `index_result` / `index_mut_result` (per-type broadcast definitions, for `[T]` and `str`),
all under `#[cfg(not(verus_verify_core))]`; plus `cfg(not(verus_verify_core))` on other `[T]` specs.
Main (#2727, #2744, #2895, #2854, #3272, #3311): `ExSliceIndex` in `slice.rs` with `in_bounds` / `index_postcondition` / `index_mut_postcondition`
and `get` / `get_mut` / `index` / `index_mut`; `str` specs in `string.rs`; many new `[T]` method specs.
rustlib's core defines its own `SliceIndexSpec` (`core/src/slice/index.rs`), so it doesn't use vstd's.

Final: **main's design**, with our `verus_verify_core` guards carried over:
- `slice.rs`: main's `ExSliceIndex`, in its own `#[cfg(not(verus_verify_core))] verus! { ... }` block.
  (A `cfg` on the trait itself isn't enough: `external_trait_extension` (`builtin_macros/src/syntax_trait.rs`, `new_trait_from` / `new_impl_for_trait`)
  creates the generated `SliceIndexSpec` / `SliceIndexSpecImpl` traits and blanket impl with no attributes,
  so they stayed in core mode and `test_is_core` failed with `trait core::slice::index::SliceIndex not declared to Verus`.
  Upstream report: follow-up 7.)
  Our `cfg` on `<[T]>::len` kept. Main removed `spec_slice_get` / `axiom_slice_get_usize`,
  so our separate core / non-core `group_slice_axioms` are no longer needed (one group, main's).
  Kept our `tracked_slice_index` / `tracked_slice_subrange` (used in `type_representation.rs` and `raw_ptr/points_to_ops.rs`)
  next to main's new `tracked_borrow` / `tracked_borrow_mut` (`tracked_slice_index` duplicates `tracked_borrow`).
- `std_specs/slice.rs`: main's file. Its `SliceIndexSpecImpl` impls and `SliceIndex` assume_specs,
  `starts_with` / `ends_with`, `IndexSpecImpl` for `[T]` / `[T; N]`, `[T]::get` / `get_mut` / `get_unchecked(_mut)`, and the `Index` / `IndexMut` specs
  are in a separate `#[cfg(not(verus_verify_core))] verus_skip_verusfmt! { ... }` block; the `SliceIndexSpec` / `IndexSpec` imports are guarded too.
  Our guards re-added on `first`, `last`, `first_mut`, `last_mut`, `split_at`, `split_at_mut`.
  Main's other new `[T]` specs are guarded too (rustlib's core defines all these methods itself),
  in two more `#[cfg(not(verus_verify_core))] verus_skip_verusfmt! { ... }` blocks:
  - `PartialEq` for `[T]` (`eq` spec and `PartialEqSpecImpl`), `contains`, `reverse`, `swap`, `rotate_left`, `rotate_right`;
  - everything after `split_at_mut`: `split_at_checked`, `split_at_(mut_)unchecked`, `split_first(_mut)`,
    `copy_from_slice`, `copy_within`, `Chunks` (type spec, `IteratorSpecImpl`, `chunks`), and the sorts.
  Left unguarded, as on our side before the merge: `unreachable_unchecked`, `Iter` / `iter` / `into_iter`,
  and main's `IterMut` / `iter_mut` (which replace our unguarded `IterMut` specs from `vec.rs`).
  `test_is_core` shows no new errors with these guards.
- `std_specs/vec.rs`: `index.in_bounds(s)` (main) instead of `valid_indices_slice(index.spec_start(s), index.spec_end(s), s)` (ours).
- `string.rs`: main's `str` SliceIndex specs (already `cfg(all(verus_keep_ghost, not(verus_verify_core)))` on main).
- Our design remains only in `source/vstd/SOUNDNESS_AUDIT.md` (a doc).
Parts of our design could be added back later (follow-up 11).

### `raw_ptr.rs` (deleted on our side, modified on main)
Main's three changes to the old file, ported to `raw_ptr/` where they apply:
- `set_lib::set_int_range(...)` → `Set::range(...)`: applied to all six uses in `raw_ptr/points_to_collections.rs`
  (`is_range`, `contains_range`, `map_from_seq`, `seq_from_map`), and removed the `set_int_range` import.
- `ptr_ref2` output lifetime fix (`Tracked<&'a PointsTo<T>>`): no change needed;
  the new API has no `ptr_ref2`, `ptr_ref` uses elided lifetimes that already tie `&T` to the `&PointsTo<T>`,
  and every explicit-`'a` function in `raw_ptr/` already ties its output to its inputs.
- Doc link `[`MemContents::Uninit`](MemContents::Uninit)` → `[`MemContents::Uninit`]`: no such links in `raw_ptr/`; the `simple_pptr.rs` one is above.
The file itself stays deleted (`git rm`'d). `raw_ptr_popl.rs` (the unbuilt old copy) is unchanged.

---

## Build fixes (auto-merged code that no longer compiles against main)

- **z3:** main requires z3 4.16.0; installed with `source/tools/get-z3.sh` (replaces `source/z3`).
- `fun!` macro syntax changed on main (function name after `;`):
  `fun!(CrateId::Vstd => "raw_ptr", "spec_ptr_addr")` → `fun!(CrateId::Vstd => "raw_ptr"; "spec_ptr_addr")`
  in `sst_util.rs`, `ast_to_sst.rs`, `prune.rs`.
- `shadow_data.rs` **[follows the `extra_rets` decision]**:
  - main removed `ParPurpose` / `ParX::purpose`: dropped from the shadow parameter, now built by a new helper `shadow_par` (used by `add_to_pars`).
  - `add_to_pars(&mut functionx.ret)` (which appended the shadow of the return value to `ret`) →
    `extra_rets = [shadow_par(outer_ret)]`.
  - New error: `shadow_data not allowed for async functions` (async functions have different `outer_ret` / `inner_ret`, and shadow data was never used with them).
  - `ShadowFun::ret_typ` from `f.x.outer_ret` (was `f.x.ret`).
- `modes.rs`:
  - `record.erasure_modes.var_modes` → `local_modes` (renamed on main, same `(Span, (Mode, Mode))` entries), in our `shadow_data(x)` check.
  - main's new atomic-call code builds `VarMode::Mode(Mode::Spec, ProphVar::No)`; added our shadow-mode field: `VarMode::Mode(Mode::Spec, None, ProphVar::No)`.
- `traits.rs`: the auto-merge kept our old tuple-form copy of the "external impl method with no `assume_specification` → dynamic call" arm
  after main's identical struct-form arm (`ExprX::Call { target, args, post_args, body }`); removed our copy.
- `recursive_types.rs`: main replaced `TypX::Primitive(_, ...)` catch-alls with explicit lists of primitives;
  added our `Primitive::ShadowData` to both lists
  (`check_well_founded_typ`: same as `Ptr`, i.e. `true`; `check_positive_uses`: check its type argument, like the others).
- `rust_verify/src/attributes.rs`: Rust 1.100 removed `box` patterns;
  our two `#[verus::trusted(spec)]` matches `Some(box [AttrTree::Fun(_, arg, None)])` → `Some([AttrTree::Fun(_, arg, None)])` (main's style elsewhere in the file).
- `rust_verify/src/automatic_derive.rs` (new on main): added our `no_cheating_trusted: false` and `has_shadow_data: false` to its `FunctionAttrsX` literal.
- `rust_verify/src/no_cheating.rs`:
  - rustc 1.100 `visit_mod` takes a `LocalModId`: `rustc_hir::CRATE_HIR_ID` → `rustc_span::def_id::CRATE_MOD_ID` (as main's `external.rs` does), twice.
  - **[decision]** `HeaderFinder::is_specification_header`: main replaced `SpecItem::OpensInvariants{None,Any,,Except,Set}` with `SpecItem::OpensInvariantMask`;
    I also added main's new `SpecItem::AtomicSpec`, since it is part of the function's signature too
    (so `--no-cheating` also scans references inside an `atomic_spec` header). Remove it if you'd rather not.
    - Background: under `--no-cheating`, trusted code must be closed under references
      (it may not reference an untrusted item in the same crate).
      For a `#[verus::trusted(spec)]` function, only the signature is trusted, not the body,
      so `RefChecker` scans its type signature plus the arguments of the header calls in its body that `is_specification_header` accepts
      (`requires`, `ensures`, `opens_invariants`, ...), and skips everything else in the body.
    - main's atomic functions (#2720) add an `atomic_spec(...)` header,
      which Verus reads as part of the function's contract (`vir/src/headers.rs` stores it as the function's atomic update,
      next to `requires` / `ensures`; `pre_header.rs` lists it with the other spec headers).
    - With `AtomicSpec` in the list: a `trusted(spec)` function's `atomic_spec` is checked like its `requires` / `ensures`,
      so it may only reference trusted items.
      Without it: the `atomic_spec` is treated as body code and not checked,
      so a trusted contract could depend on an untrusted spec function in the same crate, which is the gap `--no-cheating` exists to close.
    - Risk of keeping it: an existing `trusted(spec)` atomic function whose `atomic_spec` references untrusted local items would now get an error.
      Nothing does this today: no test combines the two (`logatom.rs` doesn't use `--no-cheating`, and the `no_cheating*.rs` tests have no atomic functions),
      and references into vstd are always allowed.
- `rust_verify/src/erase.rs` (`full_erasure_erases_call`) and `fn_call_to_vir.rs` (`uncompilable_verus_fn`): added our `VerusItem::MutRefPtr` next to `MutRefCurrent` / `MutRefFuture` (erased; uncompilable in exec code).
- `vstd/raw_ptr.rs`: `git rm`'d (main's copy was left in the working tree next to our `raw_ptr/mod.rs`, which made `mod raw_ptr` ambiguous).
- `vstd/std_specs/core.rs`: main renamed the file's macro alias `verus_` → `verus_skip_verusfmt`; renamed it in our two `verus_! { ... }` blocks (the `cfg(not(verus_verify_core))` Index block and the next one).
- `vstd/std_specs/option.rs` **[ported]**: our `Option::into_iter` spec (cherry-pick 37cd71da7; main has no equivalent) used the old iterator API.
  Ported to main's API, following main's slice `Iter` spec:
  - `IteratorSpecImpl for IntoIter<A>`: replaced `will_return_none` / `initial_value_relation` with `produces` (all `true`).
  - Removed `spec_into_iter`, `axiom_spec_into_iter` and the `when_used_as_spec` (nothing used them; main dropped this pattern in #2739);
    the facts move into the `into_iter` `ensures`:
    `o is None ==> remaining.len() == 0`, `o matches Some(a) ==> remaining == seq![a]`, `into_iter_opt(iter) == o`, `decrease is Some`.
- `vstd/std_specs/vec.rs`: removed our `slice::IterMut` block (cherry-pick 3159ae581: `ExIterMut`, `IteratorSpecImpl`, `iter_mut_ensures`, `<[T]>::iter_mut`,
  `iter_mut_next_post` / `iter_mut_next_postcondition`, `IterMut::next` / `size_hint` specs) and `iter_mut_next_postcondition` from `group_vec_axioms`;
  main has its own `ExIterMut` + `<[T]>::iter_mut` spec in `std_specs/slice.rs`.
  `SliceIndexSpec` import from `super::super::slice` (main's location).
  `vec.rs` now differs from main's only by our `cfg(not(verus_verify_core))` guards.
  (`SOUNDNESS_AUDIT_ITER.md` still mentions the removed `iter_mut_next_postcondition`: follow-up 13.)
- **exec_spec `MemContents` support (main's #3307, JakeGinesin) [decision: taken out of the build]**:
  main added `vstd/contrib/exec_spec/mem_contents.rs`, an exec mirror (`ExecMemContents`) of the old `raw_ptr::MemContents`,
  which our new `raw_ptr` replaces with `TypedValue` (a tracked enum, `Empty` / `Valid(Tracked<T>)`).
  - `contrib/exec_spec/mod.rs`: `mod mem_contents;` / `pub use mem_contents::*;` commented out with a `TODO(raw-ptr-final)`; the file is kept.
  - Tests `#[ignore]`d with a `TODO(raw-ptr-final)`: `test_exec_spec_mem_contents` and `test_exec_spec_pptr_permissions` (`exec_spec_verified.rs`),
    `test_exec_spec_unverified_misc_forms` (`exec_spec_unverified.rs`).
  - Left as is: the `MemContents` case in `builtin_macros/src/contrib/exec_spec.rs` (it only applies when a spec mentions `MemContents`).
  - Port to `TypedValue`: follow-up 9.
- **`vstd/atomic.rs` `ptr_atomic_methods` (main's #2720, Ziqiao Zhou) [ported trusted specs — please review]**:
  `from_ptr_store`, `from_ptr_load`, `from_ptr_swap` (`external_body`, `verifier::atomic`) were written against the old `PointsTo`.
  Ported per `POINTS_TO_MIGRATION.md`, matching our `ptr_mut_write` / `ptr_mut_read`:
  - import `PTPhys`, `PTTypedValue` (for `ptr()` / `wf()`) next to `PointsTo`.
  - `#[cfg(not(verus_verify_core))]` on the import, and added to the macro's two `target_has_atomic_primitive_alignment` cfgs,
    so rustlib has no trusted specs on `PointsTo`.
  - `is_init()` → `is_valid()`.
  - **added `wf()`** (the old `PointsTo` had a type invariant; the new one needs it explicit):
    `requires old(perm).wf()` + `ensures final(perm).wf()` on `from_ptr_store` and `from_ptr_swap`; `requires perm.wf()` on `from_ptr_load`.
  ```rust
  from_ptr_store: requires old(perm).ptr() == ptr, old(perm).wf(),
                  ensures value == final(perm).value(), old(perm).ptr() == final(perm).ptr(), final(perm).is_valid(), final(perm).wf(),
  from_ptr_load:  requires perm.ptr() == ptr, perm.is_valid(), perm.wf(),
                  ensures ret == perm.value(),
  from_ptr_swap:  requires ptr == old(perm).ptr(), old(perm).is_valid(), old(perm).wf(),
                  ensures final(perm).value() == v, final(perm).is_valid(), old(perm).value() == ret, ptr == final(perm).ptr(), final(perm).wf(),
  ```
- `vstd/std_specs/maybe_uninit.rs`: our side had already moved this file to `TypedValue`;
  main's newer `MaybeUninit::write` (#3247) and `array_assume_init` (#3302) specs used `is_init()` → `is_valid()`.
- Not changed: `PointsToRaw`'s type invariant still has `self.bytes.dom().finite()`,
  which main made always true (every `Set` is finite) and deprecated; it's a warning only (follow-up 14).

---

## vstd verification status at the merge commit (5 failures, to fix in follow-up commits)

**Upstream bug from main's #2908** ("Avoid unneeded boxing in UnaryOp::CastToInteger", Chris Hawblitzel):
`d as int` for a generic `d: B` (`B: Integer`) is now the raw `Poly` `d`, retyped as a boxed int.
Inside a closure (`|i, d: B| d as int`) the closure returns a boxed `B` where its type says `int`,
so the closure's `has_type` fails and facts about `s.map(...)` (even `.len()`) never fire.
Repro (scratchpad `cast_map.rs`): `assert(s.map(|i, d: B| d as int).len() == s.len())` fails;
`(d as int) + 0`, a concrete `u8`, or a cast outside a closure all verify.
main's vstd doesn't use this pattern; ours does. Failures caused by it:
- `endian.rs:1133` (`to_big_from_digits_single`: precondition `x.len() == Self::exp()`)
- `raw_ptr/points_to_ops.rs:2667`, `:2668` (`as_big_unaligned`: `in_bounds(digits.map(...))`, `wf()`)
- `type_representation.rs:646`, `:654` (`lemma_bytes_to_endian_digits`)

**Per your instruction: not fixed in the merge commit** (follow-up 1).

**Flaky proof in main's code:** `resource/impls/seq.rs:243` `GhostSubseq::agree_map` postcondition
(expand-errors: all sub-assertions succeed). The merge doesn't touch `resource/impls/seq.rs`;
likely perturbed by the merge adding our `raw_ptr::group_points_to_lemmas` to `group_vstd_default`.
Follow-up 2.
