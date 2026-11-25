# Remaining work on `verify-rustlib`

Covers both repos:
verus (branch `verify-rustlib`) and rustlib (`main`, and `port-raw-ptr-final`, which is behind `main`).

`verify-rustlib` goes into `main` as a series of PRs.
Only the high-priority items need to be done before then;
the rest are for later.

## Verus side

### High priority (before the PRs into `main`)

1. **Port the remaining specs from `raw_ptr_old.rs`**
   (`main`'s `raw_ptr.rs` plus the rustlib-era additions)
   to the new `raw_ptr/`.
   Everything else has a counterpart in `raw_ptr/`,
   or a migration path in `POINTS_TO_MIGRATION.md` / `POINTS_TO_RAW_MIGRATION.md`
   (e.g. `PointsToRaw::into_typed` / `PointsTo::into_raw` go through `PointsToUntyped`).
   The items with neither:
   - `ptr_mut_write` and `ptr_mut_read` (exec).
   - `PointsTo::leak_contents`.
   - `IsExposed` (`view`, `provenance`, `null`), `expose_provenance` and `with_exposed_provenance`.

   No `Dealloc` token:
   `allocate` / `deallocate` stay over a `PointsToUntyped`,
   and the facts `Dealloc` carried are on the provenance
   (`orig_size()`, `start_addr()`, `alignment()`,
   and, since `7bb6b930e`, `alloc_len() == orig_size()` for the `Global` allocator).
   New trusted specs need approval before they're committed.
2. **Restore `simple_pptr`** on the ported specs:
   update it to the new API (`TypedValue`, `PointsToUntyped`, provenance in place of `Dealloc`),
   and uncomment `pub mod simple_pptr` in `vstd.rs`.
3. **Undo the doc changes in `9df34716`** once `simple_pptr` builds.
   That commit turned the links to `simple_pptr::PPtr` into plain code text in
   `vstd/cell.rs`, `vstd/cell/pcell.rs`, `vstd/invariant.rs` and `vstd/raw_ptr/ptr_model.rs`.
4. **Update the tests to the new `raw_ptr`** (`diff.md`: "TODO: update tests to match new raw_ptr").
   - `TypedValue` rename (`MemContents` → `TypedValue`, `Uninit` / `Init(v)` → `Empty` / `Valid(..)`) in
     `examples/cells.rs`, `examples/doubly_linked.rs`, `examples/even_cell.rs`, `examples/rfmig_script.rs`,
     `examples/state_machines/tutorial/pcell_example.rs` and `examples/statics.rs`.
   - `rust_verify_test/tests/cell_lib.rs`: the `PCell` tests are done;
     the 12 pointer tests need rewriting for `allocate` without `Dealloc`
     and for the ported `ptr_mut_write` / `ptr_mut_read` (item 1).
   - Sweep the rest of `rust_verify_test` for the old API.
5. **`core_special_setup.rs`**: check that the `assume_specs` added for cfg'd-out definitions match rustlib's definitions.
6. **Keep the unsafe-attributes workaround** (`rust_verify/src/attributes.rs`) **out of `main`.**
7. **Bring `verify-rustlib` and rustlib in line with the opened PRs** (3, 4, 5 and 6a–c stay as they are):
   take each PR's version of its files, update the callers of 6b's and 6c's renamed and dropped functions
   (both repos; listed in `diff.md` under PRs 8 and 9),
   and fix rustlib's `grow_amortized` (`alloc/src/raw_vec/mod.rs`) for 6b's weaker `spec_from_from_spec`,
   which now also requires `obeys_from_spec()`
   (`FromSpecImpl<TryReserveErrorKind> for TryReserveError`'s is `closed`; making it `open` or adding a lemma is a spec change, so propose it first).
   Details: `diff.md`, "Bring verify-rustlib in line with the opened PRs".

### Later

8. **`ptr_specs.rs` TODOs:**
   - Remove `spec_ptr_addr`'s `rustc_diagnostic_item` once Travis's fix for the diagnostic item conflict is in.
   - Merge `mut_ref_from_parts` and `mut_ref_from_parts_slice` into one axiom over `T: ?Sized`
     (and `ref_from_parts` / `ref_to_parts` with their `_slice` versions, through a generic `pt_parts_wf`).
     Blocked: Verus doesn't know that a `&mut [T]`'s final length equals its current length.
9. **`SeqPointsTo` covariance:** `ptr: Ghost<*mut [T]>` makes it invariant in `T`.
   Options: a covariant ghost wrapper `CovariantPtr<T>` with two inverse axioms with `*mut T`,
   or separate ghost fields for the address, provenance and length.
   rustlib's `RawVec` / `Vec` covariance depends on this.
10. **Merge `verify-rustlib` into `verify-rustlib-refactor`**:
    take `verify-rustlib`'s side at the `TODO(verify-rustlib-transmute-v2)` spots,
    and drop the `SharedReference` parts of `TRUSTED_REVIEW.md` and `TODO.md` (`SharedReference` is deleted).
11. **Large `usize` enum discriminants under `--is-core`** (`rust_verify/src/rust_to_vir_expr.rs`, `expr_cast_enum_int_to_vir`; before PR 7 in `diff.md`):
    main's #2770 rejects `enum as usize` casts with discriminants above `u32::MAX`;
    for the Rust 1.100 update this is allowed whenever `--is-core` is set (rustlib's 64-bit `AlignmentEnum`, `core/src/mem/alignment.rs`).
    Make sure the target width is actually fixed when it's allowed:
    rustlib's `global layout usize is size == ...` (`specs/intrinsics.rs`) and the `target_pointer_width` cfgs on `AlignmentEnum` must agree with the `--target` rustlib is verified for,
    and consider checking against the target's pointer width (as the `isize` case does with `tcx.data_layout`) instead of trusting `--is-core`.

## Rust 1.100 update: steps 4-5 (rustlib branch `update-1.100.0`)

Remove each item once it's done.

1. **Port errors to expect in alloc** (from the merge; `MERGE_DECISIONS.md` follow-up 5):
   - main's iterator API (`will_return_none` / `initial_value_relation` → `produces`)
     in `alloc/src/vec/into_iter.rs` and `alloc/src/collections/linked_list.rs`
     (core's `str/validations.rs` is done: `produces` lost exactly the consumed items);
   - `group_iter_axioms` is no longer in `group_vstd_default` under `verus_verify_core`:
     modules that need the iterator axioms must `broadcast use crate::vstd::std_specs::iter::group_iter_axioms`;
   - specs using vstd APIs main changed (`Option::into_iter`);
   - `#[unstable_feature_bound(allocator_ext)]` on `impl AllocatorNightly for A` (`alloc/src/alloc.rs`), if Verus sees it.
2. **Fix core's verification failures** (core builds; 13 failing functions after the port errors):
   `cmp::max` (`core/src/cmp.rs`), `niche_types`' type-representation proofs and an overflow (`core/src/num/niche_types.rs`),
   `NonNull` (`core/src/ptr/non_null.rs`; after its axiomatization, rustlib item 16),
   `small_slice_eq`'s zip loop (`core/src/str/pattern.rs`),
   and vstd's `raw_ptr/points_to_collections.rs` (`untyped_mut_join`'s caller).
3. **Check in the alloc build:**
   - `const` closures with an `ensures` (`layout_array` / `finish_grow`, `alloc/src/raw_vec/mod.rs`);
   - `#[derive_const]` on `Global`;
   - `#[unstable(feature = "allocator_api")]` on Box's Verus-only functions (stable in 1.100; probably `allocator_ext`);
   - `current_memory`'s `self.ptr.into()` resolving to vstd's identity `FromSpecImpl<T> for T`
     (if not, put `impl<T> From<T> for T` in `verus!`);
   - the `IntoIter::next` changes in rustlib items 9 and 10.
4. **After the port errors** (approved):
   - `dealloc_verus` takes `NonNull<u8>` and the runtime path calls `dealloc_nonnull` (send the spec text first);
   - `#[verus::trusted] // just for closure` on `dealloc_nonnull`, `realloc_nonnull` (`alloc/src/alloc.rs`),
     `forget_remaining_elements_and_dealloc` and `dealloc_only` (`alloc/src/vec/into_iter.rs`);
   - try `LinkedList::front_mut`'s proof before the borrow (dropping `res`); keep it only if it verifies;
   - remove the remaining `CHANGED (1.100)` / `TODO(1.100)` comments
     (`CHANGED` marks only differences from the library, not version history).
5. **Re-check that the verified `Global` and `Box` code follows 1.100's call graph** (`alloc/src/alloc.rs`, `alloc/src/boxed.rs`;
   `GLOBAL_ALLOC_PLAN.md` claims it does, checked against 1.95; nothing checks it automatically,
   `--no-cheating` only checks that trusted code stays closed).
   Upstream 1.100 changes (`diff -u library-1.95.0/alloc/src/alloc.rs library-1.100.0/alloc/src/alloc.rs`):
   - `__rust_dealloc` / `__rust_realloc` take `NonNull<u8>`;
   - `dealloc` / `realloc` now call new private `dealloc_nonnull` / `realloc_nonnull`;
   - `deallocate_impl_runtime` calls `dealloc_nonnull(ptr, layout)` (ours: `dealloc_verus(ptr.as_ptr(), ...)`);
   - `grow_impl_runtime` / `shrink_impl_runtime` call `realloc_nonnull` (rustlib dropped the realloc path);
   - `NonNull::slice_from_raw_parts` → `cast_slice` (done in the verified code; see rustlib item 12).
   Update `GLOBAL_ALLOC_PLAN.md`'s call-graph description to match.
   `Box` (`diff -u library-1.95.0/alloc/src/boxed.rs library-1.100.0/alloc/src/boxed.rs`; mostly docs and attributes):
   - `new_in` / `try_new_in` / `new_uninit_in` dropped their `where A: Allocator` clauses (same calls);
   - `into_unique` was removed;
   - `Drop` for `Box` was restructured (still `Layout::for_value_raw` then `deallocate`);
   - check that the axiomatized `new_in`, `from_raw_in_untyped_with_typed_value` and
     `into_non_null_with_allocator_untyped_with_typed_value` still describe what 1.100's bodies do.

## rustlib side (later)

1. **Bring `port-raw-ptr-final` up to date with `main`.**
2. **Verify `read_unaligned` and `MaybeUninit`** (on hold since 2026-11-02).
   `read_unaligned_verus` (`core/src/ptr/mod.rs`) is still `external_body`.
   The design is in `TODO.md` on verus's `verify-rustlib-refactor`:
   one new trusted function (`as_mut_ptr_verus`),
   a verified `uninit` and `assume_init_verus`,
   and `CopyPointsToUnaligned::tracked_pt_untyped` / `into_typed_value`.
3. **Specify `grow_zeroed_verus` and `shrink_verus`** (`core/src/alloc/mod.rs`); they're `requires false`.
4. **Verify `addr`**:
   give rustlib's `addr` a spec and `when_used_as_spec(spec_addr)`,
   or rewrite its spec uses (`NonNull::inv` / `to_nat`, `RawVecInner::ptr_properties` / `extra_properties`) as `ptr@.addr`.
5. **Cfg out all of vstd's `assume_specification`s in the rustlib build**:
   get rustlib to the point where every `assume_specification` (and external type/trait spec) that vstd builds under `verus_verify_core`
   can be gated with `#[cfg(not(verus_verify_core))]`,
   so that rustlib's own specs (verified, or trusted in rustlib) are the only specs for core items.
   For each one still built, add the spec in rustlib (verify it, or mark it `#[verus::trusted]`) and gate vstd's.
   Already gated during the Rust 1.100 update: `std_specs::{nonzero, bits, char, ptr}` (whole modules)
   and the `core::cmp::{min, max, min_by, max_by, min_by_key, max_by_key}` specs in `std_specs/cmp.rs`.
6. **Verify the axiomatized `Box` functions** (`Box::new_in`, `from_raw_in_untyped_with_typed_value`,
   `into_non_null_with_allocator_untyped_with_typed_value`) down to the allocator and raw-pointer specs.
   Blocked on Verus treating `Box` specially.
7. **Reorganize `specs/` and `proofs/`**: trusted items in `specs/`, helper proofs in `proofs/`.
8. **Covariance:**
   - `RawVec<T>` / `Vec<T>`, after verus item 9.
   - `LinkedList<T>` and its `IntoIter`:
     `LinkedListGhost::ptrs` is a `Seq<*mut Node<T>>`; use `*const Node<T>` or `NonNull<Node<T>>`,
     then restore std's `assert_covariance` check at the end of `linked_list.rs`.
9. **Verify `IntoIter::next`'s end check** (rustlib `alloc/src/vec/into_iter.rs`),
    `self.ptr == unsafe { *((&self.end as *const *const T) as *const NonNull<T>) }`
    (upstream's `non_null!(self.end, T)` without the raw borrow):
    - vstd: a permission cast from `PointsTo<*const T>` to `PointsTo<NonNull<T>>`
      (a replacement for the old `cast_points_to`), to justify the read;
    - rustlib: a spec for `PartialEq for NonNull<T>` (`core/src/ptr/non_null.rs`, now outside `verus!`).
10. **`IntoIter::next`'s read** (rustlib `alloc/src/vec/into_iter.rs`) now calls `ptr.read_verus(...)` inline
    instead of the `read_front` helper.
    If that doesn't verify (the helper's comment says inlining breaks the type invariant), switch back to `read_front`;
    if it does, take `read_front` out.
11. **(Lower priority) Bring `Vec::into_iter` closer to upstream** (rustlib `alloc/src/vec/mod.rs`):
    upstream's order and single `unsafe` block, reading through `me` (the `ManuallyDrop`),
    and the `IntoIter { .. }` literal instead of `IntoIter::new_verified`;
    only taking the permission before `ManuallyDrop::new` and `read_alloc` would stay `CHANGED`.
    Needs specs for `ManuallyDrop::new` and its `Deref` (`core/src/mem/manually_drop.rs` has none),
    and a way to prove `IntoIter::wf()` (closed in `into_iter.rs`) from `vec/mod.rs`.
12. **Spec for `NonNull::cast_slice`** (rustlib core, outside `verus!`),
    if verified code needs it (`alloc_impl_runtime_verus`, `alloc/src/alloc.rs`).
    `<*const T>::cast_slice` and `<*mut T>::cast_slice` have `#[verus::trusted(spec)]` specs (approved),
    matching `slice_from_raw_parts(_mut)`. New specs, so propose them for approval first.
13. **See whether rustlib's `core/src/lib.rs` and `alloc/src/lib.rs` can differ less from the library**
    (commented-out features and lints, added attributes and modules); many of the changes will probably have to stay.
14. **Switch `count_ones` to vstd's `nat_count_ones`** once the rustlib port is done and rustlib's vstd includes PR 1c (`pr-vstd-count-ones`;
    already applied on verify-rustlib-update-1.100.0),
    then drop verify-rustlib's per-type `count_ones`, `lemma_count_ones_is_pow2` and `group_count_ones_is_pow2` from `wrapping.rs`
    (main never had them, so 1c leaves `wrapping.rs` alone):
    - `specs/intrinsics.rs`: `spec_count_ones::<$t>(x) as nat == $modname::count_ones(x)` → `nat_count_ones(x as nat)`;
    - `core/src/num/uint_macros.rs` `is_power_of_two`: `broadcast use crate::vstd::wrapping::group_count_ones_is_pow2`
      → `crate::vstd::bits::lemma_nat_count_ones_is_pow2`.
15. **Port `str` indexing by `ops::Range<usize>` to 1.100's structure** (rustlib `core/src/str/traits.rs`; before item 18).
    Upstream's `get` / `get_mut` / `index` / `index_mut` for `ops::Range<usize>` now delegate to `range::Range::from(self)`,
    and the logic moved to `SliceIndex<str> for range::Range<usize>`, which uses a new helper, `check_range`.
    rustlib still has the 1.95 bodies in the `ops::Range` impl (marked `CHANGED: original: range::Range::from(self)...`).
    - Code: the four `ops::Range` bodies become upstream's delegations;
      put the `range::Range<usize>` impl in `verus!` with the verified bodies (trusted `get_unchecked(_mut)`, a `SliceIndexVerus` impl);
      a verified `check_range` (upstream's form, with `add_verus` / `read_verus`).
    - Specs and proofs: `SliceIndexSpecImpl` for `range::Range<usize>`,
      a spec for `From<ops::Range<T>> for range::Range<T>` (`core/src/range.rs`),
      a spec for `check_range` (in bounds and both ends on char boundaries),
      and the moved proofs.
16. **`NonNull` in 1.100** (rustlib `core/src/ptr/non_null.rs`; before item 18):
    - Upstream changed the field from `pointer: *const T` (with `#[rustc_layout_scalar_valid_range_start(1)]`, now removed from core)
      to the pattern type `pointer: pattern_type!(*const T is !null)`, which Verus doesn't support.
      For the port, rustlib keeps 1.100's struct as `#[verifier::external_body]` and axiomatizes it, like `niche_types.rs`
      (the original lines are commented out next to the replacements):
      trusted `uninterp` `view` and `from_inner`, axioms `as_inner_tracked` / `from_inner_tracked`,
      `group_nonnull_axioms` (`from_inner` and `view` are inverses), and `nonnull_transmutable` is now trusted.
      Replace this with real support for pattern types in Verus (map `pattern_type!(T is p)` to `T`,
      plus a ghost conversion between the two for `NonNull { pointer: p }` / `self.pointer`), or keep the axioms.
    - Then review this file's diff from the library on its own.
17. **(Lower priority) Strengthen `next_code_point` / `next_code_point_reverse`'s `produces` postconditions** (rustlib `core/src/str/validations.rs`):
    besides `produces()` losing exactly the consumed items,
    state that the consumed items were produced (`old.produces().take(k)` all true for `next_code_point`,
    the last `k` entries for `next_code_point_reverse`, where `k` is the number of bytes consumed),
    as main's own `next` / `all` specs do.
    Needed only if `Chars::next` / `next_back` (`core/src/str/iter.rs`, outside `verus!`) get specs built on these.
18. **(Last) Review the differences from the library** once the Rust 1.100 update (rustlib branch `update-1.100.0`) builds and verifies,
    and after the other 1.100 items above:
    go through `diff -r library-1.100.0 verified-1.100.0`
    and undo changes that aren't needed (code that can match upstream again,
    workarounds Verus no longer needs, comments that describe version history instead of a difference from the library).
