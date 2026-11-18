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

### Later

7. **`ptr_specs.rs` TODOs:**
   - Remove `spec_ptr_addr`'s `rustc_diagnostic_item` once Travis's fix for the diagnostic item conflict is in.
   - Merge `mut_ref_from_parts` and `mut_ref_from_parts_slice` into one axiom over `T: ?Sized`
     (and `ref_from_parts` / `ref_to_parts` with their `_slice` versions, through a generic `pt_parts_wf`).
     Blocked: Verus doesn't know that a `&mut [T]`'s final length equals its current length.
8. **`SeqPointsTo` covariance:** `ptr: Ghost<*mut [T]>` makes it invariant in `T`.
   Options: a covariant ghost wrapper `CovariantPtr<T>` with two inverse axioms with `*mut T`,
   or separate ghost fields for the address, provenance and length.
   rustlib's `RawVec` / `Vec` covariance depends on this.
9. **Merge `verify-rustlib` into `verify-rustlib-refactor`**:
   take `verify-rustlib`'s side at the `TODO(verify-rustlib-transmute-v2)` spots,
   and drop the `SharedReference` parts of `TRUSTED_REVIEW.md` and `TODO.md` (`SharedReference` is deleted).

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
5. **Audit vstd's `assume_specification`s in the rustlib build**:
   for each one vstd builds under `verus_verify_core`,
   gate it with `#[cfg(not(verus_verify_core))]` and verify it in rustlib, or keep trusting it.
6. **Verify the axiomatized `Box` functions** (`Box::new_in`, `from_raw_in_untyped_with_typed_value`,
   `into_non_null_with_allocator_untyped_with_typed_value`) down to the allocator and raw-pointer specs.
   Blocked on Verus treating `Box` specially.
7. **Reorganize `specs/` and `proofs/`**: trusted items in `specs/`, helper proofs in `proofs/`.
8. **Covariance:**
   - `RawVec<T>` / `Vec<T>`, after verus item 8.
   - `LinkedList<T>` and its `IntoIter`:
     `LinkedListGhost::ptrs` is a `Seq<*mut Node<T>>`; use `*const Node<T>` or `NonNull<Node<T>>`,
     then restore std's `assert_covariance` check at the end of `linked_list.rs`.
