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

## rustlib side (later)

1. **Bring `port-raw-ptr-final` up to date with `main`.**
2. **Verify `read_unaligned` and `MaybeUninit`** (on hold since 2026-11-02).
   `read_unaligned_verus` (`core/src/ptr/mod.rs`) is still `external_body`.
   The design is [below](#design-verifying-read_unaligned-and-maybeuninit).
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

---

## Remaining `PointsTo` uses

**Trusted specs over `PointsTo` / `PointsToUnaligned`:**

- vstd's structural axioms (`points_to_structs.rs`):
  `PointsToUnaligned::from_raw_parts_ref` / `from_raw_parts_mut` and `PointsTo::from_raw_parts_mut`.
  They are field primitives of the structs, so they can't be stated over the parts.
- rustlib's `ptr::read_unaligned_verus` (`core/src/ptr/mod.rs`), over a `PointsToUnalignedArg`; on hold (below).

**Specs taking a `&mut PointsTo`:** none that could take a `Tracked<&mut T>`.
These change the value's validity, so they need the permission:

- `ptr::read_verus` and `NonNull::read_verus` move the value out, leaving the permission empty.
- `ptr::write_verus` writes to memory that may not hold a valid value.
- `PointsToUnalignedArg::Move` and `PointsToArg::Move` (`specs/ptr.rs`) move the value out.

vstd keeps `ptr_mut_ref` and `ptr_mut_ref_slice` for code outside rustlib.

**Specs taking or giving a shared `&PointsTo`:**

- `shr_ref_points_to`, `shr_ref_points_to_slice` (vstd) and `shr_ref_points_to_str` (rustlib) give a `&PointsTo` for a reference.
  About 25 rustlib proof bodies use them to reach the permission API (`subrange`, `borrow_index`, `as_big_*`, `ptr_bounds`, ...).
- `CopyPointsTo`, `CopyPointsToUnaligned` and `PointsToArg` (`specs/ptr.rs`); on hold (below).
- vstd keeps `ptr_ref`, `ptr_ref_slice`, `mut_ref_to_shr_points_to` and `mut_ref_to_shr_points_to_slice` for code outside rustlib.

The permission types' own methods (`as_aligned`, `borrow_index`, `subrange`, `as_big_*`, `as_bytes`, `is_disjoint_*`, ...)
are left out of these lists.

## Design: verifying `read_unaligned` and `MaybeUninit`

**On hold (2026-11-02), to come back to after the rest is implemented.**
Until then, `read_unaligned_verus` stays as it is now:
trusted (`external_body`), taking a `PointsToUnalignedArg`, so it is the one remaining trusted spec over `PointsToUnaligned`.
`MaybeUninit`, `CopyPointsToUnaligned` and vstd's `std_specs/maybe_uninit.rs` are unchanged.
So are their aligned counterparts in rustlib's `specs/ptr.rs`, `CopyPointsTo` and `PointsToArg`,
which still hold a `&PointsTo` (and, for `PointsToArg::Move`, a `&mut PointsTo`)
and have no users;
`CopyPointsTo::new` can't take a `Tracked<&T>` in their place,
since it stores the borrow in a struct field, where shadow data isn't tracked.

To check when this resumes:
whether Verus accepts an exec union field read under an `is_variant` precondition (`assume_init_verus`),
and whether anything else depends on `CopyPointsToUnaligned`'s layout.

**`read_unaligned`** (`core/src/ptr/mod.rs`): verified, following Rust's own body.

```rust
let mut tmp = MaybeUninit::<T>::uninit();
copy_nonoverlapping(src as *const u8, tmp.as_mut_ptr() as *mut u8, size_of::<T>());
tmp.assume_init()
```

`read_unaligned_verus` keeps its name and spec (taking a `PointsToUnalignedArg`) and loses `external_body`.
Its body is the above, with `copy_nonoverlapping_verus` (trusted, over `PointsToUntyped`, already exists)
and rustlib's own `MaybeUninit`, verified (below).

**`MaybeUninit`** (`core/src/mem/maybe_uninit.rs`): verified, only what `read_unaligned` reaches.

- **The union** moves into `verus!` as is (Verus supports unions, modelled with `is_variant` / `get_union_field`):
  ```rust
  pub union MaybeUninit<T> {
      uninit: (),
      value: ManuallyDrop<T>,
  }
  ```
  vstd's axiomatized `std_specs/maybe_uninit.rs` (`mem_contents`, and `assume_specification`s for `new`, `uninit`, `assume_init`, ...)
  is left out of the rustlib build (`#[cfg(not(verus_verify_core))]`); nothing in rustlib uses it.
- **`uninit`**: verified with its current body (`MaybeUninit { uninit: () }`).
  ```rust
  pub const fn uninit() -> (res: MaybeUninit<T>)
      ensures
          is_variant(res, "uninit"),
  ```
- **`as_mut_ptr_verus`** (new, trusted): `as_mut_ptr`'s body (`self as *mut _ as *mut T`), with the parts of a permission for `self`'s memory.
  This is the one new trusted function: it ties the bytes written through the pointer to the union's typed value.
  ```rust
  /// Returns a pointer to the contained value,
  /// with the parts of a permission for its memory.
  /// If the final parts are well-formed for the same pointer and valid,
  /// `self` finally holds the final value.
  #[verifier::external_body]
  pub const fn as_mut_ptr_verus(&mut self) -> ((ptr, pt_untyped, typed_value): (
      *mut T,
      Tracked<&mut PointsToUntyped>,
      Tracked<&mut TypedValue<T>>,
  ))
      ensures
          pt_parts_wf(ptr@, *pt_untyped@, *typed_value@),
          is_variant(*old(self), "value") ==> {
              &&& typed_value@.is_valid()
              &&& typed_value@.value() == get_union_field::<_, ManuallyDrop<T>>(*old(self), "value")@
          },
          !is_variant(*old(self), "value") ==> typed_value@.is_empty(),
          final(pt_untyped@).ptr() == pt_untyped@.ptr()
              && pt_parts_wf(ptr@, *final(pt_untyped@), *final(typed_value@))
              && final(typed_value@).is_valid() ==> {
              &&& is_variant(*final(self), "value")
              &&& get_union_field::<_, ManuallyDrop<T>>(*final(self), "value")@ == final(typed_value@).value()
          },
  ```
- **`assume_init_verus`** (new, verified):
  ```rust
  pub const unsafe fn assume_init_verus(self) -> (out: T)
      requires
          is_variant(self, "value"),
      ensures
          out == get_union_field::<_, ManuallyDrop<T>>(self, "value")@,
  {
      ManuallyDrop::into_inner(unsafe { self.value })
  }
  ```
  The original body reads `self.value` through a raw pointer (`(&raw const self.value).cast::<T>().read()`),
  which would need a permission for `self`'s own memory;
  reading the union field instead is equivalent (the original does it the raw way only for Miri's error messages).
  `ManuallyDrop::into_inner` uses vstd's existing `ManuallyDrop` specs.
  `intrinsics::assert_inhabited::<T>()` is left out: it only panics for an uninhabited `T`,
  and the precondition (a `value` variant, so a value of type `T` exists) rules that out.

The proof:
1. **Get the value.** `Move`: take the `TypedValue` out of the permission (`as_raw_parts_mut`), leaving `Empty`.
   `Copy`: a ghost copy of it (below).
2. **Borrow `tmp`'s memory** with `as_mut_ptr_verus`; it starts `Empty`, since `tmp` is `uninit`.
3. **Copy the bytes.** `copy_nonoverlapping_verus::<u8>` from the source's `PointsToUntyped` into `tmp`'s,
   so `tmp`'s bytes equal the source's, which decode to the value.
4. **Put the value** into `tmp`'s `TypedValue`, so the final parts are well-formed and valid,
   and `tmp` holds the value (variant `value`) once the borrow ends.
5. **`assume_init_verus`** returns it.

**`CopyPointsToUnaligned`** (`specs/ptr.rs`) needs to give the `Copy` case an owned copy of the value,
since `read_unaligned_verus` has no `T: Copy` bound.
Its `new` (which has `T: Copy`) stores a ghost copy (`TypedValue::tracked_copy`),
and it gets two verified functions (spec of `new` unchanged):

| Function | Ensures |
|---|---|
| `tracked_pt_untyped(tracked &self) -> &PointsToUntyped` | `*out == ` the permission's `pt_untyped()` |
| `into_typed_value(tracked self) -> TypedValue<T>` | `out == self.typed_value()` |

`pt_unaligned_parts_wf` then has no trusted users of its own; it's only part of `pt_parts_wf`'s definition.
