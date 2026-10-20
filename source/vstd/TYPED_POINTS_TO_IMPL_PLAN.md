# Implementation plan: `PTValueOps` trait and typed `SeqPointsTo` (level 3)

The phases for implementing the design in [TYPED_POINTS_TO_PLAN.md](TYPED_POINTS_TO_PLAN.md).
The design document has the target traits, impls, conversions and full specifications;
this document has the order of work, the phase 0 spike results, and the risks.
It supersedes GHOST_METADATA_PLAN.md, whose remaining steps are phases 2b, 3b, 4b and 5 here.

**Status.** Already done (from the earlier ghost metadata plan):
the `metadata` field,
the slice `PTPhys`/`PTProperties`/`View` impls,
and `abs_decode_slice`.
The empty slice functions were written as inherent functions,
then reverted and saved in [step3_slice_wip.patch](step3_slice_wip.patch);
their bodies move into the trait impls in phase 2b.
Phase 0 (the spike) is done; see [Phase 0 results](#phase-0-results).
See [Order](#order).

Each phase ends with both builds green (`source/tools/build-expand-errors.sh` and
`source/tools/build-verify-core.sh`) and is meant to be a separate commit, so the work can stop after
any phase with the tree in a good state.

## Phases

### Phase 0: spike the risky Verus features

In a scratch file, not `points_to_permissions.rs`, check the things this plan relies on but hasn't
verified:

1. A trait `proof fn` taking `tracked &mut self`, implemented on one type with a real body and on a
   wrapper type by delegating to a field (`self.pt_unaligned.take()`), with `final(self)` contracts.
   No existing test covers `tracked &mut self` in traits.
2. A generic impl bounded by an associated-type equality, `P: PTSizedValue<A = T>` (where `A`
   comes from `PTPhys`), and that `P::A` and `T` are interchangeable in specs.
3. How to say `Self::A: Sized` for `PTSizedValue`'s by-value methods: a trait-level
   `where Self::A: Sized` (may not be implied at use sites), per-method `where Self::A: Sized`, or
   relying on the generic `SeqPointsTo` impl's `T` being `Sized` together with `A = T`.
4. A trait method with a `where Self::A: Copy` bound.
5. Name resolution when a trait spec fn (`bytes`, `typed_value`) has the same name as the existing
   inherent `?Sized` spec fn on `PointsTo`/`PointsToUnaligned`. The inherent one should win in
   method syntax on concrete types and the trait one in generic code. If that causes trouble, rename
   the trait methods (e.g. `tp_bytes`).
6. Whether a trait `proof fn` can be `broadcast`. `PointsTo::lemma_ptrs_len_same_valid` is in
   `group_points_to_permissions_lemmas` today. If trait methods can't be broadcast, keep a small
   inherent broadcast wrapper per type that calls the trait lemma.

7. `Metadata<Self::A>` in trait signatures:
   that it normalizes to `()` in the `PointsTo<T>` impl and to `usize` in the `PointsTo<[T]>` impl,
   and that a generic caller with `P: PTSizedValue<A = T>` can pass `()`.
   (Generic Sized code already writes `metadata: ()` in `PtrData<T>`, e.g. `view_reverse_for_eq_sized`.)
   Also check the non-ghost build, where `Metadata<T>` is `FakeMetadata<T>`.
8. A generic inherent impl `impl<T: ?Sized> PointsToUnaligned<T> where PointsToUnaligned<T>:
   PTValueOps<A = T>` for the aligned/unaligned conversions,
   including `shr_ref_struct_wrap` in `as_aligned` with generic `T`.
9. Generic trait impls `impl<T: ?Sized> Trait for PointsTo<T> where PointsToUnaligned<T>:
   PTValueOps<A = T>` (for `PTPhys`, `PTProperties`, `View` and `PTValueOps`),
   instantiated at a Sized `T` and at `[T]`.
   Check that Verus accepts the `where` clause on a trait impl,
   that the alignment resolves correctly for each instantiation,
   and that a constructor (`from_untyped`) can call `into_aligned` from inside the impl
   without a recursion or cycle error.
   Also check that `FixedSize for PointsTo<T>` (Sized only) can sit next to the generic impls.

If (1) or (2) fails, stop and revisit the design before continuing.
If (7) or (8) fails, use the fallbacks in [Traits](TYPED_POINTS_TO_NOTES.md#traits).
If (9) fails, use the fallback in [The generic `PointsTo` impl](TYPED_POINTS_TO_NOTES.md#the-generic-pointsto-impl).

#### Phase 0 results

The spike is in [source/phase0_spike/](../phase0_spike/),
run with `source/tools/verify-spike-all.sh` (each file separately, against the built vstd).
It uses mock `PointsToUnaligned`/`PointsTo`/`SeqPointsTo` types
that implement vstd's real `PTPhys`, `PTProperties` and `FixedSize`,
with a Sized and a slice `PointsToUnaligned` impl,
and `PTValueOps`/`PTSizedValue` as in [Traits](TYPED_POINTS_TO_APPROVED.md#trait-definitions).
A deliberately wrong call (aligned slice `zero_sized` without the alignment precondition)
was checked to fail, so the passing results aren't vacuous.

| Item | Result | File | Notes |
|---|---|---|---|
| 1. `tracked &mut self` trait methods, delegation to a field, `final(self)` | works | `main.rs` | `take_typed_value`, `take` delegate through `self.pt_unaligned`. |
| 2. `P: PTSizedValue<A = T>`, `P::A` and `T` interchangeable | works | `main.rs` | Generic `take_at`/`copy_at` on the mock sequence, instantiated with aligned and unaligned elements. |
| 3. Expressing `Self::A: Sized` | use the associated type bound | `item3_assoc_bound.rs`, `item3_trait_where.rs` | `PTSizedValue: PTValueOps<A: Sized> + FixedSize` works and is implied at use sites, even with only `P: PTSizedValue`. A trait-level `where Self::A: Sized` is not implied (E0277) unless the use site states `A = T`. Per-method `where` also works but is noisier. |
| 4. `where Self::A: Copy` on a trait method | works | `main.rs` | `copy_typed_value`, called from generic code with `T: Copy`. |
| 5. Trait spec fn with the same name as an inherent `?Sized` one | works, with a caveat | `main.rs` | In an impl, `self.typed_value()` resolves to the inherent fn (no recursion), and on concrete types the two are provably equal. In generic code they aren't known equal, so generic delegations must name the trait fn. No rename needed. |
| 6. Broadcast trait lemmas | works, through the trait path | `item6_*.rs` | A trait can declare a `broadcast proof fn`. A broadcast group must name the trait method (`Lemmas::lemma_good`); it then fires for every impl, in generic and concrete code. Naming the impl path (`Mock::lemma_good`) is "not found", and `broadcast use P::lemma` / `<P as Lemmas>::lemma` in a generic fn is E0401. The inherent-wrapper fallback also works. Impl-side broadcast fns warn about missing triggers (harmless; the trigger is on the declaration). |
| 7. `Metadata<Self::A>` in trait signatures | works (ghost build) | `main.rs` | Impls can write `()` (Sized) and `usize` (slices) directly; a generic Sized caller passes `()` (`P::size_for(())`). The non-ghost build (`FakeMetadata`) wasn't tested here; these are all spec/proof signatures, which the existing `?Sized` `PointsToUnaligned::metadata` already has. |
| 8. Generic aligned/unaligned impl, incl. `shr_ref_struct_wrap` | works | `main.rs` | Bounded only by `PointsToUnaligned<T>: PTValueOps<A = T>`; checked at a Sized type and a slice. |
| 9. Generic trait impls for `PointsTo` | works | `main.rs` | Generic `PTPhys`/`PTProperties`/`PTValueOps` for `PointsTo<T: ?Sized>`, next to Sized-only `FixedSize`/`PTSizedValue`. The alignment, `spec_align_of_val::<T>(arbitrary())`, reduces to `align_of::<u32>()` / `align_of::<u16>()` at `u32` / `[u16]` via `layout_of_sized` / `layout_of_slices` (and to 1 for `str` via `layout_of_str`, `align_unsized.rs`), so no `align()` hook is needed. `zero_sized` calls `into_aligned` inside the impl without a cycle error. Requires `satisfies_alignment` to include the unaligned `satisfies_alignment` (see [Traits](TYPED_POINTS_TO_APPROVED.md#trait-definitions)). |

Follow-up checks:

| Check | Result | File | Notes |
|---|---|---|---|
| Alignment without an `align()` hook | works | `align_unsized.rs`, `main.rs` | `spec_align_of_val::<T>(arbitrary())` reduces to `align_of::<T>()` for both `T` and `[T]`, and 1 for `str`, via the existing layout axioms. |
| `size` defined as `Self::size_for(..)` (cross-trait) | rejected | `size_cycle.rs` | "recursive function must have a decreases clause" on `size`. |
| `size`/`const_size`/`size_for` through an inherent `size_of_metadata` | works | `size_inherent.rs` | `lemma_size` and `lemma_const_size` have empty proofs, and generic code gets `x.size() == P::const_size()` from them. |

Other findings:

- **Impl type-parameter names must match the trait's.**
  Renaming `is_disjoint<OtherPointsToPerm>` to `is_disjoint<O>` in an impl
  crashes Verus ("generated ill-typed AIR code": undeclared `OtherPointsToPerm`).
  The existing impls already use the trait's names; keep doing so.
- **Not covered by the spike:**
  verification time and trigger behavior at real scale (phase 3's risk),
  broadcast cyclicity with `group_vstd_default`,
  and the non-ghost build.
- The spike was written before the [`SeqPointsTo` pointer change](TYPED_POINTS_TO_NOTES.md#seqpointstos-pointer-and-sizes),
  so it still uses `FixedSize`, `size(self)` and a per-trait `size_for`.
  The size rows above are superseded by that design; the other results don't depend on it.

#### Phase 0 pending checks

These cover the [`SeqPointsTo` pointer change](TYPED_POINTS_TO_NOTES.md#seqpointstos-pointer-and-sizes),
[`PointsToRaw`](TYPED_POINTS_TO_NOTES.md#pointstoraw) and [`wf_basic` and `wf`](TYPED_POINTS_TO_NOTES.md#wf_basic-and-wf).

10. **The new `SeqPointsTo` shape.**
    - *Done:* a generic inherent impl `impl<T, P: Typed<A = T>> Seq2<T, P>`
      next to `impl Seq2<u8, Byte>` (where `Byte` doesn't implement `Typed`),
      both defining `wf`, is accepted, with no E0592 (`seq_overlap.rs`).
      A struct bound `P: Phys<A = T>` forces `#[verifier::reject_recursive_types(T)]`,
      which would reject types like `struct Tree { children: Vec<Tree> }` (`recursive_types.rs`).
      So the struct bound is `P: PTProperties` with `accept_recursive_types(T)`,
      and `A = T` goes on the impls.
    - *Done* (`seq_shape.rs`, verifies): the full struct with `ptr: Ghost<*mut [T]>`,
      `PTPhys::size(len) = len * P::size(())`, `wf_basic` with the metadata clause and today's provenance clause,
      and `empty` / `from_seq` / `split_basic` with their thin-pointer (`ptr() as *mut T`) contracts, generic over `P`.
      For generic Sized `T`, `ptr()@.metadata == ()` is known, so elements' `P::size(metadata)` matches `P::size(())`;
      `split_basic`'s address bound comes from an element's `ptr_bounds`; a few `nonlinear_arith` steps are needed.
11. **`PointsToRaw`'s representation.**
    - *Known:* `#[verifier::type_invariant]` works on tracked structs
      (`raw_ptr.rs` line 370, with `use_type_invariant` in proof fns).
    - *Done* (`raw_range.rs`, verifies): a `Map<int, Byte>` with a type invariant,
      and the recursive helper that removes a contiguous range's bytes, in address order, into a `Seq`.
12. **Generic `PTProperties` and `wf` for `PointsToUnaligned`.**
    - *Done:* trait default bodies for `spec` and `proof` fns are accepted on this branch
      (the trait needs `Sized`, which `PTPhys` has),
      and a concrete type that doesn't override sees the default.
      But a default spec body does **not** unfold in generic code,
      nor inside a default proof body (`default_methods.rs`),
      presumably because an impl may override it.
      So `PTValueOps::wf` may be a default body (written once),
      but generic code gets its facts only from the trait lemmas
      (`bytes_decode`, `satisfies_alignment_of_wf`, `lemma_wf_basic`),
      which need per-impl proofs (empty, since `wf` unfolds at the concrete type).
    - *Dropped:* a generic `impl<T: ?Sized> PTProperties for PointsToUnaligned<T>`
      next to per-type `PTPhys` impls.
      Its delegations need the per-type `wf_basic` and `ptr` bodies, which by the result above
      don't unfold in generic code, so `PTProperties` is per type, like `PTPhys`.
13. **Default proof bodies that call other trait methods.**
    *Known (no spike needed):* default proof bodies that only call other trait methods
    and use their contracts are fine. This covers the proof defaults in the trait
    (`borrow`, `into_untyped`, `from_untyped`, `zero_sized`, `take`, `put`, `copy`, `copy_typed_value`,
    `from_untyped_with_value`). It differs from what `default_methods.rs` tested,
    a default proof body that needed a default *spec* body to unfold (which fails).
14. **Dropping `SeqPointsTo`'s `T` parameter** (`SeqPointsTo<P>` with `ptr: Ghost<*mut [P::A]>`,
    to avoid repeating `<A = T>` in every bound).
    - *Done, rejected* (`seq_drop_t.rs`): Verus's Trait-Conflict-Checker reports
      "the size for values of type `<P as Phys>::A` cannot be known at compilation time"
      for `*mut [P::A]` in the struct field and in `type A = [P::A]`,
      whether the bound is written `P: Phys<A: Sized>`, `where P::A: Sized`,
      or through a subtrait with `Phys<A: Sized>` as supertrait. rustc accepts all three.
      So `SeqPointsTo` keeps `T`, with `P: PTProperties<A = T>` on the impls (item 10).
15. **Child-module access** (for `points_to_ops` under `points_to_model`).
    - *Done* (`child_module_access.rs`, verifies): a child module can build a struct literal
      from the parent's private fields, unfold the parent's `closed` specs,
      and return disjoint `&mut` borrows of two private fields (the shape of `as_raw_parts_mut`).
    - *Done* (`child_module_access_neg.rs`): a sibling module can't
      (private field: rustc E0616; `closed` body: doesn't unfold).
16. **`TypedValue::valid_ref` from `tracked_ref`.**
    - *Done* (`valid_ref.rs`, verifies): with a local `tracked_ref` axiom,
      `shr_ref_struct_wrap(t, &TypedValue::Valid(*t), "Valid", "0")` proves `valid_ref`
      for `T: ?Sized`, used at `u64` and at `str`.
17. **The generic `PointsTo` impl with default `wf`.**
    - *Done* (`generic_wf_delegate.rs`): with `wf` as the trait default,
      the generic impl can't delegate its lemmas to `pt_unaligned`:
      `pt_unaligned.wf()` is a default body at a generic type, so it doesn't unfold
      and can't be built from the parts of `self.wf()`.
      (`PointsTo`'s own default `wf` does unfold inside its impl.)
      Overriding `wf` as `self.pt_unaligned().wf()` plus alignment verifies, delegating every lemma.
      So the generic `PointsTo` overrides `wf`, and `ptrs_len_same_valid` for the same reason;
      `PointsToUnaligned` keeps the defaults.
    - *Done* (`recursive_points_to.rs`, verifies): today's `PointsTo<T>` allows recursive types
      (`PointsTo<Node>`, `PointsTo<[Node]>` inside `Node`) with no attribute.

### Phase 1: structural generalization and module layout (assessment section 1, groups 1-3)

Independent of the trait.
The design is in [Module layout](TYPED_POINTS_TO_NOTES.md#module-layout).

- Rename `PointsToSingleton` to `PointsToByte` (and `PointsToSingletonData` to `PointsToByteData`),
  so it isn't confused with `PTValueOps`.
  Purely mechanical; also update the docs that mention it
  (`PORTING_STATUS.md`, `POINTS_TO_MIGRATION.md`, `GENERALIZATION_ASSESSMENT.md`).
- Create the `raw_ptr` directory ([Module layout](TYPED_POINTS_TO_APPROVED.md#module-layout)):
  split `raw_ptr_new.rs` into `ptr_model.rs` and `ptr_specs.rs`,
  and `points_to.rs` / `points_to_permissions.rs` into `points_to_model.rs`,
  `points_to_ops.rs` (a child module of `points_to_model`) and `points_to_collections.rs`;
  move `shared_reference.rs` in; `mod.rs` re-exports everything,
  and importers (vstd and rustlib) switch to `vstd::raw_ptr`.
  The old `raw_ptr.rs` is replaced.
  Child-module access is confirmed ([phase 0 item 15](#phase-0-pending-checks)).
- Move `tracked_seq_pt`, `tracked_seq_pt_mut`, `index_mut`, `from_seq`, `empty`, `into_seq` into the
  structural `impl<T, P> SeqPointsTo<T, P>` (in `points_to_ops.rs`), stated with `wf_basic()` and `P::size(())`
  (after phase 1b; `P::const_size()` if phase 1 lands first).
  No typed versions with the same names (they'd be E0592 duplicates);
  typed callers get element `wf` by unfolding the typed `wf`.
- Add `split_basic`, `join_basic`, `subrange_basic` to the structural impl,
  and make the typed `split` / `join` / `subrange` and `PointsToUntyped`'s `split` / `join` / `split_ref`
  wrappers over them.
- Rewrite the remaining typed field uses
  (`zero_sized_helper`, `into_untyped_with_typed_value`, `as_untyped_mut`, the borrow helpers)
  with the structural functions, so the typed impl compiles from `points_to_collections.rs`.
- Keep the specialized `is_disjoint_seqpt` and `PointsToUntyped::is_disjoint_untyped`
  (no generic `is_disjoint_seq`).
- Update call sites and verify.

### Phase 1b: `SeqPointsTo`'s slice pointer, `size(metadata)`, no `FixedSize`

The design is in [`SeqPointsTo`'s pointer and sizes](TYPED_POINTS_TO_NOTES.md#seqpointstos-pointer-and-sizes).
[Phase 0 check 10](#phase-0-pending-checks) is done (`seq_shape.rs`).
Independent of the new traits; it changes existing ones.

1. `PTPhys::size(self)` becomes `size(metadata: Metadata<Self::A>)` in every existing impl:
   `PointsToSingleton`/`PointsToByte` (`1`), `PointsToUnaligned<T>` / `PointsTo<T>` (`size_of::<T>()`),
   `PointsToUnaligned<[T]>` / `PointsTo<[T]>` (`len * size_of::<T>()`),
   `SeqPointsTo` (`len * P::size(())`).
   Rewrite `x.size()` uses as `X::size(x.ptr()@.metadata)`,
   starting with `PTProperties`' own contracts.
2. `SeqPointsTo`: `ptr: Ghost<*mut [T]>`, struct bound `P: PTProperties`
   (with `#[verifier::accept_recursive_types(T)]`; impls bound `P: PTProperties<A = T>`),
   `wf_basic` gains `ptr()@.metadata == len()`;
   `PointsToUntyped = SeqPointsTo<u8, PointsToByte>`, and its `wf()` loses the clause that moved.
3. Remove `FixedSize`: `P::const_size()` → `P::size(())`; drop the `size_eq_const_size` calls.
4. Add `thin_ptr` (`self.ptr() as *mut T`) to `SeqPointsTo<T, PointsTo<T>>` in `points_to_collections.rs`,
   and restate the pointer contracts
   ([`SeqPointsTo`'s pointer and sizes](TYPED_POINTS_TO_NOTES.md#seqpointstos-pointer-and-sizes)):
   constructors from a thin pointer (`from_seq`, `empty`, `zero_sized`/`zero_sized_helper`)
   state it with `ptr() as *mut T` or `thin_ptr()`;
   `split`, `join`, `subrange`, `subrange_mut` (and their `_basic` versions) state the full `*mut [T]`;
   `from_untyped`, `from_untyped_with_typed_value` state the address and provenance;
   `untyped_mut_join` keeps a thin `base`;
   and the `View` / `SeqPointsToData` `ptr` field is `thin_ptr()`.
5. rustlib uses these types; update its call sites in the same change (not visible from this repo).
6. Verify both builds.

### Phase 2: introduce the traits and the Sized impls

The `metadata` field is already in, so moved bodies include it from the start.

1. Add `TypedValue::value_ref` (`?Sized`). Restate the existing decode clauses with it where that
   simplifies things. `TypedValue<T>::value()` and `TypedValue<[T]>::value()` can stay as they are.
2. Add `PTValueOps` and `PTSizedValue` next to `PTProperties` in `points_to_model.rs`.
3. `PointsToUnaligned`'s pointer and `PTProperties` ([`wf_basic` and `wf`](TYPED_POINTS_TO_NOTES.md#wf_basic-and-wf)):
   build `ptr` from the stored metadata in both `PTPhys` impls (Sized and slice),
   and replace the two `PTProperties` impls with one generic impl
   whose `wf_basic` is only `pt_untyped().wf()` and the byte count.
   The decode, length and metadata clauses leave `wf_basic`:
   for Sized `T` into `PTValueOps::wf` (next step);
   for slices into the existing inherent `PointsToUnaligned<[T]>::wf` until phase 2b.
   Restate Sized pointer contracts on `@.addr` / `@.provenance` where the cast-based proofs break.
   Rename `PTProperties::ptrs_len_same_valid` to `ptrs_len_same` (pointer-level, no decoding)
   in every impl, including `SeqPointsTo`'s and `PointsToUntyped`'s
   (whose lemma becomes `lemma_ptrs_len_same_untyped`);
   the decoding version becomes `PTValueOps::ptrs_len_same_valid` in the next step,
   and the typed `SeqPointsTo` gets an inherent `ptrs_len_same_valid` over its elements'.
4. `impl<T> PTValueOps + PTSizedValue for PointsToUnaligned<T>`: real bodies. Most are today's
   `PointsTo<T>` bodies with `self.pt_unaligned.` removed.
   `wf` is the formula in [`wf_basic` and `wf`](TYPED_POINTS_TO_NOTES.md#wf_basic-and-wf), `metadata_matches` is `true`,
   `satisfies_alignment` is `true`, and `from_untyped` loses its alignment precondition.
5. `impl<T> PTValueOps for PointsTo<T>` (Sized only for now):
   one-line delegations to `self.pt_unaligned`,
   except `satisfies_alignment(addr)` (`PointsToUnaligned::<T>::satisfies_alignment(addr) && addr as nat % spec_align_of_val::<T>(arbitrary()) == 0`)
   and `from_untyped` (`PointsToUnaligned::from_untyped(u, m).into_aligned()`).
   Write it in the shape of [the generic impl](TYPED_POINTS_TO_NOTES.md#the-generic-pointsto-impl),
   so phase 2b only has to widen `impl<T>` to `impl<T: ?Sized> ... where ...`.
   It can't be generic yet: a `?Sized` `PTValueOps` impl needs `?Sized` supertrait impls,
   and those would drop `PointsTo<[T]>`'s existing ones until `PointsToUnaligned<[T]>` has the trait.
6. `impl<T> PTSizedValue for PointsTo<T>`: delegations, plus `lemma_satisfies_alignment_offset`,
   which is the `lemma_mul_mod_noop_right`/`lemma_add_mod_noop`/`layout_of_sized` argument
   currently inlined in `split`/`subrange`/`from_untyped_with_typed_value`.
7. Remove the inherent `PointsTo<T>` / `PointsToUnaligned<T>` versions of the moved functions,
   including the inherent `wf` and `stays_wf`:
   inherent fns win over trait fns at concrete types (phase 0, item 5),
   and the old inherent `wf` (= `wf_basic`) would shadow the trait's `wf` with a different meaning.
   Keep `is_aligned`, `value`, `is_disjoint_pointsto`
   (`into_unaligned`/`as_unaligned` move to the generic conversion impl).
8. Callers outside the module need the traits in scope for method syntax.
   Re-export `PTPhys`, `PTProperties`, `PTValueOps` and `PTSizedValue`
   from `points_to_permissions.rs` (not the prelude),
   then grep for uses of the moved methods (`raw_ptr_new.rs`, `shared_reference.rs`, rustlib, ...)
   and make sure those files import `points_to_permissions::*` (or the traits).
9. If any trait method ends up on the dependency path of a broadcast group, its proofs use the
   specific groups `{group_raw_ptr_axioms, group_layout_axioms, group_seq_axioms}`, never
   `group_vstd_default`, to avoid cyclicity errors (as the existing trait impls already do).
10. Verify. At this point `SeqPointsTo<T, PointsTo<T>>` is unchanged and just calls trait methods on
   its elements.

### Phase 2b: slice impls

1. `impl<T> PTValueOps for PointsToUnaligned<[T]>`,
   reusing the bodies of the empty slice functions,
   which were reverted and saved in [step3_slice_wip.patch](step3_slice_wip.patch).
   Its `size(len)` (`len * size_of::<T>()`) is already there from phase 1b,
   `satisfies_alignment` is `true`, and `metadata_matches(v, len)` is `v@.len() == len`.
   The inherent `PointsToUnaligned<[T]>::wf` from phase 2, step 3, is replaced by the trait's `wf`.
2. Make the `PointsTo` impls generic ([The generic `PointsTo` impl](TYPED_POINTS_TO_NOTES.md#the-generic-pointsto-impl)):
   widen phase 2's `PTValueOps for PointsTo<T>` to `T: ?Sized`,
   and replace the per-type `PTPhys`/`PTProperties`/`View` impls
   for `PointsTo<T>` and `PointsTo<[T]>` with one generic impl each.
   `PointsTo<[T]>` then has the trait with no slice-specific code.

`borrow` is a trait method, so it comes with this phase.
For slices it is a field borrow of `Valid(t)`,
the same way `TypedValue<[T]>::value()` already reads `&*self->0`.
This needs `Tracked`'s `Deref` to take `A: ?Sized`.
builtin's does, and so does rustlib's const impl used under `verus_verify_core`
(`impl<A: ?Sized> const Deref for Tracked<A>` in `verified-1.95.0/core/src/ops/deref.rs`).
The inherent slice functions and their `_slice`-suffixed lemmas are dropped,
and so is the `PointsTo::<T>::zero_sized` turbofish they needed.

### Phase 2c: `PointsToRaw`

The design is in [`PointsToRaw`](TYPED_POINTS_TO_NOTES.md#pointstoraw). [Phase 0 check 11](#phase-0-pending-checks) is done (`raw_range.rs`).

1. The struct, its type invariant, and the specs `provenance`, `dom`, `is_range`, `contains_range`.
2. `empty`, `split`, `join`, `ptr_bounds`, `provenance_not_none` (renamed from `provenance_non_null`), `is_disjoint`.
3. `from_untyped(PointsToUntyped) -> PointsToRaw` and `into_untyped(start, len) -> PointsToUntyped`.
   These only need phase 1b, so they can land earlier.
   There are no typed conversions on `PointsToRaw`: typed permissions go through `PointsToUntyped`.

All of `PointsToRaw` goes in `points_to_collections.rs` (it is verified);
it uses `PointsToUntyped` only through `from_seq` / `into_seq`.
4. Port `allocate` and `deallocate` (trusted), returning and taking a `PointsToUntyped`
   for the whole allocation, so nothing trusted depends on `PointsToRaw`.
   `Dealloc` is dropped:
   `ProvenanceData::orig_size` replaces its tracking of the original allocation size.
   They go in `ptr_specs.rs`.
5. Add the trusted items to `POINTS_TO_AXIOMS.md` and note the removed `PointsToRaw` axioms.

### Phase 3: typed `SeqPointsTo`

No generalization: there is no `SeqPointsTo<T, PointsToUnaligned<T>>`,
so the typed impl stays `impl<T> SeqPointsTo<T, PointsTo<T>>`.

1. Update it for the phase 2 traits: calls to removed inherent `PointsTo<T>` methods
   become trait method calls (`PointsTo<T>`'s open specs still unfold).
2. Rename `borrow_value_subrange` to `borrow_subrange`.
3. Keep `subrange_mut` as an axiom until phase 3b proves it.

### Phase 3b: borrowed-assembly axioms

The design is in [Borrowed-assembly axioms](TYPED_POINTS_TO_PLAN.md#borrowed-assembly-axioms-phase-3b).
Needs phases 2b and 3.

1. Both assumptions are confirmed:
   `shr_ref_struct_wrap` accepts `tracked_ref`'s `&Tracked<T>` for `Valid`'s field,
   for `T: ?Sized` (phase 0 item 16),
   and disjoint `&mut` field borrows work from the struct's module or a child (phase 0 item 15).
2. Add the shared axioms (`tracked_slice_index`, `tracked_ref`,
   `from_raw_parts_ref`, `TypedValue::<[T]>::from_elems_ref`), then prove `TypedValue::valid_ref`.
3. Add M1 and M3–M5.
4. Prove the existing axiom that becomes provable, and remove it:
   `SeqPointsTo::subrange_mut` (M5), staying on `SeqPointsTo<T, PointsTo<T>>`.
   Restore `PointsToUntyped::split_mut` (M5 and `Seq::tracked_split_borrow_mut`).
   `PointsToUntyped::join_ref` and `join_mut` stay axioms.
5. Prove `as_aligned_mut` (M4).

### Phase 4: sequence → slice and slice indexing

Needs phase 3b's axioms (`from_raw_parts_ref`, `tracked_slice_index`, `from_elems_ref`, M1, M3–M5).
The design is in [Sequence → slice conversions](TYPED_POINTS_TO_PLAN.md#sequence--slice-conversions-phase-4).

1. `PointsToUnaligned::as_raw_parts_mut` in `points_to_ops.rs` (disjoint field borrows).
2. The sequence → slice conversions, `SeqPointsTo<T, PointsTo<T>>` → `PointsTo<[T]>` (`&` and `&mut`),
   as described in the design.
3. `borrow_index` on `PointsToUnaligned<[T]>`, and on `PointsTo<[T]>` through the aligned/unaligned conversions.

### Phase 4b: restore the slice reference helpers

These are where valid slice permissions come from:
a real `&[T]` or `&mut [T]` supplies the tracked `[T]`.
Restore the commented-out:

- `SharedReference<[T]>::points_to` (`shared_reference.rs:126`): `&[T]` → `&PointsTo<[T]>`,
  and `ptr_ref2_slice_ghost` (`:221`), the way back;
- `mut_ref_to_shr_points_to_slice` (`raw_ptr_new.rs:683`): `&&mut [T]` → `&PointsTo<[T]>`;
- `ptr_ref_slice` and `ptr_mut_ref_slice` (`raw_ptr_new.rs:524`, `:559`),
  which go back from a pointer and a permission to a real reference.

Update their contracts to the new specs, and review them when they're restored
(they are trusted; where they go is part of the open placement decision in the design's Overview).

### Phase 5: docs

- `PORTING_STATUS.md`: replace the "Port `impl<T> PointsTo<[T]>`" TODO and the unaligned-slices on-hold item;
  note that `cast_points_to` / `cast_points_to_unaligned` now have a home.
- `POINTS_TO_MIGRATION.md` §7–8: `PointsTo<[T]>` exists again for whole-slice values
  (and `borrow` for `&[T]`, listed as "Not possible" in §7);
  per-element validity is still `SeqPointsTo`.
- `POINTS_TO_AXIOMS.md`: the phase 3b axioms and `abs_decode_slice`
  (the slice-level ones may belong in `slice.rs`'s own docs instead),
  the removed axioms (`join_ref`, `join_mut`, `subrange_mut`, `PointsToRaw`'s),
  and any axiom whose scope changed.
- `GENERALIZATION_ASSESSMENT.md`: mark level 3 done, and the §2 `ptr()` blocker resolved for slices.
- Delete GHOST_METADATA_PLAN.md (superseded).

## Order

| # | Step | Status | Why here |
|---|---|---|---|
| 1 | The `metadata` field; slice `PTPhys`/`PTProperties`/`View` impls; `abs_decode_slice` | done | Don't depend on the trait. |
| 2 | Phase 0: spike | done ([results](#phase-0-results)) | Settles the trait mechanics first. |
| 3 | Phase 1: structural generic `SeqPointsTo` | next | Independent; small. |
| 3b | Phase 1b: `SeqPointsTo` slice pointer, `size(metadata)`, no `FixedSize` | | Before phase 2, which writes the new traits against `PTPhys::size(metadata)`. |
| 4 | Phase 2: traits + Sized impls | | Fixes the API the slice impls implement. |
| 5 | Phase 2b: slice impls | bodies in `step3_slice_wip.patch` | Uses the trait from row 4. |
| 5b | Phase 2c: `PointsToRaw` | | Only needs row 3b; `allocate` / `deallocate` use `PointsToUntyped`. |
| 6 | Phase 3: typed `SeqPointsTo` on the new traits | | Small; can merge into phase 2. |
| 7 | Phase 3b: borrowed-assembly axioms; prove `subrange_mut` and `split_mut` | | Needs rows 5-6. |
| 8 | Phase 4 and phase 4b | | Both build on row 7. |
| 9 | Phase 5: docs | | |
| 10 | rustlib: `str` impls and conversions | | See [`str` in rustlib](TYPED_POINTS_TO_NOTES.md#str-in-rustlib). Needs rows 5 and 7. |

Row 3 can move later without affecting the slice work.

## Risks

- **Phase 0 failures.** `tracked &mut self` in trait methods, associated-type equality bounds, and
  expressing `Self::A: Sized` are the load-bearing assumptions.
  The generic `PointsTo` impl (item 9) is not load-bearing:
  its fallback is per-type delegating impls, at the cost of the duplication it avoids.
- **Broadcast cyclicity.** Moving lemmas into traits can change which functions are on a broadcast
  group's dependency path. The latest commit (`cd02a6bae`) already had to fix cyclicity errors of
  this kind.
- **Verification time.** Generic proofs with trait-bounded quantifiers can be slower; watch for
  timeouts in the byte lemmas.
