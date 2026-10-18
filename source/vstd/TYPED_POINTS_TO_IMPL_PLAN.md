# Implementation plan: `PointsToSingleValue` trait and a generic typed `SeqPointsTo` (level 3)

The phases for implementing the design in [TYPED_POINTS_TO_PLAN.md](TYPED_POINTS_TO_PLAN.md),
and how they interleave with [GHOST_METADATA_PLAN.md](GHOST_METADATA_PLAN.md).
The design document has the target traits, impls, conversions and full specifications;
this document has the order of work, the phase 0 spike results, and the risks.

**Status.** Ghost metadata steps 1, 2 and 4 are done
(the `metadata` field,
the slice `PointsToPhys`/`PointsToProperties`/`View` impls,
and `abs_decode_slice`).
Ghost step 3 (empty slice permissions) was written as inherent functions,
then reverted and saved in [step3_slice_wip.patch](step3_slice_wip.patch).
This plan now comes before the rest of the ghost metadata plan,
so that the slice functions are trait impls with shared contracts,
and there are fewer separate specs to review.
Step 3's bodies move into the trait impls in phase 2b.
Phase 0 (the spike) is done; see [Phase 0 results](#phase-0-results).
See [Combined order](#combined-order).

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
2. A generic impl bounded by an associated-type equality, `P: PointsToSingleValueSized<A = T>` (where `A`
   comes from `PointsToPhys`), and that `P::A` and `T` are interchangeable in specs.
3. How to say `Self::A: Sized` for `PointsToSingleValueSized`'s by-value methods: a trait-level
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
   that it normalizes to `()` in the `PointsTo<T>` impl and to `usize` in the `PointsTo<[E]>` impl,
   and that a generic caller with `P: PointsToSingleValueSized<A = T>` can pass `()`.
   (Generic Sized code already writes `metadata: ()` in `PtrData<T>`, e.g. `view_reverse_for_eq_sized`.)
   Also check the non-ghost build, where `Metadata<T>` is `FakeMetadata<T>`.
8. A generic inherent impl `impl<T: ?Sized> PointsToUnaligned<T> where PointsToUnaligned<T>:
   PointsToSingleValue<A = T>` for the aligned/unaligned conversions,
   including `shr_ref_struct_wrap` in `as_aligned` with generic `T`.
9. Generic trait impls `impl<T: ?Sized> Trait for PointsTo<T> where PointsToUnaligned<T>:
   PointsToSingleValue<A = T>` (for `PointsToPhys`, `PointsToProperties`, `View` and `PointsToSingleValue`),
   instantiated at a Sized `T` and at `[E]`.
   Check that Verus accepts the `where` clause on a trait impl,
   that the alignment resolves correctly for each instantiation,
   and that a constructor (`from_untyped`) can call `into_aligned` from inside the impl
   without a recursion or cycle error.
   Also check that `FixedSize for PointsTo<T>` (Sized only) can sit next to the generic impls.

If (1) or (2) fails, stop and revisit the design before continuing.
If (7) or (8) fails, use the fallbacks in [Two traits](TYPED_POINTS_TO_PLAN.md#two-traits).
If (9) fails, use the fallback in [The generic `PointsTo` impl](TYPED_POINTS_TO_PLAN.md#the-generic-pointsto-impl).

#### Phase 0 results

The spike is in [source/phase0_spike/](../phase0_spike/),
run with `source/tools/verify-spike-all.sh` (each file separately, against the built vstd).
It uses mock `PointsToUnaligned`/`PointsTo`/`SeqPointsTo` types
that implement vstd's real `PointsToPhys`, `PointsToProperties` and `FixedSize`,
with a Sized and a slice `PointsToUnaligned` impl,
and `PointsToSingleValue`/`PointsToSingleValueSized` as in [Two traits](TYPED_POINTS_TO_PLAN.md#two-traits).
A deliberately wrong call (aligned slice `zero_sized` without the alignment precondition)
was checked to fail, so the passing results aren't vacuous.

| Item | Result | File | Notes |
|---|---|---|---|
| 1. `tracked &mut self` trait methods, delegation to a field, `final(self)` | works | `main.rs` | `take_typed_value`, `take` delegate through `self.pt_unaligned`. |
| 2. `P: PointsToSingleValueSized<A = T>`, `P::A` and `T` interchangeable | works | `main.rs` | Generic `take_at`/`copy_at` on the mock sequence, instantiated with aligned and unaligned elements. |
| 3. Expressing `Self::A: Sized` | use the associated type bound | `item3_assoc_bound.rs`, `item3_trait_where.rs` | `PointsToSingleValueSized: PointsToSingleValue<A: Sized> + FixedSize` works and is implied at use sites, even with only `P: PointsToSingleValueSized`. A trait-level `where Self::A: Sized` is not implied (E0277) unless the use site states `A = T`. Per-method `where` also works but is noisier. |
| 4. `where Self::A: Copy` on a trait method | works | `main.rs` | `copy_typed_value`, called from generic code with `T: Copy`. |
| 5. Trait spec fn with the same name as an inherent `?Sized` one | works, with a caveat | `main.rs` | In an impl, `self.typed_value()` resolves to the inherent fn (no recursion), and on concrete types the two are provably equal. In generic code they aren't known equal, so generic delegations must name the trait fn. No rename needed. |
| 6. Broadcast trait lemmas | works, through the trait path | `item6_*.rs` | A trait can declare a `broadcast proof fn`. A broadcast group must name the trait method (`Lemmas::lemma_good`); it then fires for every impl, in generic and concrete code. Naming the impl path (`Mock::lemma_good`) is "not found", and `broadcast use P::lemma` / `<P as Lemmas>::lemma` in a generic fn is E0401. The inherent-wrapper fallback also works. Impl-side broadcast fns warn about missing triggers (harmless; the trigger is on the declaration). |
| 7. `Metadata<Self::A>` in trait signatures | works (ghost build) | `main.rs` | Impls can write `()` (Sized) and `usize` (slices) directly; a generic Sized caller passes `()` (`P::size_for(())`). The non-ghost build (`FakeMetadata`) wasn't tested here; these are all spec/proof signatures, which the existing `?Sized` `PointsToUnaligned::metadata` already has. |
| 8. Generic aligned/unaligned impl, incl. `shr_ref_struct_wrap` | works | `main.rs` | Bounded only by `PointsToUnaligned<T>: PointsToSingleValue<A = T>`; checked at a Sized type and a slice. |
| 9. Generic trait impls for `PointsTo` | works | `main.rs` | Generic `PointsToPhys`/`PointsToProperties`/`PointsToSingleValue` for `PointsTo<T: ?Sized>`, next to Sized-only `FixedSize`/`PointsToSingleValueSized`. The alignment, `spec_align_of_val::<T>(arbitrary())`, reduces to `align_of::<u32>()` / `align_of::<u16>()` at `u32` / `[u16]` via `layout_of_sized` / `layout_of_slices` (and to 1 for `str` via `layout_of_str`, `align_unsized.rs`), so no `align()` hook is needed. `zero_sized` calls `into_aligned` inside the impl without a cycle error. Requires `satisfies_alignment` to include the unaligned `satisfies_alignment` (see [Two traits](TYPED_POINTS_TO_PLAN.md#two-traits)). |

Follow-up checks:

| Check | Result | File | Notes |
|---|---|---|---|
| Alignment without an `align()` hook | works | `align_unsized.rs`, `main.rs` | `spec_align_of_val::<T>(arbitrary())` reduces to `align_of::<T>()`, `align_of::<E>()`, 1 for `str` via the existing layout axioms. |
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
- The spike was written before the [`SeqPointsTo` pointer change](TYPED_POINTS_TO_PLAN.md#seqpointstos-pointer-and-sizes),
  so it still uses `FixedSize`, `size(self)` and a per-trait `size_for`.
  The size rows above are superseded by that design; the other results don't depend on it.

#### Phase 0 pending checks

These cover the [`SeqPointsTo` pointer change](TYPED_POINTS_TO_PLAN.md#seqpointstos-pointer-and-sizes),
[`PointsToRaw`](TYPED_POINTS_TO_PLAN.md#pointstoraw) and [`wf_basic` and `wf`](TYPED_POINTS_TO_PLAN.md#wf_basic-and-wf).

10. **The new `SeqPointsTo` shape.**
    - *Done:* a generic inherent impl `impl<T, P: Typed<A = T>> Seq2<T, P>`
      next to `impl Seq2<u8, Byte>` (where `Byte` doesn't implement `Typed`),
      both defining `wf`, is accepted, with no E0592 (`seq_overlap.rs`).
      The struct needs `#[verifier::reject_recursive_types(T)]`
      once `T` appears in the bound `P: Phys<A = T>`;
      the real `SeqPointsTo` will need it too.
    - *Not run (routine):* the full struct with `ptr: Ghost<*mut [T]>`,
      `PointsToPhys::size(len) = len * P::size(())`, and the `thin_ptr` contracts.
11. **`PointsToRaw`'s representation.**
    - *Known:* `#[verifier::type_invariant]` works on tracked structs
      (`raw_ptr.rs` line 370, with `use_type_invariant` in proof fns).
    - *Not run (routine):* the recursive helper that removes a contiguous range's bytes,
      in address order, into a `Seq`.
12. **Generic `PointsToProperties` and `wf` for `PointsToUnaligned`.**
    - *Done:* trait default bodies for `spec` and `proof` fns are accepted on this branch
      (the trait needs `Sized`, which `PointsToPhys` has),
      and a concrete type that doesn't override sees the default.
      But a default spec body does **not** unfold in generic code,
      nor inside a default proof body (`default_methods.rs`),
      presumably because an impl may override it.
      So `PointsToSingleValue::wf` may be a default body (written once),
      but generic code gets its facts only from the trait lemmas
      (`bytes_decode`, `satisfies_alignment_of_wf`, `lemma_wf_basic`),
      which need per-impl proofs (empty, since `wf` unfolds at the concrete type).
    - *Not run (low risk, same pattern as item 9):*
      `impl<T: ?Sized> PointsToProperties for PointsToUnaligned<T> where PointsToUnaligned<T>: PointsToPhys<A = T>`
      next to per-type `PointsToPhys` impls with the `ptr_mut_from_data` pointer.
13. **Default proof bodies that call other trait methods.**
    *Known (no spike needed):* default proof bodies that only call other trait methods
    and use their contracts are fine. This covers the proof defaults in the trait
    (`borrow`, `into_untyped`, `from_untyped`, `zero_sized`, `take`, `put`, `copy`, `copy_typed_value`,
    `from_untyped_with_value`). It differs from what `default_methods.rs` tested,
    a default proof body that needed a default *spec* body to unfold (which fails).

### Phase 1: structural generalization (assessment section 1, groups 1 and 3)

Independent of the trait, and the generic typed impl needs these.

- Move `tracked_seq_pt`, `tracked_seq_pt_mut`, `index_mut`, `from_seq`, `empty`, `into_seq` into the
  generic `impl<T, P> SeqPointsTo<T, P>`, stated with `wf_basic()` and `P::size(())`
  (after phase 1b; `P::const_size()` if phase 1 lands first).
  Keep thin `wf()` wrappers on `SeqPointsTo<T, PointsTo<T>>` for now; phase 3 removes them.
- Keep the specialized `is_disjoint_seqpt` and `PointsToUntyped::is_disjoint_untyped`
  (no generic `is_disjoint_seq`).
- Rename `PointsToSingleton` to `PointsToByte` (and `PointsToSingletonData` to `PointsToByteData`),
  so it isn't confused with `PointsToSingleValue`.
  Purely mechanical; also update the docs that mention it
  (`PORTING_STATUS.md`, `POINTS_TO_MIGRATION.md`, `GENERALIZATION_ASSESSMENT.md`).
- Update call sites and verify.

### Phase 1b: `SeqPointsTo`'s slice pointer, `size(metadata)`, no `FixedSize`

The design is in [`SeqPointsTo`'s pointer and sizes](TYPED_POINTS_TO_PLAN.md#seqpointstos-pointer-and-sizes).
Run [phase 0 check 10](#phase-0-pending-checks) first.
Independent of the new traits; it changes existing ones.

1. `PointsToPhys::size(self)` becomes `size(metadata: Metadata<Self::A>)` in every existing impl:
   `PointsToSingleton`/`PointsToByte` (`1`), `PointsToUnaligned<T>` / `PointsTo<T>` (`size_of::<T>()`),
   `PointsToUnaligned<[T]>` / `PointsTo<[T]>` (`len * size_of::<T>()`),
   `SeqPointsTo` (`len * P::size(())`).
   Rewrite `x.size()` uses as `X::size(x.ptr()@.metadata)`,
   starting with `PointsToProperties`' own contracts.
2. `SeqPointsTo`: `ptr: Ghost<*mut [T]>`, bound `P: PointsToProperties<A = T>`
   (with `#[verifier::reject_recursive_types(T)]`),
   `wf_basic` gains `ptr()@.metadata == len()`;
   `PointsToUntyped = SeqPointsTo<u8, PointsToByte>`, and its `wf()` loses the clause that moved.
3. Remove `FixedSize`: `P::const_size()` → `P::size(())`; drop the `size_eq_const_size` calls.
4. Add `thin_ptr` to `SeqPointsTo<T, PointsTo<T>>`,
   and restate the typed impl's pointer contracts with it
   (list in [`SeqPointsTo`'s pointer and sizes](TYPED_POINTS_TO_PLAN.md#seqpointstos-pointer-and-sizes)):
   `from_seq`, `empty`, `zero_sized`/`zero_sized_helper`, `split`, `join`,
   `subrange`, `subrange_mut`, `from_untyped`, `from_untyped_with_typed_value`, `untyped_mut_join`,
   and the `View` / `SeqPointsToData` `ptr` field.
5. Update the plan's ghost step 6 contracts and `from_refs`
   (see [What this plan changes in the ghost metadata plan](#what-this-plan-changes-in-the-ghost-metadata-plan)).
6. rustlib uses these types; update its call sites in the same change (not visible from this repo).
7. Verify both builds.

### Phase 2: introduce the traits and the Sized impls

Assumes ghost metadata step 1 (the field) is already in, so moved bodies include `metadata` from the
start (see the combined order).

1. Add `TypedValue::value_ref` (`?Sized`). Restate the existing decode clauses with it where that
   simplifies things. `TypedValue<T>::value()` and `TypedValue<[T]>::value()` can stay as they are.
2. Add `PointsToSingleValue` and `PointsToSingleValueSized` (next to `PointsToProperties` in `points_to.rs`, or at
   the top of `points_to_permissions.rs`).
3. `PointsToUnaligned`'s pointer and `PointsToProperties` ([`wf_basic` and `wf`](TYPED_POINTS_TO_PLAN.md#wf_basic-and-wf)):
   build `ptr` from the stored metadata in both `PointsToPhys` impls (Sized and slice),
   and replace the two `PointsToProperties` impls with one generic impl
   whose `wf_basic` is only `pt_untyped().wf()` and the byte count.
   The decode, length and metadata clauses leave `wf_basic`:
   for Sized `T` into `PointsToSingleValue::wf` (next step);
   for slices into the existing inherent `PointsToUnaligned<[T]>::wf` until phase 2b.
   Restate Sized pointer contracts on `@.addr` / `@.provenance` where the cast-based proofs break.
   Rename `PointsToProperties::ptrs_len_same_valid` to `ptrs_len_same` (byte-level, no decoding)
   in every impl, including `SeqPointsTo`'s and `PointsToUntyped`'s
   (whose lemma becomes `lemma_ptrs_len_same_untyped`);
   the decoding version becomes `PointsToSingleValue::ptrs_len_same_valid` in the next step,
   and the typed `SeqPointsTo` gets an inherent `ptrs_len_same_valid` over its elements'.
4. `impl<T> PointsToSingleValue + PointsToSingleValueSized for PointsToUnaligned<T>`: real bodies. Most are today's
   `PointsTo<T>` bodies with `self.pt_unaligned.` removed.
   `wf` is the formula in [`wf_basic` and `wf`](TYPED_POINTS_TO_PLAN.md#wf_basic-and-wf), `metadata_matches` is `true`,
   `satisfies_alignment` is `true`, and `from_untyped` loses its alignment precondition.
5. `impl<T> PointsToSingleValue for PointsTo<T>` (Sized only for now):
   one-line delegations to `self.pt_unaligned`,
   except `satisfies_alignment(addr)` (`PointsToUnaligned::<T>::satisfies_alignment(addr) && addr as nat % spec_align_of_val::<T>(arbitrary()) == 0`)
   and `from_untyped` (`PointsToUnaligned::from_untyped(u, m).into_aligned()`).
   Write it in the shape of [the generic impl](TYPED_POINTS_TO_PLAN.md#the-generic-pointsto-impl),
   so phase 2b only has to widen `impl<T>` to `impl<T: ?Sized> ... where ...`.
   It can't be generic yet: a `?Sized` `PointsToSingleValue` impl needs `?Sized` supertrait impls,
   and those would drop `PointsTo<[T]>`'s existing ones until `PointsToUnaligned<[E]>` has the trait.
6. `impl<T> PointsToSingleValueSized for PointsTo<T>`: delegations, plus `lemma_satisfies_alignment_offset`,
   which is the `lemma_mul_mod_noop_right`/`lemma_add_mod_noop`/`layout_of_sized` argument
   currently inlined in `split`/`subrange`/`from_untyped_with_typed_value`.
7. Remove the inherent `PointsTo<T>` / `PointsToUnaligned<T>` versions of the moved functions,
   including the inherent `wf` and `stays_wf`:
   inherent fns win over trait fns at concrete types (phase 0, item 5),
   and the old inherent `wf` (= `wf_basic`) would shadow the trait's `wf` with a different meaning.
   Keep `is_aligned`, `value`, `is_disjoint_pointsto`
   (`into_unaligned`/`as_unaligned` move to the generic conversion impl).
8. Callers outside the module need the traits in scope for method syntax.
   Re-export `PointsToPhys`, `PointsToProperties`, `PointsToSingleValue` and `PointsToSingleValueSized`
   from `points_to_permissions.rs` (not the prelude),
   then grep for uses of the moved methods (`raw_ptr_new.rs`, `shared_reference.rs`, rustlib, ...)
   and make sure those files import `points_to_permissions::*` (or the traits).
9. If any trait method ends up on the dependency path of a broadcast group, its proofs use the
   specific groups `{group_raw_ptr_axioms, group_layout_axioms, group_seq_axioms}`, never
   `group_vstd_default`, to avoid cyclicity errors (as the existing trait impls already do).
10. Verify. At this point `SeqPointsTo<T, PointsTo<T>>` is unchanged and just calls trait methods on
   its elements.

### Phase 2b: slice impls (ghost steps 3 and 5)

1. `impl<E> PointsToSingleValue for PointsToUnaligned<[E]>`,
   reusing the bodies from the ghost step 3 code,
   which was reverted and saved in [step3_slice_wip.patch](step3_slice_wip.patch).
   Its `size(len)` (`len * size_of::<E>()`) is already there from phase 1b,
   `satisfies_alignment` is `true`, and `metadata_matches(v, len)` is `v@.len() == len`.
   The inherent `PointsToUnaligned<[T]>::wf` from phase 2, step 3, is replaced by the trait's `wf`.
2. Make the `PointsTo` impls generic ([The generic `PointsTo` impl](TYPED_POINTS_TO_PLAN.md#the-generic-pointsto-impl)):
   widen phase 2's `PointsToSingleValue for PointsTo<T>` to `T: ?Sized`,
   and replace the per-type `PointsToPhys`/`PointsToProperties`/`View` impls
   for `PointsTo<T>` and `PointsTo<[T]>` with one generic impl each.
   `PointsTo<[E]>` then has the trait with no slice-specific code.

`borrow` (ghost step 5's `borrow_value`, renamed) is a trait method, so it comes with this phase.
The inherent slice functions and the `_slice`-suffixed lemmas from step 3 are dropped,
and so is the `PointsTo::<T>::zero_sized` turbofish it needed.

### Phase 2c: `PointsToRaw`

The design is in [`PointsToRaw`](TYPED_POINTS_TO_PLAN.md#pointstoraw). Run [phase 0 check 11](#phase-0-pending-checks) first.

1. The struct, its type invariant, and the specs `provenance`, `dom`, `is_range`, `contains_range`.
2. `empty`, `split`, `join`, `ptr_bounds`, `provenance_non_null`, `is_disjoint`.
3. `from_untyped(PointsToUntyped) -> PointsToRaw` and `into_untyped(start, len) -> PointsToUntyped`.
   These only need phase 1b, so 1-3 can land earlier.
4. The generic `into_typed::<P: PointsToSingleValue>` / `from_typed::<P: PointsToSingleValue>`,
   and `SeqPointsTo` versions (needs phases 2 and 2b).
5. Port `Dealloc`, `allocate` and `deallocate` (trusted, unchanged).
6. Add the trusted items to `POINTS_TO_AXIOMS.md` and note the removed `PointsToRaw` axioms.

### Phase 3: generic typed `SeqPointsTo`

Move the `SeqPointsTo<T, PointsTo<T>>` impl to `impl<T, P: PointsToSingleValueSized<A = T>>
SeqPointsTo<T, P>`, in this order (each step depends on the previous ones):

1. **Specs:** `wf` (generic definition in the design), `bytes`/`bytes_inner`, `seq_typed_value`, `is_valid*`,
   `is_empty`, `is_fully_empty`, `seq_value`, `value_subrange`, `stays_wf`. Drop the phase 1 `wf()`
   wrappers.
2. **Byte lemmas:** `typed_value_equiv`, `bytes_len_helper`/`bytes_len`, `bytes_subrange`,
   `bytes_equiv`, `bytes_subrange_equiv`, `bytes_decode_helper`/`bytes_decode`, `bytes_inner_ext`.
   These need `P::bytes_decode` plus `P::size(())` for each element's byte length. Expect most
   of the trigger fixup work here, since `P::bytes()` is opaque in generic code.
3. **Structure with alignment:** `split`, `join`, `subrange`, `zero_sized`/`zero_sized_helper`,
   `ptrs_len_same_valid`/`lemma_ptrs_len_same_valid`,
   using `P::lemma_satisfies_alignment_offset` and `P::satisfies_alignment_of_wf`.
4. **Untyped conversions:** `into_untyped_with_typed_value`, `into_untyped`, `from_untyped`,
   `from_untyped_with_typed_value`, `untyped_ref_join`/`as_untyped`, `untyped_mut_join`/
   `as_untyped_mut`.
5. **Value operations:** the borrow/take/put/copy subrange functions and their helpers
   (renaming `borrow_value_subrange` to `borrow_subrange`).
6. **`subrange_mut`:** keep it as an axiom on `SeqPointsTo<T, PointsTo<T>>` for now. With the ghost
   metadata plan's M5 it becomes provable for any `P` (see below), so don't generalize the axiom.
7. Generalize `View` to `impl<T, P: PointsToSingleValueSized<A = T>> View for SeqPointsTo<T, P>`
   (`SeqPointsToData<T, P>`; `PointsToUntyped` keeps its own).
   Leave in `impl<T> SeqPointsTo<T, PointsTo<T>>` only `is_aligned`, `is_disjoint_seqpt`
   and `subrange_mut` (until proved).

The recursive helpers are fine here because they're inherent methods. Only trait default methods
can't recurse.

### Phase 4: `SeqPointsTo<T, PointsToUnaligned<T>>` conversions

With the generic impl in place, the unaligned sequence exists. Add the conversions between the two
sequence types (the "(Lower priority) add the unaligned conversions" TODO):

- `into_unaligned` / `into_aligned` (by value): convert each element and rebuild with `from_seq`.
- `as_unaligned` / `as_aligned` (by reference): the element type changes, so this isn't a
  `shr_ref_struct_wrap`. With the ghost metadata plan's `tracked_collect_perm_refs` and `from_refs`,
  it is provable: borrow each element, convert it (`as_unaligned` / `as_aligned`), collect, wrap.
  Without them it would need an axiom; leave it out until then.
- `&mut` versions: provable the same way from M4-M6 once those exist.

Also add the unaligned slice conversions,
`PointsToUnaligned<[E]>` ↔ `SeqPointsTo<E, PointsToUnaligned<E>>` (`&` and `&mut`),
in a `PointsToUnaligned<E>`-specific sequence impl.
They follow ghost step 6's aligned versions without the M4 wrap:
each element is assembled directly with `from_raw_parts_ref` (shared) or M3 (`&mut`).
Optionally, the aligned versions could then be proved from these
plus the aligned/unaligned conversions, instead of separately.

### Phase 5: docs

Update `PORTING_STATUS.md`, `GENERALIZATION_ASSESSMENT.md` (mark level 3 done), and
`POINTS_TO_AXIOMS.md` if any axiom's scope changed.

## Interaction with the ghost metadata plan

The two plans touch the same types, but neither depends on the other being finished. These are the
points where they meet.

### What the ghost metadata plan changes here

- **The new field (ghost step 1).** `PointsToUnaligned` construction and destructuring sites get
  `metadata: Ghost(())` / `metadata: _`. Phase 2 moves most of those sites from `PointsTo` into the
  `PointsToUnaligned` impl, so doing ghost step 1 first means they're edited once.
- **Trait shape.** The slice impls are why `PointsToSingleValue` doesn't require `A: Sized`, states
  sizes with `Self::size(self.ptr()@.metadata)`, decodes through `value_ref`, and keeps by-value methods and constructors
  in `PointsToSingleValueSized`.
- **`subrange_mut` becomes provable.** M5 (`SeqPointsTo::from_seq_mut`) plus the existing
  `tracked_seq_pt_mut` and `Seq::tracked_split_borrow_mut` give a proof of `subrange_mut` for any
  `P`: borrow the sequence, split off the middle, wrap it with M5 at the offset pointer. This replaces
  open decision 2 of the earlier version of this plan (whether to generalize the axiom). It is the
  same result the reverted `wrap_mut` gave, but from a type-specific axiom.
- **`join_ref`/`join_mut` become provable** (ghost plan, "Existing" trusted items), so the
  assessment's section 1, group 2 idea of generalizing those axioms is no longer needed.
- **`SeqPointsTo<T, PointsToUnaligned<T>>` borrowed conversions** (phase 4) become provable from
  `from_refs` and M4-M6 instead of needing new axioms.

### What this plan changes in the ghost metadata plan

- **Steps 3 and 5 implement `PointsToSingleValue`** for `PointsToUnaligned<[E]>`
  (phase 2b) instead of adding inherent functions;
  `PointsTo<[E]>` gets it from the generic `PointsTo` impl.
  Everything in step 3 is a trait method or part of the generic aligned/unaligned impl,
  so no slice-only contracts remain (unless phase 0, items 7 or 8, fail).
  Step 2's impls for `PointsToUnaligned<[E]>` stay as they are;
  its `PointsTo<[E]>` impls are folded into the generic `PointsTo` impls in phase 2b.
- **The `lemma_ptrs_len_same_valid` naming problem goes away.** The uncommitted step 3 code
  used `_slice`-suffixed lemma names, because the broadcast group names lemmas by type,
  and inherent functions with the same name on `PointsTo<T>` and `PointsTo<[T]>`
  also made path calls like `PointsTo::zero_sized(p)` ambiguous.
  As trait methods, each impl has its own `lemma_ptrs_len_same_valid` with no clash
  (subject to phase 0, item 6, for broadcasting).
- **Step 6's sequence-side functions** (`SeqPointsTo::<E, PointsTo<E>>::from_untyped_ref`,
  `from_untyped_with_value_ref`, `as_slice_pt(_mut)`, and the `SeqPointsTo` side of `as_seq_pt(_mut)`)
  go in the `PointsTo<E>`-specific impl, not the generic one: they produce or consume `PointsTo<[E]>`
  and use M4. The unaligned counterparts (`SeqPointsTo<E, PointsToUnaligned<E>>` ↔
  `PointsToUnaligned<[E]>`) are simpler (no M4 needed) and are added in phase 4.
- **`from_refs` and M5** are already in the generic `SeqPointsTo<T, P>` impl in the ghost plan, which
  matches phase 1.
  After phase 1b their bound is `P: PointsToProperties<A = T>` (not `+ FixedSize`),
  element offsets use `P::size(())`,
  and their pointer argument is a thin `*mut T`, with `out.thin_ptr() == ptr` and `out.len() == perms.len()`.
- **Step 6's conversions can state `out.ptr() == self.ptr()`** after phase 1b,
  since `PointsTo<[E]>` and `SeqPointsTo<E, _>` then both have a `*mut [E]`,
  instead of restating address, provenance and `len() == metadata`.

### Combined order

| # | Step | Status | Why here |
|---|---|---|---|
| 1 | Ghost step 1: add the `metadata` field | done | Small; lets phase 2 move bodies once. |
| 2 | Ghost steps 2 and 4: slice `PointsToPhys`/`PointsToProperties`/`View` impls, `abs_decode_slice` | done | Don't depend on the trait. |
| 3 | Phase 0: spike | done ([results](#phase-0-results)) | Settles the trait mechanics before either plan commits to them. |
| 4 | Phase 1: structural generic `SeqPointsTo` | next | Independent; small. |
| 4b | Phase 0 check 10, then phase 1b: `SeqPointsTo` slice pointer, `size(metadata)`, no `FixedSize` | | Before phase 2, which writes the new traits against `PointsToPhys::size(metadata)`. |
| 5 | Phase 2: traits + Sized impls | | Fixes the API the slice impls implement. |
| 6 | Phase 2b: slice impls (ghost steps 3 and 5) | step 3 bodies in `step3_slice_wip.patch` | Uses the trait from row 5. |
| 6b | Phase 0 check 11, then phase 2c: `PointsToRaw` | | Its generic typed conversions use rows 5-6; its untyped part only needs row 4b. |
| 7 | Phase 3: generic typed `SeqPointsTo` | | Before ghost step 6, so step 6's code lands in the final impl structure. |
| 8 | Ghost step 6: borrowed conversions and new axioms; then prove `subrange_mut`, `join_ref`, `join_mut` | | Needs rows 6-7. |
| 9 | Phase 4 and ghost step 7 | | Both build on row 8. |
| 10 | Phase 5 and ghost step 8: docs | | |
| 11 | rustlib: `str` impls and conversions | | See [`str` in rustlib](TYPED_POINTS_TO_PLAN.md#str-in-rustlib). Needs rows 6 and 8. |

Row 4 can move later without affecting the slice work.
Row 7 can also move after row 8,
at the cost of moving step 6's sequence-side functions again in phase 3
(they stay `PointsTo<E>`-specific, so that's mostly a relocation).

## Risks

- **Phase 0 failures.** `tracked &mut self` in trait methods, associated-type equality bounds, and
  expressing `Self::A: Sized` are the load-bearing assumptions.
  The generic `PointsTo` impl (item 9) is not load-bearing:
  its fallback is per-type delegating impls, at the cost of the duplication it avoids.
- **Proof fixups in phase 3.** Every fact about element bytes and values goes through opaque trait
  specs, so proofs that currently unfold `PointsTo` definitions will need trait lemma calls. This is
  likely the bulk of the effort.
- **Broadcast cyclicity.** Moving lemmas into traits can change which functions are on a broadcast
  group's dependency path. The latest commit (`cd02a6bae`) already had to fix cyclicity errors of
  this kind.
- **Verification time.** Generic proofs with trait-bounded quantifiers can be slower; watch for
  timeouts in the byte lemmas.
