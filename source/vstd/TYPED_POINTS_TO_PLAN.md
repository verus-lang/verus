# Plan: `TypedPointsTo` trait and a generic typed `SeqPointsTo` (level 3)

This is the implementation plan for "level 3" from
[GENERALIZATION_ASSESSMENT.md](GENERALIZATION_ASSESSMENT.md#4-a-typedpointsto-trait-for-typed-permissions):
a `TypedPointsTo` trait implemented by `PointsTo<T>` and `PointsToUnaligned<T>`, and one generic
`impl<T, P: TypedPointsToElem<A = T>> SeqPointsTo<T, P>` replacing most of today's
`impl<T> SeqPointsTo<T, PointsTo<T>>`. As a result, `SeqPointsTo<T, PointsToUnaligned<T>>` gets the
full typed API without duplicating the ~1000-line impl.

It is designed to fit together with [GHOST_METADATA_PLAN.md](GHOST_METADATA_PLAN.md), which adds
`metadata: Ghost<Metadata<T>>` to `PointsToUnaligned<T>` and gives `PointsTo<[E]>` /
`PointsToUnaligned<[E]>` their own trait impls. The trait is split so that those slice impls can
implement it too. See [Interaction with the ghost metadata plan](#interaction-with-the-ghost-metadata-plan)
for what changes in each plan and a combined order.

Level 3 builds on level 1 (each contract written once in the trait). Level 2 (default method bodies)
is not needed and is left out for now; see [Deferred](#deferred).

Each phase ends with both builds green (`source/tools/build-expand-errors.sh` and
`source/tools/build-verify-core.sh`) and is meant to be a separate commit, so the work can stop after
any phase with the tree in a good state.

## Target design

### Two traits

`TypedPointsTo` covers every typed permission, including slices. `TypedPointsToElem` adds what only
fixed-size, `Sized` permissions can provide, and is what `SeqPointsTo` elements need.

```rust
/// Any typed permission: PointsTo<T>, PointsToUnaligned<T>, and (with the ghost metadata plan)
/// PointsTo<[E]>, PointsToUnaligned<[E]>. Self::A may be unsized.
pub trait TypedPointsTo: PointsToProperties {
    // --- specs ---
    spec fn typed_value(self) -> TypedValue<Self::A>;
    spec fn bytes(self) -> Seq<AbstractByte>;
    /// Address condition the type adds on top of `wf_basic`: alignment for `PointsTo`
    /// (to `align_of::<T>()`, or `align_of::<E>()` for slices), `true` for `PointsToUnaligned`.
    spec fn addr_ok(addr: usize) -> bool;

    // --- lemmas ---
    proof fn bytes_decode(&self)    // wf_basic ==> bytes().len() == size()
                                    //   && (valid ==> abs_decode(bytes(), typed_value().value_ref()))
    proof fn addr_ok_of_wf(&self)   // wf_basic ==> addr_ok(ptr()@.addr)
    proof fn lemma_ptrs_len_same_valid(old: Self, new: Self)  // both wf_basic, same ptr ==> ptrs_len_same_valid

    // --- typed value operations (TypedValue<A> is Sized even when A isn't) ---
    borrow_typed_value, take_typed_value, put_typed_value,
    borrow_value (returns &A, so fine for unsized A)

    // --- untyped conversions that don't construct Self ---
    into_untyped_with_typed_value, into_untyped, as_untyped, as_untyped_mut
}

/// Fixed-size, Sized typed permissions: PointsTo<T> and PointsToUnaligned<T>. SeqPointsTo elements.
pub trait TypedPointsToElem: TypedPointsTo + FixedSize {
    // Self::A: Sized in every impl; how that is expressed is a phase 0 question.
    proof fn lemma_addr_ok_offset(addr: usize, i: nat)  // addr_ok(addr) ==> addr_ok(addr + i * const_size())
    take, put, copy (A: Copy), copy_typed_value (A: Copy)
    from_untyped (requires len == const_size(), addr_ok), from_untyped_with_value,
    zero_sized (requires const_size() == 0, addr_ok)
}
```

Why the split falls here:

- **By value vs by reference.** `take`, `put`, `copy` and `from_untyped_with_value` move an `A`, which
  needs `A: Sized`. Everything on `TypedValue<A>` and `&A` works for unsized `A`.
- **Size.** Contracts in `TypedPointsTo` use the per-permission `self.size()`, not
  `Self::const_size()`, since a slice's size depends on its metadata. Only `TypedPointsToElem` uses
  `const_size()`.
- **Constructors.** `from_untyped` and `zero_sized` need to know the size before a permission exists:
  `const_size()` for `Sized` types, a length argument for slices. The slice versions stay inherent
  (as in the ghost metadata plan, step 3).

Contract conventions:

- Contracts say `wf_basic()`, never `wf()`. This loses nothing for `PointsTo`/`PointsToUnaligned`
  (sized or slice), since `wf()` is `wf_basic()` for all of them.
- Decoding is stated with a new `?Sized` spec `TypedValue::value_ref(&self) -> &T` (`&*self->0`),
  so `abs_decode(bytes, tv.value_ref())` reads the same for `T` and `[E]`. This generalizes the
  existing `TypedValue<[T]>::value() -> &[T]`.
- Pointer facts between a permission and its `PointsToUntyped` are stated on `@.addr` and
  `@.provenance`, not with an `as *mut T` cast, so they read the same for every impl.
- Otherwise the contracts are today's `PointsTo<T>` contracts, with `size_of::<T>()` replaced by
  `self.size()` / `Self::const_size()` and alignment replaced by `Self::addr_ok`.

### The generic `SeqPointsTo`

- `wf()` becomes generic: `self.wf_basic() && P::addr_ok(self.ptr()@.addr)`. For `PointsTo<T>` this
  unfolds to today's definition. `PointsToUntyped::wf()` is unaffected: `PointsToSingleton` doesn't
  implement `TypedPointsToElem`, and `[u8]` isn't `Sized`, so the impls don't overlap.
- Everything in today's `impl<T> SeqPointsTo<T, PointsTo<T>>` moves into the generic impl, with
  `size_of::<T>()` → `P::const_size()`, alignment arithmetic → `P::lemma_addr_ok_offset`, and direct
  field access (`elt.pt_unaligned.val`) → trait calls (`elt.take_typed_value()`).
- What stays specific to `PointsTo<T>`: `is_aligned` (unfolds `addr_ok`), possibly `View` (see
  [Open decisions](#open-decisions)), and the slice conversions from the ghost metadata plan's step 6
  (see below).

## Phases

### Phase 0: spike the risky Verus features

In a scratch file, not `points_to_permissions.rs`, check the things this plan relies on but hasn't
verified:

1. A trait `proof fn` taking `tracked &mut self`, implemented on one type with a real body and on a
   wrapper type by delegating to a field (`self.pt_unaligned.take()`), with `final(self)` contracts.
   No existing test covers `tracked &mut self` in traits.
2. A generic impl bounded by an associated-type equality, `P: TypedPointsToElem<A = T>` (where `A`
   comes from `PointsToPhys`), and that `P::A` and `T` are interchangeable in specs.
3. How to say `Self::A: Sized` for `TypedPointsToElem`'s by-value methods: a trait-level
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

If (1) or (2) fails, stop and revisit the design before continuing.

### Phase 1: structural generalization (assessment section 1, groups 1 and 3)

Independent of the trait, and the generic typed impl needs these.

- Move `tracked_seq_pt`, `tracked_seq_pt_mut`, `index_mut`, `from_seq`, `empty`, `into_seq` into the
  generic `impl<T: ?Sized, P> SeqPointsTo<T, P>`, stated with `wf_basic()` and `P::const_size()`.
  Keep thin `wf()` wrappers on `SeqPointsTo<T, PointsTo<T>>` for now; phase 3 removes them.
- Replace `is_disjoint_seqpt` and `PointsToUntyped::is_disjoint_untyped` with one generic
  `is_disjoint_seq<S: ?Sized, Q>`.
- Update call sites and verify.

### Phase 2: introduce the traits and the Sized impls

Assumes ghost metadata step 1 (the field) is already in, so moved bodies include `metadata` from the
start (see the combined order).

1. Add `TypedValue::value_ref` (`?Sized`). Restate the existing decode clauses with it where that
   simplifies things. `TypedValue<T>::value()` and `TypedValue<[T]>::value()` can stay as they are.
2. Add `TypedPointsTo` and `TypedPointsToElem` (next to `PointsToProperties` in `points_to.rs`, or at
   the top of `points_to_permissions.rs`).
3. `impl<T> TypedPointsTo + TypedPointsToElem for PointsToUnaligned<T>`: real bodies. Most are today's
   `PointsTo<T>` bodies with `self.pt_unaligned.` removed. `addr_ok` is `true`, and `from_untyped`
   loses its alignment precondition.
4. `impl<T> TypedPointsTo + TypedPointsToElem for PointsTo<T>`: one-line delegations to
   `self.pt_unaligned`. `addr_ok(addr)` is `addr as nat % align_of::<T>() == 0`. `from_untyped` is
   `PointsToUnaligned::from_untyped(u).into_aligned()`. `lemma_addr_ok_offset` is the
   `lemma_mul_mod_noop_right`/`lemma_add_mod_noop`/`layout_of_sized` argument currently inlined in
   `split`/`subrange`/`from_untyped_with_typed_value`.
5. Remove the inherent `PointsTo<T>` versions of the moved functions. Keep `wf`, `stays_wf`,
   `is_aligned`, `into_unaligned`, `as_unaligned`, `value`, `is_disjoint_pointsto`.
6. Callers outside the module need the traits in scope for method syntax. Grep for uses of the moved
   methods (`raw_ptr_new.rs`, `shared_reference.rs`, ...), and either import the traits there or
   export them through the prelude.
7. If any trait method ends up on the dependency path of a broadcast group, its proofs use the
   specific groups `{group_raw_ptr_axioms, group_layout_axioms, group_seq_axioms}`, never
   `group_vstd_default`, to avoid cyclicity errors (as the existing trait impls already do).
8. Verify. At this point `SeqPointsTo<T, PointsTo<T>>` is unchanged and just calls trait methods on
   its elements.

### Phase 3: generic typed `SeqPointsTo`

Move the `SeqPointsTo<T, PointsTo<T>>` impl to `impl<T, P: TypedPointsToElem<A = T>>
SeqPointsTo<T, P>`, in this order (each step depends on the previous ones):

1. **Specs:** `wf` (generic definition above), `bytes`/`bytes_inner`, `seq_typed_value`, `is_valid*`,
   `is_empty`, `is_fully_empty`, `seq_value`, `value_subrange`, `stays_wf`. Drop the phase 1 `wf()`
   wrappers.
2. **Byte lemmas:** `typed_value_equiv`, `bytes_len_helper`/`bytes_len`, `bytes_subrange`,
   `bytes_equiv`, `bytes_subrange_equiv`, `bytes_decode_helper`/`bytes_decode`, `bytes_inner_ext`.
   These need `P::bytes_decode` plus `size_eq_const_size` for each element's byte length. Expect most
   of the trigger fixup work here, since `P::bytes()` is opaque in generic code.
3. **Structure with alignment:** `split`, `join`, `subrange`, `zero_sized`/`zero_sized_helper`,
   `lemma_ptrs_len_same_valid`, using `P::lemma_addr_ok_offset` and `P::addr_ok_of_wf`.
4. **Untyped conversions:** `into_untyped_with_typed_value`, `into_untyped`, `from_untyped`,
   `from_untyped_with_typed_value`, `untyped_ref_join`/`as_untyped`, `untyped_mut_join`/
   `as_untyped_mut`.
5. **Value operations:** the borrow/take/put/copy subrange functions and their helpers.
6. **`subrange_mut`:** keep it as an axiom on `SeqPointsTo<T, PointsTo<T>>` for now. With the ghost
   metadata plan's M5 it becomes provable for any `P` (see below), so don't generalize the axiom.
7. Leave in `impl<T> SeqPointsTo<T, PointsTo<T>>` only `is_aligned`, `subrange_mut` (until proved),
   and `View` if it isn't generalized.

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
- **Trait shape.** The slice impls are why `TypedPointsTo` has no `FixedSize` supertrait, states
  sizes with `self.size()`, decodes through `value_ref`, and keeps by-value methods and constructors
  in `TypedPointsToElem`.
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

- **Steps 2, 3 and 5 implement `TypedPointsTo`** for `PointsToUnaligned<[E]>` and `PointsTo<[E]>`
  instead of adding inherent functions: `into_untyped*`, `as_untyped`, `as_untyped_mut`,
  `borrow_value`, the `*_typed_value` operations, `bytes_decode` and `lemma_ptrs_len_same_valid` are
  trait methods there. Slice-only functions stay inherent: `from_untyped(pt_untyped, len)`,
  `zero_sized`, `into_aligned`/`as_aligned`/`into_unaligned`/`as_unaligned`.
- **The `lemma_ptrs_len_same_valid` naming problem goes away.** Ghost step 3 notes that the slice
  lemmas may need suffixed names because inherent functions can't share a name across impls of the
  same type. As trait methods, each impl has its own `lemma_ptrs_len_same_valid` with no clash
  (subject to phase 0, item 6, for broadcasting).
- **Step 6's sequence-side functions** (`SeqPointsTo::<E, PointsTo<E>>::from_untyped_ref`,
  `from_untyped_with_value_ref`, `as_slice_pt(_mut)`, and the `SeqPointsTo` side of `as_seq_pt(_mut)`)
  go in the `PointsTo<E>`-specific impl, not the generic one: they produce or consume `PointsTo<[E]>`
  and use M4. Unaligned counterparts (`SeqPointsTo<E, PointsToUnaligned<E>>` ↔
  `PointsToUnaligned<[E]>`) would be simpler (no M4 needed) and can be added later if needed.
- **`from_refs` and M5** are already in the generic `SeqPointsTo<T, P>` impl in the ghost plan, which
  matches phase 1.

### Combined order

| # | Step | Why here |
|---|---|---|
| 1 | Ghost step 1: add the `metadata` field | Small; lets phase 2 move bodies once. |
| 2 | Phase 0: spike | Settles the trait mechanics before either plan commits to them. |
| 3 | Phase 1: structural generic `SeqPointsTo` | Independent; small. |
| 4 | Phase 2: traits + Sized impls | Fixes the API the slice impls implement. |
| 5 | Ghost steps 2-5: slice impls (implementing `TypedPointsTo`), `abs_decode_slice`, `borrow_value` | Uses the trait from row 4. |
| 6 | Phase 3: generic typed `SeqPointsTo` | Before ghost step 6, so step 6's code lands in the final impl structure. |
| 7 | Ghost step 6: borrowed conversions and new axioms; then prove `subrange_mut`, `join_ref`, `join_mut` | Needs rows 5-6. |
| 8 | Phase 4 and ghost step 7 | Both build on row 7. |
| 9 | Phase 5 and ghost step 8: docs | |

Rows 3 and 6 can move later without affecting the slice work. If the ghost plan is more urgent, rows
5 and 7 can come before row 6, at the cost of moving step 6's sequence-side functions again in phase
3 (they stay `PointsTo<E>`-specific, so that's mostly a relocation).

## Open decisions

1. **`View` for `SeqPointsTo`.** `SeqPointsToData<T>` holds a `Seq<PointsTo<T>>`. Either generalize
   it to `SeqPointsToData<T, P>` (one generic `View`) or keep `View` only for the `PointsTo<T>`
   instantiation. The ghost plan has the matching question for `PointsToData<T>` (make it `?Sized` or
   skip `View` for slices); decide both together.
2. **Inherent wrappers on `PointsTo<T>`.** Removing the inherent methods (phase 2, step 5) means
   callers need the traits in scope. Keeping inherent one-line wrappers avoids that but brings back
   the duplication. Recommendation: remove them and export the traits.
3. **`addr_ok` vs `ptr_ok`.** The plan uses an address-only hook because alignment only depends on
   the address (for slices too: `align_of::<E>()`), and it keeps `lemma_addr_ok_offset` simple.
4. **Trait names.** `TypedPointsTo` / `TypedPointsToElem` are placeholders.

## Deferred

- **Level 2 (default bodies).** With level 1, the `PointsTo<T>` bodies are already one-line
  delegations, so default methods would only save the `PointsToUnaligned` bodies. Revisit if more
  impls appear (the slice impls are a candidate).
- **Other unsized types.** `str` follows the ghost plan's pattern later (metadata is the byte length)
  and would implement `TypedPointsTo` the same way. `dyn` and custom DSTs are out of scope.
- **Generalizing `split`/`join`/`subrange` across `PointsToUntyped`** (assessment section 1, group 2).
  Orthogonal and still optional.

## Risks

- **Phase 0 failures.** `tracked &mut self` in trait methods, associated-type equality bounds, and
  expressing `Self::A: Sized` are the load-bearing assumptions.
- **Proof fixups in phase 3.** Every fact about element bytes and values goes through opaque trait
  specs, so proofs that currently unfold `PointsTo` definitions will need trait lemma calls. This is
  likely the bulk of the effort.
- **Broadcast cyclicity.** Moving lemmas into traits can change which functions are on a broadcast
  group's dependency path. The latest commit (`cd02a6bae`) already had to fix cyclicity errors of
  this kind.
- **Verification time.** Generic proofs with trait-bounded quantifiers can be slower; watch for
  timeouts in the byte lemmas.
