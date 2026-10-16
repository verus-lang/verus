# Assessment: generalizing the `points_to_permissions.rs` API

This file answers the `PORTING_STATUS.md` TODO about making `SeqPointsTo<T, PointsTo<T>>` functions
generic, plus two related questions that came up while assessing it:

1. Which `SeqPointsTo<T, PointsTo<T>>` functions could move to the generic
   `impl<T: ?Sized, P> SeqPointsTo<T, P>` block?
2. Which `impl<T> PointsTo<T>` functions could move to `impl<T: ?Sized> PointsTo<T>`?
3. Which `PointsTo<T>` functions could be defined on `PointsToUnaligned<T>` instead?
4. How a trait for typed permissions (`TypedPointsTo` below) would reduce the duplication, and how
   it changes the answers to 1-3.

The assessment is based on the committed `points_to_permissions.rs` at `cd02a6bae`, read but not
verified. None of the generic versions sketched here have been checked by Verus yet.

## Background facts the assessments rely on

- `PointsTo::wf()` and `PointsToUnaligned::wf()` are both exactly `wf_basic()`. `PointsToUntyped::wf()`
  adds a metadata condition (`ptr()@.metadata == len()`), and `SeqPointsTo<T, PointsTo<T>>::wf()`
  adds alignment of the base pointer.
- `PointsTo<T>::const_size()` and `PointsToUnaligned<T>::const_size()` are both `size_of::<T>()`.
- `PointsTo<T>::ptrs_len_same_valid` already includes `new.ptr() == old.ptr()`.
- `PointsToPhys`, `FixedSize` and `PointsToProperties` are only implemented for sized `PointsTo<T>`
  and `PointsToUnaligned<T>`. For `?Sized` `T` there is no `ptr()`, `wf_basic()` or `wf()`.
- `size_of` and `align_of` are `V: Sized`. `spec_size_of_val` and `spec_align_of_val` are `?Sized`
  but take a `&V`, which an `Empty` permission doesn't have. `abs_decode` is `?Sized`.
  `TypedValue::value()` is only defined for sized `T` (plus a separate
  `TypedValue<[T]>::value() -> &[T]`).

## 1. `SeqPointsTo<T, PointsTo<T>>` → generic `SeqPointsTo<T, P>`

Generic code can only use `wf_basic()`, not the per-instantiation `wf()`. So each instantiation keeps
a thin wrapper wherever `wf()` matters. Because element `wf()` is `wf_basic()` for `PointsTo<T>` and
offsets use `const_size() == size_of::<T>()`, a generic function that ensures `wf_basic()` per
element gives the `PointsTo<T>` version what it needs.

### Group 1: can move, with thin `wf()` wrappers

These only touch `seq_pt`/`ptr`, and nothing in their proofs is specific to `PointsTo`.

| Function | Generic version | What the `PointsTo<T>` wrapper adds |
|---|---|---|
| `tracked_seq_pt`, `into_seq` | requires/ensures `wf_basic()` for each element | nothing, since element `wf()` is `wf_basic()` |
| `tracked_seq_pt_mut` | `ptrs_len_same_valid(old, final) ==> final.wf_basic()` | alignment carries over because `ptr` is unchanged |
| `index_mut` | `P::ptrs_len_same_valid(*ret, *final(ret)) && final(ret).ptr() == ret.ptr() ==> final.wf_basic()` | for `PointsTo`, the trait predicate already includes pointer equality |
| `from_seq` | offsets use `P::const_size()`, elements `wf_basic()` | the alignment precondition |
| `empty` | needs only non-null and in-bounds | the alignment precondition |

`PointsToUntyped` would get all of these for free. Today it has no `index_mut` or `from_seq`.

### Group 2: logic could be shared, but the pointers differ by type

`split`, `join`, `subrange` and `subrange_mut` share the same core: `tracked_skip`/`tracked_add`/
`tracked_borrow_subrange`, the per-element offset arithmetic, and the provenance-bounds argument.
What differs is the pointer of each half (`PointsTo<T>` keeps the metadata, `PointsToUntyped` sets it
to `mid` / `len - mid`) and the `bytes()` postconditions.

One option is a generic version that takes the result pointers as arguments, e.g.
`split_with_ptrs(self, mid, p1, p2)` (placeholder name). It would require their addr/provenance and
ensure `wf_basic()`, and each type would pick its pointers and prove its own `wf()` and `bytes()`.
This would remove the near-duplicates `PointsToUntyped::split`/`split_ref`/`join`.

The `join_ref`/`join_mut` axioms (currently only on `PointsToUntyped`) and the `subrange_mut` axiom
could also be stated for any `P`. That grows the axioms' scope, so it should get the same soundness
review as `wrap_mut` first.

### Group 3: small cleanup

`is_disjoint_seqpt<S>` and `PointsToUntyped::is_disjoint_untyped` both specialize the trait
`is_disjoint` by turning `size()` into `len * const_size`. One generic
`is_disjoint_seq<S: ?Sized, Q>` could replace both.

### Group 4: stays specific to `PointsTo<T>` (without a `TypedPointsTo` trait)

These use `bytes()`, `typed_value`/`value`, `abs_decode`, `size_of::<T>()`/alignment, or `PointsTo`
internals like `pt_unaligned.val`:

- **Specs:** `wf`, `bytes`/`bytes_inner`, `seq_typed_value`, `is_valid*`, `is_empty`,
  `is_fully_empty`, `seq_value`, `value_subrange`
- **Byte lemmas:** `typed_value_equiv`, `bytes_len*`, `bytes_subrange*`, `bytes_equiv`,
  `bytes_decode*`, `bytes_inner_ext`
- **Untyped conversions:** `into_untyped*`, `from_untyped*`, `as_untyped*`,
  `untyped_ref_join`/`untyped_mut_join`
- **Value operations:** all the borrow/take/put/copy subrange functions and their helpers
- **Others:** `is_aligned`, `stays_wf` (already generic through the trait's `stays_wf_basic`, so only
  the `wf()` wrapper is left)
- **Needs a trait change:** `lemma_ptrs_len_same_valid` (needs a trait-level lemma) and
  `zero_sized` (needs a trait method that builds a zero-sized element)

See [section 4](#how-the-trait-changes-the-earlier-assessments) for how a `TypedPointsTo` trait
changes this group.

### Recommendation

Do group 1 and the `is_disjoint` merge in group 3: both are cheap and low-risk. Group 2 is optional.
Leave the axioms alone until they've been reviewed for soundness.

## 2. `impl<T> PointsTo<T>` → `impl<T: ?Sized> PointsTo<T>`

Almost nothing can move yet, and the problem is in the trait impls underneath rather than the
function bodies. Most functions take `requires self.wf()` and mention `self.ptr()`, and for `?Sized`
`T` neither exists:

- **Trait impls are Sized-only.** `FixedSize` can't apply to an unsized `T` anyway (only
  `SeqPointsTo` elements need it), but `PointsToPhys`/`PointsToProperties` would need `?Sized` impls.
- **`ptr()` doesn't work for unsized types.** `PointsToUnaligned::ptr()` is
  `pt_untyped().ptr() as *mut T`, which for an unsized `T` would have to invent the metadata (e.g. a
  slice's length). The struct would need to store a `Ghost<*mut T>`, or each unsized type would need
  its own rule for deriving it.
- **The layout specs are Sized-only.** `wf_basic` uses `size_of::<T>()` and `align_of::<T>()`. The
  `_val` versions need a value, and there's no layout spec computed from pointer metadata.
- **`TypedValue::value()` is Sized-only.**

| Function | Verdict |
|---|---|
| `take`, `put`, `copy`, `from_untyped_with_value` | **Never.** They move `T` by value, and `copy` needs `Copy`, which implies `Sized`. |
| `zero_sized` | **Never in this form.** `size_of::<T>() == 0` only makes sense for sized types. An empty slice would need a different lemma. |
| `is_aligned`, `bytes_decode`, `stays_wf`, `lemma_ptrs_len_same_valid`, `is_disjoint_pointsto` | **Blocked** until unsized `T` has `wf`, `ptr` and `size` definitions. |
| `into_unaligned`, `as_unaligned`, `borrow_value` (`&T` is fine for unsized `T`) | **Blocked only by `wf`.** The bodies are plain field access, so they move as soon as an unsized `wf` exists. |
| `into_untyped_with_typed_value`, `into_untyped`, `as_untyped`, `from_untyped` | Bodies work for unsized `T`, but the contracts mention `wf()`, `ptr()` and `size_of`. A version without `wf` (like `tracked_pt_unaligned`) could move now, but would be too weak to be useful. |
| `as_untyped_mut` | Body works for unsized `T`, but the clause restoring `wf()` is the point of it. Blocked. |
| `borrow_typed_value`, `take_typed_value` | **Could move now**, each with a Sized wrapper that adds `wf()` back. |
| `put_typed_value`, `copy_typed_value` | `put_typed_value` would also need a `?Sized` value spec on `TypedValue` returning `&T` (generalizing the `[T]` one). `copy_typed_value` needs `Copy`, so it stays Sized. |

### Recommendation

Don't generalize yet. The few functions that could move now would only turn into generic/wrapper
pairs. The real prerequisite is deciding how `ptr()`, `size()`, alignment and `wf()` work for an
unsized `T`. That's the same design question as the open "Port `impl<T> PointsTo<[T]>`" TODO, and it
depends on whether slices end up as `PointsTo<[T]>` at all (`PORTING_STATUS.md` currently plans to
make them `SeqPointsTo`). Fold this into that TODO. Once unsized `T` has a `wf` (most likely one impl
per unsized type, like `TypedValue<[T]>::value`), the group blocked only by `wf` moves almost for
free.

## 3. `PointsTo<T>` → `PointsToUnaligned<T>`

`PointsTo<T>` is a wrapper around one `pt_unaligned` field, and its `wf()` is the unaligned `wf()`
plus alignment. So every function whose contract doesn't mention alignment could be defined on
`PointsToUnaligned<T>`, with a one-line wrapper on `PointsTo<T>` that keeps alignment (the pointer
doesn't change).

Today `PointsToUnaligned<T>` only has `value`, `wf`, `stays_wf`, `into_aligned`/`as_aligned`,
`zero_sized` and `is_disjoint_unaligned`. You can't take or put a value or convert to/from untyped
without first going through an aligned `PointsTo`, and there's no `as_unaligned_mut` to work around
that for `&mut`.

### Could move (the `PointsTo` version becomes a delegating wrapper)

| `PointsTo<T>` function | Unaligned version | `PointsTo` wrapper |
|---|---|---|
| `borrow_value`, `borrow_typed_value` | unchanged, requires unaligned `wf()` | `self.pt_unaligned.borrow_value()` |
| `take`, `put`, `copy`, `take_typed_value`, `put_typed_value`, `copy_typed_value` | unchanged (they only touch `val` and the unaligned `wf`) | `self.pt_unaligned.take()` etc.; same `ptr()` means alignment still holds |
| `into_untyped_with_typed_value`, `into_untyped`, `as_untyped` | unchanged | destructure or delegate |
| `as_untyped_mut` | ensures `PointsToUntyped::ptrs_len_same_valid(..) ==> final(self).wf()` (unaligned) | delegate; the untyped `ptrs_len_same_valid` keeps the same pointer, so alignment carries over |
| `from_untyped`, `from_untyped_with_value` | **no alignment precondition** | `PointsToUnaligned::from_untyped(u).into_aligned()` |
| `bytes_decode` | unchanged; follows from the unaligned `wf_basic` | trivial |
| `lemma_ptrs_len_same_valid` | same body (it already reasons through `pt_unaligned().pt_untyped()`), or call `PointsToUntyped::lemma_ptrs_len_same_valid_untyped` | call the unaligned lemma |
| `is_disjoint_pointsto` | already exists as `is_disjoint_unaligned` | could delegate |

### Stays on `PointsTo<T>`

- `is_aligned`: the alignment fact itself.
- `into_unaligned`, `as_unaligned`: the bridges between the two types.
- `wf`, `stays_wf`, `zero_sized`: already exist on both types (`zero_sized` already delegates).

### Trade-off

**Benefits:** `PointsToUnaligned<T>` gets a real API, which `read_unaligned`/`write_unaligned`-style
use cases need, and which the "(Lower priority) add the unaligned conversions" TODO and a future
`SeqPointsTo<T, PointsToUnaligned<T>>` need too. `from_untyped` on unaligned memory becomes possible
without an alignment proof.

**Cost:** about 15 contracts written twice. The `PointsTo` bodies shrink to delegations, but the
specs don't get shorter. Section 4 addresses this.

## 4. A `TypedPointsTo` trait for typed permissions

A trait shared by `PointsTo<T>` and `PointsToUnaligned<T>` removes duplication at three levels.

### Level 1: each contract is written once

In Verus, the `requires`/`ensures` on a trait method apply to every impl. If `take`, `put`, etc. are
trait methods, their specs live in the trait and each impl only writes a (one-line) body. This works
neatly here because `wf()` is `wf_basic()` for both types, so trait contracts can say `wf_basic()`
with nothing lost. (That isn't true of `PointsToUntyped`, which is why section 1 needed wrappers.)

```rust
pub trait TypedPointsTo: PointsToProperties {   // Self::A is the T
    spec fn typed_value(self) -> TypedValue<Self::A>;
    spec fn bytes(self) -> Seq<AbstractByte>;

    proof fn take(tracked &mut self) -> (tracked val: Self::A)
        requires old(self).wf_basic(), old(self).typed_value().is_valid(),
        ensures val == old(self).typed_value().value(),
                final(self).ptr() == old(self).ptr(),
                final(self).bytes() == old(self).bytes(),
                final(self).typed_value().is_empty(),
                final(self).wf_basic();
    // put, copy, borrow_value, *_typed_value, bytes_decode, ... likewise
}

impl<T> TypedPointsTo for PointsToUnaligned<T> {
    proof fn take(tracked &mut self) -> (tracked val: T) { /* swap on self.val */ }
}
impl<T> TypedPointsTo for PointsTo<T> {
    proof fn take(tracked &mut self) -> (tracked val: T) { self.pt_unaligned.take() }
}
```

### Level 2 (optional): each body is written once

Give the trait one or two primitives and write the rest as default methods in terms of them. For
example, a guarded `&mut TypedValue` borrow:

```rust
proof fn typed_value_mut(tracked &mut self) -> (tracked v: &mut TypedValue<Self::A>)
    requires old(self).wf_basic(),
    ensures *v == old(self).typed_value(),
            final(self).typed_value() == *final(v),
            final(self).bytes() == old(self).bytes(),
            final(self).ptr() == old(self).ptr(),
            (final(v).is_valid() ==> abs_decode(final(self).bytes(), &final(v).value()))
                ==> final(self).wf_basic();
```

Then `take`, `put`, `copy` and `*_typed_value` each become a default `tracked_swap`/assignment written
once, and each impl only writes `typed_value_mut`.

The untyped conversions work the same way with a primitive pair: `into_parts` returning
`(PointsToUntyped, TypedValue)` and `from_parts` taking them back. `PointsTo::from_parts` needs
alignment and the unaligned version doesn't; the trait handles that with a hook such as
`spec fn ptr_ok(p: *mut Self::A) -> bool`, meaning "aligned" for `PointsTo` and `true` for
`PointsToUnaligned`, which `from_parts` requires.

### Level 3: generic `SeqPointsTo` over typed elements

The bigger payoff. With a trait bound, the value and untyped operations in the
`SeqPointsTo<T, PointsTo<T>>` impl could be written once as
`impl<T, P: TypedPointsTo<A = T> + FixedSize> SeqPointsTo<T, P>`, giving
`SeqPointsTo<T, PointsToUnaligned<T>>` almost for free. Without the trait, that impl is about 1000
more lines to duplicate.

### Costs and risks

- **Opaque specs in generic code.** Inside a generic impl, `P::bytes()` and `P::typed_value()` can't
  be unfolded, so any fact the proofs need must be a trait lemma (for example
  `bytes().len() == const_size()`). Expect trigger and fixup work, like the `ptrs_len_same` move into
  `PointsToProperties`.
- **Default `proof fn` bodies.** Supported on this branch: see `test_default1`-`test_default20` in
  `rust_verify_test/tests/traits.rs`. Default proof bodies are verified and inherited (`test_default7`),
  can call a required method of the same trait and use its `ensures` (`test_default8`, the level 2
  pattern), and can take `tracked` parameters (`test_default9`). Limits:
  - Default methods can't be recursive or use `decreases` (`test_default5`). The level 2 defaults
    (`take`/`put`/`copy` as a swap or assignment) are fine, but anything inductive (the subrange
    operations, `bytes_len_helper`) has to live in a generic inherent impl (level 3), not as a
    default.
  - A default can't call a free function that needs `Self: TypedPointsTo` if that leads back
    through the trait (`test_default12`, `test_default14`); calling `Self::method()` directly is
    fine.
  - No test covers `tracked &mut self` in a default body, which is the shape `take`/`put` need.
    Expected to work, but verify one small default first.
- **Alignment never appears in trait contracts.** It has to go through the `ptr_ok` hook or through
  `PointsTo`-only functions like `is_aligned`.

### How the trait changes the earlier assessments

**Section 3 (`PointsTo` → `PointsToUnaligned`).** The trait is what makes this worth doing. Its
main cost was writing about 15 contracts twice. With level 1, each contract is written once in the
trait. Most of the table in section 3 becomes trait methods implemented by both types. Only
`is_aligned`, `into_unaligned`/`as_unaligned` and the `wf`/`stays_wf` wrappers stay inherent.
`from_untyped`/`from_untyped_with_value` become trait methods via the `ptr_ok` hook.

**Section 1 (`SeqPointsTo` generalization).** Groups 1-3 are unchanged: they only need
`PointsToProperties`. Most of group 4 moves into a second generic impl bounded by
`P: TypedPointsTo + FixedSize`:

| Group 4 item | With `TypedPointsTo` |
|---|---|
| `bytes`/`bytes_inner`, `seq_typed_value`, `is_valid*`, `is_empty`, `is_fully_empty`, `seq_value`, `value_subrange` | generic, using `P::bytes()`/`P::typed_value()` |
| `typed_value_equiv`, `bytes_len*`, `bytes_subrange*`, `bytes_equiv`, `bytes_decode*`, `bytes_inner_ext` | generic, given a trait lemma `bytes().len() == const_size()` and a trait-level `bytes_decode` |
| borrow/take/put/copy subrange functions and helpers | generic, built from the per-element trait methods through `index_mut` |
| `into_untyped*`, `as_untyped*`, `untyped_ref_join`/`untyped_mut_join` | generic, from the per-element `into_parts`/`as_untyped`/`as_untyped_mut` |
| `from_untyped*` | generic, with the base pointer required to satisfy `P::ptr_ok` |
| `wf`, `is_aligned`, the alignment arithmetic in `split`/`join`/`subrange` | stay per instantiation (alignment) |
| `lemma_ptrs_len_same_valid` | generic if the trait gets a `lemma_ptrs_len_same_valid` |
| `zero_sized` | generic if the trait gets a `zero_sized` constructor |

`SeqPointsTo<T, P>::wf()` still can't be defined once in a generic impl (it means alignment for
`PointsTo<T>` and nothing extra for `PointsToUnaligned<T>`). A generic `wf` could be expressed as
`wf_basic() && P::ptr_ok(ptr)`, so the `ptr_ok` hook might serve both purposes. That is worth trying
before committing to per-instantiation `wf`s.

**Section 2 (`?Sized`).** The trait doesn't remove the blockers: unsized `T` still needs `ptr()`,
`size()`, alignment and `wf()` definitions first. Two points for when that happens:

- `PointsToPhys` requires `Self: Sized`, but `type A` can already be unsized (`PointsToUntyped` has
  `A = [u8]`), so `TypedPointsTo` itself can be stated for unsized `A`.
- The by-value methods (`take`, `put`, `copy`, `from_parts` with a value) would need
  `where Self::A: Sized` and the by-reference ones a `?Sized` way to get `&A` out of a `TypedValue`.
  Splitting the trait along that line, or adding those bounds per method, would let an unsized
  `PointsTo<[E]>` implement the by-reference half.

### Recommendation

1. Do section 1 groups 1 and 3 now (cheap, independent of the trait).
2. If unaligned support is on the near-term path, introduce `TypedPointsTo` at level 1 for the value
   operations on `PointsTo<T>`/`PointsToUnaligned<T>`, then add the untyped conversions with the
   `ptr_ok` hook. This replaces doing section 3 with duplicated contracts.
3. Do the level 3 generic `SeqPointsTo` impl only once a `SeqPointsTo<T, PointsToUnaligned<T>>` is
   actually needed.
4. Leave section 2 under the `PointsTo<[T]>` TODO.
