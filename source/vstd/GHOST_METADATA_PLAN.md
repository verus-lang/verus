# Plan: ghost metadata on `PointsToUnaligned`

Based on commit `cd02a6bae` on `verify-rustlib-refactor`. Uncommitted work (the `str` impls) is not
taken into account. Line numbers refer to `points_to_permissions.rs` at that commit.

**In short:** add `metadata: Ghost<Metadata<T>>` to `PointsToUnaligned<T>`. Sized code only has to
fill in the field (which is `()`) at two construction sites; its `ptr()`, `size()` and proofs stay
as they are.
Slices then get their own `PointsToPhys`/`PointsToProperties` impls, with a pointer built from the
stored metadata. Empty slice permissions can be proved from `PointsToUntyped`. A *valid* slice needs
two new axioms: one for how a slice decodes, and one to build a tracked `[T]` from per-element
permissions.

## The problem

`PointsToUnaligned<T>::ptr()` is `self.pt_untyped().ptr() as *mut T` (line 735), and `size()` is
`size_of::<T>()`. Both only exist for `Sized` `T`: the `PointsToPhys`, `FixedSize` and
`PointsToProperties` impls are all `impl<T>`. For a slice permission `PointsToUnaligned<[T]>`,
nothing in the struct can produce the `*mut [T]`:

- The untyped pointer is a `*mut [u8]` whose metadata is a *byte* count. A `*mut [T]` needs an
  *element* count.
- The byte count doesn't determine the element count when `size_of::<T>() == 0`: every length has
  zero bytes.
- An `Empty` permission has no value to read a length from.

This is the blocker [GENERALIZATION_ASSESSMENT.md](GENERALIZATION_ASSESSMENT.md) §2 calls "`ptr()`
doesn't work for unsized types". It is also why `PointsTo<[T]>`, `PointsToUnaligned<[T]>`,
`tracked_borrow` (`&[T]`) and the commented-out `ptr_ref_slice` / `ptr_mut_ref_slice`
(`raw_ptr_new.rs:524`, `:559`) are on hold.

## Design decisions

All four decisions are confirmed.

### 1. Store only the metadata, not the whole pointer

```rust
pub tracked struct PointsToUnaligned<T: ?Sized> {
    val: TypedValue<T>,
    pt_untyped: PointsToUntyped,
    metadata: Ghost<Metadata<T>>,   // () for Sized T; the element count for [T]
}
```

The address and provenance already live in `pt_untyped`. Storing only the metadata keeps them in
one place, so `wf()` needs no "stored pointer agrees with the untyped pointer" clause. The
alternative is a full `ptr: Ghost<*mut T>`, as `SeqPointsTo` does. It would make `ptr()` a plain
field read, but every `wf` would need that agreement clause, and every constructor and mutator would
need to prove it.

`Metadata<T>` is `<T as Pointee>::Metadata` in ghost builds and `FakeMetadata<T>` otherwise
(`raw_ptr_new.rs:166-175`). Both are fine inside a `Ghost`.

### 2. Leave the Sized impls alone

(Revisited in [TYPED_POINTS_TO_PLAN.md](TYPED_POINTS_TO_PLAN.md#wf_basic-and-wf):
there, every `PointsToUnaligned` pointer, including the Sized one, is built from the stored metadata,
so `PointsToProperties` can be one generic impl.)

For Sized `T` the metadata is `()`, so `ptr()` stays `pt_untyped().ptr() as *mut T` and `size()`
stays `size_of::<T>()`. The roughly ten specs that say `out.ptr() == pt_untyped.ptr() as *mut T`
(e.g. lines 1318, 1347, 1365, 1383, 1401-1405, 2183, 2242) are unaffected. So are all the
`SeqPointsTo<T, PointsTo<T>>` proofs.

### 3. One impl per unsized type, rather than one generic `?Sized` impl

A single `impl<T: ?Sized> PointsToPhys for PointsToUnaligned<T>` would need a size computed from
metadata, i.e. a new `size_of_metadata::<T>(m)` layout spec (the spec counterpart of the unstable
`size_of_val_raw`). It would also need axioms tying that spec to `size_of` and `spec_size_of_val`
for every unsized type. Per-type impls avoid all of that: the slice impl's size is
`metadata * size_of::<T>()`, built from what `layout.rs` already has (`layout_of_slices`, line 235).
The generic version can come later if `dyn` or custom DSTs are ever needed. Rust accepts
`impl<T> PointsToPhys for PointsToUnaligned<T>` (implicitly `T: Sized`) next to
`impl<T> PointsToPhys for PointsToUnaligned<[T]>`, since `[T]` is never `Sized`.

### 4. A slice permission is all valid or all empty

`TypedValue<[T]>` holds the whole slice or nothing. This is one of the distinguishing differences
between `PointsTo<[T]>` and `SeqPointsTo<T, PointsTo<T>>`, where each element is valid or empty
independently. `SeqPointsTo` keeps its current role for per-element validity. `PointsTo<[T]>` adds
what `SeqPointsTo` can't give: a real `*mut [T]` pointer and a real `&[T]` borrow. Conversions
between the two are part of the plan (step 6).

## Steps

Each step should leave the builds green:

- **Here:** the normal build, `source/tools/build-expand-errors.sh`.
- **In rustlib** (`/Users/estang/Documents/Verus/rustlib`): the verify-core configuration, by
  running `make core` there (`source/tools/build-rustlib-core.sh` does this). Under
  `verus_verify_core`, builtin's `Tracked` `Deref` / `DerefMut` impls are cfg'd out, because rustlib
  provides its own const `Deref` impl for `Tracked`, so that configuration has to be tested there.

### Step 1: add the field; update the Sized construction sites (done)

Check that `Ghost<Metadata<T>>` compiles in both configurations above, including the non-ghost
compile, where `Metadata<T>` is `FakeMetadata<T>`.

- Struct literals (for Sized `T` the metadata is `()`, so nothing else changes):
  - `PointsToUnaligned::zero_sized(ptr)` (line 913): `metadata: Ghost(ptr@.metadata)`, to make the
    connection to `ptr` explicit.
  - `PointsTo::from_untyped(pt_untyped)` (line 1325): `metadata: Ghost(())`, since there's no
    pointer parameter to take it from.
- Destructuring patterns in `into_untyped_with_typed_value` (line 1304) and `into_untyped`
  (line 1373) get `metadata: _` (or `..`).
- Add `&&& self.metadata() == self.ptr()@.metadata` to the Sized `PointsToUnaligned::wf_basic`, to
  make the connection between the field and the pointer explicit (`PointsTo::wf_basic` inherits it
  through `pt_unaligned().wf()`).
- Add a closed accessor in the `impl<T: ?Sized> PointsToUnaligned<T>` block (line 686):
  `pub closed spec fn metadata(self) -> Metadata<T> { self.metadata@ }`, and an open delegating
  `PointsTo::metadata()`.

### Step 2: slice trait impls (done)

Implemented as below, plus inherent `wf()` (= `wf_basic()`) on `PointsToUnaligned<[T]>` and
`PointsTo<[T]>`, which Rust accepts alongside the Sized `wf()`. `PointsTo<[T]>::size()` delegates
to `pt_unaligned().size()`. No `View` for slices yet.

```rust
impl<T> PointsToPhys for PointsToUnaligned<[T]> {
    type A = [T];
    closed spec fn ptr(self) -> *mut [T] {
        ptr_mut_from_data::<[T]>(PtrData {
            addr: self.pt_untyped().ptr()@.addr,
            provenance: self.pt_untyped().ptr()@.provenance,
            metadata: self.metadata(),
        })
    }
    open spec fn size(self) -> nat { self.metadata() as nat * size_of::<T>() }
}

impl<T> PointsToProperties for PointsToUnaligned<[T]> {
    open spec fn wf_basic(self) -> bool {
        &&& self.bytes().len() == self.size()
        &&& self.pt_untyped().wf()
        &&& self.metadata() == self.ptr()@.metadata   // as in the Sized wf_basic
        &&& self.is_valid() ==> {
            &&& self.typed_value().value()@.len() == self.metadata()
            &&& abs_decode::<[T]>(self.bytes(), self.typed_value().value())
        }
    }
    // is_nonnull, ptr_bounds, provenance_not_none, is_disjoint, stays_wf_basic:
    // delegate to pt_untyped, as the Sized impl does (lines 766-821).
    open spec fn ptrs_len_same_valid(old: Self, new: Self) -> bool {
        &&& new.ptr() == old.ptr()          // also fixes the metadata
        &&& PointsToUntyped::ptrs_len_same_valid(old.pt_untyped(), new.pt_untyped())
        &&& new.is_valid() ==> abs_decode::<[T]>(new.bytes(), new.typed_value().value())
    }
}
```

- `PointsTo<[T]>` gets the same pair. Its `wf_basic` adds alignment to `align_of::<T>()` (matching
  `layout_of_slices`), and `ptr()` delegates to `pt_unaligned()`.
- No `FixedSize` impl: slices aren't `SeqPointsTo` elements.
- No separate bound on the metadata (e.g. `metadata * size_of::<T>() <= isize::MAX`). When
  `size_of::<T>() > 0`, the product is the byte length, which the untyped permission's provenance
  bounds already limit. When `size_of::<T>() == 0`, the product is 0, so the bound would say
  nothing; Rust doesn't limit a ZST slice's length beyond the metadata being a `usize`.
- The trait methods (`is_nonnull` etc.) are on the dependency path of
  `group_points_to_permissions_lemmas`, so they use the specific groups
  `{group_raw_ptr_axioms, group_layout_axioms, group_seq_axioms}`, never `group_vstd_default`.
- `View`: `PointsToData<T>` is Sized-only (line 1002). Either give it `T: ?Sized` (its `value` field
  is a `TypedValue<T>`, which already allows that) or skip `View` for slices at first.

### Step 3: empty slice permissions (all proved) (written, reverted, saved in `step3_slice_wip.patch`)

On hold until the `PointsToSingleValue` trait is in:
these become trait impls in its phase 2b
(see [TYPED_POINTS_TO_IMPL_PLAN.md](TYPED_POINTS_TO_IMPL_PLAN.md#phase-2b-slice-impls-ghost-steps-3-and-5)).
The inherent versions were written as listed below, with these details:

- `PointsToUnaligned<[T]>` has `from_untyped`, `into_aligned`, `as_aligned`, `zero_sized`
  and `lemma_ptrs_len_same_valid_slice`,
  mirroring the Sized `PointsToUnaligned` (plus `from_untyped`).
- `PointsTo<[T]>` has `from_untyped`, `into_untyped`, `as_untyped`,
  `into_untyped_with_typed_value`, `into_unaligned`, `as_unaligned`, `zero_sized`
  and `lemma_ptrs_len_same_valid_slice`.
  There is no `as_untyped_mut` yet.
- Pointers can't be cast to `*mut [T]`, so the untyped conversions state the address,
  provenance and length (`self.size()`) separately,
  and `from_untyped` states `out.ptr() == ptr_mut_from_data::<[T]>(...)` with metadata `len`.
- Both `lemma_ptrs_len_same_valid_slice` lemmas are in `group_points_to_permissions_lemmas`.
- Since `PointsTo<T>` and `PointsTo<[T]>` now share inherent function names,
  a path call like `PointsTo::zero_sized(p)` is ambiguous,
  so the one such call (in `SeqPointsTo::zero_sized_helper`) is now `PointsTo::<T>::zero_sized`.
  Method calls are unaffected.

None of these need a slice value, so they are plain field construction and destructuring:

- `PointsToUnaligned::<[T]>::from_untyped(pt_untyped, len)`: requires `pt_untyped.wf()` and
  `pt_untyped.len() == len * size_of::<T>()`; ensures `wf()`, `is_empty()` and
  `ptr()@.metadata == len`. The aligned version also requires alignment to `align_of::<T>()`.
- `into_untyped`, `as_untyped`, `into_untyped_with_typed_value`, mirroring the Sized versions.
- `into_aligned` / `as_aligned` / `into_unaligned` / `as_unaligned` for slices.
- `zero_sized` variants: any length when `size_of::<T>() == 0`, or `len == 0` for any `T`. The
  stored metadata is what makes the ZST case expressible at all.
- `lemma_ptrs_len_same_valid` for the slice impls, added to the broadcast group. The `PointsTo` and
  `SeqPointsTo` versions can't share a name across impls of the same type, so these lemmas may need
  suffixed names (as with the earlier `_untyped` rename).

### Step 4: how a slice decodes (new axiom) (done)

Added to `type_representation.rs` after `encode_decode_inverse`, and to
`group_type_representation_axioms`. The inner `forall` is triggered on `v@[i]`, since the
per-element `abs_decode::<T>` term contains arithmetic on `i`.

`abs_decode` is uninterpreted, and its only general axiom ties length to `size_of`, which needs
`Sized`. A valid slice needs a rule like this one, in `type_representation.rs`:

```rust
pub broadcast axiom fn abs_decode_slice<T>(bytes: Seq<AbstractByte>, v: &[T])
    ensures
        #[trigger] abs_decode::<[T]>(bytes, v) <==> {
            &&& bytes.len() == v@.len() * size_of::<T>()
            &&& forall|i: int| 0 <= i < v@.len() ==> #[trigger] abs_decode::<T>(
                bytes.subrange(i * size_of::<T>(), (i + 1) * size_of::<T>()), &v@[i])
        },
;
```

This follows the same pattern as the existing `[u8]` axiom: `EncodingU8Slice`'s `abs_encode_impl`
([type_representation.rs:1390](type_representation.rs)) states
`EncodingU8Slice::decode(b, v) <==> abs_decode::<[u8]>(b, v)`, where `decode` is a per-element
condition (`v@.len() == b.len()` and each byte decodes to its element). `abs_decode_slice` states
the same per-element shape for any `[T]`, with each element taking a `size_of::<T>()`-byte slot and
decoding by `abs_decode::<T>`. For `T = u8` the two agree, since `u8`'s own `abs_encode_impl`
makes `u8::decode` and `abs_decode::<u8>` equivalent and `size_of::<u8>() == 1`.

It goes in `type_representation.rs` with the other encoding facts.

Not part of this plan: generalizing `EncodingU8Slice` itself into an
`AbstractByteRepresentationUnsized<[T]>` impl for every `T: AbstractByteRepresentation`, which
would replace the `[u8]` axiom with one for all such slices. That can be done later.

### Step 5: borrow the slice (proved)

`Tracked`'s `Deref` in builtin now takes `A: ?Sized`. Under `verus_verify_core` it is cfg'd out and
rustlib's const `Deref` impl for `Tracked` is used instead, so that impl must also take
`A: ?Sized` (to check in rustlib). So `PointsTo<[T]>::borrow(&self) -> &[T]` (named `borrow_value` before TYPED_POINTS_TO_PLAN.md's rename) can be a field
borrow of `Valid(t)`, the same way
`TypedValue<[T]>::value()` already reads `&*self->0` (line 655). This is the `tracked_borrow` that
[POINTS_TO_MIGRATION.md](POINTS_TO_MIGRATION.md) §7 lists as "Not possible".

### Step 6: borrowed conversions between `SeqPointsTo` and `PointsTo<[T]>`

Valid slice permissions come from real `&[T]` / `&mut [T]` references (step 7), which supply the
tracked `[T]`. Proof code never needs to turn an owned `SeqPointsTo<T, PointsTo<T>>` into an owned
`PointsTo<[T]>`, so there is nothing for that. The conversions to support are:

- `&SeqPointsTo<T, PointsTo<T>>` ↔ `&PointsTo<[T]>`
- `&mut SeqPointsTo<T, PointsTo<T>>` ↔ `&mut PointsTo<[T]>`

Indexing into a `PointsTo<[T]>` is done by converting to a `SeqPointsTo` and indexing that, so there
is no separate element-borrow function.

The bytes part of each conversion is already provable (`SeqPointsTo::as_untyped`, or `as_untyped` +
`PointsToUntyped::split_ref`). What's missing is the typed value and a way to assemble the result.
`shr_ref_struct_wrap` can't build a `&PointsToUnaligned<T>` from a `&PointsToUntyped`, because it
requires every other field of the target to be ghost (`rust_verify` checks this in
`well_formed.rs`), and `val: TypedValue<T>` is tracked. That holds even for an `Empty` value or a
`Copy` `T`. Likewise, a `&SeqPointsTo` needs a stored `Seq` of permissions to borrow.

Rather than one axiom per conversion, the plan adds a few low-level axioms that only describe slice
structure or field assembly, and proves the conversions from them.

#### Low-level axioms

```rust
// slice.rs: no permissions involved
pub axiom fn tracked_slice_index<'a, T>(tracked s: &'a [T], i: int) -> (tracked e: &'a T)
    requires
        0 <= i < s@.len(),
    ensures
        *e == s@[i],
;

pub axiom fn tracked_slice_from_refs<'a, T>(tracked refs: Seq<&'a T>) -> (tracked s: &'a [T])
    ensures
        s@ == refs.map_values(|r: &T| *r),
;

// points_to_permissions.rs: borrowed versions of the struct literals; no wf
impl<T: ?Sized> PointsToUnaligned<T> {
    pub axiom fn from_raw_parts_ref<'a>(
        tracked pt_untyped: &'a PointsToUntyped,
        tracked typed_value: &'a TypedValue<T>,
        metadata: Metadata<T>,
    ) -> (tracked out: &'a Self)
        ensures
            out.pt_untyped() == *pt_untyped,
            out.typed_value() == *typed_value,
            out.metadata() == metadata,
    ;
}

// Collects borrowed permissions (not arbitrary values) into a borrowed Seq.
pub axiom fn tracked_collect_perm_refs<'a, P: PointsToProperties>(tracked perms: Seq<&'a P>)
    -> (tracked out: &'a Seq<P>)
    ensures
        *out == perms.map_values(|r: &P| *r),
;
```

There's no precondition. The same reference may be passed more than once, which is harmless: a
shared reference never guarantees uniqueness (several `&PointsTo<T>` to one permission can already
exist), so distinctness of permissions is only ever derived through `&mut`, as with `is_disjoint`.
The axiom says nothing about `SeqPointsTo` or `wf()`.

`SeqPointsTo::from_refs` is then proved, the same way `PointsToUntyped::split_ref` is:
`SeqPointsTo`'s only other field is `ptr: Ghost<*mut T>`, so `shr_ref_struct_wrap` can wrap the
collected `&Seq<P>`.

(Written against the current `SeqPointsTo`.
After [TYPED_POINTS_TO_PLAN.md phase 1b](TYPED_POINTS_TO_PLAN.md#seqpointstos-pointer-and-sizes)
the bound is `P: PointsToProperties<A = T>`, offsets use `P::size(())`,
`ptr` is a thin `*mut T`, and the result has `out.thin_ptr() == ptr`.)

```rust
impl<T: ?Sized, P: PointsToProperties + FixedSize> SeqPointsTo<T, P> {
    pub proof fn from_refs<'a>(tracked perms: Seq<&'a P>, ptr: *mut T) -> (tracked out: &'a Self)
        requires
            forall|i: int| 0 <= i < perms.len() ==> {
                &&& (#[trigger] perms[i]).ptr()@.provenance == ptr@.provenance
                &&& perms[i].ptr()@.addr == ptr@.addr + i * P::const_size()
            },
        ensures
            out.seq_pt() == perms.map_values(|r: &P| *r),
            out.ptr() == ptr,
    {
        let tracked s = tracked_collect_perm_refs(perms);
        shr_ref_struct_wrap(s, &SeqPointsTo { seq_pt: *s, ptr: Ghost(ptr) }, "", "seq_pt")
    }
}
```

Like `from_raw_parts_ref`, `from_refs` says nothing about `wf()`: callers prove `wf_basic()` /
`wf()` from the elements, as the owned `from_seq` does. Since it works for any element type,
`PointsToUntyped::join_ref` should become provable from it (borrow both halves'
`PointsToSingleton`s, concatenate, `from_refs`), removing that existing axiom.

Plus two small pieces for producing a `&'a TypedValue<T>`:

- **`tracked_ref`**, a vstd axiom (e.g. in `modes.rs`, next to `tracked_swap`), and the proved
  `TypedValue::valid_ref` built on it:

  ```rust
  pub axiom fn tracked_ref<'a, T: ?Sized>(tracked t: &'a T) -> (tracked out: &'a Tracked<T>)
      ensures
          &**out == t,
  ;

  impl<T: ?Sized> TypedValue<T> {
      pub proof fn valid_ref<'a>(tracked v: &'a T) -> (tracked out: &'a TypedValue<T>)
          ensures
              out.is_valid(),
              &*out->0 == v,
      {
          let tracked t = tracked_ref(v);
          shr_ref_struct_wrap(t, &TypedValue::Valid(*t), "Valid", "0")
      }
  }
  ```

  `shr_ref_struct_wrap` can't wrap a `&T` into `Valid` directly, because `Valid`'s field is a
  `Tracked<T>` and the wrap's field-type check is strict. It can wrap a `&Tracked<T>`: `TypedValue`
  is a non-ghost datatype, `Valid` has that one field, the types match exactly, and there are no
  other fields. `tracked_ref` is trivially sound, since `Tracked<T>` is `T` in ghost code, and says
  nothing about permissions. Its postcondition and `valid_ref`'s use `Tracked`'s `Deref`, which
  under verify-core is rustlib's const impl (see step 5). Not yet built: confirm at the start of
  implementation that the first
  argument's recorded type matches the field's `Tracked<T>` (the check notes it isn't robust to
  normalization). A small Verus change to that check could later remove `tracked_ref` (see
  [Follow-up after this plan](#follow-up-after-this-plan)).
- **An empty `&'a TypedValue<T>`**, for the empty cases: proved, not an axiom.
  `tracked_static_ref(TypedValue::Empty)` (`modes.rs:19`, proved from the existing
  `tracked_static_mut_ref` axiom) gives a `&'static TypedValue<T>`, which coerces to `&'a`.
  `SeqPointsTo::as_untyped` already uses the same trick for its empty case. This works for
  `TypedValue<[T]>` too, since it is `Sized`. So a borrowed empty constructor
  (`from_untyped_ref`) is `from_raw_parts_ref(pt_untyped, tracked_static_ref(TypedValue::Empty),
  metadata)`.

None of these mention `wf()`, alignment or decoding, so those facts are still proved by the callers.
`&PointsToUnaligned<T>` → `&PointsTo<T>` is already provable with `shr_ref_struct_wrap`
(`PointsTo` has one field).

#### Proved borrowed constructors

These are the borrowed counterparts of the owned `from_untyped` / `from_untyped_with_typed_value`.
Each conversion below picks one depending on whether the permission is all valid or all empty.

- **`PointsTo::<[T]>::from_untyped_ref(&'a PointsToUntyped, len) -> &'a PointsTo<[T]>`** (empty):
  `from_raw_parts_ref(pt_untyped, tracked_static_ref(TypedValue::Empty), len)`, then wrap into
  `&PointsTo<[T]>`.
- **`PointsTo::<[T]>::from_untyped_with_value_ref(&'a PointsToUntyped, &'a [T]) -> &'a PointsTo<[T]>`**
  (valid): `from_raw_parts_ref(pt_untyped, valid_ref(value), value@.len())`, then wrap.
- **`SeqPointsTo::<T, PointsTo<T>>::from_untyped_ref(&'a PointsToUntyped, len)`** (empty): split the
  bytes per element with `split_ref`, build each element's `&PointsTo<T>` with `from_raw_parts_ref`
  and `tracked_static_ref(TypedValue::Empty)`, then `from_refs`.
- **`SeqPointsTo::<T, PointsTo<T>>::from_untyped_with_value_ref(&'a PointsToUntyped, &'a [T])`**
  (valid): the same, with each element's typed value from `tracked_slice_index` → `valid_ref`.

Each requires the conditions the owned versions require (`wf()`, alignment, length, and for the
valid ones that the bytes decode to the value), and ensures `wf()` of the result, proved from the
alignment arithmetic and, for the valid ones, `abs_decode_slice`.

#### Proved shared conversions

- **`SeqPointsTo::<T, PointsTo<T>>::as_slice_pt(&self) -> &PointsTo<[T]>`:** requires the sequence
  to be all valid or all empty, since a `PointsTo<[T]>` can't represent a mix. Bytes from
  `SeqPointsTo::as_untyped` (proved). If valid: `borrow_subrange` (proved; renamed from `borrow_value_subrange`) → `Seq<&T>` →
  `tracked_slice_from_refs` → `&[T]`, then `PointsTo::<[T]>::from_untyped_with_value_ref`. If empty:
  `PointsTo::<[T]>::from_untyped_ref`. A zero-length sequence is vacuously `is_valid()`, so it comes
  back as a valid, empty slice and is never required to be valid and empty at once.
- **`PointsTo::<[T]>::as_seq_pt(&self) -> &SeqPointsTo<T, PointsTo<T>>`:** bytes from `as_untyped`
  (proved). If valid: `&[T]` (proved, via `Tracked`'s `Deref`), then
  `SeqPointsTo::from_untyped_with_value_ref`. If empty: `SeqPointsTo::from_untyped_ref`. Ensures
  `len() == metadata`, the same address and provenance, the same bytes, and all valid with
  `seq_value() == value()@` or fully empty.

#### `&mut` conversions: split into bytes and typed values

Each permission is borrowed as two disjoint parts, its bytes (`&mut PointsToUntyped`) and its typed
value (`&mut TypedValue<_>`), and each part is converted separately. This needs neither
`PointsTo::borrow_mut` nor the reverted generic `wrap_mut`, and it has three advantages:

- **No `borrow_mut`.** Values are borrowed as `&mut TypedValue<T>`, never as `&mut T`, and the bytes
  are a separate borrow. Nothing asserts that the bytes follow a ghost write to the value. When the
  borrow ends, the original is `wf()` again only if the final bytes decode the final value. Exec
  writes (e.g. through the restored `ptr_mut_ref_slice`) update both, so they get `wf()` back;
  ghost-only writes that leave the bytes stale don't.
- **Validity can change inside the borrow.** Borrowing whole `TypedValue`s (rather than `&mut T`)
  lets the value conversions carry `Valid` ↔ `Empty` changes across. Taking the slice's value out
  leaves every element empty; putting a slice in makes every element valid.
- **Each mutable wrap is its own small axiom**, for one specific struct, instead of a generic
  `wrap_mut`.

##### New `&mut` axioms

All of these follow `PointsToUntyped::join_mut`'s pattern: the borrowed parts' final values are
tied to the result's final value, conditionally where the structure could change.

```rust
// Value conversions (TypedValue level)
impl<T> TypedValue<[T]> {
    // M1: per-element typed values -> slice typed value
    pub axiom fn from_elems_mut<'a>(tracked elems: Seq<&'a mut TypedValue<T>>)
        -> (tracked out: &'a mut TypedValue<[T]>)
        requires
            (forall|i: int| 0 <= i < elems.len() ==> (*elems[i]).is_valid())
                || (forall|i: int| 0 <= i < elems.len() ==> (*elems[i]).is_empty()),
        ensures
            // initially: valid with the elements' values (a zero-length Seq counts as valid), or empty
            // finally: if final(out) is valid with length elems.len(), each *final(elems[i]) is
            //          valid with final(out).value()@[i]; otherwise each is empty
    ;

    // M2: slice typed value -> per-element typed values (the inverse of M1)
    pub axiom fn into_elems_mut<'a>(tracked &'a mut self, len: nat)
        -> (tracked elems: Seq<&'a mut TypedValue<T>>)
        requires
            old(self).is_valid() ==> old(self).value()@.len() == len,
        ensures
            // initially: elems.len() == len, each valid with old(self).value()@[i], or each empty
            // finally: if every *final(elems[i]) is valid, final(self) is valid holding them;
            //          otherwise final(self) is empty (any remaining values are dropped)
    ;
}

// Field assembly (the &mut version of from_raw_parts_ref)
impl<T: ?Sized> PointsToUnaligned<T> {
    // M3
    pub axiom fn from_raw_parts_mut<'a>(
        tracked pt_untyped: &'a mut PointsToUntyped,
        tracked typed_value: &'a mut TypedValue<T>,
        metadata: Metadata<T>,
    ) -> (tracked out: &'a mut Self)
        ensures
            out.pt_untyped() == *old(pt_untyped),
            out.typed_value() == *old(typed_value),
            out.metadata() == metadata,
            *final(pt_untyped) == final(out).pt_untyped(),
            *final(typed_value) == final(out).typed_value(),
    ;
}

// Single-field wraps (the &mut counterparts of the shr_ref_struct_wrap uses)
impl<T: ?Sized> PointsTo<T> {
    // M4: &mut PointsToUnaligned<T> -> &mut PointsTo<T> (also gives the missing as_aligned_mut)
    pub axiom fn from_unaligned_mut<'a>(tracked u: &'a mut PointsToUnaligned<T>)
        -> (tracked out: &'a mut Self)
        ensures
            out.pt_unaligned() == *old(u),
            *final(u) == final(out).pt_unaligned(),
    ;
}

impl<T: ?Sized, P: PointsToProperties + FixedSize> SeqPointsTo<T, P> {
    // M5: &mut Seq<P> -> &mut SeqPointsTo<T, P> (ptr is the only other field, and is Ghost)
    pub axiom fn from_seq_mut<'a>(tracked s: &'a mut Seq<P>, ptr: *mut T)
        -> (tracked out: &'a mut Self)
        ensures
            out.seq_pt() == *old(s),
            out.ptr() == ptr,
            *final(s) == final(out).seq_pt(),
    ;
}

// Collecting permissions (the &mut version of tracked_collect_perm_refs)
// M6
pub axiom fn tracked_collect_perm_muts<'a, P: PointsToProperties>(tracked perms: Seq<&'a mut P>)
    -> (tracked out: &'a mut Seq<P>)
    ensures
        *out == perms.map_values(|r: &mut P| *r),
        // finally: if final(out).len() == perms.len(), each *final(perms[i]) == final(out)[i]
;
```

Things that are proved from existing pieces, so need no new axiom:
- `&mut SeqPointsTo` → `&mut Seq<P>`: `tracked_seq_pt_mut` (existing).
- `&mut Seq<P>` → `Seq<&mut P>`: repeated `Seq::tracked_split_borrow_mut` (existing `external_body`).
- `&mut PointsTo<T>` → `&mut PointsToUnaligned<T>` → (`&mut PointsToUntyped`, `&mut TypedValue<T>`):
  field borrows of disjoint fields, inside the module. Expected to be accepted by Verus's `&mut`
  support; confirm at the start of implementation.
- An empty `&'a mut TypedValue<T>` when there are no elements: `tracked_static_mut_ref` (existing).
- `PointsToUntyped::split_mut` (commented out since it was proved from `wrap_mut`): proved from M6
  and M5 instead. Likewise `PointsToUntyped::join_mut`, which would turn that existing axiom into a
  proved function.

##### Proved `&mut` conversions

- **`SeqPointsTo::<T, PointsTo<T>>::as_slice_pt_mut(&mut self) -> &mut PointsTo<[T]>`.** Requires
  `wf()` and all valid or all empty. Borrow the `Seq<PointsTo<T>>` (`tracked_seq_pt_mut`) and split
  it per element; split each element into its bytes and typed value. Join the bytes with `join_mut`
  (or M6 + M5), join the typed values with M1, assemble with M3 and wrap with M4. Ensures: initially
  the same facts as `as_slice_pt`; finally, if the slice keeps its pointer and stays well-formed
  (`PointsTo::<[T]>::ptrs_len_same_valid(*s, *final(s))`), then `final(self)` is `wf()` with the
  same pointer, length and bytes as the slice, and is all valid with
  `seq_value() == final(s).value()@` if the slice ends valid, or fully empty if it ends empty.
- **`PointsTo::<[T]>::as_seq_pt_mut(&mut self) -> &mut SeqPointsTo<T, PointsTo<T>>`.** Requires
  `wf()`. Split `self` into its bytes and typed value. Split the bytes per element (`split_mut`,
  proved from M6 + M5), split the typed value with M2, assemble each element with M3 + M4, collect
  with M6 and wrap with M5. Ensures: initially the same facts as `as_seq_pt`; finally, if the
  sequence keeps its pointer and length and stays well-formed
  (`SeqPointsTo::ptrs_len_same_valid(*q, *final(q))`), then `final(self)` is `wf()` with the same
  pointer and the sequence's bytes, and is valid with `value()@ == final(q).seq_value()` if every
  element ends valid, or empty otherwise. A mix of valid and empty elements can't be represented, so
  the remaining values are dropped.

All the trusted items step 6 relies on are listed in [Trusted surface](#trusted-surface).

#### Notes

- **Empty owned conversions** (an empty `PointsTo<[T]>` to and from an empty `SeqPointsTo`) can be
  proved through the untyped permission (`into_untyped`, then `from_untyped`) if they turn out to be
  useful.

### Step 7: re-enable the slice helpers (where valid slices come from)

These are the planned sources of valid `PointsTo<[T]>` permissions: they come from a real `&[T]` or
`&mut [T]`, which supplies the tracked `[T]`. With `PointsTo<[T]>` in place, restore the
commented-out:

- `SharedReference<[T]>::points_to` (`shared_reference.rs:126`, `:223`): `&[T]` → `&PointsTo<[T]>`;
- the `&mut [T]` conversion at `raw_ptr_new.rs:691`: `&mut [T]` → `&mut PointsTo<[T]>`;
- `ptr_ref_slice` and `ptr_mut_ref_slice` (`raw_ptr_new.rs:524`, `:559`), which go back from a
  pointer and a permission to a real reference.

Update their contracts to the new specs, and review them when they're restored.

### Step 8: docs

- [PORTING_STATUS.md](PORTING_STATUS.md): replace the "Port `impl<T> PointsTo<[T]>`" TODO and the
  unaligned-slices on-hold item. Note that `cast_points_to` / `cast_points_to_unaligned` now have a
  home.
- [POINTS_TO_MIGRATION.md](POINTS_TO_MIGRATION.md) §7-8: `PointsTo<[T]>` exists again for
  whole-slice values; per-element validity is still `SeqPointsTo`.
- [POINTS_TO_AXIOMS.md](POINTS_TO_AXIOMS.md): the new axioms from steps 4 and 6 (the slice-level
  ones may belong in `slice.rs`'s own docs instead).
- [GENERALIZATION_ASSESSMENT.md](GENERALIZATION_ASSESSMENT.md) §2: the `ptr()` blocker is resolved
  for slices.

## Trusted surface

Everything the plan trusts, in one place. The contracts are in the steps that introduce each item
(step 4 for `abs_decode_slice`, step 6 for the rest).

### New

| Item | Input → output | Used by | What it says | Why it can't be proved |
|---|---|---|---|---|
| `abs_decode_slice` | `Seq<AbstractByte>`, `&[T]` → (broadcast fact) | slice `wf` (step 2) | Bytes decode to a slice exactly when each element's slot decodes to that element (same pattern as the existing `[u8]` axiom). | `abs_decode` is uninterpreted; the slice encoding has to be stated. |
| `tracked_slice_index` | `&'a [T]`, `int` → `&'a T` | shared | Borrows an element of a borrowed slice. | No proof-mode slice indexing. |
| `tracked_slice_from_refs` | `Seq<&'a T>` → `&'a [T]` | shared | Borrowed elements act as one borrowed slice. | No proof-mode way to build a borrowed slice from borrowed elements. |
| `tracked_ref` | `&'a T` → `&'a Tracked<T>` | shared | A borrowed value is a borrowed `Tracked` of itself. Makes `TypedValue::valid_ref` provable. | No proof-mode way to view a borrow as a borrowed `Tracked`. Could be removed afterwards by a Verus check change (see the follow-up). |
| `PointsToUnaligned::from_raw_parts_ref` | `&'a PointsToUntyped`, `&'a TypedValue<T>`, `Metadata<T>` → `&'a PointsToUnaligned<T>` | shared | Borrowed bytes and typed value act as one borrowed permission. | `shr_ref_struct_wrap` can't assemble a struct with more than one tracked field. |
| `tracked_collect_perm_refs` | `Seq<&'a P>` → `&'a Seq<P>` | shared | Borrowed permissions act as one borrowed `Seq`. Makes `SeqPointsTo::from_refs` provable. | No stored `Seq` of permissions to borrow. |
| M1 `TypedValue::<[T]>::from_elems_mut` | `Seq<&'a mut TypedValue<T>>` → `&'a mut TypedValue<[T]>` | `&mut` | Borrowed per-element typed values act as one borrowed slice typed value; validity changes are distributed back to the elements. | A tracked `[T]` can't be assembled from or split into elements in proof code. |
| M2 `TypedValue::<[T]>::into_elems_mut` | `&'a mut TypedValue<[T]>`, `nat` → `Seq<&'a mut TypedValue<T>>` | `&mut` | The inverse of M1; a mixed final state drops the remaining values. | Same as M1. |
| M3 `PointsToUnaligned::from_raw_parts_mut` | `&'a mut PointsToUntyped`, `&'a mut TypedValue<T>`, `Metadata<T>` → `&'a mut PointsToUnaligned<T>` | `&mut` | Borrowed bytes and typed value act as one borrowed permission. | No mutable struct wrap for structs with two tracked fields. |
| M4 `PointsTo::from_unaligned_mut` | `&'a mut PointsToUnaligned<T>` → `&'a mut PointsTo<T>` | `&mut` | A borrowed `PointsToUnaligned` acts as a borrowed `PointsTo`. | No mutable counterpart of `shr_ref_struct_wrap`. |
| M5 `SeqPointsTo::from_seq_mut` | `&'a mut Seq<P>`, `*mut T` → `&'a mut SeqPointsTo<T, P>` | `&mut` | A borrowed `Seq<P>` acts as a borrowed `SeqPointsTo` with the given (ghost) pointer. | Same as M4. |
| M6 `tracked_collect_perm_muts` | `Seq<&'a mut P>` → `&'a mut Seq<P>` | `&mut` | Borrowed permissions act as one borrowed `Seq`. | No stored `Seq` to borrow. |
| `&[T]` / `&mut [T]` → `PointsTo<[T]>` | `&[T]` → `&PointsTo<[T]>`; `&mut [T]` → `&mut PointsTo<[T]>` (exact shapes, e.g. whether a pointer is also returned, settled when restored) | sources of valid slices (step 7) | A real slice reference gives a slice permission (and the tracked `[T]`). | Exec/ghost boundary; existed in the old model (`raw_ptr_new.rs:691`, `shared_reference.rs:126`) but commented out today. |

### Existing

| Item | Input → output | Kind | Used by | Status |
|---|---|---|---|---|
| `PointsToUntyped::join_ref` | `&'a PointsToUntyped`, `&'a PointsToUntyped` → `&'a PointsToUntyped` | axiom | shared (via `SeqPointsTo::as_untyped`) | Becomes provable from `tracked_collect_perm_refs` (via `from_refs`). |
| `PointsToUntyped::join_mut` | `&'a mut PointsToUntyped`, `&'a mut PointsToUntyped` → `&'a mut PointsToUntyped` | axiom | `&mut` | Becomes provable from M5 + M6. |
| `tracked_static_mut_ref` | `V` → `&'static mut V` | axiom | shared (via `tracked_static_ref`) and `&mut`, for the empty cases | Unchanged. |
| `Seq::tracked_borrow` | `&Seq<A>`, `int` → `&A` | `external_body` | shared | Unchanged. |
| `Seq::tracked_borrow_subrange` | `&Seq<A>`, `int`, `int` → `&Seq<A>` | `external_body` | shared (via `split_ref`) | Unchanged. |
| `Seq::tracked_split_borrow_mut` | `&mut Seq<A>`, `int` → `(&mut Seq<A>, &mut Seq<A>)` | `external_body` | `&mut` | Unchanged. |

### Not trusted

- No axiom turns an owned `SeqPointsTo<T, PointsTo<T>>` into an owned `PointsTo<[T]>`.
- No new axiom mentions `wf()`, alignment, or decoding, except `abs_decode_slice`.
- Proved from the items above: the field, the trait impls, the owned empty constructors,
  `borrow`, `TypedValue::valid_ref`, the borrowed constructors, `SeqPointsTo::from_refs`, all
  four conversions (`as_slice_pt`, `as_seq_pt`, `as_slice_pt_mut`, `as_seq_pt_mut`), and the empty
  owned conversions.
- Not needed at all: `PointsTo::borrow_mut`, `borrow_mut_subrange`, `wrap_mut`, and any
  `&mut [T]` / `&mut T` slice axioms.

### Review notes

- **Duplicate references.** `tracked_slice_from_refs` and `tracked_collect_perm_refs` can be given
  the same reference more than once, producing a borrowed slice or `Seq` with repeated elements.
  This is harmless: a shared reference never guarantees uniqueness (several `&PointsTo<T>` to one
  permission can already exist), so distinctness is only derived through `&mut`, which is why
  `is_disjoint` takes `&mut` even though it doesn't modify anything. All disjointness lemmas on
  points-to permissions require `&mut`, so none can conclude distinctness from the collected
  shared borrow. M6 can't receive duplicates at all: a `Seq<&mut P>` can't hold the same mutable
  borrow twice.
- **The `&mut` axioms (M1–M6)** are accepted. Like `join_mut`, each hands out a `&mut` to something
  that isn't stored. Each is sound because every final state of the result maps to a consistent
  final state of the borrowed parts without duplicating a tracked value: M1/M2 drop values rather
  than duplicate them when the final state can't be distributed, and M6's finals are only tied when
  the length is unchanged.
- **The restored `&mut [T]` conversions** (step 7) still need their contracts updated and reviewed
  when they're restored.

## Follow-up after this plan

- **Replace `tracked_ref` with a Verus change.** The plan uses the `tracked_ref` axiom. Afterwards,
  it can be removed by relaxing `shr_ref_struct_wrap`'s field-type check. In VIR, `Tracked<A>` is a
  type decoration on `A`, not a struct (`rust_to_vir_base.rs:1149`), so `shr_ref_struct_wrap` can't
  produce a `&Tracked<A>`, and wrapping a `&A` into `TypedValue::Valid`'s `Tracked<A>` field fails
  the strict field-type check (`well_formed.rs:785`). Relaxing that check to accept a first argument
  of type `X` for a field of type `Tracked<X>` would let `valid_ref` wrap the `&T` directly, with no
  axiom. `Tracked<X>` and `X` are the same value in ghost code, and `shr_ref_struct_wrap` is
  proof-only, so `Tracked`'s runtime layout doesn't matter. Confirm `ast_simplify.rs:475` handles
  the decorated field. To be checked with a Verus developer.

## Out of scope

- **`PointsToSingleValue`** (the trait proposed in `GENERALIZATION_ASSESSMENT.md` §4) now comes
  before steps 3 and 5-8,
  so that the slice functions are trait impls with shared contracts.
  See [TYPED_POINTS_TO_IMPL_PLAN.md](TYPED_POINTS_TO_IMPL_PLAN.md#combined-order) for the combined order.
- **`str`** follows the same pattern (metadata equal to the byte length), but it will be done in
  the rustlib repo (`/Users/estang/Documents/Verus/rustlib`), not in vstd. There, the view of a
  `str` is its bytes, rather than its characters as in vstd.
  There is no `SeqPointsTo<str, _>`; `str` permissions convert to and from `PointsTo<[u8]>`.
  See [TYPED_POINTS_TO_PLAN.md](TYPED_POINTS_TO_PLAN.md#str-in-rustlib).
