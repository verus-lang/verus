# Soundness bug: `is_disjoint` doesn't require `other` to be well-formed

**Status:** fixed in the current code on `verify-rustlib-refactor` (2026-10-19),
by the suggested approach below:
`wf_basic` moved into `PointsToPhys`,
and `is_disjoint` and its specialized versions now require `other` to be well-formed.
The reproduction now fails (`precondition not satisfied` on `other.wf_basic()`).
The matching change to the approved trait design is in `TYPED_POINTS_TO_APPROVED.md` (approved 2026-10-19).
Still open: the `is_disjoint_byte` rename
and the unsealed-trait hole described under "Remaining hole".

## Summary

`PointsToProperties::is_disjoint` (`points_to.rs:90`) promises that the memory ranges of `self` and `other` don't overlap.
It requires `self.wf_basic()`, but nothing about `other`:

```rust
proof fn is_disjoint<OtherPointsToPerm: PointsToPhys>(
    tracked &mut self,
    tracked other: &OtherPointsToPerm,
)
    requires
        self.size() != 0,
        other.size() != 0,
        self.wf_basic(),
    ensures
        *old(self) == *final(self),
        final(self).ptr() as int + final(self).size() <= other.ptr() as int
            || other.ptr() as int + other.size() <= final(self).ptr() as int,
;
```

Every impl delegates down to the base axiom, `PointsToSingleton::is_disjoint` (`points_to.rs:161`).
That axiom assumes `other`'s whole `size()` range is memory that `other` actually owns.
For `PointsTo<T>` and `PointsToUnaligned<T>`, though, `size()` is `size_of::<T>()`, fixed by the type.
Only `wf_basic` ties it to the bytes the permission really holds (`pt_untyped().len()`).
So a permission that isn't `wf_basic` can claim memory it doesn't own,
and `is_disjoint` turns that claim into a contradiction.

## How to get a non-wf permission

`PointsTo::as_untyped_mut` (`points_to_permissions.rs:1544`) only promises `final(self).wf()`
when the final untyped permission keeps the original pointers and length:

```rust
PointsToUntyped::ptrs_len_same_valid(*pt_untyped, *final(pt_untyped)) ==> final(self).wf(),
```

Inside the borrow, a caller can swap an empty, zero-length `PointsToUntyped` at the same address
into the borrowed slot (`tracked_swap`), and keep the original bytes.
When the borrow ends, they hold both:

- the original 8 bytes, as a well-formed `PointsToUntyped`, and
- a `PointsTo<u64>` at the same address with `size() == 8` but no bytes (not `wf`).

`bytes.is_disjoint(&that_points_to)` then says two ranges starting at the same address are disjoint.

## Reproduction

Save as a standalone file and verify against the built vstd
(from `source/`: `./target-verus/release/verus --crate-type=lib <file>.rs`).
It verifies (proves `false`). Commenting out the last line makes it fail, so the result isn't vacuous.

```rust
use vstd::layout::*;
use vstd::points_to::*;
use vstd::points_to_permissions::*;
use vstd::prelude::*;
use vstd::raw_ptr_new::*;

verus! {

proof fn exploit(tracked p: PointsTo<u64>)
    requires
        p.wf(),
    ensures
        false,
{
    broadcast use vstd::group_vstd_default;

    let tracked mut p = p;
    let ghost a = p.ptr();
    p.is_nonnull();
    p.provenance_not_none();
    p.ptr_bounds();
    let ghost zp: *mut () = ptr_mut_from_data::<()>(
        PtrData { addr: a@.addr, provenance: a@.provenance, metadata: () },
    );
    assert(ptr_addr_in_bounds(zp));
    let tracked mut z = PointsToUntyped::zero_sized(zp);
    {
        let tracked u = p.as_untyped_mut();
        // Take the original 8 bytes out, leaving a zero-length permission in the borrow.
        vstd::modes::tracked_swap(u, &mut z);
    }
    // z: the original 8 bytes at a. p: a PointsTo<u64> at a with no bytes (not wf).
    assert(z.ptr()@.addr == a@.addr);
    assert(p.ptr()@.addr == a@.addr);
    z.is_disjoint(&p);
}

} // verus!
```

## Fix direction

The fix is to require `other` to be pointer-level well-formed (`other.wf_basic()`),
which ties `other.size()` to the bytes it holds.

**The obvious version doesn't work.**
Bounding `OtherPointsToPerm: PointsToProperties` (so `other.wf_basic()` can be named)
makes `PointsToProperties` refer to itself in its own method signature,
which Verus rejects as a cycle.
That cycle is why `PointsToPhys` and `PointsToProperties` are separate traits in the first place.

**Suggested approach: move `wf_basic` into `PointsToPhys`, if Verus allows it.**
Then `is_disjoint` can keep the bound `OtherPointsToPerm: PointsToPhys` and require `other.wf_basic()`.
Things to check first, ideally in a small standalone spike:

- That declaring `wf_basic` in `PointsToPhys` and using it in `PointsToProperties`' contracts
  (including on a generic `OtherPointsToPerm: PointsToPhys`) doesn't hit the same cyclicity error.
- That the existing `wf_basic` bodies still type-check from a `PointsToPhys` impl.
  They call inherent specs on fields (e.g. `pt_untyped().wf()`, `pt_unaligned().wf()`);
  a `PointsToPhys` impl must not end up calling a `PointsToProperties` (subtrait) impl,
  which Verus also rejects as recursion.
- That broadcast groups (`group_points_to_permissions_lemmas`, `group_vstd_default`)
  don't pick up new cyclicity errors.

**The specialized versions should get the same requirement** (`other.wf()`, or `other.wf_basic()`),
for the same reason:

| Function | Location |
|---|---|
| `PointsToUntyped::is_disjoint_untyped` | `points_to_permissions.rs:261` |
| `PointsToUnaligned::is_disjoint_unaligned` | `points_to_permissions.rs:891` |
| `PointsTo::is_disjoint_pointsto` | `points_to_permissions.rs:1361` |
| `SeqPointsTo::is_disjoint_seqpt` | `points_to_permissions.rs:3457` |
| `PointsToSingleton::is_disjoint_singleton` | `points_to.rs:195` |

`is_disjoint_singleton` doesn't strictly need it (a byte permission's `wf_basic` is always `true`),
but update it the same way for consistency,
and rename it to `is_disjoint_byte` to match the planned `PointsToSingleton` → `PointsToByte` rename.

## Remaining hole: `PointsToPhys` can be implemented outside vstd

The base axiom trusts every `PointsToPhys` impl's `wf_basic` to tie `size()` to memory it really owns.
That holds for vstd's impls,
but the trait is public and unsealed,
so user code can write an impl with no memory behind it:

```rust
struct Fake { p: Ghost<*mut u8> }
impl PointsToPhys for Fake {
    type A = u8;
    spec fn ptr(self) -> *mut u8 { self.p@ }
    spec fn size(self) -> nat { 1 }
    spec fn wf_basic(self) -> bool { true }
}
// byte.is_disjoint(&Fake { p: Ghost(byte.ptr()) }) proves false.
```

This was already possible before the fix, since `other` had no requirements at all.
A fix is to seal `PointsToPhys`
(e.g. a `pub(crate)` supertrait, or Verus's `#[verifier::sealed]` if it supports trait sealing here),
so only vstd can implement it.
Only `PointsToPhys` needs sealing:
its items are all specs, with no proof obligations,
while impls of the subtraits have to prove their lemmas.

Effect on rustlib's `str` permissions: none, with a crate-private seal.
In rustlib, vstd is compiled as a module of `core`,
so `core`'s `str` impls are in the same crate as the seal and can still implement `PointsToPhys`,
while crates outside `core` (or outside a standalone vstd) can't.
(If the impl ever had to move into vstd, the planned design would also allow it:
`PointsToPhys` for `str` is just `ptr`, `size(len) = len` and the generic pointer-level `wf_basic`,
none of which mention the `str` view.)

## Coordination with the points-to overhaul

A separate effort is redesigning these traits;
see `TYPED_POINTS_TO_PLAN.md`, `TYPED_POINTS_TO_APPROVED.md` and `TYPED_POINTS_TO_IMPL_PLAN.md` in this directory.

- **The approved trait design has the same bug.**
  `PointsToProperties::is_disjoint` in `TYPED_POINTS_TO_APPROVED.md` has the same unconstrained `other`,
  and the planned `as_untyped_mut` also only re-establishes `wf` conditionally.
  Any fix here needs a matching change to that approved trait.
  That document needs the user's re-approval for every change, so propose the change rather than editing it.
- **Moving `wf_basic` into `PointsToPhys` changes the approved trait split.**
  In the planned design, `PointsToProperties` holds `wf_basic` and the pointer-level lemmas,
  `PointsToSingleValue::wf` builds on `wf_basic`,
  and `PointsToPhys::size` takes the pointer metadata instead of `self`.
  The fix should be designed against both the current code and that planned shape.
- **The `PointsToByte` rename is phase 1 of the overhaul.**
  Rename `is_disjoint_singleton` together with it, or leave a note if this fix lands first.

Already done in the overhaul session (not part of this bug):
the `ptr_ref` family (`ptr_ref`, `ptr_mut_ref`, `ptr_ref2`, `ptr_ref2_ghost`) now requires `perm.wf()`,
and `ptr_mut_ref` also ensures `final(perm).wf()`.

## Verifying a fix

- The reproduction above should fail (`postcondition not satisfied`).
- `source/tools/build-expand-errors.sh` (vstd) and `source/tools/build-rustlib-core.sh` (rustlib's core configuration)
  should both pass with 0 errors. rustlib calls these functions, so callers there may need `wf` facts added.
