Our aim is to implement an important step in the work-in-progress "native raw pointers" feature.

Specifically: In `rustc_mir_build/` and `rustc_mir_build_additional_files/` is a fork of rustc's `rustc_mir_build` crate which contains the MIR-generation code. We want to modify this so that all place expressions containing _raw pointer dereferences_ are annotated with relevant permissions.

We want to handle arbitrarily nested place expressions, which may contain fields, multiple raw pointer dereferences, and array/slice index expressions. The relevant code to modify is `rustc_mir_build/src/builder/expr/as_place.rs`. See the `mir-place-notes.md` for your previous review of this file.

# Implementation guidelines

(This is not a hard requirement, but to the extent possible: keep changes in `rustc_mir_build/` to a minimum; add new code in `rustc_mir_build_additional_files`, then call into that code from `rustc_mir_build`.)

# Plan

Given a MIR-level `Place` like `(*(*(*a).x).y).z` there may be multiple raw-pointer derefs of interest. (For this example, we'll take each `*` to be a raw-pointer-dereference rather than a safe deref like a box or reference.) To ensure the safety of the pointer operation, we need to emit some permission-related code. How we use the permission (e.g., mutable or read-only) depends on the context. For the _outermost_ raw pointer, this will depend on how the place is used (move, copy, assign, borrow?) but for the _inner_ raw pointers, we will always be reading.

Let's say we have `Perm_A` for `a`, `Perm_B` for `(*a).x`, and `Perm_C` for (*(*a).x).y.

## Move from a place

Rust doesn't allowing moving from behind a raw pointer. Don't do anything for this case,
just let Rust error about it.

## Copy from a place

A copy should read from every permission.

```
a = &Perm_A
b = &Perm_B
c = &Perm_C
m = copy (*(*(*a).x).y).z;
```

(The `a`, `b`, and `c` are unused and just there to allow the borrow to exist momentarily.)

## Assign to a place

An assign should require the outermost permission to be mutable:

```
a = &Perm_A
b = &Perm_B
c = &mut Perm_C
(*(*(*a).x).y).z = ...;
```

## Mutable borrow of a place

An mutable borrow should require the outermost permission to be mutable, and should tie the lifetime
of the permission's mutable borrow to the target borrow:

```
a = &Perm_A
b = &Perm_B
r = mutable_reference_tie(&mut (*(*(*a).x).y).z, mutable_reference_tie(&mut Perm_C, &mut Shadow_Perm_C))
```

Here `mutable_reference_tie` is defined in `builtin/src/lib.rs`:

```
pub fn mutable_reference_tie<'a, T: ?Sized, U: ?Sized>(_a: &'a mut T, _b: &'a mut U) -> &'a mut T;
```

The `Shadow_Perm_C` is the "shadow place" of `Perm_C`. See the documentation in 
`rustc_mir_build_additional_files/verus_time_travel_prevention.rs` for an explanation of what this is.

(Two-phase borrows are nasty; we don't want to deal with them here. For now, just have
Verus error if there is any two-phase borrow from a place with a raw-pointer derereference.)

## Shared borrow of a place

A shared borrow should require the outermost permission to be shared, and should tie the lifetime
of the permission's mutable borrow to the target borrow:

```
a = &Perm_A
b = &Perm_B
r = shared_reference_tie(&mut (*(*(*a).x).y).z, &mut Perm_C)
```

The `shared_reference_tie` needs to be defined, similarly to the existing `mutable_reference_tie`.

```
pub fn shared_reference_tie<'a, T: ?Sized, U: ?Sized>(_a: &'a T, _b: &'a U) -> &'a T;
```

There's no need to deal with shadow vars here.

## Raw borrow of a place

For a raw borrow, the outermost permissions should not be mentioned at all.

```
a = &Perm_A
b = &Perm_B
r = &raw (*(*(*a).x).y).z
```

Verus doesn't support raw borrows right now, so raw borrows are only relevant to code generated
by the MIR builder; see below.

# Working with THIR-level places

A place expression in THIR may be lowered to multiple MIR places. Take the example from
mir-place-notes.md. The place expression `*(*(*a)[{ let y = 13; 0 }])[11]`
is lowered to multiple operations with place expressions.

First for the bounds-check:

```
_9 = &raw const (fake) (*(*_1)[_5]);
```

and later:

```
_4 = copy (*(*(*_1)[_5])[_8]);
```

Both of these statements need to be annotated in the method above. 
(The bounds-check statements won't need anything other than read permissions.)

# Mapping raw pointers to permissions

The mapping of raw pointer dereferences needs to be mapped from the VIR to the mir builder code.

In VIR, each `DerefRaw` node has a Place argument (the second one) which indicates the permission.  Only a limited form of places can appear here (see `get_permission_place` in `rust_to_vir_expr.rs` which computes these). This includes mutable borrow dereferences, fields (and implicit dereferences; see the documentation on `Place`).
This place argument is optional; if it's None, just skip emitting any permission for that particular pointer.

Information can flow from `modes.rs` to the MIR building code as follows:

 * Put a map in `ErasureModes` mapping the `DerefRaw` node to the relevant permission `Place`
 * In `erase.rs`, repackage the information through the HirId mappings into the `VerusErasureCtxt`
 * In `rustc_mir_build_additional_files/verus.rs` (the THIR generation code) we can save additional information in the `extra_thir` which is then available in the MIR building code.

(Note that due to the forking structure, it's not possible to modify the THIR data structure directly.)

## Testing

Some basic tests are in native-ptrs.rs. Many of these functions pass when they should fail because of a Rust borrow-checking error. Some of them fail because of an SMT error when they should instead fail because of a Rust borrow-checking error.

Please package these up into real test cases in `rust_verify_test/tests/native_ptrs.rs`. Add test cases for as many nasty corner cases as you can think of:

 * Do complex stuff with index expressions with side effects, the evaluation order of bounds-checks, differences between slices and arrays
 * Have side effects that modify the permission variable itself.
