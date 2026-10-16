We need to fix the `lifetimes_behind_pointer_mismatch_*` tests in `rust_verify_test/tests/native_ptrs_borrow_checking.rs`

The issue with our current scheme is that the type `T` in `PointsTo<T>` doesn't get tied to the type of the value being borrowed, assigned to, or read from.

### Fixing borrows

For example, we have:

```
r = shared_reference_tie(&(*(*(*a).x).y).z, &Perm_C);
```

but the type of `shared_reference_tie` is `(_a: &'a T, _b: &'a U) -> &'a T` so the type of the right-hand side gets ignored completely.
Same issue for `mutable_reference_tie`. And in the assignments / reads, the permission is completely disconnected from the actual operation.

We can switch the arguments, though we also need to turn `&Perm_C` (with type `&PointsTo<T>`) into `&T`. Thus we need to extend our projections to go from `&PointsTo<T> -> T`, `&mut PointsTo<T> -> &mut T`, etc. This can be done with `vstd::raw_ptr::borrow` and `vstd::raw_ptr::borrow_mut`.

### Fixing assignment

Instead of,

```rust
_ = &Perm_A; _ = &Perm_B; _ = &mut Perm_C;
(*(*(*a).x).y).z = ...;
```

We should emit something like

```rust
_ = &Perm_A; _ = &Perm_B; _ = &mut Perm_C;
(*(*(*a).x).y).z = v;
tie_ptr_write(&mut Perm_C, &mut (*(*(*a).x).y).z, v);
```

where the type signature is:

```
tie_ptr_write<T, U> (&mut T, &mut U, T)
```

### Fixing copy

Instead of,

```rust
_ = &Perm_A; _ = &Perm_B; _ = &mut Perm_C;
x = copy (*(*(*a).x).y).z;
```

We should emit something like

```rust
_ = &Perm_A; _ = &Perm_B; _ = &mut Perm_C;
(*(*(*a).x).y).z = v;
x = copy *tie_ptr_read(&Perm_C, &(*(*(*a).x).y).z);
```

where the type signature is:

```
tie_ptr_read<T, U> (&T, &U) -> &T
```
