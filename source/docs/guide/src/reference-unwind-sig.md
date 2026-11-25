# Panic and unwinding signature

For any `exec`-mode function, it is possible to specify whether that function may
[panic](https://doc.rust-lang.org/std/macro.panic.html), and whether it may
[unwind](https://doc.rust-lang.org/nomicon/unwinding.html).
A panic either unwinds or aborts the program, so unwinding implies a panic, but not vice versa:
a function that never unwinds might still panic by aborting.

The allowed forms of the signature are:

 * No signature (default) - The function may panic (and may unwind).
 * `no_panic` - The function never panics (and hence never unwinds).
 * `requires[no_panic] {conditions}` - _If_ the conditions hold, then the function will not panic.
   The conditions are checked at call sites by default (see below).
 * `requires[no_panic exact] {conditions}` - The function will not panic if the conditions hold,
   and it _will_ panic if they do not.
 * `no_unwind` - The function never unwinds, but it may still panic by aborting.
 * `no_unwind when {condition}` (deprecated) - _If_ the condition holds, then the function will not unwind.
   Use `requires[no_panic]`, `requires[no_panic exact]`, or `ensures[on unwind]` instead.

In addition, a function may specify what holds if it panics or unwinds:

 * `ensures[on panic] {conditions}` - If the function panics (whether it unwinds or aborts),
   then the conditions hold.
 * `ensures[on unwind] {conditions}` - If the function unwinds, then the conditions hold.

By default, a function is allowed to panic. (Note, though, that Verus _does_
rule out common sources of panics, such as integer overflow, even when the function
signature technically allows panicking.)

All of these conditions may only refer to the function's arguments (in their state at the call).

## `no_panic`

A `no_panic` function may only call functions that cannot panic
(at least under the conditions where the call happens).
Note that calling a `no_unwind` function is not enough, since it might still panic by aborting.

## `requires[no_panic]`

A function can give the condition under which it will not panic as a `requires`-like clause:

```rust
fn unwrap<T>(o: Option<T>) -> T
    requires[no_panic]
        o.is_some(),
```

This means that the function will not panic if `o.is_some()`.
By default, the condition is checked at every call site, as if it were a precondition,
even if the caller is itself allowed to panic.

To skip this check, use `#[verifier::deny_panic(false)]`. This attribute can be placed
on a call expression, or on a function, impl, module, or crate, in which case it applies to all
calls inside it. When `deny_panic` is false for a call, the condition is only checked
to the extent needed to show that the caller meets its own panic signature.

The form `requires[no_panic exact]` additionally specifies that the function
_will_ panic if the condition does not hold.
Equivalently, if the function returns normally, then the condition holds.
Verus checks this in the body of the function (the condition must hold at every normal return),
and callers may assume the condition after the call returns:

```rust
fn unwrap<T>(o: Option<T>) -> T
    requires[no_panic exact]
        o.is_some(),

#[verifier::deny_panic(false)]
fn test(o: Option<u8>) {
    let x = unwrap(o);
    assert(o.is_some());
}
```

`no_panic` is equivalent to `requires[no_panic] true`.

A function may use at most one of `no_panic`, `requires[no_panic]`, `requires[no_panic exact]`,
`no_unwind`, and `no_unwind when`.
`requires[no_panic ...]` can be combined with an ordinary `requires` clause.

## `ensures[on panic]` and `ensures[on unwind]`

A function can specify conditions that hold if it panics or unwinds:

```rust
fn f(i: u8)
    ensures[on panic]
        i >= 10,
```

This means that if the function panics, then `i >= 10`; equivalently, if `i < 10`,
then the function will not panic.
Unlike `requires[no_panic]`, these conditions are never checked at call sites;
instead, callers may assume them if the call panics or unwinds.

`ensures[on panic]` implies the corresponding `ensures[on unwind]`, since unwinding implies panicking.
`ensures[on unwind]` is weaker: it says nothing about a panic that aborts.

Verus checks these conditions at every point where the function might panic or unwind,
along with the negation of the function's `requires[no_panic]` condition (if any).
They can be combined with `ensures` and with any of the specifications above.

## Restrictions with invariants

You cannot unwind when an [invariant](https://verus-lang.github.io/verus/verusdoc/vstd/macro.open_local_invariant.html) is open.
This restriction is necessary because an unwinding operation does not necessarily abort a program.
Rust allows a program to ["catch" an unwind](https://doc.rust-lang.org/std/panic/fn.catch_unwind.html), for example, or there might be other threads to continue execution.
As a result, Verus cannot permit the program to exit an invariant-block early without restoring
the invariant, not even for unwinding.
(Panicking by aborting is allowed, since the program does not continue.)

This restriction is what enables Verus to rule out [exception safety violations](https://doc.rust-lang.org/nomicon/exception-safety.html).

## Drops

If you implement `Drop` for a type, you are required to give it a signature of `no_unwind` or `no_panic`.
