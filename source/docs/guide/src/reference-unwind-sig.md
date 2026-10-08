# Unwinding signature

For any `exec`-mode function, it is possible to specify whether that function may [unwind](https://doc.rust-lang.org/nomicon/unwinding.html). The allowed forms of the signature are:

 * No signature (default) - This means the function may unwind.
 * `no_unwind` - This means the function may not unwind.
 * `no_unwind when {boolean expression in the input arguments}` - _If_ the given condition holds, then the call is guaranteed to not unwind.
    * `no_unwind when true` is equivalent to `no_unwind`
    * `no_unwind when false` is equivalent to the default behavior

By default, a function is allowed to unwind. (Note, though, that Verus _does_
rule out common sources of unwinding, such as integer overflow, even when the function
signature technically allows unwinding.)

## Example

Suppose you want to write a function which takes an index, and that you want to specify:

 * The function will execute normally if the index is in-bounds
 * The function will unwind otherwise

You might write it like this:

```rust
fn get(&self, i: usize) -> (res: T)
    ensures i < self.len() && res == self[i]
    no_unwind when i < self.len()
```

This effectively says:

 * If `i < self.len()`, then the function will not unwind.
 * If the function returns normally, then `i < self.len()` (equivalently, if `i >= self.len()`, then the function must unwind).

## `requires[no_unwind]`

A function can also give its no-unwind condition as a `requires`-like clause:

```rust
fn unwrap<T>(o: Option<T>) -> T
    requires[no_unwind]
        o.is_some(),
```

Like `no_unwind when o.is_some()`, this means that the function will not unwind
if the condition holds. The difference is that the condition is checked at every call site
by default, as if it were a precondition, even if the caller is itself allowed to unwind.

To skip this check, use `#[verifier::restrict_unwind(false)]`. This attribute can be placed
on a call expression, or on a function, impl, module, or crate, in which case it applies to all
calls inside it. When `restrict_unwind` is false for a call, the condition is only checked
to the extent needed to show that the caller meets its own unwinding signature
(as with `no_unwind when`).

The form `requires[no_unwind exact]` additionally specifies that the function
_will_ unwind if the condition does not hold.
Equivalently, if the function returns normally, then the condition holds.
Verus checks this in the body of the function (the condition must hold at every normal return),
and callers may assume the condition after the call returns:

```rust
fn unwrap<T>(o: Option<T>) -> T
    requires[no_unwind exact]
        o.is_some(),

#[verifier::restrict_unwind(false)]
fn test(o: Option<u8>) {
    let x = unwrap(o);
    assert(o.is_some());
}
```

A function may use either `requires[no_unwind]`, `requires[no_unwind exact]`,
or `no_unwind`/`no_unwind when`, but not more than one of these.
`requires[no_unwind ...]` can be combined with an ordinary `requires` clause.

## Restrictions with invariants

You cannot unwind when an [invariant](https://verus-lang.github.io/verus/verusdoc/vstd/macro.open_local_invariant.html) is open.
This restriction is necessary because an unwinding operation does not necessarily abort a program.
Rust allows a program to ["catch" an unwind](https://doc.rust-lang.org/std/panic/fn.catch_unwind.html), for example, or there might be other threads to continue execution.
As a result, Verus cannot permit the program to exit an invariant-block early without restoring
the invariant, not even for unwinding.

This is restriction is what enables Verus to rule out [exception safety violations](https://doc.rust-lang.org/nomicon/exception-safety.html).

## Drops

If you implement `Drop` for a type, you are required to give it a signature of `no_unwind`.
