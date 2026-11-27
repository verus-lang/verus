## Panic specifications

In the previous section, we saw a piece of code that intentionally panics:

```rust
#[check_user_panics(false)]
fn checked_double(x: u8) -> (res: u8)
    ensures res == 2 * x,
{
    if x >= 128 {
        panic!("checked_double: overflow");
    }
    x * 2
}
```

That's great and all, but it leaves clients in the lurch.
The `checked_double` function contains the `panic!` as a purely internal details. Nothing in
its specification says anything about panicking, so a client would have to conservatively assume
it can just panic for any reason whatosever.
In this section, we'll see how to write specifications that describe the panicking behaviors.

In all our examples, we'll keep the `#[check_user_panics(false)]`.
Thus, all panic-related errors will result from our explicit specifications.

We can declare that a function won't panic using the `no_panic`. Let's try it out, by writing
a client of `checked_double`:

```rust
#![check_user_panics(false)] // apply to the whole module
use vstd::prelude::*;

verus!{

fn checked_double(x: u8) -> (res: u8)
    ensures res == 2 * x,
{
    if x >= 128 {
        panic!("checked_double: overflow");
    }
    x * 2
}

fn client()
    no_panic
{
    checked_double(20);
}
```

This doesn't work:

```rust
error: possible panic
  --> panic_example.rs:29:5
   |
   |     checked_double(20);
   |     ^^^^^^^^^^^^^^^^^^ call to `panic_example::checked_double` might panic
```

The error says `checked_double` might panic, and indeed, it might! The signature of
`checked_double` still says nothing about its own panicking behavior.

To fix this, we can write a _postcondition_ for `checked_double` that applies only on the
_abnormal exit path_ of a panic.

```rust
fn checked_double(x: u8) -> (res: u8)
    ensures res == 2 * x,
    ensures[panic] x >= 128
{
    if x >= 128 {
        panic!("checked_double: overflow"); // checks the panic-postcondition: `x >= 128`
    }
    return x * 2; // checks the normal postcondition: `x >= 128`
}
```

With this signature for `checked_double`, our `client()` function will now pass:

```rust
fn client()
    no_panic
{
    checked_double(20); // If this function panics, then the panic postcondition holds:
                        // `20 >= 128`. This is a contradiction, showing the panic path is impossible.
}
```

### Panicking conditions as preconditions

It's also possible to write the panicking condition in "precondition-style".

```rust
fn checked_double(x: u8) -> (res: u8)
    requires[no_panic] x < 128
    ensures res == 2 * x,
{
    if x >= 128 {
        panic!("checked_double: overflow"); // checks the panic-postcondition: `x >= 128`
    }
    return x * 2; // checks the normal postcondition: `x >= 128`
}
```

This can be more intuitive, since users of the function often want to know what precondition
they need to establish in order to correctly call the function. Don't get it confused with a
"normal" precondition, though. Verus still has to check the panicking paths for memory safety.
This would still be an error:

```rust
fn my_unwrap(x: Option<u8>)
    requires[no_panic] x.is_some()
{
    let y = unsafe { x.unwrap_unchecked() }; // this is UB if x == None
}
```

That is, having a `requires[no_panic]` is not the same as an assertion that the condition
only holds true. Rather, it just means that any path through the function that panics cannot
hold true under that hypothesis.
Formally speaking, `requires[no_panic] e` is just equivalent to `ensures[panic] !e`;
the use of `requires[no_panic]` is primarily a matter of framing.

Which style should you use?
Depending on the situation, one or the other might be more natural.
Generally speaking, `requires[no_panic]` is more suitable for conditions that you expect a client
to be able to uphold, while `ensures[panic]` is suitable for unexpected conditions that may not
be easy to predict in advance (like OOM).

Furthermore, the `requires[no_panic]` registers the condition as a "user panic", causing it to
be checked if `check_user_panics` is enabled.

### Even more precise specs

The `requires[no_panic]` has an even stronger form, `requires[no_panic exact]`, which means
that if the condition _doesn't_ hold, then the function _will_ panic (modulo nontermination).

```rust
fn checked_double(x: u8) -> (res: u8)
    requires[no_panic exact] x < 128
    ensures res == 2 * x,
```

This implies that if `checked_double` exits normally, then the `x < 128` condition does hold.
This may be useful if the fact wasn't known _a priori_.

```rust
fn client2(x: u8) {
    // Not sure if this is going to panic ...
    let d = double2(x);

    // But if program reaches this point, then I know it didn't panic, and therefore:
    assert(x < 128);
}
```

(In our example, the `no_panic exact` condition is technically redundant, because the postcondition `res == 2*x` where `res: u8` happens to imply that `x < 128` already.)

## Specifying recovable panics

When a panic occurs in Rust, the runtime first executes the "panic handler" and then either
_aborts_ or _unwinds_. In the latter case, execution resumes by walking up the stack, invoking
destructors within each stack frame. It is possible for an unwinding to be "caught", with the
program resuming normal execution.

To reason about this specific scenario, Verus also provides `ensures[unwind]`, which applies
to the subset of panics that take the unwinding path. 

## Summary

| Signature header          | Meaning                                                     | Considered "user panic"? |
|---------------------------|-------------------------------------------------------------|--------------------------|
| `ensures e`               | Condition must hold on any normal exit                      | 
| `ensures[panic] e`        | Condition must hold on any panicking exit (unwind or abort) | 
| `ensures[unwind] e`       | Condition must hold on any unwinding panicking exit         |                          |
| `no_panic`                | `ensures[panic] false`                                      |                          |
| `no_unwind`               | `ensures[unwind] false`                                     |                          |
| `requires[panic] e`       | `ensures[panic] !e`                                         | ✓                        |
| `requires[panic exact] e` | `ensures e`, `ensures[panic] !e`                            | ✓                        |

> [!NOTE]
> Since unwinding panics are recoverable, it is possible that a function executes a panic handler,
> recovers from a panic, and returns. For the purposes of these specifications, this still counts
> as a normal exit, not a panicking exit.
> In other words, it is still possible for a `no_panic` function
> to execute the panic handler, which may have observable side effects
> (like printing a backtrace to stderr).
