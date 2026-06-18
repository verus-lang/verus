# Calling a logically atomic function

To call a logically atomic function, we use the following syntax:

```rs
let py = function(px) atomically loop |update| -> (au)
    invariant ...,
{
    // ...
    // assert atomic pre
    let ay = update(ax);
    // assume atomic post
    // ...
    break/continue
}
```

The atomic function call binds an `update` function, which represents the effects of the `try_open_atomic_update` macro to the client.
It is helpful to think of the macro as defining the `update` function, as their inputs and outputs, as well as their pre- and postcondition match precisely.
While the user is free call this function whatever they like, we will always call this function `update` throughout this guide for consistency.
The `update` function is `proof`-mode, allowing atomic invariants to be opened around it.
The body of the `atomically` block also is `proof`-mode.

The arrow syntax `-> (au: AtomicUpdate<...>)` with optional type hint, gives users `spec`-mode access to the atomic update as it is being created.
This is particularly useful for proof debugging, as it can be used to assert the atomic pre- or postcondition manually in different parts of the `atomically` block.
It also gives users a place to specify the input and output types of the atomic update in cases where type inference fails.

## Handling the abort case

Since the library function may open the atomic update multiple times, due to aborting, the client must prove that it can provide the required resources as many times as necessary, meaning the atomic function call must be a loop.
This loop supports all the common loop header clauses:
`invariant_except_breaks`, `invariants`, and `ensures`.

If the atomic update is committed by the library, as indicated by the `UpdateTry` implementation on the output type, the client must `break` out of the loop.
Similarly, if the library aborts the atomic update, the loop must `continue`, either explicitly or implicitly.
Verus checks that these control flow constructs are used correctly using additional verification conditions, i.e. `break` and `continue` get a precondition that `ax.branch()` is equal to `Commit` or `Abort` respectively.

In cases where this aborting mechanism is not necessary (e.g. if the output type of the atomic update is `Commit<T>`), **the `loop` keyword can be removed** to disable this feature.
This is equivalent to adding a `break` to the end of the `atomically` block, except it provides slightly better proof automation and eliminates the need for loop invariants in straight line code.

## Invariant masks

The outer mask of the atomic update restricts what invariants can be opened inside the `atomically` block, so an invariant can only be opened if its namespace is in the outer mask.
The inner mask specifies the invariant mask of the `update` function, meaning it restricts which invariants can be opened around the `update` itself.

The most general atomic update has `outer_mask any` and `inner_mask none`, allowing the client to open any invariant inside the atomic function call.
Inversely, if the inner mask is not a subset of the outer mask, the function cannot be called.

## Running examples

This is how we can call our two example functions *synchronously*, meaning we have full ownership of the permission object:

```rs
{{#include ../../../../examples/guide/logatom.rs:reset_client_sync}}
```

```rs
{{#include ../../../../examples/guide/logatom.rs:increment_client_sync}}
```

Here are two simple *asynchronous* clients for our example functions, where we call the functions using an atomic invariant, allowing multiple threads to use these functions concurrently.
The invariant we use in this example makes no statement about the value of the atomic, we simply assert that `perm.is_for(var)`.

```rs
{{#include ../../../../examples/guide/logatom.rs:reset_client_async}}
```

```rs
{{#include ../../../../examples/guide/logatom.rs:increment_client_async}}
```

The last example shows the need for the invariant credits in the signature of the `increment` function.
Since the body of the atomic function call is `proof`-mode, we must spend an invariant credit to open the atomic invariant in both of our asynchronous example clients.
To call our `reset` function, we only need to open the invariant once, so we just need one credit.
For the `increment` function, we want to open an invariant in an unbounded loop, so we need a steady supply of credits that we can spend on the invariant.

We solve this by passing an invariant credit from the library to the client every time the atomic update is aborted.
The client then acquires one initial credit before the atomic function call, which is then spent on the invariant, and restored in case the atomic update is aborted, which can then be spent in the next loop iteration.

Note that we need two `match` expressions here, because `break` and `continue` are not allowed to appear inside the `open_atomic_invariant` macro.
The first `match` closes the invariant, and the second `match` handles the control flow of the atomic function call.
Nevertheless, Verus is smart enough to realize that the `break` is executed if and only if the result of the `update` functions signals that the atomic update has been aborted.
