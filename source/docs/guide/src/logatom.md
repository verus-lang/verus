# Logical atomicity

In short, logical atomicity is a proof technique that allows us to treat an `exec`-mode function as if it executes in a single atomic step, even if internally, it performs multiple atomic operations.
This enables us to call such a function using an atomic invariant.

> [!NOTE]
> **This feature is experimental.** While all functionality presented in this chapter is implemented and tested in the latest release, we are still actively developing this feature further, and things may change slightly in the future.

## Running examples

To make the ideas in this section a bit more concrete, we will consider two simple logically atomic example functions: `reset` and `increment`.
The former sets a `PAtomicU64` to zero, the latter increases its value by one using a compare-and-swap loop.
These two function can be implemented in Rust as follows:

```rs
use std::sync::atomic::{AtomicU64, Ordering::SeqCst};

fn reset(var: &AtomicU64) {
    var.store(0, SeqCst);
}

fn increment(var: &AtomicU64) -> u64 {
    let mut curr = var.load(SeqCst);
    loop {
        match var.compare_exchange_weak(curr, curr + 1, SeqCst, SeqCst) {
            Ok(_) => return curr,
            Err(new) => curr = new,
        }
    }
}
```

The latter example is particularly interesting, as the `increment` function internally performs multiple atomic operations, and even repeats one of them in an unbounded loop, yet from the outside, the function is observationally equivalent to a single atomic operation.

The `reset` function on the other hand is actually physically atomic, since it only contains a single `exec`-mode operation (`store`), which it itself physically atomic.
This means, instead of proving logical atomicity, we could annotate the function with [`#[verifier::atomic]`](reference-attributes.html#verifieratomic) to make Verus treat it as physically atomic.

## Main concepts

The two functions above are logically atomic, because they have a **linearization point (LP)**, that is, a single atomic step which updates the state of the program.
In the `increment` function, for example, the LP occurs when the `compare_exchange_weak` operations runs successfully.
Identifying the LP in a function is the first important step in proving it is logically atomic.

We can then specify the behavior of such a function using an *atomic* pre- and postcondition.
These describe the state of the program immediately before and after the LP, and they live alongside the "regular" function pre- and postconditions.
Together, they describe the state of the program at four distinct points in time:
- **function pre** at the start of the function,
- **atomic pre** just *before* the LP,
- **atomic post** just *after* the LP, and
- **function post** at the end of the function.

Following the Iris implementation of logical atomicity, we abstract the LP using a tracked ghost object called the **atomic update (AU)**.
The atomic specification declares what the atomic update looks like for a particular function.
This object is constructed by the client/caller, and it is destructed (or "opened") by the library/callee.

### The abort case

In some cases, it is not enough to open the AU just once at the LP, we also need a mechanism to "peek into" the AU without consuming it.
In our `increment` function, for example, we need some way to reason about the initial load and the failed compare exchange operations.
To do so, we need some way to gain temporary read-only access to the resources in the AU, but opening it would consume the AU, making it impossible to open it again at the LP.

To get around this, our atomic update has an abort case, meaning when we open the atomic update, we have the choice to either "commit" it and prove the atomic postcondition at the LP, or to "abort" it, in which case we re-establish the atomic precondition and get back the AU, allowing us to open it again later.
We will see how this works in detail throughout the rest of this chapter.

### Notes on helping

One important concept in the design and implementation of lock-free and wait-free algorithms is "helping", i.e. where one process starts a task, gets interrupted by another process, and the interrupting process "helps" to finish the incomplete task.
This kind of interaction can be difficult to reason about, because it allows the linearization point of one function to be invoked on a *different concurrent process* entirely.

Our implementation of logical atomicity yields a powerful proof technique for these cases.
In particular, we can "send" an atomic update to a different process by placing it into an [`AtomicInvariant`](https://verus-lang.github.io/verus/verusdoc/vstd/invariant/struct.AtomicInvariant.html) on one thread, and taking it back out on another.
We can use the same invariant to communicate back to the first thread that the atomic update has been committed successfully.

For a simple example that demonstrates the concept of helping, `examples/helping.rs` implements a simple boolean flag with a logically atomic `flip` method.
When two concurrent processes call `flip` at the same time, we perform a handshake that *logically* flips the boolean twice, while leaving the underlying physical boolean unchanged.

## Previous & related work

Formalizations of logical atomicity come in two flavors, which are commonly referred to as "HOCAP-style" and "TaDA-style" logical atomicity.

HOCAP-style logical atomicity was first introduced by VeriFast ([Jacobs & Piessens POPL'11](https://dl.acm.org/doi/abs/10.1145/1926385.1926417)) and later refined by HOCAP ([Svendsen et al. ESOP'13](https://link.springer.com/chapter/10.1007/978-3-642-37036-6_11)).
Here, a logically atomic function takes a "ghost callback" which is invoked at the linearization point to temporarily acquire the caller's permission and update the relevant ghost state.
This approach has been applied in Verus to verify CapybaraKV ([LeBlanc et al. OSDI'25](https://www.usenix.org/conference/osdi25/presentation/leblanc)), and the traits they used can be found in the [`vstd::logatom`](https://verus-lang.github.io/verus/verusdoc/vstd/logatom/index.html) module.

While this approach has the advantage of being fully verified in Verus, it comes with significant downsides to ergonomics and flexibility.
In particular, this encoding of logical atomicity is inherently higher-order and cumbersome to reason about.
It requires a significant amount of boilerplate code, both for the library/callee but also for the client/caller, to define the auxilary types and trait implementations requires for this encoding.
All this buries the function specification in layers of abstraction.
Finally, this approach only allows ghost state to be updated at the LP, making this approach too weak to verify either of our two running examples without awkward workarounds.

TaDA-style logical atomicity is named after the TaDA logic ([da Rocha Pinto et al. ECOOP'14](https://link.springer.com/chapter/10.1007/978-3-662-44202-9_9)) which introduced atomic triples as a primitive part of its logic.
Building on these ideas, Iris ([Jung et al. POPL'15](https://dl.acm.org/doi/abs/10.1145/2775051.2676980)) then presented a similar notion of atomic specifications, which can be fully encoded in its separation logic.
Our implementation of logical atomicity in Verus is based on the atomic specification as they have been verified in Iris.

<!--
This extension to Verus is the master thesis project of Aaron Bies at Saarland University, submitted there in collaboration with MPI-SWS.
-->
