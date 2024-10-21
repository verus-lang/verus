# Intro

_**Note:** this guide is a work-in-progress._

### What's this guide about?

It's hard to say exactly what this guide is about.
It's easiest to say that it is primarily about
verifying **multi-threaded concurrent code** in [Verus](https://github.com/verus-lang/verus),
and in fact, we developed most of this framework with that goal in mind,
but these techniques are actually useful for single-threaded code, too.
We might also say that it's about verifying **code that needs unsafe features**
(especially raw pointers and unsafe cells), though again, there are plenty of use-cases
where this does not apply.

The unifying theme for the above are programs that require some kind of **nontrivial
ownership discipline**, where different objects that might be "owned independently"
need to coordinate somehow.
For example:

 * Locks need to manage ownership of some underlying resource between multiple clients.
 * Reference-counted smart pointers need to coordinate to agree on a reference-count.
 * Concurrent data structures (queues, hash tables, and so on) require their
    client threads to coordinate their access to the data structure.

This kind of nontrivial ownership can be implemented through Verus's
`tokenized_state_machine!` utility, and this utility will be the main
tool we'll learn how to use in this guide.

### Who's this guide for?

Read this if you're interested in learning how to:

 1. Verify multi-threaded concurrent code in Verus.
 2. Verify code that requires "unsafe" code in unverified Rust
    (e.g., code with raw pointers or unsafe cells)

Or if you just want to know what any of these Verus features are for:

 3. Verus's `state_machine!` or `tokenized_state_machine!` macros
 4. Verus's `tracked` variable mode ("linear ghost state").

This guide expects general familiarity with Verus, so readers unfamiliar with Verus
should check out the general [Verus user guide](https://verus-lang.github.io/verus/guide/)
first and become proficient at coding within its `spec`, `proof`, and `exec` modes,
using `ghost` and `exec` variables.

### Further Reading

For a fully comprehensive account, please see [Verifying Concurrent Systems Code](https://www.andrew.cmu.edu/user/bparno/papers/hance_thesis.pdf).
