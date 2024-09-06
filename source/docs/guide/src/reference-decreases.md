# decreases ... when ... via ...

The `decreases` clause is necessary for ensuring termination of recursive and mutually-recursive
functions. See [this tutorial page](./recursion.md) for an introduction.

## Overview

A collection of functions is _mutually recursive_
if their call graph is strongly connected (i.e., every function in the collection depends, directly or indirectly, on every function in the collection).
(A single function that calls itself forms a mutually recursive collection of size 1.)
A function is _recursive_ if it is in some mutually recursive collection.

A recursive spec function is required to supply a `decreases` clause, which takes
the form:

```rust
decreases EXPR_1, ...
    [ when BOOL_EXPR ]?
    [ via FUNCTION_NAME ]?
```

The sequence of expressions in the decreases clause is the _decreases-measure_.
The expressions in the decreases-measure and the expression in the `when`-clause
may reference the function's arguments.

Verus requires that, for any two mutually recursive functions,
the number of elements in their decreases-measure must be the same.

### The decreases-measure

Verus checks that, when a recursive function calls itself or any other function in
its mutually recursive collection, the decreases-measure of the caller _decreases-to_
the decreases-measure of the callee.
See [the formal definition of _decreases-to_](./reference-decreases-to.md).

### The `when` clause

If the `when` clause is supplied, then the given condition may be assumed when
proving the decreases properties.
However, the function will only be defined when the `when` clause is true.
In other words, something like this:

```rust
fn f(...) -> _
    decreases ...
        when condition
{
    body
}
```

Will be equivalent to this:

```rust
fn f(args...) -> _
{
    if condition {
        body
    } else {
        some_unknown_function(args...)
    }
}
```

### The `via` clause

Sometimes, it may be true that the decreases-measure decreases, but Verus cannot prove
it automatically. In this case, the user can supply a lemma to prove the decreases property.

If the `via` clause is supplied,
the `FUNCTION_NAME` must be the name of a `proof` function defined in the same module.
The number of expressions in the `decreases` clause must be the same for each function
in a mutually recursive collection.
This proof function must also be annotated with the `#[via_fn]` attribute.

It is the job of the proof function to prove the relevant decreases property for each
call site.
