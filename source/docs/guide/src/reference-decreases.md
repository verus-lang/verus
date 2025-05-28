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
However, the function definition will only be concretely specified when the `when` clause is true.
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

### Helping Verus prove termination

Sometimes, it may be true that the decreases-measure decreases, but Verus cannot prove
it automatically.  When this happens, the user can either supply a proof inside the body
of the recursive function, or use a separate lemma to prove the decreases property.
In the vast majority of cases, writing a proof inside the function body is simpler
and easier to read.  The main reason to use a separate lemma is if you want
to keep your trusted specifications as minimal as possible.

**Example.**
On its own, Verus cannot see that `n` decreases at each recursive call.
We'll use this example to illustrate the two methods of helping Verus prove termination.
```rust
spec fn floor_log2(n: u64) -> int 
    decreases n
{
    if n <= 1 { 
        0   
    } else {
        floor_log2(n >> 1) + 1 
    }   
}
```
In order to check that the recursion in `floor_log2` terminates, Verus generates a proof obligation
that `n > 1 ==> decreases_to!(n => n >> 1)`. (The `n > 1` hypothesis stems from the fact that
the recursive call is in the else-block.) Thus we need to show:

`n > 1 ==> (n >> 1) < n`

Verus cannot prove this automatically. 

#### Writing an proof of termination inside your recursive function

For the purposes of termination checking, you can include a `proof {}` block
in the body of your spec function.  The proof needs to demonstrate that your
decreases measure really does decrease at each recursive call site.

Note that at present, this proof block can only assist with termination.
You cannot use it, for example, to prove additional properties about your function
for use elsewhere.

**Example**
Here we supply the fact Verus was missing using Verus's specialized 
[bit-vector reasoning mode](bitvec.md).

```rust
{{#include ../../../../examples/guide/recursion.rs:example_proof_in_spec}}
```

#### Writing a separate proof of termination with the `via` clause

To avoid cluttering your recursive spec function with proof material,
you can add a `via PROOF_FUNCTION_NAME` clause to the spec function.
`FUNCTION_NAME` must be the name of a `proof` function defined in the same module
that takes the same arguments as the recursive function.
This proof function must also be annotated with the `#[via_fn]` attribute.

The proof function's job is to prove the relevant decreases property for each
call site.  In other words, it needs to show that the decreases measure actually
decreases at each recursive call in the spec function's body.

**Example.**
In the following definition, we use a `via` clause to prove that the decreases-measure
decreases.

```rust
{{#include ../../../../examples/guide/recursion.rs:example_proof_using_via}}
```
The proof function `floor_log2_decreases_proof` is defined as a `via_fn` and is referenced from the `via` clause. The body of the proof function contains a proof that `n > 1 ==> (n >> 1) < n` (the same proof we used inline above).
