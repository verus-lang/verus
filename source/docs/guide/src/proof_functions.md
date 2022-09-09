# proof functions

Consider the `pub closed spec` `min` function from the previous section.
This defined an abstract `min` function without revealing the internal
definition of `min` to other modules.
However, an abstract function definition is useless unless we can say something about the function.
For this, we can use a `proof` function.
In general, `proof` functions will reveal or prove properties about specifications.
In this example, we'll define a `proof` function named `lemma_min` that
reveals properties about `min` without revealing the exact definition of `min`.
Specifically, `lemma_min` reveals that `min(x, y)` equals either `x` or `y` and
is no larger than `x` and `y`:

```rust
{{#include ../../../rust_verify/example/guide/modes.rs:spec_fun_proof}}
```

Like `exec` functions, `proof` functions may have `requires` and `ensures` clauses.
Unlike `exec` functions, `proof` functions are ghost and are not compiled to executable code.
In the example above, the `lemma_min(10, 20)` function is used to help the function `test` in module `M2`
prove an assertion about `min(10, 20)`, even when `M2` cannot see the internal definition of `min`
because `min` is `closed`.
On the other hand, the assertion about `min(100, 200)` still fails
unless `test` also calls `lemma_min(100, 200)`.

# proof blocks

Ultimately, the purpose of `spec` functions and `proof` functions is to help prove
properties about executable code in `exec` functions.
In fact, `exec` functions can contain pieces of `proof` code in *proof blocks*,
written with `proof { ... }`.
Just like a `proof` function contains `proof` code,
a `proof` block in an `exec` function contains `proof` code
and can use all of the ghost code features that `proof` functions can use,
such as the `int` and `nat` types.

Consider an [earlier example](integers.md#integer-constants) that introduced
variables inside an assertion:

```rust
{{#include ../../../rust_verify/example/guide/integers.rs:test_consts_infer}}
```

We can write this in a more natural style using a proof block:

```rust
{{#include ../../../rust_verify/example/guide/modes.rs:spec_fun_proof_block1}}
```

Here, the `proof` code inside the `proof` block can create local variables
of type `int` and `nat`,
which can then be used in a subsequent assertion.
The entire `proof` block is ghost code, so all of it, including its local variables,
will be erased before compilation to executable code.

Proof blocks can call `proof` functions.
In fact, any calls from an `exec` function to a `proof` function
must appear inside `proof` code such as a `proof` block,
rather than being called directly from the `exec` function's `exec` code.
This helps clarify which code is executable and which code is ghost,
both for the compiler and for programmers reading the code.
In the exec function `test` shown below,
a `proof` block is used to call `lemma_min`,
allowing subsequent assertions about `min` to succeed.

```rust
{{#include ../../../rust_verify/example/guide/modes.rs:spec_fun_proof_block2}}
```

# assert-by

Notice that in the previous example,
the information that `test` gains about `min`
is not confined to the `proof` block,
but instead propagates past the end of the `proof` block
to help prove the subsequent assertions.
This is often useful,
particularly when the `proof` block helps
prove preconditions to subsequent calls to `exec` functions,
which must appear outside the `proof` block.

However, sometimes we only need to prove information for a specific purpose,
and it clarifies the structure of the code if we limit the scope
of the information gained.
For this reason,
Verus supports `assert(...) by { ... }` expressions,
which allows `proof` code inside the `by { ... }` block whose sole purpose
is to prove the asserted expression in the `assert(...)`.
Any additional information gained in the `proof` code is limited to the scope of the block
and does not propagate outside the `assert(...) by { ... }` expression.

In the example below,
the `proof` code in the block calls both `lemma_min(10, 20)` and `lemma_min(100, 200)`.
The first call is used to prove `min(10, 20) == 10` in the `assert(...) by { ... }` expression.
Once this is proven, the subsequent assertion `assert(min(10, 20) == 10);` succeeds.
However, the assertion `assert(min(100, 200) == 100);` fails,
because the information gained by the `lemma_min(100, 200)` call
does not propagate outside the block that contains the call.

```rust
{{#include ../../../rust_verify/example/guide/modes.rs:assert_by}}
```
