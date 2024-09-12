# Preconditions (requires clauses)

Let's start with a small example.
Suppose we want to verify a function `octuple` that multiplies a number by 8:

```rust
{{#include ../../../rust_verify/example/guide/requires_ensures_edit.rs:init}}
```

If we ask Verus to verify this code, Verus immediately reports errors about `octuple`:

```
error: possible arithmetic underflow/overflow
   |
   |     let x2 = x1 + x1;
   |              ^^^^^^^
```

Here, Verus cannot prove that the result of `x1 + x1` fits in an 8-bit `i8` value,
which allows values in the range `-128`...`127`.
If `x1` were `100`, for example, `x1 + x1` would be `200`, which is larger than `127`.
We need to make sure that when `octuple` is called, the argument `x1` is not too large.
We can do this by adding *preconditions* (also known as "`requires` clauses")
to `octuple` specifying which values for `x1` are allowed.
In Verus, preconditions are written with a `requires` followed by zero or more boolean expressions
separated by commas:

```rust
{{#include ../../../rust_verify/example/guide/requires_ensures_edit.rs:pre1}}
```

The two preconditions above say that x1 must be at least `-64` and less than `64`,
so that `x1 + x1` will fit in the range `-128`...`127`.
This fixes the error about `x1 + x1`, but we still get an error about `x2 + x2`:

```
error: possible arithmetic underflow/overflow
   |
   |     let x4 = x2 + x2;
   |              ^^^^^^^
```

If we want `x1 + x1`, `x2 + x2`, and `x4 + x4` to all succeed, we need a tighter bound on `x1`:

```rust
{{#include ../../../rust_verify/example/guide/requires_ensures_edit.rs:pre2}}
```

This time, verification is successful.

Now suppose we try to call `octuple` with a value that does not satisfy `octuple`'s precondition:

```rust
{{#include ../../../rust_verify/example/guide/requires_ensures_edit.rs:pre3}}
```

For this call, Verus reports an error, since `20` is not less than `16`:

```
error: precondition not satisfied
   |
   |         x1 < 16,
   |         ------- failed precondition
...
   |     let n = octuple(20);
   |             ^^^^^^^^^^^
```

If we pass `10` instead of `20`, verification succeeds:

```rust
{{#include ../../../rust_verify/example/guide/requires_ensures_edit.rs:pre4}}
```

# Postconditions (ensures clauses)

Suppose we want to verify properties about the value returned from `octuple`.
For example, we might want to assert that the value returned from `octuple`
is 8 times as large as the argument passed to `octuple`.
Let's try putting an assertion in `main` that the result of calling `octuple(10)` is `80`:

```rust
{{#include ../../../rust_verify/example/guide/requires_ensures_edit.rs:post1}}
```

Although `octuple(10)` really does return `80`,
Verus nevertheless reports an error:

```
error: assertion failed
   |
   |     assert(n == 80);
   |            ^^^^^^^ assertion failed
```

The error occurs because, even though `octuple` multiplies its argument by `8`,
`octuple` doesn't publicize this fact to the other functions in the program.
To do this, we can add postconditions (`ensures` clauses) to `octuple` specifying
some properties of `octuple`'s return value:

```rust
{{#include ../../../rust_verify/example/guide/requires_ensures_edit.rs:post2}}
```

To write a property about the return value, we need to give a name to the return value.
The Verus syntax for this is `-> (name: return_type)`.  In the example above,
saying `-> (x8: i8)` allows the postcondition `x8 == 8 * x1` to use the name `x8`
for `octuple`'s return value.

Preconditions and postconditions establish a modular verification protocol between functions.
When `main` calls `octuple`, Verus checks that the arguments in the call satisfy `octuple`'s
preconditions.
When Verus verifies the body of the `octuple` function,
it can assume that the preconditions are satisfied,
without having to know anything about the exact arguments passed in by `main`.
Likewise, when Verus verifies the body of the `main` function,
it can assume that `octuple` satisfies its postconditions,
without having to know anything about the body of `octuple`.
In this way, Verus can verify each function independently.
This *modular verification* approach breaks verification into small, manageable pieces,
which makes verification more efficient than if Verus tried to verify
all of a program's functions together simultaneously.
Nevertheless, writing preconditions and postconditions requires significant programmer effort ---
if you want to verify a large program with a lot of functions,
you'll probably spend substantial time writing preconditions and postconditions for the functions.

# assert and assume

While `requires` and `ensures` connect functions together,
`assert` makes a local, private request to the SMT solver to prove a certain fact.
(Note: `assert(...)` should not be confused with the Rust `assert!(...)` macro ---
the former is statically checked using the SMT solver, while the latter is checked at run-time.)

`assert` has an evil twin named `assume`, which asks the SMT solver to
simply accept some boolean expression as a fact without proof.
While `assert` is harmless and won't cause any unsoundness in a proof,
assume can easily enable a "proof" of a fact that isn't true.
In fact, by writing `assume(false)`, you can prove anything you want:

```rust
assume(false);
assert(2 + 2 == 5); // succeeds
```

Verus programmers often use `assert` and `assume` to help develop and debug proofs.
They may add temporary `assert`s to determine which facts the SMT solver can prove
and which it can't,
and they may add temporary `assume`s to see which additional assumptions are necessary
for the SMT solver to complete a proof,
or as a placeholder for parts of the proof that haven't yet been written.
As the proof evolves, the programmer replaces `assume`s with `assert`s,
and may eventually remove the `assert`s.
A complete proof may contain `assert`s, but should not contain any `assume`s.

(In some situations, `assert` can help the SMT solver complete a proof,
by giving the SMT hints about how to manipulate `forall` and `exists` expressions; see TODO.
There are also special forms of `assert`, such as `assert(...) by(bit_vector)`,
to help prove properties about bit vectors, nonlinear integer arithmetic,
`forall` expressions, etc.  These are covered in section TODO.)

# Executable code and ghost code

Let's put everything from this section together into a final version of our example program:

```rust
{{#include ../../../rust_verify/example/guide/requires_ensures.rs}}
```

Here, we've made a few final adjustments.

First, we've combined the two preconditions `-16 <= x1` and `x1 < 16`
into a single preconditon `-16 <= x1 < 16`,
since Verus lets us chain multiple inequalities together in a single expression
(equivalently, we could have also written `-16 <= x1 && x1 < 16`).

Second, we've added a function `print_two_digit_number` to print the result of `octuple`.
Unlike `main` and `octuple`, we ask Verus not to verify `print_two_digit_number`.
We do this by marking it `#[verifier::external_body]`,
so that Verus pays attention to the function's preconditions and postconditions but ignores
the function's body.
This is common in projects using Verus:
you may want to verify some of it (perhaps the program's core algorithms),
but leave other aspects, such as input-output operations, unverified.
More generally, since verifying all the software in the world is still infeasible,
there will be some boundary between verified code and unverified code,
and `#[verifier::external_body]` can be used to mark this boundary.

We can now compile the program above using the `--compile` option to Verus:

```
./tools/rust-verify.sh --compile rust_verify/example/guide/requires_ensures.rs
```

This will produce an executable that prints a message when run:

```
The answer is 80
```

Note that the generated executable does not contain the `requires`, `ensures`, and `assert` code,
since these are only needed during static verification,
not during run-time execution.
We refer to `requires`, `ensures`, `assert`, and `assume` as *ghost code*,
in contast to the *executable code* that actually gets compiled.
Verus erases all ghost code before compilation so that it imposes no run-time overhead.
