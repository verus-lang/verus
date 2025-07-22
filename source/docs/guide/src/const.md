# const declarations

In Verus, `const` declarations are treated internally as 0-argument function calls. 
Thus just like functions, `const` declarations can be marked `spec`, `proof`, `exec`, 
or left without an explicit mode. 
By default, a `const` without an explicit mode is assigned a dual `spec/exec` mode. 
We'll go through what each of these modes mean.

## `spec` consts
A `spec const` is like a `spec` function with no arguments.
It is always ghost and cannot be used as an `exec` value. 

```rust
{{#include ../../../../examples/guide/const.rs:spec_const}}
```

## `proof` and `exec` consts
Just as `proof` and `exec` functions can have `ensures` clauses specifying a postcondition, 
`proof` and `exec` consts can have `ensures` clauses to tie the declaration to a `spec` expression. 
The syntax follows the syntax of a function definition. 

```rust
{{#include ../../../../examples/guide/const.rs:exec_const_syntax}}
```

Note here that we can also use `assert` when defining the const, 
and that we can define it using a call to another `const` function. 

```rust
{{#include ../../../../examples/guide/const.rs:exec_const_complicated}}
```

## `spec/exec` consts
A `const` without an explicit mode is dual-use:
it is usable as both an `exec` value and a `spec` value. 

```rust
{{#include ../../../../examples/guide/const.rs:spec_exec_const}}
```

Therefore, the `const` definition is restricted to obey the rules
for both `exec` code and `spec` code.
For example, as with `exec` code, its type must be compilable (e.g. `u8`, not `int`),
and, as with `spec` code, it cannot call any `exec` or `proof` functions. 

```rust
const fn foo() -> u64 { 1 }
const C: u64 = foo();  // FAILS with error "cannot call function `foo` with mode exec"
```

## Using an `exec const` in a `spec` or `proof` context
Similar to functions, if you want to use an `exec const` in a `spec` or `proof` context, 
you can annotate the declaration with `[verifier::when_used_as_spec(SPEC_DEF)]`, 
where `SPEC_DEF` is the name of a `spec const` or a `spec` function with no arguments. 

```rust
{{#include ../../../../examples/guide/const.rs:when_used_as_spec}}
```
In this example, without the annotation, Verus will give the error 
"cannot read const with mode exec." 

Moreover, attempting to use the annotation 
`#[verifier::when_used_as_spec(layout::size_of::<usize>)]`,
without defining `SPEC_USIZE_BYTES` separately,
will also result in an error: 
`when_used_as_spec` can only handle the case when two functions or consts have the same signature. 
It doesn't handle using something like `::<usize>` to coerce a function to a different signature.

## Trouble-shooting overflow errors
Verus may have difficulty proving that a `const` declaration does not overflow; 
using `[verifier::when_used_as_const(SPEC_DEF)]` 
or `[verifier::non_linear]` may help. 

For example, here `[verifier::non_linear]` is added to prevent the error 
"possible arithmetic underflow/overflow." 
This allows Verus to reason about the (seemingly) 
non-linear expression `BAR_PLUS_ONE * BAR`, 
instead of giving up immediately. 
See the [chapter on non-linear reasoning](nonlinear.md) for more details.

```rust
{{#include ../../../../examples/guide/const.rs:nonlinear}}
```