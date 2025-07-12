# const declarations

In Verus, `const` declarations are treated internally as 0-argument function calls. 
Thus just like functions, `const` declarations can be marked `spec`, `proof`, `exec`, 
or left without a mode. 
By default, a `const` without a mode has a dual `spec/exec` mode. 
We'll go through what each of these modes mean.

## `spec` consts
A `spec const` is like a `spec` function with no arguments.
It is always ghost and cannot be used as an `exec` value. 

```rust
spec const SPEC_ONE: int = 1;

spec fn spec_add_one(x: int) -> int {
    x + SPEC_ONE
}
```

## `proof` and `exec` consts
<!-- `proof` and `spec` consts are like `proof` and `exec` functions with no arguments.  -->
Just as `proof` and `exec` functions can have `ensures` clauses specifying a post-condition, 
`proof` and `exec` consts have `ensures` clauses to tie the declaration to a `spec` expression. 
The syntax follows the syntax of a function definition: we define the type, 
followed by the ensures clause, followed by the declaration in curly brackets. 

```rust
exec const C: u64 
    ensures C == 7 
{
    7 
}
```

Idiomatically, the ensures clause is typically on the same line as the type, 
and if the definition is short enough, 
the entire declaration will be on one line. 
Note here that we can also use `assert` when defining the const. 

```rust
spec fn f() -> int { 1 }
const fn e() -> (u: u64) ensures u == f() { 1 }
exec const E: u64 ensures E == 2 {
    assert(f() == 1);
    1 + e()
}

exec const C: int ensures C == 7 { 7 }
```

## `spec/exec` consts
A `const` without a mode is dual-use:
it is usable as both an `exec` value and a `spec` value. 

```rust
const ONE: u8 = 1;

fn add_one(x: u8) -> (ret: u8)
    requires
        x < 0xff,
    ensures
        ret == x + ONE,  // use "ONE" in spec code
{
    x + ONE  // use "ONE" in exec code
}
```

Therefore, the `const` definition is restricted to obey the rules
for both `exec` code and `spec` code.
For example, as with `exec` code, its type must be compilable (e.g. `u8`, not `int`),
and, as with `spec` code, it cannot call any `exec` or `proof` functions. 

```rust
const fn foo() -> u64 { 1 }
const C: u64 = foo();  // FAILS with error "cannot call function `foo` with mode exec"
```

## Using `when_used_as_spec`
Similar to functions, if you want to use an `exec const` in a `spec` or `proof` context, 
you can annotate the declaration with `[verifier::when_used_as_const(SPEC_DEF)]`. 
In this example, without the annotation, Verus will give the error 
"cannot read const with mode exec."

```rust
spec const EIGHT_SPEC: u8 = 8;

#[verifier::when_used_as_spec(EIGHT_SPEC)]
exec const EIGHT: u8 ensures EIGHT == EIGHT_SPEC { 8 }

fn test(){
    assert(EIGHT == EIGHT_SPEC);
}
```

## Trouble-shooting overflow errors
Verus may have difficulty proving that a `const` declaration does not overflow; 
using `[verifier::when_used_as_const(SPEC_DEF)]` 
or with `[verifier::non_linear]` may help. 

For example, here `[verifier::non_linear]` is added to prevent the error 
"possible arithmetic underflow/overflow." 
This tells Verus to perform const propagation. 

```rust
pub const FOO: u8 = 4;
pub const BAR: u8 = FOO; //4
pub const BAR_PLUS_ONE: u8 = BAR + 1; 
#[verifier::nonlinear]
pub const C: u8 = BAR_PLUS_ONE * BAR; 
```