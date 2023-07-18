# Variable modes

In addition to having three function modes, Verus has three _variable_ modes: `exec`, `tracked`, and `ghost`. Only `exec` variables exist in the compiled code, while `ghost` and `tracked` variables are "erased" from the compiled code.

See [this tutorial page](./modes.md) for an introduction to the concept of modes.
The tracked mode is an advanced feature, and is discussed more in the [concurrency guide](https://verus-lang.github.io/verus/state_machines/intro.html).

## Variable modes and function modes

Which variables are allowed depends on the expression mode, according to the following table:

|            | Default variable mode | `ghost` variables | `tracked` variables | `exec` variables |
|------------|-----------------------|-------------------|---------------------|------------------|
| spec code  | `ghost`               | yes               |                     |                  |
| proof code | `ghost`               | yes               | yes                 |                  |
| exec code  | `exec`                | yes               | yes                 | yes              |

Although `exec` code allows variables of any mode, there are some restrictions; see below.

## Using `tracked` and `ghost` variables from a `proof` function.

By default, any variable in a proof function has `ghost` mode. Parameters, variables,
and return values may be marked tracked. For example:

```rust
fn some_proof_fn(tracked param: Foo) -> (tracked ret: RetType) {
    let tracked x = ...;
}
```

For return values, the `tracked` keyword can only apply to the entire return type.
It is not possible to selectively apply `tracked` to individual elements of a tuple,
for example.

To mix-and-match tracked and ghost data, there are a few possibilities.
First, you can create a struct
marked `tracked`, which individual fields either marked `ghost` or `tracked`.

Secondly, you can use the `Tracked` and `Ghost` types from Verus's builtin library to
create tuples like `(Tracked<X>, Ghost<Y>)`. These support pattern matching:

```rust
proof fn some_call() -> (tracked ret: (Tracked<X>, Ghost<Y>)) { ... }

proof fn example() {
    // The lower-case `tracked` keyword is used to indicate the right-hand side
    // has `proof` mode, in order to allow the `tracked` call.
    // The upper-case `Tracked` and `Ghost` are used in the pattern matching to unwrap
    // the `X` and `Y` objects.
    let tracked (Tracked(x), Ghost(y)) = some_call();
}
```

## Using `tracked` and `ghost` variables from an `exec` function.

Variables in `exec` code may be marked `tracked` or `ghost`. These variables will be erased
when the code is compiled. However, there are some restrictions.
In particular, variables marked `tracked` or `ghost` may be declared anywhere in an `exec` block. However, such variables may only be _assigned_ to from inside a `proof { ... }` block.

```rust
fn some_exec_fn() {
    let ghost mut x = 5; // this is allowed

    proof {
        x = 7; // this is allowed
    }

    x = 9; // this is not allowed
}
```

Futhermore:

 * Arguments and return values for an `exec` function must be `exec` mode.

 * Struct fields of an `exec` struct must be `exec` mode.

To work around these, programs can use the `Tracked` and `Ghost` types.
Like in proof code, Verus supports pattern-matching for these types.

```rust
exec fn example() {
    // Because of the keyword `tracked`, Verus interprets the right-hand side
    // as if it were in a `proof` block.
    let tracked (Tracked(x), Ghost(y)) = some_call();
}
```

To handle parameters that must be passed via `Tracked` or `Ghost` types, 
you can unwrap them via pattern matching:

```rust
exec fn example(Tracked(x): Tracked<X>, Ghost(y): Ghost<Y>) {
    // Use `x` as if it were declared `let tracked x`
    // Use `y` as if it were declared `let tracked y`
}
```

## Cheat sheet

### Proof function, take tracked or ghost param

```rust
proof fn example(tracked x: X, ghost y: Y)
```

To call this function from proof code:

```rust
proof fn test(tracked x: X, ghost y: Y) {
    example(x, y);
}
```

To call this function from exec code:

```rust
fn test() {
    let tracked x = ...;
    let ghost y = ...;

    // From a proof block:
    proof { example(x, y); }
}
```

### Proof function, return ghost param

```rust
proof fn example() -> (ret: Y)
```

To call this function from proof code:

```rust
proof fn test() {
    let y = example();
}
```

To call this function from exec code:

```rust
fn test() {
    let ghost y = example();
}
```

### Proof function, return tracked param

```rust
proof fn example() -> (tracked ret: X)
```

To call this function from proof code:

```rust
proof fn test() {
    let tracked y = example();
}
```

To call this function from exec code:

```rust
fn test() {
    // In a proof block:
    proof { let tracked y = example(); }

    // Or outside a proof block:
    let tracked y = example();
}
```

### Proof function, return both a ghost param and tracked param

```rust
proof fn example() -> (tracked ret: (Tracked<X>, Ghost<Y>))
```

To call this function from proof code:

```rust
proof fn test() {
    let tracked (Tracked(x), Ghost(y)) = example();
}
```

To call this function from exec code:

```rust
fn test() {
    // In a proof block:
    proof { let tracked (Tracked(x), Ghost(y)) = example(); }

    // or outside a proof block:
    let tracked (Tracked(x), Ghost(y)) = example();
}
```

### Exec function, take a tracked and ghost parameter:

```rust
fn example(Tracked(x): Tracked<X>, Ghost(y): Ghost<Y>)
```

To call this function from exec code:

```rust
fn test() {
    let tracked x = ...;
    let ghost y = ...;

    example(Tracked(x), Ghost(y));
}
```

### Exec function, return a tracked and ghost value:

```rust
fn example() -> (Tracked<X>, Ghost<Y>)
```

To call this function from exec code:

```rust
fn test() {
    let (Tracked(x), Ghost(y)) = example();
}
```

### Exec function, take a tracked parameter that is a mutable reference:

```rust
fn example(Tracked(x): Tracked<&mut X>)
```

To call this function from exec code:

```rust
fn test() {
    let tracked mut x = ...;

    example(Tracked(&mut x));
}
```
