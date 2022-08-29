An example of an attribute procedural macro. The `#[trace_var(...)]` attribute
prints the value of the given variables each time they are reassigned.

- [`trace-var/src/lib.rs`](trace-var/src/lib.rs)
- [`example/src/main.rs`](example/src/main.rs)

Consider the following factorial implementation.

```rust
#[trace_var(p, n)]
fn factorial(mut n: u64) -> u64 {
    let mut p = 1;
    while n > 1 {
        p *= n;
        n -= 1;
    }
    p
}
```

Invoking this with `factorial(8)` prints all the values of `p` and `n` during
the execution of the function.

```
p = 1
p = 8
n = 7
p = 56
n = 6
p = 336
n = 5
p = 1680
n = 4
p = 6720
n = 3
p = 20160
n = 2
p = 40320
n = 1
```

The procedural macro uses a syntax tree [`Fold`] to rewrite every `let`
statement and assignment expression in the following way:

[`Fold`]: https://docs.rs/syn/1.0/syn/fold/trait.Fold.html

```rust
// Before
let VAR = INIT;

// After
let VAR = { let VAR = INIT; println!("VAR = {:?}", VAR); VAR };
```

```rust
// Before
VAR = INIT

// After
{ VAR = INIT; println!("VAR = {:?}", VAR); }
```
