An example of parsing a custom syntax within a `functionlike!(...)` procedural
macro. Demonstrates how to trigger custom warnings and error messages on
individual tokens of the input.

- [`lazy-static/src/lib.rs`](lazy-static/src/lib.rs)
- [`example/src/main.rs`](example/src/main.rs)

The library implements a `lazy_static!` macro similar to the one from the real
[`lazy_static`](https://docs.rs/lazy_static/1.0/lazy_static/) crate on
crates.io.

```rust
lazy_static! {
    static ref USERNAME: Regex = Regex::new("^[a-z0-9_-]{3,16}$").unwrap();
}
```

Compile and run the example by doing `cargo run` in the directory of the
`example` crate.

The implementation shows how to trigger custom warnings and error messages on
the macro input. For example if you try adding an uncreatively named `FOO` lazy
static, the macro will scold you with the following warning.

```
warning: come on, pick a more creative name
  --> src/main.rs:10:16
   |
10 |     static ref FOO: String = "lazy_static".to_owned();
   |                ^^^
```

And if you try to lazily initialize `() = ()`, the macro will outright refuse to
compile it for you.

```
error: I can't think of a legitimate use for lazily initializing the value `()`
  --> src/main.rs:10:27
   |
10 |     static ref UNIT: () = ();
   |                           ^^
```
