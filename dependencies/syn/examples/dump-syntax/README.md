Parse a Rust source file into a `syn::File` and print out a debug representation
of the syntax tree.

Use the following command from this directory to test this program by running it
on its own source code:

```
cargo run -- src/main.rs
```

The output will begin with:

```
File {
    shebang: None,
    attrs: [
        Attribute {
            pound_token: Pound,
            style: Inner(
                Bang
            ),
            bracket_token: Bracket,
            path: Path {
                leading_colon: None,
                segments: [
    ...
}
```
