# Getting started with VSCode

This page will get you set up using Verus in VSCode using the [verus-analyzer](https://github.com/verus-lang/verus-analyzer) extension. Note that verus-analyzer is **very experimental.**

## 1. Install Verus.

To install Verus, follow the instructions at [INSTALL.md](https://github.com/verus-lang/verus/blob/main/INSTALL.md).

## 2. Create a Rust crate

Find a scratch directory to use, and run:

```
cargo init verus_test
```

This will create the following files:

 * `verus_test/Cargo.toml`
 * `verus_test/src/main.rs`

## 3. Install verus-analyzer via VSCode

Open VSCode and install `verus-analyzer` through the VSCode marketplace.

## 4. Test that Verus is working.

Open your `verus_test` project and navigate to the `src/main.rs` file. Paste in the following:

```rust
use vstd::prelude::*;

verus! {

spec fn min(x: int, y: int) -> int {
    if x <= y {
        x
    } else {
        y
    }
}

fn main() {
    assert(min(10, 20) == 10);
    assert(min(-10, -20) == -20);
    assert(forall|i: int, j: int| min(i, j) <= i && min(i, j) <= j);
    assert(forall|i: int, j: int| min(i, j) == i || min(i, j) == j);
    assert(forall|i: int, j: int| min(i, j) == min(j, i));
    assert(forall|i: int, j: int| min(i, j) == min(i, i));
}

} // verus!
```

Save the file in order to trigger verus-analyzer.

This program has an error which Verus should detect.
If everything is working correctly, you should see an error from Verus on the final `assert` line:

![Screenshot of VSCode indicating an error on the file source line](graphics/verus-analyzer-error-example.png)

If you click the link, "Click for full compiler diagnostic", you should see an error like:

```
error: assertion failed
  --> verus_test/src/main.rs:19:12
   |
19 |     assert(forall|i: int, j: int| min(i, j) == min(i, i));
   |            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ assertion failed
```

Delete this line, and now Verus should say that the file verifies successfully.

## 5. Learn more about the verus-analyzer extension.

See [the verus-analyzer README](https://github.com/verus-lang/verus-analyzer) for more information and tips on using verus-analyzer.
