# Documentation with Rustdoc

Verus provides a tool to help make Verus specification look nice in rustdoc.
To do this, you first run `rustdoc` on a crate and then run an HTML postprocessor called
Verusdoc.

First, make sure `verusdoc` is built by running `vargo build -p verusdoc` in the
`verus/source` directory.

Unfortunately, we currently don't have helpful tooling for running `rustdoc` with the
appropriate dependencies and flags, so you'll need to set that up manually.
Here is an example:

```bash
VERUS=/path/to/verus/source

if [ `uname` == "Darwin" ]; then
    DYN_LIB_EXT=dylib
elif [ `uname` == "Linux" ]; then
    DYN_LIB_EXT=so
fi

# Run rustdoc.
# Note the VERUSDOC environment variable.

RUSTC_BOOTSTRAP=1 VERUSDOC=1 rustdoc \
  --extern builtin=$VERUS/target-verus/debug/libbuiltin.rlib \
  --extern builtin_macros=$VERUS/target-verus/debug/libbuiltin_macros.$DYN_LIB_EXT \
  --extern state_machines_macros=$VERUS/target-verus/debug/libstate_machines_macros.$DYN_LIB_EXT \
  --extern vstd=$VERUS/target-verus/debug/libvstd.rlib \
  --edition=2021 \
  --cfg verus_keep_ghost \
  --cfg verus_keep_ghost_body \
  --cfg 'feature="std"' \
  --cfg 'feature="alloc"' \
  '-Zcrate-attr=feature(register_tool)' \
  '-Zcrate-attr=register_tool(verus)' \
  '-Zcrate-attr=register_tool(verifier)' \
  '-Zcrate-attr=register_tool(verusfmt)' \
  --crate-type=lib \
  ./lib.rs

# Run the post-processor.

$VERUS/target/debug/verusdoc
```

If you run it with a file `lib.rs` like this:

```
#![allow(unused_imports)]

use builtin::*;
use builtin_macros::*;
use vstd::prelude::*;

verus!{

/// Computes the max
pub fn compute_max(x: u32, y: u32) -> (max: u32)
    ensures max == (if x > y { x } else { y }),
{
    if x < y {
        y
    } else {
        x
    }
}

}
```

It will generate rustdoc that looks like this:


![Screenshot of a verusdoc example illustrating the inclusion of an `ensures` clauses](graphics/verusdoc-example.png)
