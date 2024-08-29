# The "global" directive

By default, Verus has no access to [layout information](https://doc.rust-lang.org/reference/type-layout.html), such as the size
([`std::mem::size_of::<T>()`](https://doc.rust-lang.org/std/mem/fn.size_of.html))
or alignment ([`std::mem::align_of::<T>()`](https://doc.rust-lang.org/std/mem/fn.align_of.html))
of a struct.
Such information is often unstable (i.e., it may vary between versions of Rust)
or may be platform-dependent (such as the size of `usize`).

This information can be provided to Verus as needed using the `global` directive.

For a type `T`, and integer literals `n` or `m`, the `global` directive is a Verus item
that takes the form:

```rust
global layout T is size == n, align == m;
```

Either `size` or `align` may be omitted. The global directive both:

 * Exports the axioms `size_of::<T>() == n` and `align_of::<T> == m` for use in Verus proofs
 * Creates a "static" check ensuring the given values are actually correct when compiled.

Note that the second check _only_ happens when codegen is run; an "ordinary" verification pass will
not perform this check. This ensures that the check is always performed on the correct
platform, but it may cause surprises if you spend time on verification without running codegen.

In order to keep the layout stable, it is recommended using Rust attributes
like [`#[repr(C)]`](https://doc.rust-lang.org/reference/type-layout.html#reprc-structs).
Keep in mind that the Verus verifier gets no information from these attributes.
Layout information can only be provided to Verus via the `global` directive.

## With `usize` and `isize`

For the integer types `usize` and `isize`, the `global` directive has additional behavior.
Specifically, it influences the _integer range_ used in encoding `usize` and `isize` types.

For an integer literal `n`, the directive,

```
global layout usize is size == n;
```

Tells Verus that:
  * `usize::BITS == 8 * n` 
  * `isize::BITS == 8 * n` 
  * The integer range for `usize` (`usize::MIN ..= usize::MAX`) is <code>0 ..= 2<sup>8*n</sup> - 1</code>
  * The integer range for `isize` (`isize::MIN ..= isize::MAX`) is <code>-2<sup>8&#42;n-1</sup> ..= 2<sup>8*n-1</sup> - 1</code>

By default (i.e., in the absence of a `global` directive regarding `usize` or `isize`),
Verus assumes that the size is either 4 or 8, i.e., that the integer range is
either 32 bits or 64 bits.

### Example

```
global layout usize is size == 4;

fn test(x: usize) {
    // This passes because Verus assumes x is a 32-bit integer:
    assert(x <= 0xffffffff);
    assert(usize::BITS == 32);
}
```
