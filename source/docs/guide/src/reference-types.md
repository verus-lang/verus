# Spec representations of types

## Integer types

Verus integer types include the standard Rust primitive types (`u8`, `u16`, `u32`, `u64`, `u128`, `usize`, `i8`, `i16`, `i132`, `i64`, `i128`, and `isize`) together with Verus builtin types
`int` and `nat`.

Every type is represented as an integer (i.e., an element of ℤ) together with an implied bound
if necessary:

 * `int`: `(-∞, ∞)` (i.e., no bound)
 * `nat`: `[0, ∞)`
 * `uN`: <code>&#x5b;0, 2<sup>N</sup>)</code>
 * `iN`: <code>&#x5b;-2<sup>N-1</sup>, 2<sup>N-1</sup>)</code>
 * `usize`: <code>&#x5b;0, 2<sup>N</sup>)</code> where `N` is the platform's word size in bits
 * `isize`: <code>&#x5b;-2<sup>N-1</sup>, 2<sup>N-1</sup>)</code> where `N` is the platform's word size in bits

For `isize` and `usize`, assumptions of the platform word size is configurable
via the [`global` directive](http://localhost:3000/reference-global.html#with-usize-and-isize).

Integer types are inter-covertible using [`as`-casts](./reference-as.md).

For all integer types, spec equality is defined as integer equality.

## Bool

A boolean is either `true` or `false`.

Verus defines 

For `bool`, spec equality is defined as boolean equivalence.

## Char

A `char` is treated as an [integer type](#integer-types) with a bespoke validity range.
Verus follows the [Rust specification for a `char`](https://doc.rust-lang.org/std/primitive.char.html):

> A char is a ‘Unicode scalar value’, which is any ‘Unicode code point’ other than a surrogate code point. This has a fixed numerical definition: code points are in the range 0 to 0x10FFFF, inclusive. Surrogate code points, used by UTF-16, are in the range 0xD800 to 0xDFFF.

That is, Verus treats `char` as an element of ℤ from:

`[0, 0xD7ff] ∪ [0xE000, 0x10FFFF]`

In spec code, a `char` is inter-covertible with the integer types using [`as`-casts](./reference-as.md).
This is more
permissive than exec code, which disallows many of these coercions.
As with other coercions, the result may be undefined if the integer being coerced does not
fit in the target range.

For `char`, spec equality is defined as integer equality.


## Tuple

## Box (`Box<T>`)

## Shared reference (`&T`)

## Mutable reference (`&mut T`)

In spec code, one reasons about a mutable reference `x: &mut T` through values:

 * `*x`: the current value behind the mutable reference.
 * `*final(x)`: the final value the mutable reference will point to when it expires.
   This value is considered [prophetic](./reference-attributes.md#verifierprophetic).


See [the guide page](./mutable-references.md)
for practical information on using mutable references.

> **Note:** In postconditions, you may be required to write `*old(x)` instead of `*x`
> where `x: &mut T` is an input to the function.
> This has no meaning at a formal level;
> it is only used to prevent user confusion regarding which value `*x` refers to.

> **Note:** Equality of mutable references in spec code is not the same as equality of mutable references in exec code.
> Exec comparisons only compare the values behind the pointers. In spec code, mutable references
> with different origins are **never** equal, not even if they have the same value, final value,
> and address. In particular, a reborrow is not equal to the mutable borrow it is borrowed from.

> **Note:** Verus does not insert "implicit reborrows" for spec-mode uses of a mutable reference.

> **Note:** Through spec-snapshots, it is possible to create self-referential mutable references
> via the `final` operator.
>
> ```rust
> struct Rec {
>     g: Option<Ghost<&'static mut Rec>>,
> }
>
> fn test() {
>     let mut r = Rec { g: None };
>
>     let mut r_ref = &mut r;
>     *r_ref = Rec { g: Some(Ghost(r_ref)) };
>
>     assert(r.g.is_some());
>     assert(r == *final(r.g.unwrap()@)); // cycle
> }
> ```
>
> As a result, Verus does not treat <code>*final(x)</code> as a subfield of `x` for the purposes of
> [decreases-to](./reference-decreases-to.md), i.e., recursion through the `final` value is
> not considered to be well-founded recursion.

> **Note:** Verus used to treat mutable references very differently before 2026-05-03 release.
> See [the migration guide](https://github.com/verus-lang/verus/blob/main/source/docs/migration-mut-ref.md) for more information about the transition.


## Pointer (`*const T` and `*mut T`)

In spec code, a pointer `ptr: *mut T` or `ptr: *const T` is defined by three pieces of data:

 * `ptr.addr()` of type `usize`: The address of the pointer
 * `ptr@.metadata` of type [`<T as Pointee>::Metadata`](https://doc.rust-lang.org/std/ptr/trait.Pointee.html)
 * `ptr@.provenance` of abstract type [`Provenance`](https://verus-lang.github.io/verus/verusdoc/vstd/raw_ptr/struct.Provenance.html)

Verus treats pointers obey extentional equality: if two pointers are equal in the above three properties,
then the pointers are equal.

See the [`raw_ptr`](https://verus-lang.github.io/verus/verusdoc/vstd/raw_ptr/index.html) vstd librararies for reasoning about pointer accesses.

> **Note:** Equality of pointers in spec code is not the same as equality of pointers in exec code.
> Exec comparisons only compare the address and metadata, while spec comparisons also compare provenance.

> **Note:** Verus treats `*const T` and `*mut T` identically, except for the usual differences
> in [variance](https://doc.rust-lang.org/reference/subtyping.html?#variance).
> Casting `*const T` to `*mut T` and vice versa is semantically a no-op.

## `String` and `str`

