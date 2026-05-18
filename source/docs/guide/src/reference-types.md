# Spec interpretations of types

## Integer types

Verus integer types include the standard Rust primitive types (`u8`, `u16`, `u32`, `u64`, `u128`, `usize`, `i8`, `i16`, `i132`, `i64`, `i128`, and `isize`) together with Verus builtin types
`int` and `nat`.

**Mathematical interpretation.**
Every integer type is represented as an integer (i.e., an element of ℤ) together with a range of accepted values:

| Type    | Bound |
|---------|-------|
| `int`   | `(-∞, ∞)` (i.e., no bound) |
| `nat`   | `[0, ∞)` |
| `uN`    | <code>&#x5b;0, 2<sup>N</sup>)</code> |
| `iN`    | <code>&#x5b;-2<sup>N-1</sup>, 2<sup>N-1</sup>)</code> |
| `usize` | <code>&#x5b;0, 2<sup>usize::BITS</sup>)</code> |
| `isize` | <code>&#x5b;-2<sup>isize::BITS-1</sup>, 2<sup>isize::BITS-1</sup>)</code>  |

For `isize` and `usize`, assumptions of the platform word size (`usize::BITS`, or equivalently, `isize::BITS`) is configurable
via the [`global` directive](http://localhost:3000/reference-global.html#with-usize-and-isize).

**Spec equality.** Spec equality on integers is defined as integer equality.

**Literal expressions**
Spec code accepts integer literals both for standard types (`u8`, `i8`, etc.) and Verus-specific types (`nat` and `int`). 
Types are inferred for bare literals, but the types may be made explicit (e.g., `1u8` or `1nat`).

**Spec operators**

* Integer types are inter-covertible using [`as`-casts](./reference-as.md).
* Verus supports [standard arithmetic operators](./spec-arithmetic.md).
* Verus supports [bit arithmetic operators](./spec-bit-ops.md).

## Bool

**Mathematical interpretation.**
A `bool` is represented by a standard boolean value, `true` or `false`.

**Spec equality.** Spec equality on `bool` is defined by standard boolean equivalence.

**Literal expressions.** Both `true` and `false` are valid literals.

**Spec operators.**
Besides the standard `&&` and `||`, Verus supports some additional boolean operators that are
standard in logic, including [`implication and equivalence`](./reference-implication.md) (`==>`, `<==` and `<==>`) and [low-predence variations](./prefix-and-or.md) of conjunctions and disjunction.


## Char

**Mathematical interpreation.**
A `char` is interpreted as an [integer type](#integer-types) with a bespoke validity range:

| Type    | Bound |
|---------|-------|
| `int`   | `[0, 0xD7ff] ∪ [0xE000, 0x10FFFF]` |

This is consistent with the
[Rust definition of a `char`](https://doc.rust-lang.org/std/primitive.char.html)
as a "Unicode scalar value":

> A char is a ‘[Unicode scalar value](https://www.unicode.org/glossary/#unicode_scalar_value)’, which is any ‘[Unicode code point](https://www.unicode.org/glossary/#code_point)’ other than a [surrogate code point](https://www.unicode.org/glossary/#surrogate_code_point). This has a fixed numerical definition: code points are in the range 0 to 0x10FFFF, inclusive. Surrogate code points, used by UTF-16, are in the range 0xD800 to 0xDFFF.

**Spec equality.** For `char`, spec equality is defined as integer equality.

**Literal expressions.** Standard [`char` literals](https://doc.rust-lang.org/reference/tokens.html#character-literals) are accepted in spec code.

**Spec operators.** In spec code, a `char` is inter-covertible with the integer types using [`as`-casts](./reference-as.md).
This is more
permissive than exec code, which disallows many of these coercions.
As with other coercions, the result may be undefined if the integer being coerced does not
fit in the target range.

## Box (`Box<T>`)

**Mathematical interpretation.**
A `Box<T>` is interpreted identically to `T` with no additional metadata.

**Spec equality.**
Spec equality on `Box<T>` is inherited from spec equality on `T`.

**Spec operators.**
Boxing operations `Box::new` and unboxing operations (`*x`) are semantically the identity function.

## Shared reference (`&T`)

**Mathematical interpretation.**
A `&T` is interpreted identically to `T` with no additional metadata.

**Spec equality.**
Spec equality on `&T` is inherited from spec equality on `T`.

**Spec operators.**
Borrowing operations `&x` and dereferencing operations (`*x`) are semantically the identity function.

## Mutable reference (`&mut T`)

Our encoding for mutable references is based on the [RustHorn encoding](https://dl.acm.org/doi/10.1145/3462205).
See [the guide page](./mutable-references.md)
for practical information on using mutable references.

> **Note:** Verus used to treat mutable references very differently before 2026-05-03 release.
> See [the migration guide](https://github.com/verus-lang/verus/blob/main/source/docs/migration-mut-ref.md) for more information about the transition.


**Mathematical interpretation.**
A `&mut T` is interpreted as an abstract type.
It is guaranteed to be compatible with a surjective function `(&mut T) -> (T, *mut T, BorrowId)`.
At this time, there is no built-in support for explicitly reasoning about the pointer or about the "BorrowId".

**Spec equality.**
There is no extensional notion of equality for mutable references, and there is currently
no way to prove equality except via basic reflexivity.

This means that even if two mutables have the same current value, final value, and address,
they are not necessarily equal. In particular, a reborrow is not equal to the mutable borrow
it is borrowed from.
For two references to compare equal, they must originate from the same borrow instruction.

```rust
fn example() {
    let mut a = 0;
    let mut b = 0;

    let a_ref1 = &mut a;
    let a_ref2 = &mut a;

    assert(a_ref1 == a_ref1); // ok, basic reflexivity
    assert(a_ref1 == a_ref2); // not ok; these originate from different borrows
}
```

However, it is still not sufficient for two mutable references to originate from
the same point. Two snapshots taken at different times will compare unequal if 
the mutable reference was updated in between:

```rust
fn example2() {
    let mut a = 0;
    let a_ref = &mut a;

    let ghost snapshot1 = a_ref;
    let ghost snapshot2 = a_ref;

    *a_ref = 30;

    let ghost snapshot3 = a_ref;

    assert(snapshot1 == snapshot2); // ok, a_ref is unchanged between the two snapshots
    assert(snapshot1 == snapshot3); // not ok, a_ref was changed between the two snapshots
}
```

> **Note:** Equality of mutable references in spec code is not the same as equality of mutable references in exec code. In exec code, equality on mutable references is defined by equality on the referred-to values.

**Spec operators.**
In spec code, one reasons about a mutable reference `x: &mut T` through two key values:

 * `*x`: the current value behind the mutable reference.
 * `*final(x)`: the final value the mutable reference will point to when it expires.
   This value is considered [prophetic](./reference-attributes.md#verifierprophetic).

> **Note:** In postconditions, you may be required to write `*old(x)` instead of `*x`
> where `x: &mut T` is an input to the function.
> This has no meaning at a formal level;
> it is only used to prevent user confusion regarding which value `*x` refers to.

**Additional notes.**

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

## Raw Pointer (`*const T` and `*mut T`)

This page only discusses the raw pointer types.
See the [`raw_ptr`](https://verus-lang.github.io/verus/verusdoc/vstd/raw_ptr/index.html) vstd librararies for practical information on reasoning with pointers.

**Mathematical interpretation.**
In spec code, a pointer `ptr: *mut T` or `ptr: *const T` is defined as a triple of three
pieces of data:

 * `ptr.addr()` of type `usize`: The address of the pointer
 * `ptr@.metadata` of type [`<T as Pointee>::Metadata`](https://doc.rust-lang.org/std/ptr/trait.Pointee.html)
 * `ptr@.provenance` of abstract type [`Provenance`](https://verus-lang.github.io/verus/verusdoc/vstd/raw_ptr/struct.Provenance.html)

> **Note:** Verus treats `*const T` and `*mut T` identically. Though they differ
> in [variance](https://doc.rust-lang.org/reference/subtyping.html?#variance), this does
> not impact their mathematical, spec-level interpretation.
> Casting `*const T` to `*mut T` and vice versa is semantically a no-op.

**Spec equality.**
Two pointers are equal if the address, metadata, and provenance are equal.

> **Note:** Equality of pointers in spec code is not the same as equality of pointers in exec code.
> Exec comparisons only compare the address and metadata, while spec comparisons also compare provenance.

**Spec operators.**

 * `ptr.addr()`, `ptr@.metadata`, and `ptr@.provenance` can be used to obtain the constituent parts of a tuple.
 * [`ptr_from_data`](https://verus-lang.github.io/verus/verusdoc/vstd/raw_ptr/fn.ptr_from_data.html) can be used to build a pointer from its constituent parts.

## `String` and `str`

**Mathematical interpretation.**
`String` and `str` are each represented as an abstract type.
It is guaranteed that this type is consistent with a surjective `view` function
to <code>Seq&lt;<a href="#char">char</a>&gt;</code>.

> **Note:** In Rust, it is possible to obtain a `str` whose bytes do not form a valid UTF-8
> encoding, using, e.g., [`from_utf8_unchecked`](https://doc.rust-lang.org/std/string/struct.String.html#method.from_utf8_unchecked) or [`as_bytes_mut`](https://doc.rust-lang.org/std/string/struct.String.html#method.as_bytes_mut), though such functions are unsafe, and creating ill-formed strings can easily lead to UB. Verus does not currently support ill-formed strings, and thus `String`/`str` values are assumed to contain valid UTF-8.

**Spec equality.**
`String` and `str` do not exhibit extensional equality. To reason about equality, always
use the `view` function.

**Literal expressions.**
Verus supports [string literal expressions](https://doc.rust-lang.org/reference/tokens.html#grammar-STRING_LITERAL) in spec code.

> **Note:** The contents of string literals are opaque to the prover by default. Use [`reveal_strlit`](./reference-reveal-strlit.md) to expose the contents of a string literal.

**Spec operators.**

The primary spec operator for strings is the "view" operator, `s@` or `s.view()`.



## Slices and arrays


## Mode wrappers: `Ghost` and `Tracked`
