# Dust: equality and references support and encoding

Andrea Lattuada, June 2nd 2021

In the document I will refer to both `struct`s and `enum`s as "algebraic data types", adts in short. For the sake of writing non-contrived examples, we are going to assume that we have chosen a design for "mathematical" sequences that's similar to dafny's sequences.

## Design dimensions

When designing the interface and encoding of equality and reference support for Dust, we need to consider both (a) the user facing language and diagnostics, and (b) the encoding to _z3_ (via _air_).

### Language

Rust uses the `PartialEq` and `Eq` trait to define the `==` (`.eq`) operator for types that implement them. An `==` implementation however does not necessarily conform to structural equality. `Eq` is implemented for `Cell`, but `Cell` has interior mutability (with an unsafe implmentation).

If the programmer uses `#[derive(PartialEq, Eq)]` for an adt without interior mutability, and all the recursively enclosed types have the same property, they obtain an `==` implementation that is structural equality. The built-in `StructuralEq` trait marks those adts where the `==` was automatically derived to be structural equality, but this property is shallow, and does not say anything about whether the enclosed types don't have interior mutability and have structural `==`.

The user needs to know, and sometimes affirm, when a type can be treated as immutable (lacking interior mutability) for the purpose of encoding; additionally, depending on the encoding, it may be important to distinguish between types that have structural equality and those that have an immutable api, but do not have structural equality, like `Vec<int>` (with the exception of `Vec::capacity` and related functions).

We also need to determine whether and how to support verifying the bodies functions for types that have an immutable api but do not have structural equality, e.g. `Vec<int>`. We may decide to restrict this support to the safe interior mutability mechanisms provided by the standard library (`Cell`, `RefCell`, `Mutex`, ...).

### Encoding

#### Adts with structural equality

Adts that only contain primitive types (possibly by means of other adts with the same property) can always have an equality implementation that conforms to smt equality (with structural equality). These can be encoded as _air_ datatypes, like in the following example:

```rust
#[derive(PartialEq, Eq)]
struct Thing { a: int, b: bool }
...
let t = Thing { a: 12, b: true };
```

```
(declare-datatypes () ((Thing (Thing/Thing (Thing/Thing/a Int) (Thing/Thing/b Bool)))))
...
(declare-const t@ Thing)
(assume
 (= t@ (Thing/Thing 12 true))
)
```

For these types, if the `==` implementation is structural equality, we can encode `==` to smt equality:

```rust
affirm(Thing { a: 12, b: true } != Thing { a: 14, b: true });
```

```
(assert
 "<span>" (req%affirm (not (= (Thing/Thing 12 true) (Thing/Thing 14 true)))))
```

This encoding is however unsound in general for any other adt, for example, for the following struct:

```rust
#[derive(Eq)]
struct Custom { a: int }

impl std::cmp::PartialEq for Custom {
    fn eq(&self, other: &Self) -> bool {
        self.a == other.a + 1
    }
}
```

This also extends to generic adts whenever the type parameters also have equality that conforms to smt equality (with structural equality).

```rust
#[derive(PartialEq, Eq)]
struct Foo<A> { a: A, b: bool }
```

In this example `==` of `Foo<Thing>` would conform to smt equality, but `Foo<Custom>` would not.

#### Adts that have interior mutability (and/or raw pointers) but expose an "immutable" interface

This set of types can also be defined those adts that do _not_ have well-defined structural equality (i.e. where at least one of the fields has interior mutability, is a raw pointer, or is another adt that recursively contains these) but "hide" the interior mutability in their public interface, and act like "immutable" types. 

`RefCell` is not one such type, as one can change its value while holding a shared reference. The following is such a (slightly contrived) type:

```rust
struct List {
  contents: RefCell<Box<[u64]>>,
}

impl List {
  /// Makes an empty List
  pub fn new() -> List {
    List { contents: RefCell::new(Box::new()) }
  }

  /// Push an item at the end of the list
  pub fn push(&mut self, v: u64) {
    let borrowed = self.contents.borrow_mut();
    // use borrowed to reallocate the boxed slice, and copy data over
  }
  
  /// Get the item at position i, or None if it doesn't exist
  pub fn get(&self, i: usize) -> Option<u64> {
    self.contents.borrow().get(i)
  }
}
```

Again, we treat generic adts as having this property if the type parameters have at least structural equality. The design needs to clarify whether there's a difference between "immutable" adts with generic arguments that have structural equality and those with generic arguments that are themselves "immutable" adts.

Possibly with the exception of `Vec::capacity` and related methods, `Vec<T>` is a type that satisfies this property, when `T` is either structural (`Vec<Thing>`) or "immutable" (`Vec<Vec<Thing>>`).

## Using _traits_ to strengthen a function's or type's spec

The rust standard library sometimes uses ("marker") traits to denote that a certain type has a specific property, potentially that a certain function has a stronger (more restrictive) specification. One example is `stc::cmp::Eq`: this trait does not define any new functions, but types implementing it promise that the `PartialEq::eq` (`==`) implementation is an equivalence relation: in addition to it being symmetric and transitive (as required by `PartialEq`), `Eq` asserts that `==` is also reflexive. Another example is `std::marker::Send` and `std::marker::Sync`, which asserts that a type is can be safely transferred across thread boundaries, and that it's one for which it's safe to share references across threads, respectively.

As described in the following section(s), we plan on leaning on this to extend the specification for `==` to, e.g., structural equality, for the types that conform to it.

## The `builtin::Structural` trait, and visibility

Because the `std::marker::StructuralEq` reflects only shallow structural equality, we add a verifier-specific marker trait, `builtin::Structural`, which can only be implemented for an adt if its `==` implementation conforms to structural equality. Adts that implement this trait are encoded as `air` datatypes, and `==` for these types is encoded as smt equality, whenever all of their fields are visible in the current scope; if at least _one_ of the fields is not visible, the encoding will be opaque, as discussed later.

The `trait builtint::Structural` can be implemented by the user, and the verifier checks that the type can indeed recursively conform to structural equality, and that the `==` implementation matches. If there are type parameters, these must also restricted to implement `builtin::Structural`. A `derive` macro is provided, so that the user can write:

```rust
#[derive(PartialEq, Eq, Structural)]
struct Thing<T> {
  value: T,
}
```

The following derived `Structural` implementation would match the following:

```rust
impl<T: builtin::Structural> builtin::Structural for Thing<T> { }
```

## `builtin::Structural` types with non-visible fields

When referencing a `Structural` type from a separate module where some of the fields are not visible (not `pub`/ `pub(crate)`), we encode the entire type as an opaque z3 "sort".

## `builtin::Immutable`, `builtin::ImmutableEq` for adts that (may) have interior mutability (and/or raw pointers) but expose an "immutable" interface

When a type may have interior mutability, but exposes an "immutable" interface (through its entire API), the user can mark it `Immutable`. Additionally, the trait `builtin::ImmutableEq` asserts that `==` conforms to "mathematical" (smt) equality. `Immutable` is required for `ImmutableEq`.



---



## The `builtin::View` trait, and `builtin::ViewEq`

In general, specifications for public functions of a type should be written in terms of an abstract representation of the type's contents. A `Vec<u64>` should be represented just as a sequence (maybe, a slice) of integers; by default none of the facts necessary to prove the implementation should leak into the publicly visible specification of the interface. In our experience with _Veribetrfs_, inadvertently exposing internal invariants and properties is one of the common causes of long verification times and timeouts; this is because the solver has access to facts internal to the implementations that are irrelevant but can still be selected and cause qunatifier triggers to fire.

With the exception of very simple ADTs that have all public fields and implement `Structural`, the abstract representation of a type must be specified by implementing the `View` trait:

```rust
trait View {
  type View : std::marker::StructEq;
  
  #[spec]
  fn view(&self) -> Self::View { unimplemented!() }
}
```

So, for `Vec`, we'd implement `View` as something like:

```rust
impl<T: builtin::StructEq> builtin::View for Vec<T> {
  type View = [T]; // (a sequence of T's)
}
```

The specification for `Vec::push` and `Vec::get` can then be along the lines of:

```rust
pub fn push(&mut self, value: T) {
  ensures(self.view() == old(self).view() + [value]);
```

```rust
pub fn get(&self, index: usize) -> Option<T> {
 	ensures(result == self.view()[index]);
```

Note that we did not provide an implementation for the `view` function. Generally speaking, `.view()` is unaffected by functions on the type that take immutable references. We are still working out the details on when `.view()` should be havoc'd.

The `builtin::ViewEq` trait indicates that the equality implemented by `==` matches view equality, which is always structural equality of the `View`. `builtin::ViewEq` is an `unsafe` trait, as the verifier generally cannot check whether `==` matches view equality. There are two ways of imlpementing `ViewEq`:

1. The user can manually write `unsafe impl builtin::ViewEq for T`, and this becomes part of the TCB. The `unsafe` keyword allows easy inspection.
2. The user can use a derive macro to `#[derive(ViewEq)]` the implementation for a type that also implements `View`. In this case the verifier will check that `a == b` $ \Leftrightarrow $ `a.view() == b.view()`.

Implementing `View` also requires that the view does **not** change except for when we have `mut` or `&mut T`: to start this is trivially enforced by having `View` require `Immutable` or `Structural`.

## Immutable references, `&_ T`



Control havoc-ing with the `builtin::Immutable` trait. `StructEq` implies `Immutable` and `View` requires `Immutable`?



## TODO

* [ ] When to havoc `.view()`
* [ ] What about `Vec<T>` where `T` is "immutable"
* [ ] What about `Vec<T>` where `T` has interior mutability -- punt on this?
* [ ] `Hash`
* [x] Auto-`opaque`

