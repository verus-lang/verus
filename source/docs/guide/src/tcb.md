# Assumptions and trusted components

Often times, it's not possible to verify every line of code and some things need to be
_assumed_. In such cases, the ultimate correctness of the code is dependent not just
on verification but on the assumptions being made.

Assumptions can be introduced through the following mechanisms:

 * As [`assume`](./requires_ensures.md) statement
 * An axiom - any proof function introduced with `#[verifier::external_body]`
 * An axiomatic specification - any exec function introduced with `#[verifier::external_body]` or `#[verifier::external_fn_specification]`
 * `#[verifier::external]` (See below.)

Types (structs and enums) can also be marked as `#[verifier::external_body]`,
though to be pedantic, this does not introduce a new assumption _per se_.
In practice, though, such types are usually associated with additional assumptions
to make them useful.

### The `#[verifier::external]` attribute

The `#[verifier::external]` annotation tells Verus to ignore an item entirely.
It can be applied to any item - a function, trait, trait implementation, type, etc.

For many items (functions, types, trait declarations), this does not, _on its own_,
introduce any new "assumptions" about that item.
Attempting to call an `external` function from a verified
function, for example, will result in an error from Verus. In practice, a developer
will often call an `external` function (say `f`) from an `external_body` function (say `g`),
in which case, the `external_body` attribute introduces assumptions about `g`, thus
_indirectly_ introducing assumptions about `f`.

Furthermore, adding `#[verifier::external]` to a _trait implementation_ requires even more
careful consideration, as Verus relies on rustc's trait-checking for some things,
so trait implementations can sometimes affect what code gets accepted or rejected.

For example:

```rust
#[verifier::external]
unsafe impl Send for X { }
```
