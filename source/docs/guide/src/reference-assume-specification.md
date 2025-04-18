# assume_specification

The `assume_specification` directive tells Verus to use the given specification for the given function.
Verus assumes that this specification holds **without proof**.

It can be used with any `exec`-mode function that Verus would otherwise be unaware of; for example,
any function marked [`external`](./reference-attributes.md#verifierexternal) or which is imported from an external crate.

It is similar to having a function which is `external_body`; the difference is that when `assume_specification` is used, the specification is separate from the function declaration
and body.

The `assume_specification` declaration does NOT have to be in the same module or crate
as its corresponding function. However:
 * The function must be visible to its `assume_specification` declaration
 * The `assume_specification` declaration must be visible wherever the function is visible.

The general form of this directive is:

<pre>
<code class="hljs">assume_specification <span style="color: #800000; font-style: italic">generics</span><sup>?</sup> [ <span style="color: #800000; font-style: italic">function_path</span> ] (<span style="color: #800000; font-style: italic">args...</span>) -&gt; <span style="color: #800000; font-style: italic">return_type_and_name</span><sup>?</sup>
    <span style="color: #800000; font-style: italic">where_clause</span><sup>?</sup>
    <span style="color: #800000; font-style: italic">requires_clause</span><sup>?</sup>
    <span style="color: #800000; font-style: italic">ensures_clause</span><sup>?</sup>
    <span style="color: #800000; font-style: italic">returns_clause</span><sup>?</sup>
    <span style="color: #800000; font-style: italic">invariants_clause</span><sup>?</sup>
    <span style="color: #800000; font-style: italic">unwind_clause</span><sup>?</sup>
    ;
</code>
</pre>

It is intended to look like an ordinary Rust function signature with a [Verus specification](./reference-exec-signature.md), except instead of having a name, it refers to a different function by path.

For associated functions and methods, the <code><span style="color: #800000; font-style: italic">function_path</span></code> should have the form `Type::method_name`,
using "turbofish syntax" for the type (e.g., `Vec::<T>`).
For trait methods, the <code><span style="color: #800000; font-style: italic">function_path</span></code> should use the "qualified self" form, `<Type as Trait>::method_name`.

The signature must be the same as the function in question, including arguments, return type, generics, and trait bounds.
All arguments should be named and should _not_ use `self`.

### Examples

To apply to an ordinary function:

```rust
pub assume_specification<T> [core::mem::swap::<T>] (a: &mut T, b: &mut T)
    ensures
        *a == *old(b),
        *b == *old(a),
    opens_invariants none
    no_unwind;
```

To apply to an associated function of `Vec`:

```rust
pub assume_specification<T>[Vec::<T>::new]() -> (v: Vec<T>)
    ensures
        v@ == Seq::<T>::empty();
```

To apply to an method of `Vec`:

```rust
pub assume_specification<T, A: Allocator>[Vec::<T, A>::clear](vec: &mut Vec<T, A>)
    ensures
        vec@ == Seq::<T>::empty();
```

To apply to `clone` for a specific type:

```rust
pub assume_specification [<bool as Clone>::clone](b: &bool) -> (res: bool)
    ensures res == b;
```
