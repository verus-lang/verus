# Passing functions as values

In Rust, functions may be passed by value using the `FnOnce`, `FnMut`, and `Fn` traits.
Just like for normal functions, Verus supports reasoning about the preconditions
and postconditions of such functions.

### Reasoning about preconditions and postconditions

Verus allows you to reason about the preconditions and postconditions of function values
via two builtin spec functions: `call_requires` and `call_ensures`.

 * `call_requires(f, args)` represents the precondition.
    It takes two arguments: the function object and arguments
    as a tuple. If it returns true, then it is possible to call `f` with the given args.
 * `call_ensures(f, args, output)` represents the postcondition.
    It takes takes _three_ arguments: the function object, arguments, and return vaue.
    It represents the valid input-output pairs for `f`.

The `vstd` library also [provides aliases](https://verus-lang.github.io/verus/verusdoc/vstd/pervasive/trait.FnWithRequiresEnsures.html), `f.requires(args)` and `f.ensures(args, output)`.
These mean the same thing as `call_requires` and `call_ensures`.

As with any normal call, Verus demands that the precondition be satisfied 
when you call a function object.
This is demonstrated by the following example:

```rust
{{#include ../../../rust_verify/example/guide/higher_order_fns.rs:example1}}
```

As we can see, `test` calls `higher_order_fn`, passing in `double`.
The `higher_order_fn` then calls the argument with `50`. This should be allowed,
according to the `requires` clause of `double`; however, `higher_order_fn` does not have
the information to know this is correct.
Verus gives an error:

```
error: Call to non-static function fails to satisfy `callee.requires(args)`
  --> vec_map.rs:25:5
   |
25 |     f(50)
   |     ^^^^^
```

To fix this, we can add a precondition to `higher_order_fn` that gives information on
the precondition of `f`:

```rust
{{#include ../../../rust_verify/example/guide/higher_order_fns.rs:example2}}
```

The `(50,)` looks a little funky. This is a 1-tuple.
The `call_requires` and `call_ensures` always take tuple arguments for the "args".
If `f` takes 0 arguments, then `call_requires` takes a unit tuple;
if `f` takes 2 arguments, then it takes a pair; etc.
Here, `f` takes 1 argument, so it takes a 1-tuple, which can be constructed by using
the trailing comma, as in `(50,)`.

Verus now accepts this code, as the precondition of `higher_order_fn` now guarantees that
`f` accepts the input of `50`.

We can go further and allow `higher_order_fn` to reason about the _output_ value of `f`:

```rust
{{#include ../../../rust_verify/example/guide/higher_order_fns.rs:example3}}
```

Observe that the precondition of `higher_order_fn` places a constraint on the postcondition
of `f`.
As a result, `higher_order_fn` learns information about the return value of `f(50)`.
Specifically, it learns that `call_ensures(f, (50,), ret)` holds, which by `higher_order_fn`'s
precondition, implies that `ret % 2 == 0`.

### An important note

The above examples show the idiomatic way to constrain the preconditions and postconditions
of a function argument. Observe that `call_requires` is used in a _positive_ position,
i.e., "`call_requires` holds for this value".
Meanwhile `call_ensures` is used in a _negative_ position, i.e., on the left hand side
of an implication: "if `call_ensures` holds for a given value, this is satisfies this particular constraint".

It is very common to need a guarantee that `f(args)` will return one specific value,
say `expected_return_value`.
In this situation, it can be tempting to write,

```rust
requires call_ensures(f, args, expected_return_value),
```

as your constraint. However, **this is almost never what you actually want**,
and in fact, Verus may not even let you prove it.
The proposition `call_ensures(f, args, expected_return_value)`
says that `expected_return_value` is a _possible_ return value of `f(args)`;
however, it says nothing about _other_ possible return values.
In general, `f` may be nondeterministic!
Just because `expected_return_value` is one possible return
value does not mean it is only one.

When faced with this situation, **what you really want is to write**:

```rust
requires forall |ret| call_ensures(f, args, ret) ==> ret == expected_return_value
```

This is the proposition that you really want, i.e., "_if_ `f(args)` returns a value `ret`,
then that value is equal to `expected_return_value`".

Of course, this is flipped around when you write a postcondition, as we'll see in the
next example.

### Example: `vec_map`

Let's take what we learned and write a simple function, `vec_map`, which applies a given
function to each element of a vector and returns a new vector.

The key challenge is to determine the right specfication to use.

The signature we want is:

```rust
{{#include ../../../rust_verify/example/guide/higher_order_fns.rs:vec_map_signature}}
```

First, what do we need to **require**? We need to require that it's okay to call `f`
with any element of the vector as input.

```rust
{{#include ../../../rust_verify/example/guide/higher_order_fns.rs:vec_map_requires}}
```

Next, what ought we to **ensure**? Naturally, we want the returned vector to have the same
length as the input. Furthermore, we want to guarantee that any element in the output
vector is a possible output when the provided function `f` is called on the corresponding
element from the input vector.

```rust
{{#include ../../../rust_verify/example/guide/higher_order_fns.rs:vec_map_ensures}}
```

Now that we have a specification, the implementation and loop invariant should
fall into place:

```rust
{{#include ../../../rust_verify/example/guide/higher_order_fns.rs:vec_map}}
```

Finally, we can try it out with an example:

```rust
{{#include ../../../rust_verify/example/guide/higher_order_fns.rs:vec_map_example}}
```

### Conclusion

In this chapter, we learned how to write higher-order functions with higher-order specifications,
i.e., specifications that constrain the specifications of functions that are passed
around as values.

All of the examples from this chapter passed functions by referring to them directly by name,
e.g., passing the function `double` by writing `double`.
In Rust, a more common way to work with higher-order functions is to pass _closures_.
In the next chapter, we'll learn how to use closures.
