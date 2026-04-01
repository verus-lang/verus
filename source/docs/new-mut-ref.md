# Feature status

The content in this document applies only to Verus's **experimental** new mutable reference support,
which can be enabled with the Verus command line option `-V new-mut-ref`.

If you're familiar with the old design, see [migration-mut-ref.md](./migration-mut-ref.md)
for more information on the transition and migration issues.

# Mutable references

For simple uses of mutable references—i.e., within a single function, and without involving
loops—Verus's proof strategy can usually track mutable references precisely and without much trouble. 
For example:

```rust
fn example1() {
    let mut a = 0;
    let a_ref = &mut a;

    *a_ref = 5;

    assert(a == 5);
}
```

Or:

```rust
fn example1() {
    let mut a = Some(0);

    match a {
        Some(inner_ref) => {
            // Obtain a reference to the contents of the Option
            *inner_ref = 20;
        }
        None => { }
    }

    assert(a == 20);
}
```

For more complex examples, we often need to write specifications about mutable references.
In the rest of the section, we'll see how to do that.

## Function specifications

One of the most common ways to work with mutable references is to have a function taking
a mutable reference as an argument. In this case, we usually need a specification that relates
the "input" value (i.e., the value behind the reference at the beginning of the function)
to the "output" (i.e., the value behind the reference at the end of the function).

```rust
fn add_1(x: &mut u8)
    requires *x < 255
    ensures *final(x) == *old(x) + 1
{
    *x += 1;
}
```

In the precondition, we use `*x` to refer to the value behind the mutable reference at the
beginning of the function. (In this case, we use the precondition to prevent overflow from the
addition operator.)
In the postcondition, we refer to both the input value (via `old`) and the output value
(via `final`).

> **Aside: Could we just use `*x` in the postcondition?**
> 
> Strictly speaking, `*x` in a specification will always refer to the value pointed to by `x`
> at the _beginning_ of the function.
> This is because `x` is an input parameter, so just like any other input parameter, it is always
> evaluated with respect to its value at call time.
>
> However, we also anticipate that this might be confusing to the untrained eye—intuitively,
> one might expect `*x` to refer to the updated value when it is used in the postcondition.
> Thus, Verus currently requires the developer to disambiguate by writing `old(x)`.
>
> _Historically_, Verus did once allow `*x` in the postcondition, where it referred to the updated
> value. However, this special case turned out to be incompatible with the formal theory
> that Verus later adopted, so this feature was removed.

## Returning mutable borrows

Let's do a more complex example, with a function that _returns_ a mutable reference.
Specifically, let's write a function that takes a `&mut (A, B)` as input and return a mutable
reference to the first field: `&mut A`.

```rust
fn get_mut_fst<A, B>(pair: &mut (A, B)) -> (ret: &mut A)
    requires ???
    ensures ???
{
    &mut pair.0
}

fn test() {
    let mut p = (10, 20);

    let r = get_mut_fst(&mut p);
    *r = 100;

    assert(p == (100, 20));
}
```


## Specs about borrowed data

You might wonder what happens if you try to access a variable in spec code while it's borrowed.

```rust
fn main() {
    let mut x = 0;
    let x_ref = &mut x;

    assert(x == 0); // ??? Will this pass?

    *x_ref = 20; 
}
```

Actually, Verus forbids this, treating it similarly to a borrow error.

```
error[E0502]: cannot borrow `(Verus spec x)` as immutable because it is also borrowed as mutable
  --> simple_test.rs:9:12
   |
 7 |     let x_ref = &mut x;
   |                 ------ mutable borrow occurs here
 8 |
 9 |     assert(x == 0); // ??? Will this pass?
   |            ^ immutable borrow occurs here
10 |
11 |     *x_ref = 20;
   |     ----------- mutable borrow later used here

error: aborting due to 1 previous error
```

The phrasing of the error message might be a little cryptic; what it's trying to say is that you can't read `x`, not even in `spec` code, because `x` is currently borrowed as mutable. The reason for the phrasing of the error message has to do with how Verus checks for this. (Verus literally injects an artificial variable called `Verus spec x` into the borrow-checking pass and forces it to be borrowed for the same lifetime as `x`.)

However, there **is** still a way to read from the value of `x`, by using the Verus builtin operator `after_borrow`. This operator allows you to read a local variable at any time, but it always gives you the value `x` _will_ have after its outstanding borrows expire. Working with this can often be a little unintuitive, and it is mainly useful for advanced situations.

For example, `after_borrow(x)` can be read even before the borrow expires:

```rust
fn main() {
    let mut x = 0;
    let x_ref = &mut x;

    assert(after_borrow(x) == after_borrow(x));

    *x_ref = 20; 
}
```

And in this particlar example, it is equal to 20:

```rust
fn main() {
    let mut x = 0;
    let x_ref = &mut x;

    *x_ref = 20; 

    assert(after_borrow(x) == 20);
}
```

However, the fact that is equal to 20 is not known until after the assignment occurs.
So this doesn't work:

```rust
fn main() {
    let mut x = 0;
    let x_ref = &mut x;

    assert(after_borrow(x) == 20); // FAILS

    *x_ref = 20; 
}
```

But you _can_ take a ghost snapshot of `after_borrow(x)` and learn that is equal to 20 later:

```rust
fn main() {
    let mut x = 0;
    let x_ref = &mut x;

    // You can read 'after_borrow(x)' even before the borrow expires ...
    let ghost after_borrow_x = after_borrow(x);

    *x_ref = 20; 

    // ... but you only learn that it is equal to 20 after the assignment is done.
    assert(after_borrow_x == 20);
}
```

This might seem a little pointless—so `after_borrow` lets you read the value of `x` before the
borrow is complete, but it seems to be meaningless until _after_ the borrow is complete.
However, this is, in fact, essential to understanding how Verus reasons about mutable borrows.


