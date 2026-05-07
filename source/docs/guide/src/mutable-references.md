# Mutable references

For simple uses of mutable references—i.e., within a single function, and without involving
loops—Verus's proof strategy can usually track mutable references precisely and without much trouble. 
For example:

```rust
fn example_basic() {
    let mut a = 0;
    let a_ref = &mut a;

    *a_ref = 5;

    assert(a == 5);
}
```

Or:

```rust
fn example_pattern() {
    let mut a = Some(0);

    match &mut a {
        Some(inner_ref) => {
            // Obtain a reference to the contents of the Option
            *inner_ref = 20;
        }
        None => { }
    }

    assert(a === Some(20));
}
```

For more complex examples, we often need to write specifications about mutable references.
In the rest of the section, we'll see how to do that.

## Function specifications

One of the most common ways to work with mutable references is to have a function that takes
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

fn get_mut_fst_test() {
    let mut p = (10, 20);

    let r = get_mut_fst(&mut p);
    *r = 100;

    assert(p === (100, 20));
}
```

Think for a moment about how you might write a specification for `get_mut_fst`.
This is a little more challenging because the "final" value of `pair.0` isn't known concretely at
the end of the function. Instead, this value can be mutated by the caller who can
manipulate the returned mutable reference, `ret`.
Therefore, the final value of `pair` needs to be _expressed in terms of_ the final value of `ret`.

Verus accepts the following specification for `get_mut_fst`, which can be used to prove `get_mut_fst_test`:

```rust
fn get_mut_fst<A, B>(pair: &mut (A, B)) -> (ret: &mut A)
    ensures
        *ret == old(pair).0,
        *final(pair) == (*final(ret), old(pair).1),
{
    &mut pair.0
}
```

Note that, even though `final(ret)` and `final(pair)` cannot be known concretely
at the end of this function (they are not known until the caller is finished with `ret`,
e.g., after the `*r = 100;` line in `get_mut_fst_test`),
this _relation_ between `final(ret)` and `final(pair)` is known.

To prove `get_mut_fst_test`, Verus reasons roughly as follows:

```rust
fn get_mut_fst_test() {
    let mut pair = (10, 20);

    let r = get_mut_fst(&mut pair);
    //                  ^^^^^^^^^ refer to this value as `pair_ref`, of type `&mut (u64, u64)`
    //
    // From the postcondition of `get_mut_fst` we know that:
    //    *final(pair_ref) == (*final(r), 20)

    *r = 100;

    // Now we we know that:
    //    *final(r) == 100
    // So:
    //    *final(pair_ref) == (100, 20)

    // Finally, since `pair_ref` was borrowed from `pair`, and the borrow has expired
    // at this point, we can deduce that:
    assert(pair == (100, 20));
}
```

## More examples

Here are a few more examples of functions that return mutable references.

**Returning multiple mutable references:**

```rust
fn pair_split<T, U>(pair: &mut (T, U)) -> ((fst, snd): (&mut T, &mut U))
    requires
    ensures
        *fst == old(pair).0,
        *snd == old(pair).1,
        *final(pair) == (*final(fst), *final(snd))
{
    (&mut pair.0, &mut pair.1)
}

fn pair_split_test() {
    let mut pair = (1, 2);
    let (fst, snd) = pair_split(&mut pair);
    *fst = 10;
    *snd = 20;

    assert(pair === (10, 20));
}
```

**Indexing into a vector:**

```rust
fn vec_index_mut<T>(vec: &mut Vec<T>, i: usize) -> (element: &mut T)
    requires
        0 <= i < vec.len(),
    ensures
        *element == old(vec)@[i as int],
        final(vec)@ == old(vec)@.update(i as int, *final(element)),
{
    &mut vec[i]
}

fn vec_index_mut_test() {
    let mut v = vec![10, 20];
    *vec_index_mut(&mut v, 1) = 200;

    assert(v.len() == 2);
    assert(v[0] == 10);
    assert(v[1] == 200);
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

The phrasing of the error message might be a little cryptic; what it's trying to say is that you can't read `x`, not even in `spec` code, because `x` is currently borrowed as mutable.
(The reason for the phrasing of the error message has to do with how Verus checks for this. Verus literally injects an artificial variable called `Verus spec x` into the borrow-checking pass and forces it to be borrowed for the same lifetime as `x`.)

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

The expression `after_borrow(x)`, much like `*final(x_ref)`, is not concretely known at this point.

```rust
fn main() {
    let mut x = 0;
    let x_ref = &mut x;

    assert(after_borrow(x) == 20); // FAILS

    *x_ref = 20; 

    assert(after_borrow(x) == 20); // ok
}
```

However, much like in the specifications above, we can still describe relations between
the non-concrete values:

```rust
fn main() {
    let mut x = 0;
    let x_ref = &mut x;

    assert(after_borrow(x) == *final(x_ref));

    *x_ref = 20; 
}
```

Now, let's see how to apply this knowledge.

## Working with loops

Using `after_borrow` to relate local variables to mutable references can be particularly
useful when you need to write loop invariants.

Let's do a toy example first.

Consider this (trivial) loop:

```rust
fn loop_test() -> (r: u64)
    ensures r == 30,
{
    let mut a = 0;
    let a_ref = &mut a;

    loop
        decreases 0nat
    {
        *a_ref = 30;
        return a;
    }
}
```

This fails due to the presence of the loop, which causes Verus to lose track of the relation
between `a` and `a_ref`. We just need to supply the relevant fact in the loop invariant.

```rust
fn loop_test() -> (r: u64)
    ensures r == 30,
{
    let mut a = 0;
    let a_ref = &mut a;

    loop
        invariant after_borrow(a) == *final(a_ref),
        decreases 0nat
    {
        *a_ref = 30;
        return a;
    }
}
```

## The `has_resolved` operator: When mutable references are "done"

How does Verus know when a mutable borrow is "complete"?
As we've seen, the creation of a mutable borrow lets us immediately reason about the
"final" value of the mutable borrow, but it doesn't become concrete until some later program
point. What exactly is that point?

For any mutable reference, we say that it is "resolved" if we have reached a program point
from which that reference will never be modified again.

```rust
fn main() {
    let mut x = 0;
    let x_ref = &mut x;
    *x_ref = 20; 
    *x_ref = 30;

    // `x_ref` is resolved at this point

    assert(x == 30);
}
```

Verus provides the `has_resolved` operator to reason about this directly.

```rust
fn main() {
    let mut x = 0;
    let x_ref = &mut x;

    assert(has_resolved(x_ref)); // fails

    *x_ref = 20; 

    assert(has_resolved(x_ref)); // fails

    *x_ref = 30;

    assert(has_resolved(x_ref)); // ok

    assert(x == 30);
}
```

To determine where `x_ref` is resolved,
Verus uses a reachability analysis that considers all program points that assign to `*x_ref`.
Usually, this works seamlessly under the hood to ensure that data from a mutable reference
makes it way back to the borrowed-from location. In more advanced situations (especially dealing
with containers of mutable references, like `(&mut T, &mut T)` or `Vec<&mut T>`), it helps
to be aware of this concept.

With the `has_resolved` operator introduced, we can fully dissect the above program to understand
how Verus confirms the assertion `x == 30`.
First, we need to be be aware that `has_resolved(x_ref) ==> *x_ref == *final(x_ref)`,
i.e., "if `x_ref` will never be modified after this point, then its current value must equal its final value".

With this, Verus reasons as follows:

```rust
fn main() {
    let mut x = 0;
    let x_ref = &mut x;

    // When taking a mutable reference, we get:
    // after_borrow(x) == *final(x_ref)

    *x_ref = 20; 
    *x_ref = 30;

    // Here we have:
    //     has_resolved(x_ref)
    // so:
    //     *x_ref == *final(x_ref)
    //
    // And of course, at this point, we have:
    //     *x_ref == 30

    // Putting all these together we get `after_borrow(x) == 30`

    // At this point, the borrow is expired, and we can refer directly to `x`:
    assert(x == 30);
}
```

The `has_resolved` operator can be applied to any variable, not just mutable references.
This is useful for containers that contain (or might contain) mutable references.
When applied to a tuple, struct, or enum, `has_resolved` means that all _nested_ mutable
references have been resolved. Such properties are provided by axioms like the following:

 * `has_resolved::<(T, U)>((t, u)) ==> has_resolved::<T>(t) && has_resolved::<U>(u)`
 * `has_resolved::<Vec<T>>(vec) ==> has_resolved::<T>(vec[i])`

## Advanced application: Building a list

Finally, let's do a more complex example to really get deeper into the mindset of
thinking about mutable references in terms of the relationships between the "final values".

Specifically, we'll see how mutable references can be used to build up a cons-list
"from the root down", and how to verify it.
The code maintains the invariant that `cur` points at the `Nil` entry at the tail of the list, and each iteration replaces the `Nil` with a `Cons(0, Nil)`. Thus, in each iteration, the list is extended by one element from the bottom, and at the end, `list` will be a list of length `len`.

```rust
enum List {
    Cons(u64, Box<List>),
    Nil,
}

fn build_zero_list(len: u64) {
    let mut list = List::Nil;
    let mut cur = &mut list;

    let mut i = 0;
    while i < len {
        *cur = List::Cons(0, Box::new(List::Nil));

        match cur {
            List::Cons(_, b) => {
                // Replace `cur` with a reference to the newly-created List::Nil,
                // the child of the previous `cur`.
                cur = &mut *b;
            }
            _ => { /* unreachable */ }
        }

        i += 1;
    }

    return list;
}
```

We start with the list (`list`) equal to `Nil` and take a reference to it (`cur`).
At each step, we replace the value pointed-to by `cur` with a `Cons` node, and then move
the reference down to the child.
Note that in this program, we both write through the cur pointer (to `*cur = ...`),
_and_ we overwrite the pointer itself (`cur = ...`).
Here, for example, we depict the state of the program at the beginning and through
the first two iterations:

<center>
<img src="graphics/mut-ref-cons-example-1.png" alt="At step 1, we have list = Nil, where cur points to Nil. At step 2, we have list = Cons, which points to Nil, and cur points to Nil. At step 3, we have list = Cons, which points to Cons, which points to Nil, and cur points to Nil. And so on.">
</center>

Now, let's verify this program; in particular, let us prove that the list at the end
has length equal to the input argument, `len`.

Thus, our primary goal is to prove something about the value of `list` after the initial
borrow (`cur = &mut list`) expires. 
The key to proving this is to observe that,
as the program progresses through the loop, the shape of this value
becomes more and more "concrete".

 * At the beginning of the loop, `cur` is borrowed from `list`. At this point, we have the
   freedom to set `*cur` to anything we want, so we don't know anything about the final value
   of `list`.
 * After one iteration, we've assigned that location to be a `Cons` node and replaced
   our `cur` reference with a reference to its child.
   That `Cons` node is now "set in stone"; we don't have a reference to it anymore,
   but we still have the freedom to set the child to whatever we want.
 * And so on.

<center>
<img src="graphics/mut-ref-cons-example-2.png" alt="At step 1, we have after_borrow(list) = the unknown final(cur),. At step 2, we have list = Cons, which points to the unknown final(cur). At step 3, we have list = Cons, which points to Cons, which points to the unknown final(cur). And so on.">
</center>

Only when the last iteration finishes and `cur` expires for good, do we learn that the
last node is "nil" and the list becomes fully concrete.

Now, this picture suggests that we can prove the program correct by writing an invariant
which relates `final(cur)` to `final(list)`.
Specifically, we can say that `final(list)` will always be equal to `final(cur)` with
`i` "Cons" nodes added to the top.

```rust
enum List {
    Cons(u64, Box<List>),
    Nil,
}

spec fn append_zeros(n: nat, list: List) -> List
    decreases n
{
    if n == 0 {
        list
    } else {
        append_zeros((n-1) as nat, List::Cons(0, Box::new(list)))
    }
}

fn build_zero_list(len: u64) -> (list: List)
    ensures list == append_zeros(len as nat, List::Nil),
{
    let mut list = List::Nil;
    let mut cur = &mut list;

    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            *cur == List::Nil,
            after_borrow(list) == append_zeros(i as nat, *final(cur)),
        decreases len - i
    {
        *cur = List::Cons(0, Box::new(List::Nil));

        match cur {
            List::Cons(_, b) => {
                // Replace `cur` with a reference to the newly-created List::Nil,
                // the child of the previous `cur`.
                cur = &mut *b;
            }
            _ => { /* clearly unreachable */ }
        }

        i += 1;
    }

    return list;
}
```

