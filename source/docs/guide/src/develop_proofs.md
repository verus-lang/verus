# Using assert and assume to develop proofs

In [an earlier chapter](./spec_lib.md), we started with an outline of a proof:

```rust
{{#include ../../../rust_verify/example/guide/lib_examples.rs:lemma_len_intersect_fail}}
```

and then filled in the crucial missing steps to complete the proof.
It didn't say, though,
how you might go about discovering which crucial steps are missing.
In practice, it takes some experimentation to fill in this kind of proof.

This section will walk through a typical process of developing a proof,
using the proof outline above as a starting point.
The process will consist of a series of queries to Verus and the SMT solver,
using `assert` and `assume` to ask questions,
and using the answers to narrow in on the cause of the verification failure.

If we run the proof above, Verus reports an error:

```
error: postcondition not satisfied
   |
   |           s1.intersect(s2).len() <= s1.len(),
   |           ---------------------------------- failed this postcondition
```

This raises a couple questions:
- Why is this postcondition failing?
- If this postcondition succeeded, would the verification of the whole function succeed?

Let's check the second question first.  We can simply assume the postcondition and see what happens:

```rust
pub proof fn lemma_len_intersect<A>(s1: Set<A>, s2: Set<A>)
    ...
{
    if s1.is_empty() {
    } else {
        let a = s1.choose();
        lemma_len_intersect::<A>(s1.remove(a), s2);
    }
    assume(s1.intersect(s2).len() <= s1.len());
}
```

In this case, verification succeeds:

```
verification results:: verified: 1 errors: 0
```

There are two paths through the code, one when `s1.is_empty()` and one when `!s1.empty()`.
The failure could lie along either path, or both.
Let's prepare to work on each branch of the `if`/`else` separately
by moving a separate copy the `assume` into each branch:

```rust
{
    if s1.is_empty() {
        assume(s1.intersect(s2).len() <= s1.len());
    } else {
        let a = s1.choose();
        lemma_len_intersect::<A>(s1.remove(a), s2);
        assume(s1.intersect(s2).len() <= s1.len());
    }
}
```
```
verification results:: verified: 1 errors: 0
```

Next, let's change the first `assume` to an `assert` to see if it succeeds in the `if` branch:

```rust
{
    if s1.is_empty() {
        assert(s1.intersect(s2).len() <= s1.len());
    } else {
        let a = s1.choose();
        lemma_len_intersect::<A>(s1.remove(a), s2);
        assume(s1.intersect(s2).len() <= s1.len());
    }
}
```

```
error: assertion failed
   |
   |         assert(s1.intersect(s2).len() <= s1.len());
   |                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ assertion failed
```

In the `s1.is_empty()` case, we expect `s1.len() == 0` (an empty set has cardinality 0).
We can double-check this with a quick assertion:

```rust
{
    if s1.is_empty() {
        assert(s1.len() == 0);
        assume(s1.intersect(s2).len() <= s1.len());
    } else {
        ...
    }
}
```
```
verification results:: verified: 1 errors: 0
```

So what we need is `s1.intersect(s2).len() <= 0`.
If this were true, we'd satisfy the postcondition here:

```rust
{
    if s1.is_empty() {
        assume(s1.intersect(s2).len() <= 0);
        assert(s1.intersect(s2).len() <= s1.len());
    } else {
        ...
    }
}
```
```
verification results:: verified: 1 errors: 0
```

Since set cardinality is a `nat`, the only way it can be `<= 0` is if it's equal to `0`:

```rust
{
    if s1.is_empty() {
        assume(s1.intersect(s2).len() == 0);
        assert(s1.intersect(s2).len() <= s1.len());
    } else {
        ...
    }
}
```
```
verification results:: verified: 1 errors: 0
```

and the only way it can be `0` is if the set is the empty set:

```rust
{
    if s1.is_empty() {
        assume(s1.intersect(s2) === Set::empty());
        assert(s1.intersect(s2).len() == 0);
        assert(s1.intersect(s2).len() <= s1.len());
    } else {
        ...
    }
}
```
```
verification results:: verified: 1 errors: 0
```

If we change the `assume` to an `assert`, the assertion fails:

```rust
{
    if s1.is_empty() {
        assert(s1.intersect(s2) === Set::empty());
        assert(s1.intersect(s2).len() == 0);
        assert(s1.intersect(s2).len() <= s1.len());
    } else {
        ...
    }
}
```
```
error: assertion failed
   |
   |         assert(s1.intersect(s2) === Set::empty());
   |                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ assertion failed
```

So we've narrowed in on the problem:
the intersection of the empty set `s1` with another set should equal the empty set,
but the verifier doesn't see this automatically.
And from the previous section's discussion of equality, we can guess why:
the SMT solver doesn't always automatically prove equalities between collections,
but instead requires us to assert the equality using extensionality.
So we can add the extensionality assertion:

```rust
{
    if s1.is_empty() {
        assert(s1.intersect(s2) =~= Set::empty());
        assert(s1.intersect(s2) === Set::empty());
        assert(s1.intersect(s2).len() == 0);
        assert(s1.intersect(s2).len() <= s1.len());
    } else {
        ...
    }
}
```
```
verification results:: verified: 1 errors: 0
```

It works!  We've now verified the `s1.is_empty()` case,
and we can turn our attention to the `!s1.is_empty()` case:

```rust
{
    if s1.is_empty() {
        ...
    } else {
        let a = s1.choose();
        lemma_len_intersect::<A>(s1.remove(a), s2);
        assume(s1.intersect(s2).len() <= s1.len());
    }
}
```

Changing this `assume` to an `assert` fails,
so we've got work to do in this case as well:

```rust
{
    if s1.is_empty() {
        ...
    } else {
        let a = s1.choose();
        lemma_len_intersect::<A>(s1.remove(a), s2);
        assert(s1.intersect(s2).len() <= s1.len());
    }
}
```
```
error: assertion failed
   |
   |         assert(s1.intersect(s2).len() <= s1.len());
   |                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ assertion failed
```

Fortunately, the recursive call `lemma_len_intersect::<A>(s1.remove(a), s2)` succeeded,
so we have some information from the postcondition of this call.
Let's write this out explictly so we can examine it more closely,
substituting `s1.remove(a)` for `s1`:

```rust
{
    if s1.is_empty() {
        ...
    } else {
        let a = s1.choose();
        lemma_len_intersect::<A>(s1.remove(a), s2);
        assert(s1.remove(a).intersect(s2).len() <= s1.remove(a).len());

        assume(s1.intersect(s2).len() <= s1.len());
    }
}
```
```
verification results:: verified: 1 errors: 0
```

Let's compare what we know above `s1.remove(a)` with what we're trying to prove about `s1`:

```rust
        assert(s1.remove(a).intersect(s2).len() <= s1.remove(a).len()); // WE KNOW THIS

        assume(s1          .intersect(s2).len() <= s1          .len()); // WE WANT THIS
```

Is there any way we can make what we know look more like what we want?
For example, how does `s1.remove(a).len()` relate to `s1.len()`?
The value `a` is an element of `s1`, so if we remove it from `s1`,
it should decrease the cardinality by 1:

```rust
{
    if s1.is_empty() {
        ...
    } else {
        let a = s1.choose();
        lemma_len_intersect::<A>(s1.remove(a), s2);
        assert(s1.remove(a).intersect(s2).len() <= s1.remove(a).len());
        assert(s1.remove(a).len() == s1.len() - 1);

        assume(s1.intersect(s2).len() <= s1.len());
    }
}
```
```
verification results:: verified: 1 errors: 0
```

So we can simplify a bit:

```rust
{
    if s1.is_empty() {
        ...
    } else {
        let a = s1.choose();
        lemma_len_intersect::<A>(s1.remove(a), s2);
        assert(s1.remove(a).intersect(s2).len() <= s1.remove(a).len());
        assert(s1.remove(a).intersect(s2).len() <= s1.len() - 1);
        assert(s1.remove(a).intersect(s2).len() + 1 <= s1.len());

        assume(s1.intersect(s2).len() <= s1.len());
    }
}
```
```
verification results:: verified: 1 errors: 0
```

Now the missing piece is the relation between `s1.remove(a).intersect(s2).len() + 1`
and `s1.intersect(s2).len()`:

```rust
{
    if s1.is_empty() {
        ...
    } else {
        let a = s1.choose();
        lemma_len_intersect::<A>(s1.remove(a), s2);
        assert(s1.remove(a).intersect(s2).len() <= s1.remove(a).len());
        assert(s1.remove(a).intersect(s2).len() <= s1.len() - 1);
        assert(s1.remove(a).intersect(s2).len() + 1 <= s1.len());

        assume(s1.intersect(s2).len() <= s1.remove(a).intersect(s2).len() + 1);

        assert(s1.intersect(s2).len() <= s1.len());
    }
}
```
```
verification results:: verified: 1 errors: 0
```

If we can prove the assumption `s1.intersect(s2).len() <= s1.remove(a).intersect(s2).len() + 1`,
we'll be done:

```rust
        assume(s1          .intersect(s2).len()
            <= s1.remove(a).intersect(s2).len() + 1);
```

Is there anyway we can make `s1.remove(a).intersect(s2)` look more like `s1.intersect(s2)`
so that it's easier to prove this inequality?
If we switched the order from `s1.remove(a).intersect(s2)` to `s1.intersect(s2).remove(a)`,
then the subexpression `s1.intersect(s2)` would match:

```rust
        assume(s1.intersect(s2)          .len()
            <= s1.intersect(s2).remove(a).len() + 1);
```

so let's try that:

```rust
{
    if s1.is_empty() {
        ...
    } else {
        let a = s1.choose();
        lemma_len_intersect::<A>(s1.remove(a), s2);
        assert(s1.remove(a).intersect(s2).len() <= s1.remove(a).len());
        assert(s1.remove(a).intersect(s2).len() <= s1.len() - 1);
        assert(s1.remove(a).intersect(s2).len() + 1 <= s1.len());

        assert(s1.intersect(s2).len() <= s1.intersect(s2).remove(a).len() + 1);
        assert(s1.intersect(s2).len() <= s1.remove(a).intersect(s2).len() + 1);

        assert(s1.intersect(s2).len() <= s1.len());
    }
}
```
```
error: assertion failed
   |
   |         assert(s1.intersect(s2).len() <= s1.remove(a).intersect(s2).len() + 1);
   |                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ assertion failed
```

One of these assertion succeeds and the other fails.
The only difference between the successful assertion
and the failing assertion is the order of `intersect` and `remove`
in `s1.intersect(s2).remove(a)` and `s1.remove(a).intersect(s2)`,
so all we need to finish the proof is for `s1.intersect(s2).remove(a)`
to be equal to `s1.remove(a).intersect(s2)`:

```rust
{
    if s1.is_empty() {
        ...
    } else {
        let a = s1.choose();
        lemma_len_intersect::<A>(s1.remove(a), s2);
        assert(s1.remove(a).intersect(s2).len() <= s1.remove(a).len());
        assert(s1.remove(a).intersect(s2).len() <= s1.len() - 1);
        assert(s1.remove(a).intersect(s2).len() + 1 <= s1.len());

        assert(s1.intersect(s2).len() <= s1.intersect(s2).remove(a).len() + 1);
        assume(s1.intersect(s2).remove(a) === s1.remove(a).intersect(s2));
        assert(s1.intersect(s2).len() <= s1.remove(a).intersect(s2).len() + 1);

        assert(s1.intersect(s2).len() <= s1.len());
    }
}
```
```
verification results:: verified: 1 errors: 0
```

Again, we found ourselves needing to know the equality of two collections.
And again, the first thing to try is to assert extensional equality:

```rust
{
    if s1.is_empty() {
        ...
    } else {
        let a = s1.choose();
        lemma_len_intersect::<A>(s1.remove(a), s2);
        assert(s1.remove(a).intersect(s2).len() <= s1.remove(a).len());
        assert(s1.remove(a).intersect(s2).len() <= s1.len() - 1);
        assert(s1.remove(a).intersect(s2).len() + 1 <= s1.len());

        assert(s1.intersect(s2).len() <= s1.intersect(s2).remove(a).len() + 1);
        assert(s1.intersect(s2).remove(a) =~= s1.remove(a).intersect(s2));
        assert(s1.intersect(s2).remove(a) === s1.remove(a).intersect(s2));
        assert(s1.intersect(s2).len() <= s1.remove(a).intersect(s2).len() + 1);

        assert(s1.intersect(s2).len() <= s1.len());
    }
}
```
```
verification results:: verified: 1 errors: 0
```

It works!
Now we've eliminated all the `assume`s, so we've completed the verification:

```rust
pub proof fn lemma_len_intersect<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        s1.intersect(s2).len() <= s1.len(),
    decreases
        s1.len(),
{
    if s1.is_empty() {
        assert(s1.intersect(s2) =~= Set::empty());
        assert(s1.intersect(s2) === Set::empty());
        assert(s1.intersect(s2).len() == 0);
        assert(s1.intersect(s2).len() <= s1.len());
    } else {
        let a = s1.choose();
        lemma_len_intersect::<A>(s1.remove(a), s2);
        assert(s1.remove(a).intersect(s2).len() <= s1.remove(a).len());
        assert(s1.remove(a).intersect(s2).len() <= s1.len() - 1);
        assert(s1.remove(a).intersect(s2).len() + 1 <= s1.len());

        assert(s1.intersect(s2).len() <= s1.intersect(s2).remove(a).len() + 1);
        assert(s1.intersect(s2).remove(a) =~= s1.remove(a).intersect(s2));
        assert(s1.intersect(s2).remove(a) === s1.remove(a).intersect(s2));
        assert(s1.intersect(s2).len() <= s1.remove(a).intersect(s2).len() + 1);

        assert(s1.intersect(s2).len() <= s1.len());
    }
}
```
```
verification results:: verified: 1 errors: 0
```

The code above contains a lot of unnecessary `assert`s, though,
so it's worth spending a few minutes cleaning the code up
for sake of anyone who has to maintain the code in the future.
We want to clear out unnecessary code so there's less code to maintain,
but keep enough information so
someone maintaining the code can still understand the code.
The right amount of information is a matter of taste,
but we can try to strike a reasonable balance between conciseness and informativeness:

```rust
{{#include ../../../rust_verify/example/guide/lib_examples.rs:lemma_len_intersect_commented}}
```
