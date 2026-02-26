# Mutable references upgrade

Verus is finally gaining extended support for mutable references, which greatly expands its capabilities.
With this new support, you can now write functions that take mutable references outside of the call-argument position, have functions that return mutable references, instantiate generic arguments with mutable references, create containers of mutable references, and take mutable references via pattern matching.

For example, you can take a mutable reference anywhere:

```rust
fn example1() {
    let mut x = 0;
    let x_ref = &mut x;
    *x_ref = 20;
    assert(x == 20);
}
```

Take a mutable reference by pattern matching:

```rust
fn example2() {
    let mut x = Some(4);
    match &mut x {
        Some(x_ref) => {
            *x_ref = 5;
        }
        None => { }
    }
    assert(x === Some(5));
}
```

Indexing into slices, arrays, and vectors now works better, too:

```rust
fn example3() {
    let mut f = vec![(0, 1), (2, 3), (4, 5)];
    f[2].1 = 6;
    assert(f@ === seq![(0, 1), (2, 3), (4, 6)]);
}
```

This change is a large conceptual overhaul within Verus. Several things worked previously because of special-casing around mutable references which no longer make sense now that `&mut T` is a "first class" type in Verus. As such, and there are a couple of breaking changes that users need to be aware of, which we will detail here.

## Opting into the experimental support

To enable the new mutable reference support, supply the additional command line option `-V new-mut-ref` to Verus. Soon, the "new-mut-ref" support will be enabled permanently, and the command line option will be removed. Until then, it is considered experimental.

This "migration guide" should give you everything you need to know to get your existing code working in the `new-mut-ref` world. It does not cover any of the new capabilities; to learn how to use the new capabilities, see the new guide. (TODO link doc)

Below, we cover the breaking changes.

# Breaking changes

## Breaking change A: mut refs in `ensures` clauses

<strong>(relevant to nearly anyone)</strong>

The most important breaking change is in the way mutable references are referred to in a specification.
Since this change is so substantial, there is a "deprecation grace period" (see below).

Previously, mutable references work like this:

```rust
fn test(a: &mut u8)
    requires *old(a) < 255,
    ensures *a == *old(a) + 1
{
    *a = *a + 1;
}
```

In the old system, `*a` in the postcondition always refered to the "new" value of the mutable reference after the function executes. However, this system relied on Verus's special-casing
around mutable references and no longer makes sense.
We aim to treat mutable references uniformly with other types, and that means that referring to
any input parameter should always refer to its pre-state value.

In the new system, mentioning a mutable variable in the precondition (e.g., `*a`) always refers to the value at entry. You can still optionally use `*old(a)`, but this is redundant.
In the post-condition, you either use `*old(a)` to refer to the value at entry, or use the newly introduced `final` operator to refer to the updated value (`*final(a)`) of the mutable variable.

```rust
fn test(a: &mut u8)
    requires *a < 255,
    ensures *final(a) == *old(a) + 1
{
    *a = *a + 1;
}
```

Observe that postconditions are maximally unambiguous: You always need to use `old` or `final`. As a result, there should not be any specification which is well-formed in both before and after these changes, but which changes meaning.  (In the future, we may relax the system so that `old` isn't necessary at all, but it would be extremely confusing if this change were made today.)

### Summary

To refer to the entry value or updated value of a parameter `x: &mut u64`:

|                                | Old system | New system            |
|--------------------------------|------------|-----------------------|
| requires clause, entry value   | `*old(x)`  | `*old(x)` or `*x`     |
| ensures clause, entry value    | `*old(x)`  | `*old(x)`             |
| ensures clause, updated value  | `*x`       | `*final(x)`           |

### Delaying the transition

To delay the transition, you can use the attribute `#[verifier::deprecated_postcondition_mut_ref_style(true)]`. This attribute can be set on any crate, module, function, etc., so it can be partially applied to a project. When this attribute is enabled for a function, the "old style" is permitted in its postcondition:

```rust
#[verifier::deprecated_postcondition_mut_ref_style(true)]
fn test(a: &mut u8)
    requires *old(a) < 255,
    ensures *a == *old(a) + 1
{
    *a = *a + 1;
}
```

This attribute will be available for some time even after `new-mut-ref` is permanently enabled; however, it will be removed eventually.

## Breaking change B: mut refs to `tracked` locations

<strong>(relevant to anyone using `tracked` code)</strong>

The new system for mutable references to tracked locations is more permissive in some ways and more restrictive in others.

For one, you can now take a mutable reference to an exec location and then modify it from ghost code, _provided_ that you only modify a ghost "sub-place". For example, this now works:

```rust
struct ExecStruct {
    real_integer: u64,
    tracked_stuff: Tracked<X>,
}

proof fn modify_tracked_stuff(tracked x: &mut ExecStruct) {
    *x.tracked_stuff = X { ... };
}

fn test() {
    let mut e = ExecStruct { ... };
    proof {
        modify_tracked_stuff(&mut e);
    }
}
```

Previously, this would have given an error for trying to coerce an exec location to a tracked location.

(Additionally, note that using `*` to dereference a `Tracked` type is now allowed.)

On the other hand, Verus doesn't always know if a mutable reference points to an exec or tracked location. For example, this no longer works:

```rust
proof fn modify_tracked_u64(tracked x: &mut u64) {
    *x = 5;    /* this is an error in new-mut-ref
    ^^^^^^      */
}

fn test() {
    proof {
        let tracked mut x = 5;
        modify_tracked_u64(&mut x);
    }
}
```

This previously worked, because Verus would assume that a `tracked` mutable reference could only
point to a `tracked` location. This assumption no longer holds.

```
error: cannot mutate exec-mode place in proof-code
 --> xyz.rs:7:5
  |
7 |     *x = 5;
  |     ^-
  |     ||
  |     |this mutable reference has mode `tracked`, but may point to an exec-mode location
  |     this place may have mode exec
```

Fortunately, this kind of code—taking a tracked reference to possibly-executable data—is fairly uncommon.
When modifying data through a mutable reference in proof code, Verus will attempt to deduce that the reference points to a non-exec place and is thus allowable in proof code.
The following are allowed:

* Writing to a location of type `X` where `X` is a struct declared as a `tracked struct`
* Writing to a location of type `Tracked<A>` or `Ghost<A>`
* Writing to a location inside a `Tracked` that is not subsequently behind a mutable reference
  * e.g., writing to `**x` where `x: &mut Tracked<T>` is ok
  * writing to `**x` where `x: Tracked<&mut T>` may not be ok

Note that common tracked-only vstd types like `PointsTo` are all `tracked`, so modifying such data will always be permitted in proof code.
On the other hand, note that `Option<T>` is always an exec type.

If you run into trouble with this error, first check to make sure your structs are marked `tracked` when possible:

```
tracked struct X {
  ...
}
```

If you really need to work with a struct that can be used both in `exec` code and in `tracked` code, you may need to work with `&mut Tracked<A>` instead. Using `&mut Tracked<A>` is also the most reliable way to work with generic types.

Finally, note that you can convert between `&mut T` and `&mut Tracked<T>`:

 * If `x: &mut Tracked<T>`, then you can do `&mut **x` to get `&mut T`
 * If `x: &mut T` (and Verus considers `T` to be a tracked-only type), then you can do [not implemented yet]
