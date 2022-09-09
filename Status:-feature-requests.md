This document tracks paper-cuts and other usability issues that are not critical at this stage, but we would like to record for the future.

## Using ghost() in spec mode should either be allowed or emit a better error message (@matthias-brun)

Sometimes it's necessary to wrap types in `Ghost` inside spec code (e.g. to construct a struct with a ghost field). Using `ghost()` in spec code results in the error message `unexpected proof/ghost/tracked`.

One can just use `Ghost::new()` instead but this isn't easily discoverable. We should either change the error message to point out `Ghost::new()` to the user or alternatively directly allow `ghost()` to be used in spec mode.

## Consider defaulting a variable's mode to the least upper bound of a datatype's constructor mode and the current mode (@tjhance)

```
#[proof] struct A { … }

// exec
fn a() {
  let a: A = A { … } 
}
```

Variable `a` should be `proof` by default.

Suggested by @tjhance. There is no consensus yet that this is desirable in general.

## Functions taking mutable arguments (@tjhance)

I find "new as default, explicitly use old(...) even in requires clause" to be a little confusing. To be specific, as I write the atomics library, some methods takes a &mut argument and some don't, and I constantly have to switch my way of thinking as I work on the specs. In particular, there is no type-level error if I screw up and forget to use old in a postcondition.

To put a finer point on it: referencing an argument x in a postcondition means something different depending on whether x is passed as &mut or not.

I think my ideal would be something like:
* in requires, doesn't matter - could omit old, or use old to be explicit
* in ensures, MUST either use old or new to be explicit


