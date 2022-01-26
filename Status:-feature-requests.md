This document tracks paper-cuts and other usability issues that are not critical at this stage, but we would like to record for the future.

## Modes

Consider defaulting a variable's mode to the least upper bound of a datatype's constructor mode and the current mode:

```
#[proof] struct A { … }

// exec
fn a() {
  let a: A = A { … } 
}
```

Variable `a` should be `proof` by default.

Suggested by @tjhance. There is no consensus yet that this is desirable in general.

## Functions taking mutable arguments

@tjhance reports:

I find "new as default, explicitly use old(...) even in requires clause" to be a little confusing. To be specific, as I write the atomics library, some methods takes a &mut argument and some don't, and I constantly have to switch my way of thinking as I work on the specs. In particular, there is no type-level error if I screw up and forget to use old in a postcondition.

To put a finer point on it: referencing an argument x in a postcondition means something different depending on whether x is passed as &mut or not.

I think my ideal would be something like:
* in requires, doesn't matter - could omit old, or use old to be explicit
* in ensures, MUST either use old or new to be explicit

## Report the first assertion in the source code that fails

Verus currently reports the first error reported by Z3, which isn't guaranteed to be the first failing assertion in the source code. This is surprising when coming from Dafny, it can be problematic for certain tests, but it's also why Verus is often much faster at reporting errors (as Dafny has to start a separate query for each error).

@Chris-Hawblitzel suggests

> So we could have Verus automatically double-check that the earlier assertions all succeed.
> [...] it would require one additional Z3 query to double-check the earlier assertions, potentially doubling the total Z3 time whenever there's an error.  So if we do this, I would prefer for Verus to print the first error message immediately, and then start the additional Z3 query.

