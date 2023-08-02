## *[Implemented]* Report the first assertion in the source code that fails

Verus currently reports the first error reported by Z3, which isn't guaranteed to be the first failing assertion in the source code. This is surprising when coming from Dafny, it can be problematic for certain tests, but it's also why Verus is often much faster at reporting errors (as Dafny has to start a separate query for each error).

@Chris-Hawblitzel suggests

> So we could have Verus automatically double-check that the earlier assertions all succeed.
> [...] it would require one additional Z3 query to double-check the earlier assertions, potentially doubling the total Z3 time whenever there's an error.  So if we do this, I would prefer for Verus to print the first error message immediately, and then start the additional Z3 query.
