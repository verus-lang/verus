# Panicking

By default, Verus checks code for panic-freedom in common, easily checkable situations
such as `Option::unwrap` or `vec[idx]`, but not in rarer events like out-of-memory ("OOM") or system failures.
This is because the former situations are easy to check against (e.g., just check `idx < vec.len()`)
while the latter are difficult to account for without modeling the entire allocator state.
We think this strikes a good balance for a lot of application code, checking properties that we intuitively
expect to be checked, without being unreasonably burdensome.

However, advanced users might be wondering:

 * What if I want to verify total panic-freedom, even against rare events like OOM?
 * What if I don't care about panic-freedom at all, and prefer to focus on other correctness properties?
 * What if my code transitively depends on some other, unverified code which might arbitrarily panic?
 * What if I need to panic in well-defined cases for ill-formed inputs?
 * Does Verus guarantee anything about my program if it panics and recovers?

The good news is that Verus lets you write arbitrary specifications to describe panicking behaviors
of your code, allowing you to be as defensive or permissive as you prefer.
And yes, Verus checks all code paths, including panic-unwinding-and-recovery paths.

> [!WARNING]
> An exception to the above claim is that Verus assumes `Drop` does not unwind.
> See [this page](./call-from-unverified-code.md#requirements-on-the-drop-trait) for more details.

In this chapter, we'll see how to write specifications about a program's panicking behaviors.


