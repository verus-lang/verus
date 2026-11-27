# Panicking

By default, Verus checks code for panic freedom in common, easily checkable situations
such as `Option::unwrap` or `vec[idx]`.

However, this statement might raise a number of questions, like:

 * What if I want to verify total panic-freedom, even against rare events resource exhaustion?
 * What if I don't care about panic-freedom at all, and prefer to focus on other correctness properties?
 * What if my code transitively depends on some other, unverified code which panics willy-nilly?
 * Does Verus guarantee anything about my program if it panics and recovers?
 * What if I need to panic in well-defined cases for ill-formed inputs?

The good news is that Verus lets you write arbitrary specifications to describe panicking behaviors
of your code, allowing you to be as defensive or permissive as you prefer.
