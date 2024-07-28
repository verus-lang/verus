# Signature inheritance

Usually, the developer does not write a signature for methods in a trait implementation,
as the signatures are inherited from the trait declaration. However, the signature can
be modified in limited ways. To ensure soundness of the trait system, Verus has to make
sure that the signature on any function must be at least as strong as the
corresponding signature on the trait declaration.

 * All `requires` clauses in a trait declaration are inherited in the trait implementation.
    The user cannot
    add additional `requires` clauses in a trait implementation.
 * All `ensures` clauses in a trait declaration are inherited in the trait implementation.
    Furthermore, the user can add additional `ensures` clauses in the trait implementation.
 * The [`opens_invariants` signature](./reference-opens-invariants.md) is inherited
    in the trait implementation and cannot be modified.
 * The [unwinding signature](./reference-unwind-sig.md) is inherited
    in the trait implementation and cannot be modified.

When a trait function is called, Verus will attempt to statically resolve the function
to a particular trait implementation.  If this is possible, it uses the possibly-stronger 
specification from the trait implementation; in all other cases, it uses the
generic specification from the trait declaration.
