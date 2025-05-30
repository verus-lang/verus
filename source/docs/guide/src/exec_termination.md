# Lightweight termination checking

While recursive `spec` functions and `proof` functions must always terminate and therefore must always contain a decreases clause, nontermination is allowed for exec functions. Nevertheless, by default, Verus still requires that recursive `exec` functions and loops in `exec` mode have a `decreases` clause. This only guarantees that the present function will terminate, on the assumption that all the callees also terminate so it should be treated as a lint, not a complete guarantee of termination.

The attribute #![verifier::exec_allows_no_decreases_clause] can be used to disable this check for a function, module, or crate. 