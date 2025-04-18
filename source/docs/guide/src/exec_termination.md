# Lightweight termination checking

By default Verus will require that all `exec` recursive functions or functions that contain loops have a `decreases` clause. This only guarantees that the present function will terminate, on the assumption that all the callees also terminates so it should be treated as a lint, not a complete guarantee of termination.

The attribute #![verifier::exec_allow_no_decreases_clause] can be used to disable this check for a function, module, or crate. Additionally, the attribute #![verifier::assume_termination] states that the current function is guaranteed to terminate, even if it does not have a `decreases` clause.