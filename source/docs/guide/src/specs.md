# Basic specifications

Verus programs contain *specifications* to describe the
intended behavior of the code.
These specifications include preconditions, postconditions, assertions, and loop invariants.
Specifications are one form of *ghost code* --- code that appears in the Rust source code for verification's sake,
but does not appear in the compiled executable.

This chapter will walk through some basic examples of preconditions, postconditions,
and assertions, showing the syntax for writing these specifications
and discussing integer arithmetic and equality in specifications.
