# Non-Linear Arith Overview

# Overview 

Nonlinear math is generally undecidable; hence Z3 rely on heuristics to prove such properties.
While wonderful when they work, these heuristics can lead to unstable proofs.  Hence, verus turns nl off in the first place, you can see `(set-option :smt.arith.nl false)` in the smt log file. Instead, the user can explicitly
invoke the lemmas in this library. All files in this portion of the library 
verify without Non-Linear arithmetic reasoning, which should keep the library itself stable.

In general, it shouldn't be necessary to directly reference anything in `internals`.

(edited from the dafny ver)


This library is ported from the [dafny standard library](https://github.com/dafny-lang/libraries).
