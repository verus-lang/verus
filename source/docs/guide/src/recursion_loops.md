# Recursion and loops

Suppose we want to compute the nth 
[triangular number](https://en.wikipedia.org/wiki/Triangular_number):

```
triangle(n) = 0 + 1 + 2 + ... + (n - 1) + n
```

We can express this as a simple recursive funciton:

```rust
{{#include ../../../rust_verify/example/guide/recursion.rs:spec}}
```

This chapter discusses how to define and use recursive functions,
including writing `decreases` clauses and using fuel.
It then explores a series of verified implementations of `triangle`,
starting with a basic recursive implementation and ending with a while loop.
