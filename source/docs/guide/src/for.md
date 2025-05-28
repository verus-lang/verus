# For Loops 

The previous section introduced a `while` loop implementation of `triangle`:

```rust
{{#include ../../../../examples/guide/recursion.rs:loop}}
```

We can rewrite this as a `for` loop as follows:

```rust
{{#include ../../../../examples/guide/recursion.rs:for_loop}}
```

The only difference between this `for` loop and the `while` loop 
is that `idx` is automatically incremented by 1 at the end of the 
each iteration. 

In addition, `iter.start`, `iter.cur`, `iter.end` reveal the start, current, and end
for the iterator of range `0..n`. 
`iter@` records all the elements that the iterator has iterated so far. 
In the above example, if `idx=3`, `iter@ =~= seq![0,1,2]`
