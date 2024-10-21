# Unsafe code & complex ownership

Here we discuss the handling of more complex patterns relating to Rust ownership including:

 * Interior mutability, where Rust allows you to mutate data even through a shared reference `&T`
 * Raw pointers, which require proper ownership handling in order to uphold safety contracts
 * Concurrency, where objects owned across different threads may need to coordinate.
