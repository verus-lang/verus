
# Verus --- SMT-based verification of low-level systems code

The Rust programming language, with its combination of high-level features, memory safety, and low-level "unsafe" primitives has proven to be an excellent tool to write high-performance systems software, with direct interactions with the hardware.

By statically preventing aliased mutable references Rust relieves the burden on the developer of reasoning about data races; when formally verifying imperative code in languages that do not restric aliasing, the developer similarly has to explicitly manage the heap and potential aliasing. In our experience, a Rust-like linear type system can be an excellent aid to Floyd-Hoare SMT-based verification of executable code.

On this foundation we are building Verus, a new tool for semi-automatic verification of Rust code using an SMT solver (Z3). Verus can efficiently verify full functional correctness of low-level systems code written in a safe Rust dialect that supports expressing specifications and proofs.

Verus leverages the fact that safe Rust has a natural, direct encoding in SMT (for code without interior mutability, which we need to address separately). Algebraic data types (ADTs) and sound generics complement safe Rust to make it a solid basis for a mathematical language for expressing specifications and proofs.

In this talk I'll discuss Verus' design, how it prioritizes lean, efficient encoding of safe Rust to SMT queries, and its features that aid verification of complex systems, such as linear ghost variables.
