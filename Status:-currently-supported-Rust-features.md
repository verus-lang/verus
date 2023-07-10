**NOTE: if you are a Verus user, refer to https://verus-lang.github.io/verus/guide/features.html instead.**

This document describes which features of Rust are currently supported by the verifier,
relative to the full set of Rust features described in [The Rust Reference](https://doc.rust-lang.org/reference/).
Since the verifier is still under construction, not all features are supported yet.
Some of these missing features are likely to be supported soon,
while others may be supported later or never.
For soundness's sake, the verifier rejects any code that attempts to use an unsupported feature.

# Lexical Structure

The verifier uses the existing Rust parser, with no modifications or restrictions.

# Macros

The verifier uses the existing Rust macro expansion, with no modifications.
We've tested simple macros, and they seem to work.

The macro_export attribute is currently disabled.
Enabling macro_export would probably cause no problems and would be easy to do.

# Crates and source files

The verifier uses standard Rust source files and the standard Rust crate system.

# Conditional compilation

The verifier uses the existing Rust conditional compilation, with no modifications.
We've tested this in simple cases, and it seems to work.

# Items

The following items are fully or partially supported:
- modules: supported
- extern crate declarations: supported
- use declarations: supported
- function definitions
    - generics: supported
    - parameters:
        - simple parameters: supported
        - self (in methods): supported
        - patterns, mut: low priority
    - return type: supported
    - where clauses: medium priority
    - const/safe/async/extern: low priority
- struct definitions
    - generic bounds and where clauses: medium priority
    - tuple structs: supported
    - unit struct constructors as constants: low priority
- enumeration definitions: supported, except for:
    - generic bounds and where clauses: medium priority
    - custom discriminants: low priority
- implementations:
    - methods: supported
    - associated functions, types, and constants: medium priority
- extern blocks: supported, but we've only made limited use of this, so there might be missing features

The following items are not yet supported:
- type aliases: high priority
- trait definitions: supported (with limitations)
- constant items: supported, for the most common uses
- static items: low priority
- union definitions: unsafe, and therefore unsupported

# Attributes

The standard Rust attributes are supported and are ignored by the verifier.

# Statements

The following statements are supported:
- let statements
- expression statements
- macro invocations

The following statements are not yet supported:
- items (e.g. function declarations, module declarations): low priority

# Expressions

- literals:
    - supported for integer, boolean, and string literals
    - other types: medium priority
- path expressions: supported
- block expressions: supported
- async blocks: low priority
- unsafe blocks: unsupported
- operators
    - `*`, `&`
        - supported for `&` types and in some cases `&mut`, work-in-progress
    - `&mut`
        - partially supported, high priority
    - `?`
        - low priority
    - `!`
        - supported for bool
        - other types: low priority (can call method instead)
    - negation
        - supported for integer types
        - other types: low priority (can call method instead)
    - `+`, `-`, `*`
        - supported for integer types
        - other types: low priority (can call method instead)
    - `/`, `%`
        - supported for unsigned integer types
        - signed integer types: low priority
        - other types: low priority (can call method instead)
    - `&`, `|`, `^`, `<<`, `>>`
        - medium priority
    - `==`, `!=`
        - supported for types that allow SMT equality
        - other types: low priority (can call method instead)
    - `<`, `>`, `<=`, `>=`
        - supported for integer types
        - other types: low priority (can call method instead)
    - `&&`, `||`
        - supported
    - type cast
        - integer numeric casts and `char` to integer supported
        - other casts: low priority
    - assignment
        - place expressions (the only supported place is a mut local variable): medium priority
        - compound assignment expressions (e.g. `x += 1`): medium priority
        - (note: need to remember that evaluation order isn't strictly left-to-right here)
- grouped expression (parentheses): supported
- array expressions: medium priority
- index expressions: high priority, supported only in spec mode
- tuple expressions: supported
- struct expressions:
    - field struct expression: supported
    - functional update syntax: supported
    - struct field init shorthand: supported
    - tuple struct expression: supported
    - unit struct expression: low priority (use `S {}`, which is supported)
- call expressions:
    - function is a simple name: supported
    - function is an expression (higher-order functions): supported for spec closures, low priority
- method-call expressions
    - supported
- field access expressions: supported
- closure expressions:
    - spec closures (not proof/exec) are supported, at least as function arguments
    - other closure expressions: low priority
- loop expressions
    - loop: medium priority
    - while: supported
    - while let: medium priority
    - for: medium priority
    - labels, break, continue: medium priority
- range expressions: medium priority
- if expressions: supported
- if let expressions: supported
- match and match guards: supported, except:
    - see limitations on patterns in next section
- return expressions: high priority
- await expressions: low priority

# Patterns

- literal patterns: low priority (use a guard)
- identifier patterns: supported
- binding modes:
    - default mode: supported
    - other modes: medium priority
- wildcard pattern: supported
- rest pattern: low priority
- range patterns: low priority
- reference patterns: low priority
- struct patterns: supported
- tuple struct patterns:
    - for enums: supported
    - for structs: medium priority
- tuple patterns: supported
- grouped patterns (parentheses): supported
- slice patterns: low priority
- path patterns: low priority
- or patterns: low priority

# Types

- bool: supported
- integer types: supported
- floating point types: low priority
- usize/isize: supported, but assumes that they are either 32-bit or 64-bit
- char and str: supported (with limitations)
- never type: high priority
- tuple types: supported
- array and slice types:
    - supporting array and slice functionality, at least indirectly: high priority
    - supporting array and slice directly: medium priority
- struct types: supported
    - except for tuple struct types: medium priority
- enum types: supported
- union types: unsupported
- function item types: low priority
- closure types: low priority for exec/proof; for specs, you can use the Map type, which can be initialized with a closure
- pointer types:
    - shared references: supported
    - mutable references: partially supported, high priority
    - raw pointers: unsupported
- function pointer types: unsupported
- trait object types: low priority
- impl trait type: low priority
- type parameters: supported
- inferred type (_): supported
- trait bounds: high priority
- lifetime bounds: medium priority
- higher-ranked trait bounds: low priority
- type coercions and lifetime elision: may be supported but yet tested
- user-defined destructors: low priority

# Special types and traits

- Box: supported using box(...) constructor
- Rc, Arc: high priority
- Pin: low priority
- UnsafeCell: unsupported
    - Cell, RefCell: medium priority
- PhantomData: low priority, unless it's needed for higher-priority features
- operator traits: high priority
- Deref and DerefMut:
    - `*` is supported for `&` types
    - `*` for `&mut` types: partially supported, work-in-progress, high priority
    - other uses of Deref and DerefMut: low priority, unless it's needed for higher-priority features
- Drop: low priority
- Copy, Clone: high priority
- Send, Sync: medium priority
- Sized, `?Sized`: low priority

# Names

- paths: supported
- visibility
    - private, `pub`: supported
    - `pub(crate)`, `pub(super)`, etc.: medium priority

# Unsafety

The verifier only supports safe code.
We do not have plans to verify unsafe code; other tools, like RustBelt already exist for this.
(We also hope that verification can reduce the need for unsafe code in the first place.)

# Compilation

The set of features supported by the `--compile` option is currently lagging behind
the set of features supported for verification.
Fixing this is a high priority.
