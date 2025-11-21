# Verus Architecture Overview

This document provides an overview of Verus internals for developers
contributing to the project. For build instructions and testing, see
[CONTRIBUTING.md](../CONTRIBUTING.md).

## Verification Pipeline Overview

Verus transforms Rust source code through multiple intermediate representations:

```
Rust Source Code
    ↓ (rustc: parsing, macro expansion)
Rust HIR (High-level Intermediate Representation)
    ↓ (rust_verify: HIR → VIR)
VIR-AST (Verification Intermediate Representation)
    ↓ (vir: AST → SST)
VIR-SST (Statement-oriented Syntax Tree)
    ↓ (vir: SST → AIR)
AIR (Assertion Intermediate Representation)
    ↓ (air: SMT encoding)
SMT-LIB queries
    ↓ (Z3, and experimentally cvc5)
Verification Results
```

## Crate Architecture

### Pipeline Call Graph Overview

```
main() → Verifier::new() → driver::run()
    ↓
VerifierCallbacksEraseMacro::after_expansion()
    ↓
Verifier::construct_vir_crate()
    ├─ rustc_hir_analysis::check_crate()  [type check]
    └─ rust_to_vir::crate_to_vir()        [HIR → VIR]
    ↓
Verifier::verify_crate_inner()
    ├─ GlobalCtx::new()
    ├─ ast_simplify::simplify_krate()
    ├─ modes::check_crate()
    ├─ buckets::get_buckets()
    └─ [per bucket, in parallel]
        └─ verify_bucket()
            └─ [per function]
                ├─ ast_to_sst_func::ast_to_sst_func()
                ├─ sst_to_air_func::func_sst_to_air()
                └─ Context::query() → SmtProcess::send()
```


### rust_verify

The main verifier driver that integrates with `rustc`.  This is the only
crate that should interact with `rustc`.  All other crates use Verus-specific
constructs.

**Key files:**
- `main.rs`: Entry point, argument parsing, output formatting
- `driver.rs`: Orchestrates `rustc` invocations for verification and compilation
- `verifier.rs`: Core `Verifier` struct and verification logic
- `context.rs`: `Context<'tcx>` carrying `rustc` state
- `config.rs`: Command-line argument definitions (`Args` struct)
- `attributes.rs`: Verus attribute parsing (`#[verifier(...)]`)
- `lifetime.rs`: Lifetime and borrow checking integration
- `rust_to_vir.rs`: Main HIR-to-VIR conversion orchestrator
- `rust_to_vir_func.rs`: Function body conversion
- `rust_to_vir_expr.rs`: Expression conversion
- `rust_to_vir_base.rs`: Type conversion and utilities
- `rust_to_vir_adts.rs`: Struct/enum conversion

**Main data structures:**
- `Verifier`: Main verifier state including VIR version of the crate(s), statistics, and configuration
- `Context<'tcx>`: Rustc integration context with type context, HIR, spans, and Verus items

**Key functions:**
- `main()`: Entry point
- `driver::run()`: Orchestrates compilation and verification
- `Verifier::construct_vir_crate()`: HIR→VIR conversion
- `Verifier::verify_crate_inner()`: Main verification loop
- `rust_to_vir::crate_to_vir()`: Converts entire crate to VIR

### vir

Defines the Verification Intermediate Representation in two forms: AST and SST.
The abstract syntax tree (AST) represents the internal subset of Rust that we
currently support for verification.  VIR also defines a Statement-oriented
Syntax Tree (SST), so that we can convert from Rust's (and VIR's) mutually
recursive expression and statement ASTs into a form (the SST) in which
expressions do not contain statements.  This simplifies the translation to AIR.

**Key files:**
- `ast.rs`: VIR-AST definitions (expressions can contain statements)
- `sst.rs`: VIR-SST definitions (expressions cannot contain statements)
- `context.rs`: `Ctx` and `GlobalCtx` for verification state
- `ast_to_sst.rs`, `ast_to_sst_func.rs`: AST→SST conversion
- `sst_to_air.rs`, `sst_to_air_func.rs`: SST→AIR conversion
- `modes.rs`: [Mode checking] (Spec/Proof/Exec)
- `well_formed.rs`: VIR structural validation
- `ast_simplify.rs`: VIR optimization passes
- `prune.rs`: Dead code elimination
- `traits.rs`: Trait handling and resolution
- `def.rs`: Constants and naming conventions for SMT identifiers

[Mode checking](https://verus-lang.github.io/verus/guide/modes.html)

**VIR-AST key concepts:**
- `Mode`: Verus supports three modes (Spec/Proof/Exec) - Spec and Proof are ghost (erased), Exec is compiled
- `Typ`/`TypX`: Types including primitives, datatypes, references, Ghost/Tracked wrappers
- `Function`/`FunctionX`: Function definitions with requires/ensures/decreases
- `Krate`/`KrateX`: Entire crate with modules, functions, datatypes, traits

**VIR-SST key concepts:**
- `Exp`/`ExpX`: Pure expressions (no embedded statements)
- `Stm`/`StmX`: Statements including assertions, assignments, control flow

**Context structures:**
- `Ctx`: Per-module verification context with functions and global context
- `GlobalCtx`: Cross-crate shared data including datatypes, call graph, and solver configuration

### air

Assertion Intermediate Representation - the final IR before SMT encoding.  AIR
is based on assert and assume statements, along with mutable updates to local
variables.

**Key files:**
- `ast.rs`: AIR AST definitions
- `context.rs`: `Context` for SMT interaction
- `smt_process.rs`: Z3/cvc5 process management
- `smt_verify.rs`: Query execution and result parsing

**AIR key concepts:**
- `Expr`/`ExprX`: Expressions including constants, variables, function applications, quantifiers
- `Stmt`/`StmtX`: Statements including Assume, Assert, Havoc, Assign
- `Typ`/`TypX`: Simple types (Bool, Int, BitVec, Named sorts)

**SMT interaction:**
- `Context`: Manages SMT solver connection, resource limits, and query state
- `SmtProcess`: Handles Z3/cvc5 process communication via stdin/stdout pipes
- `ValidityResult`: Query results (Valid, Invalid with counterexample, Canceled, TypeError)

### Supporting crates

- **builtin**: Defines verification-related Rust "functions" (e.g., `assert`,
  `requires`, `ensures`, `decreases`), so that the Rust compiler will
  automatically create correctly typed internal representations.  These are
  handled in a custom manner inside of Verus.
- **builtin_macros**: Core Verus macros that parse and transform Verus syntax.
  The top-level `verus! { }` macro parses Verus-extended Rust syntax (using a
  forked `syn` crate) and rewrites it into standard Rust with appropriate
  attributes. Key files include:
  - `syntax.rs`: Main `verus!` macro implementation and syntax parsing
  - `fndecl.rs`: Function declaration parsing and rewriting
  - `struct_decl_inv.rs`: Struct invariant handling
  - `attr_rewrite.rs`: Attribute-based code transformations
- **vstd**: The Verus standard library providing verified implementations and
  specifications. Organized into:
  - Core types: `seq.rs`, `set.rs`, `map.rs`, `multiset.rs`
  - Arithmetic: `arithmetic/` directory with modular arithmetic, logarithms, powers
  - Concurrency: `atomic.rs`, `atomic_ghost.rs`, `cell.rs`, `rwlock.rs`
  - Memory: `raw_ptr.rs`, `simple_pptr.rs`, `layout.rs`
  - Utilities: `bytes.rs`, `string.rs`, `slice.rs`, `hash_map.rs`, `hash_set.rs`
  - Specifications for Rust's standard library: `std_specs/` directory
- **state_machines_macros**: Macros for [concurrency-related verification](https://verus-lang.github.io/verus/state_machines/)
- **rust_verify_test_macros**: Test utilities
- **cargo-verus**: Cargo integration

### Vendored dependencies

The `dependencies/` directory contains forked versions of external crates:

- **syn**: Verus extends Rust syntax with verification constructs (e.g., `spec`,
  `proof`, `requires`, `ensures`, `Ghost<T>`). The forked `syn` crate adds
  parsing support for these extensions so that `builtin_macros` can parse Verus
  code inside `verus! { }` blocks.
- **prettyplease**: A Rust code formatter used for generating readable output.
  The fork includes modifications to handle Verus-specific syntax when
  pretty-printing transformed code.

These forks are necessary because Verus syntax is not valid standard Rust, so
the standard `syn` parser would reject it. By extending `syn`, Verus can parse
its custom syntax, transform it appropriately, and emit valid Rust for `rustc`.

## Detailed Pipeline Stages


### Stage 1: Rustc Integration

Verus runs multiple rustc invocations (see detailed comment in `driver.rs`):

1. **Verification pass**: Full verification with all ghost code present
2. **Compilation pass** (when `--compile` is used): Compiles with ghost code erased for executable output

The `VerifierCallbacksEraseMacro` implements `rustc_driver::Callbacks` to hook into rustc:
- `config()`: Sets up query provider overrides
- `after_expansion()`: Called after macro expansion, triggers VIR construction and verification

### Stage 2: HIR to VIR-AST

**Entry**: `rust_to_vir::crate_to_vir()` called from `Verifier::construct_vir_crate()`

The conversion iterates through HIR items and dispatches to specialized handlers:

- Functions: `rust_to_vir_func::check_item_fn()`
- Structs: `rust_to_vir_adts::check_item_struct()`
- Enums: `rust_to_vir_adts::check_item_enum()`
- Traits/impls, type aliases, constants, statics

**Type conversion**: `rust_to_vir_base::mid_ty_to_vir()` converts rustc `Ty<'tcx>` to VIR `Typ`

**Key operations:**
- Extract Verus attributes (`#[verifier(...)]`)
- Convert Rust types to VIR types
- Parse specifications (requires, ensures, invariants)
- Handle mode annotations (spec, proof, exec)

### Stage 3: VIR Simplification

After VIR construction, several passes run:

1. `ast_simplify::simplify_krate()`: Optimizations and normalizations
2. `modes::check_crate()`: Validate Spec/Proof/Exec mode usage
3. `well_formed::check_crate()`: Structural validation
4. `prune::prune_krate_for_module_or_krate()`: Remove unused definitions
5. `traits::merge_external_traits()`: Resolve trait implementations

### Stage 4: VIR-AST to VIR-SST

**Entry**: `ast_to_sst_crate::ast_to_sst_crate()`

Key transformations:
- **Statement extraction**: Move statements out of expressions
- **Variable renaming**: Eliminate shadowing with unique identifiers
- **Local declaration collection**: Track all variable types

### Stage 5: Bucketing and Parallelization

Functions are grouped into **buckets** for parallel verification:

- `buckets::get_buckets()` creates verification units
- Each bucket runs in a separate thread with its own SMT solver
- The source-level `#[spinoff_prover]` attribute also creates separate buckets
- Results merge at the end

### Stage 6: VIR-SST to AIR

**Entry**: `sst_to_air_func::func_sst_to_air()`

For each function:
1. `func_decl_to_air()`: Generate declarations for parameters, return values
2. `func_axioms_to_air()`: Generate axioms from specifications
3. Convert body to AIR assertions

### Stage 7: SMT Verification

**Query execution** (`air::context::Context::query()`):

1. Build SMT-LIB declarations and assertions
2. For each assertion:
   - Push scope: `(push)`
   - Add assumptions (preconditions)
   - Assert goal (postcondition)
   - Check satisfiability: `(check-sat)`
   - Pop scope: `(pop)`
3. Parse Z3/cvc5 response

**Resource limiting**:
`--rlimit` sets Z3 resource budget per function (cvc5 does not support per-function settings)

## Compilation Pipeline

When `--compile` is passed to Verus, it produces an executable binary after verification succeeds.

### Ghost Code Erasure

Verus uses a two-phase approach:

1. **Verification phase**: All code (including ghost) is processed for verification
2. **Compilation phase**: Ghost code is erased before rustc generates the executable

Ghost code includes:
- `spec` functions and closures
- `proof` functions and blocks
- `Ghost<T>` and `Tracked<T>` wrapper contents
- Specifications (requires, ensures, invariants, decreases)
- Assertions and assumptions

### Erasure Mechanism

The `ErasureInfo` structure tracks what needs to be erased:
- `ErasureModes`: Classifies each expression/statement by mode
- `ResolvedCalls`: Records how function calls should be handled

During the compilation pass:
- `EraseMacro` callback processes the code with erasure hints
- Ghost expressions are replaced with unit `()` or removed entirely
- `Ghost<T>` and `Tracked<T>` both unwrap to `T`

### Executable Output

After erasure, standard rustc compilation proceeds:
- MIR generation
- LLVM codegen
- Linking

The result is a normal Rust executable with all verification overhead removed.

## Key Abstractions

### Visitor Pattern

VIR provides visitors for AST traversal in `ast_visitor.rs` and
`sst_visitor.rs`. Similar patterns exist in AIR's `visitor.rs`.

### Error Handling

All pipeline stages return `Result<T, VirErr>` where `VirErr` is a `Message`
containing error level, description, source spans, labels, and optional help text.

### Scope Management

`ScopeMap<K, V>` manages nested scopes for variable bindings throughout the pipeline.

### SMT Identifier Naming

Conventions from `vir/src/def.rs`:
- Variables: `x@` (statement-bound) or `x$` (expression-bound)
- Types: `TYPE%ClassName`
- Snapshots: `snap%name`
- Fuel: `fuel%function_name`

## Developer Workflows

### Adding a New Verus Attribute

1. Define in `rust_verify/src/attributes.rs`
2. Handle in appropriate converter (`rust_to_vir_func.rs`, `rust_to_vir_adts.rs`)
3. Add tests in `rust_verify_test`

### Fixing a Type Conversion Bug

1. Check `rust_to_vir_base.rs` for type conversion logic
2. Check `vir/src/modes.rs` for mode checking
3. Check `vir/src/well_formed.rs` for validation

### Adding a New Expression/Statement Form

1. Add variant to `vir::ast::ExprX` or `StmtX`
2. Add corresponding SST variant in `vir::sst`
3. Handle in `ast_to_sst.rs` conversion
4. Handle in `sst_to_air.rs` conversion
5. Add tests

### Debugging Verification Issues

1. Use `--log-all` to generate intermediate representations
2. Check `.verus-log/` for VIR, AIR, and SMT-LIB files
3. Run a single test at a time when logging

### Understanding a Verification Failure

1. Find the assertion in `sst_to_air.rs` that generates the failing query
2. Check the SMT-LIB output to understand what's being asked

## Important Environment Variables

- `VERUS_Z3_PATH`: Path to Z3 executable
- `VERUS_EXTRA_ARGS`: Additional verifier arguments (useful in tests)

## Additional Resources

- Internal rustdoc: Run `RUSTC_BOOTSTRAP=1 cargo doc` from `source/`
- Test examples: `rust_verify_test/tests/` contains many usage examples
- Intermediate output: Use `--log-all` to inspect VIR/AIR/SMT at each stage
