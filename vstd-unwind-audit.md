# vstd panic/unwind specification audit

This audit covers every vstd function that had an unwind-related specification (`no_unwind`, `no_unwind when`,
`requires[no_panic]`, `ensures[on unwind]`): 201 sites in 24 files, as of branch `unwind-experiment`.
Many sites are inside macros, so one site can cover several instantiations.

## Semantics

Unwinding implies a panic, but a panic may also abort without unwinding. In particular, a `no_unwind`
function may still panic by aborting, so a `no_panic` function cannot call it.

- `no_unwind`: the function never unwinds, but it may panic by aborting.
- `no_panic`: the function never panics (and so never unwinds).
- `requires[no_panic] P` / `requires[no_panic exact] P`: the function doesn't panic if P holds (and with `exact`, panics if P fails).
- `ensures[on panic] Q`: if the function panics, Q holds.

## Method

For each site, I read the vstd source and determined whether the spec is trusted (`assume_specification`,
`external_body`) or checked (a verified body). I then checked the official Rust 1.100 documentation for the
corresponding std/core/alloc function: its `# Panics` section, whether it can touch the global allocator
(any function that can allocate is treated as able to panic), argument-dependent panics (orderings,
out-of-bounds, overflow), debug UB checks, and whether it runs user code. A panic was considered ruled out
only if the existing `requires` excludes it. Functions that allocate (for example `PPtr::new`/`empty`/`free`,
`Vec::push`) had no unwind spec and were left unchanged.

## Result

| outcome | sites |
|---|---|
| `no_unwind` → `no_panic` | 199 |
| `no_unwind when !may_unwind()` → `ensures[on panic] may_unwind()` (std_specs/control_flow.rs) | 2 |
| kept `no_unwind` | 0 |
| removed / weakened | 0 |

No existing `no_unwind` spec was found to be wrong. vstd verifies with the changes (2354 verified, 0 errors),
and the full rust_verify_test suite passes.

## `requires[no_panic exact]` (applied in a follow-up commit)

For these functions, the Rust docs guarantee a panic, not UB, exactly when the old plain `requires`
fails. Their plain `requires` + `no_panic` has been replaced with `requires[no_panic exact]`.
The condition is still checked at call sites by default, but with `#[verifier::deny_panic(false)]`
callers may let them panic, and may assume the condition after a normal return.

- slices: `swap`, `rotate_left`, `rotate_right`, `split_at`, `split_at_mut`
- `Vec` indexing (`vec_index`, `vec_index_mut`)
- `Option::unwrap`/`expect`, `Result::unwrap`/`expect`
- atomics (std_specs/atomic.rs): `load` (Release/AcqRel) and `store` (Acquire/AcqRel). Not
  `compare_exchange(_weak)`: the docs don't promise a panic for a bad failure ordering.

Not candidates (violations are UB, so the plain `requires` must stay): `NonZero::new_unchecked`,
`split_at_unchecked`/`split_at_mut_unchecked`, `ptr::read`/`write`, `NonNull::new_unchecked`,
`MaybeUninit::assume_init*`. Some of these have debug UB checks that abort, but those checks are optional and
can't be relied on.

## Panic functions (follow-up commit)

`core::panicking::{panic, panic_fmt, assert_failed}` (std_specs/core.rs) and vstd's `__call_panic`
(pervasive.rs, used by `vpanic!`) were `requires false` (or `requires allow_panic()`, controlled by
the `allow_panic` cargo feature). They are now `requires[no_panic exact] false` ("always panics"), and the `allow_panic`
feature is removed. A reachable panic is still an error by default (the call-site check fails). With
`#[verifier::deny_panic(false)]`, the caller may panic instead, unless it has its own no-panic obligations.

## Concerns and assumptions

- **Destructors.** Several `no_panic` specs run a destructor of a user value (`PCell::write` in cell/pcell.rs,
  `Option::unwrap_or`, `Result::ok`/`err`). They rely on Verus's existing assumption that destructors don't panic.
- **Debug UB checks.** `ptr::read`/`write`, `NonNull::new_unchecked`, debug null/alignment checks on dereference,
  and `assert_inhabited` in `MaybeUninit::assume_init*` can abort. In each case the existing `requires` (or the
  `PointsTo::is_nonnull`/`is_aligned` axioms) rules the condition out.
- **`MaybeUninit::assume_init*`** is `no_panic` only because Verus can't prove `is_init()` for an uninhabited
  type. That holds while only `new` and `write` produce initialized values. A future spec such as `zeroed`
  would need to revisit this.
- **`control_flow.rs`.** `may_unwind()` is `false` for `branch`/`from_residual` on Option, ControlFlow and
  (for `branch`) Result, which are pure match/rewrap. It's `true` for Result's `from_residual`, which calls the
  user's `From`. The `?` operator in a `no_panic` function works through the inherited trait-level
  `ensures[on panic]` (tested in `no_panic_vstd_calls`). The name `may_unwind` was kept, to avoid breaking
  users, but it now means "may panic".
- **Constructors:** the non-allocating constructors that had no unwind spec (the `PAtomic*::new` wrappers in atomic.rs,
  `cell::PCell::{empty,new}`, `pcell_maybe_uninit::PCell::{empty,new}`) are now marked `no_panic` (follow-up commit).
- The 1.100 toolchain has no local rust-src. Implementations were read from the local 1.98.1 rust-src, and
  the docs were checked online against 1.100.

# Per-site tables

## Audit group A: integer / num / bits / nonzero / float / core / bytes

All paths relative to `source/vstd`. Docs checked against
`https://doc.rust-lang.org/1.100.0/core/...`. For the integer pages, U = `core/primitive.u32.html` and
I = `core/primitive.i32.html`. The same text appears on every width's page.

### Macro `num_specs!` (std_specs/num.rs:24-540)
It is instantiated 6 times (num.rs:543-563), with ($uN, $iN) = (u8,i8), (u16,i16), (u32,i32), (u64,i64),
(u128,i128), (usize,isize). Each num.rs row below covers all 6 widths: for example, the line-101 row covers
`u8::wrapping_add` through `usize::wrapping_add`, and the line-379 row covers `i8::wrapping_add` through `isize::wrapping_add`.
All of these are `assume_specification`s with no `requires`, gated by `#[cfg(not(verus_verify_core))]`.

| file:line | item (and Rust path) | kind | current | recommendation | justification |
|---|---|---|---|---|---|
| bytes.rs:21 | `u8::from_le_bytes` | assume_spec | no_unwind | no_panic | Docs list no panics and there's no allocation (U#method.from_le_bytes). It's a pure byte reinterpretation. |
| bytes.rs:103 | `u16::from_le_bytes` | assume_spec | no_unwind | no_panic | Same as above. |
| bytes.rs:206 | `u32::from_le_bytes` | assume_spec | no_unwind | no_panic | Same as above. |
| bytes.rs:371 | `u64::from_le_bytes` | assume_spec | no_unwind | no_panic | Same as above. |
| float.rs:131 | `vstd::float::float_cast<From,To>`. It models the `as` casts float<->float, int->float and float->int (rust_to_vir_expr.rs:2905-2931). It isn't a real std fn and is never compiled to executable code. | external_body (body `unimplemented!{}`) | no_unwind | no_panic | Rust `as` numeric casts never panic. Float->int saturates, with NaN giving 0 (Reference, "Numeric cast": https://doc.rust-lang.org/1.100.0/reference/expressions/operator-expr.html#numeric-cast). Int->float and float->float round. No allocation. |
| std_specs/bits.rs:193 | `u8::reverse_bits` | assume_spec | no_unwind | no_panic | Docs list no panics and there's no allocation (U#method.reverse_bits). |
| std_specs/bits.rs:389 | `u16::reverse_bits` | assume_spec | no_unwind | no_panic | Same as above. |
| std_specs/bits.rs:585 | `u32::reverse_bits` | assume_spec | no_unwind | no_panic | Same as above. |
| std_specs/bits.rs:783 | `u64::reverse_bits` | assume_spec | no_unwind | no_panic | Same as above. |
| std_specs/bits.rs:1052 | `u8::count_ones` | assume_spec | no_unwind | no_panic | Docs list no panics and there's no allocation (U#method.count_ones). |
| std_specs/bits.rs:1061 | `u16::count_ones` | assume_spec | no_unwind | no_panic | Same as above. |
| std_specs/bits.rs:1070 | `u32::count_ones` | assume_spec | no_unwind | no_panic | Same as above. |
| std_specs/bits.rs:1079 | `u64::count_ones` | assume_spec | no_unwind | no_panic | Same as above. |
| std_specs/bits.rs:1088 | `u128::count_ones` | assume_spec | no_unwind | no_panic | Same as above. |
| std_specs/bits.rs:1097 | `usize::count_ones` | assume_spec | no_unwind | no_panic | Same as above. |
| std_specs/core.rs:182 | `core::mem::swap::<T>` | assume_spec | no_unwind | no_panic | Docs list no panics (core/mem/fn.swap.html): "Swaps the values at two mutable locations, without deinitializing either one." It's a bitwise swap. No Clone/Drop/user code, no allocation. |
| std_specs/nonzero.rs:78 | `NonZero::<T>::new` | assume_spec | no_unwind | no_panic | Docs list no panics (core/num/struct.NonZero.html#method.new): "Creates a non-zero if the given value is not zero." |
| std_specs/nonzero.rs:88 | `NonZero::<T>::new_unchecked` (unsafe) | assume_spec, `requires !n.is_zero()` | no_unwind | no_panic | Zero is UB, not a guaranteed panic: "This results in undefined behavior if the value is zero" (#method.new_unchecked). The debug `ub_checks` precondition assert, which aborts, can only fire on zero, and the existing `requires` rules zero out. So this is not a `requires[no_panic]` candidate. |
| std_specs/nonzero.rs:101 | `NonZero::<T>::get` | assume_spec | no_unwind | no_panic | Docs list no panics (#method.get). Plain field read. |
| std_specs/num.rs:101 | `<uN>::wrapping_add` (x6) | assume_spec | no_unwind | no_panic | Docs list no panics. "Wrapping (modular) addition" (U#method.wrapping_add). No overflow check. |
| std_specs/num.rs:108 | `<uN>::wrapping_add_signed` (x6) | assume_spec | no_unwind | no_panic | Docs list no panics (U#method.wrapping_add_signed). |
| std_specs/num.rs:115 | `<uN>::wrapping_sub` (x6) | assume_spec | no_unwind | no_panic | Docs list no panics (U#method.wrapping_sub). |
| std_specs/num.rs:122 | `<uN>::wrapping_mul` (x6) | assume_spec | no_unwind | no_panic | Docs list no panics (U#method.wrapping_mul). |
| std_specs/num.rs:129 | `<uN>::wrapping_shl` (x6) | assume_spec | no_unwind | no_panic | U#method.wrapping_shl: "Panic-free bitwise shift-left; yields self << mask(rhs)". Out-of-range `rhs` is masked. |
| std_specs/num.rs:136 | `<uN>::wrapping_shr` (x6) | assume_spec | no_unwind | no_panic | U#method.wrapping_shr: "Panic-free bitwise shift-right". |
| std_specs/num.rs:143 | `<uN>::rotate_left` (x6) | assume_spec | no_unwind | no_panic | Docs list no panics, and any `n` is allowed (U#method.rotate_left): "a rotation by the number of bits in self returns the input value unchanged". |
| std_specs/num.rs:150 | `<uN>::rotate_right` (x6) | assume_spec | no_unwind | no_panic | Same as above (U#method.rotate_right). |
| std_specs/num.rs:162 | `<uN>::checked_add` (x6) | assume_spec | no_unwind | no_panic | U#method.checked_add: "returning None if overflow occurred". No panic. |
| std_specs/num.rs:174 | `<uN>::checked_add_signed` (x6) | assume_spec | no_unwind | no_panic | Same pattern, returns None (U#method.checked_add_signed). |
| std_specs/num.rs:186 | `<uN>::checked_sub` (x6) | assume_spec | no_unwind | no_panic | Same pattern, returns None (U#method.checked_sub). |
| std_specs/num.rs:198 | `<uN>::checked_mul` (x6) | assume_spec | no_unwind | no_panic | Same pattern, returns None (U#method.checked_mul). |
| std_specs/num.rs:212 | `<uN>::checked_next_multiple_of` (x6) | assume_spec | no_unwind | no_panic | U#method.checked_next_multiple_of: "Returns None if rhs is zero or the operation would result in overflow." Unlike `next_multiple_of`, it doesn't panic on 0. |
| std_specs/num.rs:227 | `<uN>::checked_div` (x6) | assume_spec | no_unwind | no_panic | U#method.checked_div: "returning None if rhs == 0". |
| std_specs/num.rs:235 | `<uN>::checked_div_euclid` (x6) | assume_spec | no_unwind | no_panic | U#method.checked_div_euclid: "returning None if rhs == 0". |
| std_specs/num.rs:248 | `<uN>::checked_rem` (x6) | assume_spec | no_unwind | no_panic | U#method.checked_rem: "returning None if rhs == 0". |
| std_specs/num.rs:261 | `<uN>::checked_rem_euclid` (x6) | assume_spec | no_unwind | no_panic | U#method.checked_rem_euclid: "returning None if rhs == 0". |
| std_specs/num.rs:273 | `<uN>::saturating_add` (x6) | assume_spec | no_unwind | no_panic | U#method.saturating_add: "saturating at the numeric bounds instead of overflowing". |
| std_specs/num.rs:285 | `<uN>::saturating_sub` (x6) | assume_spec | no_unwind | no_panic | Same as above (U#method.saturating_sub). |
| std_specs/num.rs:297 | `<uN>::saturating_mul` (x6) | assume_spec | no_unwind | no_panic | Same as above (U#method.saturating_mul). |
| std_specs/num.rs:305 | `<uN>::is_multiple_of` (x6, unsigned only) | assume_spec | no_unwind | no_panic | U#method.is_multiple_of: "equivalent to self % rhs == 0, except that it will not panic for rhs == 0". |
| std_specs/num.rs:379 | `<iN>::wrapping_add` (x6) | assume_spec | no_unwind | no_panic | Docs list no panics (I#method.wrapping_add). |
| std_specs/num.rs:386 | `<iN>::wrapping_add_unsigned` (x6) | assume_spec | no_unwind | no_panic | Docs list no panics (I#method.wrapping_add_unsigned). |
| std_specs/num.rs:393 | `<iN>::wrapping_sub` (x6) | assume_spec | no_unwind | no_panic | Docs list no panics (I#method.wrapping_sub). |
| std_specs/num.rs:400 | `<iN>::wrapping_mul` (x6) | assume_spec | no_unwind | no_panic | Docs list no panics (I#method.wrapping_mul). MIN*-1 wraps. |
| std_specs/num.rs:407 | `<iN>::wrapping_shl` (x6) | assume_spec | no_unwind | no_panic | I#method.wrapping_shl: "Panic-free bitwise shift-left". |
| std_specs/num.rs:414 | `<iN>::wrapping_shr` (x6) | assume_spec | no_unwind | no_panic | I#method.wrapping_shr: "Panic-free bitwise shift-right". |
| std_specs/num.rs:421 | `<iN>::rotate_left` (x6) | assume_spec | no_unwind | no_panic | Docs list no panics (I#method.rotate_left). |
| std_specs/num.rs:428 | `<iN>::rotate_right` (x6) | assume_spec | no_unwind | no_panic | Docs list no panics (I#method.rotate_right). |
| std_specs/num.rs:440 | `<iN>::checked_add` (x6) | assume_spec | no_unwind | no_panic | Returns None on overflow (I#method.checked_add). |
| std_specs/num.rs:452 | `<iN>::checked_add_unsigned` (x6) | assume_spec | no_unwind | no_panic | Returns None on overflow (I#method.checked_add_unsigned). |
| std_specs/num.rs:464 | `<iN>::checked_sub` (x6) | assume_spec | no_unwind | no_panic | Returns None on overflow (I#method.checked_sub). |
| std_specs/num.rs:476 | `<iN>::checked_sub_unsigned` (x6) | assume_spec | no_unwind | no_panic | Returns None on overflow (I#method.checked_sub_unsigned). |
| std_specs/num.rs:488 | `<iN>::checked_mul` (x6) | assume_spec | no_unwind | no_panic | Returns None on overflow (I#method.checked_mul). |
| std_specs/num.rs:500 | `<iN>::checked_div` (x6) | assume_spec | no_unwind | no_panic | I#method.checked_div: "returning None if rhs == 0 or the division results in overflow". So MIN/-1 is covered too. |
| std_specs/num.rs:512 | `<iN>::checked_div_euclid` (x6) | assume_spec | no_unwind | no_panic | I#method.checked_div_euclid: "returning None if rhs == 0 or the division results in overflow". |
| std_specs/num.rs:524 | `<iN>::checked_rem` (x6) | assume_spec | no_unwind | no_panic | I#method.checked_rem: "returning None if rhs == 0 or the division results in overflow". |
| std_specs/num.rs:536 | `<iN>::checked_rem_euclid` (x6) | assume_spec | no_unwind | no_panic | I#method.checked_rem_euclid: "returning None if rhs == 0 or the division results in overflow". |

None of the items above allocate or call user code (Clone, Drop, PartialEq, closures).

### Candidates for requires[no_panic]
- None. The only site with a `requires` is `NonZero::new_unchecked`. Its failure mode (zero) is documented
  as UB rather than a guaranteed panic, so the plain `requires` must stay.

### Concerns
- None blocking. Every site is a total, non-allocating primitive operation. No verified bodies are involved:
  `float_cast` is `external_body` with an `unimplemented!{}` body, and it is never compiled.
- Note: this group contains none of the panicking integer methods (`pow`, `abs`, `div_euclid`, `ilog`,
  `isqrt`, `next_power_of_two`, plain shifts, `next_multiple_of`). Only the checked_/wrapping_/saturating_ variants,
  rotates, bit ops and `is_multiple_of` appear.
- `new_unchecked`: in debug or `-Zub-checks` builds, std's `assert_unsafe_precondition!` aborts with a
  non-unwinding panic on zero. That's irrelevant given `requires !n.is_zero()`, but it would matter if anyone later
  tried to weaken the requires.
- `float_cast` doesn't correspond to a std function. It stands in for the language-level `as` casts, which are
  panic-free.

## Audit group B: vstd atomic.rs, std_specs/atomic.rs, cell.rs, cell/pcell.rs, cell/pcell_maybe_uninit.rs

Paths are relative to `source/vstd`. Rust docs were checked at
`https://doc.rust-lang.org/stable/core/sync/atomic/type.AtomicU32.html` (the page reports 1.100.0; in 1.100 the
`AtomicXX` types are aliases of `Atomic<T>`, so `struct.AtomicU32.html` and the `/1.100.0/` URL return 404) and at
`type.AtomicPtr.html`. The local 1.98.1 rust-src (`~/.rustup/toolchains/1.98.1-*/lib/rustlib/src/rust/library/core/src/sync/atomic.rs`)
was used to look at the implementation. No 1.100 rust-src is installed.

Shared facts used below:
- **No atomic op allocates.** `new` and `into_inner` are `transmute`s. Every other op goes through
  `atomic_load`, `atomic_store`, `atomic_swap`, `atomic_add`, `atomic_compare_exchange` and so on: a `match order`
  that dispatches to an intrinsic. The only `panic!`s are in the invalid-ordering arms (source lines 3871-3897 and 936/942).
  Those are ordinary `core::panic!` and **can unwind**.
- **The vstd `PAtomic*` wrappers (atomic.rs) hardcode `Ordering::SeqCst`** everywhere, so no ordering panic is reachable.
- **Overflow:** fetch_add and fetch_sub are documented as "This operation wraps around on overflow", so they have no overflow panic.
  The fetch_* bitwise, min and max ops say "All ordering modes are possible" and have no Panics section.

### Table

| file:line | item (and Rust path) | kind | current | recommendation | justification |
|---|---|---|---|---|---|
| atomic.rs:174 (macro `atomic_common_methods`) | `load` -> `Atomic*::load(SeqCst)`. Instantiated for PAtomicBool, U8/U16/U32/U64/Usize, I8/I16/I32/I64/Isize, PAtomicPtr<T> | external_body | no_unwind | no_panic | Docs: "Panics if `order` is Release or AcqRel" ([load](https://doc.rust-lang.org/stable/core/sync/atomic/type.AtomicU32.html#method.load)). The wrapper hardcodes SeqCst, so this can't happen. No allocation. |
| atomic.rs:187 (same macro) | `store` -> `Atomic*::store(v, SeqCst)`. Same instantiations | external_body | no_unwind | no_panic | Docs: "Panics if `order` is Acquire or AcqRel" ([store](https://doc.rust-lang.org/stable/core/sync/atomic/type.AtomicU32.html#method.store)). Hardcoded SeqCst. |
| atomic.rs:211 (same macro) | `compare_exchange` -> `Atomic*::compare_exchange(c, n, SeqCst, SeqCst)`. Same instantiations | external_body | no_unwind | no_panic | Docs: "The failure ordering can only be SeqCst, Acquire or Relaxed" ([compare_exchange](https://doc.rust-lang.org/stable/core/sync/atomic/type.AtomicU32.html#method.compare_exchange)). The failure ordering is hardcoded to SeqCst. No allocation. |
| atomic.rs:234 (same macro) | `compare_exchange_weak` -> `Atomic*::compare_exchange_weak(.., SeqCst, SeqCst)`. Same instantiations | external_body | no_unwind | no_panic | Same as above ([compare_exchange_weak](https://doc.rust-lang.org/stable/core/sync/atomic/type.AtomicU32.html#method.compare_exchange_weak)). A spurious failure is an `Err` return, not a panic. |
| atomic.rs:250 (same macro) | `swap` -> `Atomic*::swap(v, SeqCst)`. Same instantiations | external_body | no_unwind | no_panic | "All ordering modes are possible". Docs list no panics. No allocation. |
| atomic.rs:262 (same macro) | `into_inner` -> `Atomic*::into_inner`. Same instantiations | external_body | no_unwind | no_panic | Docs list no panics (the implementation is a `transmute`). No allocation. |
| atomic.rs:288 (macro `atomic_integer_methods`) | `fetch_add_wrapping` -> `AtomicN::fetch_add(n, SeqCst)`. Instantiated for U8/U16/U32/U64/Usize, I8/I16/I32/I64/Isize | external_body | no_unwind | no_panic | Docs: "This operation wraps around on overflow." Docs list no panics ([fetch_add](https://doc.rust-lang.org/stable/core/sync/atomic/type.AtomicU32.html#method.fetch_add)). |
| atomic.rs:303 (same macro) | `fetch_sub_wrapping` -> `AtomicN::fetch_sub(n, SeqCst)`. Same instantiations | external_body | no_unwind | no_panic | "wraps around on overflow". Docs list no panics. |
| atomic.rs:323 (same macro) | `fetch_add`: vstd wrapper, no direct Rust counterpart | verified (calls `self.fetch_add_wrapping`) | no_unwind | no_panic | The body only calls fetch_add_wrapping (line 288). It verifies as no_panic once 288 is no_panic. |
| atomic.rs:340 (same macro) | `fetch_sub`: vstd wrapper | verified (calls `self.fetch_sub_wrapping`) | no_unwind | no_panic | The body only calls fetch_sub_wrapping (line 303). |
| atomic.rs:355 (same macro) | `fetch_and` -> `AtomicN::fetch_and(n, SeqCst)` | external_body | no_unwind | no_panic | Docs list no panics. No allocation. |
| atomic.rs:370 (same macro) | `fetch_or` -> `AtomicN::fetch_or` | external_body | no_unwind | no_panic | Docs list no panics. No allocation. |
| atomic.rs:385 (same macro) | `fetch_xor` -> `AtomicN::fetch_xor` | external_body | no_unwind | no_panic | Docs list no panics. No allocation. |
| atomic.rs:400 (same macro) | `fetch_nand` -> `AtomicN::fetch_nand` | external_body | no_unwind | no_panic | Docs list no panics. No allocation. |
| atomic.rs:415 (same macro) | `fetch_max` -> `AtomicN::fetch_max` | external_body | no_unwind | no_panic | Docs list no panics. No allocation. |
| atomic.rs:430 (same macro) | `fetch_min` -> `AtomicN::fetch_min` | external_body | no_unwind | no_panic | Docs list no panics. No allocation. |
| atomic.rs:454 (macro `atomic_bool_methods`, PAtomicBool only) | `fetch_and` -> `AtomicBool::fetch_and(n, SeqCst)` | external_body | no_unwind | no_panic | Docs list no panics. No allocation. |
| atomic.rs:470 (same) | `fetch_or` -> `AtomicBool::fetch_or` | external_body | no_unwind | no_panic | Docs list no panics. No allocation. |
| atomic.rs:486 (same) | `fetch_xor` -> `AtomicBool::fetch_xor` | external_body | no_unwind | no_panic | Docs list no panics. No allocation. |
| atomic.rs:502 (same) | `fetch_nand` -> `AtomicBool::fetch_nand` | external_body | no_unwind | no_panic | Docs list no panics. No allocation. |
| atomic.rs:554 (macro `ptr_atomic_methods`) | `from_ptr_store` -> `unsafe AtomicN::from_ptr(ptr).store(v, SeqCst)`. Instantiated for PAtomicU8/U16/U32/U64/Usize, I8/I16/I32/I64/Isize, each under `cfg(target_has_atomic_primitive_alignment = width)` | external_body | no_unwind | no_panic | from_ptr's safety requires alignment to `align_of::<AtomicN>()` ([from_ptr](https://doc.rust-lang.org/stable/core/sync/atomic/type.AtomicU32.html#method.from_ptr)). The cfg plus the const assert make that equal to `align_of::<N>()`, and `PointsTo::is_aligned`/`is_nonnull` (raw_ptr.rs:272/278) cover it. The body is `&*ptr.cast()` (no panic). Store uses SeqCst. |
| atomic.rs:570 (same macro) | `from_ptr_load` -> `from_ptr(ptr).load(SeqCst)` | external_body | no_unwind | no_panic | As above. Load uses SeqCst. `requires perm.is_init()`. |
| atomic.rs:592 (same macro) | `from_ptr_swap` -> `from_ptr(ptr).swap(v, SeqCst)` | external_body | no_unwind | no_panic | As above. Swap allows any ordering. |
| atomic.rs:1231 | `PAtomicPtr<T>::fetch_and` -> `AtomicPtr::fetch_and(n, SeqCst)` | external_body | no_unwind | no_panic | Docs list no panics ([AtomicPtr::fetch_and](https://doc.rust-lang.org/stable/core/sync/atomic/type.AtomicPtr.html#method.fetch_and)). Stable since 1.91. No allocation. |
| atomic.rs:1251 | `PAtomicPtr<T>::fetch_xor` -> `AtomicPtr::fetch_xor` | external_body | no_unwind | no_panic | Same as above. |
| atomic.rs:1270 | `PAtomicPtr<T>::fetch_or` -> `AtomicPtr::fetch_or` | external_body | no_unwind | no_panic | Same as above. |
| cell.rs:194 | (deprecated) `cell::PCell::put`: raw write `*ucell.get() = MaybeUninit::new(v)` | external_body | no_unwind | no_panic | The overwritten `MaybeUninit` has no drop glue, so no user Drop runs. Raw deref of a valid `UnsafeCell::get` pointer. No allocation. |
| cell.rs:212 | `cell::PCell::take`: `mem::swap` + `assume_init` | external_body | no_unwind | no_panic | `mem::swap` docs list no panics. `assume_init` only has `assert_inhabited` (nounwind, fires only for uninhabited V), and `requires old(perm).is_init()` rules that out. |
| cell.rs:232 | `cell::PCell::replace`: `mem::swap` + `assume_init` | external_body | no_unwind | no_panic | Same as take. |
| cell.rs:253 | `cell::PCell::borrow`: `assume_init_ref` | external_body | no_unwind | no_panic | `requires perm.is_init()`. No allocation. |
| cell.rs:268 | `cell::PCell::into_inner` | verified (calls `self.take`) | no_unwind | no_panic | Calls take (212). Dropping `self` is dropping `UnsafeCell<MaybeUninit<V>>`, which has no drop glue. |
| cell.rs:287 | `cell::PCell::borrow_mut`: `assume_init_mut` | external_body | no_unwind | no_panic | `requires perm.is_init()`. No allocation. |
| cell.rs:304 | `cell::PCell::write` (V: Copy) | verified (calls `self.replace`) | no_unwind | no_panic | Calls replace (232). `_out: V` is Copy, so nothing is dropped. |
| cell/pcell.rs:146 | `pcell::PCell::new`: `ManuallyDrop::new(UnsafeCell::new(v))` | external_body | no_unwind | no_panic | The value is stored inline. **No Box, no allocation.** `UnsafeCell::new`/`ManuallyDrop::new` are const wrappers with no listed panics. |
| cell/pcell.rs:160 | `pcell::PCell::borrow`: `&*(*ucell).get()` | external_body | no_unwind | no_panic | A reference from a valid pointer. Docs list no panics. |
| cell/pcell.rs:176 | `pcell::PCell::borrow_mut`: `&mut *(*ucell).get()` | external_body | no_unwind | no_panic | Same as borrow. |
| cell/pcell.rs:191 | `pcell::PCell::into_inner`: `ManuallyDrop::into_inner(..).into_inner()` | external_body | no_unwind | no_panic | Moves the value out. Docs list no panics. No drop. |
| cell/pcell.rs:210 | `pcell::PCell::replace` | verified (calls `core::mem::swap` (std_specs/core.rs:177, no_unwind) and `self.borrow_mut`) | no_unwind | no_panic | Needs std_specs/core.rs:177 `mem::swap` to become no_panic too (another group's site). `mem::swap` has no Panics section and doesn't allocate. |
| cell/pcell.rs:226 | `pcell::PCell::write` | verified (calls `self.replace`, then **drops `_out: T`**) | no_unwind | no_panic (with caveat) | The body runs the user's `Drop for T` on the old value. Under Verus' "destructors don't panic" assumption this is fine. Without it, even `no_unwind` would be wrong. See Concerns. |
| cell/pcell.rs:239 | `pcell::PCell::read` (T: Copy) | verified (`*self.borrow(..)`) | no_unwind | no_panic | Calls borrow (160), then a Copy deref. |
| cell/pcell_maybe_uninit.rs:135 | `pcell_maybe_uninit::PCell::put` | verified (`pc::PCell::replace` + `MaybeUninit::new`) | no_unwind | no_panic | The discarded `MaybeUninit<V>` has no drop glue, so no user Drop runs. Needs std_specs/maybe_uninit.rs `MaybeUninit::new` to become no_panic. |
| cell/pcell_maybe_uninit.rs:150 | `::take` | verified (`pc::PCell::replace`, `MaybeUninit::uninit`, `assume_init`) | no_unwind | no_panic | `requires is_init`. Needs the std_specs/maybe_uninit.rs `uninit` and `assume_init` specs to become no_panic. |
| cell/pcell_maybe_uninit.rs:167 | `::replace` | verified (`pc::PCell::replace`, `MaybeUninit::new`, `assume_init`) | no_unwind | no_panic | Same as take. |
| cell/pcell_maybe_uninit.rs:182 | `::borrow` | verified (`pc::PCell::borrow`, `assume_init_ref`) | no_unwind | no_panic | `requires is_init`. Depends on the maybe_uninit.rs:45 spec. |
| cell/pcell_maybe_uninit.rs:200 | `::borrow_mut` | verified (`pc::PCell::borrow_mut`, `assume_init_mut`) | no_unwind | no_panic | `requires is_init`. Depends on the maybe_uninit.rs:51 spec. |
| cell/pcell_maybe_uninit.rs:215 | `::into_inner` | verified (calls `self.take`) | no_unwind | no_panic | Dropping `self` is dropping `pc::PCell<MaybeUninit<V>>`, which is `ManuallyDrop` with no drop glue. |
| cell/pcell_maybe_uninit.rs:229 | `::write` | verified (`pc::PCell::replace` + `MaybeUninit::new`) | no_unwind | no_panic | The old `MaybeUninit<V>` is discarded without a drop (the old value is leaked, not dropped). |
| cell/pcell_maybe_uninit.rs:243 | `::read` (V: Copy) | verified (`*self.borrow`) | no_unwind | no_panic | Calls borrow (182). |
| std_specs/atomic.rs:28 (macro `atomic_specs_common`) | `<Atomic{U8,U16,U32,U64,Usize,I8,I16,I32,I64,Isize,Bool}>::new` | assume_spec | no_unwind | no_panic | Docs list no panics ("Creates a new atomic integer"). The implementation is a `transmute`. |
| std_specs/atomic.rs:40 (same) | `::compare_exchange(atomic, cur, new, success, failure)` | assume_spec | no_unwind (+ `requires failure != Release, failure != AcqRel`) | no_panic | Docs: "The failure ordering can only be SeqCst, Acquire or Relaxed" (no Panics section). The source panics on `(_, AcqRel)`/`(_, Release)`, and the existing requires rules out both. |
| std_specs/atomic.rs:52 (same) | `::compare_exchange_weak` | assume_spec | no_unwind (+ same requires) | no_panic | Same as compare_exchange. |
| std_specs/atomic.rs:55 (same) | `::fetch_and` | assume_spec | no_unwind | no_panic | "All ordering modes are possible". Docs list no panics. No allocation. |
| std_specs/atomic.rs:58 (same) | `::fetch_nand` | assume_spec | no_unwind | no_panic | Same as fetch_and. |
| std_specs/atomic.rs:61 (same) | `::fetch_or` | assume_spec | no_unwind | no_panic | Same as fetch_and. |
| std_specs/atomic.rs:64 (same) | `::fetch_xor` | assume_spec | no_unwind | no_panic | Same as fetch_and. |
| std_specs/atomic.rs:70 (same) | `::load(atomic, order)` | assume_spec | no_unwind (+ `requires order != Release, order != AcqRel`) | no_panic | "Panics if `order` is Release or AcqRel" ([load](https://doc.rust-lang.org/stable/core/sync/atomic/type.AtomicU32.html#method.load)). The requires rules out both. |
| std_specs/atomic.rs:76 (same) | `::store(atomic, val, order)` | assume_spec | no_unwind (+ `requires order != Acquire, order != AcqRel`) | no_panic | "Panics if `order` is Acquire or AcqRel" ([store](https://doc.rust-lang.org/stable/core/sync/atomic/type.AtomicU32.html#method.store)). The requires rules out both. |
| std_specs/atomic.rs:79 (same) | `::swap` | assume_spec | no_unwind | no_panic | "All ordering modes are possible". Docs list no panics. |
| std_specs/atomic.rs:90 (macro `atomic_specs_int_specific`; ints only, not Bool) | `::fetch_add` | assume_spec | no_unwind | no_panic | "This operation wraps around on overflow." Docs list no panics. |
| std_specs/atomic.rs:93 (same) | `::fetch_sub` | assume_spec | no_unwind | no_panic | "wraps around on overflow". Docs list no panics. |
| std_specs/atomic.rs:96 (same) | `::fetch_min` | assume_spec | no_unwind | no_panic | Docs list no panics. No allocation. |
| std_specs/atomic.rs:99 (same) | `::fetch_max` | assume_spec | no_unwind | no_panic | Docs list no panics. No allocation. |

### Candidates for requires[no_panic]
- **std_specs/atomic.rs:70 `load`:** `requires order != Release && order != AcqRel` could become `requires[no_panic exact]`, because the docs guarantee "Panics if `order` is Release or AcqRel" (a panic, not UB).
- **std_specs/atomic.rs:76 `store`:** same idea for `order != Acquire && order != AcqRel`. The docs guarantee "Panics if `order` is Acquire or AcqRel".
- **std_specs/atomic.rs:40/52 `compare_exchange(_weak)`:** *not* recommended. The docs only say "The failure ordering can only be SeqCst, Acquire or Relaxed" and have no Panics section. The current implementation panics, but the docs don't guarantee it, so keep the plain `requires`.
- The default recommendation for all of the above is still to keep the `requires` and add `no_panic`.

### Concerns
1. **cell/pcell.rs:226 `pcell::PCell::write` drops a user value.** `let _out = self.replace(..)` drops the old `T` (no `Copy` bound), which runs the user's `Drop`. The current `no_unwind`, and a future `no_panic`, are only sound under Verus' assumption that destructors don't panic. In comparison, `pcell_maybe_uninit::write`/`put` discard a `MaybeUninit<V>` (no drop glue), and `cell::PCell::write` requires `V: Copy`.
2. **Verified bodies depend on specs outside group B.** These must also become `no_panic`, or the verified bodies here will fail as `no_panic`:
   - `core::mem::swap` (std_specs/core.rs:177), used by pcell.rs:210 `replace` and so transitively by `write` and all of pcell_maybe_uninit.
   - `MaybeUninit::{new, uninit, assume_init, assume_init_ref, assume_init_mut}` (std_specs/maybe_uninit.rs:29/34/39/45/51), used by pcell_maybe_uninit.rs.

   `assume_init*` contain `intrinsics::assert_inhabited::<T>()` (`#[rustc_nounwind]`, so it panics without unwinding when T is uninhabited). The existing `requires is_init` rules that out, so `no_panic` is still fine for them.
3. **The from_ptr_* bodies rely on `PointsTo::is_aligned`/`is_nonnull`**, which are proof axioms. The external_body doesn't call them explicitly, but they are what rules out from_ptr's UB and the nounwind null/misalignment UB-check panics that rustc may insert on `&*ptr`. This is an argument from the trusted spec, not from a requires clause. It looks fine; I'm noting it for the reviewer.
4. **Minor: `cfg(any(verus_keep_ghost, feature = "strict_provenance_atomic_ptr"))` on atomic.rs:1225-1276 looks stale.** `AtomicPtr::fetch_and/or/xor` have been stable since 1.91. This doesn't affect panic behavior.
5. **Constructors without `no_unwind` (not in the list, FYI):** `atomic_common_methods::new` (atomic.rs:~155), `cell::PCell::{empty,new}` (cell.rs:~170/~180) and `pcell_maybe_uninit::PCell::{empty,new}` (verified, call `pc::PCell::new`) have no unwind spec. None of them allocates, so they could all be marked `no_panic` if wanted.
6. No existing `no_unwind` in this group looks wrong. None of these sites allocates, and none can panic under its existing requires.

## Audit group C: raw_ptr.rs, simple_pptr.rs, layout.rs, std_specs/ptr.rs, std_specs/maybe_uninit.rs

Paths are relative to `source/vstd`. The 1.100.0 toolchain has no rust-src locally, so I read the std source from the 1.98.1 rust-src (`~/.rustup/toolchains/1.98.1-*/lib/rustlib/src/rust/library/core/src`). I spot-checked the 1.100.0 docs for `ptr::write`: still no Panics section.

Background on std debug checks: `ub_checks::assert_unsafe_precondition!` (`core/src/ub_checks.rs`) is gated on `check_language_ub()`, which is on in debug builds. On failure it calls `panic_nounwind_fmt`, so it panics by aborting (the panic hook runs, then the process aborts). The same applies to the `assert_inhabited` intrinsic (`#[rustc_nounwind]`) and to the compiler-inserted debug MIR checks for misaligned or null pointer dereference. None of these can unwind, but all of them count as panics under the new model. So `no_panic` is sound only when the existing `requires` rules out the checked condition. Where the checked condition is UB rather than a guaranteed panic (the docs say the check "is optional, and cannot be relied on for safety"), it is **not** a `requires[no_panic]` candidate.

| file:line | item (and Rust path) | kind | current | recommendation | justification |
|---|---|---|---|---|---|
| layout.rs:81 | `core::mem::size_of::<V>` | assume_spec | no_unwind | no_panic | `const fn` that returns a compile-time constant. Docs list no panics; no allocation. https://doc.rust-lang.org/1.100.0/core/mem/fn.size_of.html |
| layout.rs:89 | `core::mem::align_of::<V>` | assume_spec | no_unwind | no_panic | `const fn`, compile-time constant. Docs list no panics; no allocation. https://doc.rust-lang.org/1.100.0/core/mem/fn.align_of.html |
| layout.rs:97 | `core::mem::size_of_val::<V: ?Sized>` | assume_spec | no_unwind | no_panic | Computed from the metadata of a valid `&V`. For slices the result is bounded by isize::MAX by the validity of the reference, and the intrinsic does no checked arithmetic. `?Sized` (now MetaSized) excludes extern types. Docs list no panics; no allocation. https://doc.rust-lang.org/1.100.0/core/mem/fn.size_of_val.html |
| layout.rs:105 | `core::mem::align_of_val::<V: ?Sized>` | assume_spec | no_unwind | no_panic | Same reasoning as `size_of_val`. Docs list no panics; no allocation. https://doc.rust-lang.org/1.100.0/core/mem/fn.align_of_val.html |
| layout.rs:126 | `layout_for_type_is_valid<V>` (vstd lemma, no Rust counterpart) | external_body | no_unwind | no_panic | Body is empty `{}`, so it is a no-op. |
| layout.rs:149 | `layout_for_val_is_valid<V>` (vstd lemma) | external_body | no_unwind | no_panic | Body is empty `{}`. Its argument is `Tracked`, which is erased. |
| raw_ptr.rs:407 | `core::ptr::null::<T>` | assume_spec | no_unwind | no_panic | `const fn` that builds a null pointer. Docs list no panics; no allocation. https://doc.rust-lang.org/1.100.0/core/ptr/fn.null.html |
| raw_ptr.rs:428 | `core::ptr::null_mut::<T>` | assume_spec | no_unwind | no_panic | Same as `null`. https://doc.rust-lang.org/1.100.0/core/ptr/fn.null_mut.html |
| raw_ptr.rs:450 | `cast_ptr_to_thin_ptr` (body: `ptr as *mut U`) | external_body | no_unwind | no_panic | A pointer `as`-cast is a compiler primitive that cannot panic. |
| raw_ptr.rs:472 | `cast_array_ptr_to_slice_ptr` (`ptr as *mut [T]`) | external_body | no_unwind | no_panic | Unsizing pointer cast, cannot panic. |
| raw_ptr.rs:496 | `cast_slice_ptr_to_slice_ptr` (`ptr as *mut [U]`) | external_body | no_unwind | no_panic | Metadata-preserving pointer cast, cannot panic. |
| raw_ptr.rs:520 | `cast_slice_ptr_to_str_ptr` (`ptr as *mut str`) | external_body | no_unwind | no_panic | Pointer cast, cannot panic. |
| raw_ptr.rs:544 | `cast_str_ptr_to_slice_ptr` (`ptr as *mut [T]`) | external_body | no_unwind | no_panic | Pointer cast, cannot panic. |
| raw_ptr.rs:564 | `cast_ptr_to_usize` (`ptr as usize`) | external_body | no_unwind | no_panic | Pointer-to-int cast, cannot panic. |
| raw_ptr.rs:586 | `ptr_mut_write` (body: `core::ptr::write`) | external_body | no_unwind | no_panic | Docs have no Panics section, but in debug builds there is a `check_language_ub` precondition "ptr::write requires that the pointer argument is aligned and non-null" that aborts via `panic_nounwind`. `requires old(perm).ptr() == ptr`, and the `PointsTo` axioms `is_nonnull` and `is_aligned` (raw_ptr.rs:272/278) rule that out. Does not drop the old contents. https://doc.rust-lang.org/1.100.0/core/ptr/fn.write.html |
| raw_ptr.rs:611 | `ptr_mut_read` (body: `core::ptr::read`) | external_body | no_unwind | no_panic | Same as `ptr::write`: a debug-only aligned/non-null check, ruled out by `perm.ptr() == ptr` plus the PointsTo nonnull/aligned axioms. Bitwise read, no user code. https://doc.rust-lang.org/1.100.0/core/ptr/fn.read.html |
| raw_ptr.rs:627 | `ptr_ref` (body: `&*ptr`) | external_body | no_unwind | no_panic | The only possible panics are the compiler's debug null/misaligned dereference checks, which are nounwind. The requires plus the PointsTo axioms make the pointer non-null and aligned. |
| raw_ptr.rs:646 | `ptr_mut_ref` (body: `&mut *ptr`) | external_body | no_unwind | no_panic | Same as `ptr_ref`. |
| raw_ptr.rs:667 | `<*mut T>::addr` and `<*const T>::addr` (macro `pointer_specs!`, instantiated for `mut` and `const`) | assume_spec | no_unwind | no_panic | Body is a pointer-to-int transmute. Docs list no panics; no allocation. https://doc.rust-lang.org/1.100.0/core/primitive.pointer.html#method.addr |
| raw_ptr.rs:678 | `<*mut T>::with_addr` and `<*const T>::with_addr` (same macro, both instantiations) | assume_spec | no_unwind | no_panic | Body uses `wrapping_sub` and `wrapping_byte_offset`, so there is no overflow panic. Docs list no panics; no allocation. https://doc.rust-lang.org/1.100.0/core/primitive.pointer.html#method.with_addr |
| raw_ptr.rs:735 | `expose_provenance` (body: `m as usize; Tracked::assume_new()`) | external_body | no_unwind | no_panic | Pointer-to-int cast, plus `Tracked::assume_new`, a `const fn` that builds a PhantomData (builtin/src/lib.rs:695). |
| raw_ptr.rs:753 | `with_exposed_provenance` (body: `addr as *mut T`) | external_body | no_unwind | no_panic | Int-to-pointer cast, cannot panic. |
| raw_ptr.rs:1048 | `ptr_ref2` (body: `SharedReference(&*ptr)`) | external_body | no_unwind | no_panic | Same as `ptr_ref`. |
| simple_pptr.rs:470 | `PPtr::put` | verified | no_unwind | no_panic | Calls `with_exposed_provenance` and `ptr_mut_write`, both recommended no_panic. Proof blocks are erased. |
| simple_pptr.rs:496 | `PPtr::take` | verified | no_unwind | no_panic | Calls `with_exposed_provenance` and `ptr_mut_read`, both no_panic. |
| simple_pptr.rs:517 | `PPtr::replace` | verified | no_unwind | no_panic | Calls `with_exposed_provenance`, `ptr_mut_read` and `ptr_mut_write`, all no_panic. Nothing is dropped. |
| simple_pptr.rs:537 | `PPtr::borrow` | verified | no_unwind | no_panic | Calls `with_exposed_provenance` and `ptr_ref`, both no_panic. |
| simple_pptr.rs:558 | `PPtr::borrow_mut` | verified | no_unwind | no_panic | Calls `with_exposed_provenance` and `ptr_mut_ref`, both no_panic. |
| simple_pptr.rs:575 | `PPtr::write` (V: Copy) | verified | no_unwind | no_panic | Calls `put` (no_panic). `leak_contents` is proof code, and the old value is Copy, so there is no drop. |
| simple_pptr.rs:592 | `PPtr::read` (V: Copy) | verified | no_unwind | no_panic | `*self.borrow(..)`: `borrow` is no_panic, and a Copy read is bitwise with no user `Clone` call. |
| std_specs/maybe_uninit.rs:32 | `MaybeUninit::<T>::new` | assume_spec | no_unwind | no_panic | `const fn` wrapping the value in a union. Docs list no panics; no allocation. https://doc.rust-lang.org/1.100.0/core/mem/union.MaybeUninit.html#method.new |
| std_specs/maybe_uninit.rs:37 | `MaybeUninit::<T>::uninit` | assume_spec | no_unwind | no_panic | `const fn`. Docs list no panics; no allocation. https://doc.rust-lang.org/1.100.0/core/mem/union.MaybeUninit.html#method.uninit |
| std_specs/maybe_uninit.rs:43 | `MaybeUninit::<T>::assume_init` | assume_spec | no_unwind | no_panic | Body runs `intrinsics::assert_inhabited::<T>()` (nounwind; panics statically only for uninhabited T), then a transmute. `requires m.mem_contents().is_init()` can only be established from a real exec `T` value (via `new`/`write`), so T is inhabited whenever it is satisfiable. See Concerns. https://doc.rust-lang.org/1.100.0/core/mem/union.MaybeUninit.html#method.assume_init |
| std_specs/maybe_uninit.rs:49 | `MaybeUninit::<T>::assume_init_ref` | assume_spec | no_unwind | no_panic | Same `assert_inhabited::<T>()` guard, same argument as `assume_init`. |
| std_specs/maybe_uninit.rs:57 | `MaybeUninit::<T>::assume_init_mut` | assume_spec | no_unwind | no_panic | Same `assert_inhabited::<T>()` guard, same argument. |
| std_specs/maybe_uninit.rs:64 | `MaybeUninit::<T>::write` | assume_spec | no_unwind | no_panic | Overwrites without dropping the old contents, so no user code runs. Docs list no panics; no allocation. https://doc.rust-lang.org/1.100.0/core/mem/union.MaybeUninit.html#method.write |
| std_specs/maybe_uninit.rs:74 | `MaybeUninit::<T>::array_assume_init::<N>` | assume_spec | no_unwind | no_panic | `assert_inhabited::<[T; N]>()` then `transmute_unchecked`. For N == 0 the array type is inhabited. For N > 0 the requires (every element init) implies T is inhabited, as for `assume_init`. Note that this method is unstable (`maybe_uninit_array_assume_init`). |
| std_specs/ptr.rs:23 | `NonNull::<T>::as_ptr` | assume_spec | no_unwind | no_panic | `const fn` returning the inner pointer. Docs list no panics; no allocation. https://doc.rust-lang.org/1.100.0/core/ptr/struct.NonNull.html#method.as_ptr |
| std_specs/ptr.rs:29 | `NonNull::<T>::new_unchecked` | assume_spec | no_unwind | no_panic | Has a debug `check_language_ub` precondition "NonNull::new_unchecked requires that the pointer is non-null" that aborts via panic_nounwind. The existing `requires ptr@.addr != 0` rules it out. https://doc.rust-lang.org/1.100.0/core/ptr/struct.NonNull.html#method.new_unchecked |
| std_specs/ptr.rs:37 | `NonNull::<T>::new` | assume_spec | no_unwind | no_panic | Checks for null and returns None. It calls `new_unchecked` only on the non-null branch, so the debug check cannot fire. Docs list no panics. https://doc.rust-lang.org/1.100.0/core/ptr/struct.NonNull.html#method.new |

### Candidates for requires[no_panic]
- None. Every panic path in this group is an optional debug UB check: `assert_unsafe_precondition!` in `ptr::read`/`ptr::write`/`NonNull::new_unchecked`, the compiler's null/misaligned dereference checks for `&*ptr`, and `assert_inhabited`. Violating those conditions is UB, not a guaranteed panic ("This Undefined Behavior check is optional, and cannot be relied on for safety", core/src/ub_checks.rs). The plain `requires` must stay.

### Concerns
- None of the sites in this group allocate or deallocate. `PPtr::empty`, `PPtr::new`, `PPtr::free` and `into_inner` (simple_pptr.rs, around lines 347-455) call `allocate`/`deallocate` and are correctly **not** `no_unwind` today. They should stay unannotated, or at most `no_unwind` if the allocator wrappers are shown not to unwind; they must not become `no_panic`. `into_inner` calls `take` (no_panic) and `free` (may panic), so it must stay may-panic.
- The verified bodies in simple_pptr (`put`, `take`, `replace`, `borrow`, `borrow_mut`, `write`, `read`) only verify as `no_panic` if `with_exposed_provenance`, `ptr_mut_write`, `ptr_mut_read`, `ptr_ref` and `ptr_mut_ref` all become `no_panic` in the same change. They should be converted together.
- `assume_init`, `assume_init_ref`, `assume_init_mut` and `array_assume_init`: the `no_panic` claim for uninhabited `T` depends on Verus never letting `mem_contents().is_init()` be proven for an uninhabited T. Verus spec types are inhabited, but `mem_contents` is uninterp and only `new`/`write` (which need an exec `T`) produce `Init`. This holds today. Any future axiom that produces an init `MaybeUninit<T>` without an exec T, such as an exec `zeroed()` spec, would make these specs unsound, because they would then abort via `assert_inhabited`.
- The `no_panic` recommendations for `ptr_mut_write`, `ptr_mut_read`, `ptr_ref`, `ptr_mut_ref` and `ptr_ref2` depend on the `PointsTo::is_nonnull` and `is_aligned` axioms (raw_ptr.rs:272/278), which cover ZSTs too. They do not depend on the raw `requires` alone.
- I could not inspect the 1.100.0 std source locally (no rust-src). I used the 1.98.1 source plus the 1.100.0 online docs. These functions are not known to have changed.

## Audit group D: vstd slice / vec / array / string / option / result / control_flow

Paths are relative to `source/vstd`. Docs are Rust 1.100.0 (`https://doc.rust-lang.org/1.100.0/...`).
General note: every `core` item below (slice, array, str, Option, Result, ControlFlow) lives in `core`, which has no access to the global allocator. The `alloc` items (`Vec::len`, `as_slice`, `as_mut_slice`, `is_empty`, `AsRef`, `String::as_str`, `is_empty`) only read the len and ptr fields and never call `A: Allocator`.

| file:line | item (and Rust path) | kind | current | recommendation | justification |
|---|---|---|---|---|---|
| array.rs:127 | `<[T; N]>::as_slice` (`core::array`, `[T; N]::as_slice`) | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/std/primitive.array.html#method.as_slice): "Equivalent to `&s[..]`". The docs list no panics, and it doesn't allocate. |
| array.rs:182 | `ref_mut_array_unsizing_coercion` (`&mut [T; N]` to `&mut [T]` unsizing coercion; body `r`) | external_body | no_unwind | no_panic | This is a built-in unsizing coercion with no code path that can panic, and it doesn't allocate. |
| slice.rs:87 | `<[T]>::len` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/std/primitive.slice.html#method.len): docs list no panics; no allocation. |
| slice.rs:99 | `<[T]>::is_empty` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/std/primitive.slice.html#method.is_empty): docs list no panics; no allocation. |
| std_specs/control_flow.rs:40 | `Try::branch` trait spec (`core::ops::Try::branch`); impls: `Option<T>`, `Result<T,E>`, `ControlFlow<B,C>`, all with `may_unwind = false` | trait spec (ext trait; impl assume_specs at :162, :193, :202 inherit it) | `ensures[on panic] self.may_unwind()` | keep (faithful) | Each of the three `branch` impls is just a `match` that moves the payload, with no user code and no allocation, so "never panics" (`may_unwind = false`) is correct. Since impls inherit `ensures[on panic]` and can't declare their own (see the well_formed.rs check), callers of `?` on these types get no-panic. For generic `T: Try`, the clause is never checked at call sites, so a caller only learns "panic implies may_unwind". That is sound. |
| std_specs/control_flow.rs:56 | `FromResidual::from_residual` trait spec; impls: `Option<T>` from `Option<Infallible>` (false), `ControlFlow<B,C>` from `ControlFlow<B,Infallible>` (false), `Result<T,F>` from `Result<Infallible,E>` (true) | trait spec (impl assume_specs at :213, :220, :237) | `ensures[on panic] Self::may_unwind(&residual)` | keep (faithful) | Option and ControlFlow: they only rewrap the residual (`None` / `Break(b)`), so they can't panic. Result: it calls the user's `F::from(e)`, which may panic, so `true` is correct and conservative. (`true` could be refined, for example to `false` when `F = E` via the blanket identity `From`, but this isn't needed.) |
| std_specs/option.rs:126 | `Option::is_some` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/core/option/enum.Option.html#method.is_some): docs list no panics; no allocation. |
| std_specs/option.rs:139 | `Option::is_none` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/core/option/enum.Option.html#method.is_none): docs list no panics; no allocation. |
| std_specs/option.rs:147 | `Option::as_ref` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/core/option/enum.Option.html#method.as_ref): docs list no panics; no allocation. |
| std_specs/option.rs:180 | `Option::unwrap_or` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/core/option/enum.Option.html#method.unwrap_or): docs list no panics; no allocation in `core`. It drops `default` when `self` is `Some`, which runs `T`'s destructor; Verus assumes destructors don't panic. |
| std_specs/option.rs:205 | `Option::take` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/core/option/enum.Option.html#method.take): docs list no panics; no allocation. It's a `mem::replace` with no drop. |
| std_specs/result.rs:138 | `Result::is_ok` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/core/result/enum.Result.html#method.is_ok): docs list no panics; no allocation. |
| std_specs/result.rs:151 | `Result::is_err` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/core/result/enum.Result.html#method.is_err): docs list no panics; no allocation. |
| std_specs/result.rs:164 | `Result::as_ref` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/core/result/enum.Result.html#method.as_ref): docs list no panics; no allocation. |
| std_specs/result.rs:460 | `Result::ok` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/core/result/enum.Result.html#method.ok): docs list no panics; no allocation in `core`. It drops `E` on `Err` ("converting the error to None"), which runs a destructor; Verus assumes destructors don't panic. |
| std_specs/result.rs:476 | `Result::err` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/core/result/enum.Result.html#method.err): docs list no panics; no allocation. It drops `T` on `Ok` ("discarding the success value"), which runs a destructor and is assumed not to panic. |
| std_specs/slice.rs:472 | `<[T]>::swap` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/std/primitive.slice.html#method.swap): "Panics if a or b are out of bounds." The existing `requires a < len, b < len` rules that out; no allocation. **Candidate** for `requires[no_panic exact]` (see below). |
| std_specs/slice.rs:481 | `<[T]>::rotate_left` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/std/primitive.slice.html#method.rotate_left): "This function will panic if mid is greater than the length of the slice." The `requires mid <= len` rules that out. It's in `core`, so it can't allocate. **Candidate**. |
| std_specs/slice.rs:490 | `<[T]>::rotate_right` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/std/primitive.slice.html#method.rotate_right): "This function will panic if k is greater than the length of the slice." The `requires k <= len` rules that out. **Candidate**. |
| std_specs/slice.rs:594 | `<[T]>::first` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/std/primitive.slice.html#method.first): docs list no panics (it returns `Option`); no allocation. |
| std_specs/slice.rs:601 | `<[T]>::last` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/std/primitive.slice.html#method.last): docs list no panics; no allocation. |
| std_specs/slice.rs:610 | `<[T]>::first_mut` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/std/primitive.slice.html#method.first_mut): docs list no panics; no allocation. |
| std_specs/slice.rs:619 | `<[T]>::last_mut` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/std/primitive.slice.html#method.last_mut): docs list no panics; no allocation. |
| std_specs/slice.rs:628 | `<[T]>::split_at` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/std/primitive.slice.html#method.split_at): "Panics if mid > len." The `requires mid <= len` rules that out. **Candidate**. |
| std_specs/slice.rs:639 | `<[T]>::split_at_mut` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/std/primitive.slice.html#method.split_at_mut): "Panics if mid > len." The `requires` rules that out. **Candidate**. |
| std_specs/slice.rs:650 | `<[T]>::split_at_checked` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/std/primitive.slice.html#method.split_at_checked): "if mid > len, returns None". Docs list no panics; no allocation. |
| std_specs/slice.rs:659 | `<[T]>::split_at_unchecked` (unsafe) | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/std/primitive.slice.html#method.split_at_unchecked): "Calling this method with an out-of-bounds index is undefined behavior". The `requires` must stay a hard precondition because violating it is UB, not a panic. Docs list no panics. |
| std_specs/slice.rs:670 | `<[T]>::split_at_mut_unchecked` (unsafe) | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/std/primitive.slice.html#method.split_at_mut_unchecked): same UB-on-OOB wording, so keep the hard `requires`. Docs list no panics. |
| std_specs/slice.rs:677 | `<[T]>::split_first` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/std/primitive.slice.html#method.split_first): docs list no panics; no allocation. |
| std_specs/slice.rs:689 | `<[T]>::split_first_mut` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/std/primitive.slice.html#method.split_first_mut): docs list no panics; no allocation. |
| std_specs/vec.rs:58 | `vec_index` (`vec[i]` for `usize`, using `<Vec<T,A> as Index<usize>>::index`, which delegates to slice indexing) | external_body | no_unwind | no_panic | Slice indexing with a `usize` panics only when out of bounds ([Index](https://doc.rust-lang.org/1.100.0/core/ops/trait.Index.html): "May panic if the index is out of bounds"). The `requires i < len` rules that out. It doesn't touch `A`. **Candidate** for `requires[no_panic exact]`. |
| std_specs/vec.rs:75 | `vec_index_mut` (`&mut vec[i]`, `IndexMut<usize>`) | external_body | no_unwind | no_panic | Same reasoning as `vec_index`: it panics only when out of bounds, which the `requires` rules out. No allocation. **Candidate**. |
| std_specs/vec.rs:96 | `Vec::<T,A>::len` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/alloc/vec/struct.Vec.html#method.len): docs list no panics. It's a field read with no allocator call. |
| std_specs/vec.rs:227 | `Vec::<T,A>::is_empty` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/alloc/vec/struct.Vec.html#method.is_empty): docs list no panics; no allocation. |
| std_specs/vec.rs:250 | `Vec::<T,A>::as_slice` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/alloc/vec/struct.Vec.html#method.as_slice): "Equivalent to `&s[..]`". Docs list no panics; no allocation. |
| std_specs/vec.rs:259 | `<Vec<T,A> as AsRef<[T]>>::as_ref` | assume_spec | no_unwind | no_panic | It returns `self` as a slice (same as `as_slice`). Docs list no panics; no allocation. |
| std_specs/vec.rs:268 | `Vec::<T,A>::as_mut_slice` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/alloc/vec/struct.Vec.html#method.as_mut_slice): "Equivalent to `&mut s[..]`". Docs list no panics; no allocation. |
| string.rs:131 | `str::as_bytes` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/std/primitive.str.html#method.as_bytes): docs list no panics; no allocation. |
| string.rs:140 | `str::len` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/std/primitive.str.html#method.len): docs list no panics; no allocation. |
| string.rs:149 | `str::is_empty` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/std/primitive.str.html#method.is_empty): docs list no panics; no allocation. |
| string.rs:392 | `String::as_str` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/alloc/string/struct.String.html#method.as_str): docs list no panics; no allocation. |
| string.rs:444 | `String::is_empty` | assume_spec | no_unwind | no_panic | [docs](https://doc.rust-lang.org/1.100.0/alloc/string/struct.String.html#method.is_empty): docs list no panics; no allocation. |

### Candidates for requires[no_panic]

For each of these, the docs guarantee a panic (not UB) exactly when the current plain `requires` fails, so `requires[no_panic exact]` would be faithful. The default recommendation is still to keep the `requires` and add `no_panic`.
- `<[T]>::swap` (slice.rs:472): `a < len && b < len`.
- `<[T]>::rotate_left` (:481): `mid <= len`. `<[T]>::rotate_right` (:490): `k <= len`.
- `<[T]>::split_at` (:628) and `split_at_mut` (:639): `mid <= len`.
- `vec_index` / `vec_index_mut` (vec.rs:58/75): `i < len`. Bounds-checked slice indexing always panics when out of bounds.
- Not on the list (they have no current panic spec), but relevant: `Option::unwrap` / `Option::expect` (option.rs:160/:193; result.rs:177/:231) with `requires option is Some`. The [docs](https://doc.rust-lang.org/1.100.0/core/option/enum.Option.html#method.unwrap) say "Panics if the self value equals None", so `requires[no_panic exact] option is Some` would be faithful. The same holds for `Result::unwrap` / `expect` ("Panics if the value is an Err"). Formatting the panic message calls the user's `E: Debug`, but the call panics in that case either way, so `exact` still holds.
- NOT candidates: `split_at_unchecked` and `split_at_mut_unchecked`. When the precondition fails they cause UB, not a panic, so their `requires` must stay hard.

### Concerns

- None of the current `no_unwind` specs in this group look wrong, and every one can become `no_panic`.
- Destructors: `Option::unwrap_or` (drops `default`), `Result::ok` (drops `E`) and `Result::err` (drops `T`) run user or std destructors. Those destructors may deallocate through the global allocator, for example when dropping a `Vec` or `Box`. `no_panic` relies on Verus's existing assumption that drops don't panic. This doesn't block anything.
- control_flow.rs: the impl assume_specs for `branch` / `from_residual` (:162–:237) carry no panic spec of their own. Their no-panic guarantee comes entirely from the inherited trait-level `ensures[on panic] may_unwind()` with `may_unwind = false`. That's faithful, but as a result callers of these impls see `ensures[on panic] false` rather than `no_panic`. It might be worth confirming that the panic-path checking treats inherited `ensures[on panic] false` as equivalent to `no_panic`, for example when `?` is used inside a `no_panic` function or inside an open invariant.
- I didn't run any verified bodies. All the sites here are assume_spec or external_body, so switching to `no_panic` won't cause verification failures in vstd bodies.

