Notes taken (by Claude) on rustc's implementation of drop scopes.

# Rust drop order and scope semantics (rustc 1.98.1, editions 2021 and 2024)

This is a reference for adding explicit `Drop` nodes to Verus VIR. It covers the rules,
where rustc implements them, and runtime checks of the rules on `rustc 1.98.1 (48a229cea 2026-09-01)`.

## 0. Sources and abbreviations

| Abbrev | Path |
|---|---|
| `region.rs` | `/local/home/trhance/verus/source/rustc_hir_analysis/src/check/region.rs`. Builds the `ScopeTree`. Identical to upstream 1.98.1. |
| `mid/region.rs` | `~/.rustup/toolchains/1.98.1-aarch64-unknown-linux-gnu/lib/rustlib/rustc-src/rust/compiler/rustc_middle/src/middle/region.rs`. `Scope`, `ScopeData`, `ScopeTree`, `temporary_scope`. Not vendored. |
| `scope.rs` | `source/rustc_mir_build/src/builder/scope.rs`. The MIR-builder scope stack, drop scheduling, break/return/unwind. |
| `block.rs` | `source/rustc_mir_build/src/builder/block.rs` |
| `into.rs`, `as_place.rs`, `as_temp.rs`, `as_operand.rs`, `as_rvalue.rs`, `stmt.rs`, `category.rs` | `source/rustc_mir_build/src/builder/expr/*.rs` |
| `matches.rs` | `source/rustc_mir_build/src/builder/matches/mod.rs` |
| `builder/mod.rs` | `source/rustc_mir_build/src/builder/mod.rs` |
| `thir/expr.rs`, `thir/block.rs` | `source/rustc_mir_build/src/thir/cx/{expr,block}.rs` |
| `ast_lowering/expr.rs` | `<rustc-src>/compiler/rustc_ast_lowering/src/expr.rs`. Desugarings for `for`, `while`, `?`, destructuring assignment. |
| `elaborate_drops.rs` | `<rustc-src>/compiler/rustc_mir_transform/src/elaborate_drops.rs` |
| Reference | `~/.rustup/toolchains/1.98.1-*/share/doc/rust/html/reference/destructors.html`. This is the 1.98 copy of https://doc.rust-lang.org/reference/destructors.html. |

`<rustc-src>` means `~/.rustup/toolchains/1.98.1-aarch64-unknown-linux-gnu/lib/rustlib/rustc-src/rust`.

**Important 1.98 facts (they differ from older rustc and from older blog posts):**

* There is **no `rvalue_scopes.rs`** and **no `RvalueScopes`** any more. Lifetime extension is
  stored directly in `ScopeTree::extended_temp_scopes` (`mid/region.rs:229`), and
  `ScopeTree::temporary_scope` consults it first (`mid/region.rs:346-357`).
* THIR `Expr` no longer carries a precomputed `temp_lifetime`. It carries
  `temp_scope_id: ItemLocalId` (`thir/expr.rs:116`). The MIR builder calls
  `region_scope_tree.temporary_scope(temp_scope_id)` lazily, only when it actually needs a
  temporary for a place (`as_place.rs:507,542,593,643`).
* `ScopeData` has a `MatchGuard` variant (`mid/region.rs:138`). `if let` guards are stable
  since 1.95 (`rustc_feature/src/accepted.rs:248`) and let-chains since 1.88 (edition 2024 only
  in `if`/`while`). In 1.98, let-chains in **match guards** compile in edition 2021 too.
* `super let` is unstable (`unstable.rs:742`), but std's `pin!` and the `format_args!` lowering use it
  (`rustc_ast_lowering/src/format.rs:450,489`). Running `-Zunpretty=hir` shows that `pin!(e)` lowers to
  `'p: { super let mut pinned = e; break 'p unsafe { Pin::new_unchecked(&mut pinned) }; ... }`.
* Verus's local edits to `rustc_mir_build` (erasure, `two_phase_mutable_reference_tie`
  reordering, `verus_time_travel_prevention`, the irrefutable-let patch) do not change the scope or drop
  machinery described here. `region.rs` is unmodified.

---

## 1. The scope model

### 1.1 `ScopeData` variants (`mid/region.rs:112-142`)

| Variant | Created for | Role |
|---|---|---|
| `Node` | every HIR expr, stmt, block and arm that has a scope (`enter_node_scope_with_dtor`, `region.rs:740-749`) | ordinary nesting; this is the scope the MIR builder actually pushes |
| `Destruction` | pushed **as parent** of `Node(id)` iff `id` is a *terminating* node (`region.rs:745-747`) | a marker only. `default_temporary_scope` stops when it sees one and returns the **child `Node`** (`mid/region.rs:314-316`). The MIR builder never pushes `Destruction` scopes. |
| `CallSite` | body of every fn, closure, const, or inline const (`region.rs:754`) | the outermost scope. `return` targets it. |
| `Arguments` | directly inside `CallSite` (`region.rs:755`) | holds parameters and their bindings. They outlive the body. |
| `IfThen` | edition <= 2021 `if`, keyed by `then.hir_id` (`region.rs:355-382`) | covers cond + then (not else). It is the **var scope** of `if let` bindings. It is **not** a temporary boundary. |
| `IfThenRescope` | edition >= 2024 `if` (same place) | the same as `IfThen`, but it **is** a temporary boundary (`mid/region.rs:318-320`) |
| `MatchGuard` | each arm **with a guard**, keyed by `arm.hir_id` (`region.rs:205`) | covers guard + arm body. It is the var scope of `if let` guard bindings and a temporary boundary in all editions. |
| `Remainder(i)` | `let` statement number `i` in a block (`region.rs:106-110,130-134`) | the suffix of the block after `let` `i`. It is the var scope of that let's bindings and the target of lifetime extension. |

Rules from the code:

* **The parent chain:** `parent_map` (`mid/region.rs:218`) gives the lexical nesting. A
  `Remainder(i)` scope is entered *before* visiting the statement, so `let` `i` (including its
  initializer `Node`) and **all later statements and the tail** are children of `Remainder(i)`.
  Each later `Remainder(j)` nests inside `Remainder(i)` (`region.rs:124-135`).
* **The var scope:** `var_map[binding] = cx.var_parent` at the time the pattern is visited
  (`region.rs:45-54,215-222`). Use `ScopeTree::var_scope` (`mid/region.rs:279`).

### 1.2 `temporary_scope(expr)` (`mid/region.rs:305-357`)

```text
temporary_scope(e):
  if e ∈ extended_temp_scopes: return extended_temp_scopes[e]     // Some(scope) or None (= 'static, never dropped)
  id := Node(e)
  loop p := parent(id):
     Destruction            => return id          // id is Node(T) for the nearest terminating T
     IfThenRescope|MatchGuard => return p
     Node|CallSite|Arguments|IfThen|Remainder => id := p
```

So a non-extended temporary lives until the end of the **nearest enclosing terminating node**,
an `IfThenRescope` (edition 2024 `if`), or a `MatchGuard` scope, whichever is innermost.
`IfThen` (edition 2021) and `Remainder` are transparent.

### 1.3 How MIR building uses the tree

* `ExprKind::Scope { region_scope: Node(e) }` wraps every THIR expression (`thir/expr.rs:113-119`).
  Every `as_*`/`into` function enters it with `in_scope` (e.g. `into.rs:48-54`, `as_temp.rs:42-48`).
  So the MIR scope stack contains a `Node` scope for **every** expression, block (`block.rs:23`),
  statement (`block.rs:73-80`), let initializer (`block.rs:259-262`), and arm (`matches.rs:437`),
  plus `Remainder` (`block.rs:246`), `IfThen`/`IfThenRescope` (`into.rs:71-73`), `MatchGuard`
  (`matches.rs:434-438`), `CallSite` and `Arguments` (`builder/mod.rs:548-561`).
* `schedule_drop(scope, local, kind)` appends to that scope's `drops` vector
  (`scope.rs:1407-1495`). On exit, drops run in **reverse push order**
  (`build_scope_drops`, `scope.rs:1869`). Scopes pop innermost first.
* So the drop order is determined by (a) which scope each value's drop is scheduled in and
  (b) the order in which drops were scheduled.

---

## 2. Terminating scopes (they get a `Destruction` parent)

All of these come from `region.rs`. A "terminating" node's temporaries die when that node finishes.

| HIR node | Terminating? | Edition | Cite |
|---|---|---|---|
| Function or closure body expression (`body.value`) | yes | all | `region.rs:790` |
| const, static, or inline-const body | yes. A `Destruction` is pushed around `body.value`, and the body is treated like a `let` initializer with `var_parent = None`, so extended temps get `None` and are never dropped (`'static`). | all | `region.rs:810-815` |
| Every statement: `Let` (non-`super`), `Expr`, `Semi` | yes | all | `region.rs:244-250` |
| `super let` statement | **no**. It is transparent. | | `region.rs:228-236` |
| Item statements | no scope at all | | `region.rs:137-140` |
| Block tail expression | **edition >= 2024: yes. Edition 2021: no.** The edition is taken from `blk.span.edition()`. | 2024 | `region.rs:144-163` |
| Block (the block node itself) | no, except for a loop body or a let-else `else` block | | `region.rs:766`, `385`, `119` |
| `loop` body block (and therefore `while` and `for` bodies, which desugar to `loop`) | yes | all | `region.rs:384-386` |
| `if` condition | yes, **unless** it is a `let` or a `&&`/`||` chain (then the operands are handled individually) | all | `region.rs:170-192,364` |
| `if` then-expression | yes | all | `region.rs:365,380` |
| `if` else-expression | yes | all | `region.rs:367` |
| `&&` / `||` LHS operand | yes, unless it is a `let` or itself `&&`/`||` | all | `region.rs:288-301,307` |
| `&&` / `||` RHS operand | yes, unless it is a `let` | all | `region.rs:305,308` |
| `match` arm (the `Arm` node: pattern + guard + body) | yes | all | `region.rs:197` |
| `match` guard expression | like an `if` condition (`resolve_cond`) | all | `region.rs:201-208` |
| `match` arm body | no, but it sits inside the terminating arm (and inside `MatchGuard` if there is a guard) | | `region.rs:209` |
| `match` scrutinee | **no** | | `region.rs:394` (default walk) |
| `let` initializer expression | no, but its parent let statement is terminating | | `region.rs:531-533` |
| let-else `else` block | yes, and it is resolved in the scope **outside** the let's `Remainder` | all | `region.rs:101-122` |
| `DropTemps(e)` (inner `e`) | yes | all | `region.rs:388-392` |
| Function call arguments, method receivers, operands of other operators, `return`/`break` operands, struct/tuple/array fields | **no** | | default `walk_expr` |

Temporary-scope boundaries that are not `Destruction` scopes:

* `IfThenRescope` (2024 `if`): covers the condition **and** the then-branch, not the else branch.
* `MatchGuard` (any arm with a guard): covers the guard **and** the arm body.

Where `DropTemps` comes from (`ast_lowering`):

* `for` loops: `DropTemps(match IntoIterator::into_iter(head) { mut iter => loop {...} })`
  (`ast_lowering/expr.rs:1881-1887`).
* `async fn` bodies: `DropTemps(user_body)` (`ast_lowering/item.rs:1616`). This makes body temporaries die before the parameters.

Desugarings that matter for scopes (Reference `destructors.scope.desugaring`):

* `while c { b }` desugars to `loop { if c { b } else { break } }`, with the `if` as the **tail expression** of the loop body
  block (`ast_lowering/expr.rs:645-682`). The comment there mentions `{ let _t = c; _t }`, but
  the lowering does **not** insert `DropTemps`. The `if`-condition rule (`resolve_cond`) does the job.
* `while let p = e { b }` desugars to `loop { if let p = e { b } else { break } }`.
* `for pat in head { body }` desugars to
  `DropTemps(match IntoIterator::into_iter(head) { mut iter => loop { match Iterator::next(&mut iter) { None => break, Some(pat) => body }; } })`.
  The inner `match` is an **expression statement**, so it is terminating.
* `e?` desugars to `match Try::branch(e) { Break(residual) => return Try::from_residual(residual), Continue(val) => val }`
  (`ast_lowering/expr.rs:1893-1990`). Inside `try {}` the `return` is a `break 'try`.
* A destructuring assignment `(a, b) = rhs` desugars to `{ let (lhs1, lhs2) = rhs; a = lhs1; b = lhs2; }`
  (`ast_lowering/expr.rs:1203-1216`). RHS temps die at the end of that synthetic `let` (unless
  extended within the synthetic block). Ordinary assignment is unchanged.

---

## 3. Where locals are dropped

### 3.1 `let` bindings in blocks

* The var scope of every binding of `let` `i` is `Remainder(i)` (`region.rs:130-135`). Remainders nest
  (later lets are inner), so at block end: **locals drop in reverse declaration order**, and each
  let's extended temporaries drop together with that let's bindings (§5.4).
* MIR: `block.rs:246` pushes `Remainder(i)`. All remainders are popped after the tail expression
  is evaluated, in reverse order (`block.rs:349-351`), then the block `Node` is popped.
* Drop scheduling for `let x = init;` (a simple by-value binding): `StorageLive` and a Storage drop come first. Then
  `init` is evaluated **directly into `x`** (no temporary). Then the Value drop is scheduled
  (`matches.rs:577-627`). Any extended temporaries created while evaluating `init` are scheduled
  in the same `Remainder` **before** `x`, so they drop **after** `x` (test `t28`: `let w = W(&D("inner"))`
  drops `W(inner)` then `inner`).
* For a complex pattern `let (a, b) = init;` the init goes through `lower_scrutinee` →
  `as_place` → a **temporary** with `temporary_scope(init)`, which is the let statement's `Node`
  unless extended (`matches.rs:629-631`, `394-405`). Bindings move out of it. **Unmoved parts
  are dropped at the end of the let statement.** For example, `let (a, _) = (D("1"), D("2"));` drops "2"
  at the `;` and "1" at block end (test `t10`).
* `let _ = e;`: if `e` is a place, nothing happens (no move, no drop). If `e` is a value, there is a temporary in the statement scope and
  it is dropped at the `;` (test `t09`: `wild` is dropped immediately).
* Shadowing (`let x = ..; let x = ..;`) does **not** drop the first `x`. It lives to block end.
* Within one pattern, bindings drop in **reverse declaration order** (bindings are scheduled in
  pattern visit order). For or-patterns, the order comes from the **first** alternative: rustc lowers
  sub-branches in reverse so that the first alternative's schedule wins (`matches.rs:549-566`; Reference
  `destructors.scope.bindings.or-patterns`; test `t24`).

### 3.2 `let x;` without an initializer

`block.rs:274-299`: the bindings are declared, `StorageLive` is emitted, and **both Storage and Value drops are
scheduled immediately** in `Remainder(i)`. Whether the drop actually runs is decided by drop
elaboration (§9). The value is dropped at block end if it was assigned on that path (test `t32`).

### 3.3 let-else: `let PAT = INIT else { ELSE };`

`block.rs:82-226` and `region.rs:101-122`:

* The `else` block is lowered in the scope **enclosing** this let (the previous `Remainder` or the
  block `Node`). It is terminating.
* `INIT`'s ordinary temps live in the init `Node`. Its *extended* temps live in this let's `Remainder(i)`.
* On pattern failure: `break_for_else` targets `last_remainder_scope` (`block.rs:206`), so the
  init temps **and the extended temps** are dropped **before** the `else` block runs (test `t45`:
  `drop tmp`, then `else`, then `drop outer` on return).
* On success: the bindings' drops are scheduled after matching. Init temps die at the end of the let statement.
  Extended temps die with the `Remainder` (test `t44`).

### 3.4 `match` arms

* `resolve_arm` (`region.rs:194-212`) enters `Destruction(arm)` and `Node(arm)`, and sets `var_parent = Node(arm)`.
  **Arm pattern bindings are dropped at the end of the arm.**
* If there is a guard: `MatchGuard(arm)` is entered inside `Node(arm)`. `if let` guard bindings get
  `var_parent = MatchGuard`. The guard's and the body's temporaries also land in `MatchGuard`
  (it is a temporary boundary). So at the end of the arm: body locals, then guard temps and guard
  bindings (reverse creation), then the arm pattern bindings (Reference example
  `destructors.scope.bindings.match-arm`; test `t35`).
* With a guard, by-value pattern bindings are **not moved until the guard succeeds**. Inside the guard
  they are references (`matches.rs:2453-2555`). If the guard fails, the guard's bindings and temps are
  dropped (`in_if_then_scope(match_scope, ...)`, `matches.rs:2474`) before the next arm is tried.
* `match x { y => .. }` moves `x` into `y`, and `y` is dropped at the end of the arm. `match x { _ => .. }`
  does not move `x`.

### 3.5 `if let` / `while let` bindings

* `var_parent` = the `IfThen` or `IfThenRescope` scope (`region.rs:362-363`). The bindings are dropped when the
  then-branch finishes, **before** the else branch in both editions. All bindings of a let-chain
  share that scope.
* At the end of the then-branch the order is: then-block locals and temps, then the if-let bindings, then (2024 only)
  the scrutinee temps (test `v1`).

### 3.6 Function parameters

`builder/mod.rs:548-566,1108-1170`:

* MIR scopes: `CallSite { Arguments { body } }`. `return` breaks to the breakable scope whose
  region is `CallSite`. It drops everything inside, **including the parameters**.
* For each parameter `i` in order, the argument local's Value drop is scheduled in `Arguments`
  (`builder/mod.rs:1114-1120`). If the pattern is not a simple by-value binding, the
  pattern bindings are then scheduled in `Arguments` too (var_parent = `Arguments`, `region.rs:784`).
  The resulting order is: `[arg0, bindings(arg0), arg1, bindings(arg1), ...]`. Reversed, that is:
  **last param's bindings, last param's remaining parts, ..., first param's bindings, first param's remaining parts.**
  The Reference example `fn f((x, _): (D,D), (_, y): (D,D))` prints `3 2 0 1` (test `t06`).
* The body expression is terminating (`region.rs:790`), so all body temporaries and locals die before any parameter.
* Arguments passed by value are moved into the callee and dropped **by the callee** at its
  `Arguments` scope exit (test `u6`: `in-take`, `drop y`, `drop x`).

### 3.7 Closures

* A closure body is a nested body inside the enclosing fn's scope tree (`region.rs:313-316`). It gets
  its own `CallSite` and `Arguments` scopes and a terminating body.
* Captured-by-move values are fields of the closure value. They drop when the closure value drops,
  in **unspecified** order among captures (Reference `destructors.operation`). A `move` closure
  that is only called by reference drops its captures at the closure variable's scope end (test `t41`).

---

## 4. Temporary scope of each expression

**The rule:** `temporary_scope(e)` from §1.2. Below is what that works out to for common shapes.
"Enclosing terminating scope" (ETS) means the nearest ancestor that is terminating, or is an
`IfThenRescope`/`MatchGuard`.

| Expression position | Temp scope (2021) | Temp scope (2024) | Tests |
|---|---|---|---|
| inside an expression statement `e;` | statement | statement | `t09`, `t16` |
| inside a `let` initializer (not extended) | the let statement | the let statement | `t05` |
| inside a block **tail** expression | ETS of the **block** (that is, after the block's locals!) | the tail expression itself (before the block's locals) | `t01`, `t20`, `t37`, `t40`, `v3` |
| `if` condition (non-`let`) | condition (dropped before then/else run) | same | `t15` |
| `if let` scrutinee / let-chain `let` operands | ETS of the whole `if` (`IfThen` is transparent). It lives through the else-branch and usually to the end of the enclosing statement. | `IfThenRescope`: dropped at the end of the then-branch, or **before the else-branch** | `t02`, `t02b`, `t25`, `v2` |
| non-`let` operands of a let-chain (`&& cond`) | the operand itself | same | `t25` (`c` before `b`, `a`) |
| then-block / else-block contents (tail) | the then/else expr (terminating) | same | `t26` |
| `match` scrutinee | ETS of the `match` (end of statement, or after locals if in a 2021 tail) | same, but a 2024 tail is terminating | `t03`, `t27`, `t37` |
| `match` arm body (no guard) | the arm (`Node(arm)`) | same | `t27`, `t43` |
| `match` arm body or guard (with guard) | `MatchGuard(arm)` | same | `t35` |
| non-`let` guard | the guard expr | same | `t14` |
| `&&`/`||` operands | each operand | same | `t13` |
| loop body | per iteration (the body block is terminating) | same | `t11`, `u3` |
| `while` condition (non-let) | the condition, per iteration | same | |
| `while let` scrutinee | dropped each iteration after the body. Via the loop-body block, because the `if` is its tail. | via `IfThenRescope` | `t11` |
| `for` head expression (`head`, `into_iter(head)`) | the `DropTemps` inner match. This lives **for the whole loop** and is dropped right after the loop. | same | `t12` |
| `for` per-iteration `next()` result | the per-iteration statement | same | |
| `return e` / `break e` operand temps | ETS. These are always dropped as part of the exit (the value is evaluated first). | same | `t08`, `t47` |
| `e?` | the scrutinee `Try::branch(e)` temp is in ETS. On `Break` the residual is converted, then everything is dropped, then the function returns. | same | `t29` |
| function arguments / method receivers / operator operands | ETS (they are not terminating) | same | `t16`, `t21`, `t30` |
| closure body | the body (terminating) | same | |

Notes:

* **The edition of the tail expression rule** is `blk.span.edition()` (`region.rs:146-147`). **The edition of the if-let rescope**
  is `expr.span.at_least_rust_2024()` on the `if` (`region.rs:357,372`; THIR mirrors it at
  `thir/expr.rs:990-1003`). The two can differ under macro expansion.
* **2021 else-if chains:** in `if let A = a() {} else if let B = b() {} else {}`, the else-expression
  (the inner `if`) is terminating. So `b()`'s temps die at the end of the else-chain, while `a()`'s
  temps live to the outer ETS. In 2021 the order is `else-body`, `drop b`, `drop a`. In 2024 it is `drop a`, `drop b`, `else-body`
  (test `v2`).
* For **2024 failure paths of a let-chain**: `then_else_break` breaks to the condition scope that is
  *outside* `IfThenRescope` (`into.rs:71`, `matches.rs:181,229`; `break_for_else` `scope.rs:1061-1087`).
  So all chain temps and bindings created so far are dropped before `else` (test `t25`: `c b a else`).
* A labeled block `'a: { ... break 'a v }` is breakable at its own block `Node` (`block.rs:23-26`).

---

## 5. Temporary lifetime extension (exact 1.98 rules)

Implemented in `resolve_local` (`region.rs:406-683`) and `record_subexpr_extended_temp_scopes`
(`region.rs:702-724`). It applies to the initializer of every **regular `let`**, and to const/static
bodies (`region.rs:815`). The extended scope is `cx.var_parent`, which is **the let's own `Remainder(i)`**.
For const bodies it is `None`, meaning "never dropped".

### 5.1 Expression grammar `E&` (`record_rvalue_scope_if_borrow_expr`, `region.rs:605-682`)

This is applied to the initializer. When it reaches `&ET`, it marks `ET` as extended.

```text
E& = & ET  | &mut ET | &raw const ET | &raw mut ET        (AddrOf, any BorrowKind)   region.rs:626-629
   | StructName { ..., f: E&, ... }                        (Struct: every field expr; NOT the `..base`) 630-634
   | [ ..., E&, ... ]   | ( ..., E&, ... )                 (Array, Tup; NOT Repeat `[e; N]`)            635-639
   | E& as T                                               (Cast)                                       640-642
   | { stmts; E& }  (any block incl. unsafe/labeled; also marks child `super let`s as extended)        643-654
   | if c { ..; E& } else { ..; E& }   (both branches; else-if recursively; NOT the condition)         655-660
   | match s { p => E&, ... }          (every arm body; NOT scrutinee or guard)                          661-665
   | Ctor(..., E&, ...)                (Call whose callee is a QPath::Resolved(None, ..) path resolving to
                                        a tuple-struct/tuple-variant ctor or `Self` ctor; e.g. Some(&x),
                                        W(&x), Self(&x))                                                 666-679
```

The cases that are **not** extending (falling to `_ => {}`) are: function or method calls (including
`identity(&temp())`), method receivers, `break`/`return` operands (so `loop { break &temp() }` and
`'a: { break 'a &temp() }` are not extended), closures, `async` blocks (they are closures in HIR), `Repeat`, `DropTemps`,
binary/unary operators, the `match` scrutinee, `if` conditions, and FRU `..base`.

Parentheses do not exist in HIR, so `( E& )` is free.

### 5.2 `ET` grammar (`record_subexpr_extended_temp_scopes`, `region.rs:702-724`)

Every node along the path gets the extended scope, not only the innermost rvalue (comment at
`region.rs:707-711`: MIR asks for the temp scope of the *outer* expression):

```text
ET = &ET | *ET | ET.f | ET[idx]   (only the indexed base; idx is NOT extended) | <anything else: stop>
```

`AddrOf` is in the code (`region.rs:716`) but missing from the doc-comment grammar. So
`let x = &&temp();` extends both the inner `&temp()` value and `temp()`. This matches Reference
`destructors.scope.lifetime-extension.sub-expressions`.

### 5.3 Pattern grammar `P&` (`is_binding_pat`, `region.rs:551-603`)

If the let pattern is `P&`, the **whole initializer** gets `ET` extension (`region.rs:517-524`).

```text
P& = ref x | ref mut x                (explicit ByRef only. Match-ergonomics implicit refs do NOT count.)
   | S { .., f: P&, .. } | V(.., P&, ..) | (.., P&, ..) | [.., P&, ..] (any of before/mid/after)
   | P& | ...  (or-pattern: any alternative) | box P& | deref!(P&) | P& if guard
NOT: x, _, &P (PatKind::Ref), literal, or range patterns.
```

Example: `let (ref a, b) = (D("ra"), D("rb"));` extends the tuple temp. `b` moves out. At block end,
`rb` (via `b`, declared later) drops, then the tuple remainder `ra` (test `t31`).

The comment's "rule B" (`let x: &T = expr`, where a type annotation causes extension) is **not implemented**. Only
patterns (rule A) and expressions (rule C) are. Coercions do not trigger extension.

### 5.4 Where extended temporaries go and their order

* The extended scope is `Remainder(i)` of the `let`. So extended temps live to the **end of the block
  containing the let** (or to the end of the iteration if that block is a loop body, test `u3`).
  This is true even when the let is nested inside an inner block:
  `let x = { let y = &D("in"); 0 };` drops `in` at the end of the inner block (test `t33`).
* Extension **overrides** the 2024 tail-expression and `IfThenRescope` narrowing.
  `let b = { &D("block") };` and `let x = if c { &D("a") } else { &D("b") };` both live to block end in both editions
  (test `t05b`).
* Within the `Remainder(i)` scope: extended temps are scheduled during init evaluation (in
  completion order), and bindings are scheduled after. So the drop order is **bindings first, then extended temps in reverse
  creation order** (tests `t28`, `t05b`, `v4`, `v5`).
* `const`/`static`/inline `const {}`: extended temps get `None` and are never dropped
  (`as_temp.rs:109-124`).
* `super let` (inside `pin!`, `format_args!`): if the enclosing block is extended by a parent
  `let`, the `super let` bindings and their extended temps take the parent let's scope
  (`region.rs:470-490`). Otherwise they take the block's temporary scope (`region.rs:491-509`). For example,
  `let x = pin!(D("pinned"));` lives to block end, while `pin!(D("x"));` as a statement dies at the `;` (test `t34`).

### 5.5 Related Reference notes

* Reference `destructors.scope.lifetime-extension.exprs` (1.98) lists exactly the cases above, including
  "arguments to an extending tuple struct or tuple enum variant constructor", the `if`/`else` final
  expressions, and match arm expressions. It notes that rustc does **not** treat array-repeat
  operands as extending (issue #146092).
* General function call arguments are **not** extending in 1.98.

---

## 6. Which expressions create temporaries (MIR builder)

`Category::of` (`category.rs:34-101`) classifies THIR expressions into these categories:

* **Place**: `VarRef`, `UpvarRef`, `Field`, `Deref`, `Index`, and place type ascription. No temp is needed to name them.
* **Constant**: literals, named consts, const params, `StaticRef`, `ConstBlock`.
* **Rvalue**: everything else (calls, ADT/tuple/array literals, borrows, binops, blocks, if, match, loops, ...).

There are three ways a value ends up in a MIR temporary.

### 6.1 Value expression in a *place* context → temp with `temporary_scope(e)` (the one that matters)

`expr_as_place` (`as_place.rs:416-597`). Any non-place expression gets
`as_temp(temporary_scope(expr.temp_scope_id))` (`as_place.rs:591-595`). The place contexts in
THIR/MIR building are:

* the operand of `&`, `&mut`, `&raw` (`into.rs:648-670` → `as_place`/`as_read_only_place`),
* **autoref adjustments**: method receivers taking `&self`/`&mut self` (`D("r").len()`); by-ref
  overloaded binary operators (`a == b` becomes `PartialEq::eq(&a, &b)`); overloaded index and deref
  (`overloaded_place`, `thir/expr.rs:1504-1538`); deref coercions (`thir/expr.rs:200-230`),
* the base of a field, index, or deref projection: `f().x`, `f()[i]`, `*f()`. This applies **even when the
  projection is read by value** (`into.rs:987-1000` → `as_place`). The base temp then has
  `temporary_scope(base)` and remaining fields are dropped there,
* the **index operand** of built-in indexing: `as_temp(temporary_scope(index))` (`as_place.rs:643-644`)
  (Copy `usize`, so no drop matters),
* `match` / `if let` / `while let` scrutinees, and `let` initializers with non-trivial patterns or `_`
  (`lower_scrutinee`, `matches.rs:394-405`),
* the functional-record-update base `S { ..base }` (`into.rs:775`),
* value type ascription (`as_place.rs:505-529`), `ByUse`, and `Reborrow` sources.

The temp's drop is scheduled when evaluation of the expression **finishes** (`as_temp.rs:128-132`).

**For HIR-level modeling:** a HIR expression `e` needs a "temporary that may need a drop" iff
(1) `e` is a value expression (not a path to a local or static, field, index, or deref of a place), and
(2) `e` appears in one of the place contexts above (including implicit autoref or overloaded-place
adjustments recorded in typeck), and (3) `e`'s type needs drop. Its drop point is
`temporary_scope(e.hir_id.local_id)` (§1.2, using `extended_temp_scopes`).
Note that the temp scope is keyed by the **HIR expr id of the expression being materialized**:
adjustments and synthesized nodes reuse the original `temp_scope_id` (`thir/expr.rs:135`, `1530`, `1248`).

### 6.2 Value expression in a *value* (operand) context → temp in the **local scope**

`as_operand`, `as_local_operand`, `as_local_call_operand`, `as_local_rvalue` (`as_operand.rs:14-157`,
`as_rvalue.rs:29-41`) use `local_temp_lifetime()`, which is the **topmost MIR scope** (`scope.rs:1386-1388`)
at the time of the request. That is the `Node` scope of the *parent* expression (call, ADT literal, tuple, binop, ...).

* These temps are **moved** into the parent's operation. `record_operands_moved` (`scope.rs:1575-1597`)
  suppresses the drop on the normal path (`scope.rs:1895`). Drop elaboration removes it anyway.
* Their drop **matters only if control leaves the parent expression before the move**: a later operand
  `break`s, `return`s, `?`s, or panics. They are then dropped in reverse order (Reference
  `destructors.scope.operands`; test `t19`: `(D("a"), D("b"), (D("c"), break), ..)` drops `c b a`;
  test `u2`: by-value arg `v1` dropped on unwind from a later arg).
* Constants that need drop also get an operand temp (`as_operand.rs:137-145`).

### 6.3 Expression statements and other fixed sinks

* `e;` where `e` is not an assign/break/continue/return: `as_temp(statement_scope)` holds the
  statement's **result value** (`stmt.rs:144-201`). That temp is scheduled after the sub-expression temps,
  so **the result value drops first, then the sub-expression temps** (test `u1`: `mk(&D("t"));` drops `ret` then `t`).
* `if` conditions and `&&`/`||` operands that are not `let`: a bool temp (`matches.rs:200-231`). It has no drop.
* `NeverToAny`: a local temp (`into.rs:137-157`).

### 6.4 Things that do **not** create a temp

* `let x = e;` with a simple by-value binding writes `e` directly into `x` (`matches.rs:577-584`).
* Block tails, `if`/`match` arm results, and `break`/`return` values are written **directly into the
  destination** (`expr_into_dest`), with no extra temp (`block.rs:317-325`, `scope.rs:783-787`).
* Moving a place (`f(x)`, `let y = x`) moves from the variable. Nothing new is created, and the source becomes
  (partially) uninitialized (§9).
* Promotion (`&5`, `&None`) happens later in MIR transforms. It only applies to values without drop
  glue or interior mutability, so it is irrelevant to drops.

---

## 7. Drop order within a scope

* **Reverse scheduling order** (`build_scope_drops` iterates `scope.drops.iter().rev()`, `scope.rs:1869`).
* Temporaries are scheduled when their evaluation **completes** (`as_temp.rs:130-132`). So among
  temps in the same scope, the order is the reverse of **completion** order. Inner sub-expressions complete before outer ones, so
  outer temps drop before the inner temps they borrow from:
  * `two(&D("1"), &D("2"));` → `drop 2, drop 1` (`t16`)
  * `D("a").len() + D("b").len();` → `drop b, drop a` (`t30`)
  * `mk(&D("t"));` → the result `ret` first, then `t` (`u1`)
* Bindings and extended temps in one `Remainder`: bindings drop first, then extended temps (§5.4).
* Several `let`s: these are nested `Remainder`s, so later lets drop first (`t04`, `u15`).
* Arm: body temps and locals (in inner scopes), then the `MatchGuard` contents, then arm bindings, then (after the
  `match` completes) the scrutinee temps in the ETS (`t27`, `v3`).
* Within a value, drop glue runs `Drop::drop` first, then fields in declaration order. Tuples and arrays go left to
  right. Vec elements go first to last (`u10`).

---

## 8. Leaving scopes early: `break`, `continue`, `return`, `?`, let-else, guards

`break_scope` (`scope.rs:746-837`):

1. **The value is evaluated first**, directly into the break destination (the loop/block result place,
   or `RETURN_PLACE` for `return`) (`scope.rs:783-787`). Temps created by that evaluation are scheduled
   in their normal scopes, which are still on the stack.
2. Then **all drops of all scopes strictly inside the target breakable scope** are added to a drop tree,
   innermost scope last-scheduled-first (`scope.rs:824-829`). Unmoved locals, temps, and (for `return`)
   the parameters are all dropped, innermost first.
3. Targets: `return` uses `breakable_scopes[0]`, whose region is `CallSite`, so everything including the `Arguments`
   scope is dropped. `break 'l` / `continue 'l` use the loop expr's `Node` scope. `continue` jumps back to the
   loop head after the drops (`scope.rs:537-584`). A labeled block uses the block's `Node` scope (`block.rs:23-26`).

Verified orders:

* `let v = loop { let _a = D("a"); break { p("eval"); 1 } };` → `eval`, `drop a` (`t07`).
* `let _a = D("a"); return D("r").len();` → `drop r` (statement temp), `drop a` (`t08`).
* `'a: { let _l = D("l"); break 'a D("v").len(); }` → `drop v`, `drop l` (`t47`).
* `fn q() -> Result<(), D> { let _a = D("a"); D("t").none().ok_or(D("err"))?; .. }` → `drop t`,
  `drop a`. `err` is moved into the returned value and dropped by the caller (`t29`).
* `let _a; let _b; { let _c; return; }` → `c b a` (`u8`).

Other early exits use the same machinery:

* `if`/let-chain/guard failure: `break_for_else` (`scope.rs:1061-1087`) drops everything inside the
  `if_then_scope` target before jumping to `else` or the next arm.
* let-else failure: §3.3.
* Explicit tail calls (`become`) drop everything immediately except the args (`scope.rs:1093-1200`). This is unstable.

---

## 9. Moved-out values, drop flags, partial moves

MIR building schedules drops **unconditionally**. `elaborate_drops` (`elaborate_drops.rs:166-189`) uses
maybe-init/maybe-uninit dataflow on move paths and turns each `Drop(place)` into one of:

* **Dead**: the place is definitely not initialized (moved out on every path) → no drop.
* **Static**: definitely initialized → an unconditional drop.
* **Conditional**: maybe initialized, single move path → a drop guarded by a **runtime drop flag**
  (for example `let x = D(..); if c { drop(x) }` drops at scope end only when `!c`; test `t23`).
* **Open**: a partially moved aggregate → drop the remaining fields individually, each Static or
  Conditional (for example `let p = (D("p0"), D("p1")); let a = p.0;` at block end drops `a` (p0) and then the remaining
  `p.1`. Test `t22`).

Notes:

* You cannot move out of a field of a type that implements `Drop` (E0509), so partial moves only occur
  in drop-glue-only aggregates (tuples, structs without `Drop`, `Box` contents).
* Assignment `place = v` when `place` needs drop: RHS is evaluated **first** (`stmt.rs:45-49`, right to left),
  then the LHS place, then `Drop(place)` with `replace: true` and the write (`scope.rs:1720-1752`). Drop
  elaboration makes it Dead, Static, or Conditional. For example, `let x; x = v;` does not drop. `x = D("new")` drops
  `old` after the RHS evaluates (`t18`). Compound assignment evaluates RHS then LHS for primitive types.
  An overloaded `+=` is a method call with left-to-right order (`region.rs:317-353`).
* A binding moved into another binding (`let y = x;`) leaves `x` dead. `y` drops at its own scope (`u11`).

---

## 10. Unwinding

* Every terminator that can unwind (Call, Assert, Drop, FalseUnwind, InlineAsm) gets a cleanup edge
  (`diverge_from`, `scope.rs:1646-1662`). On that edge, **all currently scheduled Value drops in all
  scopes** run, innermost and last-scheduled first, ending in `UnwindResume`. StorageDead is skipped, except in
  coroutines. The cleanup trees are built at the end (`build_drop_trees`, `scope.rs:2059`).
* Values moved before the panic point are not dropped, because drop elaboration applies on unwind paths too.
  Operand temps already evaluated for a pending call or aggregate **are** dropped (`u2`). `moved_locals` is
  ignored on unwind paths (`scope.rs:1892-1897`).
* If a `Drop` panics during a normal scope exit, the remaining drops of that scope (and outer scopes)
  run on the unwind path (`build_scope_drops` comments, `scope.rs:1838-1857`). A panic while already
  unwinding aborts.
* Example `t36`: `let _a; let _b; two(&D("t1"), &{ panic!(); D("t2") });` → `t1 b a`.

---

## 11. Ambiguities in the Reference, resolved by rustc

1. **The Reference says "each expression is a drop scope", and the parent of a match guard is "the arm".** rustc does push a
   `Node` scope per expression, but temporaries only land in *terminating* scopes (§2). Operand temps
   land in the parent expression's scope (§6.2). Guards with `if let` get an extra `MatchGuard` scope
   that also contains the arm body. Arm bindings live in the outer arm `Node`.
2. **"The pattern-matching condition and loop body of `while`"**: there is no special `while` scope.
   It is an `if` that is the tail of the loop body block. In 2021 the scrutinee temp drops at the end of the
   loop-body block, and in 2024 at `IfThenRescope`. Both editions observably drop after the body of each iteration (`t11`).
3. **Which edition applies under macros**: for tail expressions, the edition of the **block's span**. For if-let
   rescope, the edition of the **`if` expression's span**.
4. **The 2021 `if let` scrutinee "lives until end of statement"**: precisely, it lives to the ETS of the `if`, which can be
   an enclosing `else`-expression in an else-if chain (`v2`), a then-block, an arm, or a loop body.
5. **Lifetime extension "to the end of the block"**: precisely, to the let's `Remainder(i)`. For let-else
   failure, extended temps are dropped *before* the else block (§3.3).
6. **Rule B in the rustc comment** (a type annotation extends) is not implemented (§5.3).
7. **Tuple-struct constructor extension** applies only when the callee is syntactically a
   `QPath::Resolved(None, path)` resolving to a fn-like ctor or `Self` ctor. A ctor reached through a
   type-relative path or a variable (`let f = Some; f(&t)`) is not extended (`region.rs:666-679`).
8. **`ET` includes `&`** (`region.rs:716`), even though the doc comment's grammar omits it.
9. **Order of a statement's result vs its operand temps**: the result drops first (`stmt.rs:183-193` plus
   `as_temp.rs:130`). The Reference only says "reverse order of creation". rustc's "creation" is
   **completion of evaluation**.
10. **Function parameters**: the Reference says "each actual parameter is dropped after any bindings
    introduced in that parameter's pattern". rustc does this by scheduling the argument local's drop before that parameter's
    bindings, per parameter, in parameter order (§3.6).
11. **`let _ = place;`** does nothing. **`let _ = value;`** drops the value at the `;`. A `_` sub-pattern in a
    by-value destructuring leaves that field in the init temp, which is dropped at the end of the let statement (`t10`).
12. **Or-patterns**: the drop order is that of the first alternative, even when another alternative matched
    (`matches.rs:549-566`).

---

## 12. Implementation checklist (HIR → VIR Drop nodes)

To place drops at the HIR level you need:

1. The `ScopeTree` for the body: `tcx.region_scope_tree(def_id)`. Use `var_scope(binding_hir_local_id)`
   for each binding, and `temporary_scope(expr_local_id)` for each materialized temp (it returns
   `Option<Scope>`. `None` means static, never dropped).
2. The set of materialized temps (§6.1): value expressions in place contexts, including typeck
   adjustments (autoref, overloaded deref/index, by-ref overloaded binops) and scrutinees/let inits.
   Operand temps (§6.2) only matter on early-exit or unwind paths.
3. For each scope, order its drops by reverse scheduling: temps by completion order, bindings after
   their initializer, args before their pattern bindings.
4. Emit drops on: normal scope exit; `break`/`continue`/`return`/`?` (after evaluating the value,
   dropping all scopes inside the target); `if`/let-chain/guard failure (to the condition scope);
   let-else failure (to the previous remainder); and unwinding.
5. Model initializedness (moves, partial moves, `let x;`) for Static, Conditional, or Open drops.
6. Edition switches: block tails are terminating in 2024 (`blk.span`). `if` uses
   `IfThenRescope` in 2024 (`if` span). `MatchGuard` behaves the same in all editions.

---

## Appendix A. Runtime check log (rustc 1.98.1, `--edition 2021` vs `--edition 2024`)

`D(s)` prints `drop s`. `p(s)` prints `s`. A row has one column when both editions agree.
The test sources were `/tmp/dropexp/{t,u,v}.rs` (scratch; the relevant code is reproduced here).

| Test | Code (essentials) | Output (2021) | Output (2024) |
|---|---|---|---|
| t01 | `fn f()->usize { let _x=D("local"); D("tail-temp").len() }` | local, tail-temp | tail-temp, local |
| t02 | `if let Some(_) = D("scrut").pick(false) { p("then") } else { p("else") }; p("after")` | else, scrut, after | scrut, else, after |
| t02' | same with `pick(true)` | then, scrut, after | |
| t03 | `match D("scrut").len() { _ => p("arm") }; p("after")` | arm, scrut, after | |
| t04 | `let x=&D("ext"); let y=D("y"); p("end")` | end, y, ext | |
| t05 | `let x = id(&D("nonext")).len(); p("after-let")` | nonext, after-let | |
| t05b | `if c {&D("if-a")} else {&D("if-b")}`, `match 0 {_=>&D("match")}`, `Some(&D)`, `S{r:&D}`, `(&D,)`, `[&D]`, `{&D}` as lets | all live to block end, reverse order | |
| t06 | `fn f((x,_):(D,D),(_,y):(D,D)){}` with `("0","1"),("2","3")` | body, 3, 2, 0, 1 | |
| t07 | `loop { let _a=D("a"); break { p("eval"); 1 } }` | eval, a | |
| t08 | `let _a=D("a"); return D("r").len();` | r, a | |
| t09 | `D("stmt"); p(..); let _=D("wild"); p(..); let _n=D("named"); p("end")` | stmt, after-stmt, wild, after-wild, end, named | |
| t10 | `let (a,_)=(D("1"),D("2")); p("after-let")` | 2, after-let, 1 | |
| t11 | `while let Some(_) = D("scrut").pick(i<2) { p("body"); i+=1 }` | body, scrut, body, scrut, scrut, after | |
| t12 | `for _ in D("head").vec() { p("body") } p("after-for")` | body, body, head, after-for | |
| t13 | `(D("first").len()==0 \|\| D("second").len()==0) \|\| D("third").len()==0;` | first, second, third | |
| t14 | `match 0 { _ if D("guard").t() => p("arm-body"), _=>{} }` | guard, arm-body | |
| t15 | `if D("cond").t() { p("then") }` | cond, then | |
| t16 | `two(&D("1"), &D("2"));` | 2, 1 | |
| t17 | `let Some(x) = D("s").none() else { p("else"); return; };` | s, else | |
| t18 | `let mut x=D("old"); x = { p("rhs"); D("new") }; p("after")` | rhs, old, after, new | |
| t19 | `loop { (D("a"), D("b"), (D("c"), break), D("never")); }` | c, b, a | |
| t20 | `let v = { let _l=D("l"); D("t").len() }; p("after-let")` | l, t, after-let | t, l, after-let |
| t22 | `let p0=(D("p0"),D("p1")); let a=p0.0; p("end")` | end, p0, p1 | |
| t23 | `let x=D("x"); if c { drop(x) } p("end")` | c=true: x, end. c=false: end, x | |
| t24 | `let (Ok([x,y]) \| Err([y,x])) = v;` | drops y then x for both alternatives | |
| t25 | `if let Some(_)=D("a").some() && let Some(_)=D("b").some() && D("c").f() {..} else { p("else") }` | n/a | c, b, a, else |
| t26 | `if c { two(&D("then-tail"), &D("x")) } else { 0 }; p("after")` | x, then-tail, after | |
| t27 | `match D("scrut").len() { _ => { two(&D("arm"), &D("arm2")); } } p("after")` | arm2, arm, scrut, after | |
| t28 | `let w = W(&D("inner")); p("end")` | end, W(inner), inner | |
| t29 | `let _a=D("a"); D("t").none().ok_or(D("err"))?;` | t, a, (caller drops) err | |
| t31 | `let (ref a, b) = (D("ra"), D("rb")); p("end")` | end, rb, ra | |
| t32 | `let x; p("decl"); x = D("late"); p("end")` | decl, end, late | |
| t33 | `let x = { let y = &D("in"); 0 }; p("after-let")` | in, after-let | |
| t34 | `let x = pin!(D("pinned")); p(..); pin!(D("pin-stmt")); p(..)` | after-let, pin-stmt, after-stmt, pinned | |
| t35 | Reference guard example (`x if let y = .. && let z = ..`) | inner-scope, first(z), second(y), last(x) | |
| t36 | `let _a; let _b; two(&D("t1"), &{ panic!(); D("t2") })` | panic, t1, b, a | |
| t37 | `fn f()->usize { let _l=D("local"); match D("scrut").len() { n => n } }` | local, scrut | scrut, local |
| t40 | `fn f()->usize { let _l=D("local"); if let Some(n)=D("scrut").some() { n } else { 0 } }` | local, scrut | scrut, local |
| t45 | `let _o=D("outer"); let Some(x) = id(Some(&D("tmp"))).and(None::<u8>) else { p("else"); return; };` | tmp, else, outer | |
| t47 | `'a: { let _l=D("l"); break 'a D("v").len(); }` | v, l | |
| t49 | `let x = &*&D("deref-ext"); let f = &(D("field-ext"),1).1;` | end, field-ext, deref-ext | |
| u1 | `fn mk(_:&D)->D; mk(&D("t"));` | ret, t | |
| u2 | `take(D("v1"), { panic!() })` | panic, v1 | |
| u3 | `for _ in 0..2 { let x=&D("ext-loop"); p("iter-end") }` | iter-end, ext-loop (x2) | |
| u6 | `take(D("x"), D("y"))` (callee prints) | in-take, y, x | |
| u15 | `let _a=D("a"); let x:&D=&D("coerce-ext"); let _y=D("y");` | end, y, coerce-ext, a | |
| v1 | `if let Some(_b)=D("scrut").pick(true) { let _l=D("then-local"); p("then-end") } else {..}; p("after")` | then-end, then-local, binding, scrut, after | |
| v2 | `if let Some(_)=D("a").pick(false) {} else if let Some(_)=D("b").pick(false) {} else { p("final-else") };` | final-else, b, a | a, b, final-else |
| v3 | `match D("scrut").pick(true) { Some(_b) => { let _l=D("arm-local"); D("arm-tail").len() }, None=>0 };` | arm-local, arm-tail, binding, scrut | arm-tail, arm-local, binding, scrut |
| v4 | `let x = (D("a"), &D("b")); p("end")` | end, a, b | |
| v6 | `let _ = D("x").pick(true); p(..)` | binding, x, after-let-wild | |

---

## 13. How Verus implements this (`ExprX::Drop`)

* VIR: `ExprX::Drop(LocalOrTemp)` (`vir/src/ast.rs`), where `LocalOrTemp::Temp(id)` names the
  `PlaceX::Temporary` whose `span.id` is `id`. `ExprX::Block`, `ExprX::Return`, and
  `ExprX::BreakOrContinue` carry a list of drops that run *after* the tail expression / return
  value / break value. `ast_to_sst` lowers `Drop` to nothing (resolution assumptions that
  `resolution_inference` attaches to a drop are still lowered).
* `rust_verify/src/drop_scopes.rs` keeps a stack of `region::Scope`s, pushed where the MIR builder
  pushes them:
  * `Node(e)` for every HIR expression (`expr_to_vir_inner`). It covers the adjustments.
  * `Node(stmt)` for every statement.
  * `Node(block)`, plus `Remainder(block, i)` before each `let`.
  * `Node(arm)` and `MatchGuard(arm)`.
  * `IfThen`/`IfThenRescope` around the condition and then-branch.
  * `Arguments(body)` for the function's and each closure's parameters. Each closure body gets a fresh stack.
* Drops are scheduled when a temporary is created (`ExprOrPlace::to_place`, overloaded
  deref/index), using `temporary_scope(expr)`. For bindings, they are scheduled after the initializer, using
  `var_scope(binding)`. When a scope is popped, its drops are emitted in reverse order. `break`/`continue`
  emit the drops of all scopes inside the loop's `Node` scope. `return` emits the drops of all scopes. If the
  target scope isn't on the stack, the nearest enclosing scope on the stack is used.
* Scheduling order is translation order. Where translation order differed from evaluation order,
  it was changed:
  * assignment: the right-hand side first
  * struct update: the fields before the `..base`
  * `if let`: the scrutinee and then-branch before the else-branch
  * let-else: the initializer before the `else` block
  * `while`: the condition before the body
* Tests: `rust_verify_test/tests/drops.rs` compares the CFGs logged by `--log resolution-cfg`
  (drops appear as `ScopeDrop`). Each case was compared to rustc's `built` MIR. The comparison
  log is `drop-test-scratch/verus_cfg_vs_rustc_mir.txt`.

Known deviations and limitations:

* Operand temporaries (§6.2) are not modeled. By-value operands are VIR expressions, not places,
  so an early exit in the middle of an expression (`f(mk(), return)`) does not drop the
  already-evaluated operands.
* Unwinding paths have no drops (VIR has no place to put them).
* `&&`/`||` operands in an `if` condition: MIR drops each operand's temporaries after branching on
  that operand; we drop them before. (Plain `if` condition temporaries are dropped at the start of
  both branches, as in MIR.)
* The false exit of a non-`let` `while` condition, and the failure path of a match guard, have no
  place for drops. Rustc's scoping rules mean those drops are always empty, except for let-chains and if-let guards.
* VIR has its own temporaries (e.g., for `let` initializers, matched against the pattern) that MIR
  doesn't have, and vice versa (reborrows, operands). MIR also omits drops for types without drop glue.
* If a `PlaceX::Temporary` is later rewritten or cancelled (e.g. `&mut *temp`), its `Drop` refers to a
  nonexistent temporary and is ignored by `resolution_inference`.
* No drops are emitted in spec or proof code, ghost blocks, or headers.
* Function parameters are dropped by their VIR parameter names. Patterns in function parameters
  are not split into separate bindings. Closure parameter patterns are split.
