/*!
This is the algorithm for computing the "resolution points" for mutable references,
i.e., the points where we resolve the prophecy ("future") variable in a mutable reference
to equal the "current" value.

The first important thing to understand about resolution is that it has nothing to do with
the *lifetimes*. Resolution is safe for any value *as long as that value will never be
mutated again*. In fact, it is crucial that this can happen before the end of a lifetime.
Consider:

```
fn example<'a>(pair: &'a mut (u64, u64) -> &'a mut u64 {
    &mut (*pair).0
}
```

Note that the lifetime clearly extends beyond the end of the function, but we will
always resolve `pair` at the end of the function. This might be surprising because
we are returning a mutable reference that is derived (via reborrow) from the input reference.
However, it remains the case that this is a different owned value. The input reference `pair`
is still resolved at the end of the function.

We effectively elaborate this example to look like this:

```
fn example<'a>(pair: &'a mut (u64, u64) -> &'a mut u64 {
    let return_value = &mut (*pair).0;    // mutates `pair`
    // resolve `pair` here
    return return_value;                  // moves `return_value`
}
```

We can resolve `pair` at line 2 because `pair` is never moved or mutated after that point.
This is necessary if we want to prove a postcondition like
`ensures mut_ref_future(return_value) == mut_ref_future(pair).0`.
The `return_value` however, IS moved at the end, so we don't resolve that one.

So again: we can determine the resolve points of a given owned value by looking at
that value in isolation, without considering global lifetime analysis.

### The analysis

The analysis operates over "places", e.g., `x` (where `x` is a local variable),
or projections from locals, e.g., `x.field.0`. This is necessary because Rust's ownership analysis
operates at this granular level, where a struct's fields can be moved independently.

For a given place P, it is safe to "resolve" it at any program point Q if:

 (i) It is "initialized" at Q (i.e., it has been assigned to and not subsequently moved from)

 (ii) It will never be moved from Q nor mutated until it is dropped.

Note that "resolution" here just means inserting an 'assume' statement into the code.
Resolution is thus idempotent, so there isn't any issue with "resolving" something more
than once. Also note that resolving p.x and p.y is the same as resolving p
(if x and y are the fields of p).

Obviously, we don't want to insert these assumptions more than necessary to avoid cluttering
the AIR code.  In general, it's best to insert the resolution as early as possible,
since that's most convenient for the user. This also guarantees that the resolution occurs
before the lifetime ends (assuming that our analysis is at least as precise as Rust's).

Also note that this method, in principle, works for any place, no matter what type it is,
even if it doesn't contains a mutable reference. Of course, if the place doesn't contain
a mutable reference, then resolution is a "trivial" operation.

Our algorithm then is roughly as follows:

 1. Turn the vir::ast::Expr into a control flow graph (CFG) with place-based operations relevant
    to the analysis (moves, mutations).

 2. Compute (i) with a forward dataflow analysis pass

 3. Compute (ii) with a backwards dataflow analysis pass

 4. Combine this information to determine, for each place P, where it's safe to
    insert Assume(HasResolved(p)). Perform an insertion at any point P where this is "useful"
    (i.e., it wasn't also safe at the previous program point(s)).

### Places behind mutable references

If `x: &mut T` is a place, then the dereference `*x` of type `T` is also a place, so we need
to consider the resolution of `*x` (e.g., in the case of nested mutable references).

However, the resolution of place `x` does NOT imply the resolution of place `*x`.
This is because of the value `*x` lives on in whatever place it was originally borrowed from.
However, there are cases where we might want to resolve `*x`, namely, when assigning to it:

```
*x = t;
```

This causes the old value of `*x` to be dropped, so we need to resolve that value here.

Thus, we need to treat the resolution of `x` independently of the resolution of `*x`.
This is in contrast with fields, where resolving `x` is equivalent to resolving all the
fields of `x`.

### Working with enums

In order to resolve the field of an enum (e.g., `opt->Some_0` for a varible `opt: Option<T>`),
the resolution needs to be conditional on the variant:

```
assume(opt is Some ==> has_resolved(opt->Some_0)
```

Since resolution is explicitly conditional, we don't need to account for variants
in the initialization analysis; when an enum place is initialized, we then consider all
fields of the enum to be initialized (until they are subsequently moved from).

More formally, we can define a notion of "conditional initialization": a place is
conditionally initialized if "parents being in the correct variant ==> place is initialized".

Example:

```
let x: Result<A, B> = Ok(foo);
```

There are two fields of interest, `x->Ok_0` and `x->Err_0`. In the above statement, *both*
of these fields are considered "conditionally initialized"

 * Ok_0 is "conditionally initialized" because it's "really" initialized
 * Err_0 is "conditionally initialized" in a vacuous sense because `x` is not in the Err state

Thus, we can compute the "conditionally initialized" places with a straightforward
analysis that treats enums like normal structs.

### Notes about scopes

For the most part, we ignore the concept of a scope entirely in our CFG, so we don't
include specific instructions for 'dropping' a place at the ends of its scope.
Our analysis will simply detect that a given place isn't modified outside the scope.
However, we *do* need to set variables back to uninitialized when we go back to the beginning
of a loop.

When handling loops, at the beginning or end of a loop, we always insert all possible
resolution assumptions (since the structure of our AIR queries wouldn't otherwise contain
that information, at least not when loop_isolation=true). When inserting an assumption
into the expression, we always check that the local variable it refers to is actually
in scope, so, e.g., we won't end up resolving any variables declared inside a loop from
outside the loop. In all other cases, this check shouldn't matter.

### Working with temporaries

Sometimes we need to work with unnamed "temporary places", given by the PlaceX::Temporary
place, e.g., we might take a mutable reference of a computed expression:

```rust
let x = &mut foo(); // equivalent to `let mut tmp = foo(); let x = &mut tmp;`
```

or we might update a mutable reference returned by some function without assigning it

```rust
*func() = y; // equivalent to `let mut tmp = func(); *tmp = y;`
```

Furthermore, these temporary places might need resolving (just like any other place).
For example, suppose `pair()` returns `(&mut A, &mut A)`. If we write:

```rust
let x = pair().0;
```

Then `pair().1` goes unused and requires immediate resolution. (This last example
also illustrates that temporaries are nontrivial even when they are not mutated.)

In our analysis, we assign a TempId to each PlaceX::Temporary node, and in the
main part of the analysis, we treat these places just like any other places.
After we compute the set of resolutions to add, we find all temporary nodes that
are mentioned in the set. We then replace those temporaries with named Local nodes.

Specifically, we can replace the place node `Temporary(expr)` with
`WithExpr({ tmp = expr; }, Local("tmp"))` for a fresh `tmp` variable.
We place the declaration `let tmp;` at a larger scope.

### Closures

A closure is its own function, so its gets its own CFG. However, we still have to deal
with captured variables.

(Verus doesn't support capturing variables by mut-ref at the time of writing,
which makes things a bit easier for the time being.)

Note that our job is a *bit* simpler than having to compute the exact same set of
moves/references as rustc would for its MIR representation. For example,
if we consider something like:

```rust
let x = ...;
let foo = move || {
    let y = &x;
}
```

Technically, this moves `x` into the closure (since the closure is marked `move`) but because
the interior only uses an immutable reference to `x`, we can ignore the move when doing
analysis on the containing function.

In a similar vein, if we have a closure that only pulls in one field:

```rust
let x = ...;
let foo = move || {
    let y = x.0;
}
```

Rust might move the entirety of `x` instead of just `x.0` (this depends on the edition),
but the point it is doesn't matter: either way, for the sake of our analysis, we can say
that only `x.0` is getting moved (the semantics don't matter either way).
(In Rust, the difference only matters for computing where the drops go.)

Therefore, to determine what moves/mutations should represent the construction of the closure
in our analysis, we only need to look at what moves/mutations happen *inside* the closure.
(Though again, mutations of captured variables are currently disallowed.)

### Assignments

Typically when we do an assignment `x.f = 5;`,
we want to resolve the (overwritten) value of `x.f` from before the mutation.
For most places, this is already handled by our analysis, which marks `x.f` as
safe-to-resolve right before the assignment. We can't do this analysis for array/slice places
however, so we need to handle the case `x[i] = 5;` separately.
While building the CFG, we find all such cases (`assigns_to_resolve`) and update the
Expr appropriately (by setting the `resolve` field on the assignment nodes).

*/

use crate::ast::{
    BinaryOp, ByRef, CtorUpdateTail, Datatype, Dt, Expr, ExprX, FieldOpr, Fun, Function, Ident,
    Mode, ModeWrapperMode, Params, Path, Pattern, PatternBinding, PatternX, Place, PlaceX,
    ReadKind, SpannedTyped, Stmt, StmtX, Typ, TypDecoration, TypX, UnaryOpr, UnfinalizedReadKind,
    VarBinders, VarIdent, VarIdentDisambiguate, VariantCheck,
};
use crate::ast_util::{bool_typ, mk_bool, undecorate_typ, unit_typ};
use crate::ast_visitor::VisitorScopeMap;
use crate::def::Spanned;
use crate::messages::{AstId, Span};
use crate::modes::ReadKindFinals;
use crate::sst_util::subst_typ_for_datatype;
use air::ast_util::str_ident;
use air::scope_map::ScopeMap;
use std::collections::{HashMap, HashSet, VecDeque};
use std::rc::Rc;
use std::sync::Arc;

/// Updates the given function body to include AssumeResolved nodes at the appropriate places.
pub(crate) fn infer_resolution(
    params: &Params,
    body: &Expr,
    read_kind_finals: &ReadKindFinals,
    datatypes: &HashMap<Path, Datatype>,
    functions: &HashMap<Fun, Function>,
    var_modes: &HashMap<VarIdent, Mode>,
    temporary_modes: &HashMap<AstId, Mode>,
) -> Expr {
    let (cfg, assigns_to_resolve) =
        new_cfg(params, body, read_kind_finals, datatypes, functions, &var_modes, temporary_modes);
    //println!("{:}", pretty_cfg(&cfg));
    let resolutions = get_resolutions(&cfg);
    apply_resolutions(&cfg, params, body, resolutions, assigns_to_resolve)
}

/// Represents the tree structure of "places" under consideration.
#[derive(Debug)]
enum PlaceTree {
    Leaf(Typ),
    /// We have 1 child for every non-ghost field. Use None in place of the ghost fields.
    /// Outer vec corresponds to variants, inner vec to fields of that variant.
    /// Use the same ordering as on the datatype.
    Struct(Typ, Dt, Vec<Vec<Option<PlaceTree>>>),
    MutRef(Typ, Box<PlaceTree>),
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
struct TempId(u64);

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
enum LocalName {
    Named(VarIdent),
    /// AST ID of the PlaceX::Temporary
    Temporary(AstId, TempId),
}

/// A local var in the function, represents the base of any place.
/// The PlaceTree is expanded to represent the total amount of detail we need about this place,
/// which depends on how it is manipulated by the program.
///
/// For example, if we have a local variable `x: (T, T, T)`, and the programs assigns to `x.0`,
/// we would expand the tree to include [x.0, x.1, x.2]. If the program also assigns to `x.0.0`,
/// we expand it further, [[x.0.0, x.0.1] x.1, x.2]
///
/// Only non-ghost places should be represented.
#[derive(Debug)]
struct Local {
    name: LocalName,
    tree: PlaceTree,
}

/// Collection of all the locals in the program.
struct LocalCollection<'a> {
    locals: Vec<Local>,
    /// Map LocalName to index within the 'locals' vec
    ident_to_idx: HashMap<LocalName, usize>,

    /// Map AstId to temp id
    ast_id_to_temp_id: HashMap<AstId, TempId>,
    next_temp_id: u64,

    datatypes: &'a HashMap<Path, Datatype>,
    var_modes: HashMap<VarIdent, Mode>,
    temporary_modes: &'a HashMap<AstId, Mode>,
}

/// A projection that maps a place to a subplace
#[derive(Clone, Debug)]
pub(crate) enum ProjectionTyped {
    StructField(FieldOpr, Typ),
    DerefMut(Typ),
}

/// "Flattened" form of the vir::ast::Place type.
/// Only represents places based on locals, not temporaries.
#[derive(Clone, Debug)]
struct FlattenedPlaceTyped {
    pub local: LocalName,
    pub typ: Typ,
    pub projections: Vec<ProjectionTyped>,
}

/// Untyped version of the ProjectionTyped. The indices are used to walk the PlaceTree.
#[derive(Clone, Copy, PartialEq, Eq, Debug, PartialOrd, Ord)]
enum Projection {
    StructField((usize, usize)),
    DerefMut,
}

// note: sort_and_remove_redundant relies on sorting order
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct FlattenedPlace {
    local: usize,
    projections: Vec<Projection>,
}

/// Represents a position in the vir::ast::Expr where an AssumeResolved can be inserted.
#[derive(Clone, Copy, Debug)]
enum AstPosition {
    /// Right before an Expr or Stmt with the given ID
    Before(AstId),
    /// Right after an Expr or Stmt with the given ID
    After(AstId),
    /// For an ExprX::Call node, right after evaluation of the arguments but before the call itself
    AfterArguments(AstId),
    /// Immediately after a call in the 'unwinding' case.
    /// (Currently this is place is not representable in VIR so we do nothing with these.)
    OnUnwind(#[allow(dead_code)] AstId),
    /// After the given bool-typed Expr, only when that expression evaluates to the given bool
    AfterBool(AstId, bool),
    /// For a PlaceX::Temporary node, this is right after assignment to that temporary.
    AfterTempAssignment(AstId),
}

struct Instruction {
    kind: InstructionKind,
    /// Position in the Expr that corresponds to the point right *after* the execution of
    /// this instruction.
    post_instruction_position: AstPosition,
}

enum InstructionKind {
    /// Move from the place; must previously be initialized, becomes uninitialized.
    MoveFrom(FlattenedPlace),
    /// Overwrite the place; it previously may be initialized, uninitialized,
    /// or partially initialized. Whatever was there before gets dropped.
    /// The place is subsequently initialized.
    Overwrite(FlattenedPlace),
    /// Mutate the value at the place, which must previously be initialized and remains initialized
    Mutate(FlattenedPlace),
    /// Drop whatever is here; the place may previously be initialized, uninitialized,
    /// or partially initialized. Whatever was there before gets dropped.
    /// The place is subsequently uninitialized.
    DropFrom(FlattenedPlace),
}

type BBIndex = usize;
struct BasicBlock {
    instructions: Vec<Instruction>,
    /// Basic blocks that might jump to this one
    predecessors: Vec<BBIndex>,
    /// Basic blocks that we might jump to after the end
    successors: Vec<BBIndex>,
    /// Can we enter here?
    /// (Should be one entry for the whole function, and one entry for every closure)
    is_entry: bool,
    /// Is it possible to return from the function at the end of this basic block
    /// (i.e., as opposed to jumping to another basic block)
    is_exit: bool,

    /// Do we always want to add resolutions for all possibly relevant places at the beginning
    /// of this basic block? (This is used for loops, see the explanation above.)
    always_add_resolution_at_start: bool,

    /// Position in the Expr that corresponds to the start of the basic block
    position_of_start: AstPosition,
}

struct CFG<'a> {
    basic_blocks: Vec<BasicBlock>,
    locals: LocalCollection<'a>,
}

#[derive(Debug)]
struct ResolutionToInsert {
    place: FlattenedPlace,
    position: AstPosition,
}

////// CFG builder

struct Builder<'a> {
    basic_blocks: Vec<BasicBlock>,
    locals: LocalCollection<'a>,
    assigns_to_resolve: Vec<AstId>,

    /// Loop stack, outermost to innermost
    loops: Vec<LoopEntry>,
    /// First element is the outermost fn, followed by closure stack, outermost to innermost
    fns: Vec<FnScope>,

    read_kind_finals: &'a ReadKindFinals,
    functions: &'a HashMap<Fun, Function>,
}

#[derive(Clone)]
struct LoopEntry {
    label: Option<String>,
    /// BB to jump to on 'break'
    break_bb: BBIndex,
    /// BB to jump to on 'continue'
    continue_bb: BBIndex,
    /// Vars that should be dropped before returning to the beginning
    drops: Rc<Vec<FlattenedPlace>>,
}

/// Represents the scope for either the top-level fn or for any closure inside it
/// Tracks the "upvars", i.e., vars captured by the closure
/// (any var declared outside the closure but referenced from within it)
#[derive(Debug)]
struct FnScope {
    scope_map: ScopeMap<VarIdent, ()>,
    upvars_mutated: Vec<FlattenedPlace>,
    upvars_moved: Vec<FlattenedPlace>,
}

#[derive(Clone, Debug)]
enum ComputedPlaceTyped {
    /// Subfield of some local
    Exact(FlattenedPlaceTyped),
    /// Exec-mode subplace of some local, at a granularity that we don't track
    /// The place given here is the most-specific non-spec place that we might do analysis over.
    /// e.g. if the place is like `x.g[i].f` then we'd return Partial(x.g).
    Partial(FlattenedPlaceTyped),
    /// Spec-mode place. This is the most specific exec-mode place that we can provide,
    /// or None for a local.
    /// Examples:
    ///   * If the user writes x.foo.bar, and `x.foo` is proof-mode but `x.foo.bar`
    ///     is spec-mode, then return the place `x.foo`.
    ///   * If the local var itself is spec-mode, then None.
    ///   * If the user writes `x.foo[i].y` where `x.foo` is exec/proof and
    ///     `y` is a ghost place then return `x.foo`
    Ghost(Option<FlattenedPlaceTyped>),
}

#[derive(Debug)]
enum ComputedPlace {
    Exact(FlattenedPlace),
    Partial(FlattenedPlace),
    Ghost(Option<FlattenedPlace>),
}

/// Compute the CFG for the given expression.
fn new_cfg<'a>(
    params: &Params,
    body: &Expr,
    read_kind_finals: &'a ReadKindFinals,
    datatypes: &'a HashMap<Path, Datatype>,
    functions: &'a HashMap<Fun, Function>,
    var_modes: &'a HashMap<VarIdent, Mode>,
    temporary_modes: &'a HashMap<AstId, Mode>,
) -> (CFG<'a>, Vec<AstId>) {
    let mut var_modes = var_modes.clone();
    for p in params.iter() {
        var_modes.insert(p.x.name.clone(), p.x.mode);
    }

    let mut builder = Builder {
        basic_blocks: vec![],
        loops: vec![],
        fns: vec![],
        assigns_to_resolve: vec![],
        locals: LocalCollection {
            locals: vec![],
            ident_to_idx: HashMap::new(),
            ast_id_to_temp_id: HashMap::new(),
            next_temp_id: 0,
            datatypes,
            var_modes,
            temporary_modes,
        },
        read_kind_finals,
        functions,
    };
    let start_bb = builder.new_bb(AstPosition::Before(body.span.id), true);
    builder.basic_blocks[start_bb].is_entry = true;

    builder.push_fn();
    builder.push_scope();

    for param in params.iter() {
        builder.scope_insert(&param.x.name);
        if param.x.mode != Mode::Spec {
            let local = FlattenedPlaceTyped {
                local: LocalName::Named(param.x.name.clone()),
                typ: param.x.typ.clone(),
                projections: vec![],
            };
            let local_place = builder.locals.add_place(&local);
            builder.push_instruction_raw(
                start_bb,
                AstPosition::Before(body.span.id),
                InstructionKind::Overwrite(local_place),
            );
        }
    }

    let end_bb = builder.build(body, start_bb);
    builder.optionally_exit(end_bb);

    builder.pop_scope();
    builder.pop_fn();
    assert!(builder.fns.len() == 0);

    builder.compute_predecessors();

    let cfg = CFG { basic_blocks: builder.basic_blocks, locals: builder.locals };
    (cfg, builder.assigns_to_resolve)
}

impl<'a> Builder<'a> {
    fn compute_predecessors(&mut self) {
        for bb1 in 0..self.basic_blocks.len() {
            for j in 0..self.basic_blocks[bb1].successors.len() {
                let bb2 = self.basic_blocks[bb1].successors[j];
                self.basic_blocks[bb2].predecessors.push(bb1);
            }
        }
    }

    /// Initialize a new empty basic block
    fn new_bb(
        &mut self,
        start_position: AstPosition,
        always_add_resolution_at_start: bool,
    ) -> BBIndex {
        self.basic_blocks.push(BasicBlock {
            instructions: vec![],
            predecessors: vec![],
            successors: vec![],
            is_entry: false,
            is_exit: false,
            always_add_resolution_at_start,
            position_of_start: start_position,
        });
        self.basic_blocks.len() - 1
    }

    fn optionally_exit(&mut self, bb: Result<BBIndex, ()>) {
        match bb {
            Ok(bb) => {
                self.basic_blocks[bb].is_exit = true;
            }
            _ => {}
        }
    }

    fn optionally_push_successor(&mut self, bb: Result<BBIndex, ()>, successor: BBIndex) {
        match bb {
            Ok(bb) => {
                self.basic_blocks[bb].successors.push(successor);
            }
            _ => {}
        }
    }

    /// Push the instruction and update the recorded upvars if necessary
    fn push_instruction_propagate(
        &mut self,
        bb: BBIndex,
        post_instruction_position: AstPosition,
        instr: InstructionKind,
    ) {
        match &instr {
            InstructionKind::Overwrite(fp) | InstructionKind::Mutate(fp) => {
                if self.place_is_upvar(fp) {
                    self.fns.last_mut().unwrap().upvars_mutated.push(fp.clone());
                }
            }
            InstructionKind::MoveFrom(fp) => {
                if self.place_is_upvar(fp) {
                    self.fns.last_mut().unwrap().upvars_moved.push(fp.clone());
                }
            }
            InstructionKind::DropFrom(_) => {}
        }
        self.push_instruction_raw(bb, post_instruction_position, instr);
    }

    /// Just push the instruction
    /// Usually use `push_instruction_propagate` instead of this; only use raw at
    /// function/closure boundaries.
    fn push_instruction_raw(
        &mut self,
        bb: BBIndex,
        post_instruction_position: AstPosition,
        instr: InstructionKind,
    ) {
        self.basic_blocks[bb]
            .instructions
            .push(Instruction { kind: instr, post_instruction_position });
    }

    fn push_drops(
        &mut self,
        bb: BBIndex,
        post_instruction_position: AstPosition,
        drops: &[FlattenedPlace],
    ) {
        for fp in drops.iter() {
            self.push_instruction_propagate(
                bb,
                post_instruction_position,
                InstructionKind::DropFrom(fp.clone()),
            );
        }
    }

    fn get_loop(&self, loop_label: &Option<String>) -> LoopEntry {
        match loop_label {
            None => self.loops[self.loops.len() - 1].clone(),
            Some(label) => {
                for l in self.loops.iter().rev() {
                    match &l.label {
                        Some(label2) if *label == **label2 => {
                            return l.clone();
                        }
                        _ => {}
                    }
                }
                panic!("Could not find label {:}", label);
            }
        }
    }

    /// Process the given expression for building the CFG. Return the basic block
    /// corresponds to the end of the expression's execution, or Err(()) if
    /// execution never reachs the end of the expression.
    /// (This is not a real Err,
    fn build(&mut self, expr: &Expr, bb: BBIndex) -> Result<BBIndex, ()> {
        let span_id = expr.span.id;
        let mut bb = bb;
        match &expr.x {
            ExprX::Const(_)
            | ExprX::Var(_)
            | ExprX::VarLoc(_)
            | ExprX::VarAt(..)
            | ExprX::ConstVar(..)
            | ExprX::StaticVar(_)
            | ExprX::Loc(_)
            | ExprX::Quant(..)
            | ExprX::Closure(..)
            | ExprX::ExecFnByName(..)
            | ExprX::Choose { .. }
            | ExprX::WithTriggers { .. }
            | ExprX::Assign { .. }
            | ExprX::Fuel(..)
            | ExprX::RevealString(_)
            | ExprX::Header(_)
            | ExprX::AssertAssume { .. }
            | ExprX::AssertAssumeUserDefinedTypeInvariant { .. }
            | ExprX::AssertBy { .. }
            | ExprX::AssertQuery { .. }
            | ExprX::AssertCompute(..)
            | ExprX::ProofInSpec(..)
            | ExprX::AirStmt(..)
            | ExprX::Nondeterministic => Ok(bb),
            ExprX::Call(call_target, es, post_args) => {
                assert!(post_args.is_none());

                // Can skip the expression in CallTarget because
                // it can only be for FnSpec which is always a pure spec expression

                let mut two_phase_delayed_mutations = vec![];

                for e in es.iter() {
                    match &e.x {
                        ExprX::TwoPhaseBorrowMut(p) => {
                            let (p, bb1) = self.build_place_and_intern(p, bb)?;
                            bb = bb1;
                            if let Some(p) = p.get_place_for_mutation() {
                                two_phase_delayed_mutations.push(p);
                            }
                        }
                        _ => {
                            bb = self.build(e, bb)?;
                        }
                    }
                }

                for p in two_phase_delayed_mutations.into_iter() {
                    // The point we mark here is after the arguments execute,
                    // but before the call executes.
                    self.push_instruction_propagate(
                        bb,
                        AstPosition::AfterArguments(span_id),
                        InstructionKind::Mutate(p),
                    );
                }

                if crate::ast_util::call_no_unwind(call_target, &self.functions) {
                    Ok(bb)
                } else {
                    // Create an extra edge that ends immediately to represent unwinding
                    let unwind_bb = self.new_bb(AstPosition::OnUnwind(expr.span.id), false);
                    let main_bb = self.new_bb(AstPosition::After(expr.span.id), false);
                    self.basic_blocks[bb].successors.push(unwind_bb);
                    self.basic_blocks[bb].successors.push(main_bb);
                    self.basic_blocks[unwind_bb].is_exit = true;
                    Ok(main_bb)
                }
            }
            ExprX::Ctor(_dt, _id, binders, Some(CtorUpdateTail { place, taken_fields })) => {
                // CtorUpdateTail can only happen for braces-style ctor, so we don't need
                // to account for TwoPhaseBorrows. (If this ever changes we'll just get a panic
                // later about unhandled TwoPhaseBorrowMut node)

                for b in binders.iter() {
                    let e = &b.a;
                    bb = self.build(e, bb)?;
                }

                let (p, bb1) = self.build_place_typed(place, bb)?;
                bb = bb1;

                for (field_name, unfinal_read_kind) in taken_fields.iter() {
                    if self.is_move(unfinal_read_kind) {
                        if !matches!(p, ComputedPlaceTyped::Exact(..)) {
                            // TODO(new_mut_ref): we need careful handling here; this case
                            // should be impossible if the source program is well-formed,
                            // but the problem is we haven't run lifetime  checking yet.
                            // So we might get `try to move from foo[i]` error here or something.
                            panic!(
                                "Verus Internal State: inconsistent state, move out of ghost place or index"
                            )
                        }
                        if let Some(mut p) = p.clone().get_place_for_move() {
                            p.projections.push(ProjectionTyped::struct_field(
                                &place.typ,
                                field_name,
                                &self.locals.datatypes,
                            ));
                            let p = self.locals.add_place(&p);
                            self.push_instruction_propagate(
                                bb,
                                AstPosition::After(place.span.id),
                                InstructionKind::MoveFrom(p),
                            );
                        }
                    }
                }

                Ok(bb)
            }
            ExprX::Ctor(_dt, _id, binders, None) => {
                let mut two_phase_delayed_mutations = vec![];

                for b in binders.iter() {
                    let e = &b.a;
                    match &e.x {
                        ExprX::TwoPhaseBorrowMut(p) => {
                            let (p, bb1) = self.build_place_and_intern(p, bb)?;
                            bb = bb1;
                            if let Some(p) = p.get_place_for_mutation() {
                                two_phase_delayed_mutations.push(p);
                            }
                        }
                        _ => {
                            bb = self.build(e, bb)?;
                        }
                    }
                }

                for p in two_phase_delayed_mutations.into_iter() {
                    // Conveniently, we can just put these mutations after the Ctor call itself
                    // since the Ctor is a trivial operation, i.e., we don't need a special
                    // place for the "post_args" like we do with calls.
                    self.push_instruction_propagate(
                        bb,
                        AstPosition::After(span_id),
                        InstructionKind::Mutate(p),
                    );
                }

                Ok(bb)
            }
            ExprX::Binary(BinaryOp::And | BinaryOp::Or | BinaryOp::Implies, e1, e2) => {
                bb = self.build(e1, bb)?;

                let snd_block = self.new_bb(AstPosition::Before(e2.span.id), false);
                self.basic_blocks[bb].successors.push(snd_block);

                let snd_bb_end = self.build(e2, snd_block);

                let join_block = self.new_bb(AstPosition::After(span_id), false);
                self.basic_blocks[bb].successors.push(join_block);
                self.optionally_push_successor(snd_bb_end, join_block);
                Ok(join_block)
            }
            ExprX::If(cond, thn, els) => {
                // TODO(new_mut_ref): if the condition has conditional short-circuiting,
                // we could make a more precise CFG. Is this needed to match Rustc's analysis?

                let thn_position = AstPosition::Before(thn.span.id);
                let els_position = match els {
                    Some(els) => AstPosition::Before(els.span.id),
                    None => AstPosition::After(span_id),
                };
                let join_position = AstPosition::After(span_id);

                bb = self.build(cond, bb)?;

                let thn_block = self.new_bb(thn_position, false);
                let els_block = self.new_bb(els_position, false);
                self.basic_blocks[bb].successors.push(thn_block);
                self.basic_blocks[bb].successors.push(els_block);

                let thn_bb_end = self.build(thn, thn_block);

                let els_bb_end = match els {
                    Some(els) => self.build(els, els_block),
                    None => Ok(els_block),
                };

                if thn_bb_end.is_ok() || els_bb_end.is_ok() {
                    let join_block = self.new_bb(join_position, false);
                    self.optionally_push_successor(thn_bb_end, join_block);
                    self.optionally_push_successor(els_bb_end, join_block);
                    Ok(join_block)
                } else {
                    Err(())
                }
            }
            ExprX::NullaryOpr(_) => Ok(bb),
            ExprX::Unary(_, e) | ExprX::UnaryOpr(_, e) => {
                bb = self.build(e, bb)?;
                Ok(bb)
            }
            ExprX::Binary(_, e1, e2) | ExprX::BinaryOpr(_, e1, e2) => {
                bb = self.build(e1, bb)?;
                bb = self.build(e2, bb)?;
                Ok(bb)
            }
            ExprX::Multi(_, es) => {
                for e in es.iter() {
                    bb = self.build(e, bb)?;
                }
                Ok(bb)
            }
            ExprX::NonSpecClosure {
                params,
                proof_fn_modes,
                body,
                requires: _,
                ensures: _,
                ret: _,
                external_spec: _,
            } => {
                // Build the closure interior as a disconnected part of the CFG
                let fn_scope = self.build_closure(params, proof_fn_modes, body);

                // Emit instructions in the parent function that correspond to the
                // construction of the closure.
                for fp in fn_scope.upvars_moved.into_iter() {
                    self.push_instruction_propagate(
                        bb,
                        AstPosition::After(expr.span.id),
                        InstructionKind::MoveFrom(fp),
                    );
                }

                Ok(bb)
            }
            ExprX::ArrayLiteral(es) => {
                for e in es.iter() {
                    bb = self.build(e, bb)?;
                }
                Ok(bb)
            }
            ExprX::Match(place, arms) => {
                let (cpt, bb) = self.build_place_typed(place, bb)?;

                let mut arm_bb_ends = vec![];
                for arm in arms.iter() {
                    // TODO(new_mut_ref) handle guards

                    let arm_bb = self.new_bb(AstPosition::Before(arm.x.body.span.id), false);
                    self.basic_blocks[bb].successors.push(arm_bb);

                    self.append_instructions_for_pattern_moves_mutations(
                        &arm.x.pattern,
                        &cpt,
                        arm_bb,
                        AstPosition::Before(arm.x.body.span.id),
                    );

                    self.push_scope();
                    self.scope_insert_pattern(&arm.x.pattern);

                    for bound_var in pattern_all_bound_vars_with_ownership(
                        &arm.x.pattern,
                        &self.locals.var_modes,
                    )
                    .into_iter()
                    {
                        let fpt = FlattenedPlaceTyped {
                            local: LocalName::Named(bound_var.name),
                            typ: bound_var.typ,
                            projections: vec![],
                        };
                        let fp = self.locals.add_place(&fpt);
                        self.push_instruction_propagate(
                            arm_bb,
                            AstPosition::Before(arm.x.body.span.id),
                            InstructionKind::Overwrite(fp),
                        );
                    }

                    let arm_bb_end = self.build(&arm.x.body, arm_bb);

                    self.pop_scope();

                    if let Ok(arm_bb_end) = arm_bb_end {
                        arm_bb_ends.push(arm_bb_end);
                    }
                }

                if arm_bb_ends.len() > 0 {
                    let join_position = AstPosition::After(expr.span.id);
                    let join_block = self.new_bb(join_position, false);
                    for arm_bb_end in arm_bb_ends {
                        self.basic_blocks[arm_bb_end].successors.push(join_block);
                    }
                    Ok(join_block)
                } else {
                    Err(())
                }
            }
            ExprX::Loop {
                loop_isolation: _,
                // for-loops have already been de-sugared by this point, so they don't
                // need special handling
                is_for_loop: _,
                label,
                cond,
                body,
                invs: _,
                decrease: _,
            } => {
                let outer_body_bb_pos = match cond {
                    Some(cond) => AstPosition::Before(cond.span.id),
                    None => AstPosition::Before(body.span.id),
                };

                let outer_body_bb = self.new_bb(outer_body_bb_pos, true);
                let post_bb = self.new_bb(AstPosition::After(expr.span.id), true);

                let drops = self.loop_drops(&expr);
                self.loops.push(LoopEntry {
                    label: label.clone(),
                    break_bb: post_bb,
                    continue_bb: outer_body_bb,
                    drops: Rc::new(drops),
                });

                self.basic_blocks[bb].successors.push(outer_body_bb);

                let inner_body_bb = if let Some(cond) = cond {
                    // loop {
                    //   (outer body)
                    //   if cond {
                    //       (pre_break_bb)
                    //       break;
                    //   }
                    //   (inner body)
                    // }
                    //
                    // outer_body_bb -> {cond} -> cond_end_bb -[on true]-> inner_body_bb
                    //                             |
                    //                             ---[on false]-> pre_break_bb -> post_bb
                    //
                    // The reason for going through 'pre_break_bb' rather than going straight to
                    // post_bb is that we can put assumes in pre_break_bb that can be helpful
                    // to prove the invariants.

                    let cond_end_bb = self.build(cond, outer_body_bb);
                    let Ok(cond_end_bb) = cond_end_bb else {
                        self.loops.pop().unwrap();
                        return Ok(post_bb);
                    };

                    let pre_break_bb =
                        self.new_bb(AstPosition::AfterBool(cond.span.id, false), false);
                    let inner_body_bb = self.new_bb(AstPosition::Before(body.span.id), false);

                    self.basic_blocks[cond_end_bb].successors.push(pre_break_bb);
                    self.basic_blocks[cond_end_bb].successors.push(inner_body_bb);

                    self.basic_blocks[pre_break_bb].successors.push(post_bb);

                    inner_body_bb
                } else {
                    outer_body_bb
                };

                let end_bb = self.build(body, inner_body_bb);

                let loop_entry = self.loops.pop().unwrap();

                match end_bb {
                    Err(()) => {}
                    Ok(end_bb) => {
                        self.push_drops(
                            end_bb,
                            AstPosition::After(body.span.id),
                            &loop_entry.drops,
                        );
                        self.basic_blocks[end_bb].successors.push(outer_body_bb);
                    }
                }

                Ok(post_bb)
            }

            ExprX::OpenInvariant(e1, _, e2, _) => {
                // TODO(new_mut_ref): test cases
                bb = self.build(e1, bb)?;
                bb = self.build(e2, bb)?;
                Ok(bb)
            }
            ExprX::Return(e_opt) => {
                if let Some(e) = e_opt {
                    bb = self.build(e, bb)?;
                }
                self.basic_blocks[bb].is_exit = true;
                Err(())
            }
            ExprX::BreakOrContinue { label, is_break } => {
                let entry = self.get_loop(label);
                if *is_break {
                    self.basic_blocks[bb].successors.push(entry.break_bb);
                } else {
                    self.push_drops(bb, AstPosition::Before(expr.span.id), &entry.drops);
                    self.basic_blocks[bb].successors.push(entry.continue_bb);
                }
                Err(())
            }
            ExprX::Ghost { alloc_wrapper: _, tracked: _, expr } => {
                bb = self.build(expr, bb)?;
                Ok(bb)
            }
            ExprX::NeverToAny(e) => {
                let _ = self.build(e, bb)?;
                Err(())
            }
            ExprX::AssignToPlace { place, rhs, op, resolve } => {
                assert!(resolve.is_none());
                let (p, bb) = self.build_place_and_intern(place, bb)?;
                let bb = self.build(rhs, bb)?;
                match &p {
                    ComputedPlace::Partial(_) => {
                        if op.is_none() {
                            self.assigns_to_resolve.push(expr.span.id);
                        }
                    }
                    ComputedPlace::Exact(_) | ComputedPlace::Ghost(_) => {
                        // Exact: resolution handled by main part of the analysis
                        // Ghost: unsound to resolve because this place is ghost
                    }
                }
                match p {
                    ComputedPlace::Exact(p) => {
                        self.push_instruction_propagate(
                            bb,
                            AstPosition::After(span_id),
                            if op.is_some() {
                                InstructionKind::Mutate(p)
                            } else {
                                InstructionKind::Overwrite(p)
                            },
                        );
                    }
                    ComputedPlace::Partial(p) | ComputedPlace::Ghost(Some(p)) => {
                        self.push_instruction_propagate(
                            bb,
                            AstPosition::After(span_id),
                            InstructionKind::Mutate(p),
                        );
                    }
                    ComputedPlace::Ghost(None) => {}
                }
                Ok(bb)
            }
            ExprX::TwoPhaseBorrowMut(_p) => {
                // These must be handled contextually, so the recursion should skip over
                // these nodes.
                panic!("Verus Internal Error: unhandled TwoPhaseBorrowMut node");
            }
            ExprX::BorrowMut(p) => {
                let (p, bb) = self.build_place_and_intern(p, bb)?;
                if let Some(p) = p.get_place_for_mutation() {
                    self.push_instruction_propagate(
                        bb,
                        AstPosition::After(span_id),
                        InstructionKind::Mutate(p),
                    );
                }
                Ok(bb)
            }
            ExprX::ReadPlace(p, unfinal_read_kind) => {
                let (p, bb) = self.build_place_typed(p, bb)?;
                if self.is_move(unfinal_read_kind) {
                    if !matches!(p, ComputedPlaceTyped::Exact(..)) {
                        // TODO(new_mut_ref): we need careful handling here; this case
                        // should be impossible if the source program is well-formed,
                        // but the problem is we haven't run lifetime  checking yet.
                        // So we might get `try to move from foo[i]` error here or something.
                        panic!(
                            "Verus Internal State: inconsistent state, move out of ghost place or index"
                        )
                    }
                    if let Some(p) = p.get_place_for_move() {
                        let p = self.locals.add_place(&p);
                        self.push_instruction_propagate(
                            bb,
                            AstPosition::After(span_id),
                            InstructionKind::MoveFrom(p),
                        );
                    }
                    Ok(bb)
                } else {
                    Ok(bb)
                }
            }
            ExprX::Block(stmts, e_opt) => {
                let mut scope_count = 0;
                for s in stmts.iter() {
                    bb = match self.build_stmt(s, bb) {
                        Ok(bb) => bb,
                        Err(()) => {
                            for _i in 0..scope_count {
                                self.pop_scope();
                            }
                            return Err(());
                        }
                    };

                    if let StmtX::Decl { .. } = &s.x {
                        scope_count += 1;
                    }
                }
                if let Some(e) = e_opt {
                    bb = match self.build(e, bb) {
                        Ok(bb) => bb,
                        Err(()) => {
                            for _i in 0..scope_count {
                                self.pop_scope();
                            }
                            return Err(());
                        }
                    };
                }
                for _i in 0..scope_count {
                    self.pop_scope();
                }
                Ok(bb)
            }
            ExprX::UseLeftWhereRightCanHaveNoAssignments(..) => {
                panic!("UseLeftWhereRightCanHaveNoAssignments shouldn't be created yet");
            }
        }
    }

    fn build_stmt(&mut self, stmt: &Stmt, bb: BBIndex) -> Result<BBIndex, ()> {
        match &stmt.x {
            StmtX::Expr(e) => self.build(e, bb),
            StmtX::Decl { pattern, mode: _, init: None, els: None } => {
                self.push_scope();
                self.scope_insert_pattern(pattern);

                Ok(bb)
            }
            StmtX::Decl { pattern, mode: _, init: Some(init), els: None } => {
                let (cpt, bb) = self.build_place_typed(init, bb)?;
                self.append_instructions_for_pattern_moves_mutations(
                    pattern,
                    &cpt,
                    bb,
                    AstPosition::After(stmt.span.id),
                );

                self.push_scope();
                self.scope_insert_pattern(pattern);

                for bound_var in
                    pattern_all_bound_vars_with_ownership(pattern, &self.locals.var_modes)
                        .into_iter()
                {
                    let fpt = FlattenedPlaceTyped {
                        local: LocalName::Named(bound_var.name),
                        typ: bound_var.typ,
                        projections: vec![],
                    };
                    let fp = self.locals.add_place(&fpt);
                    self.push_instruction_propagate(
                        bb,
                        AstPosition::After(stmt.span.id),
                        InstructionKind::Overwrite(fp),
                    );
                }
                Ok(bb)
            }
            StmtX::Decl { pattern: _, mode: _, init: _, els: Some(_) } => {
                todo!()
            }
        }
    }

    fn build_place_and_intern(
        &mut self,
        place: &Place,
        bb: BBIndex,
    ) -> Result<(ComputedPlace, BBIndex), ()> {
        let r = self.build_place_typed(place, bb);
        match r {
            Ok((p, bb)) => {
                let sp = self.locals.add_computed_place(p);
                Ok((sp, bb))
            }
            Err(e) => Err(e),
        }
    }

    /// Returns Err(()) if the place expression never returns (can happen if it's a temporary)
    fn build_place_typed(
        &mut self,
        place: &Place,
        bb: BBIndex,
    ) -> Result<(ComputedPlaceTyped, BBIndex), ()> {
        match &place.x {
            PlaceX::Field(field_opr, p) => match self.build_place_typed(p, bb) {
                Ok((ComputedPlaceTyped::Exact(mut fpt), bb)) => {
                    let mode = field_opr_to_mode(field_opr, &self.locals.datatypes);
                    if mode == Mode::Spec {
                        Ok((ComputedPlaceTyped::Ghost(Some(fpt)), bb))
                    } else {
                        fpt.projections.push(ProjectionTyped::StructField(
                            FieldOpr { check: VariantCheck::None, ..field_opr.clone() },
                            place.typ.clone(),
                        ));
                        Ok((ComputedPlaceTyped::Exact(fpt), bb))
                    }
                }
                Ok((ComputedPlaceTyped::Partial(fpt), bb)) => {
                    let mode = field_opr_to_mode(field_opr, &self.locals.datatypes);
                    if mode == Mode::Spec {
                        Ok((ComputedPlaceTyped::Ghost(Some(fpt)), bb))
                    } else {
                        Ok((ComputedPlaceTyped::Partial(fpt), bb))
                    }
                }
                Ok((ComputedPlaceTyped::Ghost(opt_fpt), bb)) => {
                    Ok((ComputedPlaceTyped::Ghost(opt_fpt), bb))
                }
                Err(()) => Err(()),
            },
            PlaceX::DerefMut(p) => match self.build_place_typed(p, bb) {
                Ok((ComputedPlaceTyped::Exact(mut fpt), bb)) => {
                    fpt.projections.push(ProjectionTyped::DerefMut(place.typ.clone()));
                    Ok((ComputedPlaceTyped::Exact(fpt), bb))
                }
                Ok((ComputedPlaceTyped::Partial(fpt), bb)) => {
                    Ok((ComputedPlaceTyped::Partial(fpt), bb))
                }
                Ok((ComputedPlaceTyped::Ghost(opt_fpt), bb)) => {
                    Ok((ComputedPlaceTyped::Ghost(opt_fpt), bb))
                }
                Err(()) => Err(()),
            },
            PlaceX::Local(var) => {
                let mode = self.locals.var_modes[var];
                if mode == Mode::Spec {
                    Ok((ComputedPlaceTyped::Ghost(None), bb))
                } else {
                    let fpt = FlattenedPlaceTyped {
                        local: LocalName::Named(var.clone()),
                        typ: place.typ.clone(),
                        projections: vec![],
                    };
                    Ok((ComputedPlaceTyped::Exact(fpt), bb))
                }
            }
            PlaceX::Temporary(e) => {
                let bb = self.build(e, bb)?;
                let mode = self.locals.temporary_modes[&place.span.id];
                if mode == Mode::Spec {
                    Ok((ComputedPlaceTyped::Ghost(None), bb))
                } else {
                    let temp_name = self.locals.new_temp_name(place.span.id);

                    let fpt = FlattenedPlaceTyped {
                        local: temp_name,
                        typ: place.typ.clone(),
                        projections: vec![],
                    };
                    let fp = self.locals.add_place(&fpt);
                    self.push_instruction_propagate(
                        bb,
                        AstPosition::AfterTempAssignment(place.span.id),
                        InstructionKind::Overwrite(fp),
                    );

                    Ok((ComputedPlaceTyped::Exact(fpt), bb))
                }
            }
            PlaceX::ModeUnwrap(p, ModeWrapperMode::Proof) => {
                // As usual we just ignore Tracked (kinda like Box)
                self.build_place_typed(p, bb)
            }
            PlaceX::ModeUnwrap(p, ModeWrapperMode::Spec) => {
                let (cpt, bb) = self.build_place_typed(p, bb)?;
                Ok((cpt.to_ghost(), bb))
            }
            PlaceX::WithExpr(..) => {
                panic!("Verus Internal Error: unexpected PlaceX::WithExpr");
            }
            PlaceX::Index(p, idx, _kind, _needs_bounds_check) => {
                let (cpt, bb) = self.build_place_typed(p, bb)?;
                let bb = self.build(idx, bb)?;
                Ok((cpt.to_partial(), bb))
            }
        }
    }

    fn is_move(&self, unfinal_read_kind: &UnfinalizedReadKind) -> bool {
        match &unfinal_read_kind.preliminary_kind {
            ReadKind::Move => {
                matches!(self.read_kind_finals[&unfinal_read_kind.id], ReadKind::Move)
            }
            _ => false,
        }
    }

    /// Get the local vars that should be dropped when returning to the beginning
    /// of the the loop.
    fn loop_drops(&mut self, loop_expr: &Expr) -> Vec<FlattenedPlace> {
        // TODO(new_mut_ref): should get temps? Actually, is this even necessary at all?
        expr_all_bound_vars_with_ownership(loop_expr, &self.locals.var_modes)
            .iter()
            .map(|bv| {
                let fpt = FlattenedPlaceTyped {
                    local: LocalName::Named(bv.name.clone()),
                    typ: bv.typ.clone(),
                    projections: vec![],
                };
                self.locals.add_place(&fpt)
            })
            .collect()
    }

    fn append_instructions_for_pattern_moves_mutations(
        &mut self,
        pattern: &Pattern,
        cpt: &ComputedPlaceTyped,
        bb: BBIndex,
        position: AstPosition,
    ) {
        match cpt {
            ComputedPlaceTyped::Exact(fpt) => {
                let places = moves_and_muts_for_place_being_matched(
                    pattern,
                    &fpt,
                    &self.locals.datatypes,
                    &self.locals.var_modes,
                );
                for (fpt, by_ref) in places.into_iter() {
                    let fp = self.locals.add_place(&fpt);
                    self.push_instruction_propagate(
                        bb,
                        position,
                        match by_ref {
                            ByRef::No => InstructionKind::MoveFrom(fp),
                            ByRef::MutRef => InstructionKind::Mutate(fp),
                            ByRef::ImmutRef => unreachable!(),
                        },
                    );
                }
            }
            ComputedPlaceTyped::Partial(fpt) | ComputedPlaceTyped::Ghost(Some(fpt)) => {
                if crate::patterns::pattern_has_mut(pattern) {
                    let fp = self.locals.add_place(fpt);
                    self.push_instruction_propagate(bb, position, InstructionKind::Mutate(fp));
                }
            }
            ComputedPlaceTyped::Ghost(None) => {
                if crate::patterns::pattern_has_mut(pattern) {
                    // Mode-checking should disallow mutable references to ghost places
                    panic!("Verus Internal Error: mut refs found when matchee is ghost");
                }
            }
        }
    }

    fn build_closure(
        &mut self,
        params: &VarBinders<Typ>,
        proof_fn_modes: &Option<(Arc<Vec<Mode>>, Mode)>,
        body: &Expr,
    ) -> FnScope {
        let closure_prologue = self.new_bb(AstPosition::Before(body.span.id), true);
        self.basic_blocks[closure_prologue].is_entry = true;
        let closure_start_bb = self.new_bb(AstPosition::Before(body.span.id), false);

        self.push_fn();
        self.push_scope();

        for (i, param) in params.iter().enumerate() {
            self.scope_insert(&param.name);

            let mode = crate::ast_util::arg_mode_from_proof_fn_modes(proof_fn_modes, i);

            let f = self.locals.var_modes.insert(param.name.clone(), mode);
            assert!(f.is_none());

            if mode != Mode::Spec {
                let local = FlattenedPlaceTyped {
                    local: LocalName::Named(param.name.clone()),
                    typ: param.a.clone(),
                    projections: vec![],
                };
                let local_place = self.locals.add_place(&local);
                self.push_instruction_raw(
                    closure_prologue,
                    AstPosition::Before(body.span.id),
                    InstructionKind::Overwrite(local_place),
                );
            }
        }

        let closure_normal_ret_bb = self.build(body, closure_start_bb);
        self.optionally_exit(closure_normal_ret_bb);

        self.pop_scope();
        let mut fn_scope = self.pop_fn();

        if fn_scope.upvars_mutated.len() > 0 {
            // TODO(new_mut_ref): make this a real error
            panic!("Verus unsupported: closure mutable references");
        }

        fn_scope.upvars_moved = sort_and_remove_redundant(fn_scope.upvars_moved);
        for fp in fn_scope.upvars_moved.iter() {
            self.push_instruction_raw(
                closure_prologue,
                AstPosition::Before(body.span.id),
                InstructionKind::Overwrite(fp.clone()),
            );
        }
        self.basic_blocks[closure_prologue].successors.push(closure_start_bb);

        fn_scope
    }

    fn push_fn(&mut self) {
        self.fns.push(FnScope {
            scope_map: ScopeMap::new(),
            upvars_mutated: vec![],
            upvars_moved: vec![],
        });
    }

    fn pop_fn(&mut self) -> FnScope {
        let p = self.fns.pop().unwrap();
        assert_eq!(p.scope_map.num_scopes(), 0);
        p
    }

    fn push_scope(&mut self) {
        // TODO(new_mut_ref): disallow shadowing
        self.fns.last_mut().unwrap().scope_map.push_scope(true);
    }

    fn pop_scope(&mut self) {
        self.fns.last_mut().unwrap().scope_map.pop_scope();
    }

    fn scope_insert(&mut self, id: &VarIdent) {
        self.fns.last_mut().unwrap().scope_map.insert(id.clone(), ()).unwrap();
    }

    fn scope_insert_pattern(&mut self, pattern: &Pattern) {
        match &pattern.x {
            PatternX::Wildcard(_) | PatternX::Expr(_) | PatternX::Range(_, _) => {
                // nothing to do
            }
            PatternX::Var(binding) => {
                self.scope_insert(&binding.name);
            }
            PatternX::Binding { binding, sub_pat } => {
                self.scope_insert(&binding.name);
                self.scope_insert_pattern(sub_pat);
            }
            PatternX::Constructor(_dt, _variant, patterns) => {
                for p in patterns.iter() {
                    self.scope_insert_pattern(&p.a);
                }
            }
            PatternX::Or(sub_pat, _) | PatternX::ImmutRef(sub_pat) | PatternX::MutRef(sub_pat) => {
                self.scope_insert_pattern(sub_pat);
            }
        }
    }

    fn place_is_upvar(&self, fp: &FlattenedPlace) -> bool {
        match &self.locals.locals[fp.local].name {
            LocalName::Named(var_ident) => {
                for i in (0..self.fns.len()).rev() {
                    if self.fns[i].scope_map.contains_key(var_ident) {
                        return i != self.fns.len() - 1;
                    }
                }
                panic!("Verus Internal Error: place_is_upvar failed to find var");
            }
            LocalName::Temporary(..) => false,
        }
    }
}

////// Patterns

pub struct BoundVar {
    pub name: VarIdent,
    pub typ: Typ,
}

/// Get all locals which are bound in this expression for which we care about
/// ownership tracking (i.e., exec and proof mode).
pub fn expr_all_bound_vars_with_ownership(
    expr: &Expr,
    modes: &HashMap<VarIdent, Mode>,
) -> Vec<BoundVar> {
    let mut out = vec![];
    let mut names = HashSet::<VarIdent>::new();
    crate::ast_visitor::ast_visitor_check::<(), _, _, _, _, _, _>(
        expr,
        &mut (),
        &mut |_env, _scope_map, _expr| Ok(()),
        &mut |_env, _scope_map, _stmt| Ok(()),
        &mut |_env, _scope_map, pattern| {
            match &pattern.x {
                PatternX::Var(PatternBinding { name, mutable: _, by_ref: _, typ, copy: _ })
                | PatternX::Binding {
                    binding: PatternBinding { name, mutable: _, by_ref: _, typ, copy: _ },
                    sub_pat: _,
                } => {
                    let spec = matches!(&modes[name], Mode::Spec);
                    if !spec {
                        if !names.contains(name) {
                            names.insert(name.clone());
                            out.push(BoundVar { name: name.clone(), typ: typ.clone() });
                        }
                    }
                }
                _ => {}
            }
            Ok(())
        },
        &mut |_env, _scope_map, _typ, _span| Ok(()),
        &mut |_env, _scope_map, _place| Ok(()),
    )
    .unwrap();
    out
}

/// Same as above, but takes a Pattern as input
pub fn pattern_all_bound_vars_with_ownership(
    pattern: &Pattern,
    modes: &HashMap<VarIdent, Mode>,
) -> Vec<BoundVar> {
    fn pattern_all_bound_vars_rec(
        pattern: &Pattern,
        out: &mut Vec<BoundVar>,
        modes: &HashMap<VarIdent, Mode>,
    ) {
        match &pattern.x {
            PatternX::Wildcard(_) => {}
            PatternX::Var(PatternBinding { name, mutable: _, by_ref: _, typ, copy: _ })
            | PatternX::Binding {
                binding: PatternBinding { name, mutable: _, by_ref: _, typ, copy: _ },
                sub_pat: _,
            } => {
                let spec = matches!(&modes[name], Mode::Spec);
                if !spec {
                    out.push(BoundVar { name: name.clone(), typ: typ.clone() });
                }

                match &pattern.x {
                    PatternX::Binding { sub_pat, .. } => {
                        pattern_all_bound_vars_rec(sub_pat, out, modes);
                    }
                    _ => {}
                }
            }
            PatternX::Constructor(_dt, _variant, patterns) => {
                for binder in patterns.iter() {
                    pattern_all_bound_vars_rec(&binder.a, out, modes);
                }
            }
            PatternX::Or(pat1, _) | PatternX::ImmutRef(pat1) | PatternX::MutRef(pat1) => {
                pattern_all_bound_vars_rec(&pat1, out, modes);
            }
            PatternX::Expr(_) => {}
            PatternX::Range(_, _) => {}
        }
    }

    let mut v = vec![];
    pattern_all_bound_vars_rec(pattern, &mut v, modes);
    v
}

/// When a place is matched against a pattern, it induces some moves,
/// e.g.:
///
/// ```
/// let (x, _) = y;   // moves y.0
/// let (x, _) = y.1; // moves y.1.0
/// ```

fn moves_and_muts_for_place_being_matched(
    pattern: &Pattern,
    fpt: &FlattenedPlaceTyped,
    datatypes: &HashMap<Path, Datatype>,
    modes: &HashMap<VarIdent, Mode>,
) -> Vec<(FlattenedPlaceTyped, ByRef)> {
    let projs = moves_and_muts_for_pattern(pattern, datatypes, modes);
    projs
        .into_iter()
        .map(|(mut projs, by_ref)| {
            let mut f = fpt.clone();
            f.projections.append(&mut projs);
            (f, by_ref)
        })
        .collect()
}

fn moves_and_muts_for_pattern(
    pattern: &Pattern,
    datatypes: &HashMap<Path, Datatype>,
    modes: &HashMap<VarIdent, Mode>,
) -> Vec<(Vec<ProjectionTyped>, ByRef)> {
    fn moves_and_muts_for_pattern_rec(
        pattern: &Pattern,
        projs: &mut Vec<ProjectionTyped>,
        out: &mut Vec<(Vec<ProjectionTyped>, ByRef)>,
        datatypes: &HashMap<Path, Datatype>,
        modes: &HashMap<VarIdent, Mode>,
    ) {
        match &pattern.x {
            PatternX::Wildcard(_) => {}
            PatternX::Var(PatternBinding { name, mutable: _, by_ref, typ: _, copy })
            | PatternX::Binding {
                binding: PatternBinding { name, mutable: _, by_ref, typ: _, copy },
                sub_pat: _,
            } => {
                // no need to descend into subpat, already moving or borrowing the whole thing
                if *by_ref != ByRef::ImmutRef && !*copy && !matches!(modes[name], Mode::Spec) {
                    out.push((projs.clone(), *by_ref));
                }
            }
            PatternX::Constructor(dt, variant, patterns) => {
                for binder in patterns.iter() {
                    let field_typ = binder.a.typ.clone();
                    let proj = ProjectionTyped::StructField(
                        FieldOpr {
                            datatype: dt.clone(),
                            variant: variant.clone(),
                            field: binder.name.clone(),
                            get_variant: false,
                            check: crate::ast::VariantCheck::None,
                        },
                        field_typ,
                    );

                    projs.push(proj);
                    moves_and_muts_for_pattern_rec(&binder.a, projs, out, datatypes, modes);
                    projs.pop();
                }
            }
            PatternX::Or(_, _) => {
                // TODO(new_mut_ref): this might be complicated, need to see what rustc does
                todo!()
            }
            PatternX::Expr(..) | PatternX::Range(..) => {}
            PatternX::ImmutRef(_) => {
                // can skip this, nothing can be moved or mutated from behind an immutable ref
            }
            PatternX::MutRef(sub_pat) => {
                let proj = ProjectionTyped::DerefMut(sub_pat.typ.clone());

                projs.push(proj);
                moves_and_muts_for_pattern_rec(sub_pat, projs, out, datatypes, modes);
                projs.pop();
            }
        }
    }

    let mut out = vec![];
    moves_and_muts_for_pattern_rec(pattern, &mut vec![], &mut out, datatypes, modes);
    out
}

////// Place trees

impl<'a> LocalCollection<'a> {
    fn new_temp_name(&mut self, ast_id: AstId) -> LocalName {
        let temp_id = TempId(self.next_temp_id);
        self.next_temp_id += 1;
        assert!(!self.ast_id_to_temp_id.contains_key(&ast_id));
        self.ast_id_to_temp_id.insert(ast_id, temp_id);
        LocalName::Temporary(ast_id, temp_id)
    }

    fn add_computed_place(&mut self, p: ComputedPlaceTyped) -> ComputedPlace {
        match p {
            ComputedPlaceTyped::Exact(fpt) => {
                let sp = self.add_place(&fpt);
                ComputedPlace::Exact(sp)
            }
            ComputedPlaceTyped::Partial(fpt) => {
                let sp = self.add_place(&fpt);
                ComputedPlace::Partial(sp)
            }
            ComputedPlaceTyped::Ghost(Some(fpt)) => {
                let sp = self.add_place(&fpt);
                ComputedPlace::Ghost(Some(sp))
            }
            ComputedPlaceTyped::Ghost(None) => ComputedPlace::Ghost(None),
        }
    }

    /// Given a FlattenedPlaceTyped, we extend the tree if necessary so that it is deep enough
    /// to incorporate the given place. Returns a FlattenedPlace which indexes into the tree.
    fn add_place(&mut self, p: &FlattenedPlaceTyped) -> FlattenedPlace {
        if !self.ident_to_idx.contains_key(&p.local) {
            self.locals.push(Local { name: p.local.clone(), tree: PlaceTree::Leaf(p.typ.clone()) });
            self.ident_to_idx.insert(p.local.clone(), self.locals.len() - 1);
        }
        let idx = self.ident_to_idx[&p.local];

        let projections =
            Self::extend_tree(&mut self.locals[idx].tree, &p.typ, &p.projections, &self.datatypes);

        FlattenedPlace { local: idx, projections: projections }
    }

    fn extend_tree(
        tree: &mut PlaceTree,
        root_typ: &Typ,
        projections: &[ProjectionTyped],
        datatypes: &HashMap<Path, Datatype>,
    ) -> Vec<Projection> {
        let mut tree: &mut PlaceTree = tree;
        let mut output_projections: Vec<Projection> = vec![];
        let mut cur_typ = root_typ.clone();
        for projection_typed in projections.iter() {
            if let PlaceTree::Leaf(_typ) = tree {
                // Note: the type off the PlaceTree::Leaf might not be head-normalized
                // (i.e., it might be a TypX::Projection instead of something concrete
                // like TypX::MutRef or TypX::Datatype).
                // (Note: TypX::Projection shouldn't be confused with the notion of
                // 'place projection' common in this file.)
                // Anyway, the `cur_typ` should be equivalent and should also be
                // head-normalized, so use that instead.
                let typ = undecorate_box_trk_decorations(&cur_typ);

                match &**typ {
                    TypX::MutRef(inner_typ) => {
                        *tree = PlaceTree::MutRef(
                            typ.clone(),
                            Box::new(PlaceTree::Leaf(inner_typ.clone())),
                        );
                    }
                    TypX::Datatype(dt, typ_args, _) => match dt {
                        Dt::Tuple(n) => {
                            *tree = PlaceTree::Struct(
                                typ.clone(),
                                dt.clone(),
                                vec![
                                    (0..*n)
                                        .map(|i| Some(PlaceTree::Leaf(typ_args[i].clone())))
                                        .collect(),
                                ],
                            );
                        }
                        Dt::Path(path) => {
                            let datatype = &datatypes[path];
                            let fields = datatype
                                .x
                                .variants
                                .iter()
                                .map(|variant| {
                                    variant
                                        .fields
                                        .iter()
                                        .map(|f| {
                                            if f.a.1 == Mode::Spec {
                                                None
                                            } else {
                                                Some(PlaceTree::Leaf(subst_typ_for_datatype(
                                                    &datatype.x.typ_params,
                                                    typ_args,
                                                    &f.a.0,
                                                )))
                                            }
                                        })
                                        .collect::<Vec<Option<PlaceTree>>>()
                                })
                                .collect::<Vec<Vec<Option<PlaceTree>>>>();
                            *tree = PlaceTree::Struct(typ.clone(), dt.clone(), fields);
                        }
                    },
                    _ => {
                        // TODO(new_mut_ref) I think this case can actually happen since
                        // lifetime-checking hasn't run yet?
                        panic!("Verus internal internal: unexpected type from projections")
                    }
                }
            }

            let projection = match projection_typed {
                ProjectionTyped::StructField(field_opr, _typ) => {
                    Projection::StructField(field_opr_to_indices(field_opr, datatypes))
                }
                ProjectionTyped::DerefMut(_typ) => Projection::DerefMut,
            };
            output_projections.push(projection);

            match &projection {
                Projection::StructField((variant_idx, field_idx)) => match tree {
                    PlaceTree::Leaf(_) => unreachable!(),
                    PlaceTree::Struct(_, _, subtrees) => {
                        // If this unwrap fails, it means we are improperly trying to
                        // manipulate a ghost place
                        tree = subtrees[*variant_idx][*field_idx].as_mut().unwrap();
                    }
                    PlaceTree::MutRef(..) => {
                        panic!(
                            "Verus internal error: extend_tree failed, conflicting projection type"
                        );
                    }
                },
                Projection::DerefMut => match tree {
                    PlaceTree::Leaf(_) => unreachable!(),
                    PlaceTree::Struct(..) => {
                        panic!(
                            "Verus internal error: extend_tree failed, conflicting projection type"
                        );
                    }
                    PlaceTree::MutRef(_, inner) => {
                        tree = &mut *inner;
                    }
                },
            }

            cur_typ = projection_typed.typ();
        }
        output_projections
    }

    /// Turn a FlattenedPlace back into a vir::ast::Place
    fn to_ast_place(&self, span: &Span, fp: &FlattenedPlace) -> Place {
        let mut ast_place = SpannedTyped::new(
            span,
            self.locals[fp.local].tree.typ(),
            PlaceX::Local(self.locals[fp.local].name.to_var_ident()),
        );
        let mut tree = &self.locals[fp.local].tree;
        for projection in fp.projections.iter() {
            match projection {
                Projection::StructField((variant_idx, field_idx)) => {
                    let (dt, inner_trees) = match tree {
                        PlaceTree::Struct(_ty, dt, trees) => (dt, trees),
                        _ => unreachable!(),
                    };
                    let inner_tree = inner_trees[*variant_idx][*field_idx].as_ref().unwrap();
                    let field_opr = match dt {
                        Dt::Tuple(n) => {
                            assert!(*variant_idx == 0);
                            crate::ast_util::mk_tuple_field_opr(*n, *field_idx)
                        }
                        Dt::Path(path) => {
                            let datatype = &self.datatypes[path];
                            let variant = &datatype.x.variants[*variant_idx];
                            FieldOpr {
                                datatype: dt.clone(),
                                variant: variant.name.clone(),
                                field: variant.fields[*field_idx].name.clone(),
                                get_variant: false,
                                check: crate::ast::VariantCheck::None,
                            }
                        }
                    };
                    ast_place = SpannedTyped::new(
                        span,
                        inner_tree.typ(),
                        PlaceX::Field(field_opr, ast_place),
                    );
                    tree = &inner_tree;
                }
                Projection::DerefMut => {
                    let inner_tree = match tree {
                        PlaceTree::MutRef(_ty, tr) => tr,
                        _ => unreachable!(),
                    };
                    ast_place =
                        SpannedTyped::new(span, inner_tree.typ(), PlaceX::DerefMut(ast_place));
                    tree = &inner_tree;
                }
            }
        }
        ast_place
    }

    fn places_skip_insides_of_mut_refs(&self) -> Vec<FlattenedPlace> {
        self.traverse_get_places(false)
    }

    fn places_including_insides_of_mut_refs(&self) -> Vec<FlattenedPlace> {
        self.traverse_get_places(true)
    }

    fn traverse_get_places(&self, go_inside_muts: bool) -> Vec<FlattenedPlace> {
        let mut v = vec![];
        for (i, local) in self.locals.iter().enumerate() {
            let mut sp = FlattenedPlace { local: i, projections: vec![] };
            Self::traverse_rec(&local.tree, &mut sp, &mut v, go_inside_muts);
        }
        v
    }

    fn traverse_rec(
        tree: &PlaceTree,
        cur: &mut FlattenedPlace,
        output: &mut Vec<FlattenedPlace>,
        go_inside_muts: bool,
    ) {
        match tree {
            PlaceTree::Leaf(_t) => {
                output.push(cur.clone());
            }
            PlaceTree::Struct(_t, _, children) => {
                for (v, variant_children) in children.iter().enumerate() {
                    for (f, child) in variant_children.iter().enumerate() {
                        if let Some(child) = child {
                            cur.projections.push(Projection::StructField((v, f)));
                            Self::traverse_rec(child, cur, output, go_inside_muts);
                            cur.projections.pop();
                        }
                    }
                }
            }
            PlaceTree::MutRef(_t, child) => {
                output.push(cur.clone());
                if go_inside_muts {
                    cur.projections.push(Projection::DerefMut);
                    Self::traverse_rec(child, cur, output, go_inside_muts);
                    cur.projections.pop();
                }
            }
        }
    }
}

fn undecorate_box_trk_decorations(t: &Typ) -> &Typ {
    match &**t {
        TypX::Decorate(TypDecoration::Box, _, t) => undecorate_box_trk_decorations(t),
        TypX::Decorate(TypDecoration::Tracked, _, t) => undecorate_box_trk_decorations(t),
        _ => t,
    }
}

fn field_opr_to_indices(
    field_opr: &FieldOpr,
    datatypes: &HashMap<Path, Datatype>,
) -> (usize, usize) {
    match &field_opr.datatype {
        Dt::Tuple(n) => {
            let p = field_opr.field.parse::<usize>().unwrap();
            assert!(p < *n);
            (0, p)
        }
        Dt::Path(path) => {
            let datatype = &datatypes[path];
            let variant_idx =
                datatype.x.variants.iter().position(|v| v.name == field_opr.variant).unwrap();
            let variant = &datatype.x.variants[variant_idx];
            let field_idx = variant.fields.iter().position(|f| f.name == field_opr.field).unwrap();
            (variant_idx, field_idx)
        }
    }
}

fn field_opr_to_mode(field_opr: &FieldOpr, datatypes: &HashMap<Path, Datatype>) -> Mode {
    match &field_opr.datatype {
        Dt::Tuple(_) => Mode::Exec,
        Dt::Path(path) => {
            let datatype = &datatypes[path];
            let variant = crate::ast_util::get_variant(&datatype.x.variants, &field_opr.variant);
            let field = crate::ast_util::get_field(&variant.fields, &field_opr.field);
            field.a.1
        }
    }
}

impl PlaceTree {
    fn typ(&self) -> &Typ {
        match self {
            PlaceTree::Leaf(t) => t,
            PlaceTree::Struct(t, _, _) => t,
            PlaceTree::MutRef(t, _) => t,
        }
    }
}

impl FlattenedPlace {
    /// Do the 2 places intersect at all?
    fn intersects(&self, other: &Self) -> bool {
        if self.local == other.local {
            let m = std::cmp::min(self.projections.len(), other.projections.len());
            (0..m).all(|i| self.projections[i] == other.projections[i])
        } else {
            false
        }
    }

    /// Does the first place fully contain the second?
    /// e.g., x, x.f  -> yes
    ///       x, x    -> yes
    ///       x, *x   -> yes
    ///       x.f, x  -> no
    fn contains(&self, other: &Self) -> bool {
        self.local == other.local
            && self.projections.len() <= other.projections.len()
            && (0..self.projections.len()).all(|i| self.projections[i] == other.projections[i])
    }

    /// Does the first place fully contain the second but NOT via deref?
    /// e.g., x, x.f  -> yes
    ///       x, *x   -> no
    fn contains_and_not_separated_by_deref(&self, other: &Self) -> bool {
        self.contains(other)
            && (self.projections.len()..other.projections.len())
                .all(|i| !matches!(other.projections[i], Projection::DerefMut))
    }

    /// Does the place have a deref projection?
    fn has_deref(&self) -> bool {
        self.projections.iter().any(|p| matches!(p, Projection::DerefMut))
    }

    /// Can the spec-value of the given place be changed by the instruction?
    fn value_may_change(&self, instr: &Instruction) -> bool {
        match &instr.kind {
            InstructionKind::MoveFrom(_) => false,
            InstructionKind::Overwrite(sp) => self.intersects(sp),
            InstructionKind::Mutate(sp) => self.intersects(sp),
            InstructionKind::DropFrom(_) => false,
        }
    }
}

impl ComputedPlace {
    fn get_place_for_mutation(self) -> Option<FlattenedPlace> {
        match self {
            ComputedPlace::Exact(p) => Some(p),
            ComputedPlace::Partial(p) => Some(p),
            ComputedPlace::Ghost(p) => {
                // When mutating a ghost place, we treat it as a mutation of whatever
                // "real" place contains it
                p
            }
        }
    }
}

impl ComputedPlaceTyped {
    fn to_ghost(self) -> ComputedPlaceTyped {
        match self {
            ComputedPlaceTyped::Exact(fpt) => ComputedPlaceTyped::Ghost(Some(fpt)),
            ComputedPlaceTyped::Partial(fpt) => ComputedPlaceTyped::Ghost(Some(fpt)),
            ComputedPlaceTyped::Ghost(opt_fpt) => ComputedPlaceTyped::Ghost(opt_fpt),
        }
    }

    fn to_partial(self) -> ComputedPlaceTyped {
        match self {
            ComputedPlaceTyped::Exact(fpt) => ComputedPlaceTyped::Partial(fpt),
            ComputedPlaceTyped::Partial(fpt) => ComputedPlaceTyped::Partial(fpt),
            ComputedPlaceTyped::Ghost(opt_fpt) => ComputedPlaceTyped::Ghost(opt_fpt),
        }
    }

    fn get_place_for_move(self) -> Option<FlattenedPlaceTyped> {
        match self {
            ComputedPlaceTyped::Exact(p) => Some(p),
            ComputedPlaceTyped::Partial(_) | ComputedPlaceTyped::Ghost(_) => {
                // reading out of a ghost field is NOT a move
                None
            }
        }
    }
}

impl ProjectionTyped {
    fn struct_field(
        dt_typ: &Typ,
        field_name: &Ident,
        datatypes: &HashMap<Path, Datatype>,
    ) -> ProjectionTyped {
        let typ = undecorate_typ(dt_typ);
        let (dt, typ_args) = match &*typ {
            TypX::Datatype(dt, typ_args, _) => (dt, typ_args),
            _ => panic!("Internal Verus Error: struct_field called for non-struct type"),
        };
        let (variant_name, field_typ) = match dt {
            Dt::Tuple(_arity) => {
                panic!("Internal Verus Error: struct_field called for tuple")
                /*let p = field_name.parse::<usize>().unwrap();
                let field_typ = typ_args[p].clone()
                let variant_name = crate::def::prefix_tuple_variant(arity);
                (variant_name, field_typ)*/
            }
            Dt::Path(path) => {
                let datatype = &datatypes[path];
                assert!(datatype.x.variants.len() == 1);
                let variant = &datatype.x.variants[0];
                let field = crate::ast_util::get_field(&variant.fields, field_name);
                let field_typ =
                    subst_typ_for_datatype(&datatype.x.typ_params, typ_args, &field.a.0);
                (variant.name.clone(), field_typ)
            }
        };
        ProjectionTyped::StructField(
            FieldOpr {
                datatype: dt.clone(),
                variant: variant_name.clone(),
                field: field_name.clone(),
                get_variant: false,
                check: crate::ast::VariantCheck::None,
            },
            field_typ,
        )
    }

    fn typ(&self) -> Typ {
        match self {
            ProjectionTyped::StructField(_, typ) => typ.clone(),
            ProjectionTyped::DerefMut(typ) => typ.clone(),
        }
    }
}

impl LocalName {
    fn to_var_ident(&self) -> VarIdent {
        match self {
            LocalName::Named(x) => {
                // This disambiguator shouldn't have been used yet
                assert!(!matches!(x.1, VarIdentDisambiguate::ResInfTemp(_)));
                x.clone()
            }
            LocalName::Temporary(_ast_id, TempId(i)) => {
                VarIdent(str_ident("tmp"), VarIdentDisambiguate::ResInfTemp(*i))
            }
        }
    }

    fn is_temp(&self) -> bool {
        match self {
            LocalName::Named(..) => false,
            LocalName::Temporary(..) => true,
        }
    }
}

fn sort_and_remove_redundant(v: Vec<FlattenedPlace>) -> Vec<FlattenedPlace> {
    let mut v = v;
    v.sort();
    let mut w: Vec<FlattenedPlace> = vec![];
    for fp in v.into_iter() {
        if w.len() == 0 || !w[w.len() - 1].contains(&fp) {
            w.push(fp);
        }
    }
    for i in 0..w.len() {
        for j in 0..i {
            assert!(!w[i].intersects(&w[j]));
        }
    }
    w
}

////// CFG dataflow analysis

/// Trait defining a lattice for dataflow analysis
trait DataflowState {
    type Const;

    fn join(&mut self, b: &Self);
    fn transfer(&self, instr: &Instruction, c: &Self::Const) -> Self;
}

enum Direction {
    Forward,
    Reverse,
}

struct DataflowOutput<D> {
    /// output[bb][0] means "value at the start of bb"
    /// output[bb][i] means "value right after instruction (i-1)"
    output: Vec<Vec<D>>,
}

fn do_dataflow<D: DataflowState + Clone + Eq>(
    cfg: &CFG,
    empty: D,
    entry_or_exit: D,
    c: &D::Const,
    dir: Direction,
) -> DataflowOutput<D> {
    let mut output = DataflowOutput { output: vec![] };
    for bb in cfg.basic_blocks.iter() {
        let mut v = vec![];
        for _i in 0..bb.instructions.len() + 1 {
            v.push(empty.clone());
        }
        output.output.push(v);
    }

    let mut worklist = VecDeque::<BBIndex>::new();
    let mut in_worklist = vec![false; cfg.basic_blocks.len()];
    let mut has_run_yet = vec![false; cfg.basic_blocks.len()];

    match dir {
        Direction::Forward => {
            for i in 0..cfg.basic_blocks.len() {
                if cfg.basic_blocks[i].is_entry {
                    *output.output[i].last_mut().unwrap() = entry_or_exit.clone();
                }
                worklist.push_back(i);
                in_worklist[i] = true;
            }

            loop {
                let Some(bb) = worklist.pop_front() else {
                    break;
                };
                in_worklist[bb] = false;

                let new_value = join_predecessors(&output, &cfg, bb, &empty, &entry_or_exit);
                let slot = &mut output.output[bb][0];

                if !has_run_yet[bb] || *slot != new_value {
                    *slot = new_value;
                    transfer_forward(&mut output.output[bb], &cfg.basic_blocks[bb].instructions, c);
                    has_run_yet[bb] = true;
                    for bb1 in cfg.basic_blocks[bb].successors.iter() {
                        if !in_worklist[*bb1] {
                            worklist.push_back(*bb1);
                            in_worklist[*bb1] = true;
                        }
                    }
                }
            }
        }
        Direction::Reverse => {
            for i in (0..cfg.basic_blocks.len()).rev() {
                if cfg.basic_blocks[i].is_exit {
                    *output.output[i].last_mut().unwrap() = entry_or_exit.clone();
                }
                worklist.push_back(i);
                in_worklist[i] = true;
            }

            while worklist.len() > 0 {
                let Some(bb) = worklist.pop_front() else {
                    break;
                };
                in_worklist[bb] = false;

                let new_value = join_successors(&output, &cfg, bb, &empty, &entry_or_exit);
                let slot = output.output[bb].last_mut().unwrap();

                if !has_run_yet[bb] || *slot != new_value {
                    *slot = new_value;
                    transfer_reverse(&mut output.output[bb], &cfg.basic_blocks[bb].instructions, c);
                    has_run_yet[bb] = true;
                    for bb1 in cfg.basic_blocks[bb].predecessors.iter() {
                        if !in_worklist[*bb1] {
                            worklist.push_back(*bb1);
                            in_worklist[*bb1] = true;
                        }
                    }
                }
            }
        }
    }

    output
}

fn join_predecessors<D: DataflowState + Clone>(
    output: &DataflowOutput<D>,
    cfg: &CFG,
    bb: BBIndex,
    empty: &D,
    entry: &D,
) -> D {
    if cfg.basic_blocks[bb].is_entry {
        let mut res = entry.clone();
        for pred in cfg.basic_blocks[bb].predecessors.iter().cloned() {
            res.join(&output.output[pred][output.output[pred].len() - 1]);
        }
        res
    } else if cfg.basic_blocks[bb].predecessors.len() > 0 {
        let pred0 = cfg.basic_blocks[bb].predecessors[0];
        let mut res = output.output[pred0][output.output[pred0].len() - 1].clone();
        for pred in cfg.basic_blocks[bb].predecessors.iter().skip(1).cloned() {
            res.join(&output.output[pred][output.output[pred].len() - 1]);
        }
        res
    } else {
        empty.clone()
    }
}

fn join_successors<D: DataflowState + Clone>(
    output: &DataflowOutput<D>,
    cfg: &CFG,
    bb: BBIndex,
    empty: &D,
    exit: &D,
) -> D {
    if cfg.basic_blocks[bb].is_exit {
        let mut res = exit.clone();
        for succ in cfg.basic_blocks[bb].successors.iter().cloned() {
            res.join(&output.output[succ][0]);
        }
        res
    } else if cfg.basic_blocks[bb].successors.len() > 0 {
        let succ0 = cfg.basic_blocks[bb].successors[0];
        let mut res = output.output[succ0][0].clone();
        for succ in cfg.basic_blocks[bb].successors.iter().skip(1).cloned() {
            res.join(&output.output[succ][0]);
        }
        res
    } else {
        empty.clone()
    }
}

fn transfer_forward<D: DataflowState>(
    output: &mut Vec<D>,
    instructions: &[Instruction],
    c: &D::Const,
) {
    for i in 0..instructions.len() {
        output[i + 1] = output[i].transfer(&instructions[i], c);
    }
}

fn transfer_reverse<D: DataflowState>(
    output: &mut Vec<D>,
    instructions: &[Instruction],
    c: &D::Const,
) {
    for i in (0..instructions.len()).rev() {
        output[i] = output[i + 1].transfer(&instructions[i], c);
    }
}

////// CFG debugging

#[allow(dead_code)]
fn pretty_cfg(cfg: &CFG) -> String {
    format!(
        "Locals:\n{:}\nCFG:\n{:}",
        pretty_locals(&cfg.locals),
        pretty_basic_blocks(&cfg, |_, _| None),
    )
}

fn pretty_locals(locals: &LocalCollection) -> String {
    let mut v = vec![];
    for l in locals.locals.iter() {
        v.push(pretty_local(l, locals.datatypes));
    }
    v.join("\n")
}

fn pretty_local(l: &Local, datatypes: &HashMap<Path, Datatype>) -> String {
    format!(
        "{:}{:} : {:}",
        pretty_local_name(&l.name),
        pretty_tree(&l.tree, datatypes),
        crate::ast_util::typ_to_diagnostic_str(l.tree.typ())
    )
}

fn pretty_tree(pt: &PlaceTree, datatypes: &HashMap<Path, Datatype>) -> String {
    match pt {
        PlaceTree::Leaf(_) => "".to_string(),
        PlaceTree::MutRef(_, pt) => format!(".*{:}", pretty_tree(&pt, datatypes)),
        PlaceTree::Struct(_, dt, variants) => {
            let mut v = vec![];
            for (variant_idx, fields) in variants.iter().enumerate() {
                for (field_idx, field) in fields.iter().enumerate() {
                    match field {
                        Some(child) => {
                            let name = pretty_field_name(dt, variant_idx, field_idx, datatypes);
                            v.push(format!("{:}{:}", name, pretty_tree(child, datatypes)));
                        }
                        _ => {}
                    }
                }
            }
            format!(".{{{:}}}", v.join(", "))
        }
    }
}

#[allow(dead_code)]
fn pretty_basics_blocks_with_dataflow<D: std::fmt::Debug>(
    cfg: &CFG,
    output: &DataflowOutput<D>,
) -> String {
    pretty_basic_blocks(cfg, |i, j| Some(format!("{:?}", output.output[i][j])))
}

#[allow(dead_code)]
fn pretty_basics_blocks_with_dataflow2<D: std::fmt::Debug, E: std::fmt::Debug>(
    cfg: &CFG,
    output: &DataflowOutput<D>,
    output2: &DataflowOutput<E>,
) -> String {
    pretty_basic_blocks(cfg, |i, j| {
        Some(format!("{:?}; {:?}", output.output[i][j], output2.output[i][j]))
    })
}

fn pretty_basic_blocks(
    cfg: &CFG,
    intersperse_fn: impl Fn(BBIndex, usize) -> Option<String>,
) -> String {
    let mut v = vec![];
    for (i, bb) in cfg.basic_blocks.iter().enumerate() {
        v.push(format!("BasicBlock {:}:\n", i));
        v.push(format!("    is_entry = {:}\n", bb.is_entry));
        v.push(format!("    Predecessors: {:?}\n", &pretty_bb_list(&bb.predecessors)));
        v.push(format!(
            "    (always_add_resolution_at_start = {:?})\n",
            bb.always_add_resolution_at_start
        ));
        v.push("    ----\n".to_string());
        for (j, instr) in bb.instructions.iter().enumerate() {
            match intersperse_fn(i, j) {
                Some(s) => {
                    v.push(format!("    // {:}\n", s));
                }
                None => {}
            }
            v.push(format!("    {:}\n", pretty_instr(&cfg.locals, instr)));
        }
        match intersperse_fn(i, bb.instructions.len()) {
            Some(s) => {
                v.push(format!("    // {:}\n", s));
            }
            None => {}
        }
        v.push("    ----\n".to_string());
        v.push(format!("    Successors: {:?}\n", &pretty_bb_list(&bb.successors)));
        v.push(format!("    is_exit = {:}\n", bb.is_exit));
        v.push("\n".to_string());
    }
    v.join("")
}

fn pretty_bb_list(l: &Vec<BBIndex>) -> String {
    l.iter().map(|s| s.to_string()).collect::<Vec<_>>().join(", ")
}

fn pretty_instr(locals: &LocalCollection, instr: &Instruction) -> String {
    let (name, fp) = match &instr.kind {
        InstructionKind::MoveFrom(fp) => ("MoveFrom", fp),
        InstructionKind::Overwrite(fp) => ("Overwrite", fp),
        InstructionKind::Mutate(fp) => ("Mutate", fp),
        InstructionKind::DropFrom(fp) => ("DropFrom", fp),
    };
    format!("{:}({:})", name, pretty_flattened_place(locals, fp))
}

fn pretty_local_name(l: &LocalName) -> String {
    match l {
        LocalName::Named(i) => (*i.0).clone(),
        LocalName::Temporary(_ast_id, TempId(i)) => format!("Temp_{i}"),
    }
}

fn pretty_flattened_place(locals: &LocalCollection, fp: &FlattenedPlace) -> String {
    let mut s: String = pretty_local_name(&locals.locals[fp.local].name);
    let mut tree: &PlaceTree = &locals.locals[fp.local].tree;
    for proj in fp.projections.iter() {
        let (x, t) = match proj {
            Projection::DerefMut => {
                let inner_tree: &PlaceTree = match tree {
                    PlaceTree::MutRef(_, t) => &**t,
                    _ => unreachable!(),
                };
                (".*".to_string(), inner_tree)
            }
            Projection::StructField((variant_idx, field_idx)) => {
                let (dt, inner_tree) = match tree {
                    PlaceTree::Struct(_, dt, trees) => (dt, &trees[*variant_idx][*field_idx]),
                    _ => unreachable!(),
                };
                let x = pretty_field_name(dt, *variant_idx, *field_idx, &locals.datatypes);
                let x = format!(".{:}", x);
                (x, inner_tree.as_ref().unwrap())
            }
        };
        s += &x;
        tree = t;
    }
    s
}

fn pretty_field_name(
    dt: &Dt,
    variant_idx: usize,
    field_idx: usize,
    datatypes: &HashMap<Path, Datatype>,
) -> String {
    match dt {
        Dt::Tuple(_) => {
            format!("{:}", field_idx)
        }
        Dt::Path(p) => {
            let datatype = &datatypes[p];
            if datatype.x.variants.len() > 1 {
                format!(
                    "{:}_{:}",
                    datatype.x.variants[variant_idx].name,
                    datatype.x.variants[variant_idx].fields[field_idx].name
                )
            } else {
                format!("{:}", datatype.x.variants[variant_idx].fields[field_idx].name)
            }
        }
    }
}

////// Analysis: Initialization

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct InitializationPossibilities {
    /// Is it possible to reach the given program point with the given place
    /// not initialized?
    /// (Using the definition of "conditionally initialized" described above)
    can_be_uninit: bool,
}

impl DataflowState for InitializationPossibilities {
    type Const = FlattenedPlace;

    fn join(&mut self, b: &Self) {
        *self =
            InitializationPossibilities { can_be_uninit: self.can_be_uninit || b.can_be_uninit };
    }

    // forward transfer
    fn transfer(&self, instr: &Instruction, place: &FlattenedPlace) -> Self {
        match &instr.kind {
            InstructionKind::MoveFrom(sp) => {
                if sp.contains(place) {
                    InitializationPossibilities { can_be_uninit: true }
                } else {
                    *self
                }
            }
            InstructionKind::Overwrite(sp) => {
                if sp.contains(place) {
                    InitializationPossibilities { can_be_uninit: false }
                } else {
                    *self
                }
            }
            InstructionKind::Mutate(_sp) => *self,
            InstructionKind::DropFrom(sp) => {
                if sp.contains(place) {
                    InitializationPossibilities { can_be_uninit: true }
                } else {
                    *self
                }
            }
        }
    }
}

impl InitializationPossibilities {
    fn empty() -> Self {
        InitializationPossibilities { can_be_uninit: false }
    }

    fn entry() -> Self {
        InitializationPossibilities { can_be_uninit: true }
    }
}

////// Analysis: Resolve

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct ResolveSafety {
    can_resolve: bool,
}

impl DataflowState for ResolveSafety {
    type Const = FlattenedPlace;

    fn join(&mut self, b: &Self) {
        *self = ResolveSafety { can_resolve: self.can_resolve && b.can_resolve }
    }

    // backward transfer
    fn transfer(&self, instr: &Instruction, place: &FlattenedPlace) -> Self {
        match &instr.kind {
            InstructionKind::MoveFrom(sp) | InstructionKind::Mutate(sp) => {
                if sp.intersects(place) {
                    ResolveSafety { can_resolve: false }
                } else {
                    *self
                }
            }
            InstructionKind::Overwrite(sp) | InstructionKind::DropFrom(sp) => {
                if sp.contains_and_not_separated_by_deref(place) {
                    ResolveSafety { can_resolve: true }
                } else if sp.intersects(place) {
                    ResolveSafety { can_resolve: false }
                } else {
                    *self
                }
            }
        }
    }
}

impl ResolveSafety {
    fn empty() -> Self {
        ResolveSafety { can_resolve: true }
    }

    fn exit(place: &FlattenedPlace) -> Self {
        ResolveSafety { can_resolve: !place.has_deref() }
    }
}

////// Use the results of the analysis to determine where resolutions should go

/// Determine the resolutions to be inserted. Doesn't account for scopes.
fn get_resolutions(cfg: &CFG) -> Vec<ResolutionToInsert> {
    // A place behind an initialized mutable reference can't be uninitialized,
    // so we only check places that aren't behind mutable references.
    let initialization_places = cfg.locals.places_skip_insides_of_mut_refs();
    let initialization_analyses: Vec<DataflowOutput<InitializationPossibilities>> =
        initialization_places
            .iter()
            .map(|place| {
                do_dataflow::<InitializationPossibilities>(
                    cfg,
                    InitializationPossibilities::empty(),
                    InitializationPossibilities::entry(),
                    place,
                    Direction::Forward,
                )
            })
            .collect();

    // A place typed as a mutable reference needs to be checked separately from
    // the places behind that mutable reference (see the explanation above).
    let resolve_places = cfg.locals.places_including_insides_of_mut_refs();
    let resolve_analyses: Vec<DataflowOutput<ResolveSafety>> = resolve_places
        .iter()
        .map(|place| {
            do_dataflow::<ResolveSafety>(
                cfg,
                ResolveSafety::empty(),
                ResolveSafety::exit(place),
                place,
                Direction::Reverse,
            )
        })
        .collect();

    let mut output = vec![];

    let mut i_idx = 0;
    for r_idx in 0..resolve_places.len() {
        while !initialization_places[i_idx].contains(&resolve_places[r_idx]) {
            i_idx += 1;
        }

        //println!("{:}\n", pretty_flattened_place(&cfg.locals, &resolve_places[r_idx]));
        //println!("{:}\n", pretty_basics_blocks_with_dataflow2(&cfg, &resolve_analyses[r_idx], &initialization_analyses[i_idx]));

        // TODO(new_mut_ref): filter for "interesting" types, i.e., those containing a &mut ref

        get_resolutions_for_place(
            cfg,
            &resolve_places[r_idx],
            &initialization_analyses[i_idx],
            &resolve_analyses[r_idx],
            &mut output,
        );
    }

    output
}

fn get_resolutions_for_place(
    cfg: &CFG,
    place: &FlattenedPlace,
    initialization_analysis: &DataflowOutput<InitializationPossibilities>,
    resolve_analysis: &DataflowOutput<ResolveSafety>,
    output: &mut Vec<ResolutionToInsert>,
) {
    let is_temp = cfg.locals.locals[place.local].name.is_temp();
    for bb in 0..cfg.basic_blocks.len() {
        for i in 0..cfg.basic_blocks[bb].instructions.len() + 1 {
            // Is it safe to resolve here?
            let can_assume_has_resolved = resolve_analysis.output[bb][i].can_resolve
                && !initialization_analysis.output[bb][i].can_be_uninit;
            if can_assume_has_resolved {
                // If so, is it *useful* to resolve here?
                let should_assume_has_resolved =
                    // At beginning of function, or beginning or end of a loop,
                    // Always add resolutions for non-temps
                    (i == 0 && cfg.basic_blocks[bb].always_add_resolution_at_start && !is_temp)
                    // If there's any predecessor block where this value can't be resolved
                    || (i == 0
                        && cfg.basic_blocks[bb].predecessors.iter().any(|pred| {
                            !resolve_analysis.output[*pred].last().unwrap().can_resolve
                        }))
                    // If this couldn't have been resolved at the previous instruction
                    || (i > 0 && !resolve_analysis.output[bb][i - 1].can_resolve)
                    // If the place had a different value at the previous instruction
                    || (i > 0 && place.value_may_change(&cfg.basic_blocks[bb].instructions[i - 1]));
                if should_assume_has_resolved {
                    output.push(ResolutionToInsert {
                        place: place.clone(),
                        position: if i == 0 {
                            cfg.basic_blocks[bb].position_of_start
                        } else {
                            cfg.basic_blocks[bb].instructions[i - 1].post_instruction_position
                        },
                    });
                }
            }
        }
    }
}

////// Modify the AST Expr with the new resolutions

/// Returns the given expression with AssumeResolved expressions inserted.
fn apply_resolutions(
    cfg: &CFG,
    params: &Params,
    body: &Expr,
    resolutions: Vec<ResolutionToInsert>,
    assigns_to_resolve: Vec<AstId>,
) -> Expr {
    // All the resolutions that apply to PlaceX::Temporary nodes
    let mut temp_map = HashMap::<AstId, (Vec<FlattenedPlace>, bool)>::new();

    // All the resolutions that apply to Expr and Stmt nodes
    let mut id_map = HashMap::<
        AstId,
        (
            Vec<FlattenedPlace>,
            Vec<FlattenedPlace>,
            Vec<FlattenedPlace>,
            Vec<FlattenedPlace>,
            Vec<FlattenedPlace>,
            bool,
            bool,
        ),
    >::new();

    for r in resolutions.into_iter() {
        // For any temp that has an Assume(HasResolved(...)) about it, we need to expand that temp
        if let Some(temp_ast_id) = r.is_for_temp(cfg) {
            temp_map.entry(temp_ast_id).or_insert_with_key(|_| (vec![], false));
        }

        let ast_id = match r.position {
            AstPosition::Before(ast_id) => ast_id,
            AstPosition::After(ast_id) => ast_id,
            AstPosition::AfterArguments(ast_id) => ast_id,
            AstPosition::OnUnwind(_) => {
                // It might be necessary to do something here for more
                // advanced unwind-related stuff?
                continue;
            }
            AstPosition::AfterBool(ast_id, _b) => ast_id,
            AstPosition::AfterTempAssignment(ast_id) => {
                temp_map.entry(ast_id).or_insert_with_key(|_| (vec![], false)).0.push(r.place);
                continue;
            }
        };

        let entry = id_map
            .entry(ast_id)
            .or_insert_with_key(|_| (vec![], vec![], vec![], vec![], vec![], false, false));

        match r.position {
            AstPosition::Before(_ast_id) => {
                entry.0.push(r.place);
            }
            AstPosition::After(_ast_id) => {
                entry.1.push(r.place);
            }
            AstPosition::AfterArguments(_ast_id) => {
                entry.2.push(r.place);
            }
            AstPosition::OnUnwind(_) => unreachable!(),
            AstPosition::AfterTempAssignment(_) => unreachable!(),
            AstPosition::AfterBool(_ast_id, false) => {
                entry.3.push(r.place);
            }
            AstPosition::AfterBool(_ast_id, true) => {
                entry.4.push(r.place);
            }
        };
    }

    for ast_id in assigns_to_resolve.into_iter() {
        let entry = id_map
            .entry(ast_id)
            .or_insert_with_key(|_| (vec![], vec![], vec![], vec![], vec![], false, false));
        assert!(!entry.5);
        entry.5 = true;
    }

    let mut maps = (id_map, temp_map);

    let mut scope_map = VisitorScopeMap::new();
    scope_map.push_scope(true);
    for param in params.iter() {
        scope_map
            .insert(
                param.x.name.clone(),
                crate::ast_visitor::ScopeEntry::new(&param.x.typ, false, true),
            )
            .unwrap();
    }

    let result = crate::ast_visitor::map_expr_visitor_env(
        body,
        &mut scope_map,
        &mut maps,
        &|(id_map, _), scope_map, expr: &Expr| {
            if let Some((befores, afters, after_args, after_f, after_t, assn, seen_yet)) =
                id_map.get_mut(&expr.span.id)
            {
                if *seen_yet {
                    panic!("Verus internal error: duplicate AstId");
                }
                *seen_yet = true;

                let befores_exprs = filter_and_make_assumes(cfg, &expr.span, scope_map, befores);
                let afters_exprs = filter_and_make_assumes(cfg, &expr.span, scope_map, afters);
                let after_args_exprs =
                    filter_and_make_assumes(cfg, &expr.span, scope_map, after_args);
                let after_f_exprs = filter_and_make_assumes(cfg, &expr.span, scope_map, after_f);
                let after_t_exprs = filter_and_make_assumes(cfg, &expr.span, scope_map, after_t);

                let mut e = expr.clone();
                if *assn {
                    e = apply_resolution_to_assignment(&e);
                }

                let e = apply_after_args_exprs(e, after_args_exprs);
                let e = apply_before_exprs(e, befores_exprs);
                let e = apply_after_exprs(e, afters_exprs);
                let e = apply_after_bool_exprs(e, after_f_exprs, after_t_exprs);

                Ok(e)
            } else {
                Ok(expr.clone())
            }
        },
        &|(id_map, _), scope_map, stmt| {
            if let Some((befores, afters, after_args, after_f, after_t, assn, seen_yet)) =
                id_map.get_mut(&stmt.span.id)
            {
                if *seen_yet {
                    panic!("Verus internal error: duplicate AstId");
                }
                if after_f.len() > 0 || after_t.len() > 0 {
                    panic!("Verus internal error: AfterBool should only apply to exprs");
                }
                if *assn {
                    panic!("Verus internal error: assignment should only apply to exprs");
                }
                assert!(after_args.len() == 0);
                *seen_yet = true;

                let befores_exprs = filter_and_make_assumes(cfg, &stmt.span, scope_map, befores);

                scope_map.push_scope(true);
                match &stmt.x {
                    StmtX::Expr(_) => {}
                    StmtX::Decl { pattern, mode: _, init, els: _ } => {
                        use crate::ast_visitor::Scoper;
                        scope_map.insert_pattern_bindings(pattern, init.is_some());
                    }
                }
                let afters_exprs = filter_and_make_assumes(cfg, &stmt.span, scope_map, afters);
                scope_map.pop_scope();

                let mut v = exprs_to_stmts(befores_exprs);
                v.push(stmt.clone());
                v.append(&mut exprs_to_stmts(afters_exprs));

                Ok(v)
            } else {
                Ok(vec![stmt.clone()])
            }
        },
        &|_, t| Ok(t.clone()),
        &|(_, temp_map), scope_map, p| {
            if matches!(&p.x, PlaceX::Temporary(_)) {
                if let Some((afters, seen_yet)) = temp_map.get_mut(&p.span.id) {
                    if *seen_yet {
                        panic!("Verus internal error: duplicate AstId");
                    }
                    *seen_yet = true;
                    let afters_exprs = filter_and_make_assumes(cfg, &p.span, scope_map, afters);
                    Ok(apply_temp_simplification(cfg, p, afters_exprs))
                } else {
                    Ok(p.clone())
                }
            } else {
                Ok(p.clone())
            }
        },
    )
    .unwrap();

    let (id_map, temp_map) = maps;

    for (_, (_, _, _, _, _, _, found)) in id_map.iter() {
        if !*found {
            panic!("resolution_inference: bad run for apply_resolutions");
        }
    }

    for (_, (_, found)) in temp_map.iter() {
        if !*found {
            panic!("resolution_inference: bad run for apply_resolutions");
        }
    }

    if temp_map.len() > 0 { add_decls_for_temps(cfg, &temp_map, &result) } else { result }
}

impl ResolutionToInsert {
    fn is_for_temp(&self, cfg: &CFG) -> Option<AstId> {
        match &cfg.locals.locals[self.place.local].name {
            LocalName::Temporary(ast_id, _temp_id) => Some(*ast_id),
            LocalName::Named(_) => None,
        }
    }
}

/// Filter for the resolutions that are actually in scope and make the AssumeResolved expressions.
fn filter_and_make_assumes(
    cfg: &CFG,
    span: &Span,
    scope_map: &VisitorScopeMap,
    v: &Vec<FlattenedPlace>,
) -> Vec<Expr> {
    v.iter()
        .filter_map(|fp| {
            let name = &cfg.locals.locals[fp.local].name;
            let keep = match name {
                LocalName::Named(name) => scope_map.contains_key(name),
                LocalName::Temporary(..) => {
                    // We can't use the scope_map to check if the temporary is in scope
                    // Instead, we make sure the algorithm doesn't try to insert a resolution
                    // for a temp-place outside of the temp scope.
                    true
                }
            };
            if keep { Some(make_assume(cfg, span, fp)) } else { None }
        })
        .collect()
}

/// Returns:
/// assume(all IsVariant conditions needed for Place to be valid ==> HasResolved(Place))
fn make_assume(cfg: &CFG, span: &Span, fp: &FlattenedPlace) -> Expr {
    let ast_place = cfg.locals.to_ast_place(span, fp);
    let e = crate::ast_util::place_to_spec_expr(&ast_place);
    // TODO(new_mut_ref): are we sure that ast_place.typ is correct including decoration?
    let has_resolvedx = ExprX::UnaryOpr(UnaryOpr::HasResolved(ast_place.typ.clone()), e);
    let has_resolved = SpannedTyped::new(&ast_place.span, &bool_typ(), has_resolvedx);
    let conditional_has_resolved =
        condition_on_enum_variants(&has_resolved, &ast_place, &cfg.locals.datatypes);
    crate::ast_util::mk_assume(&ast_place.span, &conditional_has_resolved)
}

/// Given an `AssignToPlace`, sets the `resolve` field to true
/// (Equivalently, adds an `assume(has_resolved(...))` for the value being overwritten
fn apply_resolution_to_assignment(e: &Expr) -> Expr {
    match &e.x {
        ExprX::AssignToPlace { place, rhs, op, resolve } => {
            // TODO(new_mut_ref): are we sure that ast_place.typ is correct including decoration?
            let typ = place.typ.clone();

            assert!(resolve.is_none());
            e.new_x(ExprX::AssignToPlace {
                place: place.clone(),
                rhs: rhs.clone(),
                op: *op,
                resolve: Some(typ),
            })
        }
        _ => {
            panic!("apply_resolution_to_assignment expects AssignToPlace node");
        }
    }
}

/// Returns:
/// `all IsVariant conditions needed for Place to be valid ==> bool_expr`
fn condition_on_enum_variants(
    bool_expr: &Expr,
    place: &Place,
    datatypes: &HashMap<Path, Datatype>,
) -> Expr {
    match &place.x {
        PlaceX::Local(_l) => bool_expr.clone(),
        PlaceX::DerefMut(p) => condition_on_enum_variants(bool_expr, p, datatypes),
        PlaceX::Field(field_opr, p) => {
            let is_irref = match &field_opr.datatype {
                Dt::Tuple(_) => true,
                Dt::Path(path) => datatypes[path].x.variants.len() == 1,
            };
            let conditioned_bool_expr = if is_irref {
                bool_expr
            } else {
                let e0 = crate::ast_util::place_to_spec_expr(p);
                let is_variantx = ExprX::UnaryOpr(
                    UnaryOpr::IsVariant {
                        datatype: field_opr.datatype.clone(),
                        variant: field_opr.variant.clone(),
                    },
                    e0,
                );
                let is_variant = SpannedTyped::new(&place.span, &bool_typ(), is_variantx);
                &crate::ast_util::mk_implies(&place.span, &is_variant, bool_expr)
            };
            condition_on_enum_variants(conditioned_bool_expr, p, datatypes)
        }
        _ => {
            // We only have to handle places produced by `to_ast_place`
            panic!("condition_on_enum_variants got unexpected Place kind")
        }
    }
}

fn exprs_to_stmts(exprs: Vec<Expr>) -> Vec<Stmt> {
    exprs.into_iter().map(|e| Spanned::new(e.span.clone(), StmtX::Expr(e.clone()))).collect()
}

fn apply_before_exprs(expr: Expr, before_exprs: Vec<Expr>) -> Expr {
    if before_exprs.len() == 0 {
        return expr;
    }
    let mut stmts = vec![];
    for e in before_exprs.into_iter() {
        stmts.push(Spanned::new(e.span.clone(), StmtX::Expr(e)));
    }
    SpannedTyped::new(&expr.span, &expr.typ, ExprX::Block(Arc::new(stmts), Some(expr.clone())))
}

fn apply_after_exprs(expr: Expr, after_exprs: Vec<Expr>) -> Expr {
    if after_exprs.len() == 0 {
        return expr;
    }
    let e = if after_exprs.len() == 1 {
        after_exprs[0].clone()
    } else {
        let mut stmts = vec![];
        for e in after_exprs.into_iter() {
            stmts.push(Spanned::new(e.span.clone(), StmtX::Expr(e)));
        }
        SpannedTyped::new(&expr.span, &unit_typ(), ExprX::Block(Arc::new(stmts), None))
    };
    SpannedTyped::new(
        &expr.span,
        &expr.typ,
        ExprX::UseLeftWhereRightCanHaveNoAssignments(expr.clone(), e),
    )
}

fn apply_after_bool_exprs(expr: Expr, after_f: Vec<Expr>, after_t: Vec<Expr>) -> Expr {
    if after_f.len() == 0 && after_t.len() == 0 {
        return expr;
    }

    // Turn b into:
    // if b { t_stmts; true } else { f_stmts; false }
    // where t_stmts are the statements to run on true, and
    // f_stmts are the statements to run on false

    let mut f_stmts = vec![];
    for e in after_f.into_iter() {
        f_stmts.push(Spanned::new(e.span.clone(), StmtX::Expr(e)));
    }

    let mut t_stmts = vec![];
    for e in after_t.into_iter() {
        t_stmts.push(Spanned::new(e.span.clone(), StmtX::Expr(e)));
    }

    SpannedTyped::new(
        &expr.span,
        &bool_typ(),
        ExprX::If(
            expr.clone(),
            SpannedTyped::new(
                &expr.span,
                &unit_typ(),
                ExprX::Block(Arc::new(t_stmts), Some(mk_bool(&expr.span, true))),
            ),
            Some(SpannedTyped::new(
                &expr.span,
                &unit_typ(),
                ExprX::Block(Arc::new(f_stmts), Some(mk_bool(&expr.span, false))),
            )),
        ),
    )
}

fn apply_after_args_exprs(expr: Expr, exprs: Vec<Expr>) -> Expr {
    if exprs.len() == 0 {
        return expr;
    }
    match &expr.x {
        ExprX::Call(ct, args, None) => {
            let mut stmts = vec![];
            for e in exprs.into_iter() {
                stmts.push(Spanned::new(e.span.clone(), StmtX::Expr(e)));
            }
            let block =
                SpannedTyped::new(&expr.span, &unit_typ(), ExprX::Block(Arc::new(stmts), None));
            SpannedTyped::new(
                &expr.span,
                &expr.typ,
                ExprX::Call(ct.clone(), args.clone(), Some(block)),
            )
        }
        _ => {
            panic!("apply_after_args_exprs expected ExprX::Call");
        }
    }
}

fn apply_temp_simplification(cfg: &CFG, place: &Place, exprs: Vec<Expr>) -> Place {
    // Note that exprs might be empty here; we still need to do the transformation if there
    // is some Assume(HasResolved) for this temporary being inserted at a different location.

    let PlaceX::Temporary(expr) = &place.x else {
        panic!("Verus Internal Error: apply_temp_simplification expected Temporary");
    };

    // Translate:
    // Temporary(expr)   -->   WithExpr({ tmp = expr; other_stmts; }, Local(tmp))
    // Use an Assign node (we add the Decl in `add_decls_for_temps`)

    let ast_id = place.span.id;
    let temp_id = cfg.locals.ast_id_to_temp_id[&ast_id];
    let x = LocalName::Temporary(ast_id, temp_id).to_var_ident();

    let tmp_local_place = SpannedTyped::new(&place.span, &place.typ, PlaceX::Local(x.clone()));

    let assign_expr = SpannedTyped::new(
        &place.span,
        &unit_typ(),
        ExprX::AssignToPlace {
            place: tmp_local_place.clone(),
            rhs: expr.clone(),
            op: None,
            resolve: None,
        },
    );

    let mut stmts = vec![Spanned::new(place.span.clone(), StmtX::Expr(assign_expr))];
    for e in exprs.into_iter() {
        stmts.push(Spanned::new(e.span.clone(), StmtX::Expr(e)));
    }

    let block_expr =
        SpannedTyped::new(&place.span, &unit_typ(), ExprX::Block(Arc::new(stmts), None));

    SpannedTyped::new(&place.span, &place.typ, PlaceX::WithExpr(block_expr, tmp_local_place))
}

fn add_decls_for_temps(
    cfg: &CFG,
    temp_map: &HashMap<AstId, (Vec<FlattenedPlace>, bool)>,
    expr: &Expr,
) -> Expr {
    // Declare all temp vars at the beginning of the function body
    // (There doesn't seem to be any point in minimizing the scope of such variables,
    // but maybe we should restrict them to individual loops?)
    // We mark them all mut, though in principle, some of them don't need to be mut,
    // e.g., the ones that are only here so we can call `assume(HasResolved(...))`.
    let mut stmts = vec![];
    for local in cfg.locals.locals.iter() {
        if let LocalName::Temporary(ast_id, temp_id) = &local.name {
            if temp_map.contains_key(ast_id) {
                let x = LocalName::Temporary(*ast_id, *temp_id).to_var_ident();
                let typ = local.tree.typ();
                stmts.push(Spanned::new(
                    expr.span.clone(),
                    StmtX::Decl {
                        pattern: PatternX::simple_var(x, true, &expr.span, typ),
                        mode: Some(Mode::Exec), // doesn't matter
                        init: None,
                        els: None,
                    },
                ));
            }
        }
    }
    SpannedTyped::new(&expr.span, &expr.typ, ExprX::Block(Arc::new(stmts), Some(expr.clone())))
}
