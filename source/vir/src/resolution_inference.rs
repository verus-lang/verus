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

*/

use crate::ast::{
    BinaryOp, ByRef, Datatype, Dt, Expr, ExprX, FieldOpr, Fun, Function, Mode, Param, Params, Path,
    Pattern, PatternBinding, PatternX, Place, PlaceX, ReadKind, SpannedTyped, Stmt, StmtX, Typ,
    TypDecoration, TypX, UnfinalizedReadKind, VarIdent,
};
use crate::ast_visitor::VisitorScopeMap;
use crate::def::Spanned;
use crate::messages::{AstId, Span};
use crate::modes::ReadKindFinals;
use crate::sst_util::subst_typ_for_datatype;
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
) -> Expr {
    let cfg = new_cfg(params, body, read_kind_finals, datatypes, functions, var_modes);
    //println!("{:}", pretty_cfg(&cfg));
    let resolutions = get_resolutions(&cfg);
    apply_resolutions(&cfg, body, resolutions)
}

/// Represents the tree structure of "places" under consideration.
#[derive(Debug)]
enum PlaceTree {
    Leaf(Typ),
    Struct(Typ, Dt, Vec<PlaceTree>),
    MutRef(Typ, Box<PlaceTree>),
}

/// A local var in the function, represents the base of any place.
/// The PlaceTree is expanded to represent the total amount of detail we need about this place,
/// which depends on how it is manipulated by the program.
///
/// For example, if we have a local variable `x: (T, T, T)`, and the programs assigns to `x.0`,
/// we would expand the tree to include [x.0, x.1, x.2]. If the program also assigns to `x.0.0`,
/// we expand it further, [[x.0.0, x.0.1] x.1, x.2]
#[derive(Debug)]
struct Local {
    name: VarIdent,
    is_param: bool,
    tree: PlaceTree,
}

/// Collection of all the locals in the program.
struct LocalCollection<'a> {
    locals: Vec<Local>,
    ident_to_idx: HashMap<VarIdent, usize>,
    datatypes: &'a HashMap<Path, Datatype>,
    var_modes: &'a HashMap<VarIdent, Mode>,
}

/// A projection that maps a place to a subplace
#[derive(Clone, Debug)]
pub(crate) enum ProjectionTyped {
    StructField(FieldOpr, Typ),
    DerefMut(Typ),
}

/// "Flattened" form of the vir::ast::Place type.
/// Only represents places based on locals, not temporaries.
#[derive(Clone)]
struct FlattenedPlaceTyped {
    pub local: VarIdent,
    pub typ: Typ,
    pub projections: Vec<ProjectionTyped>,
}

/// Untyped version of the ProjectionTyped. The indices are used to walk the PlaceTree.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Projection {
    StructField(usize),
    DerefMut,
}

#[derive(Clone, Debug)]
struct FlattenedPlace {
    local: usize,
    projections: Vec<Projection>,
}

/// Represents a position in the vir::ast::Expr where an AssumeResolved can be inserted.
#[derive(Clone, Copy, Debug)]
enum AstPosition {
    Before(AstId),
    After(AstId),
    AfterArguments(AstId),
    OnUnwind(#[allow(dead_code)] AstId),
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
    loops: Vec<LoopEntry>,
    locals: LocalCollection<'a>,
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

/// Compute the CFG for the given expression.
fn new_cfg<'a>(
    params: &Params,
    body: &Expr,
    read_kind_finals: &'a ReadKindFinals,
    datatypes: &'a HashMap<Path, Datatype>,
    functions: &'a HashMap<Fun, Function>,
    var_modes: &'a HashMap<VarIdent, Mode>,
) -> CFG<'a> {
    let mut builder = Builder {
        basic_blocks: vec![],
        loops: vec![],
        locals: LocalCollection {
            locals: vec![],
            ident_to_idx: HashMap::new(),
            datatypes,
            var_modes,
        },
        read_kind_finals,
        functions,
    };
    let start_bb = builder.new_bb(AstPosition::Before(body.span.id), true);

    for param in params.iter() {
        builder.locals.add_param(param);
    }
    let end_bb = builder.build(body, start_bb);
    builder.optionally_exit(end_bb);

    builder.compute_predecessors();

    CFG { basic_blocks: builder.basic_blocks, locals: builder.locals }
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

    fn push_instruction(
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
            self.push_instruction(
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
            | ExprX::Nondeterministic
            | ExprX::AssumeResolved(..) => Ok(bb),
            ExprX::Call(call_target, es, post_args) => {
                assert!(post_args.is_none());

                // Can skip the expression in CallTarget because
                // it can only be for FnSpec which is always a pure spec expression

                let mut two_phase_delayed_mutations = vec![];

                for e in es.iter() {
                    match &e.x {
                        ExprX::TwoPhaseBorrowMut(p) => {
                            let (p, bb1) = self.build_place(p, bb)?;
                            bb = bb1;
                            if let Some(p) = p {
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
                    self.push_instruction(
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
            ExprX::Ctor(_dt, _id, binders, opt_place) => {
                let mut two_phase_delayed_mutations = vec![];

                // TODO(new_mut_ref): tests for two-phase borrows

                for b in binders.iter() {
                    let e = &b.a;
                    match &e.x {
                        ExprX::TwoPhaseBorrowMut(p) => {
                            let (p, bb1) = self.build_place(p, bb)?;
                            bb = bb1;
                            if let Some(p) = p {
                                two_phase_delayed_mutations.push(p);
                            }
                        }
                        _ => {
                            bb = self.build(e, bb)?;
                        }
                    }
                }

                for p in two_phase_delayed_mutations.into_iter() {
                    // Convenentially, we can just put these mutations after the Ctor call itself
                    // since the Ctor is a trivial operation, i.e., we don't need a special
                    // place for the "post_args" like we do with calls.
                    self.push_instruction(
                        bb,
                        AstPosition::After(span_id),
                        InstructionKind::Mutate(p),
                    );
                }

                if opt_place.is_some() {
                    todo!()
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
            ExprX::NonSpecClosure { .. } => {
                todo!()
            }
            ExprX::ArrayLiteral(es) => {
                for e in es.iter() {
                    bb = self.build(e, bb)?;
                }
                Ok(bb)
            }
            ExprX::Match(place, arms) => {
                let (fpt, bb) = self.build_place_typed(place, bb)?;

                let mut arm_bb_ends = vec![];
                for arm in arms.iter() {
                    // TODO(new_mut_ref) handle guards

                    let arm_bb = self.new_bb(AstPosition::Before(arm.x.body.span.id), false);
                    self.basic_blocks[bb].successors.push(arm_bb);

                    if let Some(fpt) = fpt.clone() {
                        self.append_instructions_for_pattern_moves_mutations(
                            &arm.x.pattern,
                            &fpt,
                            arm_bb,
                            AstPosition::Before(arm.x.body.span.id),
                        );
                    }

                    for bound_var in pattern_all_bound_vars_with_ownership(
                        &arm.x.pattern,
                        &self.locals.var_modes,
                    )
                    .into_iter()
                    {
                        let fpt = FlattenedPlaceTyped {
                            local: bound_var.name,
                            typ: bound_var.typ,
                            projections: vec![],
                        };
                        let fp = self.locals.add_place(fpt, false);
                        self.push_instruction(
                            bb,
                            AstPosition::Before(arm.x.body.span.id),
                            InstructionKind::Overwrite(fp),
                        );
                    }

                    let arm_bb_end = self.build(&arm.x.body, arm_bb);
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
                is_for_loop,
                label,
                cond,
                body,
                invs: _,
                decrease: _,
            } => {
                if cond.is_some() {
                    todo!() // TODO(new_mut_ref)
                }
                if *is_for_loop {
                    todo!() // TODO(new_mut_ref)
                }

                let body_bb = self.new_bb(AstPosition::Before(body.span.id), true);
                let post_bb = self.new_bb(AstPosition::After(expr.span.id), true);

                let drops = self.loop_drops(&expr);
                self.loops.push(LoopEntry {
                    label: label.clone(),
                    break_bb: post_bb,
                    continue_bb: body_bb,
                    drops: Rc::new(drops),
                });

                self.basic_blocks[bb].successors.push(body_bb);

                let end_bb = self.build(body, body_bb);

                let loop_entry = self.loops.pop().unwrap();

                match end_bb {
                    Err(()) => {}
                    Ok(end_bb) => {
                        self.push_drops(
                            end_bb,
                            AstPosition::After(body.span.id),
                            &loop_entry.drops,
                        );
                        self.basic_blocks[end_bb].successors.push(body_bb);
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
            ExprX::AssignToPlace { place, rhs, op: None } => {
                let (p, bb) = self.build_place(place, bb)?;
                let bb = self.build(rhs, bb)?;
                if let Some(p) = p {
                    self.push_instruction(
                        bb,
                        AstPosition::After(span_id),
                        InstructionKind::Overwrite(p),
                    );
                }
                Ok(bb)
            }
            ExprX::AssignToPlace { place: _, rhs: _, op: Some(_) } => {
                todo!()
            }
            ExprX::TwoPhaseBorrowMut(_p) => {
                // These must be handled contextually, so the recursion should skip over
                // these nodes.
                panic!("Verus Internal Error: unhandled TwoPhaseBorrowMut node");
            }
            ExprX::BorrowMut(p) => {
                let (p, bb) = self.build_place(p, bb)?;
                if let Some(p) = p {
                    self.push_instruction(
                        bb,
                        AstPosition::After(span_id),
                        InstructionKind::Mutate(p),
                    );
                }
                Ok(bb)
            }
            ExprX::ReadPlace(p, unfinal_read_kind) => {
                if self.is_move(unfinal_read_kind) {
                    let (p, bb) = self.build_place(p, bb)?;
                    if let Some(p) = p {
                        self.push_instruction(
                            bb,
                            AstPosition::After(span_id),
                            InstructionKind::MoveFrom(p),
                        );
                    }
                    Ok(bb)
                } else {
                    let (_p, bb) = self.build_place_typed(p, bb)?;
                    Ok(bb)
                }
            }
            ExprX::Block(stmts, e_opt) => {
                for s in stmts.iter() {
                    bb = self.build_stmt(s, bb)?;
                }
                if let Some(e) = e_opt {
                    bb = self.build(e, bb)?;
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
            StmtX::Decl { pattern: _, mode: _, init: None, els: None } => {
                // do nothing
                Ok(bb)
            }
            StmtX::Decl { pattern, mode: _, init: Some(init), els: None } => {
                let (fp, bb) = self.build_place_typed(init, bb)?;
                if let Some(fp) = fp {
                    self.append_instructions_for_pattern_moves_mutations(
                        pattern,
                        &fp,
                        bb,
                        AstPosition::After(stmt.span.id),
                    );
                }
                for bound_var in
                    pattern_all_bound_vars_with_ownership(pattern, &self.locals.var_modes)
                        .into_iter()
                {
                    let fpt = FlattenedPlaceTyped {
                        local: bound_var.name,
                        typ: bound_var.typ,
                        projections: vec![],
                    };
                    let fp = self.locals.add_place(fpt, false);
                    self.push_instruction(
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

    fn build_place(
        &mut self,
        place: &Place,
        bb: BBIndex,
    ) -> Result<(Option<FlattenedPlace>, BBIndex), ()> {
        let r = self.build_place_typed(place, bb);
        match r {
            Ok((Some(fpi), bb)) => {
                let sp = self.locals.add_place(fpi, false);
                Ok((Some(sp), bb))
            }
            Ok((None, bb)) => Ok((None, bb)),
            Err(e) => Err(e),
        }
    }

    /// Returns Err(()) if the place expression never returns (can happen if it's a temporary)
    /// Ok(None) means it's a temporary
    /// Ok(Some(_)) means it's a place based on a local
    fn build_place_typed(
        &mut self,
        place: &Place,
        bb: BBIndex,
    ) -> Result<(Option<FlattenedPlaceTyped>, BBIndex), ()> {
        match &place.x {
            PlaceX::Field(field_opr, p) => match self.build_place_typed(p, bb) {
                Ok((Some(mut fpt), bb)) => {
                    fpt.projections
                        .push(ProjectionTyped::StructField(field_opr.clone(), place.typ.clone()));
                    Ok((Some(fpt), bb))
                }
                Ok((None, bb)) => Ok((None, bb)),
                Err(()) => Err(()),
            },
            PlaceX::DerefMut(p) => match self.build_place_typed(p, bb) {
                Ok((Some(mut fpt), bb)) => {
                    fpt.projections.push(ProjectionTyped::DerefMut(place.typ.clone()));
                    Ok((Some(fpt), bb))
                }
                Ok((None, bb)) => Ok((None, bb)),
                Err(()) => Err(()),
            },
            PlaceX::Local(var) => {
                let fpt = FlattenedPlaceTyped {
                    local: var.clone(),
                    typ: place.typ.clone(),
                    projections: vec![],
                };
                Ok((Some(fpt), bb))
            }
            PlaceX::Temporary(e) => {
                let bb = self.build(e, bb)?;
                Ok((None, bb))
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
        expr_all_bound_vars_with_ownership(loop_expr, &self.locals.var_modes)
            .iter()
            .map(|bv| {
                let fpt = FlattenedPlaceTyped {
                    local: bv.name.clone(),
                    typ: bv.typ.clone(),
                    projections: vec![],
                };
                self.locals.add_place(fpt, false)
            })
            .collect()
    }

    fn append_instructions_for_pattern_moves_mutations(
        &mut self,
        pattern: &Pattern,
        fpt: &FlattenedPlaceTyped,
        bb: BBIndex,
        position: AstPosition,
    ) {
        let places = moves_and_muts_for_place_being_matched(
            pattern,
            &fpt,
            &self.locals.datatypes,
            &self.locals.var_modes,
        );
        for (fpt, by_ref) in places.into_iter() {
            let fp = self.locals.add_place(fpt, false);
            self.push_instruction(
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
    // TODO(new_mut_ref) the mode-checking here needs to be exercised in test cases

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
    // TODO(new_mut_ref) need to check if stuff is copy vs move
    // TODO(new_mut_ref) need to account for pattern-ergonomics
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
                let is_irrefutable = match dt {
                    Dt::Path(path) => {
                        let datatype = &datatypes[path];
                        datatype.x.variants.len() == 1
                    }
                    Dt::Tuple(_) => true,
                };

                if is_irrefutable {
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
                } else {
                    // TODO(new_mut_ref) this is not quite right, need to check if anything
                    // is actually bound in here, irrefutability issues, Copy,
                    // what if there's a mixture of muts and moves
                    if crate::patterns::pattern_has_move(pattern, modes) {
                        out.push((projs.clone(), ByRef::No));
                    } else if crate::patterns::pattern_has_mut(pattern) {
                        out.push((projs.clone(), ByRef::MutRef));
                    }
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
    fn add_param(&mut self, p: &Param) {
        if p.x.mode != Mode::Spec {
            self.add_place(
                FlattenedPlaceTyped {
                    local: p.x.name.clone(),
                    typ: p.x.typ.clone(),
                    projections: vec![],
                },
                true,
            );
        }
    }

    /// Given a FlattenedPlaceTyped, we extend the tree if necessary so that it is deep enough
    /// to incorporate the given place. Returns a FlattenedPlace which indexes into the tree.
    fn add_place(&mut self, p: FlattenedPlaceTyped, is_param: bool) -> FlattenedPlace {
        if !self.ident_to_idx.contains_key(&p.local) {
            self.locals.push(Local {
                name: p.local.clone(),
                tree: PlaceTree::Leaf(p.typ.clone()),
                is_param,
            });
            self.ident_to_idx.insert(p.local.clone(), self.locals.len() - 1);
        }
        let idx = self.ident_to_idx[&p.local];

        let projections =
            Self::extend_tree(&mut self.locals[idx].tree, &p.projections, &self.datatypes);

        FlattenedPlace { local: idx, projections: projections }
    }

    fn extend_tree(
        tree: &mut PlaceTree,
        projections: &[ProjectionTyped],
        datatypes: &HashMap<Path, Datatype>,
    ) -> Vec<Projection> {
        let mut tree: &mut PlaceTree = tree;
        let mut output_projections: Vec<Projection> = vec![];
        for projection_typed in projections.iter() {
            if let PlaceTree::Leaf(typ) = tree {
                let typ = undecorate_box_decorations(typ);
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
                                (0..*n).map(|i| PlaceTree::Leaf(typ_args[i].clone())).collect(),
                            );
                        }
                        Dt::Path(path) => {
                            let datatype = &datatypes[path];
                            assert!(datatype.x.variants.len() == 1);
                            let variant = &datatype.x.variants[0];
                            let fields = variant
                                .fields
                                .iter()
                                .map(|f| {
                                    PlaceTree::Leaf(subst_typ_for_datatype(
                                        &datatype.x.typ_params,
                                        typ_args,
                                        &f.a.0,
                                    ))
                                })
                                .collect();
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
                    Projection::StructField(field_opr_to_index(field_opr, datatypes))
                }
                ProjectionTyped::DerefMut(_typ) => Projection::DerefMut,
            };
            output_projections.push(projection);

            match &projection {
                Projection::StructField(field_idx) => match tree {
                    PlaceTree::Leaf(_) => unreachable!(),
                    PlaceTree::Struct(_, _, subtrees) => {
                        tree = &mut subtrees[*field_idx];
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
        }
        output_projections
    }

    /// Turn a FlattenedPlace back into a vir::ast::Place
    fn to_ast_place(&self, span: &Span, fp: &FlattenedPlace) -> Place {
        let mut ast_place = SpannedTyped::new(
            span,
            self.locals[fp.local].tree.typ(),
            PlaceX::Local(self.locals[fp.local].name.clone()),
        );
        let mut tree = &self.locals[fp.local].tree;
        for projection in fp.projections.iter() {
            match projection {
                Projection::StructField(idx) => {
                    let (dt, inner_trees) = match tree {
                        PlaceTree::Struct(_ty, dt, trees) => (dt, trees),
                        _ => unreachable!(),
                    };
                    let inner_tree = &inner_trees[*idx];
                    let field_opr = match dt {
                        Dt::Tuple(n) => crate::ast_util::mk_tuple_field_opr(*n, *idx),
                        Dt::Path(path) => {
                            let datatype = &self.datatypes[path];
                            assert!(datatype.x.variants.len() == 1);
                            let variant = &datatype.x.variants[0];
                            FieldOpr {
                                datatype: dt.clone(),
                                variant: variant.name.clone(),
                                field: variant.fields[*idx].name.clone(),
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
                for (f, child) in children.iter().enumerate() {
                    cur.projections.push(Projection::StructField(f));
                    Self::traverse_rec(child, cur, output, go_inside_muts);
                    cur.projections.pop();
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

fn undecorate_box_decorations(t: &Typ) -> &Typ {
    match &**t {
        TypX::Decorate(TypDecoration::Box, _, t) => undecorate_box_decorations(t),
        _ => t,
    }
}

fn field_opr_to_index(field_opr: &FieldOpr, datatypes: &HashMap<Path, Datatype>) -> usize {
    match &field_opr.datatype {
        Dt::Tuple(n) => {
            let p = field_opr.field.parse::<usize>().unwrap();
            assert!(p < *n);
            p
        }
        Dt::Path(path) => {
            let datatype = &datatypes[path];
            assert!(datatype.x.variants.len() == 1);
            let variant = &datatype.x.variants[0];
            variant.fields.iter().position(|f| f.name == field_opr.field).unwrap()
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
            output.output[0][0] = entry_or_exit.clone();

            for i in 0..cfg.basic_blocks.len() {
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
    if bb == 0 {
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
    format!("{:#?}", &locals.locals)
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

fn pretty_flattened_place(locals: &LocalCollection, fp: &FlattenedPlace) -> String {
    let mut s: String = (*locals.locals[fp.local].name.0).clone();
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
            Projection::StructField(idx) => {
                let (dt, inner_tree) = match tree {
                    PlaceTree::Struct(_, dt, trees) => (dt, &trees[*idx]),
                    _ => unreachable!(),
                };
                let x = match dt {
                    Dt::Tuple(_) => {
                        format!(".{:}", idx)
                    }
                    Dt::Path(p) => {
                        let datatype = &locals.datatypes[p];
                        format!(".{:}", datatype.x.variants[0].fields[*idx].name)
                    }
                };
                (x, inner_tree)
            }
        };
        s += &x;
        tree = t;
    }
    s
}

////// Analysis: Initialization

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct InitializationPossibilities {
    /// Is it possible to reach the given program point when the given place uninitialized?
    can_be_uninit: bool,
    /// Is it possible to reach the given program point when the given place initialized?
    can_be_init: bool,
}

impl DataflowState for InitializationPossibilities {
    type Const = FlattenedPlace;

    fn join(&mut self, b: &Self) {
        *self = InitializationPossibilities {
            can_be_uninit: self.can_be_uninit || b.can_be_uninit,
            can_be_init: self.can_be_init || b.can_be_init,
        };
    }

    // forward transfer
    fn transfer(&self, instr: &Instruction, place: &FlattenedPlace) -> Self {
        match &instr.kind {
            InstructionKind::MoveFrom(sp) => {
                if sp.contains(place) {
                    InitializationPossibilities {
                        can_be_uninit: self.can_be_init || self.can_be_uninit,
                        can_be_init: false,
                    }
                } else {
                    *self
                }
            }
            InstructionKind::Overwrite(sp) => {
                if sp.contains(place) {
                    InitializationPossibilities {
                        can_be_uninit: false,
                        can_be_init: self.can_be_init || self.can_be_uninit,
                    }
                } else {
                    *self
                }
            }
            InstructionKind::Mutate(_sp) => *self,
            InstructionKind::DropFrom(sp) => {
                if sp.contains(place) {
                    InitializationPossibilities {
                        can_be_uninit: self.can_be_init || self.can_be_uninit,
                        can_be_init: false,
                    }
                } else {
                    *self
                }
            }
        }
    }
}

impl InitializationPossibilities {
    fn empty() -> Self {
        InitializationPossibilities { can_be_uninit: false, can_be_init: false }
    }

    fn entry(local: &Local) -> Self {
        // Params are initialized at the start, nothing else is
        InitializationPossibilities { can_be_uninit: !local.is_param, can_be_init: local.is_param }
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
                    InitializationPossibilities::entry(&cfg.locals.locals[place.local]),
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
    for bb in 0..cfg.basic_blocks.len() {
        for i in 0..cfg.basic_blocks[bb].instructions.len() + 1 {
            // Is it safe to resolve here?
            let can_assume_has_resolved = resolve_analysis.output[bb][i].can_resolve
                && !initialization_analysis.output[bb][i].can_be_uninit;
            if can_assume_has_resolved {
                // If so, is it *useful* to resolve here?
                let should_assume_has_resolved =
                    // At beginning of function, or beginning or end of a loop,
                    // Always add resolutions
                    (i == 0 && cfg.basic_blocks[bb].always_add_resolution_at_start)
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
fn apply_resolutions(cfg: &CFG, body: &Expr, resolutions: Vec<ResolutionToInsert>) -> Expr {
    let mut id_map = HashMap::<
        AstId,
        (Vec<FlattenedPlace>, Vec<FlattenedPlace>, Vec<FlattenedPlace>, bool),
    >::new();
    for r in resolutions.into_iter() {
        let ast_id = match r.position {
            AstPosition::Before(ast_id) => ast_id,
            AstPosition::After(ast_id) => ast_id,
            AstPosition::AfterArguments(ast_id) => ast_id,
            AstPosition::OnUnwind(_) => {
                // It might be necessary to do something here for more
                // advanced unwind-related stuff?
                continue;
            }
        };
        if !id_map.contains_key(&ast_id) {
            id_map.insert(ast_id, (vec![], vec![], vec![], false));
        }

        let entry = id_map.get_mut(&ast_id).unwrap();

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
        };
    }

    let result = crate::ast_visitor::map_expr_visitor_env(
        body,
        &mut VisitorScopeMap::new(),
        &mut id_map,
        &|id_map, scope_map, expr: &Expr| {
            if let Some((befores, afters, after_args, seen_yet)) = id_map.get_mut(&expr.span.id) {
                if *seen_yet {
                    panic!("Verus internal error: duplicate AstId");
                }
                *seen_yet = true;

                let befores_exprs = filter_and_make_assumes(cfg, &expr.span, scope_map, befores);
                let afters_exprs = filter_and_make_assumes(cfg, &expr.span, scope_map, afters);
                let after_args_exprs =
                    filter_and_make_assumes(cfg, &expr.span, scope_map, after_args);

                let e = expr.clone();
                let e = apply_after_args_exprs(e, after_args_exprs);
                let e = apply_before_exprs(e, befores_exprs);
                let e = apply_after_exprs(e, afters_exprs);

                Ok(e)
            } else {
                Ok(expr.clone())
            }
        },
        &|id_map, scope_map, stmt| {
            if let Some((befores, afters, after_args, seen_yet)) = id_map.get_mut(&stmt.span.id) {
                if *seen_yet {
                    panic!("Verus internal error: duplicate AstId");
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
        &|_, _, p| Ok(p.clone()),
    )
    .unwrap();

    for (_, (_, _, _, found)) in id_map.iter() {
        if !*found {
            panic!("resolution_inference: bad run for apply_resolutions");
        }
    }

    result
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
            if scope_map.contains_key(name) { Some(make_assume(cfg, span, fp)) } else { None }
        })
        .collect()
}

fn make_assume(cfg: &CFG, span: &Span, fp: &FlattenedPlace) -> Expr {
    let ast_place = cfg.locals.to_ast_place(span, fp);
    let e = SpannedTyped::new(
        &ast_place.span,
        &ast_place.typ,
        ExprX::ReadPlace(
            ast_place.clone(),
            UnfinalizedReadKind { preliminary_kind: ReadKind::Spec, id: u64::MAX },
        ),
    );
    SpannedTyped::new(
        &ast_place.span,
        &crate::ast_util::unit_typ(),
        ExprX::AssumeResolved(e, ast_place.typ.clone()),
    )
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
        SpannedTyped::new(
            &expr.span,
            &crate::ast_util::unit_typ(),
            ExprX::Block(Arc::new(stmts), None),
        )
    };
    SpannedTyped::new(
        &expr.span,
        &expr.typ,
        ExprX::UseLeftWhereRightCanHaveNoAssignments(expr.clone(), e),
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
            let block = SpannedTyped::new(
                &expr.span,
                &crate::ast_util::unit_typ(),
                ExprX::Block(Arc::new(stmts), None),
            );
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
