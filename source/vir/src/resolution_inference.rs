#![allow(unused_variables)] // TODO remove
#![allow(dead_code)]

use crate::modes::ReadKindFinals;
use crate::ast::{Expr, Place, Params, Param, ExprX, ReadKind, Typ, VarIdent, BinaryOp, PlaceX, UnfinalizedReadKind, Stmt, StmtX, SpannedTyped};
use std::collections::{VecDeque, HashMap};
use crate::messages::AstId;
use crate::ast_visitor::VisitorScopeMap;
use crate::def::Spanned;
use std::sync::Arc;

enum PlaceTree {
    Leaf(Typ),
    Struct(Typ, Vec<PlaceTree>),
    MutRef(Typ, Box<PlaceTree>),
}

struct Local {
    name: VarIdent,
    is_param: bool,
    tree: PlaceTree,
}

struct LocalCollection {
    locals: Vec<Local>,
    ident_to_idx: HashMap<VarIdent, usize>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Projection {
    StructField(usize),
    MutDeref,
}

struct FlattenedPlaceTyped {
    local: VarIdent,
    typ: Typ,
    projections: Vec<Projection>,
}

#[derive(Clone)]
struct FlattenedPlace {
    local: usize,
    projections: Vec<Projection>,
}

#[derive(Clone, Copy)]
enum AstPosition {
    Before(AstId),
    After(AstId),
}

struct Instruction {
    kind: InstructionKind,
    position: AstPosition,
}

enum InstructionKind {
    /// Move from the place; must previously be initialized, becomes uninitialized.
    MoveFrom(FlattenedPlace),
    /// Overwrite the place; it previously may be initialized, uninitialized,
    /// or partially initialized. Whatever was there before gets dropped.
    Overwrite(FlattenedPlace),
    /// Mutate the value at the place, which must previously be initialized and remains initialized
    Mutate(FlattenedPlace),
}

type BBIndex = usize;
struct BasicBlock {
    instructions: Vec<Instruction>,
    predecessors: Vec<BBIndex>,
    successors: Vec<BBIndex>,
    is_exit: bool,

    always_add_resolution_at_start: bool,
    position_of_start: AstPosition,
}

struct CFG {
    basic_blocks: Vec<BasicBlock>,
    locals: LocalCollection,
}

struct ResolutionToInsert {
    place: FlattenedPlace,
    position: AstPosition,
}

pub(crate) fn infer_resolution(params: &Params, body: &Expr, read_kind_finals: &ReadKindFinals) -> Expr {
    let cfg = new_cfg(params, body, read_kind_finals);
    let resolutions = get_resolutions(&cfg);
    apply_resolutions(&cfg, body, resolutions)
}

////// CFG builder

struct Builder<'a> {
    basic_blocks: Vec<BasicBlock>,
    loops: Vec<LoopEntry>,
    locals: LocalCollection,
    read_kind_finals: &'a ReadKindFinals,
}

struct LoopEntry {
    label: Option<String>,
    break_bb: BBIndex,
    continue_bb: BBIndex,
}

fn new_cfg(params: &Params, body: &Expr, read_kind_finals: &ReadKindFinals) -> CFG {
    let mut builder = Builder {
        basic_blocks: vec![],
        loops: vec![],
        locals: LocalCollection {
            locals: vec![],
            ident_to_idx: HashMap::new(),
        },
        read_kind_finals,
    };
    let start_bb = builder.new_bb(AstPosition::Before(body.span.id), true);

    for param in params.iter() {
        builder.locals.add_param(param);
    }
    let end_bb = builder.build(body, start_bb);
    builder.optionally_exit(end_bb);

    builder.compute_predecessors();

    CFG {
        basic_blocks: builder.basic_blocks,
        locals: builder.locals,
    }
}

impl<'a> Builder<'a> {
    fn compute_predecessors(&mut self) {
        for bb1 in 0 .. self.basic_blocks.len() {
            for j in 0 .. self.basic_blocks[bb1].successors.len() {
                let bb2 = self.basic_blocks[bb1].successors[j];
                self.basic_blocks[bb2].predecessors.push(bb1);
            }
        }
    }

    fn new_bb(&mut self, start_position: AstPosition, always_add_resolution_at_start: bool) -> BBIndex {
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
            Ok(bb) => { self.basic_blocks[bb].is_exit = true; }
            _ => { }
        }
    }

    fn optionally_push_successor(&mut self, bb: Result<BBIndex, ()>, successor: BBIndex) {
        match bb {
            Ok(bb) => { self.basic_blocks[bb].successors.push(successor); }
            _ => { }
        }
    }

    fn push_instruction(&mut self, bb: BBIndex, pos: AstPosition, instr: InstructionKind) {
        self.basic_blocks[bb].instructions.push(Instruction {
            kind: instr,
            position: pos
        });
    }

    fn get_loop<'b: 'a>(&'b self, loop_label: &Option<String>) -> &'b LoopEntry {
        match loop_label {
            None => &self.loops[self.loops.len() - 1],
            Some(label) => {
                for l in self.loops.iter().rev() {
                    match &l.label {
                        Some(label2) if label == label2 => { return l; }
                        _ => { }
                    }
                }
                panic!("Could not find label {:}", label);
            }
        }
    }

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
             | ExprX::AssumeResolved(..)
             => {
                Ok(bb)
            }
            ExprX::Call(_ct, es) => {
                // can skip the expression in ct, it can only be for FnSpec which is always
                // a pure spec expression
                for e in es.iter() {
                    bb = self.build(e, bb)?;
                }
                Ok(bb)
            }
            ExprX::Ctor(_dt, _id, binders, opt_place) => {
                for b in binders.iter() {
                    bb = self.build(&b.a, bb)?;
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
            ExprX::NullaryOpr(_) => {
                Ok(bb)
            }
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
                todo!()
            }
            ExprX::Loop { loop_isolation: _, is_for_loop: _, label, cond, body, invs: _, decrease: _ } => {
                todo!()
            }
            ExprX::OpenInvariant(e1, _, e2, _) => {
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
                let next_bb = if *is_break { entry.break_bb } else { entry.continue_bb };
                self.basic_blocks[bb].successors.push(next_bb);
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
                    self.push_instruction(bb,
                        AstPosition::After(span_id),
                        InstructionKind::Overwrite(p));
                }
                Ok(bb)
            }
            ExprX::AssignToPlace { place, rhs, op: Some(_) } => {
                todo!()
            }
            ExprX::BorrowMut(p) => {
                let (p, bb) = self.build_place(p, bb)?;
                if let Some(p) = p {
                    self.push_instruction(bb,
                        AstPosition::After(span_id),
                        InstructionKind::Mutate(p));
                }
                Ok(bb)
            }
            ExprX::BorrowMutPhaseOne(..) | ExprX::BorrowMutPhaseTwo(..) => {
                panic!("BorrowMutPhaseOne/BorrowMutPhaseTwo shouldn't be created yet");
            }
            ExprX::ReadPlace(p, unfinal_read_kind) => {
                let (p, bb) = self.build_place(p, bb)?;
                if let Some(p) = p {
                    if matches!(self.get_read_kind(unfinal_read_kind), ReadKind::Move) {
                        self.push_instruction(bb,
                            AstPosition::After(span_id),
                            InstructionKind::MoveFrom(p));
                    }
                }
                Ok(bb)
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
        }
    }

    fn build_stmt(&mut self, stmt: &Stmt, bb: BBIndex) -> Result<BBIndex, ()> {
        match &stmt.x {
            StmtX::Expr(e) => {
                self.build(e, bb)
            }
            StmtX::Decl { pattern: _, mode: _, init: _, els: _ } => {
                todo!()
            }
        }
    }

    fn build_place(&mut self, place: &Place, bb: BBIndex) -> Result<(Option<FlattenedPlace>, BBIndex), ()> {
        let r = self.build_place_rec(place, bb);
        match r {
            Ok((Some(fpi), bb)) => {
                let sp = self.locals.add_place(fpi, false);
                Ok((Some(sp), bb))
            }
            Ok((None, bb)) => Ok((None, bb)),
            Err(e) => Err(e),
        }
    }

    fn build_place_rec(&mut self, place: &Place, bb: BBIndex) -> Result<(Option<FlattenedPlaceTyped>, BBIndex), ()> {
        match &place.x {
            PlaceX::Field(field_opr, p) => {
                todo!()
            }
            PlaceX::DerefMut(p) => {
                todo!()
            }
            PlaceX::Local(var) => {
                todo!()
            }
            PlaceX::Temporary(e) => {
                let b = self.build(e, bb)?;
                Ok((None, b))
            }
        }
    }

    fn get_read_kind(&self, unfinal_read_kind: &UnfinalizedReadKind) -> ReadKind {
        todo!()
    }
}

////// Place trees

impl LocalCollection {
    fn add_param(&mut self, p: &Param) {
        todo!();
    }

    fn add_place(&mut self, p: FlattenedPlaceTyped, is_param: bool) -> FlattenedPlace {
        if !self.ident_to_idx.contains_key(&p.local) {
            self.locals.push(Local { name: p.local.clone(), tree: PlaceTree::Leaf(p.typ.clone()), is_param });
            self.ident_to_idx.insert(p.local.clone(), self.locals.len() - 1);
        }
        let idx = self.ident_to_idx[&p.local];

        Self::extend_tree(&mut self.locals[idx].tree, &p.projections);

        FlattenedPlace { local: idx, projections: p.projections }
    }

    fn extend_tree(tree: &mut PlaceTree, projections: &[Projection]) {
        if projections.len() == 0 {
            return;
        }

        if matches!(tree, PlaceTree::Leaf(_)) {
            todo!();
        }

        match &projections[0] {
            Projection::StructField(field_idx) => {
                match tree {
                    PlaceTree::Leaf(_) => unreachable!(),
                    PlaceTree::Struct(_, subtrees) => {
                        Self::extend_tree(&mut subtrees[*field_idx], &projections[1..]);
                    }
                    PlaceTree::MutRef(..) => {
                        panic!("Verus internal error: extend_tree failed, conflicting projection type");
                    }
                }
            }
            Projection::MutDeref => {
                match tree {
                    PlaceTree::Leaf(_) => unreachable!(),
                    PlaceTree::Struct(..) => {
                        panic!("Verus internal error: extend_tree failed, conflicting projection type");
                    }
                    PlaceTree::MutRef(_, inner) => {
                        Self::extend_tree(&mut *inner, &projections[1..]);
                    }
                }
            }
        }
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

    fn traverse_rec(tree: &PlaceTree, cur: &mut FlattenedPlace, output: &mut Vec<FlattenedPlace>,
        go_inside_muts: bool)
    {
        match tree {
            PlaceTree::Leaf(_t) => {
                output.push(cur.clone());
            }
            PlaceTree::Struct(_t, children) => {
                for (f, child) in children.iter().enumerate() {
                    cur.projections.push(Projection::StructField(f));
                    Self::traverse_rec(child, cur, output, go_inside_muts);
                    cur.projections.pop();
                }
            }
            PlaceTree::MutRef(_t, child) => {
                output.push(cur.clone());
                if go_inside_muts {
                    cur.projections.push(Projection::MutDeref);
                    Self::traverse_rec(child, cur, output, go_inside_muts);
                    cur.projections.pop();
                }
            }
        }
    }
}

impl FlattenedPlace {
    fn intersects(&self, other: &Self) -> bool {
        if self.local == other.local {
            let m = std::cmp::min(self.projections.len(), other.projections.len());
            (0 .. m).all(|i| self.projections[i] == other.projections[i])
        } else {
            false
        }
    }

    fn contains(&self, other: &Self) -> bool {
        self.local == other.local
            && self.projections.len() <= other.projections.len()
            && (0 .. self.projections.len()).all(|i| self.projections[i] == other.projections[i])
    }

    fn contains_and_not_separated_by_deref(&self, other: &Self) -> bool {
        self.contains(other)
            && (self.projections.len() .. other.projections.len())
                .all(|i| !matches!(other.projections[i], Projection::MutDeref))
    }

    fn has_deref(&self) -> bool {
        self.projections.iter().any(|p| matches!(p, Projection::MutDeref))
    }

    fn value_may_change(&self, instr: &Instruction) -> bool {
        match &instr.kind {
            InstructionKind::MoveFrom(_) => false,
            InstructionKind::Overwrite(sp) => self.intersects(sp),
            InstructionKind::Mutate(sp) => self.intersects(sp),
        }
    }
}

////// CFG dataflow analysis

trait DataflowState {
    type Const;

    fn join(&mut self, b: &Self);
    fn transfer(&self, instr: &Instruction, c: &Self::Const) -> Self;
}

enum Direction {
    Forward,
    Reverse
}

struct DataflowOutput<D> {
    output: Vec<Vec<D>>,
}

fn do_dataflow<D: DataflowState + Clone + Eq>(cfg: &CFG, empty: D, entry_or_exit: D, c: &D::Const, dir: Direction)
    -> DataflowOutput<D>
{
    let mut output = DataflowOutput { output: vec![] };
    for bb in cfg.basic_blocks.iter() {
        let mut v = vec![];
        for i in 0 .. bb.instructions.len() + 1 {
            v.push(empty.clone());
        }
        output.output.push(v);
    }

    let mut worklist = VecDeque::<BBIndex>::new();
    let mut in_worklist = vec![false; cfg.basic_blocks.len()];

    match dir {
        Direction::Forward => {
            output.output[0][0] = entry_or_exit.clone();
            worklist.push_back(0);
            in_worklist[0] = true;

            loop {
                let Some(bb) = worklist.pop_front() else { break; };
                in_worklist[bb] = false;

                let new_value = join_predecessors(&output, &cfg, bb, &empty, &entry_or_exit);
                let slot = &mut output.output[bb][0];

                if *slot != new_value {
                    *slot = new_value;
                    transfer_forward(&mut output.output[bb], &cfg.basic_blocks[bb].instructions, c);
                }
                for bb1 in cfg.basic_blocks[bb].successors.iter() {
                    if !in_worklist[*bb1] {
                        worklist.push_back(*bb1);
                        in_worklist[*bb1] = true;
                    }
                }
            }
        }
        Direction::Reverse => {
            for i in 0 .. cfg.basic_blocks.len() {
                if cfg.basic_blocks[i].is_exit {
                    *output.output[i].last_mut().unwrap() = entry_or_exit.clone();
                    worklist.push_back(i);
                    in_worklist[i] = true;
                }
            }

            while worklist.len() > 0 {
                let Some(bb) = worklist.pop_front() else { break; };
                in_worklist[bb] = false;

                let new_value = join_successors(&output, &cfg, bb, &empty, &entry_or_exit);
                let slot = output.output[bb].last_mut().unwrap();

                if *slot != new_value {
                    *slot = new_value;
                    transfer_reverse(&mut output.output[bb], &cfg.basic_blocks[bb].instructions, c);
                }
                for bb1 in cfg.basic_blocks[bb].predecessors.iter() {
                    if !in_worklist[*bb1] {
                        worklist.push_back(*bb1);
                        in_worklist[*bb1] = true;
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
    for i in 0 .. instructions.len() {
        output[i+1] = output[i].transfer(&instructions[i], c);
    }
}

fn transfer_reverse<D: DataflowState>(
    output: &mut Vec<D>,
    instructions: &[Instruction],
    c: &D::Const,
) {
    for i in (0 .. instructions.len()).rev() {
        output[i] = output[i+1].transfer(&instructions[i], c);
    }
}



/*
impl<D: DataflowState> DataflowState for Rc<Vec<D>> {
    fn join(&self, b: &Self) -> Self {
        Rc::new(self.iter().zip(b.iter()).map(|(a, b)| a.join(b)).collect::<Vec<_>>())
    }

    fn transfer(&self, instr: &Instruction) -> Self {
        let idx = match instr {
            Instruction::MoveFrom(p) => p.local,
            Instruction::AssignTo(p) => p.local,
        };
        let v: Vec<D> = (**self).clone();
        v[idx] = v[idx].transfer(instr);
        Rc::new(v)
    }
}

////// Analysis: Initialization

struct InitializationPossibilities {
    can_be_uninit: bool,
    can_be_init: bool,
}

impl DataflowState for InitializationPossibilities {
    fn join(&self, b: &Self) -> Self {
        InitializationPossibilities {
            can_be_uninit: self.can_be_uninit || b.can_be_uninit,
            can_be_init: self.can_be_init || b.can_be_init,
        }
    }

    fn transfer(&self, instr: &Instruction) -> Self {
        match instr {
            Instruction::MoveFrom(p) => {
                InitializationPossibilities {
                    can_be_init: false,
                    can_be_uninit: 
                }
            }
            Instruction::AssignTo(p) => {
            }
        }
    }
}
*/

////// Analysis: Initialization

#[derive(Clone, Copy, PartialEq, Eq)]
struct InitializationPossibilities {
    can_be_uninit: bool,
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
            InstructionKind::Mutate(sp) => {
                *self
            }
        }
    }
}

impl InitializationPossibilities {
    fn empty() -> Self {
        InitializationPossibilities {
            can_be_uninit: false,
            can_be_init: false,
        }
    }

    fn entry(local: &Local) -> Self {
        InitializationPossibilities {
            can_be_uninit: !local.is_param,
            can_be_init: local.is_param,
        }
    }
}

////// Analysis: Resolve

#[derive(Clone, Copy, PartialEq, Eq)]
struct ResolveSafety {
    can_resolve: bool,
}

impl DataflowState for ResolveSafety {
    type Const = FlattenedPlace;

    fn join(&mut self, b: &Self) {
        *self = ResolveSafety {
            can_resolve: self.can_resolve && b.can_resolve,
        }
    }

    // backward transfer
    fn transfer(&self, instr: &Instruction, place: &FlattenedPlace) -> Self {
        match &instr.kind {
            InstructionKind::MoveFrom(sp) => {
                if sp.intersects(place) {
                    ResolveSafety { can_resolve: false }
                } else {
                    *self
                }
            }
            InstructionKind::Overwrite(sp) => {
                if sp.contains_and_not_separated_by_deref(place) {
                    ResolveSafety { can_resolve: true }
                } else if sp.intersects(place) {
                    ResolveSafety { can_resolve: false }
                } else {
                    *self
                }
            }
            InstructionKind::Mutate(sp) => {
                if sp.intersects(place) {
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

fn get_resolutions(cfg: &CFG) -> Vec<ResolutionToInsert> {
    let initialization_places = cfg.locals.places_skip_insides_of_mut_refs();
    let initialization_analyses: Vec<DataflowOutput<InitializationPossibilities>>
      = initialization_places.iter().map(|place| {
        do_dataflow::<InitializationPossibilities>(cfg,
            InitializationPossibilities::empty(),
            InitializationPossibilities::entry(&cfg.locals.locals[place.local]),
            place,
            Direction::Forward)
    }).collect();

    let resolve_places = cfg.locals.places_including_insides_of_mut_refs();
    let resolve_analyses: Vec<DataflowOutput<ResolveSafety>>
      = resolve_places.iter().map(|place| {
        do_dataflow::<ResolveSafety>(cfg,
            ResolveSafety::empty(),
            ResolveSafety::exit(place),
            place,
            Direction::Reverse)
    }).collect();

    let mut output = vec![];

    let mut i_idx = 0;
    for r_idx in 0 .. resolve_places.len() {
        while !initialization_places[i_idx].contains(&resolve_places[i_idx]) {
            i_idx += 1;
        }

        // TODO(new_mut_ref): filter for "interesting" types, i.e., those containing a &mut ref
        // TODO(new_mut_ref): need to account for drops

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
    for bb in 0 .. cfg.basic_blocks.len() {
        for i in 0 .. cfg.basic_blocks[bb].instructions.len() + 1 {
            let can_assume_has_resolved =
                resolve_analysis.output[bb][i].can_resolve
                  && !initialization_analysis.output[bb][i].can_be_uninit;
            if can_assume_has_resolved {
                let should_assume_has_resolved =
                    (i == 0 && cfg.basic_blocks[bb].always_add_resolution_at_start)
                    || (i == 0 && cfg.basic_blocks[bb].predecessors.iter().any(|pred|
                        !resolve_analysis.output[*pred].last().unwrap().can_resolve
                    ))
                    || (i > 0 && !resolve_analysis.output[bb][i-1].can_resolve)
                    || (i > 0 && place.value_may_change(&cfg.basic_blocks[bb].instructions[i-1]));
                if should_assume_has_resolved {
                    output.push(ResolutionToInsert {
                        place: place.clone(),
                        position: if i == 0 {
                            cfg.basic_blocks[bb].position_of_start
                        } else {
                            cfg.basic_blocks[bb].instructions[i - 1].position
                        }
                    });
                }
            }
        }
    }
}

////// Modify the AST Expr with the new resolutions

fn apply_resolutions(cfg: &CFG, body: &Expr, resolutions: Vec<ResolutionToInsert>) -> Expr {
    let mut id_map = HashMap::<AstId, (Vec<FlattenedPlace>, Vec<FlattenedPlace>, bool)>::new();
    for r in resolutions.into_iter() {
        let ast_id = match r.position {
            AstPosition::Before(ast_id) => ast_id,
            AstPosition::After(ast_id) => ast_id,
        };
        if !id_map.contains_key(&ast_id) {
            id_map.insert(ast_id, (vec![], vec![], false));
        }

        let entry = id_map.get_mut(&ast_id).unwrap();

        match r.position {
            AstPosition::Before(ast_id) => { entry.0.push(r.place); }
            AstPosition::After(ast_id) => { entry.1.push(r.place); }
        };
    }

    crate::ast_visitor::map_expr_visitor_env(
        body,
        &mut VisitorScopeMap::new(),
        &mut id_map,
        &|id_map, scope_map, expr: &Expr| {
            if let Some((befores, afters, seen_yet)) = id_map.get_mut(&expr.span.id) {
                if *seen_yet {
                    panic!("Verus internal error: duplicate AstId");
                }
                *seen_yet = true;

                let befores_exprs = filter_and_make_assumes(cfg, scope_map, befores);
                let afters_exprs = filter_and_make_assumes(cfg, scope_map, afters);

                let mut e = expr.clone();
                e = apply_before_exprs(e, befores_exprs);
                e = apply_after_exprs(e, afters_exprs);
                Ok(e)
            } else {
                Ok(expr.clone())
            }
        },
        &|_, _, s| Ok(vec![s.clone()]),
        &|_, t| Ok(t.clone()),
        &|_, _, p| Ok(p.clone()),
    ).unwrap()
}

fn filter_and_make_assumes(cfg: &CFG, scope_map: &VisitorScopeMap, v: &Vec<FlattenedPlace>)
    -> Vec<Expr>
{
    v.iter().filter_map(|fp| {
        let name = &cfg.locals.locals[fp.local].name;
        if scope_map.contains_key(name) {
            Some(make_assume(cfg, fp))
        } else {
            None
        }
    }).collect()
}

fn make_assume(cfg: &CFG, fp: &FlattenedPlace) -> Expr {
    todo!()
}

fn apply_before_exprs(expr: Expr, before_exprs: Vec<Expr>) -> Expr {
    if before_exprs.len() == 0 {
        return expr;
    }
    let mut stmts = vec![];
    for e in before_exprs.into_iter() {
        stmts.push(Spanned::new(e.span.clone(), StmtX::Expr(e)));
    }
    SpannedTyped::new(
        &expr.span,
        &expr.typ,
        ExprX::Block(Arc::new(stmts), Some(expr.clone())))
}

fn apply_after_exprs(expr: Expr, after_exprs: Vec<Expr>) -> Expr {
    todo!()
}
