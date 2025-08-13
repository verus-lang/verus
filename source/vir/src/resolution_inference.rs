use crate::modes::ReadKindFinals;
use crate::ast::{Expr, Place, Params, Param, ExprX, ReadKind};
use std::collections::VecDeque;

enum PlaceTree {
    Leaf(Typ),
    Struct(Typ, Vec<PlaceTree>),
    MutRef(Typ, Box<PlaceTree>),
}

struct Local {
    name: VarIdent,
    tree: PlaceTree,
}

struct LocalCollection {
    locals: Vec<Local>,
    ident_to_idx: HashMap<VarIdent, usize>,
}

enum Projection {
    StructField(usize),
    MutRefDeref,
}

struct SimplePlace {
    local: usize,
    projections: Vec<Projection>,
}


enum Instruction {
    /// Move from the place; must previously be initialized, becomes uninitialized.
    MoveFrom(SimplePlace),
    /// Overwrite the place; it previously may be initialized, uninitialized,
    /// or partially initialized. Whatever was there before gets dropped.
    Overwrite(SimplePlace),
    /// Mutate the value at the place, which must previously be initialized and remains initialized
    Mutate(SimplePlace),
}

type BBIndex = usize;
struct BasicBlock {
    instructions: Vec<Instruction>,
    predecessors: Vec<BBIndex>,
    successors: Vec<BBIndex>,
    is_exit: bool,

    always_add_resolution_at_start: bool,
}

struct CFG {
    basic_blocks: Vec<BasicBlock>,
    locals: LocalCollection,
}

pub(crate) fn infer_resolution(params: &Params, expr: &Expr, read_kind_finals: &ReadKindFinals) -> Expr {
    let cfg = new_cfg(params, expr);

    /*
    let safe_to_resolve = analysis_safe_to_resolve(&cfg);
    let initialization = analysis_initialization(&cfg);

    let resolutions = get_resolutions(&cfg, &safe_to_resolve, &initialization);
    apply_resolutions(expr, &resolutions)
    */
    todo!()
}

////// CFG builder

struct Builder {
    basic_blocks: Vec<BasicBlock>,
    loops: Vec<LoopEntry>,
}

struct LoopEntry {
    label: Option<String>,
    break_bb: BBIndex,
    continue_bb: BBIndex,
}

fn new_cfg(params: &Params, e: &Expr) -> CFG {
    let mut builder = Builder { basic_blocks: vec![], loops: vec![] };
    let start_bb = builder.new_bb(true);

    for param in params.iter() {
        let place = builder.place_from_param(param);
        builder.push_instruction(start_bb, Instruction::Overwrite(place));
    }
    let end_bb = builder.build(e, start_bb);
    builder.optionally_exit(end_bb);

    builder.compute_predecessors();

    CFG {
        basic_blocks: builder.basic_blocks
    }
}

impl Builder {
    fn compute_predecessors(&mut self) {
        for bb1 in 0 .. self.basic_blocks.len() {
            for j in 0 .. self.basic_blocks[bb1].successors.len() {
                let bb2 = self.basic_blocks[bb1].successors[j];
                self.basic_blocks[bb2].predecessors.push(bb1);
            }
        }
    }

    fn new_bb(&mut self, always_add_resolution_at_start: bool) -> BBIndex {
        self.basic_blocks.push(BasicBlock {
            instructions: vec![],
            predecessors: vec![],
            successors: vec![],
            is_exit: false,
            always_add_resolution_at_start,
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

    fn push_instruction(&mut self, bb: BBIndex, instr: Instruction) {
        self.basic_blocks[bb].instructions.push(instr);
    }

    fn get_loop<'a>(&'a self, loop_label: &Option<String>) -> &'a LoopEntry {
        match loop_label {
            None => &self.loops[self.loops.len() - 1],
            Some(label) => {
                for l in self.loops.iter().rev() {
                    match &l.label {
                        Some(label2) if label == label2 => { return l; }
                        None => { }
                    }
                }
                panic!("Could not find label {:}", label);
            }
        }
    }

    fn build(&mut self, e: &Expr, bb: BBIndex) -> Result<BBIndex, ()> {
        let mut bb = bb;
        match &e.x {
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
            ExprX::Call(ct, es) => {
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
            ExprX::NullaryOpr(_) => {
                Ok(bb)
            }
            ExprX::Unary(_, e) | ExprX::UnaryOpr(_, e) => {
                bb = self.build(e, bb)?;
                Ok(bb)
            }
            ExprX::Binary(BinaryOp::And | BinaryOp::Or | BinaryOp::Implies, e1, e2) => {
                todo!();
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
            ExprX::If(cond, thn, els) => {
                bb = self.build(cond, bb)?;

                let thn_block = self.new_bb(false);
                let els_block = self.new_bb(false);
                self.basic_blocks[bb].successors.push(thn_block);
                self.basic_blocks[bb].successors.push(els_block);

                let thn_bb_end = self.build(thn, thn_block);

                let els_bb_end = match els {
                    Some(els) => self.build(els, els_block),
                    None => Ok(els_block),
                };

                if thn_bb_end.is_ok() || els_bb_end.is_ok() {
                    let join_block = self.new_bb(false);
                    self.optionally_push_successor(thn_bb_end, join_block);
                    self.optionally_push_successor(els_bb_end, join_block);
                    Ok(join_block)
                } else {
                    Err(())
                }
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
                let (p, bb) = self.build_place(place)?;
                let bb = self.build(rhs)?;
                self.push_instruction(bb, Instruction::Overwrite(p));
                Ok(bb)
            }
            ExprX::BorrowMut(p) => {
                let (p, bb) = self.build_place(p, bb)?;
                self.push_instruction(bb, Instruction::BorrowMut(p));
                Ok(bb)
            }
            ExprX::BorrowMutPhaseOne(p) => {
                let (p, bb) = self.build_place(p, bb)?;
                Ok(bb)
            }
            ExprX::BorrowMutPhaseTwo(p, e) => {
                let (p, bb) = self.build_place(p, bb)?;
                let bb = self.build(e, bb)?;
                self.push_instruction(bb, Instruction::BorrowMut(p));
                Ok(bb)
            }
            ExprX::ReadPlace(p, urk) => {
                let (p, bb) = self.build_place(p, bb)?;
                if matches!(self.get_read_kind(urk), ReadKind::Move) {
                    self.push_instruction(bb, Instruction::MoveFrom(p));
                }
                Ok(bb)
            }
            ExprX::Block(stmts, e_opt) => {
                for s in stmts.iter() {
                    bb = self.build_stmt(s, bb)?;
                }
                if let Some(e) = e_opt {
                    bb = self.build(bb)?;
                }
                Ok(bb)
            }
        }
    }

    fn build_place(place: &Place, bb: BBIndex) -> Result<(Option<SimplePlace>, BBIndex), ()> {
        match build_place_rec(place, bb) {
            Ok((Some(r),
            Ok((None, x))
        }
    }

    fn build_place_rec(place: &Place, bb: BBIndex) -> Result<(Option<SimplePlace>, BBIndex), ()> {
        match &p.x {
            PlaceX::Field(field_opr, p) => {
            }
            PlaceX::DerefMut(p) => {
            }
            PlaceX::Local(var) => {
            }
            PlaceX::Temporary(e) => {
                let b = self.build(e, bb)?;
                Ok((None, b))
            }
        }
    }

    fn place_from_param(&mut self, param: &Param) -> SimplePlace {
        todo!();
    }
}

////// Place trees

impl LocalCollection {
    fn add_place(&mut self, local: VarIdent, typ: Typ, projections: Vec<Projection>) -> SimplePlace {
        if !self.ident_to_idx.contains(local) {
            self.locals.push(Local { name: local, tree: PlaceTree::Leaf(typ.clone()) });
            self.ident_to_idx.insert(local, self.locals.len() - 1);
        }
        let idx = self.ident_to_idx[local];

        Self::extend_tree(&mut self.locals[idx].tree, &projections);
    }

    fn extend_tree(tree: &mut PlaceTree, projections: &[Projection]) {
        if projections.len() == 0 {
            return;
        }

        if matches!(tree, PlaceTree::Leaf) {
            todo!();
        }

        match &projections[0] {
            Projection::StructField(field_idx) => {
                match tree {
                    PlaceTree::Leaf(_) => unreachable!(),
                    PlaceTree::Struct(_, subtrees) => {
                        Self::extend_tree(&mut subtrees[field_idx], &projections[1..]);
                    }
                    PlaceTree::MutRef(..) => {
                        panic!("Verus internal error: extend_tree failed, conflicting projection type");
                    }
                }
            }
            Projection::MutRefDeref => {
                match tree {
                    PlaceTree::Leaf(_) => unreachable!(),
                    PlaceTree::Struct(..) => {
                        panic!("Verus internal error: extend_tree failed, conflicting projection type");
                    }
                    PlaceTree::MutRef(inner) => {
                        Self::extend_tree(&mut inner, &projections[1..]);
                    }
                }
            }
        }
    }

    fn leaf_places() -> Vec<SimplePlace> {
        
    }
}

////// CFG analysis

trait DataflowState {
    fn join(&mut self, b: &Self);
    fn transfer(&self, instr: &Instruction, out: &mut Self);
}

enum Direction {
    Forward,
    Reverse
}

struct DataflowOutput<D> {
    output: Vec<Vec<D>>,
}

pub(crate) fn do_dataflow<D: DataflowState + Clone + Eq>(cfg: &CFG, empty: D, entry_or_exit: D, dir: Direction)
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
    let mut in_worklist = Vec::<bool>::fill(false, cfg.basic_blocks.len());

    match dir {
        Direction::Forward => {
            output.output[0][0] = entry_or_exit;
            worklist.push_back(0);
            in_worklist[0] = true;

            while worklist.len() > 0 {
                let bb = worklist.pop_front();
                in_worklist[bb] = false;

                let new_value = join_predecessors(&output, &cfg, bb, &empty, &entry_or_exit);
                let slot = &mut output.output[bb][0];

                if *slot != new_value {
                    *slot = new_value;
                    transfer_forward(&mut output.output[bb], &cfg.basic_blocks[bb]);
                }
                for bb in cfg.basic_blocks.successors.iter() {
                    if !in_worklist[bb] {
                        worklist.push_back(bb);
                        in_worklist[bb] = true;
                    }
                }
            }
        }
        Direction::Reverse => {
            for i in 0 .. cfg.basic_blocks.len() {
                if cfg.basic_blocks[i].is_exit {
                    output.output[i][output.output[i].len() - 1] = entry_or_exit;
                    worklist.push_back(i);
                    in_worklist[i] = true;
                }
            }

            while worklist.len() > 0 {
                let bb = worklist.pop_front();
                in_worklist[bb] = false;

                let new_value = join_successors(&output, &cfg, bb, &empty, &entry_or_exit);
                let slot = &mut output.output[bb][output.output[bb].len() - 1];

                if *slot != new_value {
                    *slot = new_value;
                    transfer_reverse(&mut output.output[bb], &cfg.basic_blocks[bb]);
                }
                for bb in cfg.basic_blocks.predecessors.iter() {
                    if !in_worklist[bb] {
                        worklist.push_back(bb);
                        in_worklist[bb] = true;
                    }
                }
            }
        }
    }

    output
}

fn join_predecessors<D: DataflowState>(
    output: &DataflowOutput<D>,
    cfg: &CFG,
    bb: BBIndex,
    empty: &D,
    entry: &D,
) {
    if bb == 0 {
        let mut res = entry.clone();
        for pred in cfg.basic_blocks[bb].predecessors.iter() {
            res.join(output[pred][output[pred].len() - 1]);
        }
        res
    } else if cfg.basic_blocks[bb].predecessors.len() > 0 {
        let pred0 = cfg.basic_blocks[bb].predecessors[0];
        let mut res = output[pred0][output[pred0].len() - 1].clone();
        for pred in cfg.basic_blocks[bb].predecessors.iter().skip(1) {
            res.join(output[pred][output[pred].len() - 1]);
        }
        res
    } else {
        empty
    }
}

fn join_successors<D: DataflowState>(
    output: &DataflowOutput<D>,
    cfg: &CFG,
    bb: BBIndex,
    empty: &D,
    exit: &D,
) {
    if cfg.basic_blocks[bb].is_exit {
        let mut res = entry.clone();
        for succ in cfg.basic_blocks[bb].successors.iter() {
            res.join(output[succ][0]);
        }
        res
    } else if cfg.basic_blocks[bb].successors.len() > 0 {
        let succ0 = cfg.basic_blocks[bb].successors[0];
        let mut res = output[succ0][0].clone();
        for succ in cfg.basic_blocks[bb].successors.iter().skip(1) {
            res.join(output[succ][0]);
        }
        res
    } else {
        empty
    }
}

fn transfer_forward<D: DataflowState>(
    output: &mut Vec<D>,
    instructions: &[Instruction],
) {
    for i in 0 .. instructions.len() {
        //output[i].transfer(&instructions[i], &mut output[i+1]);
        let (a, b) = output.split_at_mut(i+1);
        a[i].transfer(&instructions[i], &mut b[0]);
    }
}

fn transfer_reverse<D: DataflowState>(
    output: &mut Vec<D>,
    instructions: &[Instruction],
) {
    for i in (0 .. instructions.len()).reverse() {
        //output[i+1].transfer(&instructions[i], &mut output[i]);
        let (a, b) = output.split_at_mut(i+1);
        b[0].transfer(&instructions[i], &mut a[i]);
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

////// Analysis: Safe to resolve?
*/

trait DataflowStatePerPlace {
    fn join(&mut self, b: &Self);
    fn transfer(&self, instr: &Instruction, out: &mut Self, place: &SimplePlace);
}

////// Analysis: Initialization

struct InitializationPossibilities {
    can_be_uninit: bool,
    can_be_init: bool,
}

impl DataflowStatePerPlace for InitializationPossibilities {
    fn join(&mut self, b: &Self) {
        *self = InitializationPossibilities {
            can_be_uninit: self.can_be_uninit || b.can_be_uninit,
            can_be_init: self.can_be_init || b.can_be_init,
        };
    }

    // forward transfer
    fn transfer(&self, instr: &Instruction, place: &SimplePlace) -> Self {
        match instr {
            Instruction::MoveFrom(sp) => {
                if sp.contains(place) {
                    InitializationPossibilities {
                        can_be_uninit: self.can_be_init || self.can_be_uninit,
                        can_be_init: false,
                    }
                } else {
                    *self
                }
            }
            Instruction::Overwrite(sp) => {
                if sp.contains(place) {
                    InitializationPossibilities {
                        can_be_uninit: false,
                        can_be_init: self.can_be_init || self.can_be_uninit,
                    }
                } else {
                    *self
                }
            }
            Instruction::Mutate(sp) => {
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

    fn entry() -> Self {
        InitializationPossibilities {
            can_be_uninit: true,
            can_be_init: false,
        }
    }
}

////// Analysis: Resolve

struct ResolveSafety {
    can_resolve: bool,
}

impl DataflowStatePerPlace for ResolveSafety {
    fn join(&mut self, b: &Self) {
        *self = ResolveSafety {
            can_resolve: self.can_resolve && b.can_resolve,
        }
    }

    // backward transfer
    fn transfer(&self, instr: &Instruction, place: &SimplePlace) -> Self {
        match instr {
            Instruction::MoveFrom(sp) => {
                if sp.intersects(place) {
                    ResolveSafety { can_resolve: false }
                } else {
                    *self
                }
            }
            Instruction::Overwrite(sp) => {
                if sp.contains_and_not_separated_by_deref(place) {
                    ResolveSafety { can_resolve: true }
                } else if sp.intersects(place) {
                    ResolveSafety { can_resolve: false }
                } else {
                    *self
                }
            }
            Instruction::Mutate(sp) => {
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

    fn exit(place: &Place) -> Self {
        ResolveSafety { can_resolve: !place.has_deref() }
    }
}
