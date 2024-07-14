#![allow(unused_imports)]
#![allow(dead_code)]
use num_bigint::BigInt;
use std::rc::Rc;
use crate::ast::{BinaryOp, BinaryOpr, UnaryOp, UnaryOpr, IntegerTypeBoundKind, Fun, Constant, Mode, FieldOpr, IntegerTypeBitwidth, VarIdent, VirErr, IntRange, ArchWordBits};
use crate::sst::{Exp, ExpX, BndX, CallFun};
use std::collections::HashMap;
use air::scope_map::ScopeMap;
use crate::context::Ctx;
use crate::ast_to_sst_func::{SstMap};
use std::convert::TryFrom;
use std::convert::TryInto;
use crate::ast_util::get_variant_and_idx;
use crate::sst_util::free_vars_exp;
use crate::interpreter::SyntacticEquality;
use std::ops::ControlFlow;
use num_traits::identities::Zero;
use num_traits::{Euclid, One, ToPrimitive, FromPrimitive};
use crate::messages::{Message, warning};
use crate::unicode::valid_unicode_scalar_bigint;
use crate::ast_to_sst_func::SstInfo;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum Value {
    Bool(bool),
    Int(BigInt),
    Ctor(u32, Rc<Vec<Value>>),

    Symbol(u32),
    Unsimplified(Rc<Unsimplified>),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum Unsimplified {
    UnaryOp(IUnaryOp, Value),
    BinaryOp(BinaryOp, Value, Value),
    TernaryOp(ITernaryOp, Value, Value, Value),
}

enum CallFrame {
    Call { return_addr: u32, memoize: Option<(u32, Vec<Value>)> },
}

type Offset = u32;

#[derive(Clone, Copy)]
struct ProcId(usize);

#[derive(Clone, Copy)]
struct LabelId(usize);

#[derive(Debug)]
enum Op {
    Unary(IUnaryOp),
    Binary(BinaryOp),
    Ternary(ITernaryOp),
    PushValue(Value),
    PushMove(Offset),
    Pop(u32),
    Move { src: Offset, dst: Offset },
    Call { addr: u32 },
    MemoizedCall { addr: u32, n_args: u32 },
    DynCall { closure: Offset },
    BuildCtor { variant: u32, n_fields: u32 },
    Return,
    ConditionalJmp { offset: u32, true_addr: u32, false_addr: u32, other_addr: u32 }, 
    Jmp { addr: u32 }, 
}

enum PreOp {
    Unary(IUnaryOp),
    Binary(BinaryOp),
    Ternary(ITernaryOp),
    PushValue(Value),
    PushMove(Offset),
    Pop(u32),
    Move { src: Offset, dst: Offset },
    Call { proc_id: ProcId },
    MemoizedCall { proc_id: ProcId, n_args: u32 },
    DynCall { closure: Offset },
    Return,
    BuildClosure { proc_id: ProcId, n_captures: u32 },
    BuildCtor { variant: u32, n_fields: u32 },
    ConditionalJmp { offset: u32, true_label: LabelId, false_label: LabelId, other_label: LabelId }, 
    Jmp { label: LabelId }, 
    Label(LabelId),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum IUnaryOp {
    Not,
    BitNot(Option<IntegerTypeBitwidth>),
    IntegerTypeBound(IntegerTypeBoundKind),
    IsVariant(u32),
    GetField(u32, u32),
    GetFieldAnyVariant(u32),
    Clip(IntRange),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum ITernaryOp {
    IfThenElse,
}

enum Procedure {
    Exp(Exp),
    Fun(Fun),
    Closure(Vec<VarIdent>, Vec<VarIdent>, Exp),
}

#[derive(Clone, Hash, PartialEq, Eq)]
pub struct InterpreterConfig {
    pub make_opaque: Vec<Fun>,
}

pub struct InterpreterCtx {
    fun_to_proc_idx: HashMap<Fun, ProcId>,
    procs: Vec<Rc<Procedure>>, 
    proc_addresses: Vec<u32>,

    ops: Vec<Op>,
}

pub struct ModuleLevelInterpreterCtx {
    ctxs: HashMap<InterpreterConfig, InterpreterCtx>,
}

enum Var {
    Symbol(u32),
    InStack(u32),
}

enum CallType {
    Fun(Fun, bool),
    Uninterp,
}

struct State<'a> {
    interp_ctx: &'a mut InterpreterCtx,
    ctx: &'a Ctx,
    fun_ssts: &'a SstMap,

    frame_size: u32,
    var_locs: ScopeMap<VarIdent, Var>,
    pre_ops: Vec<PreOp>,
    next_label_id: usize,
}

impl<'a> State<'a> {
    fn push_value(&mut self, v: Value) {
        self.pre_ops.push(PreOp::PushValue(v));
        self.frame_size += 1;
    }

    fn push_value_default(&mut self) {
        self.push_value(Value::Bool(false));
    }

    fn push_move(&mut self, offset: Offset) {
        self.pre_ops.push(PreOp::PushMove(offset));
        self.frame_size += 1;
    }

    fn do_move(&mut self, src: Offset, dst: Offset) {
        if src != dst {
            self.pre_ops.push(PreOp::Move { src, dst });
        }
    }

    fn do_pop(&mut self, n: u32) {
        if n > 0 {
            self.pre_ops.push(PreOp::Pop(n));
            self.frame_size -= n;
        }
    }

    fn fresh_label(&mut self) -> LabelId {
        let next = self.next_label_id;
        self.next_label_id += 1;
        LabelId(next)
    }

    fn set_label(&mut self, label_id: LabelId) {
        self.pre_ops.push(PreOp::Label(label_id));
    }

    fn do_unary(&mut self, unary_op: IUnaryOp) {
        self.pre_ops.push(PreOp::Unary(unary_op));
    }

    fn do_binary(&mut self, binary_op: BinaryOp) {
        self.pre_ops.push(PreOp::Binary(binary_op));
        self.frame_size -= 1;
    }

    fn do_ternary(&mut self, ternary_op: ITernaryOp) {
        self.pre_ops.push(PreOp::Ternary(ternary_op));
        self.frame_size -= 2;
    }

    fn do_return(&mut self) {
        self.pre_ops.push(PreOp::Return);
    }

    /// Caller is responsible for adjusting self.frame_size
    fn jmp(&mut self, label_id: LabelId) {
        self.pre_ops.push(PreOp::Jmp { label: label_id });
    }

    /// Caller is responsible for adjusting self.frame_size
    fn jmp_conditional(&mut self, offset: u32, true_label: LabelId, false_label: LabelId, other_label: LabelId) {
        self.pre_ops.push(PreOp::ConditionalJmp { offset, true_label, false_label, other_label });
    }

    fn dyn_call(&mut self, offset_of_closure: u32) {
        // offset should be 1 more than the # of args
        // e.g., if there are 2 args, then the closure is in the 3rd-to-last slot
        self.pre_ops.push(PreOp::DynCall { closure: offset_of_closure });
        self.frame_size -= offset_of_closure - 1;
    }

    fn normal_call(&mut self, proc_id: ProcId, n_args: usize) {
        let n_args: u32 = n_args.try_into().unwrap();
        self.pre_ops.push(PreOp::Call { proc_id });
        self.frame_size = self.frame_size + 1 - n_args;
    }

    fn cached_call(&mut self, proc_id: ProcId, n_args: usize) {
        let n_args = n_args.try_into().unwrap();
        self.pre_ops.push(PreOp::MemoizedCall { proc_id, n_args });
        self.frame_size = self.frame_size + 1 - n_args;
    }

    fn build_closure(&mut self, proc_id: ProcId, n_captures: usize) {
        let n_captures = n_captures.try_into().unwrap();
        self.pre_ops.push(PreOp::BuildClosure { proc_id, n_captures });
        self.frame_size = self.frame_size + 1 - n_captures;
    }

    fn build_ctor(&mut self, variant: u32, n_fields: usize) {
        let n_fields = n_fields.try_into().unwrap();
        self.pre_ops.push(PreOp::BuildCtor { variant, n_fields });
        self.frame_size = self.frame_size + 1 - n_fields;
    }

    fn get_proc_id_inserting_if_necessary(&mut self, fun: &Fun) -> ProcId {
        match self.interp_ctx.fun_to_proc_idx.get(fun) {
            Some(proc_id) => *proc_id,
            None => {
                let proc_id = ProcId(self.interp_ctx.procs.len());
                self.interp_ctx.procs.push(Rc::new(Procedure::Fun(fun.clone())));
                self.interp_ctx.fun_to_proc_idx.insert(fun.clone(), proc_id);
                proc_id
            }
        }
    }

    fn push_exp(&mut self, e: &Exp) {
        match &e.x {
            ExpX::Const(Constant::Bool(b)) => {
                self.push_value(Value::Bool(*b));
            }
            ExpX::Const(Constant::Int(i)) => {
                self.push_value(Value::Int(i.clone()));
            }
            ExpX::Const(_) => todo!(),
            ExpX::Var(uid) => {
                match self.var_locs.get(uid).unwrap() {
                    Var::Symbol(_sym) => {
                        todo!();
                    }
                    Var::InStack(idx) => {
                        self.push_move(self.frame_size - idx);
                    }
                }
            }
            ExpX::VarLoc(..) => todo!(),
            ExpX::VarAt(..) => todo!(),
            ExpX::StaticVar(..) => todo!(),
            ExpX::Old(..) => todo!(),
            ExpX::Loc(..) => todo!(),
            ExpX::ExecFnByName(..) => todo!(),
            ExpX::Interp(..) => todo!(),
            ExpX::FuelConst(..) => panic!("FuelConst not expected here"),
            ExpX::WithTriggers(_trigs, exp) => {
                self.push_exp(exp);
            }
            ExpX::If(cond, thn, els) => {
                // This is more complex than it seems like it ought to be because of
                // the possibility that `cond` evaluates symbolically,
                // but we still want to short-circuit in the common case.

                // push_exp cond
                // jmp (-1) [true -> thn_body, false -> els_normal, _ -> thn_body ]
                // thn_body:
                //   push_exp thn
                //   jmp (-2) [ true -> done_true, false -> ?, _ -> els_body ]
                // done_true:
                //   push_value false /* dummy value */
                //   jmp done
                // els_normal:
                //   push_value false /* dummy value */
                // els_body:
                //   push_exp els
                // done:
                //   ternarny_op IfThenElse

                let lbl_thn_body = self.fresh_label();
                let lbl_done_true = self.fresh_label();
                let lbl_els_normal = self.fresh_label();
                let lbl_els_body = self.fresh_label();
                let lbl_done = self.fresh_label();
                let lbl_dummy = lbl_done_true;

                self.push_exp(cond);
                self.jmp_conditional(1, lbl_thn_body, lbl_els_normal, lbl_thn_body);

                self.set_label(lbl_thn_body);
                self.push_exp(thn);
                self.jmp_conditional(2, lbl_done_true, lbl_dummy, lbl_els_body);

                self.set_label(lbl_done_true);
                self.push_value_default();
                self.jmp(lbl_done);

                self.set_label(lbl_els_normal);
                self.frame_size -= 2;
                self.push_value_default();

                self.set_label(lbl_els_body);
                self.push_exp(els);

                self.set_label(lbl_done);
                self.do_ternary(ITernaryOp::IfThenElse);
            }
            ExpX::Binary(op @ (BinaryOp::Or | BinaryOp::And | BinaryOp::Implies), lhs, rhs) => {
                // Short-circuiting binary ops. Again we need to account for symbolic values

                // push_exp lhs
                // negate the value if it's ==>
                // jmp (-1) [ true -> done, false -> do_rhs, symbolic -> do_rhs ]
                //      (possibly swap arguments depending on what kind of short circuiting)
                // do_rhs:
                //   push_exp rhs
                //   binary_op
                // done:

                let lbl_do_rhs = self.fresh_label();
                let lbl_done = self.fresh_label();

                self.push_exp(lhs);

                if op == &BinaryOp::Implies {
                    self.do_unary(IUnaryOp::Not);
                }
                // From here on out, treat ==> as an OR
                let is_and = op == &BinaryOp::And;

                if is_and {
                    self.jmp_conditional(1, lbl_do_rhs, lbl_done, lbl_do_rhs);
                } else {
                    self.jmp_conditional(1, lbl_done, lbl_do_rhs, lbl_do_rhs);
                }

                self.set_label(lbl_do_rhs);
                self.push_exp(rhs);
                self.do_binary(if is_and { BinaryOp::And } else { BinaryOp::Or });
                self.set_label(lbl_done);
            }
            ExpX::Binary(bop, lhs, rhs) => {
                self.push_exp(lhs);
                self.push_exp(rhs);
                self.do_binary(*bop);
            }
            ExpX::BinaryOpr(BinaryOpr::ExtEq(true | false, _typ), lhs, rhs) => {
                self.push_exp(lhs);
                self.push_exp(rhs);
                self.do_binary(BinaryOp::Eq(Mode::Spec));
            }
            ExpX::Unary(UnaryOp::Not, e) => {
                self.push_exp(e);
                self.do_unary(IUnaryOp::Not);
            }
            ExpX::Unary(UnaryOp::BitNot(x), e) => {
                self.push_exp(e);
                self.do_unary(IUnaryOp::BitNot(*x));
            }
            ExpX::Unary(UnaryOp::Trigger(_) | UnaryOp::CoerceMode { .. }, e) => {
                self.push_exp(e);
            }
            ExpX::Unary(UnaryOp::Clip { range, truncate: _ }, e) => {
                self.push_exp(e);
                if !matches!(range, IntRange::Int) {
                    self.do_unary(IUnaryOp::Clip(*range))
                }
            }
            ExpX::Unary(UnaryOp::HeightTrigger, _e) => todo!(),
            ExpX::Unary(UnaryOp::StrLen, _e) => todo!(),
            ExpX::Unary(UnaryOp::StrIsAscii, _e) => todo!(),
            ExpX::Unary(UnaryOp::MustBeFinalized, _e) => panic!("MustBeFinalized unexpected"),
            ExpX::Unary(UnaryOp::InferSpecForLoopIter { .. }, _e) => todo!(),
            ExpX::Unary(UnaryOp::CastToInteger, _e) => todo!(),
            ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_) | UnaryOpr::CustomErr(_), e) => {
                self.push_exp(e);
            }
            ExpX::UnaryOpr(UnaryOpr::HasType(_) | UnaryOpr::TupleField { .. }, _) => unreachable!(),
            ExpX::UnaryOpr(UnaryOpr::IsVariant { datatype, variant }, e) => {
                let (_variant, idx) = get_variant_and_idx(&self.ctx.global.datatypes[datatype].1, variant);
                self.push_exp(e);
                let idx = u32::try_from(idx).unwrap();
                self.do_unary(IUnaryOp::IsVariant(idx));
            }
            ExpX::UnaryOpr(UnaryOpr::Field(FieldOpr { datatype, variant, field, .. }), e) => {
                let (variant, idx) = get_variant_and_idx(&self.ctx.global.datatypes[datatype].1, variant);
                let field_idx = variant.fields.iter().position(|f| &f.name == field).unwrap();

                let idx = u32::try_from(idx).unwrap();
                let field_idx = u32::try_from(field_idx).unwrap();

                self.push_exp(e);
                self.do_unary(IUnaryOp::GetField(idx, field_idx));
            }
            ExpX::UnaryOpr(UnaryOpr::IntegerTypeBound(kind, _mode), e) => {
                self.push_exp(e);
                self.do_unary(IUnaryOp::IntegerTypeBound(*kind));
            }
            ExpX::NullaryOpr(..) => todo!(),
            ExpX::CallLambda(_, closure, args) => {
                self.push_exp(closure);
                for arg in args.iter() {
                    self.push_exp(arg);
                }
                self.dyn_call(u32::try_from(args.len() + 1).unwrap());
            }
            ExpX::Call(call_fun, _typs, args) => {
                for arg in args.iter() {
                    self.push_exp(arg);
                }

                let call_type = self.get_call_type(call_fun);
                match call_type {
                    CallType::Fun(fun, cached) => {
                        let proc_id = self.get_proc_id_inserting_if_necessary(&fun);
                        if cached {
                            self.cached_call(proc_id, args.len());
                        } else {
                            self.normal_call(proc_id, args.len());
                        }
                    }
                    CallType::Uninterp => {
                        dbg!(call_fun);
                        todo!();
                    }
                }
            }
            ExpX::Bind(bnd, body) => match &bnd.x {
                BndX::Let(binders) => {
                    let mut v = vec![];
                    for binder in binders.iter() {
                        self.push_exp(&binder.a);
                        let uid = binder.name.clone();
                        v.push((uid, Var::InStack(self.frame_size - 1)));
                    }

                    self.var_locs.push_scope(false);
                    for (uid, var) in v.into_iter() {
                        self.var_locs.insert(uid, var).unwrap();
                    }

                    self.push_exp(body);

                    self.var_locs.pop_scope();

                    self.do_move(1, (binders.len() + 1).try_into().unwrap());
                    self.do_pop(binders.len().try_into().unwrap());
                }
                BndX::Lambda(binders, _triggers) => {
                    // use e here, not body, to make sure
                    // the lambda params don't get counted
                    let free_vars = free_vars_exp(e);

                    let mut captured_vars = vec![];
                    for (fv, _typ) in free_vars.iter() {
                        match self.var_locs.get(&fv).unwrap() {
                            Var::Symbol(_) => { }
                            Var::InStack(i) => {
                                captured_vars.push(fv.clone());
                                self.push_move(self.frame_size - i);
                            }
                        }
                    }
                    let num_captured_vars = captured_vars.len();
                    let params = binders.iter().map(|t| t.name.clone()).collect();

                    let proc_id = ProcId(self.interp_ctx.procs.len().try_into().unwrap());
                    self.interp_ctx.procs.push(Rc::new(Procedure::Closure(
                        captured_vars, params, body.clone())));

                    self.build_closure(proc_id, num_captured_vars);
                }
                BndX::Quant(..) => todo!(),
                BndX::Choose(..) => todo!(),
            }
            ExpX::Ctor(path, variant, binders) => {
                let (variant, idx) = get_variant_and_idx(&self.ctx.global.datatypes[path].1, variant);
                let fields = &variant.fields;
                for f in fields.iter() {
                    let e = &crate::ast_util::get_field(binders, &f.name).a;
                    self.push_exp(e);
                }
                self.build_ctor(idx.try_into().unwrap(), fields.len());
            }
        }
    }

    fn compile_procedure(&mut self, procedure: &Procedure) {
        self.frame_size = 0;
        self.var_locs = ScopeMap::new();
        self.var_locs.push_scope(false);

        match procedure {
            Procedure::Exp(exp) => {
                let free_vars = free_vars_exp(exp);
                let mut symbol = 0;
                for (fv, _typ) in free_vars.into_iter() {
                    self.var_locs.insert(fv, Var::Symbol(symbol)).unwrap();
                    symbol += 1;
                }
                self.push_exp(exp);
                self.do_return();
            }
            Procedure::Fun(fun) => {
                let function = self.ctx.func_map.get(fun).unwrap();
                let fun_sst = self.fun_ssts.borrow().get(fun).unwrap();

                self.frame_size = function.x.params.len().try_into().unwrap();
                for (i, p) in function.x.params.iter().enumerate() {
                    let i = i.try_into().unwrap();
                    let uid = p.x.name.clone();
                    self.var_locs.insert(uid, Var::InStack(i)).unwrap();
                }

                self.push_exp(&fun_sst.body);
                self.do_move(1, self.frame_size);
                self.do_pop(self.frame_size - 1);
                self.do_return();
            }
            Procedure::Closure(captured, params, body) => {
                // The closure itself is the first parameter, so
                // the stack starts with (closure, param1, param2, ...)
                self.frame_size = (params.len() + 1).try_into().unwrap();
                for (i, p) in params.iter().enumerate() {
                    let idx = (i + 1).try_into().unwrap();
                    self.var_locs.insert(p.clone(), Var::InStack(idx)).unwrap();
                }

                // Start by unpacking the closure so that our stack looks like
                // (closure, param1, param2, ..., captured1, captured2, ...)
                for (i, captured_var) in captured.iter().enumerate() {
                    self.var_locs.insert(captured_var.clone(), Var::InStack(self.frame_size)).unwrap();
                    self.push_move(self.frame_size);
                    self.do_unary(IUnaryOp::GetFieldAnyVariant(i.try_into().unwrap()));
                }

                self.push_exp(body);
                self.do_move(1, self.frame_size);
                self.do_pop(self.frame_size - 1);
                self.do_return();
            }
        }
    }

    fn get_call_type(&self, call_fun: &CallFun) -> CallType {
        let fun = match call_fun {
            CallFun::Fun(fun, None) => fun,
            CallFun::Fun(_fun, Some((fun, _typs))) => fun,
            CallFun::Recursive(..) => { return CallType::Uninterp; }
            CallFun::InternalFun(..) => { return CallType::Uninterp; }
        };
        let fun_ssts = self.fun_ssts.borrow();
        match fun_ssts.get(fun) {
            None => {
                CallType::Uninterp
            }
            Some(SstInfo { params: _, body: _, memoize, inline: _ }) => {
                CallType::Fun(fun.clone(), *memoize)
            }
        }
    }
}

impl InterpreterCtx {
    fn compile(&mut self, ctx: &Ctx, fun_ssts: &SstMap, e: &Exp) -> ProcId {
        let mut state = State {
            interp_ctx: self,
            fun_ssts,
            ctx,
            frame_size: 0,
            var_locs: ScopeMap::new(),
            pre_ops: vec![],
            next_label_id: 0,
        };

        state.interp_ctx.procs.push(Rc::new(Procedure::Exp(e.clone())));
        let mut i = state.interp_ctx.procs.len() - 1;
        let my_proc_id = ProcId(i);
        let mut pre_ops_lists = vec![];
        while i < state.interp_ctx.procs.len() {
            state.compile_procedure(&state.interp_ctx.procs[i].clone());
            i += 1;

            let pre_ops = std::mem::take(&mut state.pre_ops);
            pre_ops_lists.push(pre_ops);
        }

        let mut label_map = HashMap::<usize, u32>::new();
        let mut current_address: u32 = state.interp_ctx.ops.len().try_into().unwrap();
        for pre_ops in pre_ops_lists.iter() {
            state.interp_ctx.proc_addresses.push(current_address);
            for pre_op in pre_ops.iter() {
                if let PreOp::Label(label_id) = pre_op {
                    assert!(!label_map.contains_key(&label_id.0));
                    label_map.insert(label_id.0, current_address);
                } else {
                    current_address += 1;
                }
            }
        }
        for pre_ops in pre_ops_lists.into_iter() {
            for pre_op in pre_ops.into_iter() {
                let op = match pre_op {
                    PreOp::Unary(op) => Op::Unary(op),
                    PreOp::Binary(op) => Op::Binary(op),
                    PreOp::Ternary(op) => Op::Ternary(op),
                    PreOp::PushValue(value) => Op::PushValue(value),
                    PreOp::PushMove(offset) => Op::PushMove(offset),
                    PreOp::Pop(n) => Op::Pop(n),
                    PreOp::Move { src, dst } => Op::Move { src, dst },
                    PreOp::Call { proc_id } =>
                        Op::Call { addr: self.proc_addresses[proc_id.0] },
                    PreOp::MemoizedCall { proc_id, n_args } =>
                        Op::MemoizedCall { addr: self.proc_addresses[proc_id.0], n_args: n_args },
                    PreOp::DynCall { closure } => Op::DynCall { closure },
                    PreOp::Return => Op::Return,
                    PreOp::BuildClosure { proc_id, n_captures } => {
                        Op::BuildCtor { variant: self.proc_addresses[proc_id.0],
                            n_fields: n_captures }
                    }
                    PreOp::BuildCtor { variant, n_fields } => {
                        Op::BuildCtor { variant, n_fields }
                    }
                    PreOp::ConditionalJmp { offset, true_label, false_label, other_label } => {
                        Op::ConditionalJmp {
                            offset: offset,
                            true_addr: *label_map.get(&true_label.0).unwrap(),
                            false_addr: *label_map.get(&false_label.0).unwrap(),
                            other_addr: *label_map.get(&other_label.0).unwrap(),
                        }
                    }
                    PreOp::Jmp { label } => {
                        Op::Jmp {
                            addr: *label_map.get(&label.0).unwrap(),
                        } 
                    }
                    PreOp::Label(_) => { continue; }
                };
                self.ops.push(op);
            }
        }

        my_proc_id
    }

    fn run(&self, proc_id: ProcId, ctx: &Ctx) -> Value {
        let mut instr_ptr = self.proc_addresses[proc_id.0];
        let mut stack: Vec<Value> = Vec::with_capacity(1000);
        let mut call_stack: Vec<CallFrame> = Vec::with_capacity(1000);
        let mut memoize_cache = HashMap::<(u32, Vec<Value>), Value>::new();
        let mut msgs: Vec<Message> = vec![];

        loop {
            match &self.ops[instr_ptr as usize] {
                Op::Unary(op) => {
                    let idx = stack.len() - 1;
                    exec_unary(&mut stack[idx], op, ctx, &mut msgs);
                }
                Op::Binary(op) => {
                    let rhs = stack.pop().unwrap();
                    let idx = stack.len() - 1;
                    exec_binary(&mut stack[idx], rhs, op, ctx);
                }
                Op::Ternary(op) => {
                    let r3 = stack.pop().unwrap();
                    let r2 = stack.pop().unwrap();
                    let idx = stack.len() - 1;
                    exec_ternary(&mut stack[idx], r2, r3, op);
                }
                Op::PushValue(value) => {
                    stack.push(value.clone());
                }
                Op::PushMove(offset) => {
                    let v = stack[stack.len() - *offset as usize].clone();
                    stack.push(v);
                }
                Op::Pop(n) => {
                    stack.truncate(stack.len() - *n as usize);
                }
                Op::Move { src, dst } => {
                    let v = stack[stack.len() - *src as usize].clone();
                    let idx = stack.len() - *dst as usize;
                    stack[idx] = v;
                }
                Op::Call { addr } => {
                    call_stack.push(CallFrame::Call { return_addr: instr_ptr + 1, memoize: None });
                    instr_ptr = *addr;
                    continue;
                }
                Op::MemoizedCall { addr, n_args } => {
                    let args = stack[stack.len() - *n_args as usize ..].to_vec();
                    let key = (*addr, args);
                    println!("memoize call");
                    match memoize_cache.get(&key) {
                        Some(ret) => {
                            stack.truncate(stack.len() - *n_args as usize);
                            stack.push(ret.clone());
                        }
                        None => {
                            call_stack.push(CallFrame::Call { return_addr: instr_ptr + 1, memoize: Some(key) });
                            instr_ptr = *addr;
                            continue;
                        }
                    }
                    todo!();
                }
                Op::DynCall { closure } => {
                    if let Value::Ctor(addr, _) = &stack[stack.len() - *closure as usize] {
                        call_stack.push(CallFrame::Call { return_addr: instr_ptr + 1, memoize: None });
                        instr_ptr = *addr;
                        continue;
                    } else {
                        todo!();
                    }
                }
                Op::BuildCtor { variant, n_fields } => {
                    let vs = stack.drain(stack.len() - *n_fields as usize ..).collect();
                    let v = Value::Ctor(*variant, Rc::new(vs));
                    stack.push(v);
                }
                Op::Return => {
                    if call_stack.len() == 0 {
                        break;
                    }
                    let frame = call_stack.pop().unwrap();
                    match frame {
                        CallFrame::Call { return_addr, memoize } => {
                            if let Some(key) = memoize {
                                println!("memoize");
                                memoize_cache.insert(key, stack[stack.len() - 1].clone());
                            }
                            instr_ptr = return_addr;
                            continue;
                        }
                    }
                }
                Op::Jmp { addr } => {
                    instr_ptr = *addr;
                    continue;
                }
                Op::ConditionalJmp { offset, true_addr, false_addr, other_addr } => {
                    let v = &stack[stack.len() - *offset as usize];
                    instr_ptr = match v {
                        Value::Bool(false) => *false_addr,
                        Value::Bool(true) => *true_addr,
                        _ => *other_addr,
                    };
                    continue;
                }
            }

            instr_ptr += 1;
        }

        assert!(stack.len() == 1);
        return stack[0].clone();
    }
}

fn exec_unary(val: &mut Value, op: &IUnaryOp, ctx: &Ctx, msgs: &mut Vec<Message>) {
    let no_eval = || Value::Unsimplified(Rc::new(Unsimplified::UnaryOp(*op, val.clone())));

    let v = match op {
        IUnaryOp::Not => {
            match val {
                Value::Bool(b) => Value::Bool(!*b),
                _ => no_eval(),
            }
        }
        IUnaryOp::Clip(range) => {
            match &*val {
                Value::Int(i) => {
                    let in_range = |lower: BigInt, upper: BigInt| !(i < &lower || i > &upper);
                    let apply_range = |lower: BigInt, upper: BigInt| {
                        if !in_range(lower, upper) {
                            //let msg =
                            //    "Computation clipped an integer that was out of range";
                            // msgs.push(warning(&exp.span, msg)); // TODO
                            // NOTE(tjh): I think we should consider doing the truncation
                            no_eval()
                        } else {
                            val.clone()
                        }
                    };
                    let apply_unicode_scalar_range = |msgs: &mut Vec<Message>| {
                        if !valid_unicode_scalar_bigint(i) {
                            //let msg =
                            //    "Computation clipped an integer that was out of range";
                            // msgs.push(warning(&exp.span, msg)); // TODO
                            no_eval()
                        } else {
                            val.clone()
                        }
                    };
                    match range {
                        IntRange::Int => val.clone(),
                        IntRange::Nat => apply_range(BigInt::zero(), i.clone()),
                        IntRange::Char => apply_unicode_scalar_range(msgs),
                        IntRange::U(n) => {
                            apply_range(
                                BigInt::zero(),
                                (BigInt::one() << n) - BigInt::one(),
                            )
                        }
                        IntRange::I(n) => apply_range(
                            -1 * (BigInt::one() << (n - 1)),
                            (BigInt::one() << (n - 1)) - BigInt::one(),
                        ),
                        IntRange::USize => {
                            let lower = BigInt::zero();
                            let upper = |n| (BigInt::one() << n) - BigInt::one();
                            match ctx.global.arch {
                                ArchWordBits::Either32Or64 => {
                                    if in_range(lower.clone(), upper(32)) {
                                        // then must be in range of 64 too
                                        val.clone()
                                    } else {
                                        // may or may not be in range of 64, we must conservatively give up.
                                        // TODO state.msgs.push(warning(&exp.span, "Computation clipped an arch-dependent integer that was out of range"));
                                        no_eval()
                                    }
                                }
                                ArchWordBits::Exactly(n) => apply_range(lower, upper(n)),
                            }
                        }
                        IntRange::ISize => {
                            let lower = |n| -1 * (BigInt::one() << (n - 1));
                            let upper = |n| (BigInt::one() << (n - 1)) - BigInt::one();
                            match ctx.global.arch {
                                ArchWordBits::Either32Or64 => {
                                    if in_range(lower(32), upper(32)) {
                                        // then must be in range of 64 too
                                        val.clone()
                                    } else {
                                        // may or may not be in range of 64, we must conservatively give up.
                                        // TODO state.msgs.push(warning(&exp.span, "Computation clipped an arch-dependent integer that was out of range"));
                                        no_eval()
                                    }
                                }
                                ArchWordBits::Exactly(n) => apply_range(lower(n), upper(n)),
                            }
                        }
                    }
                }
                _ => no_eval(),
            }
        }
        IUnaryOp::IntegerTypeBound(kind) => {
            // We're about to take an exponent, so bound this
            // by something reasonable.
            match &*val {
                Value::Int(i) => match i.to_u32() {
                    Some(i) if i <= 1024 => match kind {
                        IntegerTypeBoundKind::ArchWordBits => match &ctx.global.arch {
                            ArchWordBits::Exactly(b) => {
                                Value::Int(BigInt::from_u32(*b).unwrap())
                            }
                            _ => no_eval()
                        },
                        _ if i == 0 => Value::Int(BigInt::from_usize(0).unwrap()),
                        IntegerTypeBoundKind::UnsignedMax => {
                            Value::Int(BigInt::from_usize(2).unwrap().pow(i) - 1)
                        }
                        IntegerTypeBoundKind::SignedMax => {
                            Value::Int(BigInt::from_usize(2).unwrap().pow(i - 1) - 1)
                        }
                        IntegerTypeBoundKind::SignedMin => {
                            Value::Int(-BigInt::from_usize(2).unwrap().pow(i - 1))
                        }
                    },
                    _ => no_eval(),
                },
                _ => no_eval(),
            }
        }
        IUnaryOp::GetField(expected_variant_idx, field_idx) => {
            match &*val {
                Value::Ctor(variant_idx, fields) if expected_variant_idx == variant_idx => {
                    fields[*field_idx as usize].clone()
                }
                _ => no_eval()
            }
        }
        IUnaryOp::GetFieldAnyVariant(field_idx) => {
            match &*val {
                Value::Ctor(variant_idx, fields) => {
                    fields[*field_idx as usize].clone()
                }
                _ => no_eval()
            }
        }
        _ => {
            dbg!(&op);
            todo!();
        }
    };
    *val = v;
}

impl Value {
    pub fn zero() -> Self { Value::Int(BigInt::zero()) }
}

fn exec_binary(val1: &mut Value, val2: Value, op: &BinaryOp, ctx: &Ctx) {
    let no_eval = || Value::Unsimplified(Rc::new(Unsimplified::BinaryOp(*op,
        val1.clone(), val2.clone())));

    let v = match op {
        BinaryOp::Eq(_) => {
            match val1.syntactic_eq(&val2) {
                None => no_eval(),
                Some(b) => Value::Bool(b),
            }
        }
        BinaryOp::Ne => {
            match val1.syntactic_eq(&val2) {
                None => no_eval(),
                Some(b) => Value::Bool(!b),
            }
        }
        BinaryOp::And => {
            match val1 {
                Value::Bool(true) => val2.clone(),
                _ => no_eval(),
            }
        }
        BinaryOp::Or => {
            match val1 {
                Value::Bool(false) => val2.clone(),
                _ => no_eval(),
            }
        }
        BinaryOp::Inequality(op) => {
            match (&*val1, &val2) {
                (Value::Int(i1), Value::Int(i2)) => {
                    use crate::ast::InequalityOp::*;
                    let b = match op {
                        Le => i1 <= i2,
                        Ge => i1 >= i2,
                        Lt => i1 < i2,
                        Gt => i1 > i2,
                    };
                    Value::Bool(b)
                }
                _ => no_eval(),
            }
        }
        BinaryOp::Arith(op, _mode) => {
            use crate::ast::ArithOp::*;
            match (&*val1, &val2) {
                // Ideal case where both sides are concrete
                (Value::Int(i1), Value::Int(i2)) => {
                    match op {
                        Add => Value::Int(i1 + i2),
                        Sub => Value::Int(i1 - i2),
                        Mul => Value::Int(i1 * i2),
                        EuclideanDiv => {
                            if i2.is_zero() {
                                no_eval() // Treat as symbolic instead of erroring
                            } else {
                                Value::Int(i1.div_euclid(i2))
                            }
                        }
                        EuclideanMod => {
                            if i2.is_zero() {
                                no_eval() // Treat as symbolic instead of erroring
                            } else {
                                Value::Int(i1.rem_euclid(i2))
                            }
                        }
                    }
                }
                // Special cases for certain concrete values
                (Value::Int(i1), _) if i1.is_zero() && matches!(op, Add) => val2.clone(),
                (Value::Int(i1), _) if i1.is_zero() && matches!(op, Mul) => Value::zero(),
                (Value::Int(i1), _) if i1.is_one() && matches!(op, Mul) => val2.clone(),
                (_, Value::Int(i2)) if i2.is_zero() => {
                    match op {
                        Add | Sub => val1.clone(),
                        Mul => Value::zero(),
                        EuclideanDiv => no_eval(),
                        EuclideanMod => no_eval(),
                    }
                }
                (_, Value::Int(i2)) if i2.is_one() && matches!(op, EuclideanMod) => {
                    Value::zero()
                }
                (_, Value::Int(i2)) if i2.is_one() && matches!(op, Mul | EuclideanDiv) => {
                    val1.clone()
                }
                _ => {
                    match op {
                        // X - X => 0
                        Sub if val1.definitely_eq(&val2) => Value::zero(),
                        _ => no_eval(),
                    }
                }
            }
        }
        BinaryOp::Bitwise(op, _) => {
            use crate::ast::BitwiseOp::*;
            match (&*val1, &val2) {
                // Ideal case where both sides are concrete
                (Value::Int(i1), Value::Int(i2)) => match op {
                    BitXor => Value::Int(i1 ^ i2),
                    BitAnd => Value::Int(i1 & i2),
                    BitOr => Value::Int(i1 | i2),
                    Shr(_) => match i2.to_u128() {
                        None => no_eval(),
                        Some(i2) => Value::Int(i1 >> i2),
                    },
                    Shl(w, signed) => {
                        if *signed {
                            match (i1.to_i128(), i2.to_u128()) {
                                (Some(i1), Some(i2)) => {
                                    let i1_shifted =
                                        if i2 >= 128 { 0i128 } else { i1 << i2 };
                                    match crate::interpreter::i128_to_width(i1_shifted, *w, ctx.global.arch) {
                                        Some(i) => Value::Int(i),
                                        None => no_eval(),
                                    }
                                }
                                _ => no_eval(),
                            }
                        } else {
                            match (i1.to_u128(), i2.to_u128()) {
                                (Some(i1), Some(i2)) => {
                                    let i1_shifted =
                                        if i2 >= 128 { 0u128 } else { i1 << i2 };
                                    match crate::interpreter::u128_to_width(i1_shifted, *w, ctx.global.arch) {
                                        Some(i) => Value::Int(i),
                                        None => no_eval(),
                                    }
                                }
                                _ => no_eval(),
                            }
                        }
                    }
                },
                // Special cases for certain concrete values
                (Value::Int(i), _) | (_, Value::Int(i))
                    if i.is_zero() && matches!(op, BitAnd) =>
                {
                    Value::zero()
                }
                (Value::Int(i1), _) if i1.is_zero() && matches!(op, BitOr) => {
                    val2.clone()
                }
                (_, Value::Int(i2)) if i2.is_zero() && matches!(op, BitOr) => {
                    val1.clone()
                }
                _ => {
                    match op {
                        // X ^ X => 0
                        BitXor if val1.definitely_eq(&val2) => Value::zero(),
                        // X & X = X, X | X = X
                        BitAnd | BitOr if val1.definitely_eq(&val2) => val1.clone(),
                        _ => no_eval()
                    }
                }
            }
        }
        _ => {
            dbg!(&op);
            todo!();
        }
    };
    *val1 = v;
}

fn exec_ternary(val1: &mut Value, val2: Value, val3: Value, op: &ITernaryOp) {
    let no_eval = || Value::Unsimplified(Rc::new(Unsimplified::TernaryOp(*op,
        val1.clone(), val2.clone(), val3.clone())));
    let v = match op {
        ITernaryOp::IfThenElse => {
            match &*val1 {
                Value::Bool(true) => val2.clone(),
                Value::Bool(false) => val3.clone(),
                _ => no_eval(),
            }
        }
    };
    *val1 = v;
}

impl SyntacticEquality for Value {
    fn syntactic_eq(&self, other: &Self) -> Option<bool> {
        match (self, other) {
            (Value::Bool(b1), Value::Bool(b2)) => Some(b1 == b2),
            (Value::Int(i1), Value::Int(i2)) => Some(i1 == i2),
            (Value::Ctor(x1, vs1), Value::Ctor(x2, vs2)) => {
                if x1 != x2 {
                    return Some(false);
                }
                vs1.syntactic_eq(vs2)
            }
            (Value::Symbol(x), Value::Symbol(y)) => {
                if x == y {
                    Some(true)
                } else {
                    None
                }
            }
            (a, b) => {
                if a == b {
                    Some(true)
                } else {
                    None
                }
            }
        }
    }
}

impl<T: SyntacticEquality> SyntacticEquality for Rc<Vec<T>> {
    fn syntactic_eq(&self, other: &Self) -> Option<bool> {
        if self.len() != other.len() {
            Some(false)
        } else {
            let check = self.iter().zip(other.iter()).try_fold(true, |def_true, (l, r)| {
                match l.syntactic_eq(r) {
                    None => ControlFlow::Continue(false), // We still continue, since we might see a definitely false result
                    Some(false) => ControlFlow::Break(()), // Short circuit
                    Some(true) => ControlFlow::Continue(def_true),
                }
            });
            match check {
                ControlFlow::Break(_) => Some(false),
                ControlFlow::Continue(def_true) => {
                    if def_true {
                        Some(true)
                    } else {
                        None
                    }
                }
            }
        }
    }
}

impl InterpreterCtx {
    pub fn new() -> Self {
        InterpreterCtx {
            fun_to_proc_idx: HashMap::new(),
            procs: Vec::new(),
            proc_addresses: Vec::new(),
            ops: Vec::new(),
        }
    }
}

impl ModuleLevelInterpreterCtx {
    pub fn new() -> Self {
        Self { ctxs: HashMap::new() }
    }

    pub fn with_config<'a>(&'a mut self, config: &InterpreterConfig) -> &'a mut InterpreterCtx {
        if !self.ctxs.contains_key(config) {
            self.ctxs.insert(config.clone(), InterpreterCtx::new());
        }
        self.ctxs.get_mut(config).unwrap()
    }

    pub fn eval(&mut self, ctx: &Ctx, fun_ssts: &SstMap, exp: &Exp) -> Result<Exp, VirErr> {
        let config = InterpreterConfig { make_opaque: vec![] };
        let interpreter_ctx = self.with_config(&config);

        let proc_id = interpreter_ctx.compile(ctx, fun_ssts, exp);
        let ret_value = interpreter_ctx.run(proc_id, ctx);

        match ret_value {
            Value::Bool(b) => Ok(crate::sst_util::sst_bool(&exp.span, b)),
            _ => todo!(),
        }
    }
}
