use num_bigint::BigInt;
use std::rc::Rc;
use crate::ast::{BinaryOp, BinaryOpr, UnaryOp, UnaryOpr, IntegerTypeBoundKind, Fun, Constant, Mode, FieldOpr};
use crate::sst::{Exp, ExpX, UniqueIdent, BndX, CallFun};
use std::collections::HashMap;
use air::scope_map::ScopeMap;
use crate::context::Ctx;
use crate::func_to_air::{SstMap};
use std::convert::TryFrom;
use std::convert::TryInto;
use crate::ast_util::get_variant_and_idx;


enum Value {
    Bool(bool),
    Int(BigInt),
    Ctor(u32, Rc<Vec<Value>>),
    Symbol(u32),
}

enum CallFrame {
    Call { return_addr: u32, memoize: Option<Vec<Value>> },
}

type Offset = u32;
struct ProcId(usize);
struct LabelId(usize);

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

enum IUnaryOp {
    Not,
    BitNot,
    IntegerTypeBound(IntegerTypeBoundKind),
    IsVariant(u32),
    GetField(u32, u32),
}

enum ITernaryOp {
    IfThenElse,
}

enum Procedure {
    Exp(Exp),
    Fun(Fun),
    Closure(Vec<UniqueIdent>, Vec<UniqueIdent>, Exp),
}

struct InterpreterConfig {
    make_opaque: Vec<Fun>,
}

struct InterpreterCtx {
    fun_to_proc_idx: HashMap<Fun, ProcId>,
    procs: Vec<Procedure>, 
    proc_addresses: Vec<u32>,

    ops: Vec<Op>,
}

struct ModuleLevelInterpreterCtx {
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
    var_locs: ScopeMap<UniqueIdent, Var>,
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
        self.pre_ops.push(PreOp::Move { src, dst });
    }

    fn pop(&mut self, n: u32) {
        self.pre_ops.push(PreOp::Pop(n));
    }

    fn mk_label(&mut self) -> LabelId {
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
        self.frame_size -= offset_of_closure;
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
                self.interp_ctx.procs.push(Procedure::Fun(fun.clone()));
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
            ExpX::Var(uid) => {
                match self.var_locs.get(uid).unwrap() {
                    Var::Symbol(sym) => {
                        todo!();
                    }
                    Var::InStack(idx) => {
                        self.push_move(self.frame_size - idx);
                    }
                }
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

                let lbl_thn_body = self.mk_label();
                let lbl_done_true = self.mk_label();
                let lbl_els_normal = self.mk_label();
                let lbl_els_body = self.mk_label();
                let lbl_done = self.mk_label();
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

                let lbl_do_rhs = self.mk_label();
                let lbl_done = self.mk_label();

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
            ExpX::Unary(UnaryOp::BitNot, e) => {
                self.push_exp(e);
                self.do_unary(IUnaryOp::BitNot);
            }
            ExpX::Unary(UnaryOp::Trigger(_) | UnaryOp::CoerceMode { .. }, e) => {
                self.push_exp(e);
            }
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
                            self.normal_call(proc_id, args.len());
                        } else {
                            self.cached_call(proc_id, args.len());
                        }
                    }
                    CallType::Uninterp => {
                        todo!();
                    }
                }
            }
            ExpX::Bind(bnd, body) => match &bnd.x {
                BndX::Let(binders) => {
                    self.var_locs.push_scope(false);
                    for binder in binders.iter() {
                        self.push_exp(&binder.a);
                        let uid = UniqueIdent { name: binder.name.clone(),
                            local: None };
                        self.var_locs.insert(uid,
                            Var::InStack(self.frame_size - 1));
                    }
                    self.push_exp(body);
                    self.var_locs.pop_scope();

                    self.do_move(1, (binders.len() + 1).try_into().unwrap());
                    self.pop(binders.len().try_into().unwrap());
                }
                BndX::Lambda(binders, _triggers) => {
                    // use e here, not body, to make sure
                    // the lambda params don't get counted
                    let free_vars = get_free_vars(e);

                    let mut captured_vars = vec![];
                    for fv in free_vars {
                        match self.var_locs.get(&fv).unwrap() {
                            Var::Symbol(_) => { }
                            Var::InStack(i) => {
                                captured_vars.push(fv);
                                self.push_move(self.frame_size - i);
                            }
                        }
                    }
                    let params = binders.iter().map(|t| UniqueIdent { name: t.name.clone(), local: None }).collect();

                    let proc_id = ProcId(self.interp_ctx.procs.len().try_into().unwrap());
                    self.interp_ctx.procs.push(Procedure::Closure(
                        captured_vars, params, body.clone()));

                    self.build_closure(proc_id, captured_vars.len());
                }
            }
            ExpX::Ctor(path, variant, binders) => {
                let (variant, idx) = get_variant_and_idx(&self.ctx.global.datatypes[path].1, variant);
                let fields = variant.fields;
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

        match procedure {
            Procedure::Exp(exp) => {
                let free_vars = get_free_vars(exp);
                let symbol = 0;
                for fv in free_vars.into_iter() {
                    self.var_locs.insert(fv, Var::Symbol(symbol));
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
                    let uid = UniqueIdent { name: p.x.name.clone(), local: None };
                    self.var_locs.insert(uid, Var::InStack(i));
                }

                self.push_exp(&fun_sst.body);
                self.do_move(0, self.frame_size);
                self.pop(self.frame_size - 1);
                self.do_return();
            }
            Procedure::Closure(captured, params, body) => {
                // The closure itself is the first parameter, so
                // the stack starts with (closure, param1, param2, ...)
                self.frame_size = (params.len() + 1).try_into().unwrap();
                for (i, p) in params.iter().enumerate() {
                    let idx = (i + 1).try_into().unwrap();
                    self.var_locs.insert(p.clone(), Var::InStack(idx));
                }

                // Start by unpacking the closure so that our stack looks like
                // (closure, param1, param2, ..., captured1, captured2, ...)
                for (i, captured_var) in captured.iter().enumerate() {
                    self.var_locs.insert(captured_var.clone(), Var::InStack(self.frame_size));
                    self.push_move(self.frame_size);
                    self.do_unary(IUnaryOp::GetField(0, i.try_into().unwrap()));
                }

                self.push_exp(body);
                self.do_move(0, self.frame_size);
                self.pop(self.frame_size - 1);
                self.do_return();
            }
        }
    }

    fn get_call_type(&self, fun: &CallFun) -> CallType {
        todo!();
    }
}

fn get_free_vars(e: &Exp) -> Vec<UniqueIdent> {
    todo!();
}

impl InterpreterCtx {
    fn compile(&mut self, ctx: &Ctx, fun_ssts: &SstMap, e: &Exp) {
        let state = State {
            interp_ctx: self,
            fun_ssts,
            ctx,
            frame_size: 0,
            var_locs: ScopeMap::new(),
            pre_ops: vec![],
            next_label_id: 0,
        };

        state.interp_ctx.procs.push(Procedure::Exp(e.clone()));
        let first_proc = state.interp_ctx.procs.len() - 1;
        let mut i = state.interp_ctx.procs.len() - 1;
        let mut pre_ops_lists = vec![];
        while i < state.interp_ctx.procs.len() {
            let res = state.compile_procedure(&state.interp_ctx.procs[i]);
            i += 1;

            let pre_ops = std::mem::take(&mut state.pre_ops);
            pre_ops_lists.push(pre_ops);
        }

        let mut label_map = HashMap::<usize, u32>::new();
        let mut current_address: u32 = self.ops.len().try_into().unwrap();
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
    }

    fn run(&self, proc_id: ProcId) -> Value {
        let instr_ptr = self.proc_addresses[proc_id.0];
        let stack: Vec<Value> = Vec::with_capacity(1000);
        let call_stack: Vec<CallFrame> = Vec::with_capacity(1000);
        let memoize_cache = HashMap::<(u32, Vec<Value>), Value>::new();

        loop {
            match &self.ops[instr_ptr] {
                Op::Unary(op) => {
                    exec_unary(&mut stack[stack.len() - 1], op);
                }
                Op::Binary(op) => {
                    let rhs = stack.pop();
                    exec_binary(&mut stack[stack.len() - 1], rhs, op);
                }
                Op::Ternary(op) => {
                    let r3 = stack.pop();
                    let r2 = stack.pop();
                    exec_ternary(&mut stack[stack.len() - 1], r2, r3, op);
                }
                Op::PushValue(value) => {
                    stack.push(value.clone());
                }
                Op::PushMove(offset) => {
                    let v = stack[stack.len() - offset].clone();
                    stack.push(v);
                }
                Op::Pop(n) => {
                    stack.truncate(stack.len() - n);
                }
                Op::Move { src, dst } => {
                    let v = stack[stack.len() - src].clone();
                    stack[stack.len() - dst] = v;
                }
                Op::Call { addr } => {
                    call_stack.push(CallFrame::Call { return_addr: instr_ptr + 1, memoize: None });
                    instr_ptr = addr;
                    continue;
                }
                Op::MemoizedCall { addr, n_args } => {
                    let args = stack[stack.len() - n_args ..].to_vec();
                    let key = (addr, args);
                    match memoize_cache.get(&key) {
                        Some(ret) => {
                            stack.truncate(stack.len() - n_args);
                            stack.push(ret.clone());
                        }
                        None => {
                            call_stack.push(CallFrame::Call { return_addr: instr_ptr + 1, memoize: Some(key) });
                            instr_ptr = addr;
                            continue;
                        }
                    }
                    todo!();
                }
                Op::DynCall { closure } => {
                    if let Value::Ctor(addr, _) = stack[stack.len() - closure] {
                        call_stack.push(CallFrame::Call { return_addr: instr_ptr + 1, memoize: None });
                        instr_ptr = addr;
                        continue;
                    } else {
                        todo!();
                    }
                }
                Op::BuiltCtor { variant, n_fields } => {
                    let vs = stack.drain(stack.len() - n_fields ..).collect();
                    let v = Value::Ctor(variant, Rc::new(vs));
                    stack.push(v);
                }
                Op::Return => {
                    if call_stack.len() == 0 {
                        break;
                    }
                    let frame = call_stack.pop();
                    match frame {
                        CallFrame::Call { return_addr, memoize } => {
                            if let Some(key) = memoize {
                                memoize_cache.insert(key, stack[stack.len() - 1].clone());
                            }
                            instr_ptr = return_addr;
                            continue;
                        }
                    }
                }
                Op::Jmp { addr } => {
                    instr_ptr = addr;
                    continue;
                }
                Op::ConditionalJmp { offset, true_addr, false_addr, other_addr } => {
                    let v = &stack[stack.len() - offset];
                    instr_ptr = match v {
                        Value::Bool(false) => false_addr,
                        Value::Bool(true) => true_addr,
                        _ => other_addr,
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
