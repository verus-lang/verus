use num_bigint::BigInt;
use std::rc::Rc;
use crate::ast::{BinaryOp, BinaryOpr, UnaryOp, UnaryOpr, IntegerTypeBoundKind, Fun, Constant, Mode};
use crate::sst::{Exp, ExpX, UniqueIdent};
use std::collections::HashMap;
use air::scope_map::ScopeMap;

enum Value {
    Bool(bool),
    Int(BigInt),
    Ctor(u32, Rc<Vec<Value>>),
    Symbol(u32),
}

type Offset = u32;
struct ProcId(u32);
struct LabelId(u32);

enum Op {
    Unary(IUnaryOp),
    Binary(BinaryOp),
    Ternary(ITernaryOp),
    PushValue(Value),
    PushMove(Offset),
    Pop(u32),
    Move { src: Offset, dst: Offset },
    Call { addr: u32 },
    MemoizedCall { addr: u32, n_args: usize },
    DynCall { closure: Offset },
    BuildCtor { variant: u32, n_fields: u32 },
    Return,
    ConditionalJmp { true_addr: u32, false_addr: u32, other_addr: u32 }, 
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
    BuildClosure { proc_id: ProcId, n_args: u32 },
    BuildCtor { variant: u32, n_fields: u32 },
    ConditionalJmp { true_label: LabelId, false_label: LabelId, other_label: LabelId }, 
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
    fun_to_proc_idx: HashMap<Fun, usize>,
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

struct State<'a> {
    ctx: &'a mut InterpreterCtx,

    frame_size: u32,
    var_locs: ScopeMap<UniqueIdent, Var>,
    pre_ops: Vec<PreOp>,
}

impl<'a> State<'a> {
    fn push_value(&mut self, v: Value) {
        self.pre_ops.push(PreOp::PushValue(v));
        self.frame_size += 1;
    }

    fn push_move(&mut self, offset: Offset) {
        self.pre_ops.push(PreOp::PushMove(offset));
        self.frame_size += 1;
    }

    fn mk_label(&mut self) -> LabelId {
        let next = self.next_label_id;
        self.next_label_id += 1;
        LabelId(next)
    }

    fn set_label(&mut self, label_id: LabelId) {
        self.pre_ops.push(PreOp::Label(label_id));
    }

    fn do_unary(&mut self, unary_op: UnaryOp) {
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

    /// Caller is responsible for adjusting self.frame_size
    fn jmp(&mut self, label_id: LabelId) {
        self.pre_ops.push(PreOp::Jmp(label_id));
    }

    fn push_exp(&mut self, e: &Exp) {
        match &e.x {
            ExpX::Const(Constant::Bool(b)) => {
                self.push_value(Value::Bool(b));
            }
            ExpX::Const(Constant::Int(i)) => {
                self.push_value(Value::Int(i));
            }
            ExpX::Var(uid) => {
                let src = self.get_offset(uid);
                self.push_move(src);
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
                self.do_ternary(TernaryOp::IfThenElse);
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

                if op == BinaryOp::Implies {
                    self.do_unary(UnaryOp::Not);
                }
                // From here on out, treat ==> as an OR
                let is_and = (op == BinaryOp::And);

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
            ExpX::BinaryOp(bop, lhs, rhs) => {
                self.push_exp(lhs);
                self.push_exp(rhs);
                self.do_binary(bop);
            }
            ExpX::BinaryOpr(BinaryOpr::ExtEq(true | false, _typ), lhs, rhs) => {
                self.push_exp(lhs);
                self.push_exp(rhs);
                self.do_binary(BinaryOp::Eq(Mode::Spec));
            }
            ExpX::UnaryOp(UnaryOp::Not, e) => {
                self.push_exp(e);
                self.do_unary(IUnaryOp::Not);
            }
            ExpX::UnaryOp(UnaryOp::BitNot, e) => {
                self.push_exp(e);
                self.do_unary(IUnaryOp::BitNot);
            }
            ExpX::UnaryOp(UnaryOp::Trigger(_) | UnaryOp::CoerceMode { .. } | UnaryOp::CustomErr(_), e) => {
                self.push_exp(e);
            }
            ExpX::UnaryOpr(UnaryOp::Box(_) | UnaryOp::Unbox(_), e) => {
                self.push_exp(e);
            }
            ExpX::UnaryOpr(UnaryOpr::HasType(_) | UnaryOpr::TupleField { .. }) => unreachable!(),
            ExpX::UnaryOpr(UnaryOpr::IsVariant { datatype, variant }) => {
                let (_variant, idx) = &get_variant_and_idx(&ctx.global.datatypes[path].1, variant);
                self.push_exp(e);
                self.get_is_variant(idx);
            }
            ExpX::UnaryOpr(UnaryOpr::Field(FieldOpr { datatype, variant, field, .. })) => {
                let (variant, idx) = &get_variant_and_idx(&ctx.global.datatypes[path].1, variant);
                let field_idx = variant.fields.iter().position(|f| f.name == field).unwrap();

                self.push_exp(e);
                self.get_field(idx, field_idx);
            }
            ExpX::UnaryOpr(UnaryOpr::IntegerTypeBound(kind, _mode), e) => {
                self.push_exp(e);
                self.do_unary(IUnaryOp::IntegerTypeBound(kind));
            }
            ExpX::CallLambda(_, closure, args) => {
                self.push_exp(closure);
                for arg in args.iter() {
                    self.push_exp(arg);
                }
                self.dyn_call(args.len() + 1);
            }
            ExpX::Call(call_fun, _typs, args) => {
                for arg in args.iter() {
                    self.push_exp(arg);
                }

                let call_type = get_call_type(call_fun);
                match call_type {
                    CallType::Fun(fun, cached) => {
                        let proc_id = self.get_proc_id(fun);
                        if cached {
                            self.normal_call(proc_id);
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
                    self.var_locs.push_scope();
                    for binder in binders {
                        self.push_exp(&binder.a);
                        self.var_locs.insert(binder.name.clone(),
                            Var::InStack(self.frame_size - 1));
                    }
                    self.push_exp(body);
                    self.var_locs.pop_scope();

                    self.do_move(1, binders.len() + 1);
                    self.pop(binders.len());
                }
                BndX::Lambda(binders, _triggers) => {
                    // use e here, not body, to make sure
                    // the lambda params don't get counted
                    let free_vars = get_free_vars(e);

                    let mut captured_vars = vec![];
                    for fv in free_vars {
                        match self.var_locs.get(fv).unwrap() {
                            Var::Symbol(_) => { }
                            Var::InStack(i) => {
                                captured_vars.push(fv);
                                self.push_move(self.frame_size - i);
                            }
                        }
                    }
                    let params = binders.iter().map(|t| t.name.clone()).collect();

                    let proc_id = self.ctx.procedures.len();
                    self.ctx.procedures.push(Procedure::Closure(
                        captured_vars, params, exp));

                    self.build_closure(proc_id, captured_vars.len());
                }
            }
            ExpX::Ctor(path, variant, binders) => {
                let (variant, idx) = &get_variant_and_idx(&ctx.global.datatypes[path].1, variant);
                let fields = variant.fields;
                let es = fields.iter().map(|f| get_field(binders, &f.name).a);
                for e in es.into_iter() {
                    self.push_exp(e);
                }
                self.build_ctor(idx, fields.len());
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
                for fv in free_vars.iter() {
                    self.var_locs.insert(fv, Var::Symbol(symbol));
                    symbol += 1;
                }
                self.push_exp(exp);
                self.do_return();
            }
            Procedure::Fun(fun) => {
                let function = ctx.func_map.get(fun);
                let body = fun_ssts.get(fun);

                self.frame_size = params.len();
                for (i, p) in function.x.params.iter().enumerate() {
                    self.var_locs.insert(p, Var::InStack(i));
                }

                self.push_exp(body);
                self.do_move(0, self.frame_size);
                self.pop(self.frame_size - 1);
                self.do_return();
            }
            Procedure::Closure(captured, params, body) => {
                // The closure itself is the first parameter, so
                // the stack starts with (closure, param1, param2, ...)
                self.frame_size = params.len() + 1;
                for (i, p) in params.iter().enumerate() {
                    self.var_locs.insert(p, Var::InStack(i + 1));
                }

                // Start by unpacking the closure so that our stack looks like
                // (closure, param1, param2, ..., captured1, captured2, ...)
                for (i, captured_var) in captured.iter().enumerate() {
                    self.var_locs.insert(captured_var, Var::InStack(self.frame_size));
                    self.push_move(self.frame_size);
                    self.do_unary(UnaryOp::GetField(i));
                }

                self.push_exp(body);
                self.do_move(0, self.frame_size);
                self.pop(self.frame_size - 1);
                self.do_return();
            }
        }
    }
}

impl InterpreterCtx {
    fn compile(&mut self, e: &Exp) {
        let state = State {
            ctx: self,
            frame_size: 0,
            var_locs: ScopeMap::new(),
            pre_ops: pre_ops,
            next_label_id: next_label_id,
        };

        state.ctx.procs.push(Procedure::Exp(e.clone()));
        let first_proc = state.ctx.procs.len() - 1;
        let mut i = state.ctx.procs.len() - 1;
        let mut pre_ops_lists = vec![];
        while i < state.ctx.procs.len() {
            let res = state.compile_procedure(&state.ctx.procs[i]);
            i += 1;

            let pre_ops = std::mem::take(&mut state.pre_ops);
            pre_ops_lists.push(pre_ops);
        }

        let mut label_map = HashMap::<u32, u32>::new();
        let mut current_address = self.ops.len();
        for pre_ops in pre_ops_lists.iter() {
            state.proc_addresses.push(current_address);
            for pre_op in pre_ops.iter() {
                if let PreOp::Label(label_id) = pre_op {
                    assert!(!label_map.contains_key(label_id.0));
                    label_map.insert(label_id.0, current_address);
                } else {
                    current_address += 1;
                }
            }
        }
        for pre_ops in pre_ops_lists.iter() {
            for pre_op in pre_ops.iter() {
                let op = match pre_op {
                    PreOp::Unary(op) => Op::Unary(Op),
                    PreOp::Binary(op) => Op::Binary(Op),
                    PreOp::Ternary(op) => Op::Ternary(Op),
                    PreOp::PushValue(value) => Op::PushValue(value),
                    PreOp::PushMove(offset) => Op::PushMove(offset),
                    PreOp::Pop(n) => Op::Pop(n),
                    PreOp::Move { src, dst } => Op::Move { src, dst },
                    PreOp::Call { proc_id } =>
                        Op::PreOp::Call { addr: self.proc_addresses[proc_id.0] },
                    PreOp::MemoizedCall { proc_id } =>
                        Op::PreOp::MemoizedCall { addr: self.proc_addresses[proc_id.0] },
                    PreOp::DynCall { closure } => Op::DynCall { closure },
                    PreOp::Return => Op::Return,
                    PreOp::BuildClosure { proc_id, n_args } => {
                        Op::BuildCtor { variant: self.proc_addresses[proc_id.0],
                            n_fields: n_args }
                    }
                    PreOp::BuildCtor { variant, n_fields } => {
                        Op::BuildCtor { variant, n_fields }
                    }
                    PreOp::ConditionalJmp { true_label, false_label, other_label } => {
                        Op::ConditionalJmp {
                            true_addr: *label_map.get(*true_label).unwrap(),
                            false_addr: *label_map.get(*false_label).unwrap(),
                            other_addr: *label_map.get(*other_label).unwrap(),
                        }
                    }
                    PreOp::Jmp { label } => {
                        Op::Jmp {
                            addr: *label_map.get(*label).unwrap(),
                        } 
                    }
                    PreOp::Label(_) => { continue; }
                };
                self.ops.push(op);
            }
        }
    }

    fn run(&self, proc_id: ProcId) -> Value {
        let instr_ptr = self.proc_addresses[proc_id];
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
                    call_stack.push(Call { return_addr: instr_ptr + 1, memoize: None });
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
                            call_stack.push(Call { return_addr: instr_ptr + 1, memoize: Some(key) });
                            instr_ptr = addr;
                            continue;
                        }
                    }
                    todo!();
                }
                Op::DynCall { closure } => {
                    if let Value::Ctor(addr, _) = stack[stack.len() - closure] {
                        call_stack.push(Call { return_addr: instr_ptr + 1, memoize: None });
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
                        Call { return_addr, memoize } => {
                            if let Some(key) = memoize {
                                memoize_cache.insert(key, stack[stack.len() - 1].clone());
                            }
                            instr_ptr = addr;
                            continue;
                        }
                    }
                }
                Op::Jmp { addr } => {
                    instr_ptr = addr;
                    continue;
                }
                Op::ConditionalJmp { true_addr, false_addr, other_addr } => {
                    let v = &stack[stack.len() - 1];
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
