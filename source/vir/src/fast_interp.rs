
enum Value {
    Bool(bool),
    Int(BigInt),
    Ctor(u32, Vec<Value>),
    Symbol(u32),
}

enum Op {
    Binary { op: BinaryOp },
    PushValue(Value),
    PushMove(Offset),
    Pop(u32),
    Move { src: Offset, dst: Offset },
    Call { fn_id: FnId },
    Return,
    ConditionalJmp { op_idx: u32 }, 
    Jmp { op_idx: u32 }, 
}

enum PreOp {
    Binary { op: BinaryOp },
    PushValue(Value),
    PushMove(Offset),
    Pop(u32),
    Move { src: Offset, dst: Offset },
    Call { fn_id: FnId },
    Return,
    ConditionalJmp { true_label: LabelId, false_label: LabelId }, 
    Jmp { label: LabelId }, 
    Label(u32),
}

enum Procedure {
    Exp(Exp),
    Fun(Fun),
    Closure(Vec<UniqueIdent>, Vec<UniqueIdent>, Exp),
}

struct InterpreterCtx {
    fun_to_proc_idx: HashMap<Fun, usize>,
    procs: Vec<Procedure>, 
    proc_offsets: Vec<u32>,

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

    fn do_ternary(&mut self, ternary_op: TernaryOp) {
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

                let lbl_thn_body = state.mk_label();
                let lbl_done_true = state.mk_label();
                let lbl_els_normal = state.mk_label();
                let lbl_els_body = state.mk_label();
                let lbl_done = state.mk_label();
                let lbl_dummy = lbl_done_true;

                state.push_exp(cond);
                state.jmp_conditional(1, lbl_thn_body, lbl_els_normal, lbl_thn_body);

                state.set_label(lbl_thn_body);
                state.push_exp(thn);
                state.jmp_conditional(2, lbl_done_true, lbl_dummy, lbl_els_body);

                state.set_label(lbl_done_true);
                state.push_value(Value::Bool(false));
                state.jmp(lbl_done);

                state.set_label(lbl_els_normal);
                state.frame_size -= 2;
                state.push_value(Value::Bool(false));

                state.set_label(lbl_els_body);
                state.push_exp(els);

                state.set_label(lbl_done):
                state.do_ternary(TernaryOp::IfThenElse);
            }
            ExpX::Binary(BinaryOp::Or | BinaryOp::And | BinaryOp::Implies, lhs, rhs) => {
                // Short-circuiting binary ops. Again we need to account for symbolic values

                // push_exp lhs
                // negate the value if it's ==>
                // jmp (-1) [ true -> done, false -> do_rhs, symbolic -> do_rhs ]
                //      (possibly swap arguments depending on what kind of short circuiting)
                // do_rhs:
                //   push_exp rhs
                //   binary_op
                // done:

                let lbl_do_rhs = state.mk_label();
                let lbl_done = state.mk_label();

                state.push_exp(lhs);

                if op == BinaryOp::Implies {
                    state.do_unary(UnaryOp::Not);
                }
                // From here on out, treat ==> as an OR
                let is_and = (op == BinaryOp::And);

                if is_and {
                    state.jmp_conditional(1, lbl_do_rhs, lbl_done, lbl_do_rhs);
                } else {
                    state.jmp_conditional(1, lbl_done, lbl_do_rhs, lbl_do_rhs);
                }

                state.set_label(lbl_do_rhs);
                state.push_exp(rhs);
                state.do_binary(if is_and { BinaryOp::And } else { BinaryOp::Or });
                state.set_label(lbl_done);
            }
            ExpX::BinaryOp(bop, lhs, rhs) => {
                state.push_exp(lhs);
                state.push_exp(rhs);
                state.do_binary(bop);
            }
            ExpX::BinaryOpr(BinaryOpr::ExtEq(true | false, _typ)) => {
                state.push_exp(lhs);
                state.push_exp(rhs);
                state.do_binary(BinaryOp::Eq(Mode::Spec));
            }
            ExpX::UnaryOp(UnaryOp::Not, e) => {
                state.push_exp(e);
                state.do_unary(IUnaryOp::Not);
            }
            ExpX::UnaryOp(UnaryOp::BitNot, e) => {
                state.push_exp(e);
                state.do_unary(IUnaryOp::BitNot);
            }
            ExpX::UnaryOp(UnaryOp::Trigger(_) | UnaryOp::CoerceMode { .. }, e) => {
                state.push_exp(e);
            }

            ExpX::UnaryOpr(UnaryOp::Box(_) | UnaryOp::Unbox(_) | UnaryOp::, e) => {
                state.push_exp(e);
            }
            ExpX::CallLambda(_, closure, args) => {
                state.push_exp(closure);
                for arg in args.iter() {
                    state.push_exp(arg);
                }
                state.dyn_call(args.len() + 1);
            }
            ExpX::Call(call_fun, _typs, args) => {
                for arg in args.iter() {
                    state.push_exp(arg);
                }

                let call_type = get_call_type(call_fun);
                match call_type {
                    CallType::Fun(fun, cached) => {
                        let proc_id = state.get_proc_id(fun);
                        if cached {
                            state.normal_call(proc_id);
                        } else {
                            state.cached_call(proc_id, args.len());
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

                    self.move(1, binders.len() + 1);
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
            ExpX::Ctor(path, variant, binders) {
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
                self.move(0, self.frame_size);
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
                self.move(0, self.frame_size);
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

        state.ctx.push(Procedure::Exp(e.clone()));
        let i = state.ctx.procs.len() - 1;
        while i < state.ctx.procs.len() {
            let res = state.compile_procedure(&state.ctx.procs[i]);
            i += 1;
        }
    }
}
