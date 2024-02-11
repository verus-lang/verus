
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

struct State {
    frame_size: u32,
    var_locs: HashMap<UniqueIdent, u32>,

    ops: Vec<Op>,
}

fn push_expr(e: &Exp, state: &mut State) {
    match &e.x {
        ExpX::Const(Constant::Bool(b)) => {
            state.ops.push(Op::PushValue(Value::Bool(b)));
            state.frame_size += 1;
        }
        ExpX::Const(Constant::Int(i)) => {
            state.ops.push(Op::PushValue(Value::Int(i)));
            state.frame_size += 1;
        }
        ExpX::Var(uid) => {
            let src = state.get_offset(uid);
            state.ops.push(Op::PushMove(src));
            state.frame_size += 1;
        }
        ExpX::If(cond, thn, els) => {
            // This is more complex than it seems like it ought to be because of
            // the possibility that `cond` evaluates symbolically.

            // push_expr cond
            // jmp (-1) [true -> thn_body, false -> els_normal, _ -> thn_body ]
            // thn_body:
            //   push_expr thn
            //   jmp (-2) [ true -> done_true, false -> ?, _ -> els_body ]
            // els_normal:
            //   push_value false /* dummy value */
            // els_body:
            //   push_expr els
            //   jmp (-3) [ true -> ?, false -> done_false, _ -> done_symbolic ]
            // done_symbolic:
            //   ternary_op IfThenElse
            //   jmp finished
            // done_true:
            //   move (-1) --> (-2)
            //   pop 1
            //   jmp finished
            // done_false:
            //   move (-1) --> (-3)
            //   pop 2
            // finished:

            let lbl_thn_body = state.mk_label();
            let lbl_els_normal = state.mk_label();
            let lbl_els_body = state.mk_label();
            let lbl_done_symbolic = state.mk_label();
            let lbl_done_true = state.mk_label();
            let lbl_done_false = state.mk_label();
            let lbl_finished = state.mk_label();
            let lbl_dummy = lbl_thn_body;

            state.push_expr(cond);
            state.jmp_conditional(1, lbl_thn_body, lbl_els_normal, lbl_thn_body);

            state.set_label(lbl_thn_body);
            state.push_expr(thn);
            state.jmp_conditional(2, lbl_done_true, lbl_dummy, lbl_els_body);

            state.set_label(lbl_els_normal);
            state.frame_size -= 1;
            state.push_value(Value::Bool(false));

            state.set_label(lbl_els_body);
            state.push_expr(els);
            state.jmp_conditional(3, lbl_dummy, lbl_done_false, lbl_done_symbolic);

            state.set_label(lbl_done_symbolic):
            state.do_ternary(TernaryOp::IfThenElse);
            state.jmp(lbl_finished);

            state.set_label(lbl_done_true):
            state.frame_size += 1;
            state.move(1, 2);
            state.pop(1);
            state.jmp(lbl_finished);

            state.set_label(lbl_done_false):
            state.frame_size += 2;
            state.move(1, 3);
            state.pop(2);

            state.set_label(lbl_finished);
        }
        ExpX::Binary(BinaryOp::Or, lhs, rhs) => {
        }
        ExpX::Binary(BinaryOp::Xor | BinaryOp::Eq(_) | BinaryOp::Ne | BinaryOp::Inequality(_) | BinaryOp::Arith(_, _) | BinaryOp::Bitwise(_, _), lhs, rhs) => {
            state.push_expr(lhs);
            state.push_expr(rhs);
            state.ops.push(Op::Binary { op: bop });
            state.frame_size -= 1;
        }
        ExpX::Call
    }
}
