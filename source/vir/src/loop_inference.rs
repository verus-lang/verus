use crate::ast::{NullaryOpr, SpannedTyped, Typ, TypX, UnaryOp};
use crate::messages::{Message, Span};
use crate::sst::{Exp, ExpX, UniqueIdent};
use std::sync::Arc;

pub(crate) fn make_option_exp(opt: Option<Exp>, span: &Span, typ: &Typ) -> Exp {
    let option_path = crate::def::option_type_path();
    let option_typx =
        TypX::Datatype(option_path.clone(), Arc::new(vec![typ.clone()]), Arc::new(vec![]));
    let expx = match opt {
        None => ExpX::Ctor(option_path.clone(), Arc::new("None".to_string()), Arc::new(vec![])),
        Some(exp) => {
            let field_id = crate::def::positional_field_ident(0);
            let field = air::ast_util::ident_binder(&field_id, &exp);
            let fields = Arc::new(vec![field]);
            ExpX::Ctor(option_path.clone(), Arc::new("Some".to_string()), fields)
        }
    };
    SpannedTyped::new(span, &Arc::new(option_typx), expx)
}

// InferSpecForLoopIter produces None if any variables in the express are modified in the loop
fn vars_unmodified(
    modified_vars: &Arc<Vec<UniqueIdent>>,
    exp: &Exp,
    print_hint: bool,
    hint_message: &mut Option<Message>,
) -> bool {
    let mut map = air::scope_map::ScopeMap::new();
    let r = crate::sst_visitor::exp_visitor_check(exp, &mut map, &mut |e: &Exp, _| match &e.x {
        ExpX::Var(x) => {
            if modified_vars.contains(x) {
                if print_hint && hint_message.is_none() {
                    let msg = "hint: because the iterator uses a variable that may be mutated \
                        inside the loop, \
                        Verus did not add an automatic loop invariant about the iterator. \
                        You may need to (1) write a manual loop invariant about the iterator, \
                        or (2) store the loop expression in a variable outside the loop, \
                        or (3) use a while loop. \
                        For example, change `for i in 0..x { ... }` to \
                        (1): `for i in iter: 0..x invariant iter.end == 10 { ... }` or \
                        (2): `let n = x; for i in 0..n invariant n == 10 { ... }`";
                    *hint_message = Some(crate::messages::note(&e.span.clone(), msg));
                }
                Err(())
            } else {
                Ok(())
            }
        }
        ExpX::NullaryOpr(NullaryOpr::NoInferSpecForLoopIter) => {
            if print_hint && hint_message.is_none() {
                let msg = "hint: because the iterator is an exec-only value (not a spec value), \
                    Verus did not add an automatic loop invariant about the iterator. \
                    You may need to (1) write a manual loop invariant about the iterator, \
                    or (2) store the loop expression in a variable outside the loop, \
                    or (3) use a while loop. \
                    For example, change `for i in 0..f() { ... }` to \
                    (1) `for i in iter: 0..f() invariant iter.end == 10 { ... }` or \
                    (2): `let n = f(); for i in 0..n invariant n == 10 { ... }`.";
                *hint_message = Some(crate::messages::note(&e.span.clone(), msg));
            }
            Err(())
        }
        _ => Ok(()),
    });
    match r {
        Ok(()) => true,
        Err(()) => false,
    }
}

pub(crate) fn finalize_inv(
    modified_vars: &Arc<Vec<UniqueIdent>>,
    exp: &Exp,
    hint_message: &mut Option<Message>,
) -> Exp {
    crate::sst_visitor::map_exp_visitor(exp, &mut |e: &Exp| {
        match &e.x {
            ExpX::Unary(UnaryOp::InferSpecForLoopIter { print_hint }, e_infer) => {
                if vars_unmodified(modified_vars, e_infer, *print_hint, hint_message) {
                    // promote to Some(e)
                    make_option_exp(Some(e_infer.clone()), &e.span, &e.typ)
                } else {
                    // otherwise, leave as-is to be removed by sst_to_air
                    e.clone()
                }
            }
            _ => e.clone(),
        }
    })
}
