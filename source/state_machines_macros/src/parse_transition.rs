use crate::ast::{SpecialOp, Transition, TransitionKind, TransitionParam, TransitionStmt};
use syn::spanned::Spanned;
use proc_macro2::Span;
use syn::{
    Block, Error, Expr, ExprCall, ExprIf, FnArg, ImplItemMethod, Local, Pat, PatIdent, Signature,
    Stmt, Ident,
};

// Translate Rust AST into an SM AST, given by a TransitionStmt.
// Every statement should be one of:
//  * A special call, e.g., require(...);
//  * A 'let' statement
//  * A conditional
// We translate each statement appropriately. Some Rust Exprs will be put into the
// SM AST as-is.

pub struct Ctxt {
    pub kind: TransitionKind,
}

pub fn parse_impl_item_method(iim: &ImplItemMethod, ctxt: &Ctxt) -> syn::parse::Result<Transition> {
    let params = parse_sig(&iim.sig)?;
    let body = parse_block(&iim.block, ctxt)?;
    let name = iim.sig.ident.clone();
    return Ok(Transition { kind: ctxt.kind, params, body, name });
}

fn parse_sig(sig: &Signature) -> syn::parse::Result<Vec<TransitionParam>> {
    if sig.generics.params.len() > 0 {
        return Err(Error::new(sig.span(), "transition expected no type arguments"));
    }
    if sig.inputs.len() == 0 {
        return Err(Error::new(sig.span(), "transition expected self as first argument"));
    }
    match sig.inputs[0] {
        FnArg::Receiver(_) => {}
        _ => {
            return Err(Error::new(
                sig.inputs[0].span(),
                "transition expected self as first argument",
            ));
        }
    }

    let mut v = Vec::new();
    for i in 1..sig.inputs.len() {
        let t = &sig.inputs[i];
        let (ident, ty) = match t {
            FnArg::Receiver(_) => {
                return Err(Error::new(t.span(), "invalid param"));
            }
            FnArg::Typed(pat) => match &*pat.pat {
                Pat::Ident(pat_ident) => (pat_ident.ident.clone(), (*pat.ty).clone()),
                _ => {
                    return Err(Error::new(t.span(), "invalid param"));
                }
            },
        };
        v.push(TransitionParam { ident, ty });
    }
    return Ok(v);
}

struct TLet(Span, Ident, Expr);

enum StmtOrLet {
    Stmt(TransitionStmt),
    Let(TLet),
}

fn parse_block(block: &Block, ctxt: &Ctxt) -> syn::parse::Result<TransitionStmt> {
    let mut tstmts = Vec::new();
    for stmt in block.stmts.iter() {
        let tstmt = parse_stmt(stmt, ctxt)?;
        tstmts.push(tstmt);
    }

    let mut cur_block = Vec::new();
    for stmt_or_let in tstmts.into_iter().rev() {
        match stmt_or_let {
            StmtOrLet::Stmt(s) => cur_block.push(s),
            StmtOrLet::Let(TLet(span, id, e)) => {
                cur_block = vec![
                    TransitionStmt::Let(span, id, e, Box::new(
                        TransitionStmt::Block(span, cur_block.into_iter().rev().collect())
                    ))
                ];
            }
        }
    }

    return Ok(TransitionStmt::Block(block.span(), cur_block.into_iter().rev().collect()));
}

fn parse_stmt(stmt: &Stmt, ctxt: &Ctxt) -> syn::parse::Result<StmtOrLet> {
    match stmt {
        Stmt::Local(local) => Ok(StmtOrLet::Let(parse_local(local, ctxt)?)),
        Stmt::Expr(expr) => Ok(StmtOrLet::Stmt(parse_expr(expr, ctxt)?)),
        Stmt::Semi(expr, _) => Ok(StmtOrLet::Stmt(parse_expr(expr, ctxt)?)),
        _ => {
            return Err(Error::new(stmt.span(), "unsupported statement type in state transition"));
        }
    }
}

fn parse_local(local: &Local, _ctxt: &Ctxt) -> syn::parse::Result<TLet> {
    let ident = match &local.pat {
        Pat::Ident(PatIdent { attrs: _, by_ref: None, mutability: None, ident, subpat: None }) => {
            ident.clone()
        }
        _ => {
            return Err(Error::new(local.span(), "unsupported Local statement type in state transition"));
        }
    };
    let e = match &local.init {
        Some((_eq, e)) => (**e).clone(),
        None => {
            return Err(Error::new(local.span(), "'let' statement must have initializer in state transition"));
        }
    };
    Ok(TLet(local.span(), ident, e))
}

fn parse_expr(expr: &Expr, ctxt: &Ctxt) -> syn::parse::Result<TransitionStmt> {
    match expr {
        Expr::If(expr_if) => parse_expr_if(expr_if, ctxt),
        Expr::Block(block) => parse_block(&block.block, ctxt),
        Expr::Call(call) => parse_call(call, ctxt),
        _ => {
            return Err(Error::new(expr.span(), "unsupported expression type in state transition"));
        }
    }
}

fn parse_expr_if(expr_if: &ExprIf, ctxt: &Ctxt) -> syn::parse::Result<TransitionStmt> {
    let thn = parse_block(&expr_if.then_branch, ctxt)?;
    let els = match &expr_if.else_branch {
        Some((_, el)) => parse_expr(el, ctxt)?,
        None => TransitionStmt::Block(expr_if.span(), Vec::new()),
    };
    match &*expr_if.cond {
        Expr::Let(..) => {
            return Err(Error::new(expr_if.cond.span(), "unsupported if-let conditional in state transition"));
        }
        _ => { }
    }
    return Ok(TransitionStmt::If(
        expr_if.span(),
        (*expr_if.cond).clone(),
        Box::new(thn),
        Box::new(els),
    ));
}

enum CallType {
    Assert,
    Require,
    Update,
    Initialize,
    AddElement,
    HaveElement,
    RemoveElement,
    AddSome,
    HaveSome,
    RemoveSome,
    WithdrawSome,
    DepositSome,
    GuardSome,
}

fn parse_call(call: &ExprCall, ctxt: &Ctxt) -> syn::parse::Result<TransitionStmt> {
    let ct = parse_call_type(&call.func, ctxt)?;
    match &ct {
        CallType::Assert => {
            if call.args.len() != 1 {
                return Err(Error::new(call.span(), "assert expected 1 arguments"));
            }
            let e = call.args[0].clone();
            return Ok(TransitionStmt::Assert(call.span(), e));
        }
        CallType::Require => {
            if call.args.len() != 1 {
                return Err(Error::new(call.span(), "require expected 1 arguments"));
            }
            let e = call.args[0].clone();
            return Ok(TransitionStmt::Require(call.span(), e));
        }
        CallType::Update
        | CallType::Initialize
        | CallType::HaveSome
        | CallType::AddSome
        | CallType::RemoveSome
        | CallType::GuardSome
        | CallType::DepositSome
        | CallType::WithdrawSome
        | CallType::HaveElement
        | CallType::AddElement
        | CallType::RemoveElement => {
            if call.args.len() != 2 {
                return Err(Error::new(call.span(), "expected 2 arguments"));
            }
            let ident = match &call.args[0] {
                Expr::Path(path) => {
                    match &path.qself {
                        Some(qself) => {
                            return Err(Error::new(qself.lt_token.span(), "expected field name"));
                        }
                        None => {}
                    }

                    match path.path.get_ident() {
                        Some(ident) => ident.clone(),
                        None => {
                            return Err(Error::new(call.args[0].span(), "expected field name"));
                        }
                    }
                }
                _ => {
                    return Err(Error::new(call.args[0].span(), "expected field name"));
                }
            };
            let e = call.args[1].clone();
            return match ct {
                CallType::Update => Ok(TransitionStmt::Update(call.span(), ident.clone(), e)),
                CallType::Initialize => {
                    Ok(TransitionStmt::Initialize(call.span(), ident.clone(), e))
                }
                CallType::HaveElement => Ok(TransitionStmt::Special(
                    call.span(),
                    ident.clone(),
                    SpecialOp::HaveElement(e),
                )),
                CallType::AddElement => Ok(TransitionStmt::Special(
                    call.span(),
                    ident.clone(),
                    SpecialOp::AddElement(e),
                )),
                CallType::RemoveElement => Ok(TransitionStmt::Special(
                    call.span(),
                    ident.clone(),
                    SpecialOp::RemoveElement(e),
                )),
                CallType::HaveSome => {
                    Ok(TransitionStmt::Special(call.span(), ident.clone(), SpecialOp::HaveSome(e)))
                }
                CallType::AddSome => {
                    Ok(TransitionStmt::Special(call.span(), ident.clone(), SpecialOp::AddSome(e)))
                }
                CallType::RemoveSome => Ok(TransitionStmt::Special(
                    call.span(),
                    ident.clone(),
                    SpecialOp::RemoveSome(e),
                )),
                CallType::GuardSome => {
                    Ok(TransitionStmt::Special(call.span(), ident.clone(), SpecialOp::GuardSome(e)))
                }
                CallType::DepositSome => Ok(TransitionStmt::Special(
                    call.span(),
                    ident.clone(),
                    SpecialOp::DepositSome(e),
                )),
                CallType::WithdrawSome => Ok(TransitionStmt::Special(
                    call.span(),
                    ident.clone(),
                    SpecialOp::WithdrawSome(e),
                )),
                _ => {
                    panic!("shouldn't get here");
                }
            };
        }
    }
}

fn parse_call_type(callf: &Expr, _ctxt: &Ctxt) -> syn::parse::Result<CallType> {
    match callf {
        Expr::Path(path) => {
            match &path.qself {
                Some(qself) => {
                    return Err(Error::new(
                        qself.lt_token.span(),
                        "unexpected token for transition op",
                    ));
                }
                None => {}
            }

            if path.path.is_ident("assert") {
                return Ok(CallType::Assert);
            }
            if path.path.is_ident("require") {
                return Ok(CallType::Require);
            }
            if path.path.is_ident("update") {
                return Ok(CallType::Update);
            }
            if path.path.is_ident("init") {
                return Ok(CallType::Initialize);
            }
            if path.path.is_ident("add_element") {
                return Ok(CallType::AddElement);
            }
            if path.path.is_ident("remove_element") {
                return Ok(CallType::RemoveElement);
            }
            if path.path.is_ident("have_element") {
                return Ok(CallType::HaveElement);
            }
            if path.path.is_ident("add_some") {
                return Ok(CallType::AddSome);
            }
            if path.path.is_ident("remove_some") {
                return Ok(CallType::RemoveSome);
            }
            if path.path.is_ident("have_some") {
                return Ok(CallType::HaveSome);
            }
            if path.path.is_ident("deposit_some") {
                return Ok(CallType::DepositSome);
            }
            if path.path.is_ident("withdraw_some") {
                return Ok(CallType::WithdrawSome);
            }
            if path.path.is_ident("guard_some") {
                return Ok(CallType::GuardSome);
            }
        }
        _ => {
            return Err(Error::new(callf.span(), "expected a valid command"));
        }
    }

    return Err(Error::new(callf.span(), "expected a valid command"));
}
