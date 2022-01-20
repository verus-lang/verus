#![allow(unused_imports)]

use proc_macro2::TokenStream;
use syn::parse::{Parse, ParseStream};
use syn::{ImplItemMethod, braced, Ident, Error, FieldsNamed, Expr, Type, Meta, NestedMeta, Attribute, AttrStyle, MetaList, FnArg, Receiver, Stmt, Pat, Signature, Block, Local, ExprIf, ExprCall, ExprPath, PathArguments, PathSegment, Path, ExprField, Member};
use syn::punctuated::Punctuated;
use syn::token::{Colon2, Dot};
use syn::buffer::Cursor;
use proc_macro2::Span;
use quote::quote_spanned;
use syn::spanned::Spanned;
use smir::ast::{SM, Invariant, Lemma, LemmaPurpose, Transition, TransitionKind, TransitionStmt, Extras, ShardableType, Arg, Field};

pub struct Ctxt {
    //pub fields: &'a Vec<smir::ast::Field<Ident, Type>>,
    pub kind: TransitionKind,
}

pub fn parse_impl_item_method(iim: &mut ImplItemMethod, ctxt: &Ctxt) ->
    syn::parse::Result<Transition<Ident, Expr, Type>>
{
    let args = parse_sig(&iim.sig)?;
    let body = parse_block(&mut iim.block, ctxt)?;
    return Ok(Transition { kind: ctxt.kind, args, body });
}

fn parse_sig(sig: &Signature) -> syn::parse::Result<Vec<Arg<Ident, Type>>> {
    if sig.generics.params.len() > 0 {
        return Err(Error::new(sig.span(), "transition expected no type arguments"));
    }
    if sig.inputs.len() == 0 {
        return Err(Error::new(sig.span(), "transition expected self as first argument"));
    }
    match sig.inputs[0] {
        FnArg::Receiver(_) => { }
        _ => {
            return Err(Error::new(sig.inputs[0].span(), "transition expected self as first argument"));
        }
    }

    let mut v = Vec::new();
    for i in 1 .. sig.inputs.len() {
        let t = &sig.inputs[i];
        let (ident, ty) = match t {
            FnArg::Receiver(_) => {
                return Err(Error::new(t.span(), "invalid param"));
            }
            FnArg::Typed(pat) => {
                match &*pat.pat {
                    Pat::Ident(pat_ident) => (pat_ident.ident.clone(), (*pat.ty).clone()),
                    _ => {
                        return Err(Error::new(t.span(), "invalid param"));
                    }
                }
            }
        };
        v.push(Arg { ident, ty });
    }
    return Ok(v);
}

fn parse_block(block: &mut Block, ctxt: &Ctxt) -> syn::parse::Result<TransitionStmt<Ident, Expr>> {
    let mut tstmts = Vec::new();
    for mut stmt in block.stmts.iter_mut() {
        let tstmt = parse_stmt(&mut stmt, ctxt)?;
        tstmts.push(tstmt);
    }
    return Ok(TransitionStmt::Block(tstmts));
}

fn parse_stmt(stmt: &mut Stmt, ctxt: &Ctxt) -> syn::parse::Result<TransitionStmt<Ident, Expr>> {
    match stmt {
        Stmt::Local(local) => parse_local(local, ctxt),
        Stmt::Expr(expr) => parse_expr(expr, ctxt),
        Stmt::Semi(expr, _) => parse_expr(expr, ctxt),
        _ => {
            println!("stmt: {:#?}", stmt);
            return Err(Error::new(stmt.span(), "unsupported statement type"));
        }
    }
}

fn parse_local(_local: &mut Local, _ctxt: &Ctxt) -> syn::parse::Result<TransitionStmt<Ident, Expr>> {
    panic!("parse_local unimplemented");
}

fn parse_expr(expr: &mut Expr, ctxt: &Ctxt) -> syn::parse::Result<TransitionStmt<Ident, Expr>> {
    match expr {
        Expr::If(expr_if) => parse_expr_if(expr_if, ctxt),
        Expr::Block(block) => parse_block(&mut block.block, ctxt),
        Expr::Call(call) => parse_call(call, ctxt),
        _ => {
            return Err(Error::new(expr.span(), "unsupported expression type"));
        }
    }
}

fn parse_expr_if(expr_if: &mut ExprIf, ctxt: &Ctxt) -> syn::parse::Result<TransitionStmt<Ident, Expr>> {
    let thn = parse_block(&mut expr_if.then_branch, ctxt)?;
    let els = match &mut expr_if.else_branch {
        Some((_, el)) => parse_expr(&mut *el, ctxt)?,
        None => TransitionStmt::Block(Vec::new()),
    };
    return Ok(TransitionStmt::If((*expr_if.cond).clone(), Box::new(thn), Box::new(els)));
}

enum CallType { Assert, Require, Update }

fn parse_call(call: &mut ExprCall, ctxt: &Ctxt) -> syn::parse::Result<TransitionStmt<Ident, Expr>> {
    let ct = parse_call_type(&call.func, ctxt)?;
    match ct {
        CallType::Assert => {
            if call.args.len() != 1 {
                return Err(Error::new(call.span(), "assert expected 1 arguments"));
            }
            call.func = Box::new(mk_builtin_path("assert", call.func.span()));
            let e = call.args[0].clone();
            return Ok(TransitionStmt::Assert(e));
        }
        CallType::Require => {
            if call.args.len() != 1 {
                return Err(Error::new(call.span(), "require expected 1 arguments"));
            }
            let e = call.args[0].clone();
            call.func = Box::new(mk_builtin_path("require", call.func.span()));
            return Ok(TransitionStmt::Assert(e));
        }
        CallType::Update => {
            if call.args.len() != 2 {
                return Err(Error::new(call.span(), "update expected 1 arguments"));
            }
            let ident = match &call.args[0] {
                Expr::Path(path) => {
                    match &path.qself {
                        Some(qself) => {
                            return Err(Error::new(qself.lt_token.span(), "expected field name"));
                        }
                        None => { }
                    }

                    match path.path.get_ident() {
                        Some(ident) => {
                            ident.clone()
                        }
                        None => {
                            return Err(Error::new(call.args[0].span(), "expected field name"));
                        }
                    }
                }
                _ => {
                    return Err(Error::new(call.args[0].span(), "expected field name"));
                }
            };
            call.func = Box::new(mk_builtin_path("update", call.func.span()));
            call.args[0] = mk_self_field(ident.clone(), call.args[0].span());
            let e = call.args[1].clone();
            return Ok(TransitionStmt::Update(ident.clone(), e));
        }
    }
}

fn parse_call_type(callf: &Expr, _ctxt: &Ctxt) -> syn::parse::Result<CallType> {
    match callf {
        Expr::Path(path) => {
            match &path.qself {
                Some(qself) => {
                  return Err(Error::new(qself.lt_token.span(), "unexpected token for transition op"));
                }
                None => { }
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
        }
        _ => {
            return Err(Error::new(callf.span(), "expected 'require', 'assert', or 'update'"));
        }
    }

    return Err(Error::new(callf.span(), "expected 'require', 'assert', or 'update'"));
}

fn mk_builtin_path(s: &str, sp: Span) -> Expr {
    let mut segments = Punctuated::<PathSegment, Colon2>::new();
    segments.push(PathSegment {
        ident: Ident::new("builtin", sp),
        arguments: PathArguments::None,
    });
    segments.push(PathSegment {
        ident: Ident::new("state_machine_ops", sp),
        arguments: PathArguments::None,
    });
    segments.push(PathSegment {
        ident: Ident::new(s, sp),
        arguments: PathArguments::None,
    });
    return Expr::Path(
        ExprPath {
            attrs: Vec::new(),
            qself: None,
            path: Path {
                leading_colon: Some(Colon2 { spans: [sp, sp] }),
                segments: segments,
            },
        },
    );
}

fn mk_self_field(ident: Ident, sp: Span) -> Expr {
    let mut self_segments = Punctuated::<PathSegment, Colon2>::new();
    self_segments.push(PathSegment {
        ident: Ident::new("self", sp),
        arguments: PathArguments::None,
    });
    return Expr::Field(
        ExprField {
            attrs: Vec::new(),
            base: Box::new(
                Expr::Path(
                    ExprPath {
                        attrs: Vec::new(),
                        qself: None,
                        path: Path {
                            leading_colon: None,
                            segments: self_segments,
                        },
                    },
                )
            ),
            dot_token: Dot { spans: [sp] },
            member: Member::Named(ident),
        }
    );
}
