#![allow(unused_imports)]

use syn::parse::{Parse, ParseStream};
use syn::{ImplItemMethod, braced, Ident, Error, FieldsNamed, Expr, Type, Meta, NestedMeta, Attribute, AttrStyle, MetaList, FnArg, Receiver};
use syn::buffer::Cursor;
use proc_macro2::Span;
use syn::spanned::Spanned;
use smir::ast::{SM, Invariant, Lemma, LemmaPurpose, Transition, TransitionKind, TransitionStmt, Extras, ShardableType, LemmaPurposeKind};
use crate::parse_transition::parse_impl_item_method;

///////// TokenStream -> ParseResult

pub struct ParseResult {
    pub name: Ident,
    pub fns: Vec<ImplItemMethod>,
    pub fields: Option<FieldsNamed>,
}

impl Parse for ParseResult {
    fn parse(input: ParseStream) -> syn::parse::Result<Self> {
        // parse
        //
        // state machine IDENT {
        //    ... a bunch of items
        // }
        keyword(input, "state")?;
        keyword(input, "machine")?;
        let name: Ident = input.parse()?;

        let items_stream;
        let _ = braced!(items_stream in input);

        let mut fns = Vec::new();
        let mut fields_opt: Option<FieldsNamed> = None;

        while !items_stream.is_empty() {
            // Attempt to parse something of the form
            //
            // fields {
            //    ... a bunch of fields
            // }
            if peek_keyword(items_stream.cursor(), "fields") {
                let kw_span = keyword(&items_stream, "fields")?;
                if fields_opt.is_some() {
                    return Err(Error::new(kw_span, "Expected only one declaration of `fields` block"));
                }

                let fields_named: FieldsNamed = items_stream.parse()?;
                fields_opt = Some(fields_named);
            }

            // Otherwise parse a function
            let item: ImplItemMethod = items_stream.parse()?;
            fns.push(item);
        }

        return Ok(ParseResult {
            name: name,
            fns: fns,
            fields: fields_opt,
        });
    }
}

fn keyword(input: ParseStream, token: &str) -> syn::parse::Result<Span> {
    input.step(|cursor| {
        if let Some((ident, rest)) = cursor.ident() {
            if ident == token {
                return Ok((ident.span(), rest));
            }
        }
        Err(cursor.error(format!("expected `{}`", token)))
    })
}

fn peek_keyword(cursor: Cursor, token: &str) -> bool {
    if let Some((ident, _rest)) = cursor.ident() {
        ident == token
    } else {
        false
    }
}

///////// ParseResult -> SMIR

enum FnAttrInfo {
    NoneFound,
    Transition,
    Static,
    Init,
    Invariant,
    Lemma(LemmaPurpose<Ident>),
}

fn err_on_dupe(info: &FnAttrInfo, span: Span) -> syn::parse::Result<()> {
    match info {
        FnAttrInfo::NoneFound => Ok(()),
        _ => Err(Error::new(span, "conflicting attributes")),
    }
}

fn parse_fn_attr_info(attrs: &Vec<Attribute>) -> syn::parse::Result<FnAttrInfo> {
    let mut fn_attr_info = FnAttrInfo::NoneFound;

    for attr in attrs {
        match attr.style {
            AttrStyle::Inner(_) => { continue; }
            AttrStyle::Outer => { }
        }

        match attr.parse_meta()? {
            Meta::Path(path) => {
                if path.is_ident("invariant") {
                    err_on_dupe(&fn_attr_info, attr.span())?;
                    fn_attr_info = FnAttrInfo::Invariant;
                }
                else if path.is_ident("transition") {
                    err_on_dupe(&fn_attr_info, attr.span())?;
                    fn_attr_info = FnAttrInfo::Transition;
                }
                else if path.is_ident("static") {
                    err_on_dupe(&fn_attr_info, attr.span())?;
                    fn_attr_info = FnAttrInfo::Static;
                }
                else if path.is_ident("init") {
                    err_on_dupe(&fn_attr_info, attr.span())?;
                    fn_attr_info = FnAttrInfo::Init;
                }
            }
            Meta::List(MetaList { path, nested, .. }) => {
                if path.is_ident("inductive") || path.is_ident("safety") {
                    let is_safety = path.is_ident("safety");
                    let attrname = if is_safety { "safety" } else { "inductive" };
                    let lp_kind = if is_safety { LemmaPurposeKind::SatisfiesAsserts } else { LemmaPurposeKind::PreservesInvariant };
                    if nested.len() != 1 {
                        return Err(Error::new(attr.span(), "expected transition name: #[".to_string() + attrname + "(name)]"));
                    }
                    err_on_dupe(&fn_attr_info, attr.span())?;

                    let transition_name = match nested.iter().next() {
                        Some(NestedMeta::Meta(Meta::Path(path))) => {
                            match path.get_ident() {
                                Some(ident) => ident.clone(),
                                None => {
                                    return Err(Error::new(attr.span(), "expected transition name: #[".to_string() + attrname + "(name)]"));
                                },
                            }
                        }
                        _ => { return Err(Error::new(attr.span(), "expected transition name: #[".to_string() + attrname + "(name)]")); }
                    };

                    fn_attr_info = FnAttrInfo::Lemma(LemmaPurpose { transition: transition_name, kind: lp_kind });
                }
            }
            _ => { }
        };
    }

    return Ok(fn_attr_info);
}

pub enum MaybeSM {
    SM(SM<Ident, ImplItemMethod, Expr, Type>, FieldsNamed, Vec<ImplItemMethod>),
    Extras(Extras<Ident, ImplItemMethod>),
}

pub struct SMAndFuncs {
    pub sm: MaybeSM,
    pub normal_fns: Vec<ImplItemMethod>,
}

fn attr_is_mode(attr: &Attribute, mode: &str) -> bool {
    match attr.parse_meta() {
        Ok(Meta::Path(path)) if path.is_ident(mode) => true,
        _ => false,
    }
}

/*
fn attr_is_any_mode(attr: &Attribute) -> bool {
    match attr.parse_meta() {
        Ok(Meta::Path(path)) if path.is_ident("spec") || path.is_ident("proof") || path.is_ident("exec") => true,
        _ => false,
    }
}
*/

fn ensure_mode(impl_item_method: &ImplItemMethod, msg: &str, mode: &str) -> syn::parse::Result<()> {
    for attr in &impl_item_method.attrs {
        if attr_is_mode(attr, mode) {
            return Ok(());
        }
    }

    return Err(Error::new(impl_item_method.span(), msg));
}

/*
fn ensure_no_mode(impl_item_method: &ImplItemMethod, msg: &str) -> syn::parse::Result<()> {
    for attr in &impl_item_method.attrs {
        if attr_is_any_mode(attr) {
            return Err(Error::new(attr.span(), msg));
        }
    }

    return Ok(());
}
*/

fn to_transition(impl_item_method: &mut ImplItemMethod, kind: TransitionKind) -> syn::parse::Result<Transition<Ident, Expr, Type>> {
    ensure_mode(&impl_item_method, "a transition fn must be labelled 'spec'", "spec")?;
    let ctxt = crate::parse_transition::Ctxt { kind };
    return parse_impl_item_method(impl_item_method, &ctxt);
}

fn to_invariant(impl_item_method: ImplItemMethod) -> syn::parse::Result<Invariant<ImplItemMethod>> {
    ensure_mode(&impl_item_method, "an invariant fn must be labelled 'spec'", "spec")?;
    if impl_item_method.sig.inputs.len() != 1 {
        return Err(Error::new(impl_item_method.sig.inputs.span(), "an invariant function must take exactly 1 argument (self)"));
    }

    let one_arg = impl_item_method.sig.inputs.iter().next().expect("one_arg");
    match one_arg {
        FnArg::Receiver(Receiver { mutability: None, .. }) => { }
        _ => {
            return Err(Error::new(one_arg.span(), "an invariant function must take 1 argument (self)"));
        }
    }

    if impl_item_method.sig.generics.params.len() > 0 {
        return Err(Error::new(impl_item_method.sig.generics.span(), "an invariant function must take 0 type arguments"));
    }

    return Ok(Invariant { func: impl_item_method });
}

fn to_lemma(impl_item_method: ImplItemMethod, purpose: LemmaPurpose<Ident>) -> syn::parse::Result<Lemma<Ident, ImplItemMethod>> {
    ensure_mode(&impl_item_method, "an inductivity lemma must be labelled 'proof'", "proof")?;
    Ok(Lemma { purpose, func: impl_item_method })
}

fn to_fields(fields_named: &FieldsNamed) -> syn::parse::Result<Vec<smir::ast::Field<Ident, Type>>> {
    let mut v: Vec<smir::ast::Field<Ident, Type>> = Vec::new();
    for field in fields_named.named.iter() {
        let ident = match &field.ident {
            None => { return Err(Error::new(field.span(), "state machine field must have a name")); }
            Some(ident) => ident.clone(),
        };

        let stype = ShardableType::Variable(field.ty.clone());
        v.push(smir::ast::Field { ident, stype });
    }
    return Ok(v);
}

pub fn parse_result_to_smir(pr: ParseResult) -> syn::parse::Result<SMAndFuncs> {
    let ParseResult { name, fns, fields } = pr;

    let mut normal_fns = Vec::new();
    let mut transitions: Vec<Transition<Ident, Expr, Type>> = Vec::new();
    let mut invariants: Vec<Invariant<ImplItemMethod>> = Vec::new();
    let mut lemmas: Vec<Lemma<Ident, ImplItemMethod>> = Vec::new();

    let err_if_not_primary = |impl_item_method: &ImplItemMethod| {
        match fields {
            None => Err(Error::new(impl_item_method.span(), "a transition definition must be in the primary body for a state machine, i.e.,the body with the 'fields' definition")),
            Some(_) => Ok(()),
        }
    };

    let mut trans_fns = Vec::new();

    for impl_item_method in fns {
        let attr_info = parse_fn_attr_info(&impl_item_method.attrs)?;
        match attr_info {
            FnAttrInfo::NoneFound => { normal_fns.push(impl_item_method); }
            FnAttrInfo::Transition |
            FnAttrInfo::Static |
            FnAttrInfo::Init => {
                let kind = match attr_info {
                    FnAttrInfo::Transition => TransitionKind::Transition,
                    FnAttrInfo::Static => TransitionKind::Static,
                    FnAttrInfo::Init => TransitionKind::Init,
                    _ => { panic!("can't get here"); }
                };

                err_if_not_primary(&impl_item_method)?;
                let mut iim = impl_item_method;
                transitions.push(to_transition(&mut iim, kind)?);
                trans_fns.push(iim);
            }
            FnAttrInfo::Invariant => { invariants.push(to_invariant(impl_item_method)?); }
            FnAttrInfo::Lemma(purpose) => { lemmas.push(to_lemma(impl_item_method, purpose)?) }
        }
    }

    let maybe_sm = match fields {
        None => {
            assert!(transitions.len() == 0);
            MaybeSM::Extras(Extras {
                name,
                invariants,
                lemmas,
            })
        }
        Some(fields_named) => {
            let fields = to_fields(&fields_named)?;
            MaybeSM::SM(SM {
                name,
                fields,
                transitions,
                invariants,
                lemmas,
            }, fields_named, trans_fns)
        }
    };
    Ok(SMAndFuncs { normal_fns, sm: maybe_sm })
}
