//! Checked physical-borrow facade. Every nominal field owns an actual storage slot;
//! compatible transition witnesses expose observations, never physical ownership.
use crate::ast::*;
use crate::field_access_visitor::visit_field_accesses;
use crate::to_token_stream::{generics_for_decl, get_generic_args};
use crate::verified_field_storage_roles as roles;
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote, ToTokens};
use std::collections::{HashMap, HashSet};
use verus_syn::{Error, Expr, Ident};

#[derive(Default)]
struct Ops {
    init: HashMap<String, Expr>,
    update: Option<(Ident, Expr)>,
    special: Vec<(Ident, SpecialOp, Option<Box<verus_syn::Pat>>)>,
    hidden: Option<(Box<verus_syn::Pat>, Expr)>,
}
fn collect(s: &TransitionStmt, o: &mut Ops) -> Result<(), Error> {
    match s {
        TransitionStmt::Block(_, xs) => {
            for x in xs {
                collect(x, o)?
            }
        }
        TransitionStmt::Initialize(_, n, e) => {
            o.init.insert(n.to_string(), e.clone());
        }
        TransitionStmt::Update(_, n, e) => {
            if o.update.replace((n.clone(), e.clone())).is_some() {
                return Err(Error::new(
                    n.span(),
                    "borrow facade requires one variable update",
                ));
            }
        }
        TransitionStmt::Require(..) | TransitionStmt::Assert(..) => {}
        TransitionStmt::Split(span, k, xs) => {
            match &**k {
                SplitKind::Special(n, p, _, b) => o.special.push((n.clone(), p.clone(), b.clone())),
                SplitKind::Let(p, _, LetKind::BirdsEye, e) => {
                    if o.hidden.replace((p.clone(), e.clone())).is_some() {
                        return Err(Error::new(
                            *span,
                            "borrow facade allows one physical selection",
                        ));
                    }
                }
                SplitKind::Let(_, _, LetKind::Normal, _) => {}
                _ => {
                    return Err(Error::new(
                        *span,
                        "borrow facade currently requires sequential lets and operations",
                    ))
                }
            }
            for x in xs {
                collect(x, o)?
            }
        }
        _ => {
            return Err(Error::new(
                *s.get_span(),
                "unsupported physical borrow statement",
            ))
        }
    }
    Ok(())
}
fn lower(
    e: &Expr,
    fields: &HashMap<String, Field>,
    var: &Field,
    v: TokenStream,
    constants: &[&Field],
    c: &[TokenStream],
) -> Result<TokenStream, Error> {
    let mut e = e.clone();
    let mut errors = vec![];
    visit_field_accesses(
        &mut e,
        |errors, f, node| {
            if f.name == var.name {
                *node = Expr::Verbatim(v.clone());
            } else if let Some(i) = constants.iter().position(|x| x.name == f.name) {
                *node = Expr::Verbatim(c[i].clone());
            } else {
                errors.push(Error::new(
                    f.name.span(),
                    "borrow facade expression requires an owned ordinary observation",
                ));
            }
        },
        &mut errors,
        fields,
    );
    if let Some(error) = errors.into_iter().next() {
        return Err(error);
    }
    Ok(quote! {#e})
}
fn predicate(
    s: &TransitionStmt,
    post: bool,
    fields: &HashMap<String, Field>,
    var: &Field,
    pre: TokenStream,
    after: TokenStream,
    constants: &[&Field],
    c: &[TokenStream],
    selected: &TokenStream,
) -> Result<TokenStream, Error> {
    let lower = |e| lower(e, fields, var, pre.clone(), constants, c);
    Ok(match s {
        TransitionStmt::Block(_, xs) => {
            let ps: Vec<_> = xs
                .iter()
                .map(|x| {
                    predicate(
                        x,
                        post,
                        fields,
                        var,
                        pre.clone(),
                        after.clone(),
                        constants,
                        c,
                        selected,
                    )
                })
                .collect::<Result<_, _>>()?;
            quote! {true #(&&(#ps))*}
        }
        TransitionStmt::Require(_, e) => lower(e)?,
        TransitionStmt::Assert(_, e, _) if post => lower(e)?,
        TransitionStmt::Update(_, _, e) if post => {
            let e = lower(e)?;
            quote! {#after==(#e)}
        }
        TransitionStmt::Split(_, k, xs) => {
            let ps: Vec<_> = xs
                .iter()
                .map(|x| {
                    predicate(
                        x,
                        post,
                        fields,
                        var,
                        pre.clone(),
                        after.clone(),
                        constants,
                        c,
                        selected,
                    )
                })
                .collect::<Result<_, _>>()?;
            let body = quote! {true #(&&(#ps))*};
            match &**k {
                SplitKind::Let(p, t, LetKind::Normal, e) => {
                    let e = lower(e)?;
                    let t = t.as_ref().map(|t| quote! {:#t});
                    quote! {{let #p #t=#e;#body}}
                }
                SplitKind::Let(p, t, LetKind::BirdsEye, _) if post => {
                    let t = t.as_ref().map(|t| quote! {:#t});
                    quote! {{let #p #t=#selected;#body}}
                }
                SplitKind::Special(_, _, _, Some(p)) if post => quote! {{let #p=#selected;#body}},
                _ => body,
            }
        }
        _ => quote! {true},
    })
}
fn fresh_names(sm: &SM, tr: &Transition) -> HashSet<String> {
    fn reserve(tokens: TokenStream, names: &mut HashSet<String>) {
        for token in tokens {
            match token {
                proc_macro2::TokenTree::Ident(n) => {
                    names.insert(n.to_string());
                }
                proc_macro2::TokenTree::Group(g) => reserve(g.stream(), names),
                _ => {}
            }
        }
    }
    fn walk(s: &TransitionStmt, names: &mut HashSet<String>) {
        match s {
            TransitionStmt::Block(_, xs) => {
                for x in xs {
                    walk(x, names)
                }
            }
            TransitionStmt::Require(_, e)
            | TransitionStmt::Assert(_, e, _)
            | TransitionStmt::Update(_, _, e)
            | TransitionStmt::Initialize(_, _, e) => reserve(quote! {#e}, names),
            TransitionStmt::Split(_, k, xs) => {
                match &**k {
                    SplitKind::Let(p, t, _, e) => {
                        reserve(quote! {#p #t #e}, names);
                    }
                    SplitKind::Special(_, op, _, p) => {
                        reserve(quote! {#p}, names);
                        match &op.elt {
                            MonoidElt::General(e)
                            | MonoidElt::OptionSome(Some(e))
                            | MonoidElt::SingletonMultiset(e) => reserve(quote! {#e}, names),
                            _ => {}
                        }
                    }
                    _ => {}
                }
                for x in xs {
                    walk(x, names)
                }
            }
            _ => {}
        }
    }
    let mut names: HashSet<_> = sm
        .fields
        .iter()
        .map(|f| f.name.to_string())
        .chain(sm.transitions.iter().map(|t| t.name.to_string()))
        .chain(tr.params.iter().map(|p| p.name.to_string()))
        .collect();
    walk(&tr.body, &mut names);
    if let Some(g) = &sm.generics {
        reserve(quote! {#g}, &mut names);
    }
    names
}
fn fresh(names: &mut HashSet<String>, stem: &str) -> Ident {
    let mut candidate = format!("__tsm_borrow_{stem}");
    while names.contains(&candidate) {
        candidate.push('_');
    }
    names.insert(candidate.clone());
    Ident::new(&candidate, Span::mixed_site())
}

pub fn output(sm: &SM, selected: &HashSet<String>) -> Result<TokenStream, Error> {
    let variables: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::Variable(_)))
        .collect();
    let bags: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::Multiset(_)))
        .collect();
    let bools: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::Bool))
        .collect();
    let stores: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::StorageOption(_)))
        .collect();
    let constants: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::Constant(_)))
        .collect();
    if variables.len() != 1
        || bags.len() != 1
        || bools.len() != 1
        || stores.len() != 1
        || sm.fields.len() != constants.len() + 4
    {
        return Err(Error::new(
            sm.name.span(),
            "borrow facade requires one variable, Bool, multiset, optional store and constants",
        ));
    }
    let variable = variables[0];
    let bagfield = bags[0];
    let boolfield = bools[0];
    let store = stores[0];
    let ShardableType::StorageOption(permission) = &store.stype else {
        unreachable!()
    };
    let ShardableType::Multiset(element) = &bagfield.stype else {
        unreachable!()
    };
    if permission.to_token_stream().to_string() != element.to_token_stream().to_string() {
        return Err(Error::new(
            store.name.span(),
            "borrow facade storage/reader payload must match",
        ));
    }
    let (g, attrs) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = generics_for_decl(&g);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let types = args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default();
    let expr = args.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default();
    let first = sm
        .transitions
        .iter()
        .find(|t| t.kind == TransitionKind::Init)
        .ok_or_else(|| {
            Error::new(
                sm.name.span(),
                "borrow facade requires checked initialization",
            )
        })?;
    let mut metadata_names = fresh_names(sm, first);
    let location = fresh(&mut metadata_names, "descriptor_location");
    let marker_field = fresh(&mut metadata_names, "descriptor_types");
    let marker = args
        .as_ref()
        .map(|a| quote! {ghost #marker_field:core::marker::PhantomData<(#a,)>,});
    let markerv = args
        .as_ref()
        .map(|_| quote! {#marker_field:core::marker::PhantomData,});
    let token = quote! {Token #types};
    let descriptor = quote! {::vstd::resource::tsm_context::Descriptor<__BorrowMetadata #types>};
    let cx = roles::Context {
        decl: &decl,
        types: &types,
        expr: &expr,
        where_clause: &wc,
        attrs: &attrs,
        token: &token,
        descriptor: &descriptor,
        protocol_location: &location,
        constants: &constants,
    };
    let wrappers = vec![
        roles::wrapper(variable, &cx)?,
        roles::wrapper(bagfield, &cx)?,
        roles::wrapper(boolfield, &cx)?,
    ];
    let var = &variable.name;
    let bag = &bagfield.name;
    let writer = &boolfield.name;
    let storage = &store.name;
    let collection = format_ident!("{bag}_collection");
    let vf = format_ident!("field_{var}");
    let vg = format_ident!("value_{var}");
    let bf = format_ident!("field_{bag}");
    let wf = format_ident!("field_{writer}");
    let cn: Vec<_> = constants.iter().map(|f| &f.name).collect();
    let ct: Vec<_> = constants.iter().map(|f| f.get_type()).collect();
    let sets: Vec<_> = cn.iter().map(|n| format_ident!("with_{n}")).collect();
    let cget: Vec<_> = cn.iter().map(|n| format_ident!("value_{n}")).collect();
    let fields: HashMap<_, _> = sm
        .fields
        .iter()
        .map(|f| (f.name.to_string(), f.clone()))
        .collect();
    let mut api_names = HashSet::from([
        "id".to_string(),
        "clone".to_string(),
        "invariant".to_string(),
        "__bag_normalize".to_string(),
    ]);
    for c in &constants {
        if !api_names.insert(c.name.to_string()) {
            return Err(Error::new(
                c.name.span(),
                "borrow facade generated constant method name collision",
            ));
        }
    }
    for t in &sm.transitions {
        if !api_names.insert(t.name.to_string()) {
            return Err(Error::new(
                t.name.span(),
                "borrow facade generated Instance method name collision",
            ));
        }
        if t.kind == TransitionKind::Transition
            && !api_names.insert(format!("__borrow_{}_raw", t.name))
        {
            return Err(Error::new(
                t.name.span(),
                "borrow facade generated raw method name collision",
            ));
        }
    }
    for f in &sm.fields {
        if !matches!(f.stype, ShardableType::Constant(_))
            && (matches!(
                f.name.to_string().as_str(),
                "Instance"
                    | "__BorrowMetadata"
                    | "Token"
                    | "StorageToken"
                    | "State"
                    | "Fragment"
                    | "Protocol"
                    | "TransitionObservation"
            ) || f.name == collection.to_string().as_str())
        {
            return Err(Error::new(
                f.name.span(),
                "borrow facade generated nominal type name collision",
            ));
        }
    }
    let mut methods = vec![];
    for tr in &sm.transitions {
        let name = &tr.name;
        let mut names = fresh_names(sm, tr);
        if tr.kind == TransitionKind::Property {
            methods.push(roles::guard_method(bagfield, tr, &cx)?);
            continue;
        }
        let mut op = Ops::default();
        collect(&tr.body, &mut op)?;
        let params: Vec<_> = tr
            .params
            .iter()
            .map(|p| {
                let n = &p.name;
                let t = &p.ty;
                quote! {#n:#t}
            })
            .collect();
        let pn: Vec<_> = tr.params.iter().map(|p| &p.name).collect();
        if tr.kind == TransitionKind::Init {
            let actual = fresh(&mut names, "init_actual");
            let out = fresh(&mut names, "init_out");
            let remaining = fresh(&mut names, "init_remaining");
            let md = fresh(&mut names, "init_md");
            let rawvar = fresh(&mut names, "init_rawvar");
            let rawwriter = fresh(&mut names, "init_rawwriter");
            let rawbag = fresh(&mut names, "init_rawbag");
            let part = fresh(&mut names, "init_part");
            let rest = fresh(&mut names, "init_rest");

            if op.init.len() != sm.fields.len()
                || op.update.is_some()
                || !op.special.is_empty()
                || op.hidden.is_some()
            {
                return Err(Error::new(
                    name.span(),
                    "borrow initializer requires exact straight-line fields",
                ));
            }
            let compact = |e: &Expr| e.to_token_stream().to_string().replace(' ', "");
            if !matches!(
                compact(&op.init[&storage.to_string()]).as_str(),
                "None" | "Option::None"
            ) || !matches!(
                compact(&op.init[&bag.to_string()]).as_str(),
                "Multiset::empty()" | "::vstd::multiset::Multiset::empty()"
            ) {
                return Err(Error::new(
                    name.span(),
                    "borrow initializer requires empty reader and None storage",
                ));
            }
            let value = &op.init[&var.to_string()];
            let constvalues: Vec<_> = cn.iter().map(|n| &op.init[&n.to_string()]).collect();
            if op.init.len() != sm.fields.len()
                || op.init[&writer.to_string()].to_token_stream().to_string() != "true"
            {
                return Err(Error::new(
                    name.span(),
                    "borrow initializer requires present Bool and all fields",
                ));
            }
            let req = predicate(
                &tr.body,
                false,
                &fields,
                variable,
                quote! {#value},
                quote! {#value},
                &constants,
                &constvalues.iter().map(|e| quote! {#e}).collect::<Vec<_>>(),
                &quote! {()},
            )?;
            let select = format_ident!("select_{var}");
            let without = format_ident!("without_{var}");
            let selectwriter = format_ident!("select_{writer}");
            let withoutwriter = format_ident!("without_{writer}");
            let returned_fields: Vec<_> = sm
                .fields
                .iter()
                .filter(|f| {
                    matches!(
                        f.stype,
                        ShardableType::Variable(_)
                            | ShardableType::Multiset(_)
                            | ShardableType::Bool
                    )
                })
                .collect();
            let ivar = verus_syn::Index::from(
                1 + returned_fields.iter().position(|f| f.name == *var).unwrap(),
            );
            let ibag = verus_syn::Index::from(
                1 + returned_fields.iter().position(|f| f.name == *bag).unwrap(),
            );
            let iwriter = verus_syn::Index::from(
                1 + returned_fields
                    .iter()
                    .position(|f| f.name == *writer)
                    .unwrap(),
            );
            let returntypes: Vec<_> = returned_fields
                .iter()
                .map(|f| match f.stype {
                    ShardableType::Variable(_) => quote! {Tracked<#var #types>},
                    ShardableType::Multiset(_) => quote! {Tracked<#collection #types>},
                    _ => quote! {Tracked<Option<#writer #types>>},
                })
                .collect();
            let returnvalues: Vec<_> = returned_fields
                .iter()
                .map(|f| match f.stype {
                    ShardableType::Variable(_) => quote! {Tracked(#rawvar)},
                    ShardableType::Multiset(_) => {
                        quote! {Tracked(#collection #expr{raw:#rawbag,metadata:#md.clone()})}
                    }
                    _ => quote! {Tracked(Some(#rawwriter))},
                })
                .collect();
            methods.push(quote!{
 pub proof fn #name(#(#params,)*tracked #actual:Option<#permission>)->(tracked #out:(Tracked<Self>,#(#returntypes),*))
 requires #req,#actual==None,
 ensures #out.#ivar@.instance_id()==#out.0@.id(),#out.#ivar@.value()==#value,#out.#ibag@.instance_id()==#out.0@.id(),#out.#ibag@.multiset()==::vstd::multiset::Multiset::empty(),#out.#iwriter@ is Some,#out.#iwriter@->Some_0.instance_id()==#out.0@.id(),#(#out.0@.#cn()==#constvalues,)*
 {
 let tracked #remaining=Protocol #expr::#name(IMap::tracked_empty(),#(#pn),*);
 let tracked #md=::vstd::resource::tsm_context::Descriptor::alloc(__BorrowMetadata #expr{#location:#remaining.loc(),#(#cn:#constvalues,)*#markerv});
 let #part=#remaining.fragment().#select()#(.#sets(#constvalues))*;let #rest=#remaining.fragment().#without();#remaining.fragment().op_unit();
 assert(Fragment #expr::op(#part,#rest)==#remaining.fragment());let tracked(#rawvar,#remaining)=#remaining.split(#part,#rest);
 let #part=#remaining.fragment().#selectwriter()#(.#sets(#constvalues))*;let #rest=#remaining.fragment().#withoutwriter();
 assert(Fragment #expr::op(#part,#rest)==#remaining.fragment());let tracked(#rawwriter,#remaining)=#remaining.split(#part,#rest);
 let #part=Fragment #expr::#bf(::vstd::multiset::Multiset::empty())#(.#sets(#constvalues))*;
 assert(Fragment #expr::op(#part,#remaining.fragment())==#remaining.fragment());let tracked(#rawbag,#remaining)=#remaining.split(#part,#remaining.fragment());
 let tracked #rawvar=<#var #types>::__from_token(#rawvar,#md.clone());let tracked #rawwriter=<#writer #types>::__from_token(#rawwriter,#md.clone());
 (Tracked(Self{metadata:#md.clone(),context:Tracked(Some(#remaining))}),#(#returnvalues),*)
 }
 });
            continue;
        }
        if !selected.contains(&name.to_string()) {
            return Err(Error::new(
                name.span(),
                "borrow facade requires checked selected readiness",
            ));
        }
        let slot = fresh(&mut names, "slot");
        let owner = fresh(&mut names, "owner");
        let consumed = fresh(&mut names, "consumed");
        let actual = fresh(&mut names, "actual");
        let out = fresh(&mut names, "out");
        let owned = fresh(&mut names, "owned");
        let initial = fresh(&mut names, "initial");
        let dep = fresh(&mut names, "dep");
        let wd = fresh(&mut names, "wd");
        let before = fresh(&mut names, "before");
        let after = fresh(&mut names, "after");
        let selected = fresh(&mut names, "selected");
        let part = fresh(&mut names, "part");
        let rest = fresh(&mut names, "rest");
        let returned = fresh(&mut names, "returned");
        let a = fresh(&mut names, "a");
        let r = fresh(&mut names, "r");
        if tr.kind != TransitionKind::Transition
            || !op.init.is_empty()
            || op.update.as_ref().map(|(n, _)| n) != Some(var)
        {
            return Err(Error::new(
                name.span(),
                "borrow facade requires one ordinary variable update",
            ));
        }
        let mut remove_writer = false;
        let mut add_writer = false;
        let mut remove_reader = false;
        let mut add_reader = false;
        let mut deposit = None;
        let mut withdraw = None;
        for (f, s, b) in &op.special {
            match (&s.stmt,&s.elt){
 (MonoidStmtType::Remove,MonoidElt::True) if f==writer=>remove_writer=true,
 (MonoidStmtType::Add(false),MonoidElt::True) if f==writer=>add_writer=true,
 (MonoidStmtType::Remove,MonoidElt::SingletonMultiset(_)) if f==bag=>remove_reader=true,
 (MonoidStmtType::Add(false),MonoidElt::SingletonMultiset(_)) if f==bag=>add_reader=true,
 (MonoidStmtType::Deposit,MonoidElt::OptionSome(Some(e))) if f==storage=>deposit=Some(e),
 (MonoidStmtType::Withdraw,MonoidElt::OptionSome(None)) if f==storage=>withdraw=b.as_ref(),
 _=>return Err(Error::new(f.span(),"borrow facade requires exclusive Bool, singleton bag and optional storage operations")),
 }
        }
        let deposit_case = remove_writer
            && deposit.is_some()
            && !add_writer
            && !remove_reader
            && !add_reader
            && withdraw.is_none()
            && op.hidden.is_none()
            && op.special.len() == 2;
        let withdraw_case = add_writer
            && withdraw.is_some()
            && !remove_writer
            && !remove_reader
            && !add_reader
            && deposit.is_none()
            && op.hidden.is_none()
            && op.special.len() == 2;
        let add_case = add_reader
            && op.hidden.is_some()
            && !remove_writer
            && !add_writer
            && !remove_reader
            && deposit.is_none()
            && withdraw.is_none()
            && op.special.len() == 1;
        let remove_case = remove_reader
            && !remove_writer
            && !add_writer
            && !add_reader
            && deposit.is_none()
            && withdraw.is_none()
            && op.hidden.is_none()
            && op.special.len() == 1;
        if !(deposit_case || withdraw_case || add_case || remove_case) {
            return Err(Error::new(
                name.span(),
                "unsupported physical borrow operation combination",
            ));
        }
        let identical = |a: &Expr, b: &Ident| a.to_token_stream().to_string() == b.to_string();
        if deposit_case || remove_case {
            let [p] = tr.params.as_slice() else {
                return Err(Error::new(
                    name.span(),
                    "borrow consumption requires one payload parameter",
                ));
            };
            if p.ty.to_token_stream().to_string() != permission.to_token_stream().to_string() {
                return Err(Error::new(
                    p.name.span(),
                    "borrow payload parameter type mismatch",
                ));
            }
            let operand = if deposit_case {
                deposit.unwrap()
            } else {
                let MonoidElt::SingletonMultiset(e) = &op.special[0].1.elt else {
                    unreachable!()
                };
                e
            };
            if !identical(operand, &p.name) {
                return Err(Error::new(
                    name.span(),
                    "borrow operand must match its payload parameter",
                ));
            }
        } else if !tr.params.is_empty() {
            return Err(Error::new(
                name.span(),
                "selected physical borrowing currently requires no payload parameters",
            ));
        }
        if withdraw_case {
            if !matches!(&**withdraw.unwrap(), verus_syn::Pat::Ident(_)) {
                return Err(Error::new(
                    name.span(),
                    "borrow withdrawal requires a single bound identifier",
                ));
            }
        }
        if add_case {
            let (pat, e) = op.hidden.as_ref().unwrap();
            let verus_syn::Pat::Ident(p) = &**pat else {
                return Err(Error::new(
                    name.span(),
                    "borrow selection requires a single bound identifier",
                ));
            };
            let MonoidElt::SingletonMultiset(operand) = &op.special[0].1.elt else {
                unreachable!()
            };
            if !identical(operand, &p.ident)
                || e.to_token_stream().to_string().replace(' ', "") != format!("pre.{storage}->0")
            {
                return Err(Error::new(
                    name.span(),
                    "borrow selection must use the optional stored payload",
                ));
            }
        }

        let raw = format_ident!("__borrow_{name}_raw");
        let observed = format_ident!("{name}_observed");
        let strong = format_ident!("{name}_strong");
        let rawconstants: Vec<_> = cget
            .iter()
            .map(|get| quote! {old(#slot)@->Some_0.fragment().#get()})
            .collect();
        let publicconstants: Vec<_> = cn.iter().map(|n| quote! {self.#n()}).collect();
        let writer_first = sm.fields.iter().position(|f| f.name == *writer).unwrap()
            < sm.fields.iter().position(|f| f.name == *storage).unwrap();
        let permission_index = verus_syn::Index::from(if writer_first { 1 } else { 0 });
        let writer_index = verus_syn::Index::from(if writer_first { 0 } else { 1 });
        let publicselected = if add_writer {
            quote! {#out.#permission_index@}
        } else if add_reader {
            quote! {#out.0@}
        } else {
            quote! {()}
        };
        let selectedvalue = if add_reader || add_writer {
            quote! {#out.0@}
        } else {
            quote! {()}
        };
        let req = predicate(
            &tr.body,
            false,
            &fields,
            variable,
            quote! {old(#owner).value()},
            quote! {final(#owner).value()},
            &constants,
            &publicconstants,
            &publicselected,
        )?;
        let rawreq = predicate(
            &tr.body,
            false,
            &fields,
            variable,
            quote! {old(#slot)@->Some_0.fragment().#vg()},
            quote! {final(#slot)@->Some_0.fragment().#vg()},
            &constants,
            &rawconstants,
            &selectedvalue,
        )?;
        let post = predicate(
            &tr.body,
            true,
            &fields,
            variable,
            quote! {old(#owner).value()},
            quote! {final(#owner).value()},
            &constants,
            &publicconstants,
            &publicselected,
        )?;
        let rawpost = predicate(
            &tr.body,
            true,
            &fields,
            variable,
            quote! {old(#slot)@->Some_0.fragment().#vg()},
            quote! {final(#slot)@->Some_0.fragment().#vg()},
            &constants,
            &rawconstants,
            &selectedvalue,
        )?;
        let rawconsume = if remove_writer {
            quote! {tracked #consumed:#token,}
        } else if remove_reader {
            quote! {tracked #consumed:#token,}
        } else {
            quote! {}
        };
        let publicconsume = if remove_writer {
            quote! {tracked #consumed:#writer #types,}
        } else if remove_reader {
            quote! {tracked #consumed:#bag #types,}
        } else {
            quote! {}
        };
        let consumedfield = if remove_writer { boolfield } else { bagfield };
        let consumedfactory = format_ident!("field_{}", consumedfield.name);
        let consumedvalue = if remove_writer {
            quote! {true}
        } else if remove_reader {
            let Some((_, s, _)) = op
                .special
                .iter()
                .find(|(f, s, _)| f == bag && matches!(s.stmt, MonoidStmtType::Remove))
            else {
                unreachable!()
            };
            let MonoidElt::SingletonMultiset(e) = &s.elt else {
                unreachable!()
            };
            quote! {::vstd::multiset::Multiset::singleton(#e)}
        } else {
            quote! {()}
        };
        let rawconsumereq = if remove_writer || remove_reader {
            quote! {#consumed.loc()==old(#slot)@->Some_0.loc(),#consumed.fragment()==Fragment #expr::#consumedfactory(#consumedvalue)#(.#sets(#rawconstants))*,}
        } else {
            quote! {}
        };
        let publicconsumereq = if remove_writer {
            quote! {#consumed.instance_id()==self.id(),}
        } else if remove_reader {
            let Some((_, s, _)) = op
                .special
                .iter()
                .find(|(f, s, _)| f == bag && matches!(s.stmt, MonoidStmtType::Remove))
            else {
                unreachable!()
            };
            let MonoidElt::SingletonMultiset(e) = &s.elt else {
                unreachable!()
            };
            quote! {#consumed.instance_id()==self.id(),#consumed.element()==#e,}
        } else {
            quote! {}
        };
        let actualparam = if deposit.is_some() {
            quote! {tracked #actual:#permission,}
        } else {
            quote! {}
        };
        let physicalreq = if let Some(e) = deposit {
            quote! {#actual==#e,}
        } else {
            quote! {}
        };
        let join = if remove_writer || remove_reader {
            quote! {#owned.fragment().op_unit();#consumed.fragment().op_unit();let tracked #owned=#owned.join(#consumed);}
        } else {
            quote! {}
        };
        let pack = if deposit.is_some() {
            quote! {let tracked #dep=::vstd::resource::tsm_helpers::singleton_map(0int,#actual);}
        } else {
            quote! {}
        };
        let actualarg = if deposit.is_some() {
            quote! {#actual,}
        } else {
            quote! {}
        };
        let deparg = if deposit.is_some() {
            quote! {#dep,}
        } else {
            quote! {}
        };
        let normbefore = if remove_reader {
            let Some((_, s, _)) = op
                .special
                .iter()
                .find(|(f, s, _)| f == bag && matches!(s.stmt, MonoidStmtType::Remove))
            else {
                unreachable!()
            };
            let MonoidElt::SingletonMultiset(e) = &s.elt else {
                unreachable!()
            };
            quote! {Self::__bag_normalize(#e);}
        } else {
            quote! {}
        };
        let normafter = if add_reader {
            quote! {Self::__bag_normalize(#selected);}
        } else {
            quote! {}
        };
        let returnclause = if add_writer {
            quote! {->(tracked #out:(Tracked<#permission>,Tracked<#token>))}
        } else if add_reader {
            quote! {->(tracked #out:(Ghost<#element>,Tracked<#token>))}
        } else {
            quote! {}
        };
        let publicreturn = if add_writer {
            if writer_first {
                quote! {->(tracked #out:(Tracked<#writer #types>,Tracked<#permission>))}
            } else {
                quote! {->(tracked #out:(Tracked<#permission>,Tracked<#writer #types>))}
            }
        } else if add_reader {
            quote! {->(tracked #out:(Ghost<#element>,Tracked<#bag #types>))}
        } else {
            quote! {}
        };
        let rolefactory = if add_writer { wf.clone() } else { bf.clone() };
        let rolevalue = if add_writer {
            quote! {true}
        } else {
            quote! {::vstd::multiset::Multiset::singleton(#out.0@)}
        };
        let rawresult = if add_writer || add_reader {
            quote! {#out.1@.loc()==old(#slot)@->Some_0.loc(),#out.1@.fragment()==Fragment #expr::#rolefactory(#rolevalue)#(.#sets(#rawconstants))*,}
        } else {
            quote! {}
        };
        let publicresult = if add_writer {
            quote! {#out.#writer_index@.instance_id()==self.id(),}
        } else if add_reader {
            quote! {#out.1@.instance_id()==self.id(),#out.1@.element()==#out.0@,}
        } else {
            quote! {}
        };
        let rawboolget = format_ident!("value_{writer}");
        let rawbagget = format_ident!("value_{bag}");
        let selectedexpression = if add_writer {
            quote! {#before.#storage->Some_0}
        } else if add_reader {
            let (_, e) = op.hidden.as_ref().unwrap();
            quote! {#e}
        } else {
            quote! {()}
        };
        let selectedexpression = if add_reader {
            let (_, e) = op.hidden.as_ref().unwrap();
            let mut e = e.clone();
            struct Pre(Ident);
            impl verus_syn::visit_mut::VisitMut for Pre {
                fn visit_expr_path_mut(&mut self, e: &mut verus_syn::ExprPath) {
                    if e.path.is_ident("pre") {
                        let n = &self.0;
                        e.path = verus_syn::parse_quote!(#n);
                    }
                }
            }
            use verus_syn::visit_mut::VisitMut;
            Pre(before.clone()).visit_expr_mut(&mut e);
            quote! {#e}
        } else {
            selectedexpression
        };
        let choosevalue = if add_writer || add_reader {
            quote! {let #selected=#selectedexpression;}
        } else {
            quote! {}
        };
        let select = format_ident!("select_{var}");
        let without = format_ident!("without_{var}");
        let take_law = format_ident!("take_{var}_law");
        let rolesplit = if add_writer || add_reader {
            let bodyvalue = if add_writer {
                quote! {true}
            } else {
                quote! {::vstd::multiset::Multiset::singleton(#selected)}
            };
            quote! {
            #owned.fragment().#take_law();#owned.fragment().op_unit();let #part=#owned.fragment().#select()#(.#sets(#initial.#cget()))*;
            let #rest=#owned.fragment().#without();
            assert(#rest==Fragment #expr::#rolefactory(#bodyvalue)#(.#sets(#initial.#cget()))*);
            assert(Fragment #expr::op(#part,#rest)==#owned.fragment());let tracked(#owned,#returned)=#owned.split(#part,#rest);
            }
        } else {
            quote! {}
        };
        let result = if add_writer {
            quote! {assert(#wd==IMap::empty().insert(0int,#selected));let tracked #actual=::vstd::resource::tsm_helpers::take_singleton(#wd,0int);(Tracked(#actual),Tracked(#returned))}
        } else if add_reader {
            quote! {(Ghost(#selected),Tracked(#returned))}
        } else {
            quote! {}
        };
        let consumeuse = if remove_writer || remove_reader {
            quote! {::vstd::prelude::use_type_invariant(&#consumed);self.metadata.agrees(&#consumed.metadata);}
        } else {
            quote! {}
        };
        let consumearg = if remove_writer || remove_reader {
            quote! {#consumed.raw.get().tracked_unwrap(),}
        } else {
            quote! {}
        };
        let call = quote! {Self::#raw(#(#pn,)*&mut #owner.raw,#consumearg #actualarg)};
        let publicbody = if add_writer {
            if writer_first {
                quote! {let tracked(#a,#r)=#call;(Tracked(<#writer #types>::__from_token(#r.get(),self.metadata.clone())),#a)}
            } else {
                quote! {let tracked(#a,#r)=#call;(#a,Tracked(<#writer #types>::__from_token(#r.get(),self.metadata.clone())))}
            }
        } else if add_reader {
            quote! {let tracked(#a,#r)=#call;(#a,Tracked(<#bag #types>::__from_token(#r.get(),self.metadata.clone(),#a@)))}
        } else {
            call
        };
        let publicinput: Vec<_> = sm
            .fields
            .iter()
            .filter_map(|f| {
                if f.name == *var {
                    Some(quote! {tracked #owner:&mut #var #types,})
                } else if f.name == *storage && deposit.is_some() {
                    Some(actualparam.clone())
                } else if f.name == *writer && remove_writer || f.name == *bag && remove_reader {
                    Some(publicconsume.clone())
                } else {
                    None
                }
            })
            .collect();
        methods.push(quote!{
 proof fn #raw(#(#params,)*tracked #slot:&mut Tracked<Option<#token>>,#rawconsume #actualparam)#returnclause
 requires old(#slot)@ is Some,old(#slot)@->Some_0.fragment()==Fragment #expr::#vf(old(#slot)@->Some_0.fragment().#vg())#(.#sets(#rawconstants))*,#rawreq,#rawconsumereq #physicalreq
 ensures final(#slot)@ is Some,final(#slot)@->Some_0.loc()==old(#slot)@->Some_0.loc(),final(#slot)@->Some_0.fragment()==Fragment #expr::#vf(final(#slot)@->Some_0.fragment().#vg())#(.#sets(#rawconstants))*,#rawpost,#rawresult
 {
 let tracked #owned=#slot.borrow_mut().tracked_take();#owned.fragment().op_unit();#join #normbefore let #initial=#owned.fragment();#pack
 let tracked TransitionObservation #expr{token:#owned,withdrawn:#wd,before:#before,after:#after,..}=Protocol #expr::#observed(#owned,#deparg #(#pn),*);
 reveal(State::#strong);
 assert(#before.#var==#initial.#vg());#(assert(#before.#cn==#initial.#cget());)*
 #choosevalue #normafter #rolesplit
 assert(#owned.fragment()==Fragment #expr::#vf(#after.#var)#(.#sets(#initial.#cget()))*);
 *#slot=Tracked(Some(#owned));#result
 }
 pub proof fn #name(tracked &self,#(#params,)*#(#publicinput)*)#publicreturn
 requires old(#owner).instance_id()==self.id(),#req,#publicconsumereq #physicalreq
 ensures final(#owner).instance_id()==self.id(),#post,#publicresult
 {
 ::vstd::prelude::use_type_invariant(&*#owner);self.metadata.agrees(&#owner.metadata);#consumeuse #publicbody
 }
 });
    }
    Ok(quote! {
    #(#attrs)*struct __BorrowMetadata #decl #wc{ghost #location: ::vstd::resource::Loc,#(ghost #cn:#ct,)*#marker}
    #(#wrappers)*
    #(#attrs)*#[allow(non_camel_case_types)]pub tracked struct #collection #decl #wc{raw:#token,metadata:#descriptor}
    impl #decl #collection #types #wc{
    #[verifier::type_invariant]spec fn invariant(self)->bool{self.raw.loc()==self.metadata.value().#location&&self.raw.fragment()==Fragment #expr::#bf(::vstd::multiset::Multiset::empty())#(.#sets(self.metadata.value().#cn))*}
    pub closed spec fn instance_id(&self)->::vstd::resource::Loc{self.metadata.id()}
    pub closed spec fn multiset(&self)->::vstd::multiset::Multiset<#element>{::vstd::multiset::Multiset::empty()}
    }
    #(#attrs)*pub tracked struct Instance #decl #wc{metadata:#descriptor,context:Tracked<Option<#token>>}
    impl #decl Instance #types #wc{
    #[verifier::type_invariant]spec fn invariant(self)->bool{::vstd::prelude::imply(self.context@ is Some,self.context@->Some_0.loc()==self.metadata.value().#location&&self.context@->Some_0.fragment()==Fragment #expr::empty()#(.#sets(self.metadata.value().#cn))*)}
    pub closed spec fn id(&self)->::vstd::resource::Loc{self.metadata.id()}
    #(pub closed spec fn #cn(&self)->#ct{self.metadata.value().#cn})*
    pub proof fn clone(tracked &self)->(tracked out:Self)ensures out.id()==self.id(),#(out.#cn()==self.#cn(),)*{Self{metadata:self.metadata.clone(),context:Tracked(None)}}
    proof fn __bag_normalize(x:#element)
    ensures ::vstd::multiset::Multiset::<#element>::empty().insert(x)==::vstd::multiset::Multiset::singleton(x),
    ::vstd::multiset::Multiset::<#element>::empty().add(::vstd::multiset::Multiset::<#element>::empty().insert(x))==::vstd::multiset::Multiset::singleton(x),
    ::vstd::multiset::Multiset::<#element>::singleton(x).sub(::vstd::multiset::Multiset::<#element>::empty().insert(x))==::vstd::multiset::Multiset::<#element>::empty(),
    {let a=::vstd::multiset::Multiset::<#element>::empty().insert(x);let b=::vstd::multiset::Multiset::<#element>::singleton(x);assert(::vstd::prelude::ext_equal(a,b));assert(::vstd::prelude::ext_equal(::vstd::multiset::Multiset::<#element>::empty().add(a),b));assert(::vstd::prelude::ext_equal(b.sub(a),::vstd::multiset::Multiset::<#element>::empty()));}
    #(#methods)*
    }
    })
}
