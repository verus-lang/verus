//! Checked physical counter/reader facade. Every nominal field owns an actual storage slot;
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
            if o.init.insert(n.to_string(), e.clone()).is_some() {
                return Err(Error::new(
                    n.span(),
                    "duplicate counter reader initialization",
                ));
            }
        }
        TransitionStmt::Update(_, n, e) => {
            if o.update.replace((n.clone(), e.clone())).is_some() {
                return Err(Error::new(
                    n.span(),
                    "counter reader facade requires one variable update",
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
                            "counter reader facade allows one physical selection",
                        ));
                    }
                }
                SplitKind::Let(_, _, LetKind::Normal, _) => {}
                _ => {
                    return Err(Error::new(
                        *span,
                        "counter reader facade currently requires sequential lets and operations",
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
                "unsupported counter reader statement",
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
                    "counter reader facade expression requires an owned ordinary observation",
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
    let readers: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::Multiset(_)))
        .collect();
    let stores: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::StorageOption(_)))
        .collect();
    if sm.fields.len() != 3 || variables.len() != 1 || readers.len() != 1 || stores.len() != 1 {
        return Err(Error::new(sm.name.span(),"singleton reader facade currently requires one Variable, one Multiset and one StorageOption"));
    }
    let variable = variables[0];
    let reader = readers[0];
    let store = stores[0];
    let ShardableType::Multiset(element) = &reader.stype else {
        unreachable!()
    };
    let ShardableType::StorageOption(permission) = &store.stype else {
        unreachable!()
    };
    if !same_type(element, permission) {
        return Err(Error::new(
            store.name.span(),
            "reader and optional storage payload types must match",
        ));
    }
    let mut api_names = HashSet::from([
        "id".to_string(),
        "clone".to_string(),
        "invariant".to_string(),
        "__reader_singleton_normalize".to_string(),
    ]);
    for tr in &sm.transitions {
        if !api_names.insert(tr.name.to_string()) {
            return Err(Error::new(
                tr.name.span(),
                "reader facade generated Instance method name collision",
            ));
        }
        if tr.kind == TransitionKind::Transition
            && !api_names.insert(format!("__reader_{}_raw", tr.name))
        {
            return Err(Error::new(
                tr.name.span(),
                "reader facade generated raw helper name collision",
            ));
        }
    }
    let generated_collection = format!("{}_collection", reader.name);
    for f in &sm.fields {
        if f.name == "Instance"
            || f.name == "__ReaderMetadata"
            || f.name == generated_collection.as_str()
        {
            return Err(Error::new(
                f.name.span(),
                "reader facade generated nominal type name collision",
            ));
        }
    }
    let fields: HashMap<_, _> = sm
        .fields
        .iter()
        .map(|f| (f.name.to_string(), f.clone()))
        .collect();
    let (generics, attrs) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = generics_for_decl(&generics);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let types = args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default();
    let expr = args.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default();
    let token = quote! {Token #types};
    let seed = sm.transitions.first().ok_or_else(|| {
        Error::new(
            sm.name.span(),
            "counter reader facade requires an initializer",
        )
    })?;
    let mut occupied = fresh_names(sm, seed);
    let metadata_type = fresh(&mut occupied, "metadata_type");
    let descriptor = quote! {::vstd::resource::tsm_context::Descriptor<#metadata_type>};
    let location = format_ident!("protocol_location");
    let cx = roles::Context {
        decl: &decl,
        types: &types,
        expr: &expr,
        where_clause: &wc,
        attrs: &attrs,
        token: &token,
        descriptor: &descriptor,
        protocol_location: &location,
        constants: &[],
    };
    let var = &variable.name;
    let bag = &reader.name;
    let storage = &store.name;
    let var_factory = format_ident!("field_{var}");
    let var_getter = format_ident!("value_{var}");
    let bag_factory = format_ident!("field_{bag}");
    let collection = format_ident!("{bag}_collection");
    let take_law = format_ident!("take_{var}_law");
    let wrappers = [roles::wrapper(variable, &cx)?, roles::wrapper(reader, &cx)?];
    let mut methods = Vec::new();
    let mut init_count = 0;
    for tr in &sm.transitions {
        let name = &tr.name;
        let mut names = fresh_names(sm, tr);
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
        if op.hidden.is_some() {
            return Err(Error::new(
                name.span(),
                "counter reader facade uses ordinary payload observations",
            ));
        }
        if tr.kind == TransitionKind::Property {
            let guards = op
                .special
                .iter()
                .filter(|(_, s, _)| matches!(s.stmt, MonoidStmtType::Guard))
                .count();
            if guards == 1 && op.special.len() == 2 {
                methods.push(roles::guard_method(reader, tr, &cx)?);
                continue;
            }
            let left = fresh(&mut names, "left");
            let right = fresh(&mut names, "right");
            let state = fresh(&mut names, "state");
            let lf = fresh(&mut names, "left_frame");
            let rf = fresh(&mut names, "right_frame");
            let enabled = format_ident!("{name}_enabled");
            let execute = format_ident!("{name}_execute");
            let strong = format_ident!("{name}_strong");
            if guards == 1 && op.special.len() == 1 {
                if !tr.params.is_empty() || !op.init.is_empty() || op.update.is_some() {
                    return Err(Error::new(
                        name.span(),
                        "ordinary storage guard requires one ordinary observer",
                    ));
                }
                let (_, s, _) = &op.special[0];
                if !matches!(s.elt, MonoidElt::OptionSome(Some(_))) {
                    return Err(Error::new(
                        name.span(),
                        "ordinary storage guard requires singleton optional operand",
                    ));
                }
                let value = operand(&tr.body, &fields, variable, quote! {#left.value()})?;
                let req = predicate(
                    &tr.body,
                    false,
                    &fields,
                    variable,
                    quote! {#left.value()},
                    quote! {#left.value()},
                    &[],
                    &[],
                    &quote! {()},
                )?;
                let owners = format_ident!("{name}_owners_enabled");
                let frame = format_ident!("{name}_frame");
                let guarded = format_ident!("{name}_guarded");
                let frag = fresh(&mut names, "fragment");
                let output = fresh(&mut names, "guarded");
                let mut lifetime_name = "__tsm_counter_guard".to_string();
                while decl.to_string().contains(&lifetime_name) {
                    lifetime_name.push('_');
                }
                let lifetime =
                    verus_syn::Lifetime::new(&format!("'{lifetime_name}"), Span::mixed_site());
                methods.push(quote!{
                pub proof fn #name<#lifetime>(tracked &self,tracked #left:&#lifetime #var #types)->(tracked #output:&#lifetime #permission)
                 requires #left.instance_id()==self.id(),#req,
                 ensures *#output==#value,
                {
                 ::vstd::prelude::use_type_invariant(#left);self.metadata.agrees(&#left.metadata);
                 let #frag=#left.raw@->Some_0.fragment();
                 assert forall|#lf:Fragment #types,#state:State #types|#state.invariant()&&Fragment #expr::op(#frag,#lf)==Protocol #expr::embed(#state)
                  implies State #expr::#enabled(#state)&&State #expr::#owners(#state,#frag,Fragment #expr::empty()) by {assert(#state.#var==#left.value());}
                 Protocol #expr::#frame(#frag);
                 assert(Protocol #expr::#guarded(#frag)==IMap::empty().insert(0int,#value));
                 ::vstd::resource::tsm_helpers::guard_value(#left.borrow_token(),0int,#value)
                }});
                continue;
            }
            if guards != 0
                || !op.init.is_empty()
                || op.update.is_some()
                || !(op.special.len() == 1 || op.special.len() == 2)
            {
                return Err(Error::new(
                    name.span(),
                    "counter reader property requires one or two singleton observations",
                ));
            }
            let mut values = vec![];
            for (field, s, b) in &op.special {
                if field != bag || b.is_some() || !matches!(s.stmt, MonoidStmtType::Have) {
                    return Err(Error::new(
                        field.span(),
                        "counter reader property requires singleton Have",
                    ));
                }
                let MonoidElt::SingletonMultiset(e) = &s.elt else {
                    return Err(Error::new(
                        field.span(),
                        "counter reader property requires singleton Have",
                    ));
                };
                values.push(e);
            }
            if values.len() != tr.params.len()
                || tr
                    .params
                    .iter()
                    .zip(values.iter())
                    .any(|(p, e)| !same_type(&p.ty, element) || !is_parameter(e, &p.name))
            {
                return Err(Error::new(
                    name.span(),
                    "counter reader property operands must match payload parameters",
                ));
            }
            let two = values.len() == 2;
            let native = if two {
                quote! {()}
            } else {
                quote! {#right.value()}
            };
            let req = predicate(
                &tr.body,
                false,
                &fields,
                variable,
                native.clone(),
                native.clone(),
                &[],
                &[],
                &quote! {()},
            )?;
            let post = predicate(
                &tr.body,
                true,
                &fields,
                variable,
                native.clone(),
                native,
                &[],
                &[],
                &quote! {()},
            )?;
            let first = values[0];
            let second = values.get(1);
            let secondreq = second.map(|e| quote! {#right.element()==#e,});
            let property_inputs = if two {
                quote! {tracked #left:&#bag #types,tracked #right:&#bag #types}
            } else if sm.fields.iter().position(|f| f.name == *var).unwrap()
                < sm.fields.iter().position(|f| f.name == *bag).unwrap()
            {
                quote! {tracked #right:&#var #types,tracked #left:&#bag #types}
            } else {
                quote! {tracked #left:&#bag #types,tracked #right:&#var #types}
            };
            let rightfacts = if let Some(second) = second {
                quote! {
                 ::vstd::resource::tsm_finite_multiset::finite_multiset_owned_frame(#right.raw@->Some_0.fragment().#bag,#rf.#bag,#state.#bag,#second);
                 assert(#state.#bag.count(#second)>0);
                }
            } else {
                quote! {assert(#state.#var==#right.value());}
            };
            methods.push(quote!{
             pub proof fn #name(tracked &self,#(#params,)*#property_inputs)
              requires #left.instance_id()==self.id(),#right.instance_id()==self.id(),#left.element()==#first,#secondreq #req,
              ensures #post,
             {
              ::vstd::prelude::use_type_invariant(#left);::vstd::prelude::use_type_invariant(#right);
              self.metadata.agrees(&#left.metadata);self.metadata.agrees(&#right.metadata);
              let (#state,#lf,#rf)=#left.borrow_token().compatible_with(#right.borrow_token());
              ::vstd::resource::tsm_finite_multiset::finite_multiset_owned_frame(#left.raw@->Some_0.fragment().#bag,#lf.#bag,#state.#bag,#first);
              assert(#state.#bag.count(#first)>0);#rightfacts
              assert(State #expr::#enabled(#state,#(#pn),*));let _=State #expr::#execute(#state,#(#pn),*);reveal(State::#strong);
             }});
            continue;
        }
        if tr.kind == TransitionKind::Init {
            init_count += 1;
            if op.update.is_some() || !op.special.is_empty() || op.init.len() != 3 {
                return Err(Error::new(
                    name.span(),
                    "counter reader initializer requires all fields",
                ));
            }
            let value = op.init.get(&var.to_string()).unwrap();
            if !is_empty_multiset(op.init.get(&bag.to_string()).unwrap())
                || !is_none(op.init.get(&storage.to_string()).unwrap())
            {
                return Err(Error::new(
                    name.span(),
                    "counter reader initializer requires empty reader and None storage",
                ));
            }
            let req = predicate(
                &tr.body,
                false,
                &fields,
                variable,
                quote! {()},
                quote! {()},
                &[],
                &[],
                &quote! {()},
            )?;
            let actual = fresh(&mut names, "initial_permission");
            let owned = fresh(&mut names, "initial_owned");
            let md = fresh(&mut names, "metadata");
            let result = fresh(&mut names, "result");
            let rawvar = fresh(&mut names, "variable");
            let rawbag = fresh(&mut names, "reader");
            let context = fresh(&mut names, "context");
            let results: Vec<_> = sm
                .fields
                .iter()
                .filter(|f| !f.stype.is_storage())
                .map(|f| {
                    if f.name == *var {
                        quote! {Tracked<#var #types>}
                    } else {
                        quote! {Tracked<#collection #types>}
                    }
                })
                .collect();
            let resultvalues: Vec<_> = sm
                .fields
                .iter()
                .filter(|f| !f.stype.is_storage())
                .map(|f| {
                    if f.name == *var {
                        quote! {Tracked(#rawvar)}
                    } else {
                        quote! {Tracked(#rawbag)}
                    }
                })
                .collect();
            let vi = verus_syn::Index::from(
                1 + sm
                    .fields
                    .iter()
                    .filter(|f| !f.stype.is_storage())
                    .position(|f| f.name == *var)
                    .unwrap(),
            );
            let bi = verus_syn::Index::from(
                1 + sm
                    .fields
                    .iter()
                    .filter(|f| !f.stype.is_storage())
                    .position(|f| f.name == *bag)
                    .unwrap(),
            );
            methods.push(quote!{
             pub proof fn #name(#(#params,)*tracked #actual:Option<#permission>)->(tracked #result:(Tracked<Self>,#(#results),*))
              requires #actual==None,#req,
              ensures #result.#vi@.instance_id()==#result.0@.id(),#result.#vi@.value()==#value,#result.#bi@.instance_id()==#result.0@.id(),#result.#bi@.multiset()==::vstd::multiset::Multiset::empty(),
             {
              let tracked #owned=Protocol #expr::#name(IMap::tracked_empty(),#(#pn),*);
              assert(#owned.fragment()==Fragment #expr::#var_factory(#value));
              let tracked #md=::vstd::resource::tsm_context::Descriptor::alloc(#metadata_type{protocol_location:#owned.loc()});
              #owned.fragment().#take_law();let tracked(#rawvar,#rawbag)=#owned.split(Fragment #expr::#var_factory(#value),Fragment #expr::#bag_factory(::vstd::multiset::Multiset::empty()));
              #rawbag.fragment().op_unit();let tracked(#context,#rawbag)=#rawbag.split(Fragment #expr::empty(),Fragment #expr::#bag_factory(::vstd::multiset::Multiset::empty()));
              let tracked #rawvar=<#var #types>::__from_token(#rawvar,#md.clone());let tracked #rawbag=#collection #expr{raw:#rawbag,metadata:#md.clone()};
              (Tracked(Self{metadata:#md,context:Tracked(Some(#context))}),#(#resultvalues),*)
             }});
            continue;
        }
        if tr.kind != TransitionKind::Transition
            || !selected.contains(&name.to_string())
            || !op.init.is_empty()
            || op.update.as_ref().map(|(n, _)| n) != Some(var)
            || op.special.len() != 1
        {
            return Err(Error::new(name.span(),"counter reader transitions require selected readiness, one variable update and one singleton operation"));
        }
        let (field, s, b) = &op.special[0];
        if b.is_some() {
            return Err(Error::new(
                field.span(),
                "counter reader operation must have an ordinary derived payload",
            ));
        }
        let add = field == bag
            && matches!(
                (&s.stmt, &s.elt),
                (MonoidStmtType::Add(false), MonoidElt::SingletonMultiset(_))
            );
        let remove = field == bag
            && matches!(
                (&s.stmt, &s.elt),
                (MonoidStmtType::Remove, MonoidElt::SingletonMultiset(_))
            );
        let deposit = field == storage
            && matches!(
                (&s.stmt, &s.elt),
                (MonoidStmtType::Deposit, MonoidElt::OptionSome(Some(_)))
            );
        let withdraw = field == storage
            && matches!(
                (&s.stmt, &s.elt),
                (MonoidStmtType::Withdraw, MonoidElt::OptionSome(Some(_)))
            );
        if !(add || remove || deposit || withdraw) {
            return Err(Error::new(
                field.span(),
                "counter reader operation must be a singleton add, remove, deposit or withdraw",
            ));
        }
        if deposit || remove {
            let [p] = tr.params.as_slice() else {
                return Err(Error::new(
                    name.span(),
                    "counter reader consumption requires one payload parameter",
                ));
            };
            let e = match &s.elt {
                MonoidElt::SingletonMultiset(e) | MonoidElt::OptionSome(Some(e)) => e,
                _ => unreachable!(),
            };
            if !same_type(&p.ty, permission) || !is_parameter(e, &p.name) {
                return Err(Error::new(
                    name.span(),
                    "counter reader consumed operand must match payload parameter",
                ));
            }
        } else if !tr.params.is_empty() {
            return Err(Error::new(
                name.span(),
                "counter reader production derives its payload from the ordinary owner",
            ));
        }
        let raw = format_ident!("__reader_{name}_raw");
        let owner = fresh(&mut names, "owner");
        let slot = fresh(&mut names, "slot");
        let consumed = fresh(&mut names, "consumed");
        let actual = fresh(&mut names, "actual");
        let owned = fresh(&mut names, "owned");
        let initial = fresh(&mut names, "initial");
        let before = fresh(&mut names, "before");
        let after = fresh(&mut names, "after");
        let wd = fresh(&mut names, "withdrawn");
        let dep = fresh(&mut names, "deposit");
        let result = fresh(&mut names, "result");
        let payload = fresh(&mut names, "payload");
        let part = fresh(&mut names, "part");
        let rest = fresh(&mut names, "rest");
        let returned = fresh(&mut names, "returned");
        let oldvalue = quote! {old(#slot)@->Some_0.fragment().#var_getter()};
        let rawreq = predicate(
            &tr.body,
            false,
            &fields,
            variable,
            oldvalue.clone(),
            quote! {()},
            &[],
            &[],
            &quote! {()},
        )?;
        let req = predicate(
            &tr.body,
            false,
            &fields,
            variable,
            quote! {old(#owner).value()},
            quote! {()},
            &[],
            &[],
            &quote! {()},
        )?;
        let rawpost = predicate(
            &tr.body,
            true,
            &fields,
            variable,
            oldvalue.clone(),
            quote! {final(#slot)@->Some_0.fragment().#var_getter()},
            &[],
            &[],
            &quote! {()},
        )?;
        let post = predicate(
            &tr.body,
            true,
            &fields,
            variable,
            quote! {old(#owner).value()},
            quote! {final(#owner).value()},
            &[],
            &[],
            &quote! {()},
        )?;
        let rawpayload = operand(&tr.body, &fields, variable, oldvalue.clone())?;
        let publicpayload = operand(&tr.body, &fields, variable, quote! {old(#owner).value()})?;
        let selectedpayload = operand(&tr.body, &fields, variable, quote! {#before.#var})?;
        let bodypayload = operand(&tr.body, &fields, variable, quote! {#initial.#var_getter()})?;
        let rawconsume = if remove {
            quote! {tracked #consumed:#token,}
        } else {
            quote! {}
        };
        let rawconsumereq = if remove {
            quote! {#consumed.loc()==old(#slot)@->Some_0.loc(),#consumed.fragment()==Fragment #expr::#bag_factory(::vstd::multiset::Multiset::singleton(#rawpayload)),}
        } else {
            quote! {}
        };
        let publicconsume = if remove {
            quote! {tracked #consumed:#bag #types,}
        } else {
            quote! {}
        };
        let publicconsumereq = if remove {
            quote! {#consumed.instance_id()==self.id(),#consumed.element()==#publicpayload,}
        } else {
            quote! {}
        };
        let physicalparam = if deposit {
            quote! {tracked #actual:#permission,}
        } else {
            quote! {}
        };
        let physicalreq = if deposit {
            quote! {#actual==#publicpayload,}
        } else {
            quote! {}
        };
        let rawphysicalreq = if deposit {
            quote! {#actual==#rawpayload,}
        } else {
            quote! {}
        };
        let join = if remove {
            quote! {let tracked #owned=#owned.join(#consumed);}
        } else {
            quote! {}
        };
        let pack = if deposit {
            quote! {let tracked #dep=::vstd::resource::tsm_helpers::singleton_map(0int,#actual);}
        } else {
            quote! {}
        };
        let deparg = if deposit {
            quote! {#dep,}
        } else {
            quote! {}
        };
        let observed = format_ident!("{name}_observed");
        let strong = format_ident!("{name}_strong");
        let rawreturn = if add {
            quote! {->(tracked #result:(Ghost<#element>,Tracked<#token>))}
        } else if withdraw {
            quote! {->(tracked #result:#permission)}
        } else {
            quote! {}
        };
        let publicreturn = if add {
            quote! {->(tracked #result:#bag #types)}
        } else if withdraw {
            quote! {->(tracked #result:#permission)}
        } else {
            quote! {}
        };
        let rawresult = if add {
            quote! {#result.0@==#rawpayload,#result.1@.loc()==old(#slot)@->Some_0.loc(),#result.1@.fragment()==Fragment #expr::#bag_factory(::vstd::multiset::Multiset::singleton(#rawpayload)),}
        } else if withdraw {
            quote! {#result==#rawpayload,}
        } else {
            quote! {}
        };
        let publicresult = if add {
            quote! {#result.instance_id()==self.id(),#result.element()==#publicpayload,}
        } else if withdraw {
            quote! {#result==#publicpayload,}
        } else {
            quote! {}
        };
        let take = format_ident!("take_{var}_law");
        let select = format_ident!("select_{var}");
        let without = format_ident!("without_{var}");
        let split = if add {
            quote! {
             #owned.fragment().#take();#owned.fragment().op_unit();let #part=#owned.fragment().#select();let #rest=#owned.fragment().#without();
             assert(#rest==Fragment #expr::#bag_factory(::vstd::multiset::Multiset::singleton(#payload)));
             assert(Fragment #expr::op(#part,#rest)==#owned.fragment());let tracked(#owned,#returned)=#owned.split(#part,#rest);
            }
        } else {
            quote! {}
        };
        let tail = if add {
            quote! {(Ghost(#payload),Tracked(#returned))}
        } else if withdraw {
            quote! {assert(#wd==IMap::empty().insert(0int,#payload));::vstd::resource::tsm_helpers::take_singleton(#wd,0int)}
        } else {
            quote! {}
        };
        let consumeuse = if remove {
            quote! {::vstd::prelude::use_type_invariant(&#consumed);self.metadata.agrees(&#consumed.metadata);}
        } else {
            quote! {}
        };
        let consumearg = if remove {
            quote! {#consumed.raw.get().tracked_unwrap(),}
        } else {
            quote! {}
        };
        let actualarg = if deposit {
            quote! {#actual,}
        } else {
            quote! {}
        };
        let call = quote! {Self::#raw(#(#pn,)*&mut #owner.raw,#consumearg #actualarg)};
        let body = if add {
            quote! {let tracked (#part,#returned)=#call;<#bag #types>::__from_token(#returned.get(),self.metadata.clone(),#part@)}
        } else {
            call
        };
        let inputs: Vec<_> = sm
            .fields
            .iter()
            .filter_map(|f| {
                if f.name == *var {
                    Some(quote! {tracked #owner:&mut #var #types,})
                } else if f.name == *bag && remove {
                    Some(publicconsume.clone())
                } else if f.name == *storage && deposit {
                    Some(physicalparam.clone())
                } else {
                    None
                }
            })
            .collect();
        methods.push(quote!{
        proof fn #raw(#(#params,)*tracked #slot:&mut Tracked<Option<#token>>,#rawconsume #physicalparam)#rawreturn
         requires old(#slot)@ is Some,old(#slot)@->Some_0.fragment()==Fragment #expr::#var_factory(#oldvalue),#rawreq,#rawconsumereq #rawphysicalreq
         ensures final(#slot)@ is Some,final(#slot)@->Some_0.loc()==old(#slot)@->Some_0.loc(),final(#slot)@->Some_0.fragment()==Fragment #expr::#var_factory(final(#slot)@->Some_0.fragment().#var_getter()),#rawpost,#rawresult
        {
         let tracked #owned=#slot.borrow_mut().tracked_take();#join let #initial=#owned.fragment();#pack
         let #payload=#bodypayload;Self::__reader_singleton_normalize(#payload);
         let tracked TransitionObservation #expr{token:#owned,withdrawn:#wd,before:#before,after:#after,..}=Protocol #expr::#observed(#owned,#deparg #(#pn),*);
         reveal(State::#strong);assert(#before.#var==#initial.#var_getter());assert(#payload==#selectedpayload);#split
         assert(#owned.fragment()==Fragment #expr::#var_factory(#after.#var));*#slot=Tracked(Some(#owned));#tail
        }
        pub proof fn #name(tracked &self,#(#params,)*#(#inputs)*)#publicreturn
         requires old(#owner).instance_id()==self.id(),#req,#publicconsumereq #physicalreq
         ensures final(#owner).instance_id()==self.id(),#post,#publicresult
        {::vstd::prelude::use_type_invariant(&*#owner);self.metadata.agrees(&#owner.metadata);#consumeuse #body}
        });
    }
    if init_count == 0 {
        return Err(Error::new(
            sm.name.span(),
            "counter reader facade requires an initializer",
        ));
    }
    Ok(quote! {
     struct #metadata_type{ghost protocol_location: ::vstd::resource::Loc}
     #(#wrappers)*
     #(#attrs)*#[allow(non_camel_case_types)]pub tracked struct #collection #decl #wc{raw:#token,metadata:#descriptor}
     impl #decl #collection #types #wc{
      #[verifier::type_invariant]spec fn invariant(self)->bool{self.raw.loc()==self.metadata.value().protocol_location&&self.raw.fragment()==Fragment #expr::#bag_factory(::vstd::multiset::Multiset::empty())}
      pub closed spec fn instance_id(&self)->::vstd::resource::Loc{self.metadata.id()}
      pub closed spec fn multiset(&self)->::vstd::multiset::Multiset<#element>{::vstd::multiset::Multiset::empty()}
     }
     #(#attrs)*pub tracked struct Instance #decl #wc{metadata:#descriptor,context:Tracked<Option<#token>>}
     impl #decl Instance #types #wc{
      #[verifier::type_invariant]spec fn invariant(self)->bool{!(self.context@ is Some)||self.context@->Some_0.loc()==self.metadata.value().protocol_location&&self.context@->Some_0.fragment()==Fragment #expr::empty()}
      pub closed spec fn id(&self)->::vstd::resource::Loc{self.metadata.id()}
      pub proof fn clone(tracked &self)->(tracked out:Self)ensures out.id()==self.id(){Self{metadata:self.metadata.clone(),context:Tracked(None)}}
      proof fn __reader_singleton_normalize(x:#element)
       ensures ::vstd::multiset::Multiset::<#element>::empty().insert(x)==::vstd::multiset::Multiset::singleton(x),::vstd::multiset::Multiset::<#element>::empty().add(::vstd::multiset::Multiset::empty().insert(x))==::vstd::multiset::Multiset::singleton(x),::vstd::multiset::Multiset::<#element>::singleton(x).sub(::vstd::multiset::Multiset::empty().insert(x))==::vstd::multiset::Multiset::empty(),
      {let inserted=::vstd::multiset::Multiset::<#element>::empty().insert(x);let singleton=::vstd::multiset::Multiset::<#element>::singleton(x);assert(::vstd::prelude::ext_equal(inserted,singleton));assert(::vstd::prelude::ext_equal(::vstd::multiset::Multiset::<#element>::empty().add(inserted),singleton));assert(::vstd::prelude::ext_equal(singleton.sub(inserted),::vstd::multiset::Multiset::empty()));}
      #(#methods)*
     }
    })
}

/// Evaluate the sole singleton operand under its ORIGINAL normal-let scope.
fn operand(
    s: &TransitionStmt,
    fields: &HashMap<String, Field>,
    var: &Field,
    pre: TokenStream,
) -> Result<TokenStream, Error> {
    fn walk(
        s: &TransitionStmt,
        fields: &HashMap<String, Field>,
        var: &Field,
        pre: &TokenStream,
    ) -> Result<Option<TokenStream>, Error> {
        Ok(match s {
            TransitionStmt::Block(_, xs) => {
                let mut value = None;
                for x in xs {
                    if let Some(v) = walk(x, fields, var, pre)? {
                        if value.replace(v).is_some() {
                            return Err(Error::new(
                                *s.get_span(),
                                "counter reader expects one selected operand",
                            ));
                        }
                    }
                }
                value
            }
            TransitionStmt::Split(span, k, xs) => {
                if let SplitKind::Special(_, special, _, None) = &**k {
                    match &special.elt {
                        MonoidElt::SingletonMultiset(e) | MonoidElt::OptionSome(Some(e)) => {
                            Some(lower(e, fields, var, pre.clone(), &[], &[])?)
                        }
                        _ => {
                            return Err(Error::new(
                                *span,
                                "counter reader requires a singleton operand",
                            ))
                        }
                    }
                } else if let SplitKind::Let(p, t, LetKind::Normal, e) = &**k {
                    let e = lower(e, fields, var, pre.clone(), &[], &[])?;
                    let ty = t.as_ref().map(|t| quote! {:#t});
                    let body = walk(&TransitionStmt::Block(*span, xs.clone()), fields, var, pre)?;
                    body.map(|b| quote! {{let #p #ty=#e;#b}})
                } else {
                    return Err(Error::new(
                        *span,
                        "counter reader operand requires sequential normal lets",
                    ));
                }
            }
            _ => None,
        })
    }
    walk(s, fields, var, &pre)?
        .ok_or_else(|| Error::new(*s.get_span(), "counter reader operand missing"))
}

/// Select only the ordinary-derived singleton slice; released explicit-payload
/// reader facades continue through their unchanged emitter.
pub fn needed(sm: &SM) -> bool {
    sm.fields.len() == 3
        && sm
            .fields
            .iter()
            .filter(|f| matches!(f.stype, ShardableType::Variable(_)))
            .count()
            == 1
        && sm
            .fields
            .iter()
            .filter(|f| matches!(f.stype, ShardableType::Multiset(_)))
            .count()
            == 1
        && sm
            .fields
            .iter()
            .filter(|f| matches!(f.stype, ShardableType::StorageOption(_)))
            .count()
            == 1
        && sm
            .transitions
            .iter()
            .any(|tr| tr.kind == TransitionKind::Transition && tr.params.is_empty())
}

// Recognize syntax structurally: proc-macro input may contain transparent groups
// and generic/path spacing unlike a parse_str-based private dump.
fn expression(expr: &Expr) -> &Expr {
    match expr {
        Expr::Group(g) => expression(&g.expr),
        Expr::Paren(p) => expression(&p.expr),
        _ => expr,
    }
}
fn is_parameter(expr: &Expr, name: &Ident) -> bool {
    matches!(expression(expr),Expr::Path(p) if p.qself.is_none()&&p.path.is_ident(name))
}
fn is_none(expr: &Expr) -> bool {
    let Expr::Path(p) = expression(expr) else {
        return false;
    };
    if p.qself.is_some() {
        return false;
    }
    let names: Vec<_> = p
        .path
        .segments
        .iter()
        .map(|s| s.ident.to_string())
        .collect();
    matches!(names.as_slice(),[n] if n=="None")
        || matches!(names.as_slice(),[o,n] if o=="Option"&&n=="None")
}
fn is_empty_multiset(expr: &Expr) -> bool {
    let Expr::Call(c) = expression(expr) else {
        return false;
    };
    let Expr::Path(p) = expression(&c.func) else {
        return false;
    };
    if !c.args.is_empty() || p.qself.is_some() {
        return false;
    }
    let names: Vec<_> = p
        .path
        .segments
        .iter()
        .map(|s| s.ident.to_string())
        .collect();
    matches!(names.as_slice(),[m,e] if m=="Multiset"&&e=="empty")
        || matches!(names.as_slice(),[v,m,ty,e] if v=="vstd"&&m=="multiset"&&ty=="Multiset"&&e=="empty")
}
fn same_type(left: &verus_syn::Type, right: &verus_syn::Type) -> bool {
    struct Ungroup;
    impl verus_syn::visit_mut::VisitMut for Ungroup {
        fn visit_type_mut(&mut self, t: &mut verus_syn::Type) {
            verus_syn::visit_mut::visit_type_mut(self, t);
            match t {
                verus_syn::Type::Group(g) => *t = (*g.elem).clone(),
                verus_syn::Type::Paren(p) => *t = (*p.elem).clone(),
                _ => {}
            }
        }
    }
    use verus_syn::visit_mut::VisitMut;
    let mut a = left.clone();
    let mut b = right.clone();
    Ungroup.visit_type_mut(&mut a);
    Ungroup.visit_type_mut(&mut b);
    a == b
}
