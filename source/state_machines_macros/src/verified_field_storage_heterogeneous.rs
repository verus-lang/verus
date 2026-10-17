//! Checked straight-line heterogeneous optional-storage role facade.
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
    initial: HashMap<String, Expr>,
    updates: HashMap<String, Expr>,
    requires: Vec<Expr>,
    asserts: Vec<Expr>,
    special: Vec<(Ident, SpecialOp)>,
    bindings: Vec<(Ident, Expr)>,
}
fn collect(stmt: &TransitionStmt, out: &mut Ops) -> Result<(), Error> {
    match stmt {
        TransitionStmt::Block(_, xs) => {
            for x in xs {
                collect(x, out)?
            }
        }
        TransitionStmt::Initialize(_, n, e) => {
            if out.initial.insert(n.to_string(), e.clone()).is_some() {
                return Err(Error::new(
                    n.span(),
                    "heterogeneous initialization requires one value per field",
                ));
            }
        }
        TransitionStmt::Update(_, n, e) => {
            if out.updates.insert(n.to_string(), e.clone()).is_some() {
                return Err(Error::new(
                    n.span(),
                    "heterogeneous transition requires one write per variable",
                ));
            }
        }
        TransitionStmt::Require(_, e) => out.requires.push(e.clone()),
        TransitionStmt::Assert(_, e, _) => out.asserts.push(e.clone()),
        TransitionStmt::Split(span, k, xs) => {
            match &**k {
                SplitKind::Let(p, _, LetKind::BirdsEye, e) => {
                    let verus_syn::Pat::Ident(p) = &**p else {
                        return Err(Error::new(
                            *span,
                            "heterogeneous selected binding requires one identifier",
                        ));
                    };
                    out.bindings.push((p.ident.clone(), e.clone()));
                }
                SplitKind::Special(n, op, _, None) => out.special.push((n.clone(), op.clone())),
                _ => {
                    return Err(Error::new(
                        *span,
                        "heterogeneous facade requires straight-line unbound singleton operations",
                    ))
                }
            }
            for x in xs {
                collect(x, out)?
            }
        }
        _ => {
            return Err(Error::new(
                *stmt.get_span(),
                "unsupported heterogeneous facade statement",
            ))
        }
    }
    Ok(())
}
fn names(tokens: TokenStream, out: &mut HashSet<String>) {
    for token in tokens {
        match token {
            proc_macro2::TokenTree::Ident(n) => {
                out.insert(n.to_string());
            }
            proc_macro2::TokenTree::Group(g) => names(g.stream(), out),
            _ => {}
        }
    }
}
fn fresh(sm: &SM, tr: &Transition, label: &str) -> Ident {
    let mut unavailable: HashSet<String> = sm
        .fields
        .iter()
        .map(|f| f.name.to_string())
        .chain(tr.params.iter().map(|p| p.name.to_string()))
        .collect();
    let generics = &sm.generics;
    names(quote! {#generics}, &mut unavailable);
    let mut ops = Ops::default();
    let _ = collect(&tr.body, &mut ops);
    for e in ops
        .initial
        .values()
        .chain(ops.updates.values())
        .chain(ops.requires.iter())
        .chain(ops.asserts.iter())
        .chain(ops.bindings.iter().map(|(_, e)| e))
    {
        names(quote! {#e}, &mut unavailable)
    }
    for (b, _) in ops.bindings {
        unavailable.insert(b.to_string());
    }
    for (_, op) in ops.special {
        match op.elt {
            MonoidElt::General(e)
            | MonoidElt::SingletonSet(e)
            | MonoidElt::SingletonMultiset(e) => names(quote! {#e}, &mut unavailable),
            MonoidElt::OptionSome(Some(e)) => names(quote! {#e}, &mut unavailable),
            _ => {}
        }
    }
    for suffix in 0usize.. {
        let candidate = format!("__tsm_roles_{label}_{suffix}");
        if !unavailable.contains(&candidate) {
            return Ident::new(&candidate, Span::mixed_site());
        }
    }
    unreachable!()
}
fn footprint(
    e: &Expr,
    fields: &HashMap<String, Field>,
    used: &mut HashSet<String>,
) -> Result<(), Error> {
    let mut e = e.clone();
    let mut errors = vec![];
    visit_field_accesses(
        &mut e,
        |_, f, _| {
            used.insert(f.name.to_string());
        },
        &mut errors,
        fields,
    );
    if let Some(e) = errors.into_iter().next() {
        return Err(e);
    }
    Ok(())
}
fn lower(
    e: &Expr,
    fields: &HashMap<String, Field>,
    values: &HashMap<String, TokenStream>,
) -> Result<TokenStream, Error> {
    let mut e = e.clone();
    let mut errors = vec![];
    visit_field_accesses(
        &mut e,
        |errors, f, node| {
            if let Some(value) = values.get(&f.name.to_string()) {
                *node = Expr::Verbatim(value.clone());
            } else {
                errors.push(Error::new(
                    f.name.span(),
                    "heterogeneous expression requires a supplied actual role observation",
                ));
            }
        },
        &mut errors,
        fields,
    );
    if let Some(e) = errors.into_iter().next() {
        return Err(e);
    }
    Ok(quote! {#e})
}
fn payload(field: &Field, elt: &MonoidElt) -> Result<TokenStream, Error> {
    Ok(match (&field.stype, elt) {
        (ShardableType::Count, MonoidElt::General(e)) => quote! {#e},
        (ShardableType::Set(_), MonoidElt::SingletonSet(e)) => quote! {#e},
        (ShardableType::Multiset(_), MonoidElt::SingletonMultiset(e)) => quote! {#e},
        (ShardableType::Option(_), MonoidElt::OptionSome(Some(e))) => quote! {#e},
        (ShardableType::Option(_),MonoidElt::General(e))=>{let e=ungroup(e);let Expr::Call(call)=e else{return Err(Error::new(field.name.span(),"optional operand requires explicit Some"));};if !matches!(&*call.func,Expr::Path(path)if path.path.is_ident("Some"))||call.args.len()!=1{return Err(Error::new(field.name.span(),"optional operand requires explicit Some"));}let value=&call.args[0];quote!{#value}},
        _ => {
            return Err(Error::new(
                field.name.span(),
                "heterogeneous role requires Count or singleton Set/Option operand",
            ))
        }
    })
}
fn contribution(field: &Field, value: &TokenStream) -> TokenStream {
    match &field.stype {
        ShardableType::Option(_) => quote! {Some(#value)},
        ShardableType::Set(t) => quote! {::vstd::set::Set::<#t>::empty().insert(#value)},
        ShardableType::Multiset(t) => quote! {::vstd::multiset::Multiset::<#t>::singleton(#value)},
        _ => value.clone(),
    }
}
fn getter(field: &Field) -> Ident {
    match &field.stype {
        ShardableType::Count => format_ident!("count"),
        ShardableType::Set(_) | ShardableType::Multiset(_) => format_ident!("element"),
        _ => format_ident!("value"),
    }
}
fn output_value(field: &Field, part: TokenStream) -> TokenStream {
    let get = format_ident!("value_{}", field.name);
    match &field.stype {
        ShardableType::Option(_) => quote! {#part.#get()->Some_0},
        ShardableType::Count | ShardableType::Variable(_) => quote! {#part.#get()},
        ShardableType::Multiset(t) => {
            quote! {choose|element:#t|#part.#get()==::vstd::multiset::Multiset::<#t>::singleton(element)}
        }
        _ => quote! {()},
    }
}
fn sum(parts: &[TokenStream], expr: &TokenStream) -> TokenStream {
    parts.iter().skip(1).fold(
        parts
            .first()
            .cloned()
            .unwrap_or_else(|| quote! {Fragment #expr::empty()}),
        |acc, x| quote! {Fragment #expr::op(#acc,#x)},
    )
}

pub fn output(sm: &SM, selected: &HashSet<String>) -> Result<TokenStream, Error> {
    let storage: Vec<_> = sm.fields.iter().filter(|f| f.stype.is_storage()).collect();
    if storage.len() != 1
        || sm.fields.iter().any(|f| {
            !matches!(
                f.stype,
                ShardableType::Variable(_)
                    | ShardableType::Constant(_)
                    | ShardableType::Count
                    | ShardableType::Set(_)
                    | ShardableType::Multiset(_)
                    | ShardableType::Option(_)
                    | ShardableType::StorageOption(_)
            )
        })
    {
        return Err(Error::new(sm.name.span(),"heterogeneous facade currently requires variables, constants, Count, Set, Option and one optional store"));
    }
    // Generated metadata fields and inherent methods share the caller's module.
    // Reject collisions explicitly instead of silently shadowing a source name.
    let mut api_names: HashSet<String> = ["id", "clone", "__roles_read_included"]
        .iter()
        .map(|name| name.to_string())
        .collect();
    for tr in &sm.transitions {
        let helper = format!("__physical_roles_raw_{}", tr.name);
        if !api_names.insert(helper) {
            return Err(Error::new(
                tr.name.span(),
                "heterogeneous generated helper name collision",
            ));
        }
    }
    for field in sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::Constant(_)))
    {
        if matches!(
            field.name.to_string().as_str(),
            "protocol_location" | "marker"
        ) || !api_names.insert(field.name.to_string())
        {
            return Err(Error::new(
                field.name.span(),
                "heterogeneous constant conflicts with generated metadata or method",
            ));
        }
    }
    for tr in &sm.transitions {
        if !api_names.insert(tr.name.to_string()) {
            return Err(Error::new(
                tr.name.span(),
                "heterogeneous transition conflicts with generated method",
            ));
        }
    }
    let ShardableType::StorageOption(permission) = &storage[0].stype else {
        return Err(Error::new(
            storage[0].name.span(),
            "heterogeneous facade requires one optional store",
        ));
    };
    let storage = storage[0];
    let constants: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::Constant(_)))
        .collect();
    let ordinary: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| !matches!(f.stype, ShardableType::Constant(_)) && !f.stype.is_storage())
        .collect();
    let (g, attrs) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = generics_for_decl(&g);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let types = args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default();
    let expr = args.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default();
    let token = quote! {Token #types};
    let metadata = quote! {__HeterogeneousStorageMetadata #types};
    let descriptor = quote! {::vstd::resource::tsm_context::Descriptor<#metadata>};
    let location = format_ident!("protocol_location");
    let marker = args
        .as_ref()
        .map(|a| quote! {ghost marker:core::marker::PhantomData<(#a,)>,});
    let markerv = args
        .as_ref()
        .map(|_| quote! {marker:core::marker::PhantomData,});
    let cn: Vec<_> = constants.iter().map(|f| &f.name).collect();
    let ct: Vec<_> = constants.iter().map(|f| f.get_type()).collect();
    let setters: Vec<_> = cn.iter().map(|n| format_ident!("with_{n}")).collect();
    let cget: Vec<_> = cn.iter().map(|n| format_ident!("value_{n}")).collect();
    let fields: HashMap<_, _> = sm
        .fields
        .iter()
        .map(|f| (f.name.to_string(), f.clone()))
        .collect();
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
    let mut wrappers = vec![];
    let original_fields = &sm.fields_named_ast;
    let collection_reservation = quote! {#original_fields};
    for field in &ordinary {
        wrappers.push(roles::wrapper(field, &cx)?);
        if matches!(&field.stype, ShardableType::Set(_) | ShardableType::Multiset(_)) {
            wrappers.push(crate::verified_field_storage_collections::wrapper(field, &cx, &collection_reservation)?);

        }
        if matches!(field.stype, ShardableType::Count) {
            let n = &field.name;
            let split = roles::count_split_method(field, &cx)?;
            let join = roles::count_join_method(field, &cx)?;
            wrappers.push(quote! {impl #decl #n #types #wc{#split #join}});
        }

    }
    let mut methods = vec![];
    for tr in &sm.transitions {
        let name = &tr.name;
        let mut ops = Ops::default();
        collect(&tr.body, &mut ops)?;
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
            if ops.initial.len() != sm.fields.len() {
                return Err(Error::new(
                    name.span(),
                    "heterogeneous initializer requires all fields",
                ));
            }
            let initial_constants: Vec<_> =
                cn.iter().map(|n| &ops.initial[&n.to_string()]).collect();
            let storage_value = &ops.initial[&storage.name.to_string()];
            let actual = fresh(sm, tr, "initial_actual");
            let deposit = fresh(sm, tr, "initial_deposit");
            let remaining = fresh(sm, tr, "initial_remaining");
            let md = fresh(sm, tr, "initial_metadata");
            let part = fresh(sm, tr, "initial_part");
            let rest = fresh(sm, tr, "initial_rest");
            let mut splits = vec![];
            let mut output_types = vec![];
            let mut output_values = vec![];
            let mut output_ens = vec![];
            for (index, field) in ordinary.iter().enumerate() {
                let n = &field.name;
                let value = &ops.initial[&n.to_string()];
                let ix = verus_syn::Index::from(index + 1);
                match &field.stype {
                    ShardableType::Option(_) => {
                        if !none_initializer(value) {
                            return Err(Error::new(
                                n.span(),
                                "heterogeneous optional initializer currently requires None",
                            ));
                        }
                        output_types.push(quote! {Tracked<Option<#n #types>>});
                        output_values.push(quote! {Tracked(None)});
                        output_ens.push(quote! {out.#ix@ is None});
                    }
                    _ => {
                        let owner = fresh(sm, tr, &format!("initial_owner_{n}"));
                        let select = format_ident!("select_{n}");
                        let without = format_ident!("without_{n}");
                        let law = format_ident!("take_{n}_law");
                        let role_type = if matches!(
                            field.stype,
                            ShardableType::Set(_) | ShardableType::Multiset(_)
                        ) {
                            format_ident!("{n}_collection")
                        } else {
                            n.clone()
                        };
                        if matches!(
                            field.stype,
                            ShardableType::Set(_) | ShardableType::Multiset(_)
                        ) && !empty_collection_initializer(value, if matches!(field.stype, ShardableType::Set(_)) { "Set" } else { "Multiset" })
                        {
                            return Err(Error::new(
                                n.span(),
                                "heterogeneous Set initializer currently requires empty collection",
                            ));
                        }
                        splits.push(quote!{#remaining.fragment().#law();let #part=#remaining.fragment().#select()#(.#setters(#initial_constants))*;let #rest=#remaining.fragment().#without();assert(Fragment #expr::op(#part,#rest)==#remaining.fragment());let tracked(#owner,#remaining)=#remaining.split(#part,#rest);});
                        if matches!(
                            field.stype,
                            ShardableType::Set(_) | ShardableType::Multiset(_)
                        ) {
                            output_values.push(
                                quote! {Tracked(<#role_type #types>::__from_token(#owner,#md.clone(),#value))},
                            );
                            let get = if matches!(field.stype, ShardableType::Set(_)) {
                                format_ident!("set")
                            } else {
                                format_ident!("multiset")
                            };
                            output_ens.push(quote! {out.#ix@.#get()==#value});
                        } else {
                            splits.push(quote!{let tracked #owner=<#n #types>::__from_token(#owner,#md.clone());});
                            let get = getter(field);
                            output_values.push(quote! {Tracked(#owner)});
                            output_ens.push(quote! {out.#ix@.#get()==#value});
                        }
                        output_types.push(quote! {Tracked<#role_type #types>});
                        output_ens.push(quote! {out.#ix@.instance_id()==out.0@.id()});
                    }
                }
            }
            let requirements = &ops.requires;
            methods.push(quote!{
 pub proof fn #name(#(#params,)*tracked #actual:Option<#permission>)->(tracked out:(Tracked<Self>,#(#output_types),*))
 requires #(#requirements,)*#actual==#storage_value,
 ensures #(#output_ens,)*#(out.0@.#cn()==#initial_constants,)*
 {let tracked #deposit=match #actual{Some(actual)=>::vstd::resource::tsm_helpers::singleton_map(0int,actual),None=>IMap::<int,#permission>::tracked_empty()};
 let tracked #remaining=Protocol #expr::#name(#deposit,#(#pn),*);let tracked #md=::vstd::resource::tsm_context::Descriptor::alloc(__HeterogeneousStorageMetadata #expr{protocol_location:#remaining.loc(),#(#cn:#initial_constants,)*#markerv});
 #(#splits)*
 (Tracked(Self{metadata:#md.clone(),context:Tracked(Some(#remaining))}),#(#output_values),*)}
 });
            continue;
        }
        if tr.kind == TransitionKind::Property && ops.special.iter().any(|(_,op)|matches!(op.stmt,MonoidStmtType::Guard)) {
            methods.push(physical_guard(sm,tr,&ops,&fields,&constants,&types,&expr)?);continue;
        }
        if tr.kind == TransitionKind::Property {
            methods.push(property(
                sm, tr, &ops, &fields, &constants, &decl, &types, &expr, &token,
            )?);
            continue;
        }
        if !selected.contains(&name.to_string()) {
            return Err(Error::new(
                name.span(),
                "heterogeneous facade requires checked selected readiness",
            ));
        }
        methods.push(transition(
            sm,
            tr,
            &ops,
            &fields,
            &constants,
            storage,
            &decl,
            &types,
            &expr,
            &token,
            &descriptor,
        )?);
    }
    Ok(quote! {
    #(#attrs)*struct __HeterogeneousStorageMetadata #decl #wc{ghost protocol_location: ::vstd::resource::Loc,#(ghost #cn:#ct,)*#marker}
    #(#wrappers)*
    #(#attrs)*pub tracked struct Instance #decl #wc{metadata:#descriptor,context:Tracked<Option<#token>>}
    impl #decl Instance #types #wc{
    #[verifier::type_invariant]spec fn invariant(self)->bool{::vstd::prelude::imply(self.context@ is Some,self.context@->Some_0.loc()==self.metadata.value().protocol_location&&self.context@->Some_0.fragment()==Fragment #expr::empty()#(.#setters(self.metadata.value().#cn))*)}
    pub closed spec fn id(&self)->::vstd::resource::Loc{self.metadata.id()}
    #(pub closed spec fn #cn(&self)->#ct{self.metadata.value().#cn})*
    pub proof fn clone(tracked &self)->(tracked out:Self)ensures out.id()==self.id(),#(out.#cn()==self.#cn(),)*{Self{metadata:self.metadata.clone(),context:Tracked(None)}}
    proof fn __roles_read_included(source:Fragment #types,middle:Fragment #types,target:Fragment #types)
    requires ::vstd::resource::tsm::fragment_included::<Protocol #types>(source,middle),::vstd::resource::tsm::fragment_included::<Protocol #types>(middle,target),
    ensures ::vstd::resource::tsm::fragment_included::<Protocol #types>(source,target),
    {let a=choose|a:Fragment #types|Fragment #expr::op(source,a)==middle;let b=choose|b:Fragment #types|Fragment #expr::op(middle,b)==target;Fragment #expr::associative(source,a,b);assert(Fragment #expr::op(source,Fragment #expr::op(a,b))==target);}
    #(#methods)*
    }
    })
}

fn property(
    sm: &SM,
    tr: &Transition,
    ops: &Ops,
    fields: &HashMap<String, Field>,
    constants: &[&Field],
    _decl: &TokenStream,
    types: &TokenStream,
    expr: &TokenStream,
    _token: &TokenStream,
) -> Result<TokenStream, Error> {
    if !ops.bindings.is_empty() || !ops.updates.is_empty() {
        return Err(Error::new(
            tr.name.span(),
            "heterogeneous property requires unbound readonly observations",
        ));
    }
    let mut used = HashSet::new();
    for e in ops.requires.iter().chain(ops.asserts.iter()) {
        footprint(e, fields, &mut used)?;
    }
    let mut has = HashMap::new();
    for (n, op) in &ops.special {
        if !matches!(op.stmt, MonoidStmtType::Have)
            || has.insert(n.to_string(), op.clone()).is_some()
        {
            return Err(Error::new(
                n.span(),
                "heterogeneous property supports one Have per role and no physical guard yet",
            ));
        }
        used.insert(n.to_string());
    }
    let supplied: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| {
            used.contains(&f.name.to_string()) && !matches!(f.stype, ShardableType::Constant(_))
        })
        .collect();
    if supplied.is_empty() {
        return Err(Error::new(
            tr.name.span(),
            "heterogeneous property requires actual readonly roles",
        ));
    }
    let arguments: HashMap<_, _> = supplied
        .iter()
        .map(|f| {
            (
                f.name.to_string(),
                fresh(sm, tr, &format!("property_input_{}", f.name)),
            )
        })
        .collect();
    let mut values: HashMap<String, TokenStream> = constants
        .iter()
        .map(|f| {
            let n = &f.name;
            (n.to_string(), quote! {self.#n()})
        })
        .collect();
    for f in &supplied {
        if matches!(f.stype, ShardableType::Variable(_)) {
            let a = &arguments[&f.name.to_string()];
            values.insert(f.name.to_string(), quote! {#a.value()});
        }
    }
    let mut pre: Vec<_> = ops
        .requires
        .iter()
        .map(|e| lower(e, fields, &values))
        .collect::<Result<_, _>>()?;
    for f in &supplied {
        if let Some(op) = has.get(&f.name.to_string()) {
            let a = &arguments[&f.name.to_string()];
            let p: Expr = verus_syn::parse2(payload(f, &op.elt)?)?;
            let value = lower(&p, fields, &values)?;
            pre.push(match f.stype {
                ShardableType::Count => quote! {#value<=#a.count()},
                ShardableType::Set(_) | ShardableType::Multiset(_) => quote! {#a.element()==#value},
                ShardableType::Option(_) => quote! {#a.value()==#value},
                _ => {
                    return Err(Error::new(
                        f.name.span(),
                        "heterogeneous property Have requires Count, Set or Option",
                    ))
                }
            });
        }
    }
    let post: Vec<_> = ops
        .asserts
        .iter()
        .map(|e| lower(e, fields, &values))
        .collect::<Result<_, _>>()?;
    let names: Vec<_> = supplied
        .iter()
        .map(|f| &arguments[&f.name.to_string()])
        .collect();
    let roletypes: Vec<_> = supplied.iter().map(|f| &f.name).collect();
    let observations: Vec<_> = supplied
        .iter()
        .map(|f| fresh(sm, tr, &format!("property_observation_{}", f.name)))
        .collect();
    let first = &observations[0];
    let upper = fresh(sm, tr, "property_upper");
    let previous = fresh(sm, tr, "property_previous");
    let before = fresh(sm, tr, "property_before");
    let outer = fresh(sm, tr, "property_outer");
    let frame = fresh(sm, tr, "property_frame");
    let post_state = fresh(sm, tr, "property_post");
    let merges:Vec<_>=observations.iter().enumerate().skip(1).map(|(i,read)|{let prior=&names[..i];let trans=if i>1{quote!{#(Self::__roles_read_included(#prior.raw@->Some_0.fragment(),#previous,#upper.fragment());)*}}else{quote!{}};quote!{let #previous=#upper.fragment();let tracked #upper=#upper.join(&#read);#trans}}).collect();
    let mut inclusions = vec![];
    for (f, a) in supplied.iter().zip(&names) {
        let n = &f.name;
        let raw = quote! {#a.raw@->Some_0.fragment()};
        let relation = match f.stype {
            ShardableType::Variable(_) => quote! {#before.#n==#a.value()},
            ShardableType::Option(_) => quote! {#before.#n==Some(#a.value())},
            ShardableType::Count => quote! {#a.count()<=#before.#n},
            ShardableType::Set(_) => quote! {#before.#n.contains(#a.element())},
            ShardableType::Multiset(_) => quote! {#before.#n.count(#a.element())>=1},
            _ => unreachable!(),
        };
        inclusions.push(quote!{let #frame=choose|#frame:Fragment #types|Fragment #expr::op(#raw,#frame)==#upper.fragment();Fragment #expr::associative(#raw,#frame,#outer);assert(Fragment #expr::op(#raw,Fragment #expr::op(#frame,#outer))==Protocol #expr::embed(#before));assert(#relation);});
    }
    let single_inclusion=if supplied.len()==1{let a=&names[0];quote!{#a.raw@->Some_0.fragment().op_unit();assert(exists|frame:Fragment #types|Fragment #expr::op(#a.raw@->Some_0.fragment(),frame)==#upper.fragment());}}else{quote!{}};
    let name = &tr.name;
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
    let execute = format_ident!("{name}_execute");
    Ok(quote! {
    pub proof fn #name(tracked &self,#(#params,)*#(tracked #names:&#roletypes #types,)*)
    requires #(#names.instance_id()==self.id(),)*#(#pre,)*ensures #(#post,)*
    {#(::vstd::prelude::use_type_invariant(#names);self.metadata.agrees(&#names.metadata);let tracked #observations=#names.raw.borrow().tracked_borrow().observe();)*
    let tracked #upper=#first;#(#merges)*#single_inclusion #upper.validate();let(#before,#outer)=choose|before:State #types,outer:Fragment #types|before.invariant()&&Fragment #expr::op(#upper.fragment(),outer)==Protocol #expr::embed(before);
    #(#inclusions)*let #post_state=State #expr::#execute(#before,#(#pn),*);
    }
    })
}

fn transition(
    sm: &SM,
    tr: &Transition,
    ops: &Ops,
    fields: &HashMap<String, Field>,
    constants: &[&Field],
    storage: &Field,
    _decl: &TokenStream,
    types: &TokenStream,
    expr: &TokenStream,
    token: &TokenStream,
    _descriptor: &TokenStream,
) -> Result<TokenStream, Error> {
    if ops.updates.len() > 1 {
        return Err(Error::new(
            tr.name.span(),
            "heterogeneous transition currently supports one mutable variable",
        ));
    }
    let mut removed = None;
    let mut added = None;
    let mut physical = None;
    let mut have = HashMap::new();
    for (n, op) in &ops.special {
        match op.stmt {
            MonoidStmtType::Remove => {
                if removed
                    .replace((fields[&n.to_string()].clone(), op.clone()))
                    .is_some()
                {
                    return Err(Error::new(
                        n.span(),
                        "heterogeneous transition currently consumes one role",
                    ));
                }
            }
            MonoidStmtType::Add(false) => {
                if added
                    .replace((fields[&n.to_string()].clone(), op.clone()))
                    .is_some()
                {
                    return Err(Error::new(
                        n.span(),
                        "heterogeneous transition currently produces one role",
                    ));
                }
            }
            MonoidStmtType::Have => {
                if have.insert(n.to_string(), op.clone()).is_some() {
                    return Err(Error::new(
                        n.span(),
                        "heterogeneous transition requires one Have per role",
                    ));
                }
            }
            MonoidStmtType::Deposit | MonoidStmtType::Withdraw => {
                if *n != storage.name || physical.replace(op.clone()).is_some() {
                    return Err(Error::new(
                        n.span(),
                        "heterogeneous transition requires one singleton physical transfer",
                    ));
                }
            }
            _ => {
                return Err(Error::new(
                    n.span(),
                    "unsupported heterogeneous transition operation",
                ))
            }
        }
    }
    let mutable = ops.updates.keys().next().map(|n| &fields[n]);
    if mutable.is_none() && removed.is_none() {
        return Err(Error::new(
            tr.name.span(),
            "heterogeneous transition requires actual mutable or consumed ownership",
        ));
    }
    if physical
        .as_ref()
        .is_some_and(|op| !matches!(op.elt, MonoidElt::OptionSome(Some(_))))
    {
        return Err(Error::new(
            tr.name.span(),
            "heterogeneous physical operation requires explicit singleton payload",
        ));
    }
    let storage_name = &storage.name;
    let withdrawing = physical
        .as_ref()
        .is_some_and(|p| matches!(p.stmt, MonoidStmtType::Withdraw));
    let depositing = physical
        .as_ref()
        .is_some_and(|p| matches!(p.stmt, MonoidStmtType::Deposit));
    if withdrawing && added.is_none() {
        return Err(Error::new(
            tr.name.span(),
            "heterogeneous withdrawal currently returns one produced logical role",
        ));
    }
    let mut used: HashSet<_> = ops.updates.keys().cloned().collect();
    for e in ops
        .updates
        .values()
        .chain(ops.requires.iter())
        .chain(ops.asserts.iter())
    {
        footprint(e, fields, &mut used)?;
    }
    for (_, op) in &ops.special {
        if let Some(e) = match &op.elt {
            MonoidElt::General(e)
            | MonoidElt::SingletonSet(e)
            | MonoidElt::SingletonMultiset(e) => Some(e),
            MonoidElt::OptionSome(Some(e)) => Some(e),
            _ => None,
        } {
            footprint(e, fields, &mut used)?;
        }
    }
    let mut supplied: Vec<&Field> = sm
        .fields
        .iter()
        .filter(|f| {
            !matches!(f.stype, ShardableType::Constant(_))
                && (used.contains(&f.name.to_string())
                    || have.contains_key(&f.name.to_string())
                    || removed.as_ref().is_some_and(|(r, _)| r.name == f.name))
        })
        .collect();
    if supplied.iter().any(|f| f.stype.is_storage()) {
        return Err(Error::new(
            tr.name.span(),
            "heterogeneous transition cannot observe physical metadata as ordinary ownership",
        ));
    }
    supplied.retain(|f| !f.stype.is_storage());
    let readonly: Vec<_> = supplied
        .iter()
        .filter(|f| {
            mutable.is_none_or(|m| m.name != f.name)
                && removed.as_ref().is_none_or(|(r, _)| r.name != f.name)
        })
        .copied()
        .collect();
    if readonly.len() > 1
        && readonly
            .iter()
            .any(|f| !matches!(f.stype, ShardableType::Variable(_)))
    {
        return Err(Error::new(
            tr.name.span(),
            "heterogeneous transition currently supports one separately borrowed role",
        ));
    }
    if withdrawing && readonly.is_empty() {
        return Err(Error::new(
            tr.name.span(),
            "heterogeneous withdrawal currently requires a separate actual readonly observation",
        ));
    }
    for f in &readonly {
        if !matches!(f.stype, ShardableType::Variable(_)) && !have.contains_key(&f.name.to_string())
        {
            return Err(Error::new(
                f.name.span(),
                "heterogeneous logical readonly role requires Have",
            ));
        }
    }
    let arguments: HashMap<_, _> = supplied
        .iter()
        .map(|f| {
            (
                f.name.to_string(),
                fresh(sm, tr, &format!("input_{}", f.name)),
            )
        })
        .collect();
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
    let slot = fresh(sm, tr, "slot");
    let consumed = fresh(sm, tr, "consumed");
    let observation = fresh(sm, tr, "observation");
    let output = fresh(sm, tr, "output");
    let actual = fresh(sm, tr, "actual");
    let remaining = fresh(sm, tr, "remaining");
    let owned = fresh(sm, tr, "owned");
    let initial = fresh(sm, tr, "initial");
    let before = fresh(sm, tr, "before");
    let after = fresh(sm, tr, "after");
    let withdrawn = fresh(sm, tr, "withdrawn");
    let deposited = fresh(sm, tr, "deposited");
    let dep = fresh(sm, tr, "deposit_value");
    let part = fresh(sm, tr, "part");
    let rest = fresh(sm, tr, "rest");
    let result = fresh(sm, tr, "result");
    let physical_value = fresh(sm, tr, "physical_value");
    let payload_value = fresh(sm, tr, "payload_value");
    let pair = fresh(sm, tr, "pair");
    let choices = fresh(sm, tr, "choices");
    let name = &tr.name;
    let raw = format_ident!("__physical_roles_raw_{name}");
    let local = format_ident!("{name}_local_requires");
    let ready = format_ident!("{name}_local_ready");
    let frame = format_ident!("{name}_frame");
    let outputs = format_ident!("{name}_outputs");
    let witness = format_ident!("{name}_witness");
    let local_op = format_ident!("{name}_local");
    let cn: Vec<_> = constants.iter().map(|f| &f.name).collect();
    let setters: Vec<_> = cn.iter().map(|n| format_ident!("with_{n}")).collect();
    let cget: Vec<_> = cn.iter().map(|n| format_ident!("value_{n}")).collect();
    let old_mut = quote! {old(#slot)@->Some_0.fragment()};
    let consumed_fragment = quote! {#consumed.fragment()};
    let mut raw_parts = vec![];
    if mutable.is_some() {
        raw_parts.push(old_mut.clone())
    }
    if removed.is_some() {
        raw_parts.push(consumed_fragment.clone())
    }
    let raw_initial = sum(&raw_parts, expr);
    let h = if readonly.is_empty() {
        quote! {Fragment #expr::empty()}
    } else {
        quote! {#observation.fragment()}
    };
    let prefragment = quote! {Fragment #expr::op(#raw_initial,#h)};
    let anchor = if mutable.is_some() {
        old_mut.clone()
    } else {
        consumed_fragment.clone()
    };
    let raw_constants: Vec<_> = cget.iter().map(|g| quote! {(#anchor).#g()}).collect();
    let mut public_values: HashMap<String, TokenStream> = constants
        .iter()
        .map(|f| {
            let n = &f.name;
            (n.to_string(), quote! {self.#n()})
        })
        .collect();
    let mut old_values = public_values.clone();
    let mut raw_values: HashMap<String, TokenStream> = constants
        .iter()
        .map(|f| {
            let g = format_ident!("value_{}", f.name);
            (f.name.to_string(), quote! {(#prefragment).#g()})
        })
        .collect();
    for f in &supplied {
        if matches!(f.stype, ShardableType::Variable(_)) {
            let a = &arguments[&f.name.to_string()];
            let g = format_ident!("value_{}", f.name);
            public_values.insert(f.name.to_string(), quote! {#a.value()});
            old_values.insert(
                f.name.to_string(),
                if mutable.is_some_and(|m| m.name == f.name) {
                    quote! {old(#a).value()}
                } else {
                    quote! {#a.value()}
                },
            );
            raw_values.insert(f.name.to_string(), quote! {(#prefragment).#g()});
        }
    }
    let raw_token_output = if withdrawing {
        quote! {#output.0}
    } else {
        quote! {#output}
    };
    let mut snapshot = None;
    if let Some((f, op)) = &added {
        if let (ShardableType::Option(t), MonoidElt::OptionSome(Some(Expr::Tuple(tuple)))) =
            (&f.stype, &op.elt)
        {
            if let verus_syn::Type::Tuple(ts) = t {
                if tuple.elems.len() == ts.elems.len()
                    && ops
                        .bindings
                        .iter()
                        .any(|(_, e)| lower(e, fields, &old_values).is_err())
                    && !withdrawing
                {
                    snapshot = Some((tuple.clone(), ts.clone()));
                }
            }
        }
    }
    let hidden_element = added.as_ref().is_some_and(|(f,op)| matches!((&f.stype,&op.elt),(ShardableType::Multiset(_),MonoidElt::SingletonMultiset(Expr::Path(path))) if ops.bindings.iter().any(|(binding,e)| path.path.is_ident(binding) && lower(e,fields,&old_values).is_err())));
    let physical_first=withdrawing&&added.as_ref().is_some_and(|(role,_)|sm.fields.iter().position(|f|f.name==storage.name)<sm.fields.iter().position(|f|f.name==role.name));
    let public_output_owner = if hidden_element {
        quote!{#output.1@}
    } else if withdrawing && physical_first {
        quote! {#output.2@}
    } else if withdrawing {
        quote! {#output.0@}
    } else if let Some((tuple, _)) = &snapshot {
        let i = verus_syn::Index::from(tuple.elems.len());
        quote! {#output.#i@}
    } else {
        quote! {#output}
    };
    let mut raw_binding_values = HashMap::new();
    let mut public_binding_values = HashMap::new();
    for (binding, e) in &ops.bindings {
        if let (Ok(raw), Ok(public)) =
            (lower(e, fields, &raw_values), lower(e, fields, &old_values))
        {
            raw_binding_values.insert(binding.to_string(), raw);
            public_binding_values.insert(binding.to_string(), public);
            continue;
        }
        if withdrawing
            && stored_option_binding(e, storage_name)
        {
            raw_binding_values.insert(binding.to_string(), quote! {#output.1});
            public_binding_values.insert(binding.to_string(),if physical_first{quote!{#output.1@}}else{quote! {#output.2@}});
            continue;
        }
        if let Some((tuple, _)) = &snapshot {
            if let Some(i) = tuple
                .elems
                .iter()
                .position(|e| matches!(e,Expr::Path(p)if p.path.is_ident(binding)))
            {
                let ix = verus_syn::Index::from(i);
                let produced = added.as_ref().unwrap().0.clone();
                let v = output_value(&produced, quote! {#raw_token_output.fragment()});
                raw_binding_values.insert(binding.to_string(), quote! {(#v).#ix});
                public_binding_values.insert(binding.to_string(), quote! {#output.#ix@});
                continue;
            }
        }
        if hidden_element
            && stored_option_binding(e, storage_name)
        {
            let produced = &added.as_ref().unwrap().0;
            raw_binding_values.insert(
                binding.to_string(),
                output_value(produced, quote! {#raw_token_output.fragment()}),
            );
            public_binding_values
                .insert(binding.to_string(), quote! {#public_output_owner.element()});
            continue;
        }
        return Err(Error::new(binding.span(),"heterogeneous selected binding must use actual supplied fields, withdrawn value, or produced tuple owner"));
    }
    let bind_block = |body: TokenStream, values: &HashMap<String, TokenStream>| {
        ops.bindings.iter().rev().fold(body, |body, (binding, _)| {
            let value = &values[&binding.to_string()];
            quote! {{let #binding=#value;#body}}
        })
    };
    let mut public_requires: Vec<_> = ops
        .requires
        .iter()
        .map(|e| lower(e, fields, &public_values))
        .collect::<Result<_, _>>()?;
    let mut raw_requires = vec![];
    let mut public_post = vec![];
    let mut raw_post = vec![];
    for e in &ops.asserts {
        public_post.push(bind_block(
            lower(e, fields, &old_values)?,
            &public_binding_values,
        ));
        raw_post.push(bind_block(
            lower(e, fields, &raw_values)?,
            &raw_binding_values,
        ));
    }
    let loc = if mutable.is_some() {
        quote! {old(#slot)@->Some_0.loc()}
    } else {
        quote! {#consumed.loc()}
    };
    if let Some(m) = mutable {
        let factory = format_ident!("field_{}", m.name);
        let g = format_ident!("value_{}", m.name);
        let own = format_ident!("owns_{}", m.name);
        let factory_set = format_ident!("with_{}", m.name);
        raw_requires.push(quote! {old(#slot)@ is Some});
        raw_requires.push(quote! {old(#slot)@->Some_0.fragment().#own()});
        raw_requires.push(quote!{old(#slot)@->Some_0.fragment()==Fragment #expr::#factory(old(#slot)@->Some_0.fragment().#g())#(.#setters(#raw_constants))*});
        let a = &arguments[&m.name.to_string()];
        let update = &ops.updates[&m.name.to_string()];
        let public_update = lower(update, fields, &old_values)?;
        let raw_update = lower(update, fields, &raw_values)?;
        public_post.push(quote! {final(#a).value()==#public_update});
        raw_post.push(quote! {final(#slot)@ is Some});
        raw_post.push(quote! {final(#slot)@->Some_0.loc()==#loc});
        raw_post.push(quote!{final(#slot)@->Some_0.fragment()==old(#slot)@->Some_0.fragment().#factory_set(#raw_update)});
    }
    if let Some((r, op)) = &removed {
        let a = &arguments[&r.name.to_string()];
        let p: Expr = verus_syn::parse2(payload(r, &op.elt)?)?;
        let public = lower(&p, fields, &public_values)?;
        let rawp = lower(&p, fields, &raw_values)?;
        let factory = format_ident!("field_{}", r.name);
        let rawpart = contribution(r, &rawp);
        let get = getter(r);
        public_requires.push(quote! {#a.#get()==#public});
        raw_requires.push(quote!{#consumed.fragment()==Fragment #expr::#factory(#rawpart)#(.#setters(#raw_constants))*});
        if mutable.is_some() {
            raw_requires.push(quote! {#consumed.loc()==#loc});
        }
    }
    for r in &readonly {
        if let Some(op) = have.get(&r.name.to_string()) {
            let a = &arguments[&r.name.to_string()];
            let p: Expr = verus_syn::parse2(payload(r, &op.elt)?)?;
            let public = lower(&p, fields, &public_values)?;
            let get = getter(r);
            public_requires.push(if matches!(r.stype, ShardableType::Count) {
                quote! {#public<=#a.#get()}
            } else {
                quote! {#a.#get()==#public}
            });
        }
    }
    let actual_parameter = if depositing {
        let ShardableType::StorageOption(t) = &storage.stype else {
            unreachable!()
        };
        quote! {tracked #actual:#t,}
    } else {
        quote! {}
    };
    let actual_argument = if depositing {
        quote! {#actual,}
    } else {
        quote! {}
    };
    let deposit_fragment = if depositing {
        quote! {IMap::empty().insert(0int,#actual)}
    } else {
        quote! {IMap::empty()}
    };
    if depositing {
        let MonoidElt::OptionSome(Some(e)) = &physical.as_ref().unwrap().elt else {
            unreachable!()
        };
        let public = lower(e, fields, &public_values)?;
        let raw = lower(e, fields, &raw_values)?;
        public_requires.push(quote! {#actual==#public});
        raw_requires.push(quote! {#actual==#raw});
    }
    if !readonly.is_empty() {
        raw_requires.push(quote! {#observation.loc()==#loc});
    }
    raw_requires.push(quote! {Protocol #expr::#local(#raw_initial,#h,#deposit_fragment,#(#pn),*)});
    let mut public_input = vec![];
    for field in &sm.fields {
        if depositing && field.name == storage.name {
            public_input.push(actual_parameter.clone());
        }
        if let Some(a) = arguments.get(&field.name.to_string()) {
            let n = &field.name;
            public_input.push(if mutable.is_some_and(|m| m.name == field.name) {
                quote! {tracked #a:&mut #n #types,}
            } else if removed.as_ref().is_some_and(|(r, _)| r.name == field.name) {
                quote! {tracked #a:#n #types,}
            } else {
                quote! {tracked #a:&#n #types,}
            });
        }
    }
    let raw_mutable = if mutable.is_some() {
        quote! {tracked #slot:&mut Tracked<Option<#token>>,}
    } else {
        quote! {}
    };
    let raw_consumed = if removed.is_some() {
        quote! {tracked #consumed:#token,}
    } else {
        quote! {}
    };
    let raw_read = if readonly.is_empty() {
        quote! {}
    } else {
        quote! {tracked #observation:&::vstd::resource::tsm_storage::StorageObservation<Protocol #types>,}
    };
    let ShardableType::StorageOption(permission) = &storage.stype else {
        unreachable!()
    };
    let raw_return_type = if withdrawing {
        quote! {(#token,#permission)}
    } else if added.is_some() {
        token.clone()
    } else {
        quote! {()}
    };
    let public_return_type = if hidden_element {
        let (r,_)=added.as_ref().unwrap();let n=&r.name;let ShardableType::Multiset(t)=&r.stype else{unreachable!()};quote!{(Ghost<#t>,Tracked<#n #types>)}
    } else if withdrawing {
        let n = &added.as_ref().unwrap().0.name;
        if physical_first{quote!{(Ghost<#permission>,Tracked<#permission>,Tracked<#n #types>)}}else{quote! {(Tracked<#n #types>,Ghost<#permission>,Tracked<#permission>)}}
    } else if let Some((_, tuple)) = &snapshot {
        let n = &added.as_ref().unwrap().0.name;
        let ts: Vec<_> = tuple.elems.iter().collect();
        quote! {(#(Ghost<#ts>,)*Tracked<#n #types>)}
    } else if let Some((f, _)) = &added {
        let n = &f.name;
        quote! {#n #types}
    } else {
        quote! {()}
    };
    let mut select_value = None;
    if let Some((r, op)) = &added {
        let factory = format_ident!("field_{}", r.name);
        let owns_optional = format_ident!("owns_{}", r.name);
        let produced_payload = if snapshot.is_some() || hidden_element {
            output_value(r, quote! {#raw_token_output.fragment()})
        } else {
            let p: Expr = verus_syn::parse2(payload(r, &op.elt)?)?;
            bind_block(lower(&p, fields, &raw_values)?, &raw_binding_values)
        };
        let produced_part = contribution(r, &produced_payload);
        raw_post.push(quote! {#raw_token_output.loc()==#loc});
        raw_post.push(quote!{#raw_token_output.fragment()==Fragment #expr::#factory(#produced_part)#(.#setters(#raw_constants))*});
        let get = getter(r);
        public_post.push(quote! {#public_output_owner.instance_id()==self.id()});
        if let Some((source_tuple, _)) = &snapshot {
            let indexes: Vec<_> = (0..source_tuple.elems.len())
                .map(verus_syn::Index::from)
                .collect();
            public_post.push(quote! {#public_output_owner.value()==(#(#output.#indexes@),*)});
            raw_post.push(quote! {#raw_token_output.fragment().#owns_optional()});
        } else {
            let p: Expr = verus_syn::parse2(payload(r, &op.elt)?)?;
            let expected = bind_block(lower(&p, fields, &old_values)?, &public_binding_values);
            public_post.push(quote! {#public_output_owner.#get()==#expected});
        }
        select_value = Some(produced_payload);
    }
    let body_take = if mutable.is_some() {
        quote! {let tracked #remaining=#slot.borrow_mut().tracked_take();}
    } else {
        quote! {let tracked #remaining=#consumed;}
    };
    let body_join = if mutable.is_some() && removed.is_some() {
        quote! {let tracked #remaining=#remaining.join(#consumed);}
    } else {
        quote! {}
    };
    let pack = if depositing {
        quote! {let tracked #deposited=::vstd::resource::tsm_helpers::singleton_map(0int,#actual);}
    } else {
        quote! {let tracked #deposited=IMap::<int,#permission>::tracked_empty();}
    };
    let execute = if readonly.is_empty() {
        let actual = if depositing {
            quote! {#deposited,}
        } else {
            quote! {}
        };
        quote! {let #dep=#deposited;let tracked #remaining=Protocol #expr::#local_op(#remaining,#actual #(#pn),*);let tracked #withdrawn=IMap::<int,#permission>::tracked_empty();}
    } else {
        quote! {
        let #dep=#deposited;Protocol #expr::#ready(#initial,#observation.fragment(),#dep,#(#pn),*);Protocol #expr::#frame(#initial,#observation.fragment(),#dep,#(#pn),*);
        let #choices=ISet::new(|#pair:(Fragment #types,IMap<int,#permission>)|Protocol #expr::#outputs(#initial,#observation.fragment(),#pair.0,#dep,#pair.1,#(#pn),*));
        let tracked(#remaining,#withdrawn)=#remaining.exchange_nondeterministic_with_observation(#observation,#deposited,#choices);
        }
    };
    let body_h = if readonly.is_empty() {
        quote! {Fragment #expr::empty()}
    } else {
        quote! {#observation.fragment()}
    };
    let witness_body = quote! {let(#before,#after,_)=Protocol #expr::#witness(#initial,#body_h,#remaining.fragment(),#dep,#withdrawn,#(#pn),*);};
    let extract = if withdrawing {
        quote! {assert(#withdrawn==IMap::empty().insert(0int,#before.#storage_name->Some_0));let tracked #physical_value=::vstd::resource::tsm_helpers::take_singleton(#withdrawn,0int);}
    } else {
        quote! {}
    };
    let mut restore = vec![];
    if let Some(m) = mutable {
        let select = format_ident!("select_{}", m.name);
        let without = format_ident!("without_{}", m.name);
        let law = format_ident!("take_{}_law", m.name);
        restore.push(quote!{#remaining.fragment().#law();let #part=#remaining.fragment().#select()#(.#setters(#initial.#cget()))*;let #rest=#remaining.fragment().#without();assert(Fragment #expr::op(#part,#rest)==#remaining.fragment());let tracked(#owned,#remaining)=#remaining.split(#part,#rest);*#slot=Tracked(Some(#owned));});
    }
    let mut split_returned = quote! {};
    let mut normalize = quote! {};
    if let Some((r, op)) = &added {
        let n = &r.name;
        let select = format_ident!("select_{n}");
        let without = format_ident!("without_{n}");
        let law = format_ident!("take_{n}_law");
        if let ShardableType::Set(t) = &r.stype {
            let factory = format_ident!("field_{n}");
            let p: Expr = verus_syn::parse2(payload(r, &op.elt)?)?;
            let v = bind_block(lower(&p, fields, &raw_values)?, &raw_binding_values);
            let v = replace_output(v, &output, &result);
            normalize = quote! {let #part=Fragment #expr::#factory(::vstd::set::Set::<#t>::empty().insert(#v));assert forall|key:#t|#remaining.fragment().#n.at(key)==#[trigger] #part.#n.at(key) by{};::vstd::resource::tsm_collections::SetFragment::<#t>::extensionality(#remaining.fragment().#n,#part.#n);};
        }
        if let ShardableType::Multiset(t)=&r.stype{
            let factory=format_ident!("field_{n}");let p:Expr=verus_syn::parse2(payload(r,&op.elt)?)?;
            let v=if hidden_element{quote!{#before.#storage_name->Some_0}}else{bind_block(lower(&p,fields,&raw_values)?,&raw_binding_values)};
            let v=replace_output(v,&output,&result);let key=fresh(sm,tr,"bag_key");
            normalize=quote!{let #part=Fragment #expr::#factory(::vstd::multiset::Multiset::<#t>::singleton(#v));assert forall|#key:#t|#remaining.fragment().#n.at(#key)==#[trigger] #part.#n.at(#key) by{};::vstd::resource::tsm_finite_multiset::FiniteMultisetRA::<#t>::extensionality(#remaining.fragment().#n,#part.#n);};
        }
        split_returned = quote! {#remaining.fragment().#law();let #part=#remaining.fragment().#select()#(.#setters(#initial.#cget()))*;let #rest=#remaining.fragment().#without();assert(Fragment #expr::op(#part,#rest)==#remaining.fragment());let tracked(#result,#remaining)=#remaining.split(#part,#rest);};
    }
    let raw_result = if withdrawing {
        quote! {(#result,#physical_value)}
    } else if added.is_some() {
        quote! {#result}
    } else {
        quote! {()}
    };
    let all_names: Vec<_> = supplied
        .iter()
        .map(|f| &arguments[&f.name.to_string()])
        .collect();
    let mut type_uses = vec![];
    for f in &supplied {
        let a = &arguments[&f.name.to_string()];
        type_uses.push(if removed.as_ref().is_some_and(|(r, _)| r.name == f.name) {
            quote! {::vstd::prelude::use_type_invariant(&#a);self.metadata.agrees(&#a.metadata);}
        } else {
            quote! {::vstd::prelude::use_type_invariant(&*#a);self.metadata.agrees(&#a.metadata);}
        });
    }
    let observation_body = if readonly.len() > 1 {
        let readers: Vec<_> = readonly
            .iter()
            .map(|f| &arguments[&f.name.to_string()])
            .collect();
        let observations: Vec<_> = readonly
            .iter()
            .map(|f| fresh(sm, tr, &format!("read_observation_{}", f.name)))
            .collect();
        let first = &observations[0];
        let upper = fresh(sm, tr, "read_upper");
        let previous = fresh(sm, tr, "read_previous");
        let whole = fresh(sm, tr, "read_whole");
        let outer = fresh(sm, tr, "read_outer");
        let lower_frame = fresh(sm, tr, "read_frame");
        let target = fresh(sm, tr, "read_target");
        let rest = fresh(sm, tr, "read_rest");
        let merges:Vec<_>=observations.iter().enumerate().skip(1).map(|(index,o)|{let prior=&readers[..index];let trans=if index>1{quote!{#(Self::__roles_read_included(#prior.raw@->Some_0.fragment(),#previous,#upper.fragment());)*}}else{quote!{}};quote!{let #previous=#upper.fragment();let tracked #upper=#upper.join(&#o);#trans}}).collect();
        let names: Vec<_> = readonly.iter().map(|f| &f.name).collect();
        let owns: Vec<_> = names.iter().map(|n| format_ident!("owns_{n}")).collect();
        let getters: Vec<_> = names.iter().map(|n| format_ident!("value_{n}")).collect();
        let selected=fresh(sm,tr,"read_selected");let next=fresh(sm,tr,"read_next");let prior=fresh(sm,tr,"read_prior");
        let projection:Vec<_>=readonly.iter().enumerate().map(|(index,f)|{let select=format_ident!("select_{}",f.name);let without=format_ident!("without_{}",f.name);let law=format_ident!("take_{}_law",f.name);
            let extend=if index==0{quote!{let #target=#selected;}}else{quote!{let #prior=#target;Fragment #expr::associative(#prior,#selected,#next);let #target=Fragment #expr::op(#prior,#selected);}};
            quote!{#rest.#law();let #selected=#rest.#select()#(.#setters(self.#cn()))*;let #next=#rest.#without();assert(Fragment #expr::op(#selected,#next)==#rest);#extend let #rest=#next;assert(Fragment #expr::op(#target,#rest)==#upper.fragment());}
        }).collect();

        quote! {
            #(let tracked #observations=#readers.borrow_token().observe();)*
            let tracked #upper=#first;#(#merges)*#upper.validate();
            let (#whole,#outer)=choose|whole:State #types,outer:Fragment #types|whole.invariant()&&Fragment #expr::op(#upper.fragment(),outer)==Protocol #expr::embed(whole);
            #(let #lower_frame=choose|frame:Fragment #types|Fragment #expr::op(#readers.raw@->Some_0.fragment(),frame)==#upper.fragment();
              Fragment #expr::associative(#readers.raw@->Some_0.fragment(),#lower_frame,#outer);
              assert(Fragment #expr::op(#readers.raw@->Some_0.fragment(),Fragment #expr::op(#lower_frame,#outer))==Protocol #expr::embed(#whole));
              assert(#whole.#names==#readers.value());assert(#upper.fragment().#owns());assert(#upper.fragment().#getters()==#readers.value());)*
            let #rest=#upper.fragment();#(#projection)*
            let tracked #observation=#upper.weaken(#target);
        }
    } else if let Some(f) = readonly.first() {
        let a = &arguments[&f.name.to_string()];
        quote! {let tracked #observation=#a.raw.borrow().tracked_borrow().observe();}
    } else {
        quote! {}
    };
    let mutable_argument = mutable.map(|m| {
        let a = &arguments[&m.name.to_string()];
        quote! {&mut #a.raw,}
    });
    let consumed_argument = removed.as_ref().map(|(r, _)| {
        let a = &arguments[&r.name.to_string()];
        quote! {#a.raw.get().tracked_unwrap(),}
    });
    let read_argument = if readonly.is_empty() {
        quote! {}
    } else {
        quote! {&#observation,}
    };
    let call = quote! {Self::#raw(#(#pn,)*#mutable_argument #consumed_argument #read_argument #actual_argument)};
    let saved_mutable = fresh(sm, tr, "public_before_variable");
    let save_mutable = mutable.map(|m| {
        let a = &arguments[&m.name.to_string()];
        quote! {let #saved_mutable=#a.value();}
    });
    let mut body_values = public_values.clone();
    if let Some(m) = mutable {
        body_values.insert(m.name.to_string(), quote! {#saved_mutable});
    }
    let mut body_bindings = HashMap::new();
    for (binding, e) in &ops.bindings {
        if let Ok(value) = lower(e, fields, &body_values) {
            body_bindings.insert(binding.to_string(), value);
        } else if withdrawing {
            body_bindings.insert(binding.to_string(), quote! {#physical_value});
        } else {
            body_bindings.insert(binding.to_string(), quote! {#payload_value});
        }
    }
    let public_result = if let Some((r, _)) = &added {
        let n = &r.name;
        let additional = if matches!(
            r.stype,
            ShardableType::Option(_) | ShardableType::Set(_) | ShardableType::Multiset(_)
        ) {
            if snapshot.is_some() {
                quote! {,#payload_value}
            } else {
                let p: Expr = verus_syn::parse2(payload(r, &added.as_ref().unwrap().1.elt)?)?;
                let value = bind_block(lower(&p, fields, &body_values)?, &body_bindings);
                quote! {,#value}
            }
        } else {
            quote! {}
        };
        if withdrawing {
            let returned=if physical_first{quote!{(Ghost(#physical_value),Tracked(#physical_value),Tracked(#result))}}else{quote!{(Tracked(#result),Ghost(#physical_value),Tracked(#physical_value))}};
            quote! {let tracked(#result,#physical_value)=#call;let tracked #result=<#n #types>::__from_token(#result,self.metadata.clone()#additional);#returned}
        } else if let Some((_, tuple)) = &snapshot {
            let value = output_value(r, quote! {#result.fragment()});
            let indexes: Vec<_> = (0..tuple.elems.len()).map(verus_syn::Index::from).collect();
            quote! {let tracked #result=#call;let #payload_value=#value;let tracked #result=<#n #types>::__from_token(#result,self.metadata.clone(),#payload_value);(#(Ghost(#payload_value.#indexes),)*Tracked(#result))}
        } else if hidden_element {
            let value = output_value(r, quote! {#result.fragment()});
            quote! {let tracked #result=#call;let #payload_value=#value;let tracked #result=<#n #types>::__from_token(#result,self.metadata.clone()#additional);(Ghost(#payload_value),Tracked(#result))}
        } else {
            quote! {let tracked #result=#call;<#n #types>::__from_token(#result,self.metadata.clone()#additional)}
        }
    } else {
        quote! {#call}
    };
    let id_post: Vec<_> = mutable
        .iter()
        .map(|m| {
            let a = &arguments[&m.name.to_string()];
            quote! {final(#a).instance_id()==self.id()}
        })
        .collect();
    Ok(quote! {
    proof fn #raw(#(#params,)*#raw_mutable #raw_consumed #raw_read #actual_parameter)->(tracked #output:#raw_return_type)
    requires #(#raw_requires,)*ensures #(#raw_post,)*
    {let #initial=#raw_initial;#body_take #body_join #pack #execute #witness_body #extract #normalize #(#restore)*#split_returned #raw_result}
    pub proof fn #name(tracked &self,#(#params,)*#(#public_input)*)->(tracked #output:#public_return_type)
    requires #(#all_names.instance_id()==self.id(),)*#(#public_requires,)*ensures #(#id_post,)*#(#public_post,)*
    {#save_mutable #(#type_uses)*#observation_body #public_result}
    })
}

fn replace_output(tokens: TokenStream, from: &Ident, to: &Ident) -> TokenStream {
    tokens
        .into_iter()
        .map(|token| match token {
            proc_macro2::TokenTree::Ident(name) if name == *from => {
                proc_macro2::TokenTree::Ident(to.clone())
            }
            proc_macro2::TokenTree::Group(group) => {
                let mut next = proc_macro2::Group::new(
                    group.delimiter(),
                    replace_output(group.stream(), from, to),
                );
                next.set_span(group.span());
                proc_macro2::TokenTree::Group(next)
            }
            other => other,
        })
        .collect()
}

fn physical_guard(sm:&SM,tr:&Transition,ops:&Ops,fields:&HashMap<String,Field>,constants:&[&Field],types:&TokenStream,expr:&TokenStream)->Result<TokenStream,Error>{
 if !ops.bindings.is_empty()||!ops.updates.is_empty(){return Err(Error::new(tr.name.span(),"physical guard requires unbound readonly operations"));}
 let [(reader,have),(store,guard)]=ops.special.as_slice()else{return Err(Error::new(tr.name.span(),"physical guard requires exactly one Have then Guard"));};
 let role=&fields[&reader.to_string()];let physical=&fields[&store.to_string()];
 let ShardableType::Multiset(element)=&role.stype else{return Err(Error::new(tr.name.span(),"physical guard requires multiset ownership"));};
 if !matches!(have.stmt,MonoidStmtType::Have)||!matches!(guard.stmt,MonoidStmtType::Guard)||!matches!(physical.stype,ShardableType::StorageOption(_)){return Err(Error::new(tr.name.span(),"physical guard requires Have then storage Guard"));}
 let value:Expr=verus_syn::parse2(payload(role,&have.elt)?)?;
 let option_field=Field{stype:ShardableType::Option(element.clone()),..physical.clone()};
 let guard_value:Expr=verus_syn::parse2(payload(&option_field,&guard.elt)?)?;
 if ungroup(&value)!=ungroup(&guard_value){return Err(Error::new(tr.name.span(),"physical guard singleton payloads must match"));}
 let values:HashMap<String,TokenStream>=constants.iter().map(|f|{let n=&f.name;(n.to_string(),quote!{self.#n()})}).collect();
 let required:Vec<_>=ops.requires.iter().map(|e|lower(e,fields,&values)).collect::<Result<_,_>>()?;let asserted:Vec<_>=ops.asserts.iter().map(|e|lower(e,fields,&values)).collect::<Result<_,_>>()?;
 let value=lower(&value,fields,&values)?;let name=&tr.name;let enabled=format_ident!("{name}_enabled");let owners=format_ident!("{name}_owners_enabled");let frame_method=format_ident!("{name}_frame");let guarded=format_ident!("{name}_guarded");let execute=format_ident!("{name}_execute");
 let input=fresh(sm,tr,"guard_input");let output=fresh(sm,tr,"guard_output");let fragment=fresh(sm,tr,"guard_fragment");let frame=fresh(sm,tr,"guard_frame");let before=fresh(sm,tr,"guard_before");let observation=fresh(sm,tr,"guard_observation");
 let mut lifetime_name=fresh(sm,tr,"guard_lifetime").to_string();while sm.generics.as_ref().is_some_and(|g|g.to_token_stream().to_string().contains(&lifetime_name)){lifetime_name.push('_');}let lifetime=verus_syn::Lifetime::new(&format!("'{lifetime_name}"),Span::mixed_site());
 let cn:Vec<_>=constants.iter().map(|f|&f.name).collect();let params:Vec<_>=tr.params.iter().map(|p|{let n=&p.name;let t=&p.ty;quote!{#n:#t}}).collect();let pn:Vec<_>=tr.params.iter().map(|p|&p.name).collect();
 Ok(quote!{
 pub proof fn #name<#lifetime>(tracked &self,#(#params,)*tracked #input:&#lifetime #reader #types)->(tracked #output:&#lifetime #element)
 requires #input.instance_id()==self.id(),#input.element()==#value,#(#required,)*ensures *#output==#value,#(#asserted,)*
 {
 ::vstd::prelude::use_type_invariant(#input);self.metadata.agrees(&#input.metadata);let #fragment=#input.raw@->Some_0.fragment();
 assert forall|#frame:Fragment #types,#before:State #types|#before.invariant()&&Fragment #expr::op(#fragment,#frame)==Protocol #expr::embed(#before)
 implies State #expr::#enabled(#before,#(#pn),*)&&State #expr::#owners(#before,#fragment,Fragment #expr::empty(),#(#pn),*) by{assert(#before.#reader.count(#value)>=1);#(assert(#before.#cn==self.#cn());)*}
 Protocol #expr::#frame_method(#fragment,#(#pn),*);assert(Protocol #expr::#guarded(#fragment,#(#pn),*)==IMap::empty().insert(0int,#value));
 let tracked #observation=#input.borrow_token().observe();#observation.validate();let(#before,#frame)=choose|before:State #types,frame:Fragment #types|before.invariant()&&Fragment #expr::op(#fragment,frame)==Protocol #expr::embed(before);
 #(assert(#before.#cn==self.#cn());)*let _=State #expr::#execute(#before,#(#pn),*);
 ::vstd::resource::tsm_helpers::guard_value(#input.borrow_token(),0int,#value)
 }
 })
}

fn ungroup(mut expression:&Expr)->&Expr{
    loop {match expression {Expr::Paren(paren)=>expression=&paren.expr,Expr::Group(group)=>expression=&group.expr,_=>return expression}}
}
fn path_constructor(path:&verus_syn::ExprPath,container:&str,constructor:&str)->bool{
    if path.path.segments.last().is_none_or(|segment|segment.ident!=constructor){return false;}
    if let Some(qself)=&path.qself{
        return matches!(&*qself.ty,verus_syn::Type::Path(ty)if ty.path.segments.last().is_some_and(|segment|segment.ident==container));
    }
    let mut segments=path.path.segments.iter().rev();segments.next();
    segments.next().is_some_and(|segment|segment.ident==container)
}
fn empty_collection_initializer(expression:&Expr,container:&str)->bool{
    let Expr::Call(call)=ungroup(expression)else{return false;};
    call.args.is_empty()&&matches!(ungroup(&call.func),Expr::Path(path)if path_constructor(path,container,"empty"))
}
fn none_initializer(expression:&Expr)->bool{
    matches!(ungroup(expression),Expr::Path(path)if path.qself.is_none()&&path.path.is_ident("None")||path_constructor(path,"Option","None"))
}
fn stored_option_binding(expression:&Expr,storage:&Ident)->bool{
    let Expr::GetField(project)=ungroup(expression)else{return false;};
    if !matches!(&project.member,verus_syn::Member::Unnamed(index)if index.index==0){return false;}
    let Expr::Field(field)=ungroup(&project.base)else{return false;};
    matches!(&field.member,verus_syn::Member::Named(name)if name==storage)
        &&matches!(ungroup(&field.base),Expr::Path(path)if path.qself.is_none()&&path.path.is_ident("pre"))
}
