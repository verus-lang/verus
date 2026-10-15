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
    withdrawals: HashMap<String, Ident>,
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
                SplitKind::Special(n, op, _, Some(pattern))
                    if matches!(op.stmt, MonoidStmtType::Withdraw) =>
                {
                    let verus_syn::Pat::Ident(binding) = &**pattern else {
                        return Err(Error::new(
                            *span,
                            "bound optional withdrawal requires one identifier",
                        ));
                    };
                    if out
                        .withdrawals
                        .insert(n.to_string(), binding.ident.clone())
                        .is_some()
                    {
                        return Err(Error::new(n.span(), "duplicate withdrawal binding"));
                    }
                    out.special.push((n.clone(), op.clone()));
                }
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
    for binding in ops.withdrawals.values() {
        unavailable.insert(binding.to_string());
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
        (
            ShardableType::Count | ShardableType::Bool | ShardableType::PersistentBool,
            MonoidElt::General(e),
        ) => quote! {#e},
        (ShardableType::Bool | ShardableType::PersistentBool, MonoidElt::True) => quote! {true},
        (ShardableType::Set(_), MonoidElt::SingletonSet(e)) => quote! {#e},
        (ShardableType::Multiset(_), MonoidElt::SingletonMultiset(e)) => quote! {#e},
        (ShardableType::Option(_), MonoidElt::OptionSome(Some(e))) => quote! {#e},
        (ShardableType::Option(_), MonoidElt::General(e)) => {
            let mut e = e;
            while let Expr::Paren(paren) = e {
                e = &paren.expr;
            }
            let Expr::Call(call) = e else {
                return Err(Error::new(
                    field.name.span(),
                    "optional operand requires explicit Some",
                ));
            };
            if !matches!(&*call.func,Expr::Path(path)if path.path.is_ident("Some"))
                || call.args.len() != 1
            {
                return Err(Error::new(
                    field.name.span(),
                    "optional operand requires explicit Some",
                ));
            }
            let value = &call.args[0];
            quote! {#value}
        }
        _ => {
            return Err(Error::new(
                field.name.span(),
                "heterogeneous role requires Count or singleton Set/Option operand",
            ))
        }
    })
}
pub fn output(sm: &SM, selected: &HashSet<String>) -> Result<TokenStream, Error> {
    let storage: Vec<_> = sm.fields.iter().filter(|f| f.stype.is_storage()).collect();
    if storage.len() < 2
        || sm.fields.iter().any(|f| {
            !matches!(
                f.stype,
                ShardableType::Constant(_)
                    | ShardableType::Variable(_)
                    | ShardableType::Bool
                    | ShardableType::PersistentBool
                    | ShardableType::StorageOption(_)
            )
        })
    {
        return Err(Error::new(
            sm.name.span(),
            "multiple physical roles require homogeneous optional stores, variables and bool roles",
        ));
    }
    let ShardableType::StorageOption(permission) = &storage[0].stype else {
        unreachable!()
    };
    for f in &storage {
        if !matches!(&f.stype,ShardableType::StorageOption(t)if t==permission) {
            return Err(Error::new(
                f.name.span(),
                "multiple optional stores must carry identical permission types",
            ));
        }
    }
    let constants: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::Constant(_)))
        .collect();
    let ordinary: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| !f.stype.is_storage() && !matches!(f.stype, ShardableType::Constant(_)))
        .collect();
    let mut coordinates = storage.clone();
    coordinates.sort_by_key(|f| f.name.to_string());
    let keys: HashMap<_, _> = coordinates
        .iter()
        .enumerate()
        .map(|(i, f)| {
            (
                f.name.to_string(),
                verus_syn::LitInt::new(&format!("{}int", i), Span::mixed_site()),
            )
        })
        .collect();
    let fields: HashMap<_, _> = sm
        .fields
        .iter()
        .map(|f| (f.name.to_string(), f.clone()))
        .collect();
    let (g, attrs) = crate::verified_tokens::datatype_generics(sm);
    let (decl, wc) = generics_for_decl(&g);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let types = args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default();
    let expr = args.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default();
    let token = quote! {Token #types};
    let metadata = quote! {__MultipleStorageMetadata #types};
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
    for f in &ordinary {
        wrappers.push(roles::wrapper(f, &cx)?);
        if matches!(f.stype, ShardableType::PersistentBool) {
            let n = &f.name;
            let raw = fresh(sm, &sm.transitions[0], "persistent_clone_raw");
            let left = fresh(sm, &sm.transitions[0], "persistent_clone_left");
            let right = fresh(sm, &sm.transitions[0], "persistent_clone_right");
            let slot = fresh(sm, &sm.transitions[0], "persistent_clone_slot");
            wrappers.push(quote!{impl #decl #n #types #wc{
 proof fn __clone_raw(tracked #slot:&mut Tracked<Option<#token>>)->(tracked out:#token)
 requires old(#slot)@ is Some,Fragment #expr::op(old(#slot)@->Some_0.fragment(),old(#slot)@->Some_0.fragment())==old(#slot)@->Some_0.fragment(),
 ensures final(#slot)@ is Some,final(#slot)@->Some_0.loc()==old(#slot)@->Some_0.loc(),final(#slot)@->Some_0.fragment()==old(#slot)@->Some_0.fragment(),out.loc()==old(#slot)@->Some_0.loc(),out.fragment()==old(#slot)@->Some_0.fragment(),
 {let tracked #raw=#slot.borrow_mut().tracked_take();let tracked(#left,#right)=#raw.split(#raw.fragment(),#raw.fragment());*#slot=Tracked(Some(#left));#right}
 pub proof fn clone(tracked &mut self)->(tracked out:Self)ensures out.instance_id()==old(self).instance_id(),out.raw_fragment()==old(self).raw_fragment(),final(self).instance_id()==old(self).instance_id(),final(self).raw_fragment()==old(self).raw_fragment(),out.value(),final(self).value(),
 {::vstd::prelude::use_type_invariant(&*self);assert(Fragment #expr::op(self.raw@->Some_0.fragment(),self.raw@->Some_0.fragment())==self.raw@->Some_0.fragment());let tracked #raw=Self::__clone_raw(&mut self.raw);Self::__from_token(#raw,self.metadata.clone())}
 }});
        }
    }

    let mut methods = vec![];
    for tr in &sm.transitions {
        let mut ops = Ops::default();
        collect(&tr.body, &mut ops)?;
        if tr.kind == TransitionKind::Init {
            if ops.initial.len() != sm.fields.len() {
                return Err(Error::new(
                    tr.name.span(),
                    "multiple storage initialization requires every field",
                ));
            }
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
            let name = &tr.name;
            let strong = format_ident!("{name}_strong");
            let values: Vec<_> = cn.iter().map(|n| &ops.initial[&n.to_string()]).collect();
            let remaining = fresh(sm, tr, "initial_remaining");
            let md = fresh(sm, tr, "initial_metadata");
            let dep = fresh(sm, tr, "initial_deposit");
            let part = fresh(sm, tr, "initial_part");
            let rest = fresh(sm, tr, "initial_rest");
            let mut inputs = vec![];
            let mut requires = vec![];
            let mut splits = vec![];
            let mut outputs = vec![];
            let mut returned = vec![];
            let mut post = vec![];
            for f in &storage {
                let n = &f.name;
                let v = &ops.initial[&n.to_string()];
                if !matches!(v,Expr::Path(p)if p.path.is_ident("None")) {
                    return Err(Error::new(
                        n.span(),
                        "multiple optional initialization currently requires empty stores",
                    ));
                }
                let a = fresh(sm, tr, &format!("initial_actual_{n}"));
                inputs.push(quote! {tracked #a:Option<#permission>,});
                requires.push(quote! {#a==None});
            }
            for (i, f) in ordinary.iter().enumerate() {
                let n = &f.name;
                let v = &ops.initial[&n.to_string()];
                let ix = verus_syn::Index::from(i + 1);
                let optional =
                    matches!(f.stype, ShardableType::Bool | ShardableType::PersistentBool);
                let present = if optional {
                    match v {
                        Expr::Lit(verus_syn::ExprLit {
                            lit: verus_syn::Lit::Bool(b),
                            ..
                        }) => b.value,
                        _ => {
                            return Err(Error::new(
                                n.span(),
                                "bool initialization requires literal true or false",
                            ))
                        }
                    }
                } else {
                    true
                };
                outputs.push(if optional {
                    quote! {Tracked<Option<#n #types>>}
                } else {
                    quote! {Tracked<#n #types>}
                });
                if present {
                    let owner = fresh(sm, tr, &format!("initial_owner_{n}"));
                    let select = format_ident!("select_{n}");
                    let without = format_ident!("without_{n}");
                    let law = format_ident!("take_{n}_law");
                    splits.push(quote!{#remaining.fragment().#law();let #part=#remaining.fragment().#select()#(.#setters(#values))*;let #rest=#remaining.fragment().#without();assert(Fragment #expr::op(#part,#rest)==#remaining.fragment());let tracked(#owner,#remaining)=#remaining.split(#part,#rest);let tracked #owner=<#n #types>::__from_token(#owner,#md.clone());});
                    if optional {
                        returned.push(quote! {Tracked(Some(#owner))});
                        post.push(quote! {out.#ix@ is Some});
                        post.push(quote! {out.#ix@->Some_0.instance_id()==out.0@.id()});
                        post.push(quote! {out.#ix@->Some_0.value()});
                    } else {
                        returned.push(quote! {Tracked(#owner)});
                        post.push(quote! {out.#ix@.instance_id()==out.0@.id()});
                        post.push(quote! {out.#ix@.value()==#v});
                    }
                } else {
                    returned.push(quote! {Tracked(None)});
                    post.push(quote! {out.#ix@ is None});
                }
            }
            let conditions = &ops.requires;
            let initial_state=fresh(sm,tr,"initial_state");
            let initial_key=fresh(sm,tr,"initial_key");
            methods.push(quote!{pub proof fn #name(#(#params,)*#(#inputs)*)->(tracked out:(Tracked<Self>,#(#outputs),*))requires #(#requires,)*#(#conditions,)*ensures #(#post,)*#(out.0@.#cn()==#values,)*{let tracked #dep=IMap::<int,#permission>::tracked_empty();assert forall|#initial_state:State #types|State #expr::#strong(#initial_state,#(#pn),*) implies #dep==#initial_state.__storage() by{assert forall|#initial_key:int|!#initial_state.__storage().contains_key(#initial_key) by{};assert(#initial_state.__storage()==IMap::<int,#permission>::empty());};let tracked #remaining=Protocol #expr::#name(#dep,#(#pn),*);let tracked #md=::vstd::resource::tsm_context::Descriptor::alloc(__MultipleStorageMetadata #expr{protocol_location:#remaining.loc(),#(#cn:#values,)*#markerv});#(#splits)*(Tracked(Self{metadata:#md.clone(),context:Tracked(Some(#remaining))}),#(#returned),*)}});
        } else if tr.kind == TransitionKind::Property {
            methods.push(multiple_property(
                sm, tr, &ops, &fields, &constants, &types, &expr,
            )?);
        } else {
            if !selected.contains(&tr.name.to_string()) {
                return Err(Error::new(
                    tr.name.span(),
                    "multiple storage roles require checked local readiness",
                ));
            }
            methods.push(multiple_transition(
                sm, tr, &ops, &fields, &constants, &keys, permission, &types, &expr,
            )?);
        }
    }
    let info_id = fresh(sm, &sm.transitions[0], "info_instance_id");
    let info_marker = args
        .as_ref()
        .map(|a| quote! {pub ghost marker:core::marker::PhantomData<(#a,)>,});
    Ok(
        quote! {#(#attrs)*pub ghost struct InstanceInfo #decl #wc{pub #info_id: ::vstd::resource::Loc,#(pub #cn:#ct,)*#info_marker}impl #decl InstanceInfo #types #wc{pub open spec fn id(&self)->::vstd::resource::Loc{self.#info_id}#(pub open spec fn #cn(&self)->#ct{self.#cn})*}#(#attrs)*struct __MultipleStorageMetadata #decl #wc{ghost protocol_location: ::vstd::resource::Loc,#(ghost #cn:#ct,)*#marker}#(#wrappers)*#(#attrs)*pub tracked struct Instance #decl #wc{metadata:#descriptor,context:Tracked<Option<#token>>}impl #decl Instance #types #wc{#[verifier::type_invariant]spec fn invariant(self)->bool{::vstd::prelude::imply(self.context@ is Some,self.context@->Some_0.loc()==self.metadata.value().protocol_location&&self.context@->Some_0.fragment()==Fragment #expr::empty()#(.#setters(self.metadata.value().#cn))*)}pub closed spec fn id(&self)->::vstd::resource::Loc{self.metadata.id()}#(pub closed spec fn #cn(&self)->#ct{self.metadata.value().#cn})*pub open spec fn info(&self)->InstanceInfo #types{InstanceInfo #expr{#info_id:self.id(),#(#cn:self.#cn(),)*#markerv}}pub proof fn clone(tracked &self)->(tracked out:Self)ensures out.id()==self.id(),out.info()==self.info(),#(out.#cn()==self.#cn(),)*{Self{metadata:self.metadata.clone(),context:Tracked(None)}}#(#methods)*}},
    )
}
fn multiple_property(
    sm: &SM,
    tr: &Transition,
    ops: &Ops,
    fields: &HashMap<String, Field>,
    constants: &[&Field],
    types: &TokenStream,
    expr: &TokenStream,
) -> Result<TokenStream, Error> {
    let [(field, operation)] = ops.special.as_slice() else {
        return Err(Error::new(
            tr.name.span(),
            "multiple-store readonly property requires one actual persistent Bool Have",
        ));
    };
    let f = &fields[&field.to_string()];
    if !matches!(f.stype, ShardableType::PersistentBool)
        || !matches!(operation.stmt, MonoidStmtType::Have)
    {
        return Err(Error::new(
            field.span(),
            "multiple-store property requires persistent Bool Have",
        ));
    }
    let name = &tr.name;
    let input = fresh(sm, tr, "property_input");
    let observed = fresh(sm, tr, "property_observed");
    let before = fresh(sm, tr, "property_before");
    let frame = fresh(sm, tr, "property_frame");
    let getter = format_ident!("value_{field}");
    let params: Vec<_> = tr
        .params
        .iter()
        .map(|p| {
            let n = &p.name;
            let t = &p.ty;
            quote! {#n:#t}
        })
        .collect();
    let mut values: HashMap<_, _> = constants
        .iter()
        .map(|f| {
            let n = &f.name;
            (n.to_string(), quote! {self.#n()})
        })
        .collect();
    values.insert(field.to_string(), quote! {#input.value()});
    let mut pre: Vec<_> = ops
        .requires
        .iter()
        .map(|e| lower(e, fields, &values))
        .collect::<Result<_, _>>()?;
    let p: Expr = verus_syn::parse2(payload(f, &operation.elt)?)?;
    let literal_true = matches!(&p,Expr::Lit(lit) if matches!(&lit.lit,verus_syn::Lit::Bool(value) if value.value));
    let p = lower(&p, fields, &values)?;
    if !literal_true {
        pre.push(quote! {#input.value()==#p});
    }
    let post: Vec<_> = ops
        .asserts
        .iter()
        .map(|e| lower(e, fields, &values))
        .collect::<Result<_, _>>()?;
    Ok(
        quote! {pub proof fn #name(tracked &self,#(#params,)*tracked #input:&#field #types)requires #input.instance_id()==self.id(),#(#pre,)*ensures #(#post,)*{::vstd::prelude::use_type_invariant(#input);self.metadata.agrees(&#input.metadata);let tracked #observed=#input.raw.borrow().tracked_borrow().observe();#observed.validate();let(#before,#frame)=choose|#before:State #types,#frame:Fragment #types|#before.invariant()&&Fragment #expr::op(#observed.fragment(),#frame)==Protocol #expr::embed(#before);assert(#observed.fragment().#getter());assert(#before.#field);}},
    )
}
fn multiple_transition(
    sm: &SM,
    tr: &Transition,
    ops: &Ops,
    fields: &HashMap<String, Field>,
    constants: &[&Field],
    keys: &HashMap<String, verus_syn::LitInt>,
    permission: &verus_syn::Type,
    types: &TokenStream,
    expr: &TokenStream,
) -> Result<TokenStream, Error> {
    let raw = multiple_transition_body(
        sm, tr, ops, fields, constants, keys, permission, types, expr, true,
    )?;
    let public = multiple_transition_body(
        sm, tr, ops, fields, constants, keys, permission, types, expr, false,
    )?;
    Ok(quote! {#raw #public})
}
fn multiple_transition_body(
    sm: &SM,
    tr: &Transition,
    ops: &Ops,
    fields: &HashMap<String, Field>,
    constants: &[&Field],
    keys: &HashMap<String, verus_syn::LitInt>,
    permission: &verus_syn::Type,
    types: &TokenStream,
    expr: &TokenStream,
    raw_mode: bool,
) -> Result<TokenStream, Error> {
    let mut removed = HashMap::new();
    let mut added = HashMap::new();
    let mut have = HashMap::new();
    let mut deposited = HashMap::new();
    let mut withdrawn = HashMap::new();
    for (n, op) in &ops.special {
        let previous = match op.stmt {
            MonoidStmtType::Remove => removed.insert(n.to_string(), op),
            MonoidStmtType::Add(true) => added.insert(n.to_string(), op),
            MonoidStmtType::Have => have.insert(n.to_string(), op),
            MonoidStmtType::Deposit => deposited.insert(n.to_string(), op),
            MonoidStmtType::Withdraw => withdrawn.insert(n.to_string(), op),
            _ => {
                return Err(Error::new(
                    n.span(),
                    "unsupported multiple-store role operation",
                ))
            }
        };
        if previous.is_some() {
            return Err(Error::new(
                n.span(),
                "multiple-store role operation must occur once per field",
            ));
        }
    }
    if ops.updates.is_empty() && removed.is_empty() {
        return Err(Error::new(
            tr.name.span(),
            "multiple-store transition requires actual mutable or consumed role ownership",
        ));
    }
    for n in ops.updates.keys() {
        if !matches!(fields[n].stype, ShardableType::Variable(_)) {
            return Err(Error::new(
                fields[n].name.span(),
                "multiple-store mutable roles must be variables",
            ));
        }
    }
    for n in removed.keys() {
        if !matches!(fields[n].stype, ShardableType::Bool) {
            return Err(Error::new(
                fields[n].name.span(),
                "multiple-store consumed roles must be strict Bools",
            ));
        }
    }
    for n in added.keys().chain(have.keys()) {
        if !matches!(fields[n].stype, ShardableType::PersistentBool) {
            return Err(Error::new(
                fields[n].name.span(),
                "multiple-store persistent operations require Bool roles",
            ));
        }
    }
    for n in withdrawn.keys().chain(deposited.keys()) {
        if !matches!(fields[n].stype, ShardableType::StorageOption(_)) {
            return Err(Error::new(
                fields[n].name.span(),
                "multiple-store physical operations require optional fields",
            ));
        }
    }
    if have.len() > 1 {
        return Err(Error::new(
            tr.name.span(),
            "multiple-store transition currently observes one persistent Bool role",
        ));
    }
    let supplied: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| {
            ops.updates.contains_key(&f.name.to_string())
                || removed.contains_key(&f.name.to_string())
                || have.contains_key(&f.name.to_string())
        })
        .collect();
    let arguments: HashMap<_, _> = supplied
        .iter()
        .map(|f| {
            (
                f.name.to_string(),
                fresh(sm, tr, &format!("input_{}", f.name)),
            )
        })
        .collect();
    let actuals: HashMap<_, _> = deposited
        .keys()
        .map(|n| (n.clone(), fresh(sm, tr, &format!("actual_{n}"))))
        .collect();
    let raw_owners: HashMap<_, _> = supplied
        .iter()
        .filter(|f| !have.contains_key(&f.name.to_string()))
        .map(|f| {
            (
                f.name.to_string(),
                fresh(sm, tr, &format!("owner_{}", f.name)),
            )
        })
        .collect();
    let oldvalues: HashMap<_, _> = ops
        .updates
        .keys()
        .map(|n| (n.clone(), fresh(sm, tr, &format!("before_{n}"))))
        .collect();
    let mut values: HashMap<_, _> = constants
        .iter()
        .map(|f| {
            let n = &f.name;
            (n.to_string(), quote! {self.#n()})
        })
        .collect();
    let mut finalvalues = values.clone();
    let mut requires = vec![];
    let mut ensures = vec![];
    let mut prefixes = vec![];
    let mut takes = vec![];
    let mut inputs = vec![];
    for f in &supplied {
        let n = &f.name;
        let a = &arguments[&n.to_string()];
        if ops.updates.contains_key(&n.to_string()) {
            let g = format_ident!("value_{n}");
            values.insert(
                n.to_string(),
                if raw_mode {
                    quote! {old(#a)@->Some_0.fragment().#g()}
                } else {
                    quote! {old(#a).value()}
                },
            );
            finalvalues.insert(
                n.to_string(),
                if raw_mode {
                    quote! {#a@->Some_0.fragment().#g()}
                } else {
                    quote! {#a.value()}
                },
            );
            let saved = &oldvalues[&n.to_string()];
            prefixes.push(if raw_mode {
                quote! {let #saved=#a@->Some_0.fragment().#g();}
            } else {
                quote! {let #saved=#a.value();}
            });
        } else {
            values.insert(
                n.to_string(),
                if raw_mode && removed.contains_key(&n.to_string()) {
                    quote! {true}
                } else {
                    quote! {#a.value()}
                },
            );
            finalvalues.insert(
                n.to_string(),
                if raw_mode && removed.contains_key(&n.to_string()) {
                    quote! {true}
                } else {
                    quote! {#a.value()}
                },
            );
        }
        if raw_mode && !have.contains_key(&n.to_string()) {
            let factory = format_ident!("field_{n}");
            let cn: Vec<_> = constants.iter().map(|f| &f.name).collect();
            let setters: Vec<_> = cn.iter().map(|n| format_ident!("with_{n}")).collect();
            if ops.updates.contains_key(&n.to_string()) {
                let g = format_ident!("value_{n}");
                requires.push(quote! {old(#a)@ is Some});
                requires
                    .push(quote! {old(#a)@->Some_0.loc()==self.metadata.value().protocol_location});
                requires.push(quote!{old(#a)@->Some_0.fragment()==Fragment #expr::#factory(old(#a)@->Some_0.fragment().#g())#(.#setters(self.#cn()))*});
            } else {
                requires.push(quote! {#a.loc()==self.metadata.value().protocol_location});
                requires.push(
                    quote! {#a.fragment()==Fragment #expr::#factory(true)#(.#setters(self.#cn()))*},
                );
            }
        } else {
            requires.push(quote! {#a.instance_id()==self.id()});
        }
        let invariant_use = if removed.contains_key(&n.to_string()) {
            quote! {::vstd::prelude::use_type_invariant(&#a);}
        } else {
            quote! {::vstd::prelude::use_type_invariant(&*#a);}
        };
        if !raw_mode || have.contains_key(&n.to_string()) {
            prefixes.push(quote! {#invariant_use self.metadata.agrees(&#a.metadata);});
        }
        if let Some(raw) = raw_owners.get(&n.to_string()) {
            takes.push(if ops.updates.contains_key(&n.to_string()) {
                if raw_mode {
                    quote! {let tracked #raw=#a.borrow_mut().tracked_take();}
                } else {
                    quote! {let tracked #raw=#a.raw.borrow_mut().tracked_take();}
                }
            } else {
                if raw_mode {
                    quote! {let tracked #raw=#a;}
                } else {
                    quote! {let tracked #raw=#a.raw.get().tracked_unwrap();}
                }
            });
        }
    }
    for e in &ops.requires {
        requires.push(lower(e, fields, &values)?);
    }
    for (n, op) in removed.iter().chain(have.iter()) {
        let f = &fields[n];
        let a = &arguments[n];
        let p: Expr = verus_syn::parse2(payload(f, &op.elt)?)?;
        if !raw_mode
            && matches!(
                &f.stype,
                ShardableType::Bool | ShardableType::PersistentBool
            )
            && matches!(&p,Expr::Lit(lit) if matches!(&lit.lit,verus_syn::Lit::Bool(value) if value.value))
        {
            continue;
        }
        let p = lower(&p, fields, &values)?;
        requires.push(if raw_mode && removed.contains_key(n) {
            quote! {true==#p}
        } else {
            quote! {#a.value()==#p}
        });
    }
    let mut dep_shape = quote! {IMap::<int,#permission>::empty()};
    let mut dep_inserts = vec![];
    let deposit = fresh(sm, tr, "deposited");
    let mut union_shape = quote! {IMap::<int,#permission>::empty()};
    for f in sm
        .fields
        .iter()
        .filter(|f| deposited.contains_key(&f.name.to_string()))
    {
        let n = &f.name;
        let a = &actuals[&n.to_string()];
        let op = deposited[&n.to_string()];
        let MonoidElt::OptionSome(Some(e)) = &op.elt else {
            return Err(Error::new(
                n.span(),
                "multiple-store deposit requires explicit singleton permission",
            ));
        };
        let v = lower(e, fields, &values)?;
        requires.push(quote! {#a==#v});
        let key = &keys[&n.to_string()];
        dep_shape = quote! {(#dep_shape).insert(#key,#a)};
        union_shape = quote! {(#union_shape).union_prefer_right(IMap::<int,#permission>::empty().insert(#key,#a))};
        dep_inserts.push(quote! {#deposit.tracked_insert(#key,#a);});
    }
    for f in &sm.fields {
        let n = &f.name;
        if let Some(a) = actuals.get(&n.to_string()) {
            inputs.push(quote! {tracked #a:#permission,});
        }
        if let Some(a) = arguments.get(&n.to_string()) {
            inputs.push(if ops.updates.contains_key(&n.to_string()) {
                if raw_mode {
                    quote! {tracked #a:&mut Tracked<Option<Token #types>>,}
                } else {
                    quote! {tracked #a:&mut #n #types,}
                }
            } else if removed.contains_key(&n.to_string()) {
                if raw_mode {
                    quote! {tracked #a:Token #types,}
                } else {
                    quote! {tracked #a:#n #types,}
                }
            } else {
                quote! {tracked #a:&#n #types,}
            });
        }
    }
    let mut bodyvalues = finalvalues.clone();
    for (n, saved) in &oldvalues {
        bodyvalues.insert(n.clone(), quote! {#saved});
    }
    for (n, e) in &ops.updates {
        let a = &arguments[n];
        let update = lower(e, fields, &values)?;
        if raw_mode {
            let factory = format_ident!("field_{n}");
            let cn: Vec<_> = constants.iter().map(|f| &f.name).collect();
            let setters: Vec<_> = cn.iter().map(|n| format_ident!("with_{n}")).collect();
            ensures.push(quote! {final(#a)@ is Some});
            ensures
                .push(quote! {final(#a)@->Some_0.loc()==self.metadata.value().protocol_location});
            ensures.push(quote!{final(#a)@->Some_0.fragment()==Fragment #expr::#factory(#update)#(.#setters(self.#cn()))*});
        } else {
            ensures.push(quote! {final(#a).value()==#update});
            ensures.push(quote! {final(#a).instance_id()==self.id()});
        }
    }
    let original_name = &tr.name;
    let declared = format_ident!("{original_name}_declared_requires");
    let owners_enabled = format_ident!("{original_name}_owners_enabled");
    let local_deposited = format_ident!("{original_name}_local_deposited");
    let local_requires = format_ident!("{original_name}_local_requires");
    let partial = fresh(sm, tr, "partial");
    let raw_name = format_ident!("__physical_multiple_raw_{original_name}");
    let name = if raw_mode { &raw_name } else { original_name };
    let local = format_ident!("{original_name}_local");
    let ready = format_ident!("{original_name}_local_ready");
    let frame = format_ident!("{original_name}_frame");
    let outputs = format_ident!("{original_name}_outputs");
    let witness = format_ident!("{original_name}_witness");
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
    let initial = fresh(sm, tr, "initial");
    let remaining = fresh(sm, tr, "remaining");
    let physical = fresh(sm, tr, "physical");
    let before = fresh(sm, tr, "before");
    let after = fresh(sm, tr, "after");
    let outer = fresh(sm, tr, "outer");
    let choices = fresh(sm, tr, "choices");
    let pair = fresh(sm, tr, "pair");
    let observation = fresh(sm, tr, "observation");
    let deposited_view = fresh(sm, tr, "deposit_view");
    let owners: Vec<_> = sm
        .fields
        .iter()
        .filter_map(|f| raw_owners.get(&f.name.to_string()))
        .collect();
    let first = owners[0];
    let mut joins = vec![];
    for other in owners.iter().skip(1) {
        joins.push(quote! {let tracked #remaining=#remaining.join(#other);});
    }
    let observe = if let Some(n) = have.keys().next() {
        let a = &arguments[n];
        quote! {let tracked #observation=#a.raw.borrow().tracked_borrow().observe();}
    } else {
        quote! {}
    };
    let h = if have.is_empty() {
        quote! {Fragment #expr::empty()}
    } else {
        quote! {#observation.fragment()}
    };
    let execute = if have.is_empty() {
        let dep_arg = if deposited.is_empty() {
            quote! {}
        } else {
            quote! {#deposit,}
        };
        if withdrawn.is_empty() {
            quote! {let tracked #remaining=Protocol #expr::#local(#remaining,#dep_arg #(#pn),*);let tracked #physical=IMap::<int,#permission>::tracked_empty();}
        } else {
            quote! {let tracked(#remaining,#physical)=Protocol #expr::#local(#remaining,#dep_arg #(#pn),*);}
        }
    } else {
        quote! {Protocol #expr::#ready(#initial,#h,#deposited_view,#(#pn),*);Protocol #expr::#frame(#initial,#h,#deposited_view,#(#pn),*);let #choices=ISet::new(|#pair:(Fragment #types,IMap<int,#permission>)|Protocol #expr::#outputs(#initial,#h,#pair.0,#deposited_view,#pair.1,#(#pn),*));let tracked(#remaining,#physical)=#remaining.exchange_nondeterministic_with_observation(&#observation,#deposit,#choices);}
    };
    let cn: Vec<_> = constants.iter().map(|f| &f.name).collect();
    let setters: Vec<_> = cn.iter().map(|n| format_ident!("with_{n}")).collect();
    let cget: Vec<_> = cn.iter().map(|n| format_ident!("value_{n}")).collect();
    let mut restores = vec![];
    let mut parts = vec![];
    let mut outtypes = vec![];
    let mut outvalues = vec![];
    let mut outfrags = HashMap::new();
    let out = fresh(sm, tr, "output");
    let produced: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| {
            added.contains_key(&f.name.to_string()) || withdrawn.contains_key(&f.name.to_string())
        })
        .collect();
    let tuple = produced.len() > 1;
    for f in sm.fields.iter().filter(|f| {
        ops.updates.contains_key(&f.name.to_string()) || added.contains_key(&f.name.to_string())
    }) {
        let n = &f.name;
        let select = format_ident!("select_{n}");
        let without = format_ident!("without_{n}");
        let law = format_ident!("take_{n}_law");
        let part = fresh(sm, tr, &format!("part_{n}"));
        let rest = fresh(sm, tr, &format!("rest_{n}"));
        let raw = fresh(sm, tr, &format!("produced_{n}"));
        let split = quote! {#remaining.fragment().#law();let #part=#remaining.fragment().#select()#(.#setters(#initial.#cget()))*;let #rest=#remaining.fragment().#without();assert(Fragment #expr::op(#part,#rest)==#remaining.fragment());let tracked(#raw,#remaining)=#remaining.split(#part,#rest);};
        if let Some(a) = arguments
            .get(&n.to_string())
            .filter(|_| ops.updates.contains_key(&n.to_string()))
        {
            restores.push(if raw_mode {
                quote! {#split *#a=Tracked(Some(#raw));}
            } else {
                quote! {#split #a.raw=Tracked(Some(#raw));}
            });
        } else {
            parts.push(quote!{#split let tracked #raw=<#n #types>::__from_token(#raw,self.metadata.clone());});
            outfrags.insert(n.to_string(), raw);
        }
    }
    let mut binding_values = HashMap::new();
    for (i, f) in produced.iter().enumerate() {
        let n = &f.name;
        let index = verus_syn::Index::from(i);
        let access = if tuple {
            quote! {#out.#index@}
        } else {
            quote! {#out}
        };
        if withdrawn.contains_key(&n.to_string()) {
            let key = &keys[&n.to_string()];
            let value = fresh(sm, tr, &format!("withdrawn_{n}"));
            parts.push(quote! {let tracked #value=#physical.tracked_remove(#key);});
            if let Some(binding) = ops.withdrawals.get(&n.to_string()) {
                binding_values.insert(binding.clone(), access.clone());
            }
            outtypes.push(if tuple {
                quote! {Tracked<#permission>}
            } else {
                quote! {#permission}
            });
            outvalues.push(if tuple {
                quote! {Tracked(#value)}
            } else {
                quote! {#value}
            });
        } else {
            let raw = &outfrags[&n.to_string()];
            outtypes.push(if tuple {
                quote! {Tracked<#n #types>}
            } else {
                quote! {#n #types}
            });
            outvalues.push(if tuple {
                quote! {Tracked(#raw)}
            } else {
                quote! {#raw}
            });
            ensures.push(quote! {#access.instance_id()==self.id()});
            ensures.push(quote! {#access.value()});
        }
    }
    for e in &ops.asserts {
        let value = lower(e, fields, &values)?;
        let bindings: Vec<_> = binding_values
            .iter()
            .map(|(n, v)| {
                quote! {let #n=#v;}
            })
            .collect();
        ensures.push(quote! {{#(#bindings)*#value}});
    }
    let returntype = if produced.is_empty() {
        quote! {()}
    } else if tuple {
        quote! {(#(#outtypes),*)}
    } else {
        outtypes[0].clone()
    };
    let returnvalue = if produced.is_empty() {
        quote! {()}
    } else if tuple {
        quote! {(#(#outvalues),*)}
    } else {
        outvalues[0].clone()
    };
    let extensional_key=fresh(sm,tr,"deposited_key");
    let body = if raw_mode {
        quote! {#(#prefixes)*#observe #(#takes)*let tracked #remaining=#first;#(#joins)*let #initial=#remaining.fragment();let tracked mut #deposit=IMap::<int,#permission>::tracked_empty();#(#dep_inserts)*let #deposited_view=#deposit;assert(#deposited_view==#union_shape) by{assert forall|#extensional_key:int|#deposited_view.contains_key(#extensional_key)==(#union_shape).contains_key(#extensional_key) by{};assert forall|#extensional_key:int|#deposited_view.contains_key(#extensional_key) implies #deposited_view[#extensional_key]==(#[trigger] #union_shape)[#extensional_key] by{};}#initial.op_unit();let #partial=Protocol #expr::__observed(Fragment #expr::op(#initial,#h));assert(State #expr::#declared(#partial,#(#pn),*));assert(State #expr::#owners_enabled(#partial,#initial,#h,#(#pn),*));assert(#deposited_view==State #expr::#local_deposited(#partial,#(#pn),*));assert(Protocol #expr::#local_requires(#initial,#h,#deposited_view,#(#pn),*));#execute let(#before,#after,#outer)=Protocol #expr::#witness(#initial,#h,#remaining.fragment(),#deposited_view,#physical,#(#pn),*);let tracked mut #physical=#physical;#(#restores)*#(#parts)*#returnvalue}
    } else {
        let mut callargs = vec![];
        for f in &sm.fields {
            let n = &f.name;
            if let Some(a) = actuals.get(&n.to_string()) {
                callargs.push(quote! {#a});
            }
            if let Some(a) = arguments.get(&n.to_string()) {
                callargs.push(if ops.updates.contains_key(&n.to_string()) {
                    quote! {&mut #a.raw}
                } else if removed.contains_key(&n.to_string()) {
                    quote! {#a.raw.get().tracked_unwrap()}
                } else {
                    quote! {#a}
                });
            }
        }
        quote! {#(#prefixes)*self.#raw_name(#(#pn,)*#(#callargs),*)}
    };
    let visibility = if raw_mode {
        quote! {}
    } else {
        quote! {pub}
    };
    Ok(
        quote! {#visibility proof fn #name(tracked &self,#(#params,)*#(#inputs)*)->(tracked #out:#returntype)requires #(#requires,)*ensures #(#ensures,)*{#body}},
    )
}
