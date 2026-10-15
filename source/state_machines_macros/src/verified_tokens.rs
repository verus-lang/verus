//! Proof-producing subset of VerusSync. Unlike the legacy token generator, this
//! backend emits ordinary checked resource-algebra and frame-update proofs.
use crate::ast::*;
use crate::field_access_visitor::visit_field_accesses;
use crate::parse_token_stream::SMBundle;
use crate::to_token_stream::{
    fix_attrs, generics_for_decl, get_generic_args, set_mode_proof, shardable_type_to_type,
};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use verus_syn::spanned::Spanned;
use verus_syn::{Error, Expr, Ident};

struct Straight {
    updates: HashMap<String, Expr>,
    requires: Vec<Expr>,
    assertions: Vec<(Expr, AssertProof)>,
    count_ops: Vec<(Ident, MonoidStmtType, Expr)>,
    multiset_ops: Vec<(Ident, MonoidStmtType, Expr)>,
    storage_op: Option<(Ident, MonoidStmtType, Expr, AssertProof)>,
}

fn flatten(stmt: &TransitionStmt, out: &mut Straight) -> Result<(), Error> {
    match stmt {
        TransitionStmt::Block(_, xs) => {
            for x in xs {
                flatten(x, out)?;
            }
        }
        TransitionStmt::Initialize(_, id, e) | TransitionStmt::Update(_, id, e) => {
            if out.updates.insert(id.to_string(), e.clone()).is_some() {
                return Err(Error::new(
                    id.span(),
                    "verified backend requires at most one assignment per field",
                ));
            }
        }
        TransitionStmt::Require(span, e) => {
            if !out.assertions.is_empty() || out.storage_op.is_some() {
                return Err(Error::new(
                    *span,
                    "verified backend requires require statements before assert and storage statements",
                ));
            }
            out.requires.push(e.clone());
        }
        TransitionStmt::Assert(_, e, p) => out.assertions.push((e.clone(), p.clone())),
        TransitionStmt::Split(span, kind, children) => {
            if let SplitKind::Special(id, op, proof, None) = &**kind {
                if let MonoidElt::SingletonMultiset(value) = &op.elt {
                    if matches!(
                        op.stmt,
                        MonoidStmtType::Add(false) | MonoidStmtType::Remove | MonoidStmtType::Have
                    ) {
                        if (!out.assertions.is_empty() || out.storage_op.is_some())
                            && !matches!(op.stmt, MonoidStmtType::Add(false))
                        {
                            return Err(Error::new(
                                *span,
                                "verified backend requires remove/have statements before assert and storage statements",
                            ));
                        }
                        out.multiset_ops.push((id.clone(), op.stmt, value.clone()));
                        for child in children {
                            flatten(child, out)?;
                        }
                        return Ok(());
                    }
                }
                if let MonoidElt::OptionSome(Some(value)) = &op.elt {
                    if matches!(
                        op.stmt,
                        MonoidStmtType::Deposit | MonoidStmtType::Withdraw | MonoidStmtType::Guard
                    ) {
                        if out.storage_op.is_some() {
                            return Err(Error::new(
                                *span,
                                "verified backend currently permits one storage operation per transition",
                            ));
                        }
                        out.storage_op = Some((id.clone(), op.stmt, value.clone(), proof.clone()));
                        for child in children {
                            flatten(child, out)?;
                        }
                        return Ok(());
                    }
                }
                if let MonoidElt::General(amount) = &op.elt {
                    if matches!(
                        op.stmt,
                        MonoidStmtType::Add(false) | MonoidStmtType::Remove | MonoidStmtType::Have
                    ) {
                        if (!out.assertions.is_empty() || out.storage_op.is_some())
                            && !matches!(op.stmt, MonoidStmtType::Add(false))
                        {
                            return Err(Error::new(
                                *span,
                                "verified backend requires remove/have statements before assert and storage statements",
                            ));
                        }
                        out.count_ops.push((id.clone(), op.stmt, amount.clone()));
                        for child in children {
                            flatten(child, out)?;
                        }
                        return Ok(());
                    }
                }
            }
            return Err(Error::new(
                *span,
                "verified backend supports count and multiset add/remove/have and storage_option Some(value) deposit/withdraw/guard",
            ));
        }
        TransitionStmt::SubUpdate(span, _, _, _) | TransitionStmt::PostCondition(span, _) => {
            return Err(Error::new(
                *span,
                "verified_tokenized_state_machine currently supports straight-line init/update/require/assert only",
            ));
        }
    }
    Ok(())
}
fn rewrite(
    e: &Expr,
    fields: &HashMap<String, Field>,
    fragment: bool,
    used: &mut HashSet<String>,
) -> Result<TokenStream, Error> {
    let mut expr = e.clone();
    let mut errors = vec![];
    visit_field_accesses(
        &mut expr,
        |errs, field, node| {
            let n = &field.name;
            used.insert(n.to_string());
            if fragment {
                let inner = match field.stype {
                    ShardableType::Variable(_) => quote! { f.#n->Some_0->Exclusive_0 },
                    ShardableType::Constant(_) => quote! { f.#n->Some_0->Agree_0 },
                    _ => {
                        errs.push(Error::new(
                            n.span(),
                            "unowned fields cannot be read by a token operation",
                        ));
                        return;
                    }
                };
                *node = Expr::Verbatim(inner);
            } else {
                *node = Expr::Verbatim(quote! { s.#n });
            }
        },
        &mut errors,
        fields,
    );
    if let Some(error) = errors.into_iter().next() {
        return Err(error);
    }
    Ok(quote! { #expr })
}

/// Polarity annotations describe generated datatypes, rather than their
/// implementations. Translate the older parameter form to item attributes so
/// it is never copied onto an impl or type alias.
pub(crate) fn datatype_generics(
    sm: &SM,
) -> (Option<verus_syn::Generics>, Vec<verus_syn::Attribute>) {
    let mut generics = sm.generics.clone();
    let mut attributes = sm.attrs.clone();
    if let Some(generics) = &mut generics {
        for parameter in &mut generics.params {
            if let verus_syn::GenericParam::Type(parameter) = parameter {
                let name = &parameter.ident;
                parameter.attrs.retain(|attribute| {
                    let path = attribute.meta.path();
                    let Some(last) = path.segments.last() else { return true };
                    if matches!(
                        last.ident.to_string().as_str(),
                        "accept_recursive_types"
                            | "reject_recursive_types"
                            | "reject_recursive_types_in_ground_variants"
                    ) {
                        let annotation = &last.ident;
                        attributes.push(verus_syn::parse_quote! {
                            #[verifier::#annotation(#name)]
                        });
                        false
                    } else {
                        true
                    }
                });
            }
        }
    }
    (generics, attributes)
}

pub fn output(bundle: SMBundle) -> Result<TokenStream, Error> {
    if crate::verified_general::needed(&bundle.sm) {
        return crate::verified_general::output(bundle);
    }
    let sm = &bundle.sm;
    if sm.init_label.is_some() || sm.transition_label.is_some() {
        return Err(Error::new(sm.name.span(), "verified backend does not yet support labels"));
    }
    let name = &sm.name;
    let (generics, datatype_attrs) = datatype_generics(sm);
    let (decl, where_clause) = generics_for_decl(&generics);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let type_args = args.as_ref().map(|a| quote! { <#a> }).unwrap_or_default();
    let expr_args = args.as_ref().map(|a| quote! { ::<#a> }).unwrap_or_default();
    let state_ty = quote! { State #type_args };
    let state_expr = quote! { State #expr_args };
    let fragment_ty = quote! { Fragment #type_args };
    let fragment_expr = quote! { Fragment #expr_args };
    let protocol_ty = quote! { Protocol #type_args };
    let protocol_expr = quote! { Protocol #expr_args };
    let token_ty = quote! { Token #type_args };
    let token_expr = quote! { Token #expr_args };
    let marker_type = args.as_ref().map(|a| quote! { core::marker::PhantomData<(#a,)> });
    let marker_field = marker_type.as_ref().map(|t| quote! { pub __tsm_phantom: #t, });
    let marker_value =
        marker_type.as_ref().map(|_| quote! { __tsm_phantom: core::marker::PhantomData, });

    let fields: HashMap<String, Field> =
        sm.fields.iter().map(|f| (f.name.to_string(), f.clone())).collect();
    let mut state_fields = vec![];
    let mut fragment_fields = vec![];
    let mut fragment_types = vec![];
    let mut names = vec![];
    let mut embed = vec![];
    let mut storage_field = None;
    for field in &sm.fields {
        let n = &field.name;
        let ty = shardable_type_to_type(field.type_span, &field.stype);
        state_fields.push(quote! { pub #n: #ty });
        let (fty, value) = match &field.stype {
            ShardableType::Variable(t) => {
                (quote! { Option<ExclusiveRA<#t>> }, quote! { Some(ExclusiveRA::Exclusive(s.#n)) })
            }
            ShardableType::Constant(t) => {
                (quote! { Option<AgreementRA<#t>> }, quote! { Some(AgreementRA::Agree(s.#n)) })
            }
            ShardableType::NotTokenized(_) => continue,
            ShardableType::StorageOption(t) => {
                if storage_field.is_some() {
                    return Err(Error::new(
                        field.type_span,
                        "verified backend supports one storage_option field",
                    ));
                }
                storage_field = Some((n.clone(), t.clone()));
                continue;
            }
            ShardableType::Count => (
                quote! { ::vstd::resource::tsm::CountRA },
                quote! { ::vstd::resource::tsm::CountRA { count: s.#n } },
            ),
            ShardableType::Multiset(t) => (
                quote! { ::vstd::resource::tsm_finite_multiset::FiniteMultisetRA<#t> },
                quote! { ::vstd::resource::tsm_finite_multiset::finite_multiset_frag(s.#n) },
            ),
            _ => {
                return Err(Error::new(
                    field.type_span,
                    "verified backend currently supports variable, constant, not_tokenized, count, multiset, and storage_option fields",
                ));
            }
        };
        names.push(n);
        fragment_types.push(fty.clone());
        fragment_fields.push(quote! { pub #n: #fty });
        embed.push(quote! { #n: #value });
    }
    if names.is_empty() {
        return Err(Error::new(name.span(), "verified machine needs at least one tokenized field"));
    }
    let (field_specs, field_takes) = crate::verified_ergonomics::field_api(
        sm, &fragment_ty, &token_ty, &names, &fragment_types,
    )?;
    let inv_names: Vec<_> = bundle.extras.invariants.iter().map(|i| &i.func.sig.ident).collect();
    let mut inv_functions = vec![];
    for inv in &bundle.extras.invariants {
        let mut f = inv.func.clone();
        fix_attrs(&mut f.attrs);
        let sig = &f.sig;
        let body = &f.block;
        // The parser represents user invariant declarations as ordinary functions.
        let id = &sig.ident;
        inv_functions.push(quote! { pub open spec fn #id(&self) -> bool #body });
    }
    let mut relations = vec![];
    let mut operations = vec![];
    let mut induction = vec![];
    for trans in &sm.transitions {
        let tr = &trans.name;
        let mut flat = Straight {
            updates: HashMap::new(),
            requires: vec![],
            assertions: vec![],
            count_ops: vec![],
            multiset_ops: vec![],
            storage_op: None,
        };
        flatten(&trans.body, &mut flat)?;
        let pnames: Vec<_> = trans.params.iter().map(|p| &p.name).collect();
        let params: Vec<_> = trans
            .params
            .iter()
            .map(|p| {
                let n = &p.name;
                let t = &p.ty;
                quote! { #n: #t }
            })
            .collect();
        let next = format_ident!("{}_next", tr);
        let local = format_ident!("{}_fragment", tr);
        let req = format_ident!("{}_requires", tr);
        let facts = format_ident!("{}_facts", tr);
        let frame_lemma = format_ident!("{}_frame", tr);
        let safety = format_ident!("{}_safety", tr);
        let strong = format_ident!("{}_strong", tr);
        let mut used = HashSet::new();
        let mut storage_next = None;
        let mut storage_condition = None;
        let mut storage_deposit = quote! { IMap::empty() };
        let mut storage_withdraw = quote! { IMap::empty() };
        let mut storage_guard = None;
        if let Some((id, op, value, proof)) = &flat.storage_op {
            if !matches!(fields[&id.to_string()].stype, ShardableType::StorageOption(_)) {
                return Err(Error::new(
                    id.span(),
                    "verified storage operations require a storage_option field",
                ));
            }
            let value_state = rewrite(value, &fields, false, &mut HashSet::new())?;
            let value_local = rewrite(value, &fields, true, &mut used)?;
            let condition = if matches!(op, MonoidStmtType::Deposit) {
                storage_next = Some(quote! { Some(#value_state) });
                storage_deposit = quote! { IMap::empty().insert(0int, #value_local) };
                quote! { s.#id is None }
            } else {
                if matches!(op, MonoidStmtType::Withdraw) {
                    storage_next = Some(quote! { None });
                    storage_withdraw = quote! { IMap::empty().insert(0int, #value_local) };
                } else {
                    storage_guard = Some(quote! { IMap::empty().insert(0int, #value_local) });
                }
                quote! { s.#id == Some(#value_state) }
            };
            storage_condition = Some((condition, proof));
        }
        let mut count_next = HashMap::new();
        let mut count_local = HashMap::new();
        let mut count_req_state = vec![];
        let mut count_req_local = vec![];
        for (id, op, amount) in &flat.count_ops {
            if !matches!(fields[&id.to_string()].stype, ShardableType::Count) {
                return Err(Error::new(
                    id.span(),
                    "verified backend currently supports add/remove/have only for count fields",
                ));
            }
            let amount_state = rewrite(amount, &fields, false, &mut HashSet::new())?;
            let amount_local = rewrite(amount, &fields, true, &mut used)?;
            if matches!(op, MonoidStmtType::Have) && count_next.contains_key(&id.to_string()) {
                return Err(Error::new(
                    id.span(),
                    "verified backend requires have before add/remove on the same count field",
                ));
            }
            if !matches!(op, MonoidStmtType::Add(false)) {
                count_req_state.push(quote! { s.#id >= (#amount_state) });
                count_req_local.push(quote! { f.#id.count >= (#amount_local) });
            }
            if matches!(op, MonoidStmtType::Add(false) | MonoidStmtType::Remove) {
                if count_next.contains_key(&id.to_string()) {
                    return Err(Error::new(
                        id.span(),
                        "verified backend currently permits one add/remove per count field per transition",
                    ));
                }
                let (state, local) = if matches!(op, MonoidStmtType::Add(false)) {
                    (quote! { s.#id + (#amount_state) }, quote! { f.#id.count + (#amount_local) })
                } else {
                    (
                        quote! { (s.#id - (#amount_state)) as nat },
                        quote! { (f.#id.count - (#amount_local)) as nat },
                    )
                };
                count_next.insert(id.to_string(), state);
                count_local.insert(id.to_string(), local);
            }
        }
        let mut bag_next = HashMap::new();
        let mut bag_local = HashMap::new();
        let mut bag_frame_facts = vec![];
        let mut bag_frame_updates = vec![];
        for (id, op, value) in &flat.multiset_ops {
            if !matches!(fields[&id.to_string()].stype, ShardableType::Multiset(_)) {
                return Err(Error::new(
                    id.span(),
                    "verified singleton multiset operations require a multiset field",
                ));
            }
            let value_state = rewrite(value, &fields, false, &mut HashSet::new())?;
            let value_local = rewrite(value, &fields, true, &mut used)?;
            if matches!(op, MonoidStmtType::Have) && bag_next.contains_key(&id.to_string()) {
                return Err(Error::new(
                    id.span(),
                    "verified backend requires have before add/remove on the same multiset field",
                ));
            }
            bag_frame_facts.push(quote! { ::vstd::resource::tsm_finite_multiset::finite_multiset_owned_frame(f.#id,z.#id,s.#id,#value_local); });
            if !matches!(op, MonoidStmtType::Add(false)) {
                count_req_state.push(quote! { s.#id.count(#value_state) >= 1 });
                count_req_local.push(quote! { f.#id.at(#value_local).count >= 1 });
            }
            if matches!(op, MonoidStmtType::Add(false) | MonoidStmtType::Remove) {
                if bag_next.contains_key(&id.to_string()) {
                    return Err(Error::new(
                        id.span(),
                        "verified backend currently permits one add/remove per multiset field per transition",
                    ));
                }
                if matches!(op, MonoidStmtType::Add(false)) {
                    bag_next.insert(id.to_string(), quote! { s.#id.insert(#value_state) });
                    bag_local.insert(id.to_string(), quote! { f.#id.insert(#value_local) });
                    bag_frame_updates.push(quote! { ::vstd::resource::tsm_finite_multiset::finite_multiset_add_frame(f.#id,z.#id,s.#id,#value_local); });
                } else {
                    bag_next.insert(id.to_string(), quote! { s.#id.remove(#value_state) });
                    bag_local.insert(id.to_string(), quote! { f.#id.remove(#value_local) });
                    bag_frame_updates.push(quote! { ::vstd::resource::tsm_finite_multiset::finite_multiset_remove_frame(f.#id,z.#id,s.#id,#value_local); });
                }
            }
        }
        let mut next_fields = vec![];
        let mut out_fields = vec![];
        for field in &sm.fields {
            let n = &field.name;
            if let Some(e) = flat.updates.get(&n.to_string()) {
                let e_state = rewrite(e, &fields, false, &mut HashSet::new())?;
                next_fields.push(quote! { #n: #e_state });
                if trans.kind != TransitionKind::Init {
                    match field.stype {
                        ShardableType::Variable(_) => {
                            used.insert(n.to_string());
                            let e_local = rewrite(e, &fields, true, &mut used)?;
                            out_fields.push(quote! { #n: Some(ExclusiveRA::Exclusive(#e_local)) });
                        }
                        ShardableType::NotTokenized(_) => {}
                        _ => {
                            return Err(Error::new(
                                n.span(),
                                "only variable fields can be updated",
                            ));
                        }
                    }
                }
            } else {
                if trans.kind == TransitionKind::Init {
                    return Err(Error::new(n.span(), "initialization must initialize every field"));
                }
                if matches!(field.stype, ShardableType::StorageOption(_)) {
                    if let Some(value) = &storage_next {
                        next_fields.push(quote! { #n: #value });
                    } else {
                        next_fields.push(quote! { #n: s.#n });
                    }
                } else if let Some(count) = count_next.get(&n.to_string()) {
                    next_fields.push(quote! { #n: #count });
                    let local = &count_local[&n.to_string()];
                    out_fields
                        .push(quote! { #n: ::vstd::resource::tsm::CountRA { count: #local } });
                } else if let Some(value) = bag_next.get(&n.to_string()) {
                    next_fields.push(quote! { #n: #value });
                    let local = &bag_local[&n.to_string()];
                    out_fields.push(quote! { #n: #local });
                } else {
                    next_fields.push(quote! { #n: s.#n });
                }
                if !matches!(
                    field.stype,
                    ShardableType::NotTokenized(_) | ShardableType::StorageOption(_)
                ) && !count_local.contains_key(&n.to_string())
                    && !bag_local.contains_key(&n.to_string())
                {
                    out_fields.push(quote! { #n: f.#n });
                }
            }
        }
        let mut req_state = count_req_state;
        let mut req_local = count_req_local;
        for e in &flat.requires {
            req_state.push(rewrite(e, &fields, false, &mut HashSet::new())?);
            req_local.push(rewrite(e, &fields, true, &mut used)?);
        }
        let mut fact_state = vec![];
        let mut fact_local = vec![];
        let mut asserts = vec![];
        for (e, proof) in &flat.assertions {
            let es = rewrite(e, &fields, false, &mut HashSet::new())?;
            fact_state.push(es.clone());
            fact_local.push(rewrite(e, &fields, true, &mut used)?);
            if let Some(block) = &proof.proof {
                asserts.push(quote! { assert(#es) by #block });
            } else {
                asserts.push(quote! { assert(#es); });
            }
        }
        if let Some((condition, proof)) = storage_condition {
            fact_state.push(condition.clone());
            if let Some(block) = &proof.proof {
                asserts.push(quote! { assert(#condition) by #block });
            } else {
                asserts.push(quote! { assert(#condition); });
            }
        }
        let mut used: Vec<_> = used.into_iter().collect();
        used.sort();
        let required_ownership: Vec<_> = used
            .iter()
            .map(|n| {
                let id = Ident::new(n, tr.span());
                match fields[n].stype {
                    ShardableType::Variable(_) => {
                        quote! { f.#id is Some && f.#id->Some_0 is Exclusive }
                    }
                    ShardableType::Constant(_) => {
                        quote! { f.#id is Some && f.#id->Some_0 is Agree }
                    }
                    _ => unreachable!(),
                }
            })
            .collect();
        let mut shared_fields = vec![];
        let mut shared_owned_requirements = vec![];
        let mut shared_bag_proofs = vec![];
        for field in &sm.fields {
            let id = &field.name;
            if matches!(
                field.stype,
                ShardableType::NotTokenized(_) | ShardableType::StorageOption(_)
            ) {
                continue;
            }
            if flat.updates.contains_key(&id.to_string()) {
                shared_owned_requirements
                    .push(quote! { owned.#id is Some && owned.#id->Some_0 is Exclusive });
                shared_fields.push(quote! { #id: Self::#local(f, #(#pnames),*).#id });
            } else if let Some((_, op, amount)) = flat.count_ops.iter().find(|(n, op, _)| {
                n == id && matches!(op, MonoidStmtType::Add(false) | MonoidStmtType::Remove)
            }) {
                let amount = rewrite(amount, &fields, true, &mut HashSet::new())?;
                let count = if matches!(op, MonoidStmtType::Add(false)) {
                    quote! { owned.#id.count + (#amount) }
                } else {
                    shared_owned_requirements.push(quote! { owned.#id.count >= (#amount) });
                    quote! { (owned.#id.count - (#amount)) as nat }
                };
                shared_fields
                    .push(quote! { #id: ::vstd::resource::tsm::CountRA { count: #count } });
            } else if let Some((_, op, value)) = flat.multiset_ops.iter().find(|(n, op, _)| {
                n == id && matches!(op, MonoidStmtType::Add(false) | MonoidStmtType::Remove)
            }) {
                let value = rewrite(value, &fields, true, &mut HashSet::new())?;
                if matches!(op, MonoidStmtType::Add(false)) {
                    shared_fields.push(quote! { #id: owned.#id.insert(#value) });
                    shared_bag_proofs.push(quote! { ::vstd::resource::tsm_finite_multiset::finite_multiset_add_frame(owned.#id,h.#id,f.#id.values,#value); });
                } else {
                    shared_owned_requirements.push(quote! { owned.#id.at(#value).count >= 1 });
                    shared_fields.push(quote! { #id: owned.#id.remove(#value) });
                    shared_bag_proofs.push(quote! { ::vstd::resource::tsm_finite_multiset::finite_multiset_remove_frame(owned.#id,h.#id,f.#id.values,#value); });
                }
            } else {
                shared_fields.push(quote! { #id: owned.#id });
            }
        }
        let lemma = bundle.extras.lemmas.iter().find(|l| l.purpose.transition == *tr);
        let induct_call = if let Some(l) = lemma {
            let id = &l.func.sig.ident;
            if trans.kind == TransitionKind::Init {
                quote! { #state_expr::#id(s, #(#pnames),*); }
            } else {
                quote! { #state_expr::#id(s, post, #(#pnames),*); }
            }
        } else {
            TokenStream::new()
        };
        if let Some(l) = lemma {
            let mut f = l.func.clone();
            fix_attrs(&mut f.attrs);
            let span = f.sig.span();
            set_mode_proof(&mut f.sig, span);
            let condition = if trans.kind == TransitionKind::Init {
                quote! { #state_expr::#tr(post, #(#pnames),*) }
            } else {
                quote! { pre.invariant() && #state_expr::#strong(pre, post, #(#pnames),*) }
            };
            let body = &f.block;
            f.block = verus_syn::parse2(
                quote! {{ requires(#condition); ensures(post.invariant()); #body }},
            )?;
            induction.push(quote! { ::vstd::prelude::verus_impl! { #f } });
        }
        relations.push(quote! {
            pub open spec fn #next(s: #state_ty, #(#params),*) -> #state_ty { #state_expr { #marker_value #(#next_fields),* } }
        });
        if trans.kind == TransitionKind::Init {
            // Init expressions cannot mention pre, and are evaluated directly.
            relations.pop();
            let init_fields: Vec<_> = sm
                .fields
                .iter()
                .map(|field| {
                    let n = &field.name;
                    let e = &flat.updates[&n.to_string()];
                    quote! {#n: #e}
                })
                .collect();
            relations.push(quote! { pub open spec fn #tr(post:#state_ty, #(#params),*) -> bool { post == #state_expr { #marker_value #(#init_fields),* } && true #(&& (#req_state))* } });
            let (base_param, base_req, allocation) = if let Some((_, ty)) = &storage_field {
                (
                    quote! { tracked __tsm_base: IMap<int, #ty>, },
                    quote! { __tsm_base == Self::storage(#state_expr { #marker_value #(#init_fields),* }), },
                    quote! { #token_expr::alloc_state(s, __tsm_base) },
                )
            } else {
                (quote! {}, quote! {}, quote! { #token_expr::alloc_state(s) })
            };
            operations.push(quote! {
                pub proof fn #tr(#base_param #(#params),*) -> (tracked token: #token_ty)
                    requires #base_req true #(&& (#req_local))*
                    ensures token.fragment() == #protocol_expr::embed(#state_expr { #marker_value #(#init_fields),* })
                {
                    let s = #state_expr { #marker_value #(#init_fields),* };
                    #induct_call
                    #allocation
                }
            });
        } else {
            relations.push(quote! {
                pub open spec fn #strong(pre:#state_ty, post:#state_ty, #(#params),*) -> bool {
                    let s = pre;
                    post == Self::#next(s, #(#pnames),*) && true #(&& (#req_state))* #(&& (#fact_state))*
                }
                pub proof fn #safety(s:#state_ty, #(#params),*)
                    requires s.invariant(), true #(&& (#req_state))*
                    ensures true #(&& (#fact_state))*
                { let pre = s; #(#asserts)* }
            });
            let storage_extras = if let Some((_, ty)) = &storage_field {
                let dep = format_ident!("{}_deposit", tr);
                let wd = format_ident!("{}_withdraw", tr);
                let gd = format_ident!("{}_guarded", tr);
                let guard_map = storage_guard.clone().unwrap_or_else(|| quote! { IMap::empty() });
                operations.push(quote! {
                    pub open spec fn #dep(f:#fragment_ty, #(#params),*) -> IMap<int,#ty> { #storage_deposit }
                    pub open spec fn #wd(f:#fragment_ty, #(#params),*) -> IMap<int,#ty> { #storage_withdraw }
                    pub open spec fn #gd(f:#fragment_ty, #(#params),*) -> IMap<int,#ty> { #guard_map }
                });
                quote! {
                    Self::storage(s).dom().disjoint(Self::#dep(f, #(#pnames),*).dom()),
                    Self::#wd(f, #(#pnames),*).submap_of(Self::storage(s).union_prefer_right(Self::#dep(f, #(#pnames),*))),
                    Self::storage(#state_expr::#next(s, #(#pnames),*)) == Self::storage(s).union_prefer_right(Self::#dep(f, #(#pnames),*)).remove_keys(Self::#wd(f, #(#pnames),*).dom()),
                    Self::#gd(f, #(#pnames),*).submap_of(Self::storage(s)),
                }
            } else {
                quote! {}
            };
            let storage_proof = if storage_field.is_some() {
                let dep = format_ident!("{}_deposit", tr);
                let wd = format_ident!("{}_withdraw", tr);
                quote! {
                    assert(::vstd::prelude::ext_equal(Self::storage(post), Self::storage(s).union_prefer_right(Self::#dep(f, #(#pnames),*)).remove_keys(Self::#wd(f, #(#pnames),*).dom())));
                }
            } else {
                quote! {}
            };
            operations.push(quote! {
                pub open spec fn #req(f: #fragment_ty, #(#params),*) -> bool {
                    true #(&& (#required_ownership))* #(&& (#req_local))*
                }
                pub open spec fn #facts(f: #fragment_ty, #(#params),*) -> bool { true #(&& (#fact_local))* }
                pub open spec fn #local(f: #fragment_ty, #(#params),*) -> #fragment_ty { #fragment_expr { #marker_value #(#out_fields),* } }
                pub proof fn #frame_lemma(f: #fragment_ty, z: #fragment_ty, s:#state_ty, #(#params),*)
                    requires Self::#req(f, #(#pnames),*), s.invariant(), #fragment_expr::op(f,z) == Self::embed(s)
                    ensures #storage_extras Self::#facts(f, #(#pnames),*), #state_expr::#next(s, #(#pnames),*).invariant(),
                        #fragment_expr::op(Self::#local(f, #(#pnames),*),z) == Self::embed(#state_expr::#next(s, #(#pnames),*))
                {
                    #(#bag_frame_facts)*
                    #state_expr::#safety(s, #(#pnames),*);
                    let post = #state_expr::#next(s, #(#pnames),*);
                    #induct_call
                    #(#bag_frame_updates)*
                    #storage_proof
                }
            });
            if let Some((_, ty)) = &storage_field {
                let dep = format_ident!("{}_deposit", tr);
                let wd = format_ident!("{}_withdraw", tr);
                let gd = format_ident!("{}_guarded", tr);
                if storage_guard.is_some() {
                    operations.push(quote! {
                        pub proof fn #tr(tracked token: &#token_ty, #(#params),*) -> (tracked out: &IMap<int,#ty>)
                            requires Self::#req(token.fragment(), #(#pnames),*)
                            ensures *out == Self::#gd(token.fragment(), #(#pnames),*), Self::#facts(token.fragment(), #(#pnames),*)
                        {
                            let f = token.fragment();
                            assert forall|z:#fragment_ty, s:#state_ty| s.invariant() && #fragment_expr::op(f,z) == Self::embed(s)
                                implies Self::#gd(f, #(#pnames),*).submap_of(Self::storage(s)) by {
                                Self::#frame_lemma(f,z,s, #(#pnames),*);
                            }
                            token.validate();
                            let (z,s) = choose|z:#fragment_ty, s:#state_ty| s.invariant() && #fragment_expr::op(f,z) == Self::embed(s);
                            Self::#frame_lemma(f,z,s, #(#pnames),*);
                            token.guard(Self::#gd(f, #(#pnames),*))
                        }
                    });
                } else {
                    let is_deposit = flat
                        .storage_op
                        .as_ref()
                        .is_some_and(|(_, op, _, _)| matches!(op, MonoidStmtType::Deposit));
                    let is_withdraw = flat
                        .storage_op
                        .as_ref()
                        .is_some_and(|(_, op, _, _)| matches!(op, MonoidStmtType::Withdraw));
                    let dep_param = if is_deposit {
                        quote! { tracked __tsm_deposit: IMap<int,#ty>, }
                    } else {
                        quote! {}
                    };
                    let dep_req = if is_deposit {
                        quote! { __tsm_deposit == Self::#dep(token.fragment(), #(#pnames),*), }
                    } else {
                        quote! {}
                    };
                    let dep_init = if is_deposit {
                        quote! {}
                    } else {
                        quote! { let tracked __tsm_deposit = IMap::tracked_empty(); }
                    };
                    let return_ty = if is_withdraw {
                        quote! { (#token_ty, IMap<int,#ty>) }
                    } else {
                        quote! { #token_ty }
                    };
                    let out_token = if is_withdraw {
                        quote! { out.0 }
                    } else {
                        quote! { out }
                    };
                    let out_map_contract = if is_withdraw {
                        quote! { out.1 == Self::#wd(token.fragment(), #(#pnames),*), }
                    } else {
                        quote! {}
                    };
                    let result = if is_withdraw {
                        quote! { (updated, resources) }
                    } else {
                        quote! { updated }
                    };
                    operations.push(quote! {
                        pub proof fn #tr(tracked token:#token_ty, #dep_param #(#params),*) -> (tracked out:#return_ty)
                            requires #dep_req Self::#req(token.fragment(), #(#pnames),*)
                            ensures #out_map_contract #out_token.loc() == token.loc(),
                                #out_token.fragment() == Self::#local(token.fragment(), #(#pnames),*), Self::#facts(token.fragment(), #(#pnames),*)
                        {
                            let f = token.fragment();
                            #dep_init
                            assert forall|z:#fragment_ty, s:#state_ty| s.invariant() && #fragment_expr::op(f,z) == Self::embed(s)
                                implies {
                                    Self::storage(s).dom().disjoint(Self::#dep(f, #(#pnames),*).dom())
                                    && Self::#wd(f, #(#pnames),*).submap_of(Self::storage(s).union_prefer_right(Self::#dep(f, #(#pnames),*)))
                                    && (exists|post:#state_ty| post.invariant()
                                        && #fragment_expr::op(Self::#local(f, #(#pnames),*),z) == Self::embed(post)
                                        && Self::storage(post) == Self::storage(s).union_prefer_right(Self::#dep(f, #(#pnames),*)).remove_keys(Self::#wd(f, #(#pnames),*).dom()))
                                } by {
                                    Self::#frame_lemma(f,z,s, #(#pnames),*);
                                    let post = #state_expr::#next(s, #(#pnames),*);
                                    assert(post.invariant()
                                        && #fragment_expr::op(Self::#local(f, #(#pnames),*),z) == Self::embed(post)
                                        && Self::storage(post) == Self::storage(s).union_prefer_right(Self::#dep(f, #(#pnames),*)).remove_keys(Self::#wd(f, #(#pnames),*).dom()));
                                }
                            token.validate();
                            let (z,s) = choose|z:#fragment_ty, s:#state_ty| s.invariant() && #fragment_expr::op(f,z) == Self::embed(s);
                            Self::#frame_lemma(f,z,s, #(#pnames),*);
                            let tracked (updated, resources) = token.exchange(__tsm_deposit, Self::#local(f, #(#pnames),*), Self::#wd(f, #(#pnames),*));
                            #result
                        }
                    });
                }
            } else {
                operations.push(quote! {
                pub proof fn #tr(tracked token: #token_ty, #(#params),*) -> (tracked out: #token_ty)
                    requires Self::#req(token.fragment(), #(#pnames),*)
                    ensures out.loc() == token.loc(), out.fragment() == Self::#local(token.fragment(), #(#pnames),*), Self::#facts(token.fragment(), #(#pnames),*)
                {
                    let f = token.fragment();
                    assert forall|z:#fragment_ty, s:#state_ty| s.invariant() && #fragment_expr::op(f,z) == Self::embed(s)
                        implies exists|post:#state_ty| post.invariant() && #fragment_expr::op(Self::#local(f, #(#pnames),*),z) == Self::embed(post) by {
                        Self::#frame_lemma(f,z,s, #(#pnames),*);
                            let post = #state_expr::#next(s, #(#pnames),*);
                            assert(post.invariant() && #fragment_expr::op(Self::#local(f, #(#pnames),*),z) == Self::embed(post));
                    }
                    token.validate();
                    let (z,s) = choose|z:#fragment_ty, s:#state_ty| s.invariant() && #fragment_expr::op(f,z) == Self::embed(s);
                    Self::#frame_lemma(f,z,s, #(#pnames),*);
                    token.update(Self::#local(f, #(#pnames),*))
                }
            });
            }
            // A shared input contributes observations, while modifications apply
            // exclusively to the consumed fragment. This is the proof-producing
            // counterpart of VerusSync's borrowed token inputs.
            if storage_guard.is_none() {
                let shared_req = format_ident!("{}_shared_requires", tr);
                let owned_next = format_ident!("{}_owned_fragment", tr);
                let shared_frame = format_ident!("{}_shared_frame", tr);
                let shared_tr = format_ident!("{}_with_shared", tr);
                let dep = format_ident!("{}_deposit", tr);
                let wd = format_ident!("{}_withdraw", tr);
                let shared_storage_contract = if storage_field.is_some() {
                    quote! {
                        Self::storage(s).dom().disjoint(Self::#dep(#fragment_expr::op(owned,h), #(#pnames),*).dom()),
                        Self::#wd(#fragment_expr::op(owned,h), #(#pnames),*).submap_of(Self::storage(s).union_prefer_right(Self::#dep(#fragment_expr::op(owned,h), #(#pnames),*))),
                        Self::storage(#state_expr::#next(s, #(#pnames),*)) == Self::storage(s).union_prefer_right(Self::#dep(#fragment_expr::op(owned,h), #(#pnames),*)).remove_keys(Self::#wd(#fragment_expr::op(owned,h), #(#pnames),*).dom()),
                    }
                } else {
                    quote! {}
                };
                operations.push(quote! {
                    pub open spec fn #shared_req(owned:#fragment_ty, h:#fragment_ty, #(#params),*) -> bool {
                        let f = #fragment_expr::op(owned,h);
                        Self::#req(f, #(#pnames),*) #(&& (#shared_owned_requirements))*
                    }
                    pub open spec fn #owned_next(owned:#fragment_ty, h:#fragment_ty, #(#params),*) -> #fragment_ty {
                        let f = #fragment_expr::op(owned,h);
                        #fragment_expr { #marker_value #(#shared_fields),* }
                    }
                    pub proof fn #shared_frame(owned:#fragment_ty, h:#fragment_ty, z:#fragment_ty, s:#state_ty, #(#params),*)
                        requires Self::#shared_req(owned,h, #(#pnames),*), s.invariant(),
                            #fragment_expr::op(#fragment_expr::op(owned,h),z) == Self::embed(s)
                        ensures #shared_storage_contract Self::#facts(#fragment_expr::op(owned,h), #(#pnames),*),
                            #state_expr::#next(s, #(#pnames),*).invariant(),
                            #fragment_expr::op(#fragment_expr::op(Self::#owned_next(owned,h, #(#pnames),*),h),z) == Self::embed(#state_expr::#next(s, #(#pnames),*))
                    {
                        let f = #fragment_expr::op(owned,h);
                        Self::#frame_lemma(f,z,s, #(#pnames),*);
                        #(#shared_bag_proofs)*
                        assert(#fragment_expr::op(Self::#owned_next(owned,h, #(#pnames),*),h) == Self::#local(f, #(#pnames),*));
                    }
                });
                if let Some((_, ty)) = &storage_field {
                    let is_deposit = flat
                        .storage_op
                        .as_ref()
                        .is_some_and(|(_, op, _, _)| matches!(op, MonoidStmtType::Deposit));
                    let is_withdraw = flat
                        .storage_op
                        .as_ref()
                        .is_some_and(|(_, op, _, _)| matches!(op, MonoidStmtType::Withdraw));
                    let dep_param = if is_deposit {
                        quote! { tracked __tsm_deposit:IMap<int,#ty>, }
                    } else {
                        quote! {}
                    };
                    let dep_req = if is_deposit {
                        quote! { __tsm_deposit == Self::#dep(#fragment_expr::op(token.fragment(),shared.fragment()), #(#pnames),*), }
                    } else {
                        quote! {}
                    };
                    let dep_init = if is_deposit {
                        quote! {}
                    } else {
                        quote! { let tracked __tsm_deposit = IMap::tracked_empty(); }
                    };
                    let return_ty = if is_withdraw {
                        quote! { (#token_ty,IMap<int,#ty>) }
                    } else {
                        quote! { #token_ty }
                    };
                    let out_token = if is_withdraw {
                        quote! { out.0 }
                    } else {
                        quote! { out }
                    };
                    let out_map = if is_withdraw {
                        quote! { out.1 == Self::#wd(#fragment_expr::op(token.fragment(),shared.fragment()), #(#pnames),*), }
                    } else {
                        quote! {}
                    };
                    let result = if is_withdraw {
                        quote! { (updated,resources) }
                    } else {
                        quote! { updated }
                    };
                    operations.push(quote! {
                        pub proof fn #shared_tr(tracked mut token:#token_ty, tracked shared:&#token_ty, #dep_param #(#params),*) -> (tracked out:#return_ty)
                            requires #dep_req token.loc()==shared.loc(), Self::#shared_req(token.fragment(),shared.fragment(), #(#pnames),*)
                            ensures #out_map #out_token.loc()==token.loc(),
                                #out_token.fragment()==Self::#owned_next(token.fragment(),shared.fragment(), #(#pnames),*),
                                Self::#facts(#fragment_expr::op(token.fragment(),shared.fragment()), #(#pnames),*)
                        {
                            let owned=token.fragment(); let h=shared.fragment(); let f=#fragment_expr::op(owned,h);
                            #dep_init
                            assert forall|z:#fragment_ty,s:#state_ty| s.invariant() && #fragment_expr::op(f,z)==Self::embed(s)
                                implies Self::storage(s).dom().disjoint(Self::#dep(f, #(#pnames),*).dom())
                                    && Self::#wd(f, #(#pnames),*).submap_of(Self::storage(s).union_prefer_right(Self::#dep(f, #(#pnames),*)))
                                    && (exists|post:#state_ty| post.invariant()
                                        && #fragment_expr::op(#fragment_expr::op(Self::#owned_next(owned,h, #(#pnames),*),h),z)==Self::embed(post)
                                        && Self::storage(post)==Self::storage(s).union_prefer_right(Self::#dep(f, #(#pnames),*)).remove_keys(Self::#wd(f, #(#pnames),*).dom())) by {
                                Self::#shared_frame(owned,h,z,s, #(#pnames),*);
                                let post=#state_expr::#next(s, #(#pnames),*);
                                assert(post.invariant()
                                    && #fragment_expr::op(#fragment_expr::op(Self::#owned_next(owned,h, #(#pnames),*),h),z)==Self::embed(post)
                                    && Self::storage(post)==Self::storage(s).union_prefer_right(Self::#dep(f, #(#pnames),*)).remove_keys(Self::#wd(f, #(#pnames),*).dom()));
                            }
                            token.validate_2(shared);
                            let (z,s)=choose|z:#fragment_ty,s:#state_ty| s.invariant() && #fragment_expr::op(f,z)==Self::embed(s);
                            Self::#shared_frame(owned,h,z,s, #(#pnames),*);
                            let tracked (updated,resources)=token.exchange_with_shared(shared,__tsm_deposit,Self::#owned_next(owned,h, #(#pnames),*),Self::#wd(f, #(#pnames),*));
                            #result
                        }
                    });
                } else {
                    operations.push(quote! {
                        pub proof fn #shared_tr(tracked mut token:#token_ty, tracked shared:&#token_ty, #(#params),*) -> (tracked out:#token_ty)
                            requires token.loc()==shared.loc(), Self::#shared_req(token.fragment(),shared.fragment(), #(#pnames),*)
                            ensures out.loc()==token.loc(), out.fragment()==Self::#owned_next(token.fragment(),shared.fragment(), #(#pnames),*),
                                Self::#facts(#fragment_expr::op(token.fragment(),shared.fragment()), #(#pnames),*)
                        {
                            let owned=token.fragment(); let h=shared.fragment(); let f=#fragment_expr::op(owned,h);
                            assert forall|z:#fragment_ty,s:#state_ty| s.invariant() && #fragment_expr::op(f,z)==Self::embed(s)
                                implies exists|post:#state_ty| post.invariant()
                                    && #fragment_expr::op(#fragment_expr::op(Self::#owned_next(owned,h, #(#pnames),*),h),z)==Self::embed(post) by {
                                Self::#shared_frame(owned,h,z,s, #(#pnames),*);
                                let post=#state_expr::#next(s, #(#pnames),*);
                                assert(post.invariant()
                                    && #fragment_expr::op(#fragment_expr::op(Self::#owned_next(owned,h, #(#pnames),*),h),z)==Self::embed(post));
                            }
                            token.validate_2(shared);
                            let (z,s)=choose|z:#fragment_ty,s:#state_ty| s.invariant() && #fragment_expr::op(f,z)==Self::embed(s);
                            Self::#shared_frame(owned,h,z,s, #(#pnames),*);
                            token.update_with_shared(shared,Self::#owned_next(owned,h, #(#pnames),*))
                        }
                    });
                }
            }
        }
    }
    let normal = &bundle.normal_fns;
    let mut broadcasts = vec![];
    if sm.fields.iter().any(|f| matches!(f.stype, ShardableType::Multiset(_))) {
        broadcasts.push(quote! { ::vstd::multiset::group_multiset_axioms });
    }
    if storage_field.is_some() {
        broadcasts.push(quote! { ::vstd::imap::group_imap_lemmas });
    }
    let multiset_definition = if broadcasts.is_empty() {
        quote! {}
    } else {
        quote! { broadcast use { #(#broadcasts),* }; }
    };
    let storage_definition = if let Some((field, ty)) = &storage_field {
        quote! {
            use ::vstd::resource::tsm_storage::StorageMachine;
            impl #decl StorageMachine for #protocol_ty #where_clause {
                type Key = int;
                type Value = #ty;
                open spec fn storage(s:#state_ty)->IMap<int,#ty> {
                    match s.#field { Some(value) => IMap::empty().insert(0int,value), None => IMap::empty() }
                }
            }
            pub type Token #decl #where_clause = ::vstd::resource::tsm_storage::StorageToken<#protocol_ty>;
        }
    } else {
        quote! { pub type Token #decl #where_clause = ::vstd::resource::tsm::Token<#protocol_ty>; }
    };
    Ok(quote! {
        pub mod #name {
            use super::*;
            ::vstd::prelude::verus! {
                use ::vstd::resource::algebra::ResourceAlgebra;
                use ::vstd::resource::pcm::PCM;
                use ::vstd::resource::exclusive::ExclusiveRA;
                use ::vstd::resource::agree::AgreementRA;
                use ::vstd::resource::tsm::Machine;
                #multiset_definition
                #(#datatype_attrs)*
                pub struct State #decl #where_clause { #marker_field #(#state_fields),* }
                impl #decl #state_ty #where_clause {
                    pub open spec fn invariant(&self)->bool { true #(&& self.#inv_names())* }
                    #(#inv_functions)* #(#relations)* #(#induction)* #(#normal)*
                }
                #(#datatype_attrs)*
                pub struct Fragment #decl #where_clause { #marker_field #(#fragment_fields),* }
                impl #decl #fragment_ty #where_clause {#field_specs}
                impl #decl ResourceAlgebra for #fragment_ty #where_clause {
                    open spec fn valid(self)->bool { true #(&& self.#names.valid())* }
                    open spec fn op(a:Self,b:Self)->Self { #fragment_expr { #marker_value #(#names: <#fragment_types>::op(a.#names,b.#names)),* } }
                    proof fn associative(a:Self,b:Self,c:Self) { #(<#fragment_types>::associative(a.#names,b.#names,c.#names);)* }
                    proof fn commutative(a:Self,b:Self) { #(<#fragment_types>::commutative(a.#names,b.#names);)* }
                    proof fn valid_op(a:Self,b:Self) { #(<#fragment_types>::valid_op(a.#names,b.#names);)* }
                }
                impl #decl PCM for #fragment_ty #where_clause {
                    open spec fn unit()->Self { #fragment_expr { #marker_value #(#names: <#fragment_types>::unit()),* } }
                    proof fn op_unit(self) { #(self.#names.op_unit();)* }
                    proof fn unit_valid() { #(<#fragment_types>::unit_valid();)* }
                }
                #(#datatype_attrs)*
                pub struct Protocol #decl #where_clause { #marker_field }
                impl #decl Machine for #protocol_ty #where_clause {
                    type Fragment = #fragment_ty;
                    type State = #state_ty;
                    open spec fn invariant(s:#state_ty)->bool { s.invariant() }
                    open spec fn embed(s:#state_ty)->#fragment_ty { #fragment_expr { #marker_value #(#embed),* } }
                }
                #storage_definition
                impl #decl #protocol_ty #where_clause { #field_takes #(#operations)* }
            }
        }
    })
}
