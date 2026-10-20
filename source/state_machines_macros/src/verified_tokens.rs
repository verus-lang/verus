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
use verus_syn::{Error, Expr, Ident, Type};

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

/// The raw interface. The straight-line backend keeps its established
/// interface for the machines it supports; every other machine is generated by
/// the general backend, which subsumes its field kinds and statement forms.
pub fn output_raw(bundle: SMBundle) -> Result<TokenStream, Error> {
    if crate::verified_general::needed(&bundle.sm) {
        return crate::verified_general::output(bundle);
    }
    match basic_output(&bundle) {
        Ok(output) => Ok(output),
        Err(_) => crate::verified_general::output(bundle),
    }
}

/// The type paths, generics and fields every item of one machine is written against.
struct Ctx<'a> {
    sm: &'a SM,
    fields: HashMap<String, Field>,
    datatype_attrs: Vec<verus_syn::Attribute>,
    decl: TokenStream,
    where_clause: TokenStream,
    state_ty: TokenStream,
    state_expr: TokenStream,
    fragment_ty: TokenStream,
    fragment_expr: TokenStream,
    protocol_ty: TokenStream,
    protocol_expr: TokenStream,
    token_ty: TokenStream,
    token_expr: TokenStream,
    marker_field: Option<TokenStream>,
    marker_value: Option<TokenStream>,
    storage_field: Option<(Ident, Type)>,
}

/// The per-field declarations of `State` and `Fragment` and the embedding of a state.
struct FieldDecls<'a> {
    state_fields: Vec<TokenStream>,
    fragment_fields: Vec<TokenStream>,
    fragment_types: Vec<TokenStream>,
    names: Vec<&'a Ident>,
    embed: Vec<TokenStream>,
    storage_field: Option<(Ident, Type)>,
}

/// The items the transitions contribute to the `State` and `Protocol` impls.
#[derive(Default)]
struct Items {
    relations: Vec<TokenStream>,
    operations: Vec<TokenStream>,
    induction: Vec<TokenStream>,
}

/// A transition's parameters and the names of its generated items.
struct Names<'a> {
    tr: &'a Ident,
    pnames: Vec<&'a Ident>,
    params: Vec<TokenStream>,
    next: Ident,
    local: Ident,
    req: Ident,
    facts: Ident,
    frame_lemma: Ident,
    safety: Ident,
    strong: Ident,
    dep: Ident,
    wd: Ident,
    gd: Ident,
    shared_req: Ident,
    owned_next: Ident,
    shared_frame: Ident,
    shared_tr: Ident,
}

/// A transition's storage effect: the next storage value, the asserted condition, and the
/// deposited, withdrawn and guarded maps.
struct StorageEffect<'a> {
    next: Option<TokenStream>,
    condition: Option<(TokenStream, &'a AssertProof)>,
    deposit: TokenStream,
    withdraw: TokenStream,
    guard: Option<TokenStream>,
}

/// A transition's count and multiset effects on the state and on the fragment, with the
/// requirements and frame facts they need.
#[derive(Default)]
struct MonoidEffects {
    count_next: HashMap<String, TokenStream>,
    count_local: HashMap<String, TokenStream>,
    bag_next: HashMap<String, TokenStream>,
    bag_local: HashMap<String, TokenStream>,
    req_state: Vec<TokenStream>,
    req_local: Vec<TokenStream>,
    bag_frame_facts: Vec<TokenStream>,
    bag_frame_updates: Vec<TokenStream>,
}

/// A transition's requirements and facts, on the state and on the consumed fragment.
struct Conditions {
    req_state: Vec<TokenStream>,
    req_local: Vec<TokenStream>,
    fact_state: Vec<TokenStream>,
    fact_local: Vec<TokenStream>,
    asserts: Vec<TokenStream>,
    required_ownership: Vec<TokenStream>,
}

/// The fragment a shared-input transition leaves to the consumed token, with its requirements
/// and multiset frame proofs.
struct SharedFragment {
    fields: Vec<TokenStream>,
    owned_requirements: Vec<TokenStream>,
    bag_proofs: Vec<TokenStream>,
}

/// The signature and result pieces of a storage exchange that differ between deposits,
/// withdrawals and plain updates.
struct ExchangeShape {
    dep_param: TokenStream,
    dep_req: TokenStream,
    dep_init: TokenStream,
    return_ty: TokenStream,
    out_token: TokenStream,
    out_map: TokenStream,
    result: TokenStream,
}

/// The straight-line emitter's module for the machine, or an error for machines outside its
/// subset (which `output_raw` then routes to the general emitter).
fn basic_output(bundle: &SMBundle) -> Result<TokenStream, Error> {
    let sm = &bundle.sm;
    if sm.init_label.is_some() || sm.transition_label.is_some() {
        return Err(Error::new(sm.name.span(), "verified backend does not yet support labels"));
    }
    let decls = field_declarations(sm)?;
    let ctx = machine_context(sm, decls.storage_field.clone());
    let (field_specs, field_takes) = crate::verified_ergonomics::field_api(
        sm,
        &ctx.fragment_ty,
        &ctx.token_ty,
        &decls.names,
        &decls.fragment_types,
    )?;
    let inv_functions = invariant_functions(bundle);
    let mut items = Items::default();
    for trans in &sm.transitions {
        transition_items(&ctx, bundle, trans, &mut items)?;
    }
    Ok(assemble(&ctx, bundle, &decls, &inv_functions, &items, &field_specs, &field_takes))
}

/// The machine context: the generated type names applied to the machine's generic
/// arguments, the phantom marker of generic machines, and the field table.
fn machine_context(sm: &SM, storage_field: Option<(Ident, Type)>) -> Ctx<'_> {
    let (generics, datatype_attrs) = datatype_generics(sm);
    let (decl, where_clause) = generics_for_decl(&generics);
    let fields = sm.fields.iter().map(|f| (f.name.to_string(), f.clone())).collect();
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let type_args = args.as_ref().map(|a| quote! { <#a> }).unwrap_or_default();
    let expr_args = args.as_ref().map(|a| quote! { ::<#a> }).unwrap_or_default();
    let marker_type = args.as_ref().map(|a| quote! { core::marker::PhantomData<(#a,)> });
    Ctx {
        sm,
        fields,
        datatype_attrs,
        decl,
        where_clause,
        state_ty: quote! { State #type_args },
        state_expr: quote! { State #expr_args },
        fragment_ty: quote! { Fragment #type_args },
        fragment_expr: quote! { Fragment #expr_args },
        protocol_ty: quote! { Protocol #type_args },
        protocol_expr: quote! { Protocol #expr_args },
        token_ty: quote! { Token #type_args },
        token_expr: quote! { Token #expr_args },
        marker_field: marker_type.as_ref().map(|t| quote! { pub __tsm_phantom: #t, }),
        marker_value: marker_type
            .as_ref()
            .map(|_| quote! { __tsm_phantom: core::marker::PhantomData, }),
        storage_field,
    }
}

/// The state and fragment declarations of every field; rejects field kinds this backend
/// does not support and machines without a tokenized field.
fn field_declarations(sm: &SM) -> Result<FieldDecls<'_>, Error> {
    let mut decls = FieldDecls {
        state_fields: vec![],
        fragment_fields: vec![],
        fragment_types: vec![],
        names: vec![],
        embed: vec![],
        storage_field: None,
    };
    for field in &sm.fields {
        let n = &field.name;
        let ty = shardable_type_to_type(field.type_span, &field.stype);
        decls.state_fields.push(quote! { pub #n: #ty });
        let (fty, value) = match &field.stype {
            ShardableType::Variable(t) => {
                (quote! { Option<ExclusiveRA<#t>> }, quote! { Some(ExclusiveRA::Exclusive(s.#n)) })
            }
            ShardableType::Constant(t) => {
                (quote! { Option<AgreementRA<#t>> }, quote! { Some(AgreementRA::Agree(s.#n)) })
            }
            ShardableType::NotTokenized(_) => continue,
            ShardableType::StorageOption(t) => {
                if decls.storage_field.is_some() {
                    return Err(Error::new(
                        field.type_span,
                        "verified backend supports one storage_option field",
                    ));
                }
                decls.storage_field = Some((n.clone(), t.clone()));
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
        decls.names.push(n);
        decls.fragment_types.push(fty.clone());
        decls.fragment_fields.push(quote! { pub #n: #fty });
        decls.embed.push(quote! { #n: #value });
    }
    if decls.names.is_empty() {
        return Err(Error::new(
            sm.name.span(),
            "verified machine needs at least one tokenized field",
        ));
    }
    Ok(decls)
}

/// The user's invariants as open spec methods of `State`.
fn invariant_functions(bundle: &SMBundle) -> Vec<TokenStream> {
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
    inv_functions
}

/// Adds a transition's relations, induction lemma and token operations to `items`.
fn transition_items(
    ctx: &Ctx,
    bundle: &SMBundle,
    trans: &Transition,
    items: &mut Items,
) -> Result<(), Error> {
    let mut flat = Straight {
        updates: HashMap::new(),
        requires: vec![],
        assertions: vec![],
        count_ops: vec![],
        multiset_ops: vec![],
        storage_op: None,
    };
    flatten(&trans.body, &mut flat)?;
    let n = transition_names(trans);
    let mut used = HashSet::new();
    let storage = storage_effect(ctx, &flat, &mut used)?;
    let mut effects = MonoidEffects::default();
    count_effects(ctx, &flat, &mut used, &mut effects)?;
    multiset_effects(ctx, &flat, &mut used, &mut effects)?;
    let (next_fields, out_fields) = post_fields(ctx, trans, &flat, &storage, &effects, &mut used)?;
    let conds = conditions(ctx, &n, &flat, &storage, &effects, used)?;
    let shared = shared_fragment(ctx, &flat, &n)?;
    let (induct_call, induction) = induction_lemma(ctx, bundle, trans, &n)?;
    items.induction.extend(induction);
    if trans.kind == TransitionKind::Init {
        // Init expressions cannot mention pre, and are evaluated directly.
        init_items(ctx, &n, &flat, &conds, &induct_call, items);
        return Ok(());
    }
    let (next, params) = (&n.next, &n.params);
    let (state_ty, state_expr, marker_value) = (&ctx.state_ty, &ctx.state_expr, &ctx.marker_value);
    items.relations.push(quote! {
        pub open spec fn #next(s: #state_ty, #(#params),*) -> #state_ty { #state_expr { #marker_value #(#next_fields),* } }
    });
    items.relations.push(step_relations(ctx, &n, &conds));
    let storage_extras = if let Some((_, ty)) = &ctx.storage_field {
        items.operations.push(storage_maps(ctx, &n, &storage, ty));
        let contract = storage_frame_contract(ctx, &n, &quote! { f });
        let (gd, pnames) = (&n.gd, &n.pnames);
        quote! { #contract Self::#gd(f, #(#pnames),*).submap_of(Self::storage(s)), }
    } else {
        quote! {}
    };
    items.operations.push(frame_items(
        ctx,
        &n,
        &conds,
        &out_fields,
        &effects,
        &storage_extras,
        &induct_call,
    ));
    let storage_op = flat.storage_op.as_ref().map(|(_, op, _, _)| *op);
    if let Some((_, ty)) = &ctx.storage_field {
        if storage.guard.is_some() {
            items.operations.push(guard_operation(ctx, &n, ty));
        } else {
            let shape = exchange_shape(ctx, &n, storage_op, ty, &quote! { token.fragment() });
            items.operations.push(exchange_operation(ctx, &n, &shape));
        }
    } else {
        items.operations.push(update_operation(ctx, &n));
    }
    // A shared input contributes observations, while modifications apply
    // exclusively to the consumed fragment. This is the proof-producing
    // counterpart of VerusSync's borrowed token inputs.
    if storage.guard.is_none() {
        shared_items(ctx, &n, &shared, storage_op, items);
    }
    Ok(())
}

/// The parameters of a transition and the names of the items generated for it.
fn transition_names(trans: &Transition) -> Names<'_> {
    let tr = &trans.name;
    Names {
        tr,
        pnames: trans.params.iter().map(|p| &p.name).collect(),
        params: trans
            .params
            .iter()
            .map(|p| {
                let n = &p.name;
                let t = &p.ty;
                quote! { #n: #t }
            })
            .collect(),
        next: format_ident!("{}_next", tr),
        local: format_ident!("{}_fragment", tr),
        req: format_ident!("{}_requires", tr),
        facts: format_ident!("{}_facts", tr),
        frame_lemma: format_ident!("{}_frame", tr),
        safety: format_ident!("{}_safety", tr),
        strong: format_ident!("{}_strong", tr),
        dep: format_ident!("{}_deposit", tr),
        wd: format_ident!("{}_withdraw", tr),
        gd: format_ident!("{}_guarded", tr),
        shared_req: format_ident!("{}_shared_requires", tr),
        owned_next: format_ident!("{}_owned_fragment", tr),
        shared_frame: format_ident!("{}_shared_frame", tr),
        shared_tr: format_ident!("{}_with_shared", tr),
    }
}

/// The effect of the transition's storage operation, if any, on the state and on storage.
fn storage_effect<'a>(
    ctx: &Ctx,
    flat: &'a Straight,
    used: &mut HashSet<String>,
) -> Result<StorageEffect<'a>, Error> {
    let fields = &ctx.fields;
    let mut storage = StorageEffect {
        next: None,
        condition: None,
        deposit: quote! { IMap::empty() },
        withdraw: quote! { IMap::empty() },
        guard: None,
    };
    if let Some((id, op, value, proof)) = &flat.storage_op {
        if !matches!(fields[&id.to_string()].stype, ShardableType::StorageOption(_)) {
            return Err(Error::new(
                id.span(),
                "verified storage operations require a storage_option field",
            ));
        }
        let value_state = rewrite(value, fields, false, &mut HashSet::new())?;
        let value_local = rewrite(value, fields, true, used)?;
        let condition = if matches!(op, MonoidStmtType::Deposit) {
            storage.next = Some(quote! { Some(#value_state) });
            storage.deposit = quote! { IMap::empty().insert(0int, #value_local) };
            quote! { s.#id is None }
        } else {
            if matches!(op, MonoidStmtType::Withdraw) {
                storage.next = Some(quote! { None });
                storage.withdraw = quote! { IMap::empty().insert(0int, #value_local) };
            } else {
                storage.guard = Some(quote! { IMap::empty().insert(0int, #value_local) });
            }
            quote! { s.#id == Some(#value_state) }
        };
        storage.condition = Some((condition, proof));
    }
    Ok(storage)
}

/// Adds the effects of the transition's count operations to `effects`.
fn count_effects(
    ctx: &Ctx,
    flat: &Straight,
    used: &mut HashSet<String>,
    effects: &mut MonoidEffects,
) -> Result<(), Error> {
    let fields = &ctx.fields;
    for (id, op, amount) in &flat.count_ops {
        if !matches!(fields[&id.to_string()].stype, ShardableType::Count) {
            return Err(Error::new(
                id.span(),
                "verified backend currently supports add/remove/have only for count fields",
            ));
        }
        let amount_state = rewrite(amount, fields, false, &mut HashSet::new())?;
        let amount_local = rewrite(amount, fields, true, used)?;
        if matches!(op, MonoidStmtType::Have) && effects.count_next.contains_key(&id.to_string()) {
            return Err(Error::new(
                id.span(),
                "verified backend requires have before add/remove on the same count field",
            ));
        }
        if !matches!(op, MonoidStmtType::Add(false)) {
            effects.req_state.push(quote! { s.#id >= (#amount_state) });
            effects.req_local.push(quote! { f.#id.count >= (#amount_local) });
        }
        if matches!(op, MonoidStmtType::Add(false) | MonoidStmtType::Remove) {
            if effects.count_next.contains_key(&id.to_string()) {
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
            effects.count_next.insert(id.to_string(), state);
            effects.count_local.insert(id.to_string(), local);
        }
    }
    Ok(())
}

/// Adds the effects of the transition's singleton multiset operations to `effects`.
fn multiset_effects(
    ctx: &Ctx,
    flat: &Straight,
    used: &mut HashSet<String>,
    effects: &mut MonoidEffects,
) -> Result<(), Error> {
    let fields = &ctx.fields;
    for (id, op, value) in &flat.multiset_ops {
        if !matches!(fields[&id.to_string()].stype, ShardableType::Multiset(_)) {
            return Err(Error::new(
                id.span(),
                "verified singleton multiset operations require a multiset field",
            ));
        }
        let value_state = rewrite(value, fields, false, &mut HashSet::new())?;
        let value_local = rewrite(value, fields, true, used)?;
        if matches!(op, MonoidStmtType::Have) && effects.bag_next.contains_key(&id.to_string()) {
            return Err(Error::new(
                id.span(),
                "verified backend requires have before add/remove on the same multiset field",
            ));
        }
        effects.bag_frame_facts.push(quote! { ::vstd::resource::tsm_finite_multiset::finite_multiset_owned_frame(f.#id,z.#id,s.#id,#value_local); });
        if !matches!(op, MonoidStmtType::Add(false)) {
            effects.req_state.push(quote! { s.#id.count(#value_state) >= 1 });
            effects.req_local.push(quote! { f.#id.at(#value_local).count >= 1 });
        }
        if matches!(op, MonoidStmtType::Add(false) | MonoidStmtType::Remove) {
            if effects.bag_next.contains_key(&id.to_string()) {
                return Err(Error::new(
                    id.span(),
                    "verified backend currently permits one add/remove per multiset field per transition",
                ));
            }
            if matches!(op, MonoidStmtType::Add(false)) {
                effects.bag_next.insert(id.to_string(), quote! { s.#id.insert(#value_state) });
                effects.bag_local.insert(id.to_string(), quote! { f.#id.insert(#value_local) });
                effects.bag_frame_updates.push(quote! { ::vstd::resource::tsm_finite_multiset::finite_multiset_add_frame(f.#id,z.#id,s.#id,#value_local); });
            } else {
                effects.bag_next.insert(id.to_string(), quote! { s.#id.remove(#value_state) });
                effects.bag_local.insert(id.to_string(), quote! { f.#id.remove(#value_local) });
                effects.bag_frame_updates.push(quote! { ::vstd::resource::tsm_finite_multiset::finite_multiset_remove_frame(f.#id,z.#id,s.#id,#value_local); });
            }
        }
    }
    Ok(())
}

/// The fields of the next state and of the fragment the transition produces.
fn post_fields(
    ctx: &Ctx,
    trans: &Transition,
    flat: &Straight,
    storage: &StorageEffect,
    effects: &MonoidEffects,
    used: &mut HashSet<String>,
) -> Result<(Vec<TokenStream>, Vec<TokenStream>), Error> {
    let fields = &ctx.fields;
    let mut next_fields = vec![];
    let mut out_fields = vec![];
    for field in &ctx.sm.fields {
        let n = &field.name;
        if let Some(e) = flat.updates.get(&n.to_string()) {
            let e_state = rewrite(e, fields, false, &mut HashSet::new())?;
            next_fields.push(quote! { #n: #e_state });
            if trans.kind != TransitionKind::Init {
                match field.stype {
                    ShardableType::Variable(_) => {
                        used.insert(n.to_string());
                        let e_local = rewrite(e, fields, true, used)?;
                        out_fields.push(quote! { #n: Some(ExclusiveRA::Exclusive(#e_local)) });
                    }
                    ShardableType::NotTokenized(_) => {}
                    _ => {
                        return Err(Error::new(n.span(), "only variable fields can be updated"));
                    }
                }
            }
        } else {
            if trans.kind == TransitionKind::Init {
                return Err(Error::new(n.span(), "initialization must initialize every field"));
            }
            if matches!(field.stype, ShardableType::StorageOption(_)) {
                if let Some(value) = &storage.next {
                    next_fields.push(quote! { #n: #value });
                } else {
                    next_fields.push(quote! { #n: s.#n });
                }
            } else if let Some(count) = effects.count_next.get(&n.to_string()) {
                next_fields.push(quote! { #n: #count });
                let local = &effects.count_local[&n.to_string()];
                out_fields.push(quote! { #n: ::vstd::resource::tsm::CountRA { count: #local } });
            } else if let Some(value) = effects.bag_next.get(&n.to_string()) {
                next_fields.push(quote! { #n: #value });
                let local = &effects.bag_local[&n.to_string()];
                out_fields.push(quote! { #n: #local });
            } else {
                next_fields.push(quote! { #n: s.#n });
            }
            if !matches!(
                field.stype,
                ShardableType::NotTokenized(_) | ShardableType::StorageOption(_)
            ) && !effects.count_local.contains_key(&n.to_string())
                && !effects.bag_local.contains_key(&n.to_string())
            {
                out_fields.push(quote! { #n: f.#n });
            }
        }
    }
    Ok((next_fields, out_fields))
}

/// The transition's requirements and asserted facts (the storage condition last), and the
/// ownership of every field the fragment-level terms read.
fn conditions(
    ctx: &Ctx,
    n: &Names,
    flat: &Straight,
    storage: &StorageEffect,
    effects: &MonoidEffects,
    mut used: HashSet<String>,
) -> Result<Conditions, Error> {
    let fields = &ctx.fields;
    let mut req_state = effects.req_state.clone();
    let mut req_local = effects.req_local.clone();
    for e in &flat.requires {
        req_state.push(rewrite(e, fields, false, &mut HashSet::new())?);
        req_local.push(rewrite(e, fields, true, &mut used)?);
    }
    let mut fact_state = vec![];
    let mut fact_local = vec![];
    let mut asserts = vec![];
    for (e, proof) in &flat.assertions {
        let es = rewrite(e, fields, false, &mut HashSet::new())?;
        fact_state.push(es.clone());
        fact_local.push(rewrite(e, fields, true, &mut used)?);
        if let Some(block) = &proof.proof {
            asserts.push(quote! { assert(#es) by #block });
        } else {
            asserts.push(quote! { assert(#es); });
        }
    }
    if let Some((condition, proof)) = &storage.condition {
        fact_state.push(condition.clone());
        if let Some(block) = &proof.proof {
            asserts.push(quote! { assert(#condition) by #block });
        } else {
            asserts.push(quote! { assert(#condition); });
        }
    }
    let mut used: Vec<_> = used.into_iter().collect();
    used.sort();
    let required_ownership = used
        .iter()
        .map(|name| {
            let id = Ident::new(name, n.tr.span());
            match fields[name].stype {
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
    Ok(Conditions { req_state, req_local, fact_state, fact_local, asserts, required_ownership })
}

/// The fragment a shared-input variant of the transition leaves to the consumed token.
fn shared_fragment(ctx: &Ctx, flat: &Straight, n: &Names) -> Result<SharedFragment, Error> {
    let fields = &ctx.fields;
    let (local, pnames) = (&n.local, &n.pnames);
    let mut shared =
        SharedFragment { fields: vec![], owned_requirements: vec![], bag_proofs: vec![] };
    for field in &ctx.sm.fields {
        let id = &field.name;
        if matches!(field.stype, ShardableType::NotTokenized(_) | ShardableType::StorageOption(_)) {
            continue;
        }
        if flat.updates.contains_key(&id.to_string()) {
            shared
                .owned_requirements
                .push(quote! { owned.#id is Some && owned.#id->Some_0 is Exclusive });
            shared.fields.push(quote! { #id: Self::#local(f, #(#pnames),*).#id });
        } else if let Some((_, op, amount)) = flat.count_ops.iter().find(|(n, op, _)| {
            n == id && matches!(op, MonoidStmtType::Add(false) | MonoidStmtType::Remove)
        }) {
            let amount = rewrite(amount, fields, true, &mut HashSet::new())?;
            let count = if matches!(op, MonoidStmtType::Add(false)) {
                quote! { owned.#id.count + (#amount) }
            } else {
                shared.owned_requirements.push(quote! { owned.#id.count >= (#amount) });
                quote! { (owned.#id.count - (#amount)) as nat }
            };
            shared.fields.push(quote! { #id: ::vstd::resource::tsm::CountRA { count: #count } });
        } else if let Some((_, op, value)) = flat.multiset_ops.iter().find(|(n, op, _)| {
            n == id && matches!(op, MonoidStmtType::Add(false) | MonoidStmtType::Remove)
        }) {
            let value = rewrite(value, fields, true, &mut HashSet::new())?;
            if matches!(op, MonoidStmtType::Add(false)) {
                shared.fields.push(quote! { #id: owned.#id.insert(#value) });
                shared.bag_proofs.push(quote! { ::vstd::resource::tsm_finite_multiset::finite_multiset_add_frame(owned.#id,h.#id,f.#id.values,#value); });
            } else {
                shared.owned_requirements.push(quote! { owned.#id.at(#value).count >= 1 });
                shared.fields.push(quote! { #id: owned.#id.remove(#value) });
                shared.bag_proofs.push(quote! { ::vstd::resource::tsm_finite_multiset::finite_multiset_remove_frame(owned.#id,h.#id,f.#id.values,#value); });
            }
        } else {
            shared.fields.push(quote! { #id: owned.#id });
        }
    }
    Ok(shared)
}

/// The call of the transition's user induction lemma (empty without one) and the lemma
/// itself, with the transition as precondition and the invariant as postcondition.
fn induction_lemma(
    ctx: &Ctx,
    bundle: &SMBundle,
    trans: &Transition,
    n: &Names,
) -> Result<(TokenStream, Option<TokenStream>), Error> {
    let (tr, strong, pnames, state_expr) = (n.tr, &n.strong, &n.pnames, &ctx.state_expr);
    let Some(l) = bundle.extras.lemmas.iter().find(|l| l.purpose.transition == *tr) else {
        return Ok((TokenStream::new(), None));
    };
    let id = &l.func.sig.ident;
    let induct_call = if trans.kind == TransitionKind::Init {
        quote! { #state_expr::#id(s, #(#pnames),*); }
    } else {
        quote! { #state_expr::#id(s, post, #(#pnames),*); }
    };
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
    f.block =
        verus_syn::parse2(quote! {{ requires(#condition); ensures(post.invariant()); #body }})?;
    let spinoff = crate::verified_model::induction_spinoff(&f.attrs);
    Ok((induct_call, Some(quote! { ::vstd::prelude::verus_impl! { #spinoff #f } })))
}

/// Adds an init transition's initial-state predicate and its token-allocating operation.
fn init_items(
    ctx: &Ctx,
    n: &Names,
    flat: &Straight,
    conds: &Conditions,
    induct_call: &TokenStream,
    items: &mut Items,
) {
    let (tr, params) = (n.tr, &n.params);
    let (state_ty, state_expr, marker_value) = (&ctx.state_ty, &ctx.state_expr, &ctx.marker_value);
    let (token_ty, token_expr, protocol_expr) =
        (&ctx.token_ty, &ctx.token_expr, &ctx.protocol_expr);
    let (req_state, req_local) = (&conds.req_state, &conds.req_local);
    let init_fields: Vec<_> = ctx
        .sm
        .fields
        .iter()
        .map(|field| {
            let n = &field.name;
            let e = &flat.updates[&n.to_string()];
            quote! {#n: #e}
        })
        .collect();
    items.relations.push(quote! { pub open spec fn #tr(post:#state_ty, #(#params),*) -> bool { post == #state_expr { #marker_value #(#init_fields),* } && true #(&& (#req_state))* } });
    let (base_param, base_req, allocation) = if let Some((_, ty)) = &ctx.storage_field {
        (
            quote! { tracked __tsm_base: IMap<int, #ty>, },
            quote! { __tsm_base == Self::storage(#state_expr { #marker_value #(#init_fields),* }), },
            quote! { #token_expr::alloc_state(s, __tsm_base) },
        )
    } else {
        (quote! {}, quote! {}, quote! { #token_expr::alloc_state(s) })
    };
    items.operations.push(quote! {
        pub proof fn #tr(#base_param #(#params),*) -> (tracked token: #token_ty)
            requires #base_req true #(&& (#req_local))*
            ensures token.fragment() == #protocol_expr::embed(#state_expr { #marker_value #(#init_fields),* })
        {
            let s = #state_expr { #marker_value #(#init_fields),* };
            #induct_call
            #allocation
        }
    });
}

/// The strong transition relation and the safety lemma proving the transition's assertions.
fn step_relations(ctx: &Ctx, n: &Names, conds: &Conditions) -> TokenStream {
    let (next, safety, strong, pnames, params) =
        (&n.next, &n.safety, &n.strong, &n.pnames, &n.params);
    let (state_ty, req_state, fact_state, asserts) =
        (&ctx.state_ty, &conds.req_state, &conds.fact_state, &conds.asserts);
    quote! {
        pub open spec fn #strong(pre:#state_ty, post:#state_ty, #(#params),*) -> bool {
            let s = pre;
            post == Self::#next(s, #(#pnames),*) && true #(&& (#req_state))* #(&& (#fact_state))*
        }
        pub proof fn #safety(s:#state_ty, #(#params),*)
            requires s.invariant(), true #(&& (#req_state))*
            ensures true #(&& (#fact_state))*
        { let pre = s; #(#asserts)* }
    }
}

/// The deposited, withdrawn and guarded storage maps of a transition as spec functions.
fn storage_maps(ctx: &Ctx, n: &Names, storage: &StorageEffect, ty: &Type) -> TokenStream {
    let (dep, wd, gd, params, fragment_ty) = (&n.dep, &n.wd, &n.gd, &n.params, &ctx.fragment_ty);
    let (deposit, withdraw) = (&storage.deposit, &storage.withdraw);
    let guard_map = storage.guard.clone().unwrap_or_else(|| quote! { IMap::empty() });
    quote! {
        pub open spec fn #dep(f:#fragment_ty, #(#params),*) -> IMap<int,#ty> { #deposit }
        pub open spec fn #wd(f:#fragment_ty, #(#params),*) -> IMap<int,#ty> { #withdraw }
        pub open spec fn #gd(f:#fragment_ty, #(#params),*) -> IMap<int,#ty> { #guard_map }
    }
}

/// The frame lemma's storage postconditions for the fragment `frag`: the deposit is fresh,
/// the withdrawal is available and the next storage is the exchanged one.
fn storage_frame_contract(ctx: &Ctx, n: &Names, frag: &TokenStream) -> TokenStream {
    let (next, dep, wd, pnames, state_expr) = (&n.next, &n.dep, &n.wd, &n.pnames, &ctx.state_expr);
    quote! {
        Self::storage(s).dom().disjoint(Self::#dep(#frag, #(#pnames),*).dom()),
        Self::#wd(#frag, #(#pnames),*).submap_of(Self::storage(s).union_prefer_right(Self::#dep(#frag, #(#pnames),*))),
        Self::storage(#state_expr::#next(s, #(#pnames),*)) == Self::storage(s).union_prefer_right(Self::#dep(#frag, #(#pnames),*)).remove_keys(Self::#wd(#frag, #(#pnames),*).dom()),
    }
}

/// The fragment-level requirement, facts and output of a transition, and its frame lemma.
fn frame_items(
    ctx: &Ctx,
    n: &Names,
    conds: &Conditions,
    out_fields: &[TokenStream],
    effects: &MonoidEffects,
    storage_extras: &TokenStream,
    induct_call: &TokenStream,
) -> TokenStream {
    let (next, local, req, facts, frame_lemma, safety) =
        (&n.next, &n.local, &n.req, &n.facts, &n.frame_lemma, &n.safety);
    let (pnames, params) = (&n.pnames, &n.params);
    let (state_ty, state_expr, marker_value) = (&ctx.state_ty, &ctx.state_expr, &ctx.marker_value);
    let (fragment_ty, fragment_expr) = (&ctx.fragment_ty, &ctx.fragment_expr);
    let (required_ownership, req_local, fact_local) =
        (&conds.required_ownership, &conds.req_local, &conds.fact_local);
    let (bag_frame_facts, bag_frame_updates) =
        (&effects.bag_frame_facts, &effects.bag_frame_updates);
    let storage_proof = if ctx.storage_field.is_some() {
        let (dep, wd) = (&n.dep, &n.wd);
        quote! {
            assert(::vstd::prelude::ext_equal(Self::storage(post), Self::storage(s).union_prefer_right(Self::#dep(f, #(#pnames),*)).remove_keys(Self::#wd(f, #(#pnames),*).dom())));
        }
    } else {
        quote! {}
    };
    quote! {
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
    }
}

/// The token operation of a storage guard: a shared token borrows the guarded map.
fn guard_operation(ctx: &Ctx, n: &Names, ty: &Type) -> TokenStream {
    let (tr, req, facts, frame_lemma, gd) = (n.tr, &n.req, &n.facts, &n.frame_lemma, &n.gd);
    let (pnames, params) = (&n.pnames, &n.params);
    let (state_ty, fragment_ty, fragment_expr, token_ty) =
        (&ctx.state_ty, &ctx.fragment_ty, &ctx.fragment_expr, &ctx.token_ty);
    quote! {
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
    }
}

/// The deposit parameter, withdrawal result and contract pieces of a storage exchange whose
/// input fragment is `frag`.
fn exchange_shape(
    ctx: &Ctx,
    n: &Names,
    storage_op: Option<MonoidStmtType>,
    ty: &Type,
    frag: &TokenStream,
) -> ExchangeShape {
    let (dep, wd, pnames, token_ty) = (&n.dep, &n.wd, &n.pnames, &ctx.token_ty);
    let is_deposit = storage_op.is_some_and(|op| matches!(op, MonoidStmtType::Deposit));
    let is_withdraw = storage_op.is_some_and(|op| matches!(op, MonoidStmtType::Withdraw));
    let (dep_param, dep_req, dep_init) = if is_deposit {
        (
            quote! { tracked __tsm_deposit: IMap<int,#ty>, },
            quote! { __tsm_deposit == Self::#dep(#frag, #(#pnames),*), },
            quote! {},
        )
    } else {
        (quote! {}, quote! {}, quote! { let tracked __tsm_deposit = IMap::tracked_empty(); })
    };
    let (return_ty, out_token, out_map, result) = if is_withdraw {
        (
            quote! { (#token_ty, IMap<int,#ty>) },
            quote! { out.0 },
            quote! { out.1 == Self::#wd(#frag, #(#pnames),*), },
            quote! { (updated, resources) },
        )
    } else {
        (quote! { #token_ty }, quote! { out }, quote! {}, quote! { updated })
    };
    ExchangeShape { dep_param, dep_req, dep_init, return_ty, out_token, out_map, result }
}

/// The token operation of a transition on a machine with storage: the token is exchanged
/// for its next fragment, taking the deposit and returning the withdrawal.
fn exchange_operation(ctx: &Ctx, n: &Names, shape: &ExchangeShape) -> TokenStream {
    let (tr, next, local, req, facts, frame_lemma, dep, wd) =
        (n.tr, &n.next, &n.local, &n.req, &n.facts, &n.frame_lemma, &n.dep, &n.wd);
    let (pnames, params) = (&n.pnames, &n.params);
    let (state_ty, state_expr, fragment_ty, fragment_expr, token_ty) =
        (&ctx.state_ty, &ctx.state_expr, &ctx.fragment_ty, &ctx.fragment_expr, &ctx.token_ty);
    let ExchangeShape { dep_param, dep_req, dep_init, return_ty, out_token, out_map, result } =
        shape;
    quote! {
        pub proof fn #tr(tracked token:#token_ty, #dep_param #(#params),*) -> (tracked out:#return_ty)
            requires #dep_req Self::#req(token.fragment(), #(#pnames),*)
            ensures #out_map #out_token.loc() == token.loc(),
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
    }
}

/// The token operation of a transition on a machine without storage: the token is updated
/// to its next fragment.
fn update_operation(ctx: &Ctx, n: &Names) -> TokenStream {
    let (tr, next, local, req, facts, frame_lemma) =
        (n.tr, &n.next, &n.local, &n.req, &n.facts, &n.frame_lemma);
    let (pnames, params) = (&n.pnames, &n.params);
    let (state_ty, state_expr, fragment_ty, fragment_expr, token_ty) =
        (&ctx.state_ty, &ctx.state_expr, &ctx.fragment_ty, &ctx.fragment_expr, &ctx.token_ty);
    quote! {
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
    }
}

/// Adds the shared-input variant of a transition: its requirement, owned output and frame
/// lemma, and the operation taking a borrowed token.
fn shared_items(
    ctx: &Ctx,
    n: &Names,
    shared: &SharedFragment,
    storage_op: Option<MonoidStmtType>,
    items: &mut Items,
) {
    let (next, local, req, facts, frame_lemma) =
        (&n.next, &n.local, &n.req, &n.facts, &n.frame_lemma);
    let (shared_req, owned_next, shared_frame) = (&n.shared_req, &n.owned_next, &n.shared_frame);
    let (pnames, params) = (&n.pnames, &n.params);
    let (state_ty, state_expr, fragment_ty, fragment_expr, marker_value) =
        (&ctx.state_ty, &ctx.state_expr, &ctx.fragment_ty, &ctx.fragment_expr, &ctx.marker_value);
    let (shared_fields, shared_owned_requirements, shared_bag_proofs) =
        (&shared.fields, &shared.owned_requirements, &shared.bag_proofs);
    let shared_storage_contract = if ctx.storage_field.is_some() {
        storage_frame_contract(ctx, n, &quote! { #fragment_expr::op(owned,h) })
    } else {
        quote! {}
    };
    items.operations.push(quote! {
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
    if let Some((_, ty)) = &ctx.storage_field {
        let frag = quote! { #fragment_expr::op(token.fragment(),shared.fragment()) };
        let shape = exchange_shape(ctx, n, storage_op, ty, &frag);
        items.operations.push(shared_exchange_operation(ctx, n, &shape));
    } else {
        items.operations.push(shared_update_operation(ctx, n));
    }
}

/// The shared-input token operation on a machine with storage.
fn shared_exchange_operation(ctx: &Ctx, n: &Names, shape: &ExchangeShape) -> TokenStream {
    let (next, facts, dep, wd, pnames, params) =
        (&n.next, &n.facts, &n.dep, &n.wd, &n.pnames, &n.params);
    let (shared_req, owned_next, shared_frame, shared_tr) =
        (&n.shared_req, &n.owned_next, &n.shared_frame, &n.shared_tr);
    let (state_ty, state_expr, fragment_ty, fragment_expr, token_ty) =
        (&ctx.state_ty, &ctx.state_expr, &ctx.fragment_ty, &ctx.fragment_expr, &ctx.token_ty);
    let ExchangeShape { dep_param, dep_req, dep_init, return_ty, out_token, out_map, result } =
        shape;
    quote! {
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
    }
}

/// The shared-input token operation on a machine without storage.
fn shared_update_operation(ctx: &Ctx, n: &Names) -> TokenStream {
    let (next, facts, pnames, params) = (&n.next, &n.facts, &n.pnames, &n.params);
    let (shared_req, owned_next, shared_frame, shared_tr) =
        (&n.shared_req, &n.owned_next, &n.shared_frame, &n.shared_tr);
    let (state_ty, state_expr, fragment_ty, fragment_expr, token_ty) =
        (&ctx.state_ty, &ctx.state_expr, &ctx.fragment_ty, &ctx.fragment_expr, &ctx.token_ty);
    quote! {
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
    }
}

/// The machine's module: the `State`, `Fragment` and `Protocol` types with their algebra,
/// storage and the transitions' items.
fn assemble(
    ctx: &Ctx,
    bundle: &SMBundle,
    decls: &FieldDecls,
    inv_functions: &[TokenStream],
    items: &Items,
    field_specs: &TokenStream,
    field_takes: &TokenStream,
) -> TokenStream {
    let sm = ctx.sm;
    let name = &sm.name;
    let (datatype_attrs, decl, where_clause) = (&ctx.datatype_attrs, &ctx.decl, &ctx.where_clause);
    let (state_ty, fragment_ty, fragment_expr, protocol_ty) =
        (&ctx.state_ty, &ctx.fragment_ty, &ctx.fragment_expr, &ctx.protocol_ty);
    let (marker_field, marker_value) = (&ctx.marker_field, &ctx.marker_value);
    let FieldDecls { state_fields, fragment_fields, fragment_types, names, embed, .. } = decls;
    let Items { relations, operations, induction } = items;
    let inv_names: Vec<_> = bundle.extras.invariants.iter().map(|i| &i.func.sig.ident).collect();
    let normal = &bundle.normal_fns;
    let mut broadcasts = vec![];
    if sm.fields.iter().any(|f| matches!(f.stype, ShardableType::Multiset(_))) {
        broadcasts.push(quote! { ::vstd::multiset::group_multiset_axioms });
    }
    if ctx.storage_field.is_some() {
        broadcasts.push(quote! { ::vstd::imap::group_imap_lemmas });
    }
    let multiset_definition = if broadcasts.is_empty() {
        quote! {}
    } else {
        quote! { broadcast use { #(#broadcasts),* }; }
    };
    let storage_definition = if let Some((field, ty)) = &ctx.storage_field {
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
    quote! {
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
    }
}
