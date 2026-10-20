//! Checked sequential execution for the proof-producing backend.
//! Resource updates quantify over every compatible completion; a chosen
//! completion is never exposed as the actual global state.
use crate::ast::*;
use crate::parse_token_stream::SMBundle;
use crate::to_token_stream::{
    fix_attrs, generics_for_decl, get_generic_args, set_mode_proof, shardable_type_to_type,
};
use crate::verified_monoids as monoids;
use proc_macro2::TokenStream;
use quote::{format_ident, quote, ToTokens};
use std::collections::{HashMap, HashSet};
use verus_syn::Error;
use verus_syn::spanned::Spanned;
use verus_syn::{Ident, Type};

fn writes(stmt: &TransitionStmt, out: &mut HashSet<String>) {
    match stmt {
        TransitionStmt::Update(_, n, _) | TransitionStmt::SubUpdate(_, n, _, _) => {
            out.insert(n.to_string());
        }
        TransitionStmt::Block(_, children) | TransitionStmt::Split(_, _, children) => {
            for child in children { writes(child, out); }
        }
        _ => {}
    }
}

/// Some transition updates a `not_tokenized` field.
fn updates_unowned(sm: &SM) -> bool {
    let hidden: HashSet<_> = sm.fields.iter()
        .filter(|f| matches!(f.stype, ShardableType::NotTokenized(_)))
        .map(|f| f.name.to_string()).collect();
    sm.transitions.iter().any(|tr| {
        let mut changed = HashSet::new();
        writes(&tr.body, &mut changed);
        changed.iter().any(|n| hidden.contains(n))
    })
}

/// Exclude updates of unowned fields from the token read footprint only.
/// The original executor, State relations, safety and all-frame obligations
/// continue to process the untouched original transition.
fn drop_unowned_updates(stmt: &mut TransitionStmt, fields: &HashMap<String, Field>) {
    match stmt {
        TransitionStmt::Update(span, n, _) | TransitionStmt::SubUpdate(span, n, _, _)
            if matches!(fields[&n.to_string()].stype, ShardableType::NotTokenized(_)) =>
        {
            *stmt = TransitionStmt::Block(*span, vec![]);
        }
        TransitionStmt::Block(_, children) | TransitionStmt::Split(_, _, children) => {
            for child in children { drop_unowned_updates(child, fields); }
        }
        _ => {}
    }
}

pub fn needs_general_emitter(sm: &SM) -> bool {
    fn walk(s: &TransitionStmt) -> bool {
        match s {
            TransitionStmt::Block(_, xs) => xs.iter().any(walk),
            TransitionStmt::Split(_, k, xs) => match &**k {
                SplitKind::If(_) | SplitKind::Match(_, _) | SplitKind::Let(_, _, _, _) => true,
                SplitKind::Special(_, _, _, Some(_)) => true,
                _ => xs.iter().any(walk),
            },
            _ => false,
        }
    }
    fn general_storage(s: &TransitionStmt, fields: &[Field]) -> bool {
        match s {
            TransitionStmt::Block(_, xs) => xs.iter().any(|s| general_storage(s, fields)),
            TransitionStmt::Split(_, k, xs) => {
                matches!(&**k,SplitKind::Special(name,op,_,_) if matches!(op.elt,MonoidElt::General(_)) && fields.iter().any(|f| f.name==*name && f.stype.is_storage()))
                    || xs.iter().any(|s| general_storage(s, fields))
            }
            _ => false,
        }
    }
    sm.transitions.iter().any(|t| walk(&t.body) || general_storage(&t.body, &sm.fields))
        || sm.fields.iter().any(|f| {
            matches!(
                f.stype,
                ShardableType::StorageMap(..)
                    | ShardableType::StorageIMap(..)
                    | ShardableType::Bool
                    | ShardableType::PersistentBool
                    | ShardableType::PersistentCount
                    | ShardableType::Multiset(_)
                    | ShardableType::Option(_)
                    | ShardableType::PersistentOption(_)
                    | ShardableType::Map(..)
                    | ShardableType::IMap(..)
                    | ShardableType::PersistentMap(..)
                    | ShardableType::PersistentIMap(..)
                    | ShardableType::Set(_)
                    | ShardableType::ISet(_)
                    | ShardableType::PersistentSet(_)
                    | ShardableType::PersistentISet(_)
            )
        })
}

fn contains_guard(s: &TransitionStmt) -> bool {
    match s {
        TransitionStmt::Block(_, xs) => xs.iter().any(contains_guard),
        TransitionStmt::Split(_, k, xs) => {
            matches!(&**k,SplitKind::Special(_,op,_,_) if op.is_guard())
                || xs.iter().any(contains_guard)
        }
        _ => false,
    }
}

/// Physical storage operations seen so far on one execution path.
#[derive(Clone, Default)]
struct StoragePath {
    /// Withdrawn locations: field name and, for singleton operands, the key text.
    /// `None` stands for the single location of a `storage_option` field.
    withdrawn: Vec<(String, Option<String>)>,
    deposited: Vec<(String, Option<String>)>,
}

/// Several deposits, withdrawals and guards may occur on one path; together
/// they form one storage exchange whose deposit is the union of all deposits
/// and whose withdrawal is the union of all withdrawals. That exchange requires
/// the deposit to be disjoint from the pre-state storage, so a deposit into a
/// location withdrawn earlier on the same path cannot be checked. Syntactically
/// identical locations are rejected here; other overlaps fail in the generated
/// storage proof.
fn check_storage_paths(
    s: &TransitionStmt,
    fields: &HashMap<String, Field>,
    path: &mut StoragePath,
) -> Result<(), Error> {
    match s {
        TransitionStmt::Block(_, children) => {
            for child in children {
                check_storage_paths(child, fields, path)?;
            }
        }
        TransitionStmt::Split(span, kind, children) => {
            if let SplitKind::Special(name, op, _, binding) = &**kind {
                let field = &fields[&name.to_string()];
                if field.stype.is_storage() {
                    let location = match (&field.stype, &op.elt) {
                        (ShardableType::StorageOption(_), MonoidElt::OptionSome(_)) => Some(None),
                        (_, MonoidElt::SingletonKV(key, _)) => {
                            Some(Some(key.to_token_stream().to_string()))
                        }
                        _ => None,
                    };
                    // A bound stored value is read from the pre-state. Earlier
                    // withdrawals cannot change a value that is still present;
                    // an earlier deposit at the same location would.
                    if let (Some(_), Some(location)) = (binding, &location) {
                        if path.deposited.contains(&(name.to_string(), location.clone())) {
                            return Err(Error::new(
                                *span,
                                "verified stored-resource bindings cannot observe a value deposited earlier in the same transition",
                            ));
                        }
                    }
                    if op.stmt.is_withdraw() {
                        if let Some(location) = location {
                            path.withdrawn.push((name.to_string(), location));
                        }
                    } else if op.stmt.is_deposit() {
                        if let Some(location) = location {
                            path.deposited.push((name.to_string(), location.clone()));
                            if path.withdrawn.contains(&(name.to_string(), location)) {
                                return Err(Error::new(
                                    *span,
                                    "verified storage cannot deposit into a location withdrawn earlier in the same transition: the combined storage exchange requires its deposit to be disjoint from the pre-state storage",
                                ));
                            }
                        }
                    }
                }
            }
            if matches!(&**kind, SplitKind::If(_) | SplitKind::Match(..)) {
                let start = path.clone();
                for child in children {
                    let mut branch = start.clone();
                    check_storage_paths(child, fields, &mut branch)?;
                    for location in branch.withdrawn {
                        if !path.withdrawn.contains(&location) {
                            path.withdrawn.push(location);
                        }
                    }
                    for location in branch.deposited {
                        if !path.deposited.contains(&location) {
                            path.deposited.push(location);
                        }
                    }
                }
            } else {
                for child in children {
                    check_storage_paths(child, fields, path)?;
                }
            }
        }
        _ => {}
    }
    Ok(())
}

fn modified(
    s: &TransitionStmt,
    out: &mut HashSet<String>,
    storage: bool,
    fields: &HashMap<String, Field>,
    property: bool,
) -> Result<(usize, bool), Error> {
    let mut operations = 0;
    let mut withdraw = false;
    match s {
        TransitionStmt::Block(_, xs) => {
            for x in xs {
                let (count, wd) = modified(x, out, storage, fields, property)?;
                operations += count;
                withdraw |= wd;
            }
        }
        TransitionStmt::Split(span, k, xs) => {
            if let SplitKind::Special(n, op, _, _) = &**k {
                if monoids::is_monoid_type(&fields[&n.to_string()].stype) {
                    // Checked separately by the monoid operand/order analyzer.
                } else if !storage
                    || !(matches!(op.stmt, MonoidStmtType::Deposit | MonoidStmtType::Withdraw)
                        || (property && op.stmt.is_guard()))
                    || !matches!(
                        op.elt,
                        MonoidElt::OptionSome(_)
                            | MonoidElt::SingletonKV(_, _)
                            | MonoidElt::General(_)
                    )
                {
                    return Err(Error::new(
                        *span,
                        "verified sequential storage backend supports optional or map deposit/withdraw operands only",
                    ));
                } else {
                    operations = 1;
                    withdraw = op.stmt.is_withdraw();
                }
            }
            let mut branch_count = 0;
            for x in xs {
                let (count, wd) = modified(x, out, storage, fields, property)?;
                branch_count = branch_count.max(count);
                withdraw |= wd;
            }
            operations += branch_count;
        }
        TransitionStmt::Update(_, n, _) | TransitionStmt::SubUpdate(_, n, _, _) => {
            out.insert(n.to_string());
        }
        _ => {}
    }
    Ok((operations, withdraw))
}

/// The legacy observation visitor omits storage-map keys, since legacy valued
/// tokens do not expose keys. Physical map exchange must observe those keys.
///
/// Withdrawal keys are evaluated in the checked full-State relation and the
/// same-witness actual output map, not in a local physical input map (in both
/// storage layouts: the exchange's withdrawal is the difference of the witness
/// states' storage). So they may read fields the operation does not own, or use
/// `pre` as a whole (as the trusted macro, which ignores storage keys, allows);
/// only their `variable` and `constant` reads are recorded. Deposits and guards
/// still require exact local ordinary observations.
fn storage_key_reads(
    s: &TransitionStmt,
    fields: &HashMap<String, Field>,
    out: &mut HashSet<String>,
) -> Result<(), Error> {
    match s {
        TransitionStmt::Block(_, xs) => {
            for x in xs {
                storage_key_reads(x, fields, out)?;
            }
        }
        TransitionStmt::Split(_, k, xs) => {
            if let SplitKind::Special(
                _,
                SpecialOp { elt: MonoidElt::SingletonKV(key, _), stmt, .. },
                _,
                _,
            ) = &**k
            {
                let withdraw = stmt.is_withdraw();
                let mut errors = vec![];
                crate::field_access_visitor::visit_field_accesses(
                    &mut key.clone(),
                    |_, f, _| {
                        if !withdraw || matches!(f.stype,ShardableType::Variable(_) | ShardableType::Constant(_)) {
                            out.insert(f.name.to_string());
                        }
                    },
                    &mut errors,
                    fields,
                );
                if withdraw {
                    errors.retain(|e| !e.to_string().contains("`pre` cannot be used opaquely"));
                }
                if let Some(e) = errors.into_iter().next() {
                    return Err(e);
                }
            }
            for x in xs {
                storage_key_reads(x, fields, out)?;
            }
        }
        _ => {}
    }
    Ok(())
}

fn has_deposit(s: &TransitionStmt) -> bool {
    match s {
        TransitionStmt::Block(_, xs) => xs.iter().any(has_deposit),
        TransitionStmt::Split(_, k, xs) => {
            matches!(&**k,SplitKind::Special(_,op,_,_) if op.stmt.is_deposit())
                || xs.iter().any(has_deposit)
        }
        _ => false,
    }
}

fn optional_storage_key(name:&Ident,fields:&HashMap<String,Field>)->TokenStream{
 let mut names:Vec<_>=fields.values().filter(|f|f.stype.is_storage()).map(|f|f.name.to_string()).collect();names.sort();
 let index=names.iter().position(|n|*n==name.to_string()).expect("validated storage field");
 let literal=verus_syn::LitInt::new(&format!("{index}int"),name.span());quote!{#literal}
}
fn deposit_expression(
    s: &TransitionStmt,
    fields: &HashMap<String, Field>,
) -> Result<TokenStream, Error> {
    deposit_expression_mode(s, fields, false, None)
}
fn local_deposit_expression(
    s: &TransitionStmt,
    fields: &HashMap<String, Field>,
) -> Result<TokenStream, Error> {
    deposit_expression_mode(s, fields, true, None)
}
fn deposit_expression_mode(
    s: &TransitionStmt,
    fields: &HashMap<String, Field>,
    normalize: bool,
    carrier: Option<&crate::verified_storage_carrier::Carrier>,
) -> Result<TokenStream, Error> {
    let empty = quote! {IMap::empty()};
    Ok(match s {
        TransitionStmt::Block(_, xs) => {
            let pieces: Vec<_> = xs
                .iter()
                .filter(|x| has_deposit(x))
                .map(|s| deposit_expression_mode(s, fields, normalize, carrier))
                .collect::<Result<_, _>>()?;
            let mut pieces = pieces.into_iter();
            let mut value = if normalize {
                pieces.next().unwrap_or(empty)
            } else {
                empty
            };
            for piece in pieces {
                value = quote! {(#value).union_prefer_right(#piece)};
            }
            value
        }
        TransitionStmt::Split(span, k, xs) => match &**k {
            SplitKind::Let(p, t, LetKind::Normal, e) => {
                let t = t.as_ref().map(|t| quote! {:#t});
                let child = deposit_expression_mode(&xs[0], fields, normalize, carrier)?;
                quote! {{let #p #t=#e;#child}}
            }
            SplitKind::Let(_, _, LetKind::BirdsEye, _) if has_deposit(s) => {
                return Err(Error::new(
                    *span,
                    "a deposited resource cannot depend on a birds_eye binding",
                ));
            }
            SplitKind::If(e) => {
                let a = deposit_expression_mode(&xs[0], fields, normalize, carrier)?;
                let b = xs
                    .get(1)
                    .map(|s| deposit_expression_mode(s, fields, normalize, carrier))
                    .transpose()?
                    .unwrap_or(empty);
                quote! {if #e{#a}else{#b}}
            }
            SplitKind::Match(e, arms) => {
                let cases: Vec<_> = arms
                    .iter()
                    .zip(xs.iter())
                    .map(|(arm, child)| {
                        let p = &arm.pat;
                        let guard = arm.guard.as_ref().map(|(i, e)| quote! {#i #e});
                        let value = deposit_expression_mode(child, fields, normalize, carrier)?;
                        Ok(quote! {#p #guard=>{#value}})
                    })
                    .collect::<Result<_, Error>>()?;
                quote! {match #e{#(#cases),*}}
            }
            SplitKind::Special(name, op, _, _) if op.stmt.is_deposit() && carrier.is_some() => {
                carrier.unwrap().singleton(name, &op.elt)?
            },
            SplitKind::Special(name, op, _, _) if op.stmt.is_deposit() => match &op.elt {
                MonoidElt::SingletonKV(k, Some(v)) => quote! {IMap::empty().insert(#k,#v)},
                MonoidElt::OptionSome(Some(v)) => {let key=optional_storage_key(name,fields);quote! {IMap::empty().insert(#key,#v)}},
                MonoidElt::General(value) => match &fields[&name.to_string()].stype {
                    ShardableType::StorageOption(_) => {let key=optional_storage_key(name,fields);quote! {
                        match #value {
                            Some(__tsm_stored_value) => IMap::empty().insert(#key,__tsm_stored_value),
                            None => IMap::empty(),
                        }
                    }},
                    ShardableType::StorageMap(..) => quote! {(#value).to_imap()},
                    ShardableType::StorageIMap(..) => quote! {#value},
                    _ => {
                        return Err(Error::new(
                            *span,
                            "a physical deposit requires a storage operand",
                        ))
                    }
                },
                _ => {
                    return Err(Error::new(
                        *span,
                        "verified deposit requires an explicit optional or map value",
                    ));
                }
            },
            SplitKind::Special(name, op, _, binding) => {
                let child = deposit_expression_mode(&xs[0], fields, normalize, carrier)?;
                if let Some(pattern) = binding {
                    let observed = match &op.elt {
                        MonoidElt::OptionSome(None) => quote! {pre.#name->Some_0},
                        MonoidElt::SingletonKV(key, None) => quote! {pre.#name[#key]},
                        _ => {
                            return Err(Error::new(
                                *span,
                                "unsupported binding before stored resource expression",
                            ));
                        }
                    };
                    monoids::bind_pattern(pattern, observed, child)
                } else {
                    child
                }
            }
            _ => empty,
        },
        _ => empty,
    })
}

/// `have` operations on exclusive map fields with a key, in a guard property.
fn guard_map_haves(s: &TransitionStmt, fields: &HashMap<String, Field>) -> Vec<(Ident, verus_syn::Expr)> {
    let mut out = vec![];
    fn walk(s: &TransitionStmt, fields: &HashMap<String, Field>, out: &mut Vec<(Ident, verus_syn::Expr)>) {
        match s {
            TransitionStmt::Block(_, xs) => xs.iter().for_each(|x| walk(x, fields, out)),
            TransitionStmt::Split(_, k, xs) => {
                if let SplitKind::Special(n, op, _, _) = &**k {
                    if matches!(op.stmt, MonoidStmtType::Have)
                        && matches!(fields[&n.to_string()].stype, ShardableType::Map(..) | ShardableType::IMap(..))
                    {
                        if let MonoidElt::SingletonKV(key, _) = &op.elt {
                            out.push((n.clone(), key.clone()));
                        }
                    }
                }
                xs.iter().for_each(|x| walk(x, fields, out));
            }
            _ => {}
        }
    }
    walk(s, fields, &mut out);
    out
}

/// Exclusive `option` fields borrowed by `have f >= Some(..)` in a guard.
/// The `option` and `persistent_option` fields of `have o >= Some(..)`
/// statements, each with whether it is persistent.
fn guard_option_haves(s: &TransitionStmt, fields: &HashMap<String, Field>) -> Vec<(Ident, bool)> {
    let mut out: Vec<(Ident, bool)> = vec![];
    fn walk(s: &TransitionStmt, fields: &HashMap<String, Field>, out: &mut Vec<(Ident, bool)>) {
        match s {
            TransitionStmt::Block(_, xs) => xs.iter().for_each(|x| walk(x, fields, out)),
            TransitionStmt::Split(_, k, xs) => {
                if let SplitKind::Special(n, op, _, _) = &**k {
                    let persistent = match fields[&n.to_string()].stype {
                        ShardableType::Option(_) => Some(false),
                        ShardableType::PersistentOption(_) => Some(true),
                        _ => None,
                    };
                    if let Some(persistent) = persistent {
                        if matches!(op.stmt, MonoidStmtType::Have)
                            && matches!(op.elt, MonoidElt::OptionSome(_))
                            && !out.iter().any(|(m, _)| m == n)
                        {
                            out.push((n.clone(), persistent));
                        }
                    }
                }
                xs.iter().for_each(|x| walk(x, fields, out));
            }
            _ => {}
        }
    }
    walk(s, fields, &mut out);
    out
}

fn guarded_storage(
    s: &TransitionStmt,
    fields: &HashMap<String, Field>,
    carrier: Option<&crate::verified_storage_carrier::Carrier>,
) -> Result<TokenStream, Error> {
    fn convert(s: &mut TransitionStmt) -> bool {
        match s {
            TransitionStmt::Block(_, xs) => {
                let mut any = false;
                for x in xs {
                    any |= convert(x);
                }
                any
            }
            TransitionStmt::Split(_, k, xs) => {
                let mut any = false;
                if let SplitKind::Special(_, op, _, _) = &mut **k {
                    if op.stmt.is_guard() {
                        op.stmt = MonoidStmtType::Deposit;
                        any = true;
                    }
                }
                for x in xs {
                    any |= convert(x);
                }
                any
            }
            _ => false,
        }
    }
    let mut clone = s.clone();
    if !convert(&mut clone) {
        return Err(Error::new(
            *s.get_span(),
            "verified sequential properties require a storage guard",
        ));
    }
    deposit_expression_mode(&clone, fields, false, carrier)
}

/// Safety uses nested conditionals for requirements. Later requirements cannot
/// enter the proof context of an earlier assertion.
fn execute(xs: &[SimplStmt], safety: bool) -> TokenStream {
    let Some((first, rest)) = xs.split_first() else {
        return if safety {
            quote! {true}
        } else {
            quote! {}
        };
    };
    let tail = execute(rest, safety);
    match first {
        SimplStmt::Require(_, e) if safety => quote! { if #e { #tail } else { false } },
        SimplStmt::Require(..) => tail,
        SimplStmt::Assert(_, e, p) => {
            let a = match &p.proof {
                Some(b) => quote! {assert(#e) by #b},
                None => quote! {assert(#e);},
            };
            quote! { #a #tail }
        }
        SimplStmt::PostCondition(..) => tail,
        SimplStmt::Assign(_, n, _, e, _) => quote! { #n = #e; #tail },
        SimplStmt::Let(_, p, ty, e, child, _) => {
            let ty = ty.as_ref().map(|t| quote! {: #t});
            let inner = execute(child, safety);
            if safety {
                quote! {let __tsm_enabled={let #p #ty = #e; #inner}; if __tsm_enabled {#tail}else{false}}
            } else {
                quote! { { let #p #ty = #e; #inner } #tail }
            }
        }
        SimplStmt::Split(_, k, branches, _) => {
            let bodies: Vec<_> = branches.iter().map(|(_, b)| execute(b, safety)).collect();
            let split = match &**k {
                SplitKind::If(e) => {
                    let a = &bodies[0];
                    let b = bodies.get(1).cloned().unwrap_or_default();
                    quote! {if #e {#a} else {#b}}
                }
                SplitKind::Match(e, arms) => {
                    let cases: Vec<_> = arms
                        .iter()
                        .zip(bodies.iter())
                        .map(|(a, b)| {
                            let p = &a.pat;
                            let guard = a.guard.as_ref().map(|(tok, e)| quote! {#tok #e});
                            quote! {#p #guard => {#b}}
                        })
                        .collect();
                    quote! {match #e {#(#cases),*}}
                }
                _ => unreachable!(),
            };
            if safety {
                quote! {let __tsm_enabled=#split; if __tsm_enabled{#tail}else{false}}
            } else {
                quote! {#split #tail}
            }
        }
    }
}

pub fn output(bundle: SMBundle) -> Result<TokenStream, Error> {
    output_with_ready(bundle, &HashSet::new())
}
pub fn output_with_ready(
    bundle: SMBundle,
    local_ready: &HashSet<String>,
) -> Result<TokenStream, Error> {
    let sm = &bundle.sm;
    // Labels are ordinary first parameters of the relations and operations;
    // only their declarations need to be emitted.
    let labels = [&sm.init_label, &sm.transition_label];
    let name = &sm.name;
    let (generics, datatype_attrs) = crate::verified_tokens::datatype_generics(sm);
    let (decl, where_clause) = generics_for_decl(&generics);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let types = args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default();
    let expr = args.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default();
    let st = quote! {State #types};
    let se = quote! {State #expr};
    let ft = quote! {Fragment #types};
    let fe = quote! {Fragment #expr};
    let pt = quote! {Protocol #types};
    let tt = quote! {Token #types};
    let te = quote! {Token #expr};
    let result_ty = quote! {TransitionObservation #types};
    let result_expr = quote! {TransitionObservation #expr};
    let marker =
        args.as_ref().map(|a| quote! {pub __tsm_phantom:core::marker::PhantomData<(#a,)>,});
    let marker_value = args.as_ref().map(|_| quote! {__tsm_phantom:core::marker::PhantomData,});
    let mut sf = vec![];
    let mut ff = vec![];
    let mut names = vec![];
    let mut ftypes = vec![];
    let mut embeds = vec![];
    let mut temps = vec![];
    let mut posts = vec![];
    let mut observations = vec![];
    let caller_helpers=&bundle.normal_fns;
    let caller_invariants:Vec<_>=bundle.extras.invariants.iter().map(|item|&item.func).collect();
    let caller_lemmas:Vec<_>=bundle.extras.lemmas.iter().map(|item|&item.func).collect();
    let carrier = crate::verified_storage_carrier::Carrier::build(sm,
        quote!{#(#caller_helpers)* #(#caller_invariants)* #(#caller_lemmas)*})?;
    let mut storage: Option<(Ident, Type, Type, TokenStream)> = None;
    // Projections of the optional stores (without a carrier), joined below.
    let mut option_projections: Vec<TokenStream> = vec![];
    let storage_fields:HashMap<_,_>=sm.fields.iter().map(|f|(f.name.to_string(),f.clone())).collect();
    let physical_count=sm.fields.iter().filter(|f|f.stype.is_storage()).count();
    if carrier.is_none()&&physical_count>1&&sm.fields.iter().any(|f|f.stype.is_storage()&&!matches!(f.stype,ShardableType::StorageOption(_))){return Err(Error::new(sm.name.span(),"multiple physical fields currently require homogeneous optional stores"));}

    for f in &sm.fields {
        let n = &f.name;
        let t = shardable_type_to_type(f.type_span, &f.stype);
        sf.push(quote! {pub #n:#t});
        let tmp = format_ident!("update_tmp_{}", n);
        temps.push(quote! {let mut #tmp:#t;});
        posts.push(quote! {#n:#tmp});
        let observed = match f.stype {
            ShardableType::Variable(_) => {
                quote! {if f.#n is Some &&f.#n->Some_0 is Exclusive{f.#n->Some_0->Exclusive_0}else{arbitrary()}}
            }
            ShardableType::Constant(_) => {
                quote! {if f.#n is Some &&f.#n->Some_0 is Agree{f.#n->Some_0->Agree_0}else{arbitrary()}}
            }
            _ => quote! {arbitrary()},
        };
        observations.push(quote! {#n:#observed});
        let (ty, v) = match &f.stype {
            ShardableType::Variable(t) => {
                (quote! {Option<ExclusiveRA<#t>>}, quote! {Some(ExclusiveRA::Exclusive(s.#n))})
            }
            ShardableType::Constant(t) => {
                (quote! {Option<AgreementRA<#t>>}, quote! {Some(AgreementRA::Agree(s.#n))})
            }
            ShardableType::NotTokenized(_) => continue,
            s if monoids::is_monoid_type(s) => (monoids::component_type(s), monoids::embed(s, quote! {s.#n})),
            ShardableType::StorageOption(v) => {
                if carrier.is_some() { continue; }
                let key=optional_storage_key(n,&storage_fields);
                let projection=quote!{match s.#n {Some(v)=>IMap::empty().insert(#key,v),None=>IMap::empty()}};
                if let Some((_,_,old_value,_))=&storage{
                    if old_value.to_token_stream().to_string()!=v.to_token_stream().to_string(){return Err(Error::new(f.type_span,"multiple optional stores require identical permission types"));}
                }else{storage=Some((n.clone(),verus_syn::parse_quote!{int},v.clone(),quote!{}));}
                option_projections.push(projection);
                continue;
            }
            ShardableType::StorageIMap(k, v) | ShardableType::StorageMap(k, v) => {
                if carrier.is_some() { continue; }
                if storage.is_some() {
                    return Err(Error::new(
                        f.type_span,
                        "verified sequential backend supports one storage field",
                    ));
                }
                let projection = if matches!(f.stype, ShardableType::StorageMap(..)) {
                    quote! {s.#n.to_imap()}
                } else {
                    quote! {s.#n}
                };
                storage = Some((n.clone(), k.clone(), v.clone(), projection));
                continue;
            }
            _ => {
                return Err(Error::new(
                    f.type_span,
                    "verified sequential backend currently supports variable, constant, not_tokenized, and storage fields",
                ));
            }
        };
        names.push(n);
        ftypes.push(ty.clone());
        ff.push(quote! {pub #n:#ty});
        embeds.push(quote! {#n:#v});
    }
    if let Some((_, _, _, projection)) = &mut storage {
        if !option_projections.is_empty() {
            let mut parts = vec![];
            if !projection.is_empty() {
                parts.push(projection.clone());
            }
            parts.extend(option_projections);
            *projection = crate::verified_storage_carrier::balanced_union(&parts);
        }
    }
    if let Some(carrier) = &carrier {
        storage = Some((carrier.fields[0].name.clone(), carrier.key.clone(), carrier.value.clone(), carrier.projection.clone()));
    }
    let carrier_declarations = carrier.as_ref().map(|c| &c.declarations);
    let (field_specs, field_takes) =
        crate::verified_ergonomics::field_api(sm, &ft, &tt, &names, &ftypes)?;
    let invnames: Vec<_> = bundle.extras.invariants.iter().map(|i| &i.func.sig.ident).collect();
    let invs: Vec<_> = bundle
        .extras
        .invariants
        .iter()
        .map(|i| {
            let n = &i.func.sig.ident;
            let b = &i.func.block;
            quote! {pub open spec fn #n(&self)->bool #b}
        })
        .collect();
    let normal: Vec<_> =
        bundle.normal_fns.iter().map(|f| quote! {::vstd::prelude::verus_impl!{#f}}).collect();
    let mut relations = crate::verified_state_relations::output(&bundle, &st)?;
    let mut ops = vec![];
    let mut lemmas = vec![];
    let fields: HashMap<_, _> = sm.fields.iter().map(|f| (f.name.to_string(), f.clone())).collect();
    for tr in &sm.transitions {
        let guard_property = matches!(tr.kind, TransitionKind::Property | TransitionKind::ReadonlyTransition) && contains_guard(&tr.body);
        let n = &tr.name;
        let ready_inline = if local_ready.contains(&n.to_string()) {
            quote! {#[verifier::inline]}
        } else {
            quote! {}
        };

        let strong = format_ident!("{}_strong", n);
        let enabled = format_ident!("{}_enabled", n);
        let safety = format_ident!("{}_safety", n);
        let run = format_ident!("{}_execute", n);
        let req = format_ident!("{}_requires", n);
        let output = format_ident!("{}_outputs", n);
        let frame = format_ident!("{}_frame", n);
        let owned_post = format_ident!("{}_owned_post", n);
        let shared = format_ident!("{}_with_shared", n);
        let deposited = format_ident!("{}_deposited", n);
        let owners = format_ident!("{}_owners_enabled", n);
        let pn: Vec<_> = tr.params.iter().map(|p| &p.name).collect();
        let params: Vec<_> = tr
            .params
            .iter()
            .map(|p| {
                let n = &p.name;
                let t = &p.ty;
                quote! {#n:#t}
            })
            .collect();
        let (sops, assigned) = crate::simplification::inline_unassigned(
            sm,
            crate::simplification::simplify_ops(sm, &tr.body, tr.kind),
        );
        // Temporaries only for the fields the transition assigns; the others
        // are read from (and kept as) `pre`.
        let tr_temps: Vec<_> = sm
            .fields
            .iter()
            .zip(&temps)
            .filter(|(f, _)| assigned.contains(&f.name.to_string()))
            .map(|(_, t)| t.clone())
            .collect();
        let tr_posts: Vec<_> = sm
            .fields
            .iter()
            .zip(&posts)
            .map(|(f, p)| {
                if assigned.contains(&f.name.to_string()) {
                    p.clone()
                } else {
                    let n = &f.name;
                    quote! {#n:pre.#n}
                }
            })
            .collect();
        let preserved: HashSet<String> =
            sm.fields.iter().map(|f| f.name.to_string()).filter(|f| !assigned.contains(f)).collect();
        // The strong relation of a non-init transition is only established by
        // the generated executor: it needs no per-conjunct error messages.
        let relation = if tr.kind == TransitionKind::Init {
            crate::to_relation::to_relation(&sops, false)
        } else {
            crate::to_relation::to_relation_plain(
                &crate::simplification::merge_preserved(sops.clone(), &preserved),
                false,
            )
        };
        let weak = crate::to_relation::to_is_enabled_condition_weak(&sops);
        let enabling = crate::to_relation::to_is_enabled_condition_strong(&sops);
        let safe_body = execute(&sops, true);
        let run_body = execute(&sops, false);
        let mut changed = HashSet::new();
        let (storage_ops, withdraw) = modified(
            &tr.body,
            &mut changed,
            storage.is_some(),
            &fields,
            matches!(tr.kind, TransitionKind::Property | TransitionKind::ReadonlyTransition),
        )?;
        check_storage_paths(&tr.body,&fields,&mut StoragePath::default())?;
        // Paired exchange outputs when some path has several storage operations.
        let paired = storage_ops > 1;
        let effects = monoids::transition_effects(tr, &fields)?;
        for e in &effects {
            changed.insert(e.field.name.to_string());
        }
        let owner_expression = crate::verified_ownership::ownership_condition(
            &tr.body,
            &fields,
            &ft,
            quote! {owned},
            quote! {h},
        )?;
        let extra_ownership = monoids::extra_ownership(&effects, &pn);
        let ownership_inline=if crate::verified_readiness::inline_ownership(sm,tr) {ready_inline.clone()}else{quote!{}};
        relations.push(quote!{#ownership_inline pub open spec fn #owners(pre:#st,owned:#ft,h:#ft,#(#params),*)->bool{(#owner_expression)&&(#extra_ownership)}});
        let (effect_declarations, effect_calls) =
            monoids::effect_declarations(&effects, &st, &ft, &pt, &strong, &owners, &pn, &params);
        relations.push(effect_declarations);
        let mut access_errors = vec![];
        let mut token_footprint=tr.body.clone();
        if updates_unowned(sm) {
            drop_unowned_updates(&mut token_footprint,&fields);
        }
        let (mut read, _) = crate::field_access_visitor::find_all_accesses(
            &mut token_footprint,
            &mut access_errors,
            &fields,
        );
        storage_key_reads(&tr.body, &fields, &mut read)?;
        if let Some(e) = access_errors.into_iter().next() {
            return Err(e);
        }
        for n in &read {
            if !matches!(fields[n].stype, ShardableType::Variable(_) | ShardableType::Constant(_)) {
                return Err(Error::new(
                    fields[n].name.span(),
                    "unowned fields cannot be read by a token operation",
                ));
            }
        }
        let init = tr.kind == TransitionKind::Init;
        let pre_param = if init {
            quote! {}
        } else {
            quote! {pre:#st,}
        };
        let inv_req = if init {
            quote! {true}
        } else {
            quote! {pre.invariant()}
        };
        // Build calls separately: declarations and expressions have different tokens.
        let pre_call = if init {
            quote! {}
        } else {
            quote! {pre,}
        };
        let rel_pre = if init {
            quote! {}
        } else {
            quote! {pre,}
        };
        let lemma = bundle.extras.lemmas.iter().find(|l| l.purpose.transition == *n);
        let induct = if let Some(l) = lemma {
            let id = &l.func.sig.ident;
            quote! {Self::#id(#rel_pre post,#(#pn),*);}
        } else {
            quote! {}
        };
        if let Some(l) = lemma {
            let mut f = l.func.clone();
            fix_attrs(&mut f.attrs);
            let span = f.sig.span();
            set_mode_proof(&mut f.sig, span);
            let cond = if init {
                quote! {Self::#n(post,#(#pn),*)}
            } else {
                quote! {pre.invariant() && Self::#strong(pre,post,#(#pn),*)}
            };
            let b = &f.block;
            let cardinality_hints: Vec<_> = if carrier.is_some() && !init {
                effects.iter().filter(|effect| matches!(effect.field.stype, ShardableType::Multiset(_))
                    && effect.op == monoids::EffectOp::Remove && !effect.replacement)
                    .map(|effect| {
                        let field = &effect.field.name;
                        let operand = &effect.function;
                        quote! {
                            match Self::#operand(pre,#(#pn),*) {
                                Some(removed) => {assert(post.#field.len()+removed.len()==pre.#field.len());},
                                None => {assert(post.#field.len()==pre.#field.len());},
                            }
                        }
                    }).collect()
            } else {vec![]};
            f.block = verus_syn::parse2(quote! {{requires(#cond);ensures(post.invariant());#b #(#cardinality_hints)*}})?;
            let spinoff=crate::verified_model::induction_spinoff(&f.attrs);
            lemmas.push(quote! {::vstd::prelude::verus_impl!{#spinoff #f}});
        }
        let init_alias = if init {
            quote! {pub open spec fn #n(post:#st,#(#params),*)->bool {Self::#strong(post,#(#pn),*)}}
        } else {
            quote! {}
        };
        let no_withdraw = !withdraw;
        let monotone_storage = if no_withdraw {
            quote! {,pre.__storage().submap_of(post.__storage())}
        } else {
            quote! {}
        };
        let storage_index =
            format_ident!("__tsm_storage_index", span = proc_macro2::Span::mixed_site());
        let agreement_goal=quote!{pre.__storage()[#storage_index]==post.__storage()[#storage_index]};
        let agreement_hint=carrier.as_ref().map(|c|c.pointwise(quote!{#storage_index},agreement_goal)).unwrap_or_default();
        let deposit_domain_goal=quote!{Self::#deposited(pre,#(#pn),*).contains_key(#storage_index)
            == post.__storage().remove_keys(pre.__storage().dom()).contains_key(#storage_index)};
        let deposit_domain_hint=carrier.as_ref().map(|c|c.pointwise(quote!{#storage_index},deposit_domain_goal)).unwrap_or_default();
        let monotone_proof = if no_withdraw {
            quote! {
                assert(pre.__storage().submap_of(post.__storage())) by {
                    assert forall|#storage_index| pre.__storage().contains_key(#storage_index)
                        implies post.__storage().contains_key(#storage_index)&&pre.__storage()[#storage_index]==post.__storage()[#storage_index] by {};
                }
            }
        } else {
            quote! {}
        };
        let storage_ens = if storage.is_some() && !init && paired {
            quote! {,pre.__storage().agrees(post.__storage()),
            pre.__storage().dom().disjoint(Self::#deposited(pre,#(#pn),*).dom()),
            post.__storage().submap_of(pre.__storage().union_prefer_right(Self::#deposited(pre,#(#pn),*)))}
        } else if storage.is_some() && !init {
            quote! {,pre.__storage().agrees(post.__storage()),Self::#deposited(pre,#(#pn),*)==post.__storage().remove_keys(pre.__storage().dom()) #monotone_storage}
        } else {
            quote! {}
        };
        let storage_proof = if storage.is_some() && !init && paired {
            quote! {
                let physical_deposit=Self::#deposited(pre,#(#pn),*);
                assert(pre.__storage().agrees(post.__storage())) by {
                    assert forall|#storage_index| pre.__storage().contains_key(#storage_index)&&post.__storage().contains_key(#storage_index)
                        implies pre.__storage()[#storage_index]==post.__storage()[#storage_index] by {#agreement_hint};
                }
                assert(pre.__storage().dom().disjoint(physical_deposit.dom())) by {
                    assert forall|#storage_index| pre.__storage().contains_key(#storage_index)
                        implies !physical_deposit.contains_key(#storage_index) by {};
                }
                let transferred=pre.__storage().union_prefer_right(physical_deposit);
                assert(post.__storage().submap_of(transferred)) by {
                    assert forall|#storage_index| post.__storage().contains_key(#storage_index)
                        implies transferred.contains_key(#storage_index)&&post.__storage()[#storage_index]==transferred[#storage_index] by {};
                }
            }
        } else if storage.is_some() && !init {
            quote! {
                #monotone_proof
                assert(pre.__storage().agrees(post.__storage())) by {
                    assert forall|#storage_index| pre.__storage().contains_key(#storage_index)&&post.__storage().contains_key(#storage_index)
                        implies pre.__storage()[#storage_index]==post.__storage()[#storage_index] by {#agreement_hint};
                }
                assert(::vstd::prelude::ext_equal(Self::#deposited(pre,#(#pn),*),post.__storage().remove_keys(pre.__storage().dom()))) by {
                    assert forall|#storage_index| Self::#deposited(pre,#(#pn),*).contains_key(#storage_index)
                        == post.__storage().remove_keys(pre.__storage().dom()).contains_key(#storage_index) by {#deposit_domain_hint};
                    assert forall|#storage_index| Self::#deposited(pre,#(#pn),*).contains_key(#storage_index)
                        implies Self::#deposited(pre,#(#pn),*)[#storage_index]==post.__storage().remove_keys(pre.__storage().dom())[#storage_index] by {};
                }
            }
        } else {
            quote! {}
        };
        if let Some((_, k, v, _)) = &storage {
            if !init {
                let expression = deposit_expression_mode(&tr.body, &fields, false, carrier.as_ref())?;
                relations.push(quote!{#ready_inline pub open spec fn #deposited(pre:#st,#(#params),*)->IMap<#k,#v>{#expression}});
            }
        }
        relations.push(quote! {
            pub open spec fn #strong(#pre_param post:#st,#(#params),*)->bool {#relation}
            #init_alias
            pub open spec fn #enabled(#pre_param #(#params),*)->bool {#weak}
            pub proof fn #safety(#pre_param #(#params),*)
                requires #inv_req
                ensures ::vstd::prelude::imply(Self::#enabled(#pre_call #(#pn),*), {#enabling})
            {#(#tr_temps)* let _={#safe_body};}
            pub proof fn #run(#pre_param #(#params),*)->(post:#st)
                requires #inv_req, Self::#enabled(#pre_call #(#pn),*)
                ensures Self::#strong(#rel_pre post,#(#pn),*),post.invariant() #storage_ens
            {
                Self::#safety(#pre_call #(#pn),*);
                #(#tr_temps)* #run_body
                let post=#se{#marker_value #(#tr_posts),*};
                #storage_proof
                #induct
                post
            }
        });
        if guard_property {
            let (storage_n, key, val, _) = storage.as_ref().unwrap();
            let guarded = format_ident!("{}_guarded", n);
            let expression = guarded_storage(&tr.body, &fields, carrier.as_ref())?;
            // Values bound by `have m >= [k => ..]` on exclusive map fields are
            // observed from the owned fragment at k, so the guarded value stays
            // a function of the fragment and is linked to `pre` by map_owned_frame.
            let map_haves = guard_map_haves(&tr.body, &fields);
            let mut observed_fields: Vec<(Ident, Vec<verus_syn::Expr>)> = vec![];
            for (field, key) in &map_haves {
                match observed_fields.iter_mut().find(|(n, _)| n == field) {
                    Some((_, keys)) => keys.push(key.clone()),
                    None => observed_fields.push((field.clone(), vec![key.clone()])),
                }
            }
            // Likewise for values bound by `have o >= Some(..)` on option
            // fields (linked to `pre` by option_owned_frame) and persistent
            // option fields (by persistent_option_owned_frame).
            let option_haves = guard_option_haves(&tr.body, &fields);
            let option_updates: Vec<_> = option_haves.iter().map(|(field, persistent)| {
                if *persistent {
                    quote! {#field: Some(f.#field->Some_0->Agree_0)}
                } else {
                    quote! {#field: Some(f.#field->Some_0->Exclusive_0)}
                }
            }).collect();
            let observed_base = if observed_fields.is_empty() && option_updates.is_empty() {
                quote! {Self::__observed(f)}
            } else {
                let updates: Vec<_> = option_updates.iter().cloned().chain(observed_fields.iter().map(|(field, keys)| {
                    let inserts = keys.iter().map(|k| quote! {.insert(#k, f.#field.at(#k)->Some_0->Exclusive_0)});
                    let empty = match fields[&field.to_string()].stype {
                        ShardableType::IMap(..) => quote! {::vstd::imap::IMap::empty()},
                        _ => quote! {::vstd::map::Map::empty()},
                    };
                    quote! {#field: #empty #(#inserts)*}
                })).collect();
                quote! {#se{#(#updates,)* ..Self::__observed(f)}}
            };
            let mut observed_links: Vec<_> = map_haves.iter().map(|(field, key)| {
                let imap = match fields[&field.to_string()].stype {
                    ShardableType::IMap(..) => quote! {pre.#field},
                    _ => quote! {pre.#field.to_imap()},
                };
                quote! {
                    ::vstd::resource::tsm_collections::map_owned_frame(f.#field, z.#field, #imap, #key,
                        f.#field.at(#key)->Some_0->Exclusive_0);
                }
            }).collect();
            for (field, persistent) in &option_haves {
                observed_links.push(if *persistent {
                    quote! {
                        ::vstd::resource::tsm_collections::persistent_option_owned_frame(f.#field, z.#field, pre.#field,
                            f.#field->Some_0->Agree_0);
                    }
                } else {
                    quote! {
                        ::vstd::resource::tsm_collections::option_owned_frame(f.#field, z.#field, pre.#field,
                            f.#field->Some_0->Exclusive_0);
                    }
                });
            }
            // Tagged multi-field carriers need a per-tag split to lift the
            // field-level guard fact to the combined storage map.
            let guard_cases = match carrier.as_ref() {
                Some(c) => {
                    let k = format_ident!("__tsm_guard_key", span = proc_macro2::Span::mixed_site());
                    let kt = &c.key;
                    let goal = quote! {Self::storage(pre).contains_key(#k)
                        && Self::storage(pre)[#k] == Self::#guarded(f,#(#pn),*)[#k]};
                    let cases = c.tagged_cases(quote! {#k}, goal.clone());
                    quote! {assert forall|#k:#kt| Self::#guarded(f,#(#pn),*).contains_key(#k) implies #goal by {#cases}}
                }
                None => quote! {},
            };
            relations.push(quote!{pub open spec fn #guarded(pre:#st,#(#params),*)->IMap<#key,#val>{#expression}});
            let mut observed_req: Vec<_> = names
                .iter()
                .filter(|n| read.contains(&n.to_string()))
                .map(|n| match fields[&n.to_string()].stype {
                    ShardableType::Variable(_) => quote! {f.#n is Some &&f.#n->Some_0 is Exclusive},
                    ShardableType::Constant(_) => quote! {f.#n is Some &&f.#n->Some_0 is Agree},
                    _ => unreachable!(),
                })
                .collect();
            for (field, persistent) in &option_haves {
                observed_req.push(if *persistent {
                    quote! {f.#field is Some && f.#field->Some_0 is Agree}
                } else {
                    quote! {f.#field is Some && f.#field->Some_0 is Exclusive}
                });
            }
            let observe_equal: Vec<_> = sm
                .fields
                .iter()
                .filter(|f| read.contains(&f.name.to_string()))
                .map(|f| {
                    let n = &f.name;
                    quote! {pre.#n==Self::__observed(f).#n}
                })
                .collect();
            ops.push(quote!{
                pub open spec fn #guarded(f:#ft,#(#params),*)->IMap<#key,#val>{#se::#guarded(#observed_base,#(#pn),*)}
                pub open spec fn #req(f:#ft,#(#params),*)->bool {
                    true #(&& #observed_req)* &&
                    forall|z:#ft,pre:#st|::vstd::prelude::imply(pre.invariant()&&<#ft>::op(f,z)==Self::embed(pre),
                        #se::#owners(pre,f,<#ft>::unit(),#(#pn),*)&&#se::#enabled(pre,#(#pn),*))
                }
                pub proof fn #frame(f:#ft,#(#params),*)
                    requires Self::#req(f,#(#pn),*)
                    ensures ::vstd::resource::tsm_storage::frame_guard::<#pt>(f,Self::#guarded(f,#(#pn),*))
                {
                    assert forall|z:#ft,pre:#st|Self::invariant(pre)&&<#ft>::op(f,z)==Self::embed(pre)
                        implies Self::#guarded(f,#(#pn),*).submap_of(Self::storage(pre)) by {
                        <#ft>::op_unit(f);
                        assert(#se::#enabled(pre,#(#pn),*));
                        let post=#se::#run(pre,#(#pn),*);
                        assert(true #(&& #observe_equal)*);
                        #(#observed_links)*
                        assert(#se::#guarded(pre,#(#pn),*)==Self::#guarded(f,#(#pn),*));
                        // The guard's storage fact (with its user proof) comes from safety.
                        #se::#safety(pre,#(#pn),*);
                        #guard_cases
                        assert(Self::#guarded(f,#(#pn),*).submap_of(Self::storage(pre)));
                    }
                }
                pub proof fn #n(tracked token:&#tt,#(#params),*)->(tracked out:&IMap<#key,#val>)
                    requires Self::#req(token.fragment(),#(#pn),*)
                    ensures *out==Self::#guarded(token.fragment(),#(#pn),*)
                {Self::#frame(token.fragment(),#(#pn),*);token.guard(Self::#guarded(token.fragment(),#(#pn),*))}
            });
            let _ = storage_n;
        } else if init {
            let base_req = quote! {#se::#enabled(#(#pn),*)};
            if let Some((_, k, v, _)) = &storage {
                ops.push(quote!{
                    pub proof fn #n(tracked base:IMap<#k,#v>,#(#params),*)->(tracked out:#tt)
                        requires #base_req,forall|s:#st|::vstd::prelude::imply(#se::#strong(s,#(#pn),*),base==s.__storage())
                        ensures exists|s:#st|#se::#n(s,#(#pn),*)&&s.invariant()&&out.fragment()==Self::embed(s)
                    {let s=#se::#run(#(#pn),*);#te::alloc_state(s,base)}
                });
            } else {
                ops.push(quote!{
                pub proof fn #n(#(#params),*)->(tracked out:#tt)
                    requires #base_req
                    ensures exists|s:#st| #se::#n(s,#(#pn),*) &&s.invariant()&&out.fragment()==Self::embed(s)
                {let s=#se::#run(#(#pn),*);#te::alloc_state(s)}
            });
            }
        } else {
            let owned_req: Vec<_> = names
                .iter()
                .filter(|n| {
                    changed.contains(&n.to_string())
                        && matches!(fields[&n.to_string()].stype, ShardableType::Variable(_))
                })
                .map(|n| quote! {owned.#n is Some &&owned.#n->Some_0 is Exclusive})
                .collect();
            let observed_req:Vec<_>=names.iter().filter(|n|read.contains(&n.to_string())).map(|n|match fields[&n.to_string()].stype {
                ShardableType::Variable(_)=>quote!{<#ft>::op(owned,h).#n is Some &&<#ft>::op(owned,h).#n->Some_0 is Exclusive},
                ShardableType::Constant(_)=>quote!{<#ft>::op(owned,h).#n is Some &&<#ft>::op(owned,h).#n->Some_0 is Agree},
                _=>unreachable!(),
            }).collect();
            let newfields: Vec<_> = names
                .iter()
                .map(|n| {
                    if changed.contains(&n.to_string()) {
                        if let Some(value) = monoids::owned_expression(&effects, n, &se, &pn) {
                            quote! {#n:#value}
                        } else {
                            quote! {#n:Some(ExclusiveRA::Exclusive(post.#n))}
                        }
                    } else {
                        quote! {#n:owned.#n}
                    }
                })
                .collect();
            if let Some((_, key, val, _)) = &storage {
                ops.push(storage_operations(
                    &n,
                    &strong,
                    &enabled,
                    &run,
                    &req,
                    &output,
                    &frame,
                    &owned_post,
                    &shared,
                    &deposited,
                    &owners,
                    &st,
                    &se,
                    &ft,
                    &fe,
                    &pt,
                    &tt,
                    &marker_value,
                    &pn,
                    &params,
                    &owned_req,
                    &observed_req,
                    &newfields,
                    &effect_calls,
                    key,
                    val,
                    withdraw,
                    has_deposit(&tr.body),
                    paired,
                ));
                if local_ready.contains(&n.to_string()) {
                    relations
                        .push(crate::verified_readiness::declared_requires_spec(tr, &st, &params)?);
                    let local_deposited = format_ident!("{}_local_deposited", n);
                    let local_expression = deposit_expression_mode(&tr.body, &fields, true, carrier.as_ref())?;
                    relations.push(quote! {#[verifier::inline] pub open spec fn #local_deposited(pre:#st,#(#params),*)->IMap<#key,#val>{#local_expression}});
                    let reads: Vec<_> = names
                        .iter()
                        .copied()
                        .filter(|n| read.contains(&n.to_string()))
                        .collect();
                    ops.push(crate::verified_readiness::local_ready_api(
                        crate::verified_readiness::Context {
                            sm,
                            tr,
                            st: &st,
                            se: &se,
                            ft: &ft,
                            tt: &tt,
                            result: &result_ty,
                            result_expr: &result_expr,
                            params: &params,
                            pn: &pn,
                            owned: &owned_req,
                            observed: &observed_req,
                            reads: &reads,
                            key,
                            val,
                            deposits: has_deposit(&tr.body),
                            withdraws: withdraw,
                            paired,
                        },
                    )?);
                }
            } else {
                ops.push(quote!{
                pub open spec fn #owned_post(owned:#ft,pre:#st,post:#st,#(#params),*)->#ft {#fe{#marker_value #(#newfields),*}}
                pub open spec fn #req(owned:#ft,h:#ft,#(#params),*)->bool {
                    true #(&& #owned_req)* #(&& #observed_req)* && forall|z:#ft,pre:#st|::vstd::prelude::imply(#[trigger] ::vstd::resource::tsm::completes_with::<#pt>(<#ft>::op(owned,h),z,pre),
                        #se::#enabled(pre,#(#pn),*)&&#se::#owners(pre,owned,h,#(#pn),*))
                }
                pub open spec fn #output(owned:#ft,h:#ft,new:#ft,#(#params),*)->bool {
                    exists|z:#ft,pre:#st,post:#st|pre.invariant()&&<#ft>::op(<#ft>::op(owned,h),z)==Self::embed(pre)
                    && #se::#strong(pre,post,#(#pn),*)&&post.invariant()&&new==Self::#owned_post(owned,pre,post,#(#pn),*)
                    &&<#ft>::op(<#ft>::op(new,h),z)==Self::embed(post)
                }
                pub proof fn #frame(owned:#ft,h:#ft,#(#params),*)
                    requires Self::#req(owned,h,#(#pn),*)
                    ensures ::vstd::resource::tsm::frame_update_nondeterministic::<#pt>(
                        <#ft>::op(owned,h),ISet::new(|new:#ft|Self::#output(owned,h,new,#(#pn),*)).map(|new:#ft|<#ft>::op(new,h)))
                {
                    let outputs=ISet::new(|new:#ft|Self::#output(owned,h,new,#(#pn),*));
                    assert forall|z:#ft,pre:#st|pre.invariant()&&<#ft>::op(<#ft>::op(owned,h),z)==Self::embed(pre)
                        implies ::vstd::resource::tsm::update_point::<#pt>(owned,h,z,pre,outputs) by {
                        assert(::vstd::resource::tsm::completes_with::<#pt>(<#ft>::op(owned,h),z,pre));
                        assert(#se::#owners(pre,owned,h,#(#pn),*));
                        let post=#se::#run(pre,#(#pn),*);
                        #(#effect_calls)*
                        let new=Self::#owned_post(owned,pre,post,#(#pn),*);
                        <#ft>::associative(new,h,z);
                        assert(Self::#output(owned,h,new,#(#pn),*));
                        ::vstd::resource::tsm::update_point_intro::<#pt>(owned,h,z,pre,outputs,new,post);
                    }
                    ::vstd::resource::tsm::frame_update_by_points::<#pt>(owned,h,outputs);
                }
                pub proof fn #shared(tracked owned:#tt,tracked shared:&#tt,#(#params),*)->(tracked out:#tt)
                    requires owned.loc()==shared.loc(),Self::#req(owned.fragment(),shared.fragment(),#(#pn),*)
                    ensures out.loc()==owned.loc(),Self::#output(owned.fragment(),shared.fragment(),out.fragment(),#(#pn),*)
                {
                    Self::#frame(owned.fragment(),shared.fragment(),#(#pn),*);
                    let outputs=ISet::new(|new:#ft|Self::#output(owned.fragment(),shared.fragment(),new,#(#pn),*));
                    owned.update_nondeterministic_with_shared(shared,outputs)
                }
                pub proof fn #n(tracked owned:#tt,#(#params),*)->(tracked out:#tt)
                    requires Self::#req(owned.fragment(),<#ft>::unit(),#(#pn),*)
                    ensures out.loc()==owned.loc(),Self::#output(owned.fragment(),<#ft>::unit(),out.fragment(),#(#pn),*)
                {
                    let tracked empty=owned.empty();
                    Self::#shared(owned,&empty,#(#pn),*)
                }
            });
            }
        }
    }
    let (storage_state, storage_trait, token_type, mut broadcast) = if let Some((
        _,
        k,
        v,
        projection,
    )) = &storage
    {
        (
            quote! {pub open spec fn __storage(&self)->IMap<#k,#v>{let s=*self;#projection}},
            quote! {impl #decl ::vstd::resource::tsm_storage::StorageMachine for #pt #where_clause {
                type Key=#k;type Value=#v;
                open spec fn storage(s:#st)->IMap<#k,#v>{s.__storage()}
            }},
            quote! {::vstd::resource::tsm_storage::StorageToken<#pt>},
            quote! {broadcast use {::vstd::iset::group_iset_lemmas,::vstd::imap::group_imap_lemmas,::vstd::map::group_map_lemmas};},
        )
    } else {
        (
            quote! {},
            quote! {},
            quote! {::vstd::resource::tsm::Token<#pt>},
            quote! {broadcast use ::vstd::iset::group_iset_lemmas;},
        )
    };
    if sm.fields.iter().any(|f| matches!(f.stype, ShardableType::Multiset(_))) {
        broadcast = if storage.is_some() {
            quote! {broadcast use {::vstd::iset::group_iset_lemmas,::vstd::imap::group_imap_lemmas,::vstd::map::group_map_lemmas,::vstd::multiset::group_multiset_axioms};}
        } else {
            quote! {broadcast use {::vstd::iset::group_iset_lemmas,::vstd::multiset::group_multiset_axioms};}
        };
    }
    let setters: Vec<_> = sm
        .fields
        .iter()
        .filter(|f| monoids::is_monoid_type(&f.stype))
        .map(|f| {
            let n = &f.name;
            let setter = format_ident!("__tsm_set_{}", n);
            let t = monoids::component_type(&f.stype);
            quote! {pub open spec fn #setter(self,part:#t)->Self{Self{#n:part,..self}}}
        })
        .collect();
    if storage.is_none()
        && sm.fields.iter().any(|f| {
            matches!(
                f.stype,
                ShardableType::Map(..)
                    | ShardableType::IMap(..)
                    | ShardableType::PersistentMap(..)
                    | ShardableType::PersistentIMap(..)
            )
        })
    {
        broadcast = if sm.fields.iter().any(|f| matches!(f.stype, ShardableType::Multiset(_))) {
            quote! {broadcast use {::vstd::iset::group_iset_lemmas,::vstd::imap::group_imap_lemmas,::vstd::map::group_map_lemmas,::vstd::multiset::group_multiset_axioms};}
        } else {
            quote! {broadcast use {::vstd::iset::group_iset_lemmas,::vstd::imap::group_imap_lemmas,::vstd::map::group_map_lemmas};}
        };
    }
    if sm
        .fields
        .iter()
        .any(|f| matches!(f.stype, ShardableType::Set(_) | ShardableType::PersistentSet(_)))
    {
        let mut groups =
            vec![quote! {::vstd::iset::group_iset_lemmas}, quote! {::vstd::set::group_set_lemmas}];
        if storage.is_some()
            || sm.fields.iter().any(|f| {
                matches!(
                    f.stype,
                    ShardableType::Map(..)
                        | ShardableType::IMap(..)
                        | ShardableType::PersistentMap(..)
                        | ShardableType::PersistentIMap(..)
                )
            })
        {
            groups.push(quote! {::vstd::imap::group_imap_lemmas});
            groups.push(quote! {::vstd::map::group_map_lemmas});
        }
        if sm.fields.iter().any(|f| matches!(f.stype, ShardableType::Multiset(_))) {
            groups.push(quote! {::vstd::multiset::group_multiset_axioms});
        }
        broadcast = quote! {broadcast use {#(#groups),*};};
    }
    let observation_inline = if local_ready.is_empty() {
        quote! {}
    } else {
        quote! {#[verifier::inline]}
    };
    let observation_result = if local_ready.is_empty() {
        quote! {}
    } else {
        let Some((_, key, val, _)) = &storage else {
            return Err(Error::new(
                name.span(),
                "local-ready currently requires a physical storage protocol",
            ));
        };
        quote! {
            #(#datatype_attrs)*
            pub tracked struct TransitionObservation #decl #where_clause {
                pub tracked token:#tt,
                pub tracked withdrawn:IMap<#key,#val>,
                pub ghost before:#st,
                pub ghost after:#st,
                pub ghost frame:#ft,
            }
        }
    };
    Ok(quote! {
        pub mod #name {use super::*;::vstd::prelude::verus!{
            use ::vstd::iset::ISet;
            use ::vstd::resource::algebra::ResourceAlgebra;use ::vstd::resource::pcm::PCM;
            use ::vstd::resource::exclusive::ExclusiveRA;use ::vstd::resource::agree::AgreementRA;
            use ::vstd::resource::tsm::Machine;
            use ::vstd::resource::tsm_storage::StorageMachine;
            #broadcast
            #carrier_declarations
            #(#datatype_attrs)*
            pub struct State #decl #where_clause {#marker #(#sf),*}
            impl #decl #st #where_clause {
                pub open spec fn invariant(&self)->bool {true #(&&self.#invnames())*}
                #storage_state #(#invs)* #(#relations)* #(#lemmas)* #(#normal)*
            }
            #(#datatype_attrs)*
            pub struct Fragment #decl #where_clause {#marker #(#ff),*}
            impl #decl #ft #where_clause {#field_specs #(#setters)*}
            impl #decl ResourceAlgebra for #ft #where_clause {
                open spec fn valid(self)->bool {true #(&&self.#names.valid())*}
                open spec fn op(a:Self,b:Self)->Self {#fe{#marker_value #(#names:<#ftypes>::op(a.#names,b.#names)),*}}
                proof fn associative(a:Self,b:Self,c:Self){#(<#ftypes>::associative(a.#names,b.#names,c.#names);)*}
                proof fn commutative(a:Self,b:Self){#(<#ftypes>::commutative(a.#names,b.#names);)*}
                proof fn valid_op(a:Self,b:Self){#(<#ftypes>::valid_op(a.#names,b.#names);)*}
            }
            impl #decl PCM for #ft #where_clause {
                open spec fn unit()->Self {#fe{#marker_value #(#names:<#ftypes>::unit()),*}}
                proof fn op_unit(self){#(self.#names.op_unit();)*}
                proof fn unit_valid(){#(<#ftypes>::unit_valid();)*}
            }
            #(#datatype_attrs)*
            pub struct Protocol #decl #where_clause {#marker}
            impl #decl Machine for #pt #where_clause {
                type Fragment=#ft;type State=#st;
                open spec fn invariant(s:#st)->bool{s.invariant()}
                open spec fn embed(s:#st)->#ft {#fe{#marker_value #(#embeds),*}}
            }
            #storage_trait
            #(#labels)*
            pub type Token #decl #where_clause=#token_type;
            #observation_result
            impl #decl #pt #where_clause {
                #observation_inline
                pub open spec fn __observed(f:#ft)->#st {#se{#marker_value #(#observations),*}}
                #field_takes #(#ops)*
            }
        }}
    })
}

#[allow(clippy::too_many_arguments)]
fn storage_operations(
    n: &Ident,
    strong: &Ident,
    enabled: &Ident,
    run: &Ident,
    req: &Ident,
    output: &Ident,
    frame: &Ident,
    owned_post: &Ident,
    shared: &Ident,
    deposited: &Ident,
    owners: &Ident,
    st: &TokenStream,
    se: &TokenStream,
    ft: &TokenStream,
    fe: &TokenStream,
    pt: &TokenStream,
    tt: &TokenStream,
    marker_value: &Option<TokenStream>,
    pn: &Vec<&Ident>,
    params: &Vec<TokenStream>,
    owned_req: &Vec<TokenStream>,
    observed_req: &Vec<TokenStream>,
    newfields: &Vec<TokenStream>,
    effect_calls: &Vec<TokenStream>,
    key: &Type,
    val: &Type,
    withdraws: bool,
    deposits: bool,
    paired: bool,
) -> TokenStream {
    let map = quote! {IMap<#key,#val>};
    let mut pair_name = "__tsm_storage_exchange_pair".to_string();
    while pn.iter().any(|name| name.to_string() == pair_name) {
        pair_name.push('_');
    }
    let pair = Ident::new(&pair_name, proc_macro2::Span::mixed_site());
    let witness = format_ident!("{}_witness", n);
    let output_at = format_ident!("__tsm_{}_output_at", n);
    let outputs =
        quote! {ISet::new(|#pair:(#ft,#map)|Self::#output(owned,h,#pair.0,deposit,#pair.1,#(#pn),*))};
    let lifted = quote! {#outputs.map(|#pair:(#ft,#map)|(<#ft>::op(#pair.0,h),#pair.1))};
    let ret = if withdraws {
        quote! {tracked out:(#tt,#map)}
    } else {
        quote! {tracked out:#tt}
    };
    let out_token = if withdraws {
        quote! {out.0}
    } else {
        quote! {out}
    };
    let deposit_param = if deposits {
        quote! {tracked deposit:#map,}
    } else {
        quote! {}
    };
    let deposit_spec = if deposits {
        quote! {deposit}
    } else {
        quote! {IMap::empty()}
    };
    let deposit_init = if deposits {
        quote! {}
    } else {
        quote! {let tracked deposit:#map=IMap::tracked_empty();}
    };
    let return_ens = if withdraws {
        quote! {Self::#output(owned.fragment(),shared.fragment(),out.0.fragment(),#deposit_spec,out.1,#(#pn),*)}
    } else {
        quote! {Self::#output(owned.fragment(),shared.fragment(),out.fragment(),#deposit_spec,IMap::empty(),#(#pn),*)}
    };
    let plain_ens = if withdraws {
        quote! {Self::#output(owned.fragment(),<#ft>::unit(),out.0.fragment(),#deposit_spec,out.1,#(#pn),*)}
    } else {
        quote! {Self::#output(owned.fragment(),<#ft>::unit(),out.fragment(),#deposit_spec,IMap::empty(),#(#pn),*)}
    };
    let return_value = if withdraws {
        quote! {(out,withdrawn)}
    } else {
        quote! {
            assert(::vstd::prelude::ext_equal(withdrawn,IMap::empty()));
            out
        }
    };
    // A step that withdraws nothing and has one storage operation per path:
    // its outputs state `withdrawn == empty` only, and the frame leaves the
    // storage bookkeeping to `exchange_point_intro_monotone`.
    let monotone = !withdraws && !paired;
    let withdrawn_value = if monotone {
        quote! {}
    } else {
        quote! {&&withdrawn==pre.__storage().union_prefer_right(deposit).remove_keys(post.__storage().dom())}
    };
    let withdrawn_result = if monotone {
        quote! {}
    } else {
        quote! {,withdrawn==result.0.__storage().union_prefer_right(deposit).remove_keys(result.1.__storage().dom())}
    };
    let withdrawal_shape = if withdraws {
        quote! {true}
    } else {
        quote! {withdrawn==IMap::empty()}
    };
    let withdrawal_proof = if withdraws {
        quote! {}
    } else if paired {
        quote! {
            assert(Self::storage(pre).submap_of(Self::storage(post)));
            assert(::vstd::prelude::ext_equal(withdrawn,IMap::empty())) by {
                assert forall|key| !withdrawn.contains_key(key) by {};
            }
        }
    } else {
        quote! {::vstd::resource::tsm_storage::storage_withdrawn_none(Self::storage(pre),Self::storage(post),deposit);}
    };
    let output_storage = if paired {
        quote! {
            deposit==#se::#deposited(pre,#(#pn),*)
                &&pre.__storage().dom().disjoint(deposit.dom())
                &&post.__storage().submap_of(pre.__storage().union_prefer_right(deposit))
        }
    } else {
        quote! {deposit==post.__storage().remove_keys(pre.__storage().dom())}
    };
    let witness_storage = if paired {
        quote! {
            deposit==#se::#deposited(result.0,#(#pn),*),
            result.0.__storage().dom().disjoint(deposit.dom()),
            result.1.__storage().submap_of(result.0.__storage().union_prefer_right(deposit))
        }
    } else {
        quote! {deposit==result.1.__storage().remove_keys(result.0.__storage().dom())}
    };
    let transfer_proof = if paired {
        quote! {
            assert(deposit==#se::#deposited(pre,#(#pn),*));
            assert(Self::storage(pre).dom().disjoint(deposit.dom()));
            assert(Self::storage(post).submap_of(Self::storage(pre).union_prefer_right(deposit)));
        }
    } else {
        quote! {}
    };
    let frame_withdrawn = if monotone {
        quote! {assert(Self::#output_at(owned,h,new,deposit,IMap::empty(),#(#pn,)* z,pre,post));}
    } else {
        quote! {
            let withdrawn=Self::storage(pre).union_prefer_right(deposit).remove_keys(Self::storage(post).dom());
            #withdrawal_proof
            assert(Self::#output_at(owned,h,new,deposit,withdrawn,#(#pn,)* z,pre,post));
        }
    };
    // The exchange's witnesses for one frame (`exchange_point`).
    let point_intro = if paired {
        quote! {::vstd::resource::tsm_storage::exchange_point_intro::<#pt>(owned,h,z,pre,deposit,outputs,new,post);}
    } else if monotone {
        quote! {::vstd::resource::tsm_storage::exchange_point_intro_monotone::<#pt>(owned,h,z,pre,deposit,outputs,new,post);}
    } else {
        quote! {::vstd::resource::tsm_storage::exchange_point_intro_delta::<#pt>(owned,h,z,pre,deposit,outputs,new,post);}
    };
    quote! {
            pub open spec fn #owned_post(owned:#ft,pre:#st,post:#st,#(#params),*)->#ft {#fe{#marker_value #(#newfields),*}}
            pub open spec fn #req(owned:#ft,h:#ft,deposit:#map,#(#params),*)->bool {
                true #(&& #owned_req)* #(&& #observed_req)* &&
                forall|z:#ft,pre:#st|::vstd::prelude::imply(
                    #[trigger] ::vstd::resource::tsm::completes_with::<#pt>(<#ft>::op(owned,h),z,pre),
                    #se::#enabled(pre,#(#pn),*)&&deposit==#se::#deposited(pre,#(#pn),*)&&#se::#owners(pre,owned,h,#(#pn),*))
            }
            pub open spec fn #output_at(owned:#ft,h:#ft,new:#ft,deposit:#map,withdrawn:#map,#(#params,)* z:#ft,pre:#st,post:#st)->bool {
                pre.invariant()&&<#ft>::op(<#ft>::op(owned,h),z)==Self::embed(pre)
                    &&#se::#strong(pre,post,#(#pn),*)&&post.invariant()&&new==Self::#owned_post(owned,pre,post,#(#pn),*)
                    &&<#ft>::op(<#ft>::op(new,h),z)==Self::embed(post)
                    &&(#output_storage)
                    #withdrawn_value
            }
            pub open spec fn #output(owned:#ft,h:#ft,new:#ft,deposit:#map,withdrawn:#map,#(#params),*)->bool {
                #withdrawal_shape && exists|z:#ft,pre:#st,post:#st| #[trigger] Self::#output_at(owned,h,new,deposit,withdrawn,#(#pn,)* z,pre,post)
            }
            pub proof fn #witness(owned:#ft,h:#ft,new:#ft,deposit:#map,withdrawn:#map,#(#params),*)
                ->(result:(#st,#st,#ft))
                requires Self::#output(owned,h,new,deposit,withdrawn,#(#pn),*)
                ensures Self::#output_at(owned,h,new,deposit,withdrawn,#(#pn,)* result.2,result.0,result.1)
            {
                let (z,pre,post)=choose|z:#ft,pre:#st,post:#st| #[trigger] Self::#output_at(owned,h,new,deposit,withdrawn,#(#pn,)* z,pre,post);
                (pre,post,z)
            }
            pub proof fn #frame(owned:#ft,h:#ft,deposit:#map,#(#params),*)
                requires Self::#req(owned,h,deposit,#(#pn),*)
                ensures ::vstd::resource::tsm_storage::frame_exchange_nondeterministic::<#pt>(<#ft>::op(owned,h),deposit,#lifted)
            {
                let outputs=#outputs;
                assert forall|z:#ft,pre:#st|Self::invariant(pre)&&<#ft>::op(<#ft>::op(owned,h),z)==Self::embed(pre)
                    implies ::vstd::resource::tsm_storage::exchange_point::<#pt>(owned,h,z,pre,deposit,outputs) by {
                        assert(::vstd::resource::tsm::completes_with::<#pt>(<#ft>::op(owned,h),z,pre));
                        let post=#se::#run(pre,#(#pn),*);
                        #(#effect_calls)*
                        let new=Self::#owned_post(owned,pre,post,#(#pn),*);
                        <#ft>::associative(new,h,z);
                        #transfer_proof
                        #frame_withdrawn
                        #point_intro
                    }
                ::vstd::resource::tsm_storage::frame_exchange_by_points::<#pt>(owned,h,deposit,outputs);
            }
    pub proof fn #shared(tracked owned:#tt,tracked shared:&#tt,#deposit_param #(#params),*)->(#ret)
                requires owned.loc()==shared.loc(),Self::#req(owned.fragment(),shared.fragment(),#deposit_spec,#(#pn),*)
                ensures #out_token.loc()==owned.loc(),#return_ens
            {
                #deposit_init
                Self::#frame(owned.fragment(),shared.fragment(),deposit,#(#pn),*);
                let outputs=ISet::new(|#pair:(#ft,#map)|Self::#output(owned.fragment(),shared.fragment(),#pair.0,deposit,#pair.1,#(#pn),*));
                let tracked (out,withdrawn)=owned.exchange_nondeterministic_with_shared(shared,deposit,outputs);
                #return_value
            }
            pub proof fn #n(tracked owned:#tt,#deposit_param #(#params),*)->(#ret)
                requires Self::#req(owned.fragment(),<#ft>::unit(),#deposit_spec,#(#pn),*)
                ensures #out_token.loc()==owned.loc(),#plain_ens
            {
                #deposit_init
                <#ft>::op_unit(owned.fragment());
                Self::#frame(owned.fragment(),<#ft>::unit(),deposit,#(#pn),*);
                let outputs=ISet::new(|#pair:(#ft,#map)|Self::#output(owned.fragment(),<#ft>::unit(),#pair.0,deposit,#pair.1,#(#pn),*));
                ::vstd::resource::tsm_storage::storage_outputs_unit::<#pt>(outputs);
                let tracked (out,withdrawn)=owned.exchange_nondeterministic(deposit,outputs);
                #return_value
            }
        }
}
