//! The monoid fields' components, canonical operands and fragment updates, and the
//! frontend restrictions of the checked backend on monoid statements (`transition_effects`).
use crate::ast::*;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use verus_syn::{Error, Ident, Type};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum EffectOp {
    Add,
    Remove,
}
/// A transition's composed `add` or `remove` effect on one monoid field (with `replacement`,
/// a remove-then-add pair), defined by the spec fn `function`.
pub struct Effect {
    pub field: Field,
    pub op: EffectOp,
    pub function: Ident,
    pub expression: TokenStream,
    pub replacement: bool,
}

/// Whether fields of this kind are monoid fields (with a resource component).
pub fn is_monoid_type(s: &ShardableType) -> bool {
    matches!(
        s,
        ShardableType::Count
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
}
/// The fragment component type of a monoid field.
pub fn component_type(s: &ShardableType) -> TokenStream {
    match s {
        ShardableType::PersistentBool | ShardableType::PersistentCount => {
            quote! {::vstd::resource::tsm_persistent::PersistentCountRA}
        }
        ShardableType::Count | ShardableType::Bool => quote! {::vstd::resource::tsm::CountRA},
        ShardableType::Multiset(t) => {
            quote! {::vstd::resource::tsm_finite_multiset::FiniteMultisetRA<#t>}
        }
        ShardableType::Set(k) | ShardableType::ISet(k) => {
            quote! {::vstd::resource::tsm_collections::SetFragment<#k>}
        }
        ShardableType::PersistentSet(k) | ShardableType::PersistentISet(k) => {
            quote! {::vstd::resource::tsm_collections::PersistentSetFragment<#k>}
        }
        ShardableType::Option(t) => quote! {::vstd::resource::tsm_collections::OptionFragment<#t>},
        ShardableType::PersistentOption(t) => {
            quote! {::vstd::resource::tsm_collections::PersistentOptionFragment<#t>}
        }
        ShardableType::Map(k, v) | ShardableType::IMap(k, v) => {
            quote! {::vstd::resource::tsm_collections::MapFragment<#k,#v>}
        }
        ShardableType::PersistentMap(k, v) | ShardableType::PersistentIMap(k, v) => {
            quote! {::vstd::resource::tsm_collections::PersistentMapFragment<#k,#v>}
        }
        _ => unreachable!(),
    }
}
/// The fragment component owning exactly the field value `value`.
pub fn embed(s: &ShardableType, value: TokenStream) -> TokenStream {
    match s {
        ShardableType::Count => quote! {::vstd::resource::tsm::CountRA{count:#value}},
        ShardableType::Bool => quote! {::vstd::resource::tsm_bool::bool_frag(#value)},
        ShardableType::PersistentBool => {
            quote! {::vstd::resource::tsm_persistent::persistent_bool_frag(#value)}
        }
        ShardableType::PersistentCount => {
            quote! {::vstd::resource::tsm_persistent::PersistentCountRA{count:#value}}
        }
        ShardableType::Multiset(_) => {
            quote! {::vstd::resource::tsm_finite_multiset::finite_multiset_frag(#value)}
        }
        ShardableType::Set(_) | ShardableType::ISet(_) => {
            let value = set_view(s, value);
            quote! {::vstd::resource::tsm_collections::set_frag(#value)}
        }
        ShardableType::PersistentSet(_) | ShardableType::PersistentISet(_) => {
            let value = set_view(s, value);
            quote! {::vstd::resource::tsm_collections::persistent_set_frag(#value)}
        }
        ShardableType::Option(_) => quote! {::vstd::resource::tsm_collections::option_frag(#value)},
        ShardableType::PersistentOption(_) => {
            quote! {::vstd::resource::tsm_collections::persistent_option_frag(#value)}
        }
        ShardableType::Map(..) | ShardableType::IMap(..) => {
            let value = map_view(s, value);
            quote! {::vstd::resource::tsm_collections::map_frag(#value)}
        }
        ShardableType::PersistentMap(..) | ShardableType::PersistentIMap(..) => {
            let value = map_view(s, value);
            quote! {::vstd::resource::tsm_collections::persistent_map_frag(#value)}
        }
        _ => unreachable!(),
    }
}
/// The type of a monoid field's operands.
pub fn operand_type(s: &ShardableType) -> Type {
    match s {
        ShardableType::Count | ShardableType::PersistentCount => verus_syn::parse_quote! {nat},
        ShardableType::Bool | ShardableType::PersistentBool => verus_syn::parse_quote! {bool},
        ShardableType::Multiset(t) => verus_syn::parse_quote! {::vstd::multiset::Multiset<#t>},
        ShardableType::Option(t) | ShardableType::PersistentOption(t) => {
            verus_syn::parse_quote! {Option<#t>}
        }
        ShardableType::Set(k)
        | ShardableType::ISet(k)
        | ShardableType::PersistentSet(k)
        | ShardableType::PersistentISet(k) => verus_syn::parse_quote! {::vstd::iset::ISet<#k>},
        ShardableType::Map(k, v)
        | ShardableType::IMap(k, v)
        | ShardableType::PersistentMap(k, v)
        | ShardableType::PersistentIMap(k, v) => {
            verus_syn::parse_quote! {::vstd::imap::IMap<#k,#v>}
        }
        _ => unreachable!(),
    }
}
/// The canonical operand of a monoid operation on `f`.
pub(crate) fn operand(
    f: &Field,
    op: &SpecialOp,
    span: proc_macro2::Span,
) -> Result<TokenStream, Error> {
    match (&f.stype, &op.elt) {
        (
            s @ (ShardableType::Set(_)
            | ShardableType::ISet(_)
            | ShardableType::PersistentSet(_)
            | ShardableType::PersistentISet(_)),
            MonoidElt::General(value),
        ) => Ok(set_view(s, quote! {#value})),
        (
            ShardableType::Set(_)
            | ShardableType::ISet(_)
            | ShardableType::PersistentSet(_)
            | ShardableType::PersistentISet(_),
            MonoidElt::SingletonSet(value),
        ) => Ok(quote! {::vstd::iset::ISet::empty().insert(#value)}),
        (
            ShardableType::Count
            | ShardableType::PersistentCount
            | ShardableType::Bool
            | ShardableType::PersistentBool,
            MonoidElt::General(e),
        ) => Ok(quote! {#e}),
        (ShardableType::Bool | ShardableType::PersistentBool, MonoidElt::True) => Ok(quote! {true}),
        (ShardableType::Multiset(_), MonoidElt::SingletonMultiset(e)) => {
            Ok(quote! {::vstd::multiset::Multiset::empty().insert(#e)})
        }
        (ShardableType::Multiset(_), MonoidElt::General(e)) => Ok(quote! {#e}),
        (ShardableType::Option(_) | ShardableType::PersistentOption(_), MonoidElt::General(e)) => {
            Ok(quote! {#e})
        }
        (
            ShardableType::Option(_) | ShardableType::PersistentOption(_),
            MonoidElt::OptionSome(Some(e)),
        ) => Ok(quote! {Some(#e)}),
        (
            ShardableType::Option(_) | ShardableType::PersistentOption(_),
            MonoidElt::OptionSome(None),
        ) => {
            let n = &f.name;
            Ok(quote! {Some(pre.#n->Some_0)})
        }
        (
            ShardableType::Map(..)
            | ShardableType::IMap(..)
            | ShardableType::PersistentMap(..)
            | ShardableType::PersistentIMap(..),
            MonoidElt::SingletonKV(k, Some(v)),
        ) => Ok(quote! {::vstd::imap::IMap::empty().insert(#k,#v)}),
        (
            ShardableType::Map(..)
            | ShardableType::IMap(..)
            | ShardableType::PersistentMap(..)
            | ShardableType::PersistentIMap(..),
            MonoidElt::SingletonKV(k, None),
        ) => {
            let n = &f.name;
            Ok(quote! {::vstd::imap::IMap::empty().insert(#k,pre.#n[#k])})
        }
        (
            stype @ (ShardableType::Map(..)
            | ShardableType::IMap(..)
            | ShardableType::PersistentMap(..)
            | ShardableType::PersistentIMap(..)),
            MonoidElt::General(value),
        ) => Ok(map_view(stype, quote! {#value})),
        _ => Err(Error::new(span, "this verified monoid operation has an unsupported operand")),
    }
}

/// `value` as an `ISet` (finite sets through `to_iset`).
pub(crate) fn set_view(s: &ShardableType, value: TokenStream) -> TokenStream {
    match s {
        ShardableType::Set(_) | ShardableType::PersistentSet(_) => quote! {(#value).to_iset()},
        ShardableType::ISet(_) | ShardableType::PersistentISet(_) => value,
        _ => unreachable!(),
    }
}

/// `value` as an `IMap` (finite maps through `to_imap`).
pub(crate) fn map_view(s: &ShardableType, value: TokenStream) -> TokenStream {
    match s {
        ShardableType::Map(..) | ShardableType::PersistentMap(..) => quote! {(#value).to_imap()},
        ShardableType::IMap(..) | ShardableType::PersistentIMap(..) => value,
        _ => unreachable!(),
    }
}

// Match the mathematical executor's handling of refutable element patterns.
// These are ordinary ghost expressions, not calls to the trusted token backend.
pub(crate) fn bind_pattern(
    p: &verus_syn::Pat,
    value: TokenStream,
    body: TokenStream,
) -> TokenStream {
    let value = verus_syn::Expr::Verbatim(value);
    match crate::concurrency_tokens::assign_pat_or_arbitrary(p, &value) {
        Some((p, value)) => quote! {{let #p=#value;#body}},
        None => body,
    }
}
/// Whether `op` is a modifier of kind `kind`.
fn is_of_kind(op: &SpecialOp, kind: EffectOp) -> bool {
    match kind {
        EffectOp::Add => op.is_add(),
        EffectOp::Remove => op.is_remove(),
    }
}
fn has_effect(s: &TransitionStmt, target: &Ident, kind: EffectOp) -> bool {
    match s {
        TransitionStmt::Block(_, xs) => xs.iter().any(|s| has_effect(s, target, kind)),
        TransitionStmt::Split(_, k, xs) => {
            matches!(&**k,SplitKind::Special(n,op,_,_) if n==target&&is_of_kind(op,kind))
                || xs.iter().any(|s| has_effect(s, target, kind))
        }
        _ => false,
    }
}
/// Whether `tokens` mention a name that `pattern` binds.
fn mentions_bound(pattern: &verus_syn::Pat, tokens: &TokenStream) -> bool {
    fn mentions(tokens: TokenStream, names: &[Ident]) -> bool {
        tokens.into_iter().any(|token| match token {
            proc_macro2::TokenTree::Ident(name) => names.contains(&name),
            proc_macro2::TokenTree::Group(group) => mentions(group.stream(), names),
            _ => false,
        })
    }
    mentions(tokens.clone(), &crate::ident_visitor::pattern_get_bound_idents(pattern))
}

/// The composed operand (an `Option`) of the `kind` operations on `f` in `s`; `None` on
/// paths without one.
fn effect_expression(s: &TransitionStmt, f: &Field, kind: EffectOp) -> Result<TokenStream, Error> {
    if !has_effect(s, &f.name, kind) {
        return Ok(quote! {None});
    }
    Ok(match s {
        TransitionStmt::Block(_, xs) => {
            // Sequential modifiers of one kind compose into one operand.
            let mut parts = vec![];
            for x in xs.iter().filter(|s| has_effect(s, &f.name, kind)) {
                parts.push(effect_expression(x, f, kind)?);
            }
            let first = parts.remove(0);
            parts.into_iter().fold(first, |a, b| sequential(f, a, b))
        }
        TransitionStmt::Split(span, k, xs) => match &**k {
            SplitKind::Let(p, t, _, e) => {
                let t = t.as_ref().map(|t| quote! {:#t});
                let child = effect_expression(&xs[0], f, kind)?;
                quote! {{let #p #t=#e;#child}}
            }
            SplitKind::If(e) => {
                let a = effect_expression(&xs[0], f, kind)?;
                let b = xs
                    .get(1)
                    .map(|s| effect_expression(s, f, kind))
                    .transpose()?
                    .unwrap_or(quote! {None});
                quote! {if #e{#a}else{#b}}
            }
            SplitKind::Match(e, arms) => {
                let cases: Vec<_> = arms
                    .iter()
                    .zip(xs)
                    .map(|(arm, s)| {
                        let p = &arm.pat;
                        let guard = arm.guard.as_ref().map(|(tok, e)| quote! {#tok #e});
                        let value = effect_expression(s, f, kind)?;
                        Ok(quote! {#p #guard=>{#value}})
                    })
                    .collect::<Result<_, Error>>()?;
                quote! {match #e{#(#cases),*}}
            }
            SplitKind::Special(n, op, _, pattern) if n == &f.name && is_of_kind(op, kind) => {
                let value = operand(f, op, *span)?;
                match xs.first() {
                    Some(rest) if has_effect(rest, &f.name, kind) => {
                        let rest = effect_expression(rest, f, kind)?;
                        // The later operands may use this statement's binding
                        // (e.g. in a condition), bound as below.
                        let rest = match (pattern, &op.elt) {
                            (
                                Some(p),
                                MonoidElt::OptionSome(None) | MonoidElt::SingletonKV(_, None),
                            ) if mentions_bound(p, &rest) => {
                                let bound = match &op.elt {
                                    MonoidElt::SingletonKV(k, None) => quote! {pre.#n[#k]},
                                    _ => quote! {pre.#n->Some_0},
                                };
                                bind_pattern(p, bound, rest)
                            }
                            _ => rest,
                        };
                        sequential(f, quote! {Some(#value)}, rest)
                    }
                    _ => quote! {Some(#value)},
                }
            }
            SplitKind::Special(n, op, _, Some(p)) => {
                let value = match &op.elt {
                    MonoidElt::OptionSome(None) => quote! {pre.#n->Some_0},
                    MonoidElt::SingletonKV(k, None) => quote! {pre.#n[#k]},
                    _ => return Err(Error::new(*span, "unsupported binding before monoid effect")),
                };
                let child = effect_expression(&xs[0], f, kind)?;
                bind_pattern(p, value, child)
            }
            _ => effect_expression(&xs[0], f, kind)?,
        },
        _ => quote! {None},
    })
}

// Compose two optional operands of the same modifier kind into one operand
// whose single application has the effect of applying both in order. For
// exclusive kinds the transition's requirements and safety conditions make
// repeated operands disjoint (e.g. key-disjoint map removals, at most one
// removed `true`), so the composition is the monoid operation. Persistent
// additions compose by the idempotent join (max, union, first defined value).
fn sequential(f: &Field, a: TokenStream, b: TokenStream) -> TokenStream {
    // Hygienic binders: operands may mention parameters of any name.
    let x = format_ident!("__tsm_first", span = proc_macro2::Span::mixed_site());
    let y = format_ident!("__tsm_second", span = proc_macro2::Span::mixed_site());
    let combine = match f.stype {
        ShardableType::Multiset(_) => quote! {#x.add(#y)},
        ShardableType::Count => quote! {(#x + #y) as nat},
        ShardableType::PersistentCount => {
            quote! {::vstd::resource::tsm_persistent::count_max(#x, #y)}
        }
        ShardableType::Bool | ShardableType::PersistentBool => quote! {(#x || #y)},
        ShardableType::Set(_)
        | ShardableType::ISet(_)
        | ShardableType::PersistentSet(_)
        | ShardableType::PersistentISet(_) => quote! {#x.union(#y)},
        ShardableType::Option(_) | ShardableType::PersistentOption(_) => {
            quote! {::vstd::resource::tsm_collections::option_union(#x, #y)}
        }
        _ => quote! {#x.union_prefer_right(#y)},
    };
    // Integer literal operands need their type before they are combined.
    let (a, b) = if matches!(f.stype, ShardableType::Count | ShardableType::PersistentCount) {
        (quote! {{let #x: Option<nat> = #a; #x}}, quote! {{let #y: Option<nat> = #b; #y}})
    } else {
        (a, b)
    };
    // Nested rather than tuple matches: see the vstd resource-algebra ops.
    quote! {match #a {
        Some(#x) => match #b { Some(#y) => Some(#combine), None => Some(#x) },
        None => #b,
    }}
}

/// Adds the modifier kinds applied to each monoid field to `kinds`; rejects unsupported
/// operations and element bindings.
fn collect_modifiers(
    s: &TransitionStmt,
    fields: &HashMap<String, Field>,
    kinds: &mut HashMap<String, HashSet<EffectOp>>,
) -> Result<(), Error> {
    match s {
        TransitionStmt::Block(_, children) => {
            for child in children {
                collect_modifiers(child, fields, kinds)?;
            }
        }
        TransitionStmt::Split(span, kind, children) => {
            if let SplitKind::Special(n, op, _, pat) = &**kind {
                let f = &fields[&n.to_string()];
                if is_monoid_type(&f.stype) {
                    operand(f, op, *span)?;
                    if pat.is_some()
                        && !matches!(
                            f.stype,
                            ShardableType::Option(_)
                                | ShardableType::PersistentOption(_)
                                | ShardableType::Map(..)
                                | ShardableType::IMap(..)
                                | ShardableType::PersistentMap(..)
                                | ShardableType::PersistentIMap(..)
                        )
                    {
                        return Err(Error::new(
                            *span,
                            "verified monoid ownership operations do not support element bindings",
                        ));
                    }
                    let modify = match op.stmt {
                        MonoidStmtType::Add(false) => Some(EffectOp::Add),
                        MonoidStmtType::Add(true) if f.stype.is_persistent() => Some(EffectOp::Add),
                        MonoidStmtType::Remove if !f.stype.is_persistent() => {
                            Some(EffectOp::Remove)
                        }
                        MonoidStmtType::Have => None,
                        _ => {
                            return Err(Error::new(*span, "unsupported verified monoid operation"));
                        }
                    };
                    if let Some(modify) = modify {
                        kinds.entry(n.to_string()).or_default().insert(modify);
                    }
                }
            }
            for child in children {
                collect_modifiers(child, fields, kinds)?;
            }
        }
        _ => {}
    }
    Ok(())
}

/// Rejects a removal from `target` after an addition to it on some path; returns the
/// stages reached (see `single_replacement`).
fn check_replacement_order(
    s: &TransitionStmt,
    target: &Ident,
    mut stages: HashSet<u8>,
) -> Result<HashSet<u8>, Error> {
    match s {
        TransitionStmt::Block(_, children) => {
            for child in children {
                stages = check_replacement_order(child, target, stages)?;
            }
        }
        TransitionStmt::Split(span, kind, children) => {
            if let SplitKind::Special(n, op, _, _) = &**kind {
                if n == target && op.is_modifier() {
                    // Removals may follow removals; additions follow removals or additions.
                    let after = if op.is_remove() { 1 } else { 2 };
                    if op.is_remove() && stages.contains(&2) {
                        return Err(Error::new(
                            *span,
                            "verified monoid updates of one field must go in the order remove, have, add on each path",
                        ));
                    }
                    stages = HashSet::from([after]);
                }
            }
            match &**kind {
                SplitKind::If(_) | SplitKind::Match(..) => {
                    let mut outcomes = HashSet::new();
                    if matches!(&**kind, SplitKind::If(_)) && children.len() == 1 {
                        outcomes.extend(stages.clone());
                    }
                    for child in children {
                        outcomes.extend(check_replacement_order(child, target, stages.clone())?);
                    }
                    stages = outcomes;
                }
                _ => {
                    for child in children {
                        stages = check_replacement_order(child, target, stages)?;
                    }
                }
            }
        }
        _ => {}
    }
    Ok(stages)
}

// Whether every modifying path removes exactly once and then adds exactly once
// (stage 0: unmodified, 1: removed, 2: removed then added).
fn single_replacement(
    s: &TransitionStmt,
    target: &Ident,
    mut stages: HashSet<u8>,
) -> Option<HashSet<u8>> {
    match s {
        TransitionStmt::Block(_, children) => {
            for child in children {
                stages = single_replacement(child, target, stages)?;
            }
        }
        TransitionStmt::Split(_, kind, children) => {
            if let SplitKind::Special(n, op, _, _) = &**kind {
                if n == target && op.is_modifier() {
                    let (before, after) = if op.is_remove() { (0, 1) } else { (1, 2) };
                    if stages.iter().any(|stage| *stage != before) {
                        return None;
                    }
                    stages = HashSet::from([after]);
                }
            }
            match &**kind {
                SplitKind::If(_) | SplitKind::Match(..) => {
                    let mut outcomes = HashSet::new();
                    if matches!(&**kind, SplitKind::If(_)) && children.len() == 1 {
                        outcomes.extend(stages.clone());
                    }
                    for child in children {
                        outcomes.extend(single_replacement(child, target, stages.clone())?);
                    }
                    stages = outcomes;
                }
                _ => {
                    for child in children {
                        stages = single_replacement(child, target, stages)?;
                    }
                }
            }
        }
        _ => {}
    }
    Some(stages)
}

// Effect selectors reconstruct element bindings from the initial mathematical
// state. A value still present after earlier removals equals its initial
// value, so only an earlier addition to the source field can change it.
fn check_binding_order(
    statement: &TransitionStmt,
    fields: &HashMap<String, Field>,
    modified: &mut HashSet<String>,
) -> Result<(), Error> {
    match statement {
        TransitionStmt::Block(_, children) => {
            for child in children {
                check_binding_order(child, fields, modified)?;
            }
        }
        TransitionStmt::Split(span, kind, children) => {
            if let SplitKind::Special(name, operation, _, pattern) = &**kind {
                if is_monoid_type(&fields[&name.to_string()].stype) {
                    if pattern.is_some()
                        && matches!(operation.stmt, MonoidStmtType::Have)
                        && modified.contains(&name.to_string())
                    {
                        return Err(Error::new(
                            *span,
                            "verified effect bindings must precede additions to their source field",
                        ));
                    }
                    if operation.is_add() {
                        modified.insert(name.to_string());
                    }
                }
            }
            if matches!(&**kind, SplitKind::If(_) | SplitKind::Match(..)) {
                let initial = modified.clone();
                for child in children {
                    let mut branch = initial.clone();
                    check_binding_order(child, fields, &mut branch)?;
                    modified.extend(branch);
                }
            } else {
                for child in children {
                    check_binding_order(child, fields, modified)?;
                }
            }
        }
        _ => {}
    }
    Ok(())
}

/// The effects of `tr` on its monoid fields, sorted by field name. It also rejects the
/// statement forms the checked backend restricts: unsupported operands and bindings, a
/// removal from a field after an addition to it, a binding after an addition to its field.
pub fn transition_effects(
    tr: &Transition,
    fields: &HashMap<String, Field>,
) -> Result<Vec<Effect>, Error> {
    check_binding_order(&tr.body, fields, &mut HashSet::new())?;
    let mut kinds = HashMap::new();
    collect_modifiers(&tr.body, fields, &mut kinds)?;
    let mut names: Vec<_> = kinds.keys().cloned().collect();
    names.sort();
    names.into_iter().map(|n|{
        let field=fields[&n].clone();let operations=&kinds[&n];let replacement=operations.len()==2;
        let op=if replacement{EffectOp::Add}else{*operations.iter().next().unwrap()};
        let expression=if replacement{
            if !replaceable(&field.stype){
                return Err(Error::new(*tr.body.get_span(),"verified replacement supports exclusive monoid fields only"));
            }
            check_replacement_order(&tr.body,&field.name,HashSet::from([0]))?;
            let old=effect_expression(&tr.body,&field,EffectOp::Remove)?;
            let new=effect_expression(&tr.body,&field,EffectOp::Add)?;
            if single_replacement(&tr.body,&field.name,HashSet::from([0])).map_or(false,|stages|!stages.contains(&1)) {
                // One removal then one addition on every modifying path.
                quote!{match (#old,#new){(Some(old),Some(new))=>Some((old,new)),_=>None}}
            } else {
                // A path that only removes (or only adds) uses the unit for the other part.
                let unit=unit_element(&field.stype);
                let removed=format_ident!("__tsm_removed",span=proc_macro2::Span::mixed_site());
                let added=format_ident!("__tsm_added",span=proc_macro2::Span::mixed_site());
                quote!{match #old {
                    Some(#removed)=>match #new {Some(#added)=>Some((#removed,#added)),None=>Some((#removed,#unit))},
                    None=>match #new {Some(#added)=>Some((#unit,#added)),None=>None},
                }}
            }
        }else{
            effect_expression(&tr.body,&field,op)?
        };
        Ok(Effect{function:format_ident!("{}_{}_effect",tr.name,field.name),field,op,expression,replacement})
    }).collect()
}

/// The operand that leaves a field unchanged.
fn unit_element(s: &ShardableType) -> TokenStream {
    match s {
        ShardableType::Count => quote! {0nat},
        ShardableType::Bool => quote! {false},
        ShardableType::Multiset(_) => quote! {::vstd::multiset::Multiset::empty()},
        ShardableType::Option(_) => quote! {None},
        ShardableType::Set(_) | ShardableType::ISet(_) => quote! {::vstd::iset::ISet::empty()},
        ShardableType::Map(..) | ShardableType::IMap(..) => quote! {::vstd::imap::IMap::empty()},
        _ => unreachable!(),
    }
}

/// Exclusive kinds whose removal and addition can both occur in one transition.
fn replaceable(s: &ShardableType) -> bool {
    matches!(
        s,
        ShardableType::Option(_)
            | ShardableType::Map(..)
            | ShardableType::IMap(..)
            | ShardableType::Multiset(_)
            | ShardableType::Count
            | ShardableType::Bool
            | ShardableType::Set(_)
            | ShardableType::ISet(_)
    )
}

/// The component `owner` after one `op` with operand `value`.
pub(crate) fn updated_component(
    stype: &ShardableType,
    op: EffectOp,
    owner: TokenStream,
    value: TokenStream,
) -> TokenStream {
    match stype {
        ShardableType::Set(_) | ShardableType::ISet(_) => match op {
            EffectOp::Add => {
                quote! {::vstd::resource::tsm_collections::SetFragment::op(#owner,::vstd::resource::tsm_collections::set_frag(#value))}
            }
            EffectOp::Remove => {
                quote! {::vstd::resource::tsm_collections::set_remove_many(#owner,#value)}
            }
        },
        ShardableType::PersistentSet(_) | ShardableType::PersistentISet(_) => {
            quote! {::vstd::resource::tsm_collections::PersistentSetFragment::op(#owner,::vstd::resource::tsm_collections::persistent_set_frag(#value))}
        }
        ShardableType::Multiset(_) => match op {
            EffectOp::Add => {
                quote! {::vstd::resource::tsm_finite_multiset::finite_multiset_frag((#owner).values.add(#value))}
            }
            EffectOp::Remove => {
                quote! {::vstd::resource::tsm_finite_multiset::finite_multiset_frag((#owner).values.sub(#value))}
            }
        },
        ShardableType::Count => match op {
            EffectOp::Add => quote! {::vstd::resource::tsm::CountRA{count:(#owner).count+(#value)}},
            EffectOp::Remove => {
                quote! {::vstd::resource::tsm::CountRA{count:((#owner).count-(#value)) as nat}}
            }
        },
        ShardableType::Bool => match op {
            EffectOp::Add => {
                quote! {::vstd::resource::tsm::CountRA{count:(#owner).count+(if #value {1nat}else{0nat})}}
            }
            EffectOp::Remove => {
                quote! {::vstd::resource::tsm::CountRA{count:((#owner).count-(if #value {1nat}else{0nat})) as nat}}
            }
        },
        ShardableType::PersistentBool => {
            quote! {::vstd::resource::tsm_persistent::PersistentCountRA::op(#owner,::vstd::resource::tsm_persistent::persistent_bool_frag(#value))}
        }
        ShardableType::PersistentCount => {
            quote! {::vstd::resource::tsm_persistent::PersistentCountRA::op(#owner,::vstd::resource::tsm_persistent::PersistentCountRA{count:#value})}
        }
        ShardableType::Option(_) => match op {
            EffectOp::Add => {
                quote! {::vstd::resource::tsm_collections::OptionFragment::op(#owner,::vstd::resource::tsm_collections::option_frag(#value))}
            }
            EffectOp::Remove => {
                quote! {::vstd::resource::tsm_collections::option_remove_operand(#owner,#value)}
            }
        },
        ShardableType::PersistentOption(_) => {
            quote! {::vstd::resource::tsm_collections::PersistentOptionFragment::op(#owner,::vstd::resource::tsm_collections::persistent_option_frag(#value))}
        }
        ShardableType::PersistentMap(..) | ShardableType::PersistentIMap(..) => quote! {
            ::vstd::resource::tsm_collections::PersistentMapFragment::op(
                #owner,::vstd::resource::tsm_collections::persistent_map_frag(#value))
        },
        ShardableType::Map(..) | ShardableType::IMap(..) => match op {
            EffectOp::Add => {
                quote! {::vstd::resource::tsm_collections::MapFragment::op(#owner,::vstd::resource::tsm_collections::map_frag(#value))}
            }
            EffectOp::Remove => {
                quote! {::vstd::resource::tsm_collections::map_remove_many(#owner,(#value).dom())}
            }
        },
        _ => unreachable!(),
    }
}

/// The effect spec fns (`<t>_<f>_effect(pre, ..)`: the composed operand of the effect)
/// of `effects`.
pub fn effect_functions(
    effects: &[&Effect],
    state: &TokenStream,
    params: &[TokenStream],
) -> TokenStream {
    let definitions = effects.iter().map(|effect| {
        let function = &effect.function;
        let expression = &effect.expression;
        let basic_element = operand_type(&effect.field.stype);
        let elem: Type = if effect.replacement {
            verus_syn::parse_quote! {(#basic_element,#basic_element)}
        } else {
            basic_element
        };
        quote! {pub open spec fn #function(pre:#state,#(#params),*)->Option<#elem>{#expression}}
    });
    quote! {#(#definitions)*}
}
