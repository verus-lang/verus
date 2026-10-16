//! Checked ownership effects with canonical collection operands.
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
pub struct Effect {
    pub field: Field,
    pub op: EffectOp,
    pub function: Ident,
    pub expression: TokenStream,
    pub replacement: bool,
}

pub fn supported(s: &ShardableType) -> bool {
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
pub fn component(s: &ShardableType) -> TokenStream {
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
pub fn element_type(s: &ShardableType) -> Type {
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
pub(crate) fn element(
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

fn set_view(s: &ShardableType, value: TokenStream) -> TokenStream {
    match s {
        ShardableType::Set(_) | ShardableType::PersistentSet(_) => quote! {(#value).to_iset()},
        ShardableType::ISet(_) | ShardableType::PersistentISet(_) => value,
        _ => unreachable!(),
    }
}

fn map_view(s: &ShardableType, value: TokenStream) -> TokenStream {
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
fn wanted(op: &SpecialOp, kind: EffectOp) -> bool {
    match kind {
        EffectOp::Add => op.is_add(),
        EffectOp::Remove => op.is_remove(),
    }
}
fn has_effect(s: &TransitionStmt, target: &Ident, kind: EffectOp) -> bool {
    match s {
        TransitionStmt::Block(_, xs) => xs.iter().any(|s| has_effect(s, target, kind)),
        TransitionStmt::Split(_, k, xs) => {
            matches!(&**k,SplitKind::Special(n,op,_,_) if n==target&&wanted(op,kind))
                || xs.iter().any(|s| has_effect(s, target, kind))
        }
        _ => false,
    }
}
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
            SplitKind::Special(n, op, _, _) if n == &f.name && wanted(op, kind) => {
                let value = element(f, op, *span)?;
                match xs.first() {
                    Some(rest) if has_effect(rest, &f.name, kind) => {
                        sequential(f, quote! {Some(#value)}, effect_expression(rest, f, kind)?)
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
        ShardableType::PersistentCount => quote! {::vstd::resource::tsm_persistent::count_max(#x, #y)},
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

fn collect(
    s: &TransitionStmt,
    fields: &HashMap<String, Field>,
    kinds: &mut HashMap<String, HashSet<EffectOp>>,
) -> Result<HashMap<String, usize>, Error> {
    let mut counts: HashMap<String, usize> = HashMap::new();
    match s {
        TransitionStmt::Block(_, children) => {
            for child in children {
                for (n, count) in collect(child, fields, kinds)? {
                    *counts.entry(n).or_default() += count;
                }
            }
        }
        TransitionStmt::Split(span, kind, children) => {
            if let SplitKind::Special(n, op, _, pat) = &**kind {
                let f = &fields[&n.to_string()];
                if supported(&f.stype) {
                    element(f, op, *span)?;
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
                        counts.insert(n.to_string(), 1);
                    }
                }
            }
            let mut alternatives: HashMap<String, usize> = HashMap::new();
            for child in children {
                for (n, count) in collect(child, fields, kinds)? {
                    let previous = alternatives.entry(n).or_default();
                    *previous = (*previous).max(count);
                }
            }
            for (n, count) in alternatives {
                *counts.entry(n).or_default() += count;
            }
        }
        _ => {}
    }
    Ok(counts)
}

fn replacement_order(
    s: &TransitionStmt,
    target: &Ident,
    mut stages: HashSet<u8>,
) -> Result<HashSet<u8>, Error> {
    match s {
        TransitionStmt::Block(_, children) => {
            for child in children {
                stages = replacement_order(child, target, stages)?;
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
                        outcomes.extend(replacement_order(child, target, stages.clone())?);
                    }
                    stages = outcomes;
                }
                _ => {
                    for child in children {
                        stages = replacement_order(child, target, stages)?;
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
fn single_replacement(s: &TransitionStmt, target: &Ident, mut stages: HashSet<u8>) -> Option<HashSet<u8>> {
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
                if supported(&fields[&name.to_string()].stype) {
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

pub fn analyze(tr: &Transition, fields: &HashMap<String, Field>) -> Result<Vec<Effect>, Error> {
    check_binding_order(&tr.body, fields, &mut HashSet::new())?;
    let mut kinds = HashMap::new();
    collect(&tr.body, fields, &mut kinds)?;
    let mut names: Vec<_> = kinds.keys().cloned().collect();
    names.sort();
    names.into_iter().map(|n|{
        let field=fields[&n].clone();let operations=&kinds[&n];let replacement=operations.len()==2;
        let op=if replacement{EffectOp::Add}else{*operations.iter().next().unwrap()};
        let expression=if replacement{
            if !replaceable(&field.stype){
                return Err(Error::new(*tr.body.get_span(),"verified replacement supports exclusive monoid fields only"));
            }
            replacement_order(&tr.body,&field.name,HashSet::from([0]))?;
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

pub fn updated(effect: &Effect, owner: TokenStream, value: TokenStream) -> TokenStream {
    if effect.replacement {
        return match effect.field.stype {
            ShardableType::Multiset(_) => quote! {
                ::vstd::resource::tsm_finite_multiset::finite_multiset_frag(
                    (#owner).values.sub((#value).0).add((#value).1))
            },
            ShardableType::Option(_) => quote! {
                ::vstd::resource::tsm_collections::OptionFragment::op(
                    ::vstd::resource::tsm_collections::option_remove_operand(#owner,(#value).0),
                    ::vstd::resource::tsm_collections::option_frag((#value).1))
            },
            ShardableType::Map(..) | ShardableType::IMap(..) => quote! {
                ::vstd::resource::tsm_collections::MapFragment::op(
                    ::vstd::resource::tsm_collections::map_remove_many(#owner,(#value).0.dom()),
                    ::vstd::resource::tsm_collections::map_frag((#value).1))
            },
            ShardableType::Count => quote! {
                ::vstd::resource::tsm::CountRA{count:(((#owner).count-(#value).0) as nat+(#value).1) as nat}
            },
            ShardableType::Bool => quote! {
                ::vstd::resource::tsm::CountRA{count:(((#owner).count-(if (#value).0 {1nat}else{0nat})) as nat
                    +(if (#value).1 {1nat}else{0nat})) as nat}
            },
            ShardableType::Set(_) | ShardableType::ISet(_) => quote! {
                ::vstd::resource::tsm_collections::SetFragment::op(
                    ::vstd::resource::tsm_collections::set_remove_many(#owner,(#value).0),
                    ::vstd::resource::tsm_collections::set_frag((#value).1))
            },
            _ => unreachable!(),
        };
    }
    updated_component(&effect.field.stype, effect.op, owner, value)
}
pub fn extra_ownership(effects: &[Effect], pn: &[&Ident]) -> TokenStream {
    let conditions:Vec<_>=effects.iter().filter_map(|effect|{
        let key_type=match &effect.field.stype {
            ShardableType::Map(k,_)|ShardableType::IMap(k,_) if effect.replacement || effect.op==EffectOp::Remove => k,
            _=>return None,
        };
        let field=&effect.field.name;
        let function=&effect.function;
        let key=format_ident!("__tsm_owned_map_key",span=proc_macro2::Span::mixed_site());
        let consumes=quote! {forall|#key:#key_type| ::vstd::prelude::imply(#[trigger] removed.contains_key(#key),owned.#field.at(#key)==Some(::vstd::resource::exclusive::ExclusiveRA::Exclusive(removed[#key])))};
        Some(if effect.replacement {
            quote! {match Self::#function(pre,#(#pn),*) {Some((removed,_added))=>(#consumes),None=>true}}
        } else {
            quote! {match Self::#function(pre,#(#pn),*) {Some(removed)=>#consumes,None=>true}}
        })
    }).collect();
    quote! {true #(&&(#conditions))*}
}
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

#[allow(clippy::too_many_arguments)]
pub fn declarations(
    effects: &[Effect],
    state: &TokenStream,
    fragment: &TokenStream,
    protocol: &TokenStream,
    strong: &Ident,
    owners: &Ident,
    pn: &[&Ident],
    params: &[TokenStream],
) -> (TokenStream, Vec<TokenStream>) {
    let mut definitions = vec![];
    let mut calls = vec![];
    for effect in effects {
        let n = &effect.field.name;
        let function = &effect.function;
        let expression = &effect.expression;
        let basic_element = element_type(&effect.field.stype);
        let elem: Type = if effect.replacement {
            verus_syn::parse_quote! {(#basic_element,#basic_element)}
        } else {
            basic_element
        };
        let ty = component(&effect.field.stype);
        let own_fn = format_ident!("{}_owned", function);
        let lemma = format_ident!("{}_frame", function);
        let update = updated(effect, quote! {owned.#n}, quote! {value});
        let pre_embed = embed(&effect.field.stype, quote! {pre.#n});
        let post_embed = embed(&effect.field.stype, quote! {post.#n});
        let state_update = if effect.replacement {
            match &effect.field.stype {
                ShardableType::Multiset(_) => quote! {pre.#n.sub(value.0).add(value.1)},
                ShardableType::Option(_) => quote! {
                    ::vstd::resource::tsm_collections::option_union(
                        ::vstd::resource::tsm_collections::option_subtract(pre.#n,value.0),value.1)
                },
                stype @ (ShardableType::Map(..) | ShardableType::IMap(..)) => {
                    let before = map_view(&stype, quote! {pre.#n});
                    quote! {(#before).remove_keys(value.0.dom()).union_prefer_right(value.1)}
                }
                ShardableType::Count => quote! {((pre.#n-value.0) as nat+value.1) as nat},
                ShardableType::Bool => quote! {((pre.#n && !value.0) || value.1)},
                s @ (ShardableType::Set(_) | ShardableType::ISet(_)) => {
                    let before = set_view(s, quote! {pre.#n});
                    quote! {(#before).difference(value.0).union(value.1)}
                }
                _ => unreachable!(),
            }
        } else {
            match (&effect.field.stype, effect.op) {
                (
                    s @ (ShardableType::Set(_)
                    | ShardableType::ISet(_)
                    | ShardableType::PersistentSet(_)
                    | ShardableType::PersistentISet(_)),
                    op,
                ) => {
                    let before = set_view(s, quote! {pre.#n});
                    match op {
                        EffectOp::Add => quote! {(#before).union(value)},
                        EffectOp::Remove => quote! {(#before).difference(value)},
                    }
                }
                (ShardableType::Multiset(_), EffectOp::Add) => quote! {pre.#n.add(value)},
                (ShardableType::Multiset(_), EffectOp::Remove) => quote! {pre.#n.sub(value)},
                (ShardableType::Count, EffectOp::Add) => quote! {pre.#n+value},
                (ShardableType::Count, EffectOp::Remove) => quote! {(pre.#n-value) as nat},
                (ShardableType::Bool, EffectOp::Add) => quote! {(pre.#n || value)},
                (ShardableType::Bool, EffectOp::Remove) => quote! {(pre.#n && !value)},
                (ShardableType::PersistentBool, EffectOp::Add) => quote! {(pre.#n || value)},
                (ShardableType::PersistentCount, EffectOp::Add) => {
                    quote! {::vstd::resource::tsm_persistent::count_max(pre.#n,value)}
                }
                (ShardableType::Option(_) | ShardableType::PersistentOption(_), EffectOp::Add) => {
                    quote! {::vstd::resource::tsm_collections::option_union(pre.#n,value)}
                }
                (ShardableType::Option(_), EffectOp::Remove) => {
                    quote! {::vstd::resource::tsm_collections::option_subtract(pre.#n,value)}
                }
                (stype @ (ShardableType::Map(..) | ShardableType::IMap(..)), EffectOp::Add) => {
                    let before = map_view(&stype, quote! {pre.#n});
                    quote! {(#before).union_prefer_right(value)}
                }
                (stype @ (ShardableType::Map(..) | ShardableType::IMap(..)), EffectOp::Remove) => {
                    let before = map_view(&stype, quote! {pre.#n});
                    quote! {(#before).remove_keys(value.dom())}
                }
                (
                    stype @ (ShardableType::PersistentMap(..) | ShardableType::PersistentIMap(..)),
                    EffectOp::Add,
                ) => {
                    let before = map_view(&stype, quote! {pre.#n});
                    quote! {(#before).union_prefer_right(value)}
                }
                _ => unreachable!(),
            }
        };
        let helper = if effect.replacement {
            match &effect.field.stype {
                ShardableType::Multiset(_) => quote! {
                    ::vstd::resource::tsm_finite_multiset::finite_multiset_remove_many_frame(
                        owned.#n,frame,pre.#n,value.0);
                    let middle=pre.#n.sub(value.0);
                    let remaining=::vstd::resource::tsm_finite_multiset::finite_multiset_frag(
                        owned.#n.values.sub(value.0));
                    ::vstd::resource::tsm_finite_multiset::finite_multiset_add_many_frame(
                        remaining,frame,middle,value.1);
                },
                ShardableType::Option(_) => quote! {
                    if value.0 is Some {
                        let local_value=owned.#n->Some_0->Exclusive_0;
                        assert(owned.#n==Some(::vstd::resource::exclusive::ExclusiveRA::Exclusive(local_value)));
                        ::vstd::resource::tsm_collections::option_owned_frame(owned.#n,frame,pre.#n,local_value);
                        assert(value.0==Some(local_value));
                    }
                    ::vstd::resource::tsm_collections::option_remove_general_frame(owned.#n,frame,pre.#n,value.0);
                    let middle=::vstd::resource::tsm_collections::option_subtract(pre.#n,value.0);
                    let remaining=::vstd::resource::tsm_collections::option_remove_operand(owned.#n,value.0);
                    assert(middle is None || value.1 is None);
                    ::vstd::resource::tsm_collections::option_add_general_frame(remaining,frame,middle,value.1);
                },
                stype @ (ShardableType::Map(..) | ShardableType::IMap(..)) => {
                    let before = map_view(&stype, quote! {pre.#n});
                    let key_type = match stype {
                        ShardableType::Map(k, _) | ShardableType::IMap(k, _) => k,
                        _ => unreachable!(),
                    };
                    let key =
                        format_ident!("__tsm_replaced_key", span = proc_macro2::Span::mixed_site());
                    quote! {
                        assert forall|#key:#key_type| #[trigger] value.0.contains_key(#key)
                            implies owned.#n.at(#key)==Some(::vstd::resource::exclusive::ExclusiveRA::Exclusive(value.0[#key])) by {
                            let local_value=owned.#n.at(#key)->Some_0->Exclusive_0;
                            assert(owned.#n.at(#key)==Some(::vstd::resource::exclusive::ExclusiveRA::Exclusive(local_value)));
                            ::vstd::resource::tsm_collections::map_owned_frame(owned.#n,frame,#before,#key,local_value);
                            assert(value.0[#key]==local_value);
                        };
                        ::vstd::resource::tsm_collections::map_remove_many_frame(owned.#n,frame,#before,value.0);
                        let middle=(#before).remove_keys(value.0.dom());
                        let remaining=::vstd::resource::tsm_collections::map_remove_many(owned.#n,value.0.dom());
                        assert(middle.dom().disjoint(value.1.dom()));
                        ::vstd::resource::tsm_collections::map_add_many_frame(remaining,frame,middle,value.1);
                    }
                }
                ShardableType::Count => quote! {},
                ShardableType::Bool => quote! {
                    let middle=pre.#n && !value.0;
                    let remaining=::vstd::resource::tsm::CountRA{count:(owned.#n.count-(if value.0 {1nat}else{0nat})) as nat};
                    if value.0 {::vstd::resource::tsm_bool::bool_remove_frame(owned.#n,frame,pre.#n);}
                    assert(::vstd::resource::tsm::CountRA::op(remaining,frame)==::vstd::resource::tsm_bool::bool_frag(middle));
                    if value.1 {::vstd::resource::tsm_bool::bool_add_frame(remaining,frame,middle);}
                },
                s @ (ShardableType::Set(_) | ShardableType::ISet(_)) => {
                    let before = set_view(s, quote! {pre.#n});
                    quote! {
                        ::vstd::resource::tsm_collections::set_remove_many_frame(owned.#n,frame,#before,value.0);
                        let middle=(#before).difference(value.0);
                        let remaining=::vstd::resource::tsm_collections::set_remove_many(owned.#n,value.0);
                        assert(middle.disjoint(value.1));
                        ::vstd::resource::tsm_collections::set_add_many_frame(remaining,frame,middle,value.1);
                    }
                }
                _ => unreachable!(),
            }
        } else {
            match (&effect.field.stype, effect.op) {
                (s @ (ShardableType::Set(_) | ShardableType::ISet(_)), op) => {
                    let before = set_view(s, quote! {pre.#n});
                    match op {
                        EffectOp::Add => {
                            quote! {::vstd::resource::tsm_collections::set_add_many_frame(owned.#n,frame,#before,value);}
                        }
                        EffectOp::Remove => {
                            quote! {::vstd::resource::tsm_collections::set_remove_many_frame(owned.#n,frame,#before,value);}
                        }
                    }
                }
                (
                    s @ (ShardableType::PersistentSet(_) | ShardableType::PersistentISet(_)),
                    EffectOp::Add,
                ) => {
                    let before = set_view(s, quote! {pre.#n});
                    quote! {::vstd::resource::tsm_collections::persistent_set_union_frame(owned.#n,frame,#before,value);}
                }
                (ShardableType::Multiset(_), EffectOp::Add) => {
                    quote! {::vstd::resource::tsm_finite_multiset::finite_multiset_add_many_frame(owned.#n,frame,pre.#n,value);}
                }
                (ShardableType::Multiset(_), EffectOp::Remove) => {
                    quote! {::vstd::resource::tsm_finite_multiset::finite_multiset_remove_many_frame(owned.#n,frame,pre.#n,value);}
                }
                (ShardableType::Bool, EffectOp::Add) => {
                    quote! {if value {::vstd::resource::tsm_bool::bool_add_frame(owned.#n,frame,pre.#n);}}
                }
                (ShardableType::Bool, EffectOp::Remove) => {
                    quote! {if value {::vstd::resource::tsm_bool::bool_remove_frame(owned.#n,frame,pre.#n);}}
                }
                (ShardableType::PersistentBool, EffectOp::Add) => {
                    quote! {::vstd::resource::tsm_persistent::persistent_bool_raise_frame(owned.#n,frame,pre.#n,value);}
                }
                (ShardableType::PersistentCount, EffectOp::Add) => {
                    quote! {::vstd::resource::tsm_persistent::persistent_count_raise_frame(owned.#n,frame,pre.#n,value);}
                }
                (ShardableType::Option(_), EffectOp::Add) => {
                    quote! {::vstd::resource::tsm_collections::option_add_general_frame(owned.#n,frame,pre.#n,value);}
                }
                (ShardableType::Option(_), EffectOp::Remove) => {
                    quote! {
                        if value is Some {
                            let local_value=owned.#n->Some_0->Exclusive_0;
                            assert(owned.#n==Some(::vstd::resource::exclusive::ExclusiveRA::Exclusive(local_value)));
                            ::vstd::resource::tsm_collections::option_owned_frame(owned.#n,frame,pre.#n,local_value);
                            assert(value==Some(local_value));
                        }
                        ::vstd::resource::tsm_collections::option_remove_general_frame(owned.#n,frame,pre.#n,value);
                    }
                }
                (ShardableType::PersistentOption(_), EffectOp::Add) => {
                    quote! {::vstd::resource::tsm_collections::persistent_option_union_general_frame(owned.#n,frame,pre.#n,value);}
                }
                (stype @ (ShardableType::Map(..) | ShardableType::IMap(..)), op) => {
                    let before = map_view(&stype, quote! {pre.#n});
                    match op {
                        EffectOp::Add => {
                            quote! {::vstd::resource::tsm_collections::map_add_many_frame(owned.#n,frame,#before,value);}
                        }
                        EffectOp::Remove => {
                            let key_type = match stype {
                                ShardableType::Map(k, _) | ShardableType::IMap(k, _) => k,
                                _ => unreachable!(),
                            };
                            let key = format_ident!(
                                "__tsm_removed_key",
                                span = proc_macro2::Span::mixed_site()
                            );
                            quote! {
                                assert forall|#key:#key_type| #[trigger] value.contains_key(#key)
                                    implies owned.#n.at(#key)==Some(::vstd::resource::exclusive::ExclusiveRA::Exclusive(value[#key])) by {
                                    let local_value=owned.#n.at(#key)->Some_0->Exclusive_0;
                                    assert(owned.#n.at(#key)==Some(::vstd::resource::exclusive::ExclusiveRA::Exclusive(local_value)));
                                    ::vstd::resource::tsm_collections::map_owned_frame(owned.#n,frame,#before,#key,local_value);
                                    assert(value[#key]==local_value);
                                };
                                ::vstd::resource::tsm_collections::map_remove_many_frame(owned.#n,frame,#before,value);
                            }
                        }
                    }
                }
                (
                    stype @ (ShardableType::PersistentMap(..) | ShardableType::PersistentIMap(..)),
                    EffectOp::Add,
                ) => {
                    let before = map_view(&stype, quote! {pre.#n});
                    quote! {::vstd::resource::tsm_collections::persistent_map_union_frame(owned.#n,frame,#before,value);}
                }
                _ => quote! {},
            }
        };
        let post_value = if matches!(
            effect.field.stype,
            ShardableType::Set(_)
                | ShardableType::ISet(_)
                | ShardableType::PersistentSet(_)
                | ShardableType::PersistentISet(_)
        ) {
            set_view(&effect.field.stype, quote! {post.#n})
        } else if matches!(
            effect.field.stype,
            ShardableType::Map(..)
                | ShardableType::IMap(..)
                | ShardableType::PersistentMap(..)
                | ShardableType::PersistentIMap(..)
        ) {
            map_view(&effect.field.stype, quote! {post.#n})
        } else {
            quote! {post.#n}
        };
        definitions.push(quote!{
            pub open spec fn #function(pre:#state,#(#params),*)->Option<#elem>{#expression}
            pub open spec fn #own_fn(owned:#fragment,pre:#state,#(#params),*)->#ty {
                match Self::#function(pre,#(#pn),*){Some(value)=>#update,None=>owned.#n}
            }
            pub proof fn #lemma(pre:#state,post:#state,owned:#fragment,h:#fragment,z:#fragment,#(#params),*)
                requires pre.invariant(),Self::#strong(pre,post,#(#pn),*),
                    <#fragment>::op(<#fragment>::op(owned,h),z)==<#protocol as ::vstd::resource::tsm::Machine>::embed(pre),
                    Self::#owners(pre,owned,h,#(#pn),*)
                ensures <#ty>::op(Self::#own_fn(owned,pre,#(#pn),*),<#ty>::op(h.#n,z.#n))==(#post_embed)
            {
                <#fragment>::associative(owned,h,z);
                let frame=<#ty>::op(h.#n,z.#n);
                assert(<#ty>::op(owned.#n,frame)==(#pre_embed));
                match Self::#function(pre,#(#pn),*) {
                    Some(value)=>{
                        assert(#post_value==#state_update);
                        #helper
                    },
                    None=>{assert(post.#n==pre.#n);}
                }
            }
        });
        calls.push(quote! {<#state>::#lemma(pre,post,owned,h,z,#(#pn),*);});
    }
    (quote! {#(#definitions)*}, calls)
}

pub fn owned_expression(
    effects: &[Effect],
    field: &Ident,
    state_expr: &TokenStream,
    pn: &[&Ident],
) -> Option<TokenStream> {
    effects.iter().find(|e| e.field.name == *field).map(|e| {
        let function = format_ident!("{}_owned", e.function);
        quote! {#state_expr::#function(owned,pre,#(#pn),*)}
    })
}
