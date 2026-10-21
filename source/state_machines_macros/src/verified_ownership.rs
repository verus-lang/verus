//! Ordered ownership checks for the proof-producing backend.
//!
//! This compiler emits a pure `(enabled, owned_fragment)` expression. Each
//! statement sees the owned rights produced by its predecessor; the borrowed
//! fragment stays fixed. These expressions are preconditions, never proofs of
//! state safety, invariant preservation, or resource updates.
use crate::ast::*;
use crate::verified_monoids::{
    EffectOp, bind_pattern, is_monoid_type, operand, operand_type, updated_component,
};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use std::collections::HashMap;
use verus_syn::{Error, Ident};

/// Compiles a transition body to its ordered `(enabled, owned_fragment)` ownership
/// expression.
struct Compiler<'a> {
    fields: &'a HashMap<String, Field>,
    fragment: &'a TokenStream,
    shared: Ident,
    next_ident: usize,
}

impl Compiler<'_> {
    /// A fresh hygienic `__tsm_ownership_<purpose>_<n>` binder.
    fn fresh(&mut self, purpose: &str) -> Ident {
        let index = self.next_ident;
        self.next_ident += 1;
        format_ident!("__tsm_ownership_{}_{}", purpose, index, span = Span::mixed_site())
    }

    /// Returning the fragment alongside the condition preserves effects across
    /// lexical scopes and across branches without moving bindings out of scope.
    /// `None` stands for `(true, current)`: the statement has no ownership
    /// condition and keeps the fragment, so the caller omits it.
    fn statement(
        &mut self,
        stmt: &TransitionStmt,
        current: TokenStream,
    ) -> Result<Option<TokenStream>, Error> {
        let trivial = |p: Option<TokenStream>, current: &TokenStream| p.unwrap_or(quote! {(true, #current)});
        match stmt {
            TransitionStmt::Block(_, children) => self.sequence(children, current),
            TransitionStmt::Split(span, kind, children) => match &**kind {
                SplitKind::Let(pattern, ty, _, expression) => {
                    let ty = ty.as_ref().map(|ty| quote! {:#ty});
                    let Some(body) = self.sequence(children, current)? else { return Ok(None) };
                    Ok(Some(quote! {{let #pattern #ty = #expression; #body}}))
                }
                SplitKind::If(condition) => {
                    let then_branch = self.statement(&children[0], current.clone())?;
                    let else_branch = match children.get(1) {
                        Some(child) => self.statement(child, current.clone())?,
                        None => None,
                    };
                    if then_branch.is_none() && else_branch.is_none() {
                        return Ok(None);
                    }
                    let then_branch = trivial(then_branch, &current);
                    let else_branch = trivial(else_branch, &current);
                    Ok(Some(quote! {if #condition {#then_branch} else {#else_branch}}))
                }
                SplitKind::Match(expression, arms) => {
                    if arms.len() != children.len() {
                        return Err(Error::new(*span, "ownership match has mismatched arms"));
                    }
                    let bodies = children
                        .iter()
                        .map(|child| self.statement(child, current.clone()))
                        .collect::<Result<Vec<_>, Error>>()?;
                    if bodies.iter().all(|b| b.is_none()) {
                        return Ok(None);
                    }
                    let cases: Vec<_> = arms
                        .iter()
                        .zip(bodies)
                        .map(|(arm, body)| {
                            let pattern = &arm.pat;
                            let guard =
                                arm.guard.as_ref().map(|(keyword, expr)| quote! {#keyword #expr});
                            let body = trivial(body, &current);
                            quote! {#pattern #guard => {#body}}
                        })
                        .collect();
                    Ok(Some(quote! {match #expression {#(#cases),*}}))
                }
                SplitKind::Special(name, operation, _, pattern) => {
                    let field = self.fields.get(&name.to_string()).ok_or_else(|| {
                        Error::new(*span, "ownership operation refers to an unknown field")
                    })?;
                    if is_monoid_type(&field.stype) {
                        self.monoid_statement(field, operation, pattern.as_deref(), children, current, *span).map(Some)
                    } else if operation.stmt.is_for_storage() {
                        // Storage bindings refer to the mathematical state's
                        // permission. Checked state safety and physical exchange
                        // obligations independently establish its provenance.
                        let Some(body) = self.sequence(children, current)? else { return Ok(None) };
                        match pattern {
                            Some(pattern) => {
                                let observed = match &operation.elt {
                                    MonoidElt::OptionSome(None) => quote! {pre.#name->Some_0},
                                    MonoidElt::SingletonKV(key, None) => quote! {pre.#name[#key]},
                                    _ => {
                                        return Err(Error::new(
                                            *span,
                                            "unsupported storage ownership binding",
                                        ));
                                    }
                                };
                                Ok(Some(bind_pattern(pattern, observed, body)))
                            }
                            None => Ok(Some(body)),
                        }
                    } else {
                        Err(Error::new(*span, "unsupported ordered ownership component"))
                    }
                }
            },
            // Ordinary conditions, assertions and variable updates are checked
            // by the independent state executor. They do not change monoid
            // ownership and must not be treated as ownership assumptions here.
            _ => Ok(None),
        }
    }

    /// Whether `statement` returns exactly its input fragment: it contains no
    /// `add`/`remove` of an ownership component (mirrors `statement`).
    fn preserves_owned(&self, stmt: &TransitionStmt) -> bool {
        match stmt {
            TransitionStmt::Block(_, children) => children.iter().all(|c| self.preserves_owned(c)),
            TransitionStmt::Split(_, kind, children) => {
                let local = match &**kind {
                    SplitKind::Special(name, operation, _, _) => {
                        match self.fields.get(&name.to_string()) {
                            Some(field) if is_monoid_type(&field.stype) => {
                                matches!(operation.stmt, MonoidStmtType::Have)
                            }
                            _ => true,
                        }
                    }
                    _ => true,
                };
                local && children.iter().all(|c| self.preserves_owned(c))
            }
            _ => true,
        }
    }

    /// The pair of a statement sequence, each statement starting from the owned fragment its
    /// predecessor leaves; `None` as for `statement`.
    fn sequence(
        &mut self,
        statements: &[TransitionStmt],
        current: TokenStream,
    ) -> Result<Option<TokenStream>, Error> {
        let mut result = current;
        let mut declarations = Vec::new();
        let mut conditions = Vec::new();
        let mut pairs = Vec::new();
        // A `remove` or `have` of a map (any strategy) quantifies over its
        // operand's keys with the trigger `observer.f.at(k)` on the fragment it
        // observes (`owned`, or `op(owned, shared)`); one of a set quantifies
        // too, with a trigger on the operand.
        let map = |t: &ShardableType| {
            matches!(
                t,
                ShardableType::Map(..)
                    | ShardableType::IMap(..)
                    | ShardableType::PersistentMap(..)
                    | ShardableType::PersistentIMap(..)
            )
        };
        let quantified = |t: &ShardableType| {
            map(t)
                || matches!(
                    t,
                    ShardableType::Set(_)
                        | ShardableType::ISet(_)
                        | ShardableType::PersistentSet(_)
                        | ShardableType::PersistentISet(_)
                )
        };
        for (index, statement) in statements.iter().enumerate() {
            let preserves = self.preserves_owned(statement);
            let Some(pair) = self.statement(statement, result.clone())? else { continue };
            pairs.push(pair.clone());
            let enabled = self.fresh("enabled");
            let direct = if !preserves
                && self.observes(std::slice::from_ref(statement), &quantified)
                && self.observes(&statements[index + 1..], &map)
            {
                self.fragment_after(statement, result.clone())?
            } else {
                None
            };
            if let Some(fragment) = direct {
                // A later map observation's trigger mentions this statement's
                // result. Bind that fragment itself, not the projection of the
                // pair: the pair also holds this statement's quantified
                // conditions, which a trigger must not contain (Z3 drops such
                // a pattern: "'=>' cannot be used in patterns").
                let next = self.fresh("owned");
                declarations.push(quote! {let #enabled = (#pair).0; let #next = #fragment;});
                result = quote! {#next};
            } else if preserves {
                // The statement returns its input fragment unchanged. Keep
                // referring to that input rather than to the projection of the
                // pair: the pair also holds the statement's conditions (with
                // their quantifiers), and a later observation's trigger
                // `op(owned, shared).f.at(k)` must not mention it, or it
                // cannot match the ground terms of the fragment (e.g. two
                // `have`s of one map field before a guard).
                declarations.push(quote! {let #enabled = (#pair).0;});
            } else {
                let next = self.fresh("owned");
                declarations.push(quote! {let (#enabled, #next) = #pair;});
                result = quote! {#next};
            }
            conditions.push(enabled);
        }
        match pairs.len() {
            0 => Ok(None),
            1 => Ok(pairs.pop()),
            _ => Ok(Some(quote! {{#(#declarations)* (true #(&& #conditions)*, #result)}})),
        }
    }

    /// The pair of a monoid `add`, `remove` or `have` on `field`, followed by `children`.
    fn monoid_statement(
        &mut self,
        field: &Field,
        operation: &SpecialOp,
        pattern: Option<&verus_syn::Pat>,
        children: &[TransitionStmt],
        current: TokenStream,
        span: Span,
    ) -> Result<TokenStream, Error> {
        let name = &field.name;
        let (observer, value) = self.observed_operand(field, operation, &current, span)?;
        // Evaluate the candidate before a pattern can shadow any name in its
        // key/value expression (e.g. `remove map -= [key => let key]`).
        let value_ident = self.fresh("value");
        let observed_value = value;
        let value = quote! {#value_ident};
        let condition = if matches!(operation.stmt, MonoidStmtType::Add(_)) {
            // Full-state absence/agreement is a state-safety obligation. A
            // local absence check cannot establish absence from other owners.
            quote! {true}
        } else {
            match field.stype {
                ShardableType::Multiset(_) => quote! {(#value).subset_of((#observer).#name.values)},
                ShardableType::Bool | ShardableType::PersistentBool => {
                    quote! {(#observer).#name.count >= (if #value {1nat}else{0nat})}
                }
                ShardableType::Count | ShardableType::PersistentCount => {
                    quote! {(#observer).#name.count >= (#value)}
                }
                ShardableType::Option(_) => quote! {
                    ::vstd::resource::tsm_collections::option_contains_operand((#observer).#name, #value)
                },
                ShardableType::PersistentOption(_) => quote! {
                    ::vstd::resource::tsm_collections::persistent_option_contains_operand((#observer).#name, #value)
                },
                ShardableType::Map(ref key_type, _) | ShardableType::IMap(ref key_type, _) => {
                    let key = self.fresh("map_key");
                    quote! {forall|#key:#key_type| ::vstd::prelude::imply((#value).contains_key(#key),(#[trigger] (#observer).#name.at(#key))==Some(::vstd::resource::exclusive::ExclusiveRA::Exclusive((#value)[#key])))}
                }
                ShardableType::PersistentMap(ref key_type, _)
                | ShardableType::PersistentIMap(ref key_type, _) => {
                    let key = self.fresh("map_key");
                    quote! {forall|#key:#key_type| ::vstd::prelude::imply((#value).contains_key(#key),(#[trigger] (#observer).#name.at(#key))==Some(::vstd::resource::agree::AgreementRA::Agree((#value)[#key])))}
                }
                ShardableType::Set(ref key_type) | ShardableType::ISet(ref key_type) => {
                    let key = self.fresh("set_key");
                    quote! {forall|#key: #key_type| ::vstd::prelude::imply(#[trigger] (#value).contains(#key),
                    (#observer).#name.at(#key)
                        == Some(::vstd::resource::exclusive::ExclusiveRA::Exclusive(())))}
                }
                ShardableType::PersistentSet(ref key_type)
                | ShardableType::PersistentISet(ref key_type) => {
                    let key = self.fresh("set_key");
                    quote! {forall|#key: #key_type| ::vstd::prelude::imply(#[trigger] (#value).contains(#key),
                    (#observer).#name.at(#key)
                        == Some(::vstd::resource::agree::AgreementRA::Agree(())))}
                }
                _ => return Err(Error::new(span, "unsupported ownership observation")),
            }
        };

        let next = self.next_fragment(field, operation, current, &value);
        let body = match self.sequence(children, next.clone())? {
            Some(body) => {
                let enabled = self.fresh("enabled");
                let owned = self.fresh("owned");
                quote! {{
                    let (#enabled, #owned) = #body;
                    ((#condition) && #enabled, #owned)
                }}
            }
            None => quote! {(#condition, #next)},
        };
        let scoped = match pattern {
            Some(pattern) => {
                bind_pattern(pattern, bound_value(field, operation, value, span)?, body)
            }
            None => body,
        };
        let value_type = operand_type(&field.stype);
        Ok(quote! {{let #value_ident: #value_type = #observed_value; #scoped}})
    }

    /// The observer of a monoid statement (the fragment it finds its operand in)
    /// and its operand, before the operand is bound to a name.
    fn observed_operand(
        &self,
        field: &Field,
        operation: &SpecialOp,
        current: &TokenStream,
        span: Span,
    ) -> Result<(TokenStream, TokenStream), Error> {
        if matches!(operation.stmt, MonoidStmtType::Remove) && field.stype.is_persistent() {
            return Err(Error::new(span, "persistent ownership cannot be removed"));
        }
        let name = &field.name;
        let fragment = self.fragment;
        let shared = &self.shared;
        let observer = match operation.stmt {
            MonoidStmtType::Remove => current.clone(),
            MonoidStmtType::Have => quote! {<#fragment>::op(#current, #shared)},
            MonoidStmtType::Add(_) => current.clone(),
            _ => return Err(Error::new(span, "unsupported ownership operation")),
        };

        // An implicit value is observed at this statement, rather than in the
        // initial fragment or initial full state. Refutable patterns are bound
        // exactly as in the mathematical executor; its safety predicate still
        // checks whether the pattern matches.
        let value = match (&field.stype, &operation.elt) {
            (ShardableType::Option(_), MonoidElt::OptionSome(None)) => {
                quote! {Some((#observer).#name->Some_0->Exclusive_0)}
            }
            (ShardableType::PersistentOption(_), MonoidElt::OptionSome(None)) => {
                quote! {Some((#observer).#name->Some_0->Agree_0)}
            }
            (
                ShardableType::Map(..) | ShardableType::IMap(..),
                MonoidElt::SingletonKV(key, None),
            ) => {
                quote! {::vstd::imap::IMap::empty().insert(#key,(#observer).#name.at(#key)->Some_0->Exclusive_0)}
            }
            (
                ShardableType::PersistentMap(..) | ShardableType::PersistentIMap(..),
                MonoidElt::SingletonKV(key, None),
            ) => {
                quote! {::vstd::imap::IMap::empty().insert(#key,(#observer).#name.at(#key)->Some_0->Agree_0)}
            }
            _ => operand(field, operation, span)?,
        };
        Ok((observer, value))
    }

    /// The owned fragment after a monoid statement with (bound) operand `value`.
    fn next_fragment(
        &self,
        field: &Field,
        operation: &SpecialOp,
        current: TokenStream,
        value: &TokenStream,
    ) -> TokenStream {
        let name = &field.name;
        let fragment = self.fragment;
        match operation.stmt {
            MonoidStmtType::Have => current,
            MonoidStmtType::Remove | MonoidStmtType::Add(_) => {
                let effect = if matches!(operation.stmt, MonoidStmtType::Remove) {
                    EffectOp::Remove
                } else {
                    EffectOp::Add
                };
                let component = updated_component(
                    &field.stype,
                    effect,
                    quote! {(#current).#name},
                    value.clone(),
                );
                let setter = format_ident!("__tsm_set_{}", name);
                quote! {<#fragment>::#setter(#current, #component)}
            }
            _ => unreachable!(),
        }
    }

    /// Whether `statements` contain a `remove` or `have` of a field whose type
    /// `kinds` accepts.
    fn observes(
        &self,
        statements: &[TransitionStmt],
        kinds: &dyn Fn(&ShardableType) -> bool,
    ) -> bool {
        statements.iter().any(|stmt| match stmt {
            TransitionStmt::Block(_, children) => self.observes(children, kinds),
            TransitionStmt::Split(_, kind, children) => {
                let here = match &**kind {
                    SplitKind::Special(name, operation, _, _) => {
                        matches!(operation.stmt, MonoidStmtType::Remove | MonoidStmtType::Have)
                            && self
                                .fields
                                .get(&name.to_string())
                                .is_some_and(|field| kinds(&field.stype))
                    }
                    _ => false,
                };
                here || self.observes(children, kinds)
            }
            _ => false,
        })
    }

    /// The owned fragment `stmt` leaves, without its conditions: the second
    /// component of its pair (`statement`); `None` when that is `current`.
    fn fragment_after(
        &mut self,
        stmt: &TransitionStmt,
        current: TokenStream,
    ) -> Result<Option<TokenStream>, Error> {
        match stmt {
            TransitionStmt::Block(_, children) => self.fragment_after_sequence(children, current),
            TransitionStmt::Split(span, kind, children) => match &**kind {
                SplitKind::Let(pattern, ty, _, expression) => {
                    let ty = ty.as_ref().map(|ty| quote! {:#ty});
                    let Some(body) = self.fragment_after_sequence(children, current)? else {
                        return Ok(None);
                    };
                    Ok(Some(quote! {{let #pattern #ty = #expression; #body}}))
                }
                SplitKind::If(condition) => {
                    let then_branch = self.fragment_after(&children[0], current.clone())?;
                    let else_branch = match children.get(1) {
                        Some(child) => self.fragment_after(child, current.clone())?,
                        None => None,
                    };
                    if then_branch.is_none() && else_branch.is_none() {
                        return Ok(None);
                    }
                    let then_branch = then_branch.unwrap_or(current.clone());
                    let else_branch = else_branch.unwrap_or(current);
                    Ok(Some(quote! {if #condition {#then_branch} else {#else_branch}}))
                }
                SplitKind::Match(expression, arms) => {
                    let bodies = children
                        .iter()
                        .map(|child| self.fragment_after(child, current.clone()))
                        .collect::<Result<Vec<_>, Error>>()?;
                    if bodies.iter().all(|b| b.is_none()) {
                        return Ok(None);
                    }
                    let cases: Vec<_> = arms
                        .iter()
                        .zip(bodies)
                        .map(|(arm, body)| {
                            let pattern = &arm.pat;
                            let guard =
                                arm.guard.as_ref().map(|(keyword, expr)| quote! {#keyword #expr});
                            let body = body.unwrap_or(current.clone());
                            quote! {#pattern #guard => {#body}}
                        })
                        .collect();
                    Ok(Some(quote! {match #expression {#(#cases),*}}))
                }
                SplitKind::Special(name, operation, _, pattern) => {
                    let field = self.fields.get(&name.to_string()).ok_or_else(|| {
                        Error::new(*span, "ownership operation refers to an unknown field")
                    })?;
                    if is_monoid_type(&field.stype) {
                        let (_, value) =
                            self.observed_operand(field, operation, &current, *span)?;
                        let value_ident = self.fresh("value");
                        let observed_value = value;
                        let value = quote! {#value_ident};
                        let next = self.next_fragment(field, operation, current, &value);
                        let body =
                            self.fragment_after_sequence(children, next.clone())?.unwrap_or(next);
                        let scoped = match pattern {
                            Some(pattern) => bind_pattern(
                                pattern,
                                bound_value(field, operation, value, *span)?,
                                body,
                            ),
                            None => body,
                        };
                        let value_type = operand_type(&field.stype);
                        Ok(Some(
                            quote! {{let #value_ident: #value_type = #observed_value; #scoped}},
                        ))
                    } else {
                        // Storage: as in `statement` (its binding observes the state).
                        let Some(body) = self.fragment_after_sequence(children, current)? else {
                            return Ok(None);
                        };
                        match pattern {
                            Some(pattern) => {
                                let observed = match &operation.elt {
                                    MonoidElt::OptionSome(None) => quote! {pre.#name->Some_0},
                                    MonoidElt::SingletonKV(key, None) => quote! {pre.#name[#key]},
                                    _ => {
                                        return Err(Error::new(
                                            *span,
                                            "unsupported storage ownership binding",
                                        ));
                                    }
                                };
                                Ok(Some(bind_pattern(pattern, observed, body)))
                            }
                            None => Ok(Some(body)),
                        }
                    }
                }
            },
            _ => Ok(None),
        }
    }

    /// `fragment_after` of a statement sequence.
    fn fragment_after_sequence(
        &mut self,
        statements: &[TransitionStmt],
        current: TokenStream,
    ) -> Result<Option<TokenStream>, Error> {
        let mut result = None;
        for statement in statements {
            if self.preserves_owned(statement) {
                continue;
            }
            let input = result.clone().unwrap_or_else(|| current.clone());
            if let Some(next) = self.fragment_after(statement, input)? {
                result = Some(next);
            }
        }
        Ok(result)
    }
}

/// The value a pattern of a monoid statement binds, given its bound operand `value`.
fn bound_value(
    field: &Field,
    operation: &SpecialOp,
    value: TokenStream,
    span: Span,
) -> Result<TokenStream, Error> {
    Ok(match field.stype {
        ShardableType::Option(_) | ShardableType::PersistentOption(_) => {
            quote! {(#value)->Some_0}
        }
        ShardableType::Map(..)
        | ShardableType::IMap(..)
        | ShardableType::PersistentMap(..)
        | ShardableType::PersistentIMap(..) => {
            let key = match &operation.elt {
                MonoidElt::SingletonKV(key, _) => key,
                _ => {
                    return Err(Error::new(span, "map bindings require singleton operands"));
                }
            };
            quote! {(#value)[#key]}
        }
        _ => value,
    })
}

/// The ordered ownership condition of `statement`: each `remove` and `have` finds its
/// operand in the owned fragment (a `have` also in `shared`).
pub(crate) fn ownership_condition(
    statement: &TransitionStmt,
    fields: &HashMap<String, Field>,
    fragment_type: &TokenStream,
    initial_owned: TokenStream,
    shared: TokenStream,
) -> Result<TokenStream, Error> {
    let shared_ident = format_ident!("__tsm_ownership_shared", span = Span::mixed_site());
    let initial_ident = format_ident!("__tsm_ownership_initial", span = Span::mixed_site());
    let mut compiler =
        Compiler { fields, fragment: fragment_type, shared: shared_ident.clone(), next_ident: 0 };
    let Some(pair) = compiler.statement(statement, quote! {#initial_ident})? else {
        return Ok(quote! {true});
    };
    Ok(quote! {{
        let #shared_ident = #shared;
        let #initial_ident = #initial_owned;
        (#pair).0
    }})
}
