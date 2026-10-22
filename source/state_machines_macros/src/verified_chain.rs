//! The chain emitter of the statement calculus (`vstd::resource::tsm_calculus`).
//!
//! For a transition whose statements the calculus covers (`supported`), `Chain` walks the
//! statement tree that the ownership compiler (`verified_ownership`) walks and emits one
//! step-lemma call per `remove`, `have` and `add`, on ground terms: the component of the
//! owned fragment the statement observes (the ownership compiler's `next_fragment` and
//! `observed_value` terms, so that each lemma's ownership precondition is literally one
//! conjunct of `<t>_owners_enabled`), the borrowed fragment, the completion frame, and
//! the field's intermediate value (the frontend's `expr_remove`/`expr_add` terms, so that
//! each lemma's enabling postcondition is literally one conjunct of `<t>_enabled`). The
//! configuration of every field starts from the machine's `__tsm_cfg_split`. An `add`'s
//! safety condition (and a user `assert`) guards the rest of the chain, as `tmp_assert`
//! guards the rest of the enabling condition; an `if`/`match` joins its arms' (fragment,
//! values, safety) tuples, and its continuation follows once. The generated proof has no
//! quantifier: all of them are inside the vstd lemmas.
use crate::ast::*;
use crate::verified_monoids::{bind_pattern, operand_type};
use crate::verified_ownership::{bound_value, next_fragment, observed_value};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use std::collections::HashMap;
use verus_syn::{Error, Expr, Ident};

/// The field kinds the calculus covers: every monoid kind.
fn covered(stype: &ShardableType) -> bool {
    crate::verified_monoids::is_monoid_type(stype)
}

/// Whether the calculus covers every `remove`, `have` and `add` of `stmt` (a storage
/// operation needs no step: see `Chain::storage`).
pub(crate) fn supported(stmt: &TransitionStmt, fields: &HashMap<String, Field>) -> bool {
    match stmt {
        TransitionStmt::Block(_, children) => children.iter().all(|c| supported(c, fields)),
        TransitionStmt::Split(_, kind, children) => {
            let here = match &**kind {
                SplitKind::Special(name, operation, _, _) => {
                    operation.stmt.is_for_storage()
                        || fields.get(&name.to_string()).is_some_and(|f| covered(&f.stype))
                            && matches!(
                                operation.stmt,
                                MonoidStmtType::Remove | MonoidStmtType::Have | MonoidStmtType::Add(_)
                            )
                }
                _ => true,
            };
            here && children.iter().all(|c| supported(c, fields))
        }
        _ => true,
    }
}

/// Whether `tr`'s readiness proof uses the chain: the calculus covers its statements
/// (`supported`; every monoid kind and the storage operations) and it has a `remove` or `have` of a collection field (a map, set or
/// multiset, exclusive or persistent). The enabling condition of a transition without one
/// follows from its ownership condition without any hint (an `option`, `count` or `bool`
/// observation is a fact about one component), and a chain would only add cost.
pub(crate) fn uses_chain(sm: &SM, tr: &Transition) -> bool {
    let fields: HashMap<_, _> = sm.fields.iter().map(|f| (f.name.to_string(), f.clone())).collect();
    tr.kind != TransitionKind::Init && supported(&tr.body, &fields) && observes_collection(&tr.body, &fields)
}

/// Whether `stmt` has a `remove` or `have` of a collection field.
fn observes_collection(stmt: &TransitionStmt, fields: &HashMap<String, Field>) -> bool {
    match stmt {
        TransitionStmt::Block(_, children) => children.iter().any(|c| observes_collection(c, fields)),
        TransitionStmt::Split(_, kind, children) => {
            let here = match &**kind {
                SplitKind::Special(name, operation, _, _) if operation.is_remove() || operation.is_have() => {
                    fields.get(&name.to_string()).is_some_and(|f| {
                        matches!(
                            f.stype,
                            ShardableType::Map(..)
                                | ShardableType::IMap(..)
                                | ShardableType::Set(_)
                                | ShardableType::ISet(_)
                                | ShardableType::Multiset(_)
                                | ShardableType::PersistentMap(..)
                                | ShardableType::PersistentIMap(..)
                                | ShardableType::PersistentSet(_)
                                | ShardableType::PersistentISet(_)
                        )
                    })
                }
                _ => false,
            };
            here || children.iter().any(|c| observes_collection(c, fields))
        }
        _ => false,
    }
}

/// The monoid fields that `stmt` modifies (`remove`, `add`), in field order.
fn modified<'a>(stmt: &TransitionStmt, sm: &'a SM) -> Vec<&'a Field> {
    fn walk(stmt: &TransitionStmt, out: &mut Vec<String>) {
        match stmt {
            TransitionStmt::Block(_, children) => children.iter().for_each(|c| walk(c, out)),
            TransitionStmt::Split(_, kind, children) => {
                if let SplitKind::Special(name, operation, _, _) = &**kind {
                    if operation.is_remove() || operation.is_add() {
                        out.push(name.to_string());
                    }
                }
                children.iter().for_each(|c| walk(c, out))
            }
            _ => {}
        }
    }
    let mut names = vec![];
    walk(stmt, &mut names);
    sm.fields.iter().filter(|f| names.contains(&f.name.to_string())).collect()
}

/// The chain's state between statements: the owned fragment, the values of the modified
/// fields (`Chain::tracked`), and the safety condition so far (`None`: `true`).
#[derive(Clone)]
struct Point {
    fragment: TokenStream,
    values: Vec<TokenStream>,
    ok: Option<TokenStream>,
}

struct Chain<'a> {
    fields: &'a HashMap<String, Field>,
    fragment_type: &'a TokenStream,
    shared: TokenStream,
    frame: TokenStream,
    tracked: Vec<&'a Field>,
    next: usize,
}

impl Chain<'_> {
    fn fresh(&mut self, purpose: &str) -> Ident {
        self.next += 1;
        format_ident!("__tsm_chain_{}_{}", purpose, self.next, span = Span::mixed_site())
    }

    /// The current value of `field` at `point`.
    fn value(&self, point: &Point, field: &Field) -> TokenStream {
        let n = &field.name;
        match self.tracked.iter().position(|f| f.name == field.name) {
            Some(i) => point.values[i].clone(),
            None => quote! {pre.#n},
        }
    }

    /// `body` guarded by the safety condition of `point`.
    fn guarded(point: &Point, body: TokenStream) -> TokenStream {
        match &point.ok {
            Some(ok) => quote! {if #ok {#body}},
            None => body,
        }
    }

    /// The tuple that a scope returns, and its pattern (fresh binders), and the point the
    /// pattern binds.
    fn export(&mut self, point: &Point) -> (TokenStream, TokenStream, Point) {
        let fragment = &point.fragment;
        let values = &point.values;
        let ok = point.ok.clone().unwrap_or(quote! {true});
        let tuple = quote! {(#fragment, #(#values,)* #ok)};
        let new_fragment = self.fresh("owned");
        let new_values: Vec<_> = (0..values.len()).map(|_| self.fresh("value")).collect();
        let new_ok = self.fresh("ok");
        let pattern = quote! {(#new_fragment, #(#new_values,)* #new_ok)};
        let point = Point {
            fragment: quote! {#new_fragment},
            values: new_values.iter().map(|v| quote! {#v}).collect(),
            ok: Some(quote! {#new_ok}),
        };
        (tuple, pattern, point)
    }

    fn sequence(&mut self, statements: &[TransitionStmt], point: Point) -> Result<(TokenStream, Point), Error> {
        let mut code = vec![];
        let mut point = point;
        for statement in statements {
            let (c, p) = self.statement(statement, point)?;
            code.push(c);
            point = p;
        }
        Ok((quote! {#(#code)*}, point))
    }

    /// A scope (`let`, a pattern) over `children`: `prefix` binds its names.
    fn scope(&mut self, prefix: TokenStream, children: &[TransitionStmt], point: Point)
        -> Result<(TokenStream, Point), Error>
    {
        let (body, end) = self.sequence(children, point)?;
        if body.is_empty() {
            return Ok((quote! {}, end));
        }
        let (tuple, pattern, after) = self.export(&end);
        Ok((quote! {let #pattern = {#prefix #body #tuple};}, after))
    }

    fn statement(&mut self, stmt: &TransitionStmt, point: Point) -> Result<(TokenStream, Point), Error> {
        match stmt {
            TransitionStmt::Block(_, children) => self.sequence(children, point),
            TransitionStmt::Assert(_, condition, _) => {
                let ok = self.fresh("ok");
                let previous = point.ok.clone().unwrap_or(quote! {true});
                let code = quote! {let #ok = #previous && (#condition);};
                Ok((code, Point { ok: Some(quote! {#ok}), ..point }))
            }
            TransitionStmt::Split(span, kind, children) => match &**kind {
                SplitKind::Let(pattern, ty, _, expression) => {
                    let ty = ty.as_ref().map(|ty| quote! {:#ty});
                    self.scope(quote! {let #pattern #ty = #expression;}, children, point)
                }
                SplitKind::If(condition) => {
                    let (then_code, then_end) = self.statement(&children[0], point.clone())?;
                    let (else_code, else_end) = match children.get(1) {
                        Some(child) => self.statement(child, point.clone())?,
                        None => (quote! {}, point.clone()),
                    };
                    if then_code.is_empty() && else_code.is_empty() {
                        return Ok((quote! {}, point));
                    }
                    let (then_tuple, pattern, after) = self.export(&then_end);
                    let (else_tuple, _, _) = self.export(&else_end);
                    Ok((
                        quote! {let #pattern = if #condition {#then_code #then_tuple} else {#else_code #else_tuple};},
                        after,
                    ))
                }
                SplitKind::Match(expression, arms) => {
                    if arms.len() != children.len() {
                        return Err(Error::new(*span, "chain match has mismatched arms"));
                    }
                    let mut bodies = vec![];
                    for child in children {
                        bodies.push(self.statement(child, point.clone())?);
                    }
                    if bodies.iter().all(|(code, _)| code.is_empty()) {
                        return Ok((quote! {}, point));
                    }
                    let mut pattern = quote! {};
                    let mut after = point.clone();
                    let mut cases = vec![];
                    for (index, (arm, (code, end))) in arms.iter().zip(bodies).enumerate() {
                        let (tuple, p, a) = self.export(&end);
                        if index == 0 {
                            pattern = p;
                            after = a;
                        }
                        let arm_pattern = &arm.pat;
                        let guard = arm.guard.as_ref().map(|(keyword, e)| quote! {#keyword #e});
                        cases.push(quote! {#arm_pattern #guard => {#code #tuple}});
                    }
                    Ok((quote! {let #pattern = match #expression {#(#cases),*};}, after))
                }
                SplitKind::Special(name, operation, _, pattern) => {
                    let field = self.fields.get(&name.to_string()).ok_or_else(|| {
                        Error::new(*span, "chain operation refers to an unknown field")
                    })?;
                    if operation.stmt.is_for_storage() {
                        return self.storage(field, operation, pattern.as_deref(), children, point, *span);
                    }
                    self.special(field, operation, pattern.as_deref(), children, point, *span)
                }
            },
            _ => Ok((quote! {}, point)),
        }
    }

    /// A `deposit`, `withdraw` or `guard`, then `children`. Its condition is an
    /// `assert` of the transition (a safety condition, which the enabling condition does
    /// not require), and it changes no monoid component: it contributes only the binding
    /// of its pattern, from the state as in the ownership condition.
    fn storage(
        &mut self,
        field: &Field,
        operation: &SpecialOp,
        pattern: Option<&verus_syn::Pat>,
        children: &[TransitionStmt],
        point: Point,
        span: Span,
    ) -> Result<(TokenStream, Point), Error> {
        let name = &field.name;
        let (body, end) = self.sequence(children, point)?;
        match pattern {
            Some(pattern) if !body.is_empty() => {
                let observed = match &operation.elt {
                    MonoidElt::OptionSome(None) => quote! {pre.#name->Some_0},
                    MonoidElt::SingletonKV(key, None) => quote! {pre.#name[#key]},
                    _ => return Err(Error::new(span, "unsupported storage binding")),
                };
                let (tuple, tuple_pattern, after) = self.export(&end);
                let bound_body = bind_pattern(pattern, observed, quote! {{#body #tuple}});
                Ok((quote! {let #tuple_pattern = #bound_body;}, after))
            }
            _ => Ok((body, end)),
        }
    }

    /// The lemma call of a `remove`, `have` or `add` on `field`, then `children`.
    fn special(
        &mut self,
        field: &Field,
        operation: &SpecialOp,
        pattern: Option<&verus_syn::Pat>,
        children: &[TransitionStmt],
        point: Point,
        span: Span,
    ) -> Result<(TokenStream, Point), Error> {
        let n = &field.name;
        let ft = self.fragment_type;
        let shared = self.shared.clone();
        let frame = self.frame.clone();
        let current = point.fragment.clone();
        let observer = match operation.stmt {
            MonoidStmtType::Have => quote! {<#ft>::op(#current, #shared)},
            _ => current.clone(),
        };
        let observed = observed_value(field, operation, &observer, span)?;
        let value_ident = self.fresh("operand");
        let value = quote! {#value_ident};
        let value_type = operand_type(&field.stype);
        let state = self.value(&point, field);
        let cur = Expr::Verbatim(state.clone());
        let c = quote! {::vstd::resource::tsm_calculus};
        // The lemma's operand arguments, after (o, h, z, v).
        use ShardableType as T;
        let finite = matches!(field.stype, T::Map(..) | T::Set(_) | T::PersistentMap(..) | T::PersistentSet(_));
        // The lemma family, whether the operand is a singleton (`_one`, `_some`) or `true`
        // (`_true`), and the lemma's operand arguments after (o, h, z, v).
        let (lemma_kind, single, arguments): (&str, Option<&str>, TokenStream) = match (&field.stype, &operation.elt) {
            (T::Map(..) | T::IMap(..), MonoidElt::SingletonKV(key, explicit)) => {
                let x = match explicit {
                    Some(x) => quote! {#x},
                    None => quote! {(#observer).#n.at(#key)->Some_0->Exclusive_0},
                };
                (if finite { "map" } else { "imap" }, Some("_one"), quote! {#key, #x})
            }
            (T::PersistentMap(..) | T::PersistentIMap(..), MonoidElt::SingletonKV(key, explicit)) => {
                let x = match explicit {
                    Some(x) => quote! {#x},
                    None => quote! {(#observer).#n.at(#key)->Some_0->Agree_0},
                };
                (if finite { "pmap" } else { "pimap" }, Some("_one"), quote! {#key, #x})
            }
            (T::Map(..) | T::IMap(..), MonoidElt::General(e)) => {
                (if finite { "map" } else { "imap" }, None, quote! {#e})
            }
            (T::PersistentMap(..) | T::PersistentIMap(..), MonoidElt::General(e)) => {
                (if finite { "pmap" } else { "pimap" }, None, quote! {#e})
            }
            (T::Set(_) | T::ISet(_), MonoidElt::SingletonSet(e)) => {
                (if finite { "set" } else { "iset" }, Some("_one"), quote! {#e})
            }
            (T::PersistentSet(_) | T::PersistentISet(_), MonoidElt::SingletonSet(e)) => {
                (if finite { "pset" } else { "piset" }, Some("_one"), quote! {#e})
            }
            (T::Set(_) | T::ISet(_), MonoidElt::General(e)) => {
                (if finite { "set" } else { "iset" }, None, quote! {#e})
            }
            (T::PersistentSet(_) | T::PersistentISet(_), MonoidElt::General(e)) => {
                (if finite { "pset" } else { "piset" }, None, quote! {#e})
            }
            (T::Option(_), MonoidElt::OptionSome(Some(e))) => ("opt", Some("_some"), quote! {#e}),
            (T::Option(_), MonoidElt::OptionSome(None)) => {
                ("opt", Some("_some"), quote! {(#observer).#n->Some_0->Exclusive_0})
            }
            (T::Option(_), MonoidElt::General(e)) => ("opt", None, quote! {#e}),
            (T::PersistentOption(_), MonoidElt::OptionSome(Some(e))) => ("popt", Some("_some"), quote! {#e}),
            (T::PersistentOption(_), MonoidElt::OptionSome(None)) => {
                ("popt", Some("_some"), quote! {(#observer).#n->Some_0->Agree_0})
            }
            (T::PersistentOption(_), MonoidElt::General(e)) => ("popt", None, quote! {#e}),
            (T::Multiset(_), MonoidElt::SingletonMultiset(e)) => ("mset", Some("_one"), quote! {#e}),
            (T::Multiset(_), MonoidElt::General(e)) => ("mset", None, quote! {#e}),
            (T::Count, MonoidElt::General(e)) => ("count", None, quote! {#e}),
            (T::PersistentCount, MonoidElt::General(e)) => ("pcount", None, quote! {#e}),
            (T::Bool, MonoidElt::True) => ("bool", Some("_true"), quote! {}),
            (T::Bool, MonoidElt::General(e)) => ("bool", None, quote! {#e}),
            (T::PersistentBool, MonoidElt::True) => ("pbool", Some("_true"), quote! {}),
            (T::PersistentBool, MonoidElt::General(e)) => ("pbool", None, quote! {#e}),
            _ => return Err(Error::new(span, "the statement calculus does not cover this operation")),
        };
        let op_name = match operation.stmt {
            MonoidStmtType::Remove => "remove",
            MonoidStmtType::Have => "have",
            MonoidStmtType::Add(_) => "add",
            _ => return Err(Error::new(span, "the statement calculus does not cover this operation")),
        };
        let lemma = format_ident!("{}_{}{}", lemma_kind, op_name, single.unwrap_or(""));
        let arguments = if arguments.is_empty() { quote! {} } else { quote! {, #arguments} };
        let mut code = vec![quote! {let #value_ident: #value_type = #observed;}];
        let mut point = point;
        // An `add`'s safety condition guards it and the rest of the chain.
        if operation.is_add() {
            if let Some(safety) = crate::simplification::expr_can_add(&field.stype, &cur, &operation.elt) {
                let ok = self.fresh("ok");
                let previous = point.ok.clone().unwrap_or(quote! {true});
                code.push(quote! {let #ok = #previous && (#safety);});
                point.ok = Some(quote! {#ok});
            }
        }
        code.push(Self::guarded(
            &point,
            quote! {#c::#lemma((#current).#n, (#shared).#n, (#frame).#n, #state #arguments);},
        ));
        // The fragment and the value the statement leaves.
        if !operation.is_have() {
            point.fragment = next_fragment(ft, field, operation, current, &value);
            let updated = if operation.is_remove() {
                crate::simplification::expr_remove(&field.stype, &cur, &operation.elt)
            } else {
                crate::simplification::expr_add(&field.stype, &cur, &operation.elt)
            };
            let i = self.tracked.iter().position(|f| f.name == field.name).unwrap();
            point.values[i] = quote! {#updated};
            // Name both, so that later terms stay small.
            let (o, v) = (self.fresh("owned"), self.fresh("value"));
            let (fragment, value) = (&point.fragment, &point.values[i]);
            code.push(quote! {let #o = #fragment; let #v = #value;});
            point.fragment = quote! {#o};
            point.values[i] = quote! {#v};
        }
        let (body, end) = self.sequence(children, point)?;
        match pattern {
            // The pattern's binders scope over the rest (as in the transition).
            Some(pattern) if !body.is_empty() => {
                let bound = bound_value(field, operation, value, span)?;
                let (tuple, tuple_pattern, after) = self.export(&end);
                let bound_body = bind_pattern(pattern, bound, quote! {{#body #tuple}});
                code.push(quote! {let #tuple_pattern = #bound_body;});
                Ok((quote! {#(#code)*}, after))
            }
            _ => {
                code.push(body);
                Ok((quote! {#(#code)*}, end))
            }
        }
    }
}

/// The chain of `tr`'s body inside a completion quantifier over `frame` (the completion
/// frame) and `state` (the completion state, bound to `pre` for the transition's
/// expressions), from the owned fragment `owned` and the borrowed fragment `shared`;
/// `split` is the machine's configuration split (`Protocol::__tsm_cfg_split`).
pub(crate) fn chain(
    sm: &SM,
    tr: &Transition,
    fragment_type: &TokenStream,
    split: &TokenStream,
    owned: TokenStream,
    shared: TokenStream,
    frame: &Ident,
    state: &Ident,
) -> Result<TokenStream, Error> {
    let fields: HashMap<_, _> = sm.fields.iter().map(|f| (f.name.to_string(), f.clone())).collect();
    let tracked = modified(&tr.body, sm);
    let mut chain = Chain {
        fields: &fields,
        fragment_type,
        shared: shared.clone(),
        frame: quote! {#frame},
        tracked: tracked.clone(),
        next: 0,
    };
    let start = Point {
        fragment: owned.clone(),
        values: tracked.iter().map(|f| {
            let n = &f.name;
            quote! {pre.#n}
        }).collect(),
        ok: None,
    };
    let (body, _) = chain.sequence(std::slice::from_ref(&tr.body), start)?;
    let pre = format_ident!("pre");
    Ok(quote! {
        let #pre = #state;
        #split(#owned, #shared, #frame, #pre);
        #body
    })
}
