//! The chain emitter of the statement calculus (`vstd::resource::tsm_calculus`).
//!
//! `Chain` walks the statement tree that the ownership compiler (`verified_ownership`)
//! walks and emits one step-lemma call per `remove`, `have` and `add`, on ground terms:
//! the component of the owned fragment the statement observes (the ownership compiler's
//! `next_fragment` and `observed_value` terms, so that each lemma's ownership
//! precondition is literally one conjunct of `<t>_owners_enabled`), the borrowed
//! fragment, the completion frame, and the field's intermediate value (the frontend's
//! `expr_remove`/`expr_add` terms, so that each lemma's enabling postcondition is
//! literally one conjunct of `<t>_enabled`). The configuration of every field starts
//! from the machine's `__tsm_cfg_split`. An `add`'s safety condition guards the later
//! steps of its field (the enabling condition guards its later conditions by all
//! safety conditions, `tmp_assert`); an `if`/`match` joins its arms' (fragment,
//! values, safety) tuples, and its continuation follows once. The generated proof has
//! no quantifier: all of them are inside the vstd lemmas.
use crate::ast::*;
use crate::verified_monoids::{bind_pattern, operand_type};
use crate::verified_ownership::{bound_value, next_fragment, observed_value};
use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use std::collections::{HashMap, HashSet};
use verus_syn::{Error, Expr, Ident};

/// Whether `stype` is a collection kind: a map, set or multiset, exclusive or persistent.
fn collection(stype: &ShardableType) -> bool {
    matches!(
        stype,
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
}

/// Whether `stype` is a counting kind (`count`, `bool` and their persistent versions),
/// whose component is a number: a frame proves its output component by arithmetic, as
/// cheaply as a chain step would (`__tsm_cfg_join` takes its plain equality).
pub(crate) fn counting(stype: &ShardableType) -> bool {
    matches!(
        stype,
        ShardableType::Count
            | ShardableType::Bool
            | ShardableType::PersistentCount
            | ShardableType::PersistentBool
    )
}

/// Whether `tr`'s readiness proof uses the chain: it has a `remove` or `have` of a
/// collection field. (The calculus covers every statement form: every monoid kind, and
/// the storage operations need no step, see `Chain::storage`.) The enabling condition
/// of a transition without one follows from its ownership condition without any hint
/// (an `option`, `count` or `bool` observation is a fact about one component), and a
/// chain would only add cost. (In a chain, too, the `count` and `bool` steps cost more
/// than such a proof does, 1.2 to 1.8 times in the corpus: their configurations carry the
/// ownership compiler's `(o.count - x) as nat` terms.)
pub(crate) fn uses_chain(sm: &SM, tr: &Transition) -> bool {
    fn observes(stmt: &TransitionStmt, sm: &SM) -> bool {
        match stmt {
            TransitionStmt::Block(_, children) => children.iter().any(|c| observes(c, sm)),
            TransitionStmt::Split(_, kind, children) => {
                let here = match &**kind {
                    SplitKind::Special(name, operation, _, _)
                        if operation.is_remove() || operation.is_have() =>
                    {
                        sm.fields.iter().any(|f| f.name == *name && collection(&f.stype))
                    }
                    _ => false,
                };
                here || children.iter().any(|c| observes(c, sm))
            }
            _ => false,
        }
    }
    tr.kind != TransitionKind::Init && observes(&tr.body, sm)
}

/// The `add`s of `statements` whose field a later `remove` or `have` observes (on some
/// path), given the fields observed after `statements` (`after`); returns the fields
/// observed in `statements` or after them. Only these `add`s need their step in a
/// readiness chain: the configuration an `add` leaves is used by its field's later steps
/// only.
fn observed_later(
    statements: &[TransitionStmt],
    after: HashSet<String>,
    needed: &mut HashSet<*const TransitionStmt>,
) -> HashSet<String> {
    let mut later = after;
    for statement in statements.iter().rev() {
        later = match statement {
            TransitionStmt::Block(_, children) => observed_later(children, later, needed),
            TransitionStmt::Split(_, kind, children) => match &**kind {
                SplitKind::If(_) | SplitKind::Match(..) => {
                    let mut joined = later.clone();
                    for child in children {
                        joined.extend(observed_later(
                            std::slice::from_ref(child),
                            later.clone(),
                            needed,
                        ));
                    }
                    joined
                }
                SplitKind::Let(..) => observed_later(children, later, needed),
                SplitKind::Special(name, operation, _, _) => {
                    let mut inner = observed_later(children, later, needed);
                    if operation.is_add() && inner.contains(&name.to_string()) {
                        needed.insert(statement as *const TransitionStmt);
                    }
                    if operation.is_remove() || operation.is_have() {
                        inner.insert(name.to_string());
                    }
                    inner
                }
            },
            _ => later,
        };
    }
    later
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

/// The chain's state between statements: the owned fragment, and the values of the
/// modified fields (`Chain::tracked`) with the safety condition of each one's steps so
/// far (`None`: `true`).
#[derive(Clone)]
struct Point {
    fragment: TokenStream,
    values: Vec<TokenStream>,
    oks: Vec<Option<TokenStream>>,
}

struct Chain<'a> {
    fields: &'a HashMap<String, Field>,
    fragment_type: &'a TokenStream,
    shared: TokenStream,
    frame: TokenStream,
    tracked: Vec<&'a Field>,
    next: usize,
    /// The `add`s whose step is needed (see `observed_later`); `None`: all of them.
    needed: Option<HashSet<*const TransitionStmt>>,
    /// A frame's chain: a `have` changes no configuration, and the strong relation holds,
    /// so it needs no step.
    frame_mode: bool,
}

impl Chain<'_> {
    fn fresh(&mut self, purpose: &str) -> Ident {
        self.next += 1;
        format_ident!("__tsm_chain_{}_{}", purpose, self.next, span = Span::mixed_site())
    }

    /// The position of `field` in `tracked`.
    fn index(&self, field: &Field) -> Option<usize> {
        self.tracked.iter().position(|f| f.name == field.name)
    }

    /// `body` guarded by the safety condition `ok`.
    fn guarded(ok: &Option<TokenStream>, body: TokenStream) -> TokenStream {
        match ok {
            Some(ok) => quote! {if #ok {#body}},
            None => body,
        }
    }

    /// The tuple that a scope returns, and its pattern (fresh binders), and the point the
    /// pattern binds.
    fn export(&mut self, point: &Point) -> (TokenStream, TokenStream, Point) {
        let fragment = &point.fragment;
        let values = &point.values;
        let oks: Vec<_> = point.oks.iter().map(|ok| ok.clone().unwrap_or(quote! {true})).collect();
        let tuple = quote! {(#fragment, #(#values,)* #(#oks,)*)};
        let new_fragment = self.fresh("owned");
        let new_values: Vec<_> = (0..values.len()).map(|_| self.fresh("value")).collect();
        let new_oks: Vec<_> = (0..values.len()).map(|_| self.fresh("ok")).collect();
        let pattern = quote! {(#new_fragment, #(#new_values,)* #(#new_oks,)*)};
        let point = Point {
            fragment: quote! {#new_fragment},
            values: new_values.iter().map(|v| quote! {#v}).collect(),
            oks: new_oks.iter().map(|ok| Some(quote! {#ok})).collect(),
        };
        (tuple, pattern, point)
    }

    fn sequence(
        &mut self,
        statements: &[TransitionStmt],
        point: Point,
    ) -> Result<(TokenStream, Point), Error> {
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
    fn scope(
        &mut self,
        prefix: TokenStream,
        children: &[TransitionStmt],
        point: Point,
    ) -> Result<(TokenStream, Point), Error> {
        let (body, end) = self.sequence(children, point)?;
        if body.is_empty() {
            return Ok((quote! {}, end));
        }
        let (tuple, pattern, after) = self.export(&end);
        Ok((quote! {let #pattern = {#prefix #body #tuple};}, after))
    }

    fn statement(
        &mut self,
        stmt: &TransitionStmt,
        point: Point,
    ) -> Result<(TokenStream, Point), Error> {
        match stmt {
            TransitionStmt::Block(_, children) => self.sequence(children, point),
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
                    let join = quote! {
                        let #pattern = if #condition {#then_code #then_tuple}
                            else {#else_code #else_tuple};
                    };
                    Ok((join, after))
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
                        return self.storage(
                            field,
                            operation,
                            pattern.as_deref(),
                            children,
                            point,
                            *span,
                        );
                    }
                    self.special(stmt, field, operation, pattern.as_deref(), children, point, *span)
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
        stmt: &TransitionStmt,
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
        let index = self.index(field);
        let state = match index {
            Some(i) => point.values[i].clone(),
            None => quote! {pre.#n},
        };
        let cur = Expr::Verbatim(state.clone());
        let c = quote! {::vstd::resource::tsm_calculus};
        // The lemma's operand arguments, after (o, h, z, v).
        use ShardableType as T;
        let finite = matches!(
            field.stype,
            T::Map(..) | T::Set(_) | T::PersistentMap(..) | T::PersistentSet(_)
        );
        // The lemma family, whether the operand is a singleton (`_one`, `_some`) or `true`
        // (`_true`), and the lemma's operand arguments after (o, h, z, v).
        let (lemma_kind, single, arguments): (&str, Option<&str>, TokenStream) =
            match (&field.stype, &operation.elt) {
                (T::Map(..) | T::IMap(..), MonoidElt::SingletonKV(key, explicit)) => {
                    let x = match explicit {
                        Some(x) => quote! {#x},
                        None => quote! {(#observer).#n.at(#key)->Some_0->Exclusive_0},
                    };
                    (if finite { "map" } else { "imap" }, Some("_one"), quote! {#key, #x})
                }
                (
                    T::PersistentMap(..) | T::PersistentIMap(..),
                    MonoidElt::SingletonKV(key, explicit),
                ) => {
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
                (T::Option(_), MonoidElt::OptionSome(Some(e))) => {
                    ("opt", Some("_some"), quote! {#e})
                }
                (T::Option(_), MonoidElt::OptionSome(None)) => {
                    ("opt", Some("_some"), quote! {(#observer).#n->Some_0->Exclusive_0})
                }
                (T::Option(_), MonoidElt::General(e)) => ("opt", None, quote! {#e}),
                (T::PersistentOption(_), MonoidElt::OptionSome(Some(e))) => {
                    ("popt", Some("_some"), quote! {#e})
                }
                (T::PersistentOption(_), MonoidElt::OptionSome(None)) => {
                    ("popt", Some("_some"), quote! {(#observer).#n->Some_0->Agree_0})
                }
                (T::PersistentOption(_), MonoidElt::General(e)) => ("popt", None, quote! {#e}),
                (T::Multiset(_), MonoidElt::SingletonMultiset(e)) => {
                    ("mset", Some("_one"), quote! {#e})
                }
                (T::Multiset(_), MonoidElt::General(e)) => ("mset", None, quote! {#e}),
                (T::Count, MonoidElt::General(e)) => ("count", None, quote! {#e}),
                (T::PersistentCount, MonoidElt::General(e)) => ("pcount", None, quote! {#e}),
                (T::Bool, MonoidElt::True) => ("bool", Some("_true"), quote! {}),
                (T::Bool, MonoidElt::General(e)) => ("bool", None, quote! {#e}),
                (T::PersistentBool, MonoidElt::True) => ("pbool", Some("_true"), quote! {}),
                (T::PersistentBool, MonoidElt::General(e)) => ("pbool", None, quote! {#e}),
                _ => {
                    return Err(Error::new(
                        span,
                        "the statement calculus does not cover this operation",
                    ));
                }
            };
        let op_name = match operation.stmt {
            MonoidStmtType::Remove => "remove",
            MonoidStmtType::Have => "have",
            MonoidStmtType::Add(_) => "add",
            _ => {
                return Err(Error::new(
                    span,
                    "the statement calculus does not cover this operation",
                ));
            }
        };
        let lemma = format_ident!("{}_{}{}", lemma_kind, op_name, single.unwrap_or(""));
        let arguments = if arguments.is_empty() {
            quote! {}
        } else {
            quote! {, #arguments}
        };
        let mut code = vec![quote! {let #value_ident: #value_type = #observed;}];
        let mut point = point;
        // An `add` needs its step only if a later step of its field uses its
        // configuration; its safety condition guards it and its field's later steps.
        let step = if self.frame_mode && counting(&field.stype) {
            false
        } else if operation.is_have() {
            // In a frame, a `have` needs its step only for the agreement of the value its
            // pattern binds (`owned_post` reads it from the state).
            !self.frame_mode || pattern.is_some()
        } else {
            !operation.is_add()
                || self
                    .needed
                    .as_ref()
                    .is_none_or(|needed| needed.contains(&(stmt as *const TransitionStmt)))
        };
        if step {
            if operation.is_add() {
                if let Some(safety) =
                    crate::simplification::expr_can_add(&field.stype, &cur, &operation.elt)
                {
                    let i = index.unwrap();
                    let ok = self.fresh("ok");
                    let condition = match &point.oks[i] {
                        Some(previous) => quote! {#previous && (#safety)},
                        None => quote! {#safety},
                    };
                    code.push(quote! {let #ok = #condition;});
                    point.oks[i] = Some(quote! {#ok});
                }
            }
            let ok = index.and_then(|i| point.oks[i].clone());
            code.push(Self::guarded(
                &ok,
                quote! {#c::#lemma((#current).#n, (#shared).#n, (#frame).#n, #state #arguments);},
            ));
        }
        // The fragment and the value the statement leaves.
        if !operation.is_have() {
            point.fragment = next_fragment(ft, field, operation, current, &value);
            let updated = if operation.is_remove() {
                crate::simplification::expr_remove(&field.stype, &cur, &operation.elt)
            } else {
                crate::simplification::expr_add(&field.stype, &cur, &operation.elt)
            };
            let i = index.unwrap();
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
    chain_of(sm, tr, fragment_type, split, owned, shared, frame, state, false)
}

/// `chain`; in `frame_mode` (`frame_chain`), with every `add`'s step and no `have`'s.
fn chain_of(
    sm: &SM,
    tr: &Transition,
    fragment_type: &TokenStream,
    split: &TokenStream,
    owned: TokenStream,
    shared: TokenStream,
    frame: &Ident,
    state: &Ident,
    frame_mode: bool,
) -> Result<TokenStream, Error> {
    let fields: HashMap<_, _> = sm.fields.iter().map(|f| (f.name.to_string(), f.clone())).collect();
    let tracked = modified(&tr.body, sm);
    let mut needed = HashSet::new();
    observed_later(std::slice::from_ref(&tr.body), HashSet::new(), &mut needed);
    // The fragments under hygienic names: a pattern of the transition may bind `owned`,
    // `h` or `z`.
    let (owned_name, shared_name, frame_name) = (
        format_ident!("__tsm_chain_owned", span = Span::mixed_site()),
        format_ident!("__tsm_chain_shared", span = Span::mixed_site()),
        format_ident!("__tsm_chain_frame", span = Span::mixed_site()),
    );
    let mut chain = Chain {
        fields: &fields,
        fragment_type,
        shared: quote! {#shared_name},
        frame: quote! {#frame_name},
        tracked: tracked.clone(),
        next: 0,
        needed: if frame_mode { None } else { Some(needed) },
        frame_mode,
    };
    let start = Point {
        fragment: quote! {#owned_name},
        values: tracked
            .iter()
            .map(|f| {
                let n = &f.name;
                quote! {pre.#n}
            })
            .collect(),
        oks: tracked.iter().map(|_| None).collect(),
    };
    let (body, _) = chain.sequence(std::slice::from_ref(&tr.body), start)?;
    let pre = format_ident!("pre");
    Ok(quote! {
        let #pre = #state;
        let #owned_name = #owned;
        let #shared_name = #shared;
        let #frame_name = #frame;
        #split(#owned_name, #shared_name, #frame_name, #pre);
        #body
    })
}

/// The owned fragment after `statements` from the fragment named `current` (`None`:
/// `current`), as the chain's fragments: the fragment component of `<t>_owned_post`. The
/// implicit value a `have`'s pattern binds is read from the state `pre` (as the frontend
/// binds it), as `owned_post` does not see the borrowed fragment. Each intermediate
/// fragment is named, so that no term is repeated.
fn post_sequence(
    statements: &[TransitionStmt],
    fields: &HashMap<String, Field>,
    fragment_type: &TokenStream,
    current: TokenStream,
    next: &mut usize,
) -> Result<Option<TokenStream>, Error> {
    for (index, statement) in statements.iter().enumerate() {
        if let Some(after) = post_fragment(statement, fields, fragment_type, current.clone(), next)?
        {
            *next += 1;
            let name = format_ident!("__tsm_post_owned_{}", *next, span = Span::mixed_site());
            let rest = post_sequence(
                &statements[index + 1..],
                fields,
                fragment_type,
                quote! {#name},
                next,
            )?
            .unwrap_or(quote! {#name});
            return Ok(Some(quote! {{let #name = #after; #rest}}));
        }
    }
    Ok(None)
}

/// The fragment after `stmt` from the fragment named `current` (`None`: `current`).
fn post_fragment(
    stmt: &TransitionStmt,
    fields: &HashMap<String, Field>,
    fragment_type: &TokenStream,
    current: TokenStream,
    next: &mut usize,
) -> Result<Option<TokenStream>, Error> {
    match stmt {
        TransitionStmt::Block(_, children) => {
            post_sequence(children, fields, fragment_type, current, next)
        }
        TransitionStmt::Split(span, kind, children) => match &**kind {
            SplitKind::Let(pattern, ty, _, expression) => {
                let ty = ty.as_ref().map(|ty| quote! {:#ty});
                Ok(post_sequence(children, fields, fragment_type, current, next)?
                    .map(|body| quote! {{let #pattern #ty = #expression; #body}}))
            }
            SplitKind::If(condition) => {
                let then_branch =
                    post_fragment(&children[0], fields, fragment_type, current.clone(), next)?;
                let else_branch = match children.get(1) {
                    Some(child) => {
                        post_fragment(child, fields, fragment_type, current.clone(), next)?
                    }
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
                let mut bodies = vec![];
                for child in children {
                    bodies.push(post_fragment(
                        child,
                        fields,
                        fragment_type,
                        current.clone(),
                        next,
                    )?);
                }
                if bodies.iter().all(|b| b.is_none()) {
                    return Ok(None);
                }
                let cases = arms.iter().zip(bodies).map(|(arm, body)| {
                    let pattern = &arm.pat;
                    let guard = arm.guard.as_ref().map(|(keyword, e)| quote! {#keyword #e});
                    let body = body.unwrap_or(current.clone());
                    quote! {#pattern #guard => {#body}}
                });
                Ok(Some(quote! {match #expression {#(#cases),*}}))
            }
            SplitKind::Special(name, operation, _, pattern) => {
                let field = fields.get(&name.to_string()).ok_or_else(|| {
                    Error::new(*span, "chain operation refers to an unknown field")
                })?;
                if operation.stmt.is_for_storage() {
                    let body = post_sequence(children, fields, fragment_type, current, next)?;
                    return Ok(match (body, pattern) {
                        (Some(body), Some(pattern)) => {
                            let observed = match &operation.elt {
                                MonoidElt::OptionSome(None) => quote! {pre.#name->Some_0},
                                MonoidElt::SingletonKV(key, None) => quote! {pre.#name[#key]},
                                _ => return Err(Error::new(*span, "unsupported storage binding")),
                            };
                            Some(bind_pattern(pattern, observed, body))
                        }
                        (body, _) => body,
                    });
                }
                // A `remove`'s implicit value is the owned fragment's (as in the chain and
                // the ownership condition); a `have`'s may be the borrowed fragment's, which
                // `owned_post` does not see: it is the state's.
                let value = if operation.is_have() {
                    crate::verified_monoids::operand(field, operation, *span)?
                } else {
                    observed_value(field, operation, &current, *span)?
                };
                *next += 1;
                let value_ident =
                    format_ident!("__tsm_post_operand_{}", *next, span = Span::mixed_site());
                let value_type = operand_type(&field.stype);
                let bind = |body: TokenStream| -> Result<TokenStream, Error> {
                    Ok(match pattern {
                        Some(pattern) => bind_pattern(
                            pattern,
                            bound_value(field, operation, quote! {#value_ident}, *span)?,
                            body,
                        ),
                        None => body,
                    })
                };
                if operation.is_have() {
                    let Some(body) = post_sequence(children, fields, fragment_type, current, next)?
                    else {
                        return Ok(None);
                    };
                    let body = bind(body)?;
                    return Ok(Some(quote! {{let #value_ident: #value_type = #value; #body}}));
                }
                let after =
                    next_fragment(fragment_type, field, operation, current, &quote! {#value_ident});
                *next += 1;
                let after_name =
                    format_ident!("__tsm_post_owned_{}", *next, span = Span::mixed_site());
                let body =
                    post_sequence(children, fields, fragment_type, quote! {#after_name}, next)?
                        .unwrap_or(quote! {#after_name});
                let body = bind(body)?;
                Ok(Some(quote! {{
                    let #value_ident: #value_type = #value;
                    let #after_name = #after;
                    #body
                }}))
            }
        },
        _ => Ok(None),
    }
}

/// The fragment component of `<t>_owned_post` (over `owned` and `pre`).
pub(crate) fn owned_post_fragment(
    sm: &SM,
    tr: &Transition,
    fragment_type: &TokenStream,
) -> Result<TokenStream, Error> {
    let fields: HashMap<_, _> = sm.fields.iter().map(|f| (f.name.to_string(), f.clone())).collect();
    // The walk starts from a hygienic name: a `let` or a pattern of the transition may
    // bind `owned`.
    let start = format_ident!("__tsm_post_owned_0", span = Span::mixed_site());
    Ok(match post_fragment(&tr.body, &fields, fragment_type, quote! {#start}, &mut 0)? {
        Some(walk) => quote! {{let #start = owned; #walk}},
        None => quote! {owned},
    })
}

/// The proof of a raw frame's output configuration inside its completion quantifier
/// (over `owned`, `h`, `z`, `pre` and `post`, the executed state, whose strong relation
/// holds): the chain of `tr` without its `have`s, the variables' updates, and the join
/// (`join`, the machine's `__tsm_cfg_join`) of the configurations at `new_fragment`
/// (`<t>_owned_post(owned, pre, post, ..)`) into `op(op(new, h), z) == embed(post)`.
pub(crate) fn frame_chain(
    sm: &SM,
    tr: &Transition,
    fragment_type: &TokenStream,
    split: &TokenStream,
    join: &TokenStream,
    new_fragment: TokenStream,
    updated_variables: &[&Ident],
) -> Result<TokenStream, Error> {
    // Without a modified monoid field (other than a counting one), `owned_post` is `owned`
    // with the updated variables and counts, and the output configuration follows from
    // the completion's directly.
    if modified(&tr.body, sm).iter().all(|f| counting(&f.stype)) {
        return Ok(quote! {});
    }
    let frame = format_ident!("z");
    let state = format_ident!("pre");
    let chain =
        chain_of(sm, tr, fragment_type, split, quote! {owned}, quote! {h}, &frame, &state, true)?;
    let c = quote! {::vstd::resource::tsm_calculus};
    let new = format_ident!("__tsm_frame_new", span = Span::mixed_site());
    let exclusive = |e: TokenStream| {
        let exclusive = quote! {::vstd::resource::exclusive::ExclusiveRA::Exclusive};
        quote! {::core::option::Option::Some(#exclusive(#e))}
    };
    let updates = updated_variables.iter().map(|n| {
        let after = exclusive(quote! {post.#n});
        let before = exclusive(quote! {pre.#n});
        quote! {
            #c::cfg_iff(owned.#n, h.#n, z.#n, #before);
            #c::var_update(owned.#n, h.#n, z.#n, pre.#n, post.#n);
            #c::cfg_iff(#after, h.#n, z.#n, #after);
        }
    });
    Ok(quote! {
        #chain
        #(#updates)*
        let #new = #new_fragment;
        #join(#new, h, z, post);
    })
}
