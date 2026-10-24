//! Interface selection for `verified_tokenized_state_machine!`, and checked
//! readiness over locally observed inputs for the raw interface (generated for
//! every transition `local_ready_supported` accepts, next to the
//! all-completion API).
use crate::ast::*;
use crate::parse_token_stream::{ParseResult, parse_result_to_smir};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashSet;
use verus_syn::{Error, Ident};

/// Selects the client interface. The default is the generic field-token
/// interface (`verified_generic_tokens`, which may also be written explicitly):
/// the trusted macro's token types and `Instance` methods, each proved by a
/// call to the raw operation. `#[verified_raw_tokens]` selects the raw
/// resource interface, with raw operations whose preconditions are stated over
/// the owned fragments (`local_ready::t`) for every non-init transition that
/// `local_ready_supported` accepts. The removed `#[verified_field_tokens]` and
/// `#[verified_local_ready(..)]` are rejected.
pub fn construct(mut parsed: ParseResult) -> Result<TokenStream, Error> {
    let mut raw = false;
    let mut generic = false;
    let mut remaining = vec![];
    for attr in parsed.attrs {
        let attribute_name =
            if attr.path().leading_colon.is_none() && attr.path().segments.len() == 1 {
                attr.path().segments[0].ident.to_string().trim_start_matches("r#").to_string()
            } else {
                String::new()
            };
        if attribute_name == "verified_field_tokens" {
            return Err(Error::new(
                attr.path().segments[0].ident.span(),
                "`#[verified_field_tokens]` was removed: per-field tokens (the generic interface) are the default; delete the attribute",
            ));
        } else if attribute_name == "verified_local_ready" {
            // TODO: drop this
            return Err(Error::new(
                attr.path().segments[0].ident.span(),
                "`#[verified_local_ready(..)]` was removed: local readiness is generated for every raw transition (`M::local_ready::t`); delete the attribute",
            ));
        } else if attribute_name == "verified_generic_tokens" {
            if generic {
                return Err(Error::new(
                    attr.path().segments[0].ident.span(),
                    "duplicate generic field tokens attribute",
                ));
            }
            if raw {
                return Err(Error::new(
                    attr.path().segments[0].ident.span(),
                    "generic field tokens and raw token attributes cannot be combined",
                ));
            }
            if !matches!(attr.meta, verus_syn::Meta::Path(_)) {
                return Err(Error::new(
                    attr.path().segments[0].ident.span(),
                    "generic field tokens attribute takes no arguments",
                ));
            }
            generic = true;
        } else if attribute_name == "verified_raw_tokens" {
            if raw {
                return Err(Error::new(
                    attr.path().segments[0].ident.span(),
                    "duplicate raw token attribute",
                ));
            }
            if generic {
                return Err(Error::new(
                    attr.path().segments[0].ident.span(),
                    "generic field tokens and raw token attributes cannot be combined",
                ));
            }
            if !matches!(attr.meta, verus_syn::Meta::Path(_)) {
                return Err(Error::new(
                    attr.path().segments[0].ident.span(),
                    "raw token attribute takes no arguments",
                ));
            }
            raw = true;
        } else {
            remaining.push(attr);
        }
    }
    parsed.attrs = remaining;
    let mut bundle = parse_result_to_smir(parsed, true)?;
    crate::lemmas::check_lemmas(&bundle)?;
    // Parameter and binder names of the generated raw operations, which transition
    // parameters must not shadow or duplicate.
    for tr in &bundle.sm.transitions {
        for param in &tr.params {
            let name = param.name.to_string();
            // Only the names that fail to compile in every position (`z`: in every
            // non-init transition); `new`, `shared`, `outputs` and `result` are accepted, as
            // they compile where no generated binder takes them (e.g. `init!`, guard-only
            // properties, generic `result`), and fail with the compiler's error elsewhere.
            let reserved = ["owned", "h", "out"].contains(&name.as_str())
                || (name == "z" && tr.kind != TransitionKind::Init);
            if reserved {
                return Err(Error::new(
                    param.name.span(),
                    format!(
                        "`{name}` cannot name a transition parameter of the checked macro: the generated raw operations use it"
                    ),
                ));
            }
        }
    }
    if !raw {
        // The generic interface has no local-ready API: every generic operation
        // already has a token-level precondition, and its generated readiness
        // lemma covers every completion.
        // Initial requirements over a storage map become named open spec
        // functions, which keeps the raw initializer's execution proof
        // stable; clients see equal terms.
        if bundle.sm.fields.iter().any(|field| matches!(field.stype, ShardableType::StorageMap(..)))
        {
            crate::verified_generic_tokens::normalize_initial_requirements(&mut bundle)?;
        }
        let api = crate::verified_generic_tokens::output(&bundle)?;
        // The generic interface is written against the general emitter's
        // interface, so every machine goes there directly. This is the
        // end point of `verified_tokens::output_raw`'s fallback as well,
        // and the general emitter carries the raw backend's lifted limits
        // (labels, several deposits/withdrawals/guards per path, ...).
        let output = crate::verified_general::output(bundle)?;
        return crate::verified_generic_tokens::append_tokens(output, api);
    }
    // The raw interface: every transition, readonly transition and property
    // that `local_ready_supported` accepts gets the local-ready API.
    let selected: HashSet<String> = bundle
        .sm
        .transitions
        .iter()
        .filter(|tr| tr.kind != TransitionKind::Init && local_ready_supported(tr).is_ok())
        .map(|tr| tr.name.to_string())
        .collect();
    if selected.is_empty() {
        return crate::verified_tokens::output_raw(bundle);
    }
    crate::verified_general::output_with_ready(bundle, &selected)
}

/// Whether the raw interface generates the local-ready API (`local_ready::t`)
/// for the non-init transition `tr`; otherwise the reason it is skipped (the
/// transition keeps its other raw operations). The rule is syntactic; it
/// excludes the forms for which the generated `local_ready::t::ready` is not
/// proved:
///
/// * a closure (`|x| ..`, not a quantifier) in an operand of a `remove`,
///   `have`, `add`, `deposit`, `withdraw` or `guard`, in the value of a `let`,
///   in an `if` condition, or in a `match` scrutinee or arm guard (anywhere
///   but in a `require`, `assert` or `update`): the readiness proof restates
///   the closure, and distinct copies of a closure are distinct terms;
/// * a `require` that the local requirement cannot state (under a binding
///   other than a `let`, `if`, `match`, `remove` or `have`; TSM itself
///   rejects these forms).
///
/// Every other form is proved by a chain of the statement calculus
/// (`verified_chain`), or needs no statement facts at all.
pub(crate) fn local_ready_supported(tr: &Transition) -> Result<(), String> {
    if let Err(e) = declared_requires(&tr.body) {
        return Err(e.to_string());
    }
    if closure_outside_conditions(&tr.body) {
        return Err("a closure in an operand, `let`, condition or scrutinee".to_string());
    }
    Ok(())
}

/// Whether `expr` contains a closure that is not a quantifier's binder.
fn has_closure(expr: &verus_syn::Expr) -> bool {
    use verus_syn::visit::Visit;
    struct Finder(bool);
    impl<'ast> Visit<'ast> for Finder {
        fn visit_expr_unary(&mut self, e: &'ast verus_syn::ExprUnary) {
            use verus_syn::UnOp;
            if let (
                UnOp::Forall(_) | UnOp::Exists(_) | UnOp::Choose(_),
                verus_syn::Expr::Closure(c),
            ) = (&e.op, &*e.expr)
            {
                self.visit_expr(&c.body);
            } else {
                verus_syn::visit::visit_expr_unary(self, e);
            }
        }
        fn visit_expr_closure(&mut self, _: &'ast verus_syn::ExprClosure) {
            self.0 = true;
        }
    }
    let mut finder = Finder(false);
    finder.visit_expr(expr);
    finder.0
}

/// Whether a closure occurs in `stmt` outside a `require`, `assert` or
/// `update` (see `local_ready_supported`).
fn closure_outside_conditions(stmt: &TransitionStmt) -> bool {
    match stmt {
        TransitionStmt::Block(_, children) => children.iter().any(closure_outside_conditions),
        TransitionStmt::Split(_, kind, children) => {
            let here = match &**kind {
                SplitKind::If(condition) => has_closure(condition),
                SplitKind::Match(scrutinee, arms) => {
                    has_closure(scrutinee)
                        || arms
                            .iter()
                            .any(|arm| arm.guard.as_ref().is_some_and(|(_, g)| has_closure(g)))
                }
                SplitKind::Let(_, _, _, value) => has_closure(value),
                SplitKind::Special(_, operation, _, _) => match &operation.elt {
                    MonoidElt::True | MonoidElt::OptionSome(None) => false,
                    MonoidElt::OptionSome(Some(e))
                    | MonoidElt::SingletonMultiset(e)
                    | MonoidElt::SingletonSet(e)
                    | MonoidElt::General(e) => has_closure(e),
                    MonoidElt::SingletonKV(key, value) => {
                        has_closure(key) || value.as_ref().is_some_and(|v| has_closure(v))
                    }
                },
            };
            here || children.iter().any(closure_outside_conditions)
        }
        _ => false,
    }
}

// General collection operands create a substantial sequential ownership term.
// Retain a named specification call at each frame/ready boundary instead of
// duplicating that term through verifier inline expansion. This changes no
// precondition: the explicit assertions below instantiate the same predicate.
pub(crate) fn inline_ownership(sm: &SM, tr: &Transition) -> bool {
    fn general_collection(stmt: &TransitionStmt, sm: &SM) -> bool {
        match stmt {
            TransitionStmt::Block(_, children) => {
                children.iter().any(|child| general_collection(child, sm))
            }
            TransitionStmt::Split(_, split, children) => {
                let here = match &**split {
                    SplitKind::Special(field, op, _, _) => {
                        matches!(op.elt, MonoidElt::General(_))
                            && sm.fields.iter().any(|f| {
                                f.name == *field
                                    && matches!(
                                        f.stype,
                                        ShardableType::Map(..)
                                            | ShardableType::IMap(..)
                                            | ShardableType::Multiset(_)
                                    )
                            })
                    }
                    _ => false,
                };
                here || children.iter().any(|child| general_collection(child, sm))
            }
            _ => false,
        }
    }
    !general_collection(&tr.body, sm)
}

fn contains_require(s: &TransitionStmt) -> bool {
    match s {
        TransitionStmt::Require(..) => true,
        TransitionStmt::Split(_, kind, _) if refutable_observation(kind).is_some() => true,
        TransitionStmt::Block(_, xs) | TransitionStmt::Split(_, _, xs) => {
            xs.iter().any(contains_require)
        }
        _ => false,
    }
}

/// The pattern of a `remove` or `have` that binds an implicit value with a
/// refutable pattern (a requirement that the value matches).
fn refutable_observation(kind: &SplitKind) -> Option<&verus_syn::Pat> {
    match kind {
        SplitKind::Special(_, operation, _, Some(pattern))
            if (operation.is_remove() || operation.is_have())
                && matches!(
                    operation.elt,
                    MonoidElt::OptionSome(None) | MonoidElt::SingletonKV(_, None)
                )
                && !crate::util::is_definitely_irrefutable(pattern) =>
        {
            Some(pattern)
        }
        _ => None,
    }
}

/// The transition's `require` conditions as one expression, keeping its `let`s, `if`s and
/// `match`es.
fn declared_requires(s: &TransitionStmt) -> Result<TokenStream, Error> {
    if !contains_require(s) {
        return Ok(quote! {true});
    }
    match s {
        TransitionStmt::Require(_, expr) => Ok(quote! {#expr}),
        TransitionStmt::Block(_, xs) => {
            let xs = xs.iter().map(declared_requires).collect::<Result<Vec<_>, _>>()?;
            Ok(quote! {true #(&& (#xs))*})
        }
        TransitionStmt::Split(span, kind, xs) => {
            let bodies = xs.iter().map(declared_requires).collect::<Result<Vec<_>, _>>()?;
            match &**kind {
                SplitKind::Let(pat, ty, LetKind::Normal, expr) => {
                    let ty = ty.as_ref().map(|ty| quote! {: #ty});
                    let body = &bodies[0];
                    Ok(quote! {{let #pat #ty = #expr; #body}})
                }
                SplitKind::If(expr) => {
                    let yes = &bodies[0];
                    let no = &bodies[1];
                    Ok(quote! {if #expr {#yes} else {#no}})
                }
                SplitKind::Match(expr, arms) => {
                    let arms: Vec<_> = arms
                        .iter()
                        .zip(bodies)
                        .map(|(arm, body)| {
                            let pat = &arm.pat;
                            let guard = arm.guard.as_ref().map(|(_, expr)| quote! {if #expr});
                            quote! {#pat #guard => {#body}}
                        })
                        .collect();
                    Ok(quote! {match #expr {#(#arms),*}})
                }
                SplitKind::Special(_, _, _, None) => Ok(quote! {true #(&& (#bodies))*}),
                // An implicit value, bound from `pre` as in the deposit (the
                // local state supplies the owner's value).
                SplitKind::Special(name, operation, _, Some(pattern)) => {
                    let observed = match &operation.elt {
                        MonoidElt::OptionSome(None) => quote! {pre.#name->Some_0},
                        MonoidElt::SingletonKV(key, None) => quote! {pre.#name[#key]},
                        _ => {
                            return Err(Error::new(
                                *span,
                                "local-ready cannot observe a hidden or special-bound require",
                            ));
                        }
                    };
                    let bound = crate::verified_monoids::bind_pattern(
                        pattern,
                        observed.clone(),
                        quote! {true #(&& (#bodies))*},
                    );
                    // A refutable pattern also requires its match, as in the
                    // transition's enabling condition.
                    Ok(match refutable_observation(kind) {
                        Some(_) => quote! {(match #observed {
                            #pattern => true,
                            #[allow(unreachable_patterns)] _ => false
                        }) && #bound},
                        None => bound,
                    })
                }
                _ => Err(Error::new(
                    *span,
                    "local-ready cannot observe a hidden or special-bound require",
                )),
            }
        }
        _ => Ok(quote! {true}),
    }
}

/// The `local_ready::<tr>::declared_requires` spec fn: the transition's own requirements on
/// `pre`.
pub fn declared_requires_spec(
    tr: &Transition,
    st: &TokenStream,
    params: &[TokenStream],
) -> Result<TokenStream, Error> {
    let expression = declared_requires(&tr.body)?;
    Ok(
        quote! {#[verifier::inline] pub open spec fn declared_requires(pre:#st,#(#params),*)->bool {#expression}},
    )
}

/// What `local_ready_api` uses of the machine and of one local-ready transition (`st`/`se`:
/// state type/expression, `pe`: protocol expression, `ft`: fragment type, `tt`: token type, `pn`: parameter names).
pub struct Context<'a> {
    pub sm: &'a SM,
    pub tr: &'a Transition,
    pub st: &'a TokenStream,
    pub se: &'a TokenStream,
    pub pe: &'a TokenStream,
    pub ft: &'a TokenStream,
    pub tt: &'a TokenStream,
    pub result: &'a TokenStream,
    pub result_expr: &'a TokenStream,
    pub params: &'a [TokenStream],
    pub pn: &'a [&'a Ident],
    pub owned: &'a [TokenStream],
    pub observed: &'a [TokenStream],
    pub reads: &'a [&'a Ident],
    /// The machine's storage, if it has one (otherwise the operations are over the plain
    /// token, without deposits and withdrawals).
    pub storage: Option<&'a crate::verified_storage_tagged::Tagged>,
    pub deposits: bool,
    pub withdraws: bool,
    pub paired: bool,
    /// Whether `ready` is proved by the statement calculus's chain (`verified_chain`).
    pub chain: bool,
}

/// A `__tsm_<stem>_<n>` name that no parameter, field, generic or body identifier of `tr`
/// uses.
fn fresh(sm: &SM, tr: &Transition, stem: &str) -> Ident {
    fn reserve(tokens: TokenStream, names: &mut HashSet<String>) {
        for token in tokens {
            match token {
                proc_macro2::TokenTree::Ident(n) => {
                    names.insert(n.to_string());
                }
                proc_macro2::TokenTree::Group(g) => reserve(g.stream(), names),
                _ => {}
            }
        }
    }
    fn visit(stmt: &TransitionStmt, names: &mut HashSet<String>) {
        match stmt {
            TransitionStmt::Block(_, children) => {
                for child in children {
                    visit(child, names)
                }
            }
            TransitionStmt::Initialize(_, _, e)
            | TransitionStmt::Update(_, _, e)
            | TransitionStmt::Require(_, e)
            | TransitionStmt::PostCondition(_, e) => reserve(quote! {#e}, names),
            TransitionStmt::Assert(_, e, proof) => {
                reserve(quote! {#e}, names);
                if let Some(block) = &proof.proof {
                    reserve(quote! {#block}, names);
                }
            }
            TransitionStmt::SubUpdate(_, _, indices, e) => {
                reserve(quote! {#e}, names);
                for index in indices {
                    if let SubIdx::Idx(e) = index {
                        reserve(quote! {#e}, names);
                    }
                }
            }
            TransitionStmt::Split(_, split, children) => {
                match &**split {
                    SplitKind::If(e) => reserve(quote! {#e}, names),
                    SplitKind::Match(e, arms) => {
                        reserve(quote! {#e}, names);
                        for arm in arms {
                            let pat = &arm.pat;
                            reserve(quote! {#pat}, names);
                            if let Some((_, guard)) = &arm.guard {
                                reserve(quote! {#guard}, names);
                            }
                        }
                    }
                    SplitKind::Let(pat, ty, _, e) => reserve(quote! {#pat #ty #e}, names),
                    SplitKind::Special(_, op, proof, pat) => {
                        reserve(quote! {#pat}, names);
                        if let Some(block) = &proof.proof {
                            reserve(quote! {#block}, names);
                        }
                        match &op.elt {
                            MonoidElt::OptionSome(Some(e))
                            | MonoidElt::SingletonMultiset(e)
                            | MonoidElt::SingletonSet(e)
                            | MonoidElt::General(e) => reserve(quote! {#e}, names),
                            MonoidElt::SingletonKV(key, value) => {
                                reserve(quote! {#key #value}, names)
                            }
                            _ => {}
                        }
                    }
                }
                for child in children {
                    visit(child, names)
                }
            }
        }
    }
    let mut unavailable: HashSet<_> = tr
        .params
        .iter()
        .map(|p| p.name.to_string())
        .chain(sm.fields.iter().map(|f| f.name.to_string()))
        .collect();
    if let Some(g) = &sm.generics {
        reserve(quote! {#g}, &mut unavailable);
    }
    visit(&tr.body, &mut unavailable);
    for suffix in 0usize.. {
        let candidate = format!("__tsm_{stem}_{suffix}");
        if !unavailable.contains(&candidate) {
            return Ident::new(&candidate, proc_macro2::Span::mixed_site());
        }
    }
    unreachable!()
}

/// Whether `stmt` has a storage operation under a `let`, `if` or `match`
/// (which `<tr>_deposited` and `local_ready::<tr>::deposited` then keep).
fn scoped_deposits(stmt: &TransitionStmt) -> bool {
    fn storage(stmt: &TransitionStmt) -> bool {
        match stmt {
            TransitionStmt::Block(_, children) => children.iter().any(storage),
            TransitionStmt::Split(_, split, children) => {
                matches!(&**split, SplitKind::Special(_, operation, ..) if operation.stmt.is_for_storage())
                    || children.iter().any(storage)
            }
            _ => false,
        }
    }
    match stmt {
        TransitionStmt::Block(_, children) => children.iter().any(scoped_deposits),
        TransitionStmt::Split(_, split, children) => {
            let scope =
                matches!(&**split, SplitKind::Let(..) | SplitKind::If(_) | SplitKind::Match(..));
            (scope && children.iter().any(storage)) || children.iter().any(scoped_deposits)
        }
        _ => false,
    }
}

/// The field of a `remove` or `have` whose pattern binds a value the operand
/// leaves implicit (`[k => let v]` of a map, `Some(let x)` of an option, either
/// exclusive or persistent): the value is the owner's, so the local state takes
/// it from the supplied fragments.
fn implicit_binding<'a>(sm: &'a SM, name: &Ident, operation: &SpecialOp) -> Option<&'a Field> {
    if !(operation.is_remove() || operation.is_have()) {
        return None;
    }
    let field = sm.fields.iter().find(|f| f.name == *name)?;
    match (&field.stype, &operation.elt) {
        (
            ShardableType::Map(..)
            | ShardableType::IMap(..)
            | ShardableType::PersistentMap(..)
            | ShardableType::PersistentIMap(..),
            MonoidElt::SingletonKV(_, None),
        )
        | (
            ShardableType::Option(_) | ShardableType::PersistentOption(_),
            MonoidElt::OptionSome(None),
        ) => Some(field),
        _ => None,
    }
}

/// The value a fragment pair holds for an implicit binding of `field` (at
/// `key` for a map): the owned fragment's entry if it has one, else the
/// shared fragment's. A `remove` finds its value in `owned`, a `have` in
/// either.
fn fragment_value(
    field: &Field,
    key: Option<&verus_syn::Expr>,
    owned: &Ident,
    shared: &Ident,
) -> TokenStream {
    let n = &field.name;
    // A named function: an `if` cannot occur in a trigger the value reaches.
    let entry = if field.stype.is_persistent() {
        quote! {agreement_entry}
    } else {
        quote! {exclusive_entry}
    };
    let at = |f: &Ident| match key {
        Some(key) => quote! {#f.#n.at(#key)},
        None => quote! {#f.#n},
    };
    let (o, s) = (at(owned), at(shared));
    quote! {::vstd::resource::tsm_collections::#entry(#o,#s)}
}

/// Builds the local state of a transition with implicit bindings: the
/// observation `__observed(op(owned, h))` with each implicitly bound entry set
/// to the fragments' value (`fragment_value`), along the transition's control
/// flow, so that every completion agrees with it on the values the
/// transition's patterns bind. Each `build`/`sequence` returns the expression
/// of the state a statement leaves (`None`: unchanged), with its scope closed.
struct LocalState<'a> {
    sm: &'a SM,
    se: &'a TokenStream,
    owned: Ident,
    shared: Ident,
    next: usize,
}

impl LocalState<'_> {
    fn fresh(&mut self, stem: &str) -> Ident {
        self.next += 1;
        format_ident!("__tsm_local_{}_{}", stem, self.next, span = proc_macro2::Span::mixed_site())
    }

    fn sequence(
        &mut self,
        statements: &[TransitionStmt],
        current: TokenStream,
    ) -> Result<Option<TokenStream>, Error> {
        let mut declarations = vec![];
        let mut current = current;
        for statement in statements {
            if let Some(next) = self.build(statement, current.clone())? {
                let name = self.fresh("state");
                declarations.push(quote! {let #name = #next;});
                current = quote! {#name};
            }
        }
        Ok((!declarations.is_empty()).then(|| quote! {{#(#declarations)* #current}}))
    }

    fn build(
        &mut self,
        statement: &TransitionStmt,
        current: TokenStream,
    ) -> Result<Option<TokenStream>, Error> {
        let (span, split, children) = match statement {
            TransitionStmt::Block(_, children) => return self.sequence(children, current),
            TransitionStmt::Split(span, split, children) => (*span, &**split, children),
            _ => return Ok(None),
        };
        // Every branch starts from `current`. (A field's `add`s follow its
        // `remove`s and `have`s on every path, so an implicit value is never
        // an added one.)
        let branches = |this: &mut Self, children: &[TransitionStmt]| {
            children
                .iter()
                .map(|child| this.build(child, current.clone()))
                .collect::<Result<Vec<_>, Error>>()
        };
        Ok(match split {
            SplitKind::Let(pattern, ty, _, expression) => {
                let ty = ty.as_ref().map(|ty| quote! {:#ty});
                self.sequence(children, current)?
                    .map(|body| quote! {{let #pattern #ty = #expression; #body}})
            }
            SplitKind::If(condition) => {
                let bodies = branches(self, children)?;
                if bodies.iter().all(Option::is_none) {
                    return Ok(None);
                }
                let then_branch = bodies[0].clone().unwrap_or(current.clone());
                let else_branch = bodies.get(1).cloned().flatten().unwrap_or(current.clone());
                Some(quote! {if #condition {#then_branch} else {#else_branch}})
            }
            SplitKind::Match(expression, arms) => {
                let bodies = branches(self, children)?;
                if bodies.iter().all(Option::is_none) {
                    return Ok(None);
                }
                let cases = arms.iter().zip(bodies).map(|(arm, body)| {
                    let pattern = &arm.pat;
                    let guard = arm.guard.as_ref().map(|(keyword, e)| quote! {#keyword #e});
                    let body = body.unwrap_or(current.clone());
                    quote! {#pattern #guard => {#body}}
                });
                Some(quote! {match #expression {#(#cases),*}})
            }
            SplitKind::Special(name, operation, _, pattern) => {
                let Some(field) = implicit_binding(self.sm, name, operation) else {
                    let body = self.sequence(children, current)?;
                    return Ok(match (body, pattern) {
                        (Some(body), Some(pattern)) => {
                            let observed = match &operation.elt {
                                MonoidElt::OptionSome(None) => quote! {pre.#name->Some_0},
                                MonoidElt::SingletonKV(key, None) => quote! {pre.#name[#key]},
                                _ => {
                                    return Err(Error::new(
                                        span,
                                        "local-ready cannot observe this binding",
                                    ));
                                }
                            };
                            Some(crate::verified_monoids::bind_pattern(pattern, observed, body))
                        }
                        (body, _) => body,
                    });
                };
                let se = self.se;
                let n = &field.name;
                let value = self.fresh("value");
                let state = self.fresh("state");
                let (key, updated) = match &operation.elt {
                    MonoidElt::SingletonKV(key, None) => {
                        (Some(key), quote! {#se{#n:(#current).#n.insert(#key,#value),..#current}})
                    }
                    _ => (None, quote! {#se{#n:Some(#value),..#current}}),
                };
                let observed = fragment_value(field, key, &self.owned, &self.shared);
                let body = self.sequence(children, quote! {#state})?.unwrap_or(quote! {#state});
                let body = match pattern {
                    Some(pattern) => {
                        crate::verified_monoids::bind_pattern(pattern, quote! {#value}, body)
                    }
                    None => body,
                };
                Some(quote! {{let #value = #observed; let #state = #updated; #body}})
            }
        })
    }
}

/// The local state of `local_ready::<tr>::precondition` for a transition with implicit
/// bindings (`implicit_binding`), over `owned`/`h`; `None` if it has none (the
/// local state is then the observation itself).
fn implicit_local_state(
    sm: &SM,
    tr: &Transition,
    se: &TokenStream,
    pe: &TokenStream,
    ft: &TokenStream,
) -> Result<Option<TokenStream>, Error> {
    let mut builder = LocalState {
        sm,
        se,
        owned: format_ident!("__tsm_local_owned", span = proc_macro2::Span::mixed_site()),
        shared: format_ident!("__tsm_local_shared", span = proc_macro2::Span::mixed_site()),
        next: 0,
    };
    let Some(state) = builder.build(&tr.body, quote! {pre})? else {
        return Ok(None);
    };
    let (o, s) = (&builder.owned, &builder.shared);
    Ok(Some(quote! {{
        let #o = owned; let #s = h;
        let pre = #pe::__observed(<#ft>::op(owned,h));
        #state
    }}))
}

/// Whether a quantifier of the local requirement may have a trigger in the observation of a
/// machine with variable or constant fields (`Protocol::__observed`, which then has
/// conditionals): a `require` with a quantifier that reads `pre`, a `remove`/`have`/`add`
/// operand that reads `pre` (its ownership condition quantifies over the operand), or a
/// singleton `remove` from a map field. The local state is then a named function, as the
/// observation's conditionals cannot occur in a trigger. (The last case needs no named
/// state since the composed effects were retired; it is kept so that the local-ready API,
/// which has `local_state` for these transitions, stays unchanged.)
fn quantified_state(sm: &SM, tr: &Transition) -> bool {
    fn mentions(tokens: TokenStream, names: &[&str]) -> bool {
        tokens.into_iter().any(|token| match token {
            proc_macro2::TokenTree::Ident(n) => names.iter().any(|name| n == name),
            proc_macro2::TokenTree::Group(g) => mentions(g.stream(), names),
            _ => false,
        })
    }
    fn walk(sm: &SM, statement: &TransitionStmt) -> bool {
        match statement {
            TransitionStmt::Block(_, children) => children.iter().any(|c| walk(sm, c)),
            TransitionStmt::Require(_, e) => {
                mentions(quote! {#e}, &["forall", "exists", "choose"])
                    && mentions(quote! {#e}, &["pre"])
            }
            TransitionStmt::Split(_, split, children) => {
                let here = match &**split {
                    SplitKind::Special(name, operation, ..) => {
                        let map_removal = operation.is_remove()
                            && matches!(operation.elt, MonoidElt::SingletonKV(..))
                            && sm.fields.iter().any(|f| {
                                f.name == *name
                                    && matches!(
                                        f.stype,
                                        ShardableType::Map(..) | ShardableType::IMap(..)
                                    )
                            });
                        let operand = match &operation.elt {
                            MonoidElt::SingletonKV(key, value) => quote! {#key #value},
                            MonoidElt::OptionSome(value) => quote! {#value},
                            MonoidElt::SingletonSet(e)
                            | MonoidElt::SingletonMultiset(e)
                            | MonoidElt::General(e) => quote! {#e},
                            _ => quote! {},
                        };
                        map_removal || mentions(operand, &["pre"])
                    }
                    _ => false,
                };
                here || children.iter().any(|c| walk(sm, c))
            }
            _ => false,
        }
    }
    let observed = sm
        .fields
        .iter()
        .any(|f| matches!(f.stype, ShardableType::Variable(_) | ShardableType::Constant(_)));
    observed && walk(sm, &tr.body)
}

/// The fields with implicit bindings in `tr`.
fn implicit_fields<'a>(sm: &'a SM, tr: &Transition) -> Vec<&'a Field> {
    fn walk<'a>(sm: &'a SM, statement: &TransitionStmt, out: &mut Vec<&'a Field>) {
        match statement {
            TransitionStmt::Block(_, children) => children.iter().for_each(|c| walk(sm, c, out)),
            TransitionStmt::Split(_, split, children) => {
                if let SplitKind::Special(name, operation, _, _) = &**split {
                    if let Some(field) = implicit_binding(sm, name, operation) {
                        if !out.iter().any(|f| f.name == field.name) {
                            out.push(field);
                        }
                    }
                }
                children.iter().for_each(|c| walk(sm, c, out))
            }
            _ => {}
        }
    }
    let mut out = vec![];
    walk(sm, &tr.body, &mut out);
    out
}

/// The fields that `agreement` covers: with implicit bindings, or with a
/// singleton `remove`/`have` whose operand mentions a name a `let` or a
/// pattern binds (the singleton hints skip those, and the sequence hints stop
/// at a refutable pattern), every map, set and option field that a singleton
/// `remove` or `have` observes; otherwise none.
fn agreement_fields<'a>(sm: &'a SM, tr: &Transition) -> Vec<&'a Field> {
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
    fn walk<'a>(
        sm: &'a SM,
        statement: &TransitionStmt,
        bound: &mut HashSet<String>,
        out: &mut Vec<&'a Field>,
        uses_bound: &mut bool,
    ) {
        match statement {
            TransitionStmt::Block(_, children) => {
                children.iter().for_each(|c| walk(sm, c, bound, out, uses_bound))
            }
            TransitionStmt::Split(_, split, children) => {
                match &**split {
                    SplitKind::Let(pattern, ..) => bound.extend(
                        crate::ident_visitor::pattern_get_bound_idents(pattern)
                            .iter()
                            .map(|n| n.to_string()),
                    ),
                    SplitKind::Match(_, arms) => {
                        for arm in arms {
                            bound.extend(
                                crate::ident_visitor::pattern_get_bound_idents(&arm.pat)
                                    .iter()
                                    .map(|n| n.to_string()),
                            )
                        }
                    }
                    SplitKind::Special(name, operation, _, pattern) => {
                        let operand = match &operation.elt {
                            MonoidElt::SingletonKV(key, value) => Some(quote! {#key #value}),
                            MonoidElt::OptionSome(value) => Some(quote! {#value}),
                            MonoidElt::SingletonSet(key) => Some(quote! {#key}),
                            _ => None,
                        };
                        let field = sm.fields.iter().find(|f| f.name == *name).filter(|f| {
                            matches!(
                                f.stype,
                                ShardableType::Map(..)
                                    | ShardableType::IMap(..)
                                    | ShardableType::PersistentMap(..)
                                    | ShardableType::PersistentIMap(..)
                                    | ShardableType::Option(_)
                                    | ShardableType::PersistentOption(_)
                                    | ShardableType::Set(_)
                                    | ShardableType::ISet(_)
                                    | ShardableType::PersistentSet(_)
                                    | ShardableType::PersistentISet(_)
                            )
                        });
                        if let (Some(field), Some(operand), true) =
                            (field, operand, operation.is_remove() || operation.is_have())
                        {
                            let mut mentioned = HashSet::new();
                            names(operand, &mut mentioned);
                            *uses_bound |= !mentioned.is_disjoint(bound);
                            if !out.iter().any(|f| f.name == field.name) {
                                out.push(field);
                            }
                        }
                        if let Some(pattern) = pattern {
                            bound.extend(
                                crate::ident_visitor::pattern_get_bound_idents(pattern)
                                    .iter()
                                    .map(|n| n.to_string()),
                            )
                        }
                    }
                    SplitKind::If(_) => {}
                }
                children.iter().for_each(|c| walk(sm, c, bound, out, uses_bound))
            }
            _ => {}
        }
    }
    let (mut out, mut uses_bound) = (vec![], false);
    walk(sm, &tr.body, &mut HashSet::new(), &mut out, &mut uses_bound);
    if uses_bound || !implicit_fields(sm, tr).is_empty() { out } else { vec![] }
}

/// Readiness facts for the fields of `agreement_fields`: every entry the
/// owned or the shared fragment holds for such a field is the completion's.
/// A map or set fact is also triggered by the completion's entry: an operand
/// key bound in the transition (by a `let` or a pattern) has no ground term on
/// the fragments until such a fact is instantiated.
fn agreement(sm: &SM, tr: &Transition, completion: &Ident, z: &Ident) -> Vec<TokenStream> {
    let c = quote! {::vstd::resource::tsm_collections};
    agreement_fields(sm, tr)
        .into_iter()
        .map(|field| {
            let n = &field.name;
            let ct = crate::verified_monoids::component_type(&field.stype);
            let persistent = field.stype.is_persistent();
            let (tag, variant) = if persistent {
                (quote! {Agree_0}, quote! {Agree})
            } else {
                (quote! {Exclusive_0}, quote! {Exclusive})
            };
            let laws = quote! {
                <#ct>::commutative(owned.#n,h.#n);
                <#ct>::associative(owned.#n,h.#n,#z.#n);
                <#ct>::associative(h.#n,owned.#n,#z.#n);
            };
            let facts: Vec<_> = [(quote! {owned}, quote! {h}), (quote! {h}, quote! {owned})]
                .into_iter()
                .map(|(this, other)| {
                    let frame = quote! {<#ct>::op(#other.#n,#z.#n)};
                    match &field.stype {
                        ShardableType::Option(_) | ShardableType::PersistentOption(_) => {
                            let lemma = if persistent {
                                quote! {#c::persistent_option_owned_frame}
                            } else {
                                quote! {#c::option_owned_frame}
                            };
                            quote! {
                                if #this.#n is Some && #this.#n->Some_0 is #variant {
                                    #lemma(#this.#n,#frame,#completion.#n,#this.#n->Some_0->#tag);
                                }
                            }
                        }
                        ShardableType::Map(key_type, _)
                        | ShardableType::IMap(key_type, _)
                        | ShardableType::PersistentMap(key_type, _)
                        | ShardableType::PersistentIMap(key_type, _) => {
                            let key = format_ident!("__tsm_local_key", span = proc_macro2::Span::mixed_site());
                            let native = crate::verified_monoids::map_view(&field.stype, quote! {#completion.#n});
                            let lemma = if persistent {
                                quote! {#c::persistent_map_owned_frame}
                            } else {
                                quote! {#c::map_owned_frame}
                            };
                            quote! {
                                assert forall|#key:#key_type|
                                    #![trigger #this.#n.at(#key)] #![trigger #completion.#n.dom().contains(#key)] #![trigger #completion.#n[#key]]
                                    #this.#n.at(#key) is Some && #this.#n.at(#key)->Some_0 is #variant
                                    implies #completion.#n.dom().contains(#key) && #completion.#n[#key]==#this.#n.at(#key)->Some_0->#tag by {
                                    #lemma(#this.#n,#frame,#native,#key,#this.#n.at(#key)->Some_0->#tag);
                                }
                            }
                        }
                        ShardableType::Set(key_type)
                        | ShardableType::ISet(key_type)
                        | ShardableType::PersistentSet(key_type)
                        | ShardableType::PersistentISet(key_type) => {
                            let key = format_ident!("__tsm_local_key", span = proc_macro2::Span::mixed_site());
                            let native = crate::verified_monoids::set_view(&field.stype, quote! {#completion.#n});
                            let (lemma, unit) = if persistent {
                                (quote! {#c::persistent_set_owned_frame}, quote! {::vstd::resource::agree::AgreementRA::Agree(())})
                            } else {
                                (quote! {#c::set_owned_frame}, quote! {::vstd::resource::exclusive::ExclusiveRA::Exclusive(())})
                            };
                            quote! {
                                assert forall|#key:#key_type| #![trigger #this.#n.at(#key)] #![trigger #completion.#n.contains(#key)]
                                    #this.#n.at(#key) == Some(#unit)
                                    implies #completion.#n.contains(#key) by {
                                    #lemma(#this.#n,#frame,#native,#key);
                                }
                            }
                        }
                        _ => unreachable!(),
                    }
                })
                .collect();
            quote! {#laws #(#facts)*}
        })
        .collect()
}

/// The local-ready items of a transition `t`, associated items of the type `local_ready::t`
/// (next to `declared_requires` and `deposited`): `precondition`, `ready`, `run`,
/// `run_with_shared` and `observed`, and `local_state` if the local state is named. (Before,
/// these were `Protocol::t_local_requires`, `t_local_ready`, `t_local`, `t_local_with_shared`,
/// `t_observed` and `t_local_state`.)
pub fn local_ready_api(c: Context<'_>) -> Result<TokenStream, Error> {
    let Context {
        sm,
        tr,
        st,
        se,
        pe,
        ft,
        tt,
        result,
        result_expr,
        params,
        pn,
        owned,
        observed,
        reads,
        storage,
        deposits,
        withdraws,
        paired,
        chain,
    } = c;
    let n = &tr.name;
    let local_req = format_ident!("precondition");
    let ready = format_ident!("ready");
    let local = format_ident!("run");
    let local_shared = format_ident!("run_with_shared");
    let observed_op = format_ident!("observed");
    let req = format_ident!("{}_requires", n);
    let enabled = format_ident!("{}_enabled", n);
    let owners = format_ident!("{}_owners_enabled", n);
    let declared = format_ident!("declared_requires");
    let deposited = format_ident!("{}_deposited", n);
    let local_deposited = format_ident!("deposited");
    let output = format_ident!("{}_outputs", n);
    let witness = format_ident!("{}_witness", n);
    let strong = format_ident!("{}_strong", n);
    let owned_post = format_ident!("{}_owned_post", n);
    let shared_op = format_ident!("{}_with_shared", n);

    let local_state = fresh(sm, tr, "local_state");
    let observation = fresh(sm, tr, "observed_state");
    let completion_frame = fresh(sm, tr, "completion_frame");
    let full_state = fresh(sm, tr, "completion_state");
    let certificate = fresh(sm, tr, "certificate");
    let initial = fresh(sm, tr, "initial_fragment");
    let physical_deposit = fresh(sm, tr, "physical_deposit");
    let next = fresh(sm, tr, "next_token");
    let returned_map = fresh(sm, tr, "withdrawn_map");
    let before = fresh(sm, tr, "before_state");
    let after = fresh(sm, tr, "after_state");
    let witness_frame = fresh(sm, tr, "witness_frame");
    // The storage parts of the API, empty without storage: `deposit` parameters
    // and arguments (`dep_decl`, `dep_args`: of the predicates; `dep_param`,
    // `dep_arg`: of the operations), the outputs' storage arguments, and the
    // storage facts of the requirement, readiness proof and certificate.
    let mut dep_param = quote! {};
    let mut dep_arg = quote! {};
    let mut dep_decl = quote! {};
    let mut dep_spec = quote! {};
    let mut dep_args = quote! {};
    let mut wd_args = quote! {};
    let mut cert_wd_args = quote! {};
    let mut local_deposit_req = quote! {};
    let mut deposit_ens = quote! {};
    let mut deposit_eq = quote! {};
    let mut ret = quote! {tracked out:#tt};
    let mut call = quote! {let tracked #next=Self::#local(owned,#(#pn),*);};
    let mut out = quote! {out};
    let mut witness_args = quote! {};
    let mut cert_storage_ens = quote! {};
    let mut cert_wd_shape = quote! {};
    let mut physical_let = quote! {};
    let mut monotone_withdrawn = quote! {};
    let mut withdrawn_field = quote! {};
    if let Some(storage) = storage {
        let map = storage.ty();
        let unit = storage.unit();
        let tracked_unit = storage.tracked_unit();
        if deposits {
            dep_param = quote! {tracked deposit:#map,};
            dep_arg = quote! {deposit,};
        }
        let dep_value = if deposits {
            quote! {deposit}
        } else {
            unit.clone()
        };
        dep_decl = quote! {deposit:#map,};
        dep_spec = quote! {deposit,};
        dep_args = quote! {#dep_value,};
        if withdraws {
            ret = quote! {tracked out:(#tt,#map)};
            call =
                quote! {let tracked (#next,#returned_map)=Self::#local(owned,#dep_arg #(#pn),*);};
            out = quote! {out.0};
        } else {
            call = quote! {let tracked #next=Self::#local(owned,#dep_arg #(#pn),*);let tracked #returned_map:#map=#tracked_unit;};
        }
        let wd = if withdraws {
            quote! {out.1}
        } else {
            unit.clone()
        };
        wd_args = quote! {#dep_value,#wd,};
        cert_wd_args = quote! {#dep_value,#certificate.withdrawn,};
        if !withdraws {
            cert_wd_shape = quote! {,#certificate.withdrawn==#unit};
        }
        let before_s = quote! {#certificate.before.__storage()};
        let after_s = quote! {#certificate.after.__storage()};
        let physical = if paired {
            let disjoint = storage.disjoint(before_s.clone(), dep_value.clone());
            let within =
                storage.le(after_s.clone(), storage.op(before_s.clone(), dep_value.clone()));
            quote! {#dep_value==#se::#deposited(#certificate.before,#(#pn),*),
            #disjoint,
            #within,}
        } else {
            let delta = storage.minus(after_s.clone(), before_s.clone());
            quote! {#dep_value==#delta,}
        };
        let withdrawn_value =
            storage.minus(storage.op(before_s.clone(), dep_value.clone()), after_s.clone());
        cert_storage_ens = quote! {#physical #certificate.withdrawn==#withdrawn_value,};
        physical_let = quote! {let ghost #physical_deposit=#dep_value;};
        // A step that withdraws nothing and has one storage operation per path:
        // its outputs do not state the withdrawn storage (only that it is the
        // unit), so the certificate derives it from the storage growing.
        if !withdraws && !paired {
            let (b, a) = (quote! {#before.__storage()}, quote! {#after.__storage()});
            let grow = storage.prove_le(
                &format_ident!("__tsm_storage_index", span = proc_macro2::Span::mixed_site()),
                b.clone(),
                a.clone(),
            );
            monotone_withdrawn = quote! {
                #grow
                ::vstd::resource::tsm_storage::storage_withdrawn_none(#b,#a,#physical_deposit);
            };
        }
        witness_args = quote! {#physical_deposit,#returned_map,};
        withdrawn_field = quote! {withdrawn:#returned_map,};
        local_deposit_req = quote! {&& deposit==Self::#local_deposited(#local_state,#(#pn),*)};
        deposit_ens = quote! {&&#se::#deposited(#full_state,#(#pn),*)==deposit};
        let deposit_index =
            format_ident!("__tsm_deposit_index", span = proc_macro2::Span::mixed_site());
        let (local_deposit, full_deposit) = (
            quote! {Self::#local_deposited(#full_state,#(#pn),*)},
            quote! {#se::#deposited(#full_state,#(#pn),*)},
        );
        deposit_eq = if !implicit_fields(sm, tr).is_empty() {
            // Both deposits are the same inlined expression. A pattern's `let` in it
            // admits no trigger for the pointwise proof, so it is compared directly.
            quote! {assert(#local_deposit==#full_deposit);}
        } else if scoped_deposits(&tr.body) {
            // Both deposit functions are inline: name them, as Verus cannot
            // choose a trigger in their `let`/`if`/`match` bodies.
            let (local_name, full_name) =
                (fresh(sm, tr, "local_deposit"), fresh(sm, tr, "deposit"));
            let eq = storage.prove_eq(&deposit_index, quote! {#local_name}, quote! {#full_name});
            quote! {let #local_name = #local_deposit; let #full_name = #full_deposit; #eq}
        } else {
            storage.prove_eq(&deposit_index, local_deposit, full_deposit)
        };
    }
    // The readiness facts of the statements: the chain (a transition without a
    // collection observation needs none).
    let hints = if chain {
        let split = quote! {#pe::__tsm_cfg_split};
        let chain = crate::verified_chain::chain(
            sm,
            tr,
            ft,
            &split,
            quote! {owned},
            quote! {h},
            &completion_frame,
            &full_state,
        )?;
        vec![chain]
    } else {
        vec![]
    };
    // With implicit bindings the local state takes their values from the
    // fragments, and every completion agrees with it on them.
    // It is a named function: terms of the requirement mention it, and the
    // observation's conditionals cannot occur in a trigger.
    // So is the plain observation when an operand key is bound (a `let` may
    // read a variable from it).
    let implicit_state = match implicit_local_state(sm, tr, se, pe, ft)? {
        None if !agreement_fields(sm, tr).is_empty() || quantified_state(sm, tr) => {
            Some(quote! {#pe::__observed(<#ft>::op(owned,h))})
        }
        state => state,
    };
    let (local_value, local_state_fn, agreement) = match implicit_state {
        Some(state) => {
            let name = format_ident!("local_state");
            (
                quote! {Self::#name(owned,h,#(#pn),*)},
                quote! {
                    /// The local state of `precondition`: values bound by patterns are the fragments'.
                    pub open spec fn #name(owned:#ft,h:#ft,#(#params),*)->#st {#state}
                },
                agreement(sm, tr, &full_state, &completion_frame),
            )
        }
        None => (quote! {#pe::__observed(<#ft>::op(owned,h))}, quote! {}, vec![]),
    };
    Ok(quote! {
        #local_state_fn
        /// Local observations suffice only because the following theorem checks every completion.
        #[verifier::inline]
        pub open spec fn #local_req(owned:#ft,h:#ft,#dep_decl #(#params),*)->bool {
            true #(&& #owned)* #(&& #observed)* && {
                let #local_state=#local_value;
                Self::#declared(#local_state,#(#pn),*) && #se::#owners(#local_state,owned,h,#(#pn),*)
                    #local_deposit_req
            }
        }
        pub proof fn #ready(owned:#ft,h:#ft,#dep_decl #(#params),*)
            requires Self::#local_req(owned,h,#dep_spec #(#pn),*)
            ensures #pe::#req(owned,h,#dep_spec #(#pn),*)
        {
            let #observation=#local_value;
            assert forall|#completion_frame:#ft,#full_state:#st|#full_state.invariant()
                &&<#ft>::op(<#ft>::op(owned,h),#completion_frame)==#pe::embed(#full_state)
                implies #se::#enabled(#full_state,#(#pn),*)
                    #deposit_ens
                    &&#se::#owners(#full_state,owned,h,#(#pn),*) by {
                #(assert(#full_state.#reads==#observation.#reads);)*
                #(#agreement)*
                assert(Self::#declared(#full_state,#(#pn),*));
                assert(#se::#owners(#full_state,owned,h,#(#pn),*));
                #(#hints)*
                #deposit_eq
            }
        }
        pub proof fn #local_shared(tracked owned:#tt,tracked shared:&#tt,#dep_param #(#params),*)->(#ret)
            requires owned.loc()==shared.loc(),Self::#local_req(owned.fragment(),shared.fragment(),#dep_args #(#pn),*)
            ensures #out.loc()==owned.loc(),#pe::#output(owned.fragment(),shared.fragment(),#out.fragment(),#wd_args #(#pn),*)
        {
            Self::#ready(owned.fragment(),shared.fragment(),#dep_args #(#pn),*);
            #pe::#shared_op(owned,shared,#dep_arg #(#pn),*)
        }
        pub proof fn #local(tracked owned:#tt,#dep_param #(#params),*)->(#ret)
            requires Self::#local_req(owned.fragment(),<#ft>::unit(),#dep_args #(#pn),*)
            ensures #out.loc()==owned.loc(),#pe::#output(owned.fragment(),<#ft>::unit(),#out.fragment(),#wd_args #(#pn),*)
        {
            Self::#ready(owned.fragment(),<#ft>::unit(),#dep_args #(#pn),*);
            #pe::#n(owned,#dep_arg #(#pn),*)
        }
        /// Returned states describe a compatible completion, not a distinguished hidden history.
        pub proof fn #observed_op(tracked owned:#tt,#dep_param #(#params),*)->(tracked #certificate:#result)
            requires Self::#local_req(owned.fragment(),<#ft>::unit(),#dep_args #(#pn),*)
            ensures #certificate.token.loc()==owned.loc(),#certificate.before.invariant(),#certificate.after.invariant(),
                <#ft>::op(<#ft>::op(owned.fragment(),<#ft>::unit()),#certificate.frame)==#pe::embed(#certificate.before),
                #se::#strong(#certificate.before,#certificate.after,#(#pn),*),
                #certificate.token.fragment()==#pe::#owned_post(owned.fragment(),#certificate.before,#certificate.after,#(#pn),*),
                <#ft>::op(<#ft>::op(#certificate.token.fragment(),<#ft>::unit()),#certificate.frame)==#pe::embed(#certificate.after),
                #cert_storage_ens
                #pe::#output(owned.fragment(),<#ft>::unit(),#certificate.token.fragment(),#cert_wd_args #(#pn),*)
                #cert_wd_shape
        {
            let ghost #initial=owned.fragment();
            #physical_let
            #call
            let (#before,#after,#witness_frame)=#pe::#witness(#initial,<#ft>::unit(),#next.fragment(),#witness_args #(#pn),*);
            #monotone_withdrawn
            #result_expr{token:#next,#withdrawn_field before:#before,after:#after,frame:#witness_frame}
        }
    })
}

/// What `local_ready_guard_api` uses of a local-ready `property!`/`readonly!`
/// transition with a `guard` (see `Context`; `sty`: the storage type,
/// `observed`: the raw requirement's conditions on the borrowed fragment `f`).
pub struct GuardContext<'a> {
    pub sm: &'a SM,
    pub tr: &'a Transition,
    pub st: &'a TokenStream,
    pub se: &'a TokenStream,
    pub pe: &'a TokenStream,
    pub ft: &'a TokenStream,
    pub tt: &'a TokenStream,
    pub sty: &'a TokenStream,
    pub params: &'a [TokenStream],
    pub pn: &'a [&'a Ident],
    pub observed: &'a [TokenStream],
    pub reads: &'a [&'a Ident],
    /// Whether `ready` is proved by the statement calculus's chain (`verified_chain`).
    pub chain: bool,
}

/// The local-ready items (of the type `local_ready::t`) of a transition with a
/// `guard`: a `property!` or `readonly!` whose raw operation `Protocol::t`
/// borrows the token and returns a shared reference into the storage.
/// `precondition(f, ..)` is over the borrowed fragment, `ready` proves that it
/// implies `Protocol::t_requires` (by `local_ready_api`'s replay, with the
/// unit as the shared fragment), and `run(&token, ..)` is `Protocol::t` with
/// the local precondition; `local_state(f, ..)` if the local state is named.
/// A readonly transition or property without a `guard` has the raw operation
/// of a mutating transition (the token is passed and returned, with a unit
/// deposit), and gets `local_ready_api`'s items.
pub fn local_ready_guard_api(c: GuardContext<'_>) -> Result<TokenStream, Error> {
    let GuardContext { sm, tr, st, se, pe, ft, tt, sty, params, pn, observed, reads, chain } = c;
    let n = &tr.name;
    let req = format_ident!("{}_requires", n);
    let enabled = format_ident!("{}_enabled", n);
    let owners = format_ident!("{}_owners_enabled", n);
    let guarded = format_ident!("{}_guarded", n);
    let local_state = fresh(sm, tr, "local_state");
    let observation = fresh(sm, tr, "observed_state");
    let completion_frame = fresh(sm, tr, "completion_frame");
    let full_state = fresh(sm, tr, "completion_state");
    // The readiness facts of the statements (as in `local_ready_api`), over `owned` and
    // `h`: here the borrowed fragment and the unit.
    let hints = if chain {
        let split = quote! {#pe::__tsm_cfg_split};
        vec![crate::verified_chain::chain(
            sm,
            tr,
            ft,
            &split,
            quote! {owned},
            quote! {h},
            &completion_frame,
            &full_state,
        )?]
    } else {
        vec![]
    };
    // The local state, as `local_ready_api`'s.
    let implicit_state = match implicit_local_state(sm, tr, se, pe, ft)? {
        None if !agreement_fields(sm, tr).is_empty() => Some(quote! {#pe::__observed(f)}),
        state => state,
    };
    let (local_value, local_state_fn, agreement) = match implicit_state {
        Some(state) => (
            quote! {Self::local_state(f,#(#pn),*)},
            quote! {
                /// The local state of `precondition`: values bound by patterns are the fragment's.
                pub open spec fn local_state(f:#ft,#(#params),*)->#st {let owned=f; let h=<#ft>::unit(); #state}
            },
            agreement(sm, tr, &full_state, &completion_frame),
        ),
        None => (quote! {#pe::__observed(f)}, quote! {}, vec![]),
    };
    Ok(quote! {
        #local_state_fn
        /// Local observations suffice only because the following theorem checks every completion.
        #[verifier::inline]
        pub open spec fn precondition(f:#ft,#(#params),*)->bool {
            true #(&& #observed)* && {
                let #local_state=#local_value;
                Self::declared_requires(#local_state,#(#pn),*) && #se::#owners(#local_state,f,<#ft>::unit(),#(#pn),*)
            }
        }
        #[allow(unused_variables)]
        pub proof fn ready(f:#ft,#(#params),*)
            requires Self::precondition(f,#(#pn),*)
            ensures #pe::#req(f,#(#pn),*)
        {
            let owned=f;
            let h=<#ft>::unit();
            <#ft>::op_unit(f);
            let #observation=#local_value;
            assert forall|#completion_frame:#ft,#full_state:#st|#full_state.invariant()
                &&<#ft>::op(f,#completion_frame)==#pe::embed(#full_state)
                implies #se::#owners(#full_state,f,<#ft>::unit(),#(#pn),*)
                    &&#se::#enabled(#full_state,#(#pn),*) by {
                assert(<#ft>::op(<#ft>::op(owned,h),#completion_frame)==#pe::embed(#full_state));
                #(assert(#full_state.#reads==#observation.#reads);)*
                #(#agreement)*
                assert(Self::declared_requires(#full_state,#(#pn),*));
                assert(#se::#owners(#full_state,owned,h,#(#pn),*));
                #(#hints)*
            }
        }
        pub proof fn run(tracked token:&#tt,#(#params),*)->(tracked out:&#sty)
            requires Self::precondition(token.fragment(),#(#pn),*)
            ensures *out==#pe::#guarded(token.fragment(),#(#pn),*)
        {
            Self::ready(token.fragment(),#(#pn),*);
            #pe::#n(token,#(#pn),*)
        }
    })
}
