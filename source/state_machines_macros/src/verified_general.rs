//! Checked sequential execution for the proof-producing backend.
//! Resource updates quantify over every compatible completion; a chosen
//! completion is never exposed as the actual global state.
use crate::ast::*;
use crate::parse_token_stream::SMBundle;
use crate::to_token_stream::{
    fix_attrs, generics_for_decl, get_generic_args, set_mode_proof, shardable_type_to_type,
};
use crate::verified_monoids as monoids;
use crate::verified_storage_tagged::Tagged;
use proc_macro2::TokenStream;
use quote::{ToTokens, format_ident, quote};
use std::collections::{HashMap, HashSet};
use verus_syn::Error;
use verus_syn::Ident;
use verus_syn::spanned::Spanned;

/// Adds the fields `stmt` updates to `out`.
fn writes(stmt: &TransitionStmt, out: &mut HashSet<String>) {
    match stmt {
        TransitionStmt::Update(_, n, _) | TransitionStmt::SubUpdate(_, n, _, _) => {
            out.insert(n.to_string());
        }
        TransitionStmt::Block(_, children) | TransitionStmt::Split(_, _, children) => {
            for child in children {
                writes(child, out);
            }
        }
        _ => {}
    }
}

/// Some transition updates a `not_tokenized` field.
fn updates_unowned(sm: &SM) -> bool {
    let hidden: HashSet<_> = sm
        .fields
        .iter()
        .filter(|f| matches!(f.stype, ShardableType::NotTokenized(_)))
        .map(|f| f.name.to_string())
        .collect();
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
            for child in children {
                drop_unowned_updates(child, fields);
            }
        }
        _ => {}
    }
}

/// Whether the machine is outside the straight-line emitter's subset (`verified_tokens`),
/// so that its raw interface is generated here.
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
                    | ShardableType::StorageOption(_)
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

/// The hint of the diagnostics for a deposit into a location withdrawn
/// earlier in the same transition (syntactic, and verification-time).
pub(crate) const STORAGE_REPLACE_HINT: &str = "split the transition in two, with the intermediate state explicit: see examples/verified_tsm/storage_replace_in_two_transitions.rs";

/// A storage location an operation touches.
#[derive(Clone, PartialEq)]
enum Location {
    /// The single location of a `storage_option` field.
    Cell,
    /// A key of a `storage_map`/`storage_imap` field: its text (the value of an integer
    /// literal), and whether it is a literal (two different literals are different keys).
    Key(String, bool),
}

/// The locations of a storage operation: the known ones, and whether there may be others.
struct Locations {
    known: Vec<Location>,
    unknown: bool,
}

fn strip_parens(e: &verus_syn::Expr) -> &verus_syn::Expr {
    match e {
        verus_syn::Expr::Paren(p) => strip_parens(&p.expr),
        verus_syn::Expr::Group(g) => strip_parens(&g.expr),
        _ => e,
    }
}

fn path_ends_with(e: &verus_syn::Expr, name: &str) -> bool {
    matches!(strip_parens(e), verus_syn::Expr::Path(p)
        if p.path.segments.last().is_some_and(|s| s.ident == name))
}

fn key_location(key: &verus_syn::Expr) -> Location {
    match strip_parens(key) {
        // `1` and `1int` are the same key
        verus_syn::Expr::Lit(verus_syn::ExprLit { lit: verus_syn::Lit::Int(i), .. }) => {
            Location::Key(i.base10_digits().to_string(), true)
        }
        verus_syn::Expr::Lit(l) => Location::Key(l.to_token_stream().to_string(), true),
        key => Location::Key(key.to_token_stream().to_string(), false),
    }
}

/// The keys of a general map operand `Map::empty().insert(k1, v1).insert(k2, v2)..`.
fn general_map_keys(e: &verus_syn::Expr) -> Option<Vec<Location>> {
    match strip_parens(e) {
        verus_syn::Expr::MethodCall(m) if m.method == "insert" && m.args.len() == 2 => {
            let mut keys = general_map_keys(&m.receiver)?;
            keys.push(key_location(&m.args[0]));
            Some(keys)
        }
        verus_syn::Expr::Call(c) if c.args.is_empty() && path_ends_with(&c.func, "empty") => {
            Some(vec![])
        }
        _ => None,
    }
}

fn storage_locations(stype: &ShardableType, elt: &MonoidElt) -> Locations {
    let known = |known| Locations { known, unknown: false };
    match (stype, elt) {
        (ShardableType::StorageOption(_), MonoidElt::OptionSome(_)) => known(vec![Location::Cell]),
        (ShardableType::StorageOption(_), MonoidElt::General(e)) => match strip_parens(e) {
            verus_syn::Expr::Call(c) if path_ends_with(&c.func, "Some") => {
                known(vec![Location::Cell])
            }
            e if path_ends_with(e, "None") => known(vec![]),
            _ => Locations { known: vec![], unknown: true },
        },
        (_, MonoidElt::SingletonKV(key, _)) => known(vec![key_location(key)]),
        (_, MonoidElt::General(e)) => match general_map_keys(e) {
            Some(keys) => known(keys),
            None => Locations { known: vec![], unknown: true },
        },
        _ => Locations { known: vec![], unknown: true },
    }
}

/// Physical storage operations seen so far on one execution path.
#[derive(Clone, Default)]
struct StoragePath {
    /// Withdrawn locations by field, and the fields withdrawn from at unknown locations.
    withdrawn: Vec<(String, Location)>,
    withdrawn_unknown: Vec<String>,
    deposited: Vec<(String, Location)>,
}

/// Several deposits, withdrawals and guards may occur on one path; together
/// they form one storage exchange whose deposit is the union of all deposits
/// and whose withdrawal is the union of all withdrawals. That exchange requires
/// the deposit to be disjoint from the pre-state storage, so a deposit into a
/// location withdrawn earlier on the same path cannot be checked (it would
/// replace the stored value: two values at one location). A deposit that is
/// syntactically at a withdrawn location is rejected here (the single location
/// of a `storage_option` field, keys with the same text, the keys of general
/// `Map::empty().insert(..)` operands). Otherwise, if a deposit may be at a
/// location withdrawn earlier on its path (keys written differently, general
/// operands), the span of the first such deposit is returned in `maybe`: the
/// storage proof's disjointness assertion is then reported there, with the same
/// hint.
fn check_storage_paths(
    s: &TransitionStmt,
    fields: &HashMap<String, Field>,
    path: &mut StoragePath,
    maybe: &mut Option<proc_macro2::Span>,
) -> Result<(), Error> {
    match s {
        TransitionStmt::Block(_, children) => {
            for child in children {
                check_storage_paths(child, fields, path, maybe)?;
            }
        }
        TransitionStmt::Split(span, kind, children) => {
            if let SplitKind::Special(name, op, _, binding) = &**kind {
                let field = &fields[&name.to_string()];
                if field.stype.is_storage() {
                    let name = name.to_string();
                    let locations = storage_locations(&field.stype, &op.elt);
                    // A bound stored value is read from the pre-state. Earlier
                    // withdrawals cannot change a value that is still present;
                    // an earlier deposit at the same location would.
                    if binding.is_some() {
                        for location in &locations.known {
                            if path.deposited.contains(&(name.clone(), location.clone())) {
                                return Err(Error::new(
                                    *span,
                                    "verified stored-resource bindings cannot observe a value deposited earlier in the same transition",
                                ));
                            }
                        }
                    }
                    if op.stmt.is_withdraw() {
                        for location in locations.known {
                            path.withdrawn.push((name.clone(), location));
                        }
                        if locations.unknown {
                            path.withdrawn_unknown.push(name);
                        }
                    } else if op.stmt.is_deposit() {
                        for location in &locations.known {
                            if path.withdrawn.contains(&(name.clone(), location.clone())) {
                                return Err(Error::new(
                                    *span,
                                    format!(
                                        "verified storage cannot deposit into a location withdrawn earlier in the same transition (one storage exchange cannot replace a stored value: its deposit must be disjoint from the pre-state storage); {}",
                                        STORAGE_REPLACE_HINT
                                    ),
                                ));
                            }
                        }
                        let may_overlap = path.withdrawn_unknown.contains(&name)
                            || path.withdrawn.iter().any(|(f, w)| {
                                *f == name
                                    && (locations.unknown
                                        || locations.known.iter().any(|d| match (w, d) {
                                            (Location::Key(_, true), Location::Key(_, true)) => {
                                                false
                                            }
                                            _ => true,
                                        }))
                            });
                        if may_overlap && maybe.is_none() {
                            *maybe = Some(*span);
                        }
                        for location in locations.known {
                            path.deposited.push((name.clone(), location));
                        }
                    }
                }
            }
            if matches!(&**kind, SplitKind::If(_) | SplitKind::Match(..)) {
                let start = path.clone();
                for child in children {
                    let mut branch = start.clone();
                    check_storage_paths(child, fields, &mut branch, maybe)?;
                    for location in branch.withdrawn {
                        if !path.withdrawn.contains(&location) {
                            path.withdrawn.push(location);
                        }
                    }
                    for name in branch.withdrawn_unknown {
                        if !path.withdrawn_unknown.contains(&name) {
                            path.withdrawn_unknown.push(name);
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
                    check_storage_paths(child, fields, path, maybe)?;
                }
            }
        }
        _ => {}
    }
    Ok(())
}

/// Adds the fields `s` updates to `out`; returns the most storage operations on one path
/// and whether any of them withdraws. Rejects unsupported storage operations.
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
/// same-witness actual output map, not in a local physical input map (the
/// exchange's withdrawal is the difference of the witness states' storage). So they may read fields the operation does not own, or use
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
                        if !withdraw
                            || matches!(
                                f.stype,
                                ShardableType::Variable(_) | ShardableType::Constant(_)
                            )
                        {
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

/// The deposit of a transition body: the union of its deposits, each a tagged
/// part of the storage (`verified_storage_tagged`), without a leading empty map
/// (a single deposit is its tagged part itself, e.g. the `__pack_f` of its
/// operand).
fn storage_deposit(
    s: &TransitionStmt,
    fields: &HashMap<String, Field>,
    storage: &crate::verified_storage_tagged::Tagged,
) -> Result<TokenStream, Error> {
    let empty = storage.unit();
    Ok(match s {
        TransitionStmt::Block(_, xs) => {
            let pieces: Vec<_> = xs
                .iter()
                .filter(|x| has_deposit(x))
                .map(|s| storage_deposit(s, fields, storage))
                .collect::<Result<_, _>>()?;
            let mut pieces = pieces.into_iter();
            let mut value = pieces.next().unwrap_or(empty);
            for piece in pieces {
                value = storage.op(value, piece);
            }
            value
        }
        TransitionStmt::Split(span, k, xs) => match &**k {
            SplitKind::Let(p, t, LetKind::Normal, e) => {
                let t = t.as_ref().map(|t| quote! {:#t});
                let child = storage_deposit(&xs[0], fields, storage)?;
                quote! {{let #p #t=#e;#child}}
            }
            SplitKind::Let(_, _, LetKind::BirdsEye, _) if has_deposit(s) => {
                return Err(Error::new(
                    *span,
                    "a deposited resource cannot depend on a birds_eye binding",
                ));
            }
            SplitKind::If(e) => {
                let a = storage_deposit(&xs[0], fields, storage)?;
                let b = xs
                    .get(1)
                    .map(|s| storage_deposit(s, fields, storage))
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
                        let value = storage_deposit(child, fields, storage)?;
                        Ok(quote! {#p #guard=>{#value}})
                    })
                    .collect::<Result<_, Error>>()?;
                quote! {match #e{#(#cases),*}}
            }
            SplitKind::Special(name, op, _, _) if op.stmt.is_deposit() => {
                storage.singleton(name, &op.elt).map_err(|_| {
                    Error::new(*span, "verified deposit requires an explicit optional or map value")
                })?
            }
            SplitKind::Special(name, op, _, binding) => {
                let child = match xs.first() {
                    Some(x) => storage_deposit(x, fields, storage)?,
                    None => empty,
                };
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

/// Where a `have` of a guard property is (`guard_map_haves`, `guard_option_haves`):
/// the names that the enclosing `let`s, `match` arms and patterns bind, and
/// whether it is under an `if` or a `match`.
#[derive(Clone, Default)]
struct GuardScope {
    bound: HashSet<String>,
    conditional: bool,
}

impl GuardScope {
    /// The scope of `split`'s children.
    fn enter(&self, split: &SplitKind) -> Vec<GuardScope> {
        let bind = |scope: &mut GuardScope, pattern: &verus_syn::Pat| {
            scope.bound.extend(
                crate::ident_visitor::pattern_get_bound_idents(pattern)
                    .iter()
                    .map(|n| n.to_string()),
            )
        };
        let mut inner = self.clone();
        match split {
            SplitKind::Let(pattern, ..) => bind(&mut inner, pattern),
            SplitKind::Special(_, _, _, Some(pattern)) => bind(&mut inner, pattern),
            SplitKind::Special(..) => {}
            SplitKind::If(_) => inner.conditional = true,
            SplitKind::Match(_, arms) => {
                inner.conditional = true;
                return arms
                    .iter()
                    .map(|arm| {
                        let mut scope = inner.clone();
                        bind(&mut scope, &arm.pat);
                        scope
                    })
                    .collect();
            }
        }
        vec![inner]
    }

    /// Whether `tokens` mention a name bound in this scope.
    fn mentions_bound(&self, tokens: TokenStream) -> bool {
        tokens.into_iter().any(|token| match token {
            proc_macro2::TokenTree::Ident(n) => self.bound.contains(&n.to_string()),
            proc_macro2::TokenTree::Group(g) => self.mentions_bound(g.stream()),
            _ => false,
        })
    }
}

/// `have` operations on exclusive map fields with a key, in a guard property,
/// with whether the `have` is under an `if` or a `match`. A key that mentions a
/// name bound in the transition is not observed (the spec fns reading the
/// observation are outside its scope).
fn guard_map_haves(
    s: &TransitionStmt,
    fields: &HashMap<String, Field>,
) -> Vec<(Ident, verus_syn::Expr, bool)> {
    let mut out = vec![];
    fn walk(
        s: &TransitionStmt,
        fields: &HashMap<String, Field>,
        scope: &GuardScope,
        out: &mut Vec<(Ident, verus_syn::Expr, bool)>,
    ) {
        match s {
            TransitionStmt::Block(_, xs) => xs.iter().for_each(|x| walk(x, fields, scope, out)),
            TransitionStmt::Split(_, k, xs) => {
                if let SplitKind::Special(n, op, _, _) = &**k {
                    if matches!(op.stmt, MonoidStmtType::Have)
                        && matches!(
                            fields[&n.to_string()].stype,
                            ShardableType::Map(..) | ShardableType::IMap(..)
                        )
                    {
                        if let MonoidElt::SingletonKV(key, _) = &op.elt {
                            if !scope.mentions_bound(quote! {#key}) {
                                out.push((n.clone(), key.clone(), scope.conditional));
                            }
                        }
                    }
                }
                let scopes = scope.enter(k);
                for (index, x) in xs.iter().enumerate() {
                    walk(x, fields, &scopes[index.min(scopes.len() - 1)], out);
                }
            }
            _ => {}
        }
    }
    walk(s, fields, &GuardScope::default(), &mut out);
    out
}

/// The `option` and `persistent_option` fields of `have o >= Some(..)`
/// statements, each with whether it is persistent and whether every such
/// `have` of it is under an `if` or a `match`.
fn guard_option_haves(
    s: &TransitionStmt,
    fields: &HashMap<String, Field>,
) -> Vec<(Ident, bool, bool)> {
    let mut out: Vec<(Ident, bool, bool)> = vec![];
    fn walk(
        s: &TransitionStmt,
        fields: &HashMap<String, Field>,
        scope: &GuardScope,
        out: &mut Vec<(Ident, bool, bool)>,
    ) {
        match s {
            TransitionStmt::Block(_, xs) => xs.iter().for_each(|x| walk(x, fields, scope, out)),
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
                        {
                            match out.iter_mut().find(|(m, _, _)| m == n) {
                                Some(entry) => entry.2 &= scope.conditional,
                                None => out.push((n.clone(), persistent, scope.conditional)),
                            }
                        }
                    }
                }
                let scopes = scope.enter(k);
                for (index, x) in xs.iter().enumerate() {
                    walk(x, fields, &scopes[index.min(scopes.len() - 1)], out);
                }
            }
            _ => {}
        }
    }
    walk(s, fields, &GuardScope::default(), &mut out);
    out
}

/// The storage a guard property borrows: the deposit its guards would make.
fn guarded_storage(
    s: &TransitionStmt,
    fields: &HashMap<String, Field>,
    storage: &crate::verified_storage_tagged::Tagged,
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
    storage_deposit(&clone, fields, storage)
}

/// The statements as proof code, or with `safety` as the enabling condition.
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
        SimplStmt::Assert(span, e, p) => {
            let a = match &p.proof {
                // As in the trusted macro (`safety_conditions.rs`): the
                // condition is reported at its statement, with its message.
                Some(b) if !p.error_msg.is_empty() => {
                    let assert_fn = Ident::new(&p.error_msg, *span);
                    quote::quote_spanned! {*span =>
                        assert(#e) by {
                            #b
                            ::vstd::state_machine_internal::#assert_fn(#e);
                        }
                    }
                }
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

/// The raw interface, with checked local-ready operations for the transitions in
/// `local_ready`.
pub fn output_with_ready(
    bundle: SMBundle,
    local_ready: &HashSet<String>,
) -> Result<TokenStream, Error> {
    let tagged = Tagged::build(&bundle)?;
    let ctx = machine_context(&bundle, local_ready, tagged.as_ref())?;
    let field_api = crate::verified_ergonomics::field_api(
        ctx.sm,
        &ctx.ft,
        &ctx.tt,
        &ctx.decls.names,
        &ctx.decls.types,
    )?;
    let mut items = Items {
        relations: crate::verified_state_relations::output(&bundle, &ctx.st)?,
        ..Items::default()
    };
    for tr in &ctx.sm.transitions {
        transition_items(&ctx, tr, &mut items)?;
    }
    Ok(machine_module(&ctx, &items, &field_api))
}

/// The machine-wide data every generated item is written against. As in
/// `verified_readiness`, `st`/`se` are `State` in type and expression position,
/// `ft`/`fe` `Fragment`, `pt`/`pe` `Protocol` and `tt`/`te` `Token`.
struct Ctx<'a> {
    bundle: &'a SMBundle,
    sm: &'a SM,
    /// The transitions with a local-ready API.
    local_ready: &'a HashSet<String>,
    /// The local-ready transitions whose readiness the statement calculus's chains prove.
    chained: HashSet<String>,
    fields: HashMap<String, Field>,
    /// The tagged storage layout (`verified_storage_tagged`), on machines with storage.
    storage: Option<&'a Tagged>,
    datatype_attrs: Vec<verus_syn::Attribute>,
    decl: TokenStream,
    where_clause: TokenStream,
    /// The generic arguments in type position (`<A, ..>`); empty without generics.
    type_args: TokenStream,
    st: TokenStream,
    se: TokenStream,
    ft: TokenStream,
    fe: TokenStream,
    pt: TokenStream,
    pe: TokenStream,
    tt: TokenStream,
    te: TokenStream,
    result_ty: TokenStream,
    result_expr: TokenStream,
    /// The phantom field of a generic machine's datatypes, and its value.
    marker_field: Option<TokenStream>,
    marker_value: Option<TokenStream>,
    decls: FieldDecls<'a>,
}

/// The per-field pieces of `State`, `Fragment` and the embedding of a state.
struct FieldDecls<'a> {
    state_fields: Vec<TokenStream>,
    /// The executor's temporaries (`update_tmp_<field>`) and the post-state fields they set.
    temps: Vec<TokenStream>,
    posts: Vec<TokenStream>,
    /// The fields of `__observed(f)`, the state a fragment observes.
    observations: Vec<TokenStream>,
    /// The fragment's fields (the tokenized ones) and their component types.
    names: Vec<&'a Ident>,
    types: Vec<TokenStream>,
    fragment_fields: Vec<TokenStream>,
    /// Each fragment field's value in `embed(s)`, and as a field initializer.
    embed_values: Vec<TokenStream>,
    embeds: Vec<TokenStream>,
}

/// The items the transitions contribute to the machine module.
#[derive(Default)]
struct Items {
    /// The relations and executors of `State`.
    relations: Vec<TokenStream>,
    /// The user's induction lemmas, as `State` methods.
    lemmas: Vec<TokenStream>,
    /// The raw operations of `Protocol`.
    operations: Vec<TokenStream>,
    /// The local-ready API of each selected transition `t`: the associated items of
    /// the type `local_ready::t` (see `verified_readiness::local_ready_api`).
    local_ready: Vec<(Ident, TokenStream)>,
}

fn machine_context<'a>(
    bundle: &'a SMBundle,
    local_ready: &'a HashSet<String>,
    storage: Option<&'a Tagged>,
) -> Result<Ctx<'a>, Error> {
    let sm = &bundle.sm;
    let (generics, datatype_attrs) = crate::verified_tokens::datatype_generics(sm);
    let (decl, where_clause) = generics_for_decl(&generics);
    let args = sm.generics.as_ref().map(|g| get_generic_args(&g.params));
    let type_args = args.as_ref().map(|a| quote! {<#a>}).unwrap_or_default();
    let expr_args = args.as_ref().map(|a| quote! {::<#a>}).unwrap_or_default();
    let chained = sm
        .transitions
        .iter()
        .filter(|tr| {
            local_ready.contains(&tr.name.to_string()) && crate::verified_chain::uses_chain(sm, tr)
        })
        .map(|tr| tr.name.to_string())
        .collect();
    Ok(Ctx {
        bundle,
        sm,
        local_ready,
        chained,
        fields: sm.fields.iter().map(|f| (f.name.to_string(), f.clone())).collect(),
        storage,
        datatype_attrs,
        decl,
        where_clause,
        st: quote! {State #type_args},
        se: quote! {State #expr_args},
        ft: quote! {Fragment #type_args},
        fe: quote! {Fragment #expr_args},
        pt: quote! {Protocol #type_args},
        pe: quote! {Protocol #expr_args},
        tt: quote! {Token #type_args},
        te: quote! {Token #expr_args},
        result_ty: quote! {TransitionObservation #type_args},
        result_expr: quote! {TransitionObservation #expr_args},
        marker_field: args
            .as_ref()
            .map(|a| quote! {pub __tsm_phantom:core::marker::PhantomData<(#a,)>,}),
        marker_value: args.as_ref().map(|_| quote! {__tsm_phantom:core::marker::PhantomData,}),
        type_args,
        decls: field_declarations(sm)?,
    })
}

/// Rejects the field kinds this backend does not support.
fn field_declarations(sm: &SM) -> Result<FieldDecls<'_>, Error> {
    let mut decls = FieldDecls {
        state_fields: vec![],
        temps: vec![],
        posts: vec![],
        observations: vec![],
        names: vec![],
        types: vec![],
        fragment_fields: vec![],
        embed_values: vec![],
        embeds: vec![],
    };
    for field in &sm.fields {
        let name = &field.name;
        let ty = shardable_type_to_type(field.type_span, &field.stype);
        decls.state_fields.push(quote! {pub #name:#ty});
        let tmp = format_ident!("update_tmp_{}", name);
        decls.temps.push(quote! {let mut #tmp:#ty;});
        decls.posts.push(quote! {#name:#tmp});
        let observed = match field.stype {
            ShardableType::Variable(_) => {
                quote! {if f.#name is Some &&f.#name->Some_0 is Exclusive{f.#name->Some_0->Exclusive_0}else{arbitrary()}}
            }
            ShardableType::Constant(_) => {
                quote! {if f.#name is Some &&f.#name->Some_0 is Agree{f.#name->Some_0->Agree_0}else{arbitrary()}}
            }
            _ => quote! {arbitrary()},
        };
        decls.observations.push(quote! {#name:#observed});
        let (component, embedded) = match &field.stype {
            ShardableType::Variable(t) => {
                (quote! {Option<ExclusiveRA<#t>>}, quote! {Some(ExclusiveRA::Exclusive(s.#name))})
            }
            ShardableType::Constant(t) => {
                (quote! {Option<AgreementRA<#t>>}, quote! {Some(AgreementRA::Agree(s.#name))})
            }
            ShardableType::NotTokenized(_) => continue,
            stype if monoids::is_monoid_type(stype) => {
                (monoids::component_type(stype), monoids::embed(stype, quote! {s.#name}))
            }
            ShardableType::StorageOption(_)
            | ShardableType::StorageIMap(..)
            | ShardableType::StorageMap(..) => continue,
            _ => {
                return Err(Error::new(
                    field.type_span,
                    "verified sequential backend currently supports variable, constant, not_tokenized, and storage fields",
                ));
            }
        };
        decls.names.push(name);
        decls.types.push(component.clone());
        decls.fragment_fields.push(quote! {pub #name:#component});
        decls.embed_values.push(embedded.clone());
        decls.embeds.push(quote! {#name:#embedded});
    }
    Ok(decls)
}

/// Adds a transition's relations, induction lemma, raw operations and local-ready
/// API to `items`.
fn transition_items(ctx: &Ctx, tr: &Transition, items: &mut Items) -> Result<(), Error> {
    let Ctx {
        bundle,
        sm,
        local_ready,
        chained,
        fields,
        st,
        se,
        ft,
        fe,
        pt,
        pe,
        tt,
        te,
        result_ty,
        result_expr,
        marker_value,
        decls,
        ..
    } = ctx;
    let storage = ctx.storage;
    let FieldDecls { names, temps, posts, .. } = decls;
    let Items { relations, lemmas, operations: ops, local_ready: local_ready_items } = items;
    let guard_property =
        matches!(tr.kind, TransitionKind::Property | TransitionKind::ReadonlyTransition)
            && contains_guard(&tr.body);
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
        .zip(temps)
        .filter(|(f, _)| assigned.contains(&f.name.to_string()))
        .map(|(_, t)| t.clone())
        .collect();
    let tr_posts: Vec<_> = sm
        .fields
        .iter()
        .zip(posts)
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
    let mut replace_candidate = None;
    check_storage_paths(&tr.body, &fields, &mut StoragePath::default(), &mut replace_candidate)?;
    // Paired exchange outputs when some path has several storage operations.
    let paired = storage_ops > 1;
    // The checked backend's restrictions on monoid statements (operand forms, bindings,
    // the remove-have-add order of one field, bindings before additions), and the
    // composed operands that the multiset cardinality hints below use.
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
        local_ready.contains(&n.to_string()),
    )?;
    let ownership_inline = if crate::verified_readiness::inline_ownership(sm, tr) {
        ready_inline.clone()
    } else {
        quote! {}
    };
    relations.push(quote!{#ownership_inline pub open spec fn #owners(pre:#st,owned:#ft,h:#ft,#(#params),*)->bool{#owner_expression}});
    // The composed removals of multiset fields, for the cardinality hints of the
    // inductiveness lemma below.
    let cardinality_effects: Vec<_> =
        if storage.is_some_and(|p| p.fields.len() > 1) && tr.kind != TransitionKind::Init {
            effects
                .iter()
                .filter(|effect| {
                    matches!(effect.field.stype, ShardableType::Multiset(_))
                        && effect.op == monoids::EffectOp::Remove
                        && !effect.replacement
                })
                .collect()
        } else {
            vec![]
        };
    relations.push(monoids::effect_functions(&cardinality_effects, &st, &params));
    let mut access_errors = vec![];
    let mut token_footprint = tr.body.clone();
    if updates_unowned(sm) {
        drop_unowned_updates(&mut token_footprint, &fields);
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
        let cardinality_hints: Vec<_> = if !init {
            cardinality_effects.iter()
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
        } else {
            vec![]
        };
        f.block = verus_syn::parse2(
            quote! {{requires(#cond);ensures(post.invariant());#b #(#cardinality_hints)*}},
        )?;
        let spinoff = crate::verified_model::induction_spinoff(&f.attrs);
        lemmas.push(quote! {::vstd::prelude::verus_impl!{#spinoff #f}});
    }
    let init_alias = if init {
        quote! {pub open spec fn #n(post:#st,#(#params),*)->bool {Self::#strong(post,#(#pn),*)}}
    } else {
        quote! {}
    };
    let no_withdraw = !withdraw;
    let storage_index =
        format_ident!("__tsm_storage_index", span = proc_macro2::Span::mixed_site());
    let (storage_ens, storage_proof) = match storage {
        Some(p) if !init => {
            let pre_s = quote! {pre.__storage()};
            let post_s = quote! {post.__storage()};
            let dep = quote! {Self::#deposited(pre,#(#pn),*)};
            let agrees = p.agrees(pre_s.clone(), post_s.clone());
            let agrees_proof =
                p.prove_agrees_at(&storage_index, pre_s.clone(), post_s.clone(), replace_candidate);
            let grow = p.le(pre_s.clone(), post_s.clone());
            let grow_proof = if no_withdraw {
                p.prove_le(&storage_index, pre_s.clone(), post_s.clone())
            } else {
                quote! {}
            };
            let grow_ens = if no_withdraw {
                quote! {,#grow}
            } else {
                quote! {}
            };
            if paired {
                let transferred = p.op(pre_s.clone(), quote! {physical_deposit});
                let disjoint = p.disjoint(pre_s.clone(), dep.clone());
                let within = p.le(post_s.clone(), p.op(pre_s.clone(), dep.clone()));
                let covered = p.le(p.op(pre_s.clone(), dep.clone()), post_s.clone());
                let covered_ens = if no_withdraw {
                    quote! {,#covered}
                } else {
                    quote! {}
                };
                let covered_proof = if no_withdraw {
                    p.prove_le(&storage_index, transferred.clone(), post_s.clone())
                } else {
                    quote! {}
                };
                (quote! {,#agrees,#disjoint,#within #grow_ens #covered_ens}, {
                    let disjoint_proof = p.prove_disjoint_at(
                        &storage_index,
                        pre_s.clone(),
                        quote! {physical_deposit},
                        replace_candidate,
                    );
                    let within_proof =
                        p.prove_le(&storage_index, post_s.clone(), transferred.clone());
                    quote! {
                        let physical_deposit=#dep;
                        #agrees_proof
                        #grow_proof
                        #disjoint_proof
                        #within_proof
                        #covered_proof
                    }
                })
            } else {
                let delta = p.minus(post_s.clone(), pre_s.clone());
                let delta_proof = p.prove_eq(&storage_index, dep.clone(), delta.clone());
                (
                    quote! {,#agrees,#dep==#delta #grow_ens},
                    quote! {
                        #grow_proof
                        #agrees_proof
                        #delta_proof
                    },
                )
            }
        }
        _ => (quote! {}, quote! {}),
    };
    if let Some(p) = storage {
        if !init {
            let expression = storage_deposit(&tr.body, &fields, p)?;
            let sty = p.ty();
            relations.push(quote!{#ready_inline pub open spec fn #deposited(pre:#st,#(#params),*)->#sty{#expression}});
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
        let p = storage.unwrap();
        let sty = p.ty();
        let guarded = format_ident!("{}_guarded", n);
        let expression = guarded_storage(&tr.body, &fields, p)?;
        // Values bound by `have m >= [k => ..]` on exclusive map fields are
        // observed from the owned fragment at k, so the guarded value stays
        // a function of the fragment and is linked to `pre` by map_owned_frame.
        let map_haves = guard_map_haves(&tr.body, &fields);
        let mut observed_fields: Vec<(Ident, Vec<verus_syn::Expr>)> = vec![];
        for (field, key, _) in &map_haves {
            match observed_fields.iter_mut().find(|(n, _)| n == field) {
                Some((_, keys)) => keys.push(key.clone()),
                None => observed_fields.push((field.clone(), vec![key.clone()])),
            }
        }
        // Likewise for values bound by `have o >= Some(..)` on option
        // fields (linked to `pre` by option_owned_frame) and persistent
        // option fields (by persistent_option_owned_frame).
        let option_haves = guard_option_haves(&tr.body, &fields);
        let option_updates: Vec<_> = option_haves
            .iter()
            .map(|(field, persistent, _)| {
                if *persistent {
                    quote! {#field: Some(f.#field->Some_0->Agree_0)}
                } else {
                    quote! {#field: Some(f.#field->Some_0->Exclusive_0)}
                }
            })
            .collect();
        let observed_base = if observed_fields.is_empty() && option_updates.is_empty() {
            quote! {Self::__observed(f)}
        } else {
            let updates: Vec<_> = option_updates
                .iter()
                .cloned()
                .chain(observed_fields.iter().map(|(field, keys)| {
                    let inserts = keys
                        .iter()
                        .map(|k| quote! {.insert(#k, f.#field.at(#k)->Some_0->Exclusive_0)});
                    let empty = match fields[&field.to_string()].stype {
                        ShardableType::IMap(..) => quote! {::vstd::imap::IMap::empty()},
                        _ => quote! {::vstd::map::Map::empty()},
                    };
                    quote! {#field: #empty #(#inserts)*}
                }))
                .collect();
            quote! {#se{#(#updates,)* ..Self::__observed(f)}}
        };
        // The values the `have`s observe in `f` are the state's: the statement
        // calculus's chain (with the unit as the borrowed fragment) states them.
        let guard_links = if map_haves.is_empty() && option_haves.is_empty() {
            quote! {}
        } else {
            let chain = crate::verified_chain::chain(
                sm,
                tr,
                &ft,
                &quote! {Self::__tsm_cfg_split},
                quote! {f},
                quote! {<#ft>::unit()},
                &format_ident!("z"),
                &format_ident!("pre"),
            )?;
            quote! {
                assert(#se::#owners(pre,f,<#ft>::unit(),#(#pn),*));
                #chain
            }
        };
        // The guard's storage fact, by a case split on each key's field.
        let guard_cases = p.prove_le_by_cases(
            &format_ident!("__tsm_guard_key", span = proc_macro2::Span::mixed_site()),
            quote! {Self::#guarded(f,#(#pn),*)},
            quote! {Self::storage(pre)},
        );
        let guard_le = p.le(quote! {Self::#guarded(f,#(#pn),*)}, quote! {Self::storage(pre)});
        relations.push(quote! {pub open spec fn #guarded(pre:#st,#(#params),*)->#sty{#expression}});
        let mut observed_req: Vec<_> = names
            .iter()
            .filter(|n| read.contains(&n.to_string()))
            .map(|n| match fields[&n.to_string()].stype {
                ShardableType::Variable(_) => quote! {f.#n is Some &&f.#n->Some_0 is Exclusive},
                ShardableType::Constant(_) => quote! {f.#n is Some &&f.#n->Some_0 is Agree},
                _ => unreachable!(),
            })
            .collect();
        for (field, persistent, _) in option_haves.iter().filter(|(_, _, conditional)| !conditional)
        {
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
                pub open spec fn #guarded(f:#ft,#(#params),*)->#sty{#se::#guarded(#observed_base,#(#pn),*)}
                pub open spec fn #req(f:#ft,#(#params),*)->bool {
                    true #(&& #observed_req)* &&
                    forall|z:#ft,pre:#st|::vstd::prelude::imply(pre.invariant()&&<#ft>::op(f,z)==Self::embed(pre),
                        #se::#owners(pre,f,<#ft>::unit(),#(#pn),*)&&#se::#enabled(pre,#(#pn),*))
                }
                pub proof fn #frame(f:#ft,#(#params),*)
                    requires Self::#req(f,#(#pn),*)
                    ensures ::vstd::resource::tsm_storage::frame_guard::<#pt>(f,Self::#guarded(f,#(#pn),*))
                {
                    // `frame_guard` is opaque; this is its proof (its users take it as an atom).
                    reveal(::vstd::resource::tsm_storage::frame_guard);
                    assert forall|z:#ft,pre:#st|Self::invariant(pre)&&<#ft>::op(f,z)==Self::embed(pre)
                        implies #guard_le by {
                        <#ft>::op_unit(f);
                        assert(#se::#enabled(pre,#(#pn),*));
                        let post=#se::#run(pre,#(#pn),*);
                        assert(true #(&& #observe_equal)*);
                        #guard_links
                        assert(#se::#guarded(pre,#(#pn),*)==Self::#guarded(f,#(#pn),*));
                        // The guard's storage fact (with its user proof) comes from safety.
                        #se::#safety(pre,#(#pn),*);
                        #guard_cases
                    }
                }
                pub proof fn #n(tracked token:&#tt,#(#params),*)->(tracked out:&#sty)
                    requires Self::#req(token.fragment(),#(#pn),*)
                    ensures *out==Self::#guarded(token.fragment(),#(#pn),*)
                {Self::#frame(token.fragment(),#(#pn),*);token.guard(Self::#guarded(token.fragment(),#(#pn),*))}
            });
        if local_ready.contains(&n.to_string()) {
            let declared_requires =
                crate::verified_readiness::declared_requires_spec(tr, &st, &params)?;
            let reads: Vec<_> =
                names.iter().copied().filter(|n| read.contains(&n.to_string())).collect();
            let api = crate::verified_readiness::local_ready_guard_api(
                crate::verified_readiness::GuardContext {
                    sm,
                    tr,
                    st: &st,
                    se: &se,
                    pe,
                    ft: &ft,
                    tt: &tt,
                    sty: &sty,
                    params: &params,
                    pn: &pn,
                    observed: &observed_req,
                    reads: &reads,
                    chain: chained.contains(&n.to_string()),
                },
            )?;
            local_ready_items.push((n.clone(), quote! {#declared_requires #api}));
        }
    } else if init {
        let base_req = quote! {#se::#enabled(#(#pn),*)};
        if let Some(p) = storage {
            let sty = p.ty();
            ops.push(quote!{
                    pub proof fn #n(tracked base:#sty,#(#params),*)->(tracked out:#tt)
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
        // The owned fragment after the transition: the chain's fragment (with the
        // patterns' values from `pre`) for the monoid fields, and the post-state's
        // values of the updated variables.
        let post_fragment =
            format_ident!("__tsm_post_fragment", span = proc_macro2::Span::mixed_site());
        let post_walk = crate::verified_chain::owned_post_fragment(sm, tr, &ft)?;
        let newfields: Vec<_> = names
            .iter()
            .map(|n| {
                if monoids::is_monoid_type(&fields[&n.to_string()].stype) {
                    quote! {#n:#post_fragment.#n}
                } else if changed.contains(&n.to_string()) {
                    quote! {#n:Some(ExclusiveRA::Exclusive(post.#n))}
                } else {
                    quote! {#n:owned.#n}
                }
            })
            .collect();
        let newfields =
            vec![quote! {{let #post_fragment = #post_walk; #fe{#marker_value #(#newfields),*}}}];
        let updated_variables: Vec<_> = names
            .iter()
            .copied()
            .filter(|n| {
                changed.contains(&n.to_string())
                    && matches!(fields[&n.to_string()].stype, ShardableType::Variable(_))
            })
            .collect();
        let effect_calls = vec![crate::verified_chain::frame_chain(
            sm,
            tr,
            &ft,
            &quote! {Self::__tsm_cfg_split},
            &quote! {Self::__tsm_cfg_join},
            quote! {Self::#owned_post(owned,pre,post,#(#pn),*)},
            &updated_variables,
        )?];
        if let Some(layout) = storage {
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
                &pt,
                &tt,
                &pn,
                &params,
                &owned_req,
                &observed_req,
                &newfields,
                &effect_calls,
                layout,
                withdraw,
                has_deposit(&tr.body),
                paired,
            ));
            if local_ready.contains(&n.to_string()) {
                let declared_requires =
                    crate::verified_readiness::declared_requires_spec(tr, &st, &params)?;
                let local_expression = storage_deposit(&tr.body, &fields, layout)?;
                let sty = layout.ty();
                let local_deposited = quote! {#[verifier::inline] pub open spec fn deposited(pre:#st,#(#params),*)->#sty{#local_expression}};
                let reads: Vec<_> =
                    names.iter().copied().filter(|n| read.contains(&n.to_string())).collect();
                let api = crate::verified_readiness::local_ready_api(
                    crate::verified_readiness::Context {
                        sm,
                        tr,
                        st: &st,
                        se: &se,
                        pe,
                        ft: &ft,
                        tt: &tt,
                        result: &result_ty,
                        result_expr: &result_expr,
                        params: &params,
                        pn: &pn,
                        owned: &owned_req,
                        observed: &observed_req,
                        reads: &reads,
                        storage: Some(layout),
                        deposits: has_deposit(&tr.body),
                        withdraws: withdraw,
                        paired,
                        chain: chained.contains(&n.to_string()),
                    },
                )?;
                local_ready_items
                    .push((n.clone(), quote! {#declared_requires #local_deposited #api}));
            }
        } else {
            ops.push(quote!{
                pub open spec fn #owned_post(owned:#ft,pre:#st,post:#st,#(#params),*)->#ft {#(#newfields)*}
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
            if local_ready.contains(&n.to_string()) {
                // Local readiness over the plain token: the same API without
                // deposits and withdrawals, and a witness for `observed`.
                let declared_requires =
                    crate::verified_readiness::declared_requires_spec(tr, &st, &params)?;
                let witness = format_ident!("{}_witness", n);
                let output_at = |z: TokenStream, pre: TokenStream, post: TokenStream| {
                    quote! {
                        #pre.invariant()&&<#ft>::op(<#ft>::op(owned,h),#z)==Self::embed(#pre)
                        && #se::#strong(#pre,#post,#(#pn),*)&&#post.invariant()&&new==Self::#owned_post(owned,#pre,#post,#(#pn),*)
                        &&<#ft>::op(<#ft>::op(new,h),#z)==Self::embed(#post)
                    }
                };
                let chosen = output_at(quote! {z}, quote! {pre}, quote! {post});
                let result = output_at(quote! {result.2}, quote! {result.0}, quote! {result.1});
                ops.push(quote! {
                        pub proof fn #witness(owned:#ft,h:#ft,new:#ft,#(#params),*)->(result:(#st,#st,#ft))
                            requires Self::#output(owned,h,new,#(#pn),*)
                            ensures #result
                        {
                            let (z,pre,post)=choose|z:#ft,pre:#st,post:#st| #chosen;
                            (pre,post,z)
                        }
                    });
                let reads: Vec<_> =
                    names.iter().copied().filter(|n| read.contains(&n.to_string())).collect();
                let api = crate::verified_readiness::local_ready_api(
                    crate::verified_readiness::Context {
                        sm,
                        tr,
                        st: &st,
                        se: &se,
                        pe,
                        ft: &ft,
                        tt: &tt,
                        result: &result_ty,
                        result_expr: &result_expr,
                        params: &params,
                        pn: &pn,
                        owned: &owned_req,
                        observed: &observed_req,
                        reads: &reads,
                        storage: None,
                        deposits: false,
                        withdraws: false,
                        paired: false,
                        chain: chained.contains(&n.to_string()),
                    },
                )?;
                local_ready_items.push((n.clone(), quote! {#declared_requires #api}));
            }
        }
    }
    Ok(())
}

/// The machine's module: `State`, `Fragment` and `Protocol` with their items, and the
/// local-ready API.
fn machine_module(ctx: &Ctx, items: &Items, field_api: &(TokenStream, TokenStream)) -> TokenStream {
    let (field_specs, field_takes) = field_api;
    let name = &ctx.sm.name;
    let broadcast = broadcast_use(ctx);
    let state = state_items(ctx, items);
    let fragment = fragment_items(ctx, field_specs);
    let protocol = protocol_items(ctx, items, field_takes);
    let local_ready = local_ready_module(ctx, &items.local_ready);
    quote! {
        pub mod #name {use super::*;::vstd::prelude::verus!{
            use ::vstd::iset::ISet;
            use ::vstd::resource::algebra::ResourceAlgebra;use ::vstd::resource::pcm::PCM;
            use ::vstd::resource::exclusive::ExclusiveRA;use ::vstd::resource::agree::AgreementRA;
            use ::vstd::resource::tsm::Machine;
            use ::vstd::resource::tsm_storage::StorageMachine;
            #broadcast
            #state
            #fragment
            #protocol
            #local_ready
        }}
    }
}

/// The lemma groups the machine's field kinds and storage need.
fn broadcast_use(ctx: &Ctx) -> TokenStream {
    let any_field = |kind: fn(&ShardableType) -> bool| ctx.sm.fields.iter().any(|f| kind(&f.stype));
    let sets = any_field(|t| matches!(t, ShardableType::Set(_) | ShardableType::PersistentSet(_)));
    let maps = ctx.storage.is_some()
        || any_field(|t| {
            matches!(
                t,
                ShardableType::Map(..)
                    | ShardableType::IMap(..)
                    | ShardableType::PersistentMap(..)
                    | ShardableType::PersistentIMap(..)
            )
        });
    let multisets = any_field(|t| matches!(t, ShardableType::Multiset(_)));
    let mut groups = vec![quote! {::vstd::iset::group_iset_lemmas}];
    if sets {
        groups.push(quote! {::vstd::set::group_set_lemmas});
    }
    if maps {
        groups.push(quote! {::vstd::imap::group_imap_lemmas});
        groups.push(quote! {::vstd::map::group_map_lemmas});
    }
    if multisets {
        groups.push(quote! {::vstd::multiset::group_multiset_axioms});
    }
    if groups.len() == 1 {
        quote! {broadcast use ::vstd::iset::group_iset_lemmas;}
    } else {
        quote! {broadcast use {#(#groups),*};}
    }
}

/// `State`, with the invariant, the storage projection, the transitions' relations and
/// induction lemmas, and the user's functions.
fn state_items(ctx: &Ctx, items: &Items) -> TokenStream {
    let Ctx { bundle, datatype_attrs, decl, where_clause, st, marker_field, decls, .. } = ctx;
    let state_fields = &decls.state_fields;
    let invariants = &bundle.extras.invariants;
    let invariant_names = invariants.iter().map(|i| &i.func.sig.ident);
    let invariant_fns = invariants.iter().map(|i| {
        let name = &i.func.sig.ident;
        let body = &i.func.block;
        quote! {pub open spec fn #name(&self)->bool #body}
    });
    let normal = bundle.normal_fns.iter().map(|f| quote! {::vstd::prelude::verus_impl!{#f}});
    let storage_state = storage_projection(ctx);
    let Items { relations, lemmas, .. } = items;
    quote! {
        #(#datatype_attrs)*
        pub struct State #decl #where_clause {#marker_field #(#state_fields),*}
        impl #decl #st #where_clause {
            pub open spec fn invariant(&self)->bool {true #(&&self.#invariant_names())*}
            #storage_state #(#invariant_fns)* #(#relations)* #(#lemmas)* #(#normal)*
        }
    }
}

/// `State::__storage`, the state's storage, on machines with storage.
fn storage_projection(ctx: &Ctx) -> TokenStream {
    let Some(layout) = ctx.storage else { return quote! {} };
    let sty = layout.ty();
    let projection = layout.projection(quote! {s});
    quote! {pub open spec fn __storage(&self)->#sty{let s=*self;#projection}}
}

/// `Fragment`, with the field API and setters, and its resource algebra: the product of
/// the fields' components.
fn fragment_items(ctx: &Ctx, field_specs: &TokenStream) -> TokenStream {
    let Ctx {
        datatype_attrs, decl, where_clause, ft, fe, marker_field, marker_value, decls, ..
    } = ctx;
    let FieldDecls { names, types, fragment_fields, .. } = decls;
    let setters = fragment_setters(ctx);
    quote! {
        #(#datatype_attrs)*
        pub struct Fragment #decl #where_clause {#marker_field #(#fragment_fields),*}
        impl #decl #ft #where_clause {#field_specs #(#setters)*}
        impl #decl ResourceAlgebra for #ft #where_clause {
            open spec fn valid(self)->bool {true #(&&self.#names.valid())*}
            open spec fn op(a:Self,b:Self)->Self {#fe{#marker_value #(#names:<#types>::op(a.#names,b.#names)),*}}
            proof fn associative(a:Self,b:Self,c:Self){#(<#types>::associative(a.#names,b.#names,c.#names);)*}
            proof fn commutative(a:Self,b:Self){#(<#types>::commutative(a.#names,b.#names);)*}
            proof fn valid_op(a:Self,b:Self){#(<#types>::valid_op(a.#names,b.#names);)*}
        }
        impl #decl PCM for #ft #where_clause {
            open spec fn unit()->Self {#fe{#marker_value #(#names:<#types>::unit()),*}}
            proof fn op_unit(self){#(self.#names.op_unit();)*}
            proof fn unit_valid(){#(<#types>::unit_valid();)*}
        }
    }
}

/// `Fragment::__tsm_set_<field>` of each monoid field, replacing its component.
fn fragment_setters(ctx: &Ctx) -> Vec<TokenStream> {
    ctx.sm
        .fields
        .iter()
        .filter(|f| monoids::is_monoid_type(&f.stype))
        .map(|f| {
            let name = &f.name;
            let setter = format_ident!("__tsm_set_{}", name);
            let component = monoids::component_type(&f.stype);
            quote! {pub open spec fn #setter(self,part:#component)->Self{Self{#name:part,..self}}}
        })
        .collect()
}

/// `Protocol` with its `Machine` (and `StorageMachine`) impl, the labels, `Token`, and
/// the impl with the raw operations.
fn protocol_items(ctx: &Ctx, items: &Items, field_takes: &TokenStream) -> TokenStream {
    let Ctx {
        sm,
        datatype_attrs,
        decl,
        where_clause,
        st,
        se,
        ft,
        fe,
        pt,
        marker_field,
        marker_value,
        decls,
        ..
    } = ctx;
    let FieldDecls { embeds, observations, .. } = decls;
    // Labels are ordinary first parameters of the relations and operations;
    // only their declarations need to be emitted.
    let labels = [&sm.init_label, &sm.transition_label];
    let storage_machine = storage_machine(ctx);
    let token_type = token_type(ctx);
    let observation = transition_observation(ctx);
    let observation_inline = if ctx.local_ready.is_empty() {
        quote! {}
    } else {
        quote! {#[verifier::inline]}
    };
    let operations = &items.operations;
    let calculus = cfg_split_join(ctx);
    quote! {
        #(#datatype_attrs)*
        pub struct Protocol #decl #where_clause {#marker_field}
        impl #decl Machine for #pt #where_clause {
            type Fragment=#ft;type State=#st;
            open spec fn invariant(s:#st)->bool{s.invariant()}
            open spec fn embed(s:#st)->#ft {#fe{#marker_value #(#embeds),*}}
        }
        #storage_machine
        #(#labels)*
        #[allow(type_alias_bounds)]
        pub type Token #decl #where_clause=#token_type;
        #observation
        impl #decl #pt #where_clause {
            #observation_inline
            pub open spec fn __observed(f:#ft)->#st {#se{#marker_value #(#observations),*}}
            #field_takes #(#operations)* #calculus
        }
    }
}

/// The storage layout's declarations and the `StorageMachine` impl, on machines with
/// storage.
fn storage_machine(ctx: &Ctx) -> TokenStream {
    let Ctx { decl, where_clause, st, pt, .. } = ctx;
    let Some(layout) = ctx.storage else { return quote! {} };
    let sty = layout.ty();
    let (key_ty, value_ty) = (layout.key_ty(), layout.value_ty());
    let storage_decl = layout.decl(decl, where_clause, st);
    quote! {#storage_decl
    impl #decl ::vstd::resource::tsm_storage::StorageMachine for #pt #where_clause {
        type Key=#key_ty;type Value=#value_ty;
        open spec fn storage(s:#st)->#sty{s.__storage()}
    }}
}

/// The type of the machine's tokens: storage tokens on machines with storage.
fn token_type(ctx: &Ctx) -> TokenStream {
    let pt = &ctx.pt;
    if ctx.storage.is_some() {
        quote! {::vstd::resource::tsm_storage::StorageToken<#pt>}
    } else {
        quote! {::vstd::resource::tsm::Token<#pt>}
    }
}

/// `TransitionObservation`, the result of the local-ready operations, on machines with a
/// local-ready API.
fn transition_observation(ctx: &Ctx) -> TokenStream {
    let Ctx { datatype_attrs, decl, where_clause, st, ft, tt, .. } = ctx;
    if ctx.local_ready.is_empty() {
        quote! {}
    } else if let Some(layout) = ctx.storage {
        let sty = layout.ty();
        quote! {
            #(#datatype_attrs)*
            pub tracked struct TransitionObservation #decl #where_clause {
                pub tracked token:#tt,
                pub tracked withdrawn:#sty,
                pub ghost before:#st,
                pub ghost after:#st,
                pub ghost frame:#ft,
            }
        }
    } else {
        // Without storage, nothing is withdrawn.
        quote! {
            #(#datatype_attrs)*
            pub tracked struct TransitionObservation #decl #where_clause {
                pub tracked token:#tt,
                pub ghost before:#st,
                pub ghost after:#st,
                pub ghost frame:#ft,
            }
        }
    }
}

/// The statement calculus's configuration split (of the monoid fields: the chains have
/// no steps of the others) and join (`verified_chain`), for the readiness chains and the
/// frames of the non-init transitions.
fn cfg_split_join(ctx: &Ctx) -> TokenStream {
    if !ctx.sm.transitions.iter().any(|tr| tr.kind != TransitionKind::Init) {
        return quote! {};
    }
    let Ctx { fields, st, ft, decls, .. } = ctx;
    let FieldDecls { names, types, embed_values, .. } = decls;
    let calculus = quote! {::vstd::resource::tsm_calculus};
    let monoid = |n: &&Ident| monoids::is_monoid_type(&fields[&n.to_string()].stype);
    let (split_names, split_values): (Vec<&&Ident>, Vec<&TokenStream>) =
        names.iter().zip(embed_values).filter(|(n, _)| monoid(n)).unzip();
    // The join takes the configurations of the components the frames' chains step
    // (not the counting kinds'), and the others' plain equalities.
    let stepped =
        |n: &&Ident| monoid(n) && !crate::verified_chain::counting(&fields[&n.to_string()].stype);
    let (join_names, join_values): (Vec<&&Ident>, Vec<&TokenStream>) =
        names.iter().zip(embed_values).filter(|(n, _)| stepped(n)).unzip();
    let (other_names, other_values): (Vec<&&Ident>, Vec<&TokenStream>) =
        names.iter().zip(embed_values).filter(|(n, _)| !stepped(n)).unzip();
    let other_types: Vec<_> =
        names.iter().zip(types).filter(|(n, _)| !stepped(n)).map(|(_, t)| t).collect();
    quote! {
        pub proof fn __tsm_cfg_split(o:#ft,h:#ft,z:#ft,s:#st)
            requires <#ft>::op(<#ft>::op(o,h),z)==Self::embed(s)
            ensures true #(&& #calculus::cfg(o.#split_names,h.#split_names,z.#split_names,#split_values))*
        {#(#calculus::cfg_iff(o.#split_names,h.#split_names,z.#split_names,#split_values);)*}
        pub proof fn __tsm_cfg_join(o:#ft,h:#ft,z:#ft,s:#st)
            requires true #(&& #calculus::cfg(o.#join_names,h.#join_names,z.#join_names,#join_values))*
                #(&& <#other_types>::op(<#other_types>::op(o.#other_names,h.#other_names),z.#other_names)==(#other_values))*
            ensures <#ft>::op(<#ft>::op(o,h),z)==Self::embed(s)
        {#(#calculus::cfg_iff(o.#join_names,h.#join_names,z.#join_names,#join_values);)*}
    }
}

/// Each local-ready transition `t` gets a type `local_ready::t` whose associated
/// items are its local-ready API (`local_ready::t::run(..)`, ...): its own
/// namespace, so these names cannot collide with other transitions' or user
/// items. The impls are in the machine module, where the transition's
/// expressions resolve as in `State`'s impl.
fn local_ready_module(ctx: &Ctx, apis: &[(Ident, TokenStream)]) -> TokenStream {
    if apis.is_empty() {
        return quote! {};
    }
    let Ctx { datatype_attrs, decl, where_clause, type_args, marker_field, .. } = ctx;
    let structs = apis.iter().map(|(name, _)| {
        quote! {
            #(#datatype_attrs)*
            #[allow(non_camel_case_types)]
            pub struct #name #decl #where_clause {#marker_field}
        }
    });
    let impls = apis.iter().map(|(name, api)| {
        quote! {impl #decl local_ready::#name #type_args #where_clause {#api}}
    });
    quote! {
        /// The local-ready API of the machine's transitions (`local_ready::t`).
        pub mod local_ready {
            #[allow(unused_imports)]
            use super::*;
            #(#structs)*
        }
        #(#impls)*
    }
}

/// The operations of a transition on a machine with storage: its requirement, outputs,
/// witness and frame lemma, and its storage exchanges.
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
    pt: &TokenStream,
    tt: &TokenStream,
    pn: &Vec<&Ident>,
    params: &Vec<TokenStream>,
    owned_req: &Vec<TokenStream>,
    observed_req: &Vec<TokenStream>,
    newfields: &Vec<TokenStream>,
    effect_calls: &Vec<TokenStream>,
    storage: &crate::verified_storage_tagged::Tagged,
    withdraws: bool,
    deposits: bool,
    paired: bool,
) -> TokenStream {
    let map = storage.ty();
    let unit = storage.unit();
    let tracked_unit = storage.tracked_unit();
    let pre_s = quote! {pre.__storage()};
    let post_s = quote! {post.__storage()};
    let withdrawn_spec = storage.minus(storage.op(pre_s.clone(), quote! {deposit}), post_s.clone());
    let mut pair_name = "__tsm_storage_exchange_pair".to_string();
    while pn.iter().any(|name| name.to_string() == pair_name) {
        pair_name.push('_');
    }
    let pair = Ident::new(&pair_name, proc_macro2::Span::mixed_site());
    let witness = format_ident!("{}_witness", n);
    let output_at = format_ident!("__tsm_{}_output_at", n);
    let outputs = quote! {ISet::new(|#pair:(#ft,#map)|Self::#output(owned,h,#pair.0,deposit,#pair.1,#(#pn),*))};
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
        unit.clone()
    };
    let deposit_init = if deposits {
        quote! {}
    } else {
        quote! {let tracked deposit:#map=#tracked_unit;}
    };
    let return_ens = if withdraws {
        quote! {Self::#output(owned.fragment(),shared.fragment(),out.0.fragment(),#deposit_spec,out.1,#(#pn),*)}
    } else {
        quote! {Self::#output(owned.fragment(),shared.fragment(),out.fragment(),#deposit_spec,#unit,#(#pn),*)}
    };
    let plain_ens = if withdraws {
        quote! {Self::#output(owned.fragment(),<#ft>::unit(),out.0.fragment(),#deposit_spec,out.1,#(#pn),*)}
    } else {
        quote! {Self::#output(owned.fragment(),<#ft>::unit(),out.fragment(),#deposit_spec,#unit,#(#pn),*)}
    };
    let return_value = if withdraws {
        quote! {(out,withdrawn)}
    } else {
        quote! {
            assert(withdrawn==#unit);
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
        quote! {&&withdrawn==#withdrawn_spec}
    };
    let withdrawal_shape = if withdraws {
        quote! {true}
    } else {
        quote! {withdrawn==#unit}
    };
    let st_pre = quote! {Self::storage(pre)};
    let st_post = quote! {Self::storage(post)};
    let whole = storage.op(st_pre.clone(), quote! {deposit});
    let withdrawal_proof = if withdraws {
        quote! {}
    } else if paired {
        // The old storage and the deposit are covered by the new storage
        // (the executor's `covered` fact): nothing is withdrawn.
        quote! {
            assert(::vstd::prelude::ext_equal(withdrawn,#unit)) by {
                assert forall|__tsm_key| !withdrawn.contains_key(__tsm_key) by {};
            }
        }
    } else {
        quote! {::vstd::resource::tsm_storage::storage_withdrawn_none(#st_pre,#st_post,deposit);}
    };
    let output_storage = if paired {
        let disjoint = storage.disjoint(pre_s.clone(), quote! {deposit});
        let within = storage.le(post_s.clone(), storage.op(pre_s.clone(), quote! {deposit}));
        quote! {
            deposit==#se::#deposited(pre,#(#pn),*)
                &&#disjoint
                &&#within
        }
    } else {
        let delta = storage.minus(post_s.clone(), pre_s.clone());
        quote! {deposit==#delta}
    };
    let transfer_proof = if paired {
        let disjoint = storage.disjoint(st_pre.clone(), quote! {deposit});
        let within = storage.le(st_post.clone(), whole.clone());
        quote! {
            assert(deposit==#se::#deposited(pre,#(#pn),*));
            assert(#disjoint);
            assert(#within);
        }
    } else {
        quote! {}
    };
    let frame_withdrawn = if monotone {
        quote! {assert(Self::#output_at(owned,h,new,deposit,#unit,#(#pn,)* z,pre,post));}
    } else {
        let withdrawn = storage.minus(whole.clone(), st_post.clone());
        quote! {
            let withdrawn=#withdrawn;
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
            pub open spec fn #owned_post(owned:#ft,pre:#st,post:#st,#(#params),*)->#ft {#(#newfields)*}
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
