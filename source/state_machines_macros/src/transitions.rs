use crate::ast::INIT_LABEL_TYPE_NAME;
use crate::ast::TRANSITION_LABEL_TYPE_NAME;
use crate::ast::{
    Field, MonoidElt, MonoidStmtType, ShardableType, SpecialOp, SplitKind, Transition,
    TransitionKind, TransitionStmt, SM,
};
use crate::check_bind_stmts::check_bind_stmts;
use crate::check_birds_eye::check_birds_eye;
use crate::ident_visitor::validate_idents_transition;
use crate::inherent_safety_conditions::check_inherent_conditions;
use crate::util::{combine_errors_or_ok, combine_results};
use proc_macro2::Span;
use std::collections::HashSet;
use syn_verus::parse;
use syn_verus::spanned::Spanned;
use syn_verus::{Error, GenericArgument, GenericParam, Ident, Path, PathArguments, Type, TypePath};

pub fn fields_contain(fields: &Vec<Field>, ident: &Ident) -> bool {
    for f in fields {
        if f.name.to_string() == ident.to_string() {
            return true;
        }
    }
    return false;
}

pub fn get_field<'a>(fields: &'a Vec<Field>, ident: &Ident) -> &'a Field {
    for f in fields {
        if f.name.to_string() == ident.to_string() {
            return f;
        }
    }
    panic!("could not find field");
}

/// Check that every update statement actually refers to a valid field.
/// We'll assume that all the fields are valid in the later checks.

fn check_updates_refer_to_valid_fields(
    fields: &Vec<Field>,
    ts: &TransitionStmt,
    errors: &mut Vec<Error>,
) {
    match ts {
        TransitionStmt::Block(_, v) => {
            for t in v.iter() {
                check_updates_refer_to_valid_fields(fields, t, errors);
            }
        }
        TransitionStmt::Split(span, kind, splits) => {
            match kind {
                SplitKind::Special(f, _, _, _) => {
                    if !fields_contain(fields, f) {
                        errors.push(Error::new(
                            span.span(),
                            format!("field '{}' not found", f.to_string()),
                        ));
                    }
                }
                _ => {}
            }
            for split in splits {
                check_updates_refer_to_valid_fields(fields, split, errors);
            }
        }
        TransitionStmt::Require(_, _) => {}
        TransitionStmt::Assert(..) => {}
        TransitionStmt::Update(span, f, _)
        | TransitionStmt::SubUpdate(span, f, _, _)
        | TransitionStmt::Initialize(span, f, _) => {
            if !fields_contain(fields, f) {
                errors
                    .push(Error::new(span.span(), format!("field '{}' not found", f.to_string())));
            }
        }
        TransitionStmt::PostCondition(..) => {}
    }
}

/// For each field, checks that this field is initialized *exactly* once.
/// This check applies for *all* fields.

fn check_exactly_one_init(sm: &SM, ts: &TransitionStmt, errors: &mut Vec<Error>) {
    for f in &sm.fields {
        match check_exactly_one_init_rec(f, ts) {
            Ok(Some(_)) => {}
            Ok(None) => {
                errors.push(Error::new(
                    *ts.get_span(),
                    format!(
                        "itialization procedure does not initialize field '{}'",
                        f.name.to_string()
                    ),
                ));
            }
            Err(e) => errors.push(e),
        }
    }
}

fn check_exactly_one_init_rec(field: &Field, ts: &TransitionStmt) -> parse::Result<Option<Span>> {
    match ts {
        TransitionStmt::Block(_, v) => {
            let mut o = None;
            for t in v.iter() {
                let o2 = check_exactly_one_init_rec(field, t)?;
                o = match (o, o2) {
                    (None, None) => None,
                    (Some(s), None) => Some(s),
                    (None, Some(s)) => Some(s),
                    (Some(_s1), Some(s2)) => {
                        return Err(Error::new(
                            s2,
                            format!(
                                "field '{}' might be initialized multiple times",
                                field.name.to_string()
                            ),
                        ));
                    }
                };
            }
            Ok(o)
        }
        TransitionStmt::Split(_, SplitKind::Let(..), es) => {
            assert!(es.len() == 1);
            let child = &es[0];
            check_exactly_one_init_rec(field, child)
        }
        TransitionStmt::Split(if_span, SplitKind::If(_), es) => {
            assert!(es.len() == 2);
            let o1 = check_exactly_one_init_rec(field, &es[0])?;
            let o2 = check_exactly_one_init_rec(field, &es[1])?;
            // The user is required to initialize the field in both branches if they update
            // it in either. Therefore we need to produce an error if there was a mismatch
            // between the two branches.
            match (o1, o2) {
                (Some(span1), Some(_span2)) => Ok(Some(span1)),
                (None, None) => Ok(None),
                (Some(_span1), None) => {
                    return Err(Error::new(
                        *if_span,
                        format!(
                            "for initialization, both branches of an if-statement must initialize the same fields; the else-branch does not initialize '{}'",
                            field.name
                        ),
                    ));
                }
                (None, Some(_span1)) => {
                    return Err(Error::new(
                        *if_span,
                        format!(
                            "for initialization, both branches of an if-statement must initialize the same fields; the if-branch does not initialize '{}'",
                            field.name
                        ),
                    ));
                }
            }
        }
        TransitionStmt::Split(_span, SplitKind::Match(..), es) => {
            let o1 = check_exactly_one_init_rec(field, &es[0])?;
            for i in 1..es.len() {
                let oi = check_exactly_one_init_rec(field, &es[i])?;
                match (o1, oi) {
                    (Some(_span1), Some(_span2)) => {}
                    (None, None) => {}
                    (Some(_span1), None) => {
                        return Err(Error::new(
                            *es[i].get_span(),
                            format!(
                                "for initialization, all branches of a match-statement must initialize the same fields; this branch does not initialize '{}'",
                                field.name
                            ),
                        ));
                    }
                    (None, Some(_span1)) => {
                        return Err(Error::new(
                            *es[0].get_span(),
                            format!(
                                "for initialization, all branches of a match-statement must initialize the same fields; this branch does not initialize '{}'",
                                field.name
                            ),
                        ));
                    }
                }
            }
            Ok(o1)
        }
        TransitionStmt::Split(_, SplitKind::Special(..), _) => Ok(None),
        TransitionStmt::Require(_, _) => Ok(None),
        TransitionStmt::Assert(..) => Ok(None),
        TransitionStmt::Initialize(span, id, _) => {
            if id.to_string() == field.name.to_string() {
                Ok(Some(*span))
            } else {
                Ok(None)
            }
        }
        TransitionStmt::Update(..) => Ok(None),
        TransitionStmt::SubUpdate(..) => Ok(None),
        TransitionStmt::PostCondition(..) => Ok(None),
    }
}

/// For each field, checks that this field is updated *at most* once.
/// Only checks 'update' statements, not special ops, and it
/// only does the check for fields for which 'update' statements are supported.
/// Ignores sub-updates, there is actually reason to have more than one of those.

fn check_at_most_one_update(sm: &SM, ts: &TransitionStmt, errors: &mut Vec<Error>) {
    for f in &sm.fields {
        if is_allowed_in_update_in_normal_transition(&f.stype) {
            match check_at_most_one_update_rec(f, ts) {
                Ok(_) => {}
                Err(e) => errors.push(e),
            }
        }
    }
}

fn check_at_most_one_update_rec(field: &Field, ts: &TransitionStmt) -> parse::Result<Option<Span>> {
    match ts {
        TransitionStmt::Block(_, v) => {
            let mut o = None;
            for t in v.iter() {
                let o2 = check_at_most_one_update_rec(field, t)?;
                o = match (o, o2) {
                    (None, None) => None,
                    (Some(s), None) => Some(s),
                    (None, Some(s)) => Some(s),
                    (Some(_s1), Some(s2)) => {
                        return Err(Error::new(
                            s2,
                            format!(
                                "field '{}' might be updated multiple times",
                                field.name.to_string()
                            ),
                        ));
                    }
                };
            }
            Ok(o)
        }
        TransitionStmt::Split(_, _, es) => {
            // In contrast to the initialization case,
            // it _is_ allowed to perform an 'update' in only one branch.
            // We return 'Some(_)' if any of the branches returned Some(_).
            let mut o = None;
            for e in es {
                let o1 = check_at_most_one_update_rec(field, e)?;
                o = o.or(o1);
            }
            Ok(o)
        }
        TransitionStmt::Require(_, _) => Ok(None),
        TransitionStmt::Assert(..) => Ok(None),
        TransitionStmt::Initialize(_, _, _) => Ok(None),
        TransitionStmt::SubUpdate(..) => Ok(None),
        TransitionStmt::Update(span, id, _) => {
            if id.to_string() == field.name.to_string() {
                Ok(Some(*span))
            } else {
                Ok(None)
            }
        }
        TransitionStmt::PostCondition(..) => Ok(None),
    }
}

/// Returns `true` if you're allowed to have an 'update' statement for the given
/// sharding strategy. Naturally, this is false for constants, which cannot be updated
/// at all, and also false for option, multiset, etc. which have to be updated with
/// special ops.

fn is_allowed_in_update_in_normal_transition(stype: &ShardableType) -> bool {
    match stype {
        ShardableType::Variable(_) | ShardableType::NotTokenized(_) => true,

        ShardableType::Constant(_)
        | ShardableType::Multiset(_)
        | ShardableType::Option(_)
        | ShardableType::Set(_)
        | ShardableType::Map(_, _)
        | ShardableType::StorageOption(_)
        | ShardableType::StorageMap(_, _)
        | ShardableType::PersistentMap(_, _)
        | ShardableType::PersistentOption(_)
        | ShardableType::PersistentSet(_)
        | ShardableType::Count
        | ShardableType::PersistentCount
        | ShardableType::Bool
        | ShardableType::PersistentBool => false,
    }
}

/// Big matrix for whether a given sharding type is allowed for a given SpecialOp type

fn is_allowed_in_special_op(
    span: Span,
    stype: &ShardableType,
    sop: &SpecialOp,
) -> parse::Result<()> {
    match stype {
        ShardableType::Constant(_)
        | ShardableType::Variable(_)
        | ShardableType::NotTokenized(_) => {
            let stmt_name = sop.stmt.name();
            let strat = stype.strategy_name();
            Err(Error::new(
                span,
                format!(
                    "'{stmt_name:}' statement not allowed for field with sharding strategy '{strat:}'; use 'update' instead"
                ),
            ))
        }

        ShardableType::Map(_, _)
        | ShardableType::Option(_)
        | ShardableType::Set(_)
        | ShardableType::Bool
        | ShardableType::Multiset(_)
        | ShardableType::StorageOption(_)
        | ShardableType::StorageMap(_, _)
        | ShardableType::PersistentMap(_, _)
        | ShardableType::PersistentOption(_)
        | ShardableType::PersistentSet(_)
        | ShardableType::PersistentBool
        | ShardableType::PersistentCount
        | ShardableType::Count => {
            if !op_matches_type(stype, &sop.elt) {
                let syntax = sop.elt.syntax();
                let elt_name = sop.elt.type_name();
                let strat = stype.strategy_name();
                return Err(Error::new(
                    span,
                    format!(
                        "`{syntax:}` gives a `{elt_name:}` element but the given field has sharding strategy '{strat:}'",
                    ),
                ));
            }

            let strat_is_persistent = stype.is_persistent();
            let strat_is_storage = stype.is_storage();
            let op_is_storage = sop.stmt.is_for_storage();

            assert!(!strat_is_storage || !strat_is_persistent);

            match sop.stmt {
                MonoidStmtType::Add(is_max) => {
                    if strat_is_persistent && !is_max {
                        let strat = stype.strategy_name();
                        return Err(Error::new(
                            span,
                            format!(
                                "for the persistent strategy `{strat:}`, use `(union)=` instead of `+=`"
                            ),
                        ));
                    } else if !strat_is_persistent && is_max {
                        let strat = stype.strategy_name();
                        return Err(Error::new(
                            span,
                            format!(
                                "for the strategy `{strat:}`, use `+=` instead of `(union)=` (only persistent strategies should use `(union)=`)"
                            ),
                        ));
                    }
                }
                _ => {}
            }

            if stype.is_persistent() && sop.is_remove() {
                let stmt_name = sop.stmt.name();
                let strat = stype.strategy_name();
                return Err(Error::new(
                    span,
                    format!(
                        "'{stmt_name:}' statement not allowed for field with sharding strategy '{strat:}'; a persistent field's value can only grow, never remove or modify its data"
                    ),
                ));
            }

            if !strat_is_storage && op_is_storage {
                let stmt_name = sop.stmt.name();
                let strat = stype.strategy_name();
                return Err(Error::new(
                    span,
                    format!(
                        "'{stmt_name:}' statement not allowed for field with sharding strategy '{strat:}'; '{stmt_name:}' is only for storage types; use add/remove/have statements instead"
                    ),
                ));
            }
            if strat_is_storage && !op_is_storage {
                let stmt_name = sop.stmt.name();
                let strat = stype.strategy_name();
                return Err(Error::new(
                    span,
                    format!(
                        "'{stmt_name:}' statement not allowed for field with sharding strategy '{strat:}'; use deposit/withdraw/guard statements for storage strategies"
                    ),
                ));
            }

            Ok(())
        }
    }
}

fn op_matches_type(stype: &ShardableType, elt: &MonoidElt) -> bool {
    match stype {
        ShardableType::Constant(_)
        | ShardableType::Variable(_)
        | ShardableType::NotTokenized(_) => false,

        ShardableType::Map(_, _)
        | ShardableType::PersistentMap(_, _)
        | ShardableType::StorageMap(_, _) => match elt {
            MonoidElt::General(_) => true,
            MonoidElt::SingletonKV(_, _) => true,
            _ => false,
        },

        ShardableType::Set(_) | ShardableType::PersistentSet(_) => match elt {
            MonoidElt::General(_) => true,
            MonoidElt::SingletonSet(_) => true,
            _ => false,
        },

        ShardableType::Bool | ShardableType::PersistentBool => match elt {
            MonoidElt::General(_) => true,
            MonoidElt::True => true,
            _ => false,
        },

        ShardableType::Option(_)
        | ShardableType::PersistentOption(_)
        | ShardableType::StorageOption(_) => match elt {
            MonoidElt::General(_) => true,
            MonoidElt::OptionSome(_) => true,
            _ => false,
        },

        ShardableType::Multiset(_) => match elt {
            MonoidElt::General(_) => true,
            MonoidElt::SingletonMultiset(_) => true,
            _ => false,
        },

        ShardableType::Count | ShardableType::PersistentCount => match elt {
            MonoidElt::General(_) => true,
            _ => false,
        },
    }
}

/// Check that every Update and SpecialOp statement is allowed for the given
/// sharding strategy of its field.
///
/// This check is meant for 'transition' and 'readonly' transitions, so it also checks
/// that there are no 'init' statements, which are only meaningful in 'init' transitions.
///
/// It also checks that no fields are modified if it's a 'readonly' transition,
/// and conversely for a 'transition' transition, it checks that there are no
/// guard operations (these operations are allowed ONLY in 'readonly' transitions).

fn check_valid_ops(
    fields: &Vec<Field>,
    ts: &TransitionStmt,
    is_readonly: bool,
    is_property: bool,
    errors: &mut Vec<Error>,
) {
    match ts {
        TransitionStmt::Block(_, v) => {
            for t in v.iter() {
                check_valid_ops(fields, t, is_readonly, is_property, errors);
            }
        }
        TransitionStmt::Split(span, SplitKind::Special(f, op, _, _), es) => {
            let field = get_field(fields, f);
            match is_allowed_in_special_op(*span, &field.stype, op) {
                Ok(()) => {}
                Err(err) => {
                    errors.push(err);
                }
            }
            if is_readonly && op.is_modifier() {
                errors.push(Error::new(
                    *span,
                    format!("'{:}' statement not allowed in readonly transition", op.stmt.name()),
                ));
            }
            if is_property && op.is_modifier() {
                errors.push(Error::new(
                    *span,
                    format!("'{:}' statement not allowed in 'property' definition", op.stmt.name()),
                ));
            }
            if !is_readonly && !is_property && op.is_only_allowed_in_property_or_readonly() {
                errors.push(Error::new(
                    *span,
                    format!("'{:}' statement only allowed in 'readonly' transition or 'property' definition", op.stmt.name()),
                ));
            }

            for e in es {
                check_valid_ops(fields, e, is_readonly, is_property, errors);
            }
        }
        TransitionStmt::Split(_, _, es) => {
            for e in es {
                check_valid_ops(fields, e, is_readonly, is_property, errors);
            }
        }
        TransitionStmt::Require(_, _) => {}
        TransitionStmt::Assert(..) => {}
        TransitionStmt::Initialize(span, _, _) => {
            errors.push(Error::new(
                span.span(),
                format!("'init' statement not allowed outside 'init' routine"),
            ));
        }
        TransitionStmt::Update(span, f, _) | TransitionStmt::SubUpdate(span, f, _, _) => {
            let field = get_field(fields, f);
            if !is_allowed_in_update_in_normal_transition(&field.stype) {
                errors.push(Error::new(
                    span.span(),
                    format!(
                        "'update' statement not allowed for field with sharding strategy '{:}'",
                        field.stype.strategy_name()
                    ),
                ));
            }
            if is_readonly {
                errors.push(Error::new(
                    span.span(),
                    format!("'update' statement not allowed in readonly transition"),
                ));
            }
            if is_property {
                errors.push(Error::new(
                    span.span(),
                    format!("'update' statement not allowed in property definition"),
                ));
            }
        }
        TransitionStmt::PostCondition(..) => {
            panic!("should not have created any PostCondition statement yet");
        }
    }
}

/// Version of `check_valid_ops` but for 'init' routines.
/// The only valid ops in an 'init' routine are the 'init' statements.
/// Updates and special ops are all disallowed.

fn check_valid_ops_init(fields: &Vec<Field>, ts: &TransitionStmt, errors: &mut Vec<Error>) {
    match ts {
        TransitionStmt::Block(_, v) => {
            for t in v.iter() {
                check_valid_ops_init(fields, t, errors);
            }
        }
        TransitionStmt::Split(span, kind, es) => {
            match kind {
                SplitKind::Special(..) => {
                    errors.push(Error::new(
                        *span,
                        format!(
                            "'{:}' statement not allowed in initialization; use 'init' instead",
                            ts.statement_name()
                        ),
                    ));
                }
                _ => {}
            }

            for e in es {
                check_valid_ops_init(fields, e, errors);
            }
        }
        TransitionStmt::Require(_, _) => {}
        TransitionStmt::Assert(span, _, _) => {
            errors.push(Error::new(*span, "'assert' statement not allowed in initialization"));
        }
        TransitionStmt::Initialize(_, _, _) => {}
        TransitionStmt::Update(span, _, _) | TransitionStmt::SubUpdate(span, _, _, _) => {
            errors.push(Error::new(
                *span,
                "'update' statement not allowed in initialization; use 'init' instead",
            ));
        }
        TransitionStmt::PostCondition(..) => {
            panic!("should have have PostCondition statement here");
        }
    }
}

/// Check that the identifiers bound in 'let' statements are all distinct,
/// and that they don't overlap with the parameters of a transition.

fn check_let_shadowing(trans: &Transition, errors: &mut Vec<Error>) {
    let mut ids = trans.params.iter().map(|p| p.name.to_string()).collect();
    check_let_shadowing_rec(&trans.body, &mut ids, errors)
}

fn check_let_shadowing_rec(ts: &TransitionStmt, ids: &mut Vec<String>, errors: &mut Vec<Error>) {
    let new_ids = stmt_get_bound_idents(ts);
    for id in new_ids {
        let s = id.to_string();
        if ids.contains(&s) {
            errors.push(Error::new(
                id.span(),
                format!(
                    "state machine transitions forbid multiple bound variables with the same name"
                ),
            ));
        } else {
            ids.push(s);
        }
    }

    match ts {
        TransitionStmt::Block(_, v) => {
            for t in v {
                check_let_shadowing_rec(t, ids, errors);
            }
        }
        TransitionStmt::Split(_, _, es) => {
            for e in es {
                check_let_shadowing_rec(e, ids, errors);
            }
        }
        TransitionStmt::Require(..) => {}
        TransitionStmt::Assert(..) => {}
        TransitionStmt::SubUpdate(..) => {}
        TransitionStmt::Update(..) => {}
        TransitionStmt::Initialize(..) => {}
        TransitionStmt::PostCondition(..) => {}
    }
}

fn stmt_get_bound_idents(ts: &TransitionStmt) -> Vec<Ident> {
    match ts {
        TransitionStmt::Block(_, _) => {}
        TransitionStmt::Split(_span, SplitKind::Let(pat, _, _, _), _) => {
            return crate::ident_visitor::pattern_get_bound_idents(pat);
        }
        TransitionStmt::Split(_span, SplitKind::Special(_, _, _, None), _) => {}
        TransitionStmt::Split(_span, SplitKind::Special(_, _, _, Some(pat)), _) => {
            return crate::ident_visitor::pattern_get_bound_idents(pat);
        }
        TransitionStmt::Split(_, SplitKind::If(_), _) => {}
        TransitionStmt::Split(_, SplitKind::Match(_, arms), _) => {
            let mut v = Vec::new();
            for arm in arms {
                v.append(&mut crate::ident_visitor::pattern_get_bound_idents(&arm.pat));
            }
            return v;
        }
        TransitionStmt::Require(..) => {}
        TransitionStmt::Assert(..) => {}
        TransitionStmt::SubUpdate(..) => {}
        TransitionStmt::Update(..) => {}
        TransitionStmt::Initialize(..) => {}
        TransitionStmt::PostCondition(..) => {}
    }
    Vec::new()
}

/// Check simple well-formedness properties of the transitions.

pub fn check_transitions(sm: &mut SM) -> parse::Result<()> {
    let mut results: Vec<parse::Result<()>> = Vec::new();

    let mut transitions = Vec::new();
    std::mem::swap(&mut transitions, &mut sm.transitions);

    let mut names: HashSet<String> = HashSet::new();

    for tr in transitions.iter_mut() {
        let name = tr.name.to_string();
        if names.contains(&name) {
            results.push(Err(Error::new(tr.name.span(), "duplicate item name")));
        }
        names.insert(name);

        results.push(check_transition(sm, tr));
    }

    std::mem::swap(&mut transitions, &mut sm.transitions);

    combine_results(results)
}

fn check_label_param(sm: &SM, tr: &Transition, errors: &mut Vec<Error>) {
    let first_arg_is_type = |is_init: bool| {
        let expected_name = if is_init { INIT_LABEL_TYPE_NAME } else { TRANSITION_LABEL_TYPE_NAME };
        if tr.params.len() == 0 {
            false
        } else {
            let ty = &tr.params[0].ty;
            match ty {
                Type::Path(TypePath {
                    qself: None,
                    path: Path { leading_colon: None, segments },
                }) => {
                    if segments.len() != 1 {
                        return false;
                    }
                    let seg = &segments[0];
                    if &seg.ident.to_string() != expected_name {
                        return false;
                    }
                    let generics = sm.get_label_generics(is_init);
                    match &seg.arguments {
                        PathArguments::None => {
                            if generics.params.len() != 0 {
                                return false;
                            }
                        }
                        PathArguments::AngleBracketed(abga) => {
                            if abga.args.len() != generics.params.len() {
                                return false;
                            }
                            for (arg, param) in abga.args.iter().zip(generics.params.iter()) {
                                match (arg, param) {
                                    (
                                        GenericArgument::Type(Type::Path(TypePath {
                                            qself: None,
                                            path,
                                        })),
                                        GenericParam::Type(tp),
                                    ) => match path.get_ident() {
                                        Some(id) => {
                                            if id.to_string() != tp.ident.to_string() {
                                                return false;
                                            }
                                        }
                                        None => {
                                            return false;
                                        }
                                    },
                                    _ => {
                                        return false;
                                    }
                                }
                            }
                        }
                        _ => {
                            return false;
                        }
                    }
                    true
                }
                _ => false,
            }
        }
    };

    match tr.kind {
        TransitionKind::Property => { /* no requirement */ }
        TransitionKind::Init => {
            if sm.init_label.is_some() && !first_arg_is_type(true) {
                errors.push(Error::new(tr.name.span(),
                  format!("Since '{INIT_LABEL_TYPE_NAME:}' was declared, the first param to an 'init' definition must be '{INIT_LABEL_TYPE_NAME:}'")));
            }
        }
        TransitionKind::ReadonlyTransition | TransitionKind::Transition => {
            if sm.transition_label.is_some() && !first_arg_is_type(false) {
                let kindname = if tr.kind == TransitionKind::ReadonlyTransition {
                    "'readonly' transition"
                } else {
                    "'transition'"
                };
                errors.push(Error::new(tr.name.span(),
                  format!("Since '{TRANSITION_LABEL_TYPE_NAME:}' was declared, the first param to a {kindname:} must be '{TRANSITION_LABEL_TYPE_NAME:}'")));
            }
        }
    }
}

pub fn check_transition(sm: &SM, tr: &mut Transition) -> parse::Result<()> {
    let mut field_names = HashSet::new();
    for field in sm.fields.iter() {
        field_names.insert(field.name.to_string());
    }
    validate_idents_transition(tr, field_names)?;

    let mut errors = Vec::new();
    check_updates_refer_to_valid_fields(&sm.fields, &tr.body, &mut errors);

    if errors.len() > 0 {
        return combine_errors_or_ok(errors);
    }

    check_label_param(sm, tr, &mut errors);

    match &tr.kind {
        TransitionKind::ReadonlyTransition => {
            check_valid_ops(&sm.fields, &tr.body, true, false, &mut errors);
        }
        TransitionKind::Property => {
            check_valid_ops(&sm.fields, &tr.body, false, true, &mut errors);
        }
        TransitionKind::Transition => {
            check_valid_ops(&sm.fields, &tr.body, false, false, &mut errors);
            check_at_most_one_update(sm, &tr.body, &mut errors);
        }
        TransitionKind::Init => {
            check_valid_ops_init(&sm.fields, &tr.body, &mut errors);
            if errors.len() == 0 {
                check_exactly_one_init(sm, &tr.body, &mut errors);
            }
        }
    }

    check_let_shadowing(tr, &mut errors);
    check_birds_eye(tr, sm.concurrent, &mut errors);
    check_inherent_conditions(sm, &mut tr.body, &mut errors);
    check_bind_stmts(sm, &mut tr.body, &mut errors);

    for p in &tr.params {
        match crate::ident_visitor::error_on_super_path(&p.ty) {
            Ok(()) => {}
            Err(e) => errors.push(e),
        }
    }

    combine_errors_or_ok(errors)
}
