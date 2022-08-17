use crate::ast::{MonoidStmtType, ShardableType, SpecialOp, SplitKind, TransitionStmt, SM};
use proc_macro2::Span;
use syn_verus::parse;
use syn_verus::parse::Error;

/// Many of the "special ops" have inherent safety conditions.
/// (That is, they contain an 'assert' when expanded out.)
/// For those that do, the user is responsible for ensuring they hold,
/// which they can do with a 'proof block' if necessary. For example:
///
///   add m += Some(x) by { /* proof here ... */ }
///
/// This function looks at the given statement and returns the error message
/// that should be used in the case that the condition fails to prove.
/// (Technically, it returns the identifier of a lemma in
/// `pervasive::state_machine_internal` that contains the error message.)
///
/// However, not all statements have nontrivial inherent safety conditions.
/// This depends on both the type of statement and the sharding strategy.
/// In the case that this is such a statement, we either:
///
///  * Return an Error if the user incorrectly adds such a block.
///  * Return Ok("") otherwise.
///
/// We check if a statement has an inherent safety condition with the following logic:
///
/// withdraw, guard: yes, has a safety condition
/// remove, have: no safety condition; thus no proof needed
/// add, desposit: yes iff the underlying monoid's composition operator is not total.
///   (e.g., composition is total for multiset)
///
/// See `docs/command-reference.md` for more explanation, or `simplification.rs`
/// for the expansions.

fn check_inherent_condition_for_special_op(
    span: Span,
    op: &SpecialOp,
    stype: &ShardableType,
    user_gave_proof_body: bool,
) -> parse::Result<String> {
    let coll_type = match stype {
        ShardableType::Multiset(_) => CollectionType::Multiset,
        ShardableType::Option(_) => CollectionType::Option,
        ShardableType::Map(_, _) => CollectionType::Map,
        ShardableType::PersistentOption(_) => CollectionType::PersistentOption,
        ShardableType::PersistentMap(_, _) => CollectionType::PersistentMap,
        ShardableType::StorageOption(_) => CollectionType::Option,
        ShardableType::StorageMap(_, _) => CollectionType::Map,
        ShardableType::Count => CollectionType::Nat,
        ShardableType::PersistentCount => CollectionType::PersistentNat,
        ShardableType::Bool => CollectionType::Bool,
        ShardableType::PersistentBool => CollectionType::PersistentBool,
        ShardableType::Set(_) => CollectionType::Set,
        ShardableType::PersistentSet(_) => CollectionType::PersistentSet,

        ShardableType::Variable(_)
        | ShardableType::Constant(_)
        | ShardableType::NotTokenized(_) => {
            return Ok("".to_string()); // this is an error which will be caught somewhere else
        }
    };

    let is_general = op.elt.is_general();

    match &op.stmt {
        MonoidStmtType::Withdraw | MonoidStmtType::Guard => {
            let name = op.stmt.name();
            let type_name = coll_type.name();
            if is_general {
                Ok(format!("assert_general_{name:}_{type_name:}"))
            } else {
                Ok(format!("assert_{name:}_{type_name:}"))
            }
        }
        MonoidStmtType::Remove | MonoidStmtType::Have => {
            if user_gave_proof_body {
                let name = op.stmt.name();
                Err(Error::new(
                    span,
                    format!(
                        "'{name:}' statement has no inherent safety condition, adding a proof body is meaningless"
                    ),
                ))
            } else {
                Ok("".to_string())
            }
        }
        MonoidStmtType::Add(_) | MonoidStmtType::Deposit => match coll_type {
            CollectionType::Multiset
            | CollectionType::Nat
            | CollectionType::PersistentNat
            | CollectionType::PersistentBool
            | CollectionType::PersistentSet => {
                if user_gave_proof_body {
                    let name = op.stmt.name();
                    let cname = coll_type.name();
                    return Err(Error::new(
                        span,
                        format!(
                            "'{name:}' statement for `{cname:}` has no nontrivial inherent safety condition (as composition is total and thus this statement never fails); adding a proof body is meaningless"
                        ),
                    ));
                } else {
                    Ok("".to_string())
                }
            }
            CollectionType::Option
            | CollectionType::PersistentOption
            | CollectionType::Map
            | CollectionType::Set
            | CollectionType::Bool
            | CollectionType::PersistentMap => {
                let name = op.stmt.name();
                let type_name = coll_type.name();
                if is_general {
                    Ok(format!("assert_general_{name:}_{type_name:}"))
                } else {
                    Ok(format!("assert_{name:}_{type_name:}"))
                }
            }
        },
    }
}

#[derive(Copy, Clone)]
enum CollectionType {
    Map,
    PersistentMap,
    Multiset,
    Option,
    PersistentOption,
    Nat,
    PersistentNat,
    Set,
    PersistentSet,
    Bool,
    PersistentBool,
}

impl CollectionType {
    fn name(self) -> &'static str {
        match self {
            CollectionType::Nat => "count",
            CollectionType::PersistentNat => "persistent_count",
            CollectionType::Map => "map",
            CollectionType::PersistentMap => "persistent_map",
            CollectionType::Set => "set",
            CollectionType::PersistentSet => "persistent_set",
            CollectionType::PersistentOption => "persistent_option",
            CollectionType::Multiset => "multiset",
            CollectionType::Option => "option",
            CollectionType::Bool => "bool",
            CollectionType::PersistentBool => "persistent_bool",
        }
    }
}

pub fn check_inherent_conditions(sm: &SM, ts: &mut TransitionStmt, errors: &mut Vec<Error>) {
    match ts {
        TransitionStmt::Block(_, v) => {
            for t in v.iter_mut() {
                check_inherent_conditions(sm, t, errors);
            }
        }
        TransitionStmt::Split(span, kind, splits) => {
            match kind {
                SplitKind::Special(ident, op, proof, _) => {
                    let field = crate::transitions::get_field(&sm.fields, ident);
                    let checked = check_inherent_condition_for_special_op(
                        *span,
                        op,
                        &field.stype,
                        proof.proof.is_some(),
                    );
                    match checked {
                        Err(err) => errors.push(err),
                        Ok(failure_msg) => {
                            proof.error_msg = failure_msg;
                        }
                    }
                }
                _ => {}
            }

            for split in splits {
                check_inherent_conditions(sm, split, errors);
            }
        }
        TransitionStmt::Require(..) => {}
        TransitionStmt::Assert(..) => {}
        TransitionStmt::Update(..) => {}
        TransitionStmt::SubUpdate(..) => {}
        TransitionStmt::Initialize(..) => {}
        TransitionStmt::PostCondition(..) => {}
    }
}
