use super::prelude::*;

pub mod algebra;
mod combinators;
mod impls;
mod lib;
pub mod pcm;
pub mod relations;
pub mod storage_protocol;
pub mod tsm;
pub mod tsm_storage;
pub mod tsm_collections;
pub mod tsm_multiset;
pub mod tsm_finite_multiset;
pub mod tsm_persistent;
pub mod tsm_bool;
pub mod tsm_helpers;
pub mod tsm_context;
pub mod tsm_generic;
pub mod tsm_calculus;

pub use combinators::agree;
pub use combinators::auth;
pub use combinators::exclusive;
pub use combinators::frac;
pub use combinators::option;
pub use combinators::product;
pub use combinators::sum;

pub use impls::frac_opt;
pub use impls::ghost_var;
pub use impls::imap;
pub use impls::iset;
pub use impls::map;
pub use impls::seq;
pub use impls::set;

pub use lib::*;

verus! {

#[derive(Eq, PartialEq)]
pub struct Loc(int);

/// Instance identity of a checked tokenized-state-machine token.
/// Tokens backed by the machine's resource at `l` use `fake == false`;
/// placeholder tokens backed by a separate private resource use `fake == true`.
/// The two spaces are disjoint, so a placeholder never matches an instance.
pub closed spec fn tsm_instance_id(l: Loc, fake: bool) -> Loc {
    Loc(2 * l.0 + if fake { 1int } else { 0int })
}

pub proof fn tsm_instance_id_injective(a: Loc, fa: bool, b: Loc, fb: bool)
    ensures
        tsm_instance_id(a, fa) == tsm_instance_id(b, fb) ==> a == b && fa == fb,
{
}

} // verus!
