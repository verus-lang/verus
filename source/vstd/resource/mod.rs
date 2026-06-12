use super::prelude::*;

pub mod algebra;
mod combinators;
mod impls;
mod lib;
pub mod pcm;
pub mod relations;
pub mod storage_protocol;

pub use combinators::agree;
pub use combinators::auth;
pub use combinators::exclusive;
pub use combinators::frac;
pub use combinators::option;
pub use combinators::product;
pub use combinators::sum;

pub use impls::frac_opt;
pub use impls::ghost_var;
pub use impls::map;
pub use impls::seq;
pub use impls::set;

pub use lib::*;

verus! {

#[derive(Eq, PartialEq)]
pub struct Loc(int);

} // verus!
