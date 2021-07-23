#![feature(or_patterns)]

pub mod ast;
mod ast_to_sst;
pub mod ast_util;
mod ast_visitor;
pub mod context;
pub mod datatype_to_air;
pub mod def;
pub mod func_to_air;
pub mod headers;
pub mod modes;
mod prelude;
mod recursion;
mod scc;
mod sst;
mod sst_to_air;
mod sst_vars;
mod sst_visitor;
mod triggers;
mod triggers_auto;
mod util;
