pub mod ast;
mod ast_to_sst;
pub mod def;
mod sst;
mod sst_to_air;
mod util;

use air::ast::Commands;
use ast::Function;

pub fn function_to_air(function: &Function) -> Commands {
    let stm = ast_to_sst::expr_to_stm(&function.x.body);
    let commands = sst_to_air::stm_to_air(&function.x.params, &stm);
    commands
}
