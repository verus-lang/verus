use crate::ast::{Typ, TypX};
use crate::context::Context;
use z3::ast::{Bool, Dynamic, Int};

pub(crate) fn new_const<'ctx>(
    context: &mut Context<'ctx>,
    name: &String,
    typ: &Typ,
) -> Dynamic<'ctx> {
    match &**typ {
        TypX::Bool => Bool::new_const(context.context, name.clone()).into(),
        TypX::Int => Int::new_const(context.context, name.clone()).into(),
        TypX::Named(x) => {
            let sort = &context.typs[x];
            let fdecl = z3::FuncDecl::new(context.context, name.clone(), &[], sort);
            fdecl.apply(&[])
        }
    }
}
