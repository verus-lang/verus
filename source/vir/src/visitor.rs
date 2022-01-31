#[derive(PartialEq, Eq, Debug)]
pub(crate) enum VisitorControlFlow<T> {
    Recurse,
    Return,
    Stop(T),
}

macro_rules! expr_visitor_control_flow {
    ($cf:expr) => {
        match $cf {
            crate::ast_visitor::VisitorControlFlow::Recurse => (),
            crate::ast_visitor::VisitorControlFlow::Return => (),
            crate::ast_visitor::VisitorControlFlow::Stop(val) => {
                return crate::ast_visitor::VisitorControlFlow::Stop(val);
            }
        }
    };
}

pub(crate) use expr_visitor_control_flow;
