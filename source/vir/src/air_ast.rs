use crate::messages::Message;

pub type CommandX = air::ast::CommandX<Message>;
pub type Command = air::ast::Command<Message>;

pub type Commands = air::ast::Commands<Message>;

pub type ExprX = air::ast::ExprX<Message>;
pub type Expr = air::ast::Expr<Message>;

pub type StmtX = air::ast::StmtX<Message>;
pub type Stmt = air::ast::Stmt<Message>;

pub type DeclX = air::ast::DeclX<Message>;
pub type Decl = air::ast::Decl<Message>;

pub type QueryX = air::ast::QueryX<Message>;
pub type Query = air::ast::Query<Message>;

pub type Trigger = air::ast::Trigger<Message>;
pub type Triggers = air::ast::Triggers<Message>;

pub use air::ast::{
    BinaryOp, Bind, BindX, Binder, BinderX, Binders, Constant, Ident, MultiOp, Qid, Quant, Typ,
    TypX,
};
