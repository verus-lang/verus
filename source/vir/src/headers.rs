use crate::ast::{Expr, ExprX, Exprs, Fun, HeaderExprX, Ident, MaskSpec, Stmt, StmtX, Typ, VirErr};
use crate::ast_util::err_str;
use std::sync::Arc;

#[derive(Clone, Debug)]
pub struct Header {
    pub hidden: Vec<Fun>,
    pub require: Exprs,
    pub ensure_id_typ: Option<(Ident, Typ)>,
    pub ensure: Exprs,
    pub invariant: Exprs,
    pub decrease: Exprs,
    pub invariant_mask: MaskSpec,
    pub extra_dependencies: Vec<Fun>,
}

fn read_header_block(block: &mut Vec<Stmt>) -> Result<Header, VirErr> {
    let mut hidden: Vec<Fun> = Vec::new();
    let mut extra_dependencies: Vec<Fun> = Vec::new();
    let mut require: Option<Exprs> = None;
    let mut ensure: Option<(Option<(Ident, Typ)>, Exprs)> = None;
    let mut invariant: Option<Exprs> = None;
    let mut decrease: Option<Exprs> = None;
    let mut invariant_mask = MaskSpec::NoSpec;
    let mut n = 0;
    for stmt in block.iter() {
        match &stmt.x {
            StmtX::Expr(expr) => match &expr.x {
                ExprX::Header(header) => match &**header {
                    HeaderExprX::Requires(es) => {
                        if require.is_some() {
                            return err_str(
                                &stmt.span,
                                "only one call to requires allowed (use requires([e1, ..., en]) for multiple expressions",
                            );
                        }
                        require = Some(es.clone());
                    }
                    HeaderExprX::Ensures(id_typ, es) => {
                        if ensure.is_some() {
                            return err_str(
                                &stmt.span,
                                "only one call to ensures allowed (use ensures([e1, ..., en]) for multiple expressions",
                            );
                        }
                        ensure = Some((id_typ.clone(), es.clone()));
                    }
                    HeaderExprX::Invariant(es) => {
                        if invariant.is_some() {
                            return err_str(
                                &stmt.span,
                                "only one call to invariant allowed (use invariant([e1, ..., en]) for multiple expressions",
                            );
                        }
                        invariant = Some(es.clone());
                    }
                    HeaderExprX::Decreases(es) => {
                        if decrease.is_some() {
                            return err_str(
                                &stmt.span,
                                "only one decreases expression currently supported",
                            );
                        }
                        decrease = Some(es.clone());
                    }
                    HeaderExprX::Hide(x) => {
                        hidden.push(x.clone());
                    }
                    HeaderExprX::ExtraDependency(x) => {
                        extra_dependencies.push(x.clone());
                    }
                    HeaderExprX::InvariantOpens(es) => {
                        match invariant_mask {
                            MaskSpec::NoSpec => {}
                            _ => {
                                return err_str(&stmt.span, "only one invariant mask spec allowed");
                            }
                        }
                        invariant_mask = MaskSpec::InvariantOpens(es.clone());
                    }
                    HeaderExprX::InvariantOpensExcept(es) => {
                        match invariant_mask {
                            MaskSpec::NoSpec => {}
                            _ => {
                                return err_str(&stmt.span, "only one invariant mask spec allowed");
                            }
                        }
                        invariant_mask = MaskSpec::InvariantOpensExcept(es.clone());
                    }
                },
                _ => break,
            },
            _ => break,
        }
        n += 1;
    }
    *block = block[n..].to_vec();
    let require = require.unwrap_or(Arc::new(vec![]));
    let (ensure_id_typ, ensure) = match ensure {
        None => (None, Arc::new(vec![])),
        Some((id_typ, es)) => (id_typ, es),
    };
    let invariant = invariant.unwrap_or(Arc::new(vec![]));
    let decrease = decrease.unwrap_or(Arc::new(vec![]));
    Ok(Header {
        hidden,
        require,
        ensure_id_typ,
        ensure,
        invariant,
        decrease,
        invariant_mask,
        extra_dependencies,
    })
}

pub fn read_header(body: &mut Expr) -> Result<Header, VirErr> {
    match &body.x {
        ExprX::Block(stmts, expr) => {
            let mut block: Vec<Stmt> = (**stmts).clone();
            let header = read_header_block(&mut block)?;
            *body = body.new_x(ExprX::Block(Arc::new(block), expr.clone()));
            Ok(header)
        }
        _ => read_header_block(&mut vec![]),
    }
}
