use crate::ast::{
    Expr, ExprX, Exprs, Fun, HeaderExprX, Ident, LoopInvariant, LoopInvariantKind, LoopInvariants,
    MaskSpec, Stmt, StmtX, Typ, VirErr,
};
use crate::ast_util::err_str;
use std::sync::Arc;

#[derive(Clone, Debug)]
pub struct Header {
    pub no_method_body: bool,
    pub hidden: Vec<Fun>,
    pub require: Exprs,
    pub recommend: Exprs,
    pub ensure_id_typ: Option<(Ident, Typ)>,
    pub ensure: Exprs,
    pub invariant: Exprs,
    pub invariant_ensure: Exprs,
    pub decrease: Exprs,
    pub decrease_when: Option<Expr>,
    pub decrease_by: Option<Fun>,
    pub invariant_mask: MaskSpec,
    pub extra_dependencies: Vec<Fun>,
}

fn read_header_block(block: &mut Vec<Stmt>) -> Result<Header, VirErr> {
    let mut hidden: Vec<Fun> = Vec::new();
    let mut extra_dependencies: Vec<Fun> = Vec::new();
    let mut require: Option<Exprs> = None;
    let mut ensure: Option<(Option<(Ident, Typ)>, Exprs)> = None;
    let mut recommend: Option<Exprs> = None;
    let mut invariant: Option<Exprs> = None;
    let mut invariant_ensure: Option<Exprs> = None;
    let mut decrease: Option<Exprs> = None;
    let mut decrease_when: Option<Expr> = None;
    let mut decrease_by: Option<Fun> = None;
    let mut invariant_mask = MaskSpec::NoSpec;
    let mut n = 0;
    for stmt in block.iter() {
        match &stmt.x {
            StmtX::Expr(expr) => match &expr.x {
                ExprX::Header(header) => match &**header {
                    HeaderExprX::NoMethodBody => {
                        return err_str(
                            &stmt.span,
                            "no_method_body() must be a method's final expression, with no semicolon",
                        );
                    }
                    HeaderExprX::Requires(es) => {
                        if require.is_some() {
                            return err_str(
                                &stmt.span,
                                "only one call to requires allowed (use requires([e1, ..., en]) for multiple expressions",
                            );
                        }
                        require = Some(es.clone());
                    }
                    HeaderExprX::Recommends(es) => {
                        if recommend.is_some() {
                            return err_str(
                                &stmt.span,
                                "only one call to recommends allowed (use recommends([e1, ..., en]) for multiple expressions",
                            );
                        }
                        recommend = Some(es.clone());
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
                    HeaderExprX::InvariantEnsures(es) => {
                        if invariant_ensure.is_some() {
                            return err_str(
                                &stmt.span,
                                "only one call to invariant_ensures allowed (use invariant_ensures([e1, ..., en]) for multiple expressions",
                            );
                        }
                        invariant_ensure = Some(es.clone());
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
                    HeaderExprX::DecreasesWhen(e) => {
                        if decrease_when.is_some() {
                            return err_str(
                                &stmt.span,
                                "only one if decrease_when expression currently supported",
                            );
                        }
                        decrease_when = Some(e.clone());
                    }
                    HeaderExprX::DecreasesBy(path) => {
                        if decrease_by.is_some() {
                            return err_str(
                                &stmt.span,
                                "only one decreases_by expression currently supported",
                            );
                        }
                        decrease_by = Some(path.clone());
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
    let recommend = recommend.unwrap_or(Arc::new(vec![]));
    let (ensure_id_typ, ensure) = match ensure {
        None => (None, Arc::new(vec![])),
        Some((id_typ, es)) => (id_typ, es),
    };
    let invariant = invariant.unwrap_or(Arc::new(vec![]));
    let invariant_ensure = invariant_ensure.unwrap_or(Arc::new(vec![]));
    let decrease = decrease.unwrap_or(Arc::new(vec![]));
    Ok(Header {
        no_method_body: false,
        hidden,
        require,
        recommend,
        ensure_id_typ,
        ensure,
        invariant,
        invariant_ensure,
        decrease,
        decrease_when,
        decrease_by,
        invariant_mask,
        extra_dependencies,
    })
}

pub fn read_header(body: &mut Expr) -> Result<Header, VirErr> {
    match &body.x {
        ExprX::Block(stmts, expr) => {
            let mut expr = expr.clone();
            let mut block: Vec<Stmt> = (**stmts).clone();
            let mut header = read_header_block(&mut block)?;
            if let Some(e) = &expr {
                if let ExprX::Header(h) = &e.x {
                    if let HeaderExprX::NoMethodBody = **h {
                        if block.len() != 0 {
                            return err_str(
                                &e.span,
                                "no statements are allowed before no_method_body()",
                            );
                        }
                        expr = None;
                        header.no_method_body = true;
                    } else {
                        return err_str(&e.span, "header must be a statement, with a semicolon");
                    }
                }
            }
            *body = body.new_x(ExprX::Block(Arc::new(block), expr));
            Ok(header)
        }
        _ => read_header_block(&mut vec![]),
    }
}

impl Header {
    fn add_invariants(invs: &mut Vec<LoopInvariant>, exprs: &Vec<Expr>, kind: LoopInvariantKind) {
        for expr in exprs {
            invs.push(LoopInvariant { kind, inv: expr.clone() });
        }
    }

    pub fn loop_invariants(&self) -> LoopInvariants {
        let mut invs: Vec<LoopInvariant> = Vec::new();
        Self::add_invariants(&mut invs, &self.invariant, LoopInvariantKind::Invariant);
        Self::add_invariants(
            &mut invs,
            &self.invariant_ensure,
            LoopInvariantKind::InvariantEnsures,
        );
        Self::add_invariants(&mut invs, &self.ensure, LoopInvariantKind::Ensures);
        Arc::new(invs)
    }
}
