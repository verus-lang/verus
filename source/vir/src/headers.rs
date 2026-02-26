use crate::ast::{
    Expr, ExprX, Exprs, Fun, Function, FunctionX, HeaderExprX, LoopInvariant, LoopInvariantKind,
    LoopInvariants, MaskSpec, Sizedness, Stmt, StmtX, Typ, UnwindSpec, UnwrapParameter, VarIdent,
    VirErr, Visibility,
};
use crate::ast_util::{air_unique_var, params_equal_opt};
use crate::def::VERUS_SPEC;
use crate::messages::error;
use crate::messages::multiple_errors;
use std::collections::HashMap;
use std::sync::Arc;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HeaderAllow {
    Require,
    // Ensure means ensures is allowed (this does not allow default_ensures)
    Ensure,
}

#[derive(Clone, Debug)]
pub enum HeaderAllows {
    All,
    Loop,
    Closure,
    Some(Vec<HeaderAllow>),
}

impl HeaderAllows {
    fn require(&self) -> bool {
        match self {
            HeaderAllows::All => true,
            HeaderAllows::Loop => true,
            HeaderAllows::Closure => true,
            HeaderAllows::Some(hs) => hs.contains(&HeaderAllow::Require),
        }
    }

    fn ensure(&self) -> bool {
        match self {
            HeaderAllows::All => true,
            HeaderAllows::Loop => true,
            HeaderAllows::Closure => true,
            HeaderAllows::Some(hs) => hs.contains(&HeaderAllow::Ensure),
        }
    }

    fn loops(&self) -> bool {
        match self {
            HeaderAllows::All => true,
            HeaderAllows::Loop => true,
            _ => false,
        }
    }

    fn all(&self) -> bool {
        match self {
            HeaderAllows::All => true,
            _ => false,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Header {
    pub no_method_body: bool,
    pub unwrap_parameters: Vec<UnwrapParameter>,
    pub hidden: Vec<Fun>,
    pub require: Exprs,
    pub recommend: Exprs,
    pub ensure_id_typ: Option<(VarIdent, Option<Typ>)>,
    pub ensure: (Exprs, Exprs),
    pub returns: Option<Expr>,
    pub invariant_except_break: Exprs,
    pub invariant: Exprs,
    pub decrease: Exprs,
    pub decrease_when: Option<Expr>,
    pub decrease_by: Option<Fun>,
    pub invariant_mask: Option<MaskSpec>,
    pub unwind_spec: Option<UnwindSpec>,
    pub extra_dependencies: Vec<Fun>,
    pub open_visibility_qualifier: Option<Visibility>,
}

pub fn read_header_block(block: &mut Vec<Stmt>, allows: &HeaderAllows) -> Result<Header, VirErr> {
    let mut unwrap_parameters: Vec<UnwrapParameter> = Vec::new();
    let mut hidden: Vec<Fun> = Vec::new();
    let mut extra_dependencies: Vec<Fun> = Vec::new();
    let mut require: Option<Exprs> = None;
    let mut ensure: Option<(Option<(VarIdent, Option<Typ>)>, (Exprs, Exprs))> = None;
    let mut returns: Option<Expr> = None;
    let mut recommend: Option<Exprs> = None;
    let mut invariant_except_break: Option<Exprs> = None;
    let mut invariant: Option<Exprs> = None;
    let mut decrease: Option<Exprs> = None;
    let mut decrease_when: Option<Expr> = None;
    let mut decrease_by: Option<Fun> = None;
    let mut invariant_mask: Option<MaskSpec> = None;
    let mut unwind_spec: Option<UnwindSpec> = None;
    let mut open_visibility_qualifier: Option<Visibility> = None;
    let mut n = 0;
    let mut unwrap_parameter_allowed = true;
    for stmt in block.iter() {
        let mut is_unwrap_parameter = false;
        let mut allowed = allows.all();
        match &stmt.x {
            StmtX::Expr(expr) => match &peel(expr).x {
                ExprX::Header(header) => match &**header {
                    HeaderExprX::UnwrapParameter(unwrap) => {
                        if !unwrap_parameter_allowed {
                            return Err(error(&stmt.span, "unwrap_parameter must appear "));
                        }
                        is_unwrap_parameter = true;
                        unwrap_parameters.push(unwrap.clone());
                    }
                    HeaderExprX::NoMethodBody => {
                        return Err(error(
                            &stmt.span,
                            "no_method_body() must be a method's final expression, with no semicolon",
                        ));
                    }
                    HeaderExprX::Requires(es) => {
                        if require.is_some() {
                            return Err(error(
                                &stmt.span,
                                "only one call to requires allowed (use requires([e1, ..., en]) for multiple expressions",
                            ));
                        }
                        allowed = allows.require();
                        require = Some(es.clone());
                    }
                    HeaderExprX::Recommends(es) => {
                        if recommend.is_some() {
                            return Err(error(
                                &stmt.span,
                                "only one call to recommends allowed (use recommends([e1, ..., en]) for multiple expressions",
                            ));
                        }
                        recommend = Some(es.clone());
                    }
                    HeaderExprX::Ensures(id_typ, es) => {
                        if ensure.is_some() {
                            return Err(error(
                                &stmt.span,
                                "only one call to ensures allowed (use ensures([e1, ..., en]) for multiple expressions",
                            ));
                        }
                        if es.1.len() == 0 {
                            allowed = allows.ensure();
                        } else if !allows.all() {
                            return Err(error(&stmt.span, "default_ensures not allowed here"));
                        }
                        ensure = Some((id_typ.clone(), es.clone()));
                    }
                    HeaderExprX::Returns(e) => {
                        if returns.is_some() {
                            return Err(error(&stmt.span, "only one call to returns allowed"));
                        }
                        returns = Some(e.clone());
                    }
                    HeaderExprX::InvariantExceptBreak(es) => {
                        if invariant_except_break.is_some() {
                            return Err(error(
                                &stmt.span,
                                "only one call to invariant_except_break allowed (use invariant_except_break([e1, ..., en]) for multiple expressions",
                            ));
                        }
                        allowed = allows.loops();
                        invariant_except_break = Some(es.clone());
                    }
                    HeaderExprX::Invariant(es) => {
                        if invariant.is_some() {
                            return Err(error(
                                &stmt.span,
                                "only one call to invariant allowed (use invariant([e1, ..., en]) for multiple expressions",
                            ));
                        }
                        allowed = allows.loops();
                        invariant = Some(es.clone());
                    }
                    HeaderExprX::Decreases(es) => {
                        if decrease.is_some() {
                            return Err(error(
                                &stmt.span,
                                "only one decreases expression currently supported",
                            ));
                        }
                        allowed = allows.loops();
                        decrease = Some(es.clone());
                    }
                    HeaderExprX::DecreasesWhen(e) => {
                        if decrease_when.is_some() {
                            return Err(error(
                                &stmt.span,
                                "only one if decrease_when expression currently supported",
                            ));
                        }
                        decrease_when = Some(e.clone());
                    }
                    HeaderExprX::DecreasesBy(path) => {
                        if decrease_by.is_some() {
                            return Err(error(
                                &stmt.span,
                                "only one decreases_by expression currently supported",
                            ));
                        }
                        decrease_by = Some(path.clone());
                    }
                    HeaderExprX::Hide(x) => {
                        hidden.push(x.clone());
                    }
                    HeaderExprX::ExtraDependency(x) => {
                        extra_dependencies.push(x.clone());
                    }
                    HeaderExprX::InvariantOpens(span, es) => {
                        match invariant_mask {
                            None => {}
                            _ => {
                                return Err(error(
                                    &stmt.span,
                                    "only one invariant mask spec allowed",
                                ));
                            }
                        }
                        invariant_mask = Some(MaskSpec::InvariantOpens(span.clone(), es.clone()));
                    }
                    HeaderExprX::InvariantOpensExcept(span, es) => {
                        match invariant_mask {
                            None => {}
                            _ => {
                                return Err(error(
                                    &stmt.span,
                                    "only one invariant mask spec allowed",
                                ));
                            }
                        }
                        invariant_mask =
                            Some(MaskSpec::InvariantOpensExcept(span.clone(), es.clone()));
                    }
                    HeaderExprX::InvariantOpensSet(e) => {
                        match invariant_mask {
                            None => {}
                            _ => {
                                return Err(error(
                                    &stmt.span,
                                    "only one invariant mask spec allowed",
                                ));
                            }
                        }
                        invariant_mask = Some(MaskSpec::InvariantOpensSet(e.clone()));
                    }
                    HeaderExprX::NoUnwind | HeaderExprX::NoUnwindWhen(_) => {
                        match unwind_spec {
                            None => {}
                            _ => {
                                return Err(error(&stmt.span, "only one unwind spec allowed"));
                            }
                        }
                        unwind_spec = match &**header {
                            HeaderExprX::NoUnwind => Some(UnwindSpec::NoUnwind),
                            HeaderExprX::NoUnwindWhen(expr) => {
                                Some(UnwindSpec::NoUnwindWhen(expr.clone()))
                            }
                            _ => unreachable!(),
                        };
                    }
                    HeaderExprX::OpenVisibilityQualifier(v) => {
                        match open_visibility_qualifier {
                            None => {}
                            _ => {
                                return Err(error(
                                    &stmt.span,
                                    "only one open_visibility_qualifier declaration allowed",
                                ));
                            }
                        }
                        open_visibility_qualifier = Some(v.clone());
                    }
                },
                _ => break,
            },
            _ => break,
        }
        if !allowed {
            return Err(error(&stmt.span, "unexpected declaration"));
        }
        if !is_unwrap_parameter {
            unwrap_parameter_allowed = false;
        }
        n += 1;
    }
    *block = block[n..].to_vec();
    let require = require.unwrap_or(Arc::new(vec![]));
    let recommend = recommend.unwrap_or(Arc::new(vec![]));
    let (ensure_id_typ, ensure) = match ensure {
        None => (None, (Arc::new(vec![]), Arc::new(vec![]))),
        Some((id_typ, es)) => (id_typ, es),
    };
    let invariant_except_break = invariant_except_break.unwrap_or(Arc::new(vec![]));
    let invariant = invariant.unwrap_or(Arc::new(vec![]));
    let decrease = decrease.unwrap_or(Arc::new(vec![]));
    Ok(Header {
        unwrap_parameters,
        no_method_body: false,
        hidden,
        require,
        recommend,
        ensure_id_typ,
        ensure,
        returns,
        invariant_except_break,
        invariant,
        decrease,
        decrease_when,
        decrease_by,
        invariant_mask,
        unwind_spec,
        extra_dependencies,
        open_visibility_qualifier,
    })
}

pub fn read_header(body: &mut Expr, allows: &HeaderAllows) -> Result<Header, VirErr> {
    let body = peel_mut(body);

    #[derive(Clone, Copy)]
    enum NestedHeaderBlock {
        No,
        Yes,
        Unknown,
        Conflict,
    }

    impl NestedHeaderBlock {
        fn join(&mut self, other: NestedHeaderBlock) {
            match (*self, other) {
                (NestedHeaderBlock::No, NestedHeaderBlock::No) => {}
                (NestedHeaderBlock::Yes, NestedHeaderBlock::Yes) => {}
                (_, NestedHeaderBlock::Unknown) => panic!("unexpected join with unknown"),
                (NestedHeaderBlock::Unknown, _) => *self = other,
                _ => *self = NestedHeaderBlock::Conflict,
            }
        }
    }

    match &body.x {
        ExprX::Block(stmts, expr) => {
            let mut expr = expr.clone();
            let mut block = Vec::new();
            for stmt in (**stmts).iter() {
                let mut nested_header_block = NestedHeaderBlock::Unknown;
                if let StmtX::Expr(e) = &stmt.x {
                    if let ExprX::Block(b, e) = &e.x {
                        for s in b.iter() {
                            if let StmtX::Expr(e) = &s.x {
                                if let ExprX::Header(_h) = &e.x {
                                    block.push(s.clone());
                                    nested_header_block = NestedHeaderBlock::Yes;
                                } else {
                                    nested_header_block.join(NestedHeaderBlock::No);
                                }
                            } else {
                                nested_header_block.join(NestedHeaderBlock::No);
                            }
                        }
                        if let Some(e) = &e {
                            if let ExprX::Header(_h) = &e.x {
                                nested_header_block = NestedHeaderBlock::Conflict;
                            }
                        }
                    } else {
                        nested_header_block.join(NestedHeaderBlock::No);
                    }
                } else {
                    nested_header_block.join(NestedHeaderBlock::No);
                }
                match nested_header_block {
                    NestedHeaderBlock::No | NestedHeaderBlock::Unknown => {
                        block.push(stmt.clone());
                    }
                    NestedHeaderBlock::Yes => {}
                    NestedHeaderBlock::Conflict => {
                        return Err(error(
                            &stmt.span,
                            "internal error: invalid nested header block",
                        ));
                    }
                }
            }
            let mut header = read_header_block(&mut block, allows)?;
            if let Some(e) = &expr {
                if let ExprX::Header(h) = &peel(e).x {
                    if let HeaderExprX::NoMethodBody = **h {
                        if block.len() != 0 {
                            return Err(error(
                                &e.span,
                                "no statements are allowed before no_method_body()",
                            ));
                        }
                        expr = None;
                        header.no_method_body = true;
                    } else {
                        return Err(error(&e.span, "header must be a statement, with a semicolon"));
                    }
                }
            }
            *body = body.new_x(ExprX::Block(Arc::new(block), expr));
            Ok(header)
        }
        _ => read_header_block(&mut vec![], allows),
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
        Self::add_invariants(
            &mut invs,
            &self.invariant_except_break,
            LoopInvariantKind::InvariantExceptBreak,
        );
        Self::add_invariants(&mut invs, &self.invariant, LoopInvariantKind::InvariantAndEnsures);
        assert!(self.ensure.1.len() == 0);
        Self::add_invariants(&mut invs, &self.ensure.0, LoopInvariantKind::Ensures);
        Arc::new(invs)
    }

    pub fn const_static_ensures(&self, const_name: &Fun, is_static: bool) -> Exprs {
        let f = |expr: &Expr| {
            Ok(match &expr.x {
                // const decl ensures clauses can refer to the const's "return value"
                // using the name of the const (which is a ConstVar to the const):
                ExprX::ConstVar(fun, _) if fun == const_name && !is_static => {
                    expr.new_x(ExprX::Var(air_unique_var(crate::def::RETURN_VALUE)))
                }
                // likewise for static
                ExprX::StaticVar(fun) if fun == const_name && is_static => {
                    expr.new_x(ExprX::Var(air_unique_var(crate::def::RETURN_VALUE)))
                }
                _ => expr.clone(),
            })
        };
        assert!(self.ensure.1.len() == 0);
        Arc::new(
            self.ensure
                .0
                .iter()
                .map(|e| crate::ast_visitor::map_expr_visitor(e, &f).unwrap())
                .collect(),
        )
    }
}

fn make_trait_decl(method: &Function, spec_method: &Function) -> Result<Function, VirErr> {
    let FunctionX {
        name: _,
        proxy: _,
        kind: _,
        visibility: _,
        body_visibility: _,
        opaqueness,
        owning_module: _,
        mode: _,
        typ_params,
        mut typ_bounds,
        params,
        ret,
        ens_has_return: _,
        require,
        ensure,
        returns,
        decrease,
        decrease_when,
        decrease_by,
        fndef_axioms: _,
        mask_spec,
        unwind_spec,
        item_kind: _,
        attrs: _,
        body: _,
        extra_dependencies,
    } = spec_method.x.clone();
    let mut methodx = method.x.clone();
    while typ_bounds.len() > methodx.typ_bounds.len() {
        // The syntax macro may add Sized bounds to spec_method so that Rust accepts the function.
        // Remove these added Sized bounds so that we can match the remaining bounds.
        use crate::ast::{GenericBoundX, TraitId};
        if let GenericBoundX::Trait(TraitId::Sizedness(Sizedness::Sized), _) =
            &**typ_bounds.last().unwrap()
        {
            Arc::make_mut(&mut typ_bounds).pop();
        }
    }
    if methodx.typ_params.len() != typ_params.len() {
        return Err(error(
            &spec_method.span,
            "method specification has different number of type parameters from method",
        ));
    }
    if methodx.typ_bounds.len() != typ_bounds.len() {
        return Err(error(
            &spec_method.span,
            "method specification has different number of type bounds from method",
        ));
    }
    for (x1, x2) in methodx.typ_params.iter().zip(typ_params.iter()) {
        if x1 != x2 {
            return Err(error(
                &spec_method.span,
                "method specification has different type parameters from method",
            ));
        }
    }
    for (b1, b2) in methodx.typ_bounds.iter().zip(typ_bounds.iter()) {
        if !crate::ast_util::generic_bounds_equal(b1, b2) {
            return Err(error(
                &spec_method.span,
                "method specification has different type parameters or bounds from method",
            ));
        }
    }
    if methodx.params.len() != params.len() {
        return Err(error(
            &spec_method.span,
            "method specification has different number of parameters from method",
        ));
    }
    for (p1, p2) in methodx.params.iter().zip(params.iter()) {
        if !params_equal_opt(p1, p2, false, false) {
            return Err(error(
                &spec_method.span,
                "method specification has different parameters from method",
            ));
        }
    }
    if !params_equal_opt(&methodx.ret, &ret, false, false) {
        return Err(error(
            &spec_method.span,
            "method specification has a different return from method",
        ));
    }

    let has_default_ensures = ensure.1.len() > 0;
    match &mut methodx.kind {
        crate::ast::FunctionKind::TraitMethodDecl { trait_path: _, has_default }
            if methodx.proxy.is_some() && has_default_ensures =>
        {
            // We use an external trait function default only if the spec mentions it:
            *has_default = true;
        }
        _ => {}
    };

    methodx.opaqueness = opaqueness;
    methodx.params = params; // this is important; the correct parameter modes are in spec_method
    methodx.ret = ret;
    methodx.require = require;
    methodx.ensure = ensure;
    methodx.returns = returns;
    methodx.decrease = decrease;
    methodx.decrease_when = decrease_when;
    methodx.decrease_by = decrease_by;
    methodx.mask_spec = mask_spec;
    methodx.unwind_spec = unwind_spec;
    methodx.extra_dependencies = extra_dependencies;
    assert!(methodx.body.is_none());
    Ok(crate::def::Spanned::new(method.span.clone(), methodx))
}

// Each trait method declaration is encoded as a pair of methods:
//   fn VERUS_SPEC__f() { requires(x); ... }
//   fn f();
// This is done to preserve f's lack of a body,
// so that Rust's type checker can check that implementations of f provide a body.
// When generating VIR, merge the methods back into a single method:
//   fn f() requires x;
pub fn make_trait_decls(methods: Vec<Function>) -> Result<Vec<Function>, VirErr> {
    let mut decls: Vec<Function> = Vec::new();
    let mut specs: HashMap<String, Function> = HashMap::new();
    for method in methods.into_iter() {
        let mut name = method.x.name.path.segments.last().expect("method name last").to_string();
        if name.starts_with(VERUS_SPEC) {
            let name = name.split_off(VERUS_SPEC.len());
            specs.insert(name, method);
        } else {
            decls.push(method);
        }
    }
    for method in decls.iter_mut() {
        let name = method.x.name.path.segments.last().expect("method name last").to_string();
        // Note: None case means no specification method, which means no requires, ensures, etc.
        if let Some(spec_method) = specs.remove(&name) {
            *method = make_trait_decl(method, &spec_method)?;
        }
    }
    if specs.is_empty() {
        Ok(decls)
    } else {
        Err(multiple_errors(
            specs.values().map(|spec| &spec.span),
            format!(
                "no matching method found for method specification{}",
                if specs.len() > 1 { "s" } else { "" },
            ),
        ))
    }
}

fn peel(expr: &Expr) -> &Expr {
    match &expr.x {
        ExprX::NeverToAny(e) => e,
        _ => expr,
    }
}

fn peel_mut(expr: &mut Expr) -> &mut Expr {
    match &expr.x {
        ExprX::NeverToAny(_) => match &mut Arc::make_mut(expr).x {
            ExprX::NeverToAny(e) => e,
            _ => unreachable!(),
        },
        _ => expr,
    }
}
