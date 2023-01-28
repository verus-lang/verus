use crate::ast::{
    BinaryOp, Constant, DatatypeX, Expr, ExprX, Exprs, Fun, FunX, FunctionX, GenericBound,
    GenericBoundX, Ident, Idents, IntRange, Mode, Param, ParamX, Params, Path, PathX, Quant,
    SpannedTyped, TriggerAnnotation, Typ, TypX, Typs, UnaryOp, Variant, Variants, VirErr,
    Visibility,
};
use crate::sst::{Par, Pars};
use crate::util::vec_map;
use air::ast::{Binder, BinderX, Binders, Span};
pub use air::ast_util::{ident_binder, str_ident};
pub use air::messages::error;
use num_bigint::{BigInt, Sign};
use std::collections::HashSet;
use std::fmt;
use std::str::FromStr;
use std::sync::Arc;

/// Construct an Error and wrap it in Err.
/// For more complex Error objects, use the builder functions in air::errors

pub fn err_str<A>(span: &Span, msg: &str) -> Result<A, VirErr> {
    Err(error(msg, span))
}

pub fn err_string<A>(span: &Span, msg: String) -> Result<A, VirErr> {
    Err(error(msg, span))
}

impl PathX {
    pub fn pop_segment(&self) -> Path {
        let mut segments = (*self.segments).clone();
        segments.pop();
        Arc::new(PathX { krate: self.krate.clone(), segments: Arc::new(segments) })
    }
}

impl fmt::Display for Mode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Mode::Spec => write!(f, "spec"),
            Mode::Proof => write!(f, "proof"),
            Mode::Exec => write!(f, "exec"),
        }
    }
}

pub fn types_equal(typ1: &Typ, typ2: &Typ) -> bool {
    match (&**typ1, &**typ2) {
        (TypX::Bool, TypX::Bool) => true,
        (TypX::Int(range1), TypX::Int(range2)) => range1 == range2,
        (TypX::Tuple(typs1), TypX::Tuple(typs2)) => n_types_equal(typs1, typs2),
        (TypX::Lambda(typs1, rtyp1), TypX::Lambda(typs2, rtyp2)) => {
            n_types_equal(typs1, typs2) && types_equal(rtyp1, rtyp2)
        }
        (TypX::Datatype(p1, typs1), TypX::Datatype(p2, typs2)) => {
            p1 == p2 && n_types_equal(typs1, typs2)
        }
        (TypX::Boxed(t1), TypX::Boxed(t2)) => types_equal(t1, t2),
        (TypX::TypParam(x1), TypX::TypParam(x2)) => x1 == x2,
        (TypX::StrSlice, TypX::StrSlice) => true,
        (TypX::Char, TypX::Char) => true,
        _ => false,
    }
}

pub fn n_types_equal(typs1: &Typs, typs2: &Typs) -> bool {
    typs1.len() == typs2.len() && typs1.iter().zip(typs2.iter()).all(|(t1, t2)| types_equal(t1, t2))
}

pub const QUANT_FORALL: Quant = Quant { quant: air::ast::Quant::Forall, boxed_params: true };

pub fn params_equal_opt(
    param1: &Param,
    param2: &Param,
    check_names: bool,
    check_modes: bool,
) -> bool {
    let ParamX { name: name1, typ: typ1, mode: mode1, is_mut: is_mut1 } = &param1.x;
    let ParamX { name: name2, typ: typ2, mode: mode2, is_mut: is_mut2 } = &param2.x;
    (!check_names || name1 == name2)
        && types_equal(typ1, typ2)
        && (!check_modes || mode1 == mode2)
        && is_mut1 == is_mut2
}

pub fn params_equal(param1: &Param, param2: &Param) -> bool {
    params_equal_opt(param1, param2, true, true)
}

pub fn generic_bounds_equal(b1: &GenericBound, b2: &GenericBound) -> bool {
    match (&**b1, &**b2) {
        (GenericBoundX::Traits(t1), GenericBoundX::Traits(t2)) => t1 == t2,
    }
}

pub fn allowed_bitvector_type(typ: &Typ) -> bool {
    match &**typ {
        TypX::Bool => true,
        TypX::Int(IntRange::U(_)) | TypX::Int(IntRange::I(_)) => true,
        TypX::Boxed(typ) => allowed_bitvector_type(typ),
        _ => false,
    }
}

pub fn bitwidth_from_type(et: &Typ) -> Option<u32> {
    match &**et {
        TypX::Int(IntRange::U(size)) | TypX::Int(IntRange::I(size)) => Some(*size),
        TypX::Boxed(in_et) => bitwidth_from_type(&*in_et),
        _ => None,
    }
}

pub(crate) fn fixed_integer_const(n: &String, typ: &Typ) -> bool {
    if let TypX::Int(IntRange::U(bits)) = &**typ {
        if let Ok(u) = n.parse::<u128>() {
            return *bits == 128 || u < 2u128 << bits;
        }
    }
    if let TypX::Int(IntRange::I(bits)) = &**typ {
        if let Ok(i) = n.parse::<i128>() {
            return *bits == 128
                || -((2u128 << (bits - 1)) as i128) <= i && i < (2u128 << (bits - 1)) as i128;
        }
    }
    false
}

impl IntRange {
    pub fn is_bounded(&self) -> bool {
        match self {
            IntRange::Int | IntRange::Nat => false,
            IntRange::U(_) | IntRange::I(_) | IntRange::USize | IntRange::ISize => true,
        }
    }
}

pub fn path_as_rust_name(path: &Path) -> String {
    let krate = match &path.krate {
        None => "crate".to_string(),
        Some(krate) => krate.to_string(),
    };
    let mut strings: Vec<String> = vec![krate];
    for segment in path.segments.iter() {
        strings.push(segment.to_string());
    }
    strings.join("::")
}

pub fn fun_as_rust_dbg(fun: &Fun) -> String {
    let FunX { path, trait_path } = &**fun;
    let path_str = path_as_rust_name(path);
    if let Some(trait_path) = trait_path {
        let trait_path_str = path_as_rust_name(trait_path);
        format!("{}<{}>", path_str, trait_path_str)
    } else {
        path_str
    }
}

pub fn fun_name_crate_relative(module: &Path, fun: &Fun) -> String {
    let full_name = fun_as_rust_dbg(fun);
    let module_prefix = path_as_rust_name(module) + "::";
    if full_name.starts_with(&module_prefix) {
        full_name[module_prefix.len()..].to_string()
    } else {
        full_name
    }
}

// Can source_module see an item owned by owning_module?
pub fn is_visible_to_of_owner(owning_module: &Option<Path>, source_module: &Path) -> bool {
    let sources = &source_module.segments;
    match owning_module {
        None => true,
        Some(target) if target.segments.len() > sources.len() => false,
        Some(target) => {
            // Child can access private item in parent, so check if target is parent:
            let targets = &target.segments;
            target.krate == source_module.krate && targets[..] == sources[..targets.len()]
        }
    }
}

// Can source_module see an item with target_visibility?
pub fn is_visible_to(target_visibility: &Visibility, source_module: &Path) -> bool {
    let Visibility { owning_module, is_private } = target_visibility;
    !is_private || is_visible_to_of_owner(owning_module, source_module)
}

impl<X> SpannedTyped<X> {
    pub fn new(span: &Span, typ: &Typ, x: X) -> Arc<Self> {
        Arc::new(SpannedTyped { span: span.clone(), typ: typ.clone(), x })
    }

    pub fn new_x(&self, x: X) -> Arc<Self> {
        Arc::new(SpannedTyped { span: self.span.clone(), typ: self.typ.clone(), x })
    }
}

pub fn mk_bool(span: &Span, b: bool) -> Expr {
    SpannedTyped::new(span, &Arc::new(TypX::Bool), ExprX::Const(Constant::Bool(b)))
}

pub fn mk_implies(span: &Span, e1: &Expr, e2: &Expr) -> Expr {
    SpannedTyped::new(
        span,
        &Arc::new(TypX::Bool),
        ExprX::Binary(BinaryOp::Implies, e1.clone(), e2.clone()),
    )
}

pub fn chain_binary(span: &Span, op: BinaryOp, init: &Expr, exprs: &Vec<Expr>) -> Expr {
    let mut expr = init.clone();
    for e in exprs.iter() {
        expr = SpannedTyped::new(span, &init.typ, ExprX::Binary(op, expr, e.clone()));
    }
    expr
}

pub fn const_int_to_u32(span: &Span, i: &BigInt) -> Result<u32, VirErr> {
    let (sign, digits) = i.to_u32_digits();
    if sign != Sign::Plus || digits.len() != 1 {
        return err_str(span, "Fuel must be a u32 value");
    }
    let n = digits[0];
    Ok(n)
}

pub fn const_int_from_u128(u: u128) -> Constant {
    Constant::Int(BigInt::from(u))
}

pub fn const_int_from_i128(i: i128) -> Constant {
    Constant::Int(BigInt::from(i))
}

pub fn const_int_from_string(s: String) -> Constant {
    Constant::Int(BigInt::from_str(&s).unwrap())
}

pub fn conjoin(span: &Span, exprs: &Vec<Expr>) -> Expr {
    chain_binary(span, BinaryOp::And, &mk_bool(span, true), exprs)
}

pub fn disjoin(span: &Span, exprs: &Vec<Expr>) -> Expr {
    chain_binary(span, BinaryOp::Or, &mk_bool(span, false), exprs)
}

pub fn if_then_else(span: &Span, cond: &Expr, thn: &Expr, els: &Expr) -> Expr {
    SpannedTyped::new(span, &thn.typ, ExprX::If(cond.clone(), thn.clone(), Some(els.clone())))
}

pub fn param_to_binder(param: &Param) -> Binder<Typ> {
    Arc::new(BinderX { name: param.x.name.clone(), a: param.x.typ.clone() })
}

pub fn par_to_binder(param: &Par) -> Binder<Typ> {
    Arc::new(BinderX { name: param.x.name.clone(), a: param.x.typ.clone() })
}

pub fn params_to_binders(params: &Params) -> Binders<Typ> {
    Arc::new(vec_map(&**params, param_to_binder))
}

pub fn pars_to_binders(pars: &Pars) -> Binders<Typ> {
    Arc::new(vec_map(&**pars, par_to_binder))
}

impl FunctionX {
    // unit return values are treated as no return value
    pub fn has_return(&self) -> bool {
        match &*self.ret.x.typ {
            TypX::Tuple(ts) if ts.len() == 0 => false,
            TypX::Datatype(path, _) if path == &crate::def::prefix_tuple_type(0) => false,
            _ => true,
        }
    }

    pub fn typ_params(&self) -> Idents {
        Arc::new(vec_map(&self.typ_bounds, |(x, _)| x.clone()))
    }

    pub fn is_main(&self) -> bool {
        **self.name.path.segments.last().expect("last segment") == "main"
    }
}

pub fn get_variant<'a>(variants: &'a Variants, variant: &Ident) -> &'a Variant {
    match variants.iter().find(|v| v.name == *variant) {
        Some(variant) => variant,
        None => panic!("internal error: missing variant {}", &variant),
    }
}

pub fn get_field<'a, A: Clone>(variant: &'a Binders<A>, field: &Ident) -> &'a Binder<A> {
    match variant.iter().find(|f| f.name == *field) {
        Some(field) => field,
        None => panic!("internal error: missing field {}", &field),
    }
}

impl DatatypeX {
    pub fn get_only_variant(&self) -> &Variant {
        assert_eq!(self.variants.len(), 1);
        &self.variants[0]
    }

    pub fn get_variant(&self, variant: &Ident) -> &Variant {
        get_variant(&self.variants, variant)
    }
}

pub(crate) fn referenced_vars_expr(exp: &Expr) -> HashSet<Ident> {
    let mut vars: HashSet<Ident> = HashSet::new();
    crate::ast_visitor::expr_visitor_dfs::<(), _>(
        exp,
        &mut crate::ast_visitor::VisitorScopeMap::new(),
        &mut |_, e| {
            match &e.x {
                ExprX::Var(x) | ExprX::VarLoc(x) => {
                    vars.insert(x.clone());
                }
                _ => (),
            }
            crate::sst_visitor::VisitorControlFlow::Recurse
        },
    );
    vars
}

pub fn mk_tuple(span: &Span, exp: &Exprs) -> Expr {
    let typs = vec_map(exp, |e| e.typ.clone());
    let tup_type = Arc::new(TypX::Tuple(Arc::new(typs)));
    SpannedTyped::new(span, &tup_type, ExprX::Tuple(exp.clone()))
}

pub fn wrap_in_trigger(expr: &Expr) -> Expr {
    SpannedTyped::new(
        &expr.span,
        &expr.typ,
        ExprX::Unary(UnaryOp::Trigger(TriggerAnnotation::Trigger(None)), expr.clone()),
    )
}
