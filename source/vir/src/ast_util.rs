use crate::ast::{
    ArchWordBits, BinaryOp, Constant, DatatypeX, Expr, ExprX, Exprs, Fun, FunX, FunctionX,
    GenericBound, GenericBoundX, Ident, IntRange, ItemKind, Mode, Param, ParamX, Params, Path,
    PathX, Quant, SpannedTyped, TriggerAnnotation, Typ, TypDecoration, TypX, Typs, UnaryOp,
    Variant, Variants, VirErr, Visibility,
};
use crate::messages::{error, Span};
use crate::sst::{Par, Pars};
use crate::util::vec_map;
use air::ast::{Binder, BinderX, Binders};
pub use air::ast_util::{ident_binder, str_ident};
use num_bigint::{BigInt, Sign};
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::str::FromStr;
use std::sync::{Arc, Mutex};

impl PathX {
    pub fn last_segment(&self) -> Ident {
        self.segments[self.segments.len() - 1].clone()
    }

    pub fn pop_segment(&self) -> Path {
        let mut segments = (*self.segments).clone();
        segments.pop();
        Arc::new(PathX { krate: self.krate.clone(), segments: Arc::new(segments) })
    }

    pub fn push_segment(&self, ident: Ident) -> Path {
        let mut segments = (*self.segments).clone();
        segments.push(ident);
        Arc::new(PathX { krate: self.krate.clone(), segments: Arc::new(segments) })
    }

    pub fn is_rust_std_path(&self) -> bool {
        match &self.krate {
            Some(k) if &**k == "std" || &**k == "alloc" || &**k == "core" => true,
            _ => false,
        }
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

pub fn type_is_bool(typ: &Typ) -> bool {
    matches!(&**typ, TypX::Bool)
}

// ImplPaths is ignored in types_equal
pub fn types_equal(typ1: &Typ, typ2: &Typ) -> bool {
    match (&**typ1, &**typ2) {
        (TypX::Bool, TypX::Bool) => true,
        (TypX::Int(r1), TypX::Int(r2)) => r1 == r2,
        (TypX::Tuple(t1), TypX::Tuple(t2)) => n_types_equal(t1, t2),
        (TypX::Lambda(ts1, t1), TypX::Lambda(ts2, t2)) => {
            n_types_equal(ts1, ts2) && types_equal(t1, t2)
        }
        (TypX::AnonymousClosure(ts1, t1, id1), TypX::AnonymousClosure(ts2, t2, id2)) => {
            n_types_equal(ts1, ts2) && types_equal(t1, t2) && id1 == id2
        }
        (TypX::Datatype(path1, ts1, _), TypX::Datatype(path2, ts2, _)) => {
            path1 == path2 && n_types_equal(ts1, ts2)
        }
        (TypX::Primitive(p1, ts1), TypX::Primitive(p2, ts2)) => p1 == p2 && n_types_equal(ts1, ts2),
        (TypX::Decorate(d1, t1), TypX::Decorate(d2, t2)) => d1 == d2 && types_equal(t1, t2),
        (TypX::Boxed(t1), TypX::Boxed(t2)) => types_equal(t1, t2),
        (TypX::TypParam(x1), TypX::TypParam(x2)) => x1 == x2,
        (
            TypX::Projection {
                trait_typ_args: trait_typ_args1,
                trait_path: trait_path1,
                name: name1,
            },
            TypX::Projection {
                trait_typ_args: trait_typ_args2,
                trait_path: trait_path2,
                name: name2,
            },
        ) => {
            n_types_equal(trait_typ_args1, trait_typ_args2)
                && trait_path1 == trait_path2
                && name1 == name2
        }
        (TypX::TypeId, TypX::TypeId) => true,
        (TypX::ConstInt(i1), TypX::ConstInt(i2)) => i1 == i2,
        (TypX::Air(a1), TypX::Air(a2)) => a1 == a2,
        (TypX::StrSlice, TypX::StrSlice) => true,
        (TypX::Char, TypX::Char) => true,
        (TypX::FnDef(f1, ts1, _res), TypX::FnDef(f2, ts2, _res2)) => {
            f1 == f2 && n_types_equal(ts1, ts2)
        }
        // rather than matching on _, repeat all the cases to catch any new variants added to TypX:
        (TypX::Bool, _) => false,
        (TypX::Int(_), _) => false,
        (TypX::Tuple(_), _) => false,
        (TypX::Lambda(_, _), _) => false,
        (TypX::AnonymousClosure(_, _, _), _) => false,
        (TypX::Datatype(_, _, _), _) => false,
        (TypX::Primitive(_, _), _) => false,
        (TypX::Decorate(_, _), _) => false,
        (TypX::Boxed(_), _) => false,
        (TypX::TypParam(_), _) => false,
        (TypX::Projection { .. }, _) => false,
        (TypX::TypeId, _) => false,
        (TypX::ConstInt(_), _) => false,
        (TypX::Air(_), _) => false,
        (TypX::StrSlice, _) => false,
        (TypX::Char, _) => false,
        (TypX::FnDef(..), _) => false,
    }
}

pub fn n_types_equal(typs1: &Typs, typs2: &Typs) -> bool {
    typs1.len() == typs2.len() && typs1.iter().zip(typs2.iter()).all(|(t1, t2)| types_equal(t1, t2))
}

pub fn typ_args_for_datatype_typ(typ: &Typ) -> &Typs {
    match &**typ {
        TypX::Decorate(_, t) => typ_args_for_datatype_typ(t),
        TypX::Datatype(_, args, _) => args,
        _ => {
            panic!("typ_args_for_datatype_typ expected datatype type");
        }
    }
}

pub const QUANT_FORALL: Quant = Quant { quant: air::ast::Quant::Forall };

pub fn params_equal_opt(
    param1: &Param,
    param2: &Param,
    check_names: bool,
    check_modes: bool,
) -> bool {
    // Note: unwrapped_info is internal to the function and is not part of comparing
    // the publicly visible parameters.
    let ParamX { name: name1, typ: typ1, mode: mode1, is_mut: is_mut1, unwrapped_info: _ } =
        &param1.x;
    let ParamX { name: name2, typ: typ2, mode: mode2, is_mut: is_mut2, unwrapped_info: _ } =
        &param2.x;
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
        (GenericBoundX::Trait(x1, ts1), GenericBoundX::Trait(x2, ts2)) => {
            x1 == x2 && n_types_equal(ts1, ts2)
        }
    }
}

pub fn undecorate_typ(typ: &Typ) -> Typ {
    if let TypX::Decorate(_, t) = &**typ { undecorate_typ(t) } else { typ.clone() }
}

pub fn allowed_bitvector_type(typ: &Typ) -> bool {
    match &*undecorate_typ(typ) {
        TypX::Bool => true,
        TypX::Int(IntRange::U(_) | IntRange::I(_) | IntRange::USize | IntRange::ISize) => true,
        TypX::Boxed(typ) => allowed_bitvector_type(typ),
        _ => false,
    }
}

pub fn is_integer_type(typ: &Typ) -> bool {
    match &*undecorate_typ(typ) {
        TypX::Int(_) => true,
        TypX::Boxed(typ) => is_integer_type(typ),
        _ => false,
    }
}

pub fn int_range_from_type(typ: &Typ) -> Option<IntRange> {
    match &*undecorate_typ(typ) {
        TypX::Int(range) => Some(*range),
        TypX::Boxed(typ) => int_range_from_type(typ),
        _ => None,
    }
}

#[derive(PartialEq, Eq, Debug)]
pub enum IntegerTypeBitwidth {
    Width(u32),
    ArchWordSize,
}

impl fmt::Display for IntegerTypeBitwidth {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IntegerTypeBitwidth::Width(w) => write!(f, "{}-bit", w),
            IntegerTypeBitwidth::ArchWordSize => write!(f, "architecture-dependent"),
        }
    }
}

impl IntegerTypeBitwidth {
    pub fn to_exact(&self, arch: &ArchWordBits) -> Option<u32> {
        match (self, arch) {
            (IntegerTypeBitwidth::Width(w), _) => Some(*w),
            (IntegerTypeBitwidth::ArchWordSize, ArchWordBits::Exactly(w)) => Some(*w),
            (IntegerTypeBitwidth::ArchWordSize, _) => None,
        }
    }
}

pub fn bitwidth_from_int_range(int_range: &IntRange) -> Option<IntegerTypeBitwidth> {
    match int_range {
        IntRange::U(size) | IntRange::I(size) => Some(IntegerTypeBitwidth::Width(*size)),
        IntRange::USize | IntRange::ISize => Some(IntegerTypeBitwidth::ArchWordSize),
        IntRange::Int | IntRange::Nat => None,
    }
}

pub fn bitwidth_from_type(et: &Typ) -> Option<IntegerTypeBitwidth> {
    match &*undecorate_typ(et) {
        TypX::Int(int_range) => bitwidth_from_int_range(int_range),
        TypX::Boxed(in_et) => bitwidth_from_type(&*in_et),
        _ => None,
    }
}

pub(crate) fn fixed_integer_const(n: &String, typ: &Typ) -> bool {
    let typ = undecorate_typ(typ);
    if let TypX::Int(IntRange::U(bits)) = &*typ {
        if let Ok(u) = n.parse::<u128>() {
            return *bits == 128 || u < 2u128 << bits;
        }
    }
    if let TypX::Int(IntRange::I(bits)) = &*typ {
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

fn path_as_friendly_rust_name_inner(path: &Path) -> String {
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

static PATH_AS_RUST_NAME_MAP: Mutex<Option<HashMap<Path, String>>> = Mutex::new(None);

pub fn set_path_as_rust_name(path: &Path, friendly: &Path) {
    if let Ok(mut guard) = PATH_AS_RUST_NAME_MAP.lock() {
        let map_opt = &mut *guard;
        if map_opt.is_none() {
            *map_opt = Some(HashMap::new());
        }
        if map_opt.as_mut().unwrap().contains_key(path) {
            return;
        }
        let name = path_as_friendly_rust_name_inner(friendly);
        map_opt.as_mut().unwrap().insert(path.clone(), name);
    }
}

pub fn get_path_as_rust_names_for_krate(krate: &Option<Ident>) -> Vec<(Path, String)> {
    let mut v: Vec<(Path, String)> = Vec::new();
    if let Ok(guard) = PATH_AS_RUST_NAME_MAP.lock() {
        if let Some(map) = &*guard {
            for (path, name) in map {
                if &path.krate == krate {
                    v.push((path.clone(), name.clone()));
                }
            }
        }
    }
    v.sort();
    v
}

pub fn path_as_friendly_rust_name(path: &Path) -> String {
    if let Ok(guard) = PATH_AS_RUST_NAME_MAP.lock() {
        if let Some(map) = &*guard {
            if let Some(name) = map.get(path) {
                return name.clone();
            }
        }
    }
    path_as_friendly_rust_name_inner(path)
}

pub fn path_as_vstd_name(path: &Path) -> Option<String> {
    crate::def::name_as_vstd_name(&path_as_friendly_rust_name(path))
}

pub fn fun_as_friendly_rust_name(fun: &Fun) -> String {
    let FunX { path } = &**fun;
    path_as_friendly_rust_name(path)
}

pub fn friendly_fun_name_crate_relative(module: &Path, fun: &Fun) -> String {
    let full_name = fun_as_friendly_rust_name(fun);
    let module_prefix = path_as_friendly_rust_name(module) + "::";
    if full_name.starts_with(&module_prefix) {
        full_name[module_prefix.len()..].to_string()
    } else {
        full_name
    }
}

// Can source_module see an item restricted to restricted_to?
pub fn is_visible_to_of_owner(restricted_to: &Option<Path>, source_module: &Path) -> bool {
    let sources = &source_module.segments;
    match restricted_to {
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
    is_visible_to_of_owner(&target_visibility.restricted_to, source_module)
}

/// Is the target visible to the module?
/// (If source_module is None, then the target needs to be visible everywhere)
pub fn is_visible_to_opt(target_visibility: &Visibility, source_module: &Option<Path>) -> bool {
    match (&target_visibility.restricted_to, source_module) {
        (None, None) => true,
        (Some(_), None) => false,
        (_, Some(source_module)) => is_visible_to(target_visibility, source_module),
    }
}

impl Visibility {
    pub(crate) fn is_private_to(&self, module: &Option<Path>) -> bool {
        module.is_some() && module == &self.restricted_to
    }

    pub fn public() -> Self {
        Visibility { restricted_to: None }
    }

    /// Return the more restrictive of the two. Panics if the two visibility descriptors
    /// are incompatible.
    pub fn join(&self, vis2: &Visibility) -> Visibility {
        match (&self.restricted_to, &vis2.restricted_to) {
            (None, _) => vis2.clone(),
            (_, None) => self.clone(),
            (Some(p1), Some(p2)) => {
                assert!(p1.krate == p2.krate);
                let m = std::cmp::min(p1.segments.len(), p2.segments.len());
                assert!(&p1.segments[..m] == &p2.segments[..m]);
                if p1.segments.len() < p2.segments.len() { vis2.clone() } else { self.clone() }
            }
        }
    }
}

impl<X> SpannedTyped<X> {
    pub fn new(span: &Span, typ: &Typ, x: X) -> Arc<Self> {
        Arc::new(SpannedTyped { span: span.clone(), typ: typ.clone(), x })
    }

    pub fn new_x<X2>(&self, x: X2) -> Arc<SpannedTyped<X2>> {
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

pub fn fuel_const_int_to_u32(span: &Span, i: &BigInt) -> Result<u32, VirErr> {
    let (sign, digits) = i.to_u32_digits();
    if sign == Sign::NoSign && digits.len() == 0 {
        return Ok(0);
    } else if sign != Sign::Plus || digits.len() != 1 {
        return Err(error(span, "Fuel must be a u32 value"));
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

impl crate::ast::CallTargetKind {
    pub(crate) fn resolved(&self) -> Option<(Fun, Typs)> {
        match self {
            crate::ast::CallTargetKind::Static => None,
            crate::ast::CallTargetKind::Method(None) => None,
            crate::ast::CallTargetKind::Method(Some((f, ts, _))) => Some((f.clone(), ts.clone())),
        }
    }
}

impl FunctionX {
    // unit return values are treated as no return value
    pub fn has_return(&self) -> bool {
        match &*self.ret.x.typ {
            TypX::Tuple(ts) if ts.len() == 0 => false,
            TypX::Datatype(path, _, _) if path == &crate::def::prefix_tuple_type(0) => false,
            _ => true,
        }
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

pub fn typ_to_diagnostic_str(typ: &Typ) -> String {
    fn typs_to_comma_separated_str(typs: &[Arc<TypX>]) -> String {
        typs.iter().map(|t| typ_to_diagnostic_str(t)).collect::<Vec<_>>().join(", ")
    }
    match &**typ {
        TypX::Bool => "bool".to_owned(),
        TypX::Int(IntRange::Nat) => "nat".to_owned(),
        TypX::Int(IntRange::Int) => "int".to_owned(),
        TypX::Int(IntRange::ISize) => "isize".to_owned(),
        TypX::Int(IntRange::USize) => "usize".to_owned(),
        TypX::Int(IntRange::U(n)) => format!("u{n}"),
        TypX::Int(IntRange::I(n)) => format!("i{n}"),
        TypX::Tuple(typs) => format!("({})", typs_to_comma_separated_str(typs)),
        TypX::Lambda(atyps, rtyp) => format!(
            "FnSpec({}) -> {}",
            typs_to_comma_separated_str(atyps),
            typ_to_diagnostic_str(rtyp)
        ),
        TypX::AnonymousClosure(atyps, rtyp, _) => format!(
            "AnonymousClosure({}) -> {}",
            typs_to_comma_separated_str(atyps),
            typ_to_diagnostic_str(rtyp)
        ),
        TypX::Primitive(prim, typs) => {
            let typs_str = typs_to_comma_separated_str(typs);
            match prim {
                crate::ast::Primitive::Array => format!("[{typs_str}; N]"),
                crate::ast::Primitive::Slice => format!("[{typs_str}]"),
            }
        }
        TypX::Datatype(path, typs, _) => format!(
            "{}{}",
            path_as_friendly_rust_name(path),
            if typs.len() > 0 {
                format!("<{}>", typs_to_comma_separated_str(typs))
            } else {
                format!("")
            }
        ),
        TypX::Decorate(TypDecoration::Ref, typ) => {
            format!("&{}", typ_to_diagnostic_str(typ))
        }
        TypX::Decorate(TypDecoration::MutRef, typ) => {
            format!("&mut {}", typ_to_diagnostic_str(typ))
        }
        TypX::Decorate(
            decoration @ (TypDecoration::Box
            | TypDecoration::Rc
            | TypDecoration::Arc
            | TypDecoration::Ghost
            | TypDecoration::Tracked),
            typ,
        ) => {
            format!("{:?}<{}>", decoration, typ_to_diagnostic_str(typ))
        }
        TypX::Decorate(TypDecoration::Never, _typ) => {
            format!("!")
        }
        TypX::Boxed(typ) => typ_to_diagnostic_str(typ),
        TypX::TypParam(ident) => (**ident).clone(),
        TypX::Projection { trait_typ_args, trait_path, name } => {
            let self_typ = typ_to_diagnostic_str(&trait_typ_args[0]);
            format!(
                "<{self_typ} as {}{}>::{name}",
                path_as_friendly_rust_name(trait_path),
                if trait_typ_args.len() > 1 {
                    format!("<{}>", typs_to_comma_separated_str(&trait_typ_args[1..]))
                } else {
                    format!("")
                }
            )
        }
        TypX::TypeId => format!("typeid"),
        TypX::ConstInt(_) => format!("constint"),
        TypX::Air(_) => panic!("unexpected air type here"),
        TypX::StrSlice => format!("StrSlice"),
        TypX::Char => format!("char"),
        TypX::FnDef(f, typs, _res) => format!(
            "FnDef({}){}",
            path_as_friendly_rust_name(&f.path),
            if typs.len() > 0 {
                format!("<{}>", typs_to_comma_separated_str(typs))
            } else {
                format!("")
            }
        ),
    }
}

impl ItemKind {
    pub fn to_string(&self) -> &'static str {
        match self {
            ItemKind::Function => "function",
            ItemKind::Const => "const item",
            ItemKind::Static => "static item",
        }
    }
}
