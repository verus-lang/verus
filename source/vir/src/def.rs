use crate::ast::{Fun, FunX, InvAtomicity, Path, PathX, VarIdent};
use crate::ast_util::air_unique_var;
use crate::messages::Span;
use crate::util::vec_map;
use air::ast::{Commands, Ident};
use serde::{Deserialize, Serialize};
use std::fmt::Debug;
use std::sync::Arc;

/*
In SMT-LIB format (used by Z3), symbols are built of letters, digits, and:
  ~ ! @ $ % ^ & * _ - + = < > . ? /
(although some words, like "pop" and "declare-fun", are reserved words.)
Symbols starting with . or @ are supposed to be reserved for the solver internals.
Z3 seems to like to introduce symbols with !
$ and % and & and ? are probably safe for prefixes and suffixes.
. and @ are safe for suffixes.
AIR uses @ as a suffix for versions of mutable variables (x@0, x@1, ...).

For VIR -> AIR, we use these suffixes:
- types
    - x.
    - x.y.z.
- globals
    - x.?
    - x.y.z.?
- locals inside functions
    - x@ (works well with AIR's mutable variable convention)
- shadowed (or otherwise repeatedly declared) locals inside functions
    - x@, x$1@, x$2@, ...
- bindings inside expressions (e.g. let, forall)
    - x$
*/

// List of prefixes, suffixes, and separators that can appear in generated AIR code
const SUFFIX_GLOBAL: &str = "?";
const SUFFIX_PARAM: &str = "!";
const SUFFIX_LOCAL_STMT: &str = "@";
const SUFFIX_LOCAL_EXPR: &str = "$";
const SUFFIX_TYPE_PARAM: &str = "&";
const SUFFIX_RUSTC_ID: &str = "~";
const SUFFIX_DECORATE_TYPE_PARAM: &str = "&.";
const SUFFIX_REC_PARAM: &str = "!$";
const SUFFIX_PATH: &str = ".";
const PREFIX_FUEL_ID: &str = "fuel%";
const PREFIX_FUEL_NAT: &str = "fuel_nat%";
const PREFIX_REQUIRES: &str = "req%";
const PREFIX_ENSURES: &str = "ens%";
const PREFIX_OPEN_INV: &str = "openinv%";
const PREFIX_NO_UNWIND_WHEN: &str = "no_unwind_when%";
const PREFIX_RECURSIVE: &str = "rec%";
const SIMPLIFY_TEMP_VAR: &str = "tmp%%";
const PREFIX_TEMP_VAR: &str = "tmp%";
pub const PREFIX_EXPAND_ERRORS_TEMP_VAR: &str = "expand%";
const PREFIX_PRE_VAR: &str = "pre%";
const PREFIX_BOX: &str = "Poly%";
const PREFIX_UNBOX: &str = "%Poly%";
const PREFIX_TYPE_ID: &str = "TYPE%";
const PREFIX_FNDEF_TYPE_ID: &str = "FNDEF%";
const PREFIX_TUPLE_TYPE: &str = "tuple%";
const PREFIX_CLOSURE_TYPE: &str = "anonymous_closure%";
const PREFIX_TUPLE_PARAM: &str = "T%";
const PREFIX_SPEC_FN_TYPE: &str = "fun%";
const PREFIX_IMPL_IDENT: &str = "impl&%";
const PREFIX_PROJECT: &str = "proj%";
const PREFIX_PROJECT_DECORATION: &str = "proj%%";
const PREFIX_PROJECT_PARAM: &str = "Proj%";
const PREFIX_TRAIT_BOUND: &str = "tr_bound%";
const PREFIX_STATIC: &str = "static%";
const PREFIX_BREAK_LABEL: &str = "break_label%";
const SLICE_TYPE: &str = "slice%";
const STRSLICE_TYPE: &str = "strslice%";
const ARRAY_TYPE: &str = "array%";
const PTR_TYPE: &str = "ptr_mut%";
const GLOBAL_TYPE: &str = "allocator_global%";
const PREFIX_SNAPSHOT: &str = "snap%";
const SUBST_RENAME_SEPARATOR: &str = "$$";
const EXPAND_ERRORS_DECL_SEPARATOR: &str = "$$$";
const BITVEC_TMP_DECL_SEPARATOR: &str = "$$$$bitvectmp";
const USER_DEF_TYPE_INV_TMP_DECL_SEPARATOR: &str = "$$$$userdeftypeinvpass";
const KRATE_SEPARATOR: &str = "!";
const PATH_SEPARATOR: &str = ".";
const PATHS_SEPARATOR: &str = "/";
const VARIANT_SEPARATOR: &str = "/";
const VARIANT_FIELD_SEPARATOR: &str = "/";
const VARIANT_FIELD_INTERNAL_SEPARATOR: &str = "/?";
const PROJECT_SEPARATOR: &str = "/";
const MONOTYPE_APP_BEGIN: &str = "<";
const MONOTYPE_APP_END: &str = ">";
const MONOTYPE_DECORATE: &str = "$%";
const TRAIT_DEFAULT_SEPARATOR: &str = "%default%";
const DECREASE_AT_ENTRY: &str = "decrease%init";
const TRAIT_SELF_TYPE_PARAM: &str = "Self%";
const DUMMY_PARAM: &str = "no%param";

pub const PREFIX_IMPL_TYPE_PARAM: &str = "impl%";
pub const SUFFIX_SNAP_MUT: &str = "_mutation";
pub const SUFFIX_SNAP_JOIN: &str = "_join";
pub const SUFFIX_SNAP_WHILE_BEGIN: &str = "_while_begin";
pub const SUFFIX_SNAP_WHILE_END: &str = "_while_end";

pub const CLOSURE_RETURN_VALUE_PREFIX: &str = "%closure_return";

pub const FNDEF_TYPE: &str = "fndef";
pub const FNDEF_SINGLETON: &str = "fndef_singleton";

// List of constant strings that can appear in generated AIR code
pub const FUEL_ID: &str = "FuelId";
pub const FUEL_TYPE: &str = "Fuel";
pub const ZERO: &str = "zero";
pub const SUCC: &str = "succ";
pub const FUEL_PARAM: &str = "fuel%";
pub const FUEL_BOOL: &str = "fuel_bool";
pub const FUEL_BOOL_DEFAULT: &str = "fuel_bool_default";
pub const FUEL_DEFAULTS: &str = "fuel_defaults";
pub const RETURN_VALUE: &str = "%return";
pub const U_HI: &str = "uHi";
pub const I_LO: &str = "iLo";
pub const I_HI: &str = "iHi";
pub const U_CLIP: &str = "uClip";
pub const I_CLIP: &str = "iClip";
pub const NAT_CLIP: &str = "nClip";
pub const CHAR_CLIP: &str = "charClip";
pub const U_INV: &str = "uInv";
pub const I_INV: &str = "iInv";
pub const CHAR_INV: &str = "charInv";
pub const ARCH_SIZE: &str = "SZ";
pub const ADD: &str = "Add";
pub const SUB: &str = "Sub";
pub const MUL: &str = "Mul";
pub const EUC_DIV: &str = "EucDiv";
pub const EUC_MOD: &str = "EucMod";
pub const SNAPSHOT_CALL: &str = "CALL";
pub const SNAPSHOT_PRE: &str = "PRE";
pub const SNAPSHOT_ASSIGN: &str = "ASSIGN";
pub const T_HEIGHT: &str = "Height";
pub const POLY: &str = "Poly";
pub const BOX_INT: &str = "I";
pub const BOX_BOOL: &str = "B";
pub const BOX_FNDEF: &str = "F";
pub const UNBOX_INT: &str = "%I";
pub const UNBOX_BOOL: &str = "%B";
pub const UNBOX_FNDEF: &str = "%F";
pub const TYPE: &str = "Type";
pub const TYPE_ID_BOOL: &str = "BOOL";
pub const TYPE_ID_INT: &str = "INT";
pub const TYPE_ID_CHAR: &str = "CHAR";
pub const TYPE_ID_NAT: &str = "NAT";
pub const TYPE_ID_UINT: &str = "UINT";
pub const TYPE_ID_SINT: &str = "SINT";
pub const TYPE_ID_CONST_INT: &str = "CONST_INT";
pub const DECORATION: &str = "Dcr";
pub const DECORATE_NIL: &str = "$";
pub const DECORATE_REF: &str = "REF";
pub const DECORATE_MUT_REF: &str = "MUT_REF";
pub const DECORATE_BOX: &str = "BOX";
pub const DECORATE_RC: &str = "RC";
pub const DECORATE_ARC: &str = "ARC";
pub const DECORATE_GHOST: &str = "GHOST";
pub const DECORATE_TRACKED: &str = "TRACKED";
pub const DECORATE_NEVER: &str = "NEVER";
pub const DECORATE_CONST_PTR: &str = "CONST_PTR";
pub const TYPE_ID_ARRAY: &str = "ARRAY";
pub const TYPE_ID_SLICE: &str = "SLICE";
pub const TYPE_ID_STRSLICE: &str = "STRSLICE";
pub const TYPE_ID_PTR: &str = "PTR";
pub const TYPE_ID_GLOBAL: &str = "ALLOCATOR_GLOBAL";
pub const HAS_TYPE: &str = "has_type";
pub const AS_TYPE: &str = "as_type";
pub const MK_FUN: &str = "mk_fun";
pub const CONST_INT: &str = "const_int";
pub const CHECK_DECREASE_INT: &str = "check_decrease_int";
pub const CHECK_DECREASE_HEIGHT: &str = "check_decrease_height";
pub const HEIGHT: &str = "height";
pub const HEIGHT_LT: &str = "height_lt";
pub const HEIGHT_REC_FUN: &str = "fun_from_recursive_field";
pub const CLOSURE_REQ: &str = "closure_req";
pub const CLOSURE_ENS: &str = "closure_ens";
pub const EXT_EQ: &str = "ext_eq";

pub const BIT_XOR: &str = "bitxor";
pub const BIT_AND: &str = "bitand";
pub const BIT_OR: &str = "bitor";
pub const BIT_SHR: &str = "bitshr";
pub const BIT_SHL: &str = "bitshl";
pub const BIT_NOT: &str = "bitnot";
pub const SINGULAR_MOD: &str = "singular_mod";

pub const ARRAY_NEW: &str = "array_new";
pub const ARRAY_INDEX: &str = "array_index";

// List of QID suffixes we add to internally generated quantifiers
pub const QID_BOX_AXIOM: &str = "box_axiom";
pub const QID_UNBOX_AXIOM: &str = "unbox_axiom";
pub const QID_CONSTRUCTOR_INNER: &str = "constructor_inner";
pub const QID_CONSTRUCTOR: &str = "constructor";
pub const QID_EXT_EQUAL: &str = "ext_equal";
pub const QID_APPLY: &str = "apply";
pub const QID_HEIGHT_APPLY: &str = "height_apply";
pub const QID_ACCESSOR: &str = "accessor";
pub const QID_INVARIANT: &str = "invariant";
pub const QID_HAS_TYPE_ALWAYS: &str = "has_type_always";
pub const QID_TRAIT_IMPL: &str = "trait_impl";
pub const QID_TRAIT_TYPE_BOUNDS: &str = "trait_type_bounds";
pub const QID_ASSOC_TYPE_BOUND: &str = "assoc_type_bound";
pub const QID_ASSOC_TYPE_IMPL: &str = "assoc_type_impl";

pub const VERUS_SPEC: &str = "VERUS_SPEC__";

pub const STRSLICE_IS_ASCII: &str = "str%strslice_is_ascii";
pub const STRSLICE_LEN: &str = "str%strslice_len";
pub const STRSLICE_GET_CHAR: &str = "str%strslice_get_char";
pub const STRSLICE_NEW_STRLIT: &str = "str%new_strlit";
// only used to prove that new_strlit is injective
pub const STRSLICE_FROM_STRLIT: &str = "str%from_strlit";

pub const VERUSLIB: &str = "vstd";
pub const VERUSLIB_PREFIX: &str = "vstd::";
pub const PERVASIVE_PREFIX: &str = "pervasive::";

pub const RUST_DEF_CTOR: &str = "ctor%";

// List of pre-defined error messages
pub const ASSERTION_FAILURE: &str = "assertion failure";
pub const PRECONDITION_FAILURE: &str = "precondition not satisfied";
pub const POSTCONDITION_FAILURE: &str = "postcondition not satisfied";
pub const THIS_POST_FAILED: &str = "failed this postcondition";
pub const THIS_PRE_FAILED: &str = "failed precondition";
pub const INV_FAIL_LOOP_END: &str = "invariant not satisfied at end of loop body";
pub const INV_FAIL_LOOP_FRONT: &str = "invariant not satisfied before loop";
pub const DEC_FAIL_LOOP_END: &str = "decreases not satisfied at end of loop";
pub const DEC_FAIL_LOOP_CONTINUE: &str = "decreases not satisfied at continue";
pub const SPLIT_ASSERT_FAILURE: &str = "split assertion failure";
pub const SPLIT_PRE_FAILURE: &str = "split precondition failure";
pub const SPLIT_POST_FAILURE: &str = "split postcondition failure";

pub const PERVASIVE_ASSERT: &[&str] = &["pervasive", "assert"];

pub fn path_to_string(path: &Path) -> String {
    let s = vec_map(&path.segments, |s| s.to_string()).join(PATH_SEPARATOR) + SUFFIX_PATH;
    if let Some(krate) = &path.krate { krate.to_string() + KRATE_SEPARATOR + &s } else { s }
}

pub fn fun_to_string(fun: &Fun) -> String {
    let FunX { path } = &(**fun);
    path_to_string(path)
}

pub fn decrease_at_entry(loop_id: Option<u64>, n: usize) -> VarIdent {
    let loop_id = loop_id.map_or("".to_string(), |s| format!("{s}%"));
    air_unique_var(&format!("{}{}{}", DECREASE_AT_ENTRY, loop_id, n))
}

pub fn trait_self_type_param() -> Ident {
    Arc::new(TRAIT_SELF_TYPE_PARAM.to_string())
}

pub(crate) fn trait_default_name(default_fun: &Fun) -> Fun {
    let path = (**default_fun).path.clone();
    let mut segments = (*path.segments).clone();
    let x = segments.last().expect("segment").to_string() + TRAIT_DEFAULT_SEPARATOR;
    *segments.last_mut().unwrap() = Arc::new(x);
    Arc::new(crate::ast::FunX {
        path: Arc::new(crate::ast::PathX {
            krate: path.krate.clone(),
            segments: Arc::new(segments),
        }),
    })
}

pub fn trait_inherit_default_name(default_fun: &Fun, impl_path: &Path) -> Fun {
    let path = (**impl_path).clone();
    let mut segments = (*path.segments).clone();
    let x = segments.last().expect("segment").to_string()
        + TRAIT_DEFAULT_SEPARATOR
        + default_fun.path.segments.last().unwrap();
    *segments.last_mut().unwrap() = Arc::new(x);
    Arc::new(crate::ast::FunX {
        path: Arc::new(crate::ast::PathX {
            krate: path.krate.clone(),
            segments: Arc::new(segments),
        }),
    })
}

pub fn suffix_global_id(ident: &Ident) -> Ident {
    Arc::new(ident.to_string() + SUFFIX_GLOBAL)
}

// TODO: this is currently only used by debugger.rs; consider replacing this
pub fn suffix_local_stmt_id(ident: &Ident) -> Ident {
    Arc::new(ident.to_string() + SUFFIX_LOCAL_STMT)
}

// TODO: get rid of this
pub(crate) fn unique_bound(id: &VarIdent) -> VarIdent {
    id.clone()
}

// TODO: get rid of this
pub(crate) fn unique_local(id: &VarIdent) -> VarIdent {
    id.clone()
}

// TODO: get rid of this
pub fn suffix_local_unique_id(ident: &VarIdent) -> Ident {
    use crate::ast_util::LowerUniqueVar;
    ident.lower()
}

pub fn subst_rename_ident(x: &VarIdent, n: u64) -> VarIdent {
    let dis = crate::ast::VarIdentDisambiguate::VirSubst(n);
    crate::ast::VarIdent(x.0.clone(), dis)
}

pub(crate) fn suffix_typ_param_var(x: &VarIdent) -> VarIdent {
    assert!(x.1 == crate::ast::VarIdentDisambiguate::TypParamBare);
    let dis = crate::ast::VarIdentDisambiguate::TypParamSuffixed;
    crate::ast::VarIdent(x.0.clone(), dis)
}

pub(crate) fn suffix_decorate_typ_param_var(x: &VarIdent) -> VarIdent {
    assert!(x.1 == crate::ast::VarIdentDisambiguate::TypParamBare);
    let dis = crate::ast::VarIdentDisambiguate::TypParamDecorated;
    crate::ast::VarIdent(x.0.clone(), dis)
}

pub(crate) fn suffix_typ_param_vars(unique_var: &VarIdent) -> Vec<VarIdent> {
    if crate::context::DECORATE {
        vec![suffix_decorate_typ_param_var(unique_var), suffix_typ_param_var(unique_var)]
    } else {
        vec![suffix_typ_param_var(unique_var)]
    }
}

pub(crate) fn suffix_typ_param_vars_types(unique_var: &VarIdent) -> Vec<(VarIdent, &'static str)> {
    if crate::context::DECORATE {
        vec![
            (suffix_decorate_typ_param_var(unique_var), DECORATION),
            (suffix_typ_param_var(unique_var), TYPE),
        ]
    } else {
        vec![(suffix_typ_param_var(unique_var), TYPE)]
    }
}

pub(crate) fn suffix_typ_param_id(ident: &Ident) -> VarIdent {
    suffix_typ_param_var(&crate::ast_util::typ_unique_var(ident))
}

pub(crate) fn suffix_typ_param_ids(ident: &Ident) -> Vec<VarIdent> {
    suffix_typ_param_vars(&crate::ast_util::typ_unique_var(ident))
}

pub(crate) fn suffix_typ_param_ids_types(ident: &Ident) -> Vec<(VarIdent, &'static str)> {
    suffix_typ_param_vars_types(&crate::ast_util::typ_unique_var(ident))
}

pub(crate) fn types() -> Vec<&'static str> {
    if crate::context::DECORATE { vec![DECORATION, TYPE] } else { vec![TYPE] }
}

pub fn rename_rec_param(ident: &VarIdent, n: usize) -> VarIdent {
    let dis = crate::ast::VarIdentDisambiguate::VirParamRecursion(n);
    crate::ast::VarIdent(ident.0.clone(), dis)
}

pub fn slice_type() -> Path {
    let ident = Arc::new(SLICE_TYPE.to_string());
    Arc::new(PathX { krate: None, segments: Arc::new(vec![ident]) })
}

pub fn strslice_type() -> Path {
    let ident = Arc::new(STRSLICE_TYPE.to_string());
    Arc::new(PathX { krate: None, segments: Arc::new(vec![ident]) })
}

pub fn array_type() -> Path {
    let ident = Arc::new(ARRAY_TYPE.to_string());
    Arc::new(PathX { krate: None, segments: Arc::new(vec![ident]) })
}

pub fn ptr_type() -> Path {
    let ident = Arc::new(PTR_TYPE.to_string());
    Arc::new(PathX { krate: None, segments: Arc::new(vec![ident]) })
}

pub fn global_type() -> Path {
    let ident = Arc::new(GLOBAL_TYPE.to_string());
    Arc::new(PathX { krate: None, segments: Arc::new(vec![ident]) })
}

pub fn prefix_type_id(path: &Path) -> Ident {
    Arc::new(PREFIX_TYPE_ID.to_string() + &path_to_string(path))
}

pub fn prefix_fndef_type_id(fun: &Fun) -> Ident {
    Arc::new(PREFIX_FNDEF_TYPE_ID.to_string() + &fun_to_string(fun))
}

pub fn prefix_tuple_type(i: usize) -> Path {
    let ident = Arc::new(format!("{}{}", PREFIX_TUPLE_TYPE, i));
    Arc::new(PathX { krate: None, segments: Arc::new(vec![ident]) })
}

pub fn prefix_closure_type(i: usize) -> Path {
    let ident = Arc::new(format!("{}{}", PREFIX_CLOSURE_TYPE, i));
    Arc::new(PathX { krate: None, segments: Arc::new(vec![ident]) })
}

pub fn prefix_tuple_variant(i: usize) -> Ident {
    Arc::new(format!("{}{}", PREFIX_TUPLE_TYPE, i))
}

pub fn prefix_tuple_param(i: usize) -> Ident {
    Arc::new(format!("{}{}", PREFIX_TUPLE_PARAM, i))
}

pub fn prefix_spec_fn_type(i: usize) -> Path {
    let ident = Arc::new(format!("{}{}", PREFIX_SPEC_FN_TYPE, i));
    Arc::new(PathX { krate: None, segments: Arc::new(vec![ident]) })
}

pub fn impl_ident(disambiguator: u32) -> Ident {
    Arc::new(format!("{}{}", PREFIX_IMPL_IDENT, disambiguator))
}

pub fn projection(decoration: bool, trait_path: &Path, name: &Ident) -> Ident {
    let proj = if decoration { PREFIX_PROJECT_DECORATION } else { PREFIX_PROJECT };
    Arc::new(format!(
        "{}{}{}{}",
        proj,
        path_to_string(trait_path),
        PROJECT_SEPARATOR,
        name.to_string()
    ))
}

pub fn proj_param(i: usize) -> Ident {
    Arc::new(format!("{}{}", PREFIX_PROJECT_PARAM, i))
}

pub fn trait_bound(trait_path: &Path) -> Ident {
    Arc::new(format!("{}{}", PREFIX_TRAIT_BOUND, path_to_string(trait_path)))
}

pub fn prefix_type_id_fun(i: usize) -> Ident {
    prefix_type_id(&prefix_spec_fn_type(i))
}

pub fn prefix_box(ident: &Path) -> Ident {
    Arc::new(PREFIX_BOX.to_string() + &path_to_string(ident))
}

pub fn prefix_unbox(ident: &Path) -> Ident {
    Arc::new(PREFIX_UNBOX.to_string() + &path_to_string(ident))
}

pub fn prefix_fuel_id(ident: &Ident) -> Ident {
    Arc::new(PREFIX_FUEL_ID.to_string() + ident)
}

pub fn prefix_fuel_nat(ident: &Ident) -> Ident {
    Arc::new(PREFIX_FUEL_NAT.to_string() + ident)
}

pub fn prefix_requires(ident: &Ident) -> Ident {
    Arc::new(PREFIX_REQUIRES.to_string() + ident)
}

pub fn prefix_ensures(ident: &Ident) -> Ident {
    Arc::new(PREFIX_ENSURES.to_string() + ident)
}

pub fn prefix_open_inv(ident: &Ident, i: usize) -> Ident {
    Arc::new(format!("{}{}%{}", PREFIX_OPEN_INV, i, ident))
}

pub fn prefix_no_unwind_when(ident: &Ident) -> Ident {
    Arc::new(PREFIX_NO_UNWIND_WHEN.to_string() + ident)
}

fn prefix_path(prefix: String, path: &Path) -> Path {
    let mut segments: Vec<Ident> = (*path.segments).clone();
    let last: &mut Ident = segments.last_mut().expect("path last segment");
    *last = Arc::new(prefix + &**last);
    let pathx = PathX { krate: path.krate.clone(), segments: Arc::new(segments) };
    Arc::new(pathx)
}

fn prefix_recursive(path: &Path) -> Path {
    prefix_path(PREFIX_RECURSIVE.to_string(), path)
}

pub fn prefix_recursive_fun(fun: &Fun) -> Fun {
    let FunX { path } = &(**fun);
    let path = prefix_recursive(path);
    Arc::new(FunX { path })
}

pub fn new_temp_var(n: u64) -> VarIdent {
    crate::ast_util::str_unique_var(PREFIX_TEMP_VAR, crate::ast::VarIdentDisambiguate::VirTemp(n))
}

// ast_simplify introduces its own temporary variables; we don't want these to conflict with prefix_temp_var
pub fn simplify_temp_var(n: u64) -> VarIdent {
    crate::ast_util::str_unique_var(SIMPLIFY_TEMP_VAR, crate::ast::VarIdentDisambiguate::VirTemp(n))
}

pub fn prefix_pre_var(name: &Ident) -> Ident {
    Arc::new(PREFIX_PRE_VAR.to_string() + name)
}

pub fn variant_ident(datatype: &Path, variant: &str) -> Ident {
    Arc::new(format!("{}{}{}", path_to_string(datatype), VARIANT_SEPARATOR, variant))
}

pub fn is_variant_ident(datatype: &Path, variant: &str) -> Ident {
    Arc::new(format!("is-{}", variant_ident(datatype, variant)))
}

pub fn variant_field_ident_internal(
    datatype: &Path,
    variant: &Ident,
    field: &Ident,
    internal: bool,
) -> Ident {
    Arc::new(format!(
        "{}{}{}{}{}",
        path_to_string(datatype),
        VARIANT_SEPARATOR,
        variant.as_str(),
        if internal { VARIANT_FIELD_INTERNAL_SEPARATOR } else { VARIANT_FIELD_SEPARATOR },
        field.as_str()
    ))
}

pub fn variant_field_ident(datatype: &Path, variant: &Ident, field: &Ident) -> Ident {
    variant_field_ident_internal(datatype, variant, field, false)
}

pub fn positional_field_ident(idx: usize) -> Ident {
    Arc::new(format!("{}", idx))
}

pub fn field_ident_from_rust(s: &str) -> Ident {
    Arc::new(format!("{}", s))
}

pub fn monotyp_apply(datatype: &Path, args: &Vec<Path>) -> Path {
    if args.len() == 0 {
        datatype.clone()
    } else {
        let mut segments = (*datatype.segments).clone();
        let last = segments.last_mut().expect("last path segment");
        let ident = Arc::new(format!(
            "{}{}{}{}",
            last,
            MONOTYPE_APP_BEGIN,
            vec_map(args, |x| path_to_string(x)).join(PATHS_SEPARATOR),
            MONOTYPE_APP_END,
        ));
        *last = ident;
        Arc::new(PathX { krate: datatype.krate.clone(), segments: Arc::new(segments) })
    }
}

pub fn monotyp_decorate(dec: crate::ast::TypDecoration, path: &Path) -> Path {
    let id = Arc::new(format!(
        "{}{}{}{}{}",
        MONOTYPE_DECORATE,
        dec as u32,
        MONOTYPE_APP_BEGIN,
        path_to_string(path),
        MONOTYPE_APP_END
    ));
    Arc::new(PathX { krate: None, segments: Arc::new(vec![id]) })
}

pub fn monotyp_decorate2(dec: crate::ast::TypDecoration, args: &Vec<Path>) -> Path {
    let id = Arc::new(format!(
        "{}{}{}{}{}",
        MONOTYPE_DECORATE,
        dec as u32,
        MONOTYPE_APP_BEGIN,
        vec_map(args, |x| path_to_string(x)).join(PATHS_SEPARATOR),
        MONOTYPE_APP_END
    ));
    Arc::new(PathX { krate: None, segments: Arc::new(vec![id]) })
}

pub fn name_as_vstd_name(name: &String) -> Option<String> {
    let name = if let Some(x) = name.strip_prefix(crate::def::VERUSLIB_PREFIX) {
        if let Some(x) = x.strip_prefix(crate::def::PERVASIVE_PREFIX) {
            return Some(x.to_string());
        }
        return Some(x.to_string());
    } else if let Some(x) = name.strip_prefix("crate::") {
        x.to_string()
    } else {
        return None;
    };
    if let Some(x) = name.strip_prefix(crate::def::PERVASIVE_PREFIX) {
        Some(x.to_string())
    } else {
        None
    }
}

// Generate a unique quantifier name
pub fn new_user_qid_name(fun_name: &str, q_count: u64) -> String {
    // In SMTLIB, unquoted attribute values cannot contain colons,
    // and sise cannot handle quoting with vertical bars
    let fun_name = str::replace(&fun_name, ":", "_");
    let qid = format!("{}{}_{}", air::profiler::USER_QUANT_PREFIX, fun_name, q_count);
    qid
}

// Generate a unique internal quantifier ID
pub fn new_internal_qid(ctx: &crate::context::Ctx, name: String) -> Option<Ident> {
    // In SMTLIB, unquoted attribute values cannot contain colons,
    // and sise cannot handle quoting with vertical bars
    let name = str::replace(&name, ":", "_");
    let name = str::replace(&name, "%", "__");
    let qid = format!("{}{}_definition", air::profiler::INTERNAL_QUANT_PREFIX, name);

    if let Some(fun) = ctx.fun.as_ref() {
        let bnd_info = crate::sst::BndInfo { fun: fun.current_fun.clone(), user: None };
        ctx.global.qid_map.borrow_mut().insert(qid.clone(), bnd_info);
    }

    Some(Arc::new(qid))
}

pub fn snapshot_ident(name: &str) -> Ident {
    Arc::new(format!("{}{}", PREFIX_SNAPSHOT, name))
}

/// For a given snapshot, does it represent the state
/// at the start of the corresponding span, the end, or the full span?
#[derive(Debug)]
pub enum SpanKind {
    Start,
    Full,
    End,
}

#[derive(Debug)]
pub struct SnapPos {
    pub snapshot_id: Ident,
    pub kind: SpanKind,
}

#[derive(Serialize, Deserialize, Clone)]
pub struct Spanned<X> {
    pub span: Span,
    pub x: X,
}

impl<X> Spanned<X> {
    pub fn new(span: Span, x: X) -> Arc<Spanned<X>> {
        Arc::new(Spanned { span: span, x: x })
    }

    pub fn new_x<X2>(&self, x: X2) -> Arc<Spanned<X2>> {
        Arc::new(Spanned { span: self.span.clone(), x })
    }

    pub fn map_x<Y>(&self, f: impl FnOnce(&X) -> Y) -> Arc<Spanned<Y>> {
        Arc::new(Spanned { span: self.span.clone(), x: f(&self.x) })
    }
}

impl<X: Debug> Debug for Spanned<X> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.debug_tuple("Spanned").field(&self.span.as_string).field(&self.x).finish()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ProverChoice {
    DefaultProver,
    Nonlinear,
    BitVector,
    Singular,
}

#[derive(Clone, Debug)]
pub struct CommandContext {
    pub fun: Fun,
    pub span: crate::messages::Span,
    pub desc: String,
}

impl CommandContext {
    pub fn with_desc_prefix(&self, prefix: Option<&str>) -> Self {
        let CommandContext { fun, span, desc } = self;
        CommandContext {
            fun: fun.clone(),
            span: span.clone(),
            desc: prefix.unwrap_or("").to_string() + desc,
        }
    }
}

#[derive(Debug)]
#[derive(Clone)]
pub struct CommandsWithContextX {
    pub context: CommandContext,
    pub commands: Commands,
    pub prover_choice: ProverChoice,
    pub skip_recommends: bool,
    pub hint_upon_failure: std::cell::RefCell<Option<crate::messages::Message>>,
}

impl CommandsWithContextX {
    pub fn new(
        fun: Fun,
        span: Span,
        desc: String,
        commands: Commands,
        prover_choice: ProverChoice,
        skip_recommends: bool,
    ) -> CommandsWithContext {
        Arc::new(CommandsWithContextX {
            context: CommandContext { fun, span, desc },
            commands,
            prover_choice,
            skip_recommends,
            hint_upon_failure: std::cell::RefCell::new(None),
        })
    }
}

pub type CommandsWithContext = Arc<CommandsWithContextX>;

fn atomicity_type_name(atomicity: InvAtomicity) -> Ident {
    match atomicity {
        InvAtomicity::Atomic => Arc::new("AtomicInvariant".to_string()),
        InvAtomicity::NonAtomic => Arc::new("LocalInvariant".to_string()),
    }
}

pub fn fn_inv_name(vstd_crate_name: &Ident, atomicity: InvAtomicity) -> Fun {
    Arc::new(FunX {
        path: Arc::new(PathX {
            krate: Some(vstd_crate_name.clone()),
            segments: Arc::new(vec![
                Arc::new("invariant".to_string()),
                atomicity_type_name(atomicity),
                Arc::new("inv".to_string()),
            ]),
        }),
    })
}

pub fn create_open_invariant_credit_path(vstd_crate_name: &Option<Ident>) -> Path {
    Arc::new(PathX {
        krate: vstd_crate_name.clone(),
        segments: Arc::new(vec![
            Arc::new("invariant".to_string()),
            Arc::new("create_open_invariant_credit".to_string()),
        ]),
    })
}

pub fn spend_open_invariant_credit_path(vstd_crate_name: &Option<Ident>) -> Path {
    Arc::new(PathX {
        krate: vstd_crate_name.clone(),
        segments: Arc::new(vec![
            Arc::new("invariant".to_string()),
            Arc::new("spend_open_invariant_credit".to_string()),
        ]),
    })
}

pub fn fn_namespace_name(vstd_crate_name: &Ident, atomicity: InvAtomicity) -> Fun {
    Arc::new(FunX {
        path: Arc::new(PathX {
            krate: Some(vstd_crate_name.clone()),
            segments: Arc::new(vec![
                Arc::new("invariant".to_string()),
                atomicity_type_name(atomicity),
                Arc::new("namespace".to_string()),
            ]),
        }),
    })
}

pub fn strslice_module_path(vstd_crate_name: &Ident) -> Path {
    Arc::new(PathX {
        krate: Some(vstd_crate_name.clone()),
        segments: Arc::new(vec![Arc::new("string".to_string())]),
    })
}

/// Inverse of unique_local_name: extracts the user_given_name from
/// a unique name (e.g., given "a~2", returns "a"
pub fn user_local_name<'a>(s: &'a VarIdent) -> &'a str {
    &s.0
}

pub fn unique_var_name(
    user_given_name: String,
    uniq_id: crate::ast::VarIdentDisambiguate,
) -> String {
    use {crate::ast::VarIdentDisambiguate, std::fmt::Write};
    let mut out = user_given_name;
    match uniq_id {
        VarIdentDisambiguate::AirLocal => {}
        VarIdentDisambiguate::NoBodyParam => {
            out.push_str(SUFFIX_PARAM);
        }
        VarIdentDisambiguate::Field => {
            out.push_str(SUFFIX_PARAM);
        }
        VarIdentDisambiguate::TypParamBare => {}
        VarIdentDisambiguate::TypParamSuffixed => {
            out.push_str(SUFFIX_TYPE_PARAM);
        }
        VarIdentDisambiguate::TypParamDecorated => {
            out.push_str(SUFFIX_DECORATE_TYPE_PARAM);
        }
        VarIdentDisambiguate::RustcId(id) => {
            out.push_str(SUFFIX_RUSTC_ID);
            write!(&mut out, "{}", id).unwrap();
        }
        VarIdentDisambiguate::VirRenumbered { is_stmt, id, .. } => {
            if is_stmt {
                if id != 0 {
                    out.push_str(SUFFIX_LOCAL_EXPR);
                    write!(&mut out, "{}", id).unwrap();
                }
                out.push_str(SUFFIX_LOCAL_STMT);
            } else {
                out.push_str(SUFFIX_LOCAL_EXPR);
                write!(&mut out, "{}", id).unwrap();
            }
        }
        VarIdentDisambiguate::VirExprNoNumber => {
            out.push_str(SUFFIX_LOCAL_EXPR);
        }
        VarIdentDisambiguate::VirParam => {
            out.push_str(SUFFIX_PARAM);
        }
        VarIdentDisambiguate::VirParamRecursion(n) => {
            out.push_str(SUFFIX_REC_PARAM);
            write!(&mut out, "{}", n).unwrap();
        }
        VarIdentDisambiguate::VirSubst(n) => {
            out.push_str(SUBST_RENAME_SEPARATOR);
            write!(&mut out, "{}", n).unwrap();
        }
        VarIdentDisambiguate::VirTemp(id) => {
            write!(&mut out, "{}", id).unwrap();
        }
        VarIdentDisambiguate::ExpandErrorsDecl(id) => {
            out.push_str(EXPAND_ERRORS_DECL_SEPARATOR);
            write!(&mut out, "{}", id).unwrap();
        }
        VarIdentDisambiguate::BitVectorToAirDecl(id) => {
            out.push_str(BITVEC_TMP_DECL_SEPARATOR);
            write!(&mut out, "{}", id).unwrap();
        }
        VarIdentDisambiguate::UserDefinedTypeInvariantPass(id) => {
            out.push_str(USER_DEF_TYPE_INV_TMP_DECL_SEPARATOR);
            write!(&mut out, "{}", id).unwrap();
        }
    }
    out
}

pub fn exec_nonstatic_call_fun(vstd_crate_name: &Ident) -> Fun {
    Arc::new(FunX { path: exec_nonstatic_call_path(&Some(vstd_crate_name.clone())) })
}

pub fn exec_nonstatic_call_path(vstd_crate_name: &Option<Ident>) -> Path {
    Arc::new(PathX {
        krate: vstd_crate_name.clone(),
        segments: Arc::new(vec![
            Arc::new("pervasive".to_string()),
            Arc::new("exec_nonstatic_call".to_string()),
        ]),
    })
}

pub fn static_name(fun: &Fun) -> Ident {
    Arc::new(PREFIX_STATIC.to_string() + &fun_to_string(fun))
}

pub fn break_label(i: u64) -> Ident {
    Arc::new(format!("{}{}", PREFIX_BREAK_LABEL, i))
}

pub fn array_new_path(vstd_crate_name: &Ident) -> Path {
    Arc::new(PathX {
        krate: Some(vstd_crate_name.clone()),
        segments: Arc::new(vec![Arc::new("array".to_string()), Arc::new("array_new".to_string())]),
    })
}

pub(crate) fn option_type_path() -> Path {
    Arc::new(PathX {
        krate: Some(Arc::new("core".to_string())),
        segments: Arc::new(vec![Arc::new("option".to_string()), Arc::new("Option".to_string())]),
    })
}

pub(crate) fn dummy_param_name() -> VarIdent {
    air_unique_var(DUMMY_PARAM)
}

pub(crate) fn is_dummy_param_name(v: &VarIdent) -> bool {
    v.0.to_string() == DUMMY_PARAM
}
