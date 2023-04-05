use crate::ast::{Fun, FunX, InvAtomicity, Path, PathX};
use crate::sst::UniqueIdent;
use crate::util::vec_map;
use air::ast::{Commands, Ident, Span};
use air::ast_util::str_ident;
use air::printer::str_to_node;
use serde::{Deserialize, Serialize};
use sise::Node;
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
const SUFFIX_LOCAL_STMT: &str = "@";
const SUFFIX_LOCAL_EXPR: &str = "$";
const SUFFIX_TYPE_PARAM: &str = "&";
const SUFFIX_RENAME: &str = "!";
const SUFFIX_PATH: &str = ".";
const PREFIX_FUEL_ID: &str = "fuel%";
const PREFIX_FUEL_NAT: &str = "fuel_nat%";
const PREFIX_REQUIRES: &str = "req%";
const PREFIX_STR: &str = "str%";
const PREFIX_CHAR: &str = "char%";
const PREFIX_ENSURES: &str = "ens%";
const PREFIX_RECURSIVE: &str = "rec%";
const PREFIX_SIMPLIFY_TEMP_VAR: &str = "tmp%%";
const PREFIX_TEMP_VAR: &str = "tmp%";
const PREFIX_PRE_VAR: &str = "pre%";
const PREFIX_BOX: &str = "Poly%";
const PREFIX_UNBOX: &str = "%Poly%";
const PREFIX_TYPE_ID: &str = "TYPE%";
const PREFIX_TUPLE_TYPE: &str = "tuple%";
const PREFIX_CLOSURE_TYPE: &str = "anonymous_closure%";
const PREFIX_TUPLE_PARAM: &str = "T%";
const PREFIX_TUPLE_FIELD: &str = "field%";
const PREFIX_LAMBDA_TYPE: &str = "fun%";
const SLICE_TYPE: &str = "slice%";
const SLICE_PARAM: &str = "sliceT%";
const PREFIX_SNAPSHOT: &str = "snap%";
const LOCAL_UNIQUE_ID_SEPARATOR: char = '~';
const SUBST_RENAME_SEPARATOR: &str = "$$";
const KRATE_SEPARATOR: &str = "!";
const PATH_SEPARATOR: &str = ".";
const PATHS_SEPARATOR: &str = "/";
const VARIANT_SEPARATOR: &str = "/";
const VARIANT_FIELD_SEPARATOR: &str = "/";
const VARIANT_FIELD_INTERNAL_SEPARATOR: &str = "/?";
const FUN_TRAIT_DEF_BEGIN: &str = "<";
const FUN_TRAIT_DEF_END: &str = ">";
const MONOTYPE_APP_BEGIN: &str = "<";
const MONOTYPE_APP_END: &str = ">";
const DECREASE_AT_ENTRY: &str = "decrease%init";
const TRAIT_SELF_TYPE_PARAM: &str = "Self%";

pub const PREFIX_IMPL_TYPE_PARAM: &str = "impl%";
pub const SUFFIX_SNAP_MUT: &str = "_mutation";
pub const SUFFIX_SNAP_JOIN: &str = "_join";
pub const SUFFIX_SNAP_WHILE_BEGIN: &str = "_while_begin";
pub const SUFFIX_SNAP_WHILE_END: &str = "_while_end";

pub const CLOSURE_RETURN_VALUE_PREFIX: &str = "%closure_return";

// List of constant strings that can appear in generated AIR code
pub const FUEL_ID: &str = "FuelId";
pub const FUEL_TYPE: &str = "Fuel";
pub const ZERO: &str = "zero";
pub const SUCC: &str = "succ";
pub const FUEL_PARAM: &str = "fuel%";
pub const FUEL_LOCAL: &str = "fuel%@";
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
pub const U_INV: &str = "uInv";
pub const I_INV: &str = "iInv";
pub const ARCH_SIZE: &str = "SZ";
pub const MUL: &str = "Mul";
pub const EUC_DIV: &str = "EucDiv";
pub const EUC_MOD: &str = "EucMod";
pub const SNAPSHOT_CALL: &str = "CALL";
pub const SNAPSHOT_PRE: &str = "PRE";
pub const SNAPSHOT_ASSIGN: &str = "ASSIGN";
pub const POLY: &str = "Poly";
pub const BOX_INT: &str = "I";
pub const BOX_BOOL: &str = "B";
pub const BOX_STRSLICE: &str = "S";
pub const BOX_CHAR: &str = "C";
pub const UNBOX_INT: &str = "%I";
pub const UNBOX_BOOL: &str = "%B";
pub const UNBOX_STRSLICE: &str = "%S";
pub const UNBOX_CHAR: &str = "%C";
pub const TYPE: &str = "Type";
pub const TYPE_ID_BOOL: &str = "BOOL";
pub const TYPE_ID_INT: &str = "INT";
pub const TYPE_ID_STRSLICE: &str = "STRSLICE";
pub const TYPE_ID_CHAR: &str = "CHAR";
pub const TYPE_ID_NAT: &str = "NAT";
pub const TYPE_ID_UINT: &str = "UINT";
pub const TYPE_ID_SINT: &str = "SINT";
pub const TYPE_ID_CONST_INT: &str = "CONST_INT";
pub const HAS_TYPE: &str = "has_type";
pub const AS_TYPE: &str = "as_type";
pub const MK_FUN: &str = "mk_fun";
pub const CONST_INT: &str = "const_int";
pub const DUMMY_PARAM: &str = "no%param";
const CHECK_DECREASE_INT: &str = "check_decrease_int";
const HEIGHT: &str = "height";
const CLOSURE_REQ: &str = "closure_req";
const CLOSURE_ENS: &str = "closure_ens";

pub const UINT_XOR: &str = "uintxor";
pub const UINT_AND: &str = "uintand";
pub const UINT_OR: &str = "uintor";
pub const UINT_SHR: &str = "uintshr";
pub const UINT_SHL: &str = "uintshl";
pub const UINT_NOT: &str = "uintnot";

// List of QID suffixes we add to internally generated quantifiers
pub const QID_BOX_AXIOM: &str = "box_axiom";
pub const QID_UNBOX_AXIOM: &str = "unbox_axiom";
pub const QID_CONSTRUCTOR_INNER: &str = "constructor_inner";
pub const QID_CONSTRUCTOR: &str = "constructor";
pub const QID_APPLY: &str = "apply";
pub const QID_ACCESSOR: &str = "accessor";
pub const QID_INVARIANT: &str = "invariant";
pub const QID_HAS_TYPE_ALWAYS: &str = "has_type_always";

pub const STRSLICE: &str = "StrSlice";
pub const STRSLICE_IS_ASCII: &str = "strslice_is_ascii";
pub const STRSLICE_LEN: &str = "strslice_len";
pub const STRSLICE_GET_CHAR: &str = "strslice_get_char";
pub const STRSLICE_NEW_STRLIT: &str = "new_strlit";
// only used to prove that new_strlit is injective
pub const STRSLICE_FROM_STRLIT: &str = "from_strlit";

pub const CHAR: &str = "Char";
pub const CHAR_FROM_UNICODE: &str = "from_unicode";
pub const CHAR_TO_UNICODE: &str = "to_unicode";

pub const VERUSLIB: &str = "vstd";
pub const VERUSLIB_PREFIX: &str = "vstd::";
pub const PERVASIVE_PREFIX: &str = "pervasive::";

pub const RUST_DEF_CTOR: &str = "ctor%";

// List of pre-defined error messages
pub const ASSERTION_FAILURE: &str = "assertion failure";
pub const PRECONDITION_FAILURE: &str = "precondition not satisfied";
pub const POSTCONDITION_FAILURE: &str = "postcondition not satisfied";
pub const THIS_POST_FAILED: &str = "failed this postcondition";
pub const INV_FAIL_LOOP_END: &str = "invariant not satisfied at end of loop body";
pub const INV_FAIL_LOOP_FRONT: &str = "invariant not satisfied before loop";
pub const SPLIT_ASSERT_FAILURE: &str = "split assertion failure";
pub const SPLIT_PRE_FAILURE: &str = "split precondition failure";
pub const SPLIT_POST_FAILURE: &str = "split postcondition failure";

pub const PERVASIVE_ASSERT: &[&str] = &["pervasive", "assert"];

pub fn path_to_string(path: &Path) -> String {
    let s = vec_map(&path.segments, |s| s.to_string()).join(PATH_SEPARATOR) + SUFFIX_PATH;
    if let Some(krate) = &path.krate { krate.to_string() + KRATE_SEPARATOR + &s } else { s }
}

pub fn fun_to_string(fun: &Fun) -> String {
    let FunX { path, trait_path } = &(**fun);
    let s = path_to_string(path);
    if let Some(trait_path) = trait_path {
        s + FUN_TRAIT_DEF_BEGIN + &path_to_string(trait_path) + FUN_TRAIT_DEF_END
    } else {
        s
    }
}

pub fn check_decrease_int() -> Fun {
    Arc::new(FunX {
        path: Arc::new(PathX {
            krate: None,
            segments: Arc::new(vec![str_ident(CHECK_DECREASE_INT)]),
        }),
        trait_path: None,
    })
}

pub fn decrease_at_entry(n: usize) -> Ident {
    Arc::new(format!("{}{}", DECREASE_AT_ENTRY, n))
}

pub fn trait_self_type_param() -> Ident {
    Arc::new(TRAIT_SELF_TYPE_PARAM.to_string())
}

pub fn height() -> Fun {
    Arc::new(FunX {
        path: Arc::new(PathX { krate: None, segments: Arc::new(vec![str_ident(HEIGHT)]) }),
        trait_path: None,
    })
}

pub fn closure_req() -> Fun {
    Arc::new(FunX {
        path: Arc::new(PathX { krate: None, segments: Arc::new(vec![str_ident(CLOSURE_REQ)]) }),
        trait_path: None,
    })
}

pub fn closure_ens() -> Fun {
    Arc::new(FunX {
        path: Arc::new(PathX { krate: None, segments: Arc::new(vec![str_ident(CLOSURE_ENS)]) }),
        trait_path: None,
    })
}

pub fn suffix_global_id(ident: &Ident) -> Ident {
    Arc::new(ident.to_string() + SUFFIX_GLOBAL)
}

pub fn suffix_local_expr_id(ident: &Ident) -> Ident {
    Arc::new(ident.to_string() + SUFFIX_LOCAL_EXPR)
}

pub fn suffix_local_stmt_id(ident: &Ident) -> Ident {
    Arc::new(ident.to_string() + SUFFIX_LOCAL_STMT)
}

pub(crate) fn unique_bound(id: &Ident) -> UniqueIdent {
    UniqueIdent { name: id.clone(), local: None }
}

pub(crate) fn unique_local(id: &Ident) -> UniqueIdent {
    UniqueIdent { name: id.clone(), local: Some(0) }
}

pub fn suffix_local_unique_id(ident: &UniqueIdent) -> Ident {
    let UniqueIdent { name: x, local: id } = ident;
    match id {
        None => suffix_local_expr_id(x),
        Some(0) => suffix_local_stmt_id(x),
        Some(i) => {
            Arc::new(format!("{}{}{}{}", x.to_string(), SUFFIX_LOCAL_EXPR, i, SUFFIX_LOCAL_STMT))
        }
    }
}

pub fn rm_suffix_local_id(ident: &Ident) -> Ident {
    let mut name = ident.to_string();
    if name.ends_with(SUFFIX_LOCAL_STMT) {
        name = name[..name.len() - SUFFIX_LOCAL_STMT.len()].to_string();
    }
    match name.rfind(SUFFIX_LOCAL_EXPR) {
        None => {}
        Some(i) => {
            name = name[..i].to_string();
        }
    }
    Arc::new(name)
}

pub fn subst_rename_ident(x: &Ident, n: u64) -> Ident {
    Arc::new(format!("{}{}{}", x.to_string(), SUBST_RENAME_SEPARATOR, n))
}

pub fn suffix_typ_param_id(ident: &Ident) -> Ident {
    Arc::new(ident.to_string() + SUFFIX_TYPE_PARAM)
}

pub fn suffix_rename(ident: &Ident) -> Ident {
    Arc::new(ident.to_string() + SUFFIX_RENAME)
}

pub fn slice_type() -> Path {
    let ident = Arc::new(SLICE_TYPE.to_string());
    Arc::new(PathX { krate: None, segments: Arc::new(vec![ident]) })
}

pub fn slice_param() -> Ident {
    Arc::new(SLICE_PARAM.to_string())
}

pub fn prefix_type_id(path: &Path) -> Ident {
    Arc::new(PREFIX_TYPE_ID.to_string() + &path_to_string(path))
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

pub fn prefix_tuple_field(i: usize) -> Ident {
    Arc::new(format!("{}{}", PREFIX_TUPLE_FIELD, i))
}

pub fn prefix_lambda_type(i: usize) -> Path {
    let ident = Arc::new(format!("{}{}", PREFIX_LAMBDA_TYPE, i));
    Arc::new(PathX { krate: None, segments: Arc::new(vec![ident]) })
}

pub fn prefix_type_id_fun(i: usize) -> Ident {
    prefix_type_id(&prefix_lambda_type(i))
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

pub fn prefix_str(ident: &Ident) -> Ident {
    Arc::new(PREFIX_STR.to_string() + ident)
}

pub fn prefix_char(ident: &Ident) -> Ident {
    Arc::new(PREFIX_CHAR.to_string() + ident)
}

pub fn prefix_ensures(ident: &Ident) -> Ident {
    Arc::new(PREFIX_ENSURES.to_string() + ident)
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
    let FunX { path, trait_path } = &(**fun);
    let path = prefix_recursive(path);
    Arc::new(FunX { path, trait_path: trait_path.clone() })
}

pub fn prefix_temp_var(n: u64) -> Ident {
    Arc::new(PREFIX_TEMP_VAR.to_string() + &n.to_string())
}

pub fn is_temp_var(x: &Ident) -> bool {
    x.starts_with(PREFIX_TEMP_VAR)
}

// ast_simplify introduces its own temporary variables; we don't want these to conflict with prefix_temp_var
pub fn prefix_simplify_temp_var(n: u64) -> Ident {
    Arc::new(PREFIX_SIMPLIFY_TEMP_VAR.to_string() + &n.to_string())
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
    Arc::new(format!("_{}", idx))
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
pub fn new_internal_qid(name: String) -> Option<Ident> {
    // In SMTLIB, unquoted attribute values cannot contain colons,
    // and sise cannot handle quoting with vertical bars
    let name = str::replace(&name, ":", "_");
    let name = str::replace(&name, "%", "__");
    let qid = format!("{}{}_definition", air::profiler::INTERNAL_QUANT_PREFIX, name);
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

#[derive(Serialize, Deserialize)]
pub struct Spanned<X> {
    pub span: Span,
    pub x: X,
}

impl<X> Spanned<X> {
    pub fn new(span: Span, x: X) -> Arc<Spanned<X>> {
        Arc::new(Spanned { span: span, x: x })
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
    Spinoff,
    BitVector,
    Singular,
}

pub struct CommandsWithContextX {
    pub span: air::ast::Span,
    pub desc: String,
    pub commands: Commands,
    pub prover_choice: ProverChoice,
    pub skip_recommends: bool,
}

impl CommandsWithContextX {
    pub fn new(
        span: Span,
        desc: String,
        commands: Commands,
        prover_choice: ProverChoice,
        skip_recommends: bool,
    ) -> CommandsWithContext {
        Arc::new(CommandsWithContextX {
            span: span,
            desc: desc,
            commands: commands,
            prover_choice: prover_choice,
            skip_recommends: skip_recommends,
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

pub fn datatype_invariant_path(vstd_crate_name: &Option<Ident>, atomicity: InvAtomicity) -> Path {
    Arc::new(PathX {
        krate: vstd_crate_name.clone(),
        segments: Arc::new(if vstd_crate_name.is_some() {
            vec![Arc::new("invariant".to_string()), atomicity_type_name(atomicity)]
        } else {
            vec![
                Arc::new("pervasive".to_string()),
                Arc::new("invariant".to_string()),
                atomicity_type_name(atomicity),
            ]
        }),
    })
}

pub fn fn_inv_name(vstd_crate_name: &Option<Ident>, atomicity: InvAtomicity) -> Fun {
    Arc::new(FunX {
        path: Arc::new(PathX {
            krate: vstd_crate_name.clone(),
            segments: Arc::new(if vstd_crate_name.is_some() {
                vec![
                    Arc::new("invariant".to_string()),
                    atomicity_type_name(atomicity),
                    Arc::new("inv".to_string()),
                ]
            } else {
                vec![
                    Arc::new("pervasive".to_string()),
                    Arc::new("invariant".to_string()),
                    atomicity_type_name(atomicity),
                    Arc::new("inv".to_string()),
                ]
            }),
        }),
        trait_path: None,
    })
}

pub fn fn_namespace_name(vstd_crate_name: &Option<Ident>, atomicity: InvAtomicity) -> Fun {
    Arc::new(FunX {
        path: Arc::new(PathX {
            krate: vstd_crate_name.clone(),
            segments: Arc::new(if vstd_crate_name.is_some() {
                vec![
                    Arc::new("invariant".to_string()),
                    atomicity_type_name(atomicity),
                    Arc::new("namespace".to_string()),
                ]
            } else {
                vec![
                    Arc::new("pervasive".to_string()),
                    Arc::new("invariant".to_string()),
                    atomicity_type_name(atomicity),
                    Arc::new("namespace".to_string()),
                ]
            }),
        }),
        trait_path: None,
    })
}

// string related definitions
pub fn strslice() -> Node {
    str_to_node(STRSLICE)
}

pub fn strslice_is_ascii_ident() -> Ident {
    prefix_str(&std::sync::Arc::new(STRSLICE_IS_ASCII.to_string()))
}

pub fn strslice_len_ident() -> Ident {
    prefix_str(&std::sync::Arc::new(STRSLICE_LEN.to_string()))
}

pub fn strslice_get_char_ident() -> Ident {
    prefix_str(&std::sync::Arc::new(STRSLICE_GET_CHAR.to_string()))
}

pub fn strslice_new_strlit_ident() -> Ident {
    prefix_str(&std::sync::Arc::new(STRSLICE_NEW_STRLIT.to_string()))
}

pub fn strslice_is_ascii() -> Node {
    str_to_node(&strslice_is_ascii_ident())
}

pub fn strslice_len() -> Node {
    str_to_node(&strslice_len_ident())
}

pub fn strslice_get_char() -> Node {
    str_to_node(&strslice_get_char_ident())
}

pub fn strslice_new_strlit() -> Node {
    str_to_node(&strslice_new_strlit_ident())
}

pub fn strslice_from_strlit() -> Node {
    str_to_node(&prefix_str(&std::sync::Arc::new(STRSLICE_FROM_STRLIT.to_string())))
}

pub fn strslice_defn_path(vstd_crate_name: &Option<Ident>) -> Path {
    Arc::new(PathX {
        krate: vstd_crate_name.clone(),
        segments: Arc::new(if vstd_crate_name.is_some() {
            vec![Arc::new("string".to_string()), Arc::new(STRSLICE.to_string())]
        } else {
            vec![
                Arc::new("pervasive".to_string()),
                Arc::new("string".to_string()),
                Arc::new(STRSLICE.to_string()),
            ]
        }),
    })
}

pub fn pervasive_assert_path() -> Path {
    Arc::new(PathX {
        krate: None,
        segments: Arc::new(PERVASIVE_ASSERT.iter().map(|x| Arc::new(x.to_string())).collect()),
    })
}

// char related definitions
pub fn char_() -> Node {
    str_to_node(CHAR)
}

pub fn char_from_unicode_ident() -> Ident {
    prefix_char(&std::sync::Arc::new(CHAR_FROM_UNICODE.to_string()))
}

pub fn char_from_unicode() -> Node {
    str_to_node(&char_from_unicode_ident())
}

pub fn char_to_unicode_ident() -> Ident {
    prefix_char(&std::sync::Arc::new(CHAR_TO_UNICODE.to_string()))
}

pub fn char_to_unicode() -> Node {
    str_to_node(&char_to_unicode_ident())
}

/// Inverse of unique_local_name: extracts the user_given_name from
/// a unique name (e.g., given "a~2", returns "a"
pub fn user_local_name<'a>(s: &'a str) -> &'a str {
    match s.find(LOCAL_UNIQUE_ID_SEPARATOR) {
        None => s,
        Some(idx) => &s[0..idx],
    }
}

pub fn unique_local_name(user_given_name: String, uniq_id: usize) -> String {
    user_given_name + &LOCAL_UNIQUE_ID_SEPARATOR.to_string() + &uniq_id.to_string()
}

pub fn exec_nonstatic_call_fun(vstd_crate_name: &Option<Ident>) -> Fun {
    Arc::new(FunX { path: exec_nonstatic_call_path(vstd_crate_name), trait_path: None })
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
