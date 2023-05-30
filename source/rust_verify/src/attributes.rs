use crate::util::{err_span, vir_err_span_str};
use rustc_ast::ast::AttrArgs;
use rustc_ast::token::{Token, TokenKind};
use rustc_ast::tokenstream::{TokenStream, TokenTree};
use rustc_ast::{AttrKind, Attribute};
use rustc_span::Span;
use vir::ast::{AcceptRecursiveType, Mode, TriggerAnnotation, VirErr};

#[derive(Debug)]
pub(crate) enum AttrTree {
    Fun(Span, String, Option<Box<[AttrTree]>>),
    //Eq(Span, String, String), // TODO(main_new)
}

pub(crate) fn token_to_string(token: &Token) -> Result<Option<String>, ()> {
    match token.kind {
        TokenKind::Literal(lit) => Ok(Some(lit.symbol.as_str().to_string())),
        TokenKind::Ident(symbol, _) => Ok(Some(symbol.as_str().to_string())),
        TokenKind::Comma => Ok(None),
        _ => Err(()),
    }
}

pub(crate) fn token_stream_to_trees(
    span: Span,
    stream: &TokenStream,
) -> Result<Box<[AttrTree]>, ()> {
    let mut token_trees: Vec<&TokenTree> = Vec::new();
    for x in stream.trees() {
        token_trees.push(x);
    }
    let mut i = 0;
    let mut trees: Vec<AttrTree> = Vec::new();
    while i < token_trees.len() {
        match &token_trees[i] {
            TokenTree::Token(token, _spacing) => {
                if let Some(name) = token_to_string(token)? {
                    let fargs = if i + 1 < token_trees.len() {
                        if let TokenTree::Delimited(_, _, token_stream) = &token_trees[i + 1] {
                            i += 1;
                            Some(token_stream_to_trees(span, token_stream)?)
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    trees.push(AttrTree::Fun(span, name, fargs));
                }
                i += 1;
            }
            _ => return Err(()),
        }
    }
    Ok(trees.into_boxed_slice())
}

// TODO(main_new) fn mac_args_to_tree(span: Span, name: String, args: &MacArgs) -> Result<AttrTree, ()> {
// TODO(main_new)     match args {
// TODO(main_new)         MacArgs::Empty => Ok(AttrTree::Fun(span, name, None)),
// TODO(main_new)         MacArgs::Delimited(_, _, token_stream) => {
// TODO(main_new)             Ok(AttrTree::Fun(span, name, Some(token_stream_to_trees(span, token_stream)?)))
// TODO(main_new)         }
// TODO(main_new)         MacArgs::Eq(_, token) => match token_to_string(token)? {
// TODO(main_new)             None => Err(()),
// TODO(main_new)             Some(token) => Ok(AttrTree::Eq(span, name, token)),
// TODO(main_new)         },
// TODO(main_new)     }
// TODO(main_new) }

fn attr_args_to_tree(span: Span, name: String, args: &AttrArgs) -> Result<AttrTree, ()> {
    match args {
        AttrArgs::Empty => Ok(AttrTree::Fun(span, name, None)),
        AttrArgs::Delimited(delim) => {
            Ok(AttrTree::Fun(span, name, Some(token_stream_to_trees(span, &delim.tokens)?)))
        }
        AttrArgs::Eq(_, rustc_ast::ast::AttrArgsEq::Ast(expr)) => {
            dbg!(&expr);
            // TODO(main_new) match token_to_string(expr.tokens)? {
            // TODO(main_new)     None => Err(()),
            // TODO(main_new)     Some(token) => Ok(AttrTree::Eq(span, name, token)),
            // TODO(main_new) },
            todo!()
        }
        AttrArgs::Eq(_, rustc_ast::ast::AttrArgsEq::Hir(lit)) => {
            dbg!(&lit);
            // TODO(main_new)
            todo!()
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum VerusPrefix {
    Internal,
    // Unsafe,
    // Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AttrPrefix {
    Verus(VerusPrefix),
    Verifier,
}

fn attr_to_tree(attr: &Attribute) -> Result<Option<(AttrPrefix, Span, AttrTree)>, VirErr> {
    match &attr.kind {
        AttrKind::Normal(item) => match &item.item.path.segments[..] {
            [segment] if segment.ident.as_str() == "verifier" => match &item.item.args {
                // TODO(main_new) MacArgs::Delimited(_, _, token_stream) => {
                // TODO(main_new)     let trees: Box<[AttrTree]> = token_stream_to_trees(attr.span, token_stream)
                // TODO(main_new)         .map_err(|_| vir_err_span_str(attr.span, "invalid verifier attribute"))?;
                // TODO(main_new)     if trees.len() != 1 {
                // TODO(main_new)         return err_span(attr.span, "invalid verifier attribute");
                // TODO(main_new)     }
                // TODO(main_new)     let mut trees = trees.into_vec().into_iter();
                // TODO(main_new)     let tree: AttrTree = trees
                // TODO(main_new)         .next()
                // TODO(main_new)         .ok_or(vir_err_span_str(attr.span, "invalid verifier attribute"))?;
                // TODO(main_new)     Ok(Some((AttrPrefix::Verifier, attr.span, tree)))
                // TODO(main_new) }
                _ => return err_span(attr.span, "invalid verifier attribute"),
            },
            [prefix_segment, segment] if prefix_segment.ident.as_str() == "verifier" => {
                attr_args_to_tree(attr.span, segment.ident.to_string(), &item.item.args)
                    .map(|tree| Some((AttrPrefix::Verifier, attr.span, tree)))
                    .map_err(|_| vir_err_span_str(attr.span, "invalid verifier attribute"))
            }
            [prefix_segment, segment] if prefix_segment.ident.as_str() == "verus" => {
                let name = segment.ident.to_string();
                let verus_prefix = match &*name {
                    "internal" => VerusPrefix::Internal,
                    _ => {
                        return err_span(attr.span, "invalid verus attribute");
                    }
                };
                match &item.item.args {
                    AttrArgs::Delimited(delim) => {
                        let trees: Box<[AttrTree]> =
                            token_stream_to_trees(attr.span, &delim.tokens).map_err(|_| {
                                vir_err_span_str(attr.span, "invalid verus attribute")
                            })?;
                        if trees.len() != 1 {
                            return err_span(attr.span, "invalid verus attribute");
                        }
                        let mut trees = trees.into_vec().into_iter();
                        let tree: AttrTree = trees
                            .next()
                            .ok_or(vir_err_span_str(attr.span, "invalid verus attribute"))?;
                        Ok(Some((AttrPrefix::Verus(verus_prefix), attr.span, tree)))
                    }
                    _ => return err_span(attr.span, "invalid verus attribute"),
                }
            }
            [segment]
                if segment.ident.as_str() == "spec"
                    || segment.ident.as_str() == "proof"
                    || segment.ident.as_str() == "exec" =>
            {
                return err_span(
                    attr.span,
                    "attributes spec, proof, exec are not supported anymore; use the verus! macro instead",
                );
            }
            _ => Ok(None),
        },
        _ => Ok(None),
    }
}

fn attrs_to_trees(attrs: &[Attribute]) -> Result<Vec<(AttrPrefix, Span, AttrTree)>, VirErr> {
    let mut attr_trees = Vec::new();
    for attr in attrs {
        if let Some(tree) = attr_to_tree(attr)? {
            attr_trees.push(tree);
        }
    }
    Ok(attr_trees)
}

#[derive(Debug)]
pub(crate) enum GetVariantField {
    Named(String),
    Unnamed(usize),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GhostBlockAttr {
    Proof,
    GhostWrapped,
    TrackedWrapped,
    Tracked,
    Wrapper,
}

#[derive(Debug)]
pub(crate) enum Attr {
    // specify mode (spec, proof, exec)
    Mode(Mode),
    // function return mode (spec, proof, exec)
    ReturnMode(Mode),
    // generated by verus! macro
    VerusMacro,
    // parse function to get header, but don't verify body
    ExternalBody,
    // don't parse function; function can't be called directly from verified code
    External,
    // hide body (from all modules) until revealed
    Opaque,
    // publish body
    Publish,
    // publish body with zero fuel
    OpaqueOutsideModule,
    // inline spec function in SMT query
    Inline,
    // Rust ghost block
    GhostBlock(GhostBlockAttr),
    // Header to unwrap Tracked<T> and Ghost<T> parameters
    UnwrapParameter,
    // type parameter is not necessarily used in strictly positive positions
    RejectRecursiveTypes(Option<String>),
    // type parameter is used in strictly positive positions
    RejectGroundRecursiveTypes(Option<String>),
    // type parameter is used in strictly positive positions
    // and is not used by the ground variant
    AcceptRecursiveTypes(Option<String>),
    // export function's require/ensure as global forall
    BroadcastForall,
    // accept the trigger chosen by triggers_auto without printing any diagnostics
    AutoTrigger,
    // exclude a particular function from being chosen in a trigger by triggers_auto
    NoAutoTrigger,
    // when used in a ghost context, redirect to a specified spec method
    Autospec(String),
    // add manual trigger to expression inside quantifier
    Trigger(Option<Vec<u64>>),
    // custom error string to report for precondition failures
    CustomReqErr(String),
    // Add custom error message for expanded diagnostics (split expressions)
    CustomErr(String),
    // verify using bitvector theory
    BitVector,
    // for 'atomic' operations (e.g., CAS)
    Atomic,
    // specifies an invariant block
    InvariantBlock,
    // an enum variant is_Variant
    IsVariant(String),
    // an enum variant get_Variant
    GetVariant(String, GetVariantField),
    // this proof function is a termination proof
    DecreasesBy,
    // in a spec function, check the body for violations of recommends
    CheckRecommends,
    // set smt.arith.nl=true
    NonLinear,
    // verify non linear arithmetic using Singular
    IntegerRing,
    // Use a new dedicated Z3 process just for this query
    SpinoffProver,
    // Memoize function call results during interpretation
    Memoize,
    // Suppress the recommends check for narrowing casts that may truncate
    Truncate,
}

fn get_trigger_arg(span: Span, attr_tree: &AttrTree) -> Result<u64, VirErr> {
    let i = match attr_tree {
        AttrTree::Fun(_, name, None) => match name.parse::<u64>() {
            Ok(i) => Some(i),
            _ => None,
        },
        _ => None,
    };
    match i {
        Some(i) => Ok(i),
        None => err_span(span, format!("expected integer constant, found {:?}", &attr_tree)),
    }
}

pub(crate) fn parse_attrs(attrs: &[Attribute]) -> Result<Vec<Attr>, VirErr> {
    let mut v: Vec<Attr> = Vec::new();
    for (prefix, span, attr) in attrs_to_trees(attrs)? {
        match prefix {
            AttrPrefix::Verifier => match &attr {
                AttrTree::Fun(_, name, None) if name == "spec" => v.push(Attr::Mode(Mode::Spec)),
                AttrTree::Fun(_, name, Some(box [AttrTree::Fun(_, arg, None)]))
                    if name == "spec" && arg == "checked" =>
                {
                    v.push(Attr::Mode(Mode::Spec));
                    v.push(Attr::CheckRecommends);
                }
                AttrTree::Fun(_, name, None) if name == "proof" => v.push(Attr::Mode(Mode::Proof)),
                AttrTree::Fun(_, name, None) if name == "exec" => v.push(Attr::Mode(Mode::Exec)),
                AttrTree::Fun(_, name, None) if name == "trigger" => v.push(Attr::Trigger(None)),
                AttrTree::Fun(span, name, Some(args)) if name == "trigger" => {
                    let mut groups: Vec<u64> = Vec::new();
                    for arg in args.iter() {
                        groups.push(get_trigger_arg(*span, arg)?);
                    }
                    if groups.len() == 0 {
                        return err_span(
                            *span,
                            "expected either #[trigger] or non-empty #[trigger(...)]",
                        );
                    }
                    v.push(Attr::Trigger(Some(groups)));
                }
                AttrTree::Fun(_, name, None) if name == "auto_trigger" => v.push(Attr::AutoTrigger),
                AttrTree::Fun(_, arg, None) if arg == "verus_macro" => v.push(Attr::VerusMacro),
                AttrTree::Fun(_, arg, None) if arg == "external_body" => v.push(Attr::ExternalBody),
                AttrTree::Fun(_, arg, None) if arg == "external" => v.push(Attr::External),
                AttrTree::Fun(_, arg, None) if arg == "opaque" => v.push(Attr::Opaque),
                AttrTree::Fun(_, arg, None) if arg == "publish" => v.push(Attr::Publish),
                AttrTree::Fun(_, arg, None) if arg == "opaque_outside_module" => {
                    v.push(Attr::OpaqueOutsideModule)
                }
                AttrTree::Fun(_, arg, None) if arg == "inline" => v.push(Attr::Inline),
                AttrTree::Fun(_, arg, None) if arg == "proof_block" => {
                    v.push(Attr::GhostBlock(GhostBlockAttr::Proof))
                }
                AttrTree::Fun(_, arg, None) if arg == "ghost_block_wrapped" => {
                    v.push(Attr::GhostBlock(GhostBlockAttr::GhostWrapped))
                }
                AttrTree::Fun(_, arg, None) if arg == "tracked_block_wrapped" => {
                    v.push(Attr::GhostBlock(GhostBlockAttr::TrackedWrapped))
                }
                AttrTree::Fun(_, arg, None) if arg == "tracked_block" => {
                    v.push(Attr::GhostBlock(GhostBlockAttr::Tracked))
                }
                AttrTree::Fun(_, arg, None) if arg == "ghost_wrapper" => {
                    v.push(Attr::GhostBlock(GhostBlockAttr::Wrapper))
                }
                // TODO: remove maybe_negative, strictly_positive
                AttrTree::Fun(_, arg, None)
                    if arg == "maybe_negative" || arg == "reject_recursive_types" =>
                {
                    v.push(Attr::RejectRecursiveTypes(None))
                }
                AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, ident, None)]))
                    if arg == "reject_recursive_types" =>
                {
                    v.push(Attr::RejectRecursiveTypes(Some(ident.clone())))
                }
                AttrTree::Fun(_, arg, None)
                    if arg == "reject_recursive_types_in_ground_variants" =>
                {
                    v.push(Attr::RejectGroundRecursiveTypes(None))
                }
                AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, ident, None)]))
                    if arg == "reject_recursive_types_in_ground_variants" =>
                {
                    v.push(Attr::RejectGroundRecursiveTypes(Some(ident.clone())))
                }
                AttrTree::Fun(_, arg, None)
                    if arg == "strictly_positive" || arg == "accept_recursive_types" =>
                {
                    v.push(Attr::AcceptRecursiveTypes(None))
                }
                AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, ident, None)]))
                    if arg == "accept_recursive_types" =>
                {
                    v.push(Attr::AcceptRecursiveTypes(Some(ident.clone())))
                }
                AttrTree::Fun(_, arg, None) if arg == "broadcast_forall" => {
                    v.push(Attr::BroadcastForall)
                }
                AttrTree::Fun(_, arg, None) if arg == "no_auto_trigger" => {
                    v.push(Attr::NoAutoTrigger)
                }
                AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, ident, None)]))
                    if arg == "when_used_as_spec" =>
                {
                    v.push(Attr::Autospec(ident.clone()))
                }
                AttrTree::Fun(_, arg, None) if arg == "atomic" => v.push(Attr::Atomic),
                AttrTree::Fun(_, arg, None) if arg == "invariant_block" => {
                    v.push(Attr::InvariantBlock)
                }
                AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, msg, None)]))
                    if arg == "custom_req_err" =>
                {
                    v.push(Attr::CustomReqErr(msg.clone()))
                }
                AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, msg, None)]))
                    if arg == "custom_err" =>
                {
                    v.push(Attr::CustomErr(msg.clone()))
                }
                AttrTree::Fun(_, arg, None) if arg == "bit_vector" => v.push(Attr::BitVector),
                AttrTree::Fun(_, arg, None) if arg == "decreases_by" || arg == "recommends_by" => {
                    v.push(Attr::DecreasesBy)
                }
                AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, name, None)]))
                    if arg == "returns" && name == "spec" =>
                {
                    v.push(Attr::ReturnMode(Mode::Spec))
                }
                AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, name, None)]))
                    if arg == "returns" && name == "proof" =>
                {
                    v.push(Attr::ReturnMode(Mode::Proof))
                }
                AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, name, None)]))
                    if arg == "returns" && name == "exec" =>
                {
                    v.push(Attr::ReturnMode(Mode::Exec))
                }
                AttrTree::Fun(_, arg, None) if arg == "integer_ring" => v.push(Attr::IntegerRing),
                AttrTree::Fun(_, arg, None) if arg == "nonlinear" => v.push(Attr::NonLinear),
                AttrTree::Fun(_, arg, None) if arg == "spinoff_prover" => {
                    v.push(Attr::SpinoffProver)
                }
                AttrTree::Fun(_, arg, None) if arg == "memoize" => v.push(Attr::Memoize),
                AttrTree::Fun(_, arg, None) if arg == "truncate" => v.push(Attr::Truncate),
                _ => return err_span(span, "unrecognized verifier attribute"),
            },
            AttrPrefix::Verus(verus_prefix) => match verus_prefix {
                VerusPrefix::Internal => match &attr {
                    AttrTree::Fun(_, name, None) if name == "spec" => {
                        v.push(Attr::Mode(Mode::Spec))
                    }
                    AttrTree::Fun(_, name, Some(box [AttrTree::Fun(_, arg, None)]))
                        if name == "spec" && arg == "checked" =>
                    {
                        v.push(Attr::Mode(Mode::Spec));
                        v.push(Attr::CheckRecommends);
                    }
                    AttrTree::Fun(_, name, None) if name == "proof" => {
                        v.push(Attr::Mode(Mode::Proof))
                    }
                    AttrTree::Fun(_, name, None) if name == "exec" => {
                        v.push(Attr::Mode(Mode::Exec))
                    }
                    AttrTree::Fun(_, name, None) if name == "trigger" => {
                        v.push(Attr::Trigger(None))
                    }
                    AttrTree::Fun(span, name, Some(args)) if name == "trigger" => {
                        let mut groups: Vec<u64> = Vec::new();
                        for arg in args.iter() {
                            groups.push(get_trigger_arg(*span, arg)?);
                        }
                        if groups.len() == 0 {
                            return err_span(
                                *span,
                                "expected either #[trigger] or non-empty #[trigger(...)]",
                            );
                        }
                        v.push(Attr::Trigger(Some(groups)));
                    }
                    AttrTree::Fun(_, name, None) if name == "auto_trigger" => {
                        v.push(Attr::AutoTrigger)
                    }
                    AttrTree::Fun(_, arg, None) if arg == "verus_macro" => v.push(Attr::VerusMacro),
                    AttrTree::Fun(_, arg, None) if arg == "external_body" => {
                        v.push(Attr::ExternalBody)
                    }
                    AttrTree::Fun(_, arg, None) if arg == "publish" => v.push(Attr::Publish),
                    AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, name, None)]))
                        if arg == "returns" && name == "spec" =>
                    {
                        v.push(Attr::ReturnMode(Mode::Spec))
                    }
                    AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, name, None)]))
                        if arg == "returns" && name == "proof" =>
                    {
                        v.push(Attr::ReturnMode(Mode::Proof))
                    }
                    AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, name, None)]))
                        if arg == "returns" && name == "exec" =>
                    {
                        v.push(Attr::ReturnMode(Mode::Exec))
                    }
                    AttrTree::Fun(_, arg, None) if arg == "header_unwrap_parameter" => {
                        v.push(Attr::UnwrapParameter)
                    }
                    AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, ident, None)]))
                        if arg == "prover" =>
                    {
                        match &**ident {
                            "nonlinear_arith" => v.push(Attr::NonLinear),
                            "bit_vector" => v.push(Attr::BitVector),
                            "integer_ring" => v.push(Attr::IntegerRing),
                            _ => return err_span(span, "invalid prover"),
                        }
                    }
                    AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, ident, None)]))
                        if arg == "is_variant" =>
                    {
                        v.push(Attr::IsVariant(ident.clone()))
                    }
                    AttrTree::Fun(
                        _,
                        arg,
                        Some(
                            box [
                                AttrTree::Fun(_, variant_ident, None),
                                AttrTree::Fun(_, field_ident, None),
                            ],
                        ),
                    ) if arg == "get_variant" => {
                        let field_ident = match field_ident.parse::<usize>().ok() {
                            Some(i) => GetVariantField::Unnamed(i),
                            None => GetVariantField::Named(field_ident.clone()),
                        };
                        v.push(Attr::GetVariant(variant_ident.clone(), field_ident))
                    }
                    AttrTree::Fun(_, arg, None) if arg == "via" => v.push(Attr::DecreasesBy),
                    _ => {
                        return err_span(span, "unrecognized internal attribute");
                    }
                },
            },
        }
    }
    Ok(v)
}

pub(crate) fn parse_attrs_opt(attrs: &[Attribute]) -> Vec<Attr> {
    match parse_attrs(attrs) {
        Ok(attrs) => attrs,
        Err(_) => vec![],
    }
}

pub(crate) fn get_ghost_block_opt(attrs: &[Attribute]) -> Option<GhostBlockAttr> {
    for attr in parse_attrs_opt(attrs) {
        match attr {
            Attr::GhostBlock(g) => return Some(g),
            _ => {}
        }
    }
    None
}

pub(crate) fn get_mode_opt(attrs: &[Attribute]) -> Option<Mode> {
    for attr in parse_attrs_opt(attrs) {
        match attr {
            Attr::Mode(m) => return Some(m),
            _ => {}
        }
    }
    None
}

pub(crate) fn get_mode(default_mode: Mode, attrs: &[Attribute]) -> Mode {
    get_mode_opt(attrs).unwrap_or(default_mode)
}

pub(crate) fn get_var_mode(function_mode: Mode, attrs: &[Attribute]) -> Mode {
    let default_mode = if function_mode == Mode::Proof { Mode::Spec } else { function_mode };
    get_mode(default_mode, attrs)
}

pub(crate) fn get_ret_mode(function_mode: Mode, attrs: &[Attribute]) -> Mode {
    let mut mode = get_var_mode(function_mode, &[]);
    for attr in parse_attrs_opt(attrs) {
        match attr {
            Attr::ReturnMode(m) => mode = m,
            _ => {}
        }
    }
    mode
}

pub(crate) fn get_trigger(attrs: &[Attribute]) -> Result<Vec<TriggerAnnotation>, VirErr> {
    let mut groups: Vec<TriggerAnnotation> = Vec::new();
    for attr in parse_attrs(attrs)? {
        match attr {
            Attr::AutoTrigger => groups.push(TriggerAnnotation::AutoTrigger),
            Attr::Trigger(None) => groups.push(TriggerAnnotation::Trigger(None)),
            Attr::Trigger(Some(group_ids)) => {
                groups.extend(group_ids.into_iter().map(|id| TriggerAnnotation::Trigger(Some(id))));
            }
            _ => {}
        }
    }
    Ok(groups)
}

pub(crate) fn get_custom_err_annotations(attrs: &[Attribute]) -> Result<Vec<String>, VirErr> {
    let mut v = Vec::new();
    for attr in parse_attrs(attrs)? {
        match attr {
            Attr::CustomErr(s) => v.push(s),
            _ => {}
        }
    }
    Ok(v)
}

pub(crate) fn get_fuel(vattrs: &VerifierAttrs) -> u32 {
    if vattrs.opaque { 0 } else { 1 }
}

pub(crate) fn get_publish(vattrs: &VerifierAttrs) -> Option<bool> {
    match (vattrs.publish, vattrs.opaque_outside_module) {
        (false, _) => None,
        (true, false) => Some(true),
        (true, true) => Some(false),
    }
}

#[derive(Debug)]
pub(crate) struct VerifierAttrs {
    pub(crate) verus_macro: bool,
    pub(crate) external_body: bool,
    pub(crate) external: bool,
    pub(crate) opaque: bool,
    pub(crate) publish: bool,
    pub(crate) opaque_outside_module: bool,
    pub(crate) inline: bool,
    // TODO: get rid of *_recursive_types: bool
    pub(crate) reject_recursive_types_in_ground_variants: bool,
    pub(crate) reject_recursive_types: bool,
    pub(crate) accept_recursive_types: bool,
    pub(crate) accept_recursive_type_list: Vec<(String, AcceptRecursiveType)>,
    pub(crate) broadcast_forall: bool,
    pub(crate) no_auto_trigger: bool,
    pub(crate) autospec: Option<String>,
    pub(crate) custom_req_err: Option<String>,
    pub(crate) bit_vector: bool,
    pub(crate) atomic: bool,
    pub(crate) integer_ring: bool,
    pub(crate) is_variant: Option<String>,
    pub(crate) get_variant: Option<(String, GetVariantField)>,
    pub(crate) decreases_by: bool,
    pub(crate) check_recommends: bool,
    pub(crate) nonlinear: bool,
    pub(crate) spinoff_prover: bool,
    pub(crate) memoize: bool,
    pub(crate) truncate: bool,
}

pub(crate) fn get_verifier_attrs(attrs: &[Attribute]) -> Result<VerifierAttrs, VirErr> {
    let mut vs = VerifierAttrs {
        verus_macro: false,
        external_body: false,
        external: false,
        opaque: false,
        publish: false,
        opaque_outside_module: false,
        inline: false,
        reject_recursive_types: false,
        reject_recursive_types_in_ground_variants: false,
        accept_recursive_types: false,
        accept_recursive_type_list: vec![],
        broadcast_forall: false,
        no_auto_trigger: false,
        autospec: None,
        custom_req_err: None,
        bit_vector: false,
        atomic: false,
        integer_ring: false,
        is_variant: None,
        get_variant: None,
        decreases_by: false,
        check_recommends: false,
        nonlinear: false,
        spinoff_prover: false,
        memoize: false,
        truncate: false,
    };
    for attr in parse_attrs(attrs)? {
        match attr {
            Attr::VerusMacro => vs.verus_macro = true,
            Attr::ExternalBody => vs.external_body = true,
            Attr::External => vs.external = true,
            Attr::Opaque => vs.opaque = true,
            Attr::Publish => vs.publish = true,
            Attr::OpaqueOutsideModule => vs.opaque_outside_module = true,
            Attr::Inline => vs.inline = true,
            Attr::RejectRecursiveTypes(None) => vs.reject_recursive_types = true,
            Attr::RejectRecursiveTypes(Some(s)) => {
                vs.accept_recursive_type_list.push((s, AcceptRecursiveType::Reject))
            }
            Attr::RejectGroundRecursiveTypes(None) => {
                vs.reject_recursive_types_in_ground_variants = true
            }
            Attr::RejectGroundRecursiveTypes(Some(s)) => {
                vs.accept_recursive_type_list.push((s, AcceptRecursiveType::RejectInGround))
            }
            Attr::AcceptRecursiveTypes(None) => vs.accept_recursive_types = true,
            Attr::AcceptRecursiveTypes(Some(s)) => {
                vs.accept_recursive_type_list.push((s, AcceptRecursiveType::Accept))
            }
            Attr::BroadcastForall => vs.broadcast_forall = true,
            Attr::NoAutoTrigger => vs.no_auto_trigger = true,
            Attr::Autospec(method_ident) => vs.autospec = Some(method_ident),
            Attr::CustomReqErr(s) => vs.custom_req_err = Some(s.clone()),
            Attr::BitVector => vs.bit_vector = true,
            Attr::Atomic => vs.atomic = true,
            Attr::IntegerRing => vs.integer_ring = true,
            Attr::IsVariant(variant_ident) => vs.is_variant = Some(variant_ident),
            Attr::GetVariant(variant_ident, field_ident) => {
                vs.get_variant = Some((variant_ident, field_ident))
            }
            Attr::DecreasesBy => vs.decreases_by = true,
            Attr::CheckRecommends => vs.check_recommends = true,
            Attr::NonLinear => vs.nonlinear = true,
            Attr::SpinoffProver => vs.spinoff_prover = true,
            Attr::Memoize => vs.memoize = true,
            Attr::Truncate => vs.truncate = true,
            _ => {}
        }
    }
    Ok(vs)
}
