use crate::rust_to_vir_base::ident_to_var;
use crate::util::{err_span_str, err_span_string};
use rustc_ast::token::{Token, TokenKind};
use rustc_ast::tokenstream::{TokenStream, TokenTree};
use rustc_ast::{AttrKind, Attribute, MacArgs};
use rustc_span::Span;
use vir::ast::{Mode, VirErr};

#[derive(Debug)]
pub(crate) enum AttrTree {
    Fun(Span, String, Option<Box<[AttrTree]>>),
    Eq(Span, String, String),
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
    let mut token_trees: Vec<TokenTree> = Vec::new();
    for x in stream.trees() {
        token_trees.push(x);
    }
    let mut i = 0;
    let mut trees: Vec<AttrTree> = Vec::new();
    while i < token_trees.len() {
        match &token_trees[i] {
            TokenTree::Token(token) => {
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

pub(crate) fn mac_args_to_tree(span: Span, name: String, args: &MacArgs) -> Result<AttrTree, ()> {
    match args {
        MacArgs::Empty => Ok(AttrTree::Fun(span, name, None)),
        MacArgs::Delimited(_, _, token_stream) => {
            Ok(AttrTree::Fun(span, name, Some(token_stream_to_trees(span, token_stream)?)))
        }
        MacArgs::Eq(_, token) => match token_to_string(token)? {
            None => Err(()),
            Some(token) => Ok(AttrTree::Eq(span, name, token)),
        },
    }
}

pub(crate) fn attr_to_tree(attr: &Attribute) -> Result<AttrTree, ()> {
    match &attr.kind {
        AttrKind::Normal(item, _) => match &item.path.segments[..] {
            [segment] => {
                let name = ident_to_var(&segment.ident).as_str().to_string();
                mac_args_to_tree(attr.span, name, &item.args)
            }
            _ => Err(()),
        },
        _ => Err(()),
    }
}

pub(crate) fn attrs_to_trees(attrs: &[Attribute]) -> Vec<AttrTree> {
    let mut attr_trees: Vec<AttrTree> = Vec::new();
    for attr in attrs {
        if let Ok(tree) = attr_to_tree(attr) {
            attr_trees.push(tree);
        }
    }
    attr_trees
}

pub(crate) enum Attr {
    // specify mode (spec, proof, exec)
    Mode(Mode),
    // function return mode (spec, proof, exec)
    ReturnMode(Mode),
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
    // type parameter is not necessarily used in strictly positive positions
    MaybeNegative,
    // type parameter is used in strictly positive positions
    StrictlyPositive,
    // export function's require/ensure as global forall
    BroadcastForall,
    // when used in a spec context, promote to spec by inserting .view()
    Autoview,
    // add manual trigger to expression inside quantifier
    Trigger(Option<Vec<u64>>),
    // custom error string to report for precondition failures
    CustomReqErr(String),
    // verify using bitvector theory
    BitVector,
    // for unforgeable token types
    Unforgeable,
    // for 'atomic' operations (e.g., CAS)
    Atomic,
    // specifies an invariant block
    InvariantBlock,
    // an enum variant is_Variant
    IsVariant,
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
        None => err_span_string(span, format!("expected integer constant, found {:?}", &attr_tree)),
    }
}

pub(crate) fn parse_attrs(attrs: &[Attribute]) -> Result<Vec<Attr>, VirErr> {
    let mut v: Vec<Attr> = Vec::new();
    for attr in attrs_to_trees(attrs) {
        match attr {
            AttrTree::Fun(_, name, None) if name == "spec" => v.push(Attr::Mode(Mode::Spec)),
            AttrTree::Fun(_, name, None) if name == "proof" => v.push(Attr::Mode(Mode::Proof)),
            AttrTree::Fun(_, name, None) if name == "exec" => v.push(Attr::Mode(Mode::Exec)),
            AttrTree::Fun(_, name, None) if name == "trigger" => v.push(Attr::Trigger(None)),
            AttrTree::Fun(span, name, Some(args)) if name == "trigger" => {
                let mut groups: Vec<u64> = Vec::new();
                for arg in args.iter() {
                    groups.push(get_trigger_arg(span, arg)?);
                }
                if groups.len() == 0 {
                    return err_span_str(
                        span,
                        "expected either #[trigger] or non-empty #[trigger(...)]",
                    );
                }
                v.push(Attr::Trigger(Some(groups)));
            }
            AttrTree::Fun(span, name, args) if name == "verifier" => match &args {
                Some(box [AttrTree::Fun(_, arg, None)]) if arg == "external_body" => {
                    v.push(Attr::ExternalBody)
                }
                Some(box [AttrTree::Fun(_, arg, None)]) if arg == "external" => {
                    v.push(Attr::External)
                }
                Some(box [AttrTree::Fun(_, arg, None)]) if arg == "opaque" => v.push(Attr::Opaque),
                Some(box [AttrTree::Fun(_, arg, None)]) if arg == "publish" => {
                    v.push(Attr::Publish)
                }
                Some(box [AttrTree::Fun(_, arg, None)]) if arg == "opaque_outside_module" => {
                    v.push(Attr::OpaqueOutsideModule)
                }
                Some(box [AttrTree::Fun(_, arg, None)]) if arg == "maybe_negative" => {
                    v.push(Attr::MaybeNegative)
                }
                Some(box [AttrTree::Fun(_, arg, None)]) if arg == "strictly_positive" => {
                    v.push(Attr::StrictlyPositive)
                }
                Some(box [AttrTree::Fun(_, arg, None)]) if arg == "broadcast_forall" => {
                    v.push(Attr::BroadcastForall)
                }
                Some(box [AttrTree::Fun(_, arg, None)]) if arg == "autoview" => {
                    v.push(Attr::Autoview)
                }
                Some(box [AttrTree::Fun(_, arg, None)]) if arg == "unforgeable" => {
                    v.push(Attr::Unforgeable)
                }
                Some(box [AttrTree::Fun(_, arg, None)]) if arg == "atomic" => v.push(Attr::Atomic),
                Some(box [AttrTree::Fun(_, arg, None)]) if arg == "invariant_block" => {
                    v.push(Attr::InvariantBlock)
                }
                Some(box [AttrTree::Fun(_, arg, None)]) if arg == "is_variant" => {
                    v.push(Attr::IsVariant)
                }
                Some(box [AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, msg, None)]))])
                    if arg == "custom_req_err" =>
                {
                    v.push(Attr::CustomReqErr(msg.clone()))
                }
                Some(box [AttrTree::Fun(_, arg, None)]) if arg == "bit_vector" => {
                    v.push(Attr::BitVector)
                }
                Some(box [AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, name, None)]))])
                    if arg == "returns" && name == "spec" =>
                {
                    v.push(Attr::ReturnMode(Mode::Spec))
                }
                Some(box [AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, name, None)]))])
                    if arg == "returns" && name == "proof" =>
                {
                    v.push(Attr::ReturnMode(Mode::Proof))
                }
                Some(box [AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, name, None)]))])
                    if arg == "returns" && name == "exec" =>
                {
                    v.push(Attr::ReturnMode(Mode::Exec))
                }
                _ => return err_span_str(span, "unrecognized verifier attribute"),
            },
            _ => {}
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

pub(crate) fn get_mode(default_mode: Mode, attrs: &[Attribute]) -> Mode {
    let mut mode = default_mode;
    for attr in parse_attrs_opt(attrs) {
        match attr {
            Attr::Mode(m) => mode = m,
            _ => {}
        }
    }
    mode
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

pub(crate) fn get_trigger(attrs: &[Attribute]) -> Result<Vec<Option<u64>>, VirErr> {
    let mut groups: Vec<Option<u64>> = Vec::new();
    for attr in parse_attrs(attrs)? {
        match attr {
            Attr::Trigger(None) => groups.push(None),
            Attr::Trigger(Some(group_ids)) => {
                groups.extend(group_ids.into_iter().map(|id| Some(id)));
            }
            _ => {}
        }
    }
    Ok(groups)
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

pub(crate) struct VerifierAttrs {
    pub(crate) external_body: bool,
    pub(crate) external: bool,
    pub(crate) opaque: bool,
    pub(crate) publish: bool,
    pub(crate) opaque_outside_module: bool,
    pub(crate) strictly_positive: bool,
    pub(crate) maybe_negative: bool,
    pub(crate) broadcast_forall: bool,
    pub(crate) autoview: bool,
    pub(crate) custom_req_err: Option<String>,
    pub(crate) bit_vector: bool,
    pub(crate) unforgeable: bool,
    pub(crate) atomic: bool,
    pub(crate) is_variant: bool,
}

pub(crate) fn get_verifier_attrs(attrs: &[Attribute]) -> Result<VerifierAttrs, VirErr> {
    let mut vs = VerifierAttrs {
        external_body: false,
        external: false,
        opaque: false,
        publish: false,
        opaque_outside_module: false,
        maybe_negative: false,
        strictly_positive: false,
        broadcast_forall: false,
        autoview: false,
        custom_req_err: None,
        bit_vector: false,
        unforgeable: false,
        atomic: false,
        is_variant: false,
    };
    for attr in parse_attrs(attrs)? {
        match attr {
            Attr::ExternalBody => vs.external_body = true,
            Attr::External => vs.external = true,
            Attr::Opaque => vs.opaque = true,
            Attr::Publish => vs.publish = true,
            Attr::OpaqueOutsideModule => vs.opaque_outside_module = true,
            Attr::MaybeNegative => vs.maybe_negative = true,
            Attr::StrictlyPositive => vs.strictly_positive = true,
            Attr::BroadcastForall => vs.broadcast_forall = true,
            Attr::Autoview => vs.autoview = true,
            Attr::CustomReqErr(s) => vs.custom_req_err = Some(s.clone()),
            Attr::BitVector => vs.bit_vector = true,
            Attr::Unforgeable => vs.unforgeable = true,
            Attr::Atomic => vs.atomic = true,
            Attr::IsVariant => vs.is_variant = true,
            _ => {}
        }
    }
    Ok(vs)
}
