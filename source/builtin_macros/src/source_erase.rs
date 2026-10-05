//! Source recording for the macro visitor. Erasure decisions stay in syntax.rs;
//! this module handles the cases where a snapshot needs to retain source syntax
//! instead of emitting the compiler's desugared representation.
use proc_macro2::{Span, TokenStream};
use quote::ToTokens;
use verus_syn::parse::Parser;
use verus_syn::spanned::Spanned;
use verus_syn::visit_mut::VisitMut;
use verus_syn::{Attribute, Expr, Macro, Meta, Signature, Stmt, Token};

use crate::syntax::{ImplItems, Items, Visitor};

#[derive(Default)]
pub(crate) struct SourceErasure {
    pub(crate) spans: Vec<Erasure>,
    pub(crate) error: Option<verus_syn::Error>,
    pub(crate) verus_depth: u32,
    pub(crate) expression_is_statement: bool,
    pub(crate) statement_macro_needs_semi: bool,
}

/// A source range selected by the macro rewriter for removal.
#[allow(dead_code)] // The fields are read by the ordinary library's callers.
pub struct Erasure {
    pub span: Span,
    pub kind: ErasureKind,
}

/// Wrappers permit removing otherwise empty lines immediately inside them.
#[allow(dead_code)] // Replacement text is read only by the ordinary library's callers.
pub enum ErasureKind {
    Node,
    /// A ghost expression used as a value must leave an executable unit block.
    Unit,
    WrapperOpen,
    WrapperClose,
    /// Small syntax repairs such as grouping parentheses or const delimiters.
    Replace(&'static str),
}

impl Erasure {
    pub(crate) fn node(span: Span) -> Self {
        Self { span, kind: ErasureKind::Node }
    }
}

// Shared with the attribute syntax's ExecReplacer.
pub(crate) fn is_proof_macro(path: &verus_syn::Path) -> bool {
    macro_name(path).is_some_and(|name| is_proof_macro_name(&name.to_string()))
}

// Without name resolution, only recognize bare canonical names and paths
// through the crates that export them. A foreign `some_crate::proof!` may
// contain executable code.
pub(crate) fn macro_name(path: &verus_syn::Path) -> Option<&verus_syn::Ident> {
    canonical_macro_name(path.segments.iter().map(|segment| &segment.ident))
}

fn macro_name_syn(path: &syn::Path) -> Option<&proc_macro2::Ident> {
    canonical_macro_name(path.segments.iter().map(|segment| &segment.ident))
}

fn canonical_macro_name<'a>(
    mut segments: impl ExactSizeIterator<Item = &'a proc_macro2::Ident>,
) -> Option<&'a proc_macro2::Ident> {
    let len = segments.len();
    let first = segments.next()?;
    if len == 1 {
        Some(first)
    } else if matches!(
        first.to_string().as_str(),
        "verus_builtin_macros" | "builtin_macros" | "vstd"
    ) {
        segments.last()
    } else {
        None
    }
}

pub(crate) fn is_item_wrapper(path: &verus_syn::Path) -> bool {
    macro_name(path).is_some_and(|name| is_item_wrapper_name(&name.to_string()))
}

pub(crate) fn is_proof_macro_name(name: &str) -> bool {
    matches!(name, "proof" | "proof_decl" | "proof_with")
}

pub(crate) fn is_item_wrapper_name(name: &str) -> bool {
    matches!(
        name,
        "verus" | "verus_keep_ghost" | "verus_erase_ghost" | "verus_impl" | "verus_trait_impl"
    )
}

fn is_proof_derive(meta: &Meta) -> bool {
    macro_name(meta.path())
        .is_some_and(|name| matches!(name.to_string().as_str(), "Structural" | "StructuralEq"))
}

fn meta_entries(meta: &Meta) -> Option<verus_syn::punctuated::Punctuated<Meta, Token![,]>> {
    let Meta::List(list) = meta else { return None };
    verus_syn::punctuated::Punctuated::<Meta, Token![,]>::parse_terminated
        .parse2(list.tokens.clone())
        .ok()
}

fn is_proof_meta(meta: &Meta) -> bool {
    if is_verus_attribute(meta.path()) {
        return true;
    }
    let Some(entries) = meta_entries(meta) else { return false };
    if meta.path().is_ident("derive") {
        !entries.is_empty() && entries.iter().all(is_proof_derive)
    } else if meta.path().is_ident("cfg_attr") {
        entries.len() > 1 && entries.iter().skip(1).all(is_proof_meta)
    } else {
        false
    }
}

/// Rust's outer grammar keeps ordinary calls such as assert(a, b) distinct from
/// Verus assertions. Only recognized macro payloads enter the Verus visitor.
pub(crate) struct RustVisitor<'a> {
    pub(crate) visitor: &'a mut Visitor,
}

impl<'ast> syn::visit::Visit<'ast> for RustVisitor<'_> {
    fn visit_block(&mut self, block: &'ast syn::Block) {
        let previous = self.visitor.source_erasure.as_ref().unwrap().statement_macro_needs_semi;
        for (index, stmt) in block.stmts.iter().enumerate() {
            self.visitor.source_erasure.as_mut().unwrap().statement_macro_needs_semi = index + 1
                < block.stmts.len()
                && matches!(stmt, syn::Stmt::Macro(mac) if mac.semi_token.is_none());
            syn::visit::Visit::visit_stmt(self, stmt);
        }
        self.visitor.source_erasure.as_mut().unwrap().statement_macro_needs_semi = previous;
    }

    fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
        if crate::syntax::has_ghost_mode_syn(&item.attrs) {
            self.visitor.record_erasure(item);
        } else {
            syn::visit::visit_item_fn(self, item);
        }
    }

    fn visit_impl_item_fn(&mut self, item: &'ast syn::ImplItemFn) {
        if crate::syntax::has_ghost_mode_syn(&item.attrs) {
            self.visitor.record_erasure(item);
        } else {
            syn::visit::visit_impl_item_fn(self, item);
        }
    }

    fn visit_trait_item_fn(&mut self, item: &'ast syn::TraitItemFn) {
        if crate::syntax::has_ghost_mode_syn(&item.attrs) {
            self.visitor.record_erasure(item);
        } else {
            syn::visit::visit_trait_item_fn(self, item);
        }
    }

    fn visit_item_const(&mut self, item: &'ast syn::ItemConst) {
        if crate::syntax::has_ghost_mode_syn(&item.attrs) {
            self.visitor.record_erasure(item);
        } else {
            syn::visit::visit_item_const(self, item);
        }
    }

    fn visit_item_static(&mut self, item: &'ast syn::ItemStatic) {
        if crate::syntax::has_ghost_mode_syn(&item.attrs) {
            self.visitor.record_erasure(item);
        } else {
            syn::visit::visit_item_static(self, item);
        }
    }

    fn visit_impl_item_const(&mut self, item: &'ast syn::ImplItemConst) {
        if crate::syntax::has_ghost_mode_syn(&item.attrs) {
            self.visitor.record_erasure(item);
        } else {
            syn::visit::visit_impl_item_const(self, item);
        }
    }

    fn visit_trait_item_const(&mut self, item: &'ast syn::TraitItemConst) {
        if crate::syntax::has_ghost_mode_syn(&item.attrs) {
            self.visitor.record_erasure(item);
        } else {
            syn::visit::visit_trait_item_const(self, item);
        }
    }

    fn visit_attribute(&mut self, attr: &'ast syn::Attribute) {
        let parser = match attr.style {
            syn::AttrStyle::Outer => Attribute::parse_outer,
            syn::AttrStyle::Inner(_) => Attribute::parse_inner,
        };
        match parser.parse2(attr.to_token_stream()) {
            Ok(attrs) => {
                for mut attr in attrs {
                    self.visitor.visit_source_attribute(&mut attr);
                }
            }
            Err(error) => self.visitor.record_source_error(error),
        }
    }

    fn visit_macro(&mut self, mac: &'ast syn::Macro) {
        match verus_syn::parse2::<Macro>(mac.to_token_stream()) {
            Ok(mut mac) => self.visitor.visit_source_macro(&mut mac),
            Err(error) => self.visitor.record_source_error(error),
        }
    }

    fn visit_expr(&mut self, expr: &'ast syn::Expr) {
        if let syn::Expr::Block(block) = expr {
            if crate::syntax::has_ghost_mode_syn(&block.attrs) {
                self.visitor
                    .source_erasure
                    .as_mut()
                    .unwrap()
                    .spans
                    .push(Erasure { span: expr.span(), kind: ErasureKind::Unit });
                return;
            }
        }
        if let syn::Expr::Macro(mac) = expr {
            if macro_name_syn(&mac.mac.path)
                .is_some_and(|name| is_proof_macro_name(&name.to_string()))
            {
                self.visitor
                    .source_erasure
                    .as_mut()
                    .unwrap()
                    .spans
                    .push(Erasure { span: expr.span(), kind: ErasureKind::Unit });
                return;
            }
        }
        syn::visit::visit_expr(self, expr);
    }

    fn visit_local(&mut self, local: &'ast syn::Local) {
        if crate::syntax::has_ghost_mode_syn(&local.attrs) {
            self.visitor.record_erasure(local);
        } else {
            syn::visit::visit_local(self, local);
        }
    }

    fn visit_stmt(&mut self, stmt: &'ast syn::Stmt) {
        if let syn::Stmt::Expr(syn::Expr::Block(block), _) = stmt {
            if crate::syntax::has_ghost_mode_syn(&block.attrs) {
                self.visitor.record_erasure(stmt);
                return;
            }
        }
        let mac = match stmt {
            syn::Stmt::Macro(mac) => Some(&mac.mac),
            syn::Stmt::Expr(syn::Expr::Macro(mac), _) => Some(&mac.mac),
            _ => None,
        };
        if mac.is_some_and(|m| {
            macro_name_syn(&m.path).is_some_and(|name| is_proof_macro_name(&name.to_string()))
        }) {
            self.visitor.record_erasure(stmt);
            return;
        }
        if let syn::Stmt::Macro(mac) = stmt {
            if macro_name_syn(&mac.mac.path)
                .is_some_and(|name| is_item_wrapper_name(&name.to_string()))
            {
                self.visitor.record_erasure(&mac.semi_token);
            }
        }
        syn::visit::visit_stmt(self, stmt);
    }

    fn visit_item_macro(&mut self, mac: &'ast syn::ItemMacro) {
        let name = macro_name_syn(&mac.mac.path).map(ToString::to_string);
        if name.as_deref().is_some_and(is_proof_macro_name) {
            self.visitor.record_erasure(mac);
            return;
        }
        if name.as_deref().is_some_and(is_item_wrapper_name) {
            self.visitor.record_erasure(&mac.semi_token);
        }
        syn::visit::visit_item_macro(self, mac);
    }

    fn visit_impl_item_macro(&mut self, mac: &'ast syn::ImplItemMacro) {
        let name = macro_name_syn(&mac.mac.path).map(ToString::to_string);
        if name.as_deref().is_some_and(is_proof_macro_name) {
            self.visitor.record_erasure(mac);
            return;
        }
        if name.as_deref().is_some_and(is_item_wrapper_name) {
            self.visitor.record_erasure(&mac.semi_token);
        }
        syn::visit::visit_impl_item_macro(self, mac);
    }

    fn visit_trait_item_macro(&mut self, mac: &'ast syn::TraitItemMacro) {
        if macro_name_syn(&mac.mac.path).is_some_and(|name| is_proof_macro_name(&name.to_string()))
        {
            self.visitor.record_erasure(mac);
            return;
        }
        syn::visit::visit_trait_item_macro(self, mac);
    }
}

pub(crate) fn is_verus_attribute(path: &verus_syn::Path) -> bool {
    let Some(first) = path.segments.first() else { return false };
    let Some(last) = path.segments.last() else { return false };
    first.ident == "verus"
        || first.ident == "verifier"
        || (macro_name(path).is_some()
            && matches!(
                last.ident.to_string().as_str(),
                "verus_spec" | "verus_verify" | "trigger" | "auto" | "all_triggers" | "via_fn"
            ))
}

impl Visitor {
    pub(crate) fn record_source_error(&mut self, error: verus_syn::Error) {
        let source = self.source_erasure.as_mut().unwrap();
        if let Some(existing) = &mut source.error {
            existing.combine(error);
        } else {
            source.error = Some(error);
        }
    }

    /// Record before the ordinary erasure logic discards a node. Empty syntax
    /// has no source span and must not produce a deletion at call_site().
    pub(crate) fn record_erasure(&mut self, node: &impl ToTokens) -> bool {
        if let Some(source) = &mut self.source_erasure {
            let tokens = node.to_token_stream();
            if !tokens.is_empty() {
                source.spans.push(Erasure::node(tokens.span()));
            }
            true
        } else {
            false
        }
    }

    pub(crate) fn erase_source_expr(&mut self, expr: &mut Expr) -> bool {
        let Some(source) = &mut self.source_erasure else { return false };
        let mut span = expr.span();
        // The RevealHide token printer omits hide_token.
        if let Expr::RevealHide(reveal) = expr {
            if let Some(hide) = reveal.hide_token {
                span = hide.span.join(span).unwrap();
            }
        }
        source.spans.push(Erasure {
            span,
            kind: if source.expression_is_statement {
                ErasureKind::Node
            } else {
                ErasureKind::Unit
            },
        });
        *expr = Expr::Verbatim(TokenStream::new());
        true
    }

    pub(crate) fn record_fn_erasure(&mut self, node: &impl ToTokens, sig: &Signature) {
        self.record_erasure(node);
        // Signature's token printer omits broadcast.
        if let (Some(source), Some(broadcast)) = (&mut self.source_erasure, sig.broadcast) {
            source
                .spans
                .push(Erasure::node(broadcast.span.join(node.to_token_stream().span()).unwrap()));
        }
    }

    pub(crate) fn record_const_block(&mut self, block: &Option<Box<verus_syn::Block>>) {
        // The macro rewriter desugars a contracted const/static into
        // `= { ... };`. Removing only `ensures` would leave invalid syntax.
        if let Some(block) = block {
            let source = self.source_erasure.as_mut().unwrap();
            source.spans.push(Erasure {
                span: block.brace_token.span.open(),
                kind: ErasureKind::Replace("= {"),
            });
            source.spans.push(Erasure {
                span: block.brace_token.span.close(),
                kind: ErasureKind::Replace("};"),
            });
        }
    }

    pub(crate) fn visit_source_signature(&mut self, sig: &mut Signature) {
        self.record_erasure(&sig.mode);
        self.record_erasure(&sig.publish);
        self.record_erasure(&sig.broadcast);
        self.record_erasure(&sig.spec);
        if let Some(invariants) = &sig.spec.invariants {
            // SignatureInvariants's printer omits the optional trailing comma.
            self.record_erasure(&invariants.comma);
        }
        // SignatureSpec's printer omits with, which adds ghost inputs/outputs.
        if let Some(with) = &sig.spec.with {
            let mut tokens = with.with.to_token_stream();
            with.inputs.to_tokens(&mut tokens);
            if let Some((arrow, outputs)) = &with.outputs {
                arrow.to_tokens(&mut tokens);
                outputs.to_tokens(&mut tokens);
            }
            self.record_erasure(&tokens);
        }
        // Preserve named returns, parameters, and Ghost/Tracked types.
        // These snapshots describe exec source; they are not macro expansion.
        verus_syn::visit_mut::visit_generics_mut(self, &mut sig.generics);
        for arg in &mut sig.inputs {
            self.record_erasure(&arg.tracked);
            arg.tracked = None;
            self.visit_fn_arg_mut(arg);
        }
        if let verus_syn::ReturnType::Type(_, tracked, _, _) = &mut sig.output {
            self.record_erasure(tracked);
            *tracked = None;
        }
        self.visit_return_type_mut(&mut sig.output);
    }

    pub(crate) fn visit_source_attribute(&mut self, attr: &mut Attribute) {
        if is_proof_meta(&attr.meta) {
            self.record_erasure(attr);
            return;
        }
        self.visit_source_meta(&attr.meta);
    }

    fn visit_source_meta(&mut self, meta: &Meta) {
        // Retain ordinary cfg_attr entries even when proof attributes share
        // the same list, including mixed Rust/Structural derives.
        let derive = meta.path().is_ident("derive");
        if derive || meta.path().is_ident("cfg_attr") {
            if let Some(entries) = meta_entries(meta) {
                let start = if derive { 0 } else { 1 };
                let proof: Vec<bool> = entries
                    .iter()
                    .enumerate()
                    .map(|(i, m)| {
                        i >= start && if derive { is_proof_derive(m) } else { is_proof_meta(m) }
                    })
                    .collect();
                for (i, pair) in entries.pairs().enumerate().skip(start) {
                    if proof[i] {
                        self.record_erasure(pair.value());
                        if let Some(comma) = pair.punct() {
                            self.record_erasure(comma);
                        } else if let Some(comma) =
                            entries.pairs().nth(i - 1).and_then(|p| p.punct().copied())
                        {
                            self.record_erasure(&comma);
                        }
                    } else if !derive {
                        self.visit_source_meta(pair.value());
                    }
                }
            }
        }
    }

    pub(crate) fn visit_source_macro(&mut self, mac: &mut Macro) {
        let Some(name) = macro_name(&mac.path).map(ToString::to_string) else { return };
        if is_proof_macro(&mac.path) {
            self.record_erasure(mac);
            return;
        }
        let tokens = verus_syn::rejoin_tokens(mac.tokens.clone());
        let depth = self.source_erasure.as_ref().unwrap().verus_depth;
        // Only these macros introduce a Verus grammar context. In ordinary Rust
        // an identifier such as assert or assume may name an executable function.
        if !matches!(
            name.as_str(),
            "verus"
                | "verus_keep_ghost"
                | "verus_erase_ghost"
                | "verus_impl"
                | "verus_trait_impl"
                | "verus_exec_expr"
                | "verus_exec_expr_keep_ghost"
                | "verus_exec_expr_erase_ghost"
        ) {
            return;
        }
        self.source_erasure.as_mut().unwrap().verus_depth += 1;
        let needs_semi = self.source_erasure.as_ref().unwrap().statement_macro_needs_semi;
        self.source_erasure.as_mut().unwrap().statement_macro_needs_semi = false;
        let result = match name.as_str() {
            "verus" | "verus_keep_ghost" | "verus_erase_ghost" => {
                verus_syn::parse2::<Items>(tokens).map(|mut items| {
                    self.visit_items_prefilter(&mut items.items);
                    for item in &mut items.items {
                        self.visit_item_mut(item);
                    }
                })
            }
            "verus_impl" | "verus_trait_impl" => {
                verus_syn::parse2::<ImplItems>(tokens).map(|mut items| {
                    self.visit_impl_items_prefilter(&mut items.items, name == "verus_trait_impl");
                    for item in &mut items.items {
                        self.visit_impl_item_mut(item);
                    }
                })
            }
            "verus_exec_expr" | "verus_exec_expr_keep_ghost" | "verus_exec_expr_erase_ghost" => {
                verus_syn::parse2::<Expr>(tokens).map(|mut expr| self.visit_expr_mut(&mut expr))
            }
            _ => unreachable!(),
        };
        self.source_erasure.as_mut().unwrap().verus_depth = depth;
        self.source_erasure.as_mut().unwrap().statement_macro_needs_semi = needs_semi;
        if let Err(error) = result {
            self.record_source_error(error);
            return;
        }
        let span = mac.delimiter.span();
        let source = self.source_erasure.as_mut().unwrap();
        let expression = !is_item_wrapper_name(&name);
        source.spans.push(Erasure {
            span: mac.path.span().join(span.open()).unwrap(),
            kind: if expression { ErasureKind::Replace("(") } else { ErasureKind::WrapperOpen },
        });
        source.spans.push(Erasure {
            span: span.close(),
            kind: if expression {
                ErasureKind::Replace(if needs_semi { ");" } else { ")" })
            } else {
                ErasureKind::WrapperClose
            },
        });
    }

    pub(crate) fn record_source_stmt(&mut self, stmt: &Stmt) {
        if let Stmt::Expr(expr, semi) = stmt {
            // Ghost expression handlers have already recorded and emptied the
            // expression. Its statement terminator belongs to the proof too.
            if matches!(expr, Expr::Verbatim(tokens) if tokens.is_empty()) {
                self.record_erasure(semi);
            }
        }
    }
}
