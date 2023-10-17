use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    ops::RangeInclusive,
};

use serde::Serialize;
use syn_verus::{spanned::Spanned, visit::Visit, Attribute, File, Meta, Signature};
use tabled::settings::{
    object::{Columns, Rows},
    Alignment, Modify, Style,
};

struct Config {
    print_all: bool,
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let program = args[0].clone();

    let mut opts = getopts::Options::new();
    opts.optflag("h", "help", "print this help menu");
    opts.optflag("p", "print-all", "print all the annotated files");

    let matches = match opts.parse(&args[1..]) {
        Ok(m) => m,
        Err(f) => {
            panic!("{}", f.to_string())
        }
    };

    fn print_usage(program: &str, opts: getopts::Options) {
        let brief = format!("Usage: {} DEPS_FILE.d [options]", program);
        print!("{}", opts.usage(&brief));
    }

    if matches.opt_present("h") {
        print_usage(&program, opts);
        return;
    }

    let deps_path = if !matches.free.is_empty() {
        matches.free[0].clone()
    } else {
        print_usage(&program, opts);
        return;
    };

    let config = Config { print_all: matches.opt_present("p") };

    match run(&config, &std::path::Path::new(&deps_path)) {
        Ok(()) => (),
        Err(err) => {
            eprintln!("error: {}", err);
            std::process::exit(1);
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, PartialOrd, Ord)]
enum CodeKind {
    Trusted,
    Spec,
    Proof,
    Exec,
    Directives,
    Definitions,
    Comment,
    Layout,
}

trait ToCodeKind {
    fn to_code_kind(&self) -> CodeKind;
}

impl ToCodeKind for syn_verus::DataMode {
    fn to_code_kind(&self) -> CodeKind {
        match self {
            syn_verus::DataMode::Ghost(_) => CodeKind::Spec,
            syn_verus::DataMode::Tracked(_) => CodeKind::Proof,
            syn_verus::DataMode::Exec(_) => CodeKind::Exec,
            syn_verus::DataMode::Default => CodeKind::Exec,
        }
    }
}

impl ToCodeKind for syn_verus::FnMode {
    fn to_code_kind(&self) -> CodeKind {
        match self {
            syn_verus::FnMode::Spec(_) | syn_verus::FnMode::SpecChecked(_) => CodeKind::Spec,
            syn_verus::FnMode::Proof(_) => CodeKind::Proof,
            syn_verus::FnMode::Exec(_) | syn_verus::FnMode::Default => CodeKind::Exec,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum LineContent {
    Const(CodeKind),
    Code(CodeKind),
    DatatypeDecl,
    TypeDefinition,
    Trait,
    ProofBlock,
    ProofDirective, // Assert, Assume, Reveal, ...
    ProofBinding,
    Impl,
    Signature(CodeKind),
    FunctionSpec,
    Body(CodeKind),
    Directive,
    MacroDefinition,
    GhostTracked(CodeKind),
    Comment,
}

struct LineInfo {
    kinds: HashSet<CodeKind>,
    #[allow(dead_code)]
    path: Vec<String>,
    line_content: HashSet<LineContent>,
    text: String,
}

struct FileStats {
    lines: Box<[LineInfo]>,
}

fn to_lines_range(spanned: &impl Spanned) -> RangeInclusive<usize> {
    let span = spanned.span();
    let proc_macro2::LineColumn { line: start_line, column: _ } = span.start();
    let proc_macro2::LineColumn { line: end_line, column: _ } = span.end();
    (start_line - 1)..=(end_line - 1)
}

impl FileStats {
    #[allow(dead_code)]
    fn mark_kind(&mut self, spanned: &impl Spanned, kind: CodeKind) {
        for l in to_lines_range(spanned) {
            self.lines[l]
                .kinds
                .retain(|x| !matches!(x, CodeKind::Spec | CodeKind::Proof | CodeKind::Exec));
            self.lines[l].kinds.insert(kind);
        }
    }

    #[allow(dead_code)]
    fn mark_additional_kind(&mut self, spanned: &impl Spanned, kind: CodeKind) {
        for l in to_lines_range(spanned) {
            self.lines[l].kinds.insert(kind);
        }
    }

    fn mark_content(&mut self, spanned: &impl Spanned, content: LineContent) {
        for l in to_lines_range(spanned) {
            self.lines[l].line_content.insert(content);
        }
    }

    fn mark(&mut self, spanned: &(impl Spanned + Debug), kind: CodeKind, content: LineContent) {
        for l in to_lines_range(spanned) {
            self.lines[l]
                .kinds
                .retain(|x| !matches!(x, CodeKind::Spec | CodeKind::Proof | CodeKind::Exec));
            self.lines[l].kinds.insert(kind);
            self.lines[l].line_content.insert(content);
        }
    }

    fn mark_with_additional_kind(
        &mut self,
        spanned: &impl Spanned,
        kind: CodeKind,
        content: LineContent,
    ) {
        for l in to_lines_range(spanned) {
            self.lines[l].kinds.insert(kind);
            self.lines[l].line_content.insert(content);
        }
    }
}

struct Visitor<'f> {
    file_stats: &'f mut FileStats,
    in_body: Option<CodeKind>,
    trusted: u64,
    in_proof_directive: u64,
}

impl<'ast, 'f> syn_verus::visit::Visit<'ast> for Visitor<'f> {
    fn visit_assert(&mut self, i: &'ast syn_verus::Assert) {
        self.in_proof_directive += 1;
        self.file_stats.mark(i, CodeKind::Proof, LineContent::ProofDirective);
        syn_verus::visit::visit_assert(self, i);
        self.in_proof_directive -= 1;
    }

    fn visit_assert_forall(&mut self, i: &'ast syn_verus::AssertForall) {
        self.in_proof_directive += 1;
        self.file_stats.mark(i, CodeKind::Proof, LineContent::ProofDirective);
        syn_verus::visit::visit_assert_forall(self, i);
        self.in_proof_directive -= 1;
    }

    fn visit_assume(&mut self, i: &'ast syn_verus::Assume) {
        self.in_proof_directive += 1;
        self.file_stats.mark(i, CodeKind::Proof, LineContent::ProofDirective);
        syn_verus::visit::visit_assume(self, i);
        self.in_proof_directive -= 1;
    }

    #[allow(unreachable_code)]
    fn visit_data(&mut self, _i: &'ast syn_verus::Data) {
        panic!("data unsupported");
        syn_verus::visit::visit_data(self, _i);
    }

    fn visit_decreases(&mut self, i: &'ast syn_verus::Decreases) {
        // self.file_stats.mark(i, self.mode_or_trusted(CodeKind::Spec), LineContent::FunctionSpec);
        syn_verus::visit::visit_decreases(self, i);
    }

    fn visit_ensures(&mut self, i: &'ast syn_verus::Ensures) {
        // self.file_stats.mark(i, self.mode_or_trusted(CodeKind::Spec), LineContent::FunctionSpec);
        syn_verus::visit::visit_ensures(self, i);
    }

    fn visit_expr(&mut self, i: &'ast syn_verus::Expr) {
        if !matches!(i, syn_verus::Expr::Block(_)) {
            if let Some(content_code_kind) = self.in_body {
                if self.in_proof_directive == 0 {
                    self.file_stats.mark(
                        &i,
                        self.mode_or_trusted(content_code_kind),
                        LineContent::Code(content_code_kind),
                    )
                }
            }
        }
        match i {
            syn_verus::Expr::Unary(syn_verus::ExprUnary {
                op: syn_verus::UnOp::Proof(..),
                attrs: _,
                expr,
            }) => {
                self.file_stats.mark(
                    expr,
                    self.mode_or_trusted(CodeKind::Proof),
                    LineContent::ProofBlock,
                );
            }
            _ => (),
        }
        syn_verus::visit::visit_expr(self, i);
    }

    fn visit_expr_block(&mut self, i: &'ast syn_verus::ExprBlock) {
        syn_verus::visit::visit_expr_block(self, i);
    }

    fn visit_expr_call(&mut self, i: &'ast syn_verus::ExprCall) {
        // Ghost / Tracked ?
        if let syn_verus::Expr::Path(path) = &*i.func {
            if let Some(wrapper_code_kind) = (path.path.segments.len() == 1)
                .then(|| path.path.segments[0].ident.to_string())
                .and_then(|c| match c.as_str() {
                    "Ghost" => {
                        if self.in_body == Some(CodeKind::Spec) {
                            Some(self.mode_or_trusted(CodeKind::Spec))
                        } else {
                            Some(self.mode_or_trusted(CodeKind::Proof))
                        }
                    }
                    "Tracked" => Some(self.mode_or_trusted(CodeKind::Proof)),
                    _ => None,
                })
            {
                self.file_stats.mark_with_additional_kind(
                    i,
                    wrapper_code_kind,
                    LineContent::GhostTracked(wrapper_code_kind),
                );
            }
        }
        syn_verus::visit::visit_expr_call(self, i);
    }

    fn visit_expr_closure(&mut self, i: &'ast syn_verus::ExprClosure) {
        // TODO
        syn_verus::visit::visit_expr_closure(self, i);
    }

    fn visit_expr_while(&mut self, i: &'ast syn_verus::ExprWhile) {
        if let Some(decreases) = &i.decreases {
            self.file_stats.mark(
                decreases,
                self.mode_or_trusted(CodeKind::Proof),
                LineContent::ProofDirective,
            );
        }
        if let Some(invariant) = &i.invariant {
            self.file_stats.mark(
                &invariant,
                self.mode_or_trusted(CodeKind::Proof),
                LineContent::ProofDirective,
            );
        }
        if let Some(invariant_ensures) = &i.invariant_ensures {
            self.file_stats.mark(
                &invariant_ensures,
                self.mode_or_trusted(CodeKind::Proof),
                LineContent::ProofDirective,
            );
        }
        if let Some(ensures) = &i.ensures {
            self.file_stats.mark(
                &ensures,
                self.mode_or_trusted(CodeKind::Proof),
                LineContent::ProofDirective,
            );
        }
        self.visit_expr(&i.cond);
        self.visit_block(&i.body);
    }

    fn visit_impl_item_method(&mut self, i: &'ast syn_verus::ImplItemMethod) {
        let content_code_kind = i.sig.mode.to_code_kind();
        let exit = self.item_attr_enter(&i.attrs);
        let code_kind = self.mode_or_trusted(content_code_kind);
        // self.file_stats.mark(&i.block, code_kind, LineContent::Code(content_code_kind));
        self.file_stats.mark_content(&i.block, LineContent::Body(content_code_kind));
        self.handle_signature(content_code_kind, code_kind, &i.sig);
        self.in_body = Some(content_code_kind);
        self.visit_block(&i.block);
        self.in_body = None;
        exit.exit(self);
    }

    fn visit_item(&mut self, i: &'ast syn_verus::Item) {
        match i {
            syn_verus::Item::Impl(_) => {
                self.file_stats.mark_content(i, LineContent::Impl);
            }
            _ => (),
        }
        syn_verus::visit::visit_item(self, i);
    }

    fn visit_item_const(&mut self, i: &'ast syn_verus::ItemConst) {
        let exit = self.item_attr_enter(&i.attrs);
        self.file_stats.mark(
            i,
            self.mode_or_trusted(i.mode.to_code_kind()),
            LineContent::Const(i.mode.to_code_kind()),
        );
        syn_verus::visit::visit_item_const(self, i);
        exit.exit(self);
    }

    fn visit_item_enum(&mut self, i: &'ast syn_verus::ItemEnum) {
        let exit = self.item_attr_enter(&i.attrs);
        self.file_stats.mark(
            &i,
            self.mode_or_trusted(i.mode.to_code_kind()),
            LineContent::DatatypeDecl,
        );
        syn_verus::visit::visit_item_enum(self, i);
        exit.exit(self);
    }

    fn visit_item_extern_crate(&mut self, i: &'ast syn_verus::ItemExternCrate) {
        let exit = self.item_attr_enter(&i.attrs);
        syn_verus::visit::visit_item_extern_crate(self, i);
        exit.exit(self);
    }

    fn visit_item_fn(&mut self, i: &'ast syn_verus::ItemFn) {
        let exit = self.item_attr_enter(&i.attrs);
        let content_code_kind = i.sig.mode.to_code_kind();
        let code_kind = self.mode_or_trusted(content_code_kind);
        // self.file_stats.mark(&i.block, code_kind, LineContent::Code(content_code_kind));
        self.file_stats.mark_content(&i.block, LineContent::Body(content_code_kind));
        self.handle_signature(content_code_kind, code_kind, &i.sig);
        self.in_body = Some(content_code_kind);
        self.visit_block(&i.block);
        self.in_body = None;
        exit.exit(self);
    }

    fn visit_item_foreign_mod(&mut self, i: &'ast syn_verus::ItemForeignMod) {
        let exit = self.item_attr_enter(&i.attrs);
        syn_verus::visit::visit_item_foreign_mod(self, i);
        exit.exit(self);
    }

    fn visit_item_impl(&mut self, i: &'ast syn_verus::ItemImpl) {
        let exit = self.item_attr_enter(&i.attrs);
        syn_verus::visit::visit_item_impl(self, i);
        exit.exit(self);
    }

    fn visit_item_macro(&mut self, i: &'ast syn_verus::ItemMacro) {
        syn_verus::visit::visit_item_macro(self, i);
    }

    fn visit_item_macro2(&mut self, i: &'ast syn_verus::ItemMacro2) {
        syn_verus::visit::visit_item_macro2(self, i);
    }

    fn visit_item_mod(&mut self, i: &'ast syn_verus::ItemMod) {
        let exit = self.item_attr_enter(&i.attrs);
        if i.content.is_none() {
            self.file_stats.mark(&i, CodeKind::Directives, LineContent::Directive);
        }
        syn_verus::visit::visit_item_mod(self, i);
        exit.exit(self);
    }

    fn visit_item_static(&mut self, i: &'ast syn_verus::ItemStatic) {
        let exit = self.item_attr_enter(&i.attrs);
        syn_verus::visit::visit_item_static(self, i);
        exit.exit(self);
    }

    fn visit_item_struct(&mut self, i: &'ast syn_verus::ItemStruct) {
        let exit = self.item_attr_enter(&i.attrs);
        self.file_stats.mark(
            &i,
            self.mode_or_trusted(i.mode.to_code_kind()),
            LineContent::DatatypeDecl,
        );
        syn_verus::visit::visit_item_struct(self, i);
        exit.exit(self);
    }

    fn visit_item_trait(&mut self, i: &'ast syn_verus::ItemTrait) {
        let exit = self.item_attr_enter(&i.attrs);
        self.file_stats.mark_content(&i, LineContent::Trait);
        if self.trusted > 0 {
            self.file_stats.mark_kind(&i, CodeKind::Trusted);
        }
        syn_verus::visit::visit_item_trait(self, i);
        exit.exit(self);
    }

    fn visit_item_trait_alias(&mut self, i: &'ast syn_verus::ItemTraitAlias) {
        let exit = self.item_attr_enter(&i.attrs);
        syn_verus::visit::visit_item_trait_alias(self, i);
        exit.exit(self);
    }

    fn visit_item_type(&mut self, i: &'ast syn_verus::ItemType) {
        let exit = self.item_attr_enter(&i.attrs);
        syn_verus::visit::visit_item_type(self, i);
        exit.exit(self);
    }

    fn visit_item_use(&mut self, i: &'ast syn_verus::ItemUse) {
        let exit = self.item_attr_enter(&i.attrs);
        syn_verus::visit::visit_item_use(self, i);
        exit.exit(self);
    }

    fn visit_label(&mut self, i: &'ast syn_verus::Label) {
        syn_verus::visit::visit_label(self, i);
    }

    fn visit_lifetime(&mut self, i: &'ast syn_verus::Lifetime) {
        syn_verus::visit::visit_lifetime(self, i);
    }

    fn visit_lifetime_def(&mut self, i: &'ast syn_verus::LifetimeDef) {
        syn_verus::visit::visit_lifetime_def(self, i);
    }

    fn visit_lit(&mut self, i: &'ast syn_verus::Lit) {
        syn_verus::visit::visit_lit(self, i);
    }

    fn visit_lit_bool(&mut self, i: &'ast syn_verus::LitBool) {
        syn_verus::visit::visit_lit_bool(self, i);
    }

    fn visit_lit_byte(&mut self, i: &'ast syn_verus::LitByte) {
        syn_verus::visit::visit_lit_byte(self, i);
    }

    fn visit_lit_byte_str(&mut self, i: &'ast syn_verus::LitByteStr) {
        syn_verus::visit::visit_lit_byte_str(self, i);
    }

    fn visit_lit_char(&mut self, i: &'ast syn_verus::LitChar) {
        syn_verus::visit::visit_lit_char(self, i);
    }

    fn visit_lit_float(&mut self, i: &'ast syn_verus::LitFloat) {
        syn_verus::visit::visit_lit_float(self, i);
    }

    fn visit_lit_int(&mut self, i: &'ast syn_verus::LitInt) {
        syn_verus::visit::visit_lit_int(self, i);
    }

    fn visit_lit_str(&mut self, i: &'ast syn_verus::LitStr) {
        syn_verus::visit::visit_lit_str(self, i);
    }

    fn visit_local(&mut self, i: &'ast syn_verus::Local) {
        if i.ghost.is_some() || i.tracked.is_some() {
            self.file_stats.mark(
                i,
                self.mode_or_trusted(CodeKind::Proof),
                LineContent::ProofBinding,
            );
        }
        syn_verus::visit::visit_local(self, i);
    }

    fn visit_macro(&mut self, i: &'ast syn_verus::Macro) {
        if i.path.segments.last().map(|s| s.ident.to_string()) == Some("macro_rules".into()) {
            self.file_stats.mark(i, CodeKind::Definitions, LineContent::MacroDefinition);
        }
        syn_verus::visit::visit_macro(self, i);
    }

    fn visit_macro_delimiter(&mut self, i: &'ast syn_verus::MacroDelimiter) {
        syn_verus::visit::visit_macro_delimiter(self, i);
    }

    fn visit_member(&mut self, i: &'ast syn_verus::Member) {
        syn_verus::visit::visit_member(self, i);
    }

    fn visit_meta(&mut self, i: &'ast syn_verus::Meta) {
        syn_verus::visit::visit_meta(self, i);
    }

    fn visit_meta_list(&mut self, i: &'ast syn_verus::MetaList) {
        syn_verus::visit::visit_meta_list(self, i);
    }

    fn visit_meta_name_value(&mut self, i: &'ast syn_verus::MetaNameValue) {
        syn_verus::visit::visit_meta_name_value(self, i);
    }

    fn visit_method_turbofish(&mut self, i: &'ast syn_verus::MethodTurbofish) {
        syn_verus::visit::visit_method_turbofish(self, i);
    }

    fn visit_mode(&mut self, i: &'ast syn_verus::Mode) {
        syn_verus::visit::visit_mode(self, i);
    }

    fn visit_mode_exec(&mut self, i: &'ast syn_verus::ModeExec) {
        syn_verus::visit::visit_mode_exec(self, i);
    }

    fn visit_mode_ghost(&mut self, i: &'ast syn_verus::ModeGhost) {
        syn_verus::visit::visit_mode_ghost(self, i);
    }

    fn visit_mode_proof(&mut self, i: &'ast syn_verus::ModeProof) {
        syn_verus::visit::visit_mode_proof(self, i);
    }

    fn visit_mode_spec(&mut self, i: &'ast syn_verus::ModeSpec) {
        syn_verus::visit::visit_mode_spec(self, i);
    }

    fn visit_mode_spec_checked(&mut self, i: &'ast syn_verus::ModeSpecChecked) {
        syn_verus::visit::visit_mode_spec_checked(self, i);
    }

    fn visit_mode_tracked(&mut self, i: &'ast syn_verus::ModeTracked) {
        syn_verus::visit::visit_mode_tracked(self, i);
    }

    fn visit_nested_meta(&mut self, i: &'ast syn_verus::NestedMeta) {
        syn_verus::visit::visit_nested_meta(self, i);
    }

    fn visit_open(&mut self, i: &'ast syn_verus::Open) {
        syn_verus::visit::visit_open(self, i);
    }

    fn visit_open_restricted(&mut self, i: &'ast syn_verus::OpenRestricted) {
        syn_verus::visit::visit_open_restricted(self, i);
    }

    fn visit_parenthesized_generic_arguments(
        &mut self,
        i: &'ast syn_verus::ParenthesizedGenericArguments,
    ) {
        syn_verus::visit::visit_parenthesized_generic_arguments(self, i);
    }

    fn visit_pat(&mut self, i: &'ast syn_verus::Pat) {
        syn_verus::visit::visit_pat(self, i);
    }

    fn visit_pat_box(&mut self, i: &'ast syn_verus::PatBox) {
        syn_verus::visit::visit_pat_box(self, i);
    }

    fn visit_pat_ident(&mut self, i: &'ast syn_verus::PatIdent) {
        syn_verus::visit::visit_pat_ident(self, i);
    }

    fn visit_pat_lit(&mut self, i: &'ast syn_verus::PatLit) {
        syn_verus::visit::visit_pat_lit(self, i);
    }

    fn visit_pat_macro(&mut self, i: &'ast syn_verus::PatMacro) {
        syn_verus::visit::visit_pat_macro(self, i);
    }

    fn visit_pat_or(&mut self, i: &'ast syn_verus::PatOr) {
        syn_verus::visit::visit_pat_or(self, i);
    }

    fn visit_pat_path(&mut self, i: &'ast syn_verus::PatPath) {
        syn_verus::visit::visit_pat_path(self, i);
    }

    fn visit_pat_range(&mut self, i: &'ast syn_verus::PatRange) {
        syn_verus::visit::visit_pat_range(self, i);
    }

    fn visit_pat_reference(&mut self, i: &'ast syn_verus::PatReference) {
        syn_verus::visit::visit_pat_reference(self, i);
    }

    fn visit_pat_rest(&mut self, i: &'ast syn_verus::PatRest) {
        syn_verus::visit::visit_pat_rest(self, i);
    }

    fn visit_pat_slice(&mut self, i: &'ast syn_verus::PatSlice) {
        syn_verus::visit::visit_pat_slice(self, i);
    }

    fn visit_pat_struct(&mut self, i: &'ast syn_verus::PatStruct) {
        syn_verus::visit::visit_pat_struct(self, i);
    }

    fn visit_pat_tuple(&mut self, i: &'ast syn_verus::PatTuple) {
        syn_verus::visit::visit_pat_tuple(self, i);
    }

    fn visit_pat_tuple_struct(&mut self, i: &'ast syn_verus::PatTupleStruct) {
        syn_verus::visit::visit_pat_tuple_struct(self, i);
    }

    fn visit_pat_type(&mut self, i: &'ast syn_verus::PatType) {
        syn_verus::visit::visit_pat_type(self, i);
    }

    fn visit_pat_wild(&mut self, i: &'ast syn_verus::PatWild) {
        syn_verus::visit::visit_pat_wild(self, i);
    }

    fn visit_path(&mut self, i: &'ast syn_verus::Path) {
        syn_verus::visit::visit_path(self, i);
    }

    fn visit_path_arguments(&mut self, i: &'ast syn_verus::PathArguments) {
        syn_verus::visit::visit_path_arguments(self, i);
    }

    fn visit_path_segment(&mut self, i: &'ast syn_verus::PathSegment) {
        syn_verus::visit::visit_path_segment(self, i);
    }

    fn visit_predicate_eq(&mut self, i: &'ast syn_verus::PredicateEq) {
        syn_verus::visit::visit_predicate_eq(self, i);
    }

    fn visit_predicate_lifetime(&mut self, i: &'ast syn_verus::PredicateLifetime) {
        syn_verus::visit::visit_predicate_lifetime(self, i);
    }

    fn visit_predicate_type(&mut self, i: &'ast syn_verus::PredicateType) {
        syn_verus::visit::visit_predicate_type(self, i);
    }

    fn visit_publish(&mut self, i: &'ast syn_verus::Publish) {
        syn_verus::visit::visit_publish(self, i);
    }

    fn visit_qself(&mut self, i: &'ast syn_verus::QSelf) {
        syn_verus::visit::visit_qself(self, i);
    }

    fn visit_range_limits(&mut self, i: &'ast syn_verus::RangeLimits) {
        syn_verus::visit::visit_range_limits(self, i);
    }

    fn visit_receiver(&mut self, i: &'ast syn_verus::Receiver) {
        syn_verus::visit::visit_receiver(self, i);
    }

    fn visit_recommends(&mut self, i: &'ast syn_verus::Recommends) {
        // self.file_stats.mark(i, self.mode_or_trusted(CodeKind::Spec), LineContent::FunctionSpec);
        syn_verus::visit::visit_recommends(self, i);
    }

    fn visit_requires(&mut self, i: &'ast syn_verus::Requires) {
        // self.file_stats.mark(i, self.mode_or_trusted(CodeKind::Spec), LineContent::FunctionSpec);
        syn_verus::visit::visit_requires(self, i);
    }

    fn visit_return_type(&mut self, i: &'ast syn_verus::ReturnType) {
        syn_verus::visit::visit_return_type(self, i);
    }

    fn visit_reveal_hide(&mut self, i: &'ast syn_verus::RevealHide) {
        syn_verus::visit::visit_reveal_hide(self, i);
    }

    fn visit_signature(&mut self, i: &'ast syn_verus::Signature) {
        syn_verus::visit::visit_signature(self, i);
    }

    fn visit_signature_decreases(&mut self, i: &'ast syn_verus::SignatureDecreases) {
        syn_verus::visit::visit_signature_decreases(self, i);
    }

    fn visit_signature_invariants(&mut self, i: &'ast syn_verus::SignatureInvariants) {
        syn_verus::visit::visit_signature_invariants(self, i);
    }

    fn visit_span(&mut self, i: &proc_macro2::Span) {
        syn_verus::visit::visit_span(self, i);
    }

    fn visit_specification(&mut self, i: &'ast syn_verus::Specification) {
        syn_verus::visit::visit_specification(self, i);
    }

    fn visit_stmt(&mut self, i: &'ast syn_verus::Stmt) {
        syn_verus::visit::visit_stmt(self, i);
    }

    fn visit_trait_bound(&mut self, i: &'ast syn_verus::TraitBound) {
        syn_verus::visit::visit_trait_bound(self, i);
    }

    fn visit_trait_bound_modifier(&mut self, i: &'ast syn_verus::TraitBoundModifier) {
        syn_verus::visit::visit_trait_bound_modifier(self, i);
    }

    fn visit_trait_item(&mut self, i: &'ast syn_verus::TraitItem) {
        syn_verus::visit::visit_trait_item(self, i);
    }

    fn visit_trait_item_const(&mut self, i: &'ast syn_verus::TraitItemConst) {
        syn_verus::visit::visit_trait_item_const(self, i);
    }

    fn visit_trait_item_macro(&mut self, i: &'ast syn_verus::TraitItemMacro) {
        syn_verus::visit::visit_trait_item_macro(self, i);
    }

    fn visit_trait_item_method(&mut self, i: &'ast syn_verus::TraitItemMethod) {
        let exit = self.item_attr_enter(&i.attrs);
        let content_code_kind = i.sig.mode.to_code_kind();
        let code_kind = self.mode_or_trusted(content_code_kind);
        self.file_stats.mark_content(&i, LineContent::Trait);
        // self.file_stats.mark(&i.default, code_kind, LineContent::Code(content_code_kind));
        self.file_stats.mark_content(&i.default, LineContent::Body(content_code_kind));
        self.handle_signature(content_code_kind, code_kind, &i.sig);
        self.in_body = Some(content_code_kind);
        if let Some(default) = &i.default {
            self.visit_block(default);
        }
        syn_verus::visit::visit_trait_item_method(self, i);
        self.in_body = None;
        exit.exit(self);
    }

    fn visit_trait_item_type(&mut self, i: &'ast syn_verus::TraitItemType) {
        self.file_stats.mark(&i, CodeKind::Definitions, LineContent::TypeDefinition);
        syn_verus::visit::visit_trait_item_type(self, i);
    }

    fn visit_type(&mut self, i: &'ast syn_verus::Type) {
        // self.file_stats.mark(&i, CodeKind::Definitions, LineContent::TypeDefinition);
        syn_verus::visit::visit_type(self, i);
    }

    fn visit_use_tree(&mut self, i: &'ast syn_verus::UseTree) {
        self.file_stats.mark(i, CodeKind::Directives, LineContent::Directive);
        syn_verus::visit::visit_use_tree(self, i);
    }

    fn visit_view(&mut self, i: &'ast syn_verus::View) {
        syn_verus::visit::visit_view(self, i);
    }

    fn visit_where_clause(&mut self, i: &'ast syn_verus::WhereClause) {
        syn_verus::visit::visit_where_clause(self, i);
    }

    fn visit_where_predicate(&mut self, i: &'ast syn_verus::WherePredicate) {
        syn_verus::visit::visit_where_predicate(self, i);
    }
}

struct ItemAttrExit {
    entered: bool,
}

impl ItemAttrExit {
    fn exit(self, visitor: &mut Visitor) {
        if self.entered {
            visitor.trusted -= 1;
        }
    }
}

impl<'f> Visitor<'f> {
    fn item_attr_enter(&mut self, attrs: &Vec<Attribute>) -> ItemAttrExit {
        for attr in attrs.iter() {
            if let Ok(Meta::Path(path)) = attr.parse_meta() {
                let mut path_iter = path.segments.iter();
                match (path_iter.next(), path_iter.next()) {
                    (Some(first), Some(second))
                        if first.ident == "verus" && second.ident == "trusted" =>
                    {
                        self.trusted += 1;
                        return ItemAttrExit { entered: true };
                    }
                    _ => {}
                }
            }

            if attr.path.segments.first().map(|x| x.ident == "doc").unwrap_or(false) {
            } else {
                self.file_stats.mark(
                    &attr,
                    self.mode_or_trusted(CodeKind::Directives),
                    LineContent::Directive,
                );
            }
        }
        ItemAttrExit { entered: false }
    }

    fn mode_or_trusted(&self, kind: CodeKind) -> CodeKind {
        if self.trusted > 0 { CodeKind::Trusted } else { kind }
    }

    fn handle_signature(
        &mut self,
        content_code_kind: CodeKind,
        code_kind: CodeKind,
        sig: &Signature,
    ) {
        self.file_stats.mark(&sig, code_kind, LineContent::Signature(content_code_kind));
        if code_kind != CodeKind::Spec {
            if let Some(requires) = &sig.requires {
                self.file_stats.mark(
                    requires,
                    self.mode_or_trusted(CodeKind::Spec),
                    LineContent::FunctionSpec,
                );
            }
            if let Some(ensures) = &sig.ensures {
                self.file_stats.mark(
                    ensures,
                    self.mode_or_trusted(CodeKind::Spec),
                    LineContent::FunctionSpec,
                );
            }
            if let Some(decreases) = &sig.decreases {
                self.file_stats.mark(
                    decreases,
                    self.mode_or_trusted(CodeKind::Spec),
                    LineContent::FunctionSpec,
                );
            }
        }
    }
}

fn cut_string(s: String, len: usize) -> String {
    s.chars().take(len).collect()
}

fn hash_map_to_fit_string<V: std::fmt::Debug>(h: &[V], len: usize) -> String {
    if h.len() != 0 {
        let each_len = (len / h.len()) - 1;
        h.iter().map(|x| cut_string(format!("{:?}", x), each_len)).collect::<Vec<_>>().join(" ")
    } else {
        "".into()
    }
}

// parse the .d file and returns a vector of files names required to generate the crate
fn get_dependencies(
    dep_file_path: &std::path::Path,
) -> Result<(std::path::PathBuf, Vec<std::path::PathBuf>), String> {
    use std::path::{Path, PathBuf};

    let file = std::fs::File::open(dep_file_path)
        .map_err(|x| format!("{}, dependency file name: {:?}", x, dep_file_path))?;
    let mut reader = std::io::BufReader::new(file);
    let mut dependencies = String::new();
    std::io::BufRead::read_line(&mut reader, &mut dependencies).map_err(|x| {
        format!("Could not read the first line of the dependency file with message: {}", x)
    })?;
    let dep_file_folder = dep_file_path
        .parent()
        .ok_or(format!("invalid dependencies file path {}", dep_file_path.display()))?;
    let result: Vec<_> = dependencies
        .split_whitespace()
        .skip(1)
        .map(|x| dep_file_folder.join(Path::new(x)))
        .collect();
    assert!(result.len() > 0);
    let mut path_iters: Vec<_> = result.iter().map(|x| x.iter()).collect();
    let mut chomp_components = 0;
    loop {
        let common = path_iters
            .iter_mut()
            .map(|x| x.next())
            .reduce(|acc, x| acc.and_then(|a| if Some(a) == x { Some(a) } else { None }))
            .flatten();
        if common.is_some() {
            chomp_components += 1;
        } else {
            break;
        }
    }
    let result_chomped: Vec<PathBuf> =
        result.iter().map(|p| PathBuf::from_iter(p.components().skip(chomp_components))).collect();
    let chomped = PathBuf::from_iter(result[0].iter().take(chomp_components));

    Ok((chomped, result_chomped))
}

#[derive(Debug, Clone)]
struct Summary {
    lines_by_kind: HashMap<Vec<CodeKind>, usize>,
}

impl std::ops::Add for Summary {
    type Output = Summary;

    fn add(self, rhs: Self) -> Self::Output {
        Summary {
            lines_by_kind: {
                let mut lines_by_kind = HashMap::new();
                for (kinds, count) in self.lines_by_kind.into_iter() {
                    *lines_by_kind.entry(kinds).or_default() += count;
                }
                for (kinds, count) in rhs.lines_by_kind.into_iter() {
                    *lines_by_kind.entry(kinds).or_default() += count;
                }
                lines_by_kind
            },
        }
    }
}

impl std::iter::Sum for Summary {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Summary { lines_by_kind: HashMap::new() }, |a, b| a + b)
    }
}

fn hash_set_to_sorted_vec<V: Clone + Ord>(h: &HashSet<V>) -> Vec<V> {
    let mut v: Vec<_> = h.iter().cloned().collect();
    v.sort();
    v
}

fn process_file(_config: &Config, input_path: &std::path::Path) -> Result<FileStats, String> {
    let file_content = std::fs::read_to_string(input_path)
        .map_err(|e| format!("cannot read {} ({})", input_path.display(), e))?;
    let file = syn_verus::parse_file(&file_content)
        .map_err(|e| format!("failed to parse file {}: {}", input_path.display(), e))?;

    let mut file_stats = FileStats {
        lines: file_content
            .lines()
            .map(|x| LineInfo {
                kinds: HashSet::new(),
                path: Vec::new(),
                line_content: HashSet::new(),
                text: x.into(),
            })
            .collect::<Vec<_>>()
            .into_boxed_slice(),
    };
    let mut visitor =
        Visitor { file_stats: &mut file_stats, in_body: None, trusted: 0, in_proof_directive: 0 };
    for attr in file.attrs.iter() {
        if let Ok(Meta::Path(path)) = attr.parse_meta() {
            let mut path_iter = path.segments.iter();
            match (path_iter.next(), path_iter.next()) {
                (Some(first), Some(second))
                    if first.ident == "verus" && second.ident == "trusted" =>
                {
                    visitor.trusted += 1;
                }
                _ => {}
            }
        }
    }
    for item in file.items.into_iter() {
        match item {
            syn_verus::Item::Macro(m) => {
                let source_toks = m.mac.tokens;
                let macro_content: File = syn_verus::parse2(source_toks).map_err(|e| {
                    format!("failed to parse file {}: {} {:?}", input_path.display(), e, e.span())
                })?;
                visitor.visit_file(&macro_content);
            }
            _ => {
                visitor.visit_item(&item);
            }
        }
    }
    let mut multiline_comment = 0;
    for line in file_stats.lines.iter_mut() {
        let trimmed = line.text.trim();
        for (m, _) in trimmed.match_indices("/*") {
            if trimmed[..m].trim().is_empty() && multiline_comment == 0 {
                line.line_content = HashSet::from([LineContent::Comment]);
                line.kinds = HashSet::from([CodeKind::Comment])
            }
            multiline_comment += 1;
        }
        for (m, _) in trimmed.match_indices("*/") {
            multiline_comment -= 1;
            if trimmed[m..].trim().is_empty() && multiline_comment == 0 {
                line.line_content = HashSet::from([LineContent::Comment]);
                line.kinds = HashSet::from([CodeKind::Comment])
            }
        }
        if multiline_comment > 0 {
            line.line_content = HashSet::from([LineContent::Comment]);
            line.kinds = HashSet::from([CodeKind::Comment])
        }
        if trimmed.starts_with("//") {
            line.line_content = HashSet::from([LineContent::Comment]);
            line.kinds = HashSet::from([CodeKind::Comment])
        }
        if line.kinds.is_empty() && (trimmed == "{" || trimmed == "}" || trimmed == "") {
            line.kinds = HashSet::from([CodeKind::Layout])
        }
    }
    Ok(file_stats)
}

fn run(config: &Config, deps_path: &std::path::Path) -> Result<(), String> {
    let (root_path, files) = get_dependencies(deps_path)?;

    let file_stats = files
        .iter()
        .map(|f| process_file(config, &root_path.join(f)).map(|fs| (f, fs)))
        .collect::<Result<Vec<_>, String>>()?;

    if config.print_all {
        eprintln!("{:18} | {:30} | {}", "Category", "Detailed contents", "");
        eprintln!();
        for (file, file_stats) in file_stats.iter() {
            eprintln!("# {}", file.display());
            for l in file_stats.lines.iter() {
                eprintln!(
                    "{:18} | {:30} | {}",
                    hash_map_to_fit_string(&hash_set_to_sorted_vec(&l.kinds)[..], 30),
                    hash_map_to_fit_string(&hash_set_to_sorted_vec(&l.line_content)[..], 30),
                    l.text
                );
            }
            eprintln!();
        }
    }

    let file_summaries = file_stats
        .iter()
        .map(|(name, file_stats)| {
            let mut lines_by_kind = HashMap::new();
            for l in file_stats.lines.iter() {
                let mut kinds = l.kinds.clone();
                if kinds.contains(&CodeKind::Exec)
                    || kinds.contains(&CodeKind::Proof)
                    || kinds.contains(&CodeKind::Spec)
                {
                    kinds
                        .retain(|x| matches!(x, CodeKind::Exec | CodeKind::Proof | CodeKind::Spec));
                }
                *lines_by_kind.entry(hash_set_to_sorted_vec(&kinds)).or_default() += 1;
            }
            (name, Summary { lines_by_kind })
        })
        .collect::<Vec<_>>();

    let total: Summary = file_summaries.iter().map(|(_, fs)| fs).cloned().sum();

    let kinds: HashSet<_> =
        file_summaries.iter().flat_map(|(_, s)| s.lines_by_kind.keys()).cloned().collect();

    let columns: Vec<_> = {
        let mut columns: Vec<_> = vec![
            HashSet::from([CodeKind::Trusted]),
            HashSet::from([CodeKind::Spec]),
            HashSet::from([CodeKind::Proof]),
            HashSet::from([CodeKind::Exec]),
            HashSet::from([CodeKind::Proof, CodeKind::Exec]),
            HashSet::from([CodeKind::Comment]),
            HashSet::from([CodeKind::Layout]),
            HashSet::from([]),
        ];
        let other_columns: Vec<_> = kinds
            .difference(&HashSet::from_iter(columns.iter().map(hash_set_to_sorted_vec)))
            .map(|h| HashSet::from_iter(h.iter().cloned()))
            .collect();
        columns.extend(other_columns);
        columns.iter().map(hash_set_to_sorted_vec).collect()
    };

    let mut table_data: Vec<Vec<String>> = file_summaries
        .iter()
        .map(|(f, s)| {
            Some(f.display().to_string())
                .into_iter()
                .chain(columns.iter().map(|k| format!("{}", s.lines_by_kind.get(k).unwrap_or(&0))))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    table_data.insert(
        0,
        Some("file".to_owned())
            .into_iter()
            .chain(columns.iter().map(|k| {
                if k.is_empty() {
                    format!("unaccounted")
                } else {
                    k.iter().map(|x| format!("{:?}", x)).collect::<Vec<_>>().join("+")
                }
            }))
            .collect(),
    );
    table_data.push(
        Some("total".to_owned())
            .into_iter()
            .chain(columns.iter().map(|k| format!("{}", total.lines_by_kind.get(k).unwrap_or(&0))))
            .collect(),
    );

    let mut table = tabled::builder::Builder::from(table_data).build();
    table
        .with(Style::markdown())
        .with(Modify::new(Columns::new(1..=kinds.len() + 1)).with(Alignment::right()))
        .with(Modify::new(Rows::last()).with(
            tabled::settings::Border::default().corner_top_left('|').corner_top_right('|').top('-'),
        ));
    println!("{}", table.to_string());

    Ok(())
}
