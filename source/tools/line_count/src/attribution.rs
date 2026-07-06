use std::{collections::BTreeSet, fmt::Debug, ops::RangeInclusive};

use serde::Serialize;
use verus_syn::spanned::Spanned;

use crate::syn_visitor::Visitor;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, PartialOrd, Ord)]
pub enum CodeKind {
    Trusted,
    Spec,
    Proof,
    Exec,
    Directives,
    Definitions,
    Comment,
    Layout,
}

impl CodeKind {
    pub fn join_prefer_left(&self, other: CodeKind) -> CodeKind {
        match (self, other) {
            (CodeKind::Spec, _) => CodeKind::Spec,
            (_, CodeKind::Spec) => CodeKind::Spec,
            (CodeKind::Proof, _) => CodeKind::Proof,
            (_, CodeKind::Proof) => CodeKind::Proof,
            (CodeKind::Exec, _) => CodeKind::Exec,
            (_, CodeKind::Exec) => CodeKind::Exec,
            (other, _) => *other,
        }
    }
}

pub trait ToCodeKind {
    fn to_code_kind(&self) -> CodeKind;
}

impl ToCodeKind for verus_syn::DataMode {
    fn to_code_kind(&self) -> CodeKind {
        match self {
            verus_syn::DataMode::Ghost(_) => CodeKind::Spec,
            verus_syn::DataMode::Tracked(_) => CodeKind::Proof,
            verus_syn::DataMode::Exec(_) => CodeKind::Exec,
            verus_syn::DataMode::Default => CodeKind::Exec,
        }
    }
}

impl ToCodeKind for verus_syn::FnMode {
    fn to_code_kind(&self) -> CodeKind {
        match self {
            verus_syn::FnMode::Spec(_) | verus_syn::FnMode::SpecChecked(_) => CodeKind::Spec,
            // REVIEW: ProofAxiom may need to be treatead as trusted, with an explicit LineContent entry
            verus_syn::FnMode::Proof(_) | verus_syn::FnMode::ProofAxiom(_) => CodeKind::Proof,
            verus_syn::FnMode::Exec(_) | verus_syn::FnMode::Default => CodeKind::Exec,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum StateMachineCode {
    NameAndFields,
    Transition,
    Property,
    StructWithInvariantBody,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LineContent {
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
    StateMachine(StateMachineCode),
    Atomic,
}

pub struct LineInfo {
    pub kinds: BTreeSet<CodeKind>,
    #[allow(dead_code)]
    pub path: Vec<String>,
    pub line_content: BTreeSet<LineContent>,
    pub text: String,
}

pub fn to_lines_range(spanned: &impl Spanned) -> RangeInclusive<usize> {
    let span = spanned.span();
    let proc_macro2::LineColumn { line: start_line, column: _ } = span.start();
    let proc_macro2::LineColumn { line: end_line, column: _ } = span.end();
    (start_line - 1)..=(end_line - 1)
}

pub(crate) struct ItemAttrExit {
    pub(crate) entered_trusted: bool,
    pub(crate) entered_ignore: bool,
    pub(crate) entered_verify: bool,
    pub(crate) entered_external: bool,
    pub(crate) entered_consider: bool,
    pub(crate) entered_verus_spec: bool,
}

impl ItemAttrExit {
    pub(crate) fn exit(self, visitor: &mut Visitor) {
        if self.entered_trusted {
            visitor.trusted -= 1;
        }
        if self.entered_ignore {
            visitor.inside_line_count_ignore_or_external -= 1;
        }
        if self.entered_verify {
            visitor.inside_verus_macro_or_verify_or_consider -= 1;
        }
        if self.entered_external {
            visitor.inside_line_count_ignore_or_external -= 1;
        }
        if self.entered_consider {
            visitor.inside_verus_macro_or_verify_or_consider -= 1;
        }
        if self.entered_verus_spec {
            visitor.inside_verus_macro_or_verify_or_consider -= 1;
        }
    }
}
