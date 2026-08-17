use std::{collections::BTreeMap, fmt::Debug};

use verus_syn::spanned::Spanned;

use crate::attribution::{CodeKind, LineContent, LineInfo, to_lines_range};

pub struct FileStats {
    pub lines: Box<[LineInfo]>,
}

impl FileStats {
    #[allow(dead_code)]
    pub fn mark_kind(&mut self, spanned: &impl Spanned, kind: CodeKind) {
        for l in to_lines_range(spanned) {
            self.lines[l]
                .kinds
                .retain(|x| !matches!(x, CodeKind::Spec | CodeKind::Proof | CodeKind::Exec));
            self.lines[l].kinds.insert(kind);
        }
    }

    #[allow(dead_code)]
    pub fn mark_additional_kind(&mut self, spanned: &impl Spanned, kind: CodeKind) {
        for l in to_lines_range(spanned) {
            self.lines[l].kinds.insert(kind);
        }
    }

    pub fn mark_content(&mut self, spanned: &impl Spanned, content: LineContent) {
        for l in to_lines_range(spanned) {
            self.lines[l].line_content.insert(content);
        }
    }

    pub fn mark(&mut self, spanned: &(impl Spanned + Debug), kind: CodeKind, content: LineContent) {
        for l in to_lines_range(spanned) {
            self.lines[l]
                .kinds
                .retain(|x| !matches!(x, CodeKind::Spec | CodeKind::Proof | CodeKind::Exec));
            self.lines[l].kinds.insert(kind);
            self.lines[l].line_content.insert(content);
        }
    }

    pub fn mark_with_additional_kind(
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

#[derive(Debug, Clone)]
pub struct Summary {
    pub lines_by_kind: BTreeMap<Vec<CodeKind>, usize>,
}

impl std::ops::Add for Summary {
    type Output = Summary;

    fn add(self, rhs: Self) -> Self::Output {
        Summary {
            lines_by_kind: {
                let mut lines_by_kind = BTreeMap::new();
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
        iter.fold(Summary { lines_by_kind: BTreeMap::new() }, |a, b| a + b)
    }
}
