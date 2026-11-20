//! Text edits at byte offsets of an original source file, shared by the MC/DC rewriter and the
//! mutant rewriter so that the edits of both can be applied to one file.
//!
//! Every edit inserts text at `off` and may delete `del` bytes there. An `Open` edit starts a
//! wrapper around the source range `span`, a `Close` edit ends one, a `Mid` edit replaces a token
//! inside a wrapper (an operator). At one offset, closes come first, then mids, then opens. Opens
//! of a larger span come first (outer wrappers open first); closes of a smaller span come first
//! (inner wrappers close first). For equal spans, `layer` orders edits from different rewriters
//! (lower layers are outer), then `depth` and `seq` order the edits of one rewriter.

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Kind {
    Close,
    Mid,
    Open,
}

#[derive(Clone, Debug)]
pub struct Insert {
    pub off: usize,
    pub del: usize,
    pub kind: Kind,
    /// Source range wrapped by an Open/Close pair. A statement inserted after a `{` uses
    /// `(off, usize::MAX)`, so it is outside every wrapper that opens at the same offset.
    pub span: (usize, usize),
    pub layer: u8,
    pub depth: u32,
    pub seq: u32,
    pub text: String,
}

/// Layers, outer to inner, for wrappers of the same source range.
pub mod layer {
    /// statements inserted after a `{`, crate attributes
    pub const POINT: u8 = 0;
    /// mutant wrappers that take the original value as one argument (`crate::__mut::b(ID, (A))`)
    pub const MUT_WRAP: u8 = 1;
    /// MC/DC decision wrappers and let-chain scaffolding
    pub const MCDC_DECISION: u8 = 2;
    /// MC/DC atom wrappers
    pub const MCDC_ATOM: u8 = 3;
    /// mutant wrappers that also replace a token inside the range (operator swaps, comparisons)
    pub const MUT_SPLIT: u8 = 4;
    /// mutant edits that replace the whole range (`matches!` variant swaps)
    pub const MUT_REPLACE: u8 = 5;
    /// text appended at the end of a file
    pub const END: u8 = 9;
}

fn cmp(a: &Insert, b: &Insert) -> std::cmp::Ordering {
    a.off.cmp(&b.off).then(a.kind.cmp(&b.kind)).then_with(|| match a.kind {
        Kind::Open => b
            .span
            .1
            .cmp(&a.span.1)
            .then(a.layer.cmp(&b.layer))
            .then(a.depth.cmp(&b.depth))
            .then(a.seq.cmp(&b.seq)),
        Kind::Close => b
            .span
            .0
            .cmp(&a.span.0)
            .then(b.layer.cmp(&a.layer))
            .then(b.depth.cmp(&a.depth))
            .then(b.seq.cmp(&a.seq)),
        Kind::Mid => a.seq.cmp(&b.seq),
    })
}

/// Applies the edits to `src`. Fails when an edit falls inside a range deleted by another.
pub fn render(src: &str, mut inserts: Vec<Insert>) -> Result<String, String> {
    inserts.sort_by(cmp);
    let mut out = String::with_capacity(src.len() * 2);
    let mut last = 0;
    for ins in &inserts {
        if ins.off < last {
            return Err(format!("overlapping edit at byte {}", ins.off));
        }
        out.push_str(&src[last..ins.off]);
        out.push_str(&ins.text);
        last = ins.off + ins.del;
    }
    out.push_str(&src[last..]);
    Ok(out)
}
