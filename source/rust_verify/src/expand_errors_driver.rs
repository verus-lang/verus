use rustc_session::config::ErrorOutputType;
use std::collections::HashMap;
use std::sync::Arc;
use vir::context::Ctx;
use vir::expand_errors::{
    cons_id, CanExpandFurther, ExpansionContext, ExpansionTree, Introduction,
};
use vir::sst::FuncCheckSst;
use vir::sst::{AssertId, Exp};

const MAX_FAILURES: u64 = 4;
const MAX_DEPTH: usize = 7;

/// Result for a single query made during the expand-errors loop
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ExpandErrorsResult {
    Fail,
    Timeout,
    Pass,
    // If we do an expansion and there are no branches,
    // then we don't actually run a sub-query since it should
    // be equivalent. Instead, we 'presume' it to be a fail.
    PresumedFail,
}

/// Object responsible for maintaining state during an expand-errors
/// invocation and determining which expansions to perform.

// How it works:
//
// Suppose that, during a normal query, assert ID 42 fails.
// This causes us to initialize expand-errors on ID 42.
// We then "expand" ID 42, which will do one level of function unfolding,
// resulting in a query that has IDs 42_0, 42_1, 42_2, etc.
// Later, 42_1 might be expanded to 42_1_0, 42_1_1, 42_1_2,
// and so on.
//
// Even though a single expansion only does one level of function unfolding,
// it *also* has a tree structure because there may be a hierarchical
// structure in the grouping of hypotheses or quantifier introductions.
// For example, suppose we have an assert with ID 42 for the expression:
//
//   (A ==>
//      (B && C && (D ==> E))
//   && (F ==> G)
//
// On expansion this becomes a tree with the sub-IDs at the leaves:
//
//  A ==>
//    B     (ID 42_0)
//    C     (ID 42_1)
//    D ==>
//      E     (ID 42_2)
//  F ==>
//    G     (ID 42_3)
//
// This structure is represented by the 'ExpansionTree'.
//
// Now, one of these sub-asserts, e.g., 42_2, might be expanded later.
// Thus we have a 'tree-of-trees' structure:
//  - A tree of expansions, giving rise to a hierarchy of assert IDs
//  - Each expansion is itself a tree of expressions (the ExpansionTree)
//
// The main objectives of this file are:
//  - Determine which expansions to perform (thus "growing" the outer-tree structure)
//    and choosing which queries to run
//  - Flattening the tree-of-trees into a form suitable to print to the user,
//    indicating which queries fail or succeed

pub struct ExpandErrorsDriver {
    /// The function we're operating on.
    pub function: vir::sst::FunctionSst,

    /// Initial ID to be expanded, should be length 1.
    base_id: AssertId,
    /// FuncCheckSst from the query that prompted the expand-errors mechancism.
    base_func_check_sst: Arc<FuncCheckSst>,
    /// Pre-computed context information
    ectx: ExpansionContext,

    /// Maps an ID to the expansion of that ID.
    /// For example, 42_1 might point to a FuncCheckSst
    /// with assert_ids 42_1_0, 42_1_1, 42_2_2, 42_2_3.
    /// The ExapansionTree is the tree that explains how 42_1
    /// was expanded into its sub-assertions.
    expansions: HashMap<AssertId, (ExpansionTree, Arc<FuncCheckSst>)>,

    /// The ID for the query we're currently running.
    /// Becomes empty [] when execution finishes.
    current: Vec<u64>,
    /// Maximum index at each level in the current stack.
    caps: Vec<u64>,
    /// num_leaf_failures
    leaf_fails: u64,

    /// Result for a given assertion
    results: HashMap<AssertId, ExpandErrorsResult>,

    /// A "mega tree" of all the expansion trees glued together,
    /// flatted (pre-order) into a list where each line has an 'indentation',
    /// resulting in a tree structure.
    /// Corresponds directly with the diagnostic output
    output: Vec<Line>,

    /// Source spans to point to corresponding to the erroring lines
    spans: Vec<(vir::messages::Span, AssertId)>,
}

#[derive(Debug)]
enum LineKind {
    Intro(Introduction),
    Leaf(AssertId, Exp),
    Explanation(String),
}

#[derive(Debug)]
struct Line {
    indent: u64,
    kind: LineKind,
}

enum Style {
    FailRed,
    SuccessGreen,
    Normal,
}

impl ExpandErrorsDriver {
    /// Create a new driver object which will repeatedly expand the given assert_id
    pub fn new(
        function: &vir::sst::FunctionSst,
        assert_id: &AssertId,
        func_check_sst: Arc<FuncCheckSst>,
    ) -> Self {
        assert!(assert_id.len() == 1);
        Self {
            function: function.clone(),
            base_id: assert_id.clone(),
            ectx: vir::expand_errors::get_expansion_ctx(&func_check_sst.body, assert_id),
            base_func_check_sst: func_check_sst,
            expansions: HashMap::new(),
            results: HashMap::new(),
            caps: vec![assert_id[0] + 1],
            leaf_fails: 0,
            current: (**assert_id).clone(),
            output: vec![],
            spans: vec![],
        }
    }

    /// Report the result for a given assert_id (must be the current assert_id).
    /// Upon creation of the driver, the client should immediately call `report`
    /// for the root ID with a Fail result, then afterwards call `report`
    /// for the other queries.
    /// This will advance the current assert_id to the next assert_id that
    /// should be queries.
    pub fn report(&mut self, ctx: &Ctx, assert_id: &AssertId, result: ExpandErrorsResult) {
        assert!(&self.current == &**assert_id);
        if assert_id.len() == 1 {
            assert!(result != ExpandErrorsResult::Pass);
        }
        let cur_depth = assert_id.len();

        self.results.insert(assert_id.clone(), result);

        if result == ExpandErrorsResult::Pass {
            self.advance();
        } else {
            if assert_id.len() > 1 {
                self.spans.push((self.get_span_for(assert_id), assert_id.clone()));
            }

            let n = self.expand(ctx, assert_id);
            if n == 1 {
                self.leaf_fails += 1;
                if self.leaf_fails >= MAX_FAILURES {
                    self.skip_to_end();
                } else {
                    self.advance();
                }
            } else {
                if cur_depth < MAX_DEPTH {
                    self.descend(n);
                } else {
                    self.advance();
                }
            }
        }
    }

    /// Get the current assert_id to query, and the FuncCheckSst
    /// which has an assertion for that id.
    /// For example, if the 'current' is 42_1, then the FuncCheckSst
    /// will be the expansion of '42', which
    /// may have asserts for 42_0, 42_1, 42_2, ...
    /// The client is responsible for focusing on the 42_1 assert.
    ///
    /// Returns None if we're done.
    pub fn get_current(&self) -> Option<(AssertId, Arc<FuncCheckSst>)> {
        if self.current.len() > 0 {
            let parent_id = self.current[..self.current.len() - 1].to_vec();
            let fsst = self.expansions.get(&parent_id).unwrap().1.clone();
            let assert_id = Arc::new(self.current.clone());
            Some((assert_id, fsst))
        } else {
            None
        }
    }

    fn descend(&mut self, n: u64) {
        self.current.push(0);
        self.caps.push(n);
    }

    fn skip_to_end(&mut self) {
        self.current = vec![];
    }

    fn advance(&mut self) {
        while self.current.len() > 0 {
            let idx = self.current.len() - 1;
            self.current[idx] += 1;
            if self.current[idx] >= self.caps[idx] {
                self.current.pop();
                self.caps.pop();
            } else {
                break;
            }
        }
    }

    fn expand(&mut self, ctx: &Ctx, assert_id: &AssertId) -> u64 {
        assert!(ctx.fun.as_ref().unwrap().current_fun == self.function.x.name);
        let func_check_sst = if &self.base_id == assert_id {
            &self.base_func_check_sst
        } else {
            let parent_id = assert_id[..assert_id.len() - 1].to_vec();
            &self.expansions.get(&parent_id).unwrap().1
        };

        let (new_function_sst, expansion_tree) =
            vir::expand_errors::do_expansion(ctx, &self.ectx, func_check_sst, assert_id);
        let num_leaves = expansion_tree.count_leaves();
        self.add_lines_to_output(&assert_id, &expansion_tree, num_leaves == 1);
        self.expansions.insert(assert_id.clone(), (expansion_tree, new_function_sst));
        if num_leaves == 1 {
            let one_assert_id = cons_id(assert_id, 0);
            self.results.insert(one_assert_id, ExpandErrorsResult::PresumedFail);
        }
        num_leaves
    }

    /// Update self.output when we do a new expansion
    /// For example, suppose self.output is like:
    ///   f()
    ///     g()
    ///       h()
    ///     k()
    ///
    /// Then if we expand h(), we need to add some lines under h().
    /// For example, if expanding h() gives us an expansion tree:
    ///   unfold h()
    ///     branch [ r(), j() ]
    ///
    /// Then we'd add this tree to self.output:
    ///
    ///   f()
    ///     g()
    ///       h()
    ///         r()
    ///         j()
    ///     k()
    ///
    /// We need to be careful not to repeat the 'h()' line, since it's already there,
    /// but it's also going to be the first unfolding in the ExpansionTree.
    fn add_lines_to_output(&mut self, id: &AssertId, tree: &ExpansionTree, explain: bool) {
        // Flatten the given tree to a list
        fn rec(tree: &ExpansionTree, indent: u64, lines: &mut Vec<Line>, explain: bool) {
            match tree {
                ExpansionTree::Branch(children) => {
                    for child in children.iter() {
                        rec(child, indent, lines, explain);
                    }
                }
                ExpansionTree::Intro(intro, child) => {
                    lines.push(Line { indent, kind: LineKind::Intro(intro.clone()) });
                    rec(&child, indent + 1, lines, explain);
                }
                ExpansionTree::Leaf(assert_id, e, can_expand_further) => {
                    lines.push(Line { indent, kind: LineKind::Leaf(assert_id.clone(), e.clone()) });
                    if let CanExpandFurther::No(Some(msg)) = can_expand_further {
                        if explain {
                            lines.push(Line {
                                indent: indent + 1,
                                kind: LineKind::Explanation(msg.clone()),
                            });
                        }
                    }
                }
            }
        }

        let (idx, start_indent) = if id.len() == 1 {
            (0, 0)
        } else {
            let idx = self
                .output
                .iter()
                .position(|l| match &l.kind {
                    LineKind::Leaf(id_vec, _) => id_vec == id,
                    _ => false,
                })
                .unwrap();
            let start_indent = self.output[idx].indent;
            (idx + 1, start_indent)
        };

        /*let tree = if id.len() == 1 {
            tree
        } else {
            // Skip the first function unfolding, it would be redundant
            match tree {
                ExpansionTree::Intro(Introduction::UnfoldFunctionDef(..), t) => &t,
                ExpansionTree::Leaf(..) => {
                    return;
                }
                _ => tree,
            }
        };*/

        // Add the new lines at the right point in the self.output list.

        let mut new_lines = vec![];
        rec(tree, start_indent, &mut new_lines, explain);

        let first_is_redundant = id.len() != 1;
        if first_is_redundant {
            new_lines.remove(0);
        }

        self.output.splice(idx..idx, new_lines);
    }

    /// Get the String to display to the user.
    /// This is mostly serializing self.output and annotating some
    /// lines with a query result.
    pub fn get_output(&self, ctx: &Ctx) -> String {
        let mut group_bars: Vec<usize> = vec![];
        fn close_up_group_bars(b: &mut Vec<String>, group_bars: &mut Vec<usize>, indent: u64) {
            while group_bars.len() > 0 {
                let level = group_bars[group_bars.len() - 1];
                if (level as u64) < indent {
                    break;
                }
                group_bars.pop();
                add_indent(b, &group_bars, level as u64);
                b.push("+---\n".to_string());
            }
        }
        fn add_indent(b: &mut Vec<String>, group_bars: &Vec<usize>, indent: u64) {
            let mut idx = 0;
            let mut i = 0;
            while i < indent {
                if idx < group_bars.len() && group_bars[idx] == i as usize {
                    b.push("|   ".to_string());
                    idx += 1;
                } else {
                    b.push("    ".to_string());
                }
                i += 1;
            }
        }

        let mut b: Vec<String> = vec!["diagnostics via expansion:\n".into()];

        for (i, line) in self.output.iter().enumerate() {
            close_up_group_bars(&mut b, &mut group_bars, line.indent);

            let (l, style) = match &line.kind {
                LineKind::Intro(intro) => {
                    let style = self.get_line_style(i);
                    let l = match intro {
                        Introduction::UnfoldFunctionDef(_fun, exp) => {
                            vec![format!("{}", exp.x.to_user_string(&ctx.global))]
                        }
                        Introduction::SplitEquality(exp) => {
                            vec![format!("{}", exp.x.to_user_string(&ctx.global))]
                        }
                        Introduction::Let(binders) => {
                            let mut w = vec![];
                            for (i, binder) in binders.iter().enumerate() {
                                let mut v = vec![];
                                if i != 0 {
                                    v.push("\n".into());
                                    add_indent(&mut v, &group_bars, line.indent);
                                }
                                v.push("let ".into());
                                v.push((*binder.name.0).clone());
                                v.push(" = ".into());
                                v.push(binder.a.x.to_user_string(&ctx.global));
                                v.push(";".into());
                                w.push(v.join(""));
                            }
                            w
                        }
                        Introduction::Forall(binders) => {
                            let mut v = vec![];
                            v.push("forall |".into());
                            for (i, binder) in binders.iter().enumerate() {
                                if i != 0 {
                                    v.push(", ".into());
                                }
                                v.push((*binder.name.0).clone());
                            }
                            v.push("|".into());
                            vec![v.join("")]
                        }
                        Introduction::Hypothesis(exp) => {
                            vec![format!("{} ==>", exp.x.to_user_string(&ctx.global))]
                        }
                    };
                    (l, style)
                }
                LineKind::Leaf(id, exp) => {
                    let (status, style) = match self.results.get(id) {
                        None => {
                            let s = if &**id == &self.current { "..." } else { "" };
                            (s, Style::Normal)
                        }
                        Some(ExpandErrorsResult::Fail) => ("✘", Style::FailRed),
                        Some(ExpandErrorsResult::Timeout) => {
                            ("✘ [rlimit exceeded]", Style::FailRed)
                        }
                        Some(ExpandErrorsResult::PresumedFail) => {
                            // Don't use an X because we didn't actually run a query
                            // But still mark it red
                            ("", Style::FailRed)
                        }
                        Some(ExpandErrorsResult::Pass) => ("✔", Style::SuccessGreen),
                    };
                    let line = format!("{} {}", exp.x.to_user_string(&ctx.global), status);
                    (vec![line], style)
                }
                LineKind::Explanation(explanation) => (vec![explanation.clone()], Style::FailRed),
            };

            for d in l.iter() {
                add_indent(&mut b, &group_bars, line.indent);

                match style {
                    Style::FailRed => {
                        b.push(console::style(&d).bright().red().to_string());
                    }
                    Style::SuccessGreen => {
                        b.push(console::style(&d).bright().blue().to_string());
                    }
                    Style::Normal => {
                        b.push(d.clone());
                    }
                }
            }

            b.push("\n".into());

            // start a group if necessary
            if matches!(
                &line.kind,
                LineKind::Intro(
                    Introduction::UnfoldFunctionDef(..) | Introduction::SplitEquality(..)
                ) | LineKind::Leaf(..)
            ) {
                if i + 1 < self.output.len()
                    && self.output[i + 1].indent > line.indent
                    && !matches!(self.output[i + 1].kind, LineKind::Explanation(..))
                {
                    group_bars.push(line.indent as usize);
                }
            }
        }
        close_up_group_bars(&mut b, &mut group_bars, 0);

        b.join("")
    }

    fn get_line_style(&self, i: usize) -> Style {
        let indent = self.output[i].indent;
        let mut j = i + 1;

        let mut all_ok = true;
        while j < self.output.len() && self.output[j].indent > indent {
            if let LineKind::Leaf(id, _) = &self.output[j].kind {
                match self.results.get(id) {
                    None => {
                        all_ok = false;
                    }
                    Some(
                        ExpandErrorsResult::Fail
                        | ExpandErrorsResult::PresumedFail
                        | ExpandErrorsResult::Timeout,
                    ) => {
                        return Style::FailRed;
                    }
                    Some(ExpandErrorsResult::Pass) => {}
                }
            }
            j += 1;
        }
        if all_ok { Style::SuccessGreen } else { Style::Normal }
    }

    pub fn has_strange_result(&self) -> bool {
        for (id, result) in self.results.iter() {
            let needs_check = match result {
                ExpandErrorsResult::Fail | ExpandErrorsResult::Timeout => true,
                ExpandErrorsResult::Pass | ExpandErrorsResult::PresumedFail => false,
            };
            if needs_check {
                if let Some((expansion_tree, _)) = self.expansions.get(id) {
                    let num_leaves = expansion_tree.count_leaves();
                    if self.all_direct_children_succeed(id, num_leaves) {
                        return true;
                    }
                }
            }
        }
        false
    }

    fn all_direct_children_succeed(&self, id: &AssertId, num_leaves: u64) -> bool {
        for i in 0..num_leaves {
            let child_id = cons_id(id, i);
            if self.results.get(&child_id) != Some(&ExpandErrorsResult::Pass) {
                return false;
            }
        }
        true
    }

    fn get_span_for(&self, assert_id: &AssertId) -> vir::messages::Span {
        let parent = Arc::new(assert_id[..assert_id.len() - 1].to_vec());
        let tree = &self.expansions[&parent].0;
        tree.get_exp_for_assert_id(assert_id).unwrap().span.clone()
    }

    pub fn get_output_as_message(
        &self,
        ctx: &Ctx,
        error_format: Option<ErrorOutputType>,
    ) -> air::messages::ArcDynMessage {
        let s = if matches!(
            error_format,
            Some(rustc_session::config::ErrorOutputType::HumanReadable(
                rustc_errors::emitter::HumanReadableErrorType::Short(_)
            ))
        ) {
            "diagnostics via expansion".into()
        } else {
            let mut s = self.get_output(ctx);

            if self.has_strange_result() {
                s += r###"
    NOTE: Verus failed to prove an assertion even though all of its
    sub-assertions succeeded. This is usually unexpected, and it may
    indicate that the proof is "flaky". It might also be a result
    of additional expressions in the triggering context in the expanded
    version."###
            }

            s
        };

        let mut note = vir::messages::note_bare(s);
        for (span, _) in self.spans.iter() {
            note = note.primary_span(span);
        }

        use vir::messages::ToAny;
        note.to_any()
    }
}
