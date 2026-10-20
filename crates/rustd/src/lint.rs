//! `cargo rustd clippy`, the worker's half: clippy's lints of the bodies of the crates of a
//! program, from [`body_lints`], which the database runs again only for the bodies an edit
//! changed. What it finds is sent to the client as places in files and the text to print.

use std::{path::PathBuf, sync::atomic::Ordering};

use either::Either;
use hir::{Crate, HirFileId, InFile};
use hir_def::{
    expr_store::{Body, BodySourceMap},
    hir::{ExprId, ExprOrPatId},
};
use hir_ty::mir::codegen::lints::{LINTED, Lint, body_lints};
use ide_db::{RootDatabase, Severity, base_db::SourceDatabase as _};
use rustc_hash::FxHashMap;
use serde::{Deserialize, Serialize};
use syntax::{AstNode, SyntaxNode, TextRange, ast};

use crate::Declared;

/// What a worker found in the crates of a program.
#[derive(Serialize, Deserialize, Default)]
pub(crate) struct Linted {
    /// How many bodies the crates have, and how many of them were linted again for this.
    pub(crate) bodies: usize,
    pub(crate) anew: usize,
    pub(crate) findings: Vec<Finding>,
}

#[derive(Serialize, Deserialize, Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(crate) struct Finding {
    pub(crate) path: PathBuf,
    pub(crate) line: usize,
    pub(crate) column: usize,
    /// The root file of the crate it is in, which says which target it is of.
    pub(crate) root: PathBuf,
    pub(crate) lint: String,
    pub(crate) group: String,
    /// The level an attribute in the source gives it, when one does.
    pub(crate) attributed: Option<Level>,
    pub(crate) message: String,
    pub(crate) help: Option<String>,
    /// The line it starts on, and how many of its characters it spans.
    pub(crate) source: String,
    pub(crate) width: usize,
}

#[derive(Serialize, Deserialize, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(crate) enum Level {
    Allow,
    Warn,
    Deny,
}

/// The lints of `crates`, with the files of the workspace at `paths`.
pub(crate) fn linted(
    db: &RootDatabase,
    crates: &[Crate],
    paths: &FxHashMap<vfs::FileId, PathBuf>,
) -> Linted {
    hir::attach_db(db, || {
        let before = LINTED.load(Ordering::Relaxed);
        let mut bodies = Vec::new();
        for &krate in crates {
            let mut declared = Declared::default();
            declared.in_modules(db, krate);
            let root = paths.get(&krate.root_file(db)).cloned().unwrap_or_default();
            bodies.extend(declared.bodies.into_iter().map(|it| (root.clone(), it)));
        }
        let mut findings: Vec<Finding> = bodies
            .iter()
            .flat_map(|(root, owner)| {
                let found = body_lints(db, *owner);
                let (_, source_map) = Body::with_source_map(db, *owner);
                found
                    .iter()
                    .filter_map(|lint| Finding::of(db, source_map, lint, root, paths))
                    .collect::<Vec<_>>()
            })
            .collect();
        findings.sort();
        findings.dedup();
        Linted { bodies: bodies.len(), anew: LINTED.load(Ordering::Relaxed) - before, findings }
    })
}

impl Finding {
    /// Where `lint` is and what to say of it. None for a finding in what a macro wrote,
    /// which clippy leaves alone too.
    fn of(
        db: &RootDatabase,
        source_map: &BodySourceMap,
        lint: &Lint,
        root: &PathBuf,
        paths: &FxHashMap<vfs::FileId, PathBuf>,
    ) -> Option<Finding> {
        let text = |expr: ExprId| {
            let (hir_file, node) = node(db, source_map, expr.into())?;
            let (file, range) = written(db, hir_file, &node)?;
            Some(db.file_text(file).text(db).get(std::ops::Range::<usize>::from(range))?.to_owned())
        };
        let (at, message, help) = match *lint {
            Lint::BoolComparison { at, operand, equal, against } => {
                let operand = text(operand)?;
                let (message, negated) = match (equal, against) {
                    (true, true) => ("equality checks against true are unnecessary", false),
                    (true, false) => {
                        ("equality checks against false can be replaced by a negation", true)
                    }
                    (false, true) => {
                        ("inequality checks against true can be replaced by a negation", true)
                    }
                    (false, false) => ("inequality checks against false are unnecessary", false),
                };
                let shown = if negated { format!("!{operand}") } else { operand };
                (
                    at.into(),
                    message.to_owned(),
                    Some(format!("try simplifying it as shown: `{shown}`")),
                )
            }
            Lint::EqOp { at, op } => {
                (at.into(), format!("equal expressions as operands to `{op}`"), None)
            }
            Lint::IdentityOp { at, operand } => (
                at.into(),
                "this operation has no effect".to_owned(),
                Some(format!("consider reducing it to: `{}`", text(operand)?)),
            ),
            Lint::NeedlessReturn { at } => (
                at.into(),
                "unneeded `return` statement".to_owned(),
                Some("remove `return`".to_owned()),
            ),
            Lint::LenZero { at, receiver, empty, one } => {
                let receiver = text(receiver)?;
                let message =
                    if one { "length comparison to one" } else { "length comparison to zero" };
                let help = match empty {
                    true => format!(
                        "using `is_empty` is clearer and more explicit: `{receiver}.is_empty()`"
                    ),
                    false => format!(
                        "using `!is_empty` is clearer and more explicit: `!{receiver}.is_empty()`"
                    ),
                };
                (at.into(), message.to_owned(), Some(help))
            }
            Lint::LetUnitValue { at } => {
                (at.into(), "this let-binding has unit value".to_owned(), None)
            }
            Lint::SelfAssignment { at, target } => {
                let target = text(target)?;
                (at.into(), format!("self-assignment of `{target}` to `{target}`"), None)
            }
            Lint::NeedlessBool { at, condition, negated, always } => {
                let condition = text(condition)?;
                match always {
                    Some(it) => (
                        at.into(),
                        format!("this if-then-else expression will always return {it}"),
                        None,
                    ),
                    None => {
                        let shown = if negated { format!("!{condition}") } else { condition };
                        (
                            at.into(),
                            "this if-then-else expression returns a bool literal".to_owned(),
                            Some(format!("you can reduce it to: `{shown}`")),
                        )
                    }
                }
            }
        };
        let (hir_file, node) = node(db, source_map, at)?;
        let node = Self::spanned(lint, node);
        let (file, range) = written(db, hir_file, &node)?;
        let warned = matches!(lint.group(), "style" | "complexity" | "suspicious" | "perf");
        let attributed = ide_diagnostics::clippy_lint_attribute(
            db,
            file,
            &InFile::new(hir_file, node.clone()),
            lint.name(),
            warned,
        )
        .map(|it| match it {
            Severity::Allow => Level::Allow,
            Severity::Error => Level::Deny,
            _ => Level::Warn,
        });
        let path = paths.get(&file)?.clone();
        let (line, column, source, width) = place(db, file, range);
        Some(Finding {
            path,
            line,
            column,
            root: root.clone(),
            lint: lint.name().to_owned(),
            group: lint.group().to_owned(),
            attributed,
            message,
            help,
            source,
            width,
        })
    }

    /// What clippy points at: the statement of a `return` or a `let`, the expression
    /// otherwise.
    fn spanned(lint: &Lint, node: SyntaxNode) -> SyntaxNode {
        let statement = match lint {
            Lint::NeedlessReturn { .. } => {
                node.parent().filter(|it| ast::ExprStmt::can_cast(it.kind()))
            }
            Lint::LetUnitValue { .. } => {
                node.ancestors().find(|it| ast::LetStmt::can_cast(it.kind()))
            }
            _ => None,
        };
        statement.unwrap_or(node)
    }
}

/// The node of `at`, in the file or the expansion of a macro it is in.
fn node(
    db: &RootDatabase,
    source_map: &BodySourceMap,
    at: ExprOrPatId,
) -> Option<(HirFileId, SyntaxNode)> {
    let source = match at {
        ExprOrPatId::ExprId(it) => source_map.expr_syntax(it).ok()?,
        ExprOrPatId::PatId(it) => source_map.pat_syntax(it).ok()?,
    };
    let root = source.file_id.parse_or_expand(db);
    let node = match source.value.to_node(&root) {
        Either::Left(it) => it.syntax().clone(),
        Either::Right(it) => it.syntax().clone(),
    };
    Some((source.file_id, node))
}

/// Where in a file `node` is written: none for one a macro wrote, which clippy leaves
/// alone too. What a macro was given, as the arguments of `println!`, is written.
fn written(
    db: &RootDatabase,
    file: HirFileId,
    node: &SyntaxNode,
) -> Option<(vfs::FileId, TextRange)> {
    if let Some(file) = file.file_id() {
        return Some((file.file_id(db), node.text_range()));
    }
    let (range, context) = InFile::new(file, node).original_file_range_opt(db)?;
    context.is_root().then(|| (range.file_id.file_id(db), range.range))
}

/// The line and column `range` starts at, counted from one, the text of that line, and how
/// many of its characters `range` spans.
fn place(db: &RootDatabase, file: vfs::FileId, range: TextRange) -> (usize, usize, String, usize) {
    let text = db.file_text(file).text(db);
    let start = usize::from(range.start()).min(text.len());
    let end = usize::from(range.end()).min(text.len());
    let line_start = text[..start].rfind('\n').map_or(0, |it| it + 1);
    let line_end = text[start..].find('\n').map_or(text.len(), |it| start + it);
    let line = text[..start].matches('\n').count() + 1;
    let column = text[line_start..start].chars().count() + 1;
    let width = text[start..end.min(line_end)].chars().count().max(1);
    (line, column, text[line_start..line_end].to_owned(), width)
}
