//! Clippy's lints, over rust-analyzer's bodies and their inference. The lints of a body are
//! one query, so the database reruns them only for a body an edit changed, or whose
//! inference changed. A finding names expressions and patterns, not places in a file: an
//! edit above a function keeps its findings.

use std::sync::atomic::{AtomicUsize, Ordering};

use hir_def::{
    DefWithBodyId, FunctionId, ItemContainerId, Lookup,
    attrs::AttrFlags,
    expr_store::Body,
    hir::{
        ArithOp, BinaryOp, CmpOp, Expr, ExprId, Literal, LogicOp, Ordering as Order, Pat, PatId,
        Statement,
    },
    signatures::FunctionSignature,
};

use rustc_type_ir::inherent::IntoKind as _;

use crate::{
    InferenceResult,
    db::HirDatabase,
    next_solver::{Ty, TyKind},
};

/// How many bodies were linted since the process started, for a client to see how much an
/// edit had linted again.
pub static LINTED: AtomicUsize = AtomicUsize::new(0);

/// What a lint found, and the expressions its message and suggestion are made of.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lint {
    /// `x == true` and the like, of `operand` against the literal `against`.
    BoolComparison { at: ExprId, operand: ExprId, equal: bool, against: bool },
    /// The two operands of `op` are the same expression, with no call in it.
    EqOp { at: ExprId, op: &'static str },
    /// `x + 0`, `x * 1` and the like, which are `operand`.
    IdentityOp { at: ExprId, operand: ExprId },
    /// A `return` that is the last thing the function does.
    NeedlessReturn { at: ExprId },
    /// `x.len() == 0` and the like, of `receiver`, for a type that has `is_empty`.
    LenZero { at: ExprId, receiver: ExprId, empty: bool, one: bool },
    /// `let x = f();` where `f()` is `()`.
    LetUnitValue { at: PatId },
    /// `a = a`.
    SelfAssignment { at: ExprId, target: ExprId },
    /// `if c { true } else { false }`, or both branches the same literal.
    NeedlessBool { at: ExprId, condition: ExprId, negated: bool, always: Option<bool> },
}

impl Lint {
    /// Clippy's name of it.
    pub fn name(&self) -> &'static str {
        match self {
            Lint::BoolComparison { .. } => "bool_comparison",
            Lint::EqOp { .. } => "eq_op",
            Lint::IdentityOp { .. } => "identity_op",
            Lint::NeedlessReturn { .. } => "needless_return",
            Lint::LenZero { .. } => "len_zero",
            Lint::LetUnitValue { .. } => "let_unit_value",
            Lint::SelfAssignment { .. } => "self_assignment",
            Lint::NeedlessBool { .. } => "needless_bool",
        }
    }

    /// The group clippy has it in, which decides how it is reported unless told otherwise.
    pub fn group(&self) -> &'static str {
        match self {
            Lint::EqOp { .. } | Lint::SelfAssignment { .. } => "correctness",
            Lint::NeedlessReturn { .. } | Lint::LenZero { .. } | Lint::LetUnitValue { .. } => {
                "style"
            }
            Lint::BoolComparison { .. } | Lint::IdentityOp { .. } | Lint::NeedlessBool { .. } => {
                "complexity"
            }
        }
    }
}

/// The lints of the body of `owner`.
#[salsa::tracked(returns(ref))]
pub fn body_lints(db: &dyn HirDatabase, owner: DefWithBodyId) -> Box<[Lint]> {
    LINTED.fetch_add(1, Ordering::Relaxed);
    let body = Body::of(db, owner);
    let infer = InferenceResult::of(db, owner);
    let linting = Linting { db, body: &body, infer, owner, found: Vec::new() };
    linting.all().into_boxed_slice()
}

struct Linting<'a, 'db> {
    db: &'db dyn HirDatabase,
    body: &'a Body,
    infer: &'db InferenceResult<'db>,
    owner: DefWithBodyId,
    found: Vec<Lint>,
}

impl<'db> Linting<'_, 'db> {
    fn all(mut self) -> Vec<Lint> {
        let function = match self.owner {
            DefWithBodyId::FunctionId(it) => Some(it),
            _ => None,
        };
        let test = function
            .is_some_and(|it| AttrFlags::query(self.db, it.into()).contains(AttrFlags::IS_TEST));
        let signature = function.map(|it| FunctionSignature::of(self.db, it));
        let named = |name: &str| signature.as_ref().is_some_and(|it| it.name.as_str() == name);
        let mut else_ifs = Vec::new();
        for (at, expr) in self.body.exprs() {
            match *expr {
                Expr::BinaryOp { lhs, rhs, op: Some(op) } => {
                    self.bool_comparison(at, lhs, rhs, op);
                    if !test {
                        self.eq_op(at, lhs, rhs, op);
                    }
                    self.identity_op(at, lhs, rhs, op);
                    if !named("is_empty") {
                        self.len_zero(at, lhs, rhs, op);
                    }
                }
                Expr::Assignment { target, value } => self.self_assignment(at, target, value),
                Expr::Block { ref statements, .. } => self.let_unit_value(statements),
                Expr::If { condition, then_branch, else_branch: Some(other) } => {
                    if matches!(self.body[other], Expr::If { .. }) {
                        else_ifs.push(other);
                    }
                    self.needless_bool(at, condition, then_branch, other);
                }
                _ => {}
            }
        }
        self.found
            .retain(|it| !matches!(it, Lint::NeedlessBool { at, .. } if else_ifs.contains(at)));
        if signature.is_some_and(|it| !it.is_async()) {
            self.needless_return(self.body.root_expr());
        }
        self.found
    }

    fn ty(&self, expr: ExprId) -> Ty<'db> {
        self.infer.expr_ty(expr)
    }

    fn bool_literal(&self, expr: ExprId) -> Option<bool> {
        match self.body[expr] {
            Expr::Literal(Literal::Bool(it)) => Some(it),
            _ => None,
        }
    }

    fn int_literal(&self, expr: ExprId) -> Option<i128> {
        match self.body[expr] {
            Expr::Literal(Literal::Int(it, _)) => Some(it),
            Expr::Literal(Literal::Uint(it, _)) => i128::try_from(it).ok(),
            _ => None,
        }
    }

    fn is_int(&self, expr: ExprId) -> bool {
        matches!(self.ty(expr).kind(), TyKind::Int(_) | TyKind::Uint(_))
    }

    fn bool_comparison(&mut self, at: ExprId, lhs: ExprId, rhs: ExprId, op: BinaryOp) {
        let BinaryOp::CmpOp(CmpOp::Eq { negated }) = op else { return };
        let (operand, against) = match (self.bool_literal(lhs), self.bool_literal(rhs)) {
            (None, Some(it)) => (lhs, it),
            (Some(it), None) => (rhs, it),
            _ => return,
        };
        if matches!(self.ty(operand).kind(), TyKind::Bool) {
            self.found.push(Lint::BoolComparison { at, operand, equal: !negated, against });
        }
    }

    fn eq_op(&mut self, at: ExprId, lhs: ExprId, rhs: ExprId, op: BinaryOp) {
        let op = match op {
            BinaryOp::CmpOp(CmpOp::Eq { negated: false }) => "==",
            BinaryOp::CmpOp(CmpOp::Eq { negated: true }) => "!=",
            BinaryOp::CmpOp(CmpOp::Ord { ordering: Order::Less, strict: true }) => "<",
            BinaryOp::CmpOp(CmpOp::Ord { ordering: Order::Less, strict: false }) => "<=",
            BinaryOp::CmpOp(CmpOp::Ord { ordering: Order::Greater, strict: true }) => ">",
            BinaryOp::CmpOp(CmpOp::Ord { ordering: Order::Greater, strict: false }) => ">=",
            BinaryOp::LogicOp(LogicOp::And) => "&&",
            BinaryOp::LogicOp(LogicOp::Or) => "||",
            BinaryOp::ArithOp(ArithOp::BitAnd) => "&",
            BinaryOp::ArithOp(ArithOp::BitOr) => "|",
            BinaryOp::ArithOp(ArithOp::BitXor) => "^",
            BinaryOp::ArithOp(ArithOp::Sub) => "-",
            BinaryOp::ArithOp(ArithOp::Div) => "/",
            _ => return,
        };
        // `x != x` is how a float says it is NaN.
        if matches!(self.ty(lhs).kind(), TyKind::Float(_)) {
            return;
        }
        if self.same(lhs, rhs) && self.names_a_place(lhs) {
            self.found.push(Lint::EqOp { at, op });
        }
    }

    /// Whether the two are the same expression, with nothing in them that could give
    /// another value the second time: no call, no block.
    fn same(&self, a: ExprId, b: ExprId) -> bool {
        match (&self.body[a], &self.body[b]) {
            (Expr::Path(a), Expr::Path(b)) => a == b,
            (Expr::Literal(a), Expr::Literal(b)) => a == b,
            (Expr::Field { expr: a, name: x }, Expr::Field { expr: b, name: y }) => {
                x == y && self.same(*a, *b)
            }
            (Expr::UnaryOp { expr: a, op: x }, Expr::UnaryOp { expr: b, op: y }) => {
                x == y && self.same(*a, *b)
            }
            (
                Expr::Ref { expr: a, mutability: x, .. },
                Expr::Ref { expr: b, mutability: y, .. },
            ) => x == y && self.same(*a, *b),
            (
                Expr::BinaryOp { lhs: a, rhs: c, op: x },
                Expr::BinaryOp { lhs: b, rhs: d, op: y },
            ) => x == y && self.same(*a, *b) && self.same(*c, *d),
            (Expr::Index { base: a, index: c }, Expr::Index { base: b, index: d }) => {
                self.same(*a, *b) && self.same(*c, *d)
            }
            _ => false,
        }
    }

    /// Whether a path is in it: two literals that are the same are left alone.
    fn names_a_place(&self, expr: ExprId) -> bool {
        let mut found = matches!(self.body[expr], Expr::Path(_));
        self.body.walk_child_exprs(expr, |it| found |= self.names_a_place(it));
        found
    }

    fn identity_op(&mut self, at: ExprId, lhs: ExprId, rhs: ExprId, op: BinaryOp) {
        let BinaryOp::ArithOp(op) = op else { return };
        if !self.is_int(at) {
            return;
        }
        let (left, right) = (self.int_literal(lhs), self.int_literal(rhs));
        let operand = match (op, left, right) {
            (ArithOp::Add | ArithOp::BitOr | ArithOp::BitXor, Some(0), None) => rhs,
            (
                ArithOp::Add
                | ArithOp::Sub
                | ArithOp::BitOr
                | ArithOp::BitXor
                | ArithOp::Shl
                | ArithOp::Shr,
                None,
                Some(0),
            ) => lhs,
            (ArithOp::Mul, Some(1), None) => rhs,
            (ArithOp::Mul | ArithOp::Div, None, Some(1)) => lhs,
            _ => return,
        };
        if self.ty(operand) == self.ty(at) {
            self.found.push(Lint::IdentityOp { at, operand });
        }
    }

    fn len_zero(&mut self, at: ExprId, lhs: ExprId, rhs: ExprId, op: BinaryOp) {
        let BinaryOp::CmpOp(op) = op else { return };
        let (call, number, len_first) = match (self.int_literal(lhs), self.int_literal(rhs)) {
            (None, Some(it)) => (lhs, it, true),
            (Some(it), None) => (rhs, it, false),
            _ => return,
        };
        let Expr::MethodCall { receiver, ref method_name, ref args, .. } = self.body[call] else {
            return;
        };
        if method_name.as_str() != "len" || !args.is_empty() || !self.has_is_empty(call) {
            return;
        }
        let greater = |ordering| match ordering {
            Order::Greater => len_first,
            Order::Less => !len_first,
        };
        let (empty, one) = match (op, number) {
            (CmpOp::Eq { negated }, 0) => (!negated, false),
            (CmpOp::Ord { ordering, strict: true }, 0) if greater(ordering) => (false, false),
            (CmpOp::Ord { ordering, strict: false }, 1) if greater(ordering) => (false, true),
            (CmpOp::Ord { ordering, strict: true }, 1) if !greater(ordering) => (true, true),
            _ => return,
        };
        self.found.push(Lint::LenZero { at, receiver, empty, one });
    }

    /// Whether the `len` that `call` calls is beside an `is_empty` of no arguments in the same
    /// `impl`.
    fn has_is_empty(&self, call: ExprId) -> bool {
        let Some((len, _)) = self.infer.method_resolution(call) else { return false };
        let ItemContainerId::ImplId(imp) = len.lookup(self.db).container else { return false };
        imp.impl_items(self.db).items.iter().any(|(name, item)| match *item {
            hir_def::AssocItemId::FunctionId(it) => {
                name.as_str() == "is_empty" && FunctionSignature::of(self.db, it).params.len() == 1
            }
            _ => false,
        })
    }

    fn let_unit_value(&mut self, statements: &[Statement]) {
        for statement in statements {
            let Statement::Let { pat, initializer: Some(init), else_branch: None, .. } = *statement
            else {
                continue;
            };
            if !matches!(self.body[pat], Pat::Bind { subpat: None, .. }) {
                continue;
            }
            if self.ty(init).is_unit() && self.surely_unit(init) {
                self.found.push(Lint::LetUnitValue { at: pat });
            }
        }
    }

    /// Whether `init` is `()` whatever its context: not a call of a function whose type
    /// is `()` only because of what it was bound to.
    fn surely_unit(&self, init: ExprId) -> bool {
        let declared_unit = |func: FunctionId| {
            let signature = FunctionSignature::of(self.db, func);
            signature.ret_type.is_none() && signature.generic_params.is_empty()
        };
        match self.body[init] {
            Expr::MethodCall { .. } => {
                self.infer.method_resolution(init).is_some_and(|(it, _)| declared_unit(it))
            }
            Expr::Call { callee, .. } => match self.ty(callee).kind() {
                TyKind::FnDef(def, _) => match def.0 {
                    crate::CallableDefId::FunctionId(it) => declared_unit(it),
                    _ => false,
                },
                _ => false,
            },
            Expr::Assignment { .. } | Expr::Tuple { .. } => true,
            _ => false,
        }
    }

    fn self_assignment(&mut self, at: ExprId, target: PatId, value: ExprId) {
        let same = match (&self.body[target], &self.body[value]) {
            (Pat::Path(a), Expr::Path(b)) => a == b,
            (Pat::Expr(a), _) => self.same(*a, value) && self.names_a_place(*a),
            _ => false,
        };
        if same {
            let target = match self.body[target] {
                Pat::Expr(it) => it,
                _ => value,
            };
            self.found.push(Lint::SelfAssignment { at, target });
        }
    }

    fn needless_bool(&mut self, at: ExprId, condition: ExprId, then: ExprId, other: ExprId) {
        let literal_block = |expr: ExprId| match self.body[expr] {
            Expr::Block { ref statements, tail: Some(tail), label: None, .. }
                if statements.is_empty() =>
            {
                self.bool_literal(tail)
            }
            _ => None,
        };
        let (Some(then), Some(other)) = (literal_block(then), literal_block(other)) else {
            return;
        };
        let always = (then == other).then_some(then);
        self.found.push(Lint::NeedlessBool { at, condition, negated: !then, always });
    }

    /// Looks for a `return` at the end of `expr`, which is what the function ends with.
    fn needless_return(&mut self, expr: ExprId) {
        match self.body[expr] {
            Expr::Block { ref statements, tail, label: None, .. } => match tail {
                Some(tail) => self.needless_return(tail),
                None => {
                    if let Some(Statement::Expr { expr, .. }) = statements.last() {
                        self.needless_return(*expr);
                    }
                }
            },
            Expr::Return { expr: Some(value) } if !self.never_returns(value) => {
                self.found.push(Lint::NeedlessReturn { at: expr });
            }
            Expr::Return { expr: None } => self.found.push(Lint::NeedlessReturn { at: expr }),
            Expr::If { then_branch, else_branch: Some(other), .. } => {
                self.needless_return(then_branch);
                self.needless_return(other);
            }
            Expr::Match { ref arms, .. } => {
                for arm in arms {
                    self.needless_return(arm.expr);
                }
            }
            _ => {}
        }
    }

    fn never_returns(&self, expr: ExprId) -> bool {
        matches!(self.ty(expr).kind(), TyKind::Never)
    }
}
