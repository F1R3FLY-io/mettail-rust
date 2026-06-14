//! `lower_language_def` — the M-RHO.0.3 spec→Rholang AST lowering of a MeTTaIL
//! `LanguageDef`'s scalar reduction rules to normalized f1r3node `Par`
//! `contract`s.
//!
//! Each scalar operator rule whose operand types, result type, and concrete
//! syntax have an exact Rholang `Expr` equivalent lowers to a normalized
//! Rholang AST equivalent to
//! `contract @"<Label>"(@a, @b, ret) = { ret!(a <op> b) }`. The Rholang-looking
//! string is kept only as a human-readable annotation; execution feeds the AST
//! directly to `RhoRuntime::inj`. Every other rule (BigInt/BigRat/Fixed/Float/
//! UInt32 ops, casts, `Err`/`Proc` injections, collections, ternary, factorial,
//! power, bitwise, …) is NOT silently dropped — it is recorded in
//! [`RhoLowering::rejected`]. This is the "miss nothing" discipline at the
//! codegen layer (cf.
//! `formal/rocq/rho_bridge/theories/RhoLoweringTotalOrRejects.v`): every rule in
//! `def.terms` is accounted for — exactly one of lowered / rejected.
//!
//! Semantic equivalence for this scalar subset is checked by the M-RHO.0.4
//! differential oracle against the Ascent evaluator. This module establishes a
//! well-formed normalized-AST lowering plus the totality/no-loss guarantee.

use mettail_ast::grammar::{GrammarRule, SyntaxExpr, TermParam};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::TypeExpr;
use models::create_bit_vector;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{
    EAnd, EDiv, EEq, EGt, EGte, ELt, ELte, EMinus, EMod, EMult, ENeg, ENeq, ENot, EOr, EPlus,
    EPlusPlus, Expr, Par, Receive, ReceiveBind,
};
use models::rust::utils::{new_boundvar_par, new_freevar_par, new_gstring_par, new_send_par};

use crate::deadlock::{
    analyze_channel_deadlocks, ChannelDeadlockReport, ChannelNetwork, ContractFlow,
};

/// Executable artifact family for the Rho backend.
///
/// `NormalizedAst` is the implementation available today. The enum is
/// non-exhaustive so the future f1r3node bytecode artifact can be added without
/// making source text the boundary again.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RhoArtifactKind {
    NormalizedAst,
}

/// Bytecode-ready backend artifact for Rho execution.
///
/// The current concrete representation is a normalized `rhoapi::Par` AST because
/// that is what f1r3node's interpreter consumes today. Future bytecode support
/// can add a new variant without changing the fact that source text is not the
/// execution boundary.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq)]
pub enum RhoProgram {
    Ast(RhoAstProgram),
}

impl RhoProgram {
    pub fn artifact_kind(&self) -> RhoArtifactKind {
        match self {
            Self::Ast(_) => RhoArtifactKind::NormalizedAst,
        }
    }

    /// Normalized AST to inject into the host Rho runtime, when this artifact is
    /// represented as `Par`.
    pub fn ast_par(&self) -> Option<&Par> {
        match self {
            Self::Ast(program) => Some(program.par()),
        }
    }

    /// Reader/debug annotation. This text is not parsed as the execution path.
    pub fn text_annotation(&self) -> &str {
        match self {
            Self::Ast(program) => program.text_annotation(),
        }
    }
}

/// Current concrete Rho program representation: normalized `Par` plus a
/// Rholang-looking annotation for people reading logs, docs, or test failures.
#[derive(Debug, Clone, PartialEq)]
pub struct RhoAstProgram {
    pub(crate) par: Par,
    pub(crate) text_annotation: String,
}

impl RhoAstProgram {
    pub(crate) fn new(par: Par, text_annotation: String) -> Self {
        Self { par, text_annotation }
    }

    pub fn par(&self) -> &Par {
        &self.par
    }

    /// Reader/debug annotation. This text is not parsed as the execution path.
    pub fn text_annotation(&self) -> &str {
        &self.text_annotation
    }
}

/// The result of lowering a `LanguageDef` to Rholang: the executable normalized
/// `program`, the rule labels that were `lowered` to contracts, and the labels
/// explicitly `rejected` (out of the supported scalar-operator subset). Every
/// rule of `def.terms` appears in exactly one of `lowered` / `rejected`.
#[derive(Debug, Clone, PartialEq)]
pub struct RhoLowering {
    pub(crate) program: RhoProgram,
    pub lowered: Vec<String>,
    pub rejected: Vec<String>,
    pub deadlock_report: ChannelDeadlockReport,
}

impl RhoLowering {
    /// Lowered backend artifact. This is exposed for inspection and validation;
    /// generated execution should consume `ValidatedRhoProgram`.
    pub fn program(&self) -> &RhoProgram {
        &self.program
    }

    pub fn artifact_kind(&self) -> RhoArtifactKind {
        self.program.artifact_kind()
    }

    /// Normalized AST to inject into the host Rho runtime, when available.
    pub fn ast_par(&self) -> Option<&Par> {
        self.program.ast_par()
    }

    /// Reader/debug annotation. This text is not parsed as the execution path.
    pub fn text_annotation(&self) -> &str {
        self.program.text_annotation()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RhoBinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Neq,
    Lt,
    Gt,
    Lte,
    Gte,
    And,
    Or,
    Concat,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RhoScalarTy {
    Int,
    Bool,
    Str,
}

impl RhoBinaryOp {
    fn symbol(self) -> &'static str {
        match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
            Self::Div => "/",
            Self::Mod => "%",
            Self::Eq => "==",
            Self::Neq => "!=",
            Self::Lt => "<",
            Self::Gt => ">",
            Self::Lte => "<=",
            Self::Gte => ">=",
            Self::And => "and",
            Self::Or => "or",
            Self::Concat => "++",
        }
    }

    fn expr(self, lhs: Par, rhs: Par) -> ExprInstance {
        match self {
            Self::Add => ExprInstance::EPlusBody(EPlus { p1: Some(lhs), p2: Some(rhs) }),
            Self::Sub => ExprInstance::EMinusBody(EMinus { p1: Some(lhs), p2: Some(rhs) }),
            Self::Mul => ExprInstance::EMultBody(EMult { p1: Some(lhs), p2: Some(rhs) }),
            Self::Div => ExprInstance::EDivBody(EDiv { p1: Some(lhs), p2: Some(rhs) }),
            Self::Mod => ExprInstance::EModBody(EMod { p1: Some(lhs), p2: Some(rhs) }),
            Self::Eq => ExprInstance::EEqBody(EEq { p1: Some(lhs), p2: Some(rhs) }),
            Self::Neq => ExprInstance::ENeqBody(ENeq { p1: Some(lhs), p2: Some(rhs) }),
            Self::Lt => ExprInstance::ELtBody(ELt { p1: Some(lhs), p2: Some(rhs) }),
            Self::Gt => ExprInstance::EGtBody(EGt { p1: Some(lhs), p2: Some(rhs) }),
            Self::Lte => ExprInstance::ELteBody(ELte { p1: Some(lhs), p2: Some(rhs) }),
            Self::Gte => ExprInstance::EGteBody(EGte { p1: Some(lhs), p2: Some(rhs) }),
            Self::And => ExprInstance::EAndBody(EAnd { p1: Some(lhs), p2: Some(rhs) }),
            Self::Or => ExprInstance::EOrBody(EOr { p1: Some(lhs), p2: Some(rhs) }),
            Self::Concat => ExprInstance::EPlusPlusBody(EPlusPlus { p1: Some(lhs), p2: Some(rhs) }),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RhoUnaryOp {
    Not,
    Neg,
}

impl RhoUnaryOp {
    fn symbol(self) -> &'static str {
        match self {
            Self::Not => "not",
            Self::Neg => "-",
        }
    }

    fn expr(self, arg: Par) -> ExprInstance {
        match self {
            Self::Not => ExprInstance::ENotBody(ENot { p: Some(arg) }),
            Self::Neg => ExprInstance::ENegBody(ENeg { p: Some(arg) }),
        }
    }
}

struct LoweredRule {
    contract: Par,
    text_annotation: String,
}

/// Map a typed infix scalar rule to its Rholang binary operator, if Rholang has
/// an exact `Expr` equivalent for that type family.
///
/// The type check is part of correctness, not just validation. For example,
/// Rholang `+` is integer addition only, while MeTTaIL Calculator also has
/// `Str "+" Str`; that string rule must lower to Rholang `++`, not integer
/// `EPlus`.
fn rho_binop(
    terminal: &str,
    lhs: RhoScalarTy,
    rhs: RhoScalarTy,
    result: RhoScalarTy,
) -> Option<RhoBinaryOp> {
    use RhoScalarTy::{Bool, Int, Str};

    if lhs != rhs {
        return None;
    }

    match (terminal, lhs, result) {
        ("+", Int, Int) => Some(RhoBinaryOp::Add),
        ("+", Str, Str) => Some(RhoBinaryOp::Concat),
        ("-", Int, Int) => Some(RhoBinaryOp::Sub),
        ("*", Int, Int) => Some(RhoBinaryOp::Mul),
        ("/", Int, Int) => Some(RhoBinaryOp::Div),
        ("%", Int, Int) => Some(RhoBinaryOp::Mod),
        ("==", Int | Bool | Str, Bool) => Some(RhoBinaryOp::Eq),
        ("!=", Int | Bool | Str, Bool) => Some(RhoBinaryOp::Neq),
        ("<", Int | Bool | Str, Bool) => Some(RhoBinaryOp::Lt),
        (">", Int | Bool | Str, Bool) => Some(RhoBinaryOp::Gt),
        ("<=", Int | Bool | Str, Bool) => Some(RhoBinaryOp::Lte),
        (">=", Int | Bool | Str, Bool) => Some(RhoBinaryOp::Gte),
        ("and", Bool, Bool) => Some(RhoBinaryOp::And),
        ("or", Bool, Bool) => Some(RhoBinaryOp::Or),
        ("++", Str, Str) => Some(RhoBinaryOp::Concat),
        _ => None,
    }
}

/// Map a typed prefix scalar rule to its Rholang unary operator, if any.
fn rho_unop(terminal: &str, arg: RhoScalarTy, result: RhoScalarTy) -> Option<RhoUnaryOp> {
    match (terminal, arg, result) {
        ("not", RhoScalarTy::Bool, RhoScalarTy::Bool) => Some(RhoUnaryOp::Not),
        ("-", RhoScalarTy::Int, RhoScalarTy::Int) => Some(RhoUnaryOp::Neg),
        _ => None,
    }
}

/// The Rholang-native scalar corresponding to a MeTTaIL type.
fn rho_native_scalar_type(ty: &TypeExpr) -> Option<RhoScalarTy> {
    match ty {
        TypeExpr::Base(id) => match id.to_string().as_str() {
            "Int" => Some(RhoScalarTy::Int),
            "Bool" => Some(RhoScalarTy::Bool),
            "Str" => Some(RhoScalarTy::Str),
            _ => None,
        },
        _ => None,
    }
}

/// The Rholang-native scalar corresponding to a simple parameter.
///
/// BigInt/BigRat/Fixed/Float/UInt32 and any non-`Simple`
/// (binder/guard/optional) parameter are NOT native — lowering their operators
/// to Rholang scalar `Expr`s would be semantically wrong, so such rules are
/// rejected and surfaced to the coverage gate.
fn param_rho_native_scalar(p: &TermParam) -> Option<RhoScalarTy> {
    match p {
        TermParam::Simple { ty, .. } => rho_native_scalar_type(ty),
        _ => None,
    }
}

fn result_rho_native_scalar(rule: &GrammarRule) -> Option<RhoScalarTy> {
    match rule.category.to_string().as_str() {
        "Int" => Some(RhoScalarTy::Int),
        "Bool" => Some(RhoScalarTy::Bool),
        "Str" => Some(RhoScalarTy::Str),
        _ => None,
    }
}

fn bitvec(indices: &[usize]) -> Vec<u8> {
    if indices.is_empty() {
        Vec::new()
    } else {
        create_bit_vector(indices)
    }
}

fn binding_bitvec(bind_count: usize) -> Vec<u8> {
    bitvec(&(0..bind_count).collect::<Vec<_>>())
}

fn bound_formal(total_formals: usize, formal_index: usize) -> Par {
    debug_assert!(formal_index < total_formals);
    new_boundvar_par((total_formals - 1 - formal_index) as i32, Vec::new(), false)
}

fn expr_par(expr_instance: ExprInstance, locally_free_indices: &[usize]) -> Par {
    let mut par = Par::default().with_exprs(vec![Expr { expr_instance: Some(expr_instance) }]);
    par.locally_free = bitvec(locally_free_indices);
    par
}

fn contract_ast(
    label: &str,
    formal_count: usize,
    result_expr: Par,
    text_annotation: String,
) -> LoweredRule {
    let all_formals = binding_bitvec(formal_count);
    let body = new_send_par(
        bound_formal(formal_count, formal_count - 1),
        vec![result_expr],
        false,
        all_formals.clone(),
        false,
        all_formals.clone(),
        false,
    );
    let receive = Receive {
        binds: vec![ReceiveBind {
            patterns: (0..formal_count)
                .map(|i| new_freevar_par(i as i32, Vec::new()))
                .collect(),
            source: Some(new_gstring_par(label.to_string(), Vec::new(), false)),
            remainder: None,
            free_count: formal_count as i32,
        }],
        body: Some(body),
        persistent: true,
        peek: false,
        bind_count: formal_count as i32,
        locally_free: Vec::new(),
        connective_used: false,
        condition: None,
    };
    LoweredRule {
        contract: Par::default().with_receives(vec![receive]),
        text_annotation,
    }
}

/// Lower one rule to a normalized Rholang contract, or `None` if it is out of the supported
/// scalar-operator subset (→ to be recorded as rejected, never dropped).
fn lower_rule(rule: &GrammarRule) -> Option<LoweredRule> {
    let pattern = rule.syntax_pattern.as_ref()?;
    // Only lower rules whose operands and result have an exact Rholang scalar
    // interpretation. Keying on the terminal alone would mis-lower e.g.
    // `AddBigInt` (`a:BigInt "+" b`) or `AddStr` as integer `EPlus`.
    let ctx = rule.term_context.as_ref()?;
    if ctx.is_empty() {
        return None;
    }
    let result_ty = result_rho_native_scalar(rule)?;
    let label = rule.label.to_string();
    match pattern.as_slice() {
        // Binary infix: `a <op> b` → contract @"L"(@a, @b, ret) = { ret!(a <op> b) }
        [SyntaxExpr::Param(a), SyntaxExpr::Literal(op), SyntaxExpr::Param(b)] => {
            let [lhs_param, rhs_param] = ctx.as_slice() else {
                return None;
            };
            let lhs_ty = param_rho_native_scalar(lhs_param)?;
            let rhs_ty = param_rho_native_scalar(rhs_param)?;
            let rop = rho_binop(op, lhs_ty, rhs_ty, result_ty)?;
            let formal_count = 3;
            let lhs = bound_formal(formal_count, 0);
            let rhs = bound_formal(formal_count, 1);
            let result_expr = expr_par(rop.expr(lhs, rhs), &[1, 2]);
            let text_annotation = format!(
                "contract @\"{label}\"(@{a}, @{b}, ret) = {{ ret!({a} {} {b}) }}",
                rop.symbol()
            );
            Some(contract_ast(&label, formal_count, result_expr, text_annotation))
        },
        // Unary prefix: `<op> a` → contract @"L"(@a, ret) = { ret!(<op> a) }
        [SyntaxExpr::Literal(op), SyntaxExpr::Param(a)] => {
            let [arg_param] = ctx.as_slice() else {
                return None;
            };
            let arg_ty = param_rho_native_scalar(arg_param)?;
            let rop = rho_unop(op, arg_ty, result_ty)?;
            let formal_count = 2;
            let arg = bound_formal(formal_count, 0);
            let result_expr = expr_par(rop.expr(arg), &[1]);
            let text_annotation =
                format!("contract @\"{label}\"(@{a}, ret) = {{ ret!({} {a}) }}", rop.symbol());
            Some(contract_ast(&label, formal_count, result_expr, text_annotation))
        },
        _ => None,
    }
}

/// Lower every scalar reduction rule of `def` to a Rholang program. Supported
/// operator rules become parallel `contract`s; all other rules are recorded in
/// `rejected` (the "miss nothing" guarantee — nothing is silently dropped).
pub fn lower_language_def(def: &LanguageDef) -> RhoLowering {
    let mut lowered = Vec::new();
    let mut rejected = Vec::new();
    let mut program = Par::default();
    let mut annotations = Vec::new();
    let mut network = ChannelNetwork::new();
    for rule in &def.terms {
        match lower_rule(rule) {
            Some(lowered_rule) => {
                let label = rule.label.to_string();
                lowered.push(label.clone());
                program = program.append(lowered_rule.contract);
                annotations.push(lowered_rule.text_annotation);
                network = network.with_external(label.clone()).with_contract(
                    ContractFlow::exported_service(label, std::iter::empty::<String>()),
                );
            },
            None => rejected.push(rule.label.to_string()),
        }
    }
    // A Rholang program is a single process; parallel-compose the contracts in
    // the AST. The annotation mirrors that shape for readers only.
    let text_annotation = if annotations.is_empty() {
        "Nil".to_string()
    } else {
        annotations.join(" |\n")
    };
    let deadlock_report = analyze_channel_deadlocks(&network);
    RhoLowering {
        program: RhoProgram::Ast(RhoAstProgram::new(program, text_annotation)),
        lowered,
        rejected,
        deadlock_report,
    }
}
