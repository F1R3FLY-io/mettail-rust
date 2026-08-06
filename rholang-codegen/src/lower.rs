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
use mettail_ast::identity::language_definition_fingerprint;
use mettail_ast::language::{LanguageDef, NativeKind};
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
    pub(crate) validation_profile: RhoAstValidationProfile,
}

impl RhoAstProgram {
    pub(crate) fn new(par: Par, text_annotation: String) -> Self {
        Self::new_with_profile(par, text_annotation, RhoAstValidationProfile::ScalarContracts)
    }

    pub(crate) fn new_with_profile(
        par: Par,
        text_annotation: String,
        validation_profile: RhoAstValidationProfile,
    ) -> Self {
        Self { par, text_annotation, validation_profile }
    }

    pub fn par(&self) -> &Par {
        &self.par
    }

    /// Reader/debug annotation. This text is not parsed as the execution path.
    pub fn text_annotation(&self) -> &str {
        &self.text_annotation
    }

    pub fn validation_profile(&self) -> RhoAstValidationProfile {
        self.validation_profile
    }
}

/// Shape validator selected for a normalized `rhoapi::Par` artifact.
///
/// Both profiles produce the same executable artifact kind
/// [`RhoArtifactKind::NormalizedAst`]. The profile names the generated shape
/// contract that must be checked before the AST can become a
/// `ValidatedRhoProgram`.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RhoAstValidationProfile {
    /// Persistent scalar operator contracts emitted by `lower_language_def`.
    ScalarContracts,
    /// Memoized call-by-need thunk network emitted by M-RHO.2 need lowering.
    CallByNeedThunk,
}

/// The result of lowering a `LanguageDef` to Rholang: the executable normalized
/// `program`, the rule labels that were `lowered` to contracts, the generated
/// scalar contract ABI for those lowered rules, and the labels explicitly
/// `rejected` (out of the supported scalar-operator subset). Every rule of
/// `def.terms` appears in exactly one of `lowered` / `rejected`.
#[derive(Debug, Clone, PartialEq)]
pub struct RhoLowering {
    pub language_name: String,
    pub definition_fingerprint: String,
    pub(crate) program: RhoProgram,
    pub lowered: Vec<String>,
    /// Call signatures for generated scalar contracts, in the same order as
    /// [`Self::lowered`]. Generated runtime installers consume this inventory
    /// instead of re-creating a hand-maintained list of scalar operations.
    pub scalar_contract_abi: Vec<RhoScalarContractAbi>,
    pub rejected: Vec<String>,
    pub deadlock_report: ChannelDeadlockReport,
}

impl RhoLowering {
    /// Name of the `LanguageDef` that produced this lowering.
    pub fn language_name(&self) -> &str {
        &self.language_name
    }

    /// Stable compiler-facing identity of the `LanguageDef` that produced this
    /// lowering.
    pub fn definition_fingerprint(&self) -> &str {
        &self.definition_fingerprint
    }

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RhoScalarType {
    Int,
    Bool,
    Str,
}

/// ABI shape of a generated Rho scalar contract.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RhoScalarContractShape {
    UnaryPrefix {
        argument: RhoScalarType,
        result: RhoScalarType,
    },
    BinaryInfix {
        left: RhoScalarType,
        right: RhoScalarType,
        result: RhoScalarType,
    },
}

impl RhoScalarContractShape {
    pub fn operand_count(self) -> usize {
        match self {
            Self::UnaryPrefix { .. } => 1,
            Self::BinaryInfix { .. } => 2,
        }
    }

    pub fn formal_count(self) -> usize {
        self.operand_count() + 1
    }

    pub fn return_channel_position(self) -> usize {
        self.operand_count()
    }

    pub fn result_type(self) -> RhoScalarType {
        match self {
            Self::UnaryPrefix { result, .. } | Self::BinaryInfix { result, .. } => result,
        }
    }
}

/// Generated call ABI for a lowered scalar contract.
///
/// Calls send all operands first and the return channel last to
/// `@"rule_label"`. The generated contract body sends one value of
/// `shape.result_type()` on that return channel.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RhoScalarContractAbi {
    pub rule_label: String,
    pub shape: RhoScalarContractShape,
}

impl RhoScalarContractAbi {
    pub fn operand_count(&self) -> usize {
        self.shape.operand_count()
    }

    pub fn formal_count(&self) -> usize {
        self.shape.formal_count()
    }

    pub fn return_channel_position(&self) -> usize {
        self.shape.return_channel_position()
    }

    pub fn result_type(&self) -> RhoScalarType {
        self.shape.result_type()
    }
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
    abi: RhoScalarContractAbi,
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
    lhs: RhoScalarType,
    rhs: RhoScalarType,
    result: RhoScalarType,
) -> Option<RhoBinaryOp> {
    use RhoScalarType::{Bool, Int, Str};

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
fn rho_unop(terminal: &str, arg: RhoScalarType, result: RhoScalarType) -> Option<RhoUnaryOp> {
    match (terminal, arg, result) {
        ("not", RhoScalarType::Bool, RhoScalarType::Bool) => Some(RhoUnaryOp::Not),
        ("-", RhoScalarType::Int, RhoScalarType::Int) => Some(RhoUnaryOp::Neg),
        _ => None,
    }
}

/// The Rholang-native scalar corresponding to a declared MeTTaIL category.
///
/// The category name itself is not semantic. A language may call an `i32`
/// category `Number`, or may declare a structural category named `Int`.
/// Lowering therefore follows the macro-expanded `LanguageDef` inventory and
/// maps only native Rust payload families that the Rho AST boundary can carry
/// exactly.
pub(crate) fn category_rho_native_scalar(
    def: &LanguageDef,
    category: &syn::Ident,
) -> Option<RhoScalarType> {
    let lang_type = def.get_type(category)?;
    let native_type = lang_type.native_type.as_ref()?;
    match NativeKind::from_syn_type(native_type) {
        NativeKind::Int8 | NativeKind::Int16 | NativeKind::Int32 | NativeKind::Int64 => {
            Some(RhoScalarType::Int)
        },
        NativeKind::Bool => Some(RhoScalarType::Bool),
        NativeKind::Str => Some(RhoScalarType::Str),
        _ => None,
    }
}

/// The Rholang-native scalar corresponding to a MeTTaIL type.
pub(crate) fn rho_native_scalar_type(def: &LanguageDef, ty: &TypeExpr) -> Option<RhoScalarType> {
    match ty {
        TypeExpr::Base(id) => category_rho_native_scalar(def, id),
        _ => None,
    }
}

/// The Rholang-native scalar corresponding to a simple parameter.
///
/// BigInt/BigRat/Fixed/Float/UInt32 and any non-`Simple`
/// (binder/guard/optional) parameter are NOT native — lowering their operators
/// to Rholang scalar `Expr`s would be semantically wrong, so such rules are
/// rejected and surfaced to the coverage gate.
fn param_rho_native_scalar(def: &LanguageDef, p: &TermParam) -> Option<RhoScalarType> {
    match p {
        TermParam::Simple { ty, .. } => rho_native_scalar_type(def, ty),
        _ => None,
    }
}

fn result_rho_native_scalar(def: &LanguageDef, rule: &GrammarRule) -> Option<RhoScalarType> {
    category_rho_native_scalar(def, &rule.category)
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
    abi: RhoScalarContractAbi,
) -> LoweredRule {
    debug_assert_eq!(formal_count, abi.formal_count());
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
        abi,
    }
}

/// Lower one rule to a normalized Rholang contract, or `None` if it is out of the supported
/// scalar-operator subset (→ to be recorded as rejected, never dropped).
fn lower_rule(def: &LanguageDef, rule: &GrammarRule) -> Option<LoweredRule> {
    let pattern = rule.syntax_pattern.as_ref()?;
    // Only lower rules whose operands and result have an exact Rholang scalar
    // interpretation. Keying on the terminal alone would mis-lower e.g.
    // `AddBigInt` (`a:BigInt "+" b`) or `AddStr` as integer `EPlus`.
    let ctx = rule.term_context.as_ref()?;
    if ctx.is_empty() {
        return None;
    }
    let result_ty = result_rho_native_scalar(def, rule)?;
    let label = rule.label.to_string();
    match pattern.as_slice() {
        // Binary infix: `a <op> b` → contract @"L"(@a, @b, ret) = { ret!(a <op> b) }
        [SyntaxExpr::Param(a), SyntaxExpr::Literal(op), SyntaxExpr::Param(b)] => {
            let [lhs_param, rhs_param] = ctx.as_slice() else {
                return None;
            };
            let lhs_ty = param_rho_native_scalar(def, lhs_param)?;
            let rhs_ty = param_rho_native_scalar(def, rhs_param)?;
            let rop = rho_binop(op, lhs_ty, rhs_ty, result_ty)?;
            let formal_count = 3;
            let abi = RhoScalarContractAbi {
                rule_label: label.clone(),
                shape: RhoScalarContractShape::BinaryInfix {
                    left: lhs_ty,
                    right: rhs_ty,
                    result: result_ty,
                },
            };
            let lhs = bound_formal(formal_count, 0);
            let rhs = bound_formal(formal_count, 1);
            let result_expr = expr_par(rop.expr(lhs, rhs), &[1, 2]);
            let text_annotation = format!(
                "contract @\"{label}\"(@{a}, @{b}, ret) = {{ ret!({a} {} {b}) }}",
                rop.symbol()
            );
            Some(contract_ast(&label, formal_count, result_expr, text_annotation, abi))
        },
        // Unary prefix: `<op> a` → contract @"L"(@a, ret) = { ret!(<op> a) }
        [SyntaxExpr::Literal(op), SyntaxExpr::Param(a)] => {
            let [arg_param] = ctx.as_slice() else {
                return None;
            };
            let arg_ty = param_rho_native_scalar(def, arg_param)?;
            let rop = rho_unop(op, arg_ty, result_ty)?;
            let formal_count = 2;
            let abi = RhoScalarContractAbi {
                rule_label: label.clone(),
                shape: RhoScalarContractShape::UnaryPrefix { argument: arg_ty, result: result_ty },
            };
            let arg = bound_formal(formal_count, 0);
            let result_expr = expr_par(rop.expr(arg), &[1]);
            let text_annotation =
                format!("contract @\"{label}\"(@{a}, ret) = {{ ret!({} {a}) }}", rop.symbol());
            Some(contract_ast(&label, formal_count, result_expr, text_annotation, abi))
        },
        _ => None,
    }
}

/// Lower every scalar reduction rule of `def` to a Rholang program. Supported
/// operator rules become parallel `contract`s; all other rules are recorded in
/// `rejected` (the "miss nothing" guarantee — nothing is silently dropped).
pub fn lower_language_def(def: &LanguageDef) -> RhoLowering {
    // E-3 Stage-0: SELF-time phase span (no-op without an active collection window).
    let _lower_language_def_span =
        crate::pipeline_spans::phase_span(crate::pipeline_spans::PipelinePhase::LowerLanguageDef);
    let mut lowered = Vec::new();
    let mut scalar_contract_abi = Vec::new();
    let mut rejected = Vec::new();
    let mut program = Par::default();
    let mut annotations = Vec::new();
    let mut network = ChannelNetwork::new();
    for rule in &def.terms {
        match lower_rule(def, rule) {
            Some(lowered_rule) => {
                let label = rule.label.to_string();
                lowered.push(label.clone());
                scalar_contract_abi.push(lowered_rule.abi);
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
        language_name: def.name.to_string(),
        definition_fingerprint: language_definition_fingerprint(def),
        program: RhoProgram::Ast(RhoAstProgram::new(program, text_annotation)),
        lowered,
        scalar_contract_abi,
        rejected,
        deadlock_report,
    }
}

/// Return a standalone `Par` containing exactly the persistent scalar contract
/// whose receive binds on `GString(label)`.
///
/// `lower_language_def` parallel-composes every generated operator contract into
/// one `program` `Par`; this locates the single contract for the native-fold
/// rule `label` by its stable `GString(label)` receive source (the shape set by
/// [`contract_ast`]) and returns it as its own closed `Par`. The `rho_net_lower`
/// walk reuses this to lower a `NativeFold` RhoNet rule to the already-proven
/// scalar contract artifact instead of re-synthesizing it, so the Rho-native
/// execution plan and the scalar backend share one contract shape. Returns
/// `None` when no lowered contract binds on `label` (the caller surfaces this as
/// `MissingScalarContract`).
pub(crate) fn scalar_contract_par_for(lowering: &RhoLowering, label: &str) -> Option<Par> {
    let program = lowering.ast_par()?;
    let source = new_gstring_par(label.to_string(), Vec::new(), false);
    program
        .receives
        .iter()
        .find(|receive| {
            receive
                .binds
                .iter()
                .any(|bind| bind.source.as_ref() == Some(&source))
        })
        .map(|receive| Par::default().with_receives(vec![receive.clone()]))
}
