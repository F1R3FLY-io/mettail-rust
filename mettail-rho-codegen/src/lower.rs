//! `lower_language_def` — the M-RHO.0.3 spec→Rholang lowering of a MeTTaIL
//! `LanguageDef`'s scalar reduction rules to f1r3node-rust Rholang `contract`s.
//!
//! Each scalar operator rule whose concrete syntax is a supported infix/prefix
//! operator (one with an exact Rholang `Expr` equivalent — `+ - * / %`,
//! comparisons `== != < > <= >=`, `and`/`or`/`not`, `++`, unary `-`) lowers to a
//! Rholang contract `contract @"<Label>"(@a, @b, ret) = { ret!(a <op> b) }`. Every
//! other rule (BigInt/BigRat/Fixed/Float/UInt32 ops, casts, `Err`/`Proc`
//! injections, collections, ternary, factorial, power, bitwise, …) is NOT silently
//! dropped — it is recorded in [`RhoLowering::rejected`]. This is the "miss
//! nothing" discipline at the codegen layer (cf.
//! `formal/rocq/rho_bridge/theories/RhoLoweringTotalOrRejects.v`): every rule in
//! `def.terms` is accounted for — exactly one of lowered / rejected.
//!
//! The semantic equivalence of the emitted Rholang to the Ascent evaluator is the
//! NEXT substage (M-RHO.0.4, the differential oracle); this substage establishes a
//! WELL-FORMED Rholang lowering (the parse round-trip via `Compiler::source_to_adt`
//! is the gate) plus the totality/no-loss guarantee.

use mettail_ast::grammar::{GrammarRule, SyntaxExpr, TermParam};
use mettail_ast::language::LanguageDef;
use mettail_ast::types::TypeExpr;

/// The result of lowering a `LanguageDef` to Rholang: the well-formed Rholang
/// `source`, the rule labels that were `lowered` to contracts, and the labels
/// explicitly `rejected` (out of the supported scalar-operator subset). Every
/// rule of `def.terms` appears in exactly one of `lowered` / `rejected`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RhoLowering {
    pub source: String,
    pub lowered: Vec<String>,
    pub rejected: Vec<String>,
}

/// Map a calculator infix terminal to its Rholang binary operator, if Rholang
/// has an exact `Expr` equivalent (`utils.rs` `BinaryExpr` set). `None` = no
/// Rholang equivalent (e.g. `^`, `bitand`, `bitor`, `xor`).
fn rho_binop(terminal: &str) -> Option<&'static str> {
    match terminal {
        "+" => Some("+"),
        "-" => Some("-"),
        "*" => Some("*"),
        "/" => Some("/"),
        "%" => Some("%"),
        "==" => Some("=="),
        "!=" => Some("!="),
        "<" => Some("<"),
        ">" => Some(">"),
        "<=" => Some("<="),
        ">=" => Some(">="),
        "and" => Some("and"),
        "or" => Some("or"),
        "++" => Some("++"),
        _ => None,
    }
}

/// Map a calculator prefix terminal to its Rholang unary operator, if any
/// (`utils.rs` `UnaryExpr` set: `not`, unary `-`).
fn rho_unop(terminal: &str) -> Option<&'static str> {
    match terminal {
        "not" => Some("not"),
        "-" => Some("-"),
        _ => None,
    }
}

/// Whether a parameter's type is a Rholang-native scalar (`Int`→GInt,
/// `Bool`→GBool, `Str`→GString). BigInt/BigRat/Fixed/Float/UInt32 and any
/// non-`Simple` (binder/guard/optional) parameter are NOT native — lowering their
/// operators to Rholang scalar `Expr`s would be semantically wrong, so such rules
/// are rejected (recorded, never silently lowered with the wrong meaning).
fn param_is_rho_native_scalar(p: &TermParam) -> bool {
    match p {
        TermParam::Simple { ty, .. } => matches!(
            ty,
            TypeExpr::Base(id)
                if matches!(id.to_string().as_str(), "Int" | "Bool" | "Str")
        ),
        _ => false,
    }
}

/// Lower one rule to a Rholang contract, or `None` if it is out of the supported
/// scalar-operator subset (→ to be recorded as rejected, never dropped).
fn lower_rule(rule: &GrammarRule) -> Option<String> {
    let pattern = rule.syntax_pattern.as_ref()?;
    // Only lower rules whose operands are ALL Rholang-native scalar types — keying
    // on the terminal alone would mis-lower e.g. `AddBigInt` (`a:BigInt "+" b`).
    let ctx = rule.term_context.as_ref()?;
    if ctx.is_empty() || !ctx.iter().all(param_is_rho_native_scalar) {
        return None;
    }
    let label = rule.label.to_string();
    match pattern.as_slice() {
        // Binary infix: `a <op> b` → contract @"L"(@a, @b, ret) = { ret!(a <op> b) }
        [SyntaxExpr::Param(a), SyntaxExpr::Literal(op), SyntaxExpr::Param(b)] => {
            let rop = rho_binop(op)?;
            Some(format!(
                "contract @\"{label}\"(@{a}, @{b}, ret) = {{ ret!({a} {rop} {b}) }}"
            ))
        }
        // Unary prefix: `<op> a` → contract @"L"(@a, ret) = { ret!(<op> a) }
        [SyntaxExpr::Literal(op), SyntaxExpr::Param(a)] => {
            let rop = rho_unop(op)?;
            Some(format!(
                "contract @\"{label}\"(@{a}, ret) = {{ ret!({rop} {a}) }}"
            ))
        }
        _ => None,
    }
}

/// Lower every scalar reduction rule of `def` to a Rholang program. Supported
/// operator rules become parallel `contract`s; all other rules are recorded in
/// `rejected` (the "miss nothing" guarantee — nothing is silently dropped).
pub fn lower_language_def(def: &LanguageDef) -> RhoLowering {
    let mut lowered = Vec::new();
    let mut rejected = Vec::new();
    let mut contracts = Vec::new();
    for rule in &def.terms {
        match lower_rule(rule) {
            Some(contract) => {
                lowered.push(rule.label.to_string());
                contracts.push(contract);
            }
            None => rejected.push(rule.label.to_string()),
        }
    }
    // A Rholang program is a single process; parallel-compose the contracts. An
    // empty program is the inert process `Nil`.
    let source = if contracts.is_empty() {
        "Nil".to_string()
    } else {
        contracts.join(" |\n")
    };
    RhoLowering {
        source,
        lowered,
        rejected,
    }
}
