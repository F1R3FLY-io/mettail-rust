//! Prefix-dispatch arm emission.
//!
//! Phase A.2 of Stage 6 plan v2. For each category, this module walks the
//! category's rule list and emits per-rule arms in the engine's
//! `WpdaState::PrefixDispatch` match. Atomic-literal rules emit a
//! `ConsumeAndPush(Return)` action so the walker captures the token,
//! advances pos, and transitions into `Unwinding` — where the Return
//! frame's pop fires the semantic action.
//!
//! Later phases (A.3 for Pratt, A.4 for cross-cat, A.6 for binders, etc.)
//! populate additional arms in the same match.

use mettail_ast::grammar::{GrammarItem, GrammarRule, NonTerminalKind};
use mettail_ast::language::{LanguageDef, NativeKind};
use mettail_prattail::binding_power::compute_prefix_bp;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{Ident, Type};

/// Lexer token family for a literal-patterned rule.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LiteralFamily {
    /// Maps to `TokenKind::IntegerLit(cat)`. Applies to all bounded-integer
    /// widths AND `CanonicalBigInt` (the lexer treats them uniformly — per-
    /// category variant with category-name payload).
    Integer,
    /// Maps to `TokenKind::RationalLit(cat)`.
    Rational,
    /// Maps to `TokenKind::FixedPointLit(cat)`.
    FixedPoint,
    /// Maps to `TokenKind::Float`. One float category per grammar (no
    /// payload since lexer only emits one variant).
    Float,
    /// Maps to `TokenKind::True | False | BooleanLit`.
    Boolean,
    /// Maps to `TokenKind::StringLit`.
    String,
}

/// B11 fix: classifies the calling context that drives literal-pattern arm
/// emission. The Integer family's bare-polymorphic `TokenKind::Integer` arm
/// is gated on this — present in `HomeCategory` (so a bare unsuffixed integer
/// in BigInt's own PrefixDispatch resolves directly to BigInt's NumLit),
/// suppressed in `FirstSet` (so primitive-integer cross-cat projections like
/// `ProcInt`/`ProcUInt32` aren't shadowed when the FIRST set of `BigInt` is
/// consumed by other categories' cross-cat dispatch). Generalizes uniformly via
/// `home_polymorphic_token_arm(family)` — adding a new kind to an existing
/// family auto-inherits the correct behavior.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EmissionContext {
    /// Emitting arms for a rule's home category (e.g., BigInt's PrefixDispatch
    /// arms). The bare-polymorphic `TokenKind::Integer` arm IS emitted for
    /// non-primitive integer kinds (`CanonicalBigInt`); without it, bare
    /// unsuffixed integers route through cross-cat to Int via heuristics.
    HomeCategory,
    /// Computing a FIRST set that will be consumed by cross-cat-projection
    /// emission. The bare-polymorphic arm is suppressed to keep the FIRST set
    /// free of home-only arms.
    FirstSet,
}

/// B11 fix: returns the bare-polymorphic-Token pattern that the lexer emits
/// for the given family in HOME context, if any. Keyed on `LiteralFamily`
/// (not `NativeKind`) so any future kind whose `literal_family_for(kind)`
/// returns `Some(Integer)` automatically gets the bare-Integer arm in home
/// context — no codegen changes required when extending `NativeKind`.
///
/// Today only `LiteralFamily::Integer` has a polymorphic Token variant
/// (`Token::Integer(_, suffix)` → `TokenKind::Integer`) emitted by the
/// lexer for unsuffixed numeric input. Other families require explicit
/// suffixes/delimiters in their lexer regexes (`r` for Rational, `p` for
/// FixedPoint, decimal/exponent for Float, quoted for String, etc.) so
/// they have no analogous polymorphic-Token routing trap.
fn home_polymorphic_token_arm(family: LiteralFamily) -> Option<TokenStream> {
    match family {
        LiteralFamily::Integer => Some(quote! {
            Some(mettail_prattail::automata::TokenKind::Integer)
        }),
        LiteralFamily::Rational
        | LiteralFamily::FixedPoint
        | LiteralFamily::Float
        | LiteralFamily::Boolean
        | LiteralFamily::String => None,
    }
}

/// Classification of a rule for Phase A.2 codegen.
#[derive(Debug, Clone)]
pub enum AtomicShape {
    /// Legacy shape: the rule consumes exactly one literal token matching a
    /// built-in `NonTerminalKind::{Integer, Boolean, StringLiteral,
    /// FloatLiteral}`. No shipped grammar uses this today — retained for
    /// forward compatibility.
    LiteralInteger,
    LiteralBoolean,
    LiteralString,
    LiteralFloat,
    /// The rule is an atomic literal whose category has a `literals { }`
    /// block. The walker captures the token text; the action body invokes
    /// the user's per-category `eval` closure (stored in
    /// `TokenDef.rust_code`) and wraps the result in the category's
    /// auto-generated literal variant (`NumLit`, `BoolLit`, `StringLit`,
    /// `RatLit`, `FixedLit`, `FloatLit`).
    LiteralPatterned {
        /// The category's name (e.g., `"Int"`). Used as the `TokenKind`
        /// payload string for per-category lexer variants.
        cat_name: String,
        /// The category's native Rust type (e.g., `i32`, `CanonicalBigRat`).
        /// Drives extraction from the intermediate type produced by
        /// `rust_code`.
        native_type: Type,
        /// Which token family the lexer emits for this category.
        family: LiteralFamily,
        /// The auto-generated AST variant name (e.g., `NumLit`, `BoolLit`).
        /// Computed via `generate_literal_label(native_type)`.
        wrapper_variant: Ident,
        /// Verbatim user rust_code (the `eval: ![ { ... } ]` block body).
        rust_code: TokenStream,
    },
    /// Terminal-keyword nullary rules like Calculator's `Err . |- "error" :
    /// Int` or `CastErrInt . |- "cast_error_int" : Int`. Match a single
    /// `TokenKind::Fixed(s)` arm and push the category's nullary variant
    /// named after the rule label.
    TerminalKeyword {
        /// Exact terminal text (e.g., `"error"`).
        terminal_text: String,
        /// The AST variant name (= rule.label).
        wrapper_variant: Ident,
    },
    /// GAP-3 (2026-06-28): 0-operand MULTI-literal keyword-PREFIX rule — the
    /// dual of B-1's LHS-anchored `MixfixLiteralRun` nullary path. Shape:
    /// empty term-context, `syntax_pattern` is two-or-more CONSECUTIVE
    /// `Literal`s with NO `Param`/`Op` (e.g. RhoCalc's
    /// `MapEmpty . |- "Map" "(" ")" : Proc`, `PathmapEmpty . |- "Pathmap" "("
    /// ")" : Proc`, `NQuoteNil . |- "@" "Nil" : Name`). The FIRST literal is
    /// the dispatch trigger; the REST are consumed (membership-checked) by the
    /// REUSED `MixfixLiteralRun { kind: 2, parts_len == 0 }` runtime arm after
    /// the prefix site pushes the marker. The marker pop fires the arity-0
    /// action, which builds the nullary AST variant named after the rule label
    /// (a `fold`, if present, lowers it to its container at eval time).
    ///
    /// Generalizes "0-operand for every rule kind": atomic single-literal
    /// (`TerminalKeyword`, sp.len() == 1); LHS-anchored mixfix nullary (B-1,
    /// `POutputEmpty`); and this prefix-anchored multi-literal nullary —
    /// any category, any delimiter alphabet, zero per-language glue.
    NullaryLiteralRun {
        /// The dispatch trigger (the FIRST literal, e.g. `"Map"`, `"@"`).
        trigger: String,
        /// The post-trigger literals consumed by the marker run (e.g.
        /// `["(", ")"]` for `Map()`, `["Nil"]` for `@Nil`).
        trailing_literals: Vec<String>,
        /// The auto-generated nullary AST variant name (= rule.label).
        wrapper_variant: Ident,
    },
    /// Phase 5a: synthetic Var rule for a user-defined category. The
    /// rule's body is a single `NonTerminal(Var, cat)` item. Match a
    /// `TokenKind::Ident` arm and push `Cat::<Var>(OrdVar(Var::Free(
    /// get_or_create_var(name))))`.
    VarRule {
        /// The Var-variant label (e.g., `TVar` for `Term`, `PVar` for `Proc`).
        wrapper_variant: Ident,
    },
    /// Stage 1.1: cross-category projection (e.g., Calculator's
    /// `ProcInt . i:Int |- i : Proc`, RhoCalc's `CastBigRat . r:BigRat |- r : Proc`).
    /// The rule's source category differs from the result category. The
    /// engine pushes a CategoryEntry sub-frame for the source category;
    /// after sub-parse, the action wraps the result in
    /// `Cat::<wrapper_variant>(Box::new(source_term))`.
    CrossCatProjection {
        /// Source category name (e.g., `"Int"` for ProcInt, `"BigRat"` for CastBigRat).
        source_cat_name: String,
        /// The AST variant name = rule.label.
        wrapper_variant: Ident,
    },
    /// Stage 1.1: cross-category prefix unary (e.g., a hypothetical
    /// `LenStr . s:Str |- "len" s : Int`). Trigger literal followed by
    /// a single sub-parse of a different category, action wraps result.
    /// Currently no shipped grammar uses this shape — kept for completeness.
    CrossCatPrefixUnary {
        /// Trigger literal (e.g., `"len"`).
        trigger: String,
        /// Source category name.
        source_cat_name: String,
        /// AST variant name = rule.label.
        wrapper_variant: Ident,
    },
    /// M6c.6.4 (2026-05-14): same-cat unary prefix operator
    /// (e.g., `Neg . a:Int |- "-" a : Int`, `BitNotInt . a:Int |-
    /// "bitnot" a : Int`). Pattern: `tc = [Simple(name, T)]`,
    /// `sp = [Literal(trigger), Param(name)]`, `T == rule.category`.
    /// Recognized via `builtin_metadata::classify_unary_prefix_shape`.
    ///
    /// The lex-Fork at PrefixDispatch emits a branch for this rule
    /// when the lex DAG offers `Fixed(trigger)` as one of the alts at
    /// the current position. Walker apply (`LexAltPrefixOp`) mirrors
    /// the standard `Fixed(trigger)` ConsumeAndPush arm: push
    /// `rule_at(cat, rule_idx, slot=1, Some(*cur_bp))` (NO
    /// `with_kind_return`), `new_state = BinderRule { ...,
    /// body_src_idx, outer_bp = *cur_bp }`, no `emit_push_token`.
    /// Operand sub-parse runs the operand at the rule's
    /// `prefix_bp_map` operand cur_bp (installed downstream by
    /// `BinderRule`'s ParamParse arm).
    PrefixOperator {
        /// Trigger literal (e.g., `"-"`, `"bitnot"`).
        trigger: String,
        /// Operand category name (== `rule.category` for same-cat).
        operand_cat_name: String,
    },
    /// Not atomic — requires Phase A.3+ emission.
    NonAtomic,
}

/// Decide if this rule is atomic and which atomic shape it has.
///
/// Returns `AtomicShape::NonAtomic` for any rule with composite syntax,
/// references to other categories (unless an atomic literal projection), or
/// binder structure. Phase A.2 handles only the atomic subset; subsequent
/// phases handle the rest.
///
/// Handles BOTH old-style rules (populated `items`) and new-style judgement
/// rules (`term_context` + `syntax_pattern`), since Calculator / RhoCalc
/// use exclusively judgement-style.
pub fn classify_atomic(rule: &GrammarRule, language: &LanguageDef) -> AtomicShape {
    // Judgement-style rules: check `term_context` + `syntax_pattern` to
    // recognize TerminalKeyword (empty context, single literal pattern).
    if let (Some(tc), Some(sp)) = (&rule.term_context, &rule.syntax_pattern) {
        // Nullary rule with a single terminal literal pattern → TerminalKeyword.
        // Example: `Err . |- "error" : Int` (tc=[], sp=[Literal("error")]).
        if tc.is_empty() && sp.len() == 1 {
            if let mettail_ast::grammar::SyntaxExpr::Literal(text) = &sp[0] {
                return AtomicShape::TerminalKeyword {
                    terminal_text: text.clone(),
                    wrapper_variant: rule.label.clone(),
                };
            }
        }
        // GAP-3 (2026-06-28): 0-operand MULTI-literal keyword-prefix rule
        // (`Map "(" ")"`, `Pathmap "(" ")"`, `@ Nil`). Empty term-context AND
        // two-or-more syntax items that are ALL `Literal` (no `Param`/`Op`).
        // The first literal is the dispatch trigger; the rest are consumed by
        // the reused `MixfixLiteralRun { kind: 2, parts_len == 0 }` arm.
        //
        // Placement safety: `tc.is_empty()` means the CrossCat* blocks below
        // (which require `tc.len() == 1`) can never match these rules, and the
        // all-`Literal` guard excludes every `Param`/`Op`-bearing shape (PPar,
        // POutput, etc. carry a `Param` ⇒ untouched). The single-literal case
        // already returned above as `TerminalKeyword`, so here `sp.len() >= 2`.
        if tc.is_empty()
            && sp.len() >= 2
            && sp
                .iter()
                .all(|e| matches!(e, mettail_ast::grammar::SyntaxExpr::Literal(_)))
        {
            let mut literals = sp.iter().filter_map(|e| match e {
                mettail_ast::grammar::SyntaxExpr::Literal(t) => Some(t.clone()),
                _ => None,
            });
            let trigger = literals
                .next()
                .expect("classify_atomic: sp.len() >= 2 guarantees a first literal");
            let trailing_literals: Vec<String> = literals.collect();
            return AtomicShape::NullaryLiteralRun {
                trigger,
                trailing_literals,
                wrapper_variant: rule.label.clone(),
            };
        }
        // Stage 1.1: cross-category projection (e.g. `ProcInt . i:Int |- i : Proc`,
        // `CastBigRat . r:BigRat |- r : Proc`). One Simple param of base type,
        // syntax_pattern is just `Param(name)`, source_cat ≠ result_cat.
        if tc.len() == 1 && sp.len() == 1 {
            if let mettail_ast::grammar::TermParam::Simple { name: param_name, ty } = &tc[0] {
                if let mettail_ast::grammar::SyntaxExpr::Param(syn_name) = &sp[0] {
                    if syn_name == param_name {
                        if let mettail_ast::types::TypeExpr::Base(source_ident) = ty {
                            let source_cat = source_ident.to_string();
                            if source_cat != rule.category.to_string() {
                                return AtomicShape::CrossCatProjection {
                                    source_cat_name: source_cat,
                                    wrapper_variant: rule.label.clone(),
                                };
                            }
                        }
                    }
                }
            }
        }
        // Stage 1.1: cross-category prefix unary (e.g. `LenStr . s:Str |- "len" s : Int`).
        // Two-element syntax_pattern: Literal + Param, single Simple param,
        // source_cat ≠ result_cat. NOT a normal Pratt prefix (which has
        // operand of same category as the result).
        if tc.len() == 1 && sp.len() == 2 {
            if let (
                mettail_ast::grammar::SyntaxExpr::Literal(trigger),
                mettail_ast::grammar::SyntaxExpr::Param(syn_name),
            ) = (&sp[0], &sp[1])
            {
                if let mettail_ast::grammar::TermParam::Simple { name: param_name, ty } = &tc[0] {
                    if syn_name == param_name {
                        if let mettail_ast::types::TypeExpr::Base(source_ident) = ty {
                            let source_cat = source_ident.to_string();
                            if source_cat != rule.category.to_string() {
                                return AtomicShape::CrossCatPrefixUnary {
                                    trigger: trigger.clone(),
                                    source_cat_name: source_cat,
                                    wrapper_variant: rule.label.clone(),
                                };
                            }
                        }
                    }
                }
            }
        }
        // M6c.6.4.b (2026-05-14): same-cat unary prefix (e.g.,
        // `Neg . a:Int |- "-" a : Int`). Recognized via the existing
        // `builtin_metadata::classify_unary_prefix_shape` (operand
        // category == rule.category guard already enforced there).
        // Emits `AtomicShape::PrefixOperator` so the lex-Fork can
        // bind `Fixed(trigger)` → this rule's `LexAltPrefixOp` branch.
        if let Some(shape) = super::builtin_metadata::classify_unary_prefix_shape(rule) {
            return AtomicShape::PrefixOperator {
                trigger: shape.trigger,
                operand_cat_name: shape.operand_category,
            };
        }
        // Other judgement-style rules need Phase A.3+ emission.
        return AtomicShape::NonAtomic;
    }

    if rule.items.len() != 1 {
        return AtomicShape::NonAtomic;
    }

    match &rule.items[0] {
        GrammarItem::NonTerminal { kind, ident } => match kind {
            NonTerminalKind::Integer => AtomicShape::LiteralInteger,
            NonTerminalKind::Boolean => AtomicShape::LiteralBoolean,
            NonTerminalKind::StringLiteral => AtomicShape::LiteralString,
            NonTerminalKind::FloatLiteral => AtomicShape::LiteralFloat,
            NonTerminalKind::Var => {
                // Phase 5a: synthetic Var rule for user-defined category.
                // Rule shape: single-item NonTerminal(Var, cat) where
                // `rule.category == ident`. Label is the Var-variant label
                // (TVar / PVar / etc.) — use rule.label directly.
                if rule.category == *ident {
                    AtomicShape::VarRule { wrapper_variant: rule.label.clone() }
                } else {
                    AtomicShape::NonAtomic
                }
            },
            NonTerminalKind::Category => {
                // LiteralPatterned detection: rule body is a single category
                // reference AND that category has a `from_literals` TokenDef
                // AND the rule's OWN category equals the referenced category
                // (so cross-cat projections like `ProcInt . i:Int |- i : Proc`
                // are NOT misclassified — they belong to Phase 3 cross-cat).
                if rule.category != *ident {
                    return AtomicShape::NonAtomic;
                }
                classify_literal_patterned(ident, language).unwrap_or(AtomicShape::NonAtomic)
            },
        },
        GrammarItem::Terminal(text) => AtomicShape::TerminalKeyword {
            terminal_text: text.clone(),
            wrapper_variant: rule.label.clone(),
        },
        _ => AtomicShape::NonAtomic,
    }
}

/// Look up the TokenDef + LangType for a category and package them into a
/// `LiteralPatterned` shape.
///
/// Two paths produce a valid shape:
///   (a) Explicit `literals { ... }` block — `from_literals: true` TokenDef
///       carries the user's `eval: ![ { ... } ]` block body in `rust_code`.
///   (b) Implicit native-type — `LangType.native_type` is `Some(_)` but no
///       explicit literals block. We fabricate a default eval body matching
///       the trampoline's auto-generated atomic-literal arm: for `![i32] as Num`
///       we emit `parse_int_lit(text, Some(Suffix::I32))`.
///
///       (This paragraph used to describe a `Token::Integer(v, suffix) if
///       suffix.matches_i32()` guard. `IntSuffix::matches_*` was retired in
///       2026-07 with zero callers — divergence I, Stage E: a documented-but-
///       unread guard family is what made a universal-acceptor `eval` look
///       guarded. A category's literal domain is decided by its own `eval`.)
fn classify_literal_patterned(cat_ident: &Ident, language: &LanguageDef) -> Option<AtomicShape> {
    let cat_name = cat_ident.to_string();
    // Find the LangType for the category to get the native Rust type.
    let lang_type = language.types.iter().find(|t| &t.name == cat_ident)?;
    let native_type = lang_type.native_type.as_ref()?.clone();
    let kind = NativeKind::from_syn_type(&native_type);
    let family = literal_family_for(&kind)?;
    let wrapper_variant = crate::gen::generate_literal_label(&native_type);

    // Case (a): explicit literals block.
    let token_def = language.token_defs.iter().find(|td| {
        td.from_literals
            && td
                .category
                .as_ref()
                .map(|c| c == cat_ident)
                .unwrap_or(false)
    });
    if let Some(td) = token_def {
        if let Some(rust_code) = td.rust_code.clone() {
            return Some(AtomicShape::LiteralPatterned {
                cat_name,
                native_type,
                family,
                wrapper_variant,
                rust_code,
            });
        }
    }

    // Case (b): implicit native-type — synthesize default eval body.
    let rust_code = default_eval_body_for_native_kind(&kind)?;
    Some(AtomicShape::LiteralPatterned {
        cat_name,
        native_type,
        family,
        wrapper_variant,
        rust_code,
    })
}

/// Synthesize a default eval-block body for a category whose `native_type`
/// is set but which has no `literals { ... }` block. Mirrors the
/// trampoline's auto-generated atomic-literal arms in
/// `prattail/src/trampoline.rs::write_atomic_lit_arm`.
fn default_eval_body_for_native_kind(kind: &NativeKind) -> Option<TokenStream> {
    let body = match kind {
        NativeKind::Int8 | NativeKind::Int16 | NativeKind::Int32 => quote! {
            mettail_prattail::parse_int_lit(text, Some(mettail_prattail::Suffix::I32))
                .map_err(|_| ())
        },
        NativeKind::Int64 => quote! {
            mettail_prattail::parse_int_lit(text, Some(mettail_prattail::Suffix::I64))
                .map_err(|_| ())
        },
        NativeKind::Int128 => quote! {
            mettail_prattail::parse_int_lit(text, None).map_err(|_| ())
        },
        NativeKind::Isize => quote! {
            mettail_prattail::parse_int_lit(text, Some(mettail_prattail::Suffix::I64))
                .map_err(|_| ())
        },
        NativeKind::UInt8 | NativeKind::UInt16 => quote! {
            mettail_prattail::parse_int_lit(text, None).map_err(|_| ())
        },
        NativeKind::UInt32 => quote! {
            mettail_prattail::parse_int_lit(text, Some(mettail_prattail::Suffix::U32))
                .map_err(|_| ())
        },
        NativeKind::UInt64 | NativeKind::Usize => quote! {
            mettail_prattail::parse_int_lit(text, Some(mettail_prattail::Suffix::U64))
                .map_err(|_| ())
        },
        NativeKind::UInt128 => quote! {
            mettail_prattail::parse_int_lit(text, None).map_err(|_| ())
        },
        NativeKind::CanonicalBigInt => quote! {
            mettail_prattail::parse_int_lit(text, None).map_err(|_| ())
        },
        NativeKind::CanonicalBigRat => quote! {
            mettail_prattail::parse_rational_lit(text).map_err(|_| ())
        },
        NativeKind::CanonicalFixedPoint => quote! {
            mettail_runtime::parse_fixed_lit(text).map_err(|_| ())
        },
        NativeKind::Float32 | NativeKind::Float64 => quote! {
            mettail_runtime::parse_float_lit(text).map_err(|_| ())
        },
        NativeKind::Bool => quote! {
            match text {
                "true" => Ok(true),
                "false" => Ok(false),
                _ => Err(()),
            }
        },
        NativeKind::Str => quote! {
            if text.len() < 2 {
                Err(())
            } else {
                let inner = &text[1..text.len() - 1];
                let unescaped = inner
                    .replace("\\\"", "\"")
                    .replace("\\\\", "\\");
                Ok(unescaped.to_string())
            }
        },
        NativeKind::Other => return None,
    };
    Some(body)
}

/// Stage 1.1: a token in a category's FIRST set, emitted as a `TokenKind`
/// pattern fragment for use in a Rust match arm.
#[derive(Debug, Clone)]
pub struct FirstToken {
    /// The token-kind pattern (e.g., `Some(TokenKind::IntegerLit(__cat))`).
    pub pattern: TokenStream,
    /// Optional extra guard (e.g., `__cat == "Int"`).
    pub extra_guard: Option<TokenStream>,
    /// AT_QUOTED_BIND_GATE (2026-07-03): the raw leading *structural literal*
    /// text when this FIRST token is a `Fixed(σ)` derived from a rule whose
    /// first syntax element is the literal `σ` (a sigil-led prefix rule such as
    /// NQuoteShort `"@" p`). `None` for non-`Fixed` tokens (Ident / native
    /// literals) and for `Fixed` tokens that are not a rule's *leading*
    /// structural trigger. Consumed ONLY by the grammar-derived over-generation
    /// characterisation in `emit_prefix_arms_for_category` (a cross-cat-LHS
    /// delegate on a sigil that ALSO directly triggers a sibling rule in the
    /// result category is redundant — see `AT_QUOTED_BIND_GATE`). Threading the
    /// literal here keeps the gate PER-token precise without re-parsing guards.
    pub leading_literal: Option<String>,
    /// CROSSCAT_LEX_COMPAT_GATE (2026-07-03): `true` iff this FIRST token is a
    /// *variable contribution* — the bare `Some(Ident)` a category acquires
    /// from its (synthetic or user) Var rule. This is the sole provenance that
    /// distinguishes "the source category can begin with an Ident because it
    /// has a Var rule" (a var-contribution) from "the source category can begin
    /// with a genuine literal/keyword token" (NOT a var-contribution). The
    /// LITERAL-FIRST set the gate keys on is exactly `FIRST − {var-contributions}`.
    /// A cross-cat PROJECTION delegate `source : result` on the `Ident` token is
    /// a proven over-generation exactly when that `Ident` is ONLY a
    /// var-contribution of `source` (the source cannot LITERALLY begin with an
    /// Ident) AND `result` already has its own home Var reading (so a bare
    /// Ident is covered without the cast). Set `true` at the two Var-rule sites
    /// in `collect_first_set`; `false` at every literal/keyword/collection/
    /// projection-recursion site. NOTE: the `Some(Ident)`-no-guard token is
    /// produced ONLY by these two Var sites in the whole codegen, so the
    /// `(pattern_str, guard_str)` dedup in `first_set_of_category` never merges
    /// a var-contribution with a literal token (no literal rule yields a bare
    /// unguarded `Some(Ident)`) — the flag survives dedup soundly.
    pub is_var_contribution: bool,
}

impl FirstToken {
    /// Construct a `Fixed(σ)` FIRST token carrying the raw sigil `σ` as its
    /// `leading_literal`. Used at every site where the FIRST token is a rule's
    /// leading structural literal so the AT_QUOTED_BIND_GATE characterisation
    /// can key on it.
    fn fixed_leading(sigil: &str) -> Self {
        FirstToken {
            pattern: quote! {
                Some(mettail_prattail::automata::TokenKind::Fixed(__kw))
            },
            extra_guard: Some(quote! { __kw == #sigil }),
            leading_literal: Some(sigil.to_string()),
            // A leading structural literal is a genuine literal token, never a
            // var contribution.
            is_var_contribution: false,
        }
    }
}

/// AT_QUOTED_BIND_GATE (2026-07-03): the set of LEADING STRUCTURAL LITERALS of
/// a category's rules — the literal `σ` at `rule.syntax_pattern[0]` /
/// `rule.items[0]` for each rule DIRECTLY in `cat_name` whose first syntax
/// element is a literal (a sigil-/keyword-led rule, e.g. `InputBindQuoted
/// "@" pat "<-" n` contributes `@`). Excludes rules whose first element is a
/// parameter (a cross-cat-LHS / whole-source rule such as `InputBind lhs "<-"
/// n`, which contributes nothing here — its `lhs` is the delegated source).
///
/// This is the grammar-derived characterisation of "a direct `σ`-triggered rule
/// exists in the result category". A cross-cat-LHS delegate `source → result`
/// on a sigil `σ` is a proven over-generation exactly when `σ` is in this set
/// for `result` AND in the FIRST set of `source` (the direct rule subsumes the
/// whole-`source` reading). Kept intentionally NARROW (leading *literal* only —
/// never a metavariable/native token) so the AT_QUOTED_BIND_GATE cannot fire on
/// an ordinary `Ident`-led cross-cat-LHS such as `x<-c`.
fn category_leading_literals(
    cat_name: &str,
    language: &LanguageDef,
) -> std::collections::BTreeSet<String> {
    let mut out = std::collections::BTreeSet::new();
    for rule in &language.terms {
        if rule.category.to_string() != cat_name {
            continue;
        }
        // Prefer the judgement-style `syntax_pattern[0]`; fall back to the
        // legacy `items[0]` Terminal for non-judgement rules.
        if let Some(sp) = rule.syntax_pattern.as_ref() {
            if let Some(mettail_ast::grammar::SyntaxExpr::Literal(text)) = sp.first() {
                out.insert(text.clone());
            }
        } else if let Some(mettail_ast::grammar::GrammarItem::Terminal(text)) =
            rule.items.first()
        {
            out.insert(text.clone());
        }
    }
    out
}

/// Stage 1.1: compute the FIRST set for a category — the set of token
/// patterns that can begin a parse of a rule for this category. Walks
/// the category's atomic rules + recursively their cross-cat projection
/// sources. Used by cross-cat projection codegen to emit specific
/// dispatch arms in the *result* category's PrefixDispatch when the
/// peek'd token belongs to the *source* category.
pub fn first_set_of_category(cat_name: &str, language: &LanguageDef) -> Vec<FirstToken> {
    let mut acc = Vec::new();
    let mut visited = std::collections::HashSet::new();
    // FIRST sets are consumed by cross-cat projection emission and other
    // codegen paths that dispatch on tokens in OTHER categories' contexts.
    // Pass `EmissionContext::FirstSet` so home-only bare-polymorphic arms
    // (e.g., `CanonicalBigInt`'s bare-Integer arm) are excluded — including
    // them here would shadow primitive-integer cross-cat projections.
    collect_first_set(cat_name, language, &mut acc, &mut visited);
    // B10 / Option κ Fix A (2026-05-07): dedup by `(pattern_str, guard_str)`.
    // The synthetic-Var pre-walk in `collect_first_set` AND the per-rule
    // VarRule pass both push `Some(Ident)`; the recursive cross-cat-projection
    // walk re-adds entries already present. Result was a Fork emission with
    // byte-identical Push branches, multiplying cursor count without changing
    // outcomes. The dedup key matches the `(pat_str, guard_str)` shape used
    // by `unified_buckets` so consumer bucket-fill stays deduplication-safe.
    let mut seen: std::collections::BTreeSet<(String, String)> = std::collections::BTreeSet::new();
    acc.retain(|ft| {
        let key = (
            ft.pattern.to_string(),
            ft.extra_guard
                .as_ref()
                .map(|g| g.to_string())
                .unwrap_or_default(),
        );
        seen.insert(key)
    });
    acc
}

fn collect_first_set(
    cat_name: &str,
    language: &LanguageDef,
    acc: &mut Vec<FirstToken>,
    visited: &mut std::collections::HashSet<String>,
) {
    // FIRST-set construction always uses `FirstSet` context. Routed through
    // `literal_patterned_pattern_and_guard_for_kind`'s `ctx` parameter to
    // preserve the home-vs-cross-cat distinction for the Integer family.
    let ctx = EmissionContext::FirstSet;
    let mut pending = std::collections::VecDeque::new();
    pending.push_back(cat_name.to_string());

    while let Some(current_cat_name) = pending.pop_front() {
        if !visited.insert(current_cat_name.clone()) {
            continue;
        }
        // Synthetic literal rule: cat_name gets a synthesized atomic-literal
        // rule when it has either:
        //   (a) An explicit `literals { ... }` block — `from_literals: true` TokenDef.
        //   (b) An implicit native_type (e.g., `![i32] as Num`) without an
        //       explicit literals block. Stage 4 fix: this used to skip the
        //       FIRST-set entry, so cross-cat projection rules whose source
        //       category was native-only didn't dispatch on bare Integer
        //       tokens (e.g., LedTest's `CastNum . a:Num |- a : Expr` failed
        //       to fire on input `0`).
        if let Some(lang_type) = language
            .types
            .iter()
            .find(|t| t.name.to_string() == current_cat_name)
        {
            if let Some(nt) = lang_type.native_type.as_ref() {
                let kind = NativeKind::from_syn_type(nt);
                if let Some(family) = literal_family_for(&kind) {
                    for (pattern, extra_guard) in literal_patterned_pattern_and_guard_for_kind(
                        &current_cat_name,
                        family,
                        Some(&kind),
                        ctx,
                    ) {
                        acc.push(FirstToken {
                            pattern,
                            extra_guard,
                            leading_literal: None,
                            is_var_contribution: false,
                        });
                    }
                }
            }
        }
        // Synthetic Var rule: every declared category that lacks an explicit
        // user Var rule gets a synthetic Var rule (Phase 5a in synthetic.rs).
        // Add Ident to FIRST.
        //
        // Stage 3.20 / Commit 4 part 2 (Plan agent Fix A, 2026-05-06): the
        // pre-fix gate `lang_type.native_type.is_none()` was wrong — it
        // caused FIRST(Int) etc. to omit Ident even though `gen/types/enums.rs`
        // unconditionally emits `Int::IVar(...)` AST variants. Now the FIRST
        // set mirrors the AST surface for every category.
        if let Some(_lang_type) = language
            .types
            .iter()
            .find(|t| t.name.to_string() == current_cat_name)
        {
            // Has-user-var-rule check: if any user rule for this cat matches
            // NonTerminal(Var), don't add (the user rule covers it).
            let has_user_var = language.terms.iter().any(|r| {
                r.category.to_string() == current_cat_name
                    && r.items
                        .first()
                        .map(|item| {
                            matches!(
                                item,
                                mettail_ast::grammar::GrammarItem::NonTerminal {
                                    kind: mettail_ast::grammar::NonTerminalKind::Var,
                                    ..
                                }
                            )
                        })
                        .unwrap_or(false)
            });
            if !has_user_var {
                acc.push(FirstToken {
                    pattern: quote! {
                        Some(mettail_prattail::automata::TokenKind::Ident)
                    },
                    extra_guard: None,
                    leading_literal: None,
                    // CROSSCAT_LEX_COMPAT_GATE: the synthetic Var rule's `Ident`
                    // is a VAR CONTRIBUTION (the category begins with an Ident
                    // ONLY because it is a variable, not a literal).
                    is_var_contribution: true,
                });
            }
        }
        // B7 Pattern 3 fix: synthetic collection-literal rules (`ListLit`,
        // `BagLit`, `MapLit`) emitted by `synthetic.rs:118-200` are NOT in
        // `language.terms` — they live in the macro's `per_cat` table. The
        // walk over `language.terms` below therefore misses them, and any
        // cross-cat projection rule whose source is a collection category
        // (e.g. Calculator's `CastBag . b:Bag |- b : Proc;`) ends up missing
        // `bag(`/`list(`/`map(` triggers in its FIRST set. The fix here is
        // to inline the synthetic-collection-rule's FIRST contribution by
        // reading `LangType::collection_kind` directly. The first-token of
        // the open delim (after trimming a trailing `(` to match the lexer's
        // 2-token tokenization of `list(`) is the FIRST element.
        if let Some(lang_type) = language
            .types
            .iter()
            .find(|t| t.name.to_string() == current_cat_name)
        {
            if let Some(coll_kind) = lang_type.collection_kind.as_ref() {
                // Stage 2 (2026-06-27): one delimiters() accessor in place of a
                // per-variant `match coll_kind { List(d) => d.open.clone(), ... }`.
                let open = coll_kind.delimiters().open.clone();
                // Mirror synthetic.rs's split-on-trailing-`(` logic so the
                // FIRST token equals the lexer's first emitted Fixed token.
                let first_open = open.trim_end_matches('(').to_string();
                acc.push(FirstToken::fixed_leading(&first_open));
            }
        }
        // Walk all rules where rule.category == current_cat_name.
        for rule in &language.terms {
            if rule.category.to_string() != current_cat_name {
                continue;
            }
            let shape = classify_atomic(rule, language);
            match shape {
                AtomicShape::LiteralPatterned { cat_name: c, family, ref native_type, .. } => {
                    let nk = NativeKind::from_syn_type(native_type);
                    for (pattern, extra_guard) in
                        literal_patterned_pattern_and_guard_for_kind(&c, family, Some(&nk), ctx)
                    {
                        acc.push(FirstToken {
                            pattern,
                            extra_guard,
                            leading_literal: None,
                            is_var_contribution: false,
                        });
                    }
                },
                AtomicShape::TerminalKeyword { terminal_text, .. } => {
                    acc.push(FirstToken::fixed_leading(&terminal_text));
                },
                AtomicShape::VarRule { .. } => {
                    acc.push(FirstToken {
                        pattern: quote! {
                            Some(mettail_prattail::automata::TokenKind::Ident)
                        },
                        extra_guard: None,
                        leading_literal: None,
                        // CROSSCAT_LEX_COMPAT_GATE: an explicit user Var rule's
                        // `Ident` is likewise a VAR CONTRIBUTION.
                        is_var_contribution: true,
                    });
                },
                AtomicShape::LiteralInteger => {
                    acc.push(FirstToken {
                        pattern: quote! {
                            Some(mettail_prattail::automata::TokenKind::Integer)
                        },
                        extra_guard: None,
                        leading_literal: None,
                        is_var_contribution: false,
                    });
                },
                AtomicShape::LiteralBoolean => {
                    acc.push(FirstToken {
                        pattern: quote! {
                            Some(mettail_prattail::automata::TokenKind::True)
                            | Some(mettail_prattail::automata::TokenKind::False)
                            | Some(mettail_prattail::automata::TokenKind::BooleanLit)
                        },
                        extra_guard: None,
                        leading_literal: None,
                        is_var_contribution: false,
                    });
                },
                AtomicShape::LiteralString => {
                    acc.push(FirstToken {
                        pattern: quote! {
                            Some(mettail_prattail::automata::TokenKind::StringLit)
                        },
                        extra_guard: None,
                        leading_literal: None,
                        is_var_contribution: false,
                    });
                },
                AtomicShape::LiteralFloat => {
                    acc.push(FirstToken {
                        pattern: quote! {
                            Some(mettail_prattail::automata::TokenKind::Float)
                        },
                        extra_guard: None,
                        leading_literal: None,
                        is_var_contribution: false,
                    });
                },
                AtomicShape::CrossCatProjection { source_cat_name, .. } => {
                    // Queue the source category's FIRST set instead of
                    // recursing. Projection cycles are cut by `visited`.
                    pending.push_back(source_cat_name);
                },
                AtomicShape::CrossCatPrefixUnary { trigger, .. } => {
                    acc.push(FirstToken::fixed_leading(&trigger));
                },
                AtomicShape::PrefixOperator { trigger, .. } => {
                    // M6c.6.4.b (2026-05-14): same-cat unary prefix uses
                    // the trigger literal as its FIRST token, matching
                    // the existing CrossCatPrefixUnary FIRST-set shape.
                    acc.push(FirstToken::fixed_leading(&trigger));
                },
                AtomicShape::NullaryLiteralRun { trigger, .. } => {
                    // GAP-3: the FIRST token of a nullary multi-literal keyword
                    // run is its trigger literal (e.g. `Map`, `@`) — identical
                    // to what the NonAtomic arm below extracted for this rule
                    // before GAP-3 classified it (sp[0] is the trigger literal).
                    acc.push(FirstToken::fixed_leading(&trigger));
                },
                AtomicShape::NonAtomic => {
                    // Pratt prefix / collection / binder rules: their FIRST
                    // typically starts with a literal trigger from
                    // syntax_pattern[0]. Best-effort extract.
                    //
                    // H1 fix (2026-05-18 from
                    // `~/.claude/plans/replicated-conjuring-turtle.md`): if
                    // syntax_pattern[0] is a Param (non-terminal ref) and
                    // rule.items[0] is a Category-kind NonTerminal whose
                    // category differs from `cat_name`, queue that
                    // category's FIRST set. This covers multi-Param non-
                    // binder rules like POutput (`n:Name, q:Proc |- n "!"
                    // "(" q ")"`) whose first syntactic item is a non-
                    // terminal of a different cat. Pre-fix the NonAtomic
                    // branch silently emitted no FIRST contribution for
                    // these rules, so e.g. Proc's FIRST set was missing
                    // Ident (via Name's synthetic Var rule), which broke
                    // PNew-body Ident-dispatch tests like
                    // `new x in { x!(0) }`.
                    if let Some(sp) = rule.syntax_pattern.as_ref() {
                        match sp.first() {
                            Some(mettail_ast::grammar::SyntaxExpr::Literal(text)) => {
                                acc.push(FirstToken::fixed_leading(text));
                            },
                            Some(mettail_ast::grammar::SyntaxExpr::Param(_)) => {
                                // First syntactic item is a param ref.
                                // Look up the corresponding NonTerminal in
                                // rule.items[0] and queue its category's
                                // FIRST if it's a different cat.
                                if let Some(mettail_ast::grammar::GrammarItem::NonTerminal {
                                    ident: nt_ident,
                                    kind: mettail_ast::grammar::NonTerminalKind::Category,
                                }) = rule.items.first()
                                {
                                    let nt_cat = nt_ident.to_string();
                                    if nt_cat != current_cat_name {
                                        pending.push_back(nt_cat);
                                    }
                                }
                            },
                            _ => {},
                        }
                    }
                },
            }
        }
    }
}

/// Cross-category INFIX-operand hop for a result category `R`: the categories
/// `S` such that a cross-category infix rule `S op S' : R` exists (the grouped
/// `S` becomes the infix's left operand, e.g. `EqInt: Int "==" Int : Bool` ⇒
/// `Int` is an infix-hop source of `Bool`). Excludes `R`. This is the edge type
/// that REQUIRES the grouped operand to open as `S` (a bare `S` could not become
/// the infix's operand of a DIFFERENT category), so it is followed TRANSITIVELY.
fn grouping_source_infix_hop(
    categories: &[String],
    language: &mettail_ast::language::LanguageDef,
    result_idx: usize,
    out: &mut std::collections::BTreeSet<u16>,
) {
    let result_cat_name = &categories[result_idx];
    for rule in &language.terms {
        if rule.category.to_string() != *result_cat_name {
            continue;
        }
        if let Some(info) = super::infix::classify_rule_public(rule) {
            if info.is_cross_category && info.category != info.result_category {
                if let Some(source_idx) = categories.iter().position(|c| c == &info.category) {
                    if source_idx != result_idx {
                        out.insert(source_idx as u16);
                    }
                }
            }
        }
    }
}

/// Cross-category PROJECTION hop for a result category `R`: the categories `S`
/// such that a cross-category projection / cast `S : R` exists (e.g.
/// `BoolToUInt32: Bool : UInt32` ⇒ `Bool` is a projection-hop source of
/// `UInt32`). Excludes `R`. A projection means a bare `S` ALREADY IS an `R`
/// (the cast fires transparently), so a grouped `(S)` grows into `R` directly —
/// this edge is included only at the FIRST closure level and NOT compounded
/// transitively, which would otherwise pull the entire cast lattice into every
/// group-open (e.g. rhocalc `Proc` has `CastX : Proc` for ~15 numeric/collection
/// `X`, and chaining their projections back through each other's casts explodes
/// the group-open fan-out → deep-paren fork blow-up). The infix hop IS still
/// followed transitively FROM these first-level projection sources, which is
/// what M4 needs (`UInt32 →proj→ Bool →infix→ Int`).
fn grouping_source_projection_hop(
    language: &mettail_ast::language::LanguageDef,
    per_cat: &[Vec<mettail_ast::grammar::GrammarRule>],
    categories: &[String],
    result_idx: usize,
    out: &mut std::collections::BTreeSet<u16>,
) {
    if let Some(rules) = per_cat.get(result_idx) {
        for rule in rules {
            if let AtomicShape::CrossCatProjection { source_cat_name, .. } =
                classify_atomic(rule, language)
            {
                if let Some(source_idx) = categories.iter().position(|c| c == &source_cat_name) {
                    if source_idx != result_idx {
                        out.insert(source_idx as u16);
                    }
                }
            }
        }
    }
}

/// The categories a `(`-group may open as when the enclosing requested category
/// is `result_idx` — a BOUNDED transitive closure over the two grouping-source
/// edge types (see [`grouping_source_infix_hop`] and
/// [`grouping_source_projection_hop`]).
///
/// One-hop was insufficient for chained cross-category continuations. Example
/// (calculator, reconnection residual M4): parsing `(1) == 4` under a `UInt32`
/// goal. `==` is `EqInt: Int "==" Int : Bool`; the whole expression reaches
/// `UInt32` via `BoolToUInt32: Bool : UInt32`. So the grouped `(1)` must be
/// openable as an **Int** — but `Int` is TWO hops from `UInt32`
/// (`UInt32 ← Bool` by projection, then `Bool ← Int` by the `EqInt` operand).
/// The old one-hop set for `UInt32` was `{UInt32, Bool}` WITHOUT `Int`, so `(1)`
/// committed to a non-`Int` category and the `Int`-operand `==` could not attach
/// — the exhaustive parse genuinely had NO derivation (`(1)==4` failed while
/// `1==4` and `(1==4)` succeeded). Bare operands already worked (prefix-dispatch
/// chains the projections directly); grouping needed the same reachability.
///
/// BOUND (perf): the closure follows the INFIX-operand relation TRANSITIVELY
/// (that edge genuinely forces the operand's category) but includes PROJECTION
/// sources only at the FIRST level (level 0 = `result_idx`), NOT compounding them
/// through further projections. Rationale: a projection `X : R` means a bare `X`
/// already IS an `R`, so a grouped `(X)` grows into `R` directly — chaining
/// projection→projection pulls the ENTIRE cast lattice into every group-open
/// (rhocalc `Proc` has `CastX : Proc` for ~15 `X`; compounding blew Proc's `(`
/// group-open from 7 to 18 branches → 18^depth deep-paren fork explosion, timing
/// out the adversarial `proc_display` proptest). Infix expansion FROM the
/// first-level projection sources is still followed, which is exactly what M4
/// needs (`UInt32 →proj→ Bool →infix→ Int`). The result category is index 0 of
/// the returned vector (the primary grouping target), preserving the ordering
/// contract used by `emit_paren_dispatch_arms`.
fn grouping_source_categories_for_result(
    categories: &[String],
    language: &mettail_ast::language::LanguageDef,
    per_cat: &[Vec<mettail_ast::grammar::GrammarRule>],
    result_idx: usize,
) -> Vec<u16> {
    let result_src_idx = result_idx as u16;
    let mut closure: std::collections::BTreeSet<u16> = std::collections::BTreeSet::new();
    let mut visited: std::collections::BTreeSet<u16> = std::collections::BTreeSet::new();
    visited.insert(result_src_idx);
    // Level 0: BOTH edge types from `result_idx` (projections included ONCE).
    let mut seed: std::collections::BTreeSet<u16> = std::collections::BTreeSet::new();
    grouping_source_infix_hop(categories, language, result_idx, &mut seed);
    grouping_source_projection_hop(language, per_cat, categories, result_idx, &mut seed);
    // BOUND (perf, 2026-07-01): the chained-operand expansion (M4:
    // `R →proj→ P →infix→ Q` needs `Q` in R's group-open) is applied ONLY when
    // `R` has FEW projection sources — a proxy for "narrow numeric-tower
    // category" (calculator `UInt32`/`Int`/…: 1-3 projection sources) versus a
    // "hub" category with a large cast lattice (rhocalc `Proc`: ~15 `CastX`
    // sources, whose infix expansion pulls in the whole comparison-operand set
    // and blows the `(` group-open fan-out to 18 → deep-paren fork explosion,
    // timing out `proc_display`). Threshold 4: keeps M4 (UInt32 has 1 projection
    // source, Bool) and never triggers for the Proc hub. Proc/hub categories
    // fall back to the level-0 seed only (their prior one-hop behavior), so a
    // grouped Proc operand still relies on the projection/bare path (unchanged),
    // while the narrow numeric categories gain the chained-infix operand needed
    // for `(1)==4`-style cross-cat comparisons.
    const HUB_PROJECTION_THRESHOLD: usize = 4;
    let projection_sources: Vec<usize> = {
        let mut pv: std::collections::BTreeSet<u16> = std::collections::BTreeSet::new();
        grouping_source_projection_hop(language, per_cat, categories, result_idx, &mut pv);
        pv.into_iter().map(|c| c as usize).collect()
    };
    for src in seed {
        closure.insert(src);
        visited.insert(src);
    }
    if projection_sources.len() < HUB_PROJECTION_THRESHOLD {
        for p in projection_sources {
            let mut hop: std::collections::BTreeSet<u16> = std::collections::BTreeSet::new();
            grouping_source_infix_hop(categories, language, p, &mut hop);
            for src in hop {
                closure.insert(src);
                visited.insert(src);
            }
        }
    }
    let mut sources = Vec::with_capacity(closure.len() + 1);
    sources.push(result_src_idx);
    sources.extend(closure);
    sources
}

/// Stage 3.20 / Commit 4 part 2 (Plan agent Fix, 2026-05-06): emit `(`-trigger
/// dispatch arms that handle BOTH the B7 paren-grouping AND any binder
/// rule whose first trigger is `"("`. Categories with source-category
/// transparent projections or category-changing infix operators also get
/// grouping branches for those declared source categories; otherwise an
/// outer requested category like `Pred` would force `(Num * Num)` to parse as
/// a `Pred` group before the `! == ...` continuation can build the `Pred`.
/// For categories with one grouping target and no `(`-binder, this still
/// degenerates to the simple grouping arm. For categories like Lambda's
/// `Term` that have a paren-triggered App rule, this emits a
/// `WpdaStepAction::Fork` over {grouping_branches, binder_rule_branches...}
/// so lex-min disambiguates per
/// `feedback_use_wpds_disambiguation_not_heuristics.md`. Grouping branches
/// use `lex_one()` (max src/rule indices) so any concrete binder rule beats
/// them on lex-min ties.
///
/// Verified empirically across `target/generated/*/wpds.rs`: only Lambda
/// has a `(`-triggered binder rule; for all other shipped grammars this emits
/// the direct grouping arm.
pub fn emit_paren_dispatch_arms(
    categories: &[String],
    language: &mettail_ast::language::LanguageDef,
    per_cat: &[Vec<mettail_ast::grammar::GrammarRule>],
    // Task #10 item 1: the fork-emission ordinal collector. Only the FORK
    // case's `(`-binder branches derive rows (a rule's initiating branch at
    // its static position AFTER the grouping branches). The grouping-marker
    // branches themselves push category MARKERS, not rules — no `(cat,
    // rule)` row is derivable from them; the NParen-class kept-wrapper
    // rules those groupings lead to resolve through the table's site-2
    // fallback `0`, which IS the grouping branches' grouping-first index
    // (byte-identical by construction). The simple no-conflict arm is not
    // a fork — no rows.
    fork_rows: &mut super::fork_emission::ForkEmissionOrdinalModel,
) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, _cat_name) in categories.iter().enumerate() {
        let result_src_idx = cat_i as u16;
        let grouping_source_indices =
            grouping_source_categories_for_result(categories, language, per_cat, cat_i);
        // Find binder rules in this category with `(` first trigger.
        let paren_binder_rules: Vec<(u16, super::binder::BinderShape)> = per_cat[cat_i]
            .iter()
            .enumerate()
            .filter_map(|(rule_i, rule)| {
                let shape = super::binder::classify_binder_in(rule, language)?;
                let first_trigger = rule.syntax_pattern.as_ref()?.first()?;
                match first_trigger {
                    mettail_ast::grammar::SyntaxExpr::Literal(text) if text == "(" => {
                        Some((rule_i as u16, shape))
                    },
                    _ => None,
                }
            })
            .collect();
        if paren_binder_rules.is_empty() && grouping_source_indices.len() == 1 {
            // No conflict: emit the simple grouping arm.
            let grouping_src_idx = grouping_source_indices[0];
            arms.push(quote! {
                Some(mettail_prattail::automata::TokenKind::Fixed(__open))
                    if __open == "(" && state_cat_src_idx == #result_src_idx => {
                    return WpdaStepAction::ConsumeAndPush {
                        symbol: StackSymbolV2::grouping_marker(
                            #grouping_src_idx, *cur_bp,
                        ),
                        weight: lex_one(),
                        new_state: WpdaState::PrefixDispatch {
                            pos: tokens.next_pos(*pos, 0).unwrap_or(*pos + 1),
                            cur_bp: 0,
                        },
                        // Phase F.8: `(` grouping discards the trigger token.
                        trigger_mode: mettail_prattail::wpda_walker::TriggerMode::Discard,
                    };
                }
            });
            continue;
        }
        // Fork over {grouping_branches, binder_rule_branches...}. consume_trigger:
        // true → walker advances pos by 1 before allocating cursors.
        let mut branches: Vec<TokenStream> = Vec::new();
        // Grouping branches come first, with the current result category
        // first. Source-category branches are grammar-derived alternatives
        // needed by transparent projections and category-changing infix.
        //
        // Quote-of-numeral PInputs fix (2026-06-20): when this category owns a
        // `(`-triggered BINDER rule (e.g. RhoCalc's `PInputs . ns:Vec(Name) …
        // |- "(" … ")" "." "{" p "}"`), the `(` is structurally claimed by the
        // binder, not by a bare grouped sub-expression. The extra
        // SOURCE-category grouping speculations (added for the pure-grouping
        // case so an outer requested category like `Pred` can grow
        // `(Num) op …`) then fork spurious cross-cat-LHS grouping cursors at the
        // binder's open position. With a numeric body inside the bound name
        // (`(@(0u32)?a).{a}` — `@(0u32)` is a Name whose quoted Proc body is a
        // numeric cast) those cursors strand the binder continuation, so the
        // whole parse dies at the `(` (every cursor dead at the open paren).
        // A pure grouping paren (Pred/Expr in LedTest — NO `(`-binder) still
        // needs the source-cat branches, so only drop them when a `(`-binder is
        // present; the result-category grouping branch plus the binder branch
        // fully cover the binder category's `(` interpretations.
        let grouping_source_indices: Vec<u16> = if paren_binder_rules.is_empty() {
            grouping_source_indices
        } else {
            vec![result_src_idx]
        };
        for grouping_src_idx in &grouping_source_indices {
            let is_cross_cat = *grouping_src_idx != result_src_idx;
            let action_kind = if is_cross_cat {
                quote! { mettail_prattail::wpda_walker::ForkActionKind::PushCrossCatLhs }
            } else {
                quote! { mettail_prattail::wpda_walker::ForkActionKind::Push }
            };
            // ── Divergence I / Stage D (2026-07-25): PAY FOR THE PROJECTION HERE ──
            //
            // A grouping branch whose source category differs from the result category
            // WILL owe a cross-category projection to get from `grouping_src_idx` back
            // to `result_src_idx`; the `(` merely defers the bill. Charging `lex_one()`
            // — the multiplicative identity — made that route FREE, so the same
            // projection was charged on two different ledgers depending on whether a
            // `(` was in the way: `BP_TIER_CROSSCAT_PROJECTION` (0.025) on `primary` at
            // a bare prefix dispatch, versus 0.0 here. With `CgllKTuple::lt` comparing
            // `lateness` first and weight second, a tie in lateness let `0.0 < 0.025`
            // decide, so a PARENTHESISED operand could elect a different reading than
            // the identical bare one — which is how `"{(1) | 2}"` came to parse as
            // `PPar({CastInt(1), CastBigInt(2)})`.
            //
            // Charging the tier the branch will owe removes the free route AT ITS
            // SOURCE, without touching the `lateness`-before-weight ordering (a
            // deliberate, separately pinned decision — see
            // `kbest_w_vs_ktuple_order_keys_differ`). SAME-category grouping branches
            // are untouched: they owe no projection, so `lex_one()` is their honest
            // price and every pure-grouping parse keeps its exact prior weight.
            //
            // This is PROPHYLAXIS, not the correctness fix. Divergence I is closed in
            // the grammar (partitioned literal domains); after that there is only ONE
            // carrier per numeral for the election to find, so no ledger argument is
            // load-bearing. This makes the two ledgers agree anyway, so a FUTURE
            // grammar with genuinely co-existing readings cannot be decided by a
            // parenthesis.
            //
            // ⚠ OPEN DEFECT (2026-07-26) — THIS WEIGHT ERASES THE SUB-DERIVATION'S
            //   TIEBREAK. Read before changing the line below.
            //
            //   `LexicographicWeight` is (open_len, primary, lex_alt_idx, src_idx,
            //   rule_idx). `Semiring::times` (`rigail/src/lex_weight.rs:496-526`)
            //   short-circuits on the ⊗ identity and OTHERWISE LEFT-PROJECTS the
            //   three tiebreak components; `is_one()` (:536-538) keys PURELY on
            //   `primary.is_one()` — i.e. on tropical cost 0.0, nothing else.
            //
            //   `lex_w(BP_TIER_CROSSCAT_PROJECTION, …)` has primary = 0.025, so it
            //   is NOT the identity. The walker composes a branch weight as the
            //   RIGHT operand (`cursor.weight.times(&branch.weight)`), and at a
            //   fresh group-open the cursor weight IS the identity — so the cursor
            //   becomes exactly this weight, and every subsequent `times` inside
            //   the group left-projects ITS triple `(lex_alt_idx = 0,
            //   src_idx = grouping_src_idx, rule_idx = 0)` over the whole
            //   parenthesised sub-derivation. The real tiebreak of everything
            //   inside the group is discarded and replaced by a constant that also
            //   FABRICATES a specific bias (`rule_idx = 0` is a real rule index,
            //   not a sentinel). `times`'s own doc-comment names this hazard:
            //   "without it, `1.times(a)` would project `1.src_idx = u16::MAX` and
            //   lose `a`'s real tiebreak".
            //
            //   NOT the cause of the grouped-cross-category-operand parse failure
            //   (`(0 + bigrat(a))` → "no realizable readings"). That was REFUTED by
            //   single-variable experiment: restoring `lex_one()` here, regenerating
            //   (charge verified absent from `target/generated/*/wpda.rs`) and
            //   re-running a 19-string A/B gave a BYTE-IDENTICAL table — same 8
            //   failures, same elected displays. The real root was the missing
            //   `slot.xcat == 0` conjunct in `cgll_pure_crosscat_boundaries`' stop
            //   test; fixed separately.
            //
            //   So this is LATENT, not benign: on the corpus measured it changed no
            //   election, but it silently destroys tiebreak information, so any
            //   future grouped sub-derivation whose readings tie on `primary` and
            //   are separated only by `(src_idx, rule_idx)` will be decided by the
            //   parenthesis — the very thing Stage D was written to prevent.
            //
            //   NO SMALL CORRECT FIX EXISTS IN THE CURRENT SEMIRING: charging a cost
            //   without owning a tiebreak is not expressible, because `is_one` is a
            //   predicate on `primary` alone. The two real options are
            //     (a) revert this branch to `lex_one()` — E1 says that is
            //         behaviour-neutral on Calculator, but Stage D is a deliberate
            //         documented prophylaxis and 19 strings in one language is not
            //         grounds to drop it; or
            //     (b) give the type a tiebreak-transparent element (an explicit
            //         "carries no tiebreak" flag, or make `is_one` structural), which
            //         requires re-proving associativity of `times` and distributivity
            //         over the lex-min `plus` — the axioms `lex_weight.rs` documents.
            //   A discriminating case is found by looking for two readings of one
            //   grouped span with equal `primary` and different `(src_idx, rule_idx)`;
            //   `PRATTAIL_CGLL_PURE_FDUMP` prints `weight_sum` per Symbol, so an
            //   A/B of this line against `lex_one()` shows the divergence directly.
            let grouping_weight = if is_cross_cat {
                quote! {
                    lex_w(
                        mettail_prattail::automata::lex_weight::BP_TIER_CROSSCAT_PROJECTION,
                        #grouping_src_idx, 0u16,
                    )
                }
            } else {
                quote! { lex_one() }
            };
            branches.push(quote! {
                mettail_prattail::wpda_walker::ForkBranch {
                    symbol: StackSymbolV2::grouping_marker(
                        #grouping_src_idx, *cur_bp,
                    ),
                    weight: #grouping_weight,
                    new_state: WpdaState::PrefixDispatch {
                        pos: tokens.next_pos(*pos, 0).unwrap_or(*pos + 1),
                        cur_bp: 0,
                    },
                    action_kind: #action_kind,
                }
            });
        }
        // Branches 1..N: each binder rule with `(` trigger.
        for (paren_binder_position, (rule_idx, shape)) in
            paren_binder_rules.iter().enumerate()
        {
            let body_src_idx = super::binder::binder_initial_body_cat(shape)
                .and_then(|name| super::binder::lookup_src_idx(name, categories))
                .unwrap_or(result_src_idx);
            let rule_idx_lit = *rule_idx;
            // Task #10 item 1: the binder branch's STATIC position = after
            // ALL grouping branches (grouping-first layout), in declaration
            // order.
            fork_rows.record_site2_row(
                result_src_idx,
                rule_idx_lit,
                (grouping_source_indices.len() + paren_binder_position) as u16,
                "paren-dispatch \"(\"",
            );
            branches.push(quote! {
                mettail_prattail::wpda_walker::ForkBranch {
                    symbol: StackSymbolV2::rule_at(
                        #result_src_idx, #rule_idx_lit, 1u8, Some(_outer_bp),
                    ),
                    weight: lex_w(
                        0.0, #result_src_idx, #rule_idx_lit,
                    ),
                    new_state: WpdaState::BinderRule {
                        result_src_idx: #result_src_idx,
                        rule_idx: #rule_idx_lit,
                        body_src_idx: #body_src_idx,
                        outer_bp: _outer_bp,
                    },
                    action_kind:
                        mettail_prattail::wpda_walker::ForkActionKind::PushWithTriggerTerminal,
                }
            });
        }
        arms.push(quote! {
            Some(mettail_prattail::automata::TokenKind::Fixed(__open))
                if __open == "(" && state_cat_src_idx == #result_src_idx => {
                return WpdaStepAction::Fork {
                    branches: vec![ #( #branches ),* ],
                    consume_trigger: true,
                };
            }
        });
    }
    quote! { #(#arms)* }
}

/// Map a `NativeKind` to the lexer's `LiteralFamily`.
fn literal_family_for(kind: &NativeKind) -> Option<LiteralFamily> {
    match kind {
        NativeKind::Int8
        | NativeKind::Int16
        | NativeKind::Int32
        | NativeKind::Int64
        | NativeKind::Int128
        | NativeKind::Isize
        | NativeKind::UInt8
        | NativeKind::UInt16
        | NativeKind::UInt32
        | NativeKind::UInt64
        | NativeKind::UInt128
        | NativeKind::Usize
        | NativeKind::CanonicalBigInt => Some(LiteralFamily::Integer),
        NativeKind::CanonicalBigRat => Some(LiteralFamily::Rational),
        NativeKind::CanonicalFixedPoint => Some(LiteralFamily::FixedPoint),
        NativeKind::Float32 | NativeKind::Float64 => Some(LiteralFamily::Float),
        NativeKind::Bool => Some(LiteralFamily::Boolean),
        NativeKind::Str => Some(LiteralFamily::String),
        NativeKind::Other => None,
    }
}

/// Emit per-rule arms in the `PrefixDispatch` match for one category.
/// CROSSCAT_LEX_COMPAT_GATE (2026-07-03): does `cat_name` have a HOME variable
/// reading — i.e. can a bare `Ident` parse as a `cat_name` term WITHOUT any
/// cross-cat projection? True iff the category either has an explicit user Var
/// rule (a `language.terms` rule whose first item is `NonTerminal{kind:Var}`) OR
/// receives the synthetic Var rule (the `!has_user_var` branch of
/// `collect_first_set`, which every declared `language.types` category takes).
/// Grammar-derived, mirrors `collect_first_set`'s Var logic EXACTLY so the gate
/// is precise. When true, a bare Ident in `cat_name` is already covered by the
/// home Var reading, so a cross-cat cast delegate `source : cat_name` on the
/// `Ident` token — where the `Ident` is ONLY a var-contribution of `source`
/// (the source cannot begin with a LITERAL Ident) — is a proven over-generation
/// (it duplicates the home var reading via a spurious ∅-realizing cast path).
fn result_has_home_var_reading(cat_name: &str, language: &LanguageDef) -> bool {
    // Must be a declared category to receive the synthetic Var rule.
    let is_declared = language
        .types
        .iter()
        .any(|t| t.name.to_string() == cat_name);
    if !is_declared {
        return false;
    }
    // Either takes the synthetic Var (always, when declared and lacking a user
    // Var rule) or already has an explicit user Var rule → in BOTH cases a bare
    // Ident reads as a home `cat_name` var. (The disjunction collapses to
    // `true` for any declared category, but is written out to track the exact
    // grammar provenance and stay correct if the synthetic-Var policy changes.)
    let has_user_var = language.terms.iter().any(|r| {
        r.category.to_string() == cat_name
            && r.items
                .first()
                .map(|item| {
                    matches!(
                        item,
                        mettail_ast::grammar::GrammarItem::NonTerminal {
                            kind: mettail_ast::grammar::NonTerminalKind::Var,
                            ..
                        }
                    )
                })
                .unwrap_or(false)
    });
    // Synthetic Var applies when !has_user_var; either branch yields a home var.
    has_user_var || !has_user_var
}

/// CROSSCAT_LEX_COMPAT_GATE (2026-07-03): is a bare `Ident` reading of the
/// PROJECTION SOURCE category `source_cat` EXCLUSIVELY that category's OWN
/// variable — i.e. does `source_cat` have NO rule (other than its Var rule)
/// that can begin with an `Ident`?
///
/// This is the DISCRIMINATOR that keeps the gate SOUND. The design's premise is
/// that a projection cast `source : result` on the `Ident` token is a proven
/// ∅-realizing over-generation "because the source cannot LITERALLY begin with
/// an Ident — its Ident-first comes solely from its Var rule". That premise
/// holds for LEAF value categories (BigInt/List/Map/…: their only Ident-first
/// is the synthetic Var; their content rules begin with a digit / `[` / `{` /
/// keyword). It is FALSE for STRUCTURAL categories whose rules are Ident-led:
/// `InputBind` has `InputBind . lhs:Name "<-" n` (begins with the Ident `lhs`),
/// and `ForRow` has `ForRowSingleNoWhere . b:InputBind` (transitively
/// Ident-first). For those, a bare Ident is the START of a REAL structured term,
/// NOT just a variable, so the projection (e.g. `InputBind : ForRow`) is the
/// ONLY path to dispatch `p <- …` and MUST NOT be pruned (pruning it broke
/// `for(p <- …)` — a genuine, non-∅ reading).
///
/// Grammar-derived: returns `true` iff EVERY rule of `source_cat` that admits an
/// `Ident` first token is its Var rule. Concretely: no NON-Var rule of
/// `source_cat` has `Ident` in its FIRST set. We compute this by walking each
/// non-Var rule's FIRST contribution (its leading terminal, or — for an
/// NT-/Param-led rule — the FIRST of the leading non-terminal's category,
/// transitively), excluding the source category's own Var-rule Ident. A rule
/// with a leading `Ident`-admitting non-terminal (e.g. a Name-led `lhs:Name`)
/// makes the source NOT var-only.
pub fn source_ident_first_is_var_only(source_cat: &str, language: &LanguageDef) -> bool {
    let mut visited = std::collections::HashSet::new();
    source_ident_first_is_var_only_rec(source_cat, language, &mut visited)
}

/// Recursive core of `source_ident_first_is_var_only` with a `visited` set to
/// cut projection cycles (e.g. Int↔BigInt via `IntToBigInt`).
///
/// KEY (transitivity through var-projections): a rule whose leading non-terminal
/// is a DIFFERENT category `C` makes the source Ident-led ONLY IF `C` is itself
/// NOT var-only-Ident. If `C` IS var-only-Ident (its only Ident-first is a var,
/// transitively), then this rule merely PROJECTS `C`'s var — a bare Ident
/// through it is still just a variable, so the source remains var-only. This is
/// what correctly classifies `BigInt` as var-only despite `IntToBigInt . i:Int
/// |- i : BigInt` (Int is var-only ⇒ the projection carries only a var), while
/// still classifying `ForRow` as NOT var-only (its `ForRowSingleNoWhere .
/// b:InputBind` leads with InputBind, which is Ident-LED via `lhs:Name "<-" n`,
/// so NOT var-only).
fn source_ident_first_is_var_only_rec(
    source_cat: &str,
    language: &LanguageDef,
    visited: &mut std::collections::HashSet<String>,
) -> bool {
    if !visited.insert(source_cat.to_string()) {
        // Cycle: treat a self/mutual projection cycle as var-only (it carries no
        // NEW literal Ident source — only the vars already accounted for). Safe:
        // a cycle of pure var-projections realizes only vars.
        return true;
    }
    for rule in &language.terms {
        if rule.category.to_string() != source_cat {
            continue;
        }
        // The source's own Var rule is the allowed Ident source — skip it.
        let is_var_rule = rule
            .items
            .first()
            .map(|it| {
                matches!(
                    it,
                    mettail_ast::grammar::GrammarItem::NonTerminal {
                        kind: mettail_ast::grammar::NonTerminalKind::Var,
                        ..
                    }
                )
            })
            .unwrap_or(false);
        if is_var_rule {
            continue;
        }
        match rule.items.first() {
            Some(mettail_ast::grammar::GrammarItem::Terminal(_)) => {
                // Literal-led: not Ident-first.
                continue;
            }
            Some(mettail_ast::grammar::GrammarItem::NonTerminal {
                ident: nt_ident,
                kind: mettail_ast::grammar::NonTerminalKind::Category,
            }) => {
                let nt_cat = nt_ident.to_string();
                if nt_cat == source_cat {
                    // Same-cat leading NT (left-recursive infix/method): no new
                    // Ident source beyond the var being folded.
                    continue;
                }
                // ★ PURE-PROJECTION gate for transitivity. Count the rule's
                // non-terminal / capture body items (a "structural" item is
                // anything that consumes input: a NonTerminal, an IdentCapture,
                // a Binder, a Collection, a SepList — a Terminal is a fixed
                // literal). Transitivity ("this rule merely projects `nt_cat`'s
                // var") is valid ONLY when the rule is a PURE PROJECTION — its
                // ENTIRE body is exactly the single leading non-terminal with NO
                // additional consuming items (e.g. `IntToBigInt . i:Int |- i :
                // BigInt`). If the rule has MORE items after the leading NT
                // (e.g. `InputBind . lhs:Name "<-" n` — a Name THEN `<-` THEN a
                // Name), a bare Ident reaching the source through it is the START
                // of a REAL structured term, NOT a var-projection ⇒ the source is
                // Ident-LED and NOT var-only. Without this gate, InputBind/ForRow
                // are mis-classified as var-only (their `lhs:Name`-led rules look
                // like they "project Name's var") and the gate over-prunes,
                // breaking `for(p <- …)`.
                let structural_item_count = rule
                    .items
                    .iter()
                    .filter(|it| {
                        !matches!(it, mettail_ast::grammar::GrammarItem::Terminal(_))
                    })
                    .count();
                let is_pure_projection = structural_item_count == 1
                    && rule.items.iter().all(|it| {
                        matches!(
                            it,
                            mettail_ast::grammar::GrammarItem::NonTerminal {
                                kind: mettail_ast::grammar::NonTerminalKind::Category,
                                ..
                            } | mettail_ast::grammar::GrammarItem::Terminal(_)
                        )
                    })
                    && rule.items.iter().all(|it| {
                        // No trailing literals either (a pure projection is a
                        // bare `source : result` with the source non-terminal as
                        // the sole element — token-transparent).
                        !matches!(it, mettail_ast::grammar::GrammarItem::Terminal(_))
                    });
                let sub_first = first_set_of_category(&nt_cat, language);
                let sub_has_ident = sub_first
                    .iter()
                    .any(|ft| ft.pattern.to_string().contains("Ident") && ft.extra_guard.is_none());
                if sub_has_ident {
                    // The leading NT can begin with an Ident. Whether that makes
                    // the source non-var-only depends on purity:
                    //   - pure projection AND `nt_cat` is var-only ⇒ still var.
                    //   - otherwise (structural rule, or `nt_cat` genuinely
                    //     Ident-led) ⇒ source is Ident-led, NOT var-only.
                    if is_pure_projection
                        && source_ident_first_is_var_only_rec(&nt_cat, language, visited)
                    {
                        continue;
                    }
                    return false;
                }
                continue;
            }
            Some(mettail_ast::grammar::GrammarItem::NonTerminal {
                kind: mettail_ast::grammar::NonTerminalKind::Var,
                ..
            }) => {
                continue;
            }
            _ => {
                // Binder / IdentCapture / other leading items. Resolve via the
                // judgement-style syntax_pattern where possible; otherwise be
                // conservative (treat as Ident-admitting ⇒ NOT var-only).
                if let Some(sp) = rule.syntax_pattern.as_ref() {
                    match sp.first() {
                        Some(mettail_ast::grammar::SyntaxExpr::Literal(_)) => continue,
                        Some(mettail_ast::grammar::SyntaxExpr::Param(_)) => return false,
                        _ => return false,
                    }
                } else {
                    return false;
                }
            }
        }
    }
    // No non-Var rule of `source_cat` admits a NEW (non-var) Ident first token ⇒
    // the ONLY Ident reading of `source_cat` is its Var (possibly via
    // var-projections) ⇒ var-only.
    true
}

pub fn emit_prefix_arms_for_category(
    language: &LanguageDef,
    category_src_idx: u16,
    category_name: &str,
    rules_in_category: &[(u16, &GrammarRule)],
    // S1-FACTORING F1 (2026-07-12, plan §D F1): this category's
    // `rule_idx → SpineDisposition` map from
    // `factoring::build_spine_emission`. EMPTY while `S1_FACTORING == false`
    // (⇒ every lookup below misses ⇒ the emission is byte-identical to the
    // pre-F1 output). `GroupFirst` members emit the group's ONE spine
    // trigger branch at their emission position; `GroupRest` members emit
    // nothing (the spine branch covers them).
    s1_dispositions: &std::collections::HashMap<u16, super::factoring::SpineDisposition>,
    // Task #10 item 1: this category's `GroupFirst rule -> ordered members`
    // map (`factoring::SpineEmission::group_members`) + the fork-emission
    // ordinal collector threaded down to `emit_unified_arm`.
    s1_group_members: &std::collections::HashMap<u16, Vec<u16>>,
    fork_rows: &mut super::fork_emission::ForkEmissionOrdinalModel,
    // Task #15 (frame-bound peel): returns `(arms, helpers)` — `arms` are the
    // PrefixDispatch `match peek` arms (each `#pat if #guard => self.prefix_arm_
    // c{cat}_a{ord}(..)`), `helpers` are the per-arm `#[inline(never)]` body
    // methods that get emitted into the sibling inherent `impl #engine_ident`.
) -> (TokenStream, TokenStream) {
    let mut arms = Vec::new();
    // Stage 1.2: cross-cat infix LHS delegation. Walk all infix rules
    // (not just rules in this category) whose result_cat == this category
    // and operand_cat ≠ this category. For each, emit FIRST(operand_cat)
    // arms in this category's PrefixDispatch that push CategoryEntry(operand_cat)
    // for the LHS sub-parse. After the LHS Int returns, InfixLoop on operand
    // sees the operator + cross-cat infix, ConsumeAndPush(Return for cross-cat
    // rule) → CrossCatDelegate for the RHS.
    let mut cross_cat_infix_sources: std::collections::HashSet<String> =
        std::collections::HashSet::new();
    for rule in &language.terms {
        if rule.category.to_string() != category_name {
            continue;
        }
        if let Some(info) = super::infix::classify_rule_public(rule) {
            if info.is_cross_category && info.category != info.result_category {
                cross_cat_infix_sources.insert(info.category.clone());
            }
        }
    }
    let categories = super::collect_category_names_with_literals(language);
    // B4 fix (2026-05-07): cross-cat infix LHS delegation with
    // bucket-then-Fork emission. Pre-fix the per-source loop emitted
    // duplicate Rust match arms with identical (pat, guard) keys when
    // multiple source categories shared a FIRST token (e.g.
    // `TokenKind::Ident` from auto-injected Var rules in
    // Bool/Fixed/Float/Int/Str). Rust's first-match-wins meant only the
    // alphabetically-first source's arm fired; arms for other sources
    // were dead code. For shipped Calculator with cross-cat-Ident
    // delegation across 4+ sources, this trapped the LHS sub-parse in
    // the FIRST source's grammar regardless of which the input intended,
    // cascading via Commit D's recovery rewire into "winner committed
    // but builder result was empty" failures (58 Calculator tests).
    //
    // Fix: bucket by (pat, guard) and emit:
    //   - Single-source bucket → Push (byte-identical to pre-fix).
    //   - Multi-source bucket → Fork over branches with one source each,
    //     using lex_w(0.0, category, src_idx) so
    //     source-order tiebreak (rule_idx slot = src_idx) selects deterministically
    //     while genuine forward-progress lex-min selects the live cursor
    //     across the parse — per `feedback_use_wpds_disambiguation_not_heuristics.md`.
    //
    // The per-cursor sub-parse fanout is bounded: only the cursor whose
    // source category actually matches the input survives; siblings die
    // via PrefixDispatch dead-end (their guarded recovery is bounded by
    // Commit D's max_recovery_depth + visited_recovery checks).
    // B7 (2026-05-07): unified bucket for cross-cat-LHS (Pass 0) +
    // atomic-shape (Pass 1) descriptors. Keying on `(pat, guard)`, a
    // bucket may contain a mix of CrossCatLhs and Atomic descriptors.
    // Singleton buckets emit byte-identical to the pre-B7 path; mixed
    // buckets emit a Fork with weights:
    //   - Atomic-home tier=0.0
    //   - Cross-cat-LHS tier=BP_TIER_CROSSCAT_LHS (0.05)
    // so lex-min picks atomic-home on parse-success ties and cross-cat
    // when only that branch survives. Per
    // `feedback_use_wpds_disambiguation_not_heuristics.md`. Eliminates
    // the silent-shadowing bug where Pass 0's cross-cat-LHS arm killed
    // Pass 1's home-cat atomic arm by Rust's first-match-wins semantics
    // when both shared a (pat, guard) key (e.g. `Some(Ident) if state==Proc`
    // shared by POutput's Name LHS delegation and PVar's atomic arm).
    let mut sorted_sources: Vec<&String> = cross_cat_infix_sources.iter().collect();
    sorted_sources.sort();
    let mut unified_buckets: std::collections::BTreeMap<(String, String), UnifiedBucket> =
        std::collections::BTreeMap::new();
    let mut unified_order: Vec<(String, String)> = Vec::new();
    // AT_QUOTED_BIND_GATE (2026-07-03): leading structural literals of THIS
    // (result) category's rules — the direct sigil-/keyword-triggered rules.
    // A cross-cat-LHS delegate on a sigil that is ALSO in this set is the
    // proven over-generation (a direct sigil-rule subsumes it). Computed once.
    let result_leading_literals = category_leading_literals(category_name, language);
    for source_cat_name in &sorted_sources {
        let source_src_idx = categories
            .iter()
            .position(|c| c == *source_cat_name)
            .map(|i| i as u16)
            .unwrap_or(0);
        let first_set = first_set_of_category(source_cat_name, language);
        for ft in first_set {
            // AT_QUOTED_BIND_GATE: this delegate's dispatch token is a leading
            // structural literal `σ` (Some) that ALSO directly triggers a
            // sibling rule in the result category ⇒ over-generation. `None`
            // (Ident / native-literal FIRST tokens) ⇒ never over-generating.
            let sigil_leads_result_rule = ft
                .leading_literal
                .as_ref()
                .map(|lit| result_leading_literals.contains(lit))
                .unwrap_or(false);
            let pat_str = ft.pattern.to_string();
            let guard_str = ft
                .extra_guard
                .as_ref()
                .map(|g| g.to_string())
                .unwrap_or_default();
            let key = (pat_str, guard_str);
            if !unified_buckets.contains_key(&key) {
                unified_order.push(key.clone());
            }
            let entry = unified_buckets.entry(key).or_insert_with(|| UnifiedBucket {
                pat: ft.pattern.clone(),
                extra_guard: ft.extra_guard.clone(),
                descs: Vec::new(),
            });
            entry
                .descs
                .push(UnifiedDescriptor::CrossCatLhs {
                    source_src_idx,
                    sigil_leads_result_rule,
                });
        }
    }
    // B11 fix (2026-04-28): two-pass emission. Pass 1 emits ALL atomic-shape
    // arms across all rules; Pass 2 emits ALL cross-cat-projection arms.
    // The previous interleaved per-rule emission (atomic + cross-cat together,
    // in source order) caused IntToBigInt's bare-Integer cross-cat arm
    // (rule_idx=1 in BigInt) to fire BEFORE NumLit's bare-Integer atomic arm
    // (synthetic rule_idx=9), routing unsuffixed integers through Int via
    // cross-cat instead of letting BigInt's NumLit consume them directly.
    // With two passes, atomic arms always precede cross-cat arms in the
    // generated match, so the home-category bare-Integer arm wins by
    // first-match-wins semantics. Rule_idx is preserved (no per_cat
    // reordering), so generated WPDA_RULES tables and stack-symbol payloads
    // remain unchanged.
    //
    // F8 fix (2026-04-28): cross-cat projection emission was per-rule with
    // an `IntSuffix::from_text` runtime guard heuristic. Post-B11 (which
    // excludes bare-Integer arms from FirstSet ctx), the `is_bare_integer`
    // branch became dead code. F8 replaces it with bucket-then-Fork: collect
    // all projections, bucket by (pattern, extra_guard), emit Push for
    // single-projection buckets, Fork for multi-projection buckets. Cross-cat
    // ambiguity (e.g., ProcInt + ProcBigInt both accepting `IntegerLit("Int")`
    // via BigInt's transitive FIRST chain) is resolved by lex-min over
    // `from_cost(0.0, src, rule_idx)` — preserves source-order tiebreak.

    // B7 (2026-05-07): home prefix descriptors fold into the SAME unified
    // bucket map as cross-cat-LHS sources above. When a (pat, guard) key
    // appears in BOTH cross-cat-LHS and a home prefix alternative, the bucket
    // emits a Fork mixing both branch kinds with the per-tier weights
    // documented above. When only one kind appears, emission is byte-identical
    // to pre-B7.
    //
    // G-PREFIX-AMB (2026-06-19): same-category binder/prefix rules are part of
    // this same bucket. They used to be emitted by `binder.rs` before
    // `all_prefix_arms`, which made Rust first-match-wins discard transparent
    // projection alternatives sharing the same trigger (for example
    // `UInt32::BitNotUInt32` shadowing `UInt32::BoolToUInt32` on `bitnot`).
    // Keeping every literal-start alternative in one bucket preserves the
    // ambiguity until runtime evidence rejects a branch.
    let mut atomic_descriptors: Vec<PrefixArmDescriptor> = Vec::new();
    for &(rule_idx, rule) in rules_in_category {
        let shape = classify_atomic(rule, language);
        atomic_descriptors.extend(atomic_arm_descriptors(category_src_idx, rule_idx, &shape));
        if let AtomicShape::CrossCatPrefixUnary {
            trigger,
            source_cat_name,
            wrapper_variant: _,
        } = &shape
        {
            let source_src_idx = categories
                .iter()
                .position(|c| c == source_cat_name)
                .map(|i| i as u16)
                .unwrap_or(category_src_idx);
            let bp_table = super::infix::build_bp_table(language);
            let operand_bp = compute_prefix_bp(source_cat_name, rule.prefix_bp, &bp_table);
            insert_unified_descriptor(
                &mut unified_buckets,
                &mut unified_order,
                quote! { Some(mettail_prattail::automata::TokenKind::Fixed(__kw)) },
                Some(quote! { __kw == #trigger }),
                UnifiedDescriptor::CrossCatPrefixUnary { rule_idx, source_src_idx, operand_bp },
            );
            continue;
        }
        // GAP-3 (2026-06-28): 0-operand multi-literal keyword-prefix rule.
        // Insert a Fixed(trigger) descriptor into the SAME unified bucket as
        // every other trigger alternative (mirror CrossCatPrefixUnary above).
        // A UNIQUE trigger (`Map`, `Pathmap`) emits a singleton arm; a SHARED
        // trigger (`@` — co-bucketed with NQuote `@(p)` / NQuoteShort `@p`)
        // folds into a multi-descriptor Fork resolved by lex-min.
        if let AtomicShape::NullaryLiteralRun { trigger, .. } = &shape {
            insert_unified_descriptor(
                &mut unified_buckets,
                &mut unified_order,
                quote! { Some(mettail_prattail::automata::TokenKind::Fixed(__kw)) },
                Some(quote! { __kw == #trigger }),
                UnifiedDescriptor::NullaryLiteralRun { rule_idx },
            );
            continue;
        }
        if matches!(shape, AtomicShape::CrossCatProjection { .. }) {
            continue;
        }
        if let Some(shape) = super::binder::classify_binder_in(rule, language) {
            let body_src_idx = super::binder::binder_initial_body_cat(&shape)
                .and_then(|name| categories.iter().position(|c| c == name).map(|i| i as u16))
                .unwrap_or(category_src_idx);
            match rule.syntax_pattern.as_ref().and_then(|sp| sp.first()) {
                Some(mettail_ast::grammar::SyntaxExpr::Literal(trigger)) => {
                    if trigger == "(" {
                        continue;
                    }
                    insert_unified_descriptor(
                        &mut unified_buckets,
                        &mut unified_order,
                        quote! { Some(mettail_prattail::automata::TokenKind::Fixed(__kw)) },
                        Some(quote! { __kw == #trigger }),
                        UnifiedDescriptor::BinderPrefix { rule_idx, body_src_idx },
                    );
                },
                // L9-3: a LEADING custom-kind capture — dispatch on the specific
                // custom kind (guard-based, mirroring the Fixed trigger path;
                // TokenKind::Custom(String) has no bare-literal pattern).
                Some(mettail_ast::grammar::SyntaxExpr::TokenKind { name, .. }) => {
                    let kind_name = name.to_string();
                    insert_unified_descriptor(
                        &mut unified_buckets,
                        &mut unified_order,
                        quote! { Some(mettail_prattail::automata::TokenKind::Custom(ref __k)) },
                        Some(quote! { __k == #kind_name }),
                        UnifiedDescriptor::LeadingTokenKindCapture {
                            rule_idx,
                            body_src_idx,
                            kind_name,
                        },
                    );
                },
                // L9-4: a LEADING guest body (`*flt(node, open, close)`) — the
                // opener kind IS the trigger; dispatch on it (guard-based, like
                // the TokenKind path) into a `LeadingGuestBody` descriptor whose
                // emission PUSHES the RuleAt frame + assembles the FltNode.
                Some(mettail_ast::grammar::SyntaxExpr::GuestBody { open, close, .. }) => {
                    let open_kind = open.to_string();
                    let close_kind = close.to_string();
                    insert_unified_descriptor(
                        &mut unified_buckets,
                        &mut unified_order,
                        quote! { Some(mettail_prattail::automata::TokenKind::Custom(ref __k)) },
                        Some(quote! { __k == #open_kind }),
                        UnifiedDescriptor::LeadingGuestBody {
                            rule_idx,
                            body_src_idx,
                            open_kind,
                            close_kind,
                        },
                    );
                },
                _ => continue,
            }
        }
    }
    for desc in atomic_descriptors {
        insert_unified_descriptor(
            &mut unified_buckets,
            &mut unified_order,
            desc.pattern.clone(),
            desc.extra_guard.clone(),
            UnifiedDescriptor::Atomic(desc),
        );
    }
    // B10 / Option κ Fix B (2026-05-07): fold Pass 2a CrossCatProjection
    // arms into the SAME unified_buckets so collisions with Pass 0/1
    // entries on the same `(pat, guard)` key emit a Fork mixing all
    // three kinds (atomic-home + cross-cat-LHS + cross-cat-projection).
    // Replaces the prior separate `emit_cross_cat_projection_arms_bucketed`
    // call which emitted projection arms AFTER the unified arms — Rust
    // first-match-wins dead-coded any projection arm whose `(pat, guard)`
    // was already taken by a Pass-1 atomic arm. Same SHAPE class as the
    // Pass-0/1 silent-shadow bug B7 closed.
    for &(rule_idx, rule) in rules_in_category {
        if let AtomicShape::CrossCatProjection { source_cat_name, .. } =
            classify_atomic(rule, language)
        {
            let source_src_idx = categories
                .iter()
                .position(|c| c == &source_cat_name)
                .map(|i| i as u16)
                .unwrap_or(0);
            for ft in first_set_of_category(&source_cat_name, language) {
                // ── CROSSCAT_LEX_COMPAT_GATE (A) — general first-token lexical
                // compatibility prune at cross-cat PROJECTION emission ──────────
                // A projection delegate `source : result` dispatches on every
                // token in FIRST(source). When that token is ONLY a
                // var-contribution of `source` (an `Ident` the source acquires
                // from its Var rule — the source cannot begin with a LITERAL
                // Ident) AND `result` already has its own home Var reading, the
                // delegate is a PROVEN over-generation: it packs the SAME bare-
                // Ident reading the home Var rule already produces, via a cast
                // path that realizes ∅ on a genuine Ident (measured alts=1 —
                // zz_inner_proc_w_enum). Pruning it removes the branch at Fork
                // CREATION (before any cursor/edge-stack/ProjDescriptorKey `W`
                // forms), which is what LINEARIZES the `.*sep`-repetition
                // frontier (a87574eb T-LinearIffWBounded: reducing #{W} is the
                // sole lever). This is SOUND FIRST-set FILTERING (removed set is
                // ∅-realizing ⇒ realized readings UNCHANGED — one-sided monotone
                // refinement), NOT the forbidden FIRST-set TIEBREAK. When the
                // kill-switch const is `false` (baseline) the conjunct is never
                // evaluated and NO token is skipped → generated wpda.rs is
                // BYTE-IDENTICAL. Grammar-derived (no language hardcode): fires
                // for EVERY category's var-contribution, inert where the source
                // has a literal first-token or the result lacks a home var.
                //
                // ★ SOUNDNESS DISCRIMINATOR (source_ident_first_is_var_only):
                // fire ONLY when the SOURCE category's bare-Ident reading is
                // EXCLUSIVELY its own variable — i.e. the source has NO non-Var
                // rule that can begin with an Ident. This holds for LEAF value
                // sources (BigInt/List/Map/…: only their synthetic Var is
                // Ident-first) but is FALSE for STRUCTURAL sources whose rules
                // are Ident-led (`InputBind . lhs:Name "<-" n`; `ForRow .
                // b:InputBind`). Without this conjunct the gate over-pruned the
                // `InputBind : ForRow` (ForRowSingleNoWhere) projection and broke
                // `for(p <- …)` (a genuine, non-∅ reading) — that projection is
                // the ONLY path to dispatch an Ident-led InputBind row. WITH it,
                // only the ∅-realizing numeric/collection casts are pruned.
                if super::forks::CROSSCAT_LEX_COMPAT_GATE
                    && ft.is_var_contribution
                    && source_ident_first_is_var_only(&source_cat_name, language)
                    && result_has_home_var_reading(category_name, language)
                {
                    continue;
                }
                insert_unified_descriptor(
                    &mut unified_buckets,
                    &mut unified_order,
                    ft.pattern.clone(),
                    ft.extra_guard.clone(),
                    UnifiedDescriptor::CrossCatProjection { rule_idx, source_src_idx },
                );
            }
        }
    }
    // Pass 2c intentionally does NOT emit source-FIRST delegates for
    // terminal-bearing wrappers such as `BoolToInt . a:Bool |- "int" "(" a
    // ")" : Int`. Those wrappers are not span-transparent projections: they
    // require literal evidence on their own continuation, so treating them as
    // zero-width CrossCatDelegate branches fabricates unsound SPPF packings
    // and explodes the frontier before realization can reject them. Explicit
    // wrappers still parse through their literal/binder arms; only Pass 2a
    // transparent projections participate in source-FIRST cross-cat wrapping.
    // Task #15 (frame-bound peel): assemble the PrefixDispatch arms AND their
    // per-arm `#[inline(never)]` helper methods. Each arm keeps its
    // pattern+guard inline in `step`'s `match peek`; its body is relocated into
    // `prefix_arm_c{cat}_a{ord}` so the PrefixDispatch alloca-sum no longer
    // inflates the `step` frame.
    let mut helpers: Vec<TokenStream> = Vec::with_capacity(unified_order.len());
    let mut helper_ord: u32 = 0;
    for key in unified_order {
        let entry = unified_buckets
            .remove(&key)
            .expect("bucket present in order");
        let (head, body) = emit_unified_arm(
            category_src_idx,
            &entry,
            s1_dispositions,
            s1_group_members,
            fork_rows,
        );
        let helper_ident = format_ident!("prefix_arm_c{}_a{}", category_src_idx, helper_ord);
        helper_ord += 1;
        arms.push(quote! {
            #head => self.#helper_ident(
                pos,
                cur_bp,
                _outer_bp,
                state_cat_src_idx,
                tokens,
                frontier_top,
                frame_ctx,
            ),
        });
        helpers.push(quote! {
            // Task #15 (frame-bound peel): one PrefixDispatch arm body,
            // #[inline(never)] so `step` reserves only skeleton + one-helper
            // frame. Pure motion — the body is verbatim; `pos`/`cur_bp` pass BY
            // REFERENCE (A5), `_outer_bp` by value (it is the derived `*cur_bp`
            // local the bodies read), and frontier_top/frame_ctx/
            // state_cat_src_idx are over-provisioned for a uniform signature
            // (silenced by the inherent impl's #[allow(unused_variables)]).
            #[inline(never)]
            fn #helper_ident(
                &self,
                pos: &usize,
                cur_bp: &u8,
                _outer_bp: u8,
                state_cat_src_idx: u16,
                tokens: &dyn mettail_prattail::wpda_runtime::WpdaTokenSource,
                frontier_top: Option<&mettail_prattail::gss::WpdaGssNode>,
                frame_ctx: mettail_prattail::wpda_runtime::FrameCtx,
            ) -> mettail_prattail::wpda_walker::WpdaStepAction<
                mettail_prattail::automata::lex_weight::LexicographicWeight,
            > #body
        });
    }
    (quote! { #(#arms)* }, quote! { #(#helpers)* })
}

// B10 / Option κ Fix B (2026-05-07): `emit_cross_cat_projection_arms_bucketed`
// removed. Pass 2a CrossCatProjection arms now fold into the same
// `unified_buckets` map as Pass 0/1 in `emit_prefix_arms_for_category`,
// emitted via `emit_unified_arm` with `BP_TIER_CROSSCAT_PROJECTION = 0.025`
// weight. Closes the Pass-1/2a silent-shadow bug analogous to B7's Pass-0/1
// fix: pre-B10 the projection arms were emitted AFTER unified arms, so any
// projection sharing a `(pat, guard)` key with a Pass-1 atomic was dead
// code via Rust's first-match-wins.

/// Emit prefix-dispatch arms for an atomic rule. Returns one or more arms.
///
/// Rust match arms allow only one `if` guard per arm. Most atomic shapes
/// emit a single arm; `LiteralPatterned` integer/rational/fixed-point shapes
/// emit multiple arms (one per TokenKind variant the lexer might produce —
/// see `literal_patterned_pattern_and_guard` for the rationale). The
/// `state_cat_src_idx == #category_src_idx` check is always appended so
/// shared token variants dispatch to different categories depending on
/// current frame.
/// Stage 3.16 invariant (Cluster 2, Mechanism γ, 2026-05-05) — descriptor
/// for a single atomic prefix arm. Used by `emit_prefix_arms_for_category`'s
/// bucket-then-Fork emission to detect atomic arms sharing a `(pat, guard)`
/// key and emit a multi-branch Fork instead of first-match-wins.
///
/// Shipped grammars have ZERO multi-arm buckets (every category's atomic
/// arms have distinct (pat, guard) pairs by construction), so the bucket
/// path is inert for current grammars — codegen output is byte-identical.
/// The bucket-then-Fork code path activates when a future G5-style grammar
/// introduces deliberate atomic-arm ambiguity (e.g., two rules in the same
/// category sharing a FIRST token).
struct PrefixArmDescriptor {
    pattern: TokenStream,
    extra_guard: Option<TokenStream>,
    rule_idx: u16,
    category_src_idx: u16,
}

/// Stage 3.16 invariant (Cluster 2, Mechanism γ, 2026-05-05) — extracts
/// pattern/guard pairs for an atomic shape, so the caller can bucket by
/// (pat, guard) before emitting either a singleton arm or a Fork.
fn atomic_arm_descriptors(
    category_src_idx: u16,
    rule_idx: u16,
    shape: &AtomicShape,
) -> Vec<PrefixArmDescriptor> {
    let pattern_guards: Vec<(TokenStream, Option<TokenStream>)> = match shape {
        AtomicShape::LiteralInteger => {
            vec![(quote! { Some(mettail_prattail::automata::TokenKind::Integer) }, None)]
        },
        AtomicShape::LiteralBoolean => vec![(
            quote! {
                Some(mettail_prattail::automata::TokenKind::True)
                | Some(mettail_prattail::automata::TokenKind::False)
                | Some(mettail_prattail::automata::TokenKind::BooleanLit)
            },
            None,
        )],
        AtomicShape::LiteralString => {
            vec![(quote! { Some(mettail_prattail::automata::TokenKind::StringLit) }, None)]
        },
        AtomicShape::LiteralFloat => {
            vec![(quote! { Some(mettail_prattail::automata::TokenKind::Float) }, None)]
        },
        AtomicShape::LiteralPatterned { cat_name, family, native_type, .. } => {
            let nk = NativeKind::from_syn_type(native_type);
            literal_patterned_pattern_and_guard_for_kind(
                cat_name,
                *family,
                Some(&nk),
                EmissionContext::HomeCategory,
            )
        },
        AtomicShape::TerminalKeyword { terminal_text, .. } => vec![(
            quote! { Some(mettail_prattail::automata::TokenKind::Fixed(__kw)) },
            Some(quote! { __kw == #terminal_text }),
        )],
        AtomicShape::VarRule { .. } => {
            vec![(quote! { Some(mettail_prattail::automata::TokenKind::Ident) }, None)]
        },
        AtomicShape::CrossCatProjection { .. } | AtomicShape::CrossCatPrefixUnary { .. } => {
            return Vec::new()
        },
        // M6c.6.4.b (2026-05-14): PrefixOperator does not emit an
        // atomic-arm descriptor — same-cat unary prefix rules are
        // handled by the standard prefix-trigger arm (BinderRule
        // entry), NOT by atomic-literal dispatch. The lex-Fork at
        // PrefixDispatch separately consults `lex_alt_rules_for_prefix`
        // to bind `Fixed(trigger)` as a Fork branch for the same rule
        // when multi-LENGTH lex ambiguity is present.
        AtomicShape::PrefixOperator { .. } => return Vec::new(),
        // GAP-3: NullaryLiteralRun does NOT emit a plain atomic singleton
        // (which would fire the action immediately, skipping the trailing
        // `( )` / `Nil` literals). Its dispatch arm is inserted into the
        // unified bucket below as `UnifiedDescriptor::NullaryLiteralRun`,
        // pushing the mixfix marker + entering `MixfixLiteralRun`.
        AtomicShape::NullaryLiteralRun { .. } => return Vec::new(),
        AtomicShape::NonAtomic => return Vec::new(),
    };
    pattern_guards
        .into_iter()
        .map(|(pattern, extra_guard)| PrefixArmDescriptor {
            pattern,
            extra_guard,
            rule_idx,
            category_src_idx,
        })
        .collect()
}

/// B7 (2026-05-07) — unified descriptor for the merged Pass 0/Pass 1
/// bucket map. Each bucket entry is a list of these; singleton buckets
/// emit a direct arm matching their kind; mixed buckets emit a Fork.
///
/// B10 / Option κ Fix B (2026-05-07): adds `CrossCatProjection` so Pass 2a
/// folds into the same bucket map. Closes the Pass-1/2a silent shadow
/// twin of the Pass-0/1 bug B7 fixed.
enum UnifiedDescriptor {
    /// Cross-cat infix LHS delegation arm — pushes
    /// `CategoryEntry(source_src_idx)` so the LHS sub-parses against
    /// the source category before InfixLoop sees the cross-cat operator.
    /// Per-tier weight: `BP_TIER_CROSSCAT_LHS = 0.05`.
    ///
    /// AT_QUOTED_BIND_GATE (2026-07-03): `sigil_leads_result_rule` is `true`
    /// when this delegate's dispatch token (the bucket's leading structural
    /// literal `σ`) is ALSO the leading literal of a SIBLING rule in the RESULT
    /// category — i.e. a direct `σ`-triggered rule (the sigil-quoted form)
    /// exists that subsumes the whole-`source` reading this delegate produces.
    /// Grammar-derived at construction (`category_leading_literals`). When
    /// `AT_QUOTED_BIND_GATE` is on AND this flag is set AND a bind-trigger is
    /// scoped-ahead at runtime, the delegate push is SUPPRESSED (drops the
    /// proven over-generation; see `forks::AT_QUOTED_BIND_GATE`). `false` for
    /// every non-sigil / non-over-generating delegate ⇒ inert.
    CrossCatLhs {
        source_src_idx: u16,
        sigil_leads_result_rule: bool,
    },
    /// Atomic-shape arm — `ConsumeAndPush(rule_at(...).Return)` for a
    /// home-category leaf rule (literal, var, terminal-keyword, etc.).
    /// Per-tier weight: `0.0` (atomic-home).
    Atomic(PrefixArmDescriptor),
    /// Literal-leading binder/prefix rule. Consumes its own trigger token,
    /// pushes `RuleAt(slot=1)`, and enters `BinderRule`.
    BinderPrefix { rule_idx: u16, body_src_idx: u16 },
    /// L9-3: a rule whose FIRST syntax element is a custom-kind capture
    /// (`b@GuestChunk …`). The prefix dispatch consumes+captures the leading
    /// token via `GuardedConsumeTokenKindAndReplace` (gated on
    /// `peek_kind == Custom(kind_name)`), pushes `RuleAt(slot=1)`, and enters
    /// `BinderRule`; the mid-rule positions (slots 1..) parse the rest. The
    /// leading capture's `ActionArg::Token` is prepended to the action args by
    /// `classify_binder_in`.
    LeadingTokenKindCapture { rule_idx: u16, body_src_idx: u16, kind_name: String },
    /// L9-4: a LEADING guest-body rule (`PFlt . |- *flt(node, open, close) :
    /// Cat`). Mirrors `LeadingTokenKindCapture` but the emitted Fork carries
    /// `ConsumeGuestBodyAndPush` (scan opener→body→closer, assemble the FltNode,
    /// PUSH `RuleAt(slot=1)`, enter `BinderRule`). The assembled
    /// `ActionArg::GuestBody` is prepended to the action args by
    /// `classify_binder_in`'s leading-prepend.
    LeadingGuestBody { rule_idx: u16, body_src_idx: u16, open_kind: String, close_kind: String },
    /// Cross-category prefix-unary rule. Consumes its own trigger token,
    /// pushes the wrapper Return frame, and delegates the operand to the
    /// source category at that source's prefix floor.
    CrossCatPrefixUnary {
        rule_idx: u16,
        source_src_idx: u16,
        operand_bp: u8,
    },
    /// B10 / Option κ Fix B — Pass 2a CrossCatProjection delegation arm.
    /// Pushes `rule_at(category, rule_idx, 0).with_kind_return()` and
    /// transitions to `CrossCatDelegate { source_src_idx, outer_bp }`.
    /// Per-tier weight: `BP_TIER_CROSSCAT_PROJECTION = 0.025`.
    /// Used for rules of shape `R . a:Y |- a : X` (sp.len()==1).
    CrossCatProjection { rule_idx: u16, source_src_idx: u16 },
    /// GAP-3 (2026-06-28): 0-operand multi-literal keyword-prefix rule
    /// (`Map ()`, `Pathmap ()`, `@ Nil`). Consumes its own trigger token
    /// (mirrored to the SPPF as a `TriggerTerminal` for span anchoring),
    /// pushes `mixfix_marker(cat, rule_idx, 0)`, and enters
    /// `MixfixLiteralRun { kind: 2, completed_idx: 0 }` — whose `parts_len
    /// == 0` arm consumes the trailing literals then pops the marker, firing
    /// the arity-0 action. Per-tier weight `0.0` (atomic-home) so a unique
    /// trigger emits a singleton and a shared trigger (e.g. `@`) folds into a
    /// lex-min Fork where declaration order (lower rule_idx) wins the tie.
    NullaryLiteralRun { rule_idx: u16 },
}

/// B7 (2026-05-07) — unified bucket entry. Replaces the separate
/// LhsBucketEntry (Pass 0) and atomic bucket map (Pass 1).
struct UnifiedBucket {
    pat: TokenStream,
    extra_guard: Option<TokenStream>,
    descs: Vec<UnifiedDescriptor>,
}

fn insert_unified_descriptor(
    unified_buckets: &mut std::collections::BTreeMap<(String, String), UnifiedBucket>,
    unified_order: &mut Vec<(String, String)>,
    pattern: TokenStream,
    extra_guard: Option<TokenStream>,
    desc: UnifiedDescriptor,
) {
    let pat_str = pattern.to_string();
    let guard_str = extra_guard
        .as_ref()
        .map(|g| g.to_string())
        .unwrap_or_default();
    let key = (pat_str, guard_str);
    if !unified_buckets.contains_key(&key) {
        unified_order.push(key.clone());
    }
    let entry = unified_buckets.entry(key).or_insert_with(|| UnifiedBucket {
        pat: pattern,
        extra_guard,
        descs: Vec::new(),
    });
    entry.descs.push(desc);
}

/// B7 (2026-05-07) — emit a unified bucket as either a singleton arm
/// (byte-identical to the pre-B7 emission for the matching kind) or a
/// Fork mixing CrossCatLhs and Atomic branches with per-tier weights:
///   - Atomic-home: `from_cost(0.0, csi, rule_idx)`.
///   - Cross-cat-LHS: `from_cost(BP_TIER_CROSSCAT_LHS, csi, src_idx)`.
///
/// Lex-min picks atomic-home on parse-success ties (preserves bare
/// PVar parsing as Proc when no operator follows); cross-cat-LHS wins
/// when only that branch survives (e.g. `x!(0)` requires Name LHS).
/// Task #10 item 1: record the fork-emission site-2 row(s) for a
/// rule-initiating dispatch branch at its static declaration position,
/// routing S1 spine dispositions: `GroupFirst` derives one row per group
/// MEMBER at the spine trigger branch's position (the branch initiates
/// every member); `GroupRest` derives nothing (no branch is emitted — the
/// member's row came from its group's `GroupFirst`); undispositioned rules
/// derive their own row.
fn record_initiating_rule_rows(
    fork_rows: &mut super::fork_emission::ForkEmissionOrdinalModel,
    category_src_idx: u16,
    rule_idx: u16,
    branch_position: u16,
    s1_dispositions: &std::collections::HashMap<u16, super::factoring::SpineDisposition>,
    s1_group_members: &std::collections::HashMap<u16, Vec<u16>>,
    bucket_tag: &str,
) {
    match s1_dispositions.get(&rule_idx) {
        Some(super::factoring::SpineDisposition::GroupFirst { .. }) => {
            let members = s1_group_members.get(&rule_idx).unwrap_or_else(|| {
                panic!(
                    "task #10 item 1: GroupFirst rule (cat {category_src_idx}, rule \
                     {rule_idx}) has no group_members entry — factoring drift",
                )
            });
            for &member in members {
                fork_rows.record_site2_row(
                    category_src_idx,
                    member,
                    branch_position,
                    bucket_tag,
                );
            }
        },
        Some(super::factoring::SpineDisposition::GroupRest) => {},
        None => {
            fork_rows.record_site2_row(
                category_src_idx,
                rule_idx,
                branch_position,
                bucket_tag,
            );
        },
    }
}

fn emit_unified_arm(
    category_src_idx: u16,
    bucket: &UnifiedBucket,
    s1_dispositions: &std::collections::HashMap<u16, super::factoring::SpineDisposition>,
    // Task #10 item 1: `GroupFirst rule -> ordered members` for THIS
    // category (`factoring::SpineEmission::group_members`) — a GroupFirst
    // descriptor's spine trigger branch is every member's initiating
    // branch, so each member derives a row at that branch's position.
    s1_group_members: &std::collections::HashMap<u16, Vec<u16>>,
    // Task #10 item 1: the fork-emission ordinal collector. Rows are
    // recorded HERE, as the branches are emitted, at their STATIC
    // DECLARATION POSITIONS (amendment 6) — runtime-gated pushes (the
    // CrossCatLhs guard) still occupy their declared slot.
    fork_rows: &mut super::fork_emission::ForkEmissionOrdinalModel,
    // Task #15 (frame-bound peel): returns `(head, body)` — `head` is the
    // arm's `#pat if #guard [#compat]` (kept inline in `step`'s PrefixDispatch
    // `match peek`), `body` is the `{ .. }` block relocated into a per-arm
    // `#[inline(never)]` helper. The guard stays with the pattern so any
    // pattern binding (e.g. `__kw`) and the `tokens`/`*pos` guard references
    // remain in the skeleton — the split is pure body-relocation (A4).
) -> (TokenStream, TokenStream) {
    let pat = &bucket.pat;
    let guard = match &bucket.extra_guard {
        Some(eg) => quote! { #eg && state_cat_src_idx == #category_src_idx },
        None => quote! { state_cat_src_idx == #category_src_idx },
    };
    // Task #10 item 1: bucket identity for the collision diagnostics.
    let fork_bucket_tag = match &bucket.extra_guard {
        Some(eg) => format!("prefix-dispatch {} if {}", bucket.pat, eg),
        None => format!("prefix-dispatch {}", bucket.pat),
    };
    // CROSSCAT_LEX_COMPAT_GATE (option B backstop): a per-projection compat
    // conjunct appended to the arm GUARD when the runtime kill-switch is on.
    // Refutes ONLY a var-only-Ident projection at runtime (fail-open otherwise);
    // when the arm's guard fails, the dispatch falls through to the next arm /
    // the `_` default, which is the SAME lex-alt / recovery path taken when no
    // projection matched — so the home var reading is never lost. Emits NOTHING
    // when the const is off ⇒ byte-identical. INERT under gate (A) (that push
    // was already pruned at codegen). Extends the SINGLETON + the MULTI-BRANCH
    // (Fork) CrossCatProjection guards identically.
    let compat_guard = |source_src_idx: u16| -> TokenStream {
        if super::forks::CROSSCAT_LEX_COMPAT_RUNTIME_GATE {
            quote! { && crosscat_proj_lex_compatible(#source_src_idx, tokens, *pos) }
        } else {
            quote! {}
        }
    };
    if bucket.descs.len() == 1 {
        match &bucket.descs[0] {
            UnifiedDescriptor::CrossCatLhs {
                source_src_idx,
                // AT_QUOTED_BIND_GATE: a SINGLETON cross-cat-LHS bucket means no
                // sibling rule shares this dispatch token (a sigil-led sibling
                // rule would co-bucket as BinderPrefix/CrossCatPrefixUnary/
                // NullaryLiteralRun on the SAME `σ` → a MULTI bucket). So
                // `sigil_leads_result_rule` is necessarily `false` here and the
                // gate is structurally inert — emit byte-identically.
                sigil_leads_result_rule: _,
            } => {
                let source_src_idx = *source_src_idx;
                (
                    quote! { #pat if #guard },
                    quote! {
                        {
                        // Cross-category LHS delegation parses a source-category
                        // atom that may later produce the target category via a
                        // category-changing infix. The target Pratt floor is
                        // captured by the runtime edge; the source parse starts
                        // at its own root floor so target-context precedence
                        // does not reject source-internal operators.
                        return WpdaStepAction::PushWithEdgeKind {
                            symbol: StackSymbolV2::category_entry(#source_src_idx),
                            weight: lex_one(),
                            new_state: WpdaState::PrefixDispatch {
                                pos: *pos,
                                cur_bp: 0,
                            },
                            edge_kind: mettail_prattail::gss::EdgeKind::CrossCatLhs {
                                source_src_idx: #source_src_idx,
                            },
                        };
                        }
                    },
                )
            },
            UnifiedDescriptor::Atomic(desc) => {
                // Task #10 item 1: the no-fork singleton fast path has no
                // peer branches — static declaration position 0 (amendment
                // 6). Recorded (not skipped) so the amendment-6 collision
                // assert also covers cross-bucket membership.
                fork_rows.record_site2_row(
                    desc.category_src_idx,
                    desc.rule_idx,
                    0,
                    &fork_bucket_tag,
                );
                emit_atomic_arm_singleton(desc)
            },
            UnifiedDescriptor::BinderPrefix { rule_idx, body_src_idx } => {
                let rule_idx = *rule_idx;
                let body_src_idx = *body_src_idx;
                // S1-FACTORING F1: a factored group needs ≥2 members sharing
                // this bucket's `(pat, guard)` key, so a grouped member can
                // never reach the SINGLETON (1-descriptor) path — asserted so
                // a bucketing drift between `factoring::discover_members` and
                // this insertion chain fails codegen loudly.
                assert!(
                    s1_dispositions.get(&rule_idx).is_none(),
                    "S1-FACTORING F1: grouped rule (cat {category_src_idx}, rule {rule_idx}) \
                     reached the singleton BinderPrefix emission",
                );
                // Task #10 item 1: singleton = position 0 (grouped members
                // asserted unreachable above, so the plain row suffices).
                fork_rows.record_site2_row(category_src_idx, rule_idx, 0, &fork_bucket_tag);
                (
                    quote! { #pat if #guard },
                    quote! {
                        {
                        return WpdaStepAction::ConsumeAndPush {
                            symbol: StackSymbolV2::rule_at(
                                #category_src_idx, #rule_idx, 1u8, Some(_outer_bp),
                            ),
                            weight: lex_w(0.0, #category_src_idx, #rule_idx),
                            new_state: WpdaState::BinderRule {
                                result_src_idx: #category_src_idx,
                                rule_idx: #rule_idx,
                                body_src_idx: #body_src_idx,
                                outer_bp: _outer_bp,
                            },
                            trigger_mode:
                                mettail_prattail::wpda_walker::TriggerMode::ConsumeAsTriggerOnly,
                        };
                        }
                    },
                )
            },
            UnifiedDescriptor::LeadingTokenKindCapture { rule_idx, body_src_idx, kind_name } => {
                let rule_idx = *rule_idx;
                let body_src_idx = *body_src_idx;
                // L9-3: leading custom-kind capture — never S1-grouped (it
                // terminates mergeability), so it always reaches the singleton
                // path. Emit a single-branch Fork carrying
                // GuardedConsumeTokenKindAndPush (a ForkActionKind — hence a
                // Fork rather than the non-capturing ConsumeAndPush the Literal
                // trigger uses): the walker gates peek_kind == Custom(kind_name),
                // captures the token as an ActionArg::Token leaf, PUSHES
                // RuleAt(slot=1) (the leading token is the trigger — there is no
                // prior literal trigger to push the frame, unlike the mid-rule
                // capture which only replaces cur_sym), and enters BinderRule for
                // the remaining mid-rule positions.
                assert!(
                    s1_dispositions.get(&rule_idx).is_none(),
                    "S1-FACTORING F1: grouped rule (cat {category_src_idx}, rule {rule_idx}) \
                     reached the singleton LeadingTokenKindCapture emission",
                );
                fork_rows.record_site2_row(category_src_idx, rule_idx, 0, &fork_bucket_tag);
                (
                    quote! { #pat if #guard },
                    quote! {
                        {
                        return WpdaStepAction::Fork {
                            branches: vec![mettail_prattail::wpda_walker::ForkBranch {
                                symbol: StackSymbolV2::rule_at(
                                    #category_src_idx, #rule_idx, 1u8, Some(_outer_bp),
                                ),
                                weight: lex_w(0.0, #category_src_idx, #rule_idx),
                                new_state: WpdaState::BinderRule {
                                    result_src_idx: #category_src_idx,
                                    rule_idx: #rule_idx,
                                    body_src_idx: #body_src_idx,
                                    outer_bp: _outer_bp,
                                },
                                action_kind:
                                    mettail_prattail::wpda_walker::ForkActionKind::GuardedConsumeTokenKindAndPush {
                                        kind_name: #kind_name.to_string(),
                                    },
                            }],
                            consume_trigger: false,
                        };
                        }
                    },
                )
            },
            UnifiedDescriptor::LeadingGuestBody { rule_idx, body_src_idx, open_kind, close_kind } => {
                let rule_idx = *rule_idx;
                let body_src_idx = *body_src_idx;
                // L9-4: leading guest body — never S1-grouped (a guest body
                // terminates mergeability), so always the singleton path. Emit a
                // single-branch Fork carrying ConsumeGuestBodyAndPush: the walker
                // gates peek_kind == Custom(open_kind), scans the whole
                // opener→body→closer region assembling the FltNode, PUSHES
                // RuleAt(slot=1), and enters BinderRule.
                assert!(
                    s1_dispositions.get(&rule_idx).is_none(),
                    "S1-FACTORING F1: grouped rule (cat {category_src_idx}, rule {rule_idx}) \
                     reached the singleton LeadingGuestBody emission",
                );
                fork_rows.record_site2_row(category_src_idx, rule_idx, 0, &fork_bucket_tag);
                (
                    quote! { #pat if #guard },
                    quote! {
                        {
                        return WpdaStepAction::Fork {
                            branches: vec![mettail_prattail::wpda_walker::ForkBranch {
                                symbol: StackSymbolV2::rule_at(
                                    #category_src_idx, #rule_idx, 1u8, Some(_outer_bp),
                                ),
                                weight: lex_w(0.0, #category_src_idx, #rule_idx),
                                new_state: WpdaState::BinderRule {
                                    result_src_idx: #category_src_idx,
                                    rule_idx: #rule_idx,
                                    body_src_idx: #body_src_idx,
                                    outer_bp: _outer_bp,
                                },
                                action_kind:
                                    mettail_prattail::wpda_walker::ForkActionKind::ConsumeGuestBodyAndPush {
                                        open_kind: #open_kind.to_string(),
                                        close_kind: #close_kind.to_string(),
                                    },
                            }],
                            consume_trigger: false,
                        };
                        }
                    },
                )
            },
            UnifiedDescriptor::CrossCatPrefixUnary { rule_idx, source_src_idx, operand_bp } => {
                let rule_idx = *rule_idx;
                let source_src_idx = *source_src_idx;
                let operand_bp = *operand_bp;
                // Task #10 item 1: singleton = position 0.
                fork_rows.record_site2_row(category_src_idx, rule_idx, 0, &fork_bucket_tag);
                (
                    quote! { #pat if #guard },
                    quote! {
                        {
                        return WpdaStepAction::ConsumeAndPush {
                            symbol: StackSymbolV2::rule_at(
                                #category_src_idx, #rule_idx, 0, Some(_outer_bp),
                            ).with_kind_return(),
                            weight: lex_w(0.0, #category_src_idx, #rule_idx),
                            new_state: WpdaState::CrossCatDelegate {
                                source_src_idx: #source_src_idx,
                                inner_cur_bp: #operand_bp,
                            },
                            trigger_mode:
                                mettail_prattail::wpda_walker::TriggerMode::ConsumeAsTriggerOnly,
                        };
                        }
                    },
                )
            },
            UnifiedDescriptor::CrossCatProjection { rule_idx, source_src_idx } => {
                let rule_idx = *rule_idx;
                let source_src_idx = *source_src_idx;
                let __compat = compat_guard(source_src_idx);
                // Task #10 item 1: singleton = position 0.
                fork_rows.record_site2_row(category_src_idx, rule_idx, 0, &fork_bucket_tag);
                (
                    quote! { #pat if #guard #__compat },
                    quote! {
                        {
                        // B10 / Option κ Fix B (2026-05-07): cross-cat
                        // projection singleton — Push the rule's Return
                        // marker and route to CrossCatDelegate so the
                        // source-cat sub-parse fires; on return, the
                        // projection's action wraps the source term.
                        // Transparent projection delegates into a source
                        // category while remaining inside the caller's Pratt
                        // operand slot. Carry the active floor through so
                        // the source parse respects the caller's binding
                        // context.
                        return WpdaStepAction::Push {
                            symbol: StackSymbolV2::rule_at(
                                #category_src_idx, #rule_idx, 0, Some(_outer_bp),
                            ).with_kind_return(),
                            weight: lex_w(
                                0.0, #category_src_idx, #rule_idx,
                            ),
                            new_state: WpdaState::CrossCatDelegate {
                                source_src_idx: #source_src_idx,
                                inner_cur_bp: *cur_bp,
                            },
                        };
                        }
                    },
                )
            },
            UnifiedDescriptor::NullaryLiteralRun { rule_idx } => {
                let rule_idx = *rule_idx;
                // S1-FACTORING F1: same singleton-unreachability assert as
                // the BinderPrefix arm above (groups need ≥2 co-bucketed
                // members).
                assert!(
                    s1_dispositions.get(&rule_idx).is_none(),
                    "S1-FACTORING F1: grouped rule (cat {category_src_idx}, rule {rule_idx}) \
                     reached the singleton NullaryLiteralRun emission",
                );
                // Task #10 item 1: singleton = position 0.
                fork_rows.record_site2_row(category_src_idx, rule_idx, 0, &fork_bucket_tag);
                (
                    quote! { #pat if #guard },
                    quote! {
                        {
                        // GAP-3: 0-operand multi-literal keyword prefix. Consume
                        // the trigger (ConsumeAsTriggerOnly mirrors it to the
                        // SPPF as a TriggerTerminal — the SOLE child under the
                        // marker, anchoring its span lo; Discard would leave 0
                        // children → span realization fail), push the mixfix
                        // marker, and enter the REUSED MixfixLiteralRun(kind=2,
                        // parts_len==0) arm, which consumes the trailing literals
                        // then pops the marker to fire the arity-0 action.
                        return WpdaStepAction::ConsumeAndPush {
                            symbol: StackSymbolV2::mixfix_marker(
                                #category_src_idx, #rule_idx, 0u8,
                            ),
                            weight: lex_w(0.0, #category_src_idx, #rule_idx),
                            new_state: WpdaState::MixfixLiteralRun {
                                result_src_idx: #category_src_idx,
                                rule_idx: #rule_idx,
                                completed_idx: 0u8,
                                kind: 2u8,
                                sub_pos: 0u8,
                            },
                            trigger_mode:
                                mettail_prattail::wpda_walker::TriggerMode::ConsumeAsTriggerOnly,
                        };
                        }
                    },
                )
            },
        }
    } else {
        // F1/H1 (2026-06-28): in a multi-descriptor PrefixDispatch fork, the
        // cross-cat-LHS EXTENSION branch is gated EXACTLY as at the lex-fork
        // site (forks.rs): keep it iff a row-scoped trigger binds this LHS OR no
        // transparent projection source→result exists as a fallback. A
        // projection `D ::= s` shares S's first-set with the S→D cross-cat-LHS,
        // so it is ALWAYS co-bucketed here — making the runtime
        // projection-fallback check exact. Non-cross-cat-LHS branches (atomic /
        // projection / binder / unary) are pushed unconditionally and IN
        // DECLARATION ORDER, byte-identical to the pre-F1 emission; only the
        // cross-cat-LHS push is wrapped in the runtime gate, preserving order.
        let n_descs = bucket.descs.len();
        // Task #10 item 1: `branch_position` = the descriptor's STATIC
        // DECLARATION POSITION within this bucket (amendment 6) — the
        // enumerate index over the SAME iteration that emits the branches,
        // so the recorded ordinals can never diverge from the emission.
        // Runtime-gated pushes (CrossCatLhs) still occupy their declared
        // slot; GroupRest descriptors emit nothing and record nothing.
        let push_stmts: Vec<TokenStream> = bucket
            .descs
            .iter()
            .enumerate()
            .map(|(branch_position, d)| match d {
                UnifiedDescriptor::CrossCatLhs {
                    source_src_idx,
                    sigil_leads_result_rule,
                } => {
                    let src_idx = *source_src_idx;
                    // AT_QUOTED_BIND_GATE (2026-07-03): the F1/H1 keep-guard is
                    // EXTENDED with a suppression conjunct ONLY when the
                    // kill-switch const AND the grammar-derived
                    // `sigil_leads_result_rule` for THIS bucket are BOTH true at
                    // codegen time. When either is false (every baseline build,
                    // and every non-over-generating delegate) the conjunct is
                    // OMITTED entirely — the emitted guard is TEXTUALLY
                    // BYTE-IDENTICAL to the pre-gate F1/H1 emission, and
                    // `prefix_at_quoted_bind_gate_evidence` is never referenced.
                    // Only in a gate-ON build over a sigil that directly
                    // triggers a sibling rule does the runtime bind-trigger
                    // evidence gate the push (dropping the proven
                    // over-generation).
                    let __gate_active =
                        super::forks::AT_QUOTED_BIND_GATE && *sigil_leads_result_rule;
                    let __keep_guard = if __gate_active {
                        quote! {
                            (prefix_crosscat_lhs_trigger_ahead_scoped(
                                #category_src_idx, tokens, *pos,
                            ) || !crosscat_lhs_has_projection_fallback(
                                #category_src_idx, #src_idx,
                            )) && !prefix_at_quoted_bind_gate_evidence(
                                #category_src_idx, tokens, *pos,
                            )
                        }
                    } else {
                        quote! {
                            prefix_crosscat_lhs_trigger_ahead_scoped(
                                #category_src_idx, tokens, *pos,
                            ) || !crosscat_lhs_has_projection_fallback(
                                #category_src_idx, #src_idx,
                            )
                        }
                    };
                    quote! {
                        // The runtime edge stores the caller's target floor;
                        // the delegated source parse starts at source root.
                        if #__keep_guard {
                            __pd_branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                symbol: StackSymbolV2::category_entry(#src_idx),
                                weight: lex_w(
                                    mettail_prattail::automata::lex_weight::BP_TIER_CROSSCAT_LHS,
                                    #category_src_idx, #src_idx,
                                ),
                                new_state: WpdaState::PrefixDispatch {
                                    pos: *pos,
                                    cur_bp: 0,
                                },
                                action_kind:
                                    mettail_prattail::wpda_walker::ForkActionKind::PushCrossCatLhs,
                            });
                        }
                    }
                }
                UnifiedDescriptor::Atomic(desc) => {
                    let rule_idx = desc.rule_idx;
                    let csi = desc.category_src_idx;
                    // Task #10 item 1: static declaration position.
                    fork_rows.record_site2_row(
                        csi,
                        rule_idx,
                        branch_position as u16,
                        &fork_bucket_tag,
                    );
                    quote! {
                        __pd_branches.push(mettail_prattail::wpda_walker::ForkBranch {
                            symbol: StackSymbolV2::rule_at(
                                #csi, #rule_idx, 0, Some(_outer_bp),
                            ).with_kind_return(),
                            weight: lex_w(
                                0.0, #csi, #rule_idx,
                            ),
                            new_state: WpdaState::Unwinding,
                            action_kind: mettail_prattail::wpda_walker::ForkActionKind::ConsumeAndCaptureAndPush,
                        });
                    }
                }
                UnifiedDescriptor::BinderPrefix { rule_idx, body_src_idx } => {
                    let rule_idx = *rule_idx;
                    let body_src_idx = *body_src_idx;
                    // Task #10 item 1: disposition-routed rows — GroupFirst
                    // derives every member's row at THIS position; GroupRest
                    // derives nothing; plain rules derive their own row.
                    record_initiating_rule_rows(
                        fork_rows,
                        category_src_idx,
                        rule_idx,
                        branch_position as u16,
                        s1_dispositions,
                        s1_group_members,
                        &fork_bucket_tag,
                    );
                    // S1-FACTORING F1 (plan §2 item 1): a grouped member's
                    // per-rule branch is replaced by the group's ONE spine
                    // trigger branch (emitted at the FIRST member's position,
                    // preserving declaration-order emission), or by nothing
                    // (GroupRest). The map is EMPTY while `S1_FACTORING ==
                    // false` ⇒ the `None` arm below is the pre-F1
                    // byte-identical emission.
                    match s1_dispositions.get(&rule_idx) {
                        Some(super::factoring::SpineDisposition::GroupFirst {
                            spine_id,
                            body_src_idx: group_body_src_idx,
                            weight_rule_idx,
                        }) => super::factoring::emit_spine_trigger_branch(
                            category_src_idx,
                            *spine_id,
                            *group_body_src_idx,
                            *weight_rule_idx,
                        ),
                        Some(super::factoring::SpineDisposition::GroupRest) => TokenStream::new(),
                        None => quote! {
                            __pd_branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                symbol: StackSymbolV2::rule_at(
                                    #category_src_idx, #rule_idx, 1u8, Some(_outer_bp),
                                ),
                                weight: lex_w(0.0, #category_src_idx, #rule_idx),
                                new_state: WpdaState::BinderRule {
                                    result_src_idx: #category_src_idx,
                                    rule_idx: #rule_idx,
                                    body_src_idx: #body_src_idx,
                                    outer_bp: _outer_bp,
                                },
                                action_kind:
                                    mettail_prattail::wpda_walker::ForkActionKind::ConsumeAndPush {
                                        trigger_mode:
                                            mettail_prattail::wpda_walker::TriggerMode::ConsumeAsTriggerOnly,
                                    },
                            });
                        },
                    }
                }
                UnifiedDescriptor::LeadingTokenKindCapture { rule_idx, body_src_idx, kind_name } => {
                    let rule_idx = *rule_idx;
                    let body_src_idx = *body_src_idx;
                    // L9-3: leading custom-kind capture in a Fork bucket (a
                    // co-bucketed same-kind sibling, or shared with other
                    // descriptors on the same (pat,guard)). Never S1-grouped ⇒
                    // a plain row + a capturing branch. Uses
                    // GuardedConsumeTokenKindAndPush (PUSHES the RuleAt frame —
                    // the leading token IS the trigger, so no prior push exists;
                    // mirrors the singleton path above) instead of the
                    // non-capturing ConsumeAsTriggerOnly the Literal trigger uses.
                    record_initiating_rule_rows(
                        fork_rows,
                        category_src_idx,
                        rule_idx,
                        branch_position as u16,
                        s1_dispositions,
                        s1_group_members,
                        &fork_bucket_tag,
                    );
                    quote! {
                        __pd_branches.push(mettail_prattail::wpda_walker::ForkBranch {
                            symbol: StackSymbolV2::rule_at(
                                #category_src_idx, #rule_idx, 1u8, Some(_outer_bp),
                            ),
                            weight: lex_w(0.0, #category_src_idx, #rule_idx),
                            new_state: WpdaState::BinderRule {
                                result_src_idx: #category_src_idx,
                                rule_idx: #rule_idx,
                                body_src_idx: #body_src_idx,
                                outer_bp: _outer_bp,
                            },
                            action_kind:
                                mettail_prattail::wpda_walker::ForkActionKind::GuardedConsumeTokenKindAndPush {
                                    kind_name: #kind_name.to_string(),
                                },
                        });
                    }
                }
                UnifiedDescriptor::LeadingGuestBody { rule_idx, body_src_idx, open_kind, close_kind } => {
                    let rule_idx = *rule_idx;
                    let body_src_idx = *body_src_idx;
                    // L9-4: leading guest body in a Fork bucket — the ConsumeGuestBodyAndPush
                    // twin of the singleton path (PUSHES the RuleAt frame).
                    record_initiating_rule_rows(
                        fork_rows,
                        category_src_idx,
                        rule_idx,
                        branch_position as u16,
                        s1_dispositions,
                        s1_group_members,
                        &fork_bucket_tag,
                    );
                    quote! {
                        __pd_branches.push(mettail_prattail::wpda_walker::ForkBranch {
                            symbol: StackSymbolV2::rule_at(
                                #category_src_idx, #rule_idx, 1u8, Some(_outer_bp),
                            ),
                            weight: lex_w(0.0, #category_src_idx, #rule_idx),
                            new_state: WpdaState::BinderRule {
                                result_src_idx: #category_src_idx,
                                rule_idx: #rule_idx,
                                body_src_idx: #body_src_idx,
                                outer_bp: _outer_bp,
                            },
                            action_kind:
                                mettail_prattail::wpda_walker::ForkActionKind::ConsumeGuestBodyAndPush {
                                    open_kind: #open_kind.to_string(),
                                    close_kind: #close_kind.to_string(),
                                },
                        });
                    }
                }
                UnifiedDescriptor::CrossCatPrefixUnary {
                    rule_idx,
                    source_src_idx,
                    operand_bp,
                } => {
                    let rule_idx = *rule_idx;
                    let source_src_idx = *source_src_idx;
                    let operand_bp = *operand_bp;
                    // Task #10 item 1: static declaration position.
                    fork_rows.record_site2_row(
                        category_src_idx,
                        rule_idx,
                        branch_position as u16,
                        &fork_bucket_tag,
                    );
                    quote! {
                        __pd_branches.push(mettail_prattail::wpda_walker::ForkBranch {
                            symbol: StackSymbolV2::rule_at(
                                #category_src_idx, #rule_idx, 0, Some(_outer_bp),
                            ).with_kind_return(),
                            weight: lex_w(0.0, #category_src_idx, #rule_idx),
                            new_state: WpdaState::CrossCatDelegate {
                                source_src_idx: #source_src_idx,
                                inner_cur_bp: #operand_bp,
                            },
                            action_kind:
                                mettail_prattail::wpda_walker::ForkActionKind::ConsumeAndPush {
                                    trigger_mode:
                                        mettail_prattail::wpda_walker::TriggerMode::ConsumeAsTriggerOnly,
                                },
                        });
                    }
                }
                UnifiedDescriptor::CrossCatProjection {
                    rule_idx,
                    source_src_idx,
                } => {
                    let rule_idx = *rule_idx;
                    let src_idx = *source_src_idx;
                    // Task #10 item 1: static declaration position (the
                    // lex-compat runtime gate below is runtime-only — the
                    // declared slot counts per amendment 6).
                    fork_rows.record_site2_row(
                        category_src_idx,
                        rule_idx,
                        branch_position as u16,
                        &fork_bucket_tag,
                    );
                    // CROSSCAT_LEX_COMPAT_GATE (option B backstop): gate THIS
                    // Fork branch's push on runtime lex-compatibility. Other
                    // branches in the same Fork (CrossCatLhs / PVar / other
                    // projections) are UNAFFECTED — only the var-only-Ident
                    // projection is refuted (fail-open otherwise). Emits an
                    // unconditional push when the const is off ⇒ byte-identical.
                    // INERT under gate (A) (branch already absent at codegen).
                    let __push = quote! {
                        __pd_branches.push(mettail_prattail::wpda_walker::ForkBranch {
                            symbol: StackSymbolV2::rule_at(
                                #category_src_idx, #rule_idx, 0, Some(_outer_bp),
                            ).with_kind_return(),
                            weight: lex_w(
                                mettail_prattail::automata::lex_weight::BP_TIER_CROSSCAT_PROJECTION,
                                #category_src_idx, #rule_idx,
                            ),
                            new_state: WpdaState::CrossCatDelegate {
                                source_src_idx: #src_idx,
                                inner_cur_bp: *cur_bp,
                            },
                            action_kind: mettail_prattail::wpda_walker::ForkActionKind::Push,
                        });
                    };
                    if super::forks::CROSSCAT_LEX_COMPAT_RUNTIME_GATE {
                        quote! {
                            // Preserve the caller's Pratt floor for the same
                            // delegated operand-context reason as the singleton
                            // CrossCatProjection arm above.
                            if crosscat_proj_lex_compatible(#src_idx, tokens, *pos) {
                                #__push
                            }
                        }
                    } else {
                        quote! {
                            // Preserve the caller's Pratt floor for the same
                            // delegated operand-context reason as the singleton
                            // CrossCatProjection arm above.
                            #__push
                        }
                    }
                }
                UnifiedDescriptor::NullaryLiteralRun { rule_idx } => {
                    let rule_idx = *rule_idx;
                    // Task #10 item 1: same disposition-routed rows as the
                    // BinderPrefix arm above.
                    record_initiating_rule_rows(
                        fork_rows,
                        category_src_idx,
                        rule_idx,
                        branch_position as u16,
                        s1_dispositions,
                        s1_group_members,
                        &fork_bucket_tag,
                    );
                    // S1-FACTORING F1: nullary members join spine groups too
                    // (the Nil-group's rules 15/16). Same disposition routing
                    // as the BinderPrefix arm above; the spine trigger branch
                    // is BinderRule-shaped regardless of member kind — a
                    // nullary member re-enters its own
                    // `MixfixLiteralRun{kind:2}` tail only at its COMMIT leaf
                    // (amendment A4 typed coordinates).
                    match s1_dispositions.get(&rule_idx) {
                        Some(super::factoring::SpineDisposition::GroupFirst {
                            spine_id,
                            body_src_idx: group_body_src_idx,
                            weight_rule_idx,
                        }) => super::factoring::emit_spine_trigger_branch(
                            category_src_idx,
                            *spine_id,
                            *group_body_src_idx,
                            *weight_rule_idx,
                        ),
                        Some(super::factoring::SpineDisposition::GroupRest) => TokenStream::new(),
                        None => quote! {
                            // GAP-3: nullary multi-literal keyword prefix Fork branch
                            // (e.g. `@ Nil` co-bucketed with `@ ( p )` / `@ p`).
                            // Consume the trigger as a TriggerTerminal, push the
                            // mixfix marker, enter MixfixLiteralRun(kind=2). Tier 0.0
                            // (atomic-home) so lex-min picks the lowest-rule_idx branch
                            // (declaration order) on a parse-success tie — NQuoteNil
                            // (declared before NQuoteShort) wins for `@Nil`.
                            __pd_branches.push(mettail_prattail::wpda_walker::ForkBranch {
                                symbol: StackSymbolV2::mixfix_marker(
                                    #category_src_idx, #rule_idx, 0u8,
                                ),
                                weight: lex_w(0.0, #category_src_idx, #rule_idx),
                                new_state: WpdaState::MixfixLiteralRun {
                                    result_src_idx: #category_src_idx,
                                    rule_idx: #rule_idx,
                                    completed_idx: 0u8,
                                    kind: 2u8,
                                    sub_pos: 0u8,
                                },
                                action_kind:
                                    mettail_prattail::wpda_walker::ForkActionKind::ConsumeAndPush {
                                        trigger_mode:
                                            mettail_prattail::wpda_walker::TriggerMode::ConsumeAsTriggerOnly,
                                    },
                            });
                        },
                    }
                }
            })
            .collect();
        (
            quote! { #pat if #guard },
            quote! {
                {
                let mut __pd_branches: Vec<mettail_prattail::wpda_walker::ForkBranch<_>> =
                    Vec::with_capacity(#n_descs);
                #( #push_stmts )*
                return WpdaStepAction::Fork {
                    branches: __pd_branches,
                    consume_trigger: false,
                };
                }
            },
        )
    }
}

/// Emit a singleton atomic arm. Task #15 (frame-bound peel): returns the
/// `(head, body)` split — `head` = `#pat if #guard` (stays inline in `step`),
/// `body` = the `{ .. }` block (relocated into a per-arm `#[inline(never)]`
/// helper). Byte-identical parse semantics; pure body-relocation.
fn emit_atomic_arm_singleton(desc: &PrefixArmDescriptor) -> (TokenStream, TokenStream) {
    let pat = &desc.pattern;
    let category_src_idx = desc.category_src_idx;
    let rule_idx = desc.rule_idx;
    let guard = match &desc.extra_guard {
        Some(eg) => quote! { #eg && state_cat_src_idx == #category_src_idx },
        None => quote! { state_cat_src_idx == #category_src_idx },
    };
    (
        quote! { #pat if #guard },
        quote! {
            {
            return WpdaStepAction::ConsumeAndPush {
                symbol: StackSymbolV2::rule_at(
                    #category_src_idx, #rule_idx, 0, Some(_outer_bp),
                ).with_kind_return(),
                weight: lex_w(0.0, #category_src_idx, #rule_idx),
                new_state: WpdaState::Unwinding,
                // Phase F.8: atomic literal arm — the consumed token IS
                // the action arg (CaptureForBuilder). Not a unary-prefix
                // trigger (no operand sub-parse).
                trigger_mode: mettail_prattail::wpda_walker::TriggerMode::CaptureForBuilder,
            };
            }
        },
    )
}

/// For a `LiteralPatterned` shape, return the `(pattern, extra_guard)` pair.
/// The `extra_guard` is combined with the `state_cat_src_idx` check into a
/// single Rust match guard by the caller.
/// Stage 3 (2026-04-27): the lexer's actual emitted TokenKind for an
/// integer/rational/fixed-point literal depends on which Token variant the
/// DFA accept-state chose:
///   - `Token::Integer(_, _)` (built-in numeric, polymorphic) →
///     `TokenKind::Integer` (untyped)
///   - `Token::<Cat>(text)` (typed payload variant) → either
///     `TokenKind::IntegerLit(cat)` (when Token enum and adapter agree on
///     the typed family) OR `TokenKind::Custom(cat)` (when the adapter's
///     `seen` HashSet collapsed Custom and IntegerLit on the same name —
///     the Custom arm wins by ordering in the generated `token_to_kind`).
///
/// To avoid relying on lexer-internal canonicalization, the prefix arm
/// matches all three TokenKind variants, with the category disambiguation
/// delegated to:
///   1. `state_cat_src_idx == #category_src_idx` (always required)
///   2. The semantic action's eval block (`parse_int_lit(text, suffix)`)
///     which validates the suffix matches the category's expected type.
///
/// **B11 (2026-04-28)**: the bare polymorphic `TokenKind::Integer` arm is
/// gated on [`EmissionContext`]. In `HomeCategory` context the bare arm is
/// always emitted for `Integer`-family kinds (including `CanonicalBigInt`)
/// so unsuffixed integers in the home category's PrefixDispatch resolve
/// directly to that category's NumLit. In `CrossCatProjection` and
/// `FirstSet` contexts the bare arm is emitted only for primitive integer
/// widths (i8/i16/i32/i64/i128/isize/u8/u16/u32/u64/u128/usize) — for
/// `CanonicalBigInt` it's suppressed so primitive-integer cross-cat
/// projections like `ProcInt`/`ProcUInt32` aren't shadowed when Proc
/// derives `FIRST(BigInt)` for its `ProcBigInt` arm. The `kind`-based
/// suppression list is unchanged from the prior `is_primitive_int`
/// predicate but is now **only consulted in non-home contexts**.
fn literal_patterned_pattern_and_guard_for_kind(
    cat_name: &str,
    family: LiteralFamily,
    kind: Option<&NativeKind>,
    ctx: EmissionContext,
) -> Vec<(TokenStream, Option<TokenStream>)> {
    match family {
        LiteralFamily::Integer => {
            let mut arms = vec![
                // Typed payload variant emitted as IntegerLit(cat).
                (
                    quote! { Some(mettail_prattail::automata::TokenKind::IntegerLit(__cat)) },
                    Some(quote! { __cat == #cat_name }),
                ),
                // Typed payload variant emitted as Custom(cat) due to
                // adapter `seen` HashSet ordering.
                (
                    quote! { Some(mettail_prattail::automata::TokenKind::Custom(__cat)) },
                    Some(quote! { __cat == #cat_name }),
                ),
            ];
            // Bare polymorphic `TokenKind::Integer` arm. Always emitted in
            // HomeCategory context; in FirstSet context emitted only for
            // primitive-integer widths so `CanonicalBigInt` doesn't shadow
            // primitive-integer cross-cat projections (see fn doc above).
            let emit_bare_arm = match ctx {
                EmissionContext::HomeCategory => home_polymorphic_token_arm(family).is_some(),
                EmissionContext::FirstSet => matches!(
                    kind,
                    None | Some(NativeKind::Int8)
                        | Some(NativeKind::Int16)
                        | Some(NativeKind::Int32)
                        | Some(NativeKind::Int64)
                        | Some(NativeKind::Int128)
                        | Some(NativeKind::Isize)
                        | Some(NativeKind::UInt8)
                        | Some(NativeKind::UInt16)
                        | Some(NativeKind::UInt32)
                        | Some(NativeKind::UInt64)
                        | Some(NativeKind::UInt128)
                        | Some(NativeKind::Usize)
                ),
            };
            if emit_bare_arm {
                if let Some(pat) = home_polymorphic_token_arm(family) {
                    arms.push((pat, None));
                }
            }
            arms
        },
        LiteralFamily::Rational => vec![
            (
                quote! { Some(mettail_prattail::automata::TokenKind::RationalLit(__cat)) },
                Some(quote! { __cat == #cat_name }),
            ),
            (
                quote! { Some(mettail_prattail::automata::TokenKind::Custom(__cat)) },
                Some(quote! { __cat == #cat_name }),
            ),
            // No bare `TokenKind::Integer` arm for Rational. Stage 4 fix
            // (2026-04-27): the default eval body for Rational
            // (`parse_rational_lit(text)`) requires an `r` suffix, so bare
            // integers like `"0"` fail. Allowing this arm caused RhoCalc's
            // Proc dispatch to route bare integers to `CastBigRat` (the
            // first declared cross-cat projection with Integer in its
            // FIRST set), shadowing `CastInt`/`CastUInt32`. The lexer
            // canonicalizes bare integers to `Token::Integer(_, _)` →
            // `TokenKind::Integer`; rational parses are reachable only via
            // typed `Token::BigRat(_)` → `TokenKind::RationalLit("BigRat")`
            // which is handled by the first arm above.
        ],
        LiteralFamily::FixedPoint => vec![
            (
                quote! { Some(mettail_prattail::automata::TokenKind::FixedPointLit(__cat)) },
                Some(quote! { __cat == #cat_name }),
            ),
            (
                quote! { Some(mettail_prattail::automata::TokenKind::Custom(__cat)) },
                Some(quote! { __cat == #cat_name }),
            ),
        ],
        LiteralFamily::Float => {
            vec![(quote! { Some(mettail_prattail::automata::TokenKind::Float) }, None)]
        },
        LiteralFamily::Boolean => vec![(
            quote! {
                Some(mettail_prattail::automata::TokenKind::True)
                | Some(mettail_prattail::automata::TokenKind::False)
                | Some(mettail_prattail::automata::TokenKind::BooleanLit)
            },
            None,
        )],
        LiteralFamily::String => {
            vec![(quote! { Some(mettail_prattail::automata::TokenKind::StringLit) }, None)]
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::grammar::{rule_fixture, GrammarItem, SyntaxExpr, TermParam};
    use mettail_ast::language::{LangType, TokenDef};
    use mettail_ast::types::TypeExpr;
    use proc_macro2::Span;
    use syn::{parse_quote, Ident};

    fn atomic_rule(label: &str, cat: &str, kind: NonTerminalKind) -> GrammarRule {
        GrammarRule {
            items: vec![GrammarItem::NonTerminal {
                ident: Ident::new(&format!("{:?}", kind), Span::call_site()),
                kind,
            }],
            ..rule_fixture(Ident::new(label, Span::call_site()), Ident::new(cat, Span::call_site()))
        }
    }

    fn category_rule(label: &str, cat: &str, referenced_cat: &str) -> GrammarRule {
        GrammarRule {
            items: vec![GrammarItem::NonTerminal {
                ident: Ident::new(referenced_cat, Span::call_site()),
                kind: NonTerminalKind::Category,
            }],
            ..rule_fixture(Ident::new(label, Span::call_site()), Ident::new(cat, Span::call_site()))
        }
    }

    fn terminal_rule(label: &str, cat: &str, text: &str) -> GrammarRule {
        GrammarRule {
            items: vec![GrammarItem::Terminal(text.into())],
            ..rule_fixture(Ident::new(label, Span::call_site()), Ident::new(cat, Span::call_site()))
        }
    }

    fn judgement_rule(
        label: &str,
        cat: &str,
        params: &[(&str, &str)],
        syntax: Vec<SyntaxExpr>,
    ) -> GrammarRule {
        GrammarRule {
            term_context: Some(
                params
                    .iter()
                    .map(|(name, ty)| TermParam::Simple {
                        name: Ident::new(name, Span::call_site()),
                        ty: TypeExpr::Base(Ident::new(ty, Span::call_site())),
                    })
                    .collect(),
            ),
            syntax_pattern: Some(syntax),
            ..rule_fixture(Ident::new(label, Span::call_site()), Ident::new(cat, Span::call_site()))
        }
    }

    fn empty_lang() -> LanguageDef {
        LanguageDef {
            name: Ident::new("Test", Span::call_site()),
            options: Default::default(),
            extends_names: Vec::new(),
            include_names: Vec::new(),
            mixin_names: Vec::new(),
            types: Vec::new(),
            refinement_types: Vec::new(),
            token_defs: Vec::new(),
            mode_defs: Vec::new(),
            sync_constraints: Vec::new(),
            tree_invariants: Vec::new(),
            terms: Vec::new(),
            equations: Vec::new(),
            rewrites: Vec::new(),
            logic: None,
            guard_config: None,
        }
    }

    fn lang_with_int_literal() -> LanguageDef {
        let mut lang = empty_lang();
        lang.types.push(LangType {
            name: Ident::new("Int", Span::call_site()),
            native_type: Some(parse_quote!(i32)),
            collection_kind: None,
        });
        lang.token_defs.push(TokenDef {
            name: Ident::new("Integer", Span::call_site()),
            pattern: r"[0-9]+".to_string(),
            category: Some(Ident::new("Int", Span::call_site())),
            rust_code: Some(quote! { Ok(text.parse::<i32>().unwrap_or(0)) }),
            priority: None,
            push_mode: None,
            is_pop: false,
            stream: None,
            from_literals: true,
        });
        lang
    }

    fn lang_with_bool_literal() -> LanguageDef {
        let mut lang = empty_lang();
        lang.types.push(LangType {
            name: Ident::new("Bool", Span::call_site()),
            native_type: Some(parse_quote!(bool)),
            collection_kind: None,
        });
        lang.token_defs.push(TokenDef {
            name: Ident::new("Boolean", Span::call_site()),
            pattern: r"true|false".to_string(),
            category: Some(Ident::new("Bool", Span::call_site())),
            rust_code: Some(quote! { Ok(text == "true") }),
            priority: None,
            push_mode: None,
            is_pop: false,
            stream: None,
            from_literals: true,
        });
        lang
    }

    #[test]
    fn classifies_integer_literal_as_atomic() {
        let lang = empty_lang();
        let rule = atomic_rule("IntLit", "Int", NonTerminalKind::Integer);
        assert!(matches!(classify_atomic(&rule, &lang), AtomicShape::LiteralInteger));
    }

    #[test]
    fn classifies_boolean_as_atomic() {
        let lang = empty_lang();
        let rule = atomic_rule("BoolLit", "Bool", NonTerminalKind::Boolean);
        assert!(matches!(classify_atomic(&rule, &lang), AtomicShape::LiteralBoolean));
    }

    #[test]
    fn classifies_string_as_atomic() {
        let lang = empty_lang();
        let rule = atomic_rule("StrLit", "Str", NonTerminalKind::StringLiteral);
        assert!(matches!(classify_atomic(&rule, &lang), AtomicShape::LiteralString));
    }

    #[test]
    fn classifies_float_as_atomic() {
        let lang = empty_lang();
        let rule = atomic_rule("FloatLit", "Float", NonTerminalKind::FloatLiteral);
        assert!(matches!(classify_atomic(&rule, &lang), AtomicShape::LiteralFloat));
    }

    #[test]
    fn judgement_style_infix_rule_is_non_atomic_in_phase_a2() {
        // A judgement-style binary-infix rule (`a "+" b`) is composite
        // (Phase A.3+ / infix territory) and must classify as NonAtomic.
        // (Pre-GAP-3 this test used an all-LITERAL nullary body `["+", "1"]`,
        // but GAP-3 reclassifies the pure-literal nullary shape as
        // `NullaryLiteralRun` — see the companion test below.)
        let lang = empty_lang();
        let rule = judgement_rule(
            "X",
            "Y",
            &[("a", "Y"), ("b", "Y")],
            vec![
                SyntaxExpr::Param(Ident::new("a", Span::call_site())),
                SyntaxExpr::Literal("+".into()),
                SyntaxExpr::Param(Ident::new("b", Span::call_site())),
            ],
        );
        assert!(matches!(classify_atomic(&rule, &lang), AtomicShape::NonAtomic));
    }

    #[test]
    fn judgement_style_nullary_multi_literal_is_nullary_literal_run() {
        // GAP-3 (2026-06-28): an empty-term-context rule whose syntax_pattern
        // is two-or-more consecutive literals (e.g. RhoCalc's
        // `MapEmpty . |- "Map" "(" ")"`) classifies as NullaryLiteralRun —
        // the FIRST literal is the trigger, the REST are the trailing literals.
        let lang = empty_lang();
        let rule = judgement_rule(
            "MapEmpty",
            "Proc",
            &[],
            vec![
                SyntaxExpr::Literal("Map".into()),
                SyntaxExpr::Literal("(".into()),
                SyntaxExpr::Literal(")".into()),
            ],
        );
        match classify_atomic(&rule, &lang) {
            AtomicShape::NullaryLiteralRun { trigger, trailing_literals, .. } => {
                assert_eq!(trigger, "Map");
                assert_eq!(trailing_literals, vec!["(".to_string(), ")".to_string()]);
            },
            other => panic!("expected NullaryLiteralRun, got {:?}", other),
        }
    }

    #[test]
    fn judgement_style_nullary_terminal_is_terminal_keyword() {
        // Calculator's `Err . |- "error" : Int` shape: empty term_context,
        // single-literal syntax_pattern. Must classify as TerminalKeyword.
        let lang = empty_lang();
        let rule = GrammarRule {
            term_context: Some(Vec::new()),
            syntax_pattern: Some(vec![mettail_ast::grammar::SyntaxExpr::Literal("error".into())]),
            ..rule_fixture(
                Ident::new("Err", Span::call_site()),
                Ident::new("Int", Span::call_site()),
            )
        };
        match classify_atomic(&rule, &lang) {
            AtomicShape::TerminalKeyword { terminal_text, wrapper_variant } => {
                assert_eq!(terminal_text, "error");
                assert_eq!(wrapper_variant.to_string(), "Err");
            },
            other => panic!("expected TerminalKeyword, got {:?}", other),
        }
    }

    #[test]
    fn multi_item_rule_is_non_atomic() {
        let lang = empty_lang();
        let mut rule = atomic_rule("Add", "Int", NonTerminalKind::Integer);
        rule.items.push(GrammarItem::Terminal("+".into()));
        rule.items.push(GrammarItem::NonTerminal {
            ident: Ident::new("Integer", Span::call_site()),
            kind: NonTerminalKind::Integer,
        });
        assert!(matches!(classify_atomic(&rule, &lang), AtomicShape::NonAtomic));
    }

    #[test]
    fn empty_rule_list_emits_no_arms() {
        let lang = empty_lang();
        let (mut ts, __ts_helpers) = emit_prefix_arms_for_category(&lang, 0, "Int", &[], &std::collections::HashMap::new(), &std::collections::HashMap::new(), &mut super::super::fork_emission::ForkEmissionOrdinalModel::new());
        // Task #15 peel: combine arms + helpers (both empty for no rules).
        ts.extend(__ts_helpers);
        assert!(ts.to_string().trim().is_empty());
    }

    #[test]
    fn atomic_integer_rule_emits_an_arm() {
        let lang = empty_lang();
        let rule = atomic_rule("IntLit", "Int", NonTerminalKind::Integer);
        let (mut ts, __ts_helpers) = emit_prefix_arms_for_category(&lang, 2, "Int", &[(0, &rule)], &std::collections::HashMap::new(), &std::collections::HashMap::new(), &mut super::super::fork_emission::ForkEmissionOrdinalModel::new());
        // Task #15 peel: assert over arms + helpers combined (bodies moved).
        ts.extend(__ts_helpers);
        let s = ts.to_string();
        assert!(s.contains("ConsumeAndPush"));
        assert!(s.contains("Integer"));
        assert!(s.contains("2u16"));
    }

    #[test]
    fn classifies_literal_patterned_int() {
        let lang = lang_with_int_literal();
        // Build a rule "IntLit . i:Int |- i : Int" shape: category = Int,
        // single item NonTerminal Category "Int", and rule.category == ident.
        let rule = category_rule("IntLit", "Int", "Int");
        match classify_atomic(&rule, &lang) {
            AtomicShape::LiteralPatterned { cat_name, family, wrapper_variant, .. } => {
                assert_eq!(cat_name, "Int");
                assert_eq!(family, LiteralFamily::Integer);
                assert_eq!(wrapper_variant.to_string(), "NumLit");
            },
            other => panic!("expected LiteralPatterned, got {:?}", other),
        }
    }

    #[test]
    fn cross_cat_projection_is_non_atomic() {
        // Calculator's `ProcInt . i:Int |- i : Proc` — single category item
        // but rule.category != ident ("Proc" != "Int"). Must classify as
        // NonAtomic (Phase 3 cross-cat territory).
        let lang = lang_with_int_literal();
        let rule = category_rule("ProcInt", "Proc", "Int");
        assert!(matches!(classify_atomic(&rule, &lang), AtomicShape::NonAtomic));
    }

    #[test]
    fn classifies_literal_patterned_bool() {
        let lang = lang_with_bool_literal();
        let rule = category_rule("BoolLit", "Bool", "Bool");
        match classify_atomic(&rule, &lang) {
            AtomicShape::LiteralPatterned { family, wrapper_variant, .. } => {
                assert_eq!(family, LiteralFamily::Boolean);
                assert_eq!(wrapper_variant.to_string(), "BoolLit");
            },
            other => panic!("expected LiteralPatterned(Boolean), got {:?}", other),
        }
    }

    #[test]
    fn classifies_terminal_keyword() {
        let lang = empty_lang();
        let rule = terminal_rule("Err", "Int", "error");
        match classify_atomic(&rule, &lang) {
            AtomicShape::TerminalKeyword { terminal_text, wrapper_variant } => {
                assert_eq!(terminal_text, "error");
                assert_eq!(wrapper_variant.to_string(), "Err");
            },
            other => panic!("expected TerminalKeyword, got {:?}", other),
        }
    }

    #[test]
    fn terminal_keyword_emits_fixed_match_guard() {
        let lang = empty_lang();
        let rule = terminal_rule("Err", "Int", "error");
        let (mut ts, __ts_helpers) = emit_prefix_arms_for_category(&lang, 2, "Int", &[(0, &rule)], &std::collections::HashMap::new(), &std::collections::HashMap::new(), &mut super::super::fork_emission::ForkEmissionOrdinalModel::new());
        // Task #15 peel: assert over arms + helpers combined (bodies moved).
        ts.extend(__ts_helpers);
        let s = ts.to_string();
        assert!(s.contains("ConsumeAndPush"));
        assert!(s.contains("Fixed"));
        assert!(s.contains("\"error\""));
        assert!(s.contains("2u16"));
    }

    #[test]
    fn literal_patterned_int_emits_integer_lit_guard() {
        let lang = lang_with_int_literal();
        let rule = category_rule("IntLit", "Int", "Int");
        let (mut ts, __ts_helpers) = emit_prefix_arms_for_category(&lang, 2, "Int", &[(0, &rule)], &std::collections::HashMap::new(), &std::collections::HashMap::new(), &mut super::super::fork_emission::ForkEmissionOrdinalModel::new());
        // Task #15 peel: assert over arms + helpers combined (bodies moved).
        ts.extend(__ts_helpers);
        let s = ts.to_string();
        assert!(s.contains("ConsumeAndPush"));
        assert!(s.contains("IntegerLit"));
        assert!(s.contains("\"Int\""));
        assert!(s.contains("2u16"));
    }

    #[test]
    fn prefix_operator_and_projection_share_one_ambiguity_bucket() {
        let mut lang = empty_lang();
        lang.types.push(LangType {
            name: Ident::new("UInt32", Span::call_site()),
            native_type: Some(parse_quote!(u32)),
            collection_kind: None,
        });
        lang.types.push(LangType {
            name: Ident::new("Bool", Span::call_site()),
            native_type: Some(parse_quote!(bool)),
            collection_kind: None,
        });

        let bool_first = judgement_rule(
            "BitNotBool",
            "Bool",
            &[("b", "Bool")],
            vec![
                SyntaxExpr::Literal("bitnot".into()),
                SyntaxExpr::Param(Ident::new("b", Span::call_site())),
            ],
        );
        let direct_prefix = judgement_rule(
            "BitNotUInt32",
            "UInt32",
            &[("u", "UInt32")],
            vec![
                SyntaxExpr::Literal("bitnot".into()),
                SyntaxExpr::Param(Ident::new("u", Span::call_site())),
            ],
        );
        let projection = judgement_rule(
            "BoolToUInt32",
            "UInt32",
            &[("b", "Bool")],
            vec![SyntaxExpr::Param(Ident::new("b", Span::call_site()))],
        );
        lang.terms = vec![direct_prefix.clone(), projection.clone(), bool_first];

        // Task #10 item 1 (Option A pin, coordinator decision 2026-07-14):
        // the projection (cat 0, rule 1) dispatches in TWO buckets at
        // DIFFERING positions — `"bitnot"` @ 1 (after the direct prefix)
        // vs the boolean-literal bucket @ 0 — the exact P7 shape that
        // refuted the amendment-6 panic. It must classify
        // AMBIGUOUS-MULTI-BUCKET (no derived ordinal → the site-2 fallback
        // 0 = the trait default, zero K-C movement), while the direct
        // prefix (single-bucket) keeps its derived position.
        let mut fork_model = super::super::fork_emission::ForkEmissionOrdinalModel::new();
        let (mut ts, __ts_helpers) = emit_prefix_arms_for_category(
            &lang,
            0,
            "UInt32",
            &[(0, &direct_prefix), (1, &projection)],
            &std::collections::HashMap::new(),
            &std::collections::HashMap::new(),
            &mut fork_model,
        );
        assert!(
            fork_model.is_ambiguous_multi_bucket(0, 1),
            "the multi-bucket projection classifies ambiguous (Option A)"
        );
        assert_eq!(
            fork_model.site2_ordinal(0, 1),
            None,
            "no guessed ordinal for the ambiguous projection"
        );
        assert_eq!(
            fork_model.site2_ordinal(0, 0),
            Some(0),
            "the single-bucket direct prefix keeps its derived position"
        );
        // Task #15 peel: the Fork body moved into the arm's helper; combine so
        // the WpdaStepAction::Fork / ForkActionKind assertions still see it.
        // The guard (with `__kw == "bitnot"`) stays in the arm, so its
        // single-occurrence count is unchanged.
        ts.extend(__ts_helpers);
        let s = ts.to_string();
        let guard = "__kw == \"bitnot\" && state_cat_src_idx == 0u16";
        assert_eq!(
            s.matches(guard).count(),
            1,
            "same fixed-token evidence must emit one arm, not first-match shadow arms: {s}"
        );
        assert!(s.contains("WpdaStepAction :: Fork"), "{s}");
        assert!(s.contains("ForkActionKind :: ConsumeAndPush"), "{s}");
        assert!(s.contains("ForkActionKind :: Push"), "{s}");
        assert!(s.contains("source_src_idx : 1u16"), "{s}");
        assert!(s.contains("consume_trigger : false"), "{s}");
    }
}
