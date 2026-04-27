//! Prefix-dispatch arm emission.
//!
//! Phase A.2 of Stage 6 plan v2. For each category, this module walks the
//! category's rule list and emits per-rule arms in the engine's
//! `WpdsState::PrefixDispatch` match. Atomic-literal rules emit a
//! `ConsumeAndPush(Return)` action so the walker captures the token,
//! advances pos, and transitions into `Unwinding` — where the Return
//! frame's pop fires the semantic action.
//!
//! Later phases (A.3 for Pratt, A.4 for cross-cat, A.6 for binders, etc.)
//! populate additional arms in the same match.

use mettail_ast::grammar::{GrammarItem, GrammarRule, NonTerminalKind};
use mettail_ast::language::{LanguageDef, NativeKind};
use proc_macro2::{Span, TokenStream};
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
                if let mettail_ast::grammar::TermParam::Simple { name: param_name, ty } = &tc[0]
                {
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
                    AtomicShape::VarRule {
                        wrapper_variant: rule.label.clone(),
                    }
                } else {
                    AtomicShape::NonAtomic
                }
            }
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
            }
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
///       the trampoline's auto-generated atomic-literal arm (e.g., for
///       `![i32] as Num`, the trampoline emits a
///       `Token::Integer(v, suffix) if suffix.matches_i32()` arm; we mirror
///       it with `parse_int_lit(text, Some(Suffix::I32))`).
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
        td.from_literals && td.category.as_ref().map(|c| c == cat_ident).unwrap_or(false)
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
}

/// Stage 1.1: compute the FIRST set for a category — the set of token
/// patterns that can begin a parse of a rule for this category. Walks
/// the category's atomic rules + recursively their cross-cat projection
/// sources. Used by cross-cat projection codegen to emit specific
/// dispatch arms in the *result* category's PrefixDispatch when the
/// peek'd token belongs to the *source* category.
pub fn first_set_of_category(
    cat_name: &str,
    language: &LanguageDef,
) -> Vec<FirstToken> {
    let mut acc = Vec::new();
    let mut visited = std::collections::HashSet::new();
    collect_first_set(cat_name, language, &mut acc, &mut visited);
    acc
}

fn collect_first_set(
    cat_name: &str,
    language: &LanguageDef,
    acc: &mut Vec<FirstToken>,
    visited: &mut std::collections::HashSet<String>,
) {
    if !visited.insert(cat_name.to_string()) {
        return; // cycle guard
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
    if let Some(lang_type) = language.types.iter().find(|t| t.name.to_string() == cat_name) {
        if let Some(nt) = lang_type.native_type.as_ref() {
            let kind = NativeKind::from_syn_type(nt);
            if let Some(family) = literal_family_for(&kind) {
                for (pattern, extra_guard) in
                    literal_patterned_pattern_and_guard_for_kind(cat_name, family, Some(&kind))
                {
                    acc.push(FirstToken { pattern, extra_guard });
                }
            }
        }
    }
    // Synthetic Var rule: user-defined categories without native_type get a
    // synthetic Var rule (Phase 5a in synthetic.rs). Add Ident to FIRST.
    if let Some(lang_type) = language.types.iter().find(|t| t.name.to_string() == cat_name) {
        if lang_type.native_type.is_none() {
            // Has-user-var-rule check: if any user rule for this cat
            // matches NonTerminal(Var), don't add (the user rule covers it).
            let has_user_var = language.terms.iter().any(|r| {
                r.category.to_string() == cat_name
                    && r.items.first().map(|item| {
                        matches!(item, mettail_ast::grammar::GrammarItem::NonTerminal {
                            kind: mettail_ast::grammar::NonTerminalKind::Var, ..
                        })
                    }).unwrap_or(false)
            });
            if !has_user_var {
                acc.push(FirstToken {
                    pattern: quote! {
                        Some(mettail_prattail::automata::TokenKind::Ident)
                    },
                    extra_guard: None,
                });
            }
        }
    }
    // Walk all rules where rule.category == cat_name.
    for rule in &language.terms {
        if rule.category.to_string() != cat_name {
            continue;
        }
        let shape = classify_atomic(rule, language);
        match shape {
            AtomicShape::LiteralPatterned { cat_name: c, family, ref native_type, .. } => {
                let nk = NativeKind::from_syn_type(native_type);
                for (pattern, extra_guard) in
                    literal_patterned_pattern_and_guard_for_kind(&c, family, Some(&nk))
                {
                    acc.push(FirstToken { pattern, extra_guard });
                }
            }
            AtomicShape::TerminalKeyword { terminal_text, .. } => {
                acc.push(FirstToken {
                    pattern: quote! {
                        Some(mettail_prattail::automata::TokenKind::Fixed(__kw))
                    },
                    extra_guard: Some(quote! { __kw == #terminal_text }),
                });
            }
            AtomicShape::VarRule { .. } => {
                acc.push(FirstToken {
                    pattern: quote! {
                        Some(mettail_prattail::automata::TokenKind::Ident)
                    },
                    extra_guard: None,
                });
            }
            AtomicShape::LiteralInteger => {
                acc.push(FirstToken {
                    pattern: quote! {
                        Some(mettail_prattail::automata::TokenKind::Integer)
                    },
                    extra_guard: None,
                });
            }
            AtomicShape::LiteralBoolean => {
                acc.push(FirstToken {
                    pattern: quote! {
                        Some(mettail_prattail::automata::TokenKind::True)
                        | Some(mettail_prattail::automata::TokenKind::False)
                        | Some(mettail_prattail::automata::TokenKind::BooleanLit)
                    },
                    extra_guard: None,
                });
            }
            AtomicShape::LiteralString => {
                acc.push(FirstToken {
                    pattern: quote! {
                        Some(mettail_prattail::automata::TokenKind::StringLit)
                    },
                    extra_guard: None,
                });
            }
            AtomicShape::LiteralFloat => {
                acc.push(FirstToken {
                    pattern: quote! {
                        Some(mettail_prattail::automata::TokenKind::Float)
                    },
                    extra_guard: None,
                });
            }
            AtomicShape::CrossCatProjection { source_cat_name, .. } => {
                // Recurse into the source category's FIRST set.
                collect_first_set(&source_cat_name, language, acc, visited);
            }
            AtomicShape::CrossCatPrefixUnary { trigger, .. } => {
                acc.push(FirstToken {
                    pattern: quote! {
                        Some(mettail_prattail::automata::TokenKind::Fixed(__kw))
                    },
                    extra_guard: Some(quote! { __kw == #trigger }),
                });
            }
            AtomicShape::NonAtomic => {
                // Pratt prefix / collection / binder rules: their FIRST
                // typically starts with a literal trigger from
                // syntax_pattern[0]. Best-effort extract.
                if let Some(sp) = rule.syntax_pattern.as_ref() {
                    if let Some(mettail_ast::grammar::SyntaxExpr::Literal(text)) =
                        sp.first()
                    {
                        acc.push(FirstToken {
                            pattern: quote! {
                                Some(mettail_prattail::automata::TokenKind::Fixed(__kw))
                            },
                            extra_guard: Some(quote! { __kw == #text }),
                        });
                    }
                }
            }
        }
    }
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
pub fn emit_prefix_arms_for_category(
    language: &LanguageDef,
    category_src_idx: u16,
    category_name: &str,
    rules_in_category: &[(u16, &GrammarRule)],
) -> TokenStream {
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
    for source_cat_name in &cross_cat_infix_sources {
        let source_src_idx = categories
            .iter()
            .position(|c| c == source_cat_name)
            .map(|i| i as u16)
            .unwrap_or(0);
        let first_set = first_set_of_category(source_cat_name, language);
        for ft in first_set {
            let pat = ft.pattern;
            let guard = match ft.extra_guard {
                Some(eg) => quote! { #eg && state_cat_src_idx == #category_src_idx },
                None => quote! { state_cat_src_idx == #category_src_idx },
            };
            arms.push(quote! {
                #pat if #guard => {
                    // Stage 1.2: cross-cat infix LHS delegation. Push
                    // CategoryEntry(source_cat) for the LHS sub-parse.
                    // After LHS returns, InfixLoop on operand_cat will see
                    // the cross-cat operator + complete the rule.
                    return WpdsStepAction::Push {
                        symbol: StackSymbolV2::category_entry(#source_src_idx),
                        weight: LexicographicWeight::one(),
                        new_state: WpdsState::PrefixDispatch {
                            pos: *pos,
                            cur_bp: *cur_bp,
                        },
                    };
                }
            });
        }
    }
    for &(rule_idx, rule) in rules_in_category {
        let shape = classify_atomic(rule, language);
        for arm in emit_atomic_arms(category_src_idx, rule_idx, &shape) {
            arms.push(arm);
        }
        // Stage 1.1: cross-cat projection rules emit one prefix arm per
        // token in the SOURCE category's FIRST set, dispatching to a
        // CrossCatDelegate state that pushes the source CategoryEntry.
        if let AtomicShape::CrossCatProjection {
            source_cat_name,
            wrapper_variant: _,
        } = &shape
        {
            let cross_cat_arms = emit_cross_cat_projection_arms(
                category_src_idx,
                rule_idx,
                source_cat_name,
                language,
            );
            arms.push(cross_cat_arms);
        }
        // Stage 1.1: cross-cat prefix unary emits an arm matching the
        // trigger literal, then delegates to source category.
        if let AtomicShape::CrossCatPrefixUnary {
            trigger,
            source_cat_name,
            wrapper_variant: _,
        } = &shape
        {
            let arm = emit_cross_cat_prefix_unary_arm(
                category_src_idx,
                rule_idx,
                trigger,
                source_cat_name,
                language,
            );
            arms.push(arm);
        }
    }
    let _ = category_name;
    quote! { #(#arms)* }
}

/// Stage 1.1: emit prefix arms for a cross-cat projection rule.
/// For each token in `FIRST(source_cat)`, emit an arm that pushes a
/// Return marker (with the result_cat's rule_idx for action lookup) then
/// transitions to CrossCatDelegate to push the source CategoryEntry.
///
/// Stage 4 fix (2026-04-27): for `TokenKind::Integer` arms whose source
/// category is a primitive integer type (i32, u32, i64, etc.), emit an
/// `IntSuffix::from_text(...)` guard so suffix-mismatched inputs fall
/// through to the next-declared cross-cat projection. Without this,
/// `0u32` parsed as Calculator's `Proc` dispatches to `ProcInt` (the
/// first declared Integer-accepting projection) and the eval block
/// silently coerces u32 → i32, producing `Proc::ProcInt(NumLit(0))`
/// instead of the correct `Proc::ProcUInt32(NumLit(0))`. Mirrors the
/// trampoline's `Token::Integer(_, suffix) if suffix.matches_X()`
/// pattern.
///
/// **TECHNICAL DEBT (per `feedback_use_wpds_disambiguation_not_heuristics.md`):**
/// the `IntSuffix` matcher guards on bare-Integer arms are HEURISTICS
/// that work around the absence of GLR-style branching in the WPDS
/// engine. The principled fix: when multiple cross-cat projections share
/// a FIRST token (e.g., `Proc::ProcInt` and `Proc::ProcUInt32` both
/// accepting `TokenKind::Integer`), emit `WpdsStepAction::Fork` with one
/// branch per projection, weighted so the lex-min selection picks the
/// correct one based on the source's eval-block success/failure. Until
/// the engine's step function drives `AmbiguityFanout` forward (currently
/// returns Idle), treat the suffix-guard layer as a temporary scaffold;
/// once Fork is fully wired, the `int_suffix_guard` helper and the
/// `is_bare_integer` branch in the loop below can be removed.
fn emit_cross_cat_projection_arms(
    category_src_idx: u16,
    rule_idx: u16,
    source_cat_name: &str,
    language: &LanguageDef,
) -> TokenStream {
    let categories = super::collect_category_names_with_literals(language);
    let source_src_idx = categories
        .iter()
        .position(|c| c == source_cat_name)
        .map(|i| i as u16)
        .unwrap_or(0);
    let first_set = first_set_of_category(source_cat_name, language);

    // Stage 4 fix: derive the source category's NativeKind to refine
    // bare TokenKind::Integer arm guards with suffix matchers.
    let source_kind: Option<NativeKind> = language
        .types
        .iter()
        .find(|t| t.name.to_string() == source_cat_name)
        .and_then(|t| t.native_type.as_ref())
        .map(|nt| NativeKind::from_syn_type(nt));
    let source_suffix_guard = source_kind.as_ref().and_then(int_suffix_guard);

    let mut arms = Vec::new();
    for ft in first_set {
        let pat = ft.pattern;
        // Detect the bare `TokenKind::Integer` arm so we can attach a
        // suffix matcher. Compare the rendered TokenStream's text since
        // `TokenStream` doesn't implement `PartialEq`.
        let pat_str = pat.to_string();
        let is_bare_integer = pat_str.contains("TokenKind :: Integer")
            && !pat_str.contains("IntegerLit");
        let guard = match (ft.extra_guard, is_bare_integer, source_suffix_guard.as_ref()) {
            (Some(eg), _, _) => quote! { #eg && state_cat_src_idx == #category_src_idx },
            (None, true, Some(sg)) => quote! {
                state_cat_src_idx == #category_src_idx
                    && {
                        let __t = tokens.peek_text(*pos).unwrap_or("");
                        let __suf = mettail_prattail::IntSuffix::from_text(__t);
                        #sg
                    }
            },
            (None, _, _) => quote! { state_cat_src_idx == #category_src_idx },
        };
        arms.push(quote! {
            #pat if #guard => {
                // Push the cross-cat Return marker; on pop after source
                // parse returns, fire the wrap-action.
                return WpdsStepAction::Push {
                    symbol: StackSymbolV2::rule_at(
                        #category_src_idx, #rule_idx, 0, Some(_outer_bp),
                    ).with_kind_return(),
                    weight: LexicographicWeight::from_cost(
                        0.0, #category_src_idx, #rule_idx,
                    ),
                    new_state: WpdsState::CrossCatDelegate {
                        source_src_idx: #source_src_idx,
                        outer_bp: _outer_bp,
                    },
                };
            }
        });
    }
    quote! { #(#arms)* }
}

/// Stage 4 fix: produce an `IntSuffix` matcher expression for primitive
/// integer kinds. Returns `None` for non-integer or non-primitive kinds —
/// callers should emit no guard in that case.
fn int_suffix_guard(kind: &NativeKind) -> Option<TokenStream> {
    match kind {
        NativeKind::Int8 => Some(quote! { __suf.matches_i8() }),
        NativeKind::Int16 => Some(quote! { __suf.matches_i16() }),
        NativeKind::Int32 => Some(quote! { __suf.matches_i32() }),
        NativeKind::Int64 => Some(quote! { __suf.matches_i64() }),
        NativeKind::Int128 => Some(quote! { __suf.matches_i128() }),
        NativeKind::Isize => Some(quote! { __suf.matches_isize() }),
        NativeKind::UInt8 => Some(quote! { __suf.matches_u8() }),
        NativeKind::UInt16 => Some(quote! { __suf.matches_u16() }),
        NativeKind::UInt32 => Some(quote! { __suf.matches_u32() }),
        NativeKind::UInt64 => Some(quote! { __suf.matches_u64() }),
        NativeKind::UInt128 => Some(quote! { __suf.matches_u128() }),
        NativeKind::Usize => Some(quote! { __suf.matches_usize() }),
        // CanonicalBigInt has no suffix matcher (it accepts any Token::BigInt).
        // CanonicalBigRat, CanonicalFixedPoint, Float32/64, Bool, Str, Other:
        // no suffix matcher applicable.
        _ => None,
    }
}

/// Stage 1.1: emit a single prefix arm for a cross-cat prefix unary rule.
fn emit_cross_cat_prefix_unary_arm(
    category_src_idx: u16,
    rule_idx: u16,
    trigger: &str,
    source_cat_name: &str,
    language: &LanguageDef,
) -> TokenStream {
    let categories = super::collect_category_names_with_literals(language);
    let source_src_idx = categories
        .iter()
        .position(|c| c == source_cat_name)
        .map(|i| i as u16)
        .unwrap_or(0);
    quote! {
        Some(mettail_prattail::automata::TokenKind::Fixed(__kw))
            if __kw == #trigger && state_cat_src_idx == #category_src_idx => {
            // Consume trigger, push Return marker, delegate to source.
            return WpdsStepAction::ConsumeAndPush {
                symbol: StackSymbolV2::rule_at(
                    #category_src_idx, #rule_idx, 0, Some(_outer_bp),
                ).with_kind_return(),
                weight: LexicographicWeight::from_cost(
                    0.0, #category_src_idx, #rule_idx,
                ),
                new_state: WpdsState::CrossCatDelegate {
                    source_src_idx: #source_src_idx,
                    outer_bp: _outer_bp,
                },
                capture_token: false,
            };
        }
    }
}

/// Emit prefix-dispatch arms for an atomic rule. Returns one or more arms.
///
/// Rust match arms allow only one `if` guard per arm. Most atomic shapes
/// emit a single arm; `LiteralPatterned` integer/rational/fixed-point shapes
/// emit multiple arms (one per TokenKind variant the lexer might produce —
/// see `literal_patterned_pattern_and_guard` for the rationale). The
/// `state_cat_src_idx == #category_src_idx` check is always appended so
/// shared token variants dispatch to different categories depending on
/// current frame.
fn emit_atomic_arms(
    category_src_idx: u16,
    rule_idx: u16,
    shape: &AtomicShape,
) -> Vec<TokenStream> {
    let pattern_guards: Vec<(TokenStream, Option<TokenStream>)> = match shape {
        AtomicShape::LiteralInteger => vec![(
            quote! { Some(mettail_prattail::automata::TokenKind::Integer) },
            None,
        )],
        AtomicShape::LiteralBoolean => vec![(
            quote! {
                Some(mettail_prattail::automata::TokenKind::True)
                | Some(mettail_prattail::automata::TokenKind::False)
                | Some(mettail_prattail::automata::TokenKind::BooleanLit)
            },
            None,
        )],
        AtomicShape::LiteralString => vec![(
            quote! { Some(mettail_prattail::automata::TokenKind::StringLit) },
            None,
        )],
        AtomicShape::LiteralFloat => vec![(
            quote! { Some(mettail_prattail::automata::TokenKind::Float) },
            None,
        )],
        AtomicShape::LiteralPatterned { cat_name, family, native_type, .. } => {
            let nk = NativeKind::from_syn_type(native_type);
            literal_patterned_pattern_and_guard_for_kind(cat_name, *family, Some(&nk))
        }
        AtomicShape::TerminalKeyword { terminal_text, .. } => vec![(
            quote! { Some(mettail_prattail::automata::TokenKind::Fixed(__kw)) },
            Some(quote! { __kw == #terminal_text }),
        )],
        AtomicShape::VarRule { .. } => vec![(
            quote! { Some(mettail_prattail::automata::TokenKind::Ident) },
            None,
        )],
        // Stage 1.1: cross-cat shapes emit their own arms via
        // emit_cross_cat_projection_arms / emit_cross_cat_prefix_unary_arm.
        AtomicShape::CrossCatProjection { .. } | AtomicShape::CrossCatPrefixUnary { .. } => {
            return Vec::new()
        }
        AtomicShape::NonAtomic => return Vec::new(),
    };
    pattern_guards
        .into_iter()
        .map(|(token_pattern, extra_guard)| {
            let guard = match extra_guard {
                Some(eg) => quote! { #eg && state_cat_src_idx == #category_src_idx },
                None => quote! { state_cat_src_idx == #category_src_idx },
            };
            quote! {
                #token_pattern if #guard => {
                    return WpdsStepAction::ConsumeAndPush {
                        symbol: StackSymbolV2::rule_at(
                            #category_src_idx, #rule_idx, 0, Some(_outer_bp),
                        ).with_kind_return(),
                        weight: LexicographicWeight::from_cost(0.0, #category_src_idx, #rule_idx),
                        new_state: WpdsState::Unwinding,
                        // Atomic literal: token is pushed to the builder so the
                        // Pop(Return) action can consume it as ActionArg::Token.
                        capture_token: true,
                    };
                }
            }
        })
        .collect()
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
fn literal_patterned_pattern_and_guard(
    cat_name: &str,
    family: LiteralFamily,
) -> Vec<(TokenStream, Option<TokenStream>)> {
    literal_patterned_pattern_and_guard_for_kind(cat_name, family, None)
}

/// Stage 4 fix: variant that takes the source `NativeKind` to refine the
/// emitted patterns. For `CanonicalBigInt` (typed payload — lexer emits
/// `Token::BigInt(text)`, NOT `Token::Integer(_, _)`), we omit the bare
/// `TokenKind::Integer` arm — it would otherwise shadow primitive-integer
/// cross-cat projections like `ProcInt`/`ProcUInt32` that DO match
/// `TokenKind::Integer`. For primitive integers (i32, u32, etc.), all three
/// patterns are emitted as the lexer canonicalizes any of them to
/// `Token::Integer(_, suffix)`.
fn literal_patterned_pattern_and_guard_for_kind(
    cat_name: &str,
    family: LiteralFamily,
    kind: Option<&NativeKind>,
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
            // Only primitive integers (i32, u32, etc.) lex as
            // `Token::Integer(_, suffix)` → `TokenKind::Integer`.
            // CanonicalBigInt lexes as `Token::BigInt(text)`; including
            // the bare Integer arm here causes BigInt's cross-cat
            // projection to fire on every unsuffixed integer, shadowing
            // the primitive-integer projections.
            let is_primitive_int = matches!(
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
            );
            if is_primitive_int {
                // Built-in polymorphic Token::Integer → TokenKind::Integer.
                arms.push((
                    quote! { Some(mettail_prattail::automata::TokenKind::Integer) },
                    None,
                ));
            }
            arms
        }
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
            let _ = cat_name;
            vec![(
                quote! { Some(mettail_prattail::automata::TokenKind::Float) },
                None,
            )]
        }
        LiteralFamily::Boolean => {
            let _ = cat_name;
            vec![(
                quote! {
                    Some(mettail_prattail::automata::TokenKind::True)
                    | Some(mettail_prattail::automata::TokenKind::False)
                    | Some(mettail_prattail::automata::TokenKind::BooleanLit)
                },
                None,
            )]
        }
        LiteralFamily::String => {
            let _ = cat_name;
            vec![(
                quote! { Some(mettail_prattail::automata::TokenKind::StringLit) },
                None,
            )]
        }
    }
}

// Silence `unused` warnings that fire only on some feature-flag combos.
#[allow(dead_code)]
fn _keep_imports_live() -> Option<Span> {
    let _ = format_ident!("Foo");
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::grammar::GrammarItem;
    use mettail_ast::language::{LangType, TokenDef};
    use proc_macro2::Span;
    use syn::{parse_quote, Ident};

    fn atomic_rule(label: &str, cat: &str, kind: NonTerminalKind) -> GrammarRule {
        GrammarRule {
            label: Ident::new(label, Span::call_site()),
            category: Ident::new(cat, Span::call_site()),
            items: vec![GrammarItem::NonTerminal {
                ident: Ident::new(&format!("{:?}", kind), Span::call_site()),
                kind,
            }],
            bindings: Vec::new(),
            term_context: None,
            syntax_pattern: None,
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
        }
    }

    fn category_rule(label: &str, cat: &str, referenced_cat: &str) -> GrammarRule {
        GrammarRule {
            label: Ident::new(label, Span::call_site()),
            category: Ident::new(cat, Span::call_site()),
            items: vec![GrammarItem::NonTerminal {
                ident: Ident::new(referenced_cat, Span::call_site()),
                kind: NonTerminalKind::Category,
            }],
            bindings: Vec::new(),
            term_context: None,
            syntax_pattern: None,
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
        }
    }

    fn terminal_rule(label: &str, cat: &str, text: &str) -> GrammarRule {
        GrammarRule {
            label: Ident::new(label, Span::call_site()),
            category: Ident::new(cat, Span::call_site()),
            items: vec![GrammarItem::Terminal(text.into())],
            bindings: Vec::new(),
            term_context: None,
            syntax_pattern: None,
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
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
        assert!(matches!(
            classify_atomic(&rule, &lang),
            AtomicShape::LiteralInteger
        ));
    }

    #[test]
    fn classifies_boolean_as_atomic() {
        let lang = empty_lang();
        let rule = atomic_rule("BoolLit", "Bool", NonTerminalKind::Boolean);
        assert!(matches!(
            classify_atomic(&rule, &lang),
            AtomicShape::LiteralBoolean
        ));
    }

    #[test]
    fn classifies_string_as_atomic() {
        let lang = empty_lang();
        let rule = atomic_rule("StrLit", "Str", NonTerminalKind::StringLiteral);
        assert!(matches!(
            classify_atomic(&rule, &lang),
            AtomicShape::LiteralString
        ));
    }

    #[test]
    fn classifies_float_as_atomic() {
        let lang = empty_lang();
        let rule = atomic_rule("FloatLit", "Float", NonTerminalKind::FloatLiteral);
        assert!(matches!(
            classify_atomic(&rule, &lang),
            AtomicShape::LiteralFloat
        ));
    }

    #[test]
    fn judgement_style_non_nullary_rule_is_non_atomic_in_phase_a2() {
        // A judgement-style rule with composite syntax_pattern (not a single
        // terminal literal) must classify as NonAtomic (Phase A.3+ territory).
        let lang = empty_lang();
        let mut rule = atomic_rule("X", "Y", NonTerminalKind::Integer);
        rule.term_context = Some(Vec::new());
        rule.syntax_pattern = Some(vec![
            mettail_ast::grammar::SyntaxExpr::Literal("+".into()),
            mettail_ast::grammar::SyntaxExpr::Literal("1".into()),
        ]);
        assert!(matches!(classify_atomic(&rule, &lang), AtomicShape::NonAtomic));
    }

    #[test]
    fn judgement_style_nullary_terminal_is_terminal_keyword() {
        // Calculator's `Err . |- "error" : Int` shape: empty term_context,
        // single-literal syntax_pattern. Must classify as TerminalKeyword.
        let lang = empty_lang();
        let mut rule = GrammarRule {
            label: Ident::new("Err", Span::call_site()),
            category: Ident::new("Int", Span::call_site()),
            items: Vec::new(),
            bindings: Vec::new(),
            term_context: Some(Vec::new()),
            syntax_pattern: Some(vec![mettail_ast::grammar::SyntaxExpr::Literal(
                "error".into(),
            )]),
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
            tier_directive: None,
        };
        let _ = &mut rule;
        match classify_atomic(&rule, &lang) {
            AtomicShape::TerminalKeyword { terminal_text, wrapper_variant } => {
                assert_eq!(terminal_text, "error");
                assert_eq!(wrapper_variant.to_string(), "Err");
            }
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
        let ts = emit_prefix_arms_for_category(&lang, 0, "Int", &[]);
        assert!(ts.to_string().trim().is_empty());
    }

    #[test]
    fn atomic_integer_rule_emits_an_arm() {
        let lang = empty_lang();
        let rule = atomic_rule("IntLit", "Int", NonTerminalKind::Integer);
        let ts = emit_prefix_arms_for_category(&lang, 2, "Int", &[(0, &rule)]);
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
            }
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
        assert!(matches!(
            classify_atomic(&rule, &lang),
            AtomicShape::NonAtomic
        ));
    }

    #[test]
    fn classifies_literal_patterned_bool() {
        let lang = lang_with_bool_literal();
        let rule = category_rule("BoolLit", "Bool", "Bool");
        match classify_atomic(&rule, &lang) {
            AtomicShape::LiteralPatterned { family, wrapper_variant, .. } => {
                assert_eq!(family, LiteralFamily::Boolean);
                assert_eq!(wrapper_variant.to_string(), "BoolLit");
            }
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
            }
            other => panic!("expected TerminalKeyword, got {:?}", other),
        }
    }

    #[test]
    fn terminal_keyword_emits_fixed_match_guard() {
        let lang = empty_lang();
        let rule = terminal_rule("Err", "Int", "error");
        let ts = emit_prefix_arms_for_category(&lang, 2, "Int", &[(0, &rule)]);
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
        let ts = emit_prefix_arms_for_category(&lang, 2, "Int", &[(0, &rule)]);
        let s = ts.to_string();
        assert!(s.contains("ConsumeAndPush"));
        assert!(s.contains("IntegerLit"));
        assert!(s.contains("\"Int\""));
        assert!(s.contains("2u16"));
    }
}
