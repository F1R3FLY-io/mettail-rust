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
use proc_macro2::TokenStream;
use quote::quote;
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
/// suppressed in `CrossCatProjection` and `FirstSet` (so primitive-integer
/// cross-cat projections like `ProcInt`/`ProcUInt32` aren't shadowed when
/// the FIRST set of `BigInt` is consumed by other categories' cross-cat
/// dispatch). Generalizes uniformly across all NativeKinds via
/// `home_polymorphic_token_arm(family)` — adding a new kind to an existing
/// family auto-inherits the correct behavior.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EmissionContext {
    /// Emitting arms for a rule's home category (e.g., BigInt's PrefixDispatch
    /// arms). The bare-polymorphic `TokenKind::Integer` arm IS emitted for
    /// non-primitive integer kinds (`CanonicalBigInt`); without it, bare
    /// unsuffixed integers route through cross-cat to Int via heuristics.
    HomeCategory,
    /// Emitting arms in another category's PrefixDispatch via cross-cat
    /// projection (e.g., Proc's `ProcBigInt` arm derived from FIRST(BigInt)).
    /// The bare-polymorphic arm is SUPPRESSED so primitive-integer cross-cat
    /// projections are not shadowed.
    CrossCatProjection,
    /// Computing a FIRST set that will be consumed by cross-cat-projection
    /// emission. Same suppression as `CrossCatProjection` to keep the FIRST
    /// set free of home-only arms.
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
    // FIRST sets are consumed by cross-cat projection emission and other
    // codegen paths that dispatch on tokens in OTHER categories' contexts.
    // Pass `EmissionContext::FirstSet` so home-only bare-polymorphic arms
    // (e.g., `CanonicalBigInt`'s bare-Integer arm) are excluded — including
    // them here would shadow primitive-integer cross-cat projections.
    collect_first_set(cat_name, language, &mut acc, &mut visited);
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
                    literal_patterned_pattern_and_guard_for_kind(cat_name, family, Some(&kind), ctx)
                {
                    acc.push(FirstToken { pattern, extra_guard });
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
    if let Some(_lang_type) = language.types.iter().find(|t| t.name.to_string() == cat_name) {
        // Has-user-var-rule check: if any user rule for this cat matches
        // NonTerminal(Var), don't add (the user rule covers it).
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
    if let Some(lang_type) = language.types.iter().find(|t| t.name.to_string() == cat_name) {
        if let Some(coll_kind) = lang_type.collection_kind.as_ref() {
            let open = match coll_kind {
                mettail_ast::language::CollectionCategory::List(d) => d.open.clone(),
                mettail_ast::language::CollectionCategory::Bag(d) => d.open.clone(),
                mettail_ast::language::CollectionCategory::Map(d) => d.open.clone(),
            };
            // Mirror synthetic.rs's split-on-trailing-`(` logic so the
            // FIRST token equals the lexer's first emitted Fixed token.
            let first_open = open.trim_end_matches('(').to_string();
            acc.push(FirstToken {
                pattern: quote! {
                    Some(mettail_prattail::automata::TokenKind::Fixed(__kw))
                },
                extra_guard: Some(quote! { __kw == #first_open }),
            });
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
                    literal_patterned_pattern_and_guard_for_kind(&c, family, Some(&nk), ctx)
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
                // Recurse into the source category's FIRST set. Option A
                // (per-cursor collection support in fanout) makes this
                // recursion unconditionally safe — F8's bucketed Fork
                // emission can now drive cursors through any FIRST token,
                // including transitive cross-cat tokens.
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

/// B7 Pattern 2: emit auto-grouping `(` arms in PrefixDispatch.
///
/// For every parseable category, emit:
/// ```text
/// Some(TokenKind::Fixed(__open)) if __open == "(" && state_cat_src_idx == #c_src => {
///     return WpdsStepAction::ConsumeAndPush {
///         symbol: StackSymbolV2::grouping_marker(#c_src, *cur_bp),
///         weight: LexicographicWeight::one(),
///         new_state: WpdsState::PrefixDispatch { pos: *pos + 1, cur_bp: 0 },
///         capture_token: false,
///     };
/// }
/// ```
///
/// Grouping is transparent: no AST node, no action, just a precedence
/// reset. The `GroupingMarker` (wpds_runtime.rs `SymbolKind::GroupingMarker`)
/// carries the saved outer `cur_bp` in its `bp` field; on `)` consumption
/// in the Unwinding-GroupingMarker arm, the engine resumes
/// `InfixLoop { cur_bp: marker.bp }`.
///
/// **Backend-uniform fix** per the user's no-per-grammar-order mandate:
/// every shipped grammar gains paren grouping without per-grammar work.
/// Conflict-safe: `(` only enters PrefixDispatch as a standalone token
/// when no in-flight collection consumes it (collection rules consume
/// their open delim's `(` via `WpdsState::CollectionOpenParen`, not
/// PrefixDispatch).
pub fn emit_grouping_arms(categories: &[String]) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, _cat_name) in categories.iter().enumerate() {
        let result_src_idx = cat_i as u16;
        arms.push(quote! {
            Some(mettail_prattail::automata::TokenKind::Fixed(__open))
                if __open == "(" && state_cat_src_idx == #result_src_idx => {
                return WpdsStepAction::ConsumeAndPush {
                    symbol: StackSymbolV2::grouping_marker(
                        #result_src_idx, *cur_bp,
                    ),
                    weight: LexicographicWeight::one(),
                    new_state: WpdsState::PrefixDispatch {
                        pos: *pos + 1,
                        cur_bp: 0,
                    },
                    capture_token: false,
                };
            }
        });
    }
    quote! { #(#arms)* }
}

/// Stage 3.20 / Commit 4 part 2 (Plan agent Fix, 2026-05-06): emit `(`-trigger
/// dispatch arms that handle BOTH the B7 paren-grouping AND any binder
/// rule whose first trigger is `"("`. For categories with no `(`-binder,
/// this degenerates to the simple grouping arm (byte-identical to
/// `emit_grouping_arms`). For categories like Lambda's `Term` that have
/// a paren-triggered App rule, this emits a `WpdsStepAction::Fork` over
/// {grouping_branch, binder_rule_branches...} so lex-min disambiguates
/// per `feedback_use_wpds_disambiguation_not_heuristics.md`. The grouping
/// branch uses `LexicographicWeight::one()` (max src/rule indices) so
/// any concrete binder rule beats it on lex-min ties.
///
/// Verified empirically across `target/generated/*/wpds.rs`: only Lambda
/// has a `(`-triggered binder rule; for all other shipped grammars the
/// emitted output is byte-identical to `emit_grouping_arms`.
pub fn emit_paren_dispatch_arms(
    categories: &[String],
    _language: &mettail_ast::language::LanguageDef,
    per_cat: &[Vec<mettail_ast::grammar::GrammarRule>],
) -> TokenStream {
    let mut arms = Vec::new();
    for (cat_i, _cat_name) in categories.iter().enumerate() {
        let result_src_idx = cat_i as u16;
        // Find binder rules in this category with `(` first trigger.
        let paren_binder_rules: Vec<(u16, super::binder::BinderShape)> = per_cat[cat_i]
            .iter()
            .enumerate()
            .filter_map(|(rule_i, rule)| {
                let shape = super::binder::classify_binder(rule)?;
                let first_trigger = rule.syntax_pattern.as_ref()?.first()?;
                match first_trigger {
                    mettail_ast::grammar::SyntaxExpr::Literal(text) if text == "(" => {
                        Some((rule_i as u16, shape))
                    }
                    _ => None,
                }
            })
            .collect();
        if paren_binder_rules.is_empty() {
            // No conflict: emit the simple grouping arm (byte-identical
            // to emit_grouping_arms).
            arms.push(quote! {
                Some(mettail_prattail::automata::TokenKind::Fixed(__open))
                    if __open == "(" && state_cat_src_idx == #result_src_idx => {
                    return WpdsStepAction::ConsumeAndPush {
                        symbol: StackSymbolV2::grouping_marker(
                            #result_src_idx, *cur_bp,
                        ),
                        weight: LexicographicWeight::one(),
                        new_state: WpdsState::PrefixDispatch {
                            pos: *pos + 1,
                            cur_bp: 0,
                        },
                        capture_token: false,
                    };
                }
            });
            continue;
        }
        // Fork over {grouping, binder_rule_branches...}. consume_trigger:
        // true → walker advances pos by 1 before allocating cursors.
        let mut branches: Vec<TokenStream> = Vec::new();
        // Branch 0: grouping. Uses one() (max src/rule via u16::MAX) so
        // any concrete binder rule beats it on lex-min ties.
        branches.push(quote! {
            mettail_prattail::wpds_walker::ForkBranch {
                symbol: StackSymbolV2::grouping_marker(
                    #result_src_idx, *cur_bp,
                ),
                weight: LexicographicWeight::one(),
                new_state: WpdsState::PrefixDispatch {
                    pos: *pos + 1,
                    cur_bp: 0,
                },
                action_kind: mettail_prattail::wpds_walker::ForkActionKind::Push,
            }
        });
        // Branches 1..N: each binder rule with `(` trigger.
        for (rule_idx, shape) in &paren_binder_rules {
            let body_src_idx = match &shape.body_cat {
                Some(name) => super::binder::lookup_src_idx(name, categories)
                    .unwrap_or(result_src_idx),
                None => result_src_idx,
            };
            let rule_idx_lit = *rule_idx;
            branches.push(quote! {
                mettail_prattail::wpds_walker::ForkBranch {
                    symbol: StackSymbolV2::rule_at(
                        #result_src_idx, #rule_idx_lit, 1u8, Some(_outer_bp),
                    ),
                    weight: LexicographicWeight::from_cost(
                        0.0, #result_src_idx, #rule_idx_lit,
                    ),
                    new_state: WpdsState::BinderRule {
                        result_src_idx: #result_src_idx,
                        rule_idx: #rule_idx_lit,
                        body_src_idx: #body_src_idx,
                        outer_bp: _outer_bp,
                    },
                    action_kind: mettail_prattail::wpds_walker::ForkActionKind::Push,
                }
            });
        }
        arms.push(quote! {
            Some(mettail_prattail::automata::TokenKind::Fixed(__open))
                if __open == "(" && state_cat_src_idx == #result_src_idx => {
                return WpdsStepAction::Fork {
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
    //     using LexicographicWeight::from_cost(0.0, category, src_idx) so
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
    let mut unified_buckets: std::collections::BTreeMap<
        (String, String),
        UnifiedBucket,
    > = std::collections::BTreeMap::new();
    let mut unified_order: Vec<(String, String)> = Vec::new();
    for source_cat_name in &sorted_sources {
        let source_src_idx = categories
            .iter()
            .position(|c| c == *source_cat_name)
            .map(|i| i as u16)
            .unwrap_or(0);
        let first_set = first_set_of_category(source_cat_name, language);
        for ft in first_set {
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
            entry.descs.push(UnifiedDescriptor::CrossCatLhs {
                source_src_idx,
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
    // reordering), so generated WPDS_RULES tables and stack-symbol payloads
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

    // B7 (2026-05-07): atomic-shape descriptors fold into the SAME
    // unified bucket map as cross-cat-LHS sources above. When a (pat,
    // guard) key appears in BOTH cross-cat-LHS and atomic, the bucket
    // emits a Fork mixing both branch kinds with the per-tier weights
    // documented above. When only one kind appears, emission is
    // byte-identical to pre-B7.
    let mut atomic_descriptors: Vec<PrefixArmDescriptor> = Vec::new();
    for &(rule_idx, rule) in rules_in_category {
        let shape = classify_atomic(rule, language);
        atomic_descriptors.extend(atomic_arm_descriptors(
            category_src_idx, rule_idx, &shape,
        ));
    }
    for desc in atomic_descriptors {
        let pat_str = desc.pattern.to_string();
        let guard_str = desc
            .extra_guard
            .as_ref()
            .map(|g| g.to_string())
            .unwrap_or_default();
        let key = (pat_str, guard_str);
        if !unified_buckets.contains_key(&key) {
            unified_order.push(key.clone());
        }
        let entry = unified_buckets.entry(key).or_insert_with(|| UnifiedBucket {
            pat: desc.pattern.clone(),
            extra_guard: desc.extra_guard.clone(),
            descs: Vec::new(),
        });
        entry.descs.push(UnifiedDescriptor::Atomic(desc));
    }
    for key in unified_order {
        let entry = unified_buckets.remove(&key).expect("bucket present in order");
        arms.push(emit_unified_arm(category_src_idx, &entry));
    }
    // Pass 2a: collect cross-cat projections, then emit bucket-then-Fork.
    // F8 (2026-04-28): replaces per-rule emission + IntSuffix runtime guard.
    let projections: Vec<(u16, String)> = rules_in_category
        .iter()
        .filter_map(|&(rule_idx, rule)| match classify_atomic(rule, language) {
            AtomicShape::CrossCatProjection { source_cat_name, .. } => {
                Some((rule_idx, source_cat_name))
            }
            _ => None,
        })
        .collect();
    if !projections.is_empty() {
        arms.push(emit_cross_cat_projection_arms_bucketed(
            category_src_idx,
            &projections,
            language,
        ));
    }
    // Pass 2b: cross-cat-prefix-unary arms (trigger-literal + delegation).
    // No shipped grammar shares a unary trigger across rules in the same
    // result category, so single-arm-per-rule emission is sufficient.
    for &(rule_idx, rule) in rules_in_category {
        if let AtomicShape::CrossCatPrefixUnary {
            trigger,
            source_cat_name,
            wrapper_variant: _,
        } = classify_atomic(rule, language)
        {
            let arm = emit_cross_cat_prefix_unary_arm(
                category_src_idx,
                rule_idx,
                &trigger,
                &source_cat_name,
                language,
            );
            arms.push(arm);
        }
    }
    quote! { #(#arms)* }
}

/// F8 (2026-04-28): emit cross-cat projection arms for ALL projections in
/// a result category, bucketed by `(pattern, extra_guard)`. Single-projection
/// buckets emit `Push` arms; multi-projection buckets emit
/// `WpdsStepAction::Fork` with one branch per projection. Lex-min over
/// `from_cost(0.0, category_src, rule_idx)` picks the surviving branch
/// (preserves source-order tiebreak).
///
/// Replaces the pre-F8 per-rule emission + `IntSuffix::from_text` runtime
/// guard heuristic. Post-B11, `EmissionContext::FirstSet` excludes
/// bare-Integer arms, so the IntSuffix guard was dead code; remaining
/// ambiguity from category-bound FIRST tokens shared via transitive FIRST
/// chains (e.g., Calculator's `IntToBigInt` cross-cat puts `IntegerLit("Int")`
/// in BigInt's FIRST, shared by `Proc::ProcInt` and `Proc::ProcBigInt`) is
/// resolved by Fork + lex-min — the principled WPDS mechanism.
fn emit_cross_cat_projection_arms_bucketed(
    category_src_idx: u16,
    projections: &[(u16, String)],
    language: &LanguageDef,
) -> TokenStream {
    use std::collections::BTreeMap;

    struct ProjectionBranch {
        rule_idx: u16,
        source_src_idx: u16,
    }
    struct BucketEntry {
        pat: TokenStream,
        extra_guard: Option<TokenStream>,
        branches: Vec<ProjectionBranch>,
    }

    let categories = super::collect_category_names_with_literals(language);
    // Bucket key = (stringified pattern, stringified extra_guard).
    // Two projections with same pat AND same guard go into one bucket
    // (Fork). Same pat with different guards are mutually exclusive at
    // runtime (e.g., `__cat == "Int"` vs `__cat == "BigInt"`) → separate
    // buckets, first-match-wins is correct semantics.
    //
    // Option A (per-cursor collection support, 2026-04-28): the walker
    // can now drive cursors through any FIRST token, including transitive
    // cross-cat tokens that lead to collection-opening in the source
    // category. Fork emission applies uniformly — no `via_cross_cat`
    // filter needed.
    let mut buckets: BTreeMap<(String, String), BucketEntry> = BTreeMap::new();
    for (rule_idx, source_cat_name) in projections {
        let source_src_idx = categories
            .iter()
            .position(|c| c == source_cat_name)
            .map(|i| i as u16)
            .unwrap_or(0);
        for ft in first_set_of_category(source_cat_name, language) {
            let pat_str = ft.pattern.to_string();
            let guard_str = ft
                .extra_guard
                .as_ref()
                .map(|g| g.to_string())
                .unwrap_or_default();
            let key = (pat_str, guard_str);
            let entry = buckets.entry(key).or_insert_with(|| BucketEntry {
                pat: ft.pattern.clone(),
                extra_guard: ft.extra_guard.clone(),
                branches: Vec::new(),
            });
            entry.branches.push(ProjectionBranch {
                rule_idx: *rule_idx,
                source_src_idx,
            });
        }
    }

    let mut arms = Vec::new();
    for (_key, entry) in buckets {
        let pat = entry.pat;
        let guard = match &entry.extra_guard {
            Some(eg) => quote! { #eg && state_cat_src_idx == #category_src_idx },
            None => quote! { state_cat_src_idx == #category_src_idx },
        };
        if entry.branches.len() == 1 {
            // Single-projection bucket: emit Push directly.
            let b = &entry.branches[0];
            let rule_idx = b.rule_idx;
            let source_src_idx = b.source_src_idx;
            arms.push(quote! {
                #pat if #guard => {
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
        } else {
            // Multi-projection bucket: emit Fork over all candidates.
            // `consume_trigger: false` because the FIRST token belongs to
            // the source-category sub-parse (CrossCatDelegate dispatches
            // into source's PrefixDispatch, which consumes the token).
            let branches: Vec<TokenStream> = entry
                .branches
                .iter()
                .map(|b| {
                    let rule_idx = b.rule_idx;
                    let source_src_idx = b.source_src_idx;
                    quote! {
                        mettail_prattail::wpds_walker::ForkBranch {
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
                            // Stage 3.12 / Class A.i (2026-05-01): default Push.
                            action_kind: mettail_prattail::wpds_walker::ForkActionKind::Push,
                        }
                    }
                })
                .collect();
            arms.push(quote! {
                #pat if #guard => {
                    return WpdsStepAction::Fork {
                        branches: vec![ #( #branches ),* ],
                        consume_trigger: false,
                    };
                }
            });
        }
    }
    quote! { #(#arms)* }
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
/// Stage 3.16 / Hack #8 (Cluster 2, Mechanism γ, 2026-05-05) — descriptor
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

/// Stage 3.16 / Hack #8 (Cluster 2, Mechanism γ, 2026-05-05) — extracted
/// pattern/guard pairs for an atomic shape. Replaces the eager TokenStream
/// emission in `emit_atomic_arms` so the caller can bucket by (pat, guard)
/// before emitting either a singleton arm or a Fork.
fn atomic_arm_descriptors(
    category_src_idx: u16,
    rule_idx: u16,
    shape: &AtomicShape,
) -> Vec<PrefixArmDescriptor> {
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
            literal_patterned_pattern_and_guard_for_kind(
                cat_name,
                *family,
                Some(&nk),
                EmissionContext::HomeCategory,
            )
        }
        AtomicShape::TerminalKeyword { terminal_text, .. } => vec![(
            quote! { Some(mettail_prattail::automata::TokenKind::Fixed(__kw)) },
            Some(quote! { __kw == #terminal_text }),
        )],
        AtomicShape::VarRule { .. } => vec![(
            quote! { Some(mettail_prattail::automata::TokenKind::Ident) },
            None,
        )],
        AtomicShape::CrossCatProjection { .. } | AtomicShape::CrossCatPrefixUnary { .. } => {
            return Vec::new()
        }
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
enum UnifiedDescriptor {
    /// Cross-cat infix LHS delegation arm — pushes
    /// `CategoryEntry(source_src_idx)` so the LHS sub-parses against
    /// the source category before InfixLoop sees the cross-cat operator.
    /// Per-tier weight: `BP_TIER_CROSSCAT_LHS = 0.05`.
    CrossCatLhs { source_src_idx: u16 },
    /// Atomic-shape arm — `ConsumeAndPush(rule_at(...).Return)` for a
    /// home-category leaf rule (literal, var, terminal-keyword, etc.).
    /// Per-tier weight: `0.0` (atomic-home).
    Atomic(PrefixArmDescriptor),
}

/// B7 (2026-05-07) — unified bucket entry. Replaces the separate
/// LhsBucketEntry (Pass 0) and atomic bucket map (Pass 1).
struct UnifiedBucket {
    pat: TokenStream,
    extra_guard: Option<TokenStream>,
    descs: Vec<UnifiedDescriptor>,
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
fn emit_unified_arm(category_src_idx: u16, bucket: &UnifiedBucket) -> TokenStream {
    let pat = &bucket.pat;
    let guard = match &bucket.extra_guard {
        Some(eg) => quote! { #eg && state_cat_src_idx == #category_src_idx },
        None => quote! { state_cat_src_idx == #category_src_idx },
    };
    if bucket.descs.len() == 1 {
        match &bucket.descs[0] {
            UnifiedDescriptor::CrossCatLhs { source_src_idx } => {
                let source_src_idx = *source_src_idx;
                quote! {
                    #pat if #guard => {
                        return WpdsStepAction::Push {
                            symbol: StackSymbolV2::category_entry(#source_src_idx),
                            weight: LexicographicWeight::one(),
                            new_state: WpdsState::PrefixDispatch {
                                pos: *pos,
                                cur_bp: *cur_bp,
                            },
                        };
                    }
                }
            }
            UnifiedDescriptor::Atomic(desc) => emit_atomic_arm_singleton(desc),
        }
    } else {
        let branches: Vec<TokenStream> = bucket
            .descs
            .iter()
            .map(|d| match d {
                UnifiedDescriptor::CrossCatLhs { source_src_idx } => {
                    let src_idx = *source_src_idx;
                    quote! {
                        mettail_prattail::wpds_walker::ForkBranch {
                            symbol: StackSymbolV2::category_entry(#src_idx),
                            weight: LexicographicWeight::from_cost(
                                mettail_prattail::automata::lex_weight::BP_TIER_CROSSCAT_LHS,
                                #category_src_idx, #src_idx,
                            ),
                            new_state: WpdsState::PrefixDispatch {
                                pos: *pos,
                                cur_bp: *cur_bp,
                            },
                            action_kind: mettail_prattail::wpds_walker::ForkActionKind::Push,
                        }
                    }
                }
                UnifiedDescriptor::Atomic(desc) => {
                    let rule_idx = desc.rule_idx;
                    let csi = desc.category_src_idx;
                    quote! {
                        mettail_prattail::wpds_walker::ForkBranch {
                            symbol: StackSymbolV2::rule_at(
                                #csi, #rule_idx, 0, Some(_outer_bp),
                            ).with_kind_return(),
                            weight: LexicographicWeight::from_cost(
                                0.0, #csi, #rule_idx,
                            ),
                            new_state: WpdsState::Unwinding,
                            action_kind: mettail_prattail::wpds_walker::ForkActionKind::ConsumeAndCaptureAndPush,
                        }
                    }
                }
            })
            .collect();
        quote! {
            #pat if #guard => {
                return WpdsStepAction::Fork {
                    branches: vec![ #( #branches ),* ],
                    consume_trigger: false,
                };
            }
        }
    }
}

/// Emit a singleton atomic arm — byte-identical to the pre-Hack-#8 emission.
fn emit_atomic_arm_singleton(desc: &PrefixArmDescriptor) -> TokenStream {
    let pat = &desc.pattern;
    let category_src_idx = desc.category_src_idx;
    let rule_idx = desc.rule_idx;
    let guard = match &desc.extra_guard {
        Some(eg) => quote! { #eg && state_cat_src_idx == #category_src_idx },
        None => quote! { state_cat_src_idx == #category_src_idx },
    };
    quote! {
        #pat if #guard => {
            return WpdsStepAction::ConsumeAndPush {
                symbol: StackSymbolV2::rule_at(
                    #category_src_idx, #rule_idx, 0, Some(_outer_bp),
                ).with_kind_return(),
                weight: LexicographicWeight::from_cost(0.0, #category_src_idx, #rule_idx),
                new_state: WpdsState::Unwinding,
                capture_token: true,
            };
        }
    }
}

/// Emit a multi-arm bucket as a Fork over the per-rule branches. Triggers
/// only when ≥2 rules share the same `(pat, guard)` key — for shipped
/// grammars this branch is unreachable; for G5 future grammars it emits
/// principled lex-min disambiguation.
fn emit_atomic_arm_fork(descs: &[PrefixArmDescriptor]) -> TokenStream {
    debug_assert!(descs.len() >= 2);
    let category_src_idx = descs[0].category_src_idx;
    let pat = &descs[0].pattern;
    let guard = match &descs[0].extra_guard {
        Some(eg) => quote! { #eg && state_cat_src_idx == #category_src_idx },
        None => quote! { state_cat_src_idx == #category_src_idx },
    };
    let branches: Vec<TokenStream> = descs.iter().map(|d| {
        let rule_idx = d.rule_idx;
        let csi = d.category_src_idx;
        quote! {
            mettail_prattail::wpds_walker::ForkBranch {
                symbol: StackSymbolV2::rule_at(
                    #csi, #rule_idx, 0, Some(_outer_bp),
                ).with_kind_return(),
                weight: LexicographicWeight::from_cost(0.0, #csi, #rule_idx),
                new_state: WpdsState::Unwinding,
                action_kind: mettail_prattail::wpds_walker::ForkActionKind::ConsumeAndCaptureAndPush,
            }
        }
    }).collect();
    quote! {
        #pat if #guard => {
            return WpdsStepAction::Fork {
                branches: vec![ #( #branches ),* ],
                consume_trigger: false,
            };
        }
    }
}

#[allow(dead_code)]
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
            // emit_atomic_arms is invoked exclusively from
            // emit_prefix_arms_for_category for the rule's HOME category, so
            // pass `EmissionContext::HomeCategory`. CanonicalBigInt picks up
            // the bare-Integer arm here so unsuffixed integers in BigInt's
            // own PrefixDispatch resolve directly to BigInt's NumLit.
            literal_patterned_pattern_and_guard_for_kind(
                cat_name,
                *family,
                Some(&nk),
                EmissionContext::HomeCategory,
            )
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
            // HomeCategory context; in CrossCatProjection / FirstSet
            // contexts emitted only for primitive-integer widths so
            // `CanonicalBigInt` doesn't shadow primitive-integer cross-cat
            // projections (see fn doc above).
            let emit_bare_arm = match ctx {
                EmissionContext::HomeCategory => {
                    home_polymorphic_token_arm(family).is_some()
                }
                EmissionContext::CrossCatProjection | EmissionContext::FirstSet => {
                    matches!(
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
                    )
                }
            };
            if emit_bare_arm {
                if let Some(pat) = home_polymorphic_token_arm(family) {
                    arms.push((pat, None));
                }
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
        LiteralFamily::Float => vec![(
            quote! { Some(mettail_prattail::automata::TokenKind::Float) },
            None,
        )],
        LiteralFamily::Boolean => vec![(
            quote! {
                Some(mettail_prattail::automata::TokenKind::True)
                | Some(mettail_prattail::automata::TokenKind::False)
                | Some(mettail_prattail::automata::TokenKind::BooleanLit)
            },
            None,
        )],
        LiteralFamily::String => vec![(
            quote! { Some(mettail_prattail::automata::TokenKind::StringLit) },
            None,
        )],
    }
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
            is_auto_injected: false,
            doc_comment: None,
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
            is_auto_injected: false,
            doc_comment: None,
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
            is_auto_injected: false,
            doc_comment: None,
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
        let rule = GrammarRule {
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
            is_auto_injected: false,
            doc_comment: None,
        };
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
