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
use mettail_ast::language::{LanguageDef, NativeKind, NativeKindFromSynType};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{Ident, Type};

/// Lexer token family for a literal-patterned rule.
pub use mettail_prattail::wpda_rule_analysis::native_first::LiteralFamily;

/// B11 fix: classifies the calling context that drives literal-pattern arm
/// emission. The Integer family's bare-polymorphic `TokenKind::Integer` arm
/// is gated on this — present in `HomeCategory` (so a bare unsuffixed integer
/// in BigInt's own PrefixDispatch resolves directly to BigInt's NumLit),
/// suppressed in `FirstSet` (so primitive-integer cross-cat projections like
/// `ProcInt`/`ProcUInt32` aren't shadowed when the FIRST set of `BigInt` is
/// consumed by other categories' cross-cat dispatch). Generalizes uniformly via
/// `home_polymorphic_token_arm(family)` — adding a new kind to an existing
/// family auto-inherits the correct behavior.
pub use mettail_prattail::wpda_rule_analysis::native_first::EmissionContext;

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
#[cfg(test)]
fn home_polymorphic_token_arm(family: LiteralFamily) -> Option<TokenStream> {
    mettail_prattail::wpda_rule_analysis::native_first::home_polymorphic_token_arm(
        family,
        &mut MacroNativeFirstConstructors,
    )
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
    /// `Literal`s with NO `Param`/`Op` (e.g. Rholang's
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
    /// `ProcInt . i:Int |- i : Proc`, Rholang's `CastBigRat . r:BigRat |- r : Proc`).
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
/// rules (`term_context` + `syntax_pattern`), since Calculator / Rholang
/// use exclusively judgement-style.
fn classify_atomic_descriptor(
    rule: &GrammarRule,
    language: &LanguageDef,
) -> mettail_prattail::wpda_rule_analysis::atomic::AtomicDescriptor<AtomicShape> {
    use mettail_prattail::wpda_rule_analysis::atomic::{
        classify_atomic as classify_shared_atomic, AtomicUnaryPrefix,
    };
    use mettail_prattail::wpda_rule_analysis::atomic_projection::{
        project_legacy_atomic_items, LegacyAtomicObservation,
    };

    let view = super::infix::project_infix_rule(rule);
    let items = project_legacy_atomic_items(&rule.items, |item| match item {
        GrammarItem::NonTerminal { kind, ident } => {
            LegacyAtomicObservation::NonTerminal { kind: *kind, ident }
        },
        GrammarItem::Terminal(text) => LegacyAtomicObservation::Terminal(text),
        _ => LegacyAtomicObservation::Other,
    });
    classify_shared_atomic(
        &view,
        &items,
        || {
            super::builtin_metadata::classify_unary_prefix_shape(rule).map(|shape| {
                AtomicUnaryPrefix {
                    trigger: shape.trigger,
                    operand_category: shape.operand_category,
                }
            })
        },
        |_| {
            // Preserve the original identifier object and resolver. The shared
            // classifier calls this only for this exact singleton Category item.
            let [GrammarItem::NonTerminal { ident, kind: NonTerminalKind::Category }] =
                rule.items.as_slice()
            else {
                unreachable!("shared atomic classifier only resolves singleton Category items");
            };
            classify_literal_patterned(ident, language)
        },
    )
}

pub fn classify_atomic(rule: &GrammarRule, language: &LanguageDef) -> AtomicShape {
    use mettail_prattail::wpda_rule_analysis::atomic::AtomicDescriptor;
    let descriptor = classify_atomic_descriptor(rule, language);
    match descriptor {
        AtomicDescriptor::LiteralInteger => AtomicShape::LiteralInteger,
        AtomicDescriptor::LiteralBoolean => AtomicShape::LiteralBoolean,
        AtomicDescriptor::LiteralString => AtomicShape::LiteralString,
        AtomicDescriptor::LiteralFloat => AtomicShape::LiteralFloat,
        AtomicDescriptor::LiteralPatterned(payload) => payload,
        AtomicDescriptor::TerminalKeyword { terminal_text, .. } => AtomicShape::TerminalKeyword {
            terminal_text,
            wrapper_variant: rule.label.clone(),
        },
        AtomicDescriptor::NullaryLiteralRun { trigger, trailing_literals, .. } => {
            AtomicShape::NullaryLiteralRun {
                trigger,
                trailing_literals,
                wrapper_variant: rule.label.clone(),
            }
        },
        AtomicDescriptor::VarRule { .. } => {
            AtomicShape::VarRule { wrapper_variant: rule.label.clone() }
        },
        AtomicDescriptor::CrossCatProjection { source_cat_name, .. } => {
            AtomicShape::CrossCatProjection {
                source_cat_name,
                wrapper_variant: rule.label.clone(),
            }
        },
        AtomicDescriptor::CrossCatPrefixUnary { trigger, source_cat_name, .. } => {
            AtomicShape::CrossCatPrefixUnary {
                trigger,
                source_cat_name,
                wrapper_variant: rule.label.clone(),
            }
        },
        AtomicDescriptor::PrefixOperator { trigger, operand_cat_name } => {
            AtomicShape::PrefixOperator { trigger, operand_cat_name }
        },
        AtomicDescriptor::NonAtomic => AtomicShape::NonAtomic,
    }
}

/// Look up the TokenDef + LangType for a category and package them into a
/// `LiteralPatterned` shape.
///
/// Two paths produce a valid shape:
///
/// * **(a) Explicit `literals { ... }` block** — a `from_literals: true` TokenDef carries the
///   user's `eval: ![ { ... } ]` block body in `rust_code`.
/// * **(b) Implicit native-type** — `LangType.native_type` is `Some(_)` but there is no explicit
///   literals block. We fabricate a default eval body matching the trampoline's auto-generated
///   atomic-literal arm: for `![i32] as Num` we emit `parse_int_lit(text, Some(Suffix::I32))`.
///
/// ⚠ This paragraph used to describe a `Token::Integer(v, suffix) if suffix.matches_i32()` guard.
/// `IntSuffix::matches_*` was retired in 2026-07 with zero callers — divergence I, Stage E: a
/// documented-but-unread guard family is what made a universal-acceptor `eval` look guarded. A
/// category's literal domain is decided by its own `eval`.
///
/// ⚠ FORMATTING, and why it is load-bearing here. The paragraph above was previously written as
/// an INDENTED continuation after a blank `///` line. Markdown reads a blank line followed by a
/// ≥4-space indent as a CODE BLOCK, and rustdoc compiles an unannotated code block as Rust — so
/// `cargo test --doc` tried to compile English prose and failed with eleven parse errors, while
/// `cargo nextest` (which does not run doctests) stayed green. Keep prose at the left margin, and
/// use a real markdown list for enumerations rather than hanging indentation.
fn classify_literal_patterned(cat_ident: &Ident, language: &LanguageDef) -> Option<AtomicShape> {
    let result =
        mettail_prattail::wpda_rule_analysis::native_literal::try_classify_literal_patterned(
            cat_ident,
            &mut MacroLiteralReader { language },
        );
    match result {
        Ok(payload) => payload.map(|payload| AtomicShape::LiteralPatterned {
            cat_name: payload.cat_name,
            native_type: payload.native_type,
            family: payload.family,
            wrapper_variant: payload.wrapper_variant,
            rust_code: payload.evaluation,
        }),
        Err(never) => match never {},
    }
}

struct MacroLiteralReader<'source> {
    language: &'source LanguageDef,
}

impl<'source> mettail_prattail::wpda_rule_analysis::native_literal::LiteralPatternedReader<'source>
    for MacroLiteralReader<'source>
{
    type Name = &'source Ident;
    type Category = mettail_ast::language::LangType;
    type Native = Type;
    type Label = Ident;
    type Evaluation = TokenStream;
    type Token = &'source mettail_ast::language::TokenDef;
    type Error = std::convert::Infallible;
    fn categories(&self) -> &'source [Self::Category] {
        &self.language.types
    }
    fn category_name(&self, category: &'source Self::Category) -> Self::Name {
        &category.name
    }
    fn names_equal(&self, left: Self::Name, right: Self::Name) -> bool {
        left == right
    }
    fn native_type(&self, category: &'source Self::Category) -> Option<Type> {
        category.native_type.as_ref().cloned()
    }
    fn native_kind(&self, native: &Type) -> NativeKind {
        NativeKind::from_syn_type(native)
    }
    fn literal_family(&self, category: &str) -> Option<LiteralFamily> {
        literal_family_for_category(category, self.language)
    }
    fn literal_label(&mut self, native: &Type) -> Result<Ident, Self::Error> {
        Ok(crate::gen::generate_literal_label(native))
    }
    fn declared_token(&self, category: &str) -> Option<Self::Token> {
        declared_literal_token_def(category, self.language)
    }
    fn evaluation(&self, token: Self::Token) -> Option<TokenStream> {
        token.rust_code.clone()
    }
    fn default_evaluation(&self, kind: &NativeKind) -> Option<TokenStream> {
        default_eval_body_for_native_kind(kind)
    }
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
            mettail_prattail::decode_double_quoted_string_literal(text).map_err(|_| ())
        },
        NativeKind::Other => return None,
    };
    Some(body)
}

/// Stage 1.1: a token in a category's FIRST set, emitted as a `TokenKind`
/// pattern fragment for use in a Rust match arm.
pub type FirstToken = mettail_prattail::wpda_rule_analysis::prefix::FirstToken<TokenStream>;

struct MacroFirstSetContext<'source> {
    language: &'source LanguageDef,
}

impl<'source>
    mettail_prattail::wpda_rule_analysis::prefix::FirstSetContext<
        'source,
        super::binder::MacroBinderSyntaxReader,
    > for MacroFirstSetContext<'source>
{
    type Category = &'source mettail_ast::language::LangType;
    type Literal = AtomicShape;
    type Pattern = TokenStream;

    fn rules_len(&self) -> usize {
        self.language.terms.len()
    }

    fn rule_at(&self, index: usize) -> &'source GrammarRule {
        &self.language.terms[index]
    }

    fn find_category(&mut self, name: &str) -> Option<Self::Category> {
        self.language
            .types
            .iter()
            .find(|ty| ty.name.to_string() == name)
    }

    fn is_data(&self, category: Self::Category) -> bool {
        category.is_data()
    }

    fn collection_open(&self, category: Self::Category) -> Option<&'source str> {
        category
            .collection_kind
            .as_ref()
            .map(|kind| kind.delimiters().open.as_str())
    }

    fn legacy_first(
        &self,
        rule: &'source GrammarRule,
    ) -> Option<
        mettail_prattail::wpda_rule_analysis::prefix::FirstLegacyItem<'source, &'source Ident>,
    > {
        use mettail_prattail::wpda_rule_analysis::prefix::FirstLegacyItem;
        rule.items.first().map(|item| match item {
            GrammarItem::Terminal(text) => FirstLegacyItem::Terminal(text),
            GrammarItem::NonTerminal { kind, ident } => {
                FirstLegacyItem::NonTerminal { kind: *kind, name: ident }
            },
            _ => FirstLegacyItem::Other,
        })
    }

    fn native_first(
        &mut self,
        lang_type: Self::Category,
        current_cat_name: &str,
    ) -> Vec<(TokenStream, Option<TokenStream>)> {
        if let Some(nt) = lang_type.native_type.as_ref() {
            let kind = NativeKind::from_syn_type(nt);
            // Keep the original category-aware family election, including its
            // declared Custom literal branch and internal source lookup.
            if let Some(family) = literal_family_for_category(current_cat_name, self.language) {
                return literal_patterned_pattern_and_guard_for_kind(
                    current_cat_name,
                    family,
                    Some(&kind),
                    EmissionContext::FirstSet,
                );
            }
        }
        Vec::new()
    }

    fn atomic(
        &mut self,
        rule: &'source GrammarRule,
    ) -> mettail_prattail::wpda_rule_analysis::atomic::AtomicDescriptor<AtomicShape> {
        classify_atomic_descriptor(rule, self.language)
    }

    fn patterned_first(&mut self, literal: AtomicShape) -> Vec<(TokenStream, Option<TokenStream>)> {
        let AtomicShape::LiteralPatterned { cat_name, family, native_type, .. } = literal else {
            unreachable!("original literal resolver returns only LiteralPatterned payloads");
        };
        let nk = NativeKind::from_syn_type(&native_type);
        literal_patterned_pattern_and_guard_for_kind(
            &cat_name,
            family,
            Some(&nk),
            EmissionContext::FirstSet,
        )
    }

    fn binder_leading(&mut self, rule: &'source GrammarRule) -> Option<String> {
        super::binder::classify_binder_in(rule, self.language)
            .and_then(|shape| shape.leading_category)
    }

    fn predicate_parts(
        &mut self,
        predicate: mettail_prattail::wpda_rule_analysis::prefix::FirstPredicate<'_>,
    ) -> (TokenStream, Option<TokenStream>) {
        first_predicate_parts(predicate)
    }
}

/// Original quotation sites shared by FIRST and atomic-row adapters.
fn first_predicate_parts(
    predicate: mettail_prattail::wpda_rule_analysis::prefix::FirstPredicate<'_>,
) -> (TokenStream, Option<TokenStream>) {
    use mettail_prattail::wpda_rule_analysis::prefix::FirstPredicate;
    match predicate {
        FirstPredicate::Fixed(sigil) => (
            quote! { Some(mettail_prattail::automata::TokenKind::Fixed(__kw)) },
            Some(quote! { __kw == #sigil }),
        ),
        FirstPredicate::Ident => {
            (quote! { Some(mettail_prattail::automata::TokenKind::Ident) }, None)
        },
        FirstPredicate::Integer => {
            (quote! { Some(mettail_prattail::automata::TokenKind::Integer) }, None)
        },
        FirstPredicate::Boolean => (
            quote! {
                Some(mettail_prattail::automata::TokenKind::True)
                | Some(mettail_prattail::automata::TokenKind::False)
                | Some(mettail_prattail::automata::TokenKind::BooleanLit)
            },
            None,
        ),
        FirstPredicate::String => {
            (quote! { Some(mettail_prattail::automata::TokenKind::StringLit) }, None)
        },
        FirstPredicate::Float => {
            (quote! { Some(mettail_prattail::automata::TokenKind::Float) }, None)
        },
        FirstPredicate::CaptureName(kind_name) => (
            quote! { Some(ref __kind) },
            Some(quote! {
                mettail_prattail::automata::token_kind_matches_capture_name(
                    #kind_name,
                    __kind,
                )
            }),
        ),
        FirstPredicate::GuestOpen(open_kind) => (
            quote! { Some(mettail_prattail::automata::TokenKind::Custom(ref __k)) },
            Some(quote! { __k == #open_kind }),
        ),
    }
}

impl<'source>
    mettail_prattail::wpda_rule_analysis::prefix::IdentSummaryContext<
        'source,
        super::binder::MacroBinderSyntaxReader,
    > for MacroFirstSetContext<'source>
{
    fn categories_len(&self) -> usize {
        self.language.types.len()
    }

    fn category_at(&self, index: usize) -> Self::Category {
        &self.language.types[index]
    }

    fn category_spelling(&self, category: Self::Category) -> String {
        category.name.to_string()
    }

    fn legacy_len(&self, rule: &'source GrammarRule) -> usize {
        rule.items.len()
    }

    fn legacy_at(
        &self,
        rule: &'source GrammarRule,
        index: usize,
    ) -> Option<
        mettail_prattail::wpda_rule_analysis::prefix::FirstLegacyItem<'source, &'source Ident>,
    > {
        use mettail_prattail::wpda_rule_analysis::prefix::FirstLegacyItem;
        rule.items.get(index).map(|item| match item {
            GrammarItem::Terminal(text) => FirstLegacyItem::Terminal(text),
            GrammarItem::NonTerminal { kind, ident } => {
                FirstLegacyItem::NonTerminal { kind: *kind, name: ident }
            },
            _ => FirstLegacyItem::Other,
        })
    }
}

impl<'source>
    mettail_prattail::wpda_rule_analysis::prefix_bucket::PrefixBucketContext<
        'source,
        super::binder::MacroBinderSyntaxReader,
    > for MacroFirstSetContext<'source>
{
    fn infix(
        &mut self,
        rule: &'source GrammarRule,
    ) -> Option<mettail_prattail::binding_power::InfixRuleInfo> {
        super::infix::classify_rule_public(rule)
    }

    fn category_names(&mut self) -> Vec<String> {
        super::collect_category_names_with_literals(self.language)
    }

    fn binding_power_table(&mut self) -> mettail_prattail::binding_power::BindingPowerTable {
        super::infix::build_bp_table(self.language)
    }

    fn explicit_prefix_bp(&self, rule: &'source GrammarRule) -> Option<u8> {
        rule.prefix_bp
    }

    fn binder_shape(&mut self, rule: &'source GrammarRule) -> Option<super::binder::BinderShape> {
        super::binder::classify_binder_in(rule, self.language)
    }

    fn atomic_rows(
        &mut self,
        category_src_idx: u16,
        rule_idx: u16,
        shape: &mettail_prattail::wpda_rule_analysis::atomic::AtomicDescriptor<AtomicShape>,
    ) -> Vec<PrefixArmDescriptor> {
        atomic_arm_descriptors(category_src_idx, rule_idx, shape)
    }

    fn nested_guest_openers(&mut self, open: &str) -> Vec<String> {
        super::guest_body_nested_open_kinds(self.language, open)
    }
}

/// Direct leading literals through the original shared worker. Present syntax
/// suppresses legacy fallback even when empty or not literal-led.
#[cfg(test)]
fn category_leading_literals(
    cat_name: &str,
    language: &LanguageDef,
) -> std::collections::BTreeSet<String> {
    mettail_prattail::wpda_rule_analysis::prefix::category_leading_literals(
        cat_name,
        &super::binder::MacroBinderSyntaxReader,
        &MacroFirstSetContext { language },
    )
}

/// Compute the original FIRST descriptor rows through the shared FIFO worker.
/// Native helper policy and token quotation remain in the source adapter.
pub fn first_set_of_category(cat_name: &str, language: &LanguageDef) -> Vec<FirstToken> {
    mettail_prattail::wpda_rule_analysis::prefix::first_set_of_category(
        cat_name,
        &super::binder::MacroBinderSyntaxReader,
        &mut MacroFirstSetContext { language },
    )
}

/// Cross-category INFIX-operand hop for a result category `R`: the categories
/// `S` such that a cross-category infix rule `S op S' : R` exists (the grouped
/// `S` becomes the infix's left operand, e.g. `EqInt: Int "==" Int : Bool` ⇒
/// `Int` is an infix-hop source of `Bool`). Excludes `R`. This is the edge type
/// that REQUIRES the grouped operand to open as `S` (a bare `S` could not become
/// the infix's operand of a DIFFERENT category). The shared driver retains the
/// original bounded schedule rather than computing a transitive closure.
#[cfg(test)]
fn grouping_source_infix_hop(
    categories: &[String],
    language: &mettail_ast::language::LanguageDef,
    result_idx: usize,
    out: &mut std::collections::BTreeSet<u16>,
) {
    mettail_prattail::wpda_rule_analysis::grouping::grouping_source_infix_hop(
        categories,
        &language.terms,
        result_idx,
        out,
        &mut |rule| rule.category.to_string(),
        &mut super::infix::classify_rule_public,
    );
}

/// Cross-category PROJECTION hop for a result category `R`: the categories `S`
/// such that a cross-category projection / cast `S : R` exists (e.g.
/// `BoolToUInt32: Bool : UInt32` ⇒ `Bool` is a projection-hop source of
/// `UInt32`). Excludes `R`. A projection means a bare `S` ALREADY IS an `R`
/// (the cast fires transparently), so a grouped `(S)` grows into `R` directly —
/// this edge is included only at the FIRST closure level and NOT compounded
/// transitively, which would otherwise pull the entire cast lattice into every
/// group-open (e.g. rholang `Proc` has `CastX : Proc` for ~15 numeric/collection
/// `X`, and chaining their projections back through each other's casts explodes
/// the group-open fan-out → deep-paren fork blow-up). One infix hop is still
/// followed FROM these first-level sources below the hub threshold, which is
/// what M4 needs (`UInt32 →proj→ Bool →infix→ Int`).
#[cfg(test)]
fn grouping_source_projection_hop(
    language: &mettail_ast::language::LanguageDef,
    per_cat: &[Vec<mettail_ast::grammar::GrammarRule>],
    categories: &[String],
    result_idx: usize,
    out: &mut std::collections::BTreeSet<u16>,
) {
    mettail_prattail::wpda_rule_analysis::grouping::grouping_source_projection_hop(
        per_cat,
        categories,
        result_idx,
        out,
        &mut |rule| match classify_atomic(rule, language) {
            AtomicShape::CrossCatProjection { source_cat_name, .. } => Some(source_cat_name),
            _ => None,
        },
    );
}

/// The categories a `(`-group may open as when the enclosing requested category
/// is `result_idx` — the original bounded two-level derivation shared through
/// `mettail_prattail::wpda_rule_analysis::grouping`.
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
/// BOUND (perf): one INFIX-operand hop is taken from each first-level projection
/// source only below the four-source hub threshold. It includes PROJECTION
/// sources only at the FIRST level (level 0 = `result_idx`), NOT compounding them
/// through further projections. Rationale: a projection `X : R` means a bare `X`
/// already IS an `R`, so a grouped `(X)` grows into `R` directly — chaining
/// projection→projection pulls the ENTIRE cast lattice into every group-open
/// (rholang `Proc` has `CastX : Proc` for ~15 `X`; compounding blew Proc's `(`
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
    mettail_prattail::wpda_rule_analysis::grouping::grouping_source_categories_for_result(
        categories,
        &language.terms,
        per_cat,
        result_idx,
        |rule| rule.category.to_string(),
        super::infix::classify_rule_public,
        |rule| match classify_atomic(rule, language) {
            AtomicShape::CrossCatProjection { source_cat_name, .. } => Some(source_cat_name),
            _ => None,
        },
    )
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
/// A source category's concrete `(`-led rules are preserved when that source
/// is entered through a cross-category infix/projection edge.  Treating the
/// source merely as a grouping target is incomplete: it would consume the
/// opener and then parse only the text *inside* the parentheses, making an
/// S-expression-style source rule unreachable from the enclosing category.
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
        // Find binder rules owned by this result category with `(` first
        // trigger.  This local set controls the historical PInputs gate below;
        // source-category rules are collected after that gate has selected the
        // admissible grouping sources.
        let local_paren_binder_rules: Vec<(u16, super::binder::BinderShape)> = per_cat[cat_i]
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
        if local_paren_binder_rules.is_empty() && grouping_source_indices.len() == 1 {
            // No conflict: emit the simple grouping arm.
            let grouping_src_idx = grouping_source_indices[0];
            arms.push(quote! {
                Some(mettail_prattail::automata::TokenKind::Fixed(__open))
                    if __open == "(" && state_cat_src_idx == #result_src_idx => {
                    return mettail_prattail::wpda_transitions::prefix::paren_singleton(
                        #grouping_src_idx, cur_bp, pos, tokens, lex_one,
                    );
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
        // `(`-triggered BINDER rule (e.g. Rholang's `PInputs . ns:Vec(Name) …
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
        let grouping_source_indices: Vec<u16> = if local_paren_binder_rules.is_empty() {
            grouping_source_indices
        } else {
            vec![result_src_idx]
        };
        for grouping_src_idx in &grouping_source_indices {
            let is_cross_cat = *grouping_src_idx != result_src_idx;
            let action_kind = if is_cross_cat {
                quote! {
                    mettail_prattail::wpda_walker::ForkActionKind::ConsumeAndPushCrossCatLhs {
                        trigger_mode: mettail_prattail::wpda_walker::TriggerMode::Discard,
                    }
                }
            } else {
                quote! {
                    mettail_prattail::wpda_walker::ForkActionKind::ConsumeAndPush {
                        trigger_mode: mettail_prattail::wpda_walker::TriggerMode::Discard,
                    }
                }
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
            //   `lex_w(BP_TIER_CROSSCAT_PROJECTION, grouping_src_idx, 0)`), and at a
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
                        #grouping_src_idx,
                        0u16,
                    )
                }
            } else {
                quote! { lex_one() }
            };
            branches.push(quote! {
                mettail_prattail::wpda_transitions::prefix::paren_grouping_branch(
                #grouping_src_idx,
                cur_bp,
                pos,
                tokens,
                || #grouping_weight,
                || #action_kind,
                )
            });
        }
        // Concrete `(`-led rules from every admitted grouping source.  The
        // owner category is carried explicitly: a source rule completes in
        // its own category and the cross-category boundary then resumes the
        // enclosing infix/projection context.  Omitting these branches reduced
        // a source category to generic parenthesized grouping and made rules
        // such as `(Ctor arg)` unavailable whenever they occurred as another
        // category's operand.
        let paren_binder_rules: Vec<(u16, u16, super::binder::BinderShape)> =
            grouping_source_indices
                .iter()
                .flat_map(|&owner_src_idx| {
                    per_cat[owner_src_idx as usize]
                        .iter()
                        .enumerate()
                        .filter_map(move |(rule_i, rule)| {
                            let shape = super::binder::classify_binder_in(rule, language)?;
                            let first_trigger = rule.syntax_pattern.as_ref()?.first()?;
                            match first_trigger {
                                mettail_ast::grammar::SyntaxExpr::Literal(text) if text == "(" => {
                                    Some((owner_src_idx, rule_i as u16, shape))
                                },
                                _ => None,
                            }
                        })
                })
                .collect();
        for (paren_binder_position, (owner_src_idx, rule_idx, shape)) in
            paren_binder_rules.iter().enumerate()
        {
            let body_src_idx = super::binder::binder_initial_body_cat(shape)
                .and_then(|name| super::binder::lookup_src_idx(name, categories))
                .unwrap_or(*owner_src_idx);
            let owner_src_idx_lit = *owner_src_idx;
            let rule_idx_lit = *rule_idx;
            // Task #10 item 1: the binder branch's STATIC position = after
            // ALL grouping branches (grouping-first layout), in declaration
            // order.
            fork_rows.record_site2_row(
                owner_src_idx_lit,
                rule_idx_lit,
                (grouping_source_indices.len() + paren_binder_position) as u16,
                "paren-dispatch \"(\"",
            );
            let (branch_symbol, action_kind) = if owner_src_idx_lit == result_src_idx {
                (
                    quote! {
                        StackSymbolV2::rule_at(
                            #owner_src_idx_lit, #rule_idx_lit, 1u8, Some(_outer_bp),
                        )
                    },
                    quote! {
                        mettail_prattail::wpda_walker::ForkActionKind::ConsumeAndPush {
                            trigger_mode:
                                mettail_prattail::wpda_walker::TriggerMode::ConsumeAsTriggerOnly,
                        }
                    },
                )
            } else {
                // Preserve the ordinary cross-category LHS stack shape:
                // target caller -> source CategoryEntry -> selected RuleAt.
                // BinderRule recognizes the intermediate CategoryEntry as a
                // trigger prelude, consumes this rule's declared leading
                // literal, and pushes RuleAt with the TriggerTerminal as its
                // initial SPPF leaf.
                (
                    quote! { StackSymbolV2::category_entry(#owner_src_idx_lit) },
                    quote! { mettail_prattail::wpda_walker::ForkActionKind::PushCrossCatLhs },
                )
            };
            let branch_weight = if owner_src_idx_lit == result_src_idx {
                quote! { lex_w(0.0, #owner_src_idx_lit, #rule_idx_lit) }
            } else {
                quote! {
                    lex_w(
                        mettail_prattail::automata::lex_weight::BP_TIER_CROSSCAT_LHS,
                        #owner_src_idx_lit,
                        #rule_idx_lit,
                    )
                }
            };
            branches.push(quote! {
                mettail_prattail::wpda_transitions::prefix::paren_binder_branch(
                #owner_src_idx_lit,
                #rule_idx_lit,
                #body_src_idx,
                _outer_bp,
                || #branch_symbol,
                || #branch_weight,
                || #action_kind,
                )
            });
        }
        let branch_count = branches.len();
        let branch_pushes = branches.iter().map(|branch| {
            quote! {
                __paren_branches.push(#branch);
            }
        });
        arms.push(quote! {
            Some(mettail_prattail::automata::TokenKind::Fixed(__open))
                if __open == "(" && state_cat_src_idx == #result_src_idx => {
                return mettail_prattail::wpda_transitions::prefix::paren_fork(
                    #branch_count,
                    |__paren_branches| { #( #branch_pushes )* },
                );
            }
        });
    }
    quote! { #(#arms)* }
}

/// The `literals { Cat { pattern: …; eval: ![{ … }] } }` declaration for `cat_name`, if the
/// grammar has one that carries an `eval` body.
///
/// One lookup, so `classify_literal_patterned` (which needs the body) and
/// [`literal_family_for_category`] (which needs only its existence) cannot disagree about
/// whether a category declared a literal.
fn declared_literal_token_def<'a>(
    cat_name: &str,
    language: &'a LanguageDef,
) -> Option<&'a mettail_ast::language::TokenDef> {
    mettail_prattail::wpda_rule_analysis::native_first::declared_literal_token_def(
        cat_name,
        &language.token_defs,
        |token| token.from_literals,
        |token| token.rust_code.is_some(),
        |token| token.category.as_ref().map(ToString::to_string),
    )
}

/// ★ THE SINGLE ELECTION SITE for a category's [`LiteralFamily`].
///
/// The built-in families come from the carrier ([`literal_family_for`]). When the carrier
/// belongs to none of them, the category still HAS a literal surface if it DECLARED one, and
/// that surface is [`LiteralFamily::Custom`].
///
/// # Why the fallback must be here rather than in `literal_family_for`
///
/// `literal_family_for` is a total function of the `NativeKind` alone and several emitters rely
/// on that (they hold a kind, not a category). The `Custom` election is a fact about the
/// GRAMMAR, not about the type: two categories with the same `NativeKind::Other` carrier differ
/// precisely in whether they declared a pattern. Keeping the two functions separate keeps
/// `literal_family_for` honest and makes this the only place a declaration can grant a family.
///
/// # The failure this closes
///
/// Before it, a declared `literals { … }` block on a category whose carrier had no built-in
/// family was **read, validated, desugared into a `TokenDef`, compiled into the lexer DFA — and
/// then dropped on the floor by the parser**, because `classify_literal_patterned` returned
/// `None` at the family lookup and the rule fell through to `AtomicShape::NonAtomic`. The token
/// was produced and nothing could consume it. That is a silent partial wiring, and it is why
/// this returns a family for the declaration rather than requiring a carrier enumeration to be
/// kept complete by hand.
fn literal_family_for_category(cat_name: &str, language: &LanguageDef) -> Option<LiteralFamily> {
    mettail_prattail::wpda_rule_analysis::native_first::literal_family_for_category(
        cat_name,
        &language.types,
        |ty| ty.name.to_string(),
        |ty| ty.native_type.as_ref(),
        NativeKind::from_syn_type,
        |name| declared_literal_token_def(name, language).is_some(),
    )
}

/// Map a `NativeKind` to the lexer's `LiteralFamily`.
///
/// ⚠ Callers that hold a CATEGORY should use [`literal_family_for_category`] instead: a category
/// whose carrier has no built-in family may still have declared its own literal, and only the
/// category-level function can see that.
#[cfg(test)]
fn literal_family_for(kind: &NativeKind) -> Option<LiteralFamily> {
    mettail_prattail::wpda_rule_analysis::native_first::literal_family_for(kind)
}

/// Emit per-rule arms in the `PrefixDispatch` match for one category.
/// CROSSCAT_LEX_COMPAT_GATE (2026-07-03): does `cat_name` have a HOME variable
/// reading — i.e. can a bare `Ident` parse as a `cat_name` term WITHOUT any
/// cross-cat projection? True iff the category either has an explicit user Var
/// rule (a `language.terms` rule whose first item is `NonTerminal{kind:Var}`) OR
/// receives the synthetic Var rule (the `!has_user_var` branch of
/// `collect_first_set`, which every open declared `language.types` category
/// takes). Closed `data` categories receive no synthetic Var constructor.
/// Grammar-derived, mirrors `collect_first_set`'s Var logic EXACTLY so the gate
/// is precise. When true, a bare Ident in `cat_name` is already covered by the
/// home Var reading, so a cross-cat cast delegate `source : cat_name` on the
/// `Ident` token — where the `Ident` is ONLY a var-contribution of `source`
/// (the source cannot begin with a LITERAL Ident) — is a proven over-generation
/// (it duplicates the home var reading via a spurious ∅-realizing cast path).
#[cfg(test)]
fn result_has_home_var_reading(cat_name: &str, language: &LanguageDef) -> bool {
    mettail_prattail::wpda_rule_analysis::prefix::result_has_home_var_reading(
        cat_name,
        &super::binder::MacroBinderSyntaxReader,
        &mut MacroFirstSetContext { language },
    )
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
    mettail_prattail::wpda_rule_analysis::prefix::source_ident_first_is_var_only(
        source_cat,
        &super::binder::MacroBinderSyntaxReader,
        &mut MacroFirstSetContext { language },
    )
}

/// Categories whose transitive FIRST set contains an unguarded `Ident` token.
///
/// This is the boolean projection of [`first_set_of_category`]: direct synthetic
/// or explicit Var contributions are seeds; cross-category projections and
/// Param-led non-atomic rules are graph edges. Computing the closure once avoids
/// rebuilding an entire FIRST set at every edge of the var-only traversal.
#[cfg(test)]
fn ident_first_categories(language: &LanguageDef) -> std::collections::HashSet<String> {
    mettail_prattail::wpda_rule_analysis::prefix::ident_first_categories(
        &super::binder::MacroBinderSyntaxReader,
        &mut MacroFirstSetContext { language },
    )
}

#[cfg(test)]
#[path = "../../../../tests/support/prefix_ident_recursive_oracle.rs"]
mod ident_recursive_oracle;

#[cfg(test)]
#[path = "../../../../tests/support/prefix_ident_summary_baselines.rs"]
mod ident_summary_baselines;

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
) -> (Vec<TokenStream>, TokenStream) {
    let mut arms = Vec::new();
    let (mut unified_buckets, unified_order) =
        mettail_prattail::wpda_rule_analysis::prefix_bucket::derive_prefix_buckets(
            &super::binder::MacroBinderSyntaxReader,
            &mut MacroFirstSetContext { language },
            category_src_idx,
            category_name,
            rules_in_category,
            super::forks::CROSSCAT_LEX_COMPAT_GATE,
        );
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
    (arms, quote! { #(#helpers)* })
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
type PrefixArmDescriptor =
    mettail_prattail::wpda_rule_analysis::atomic_prefix::PrefixArmDescriptor<TokenStream>;

/// Stage 3.16 invariant (Cluster 2, Mechanism γ, 2026-05-05) — extracts
/// pattern/guard pairs for an atomic shape, so the caller can bucket by
/// (pat, guard) before emitting either a singleton arm or a Fork.
fn atomic_arm_descriptors(
    category_src_idx: u16,
    rule_idx: u16,
    shape: &mettail_prattail::wpda_rule_analysis::atomic::AtomicDescriptor<AtomicShape>,
) -> Vec<PrefixArmDescriptor> {
    mettail_prattail::wpda_rule_analysis::atomic_prefix::atomic_arm_descriptors(
        category_src_idx,
        rule_idx,
        shape,
        first_predicate_parts,
        |literal, context| {
            let AtomicShape::LiteralPatterned { cat_name, family, native_type, .. } = literal
            else {
                unreachable!("original literal resolver returns only LiteralPatterned payloads");
            };
            let nk = NativeKind::from_syn_type(native_type);
            literal_patterned_pattern_and_guard_for_kind(cat_name, *family, Some(&nk), context)
        },
    )
}

/// Return the ordinary led-dispatch floor for a rule that is represented in
/// the binding-power table as a same-category operator. The table is the
/// authoritative classifier: the prefix and led surfaces therefore cannot
/// disagree about whether a rule is precedence-gated or about its power.
pub(crate) fn same_category_led_left_bp(
    rule: &GrammarRule,
    result_category: &str,
    bp_table: &mettail_prattail::binding_power::BindingPowerTable,
) -> Option<u8> {
    let label = rule.label.to_string();
    mettail_prattail::wpda_rule_analysis::atomic_prefix::same_category_led_left_bp(
        &label,
        result_category,
        bp_table,
    )
}

/// B7 (2026-05-07) — unified descriptor for the merged Pass 0/Pass 1
/// bucket map. Each bucket entry is a list of these; singleton buckets
/// emit a direct arm matching their kind; mixed buckets emit a Fork.
///
/// B10 / Option κ Fix B (2026-05-07): adds `CrossCatProjection` so Pass 2a
/// folds into the same bucket map. Closes the Pass-1/2a silent shadow
/// twin of the Pass-0/1 bug B7 fixed.
type UnifiedDescriptor =
    mettail_prattail::wpda_rule_analysis::atomic_prefix::UnifiedDescriptor<TokenStream>;

/// B7 (2026-05-07) — unified bucket entry. Replaces the separate
/// LhsBucketEntry (Pass 0) and atomic bucket map (Pass 1).
type UnifiedBucket =
    mettail_prattail::wpda_rule_analysis::prefix::UnifiedBucket<TokenStream, UnifiedDescriptor>;

#[cfg(test)]
use mettail_prattail::wpda_rule_analysis::prefix::insert_unified_descriptor;

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
///
/// ★ #141 G4 — returns `Some(compile_error!)` when the factoring model has
/// drifted, `None` on every path that records rows normally.
///
/// The `panic!` this replaces claimed to make a drift "fail codegen loudly" and
/// could not: under this workspace's cranelift dev backend a proc-macro panic
/// prints NOTHING (#141 RED-0, 2026-07-29). This function records into a
/// macro-time model rather than emitting, so it cannot refuse in place; it hands
/// the refusal back and each of the four callers splices it into the branch
/// tokens it was about to emit. `Option<TokenStream>` interpolates as nothing on
/// the success path, so the emitted bytes are unchanged wherever there is no
/// drift.
#[allow(clippy::too_many_arguments)]
#[must_use]
fn record_initiating_rule_rows(
    fork_rows: &mut super::fork_emission::ForkEmissionOrdinalModel,
    category_src_idx: u16,
    rule_idx: u16,
    branch_position: u16,
    s1_dispositions: &std::collections::HashMap<u16, super::factoring::SpineDisposition>,
    s1_group_members: &std::collections::HashMap<u16, Vec<u16>>,
    bucket_tag: &str,
) -> Option<TokenStream> {
    use mettail_prattail::wpda_rule_analysis::prefix::{
        record_initiating_rule_rows as record_shared_rows, InitiatingRuleDisposition,
    };

    let missing = record_shared_rows(
        fork_rows.descriptor_mut(),
        category_src_idx,
        rule_idx,
        branch_position,
        |rule| {
            s1_dispositions
                .get(&rule)
                .map(|disposition| match disposition {
                    super::factoring::SpineDisposition::GroupFirst { .. } => {
                        InitiatingRuleDisposition::GroupFirst
                    },
                    super::factoring::SpineDisposition::GroupRest => {
                        InitiatingRuleDisposition::GroupRest
                    },
                })
        },
        |rule| s1_group_members.get(&rule).map(Vec::as_slice),
        bucket_tag,
    )?;
    let category_src_idx = missing.category_src_idx;
    let rule_idx = missing.rule_idx;
    let message = format!(
        "mettail: task #10 item 1 — the rule at category index \
         {category_src_idx}, rule index {rule_idx} is dispositioned \
         `GroupFirst` by the S1 factoring model but has no `group_members` \
         entry, so the fork emission cannot derive the site-2 rows its \
         members are owed. The two halves of the factoring model disagree; \
         this is a macro bug, not a grammar bug — please report it.",
    );
    Some(quote! { compile_error!(#message); })
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
                            return mettail_prattail::wpda_transitions::prefix::singleton_crosscat_lhs(
                            pos,
                            #source_src_idx,
                            lex_one,
                            );
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
                // ★ #141 G9. The singleton path is unreachable for a GROUPED rule
                // because a factored group needs ≥2 co-bucketed members — a claim
                // about `factoring::discover_members` and this insertion chain
                // bucketing identically, which nothing checks. The `assert!` said it
                // would "fail codegen loudly" and could not: a proc-macro panic under
                // this workspace's cranelift dev backend prints nothing at all (#141
                // RED-0). It is now a `compile_error!` spliced into the arm body — a
                // token `rustc` renders — and EMPTY on the success path, so the
                // emitted bytes are unchanged wherever the claim holds.
                let s1_singleton_refusal: TokenStream = match s1_dispositions
                    .get(&rule_idx)
                    .is_none()
                {
                    true => TokenStream::new(),
                    false => {
                        let message = format!(
                            "mettail: S1-FACTORING F1 — the rule at category index \
                             {category_src_idx}, rule index {rule_idx}, is dispositioned \
                             into a factored spine group but reached the singleton BinderPrefix emission, which \
                             only an UNGROUPED rule can reach. `factoring::discover_members` \
                             and the unified-bucket insertion chain have bucketed it \
                             differently. This is a macro bug, not a grammar bug — please \
                             report it."
                        );
                        quote! { compile_error!(#message); }
                    },
                };
                // Task #10 item 1: singleton = position 0 (grouped members
                // asserted unreachable above, so the plain row suffices).
                fork_rows.record_site2_row(category_src_idx, rule_idx, 0, &fork_bucket_tag);
                (
                    quote! { #pat if #guard },
                    quote! {
                        {
                            #s1_singleton_refusal
                            return mettail_prattail::wpda_transitions::prefix::singleton_binder_prefix(
                            _outer_bp,
                            #category_src_idx,
                            #rule_idx,
                            #body_src_idx,
                            lex_w,
                            );
                        }
                    },
                )
            },
            UnifiedDescriptor::LeadingCategory { rule_idx, source_src_idx } => {
                let rule_idx = *rule_idx;
                let source_src_idx = *source_src_idx;
                fork_rows.record_site2_row(category_src_idx, rule_idx, 0, &fork_bucket_tag);
                (
                    quote! { #pat if #guard },
                    quote! {
                        {
                            return mettail_prattail::wpda_transitions::prefix::singleton_leading_category(
                            _outer_bp,
                            pos,
                            #category_src_idx,
                            #rule_idx,
                            #source_src_idx,
                            lex_w,
                            );
                        }
                    },
                )
            },
            UnifiedDescriptor::LeadingTokenKindCapture { rule_idx, body_src_idx, kind_name } => {
                let rule_idx = *rule_idx;
                let body_src_idx = *body_src_idx;
                // L9-3: leading builtin/custom token-family capture — never S1-grouped (it
                // terminates mergeability), so it always reaches the singleton
                // path. Emit a single-branch Fork carrying
                // GuardedConsumeTokenKindAndPush (a ForkActionKind — hence a
                // Fork rather than the non-capturing ConsumeAndPush the Literal
                // trigger uses): the walker gates the actual token through the
                // shared named-family predicate,
                // captures the token as an ActionArg::Token leaf, PUSHES
                // RuleAt(slot=1) (the leading token is the trigger — there is no
                // prior literal trigger to push the frame, unlike the mid-rule
                // capture which only replaces cur_sym), and enters BinderRule for
                // the remaining mid-rule positions.
                // ★ #141 G9. The singleton path is unreachable for a GROUPED rule
                // because a factored group needs ≥2 co-bucketed members — a claim
                // about `factoring::discover_members` and this insertion chain
                // bucketing identically, which nothing checks. The `assert!` said it
                // would "fail codegen loudly" and could not: a proc-macro panic under
                // this workspace's cranelift dev backend prints nothing at all (#141
                // RED-0). It is now a `compile_error!` spliced into the arm body — a
                // token `rustc` renders — and EMPTY on the success path, so the
                // emitted bytes are unchanged wherever the claim holds.
                let s1_singleton_refusal: TokenStream = match s1_dispositions
                    .get(&rule_idx)
                    .is_none()
                {
                    true => TokenStream::new(),
                    false => {
                        let message = format!(
                            "mettail: S1-FACTORING F1 — the rule at category index \
                             {category_src_idx}, rule index {rule_idx}, is dispositioned \
                             into a factored spine group but reached the singleton LeadingTokenKindCapture emission, which \
                             only an UNGROUPED rule can reach. `factoring::discover_members` \
                             and the unified-bucket insertion chain have bucketed it \
                             differently. This is a macro bug, not a grammar bug — please \
                             report it."
                        );
                        quote! { compile_error!(#message); }
                    },
                };
                fork_rows.record_site2_row(category_src_idx, rule_idx, 0, &fork_bucket_tag);
                (
                    quote! { #pat if #guard },
                    quote! {
                        {
                            #s1_singleton_refusal
                            return mettail_prattail::wpda_transitions::prefix::singleton_token_capture(
                            _outer_bp,
                            #category_src_idx,
                            #rule_idx,
                            #body_src_idx,
                            #kind_name,
                            lex_w,
                            );
                        }
                    },
                )
            },
            UnifiedDescriptor::LeadingGuestBody {
                rule_idx,
                body_src_idx,
                open_kind,
                nested_open_kinds,
                close_kind,
            } => {
                let rule_idx = *rule_idx;
                let body_src_idx = *body_src_idx;
                let nested_open_kinds = nested_open_kinds
                    .iter()
                    .map(|kind| quote! { #kind.to_string() })
                    .collect::<Vec<_>>();
                // L9-4: leading guest body — never S1-grouped (a guest body
                // terminates mergeability), so always the singleton path. Emit a
                // single-branch Fork carrying ConsumeGuestBodyAndPush: the walker
                // gates peek_kind == Custom(open_kind), scans the whole
                // opener→body→closer region assembling the FltNode, PUSHES
                // RuleAt(slot=1), and enters BinderRule.
                // ★ #141 G9. The singleton path is unreachable for a GROUPED rule
                // because a factored group needs ≥2 co-bucketed members — a claim
                // about `factoring::discover_members` and this insertion chain
                // bucketing identically, which nothing checks. The `assert!` said it
                // would "fail codegen loudly" and could not: a proc-macro panic under
                // this workspace's cranelift dev backend prints nothing at all (#141
                // RED-0). It is now a `compile_error!` spliced into the arm body — a
                // token `rustc` renders — and EMPTY on the success path, so the
                // emitted bytes are unchanged wherever the claim holds.
                let s1_singleton_refusal: TokenStream = match s1_dispositions
                    .get(&rule_idx)
                    .is_none()
                {
                    true => TokenStream::new(),
                    false => {
                        let message = format!(
                            "mettail: S1-FACTORING F1 — the rule at category index \
                             {category_src_idx}, rule index {rule_idx}, is dispositioned \
                             into a factored spine group but reached the singleton LeadingGuestBody emission, which \
                             only an UNGROUPED rule can reach. `factoring::discover_members` \
                             and the unified-bucket insertion chain have bucketed it \
                             differently. This is a macro bug, not a grammar bug — please \
                             report it."
                        );
                        quote! { compile_error!(#message); }
                    },
                };
                fork_rows.record_site2_row(category_src_idx, rule_idx, 0, &fork_bucket_tag);
                (
                    quote! { #pat if #guard },
                    quote! {
                        {
                            #s1_singleton_refusal
                            return mettail_prattail::wpda_transitions::prefix::singleton_guest_body(
                            _outer_bp,
                            #category_src_idx,
                            #rule_idx,
                            #body_src_idx,
                            #open_kind,
                            || vec![#(#nested_open_kinds),*],
                            #close_kind,
                            lex_w,
                            );
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
                            return mettail_prattail::wpda_transitions::prefix::singleton_crosscat_unary(
                            _outer_bp,
                            #category_src_idx,
                            #rule_idx,
                            #source_src_idx,
                            #operand_bp,
                            lex_w,
                            );
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
                            return mettail_prattail::wpda_transitions::prefix::singleton_crosscat_projection(
                            _outer_bp,
                            cur_bp,
                            #category_src_idx,
                            #rule_idx,
                            #source_src_idx,
                            lex_w,
                            );
                        }
                    },
                )
            },
            UnifiedDescriptor::NullaryLiteralRun { rule_idx } => {
                let rule_idx = *rule_idx;
                // S1-FACTORING F1: same singleton-unreachability assert as
                // the BinderPrefix arm above (groups need ≥2 co-bucketed
                // members).
                // ★ #141 G9. The singleton path is unreachable for a GROUPED rule
                // because a factored group needs ≥2 co-bucketed members — a claim
                // about `factoring::discover_members` and this insertion chain
                // bucketing identically, which nothing checks. The `assert!` said it
                // would "fail codegen loudly" and could not: a proc-macro panic under
                // this workspace's cranelift dev backend prints nothing at all (#141
                // RED-0). It is now a `compile_error!` spliced into the arm body — a
                // token `rustc` renders — and EMPTY on the success path, so the
                // emitted bytes are unchanged wherever the claim holds.
                let s1_singleton_refusal: TokenStream = match s1_dispositions
                    .get(&rule_idx)
                    .is_none()
                {
                    true => TokenStream::new(),
                    false => {
                        let message = format!(
                            "mettail: S1-FACTORING F1 — the rule at category index \
                             {category_src_idx}, rule index {rule_idx}, is dispositioned \
                             into a factored spine group but reached the singleton NullaryLiteralRun emission, which \
                             only an UNGROUPED rule can reach. `factoring::discover_members` \
                             and the unified-bucket insertion chain have bucketed it \
                             differently. This is a macro bug, not a grammar bug — please \
                             report it."
                        );
                        quote! { compile_error!(#message); }
                    },
                };
                // Task #10 item 1: singleton = position 0.
                fork_rows.record_site2_row(category_src_idx, rule_idx, 0, &fork_bucket_tag);
                (
                    quote! { #pat if #guard },
                    quote! {
                        {
                            #s1_singleton_refusal
                            return mettail_prattail::wpda_transitions::prefix::singleton_nullary_literal_run(
                            cur_bp,
                            #category_src_idx,
                            #rule_idx,
                            lex_w,
                            );
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
                UnifiedDescriptor::CrossCatLhs { source_src_idx, sigil_leads_result_rule } => {
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
                        mettail_prattail::wpda_transitions::prefix::push_crosscat_lhs(
                        __pd_branches,
                        pos,
                        #category_src_idx,
                        #src_idx,
                        || #__keep_guard,
                        lex_w,
                        );
                    }
                },
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
                        mettail_prattail::wpda_transitions::prefix::push_atomic(
                        __pd_branches,
                        _outer_bp,
                        #csi,
                        #rule_idx,
                        lex_w,
                        );
                    }
                },
                UnifiedDescriptor::BinderPrefix { rule_idx, body_src_idx } => {
                    let rule_idx = *rule_idx;
                    let body_src_idx = *body_src_idx;
                    // Task #10 item 1: disposition-routed rows — GroupFirst
                    // derives every member's row at THIS position; GroupRest
                    // derives nothing; plain rules derive their own row.
                    let rows_refusal = record_initiating_rule_rows(
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
                    let branch = match s1_dispositions.get(&rule_idx) {
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
                            mettail_prattail::wpda_transitions::prefix::push_binder_prefix(
                            __pd_branches,
                            _outer_bp,
                            #category_src_idx,
                            #rule_idx,
                            #body_src_idx,
                            lex_w,
                            );
                        },
                    };
                    quote! { #rows_refusal #branch }
                },
                UnifiedDescriptor::LeadingCategory { rule_idx, source_src_idx } => {
                    let rule_idx = *rule_idx;
                    let source_src_idx = *source_src_idx;
                    fork_rows.record_site2_row(
                        category_src_idx,
                        rule_idx,
                        branch_position as u16,
                        &fork_bucket_tag,
                    );
                    quote! {
                        mettail_prattail::wpda_transitions::prefix::push_leading_category(
                        __pd_branches,
                        _outer_bp,
                        pos,
                        #category_src_idx,
                        #rule_idx,
                        #source_src_idx,
                        lex_w,
                        );
                    }
                },
                UnifiedDescriptor::LeadingTokenKindCapture {
                    rule_idx,
                    body_src_idx,
                    kind_name,
                } => {
                    let rule_idx = *rule_idx;
                    let body_src_idx = *body_src_idx;
                    // L9-3: leading builtin/custom token-family capture in a Fork bucket (a
                    // co-bucketed same-kind sibling, or shared with other
                    // descriptors on the same (pat,guard)). Never S1-grouped ⇒
                    // a plain row + a capturing branch. Uses
                    // GuardedConsumeTokenKindAndPush (PUSHES the RuleAt frame —
                    // the leading token IS the trigger, so no prior push exists;
                    // mirrors the singleton path above) instead of the
                    // non-capturing ConsumeAsTriggerOnly the Literal trigger uses.
                    let rows_refusal = record_initiating_rule_rows(
                        fork_rows,
                        category_src_idx,
                        rule_idx,
                        branch_position as u16,
                        s1_dispositions,
                        s1_group_members,
                        &fork_bucket_tag,
                    );
                    quote! {
                        #rows_refusal
                        mettail_prattail::wpda_transitions::prefix::push_token_capture(
                        __pd_branches,
                        _outer_bp,
                        #category_src_idx,
                        #rule_idx,
                        #body_src_idx,
                        #kind_name,
                        lex_w,
                        );
                    }
                },
                UnifiedDescriptor::LeadingGuestBody {
                    rule_idx,
                    body_src_idx,
                    open_kind,
                    nested_open_kinds,
                    close_kind,
                } => {
                    let rule_idx = *rule_idx;
                    let body_src_idx = *body_src_idx;
                    let nested_open_kinds = nested_open_kinds
                        .iter()
                        .map(|kind| quote! { #kind.to_string() })
                        .collect::<Vec<_>>();
                    // L9-4: leading guest body in a Fork bucket — the ConsumeGuestBodyAndPush
                    // twin of the singleton path (PUSHES the RuleAt frame).
                    let rows_refusal = record_initiating_rule_rows(
                        fork_rows,
                        category_src_idx,
                        rule_idx,
                        branch_position as u16,
                        s1_dispositions,
                        s1_group_members,
                        &fork_bucket_tag,
                    );
                    quote! {
                        #rows_refusal
                        mettail_prattail::wpda_transitions::prefix::push_guest_body(
                        __pd_branches,
                        _outer_bp,
                        #category_src_idx,
                        #rule_idx,
                        #body_src_idx,
                        #open_kind,
                        || vec![#(#nested_open_kinds),*],
                        #close_kind,
                        lex_w,
                        );
                    }
                },
                UnifiedDescriptor::CrossCatPrefixUnary { rule_idx, source_src_idx, operand_bp } => {
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
                        mettail_prattail::wpda_transitions::prefix::push_crosscat_unary(
                        __pd_branches,
                        _outer_bp,
                        #category_src_idx,
                        #rule_idx,
                        #source_src_idx,
                        #operand_bp,
                        lex_w,
                        );
                    }
                },
                UnifiedDescriptor::CrossCatProjection { rule_idx, source_src_idx } => {
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
                        mettail_prattail::wpda_transitions::prefix::push_crosscat_projection(
                        __pd_branches,
                        _outer_bp,
                        cur_bp,
                        #category_src_idx,
                        #rule_idx,
                        #src_idx,
                        lex_w,
                        );
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
                },
                UnifiedDescriptor::NullaryLiteralRun { rule_idx } => {
                    let rule_idx = *rule_idx;
                    // Task #10 item 1: same disposition-routed rows as the
                    // BinderPrefix arm above.
                    let rows_refusal = record_initiating_rule_rows(
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
                    let branch = match s1_dispositions.get(&rule_idx) {
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
                            mettail_prattail::wpda_transitions::prefix::push_nullary_literal_run(
                            __pd_branches,
                            cur_bp,
                            #category_src_idx,
                            #rule_idx,
                            lex_w,
                            );
                        },
                    };
                    quote! { #rows_refusal #branch }
                },
            })
            .collect();
        (
            quote! { #pat if #guard },
            quote! {
                {
                    return mettail_prattail::wpda_transitions::prefix::unified_fork(
                        #n_descs,
                        |__pd_branches| { #( #push_stmts )* },
                    );
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
                return mettail_prattail::wpda_transitions::prefix::singleton_atomic(
                _outer_bp,
                #category_src_idx,
                #rule_idx,
                lex_w,
                );
            }
        },
    )
}

/// Static quotation payloads for the original shared native descriptor sites.
struct MacroNativeFirstConstructors;

impl mettail_prattail::wpda_rule_analysis::native_first::NativeFirstConstructors
    for MacroNativeFirstConstructors
{
    type Pattern = TokenStream;

    fn pattern(
        &mut self,
        site: mettail_prattail::wpda_rule_analysis::native_first::NativePatternSite,
    ) -> TokenStream {
        use mettail_prattail::wpda_rule_analysis::native_first::NativePatternSite;
        match site {
            NativePatternSite::IntegerTyped => {
                quote! { Some(mettail_prattail::automata::TokenKind::IntegerLit(__cat)) }
            },
            NativePatternSite::CustomTyped => {
                quote! { Some(mettail_prattail::automata::TokenKind::Custom(__cat)) }
            },
            NativePatternSite::RationalTyped => {
                quote! { Some(mettail_prattail::automata::TokenKind::RationalLit(__cat)) }
            },
            NativePatternSite::FixedPointTyped => {
                quote! { Some(mettail_prattail::automata::TokenKind::FixedPointLit(__cat)) }
            },
            NativePatternSite::FloatBare => {
                quote! { Some(mettail_prattail::automata::TokenKind::Float) }
            },
            NativePatternSite::BooleanAlternative => quote! {
                Some(mettail_prattail::automata::TokenKind::True)
                | Some(mettail_prattail::automata::TokenKind::False)
                | Some(mettail_prattail::automata::TokenKind::BooleanLit)
            },
            NativePatternSite::StringBare => {
                quote! { Some(mettail_prattail::automata::TokenKind::StringLit) }
            },
            NativePatternSite::IntegerBare => {
                quote! { Some(mettail_prattail::automata::TokenKind::Integer) }
            },
        }
    }

    fn category_guard(&mut self, cat_name: &str) -> TokenStream {
        quote! { __cat == #cat_name }
    }
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
    mettail_prattail::wpda_rule_analysis::native_first::literal_patterned_pattern_and_guard_for_kind(
        cat_name,
        family,
        kind,
        ctx,
        &mut MacroNativeFirstConstructors,
    )
}

#[cfg(test)]
#[path = "../../../../tests/support/prefix_first_set_baselines.rs"]
mod prefix_first_set_baselines;

#[cfg(test)]
#[path = "../../../../tests/support/unified_prefix_descriptor_baselines.rs"]
mod unified_prefix_descriptor_baselines;

#[cfg(test)]
#[path = "../../../../tests/support/grouping_source_descriptor_baselines.rs"]
mod grouping_source_descriptor_baselines;

#[cfg(test)]
#[path = "../../../../tests/support/native_first_descriptor_baselines.rs"]
mod native_first_descriptor_baselines;

#[cfg(test)]
#[path = "../../../../tests/support/atomic_prefix_descriptor_baselines.rs"]
mod atomic_prefix_descriptor_baselines;

#[cfg(test)]
#[path = "../../../../tests/support/prefix_bucket_driver_baselines.rs"]
mod prefix_bucket_driver_baselines;

#[cfg(test)]
#[path = "../../../../tests/support/neutral_prefix_pattern_reuse.rs"]
mod neutral_prefix_pattern_reuse;

#[cfg(test)]
mod tests {
    use super::*;

    include!("../../../../tests/support/owned_atomic_reuse.rs");
    include!("../../../../tests/support/owned_prefix_reuse.rs");
    include!("../../../../tests/support/owned_descriptor_reuse.rs");
    include!("../../../../tests/support/owned_cast_reuse.rs");

    mod bucket_driver_shared {
        include!("../../../../tests/support/prefix_bucket_shared.rs");
    }
    use mettail_ast::grammar::{
        rule_fixture, DelimitedRegionKind, GrammarItem, SyntaxExpr, TermParam,
    };
    use mettail_ast::language::{CategoryRole, LangType, TokenDef};
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
            role: CategoryRole::Object,
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
            role: CategoryRole::Object,
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

    // Compare the original classifier's complete result to fixed descriptors;
    // no second classifier or native-kind resolver is implemented by these tests.
    fn assert_atomic_projection_baseline(
        rule: &GrammarRule,
        language: &LanguageDef,
        expected: AtomicShape,
    ) {
        let actual = classify_atomic(rule, language);
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
        owned_atomic_reuse::assert_owned_parity(rule, language);
    }

    #[test]
    fn atomic_projection_baseline_judgement_priority_and_absence() {
        let language = lang_with_int_literal();
        let mut rule = category_rule("Declared", "Int", "Int");
        rule.term_context = Some(Vec::new());
        rule.syntax_pattern = Some(vec![SyntaxExpr::Literal("keyword".into())]);
        assert_atomic_projection_baseline(
            &rule,
            &language,
            AtomicShape::TerminalKeyword {
                terminal_text: "keyword".into(),
                wrapper_variant: rule.label.clone(),
            },
        );
        rule.syntax_pattern = Some(Vec::new());
        assert_atomic_projection_baseline(&rule, &language, AtomicShape::NonAtomic);

        // Legacy fallback occurs when EITHER judgement field is absent, but
        // never when both are present and judgement classification refuses.
        for (tc_present, sp_present) in [(false, false), (true, false), (false, true)] {
            let mut rule = atomic_rule("Legacy", "Int", NonTerminalKind::Integer);
            rule.term_context = tc_present.then(Vec::new);
            rule.syntax_pattern = sp_present.then(Vec::new);
            assert_atomic_projection_baseline(&rule, &language, AtomicShape::LiteralInteger);
        }
    }

    #[test]
    fn atomic_projection_baseline_every_legacy_nonterminal_kind() {
        let language = empty_lang();
        for (kind, expected) in [
            (NonTerminalKind::Integer, AtomicShape::LiteralInteger),
            (NonTerminalKind::Boolean, AtomicShape::LiteralBoolean),
            (NonTerminalKind::StringLiteral, AtomicShape::LiteralString),
            (NonTerminalKind::FloatLiteral, AtomicShape::LiteralFloat),
            (NonTerminalKind::Ident, AtomicShape::NonAtomic),
            (NonTerminalKind::Category, AtomicShape::NonAtomic),
            (NonTerminalKind::Var, AtomicShape::NonAtomic),
        ] {
            let rule = atomic_rule("Legacy", "Int", kind);
            assert_atomic_projection_baseline(&rule, &language, expected);
        }
        let mut variable = category_rule("IVar", "Int", "Int");
        if let GrammarItem::NonTerminal { kind, .. } = &mut variable.items[0] {
            *kind = NonTerminalKind::Var;
        }
        assert_atomic_projection_baseline(
            &variable,
            &language,
            AtomicShape::VarRule { wrapper_variant: variable.label.clone() },
        );
        let keyword = terminal_rule("Keyword", "Int", "exact");
        assert_atomic_projection_baseline(
            &keyword,
            &language,
            AtomicShape::TerminalKeyword {
                terminal_text: "exact".into(),
                wrapper_variant: keyword.label.clone(),
            },
        );
        variable.items.clear();
        assert_atomic_projection_baseline(&variable, &language, AtomicShape::NonAtomic);
        variable.items = vec![GrammarItem::Terminal("a".into()), GrammarItem::Terminal("b".into())];
        assert_atomic_projection_baseline(&variable, &language, AtomicShape::NonAtomic);
    }

    #[test]
    fn atomic_projection_baseline_nullary_run_requires_all_literals() {
        let language = empty_lang();
        let mut rule = judgement_rule(
            "Empty",
            "Int",
            &[],
            vec![
                SyntaxExpr::Literal("Map".into()),
                SyntaxExpr::Literal("(".into()),
                SyntaxExpr::Literal(")".into()),
            ],
        );
        // Legacy items must not replace a rejected judgement shape.
        rule.items = vec![GrammarItem::Terminal("legacy".into())];
        assert_atomic_projection_baseline(
            &rule,
            &language,
            AtomicShape::NullaryLiteralRun {
                trigger: "Map".into(),
                trailing_literals: vec!["(".into(), ")".into()],
                wrapper_variant: rule.label.clone(),
            },
        );
        for position in 0..3 {
            let mut unsupported = rule.clone();
            unsupported
                .syntax_pattern
                .as_mut()
                .expect("baseline fixture contains this declared field")[position] =
                SyntaxExpr::TokenKind {
                    name: Ident::new("Ident", Span::call_site()),
                    bind: None,
                };
            assert_atomic_projection_baseline(&unsupported, &language, AtomicShape::NonAtomic);
        }
        rule.term_context = Some(vec![TermParam::GuardBody {
            name: Ident::new("guard", Span::call_site()),
        }]);
        assert_atomic_projection_baseline(&rule, &language, AtomicShape::NonAtomic);
    }

    #[test]
    fn atomic_projection_baseline_ident_guard_is_prefix_only() {
        let language = empty_lang();
        let mut rule = judgement_rule(
            "Tagged",
            "Int",
            &[("name", "Ident")],
            vec![
                SyntaxExpr::Literal("tag".into()),
                SyntaxExpr::Param(Ident::new("name", Span::call_site())),
            ],
        );
        assert_atomic_projection_baseline(&rule, &language, AtomicShape::NonAtomic);
        rule.syntax_pattern = Some(vec![SyntaxExpr::Param(Ident::new("name", Span::call_site()))]);
        assert_atomic_projection_baseline(
            &rule,
            &language,
            AtomicShape::CrossCatProjection {
                source_cat_name: "Ident".into(),
                wrapper_variant: rule.label.clone(),
            },
        );

        let cross = judgement_rule(
            "Cross",
            "Int",
            &[("value", "Other")],
            vec![
                SyntaxExpr::Literal("cast".into()),
                SyntaxExpr::Param(Ident::new("value", Span::call_site())),
            ],
        );
        assert_atomic_projection_baseline(
            &cross,
            &language,
            AtomicShape::CrossCatPrefixUnary {
                trigger: "cast".into(),
                source_cat_name: "Other".into(),
                wrapper_variant: cross.label.clone(),
            },
        );
        let mut same = judgement_rule(
            "Neg",
            "Int",
            &[("value", "Int")],
            vec![
                SyntaxExpr::Literal("-".into()),
                SyntaxExpr::Param(Ident::new("value", Span::call_site())),
            ],
        );
        assert_atomic_projection_baseline(
            &same,
            &language,
            AtomicShape::PrefixOperator {
                trigger: "-".into(),
                operand_cat_name: "Int".into(),
            },
        );
        same.syntax_pattern
            .as_mut()
            .expect("baseline fixture contains this declared field")[1] =
            SyntaxExpr::Param(Ident::new("different", Span::call_site()));
        assert_atomic_projection_baseline(&same, &language, AtomicShape::NonAtomic);
    }

    #[test]
    fn atomic_projection_baseline_literal_payload_is_unchanged() {
        let mut language = lang_with_int_literal();
        let payload =
            quote! { { let marker = "payload untouched"; user_eval::<i32>(text, marker) } };
        language.token_defs[0].rust_code = Some(payload.clone());
        let mut rule = category_rule("NotTheLiteralWrapper", "Int", "Int");
        rule.rust_code = Some(mettail_ast::types::RustCodeBlock {
            code: parse_quote! { wrong_rule_payload(text) },
        });
        assert_atomic_projection_baseline(
            &rule,
            &language,
            AtomicShape::LiteralPatterned {
                cat_name: "Int".into(),
                native_type: language.types[0]
                    .native_type
                    .clone()
                    .expect("baseline fixture contains this declared field"),
                family: LiteralFamily::Integer,
                wrapper_variant: Ident::new("NumLit", Span::call_site()),
                rust_code: payload.clone(),
            },
        );
        assert_eq!(
            language.token_defs[0]
                .rust_code
                .as_ref()
                .expect("baseline fixture contains this declared field")
                .to_string(),
            payload.to_string()
        );
        let cross = category_rule("Cross", "Other", "Int");
        assert_atomic_projection_baseline(&cross, &language, AtomicShape::NonAtomic);
    }

    #[test]
    fn atomic_projection_baseline_native_default_and_custom_election() {
        let mut language = lang_with_int_literal();
        language.token_defs[0].rust_code = None;
        let rule = category_rule("Literal", "Int", "Int");
        let default_payload = quote! {
            mettail_prattail::parse_int_lit(text, Some(mettail_prattail::Suffix::I32))
                .map_err(|_| ())
        };
        assert_atomic_projection_baseline(
            &rule,
            &language,
            AtomicShape::LiteralPatterned {
                cat_name: "Int".into(),
                native_type: language.types[0]
                    .native_type
                    .clone()
                    .expect("baseline fixture contains this declared field"),
                family: LiteralFamily::Integer,
                wrapper_variant: Ident::new("NumLit", Span::call_site()),
                rust_code: default_payload,
            },
        );

        language.types[0].native_type = Some(parse_quote!(OpaqueCarrier));
        assert_atomic_projection_baseline(&rule, &language, AtomicShape::NonAtomic);
        let payload = quote! { decode_opaque(text) };
        language.token_defs[0].rust_code = Some(payload.clone());
        assert_atomic_projection_baseline(
            &rule,
            &language,
            AtomicShape::LiteralPatterned {
                cat_name: "Int".into(),
                native_type: language.types[0]
                    .native_type
                    .clone()
                    .expect("baseline fixture contains this declared field"),
                family: LiteralFamily::Custom,
                wrapper_variant: Ident::new("Lit", Span::call_site()),
                rust_code: payload,
            },
        );
        language.token_defs[0].from_literals = false;
        assert_atomic_projection_baseline(&rule, &language, AtomicShape::NonAtomic);
        language.token_defs[0].from_literals = true;
        language.types[0].native_type = None;
        assert_atomic_projection_baseline(&rule, &language, AtomicShape::NonAtomic);
    }

    #[test]
    fn atomic_projection_baseline_uses_first_eligible_literal_payload() {
        let mut language = lang_with_int_literal();
        let mut ineligible = language.token_defs[0].clone();
        ineligible.rust_code = None;
        language.token_defs.insert(0, ineligible);
        let first = quote! { first_eligible(text) };
        language.token_defs[1].rust_code = Some(first.clone());
        let mut later = language.token_defs[1].clone();
        later.rust_code = Some(quote! { later_must_not_win(text) });
        language.token_defs.push(later);
        let rule = category_rule("Literal", "Int", "Int");
        assert_atomic_projection_baseline(
            &rule,
            &language,
            AtomicShape::LiteralPatterned {
                cat_name: "Int".into(),
                native_type: language.types[0]
                    .native_type
                    .clone()
                    .expect("baseline fixture contains this declared field"),
                family: LiteralFamily::Integer,
                wrapper_variant: Ident::new("NumLit", Span::call_site()),
                rust_code: first,
            },
        );
    }

    #[test]
    fn default_string_action_uses_the_shared_left_to_right_decoder() {
        let generated = default_eval_body_for_native_kind(&NativeKind::Str)
            .expect("String has a generated native action")
            .to_string();
        assert!(generated.contains("decode_double_quoted_string_literal"));
        assert!(!generated.contains("replace"));
    }

    #[test]
    fn first_set_includes_leading_structural_capture_terminals() {
        let mut lang = empty_lang();
        lang.types.push(LangType {
            name: Ident::new("Captured", Span::call_site()),
            role: CategoryRole::Data,
            native_type: None,
            collection_kind: None,
        });
        lang.types.push(LangType {
            name: Ident::new("Guest", Span::call_site()),
            role: CategoryRole::Data,
            native_type: None,
            collection_kind: None,
        });
        lang.terms.push(judgement_rule(
            "CapturedIdent",
            "Captured",
            &[],
            vec![SyntaxExpr::TokenKind {
                name: Ident::new("Ident", Span::call_site()),
                bind: Some(Ident::new("name", Span::call_site())),
            }],
        ));
        lang.terms.push(judgement_rule(
            "GuestRegion",
            "Guest",
            &[],
            vec![SyntaxExpr::GuestBody {
                open: Ident::new("GuestOpen", Span::call_site()),
                close: Ident::new("GuestClose", Span::call_site()),
                bind: Ident::new("body", Span::call_site()),
                kind: DelimitedRegionKind::Flt,
            }],
        ));

        let captured = first_set_of_category("Captured", &lang);
        assert_eq!(captured.len(), 1, "closed data category has one declared FIRST terminal");
        let captured_pattern = captured[0].pattern.to_string();
        let captured_guard = captured[0]
            .extra_guard
            .as_ref()
            .expect("named token capture has a family guard")
            .to_string();
        assert!(captured_pattern.contains("ref __kind"), "{captured_pattern}");
        assert!(captured_guard.contains("token_kind_matches_capture_name"), "{captured_guard}");
        assert!(captured_guard.contains("\"Ident\""), "{captured_guard}");
        assert!(!captured[0].is_var_contribution);

        let guest = first_set_of_category("Guest", &lang);
        assert_eq!(guest.len(), 1, "closed data category has one declared FIRST terminal");
        let guest_pattern = guest[0].pattern.to_string();
        let guest_guard = guest[0]
            .extra_guard
            .as_ref()
            .expect("guest-body opener has a kind guard")
            .to_string();
        assert!(guest_pattern.contains("TokenKind :: Custom"), "{guest_pattern}");
        assert!(guest_guard.contains("\"GuestOpen\""), "{guest_guard}");
        assert!(!guest[0].is_var_contribution);
    }

    #[test]
    fn ident_first_seed_excludes_closed_data_categories() {
        let mut lang = empty_lang();
        lang.types.push(LangType {
            name: Ident::new("Open", Span::call_site()),
            role: CategoryRole::Object,
            native_type: None,
            collection_kind: None,
        });
        lang.types.push(LangType {
            name: Ident::new("Closed", Span::call_site()),
            role: CategoryRole::Data,
            native_type: None,
            collection_kind: None,
        });

        let ident_first = ident_first_categories(&lang);
        assert!(ident_first.contains("Open"));
        assert!(!ident_first.contains("Closed"));
        assert!(result_has_home_var_reading("Open", &lang));
        assert!(!result_has_home_var_reading("Closed", &lang));

        let open_first = first_set_of_category("Open", &lang);
        assert_eq!(open_first.len(), 1);
        assert!(open_first[0].is_var_contribution);
        assert!(first_set_of_category("Closed", &lang).is_empty());
    }

    #[test]
    fn cross_category_paren_dispatch_preserves_source_rules() {
        let mut lang = empty_lang();
        for name in ["Equation", "Ast"] {
            lang.types.push(LangType {
                name: Ident::new(name, Span::call_site()),
                role: CategoryRole::Data,
                native_type: None,
                collection_kind: None,
            });
        }

        let equation = judgement_rule(
            "Equation",
            "Equation",
            &[("left", "Ast"), ("right", "Ast")],
            vec![
                SyntaxExpr::Param(Ident::new("left", Span::call_site())),
                SyntaxExpr::Literal("==".into()),
                SyntaxExpr::Param(Ident::new("right", Span::call_site())),
            ],
        );
        let sexp = judgement_rule(
            "SExp",
            "Ast",
            &[("body", "Ast")],
            vec![
                SyntaxExpr::Literal("(".into()),
                SyntaxExpr::Param(Ident::new("body", Span::call_site())),
                SyntaxExpr::Literal(")".into()),
            ],
        );
        lang.terms.extend([equation.clone(), sexp.clone()]);

        let categories = vec!["Equation".to_string(), "Ast".to_string()];
        let per_cat = vec![vec![equation], vec![sexp]];
        let mut fork_rows = super::super::fork_emission::ForkEmissionOrdinalModel::new();
        let emitted =
            emit_paren_dispatch_arms(&categories, &lang, &per_cat, &mut fork_rows).to_string();

        assert!(
            emitted.contains("StackSymbolV2 :: category_entry (1u16)"),
            "the Equation dispatch must retain Ast's source continuation: {emitted}"
        );
        assert!(
            emitted.contains("paren_binder_branch (1u16 , 0u16 , 1u16 , _outer_bp"),
            "the delegated branch must select the source rule identity: {emitted}"
        );
        assert!(
            emitted.contains("BP_TIER_CROSSCAT_LHS"),
            "the delegated rule must carry its cross-category transition cost: {emitted}"
        );
        assert!(
            emitted.contains("wpda_transitions :: prefix :: paren_fork"),
            "heterogeneous paren branches must use branch-local consumption: {emitted}"
        );
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
        // is two-or-more consecutive literals (e.g. Rholang's
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
        let (arms, __ts_helpers) = emit_prefix_arms_for_category(
            &lang,
            0,
            "Int",
            &[],
            &std::collections::HashMap::new(),
            &std::collections::HashMap::new(),
            &mut super::super::fork_emission::ForkEmissionOrdinalModel::new(),
        );
        // Task #15 peel: combine arms + helpers (both empty for no rules).
        let mut ts: TokenStream = arms.into_iter().collect();
        ts.extend(__ts_helpers);
        assert!(ts.to_string().trim().is_empty());
    }

    #[test]
    fn atomic_integer_rule_emits_an_arm() {
        let lang = empty_lang();
        let rule = atomic_rule("IntLit", "Int", NonTerminalKind::Integer);
        let (arms, __ts_helpers) = emit_prefix_arms_for_category(
            &lang,
            2,
            "Int",
            &[(0, &rule)],
            &std::collections::HashMap::new(),
            &std::collections::HashMap::new(),
            &mut super::super::fork_emission::ForkEmissionOrdinalModel::new(),
        );
        // Task #15 peel: assert over arms + helpers combined (bodies moved).
        let mut ts: TokenStream = arms.into_iter().collect();
        ts.extend(__ts_helpers);
        let s = ts.to_string();
        assert!(s.contains("singleton_atomic (_outer_bp , 2u16 , 0u16 , lex_w"));
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
        let (arms, __ts_helpers) = emit_prefix_arms_for_category(
            &lang,
            2,
            "Int",
            &[(0, &rule)],
            &std::collections::HashMap::new(),
            &std::collections::HashMap::new(),
            &mut super::super::fork_emission::ForkEmissionOrdinalModel::new(),
        );
        // Task #15 peel: assert over arms + helpers combined (bodies moved).
        let mut ts: TokenStream = arms.into_iter().collect();
        ts.extend(__ts_helpers);
        let s = ts.to_string();
        assert!(s.contains("singleton_atomic (_outer_bp , 2u16 , 0u16 , lex_w"));
        assert!(s.contains("Fixed"));
        assert!(s.contains("\"error\""));
        assert!(s.contains("2u16"));
    }

    #[test]
    fn literal_patterned_int_emits_integer_lit_guard() {
        let lang = lang_with_int_literal();
        let rule = category_rule("IntLit", "Int", "Int");
        let (arms, __ts_helpers) = emit_prefix_arms_for_category(
            &lang,
            2,
            "Int",
            &[(0, &rule)],
            &std::collections::HashMap::new(),
            &std::collections::HashMap::new(),
            &mut super::super::fork_emission::ForkEmissionOrdinalModel::new(),
        );
        // Task #15 peel: assert over arms + helpers combined (bodies moved).
        let mut ts: TokenStream = arms.into_iter().collect();
        ts.extend(__ts_helpers);
        let s = ts.to_string();
        assert!(s.contains("singleton_atomic (_outer_bp , 2u16 , 0u16 , lex_w"));
        assert!(s.contains("IntegerLit"));
        assert!(s.contains("\"Int\""));
        assert!(s.contains("2u16"));
    }

    #[test]
    fn same_category_led_rule_is_excluded_from_prefix_dispatch() {
        let atom = terminal_rule("Atom", "Expr", "a");
        let par = judgement_rule(
            "Par",
            "Expr",
            &[("left", "Expr"), ("right", "Expr")],
            vec![
                SyntaxExpr::Param(Ident::new("left", Span::call_site())),
                SyntaxExpr::Literal("|".into()),
                SyntaxExpr::Param(Ident::new("right", Span::call_site())),
            ],
        );
        let mut lang = empty_lang();
        lang.terms = vec![atom.clone(), par.clone()];
        let bp_table = super::super::infix::build_bp_table(&lang);
        assert_eq!(same_category_led_left_bp(&par, "Expr", &bp_table), Some(2));

        let (arms, helpers) = emit_prefix_arms_for_category(
            &lang,
            0,
            "Expr",
            &[(0, &atom), (1, &par)],
            &std::collections::HashMap::new(),
            &std::collections::HashMap::new(),
            &mut super::super::fork_emission::ForkEmissionOrdinalModel::new(),
        );
        let mut emitted: TokenStream = arms.into_iter().collect();
        emitted.extend(helpers);
        let emitted = emitted.to_string();
        assert!(
            !emitted.contains("singleton_leading_category")
                && !emitted.contains("push_leading_category"),
            "same-category led rule leaked into generic prefix descent: {emitted}",
        );
    }

    #[test]
    fn cross_category_closed_prefix_seed_does_not_consume_the_result_floor() {
        let name_atom = terminal_rule("NameAtom", "Name", "n");
        let proc_atom = terminal_rule("ProcAtom", "Proc", "p");
        let send = judgement_rule(
            "Send",
            "Proc",
            &[("name", "Name"), ("body", "Proc")],
            vec![
                SyntaxExpr::Param(Ident::new("name", Span::call_site())),
                SyntaxExpr::Literal("!".into()),
                SyntaxExpr::Literal("(".into()),
                SyntaxExpr::Param(Ident::new("body", Span::call_site())),
                SyntaxExpr::Literal(")".into()),
            ],
        );
        let mut lang = empty_lang();
        lang.terms = vec![name_atom, proc_atom, send.clone()];
        let bp_table = super::super::infix::build_bp_table(&lang);
        assert_eq!(same_category_led_left_bp(&send, "Proc", &bp_table), None);
    }

    #[test]
    fn prefix_operator_and_projection_share_one_ambiguity_bucket() {
        let mut lang = empty_lang();
        lang.types.push(LangType {
            name: Ident::new("UInt32", Span::call_site()),
            role: CategoryRole::Object,
            native_type: Some(parse_quote!(u32)),
            collection_kind: None,
        });
        lang.types.push(LangType {
            name: Ident::new("Bool", Span::call_site()),
            role: CategoryRole::Object,
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
        let (arms, __ts_helpers) = emit_prefix_arms_for_category(
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
        // Combine the static arms and helpers to check the shared transition
        // calls and their original source identities.
        // The guard (with `__kw == "bitnot"`) stays in the arm, so its
        // single-occurrence count is unchanged.
        let mut ts: TokenStream = arms.into_iter().collect();
        ts.extend(__ts_helpers);
        let s = ts.to_string();
        let guard = "__kw == \"bitnot\" && state_cat_src_idx == 0u16";
        assert_eq!(
            s.matches(guard).count(),
            1,
            "same fixed-token evidence must emit one arm, not first-match shadow arms: {s}"
        );
        assert!(s.contains("wpda_transitions :: prefix :: unified_fork"), "{s}");
        assert!(
            s.contains(
                "push_binder_prefix (__pd_branches , _outer_bp , 0u16 , 0u16 , 0u16 , lex_w"
            ),
            "the direct-prefix branch must retain its rule and body identities: {s}"
        );
        assert!(
            s.contains("push_crosscat_projection (__pd_branches , _outer_bp , cur_bp , 0u16 , 1u16 , 1u16 , lex_w"),
            "{s}"
        );
    }
}
