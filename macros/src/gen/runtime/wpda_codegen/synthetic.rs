//! Synthetic grammar rules for implicit atomic literals.
//!
//! Calculator / Rholang / other grammars do NOT write explicit
//! `IntLit . i:Int |- i : Int` rules in their `terms { }` block —
//! the atomic-literal variant (`Int::NumLit(i32)`, `Bool::BoolLit(bool)`,
//! `Str::StringLit(String)`, etc.) is **synthesized** by
//! `macros/src/gen/types/enums.rs` directly from each `LangType.native_type`.
//!
//! To parse these implicit atomic literals via WPDS, this module fabricates
//! corresponding `GrammarRule` entries — one per category with a
//! `from_literals` `TokenDef`. The fabricated rule's shape makes it classify
//! as `AtomicShape::LiteralPatterned` in `prefix.rs::classify_atomic`.
//!
//! Synthetic rules receive stable `rule_idx` values that appear in the
//! emitted `WPDA_RULES` table alongside user-written rules. Callers
//! (`emit_rule_table`, `emit_prefix_arms_for_category`, `emit_action_for_body`)
//! consume the combined `user + synthetic` list so every downstream emission
//! stays consistent.

use mettail_ast::grammar::{GrammarItem, GrammarRule, NonTerminalKind};
#[cfg(test)]
use mettail_ast::language::CollectionCategory;
use mettail_ast::language::LanguageDef;
use mettail_ast::types::CollectionType;
use proc_macro2::Span;
use quote::format_ident;
use syn::Ident;

/// Build the full rule set per category, combining user-written rules from
/// `language.terms` with synthetic literal-patterned rules derived from
/// `language.token_defs`.
///
/// Returned `Vec<Vec<GrammarRule>>` is indexed by `categories` source-index.
/// Synthetic rules are appended after user rules so their `rule_idx` values
/// are `len(user_rules_in_cat) + k`.
pub(crate) fn build_per_category_rules(
    language: &LanguageDef,
    categories: &[String],
) -> Vec<Vec<GrammarRule>> {
    use mettail_prattail::wpda_rule_analysis::synthetic::{
        build_per_category_rules as build_shared_rules, TypeInput, UserInput,
    };
    let users: Vec<_> = language
        .terms
        .iter()
        .map(|rule| UserInput {
            category: rule.category.to_string(),
            source: rule,
        })
        .collect();
    let types: Vec<_> = language
        .types
        .iter()
        .map(|ty| TypeInput {
            name: ty.name.to_string(),
            is_data: ty.is_data(),
            has_native: ty.native_type.is_some(),
            has_collection: ty.collection_kind.is_some(),
            source: ty,
        })
        .collect();
    let mut adapter = MacroSynthesisAdapter { language };
    let derived = build_shared_rules(categories, &users, &types, CollectionType::Vec, &mut adapter);
    // Retain the original harmless macro expansion at the same final phase.
    let _ = format_ident!("_unused");
    derived
}

/// Only source-specific observations and original operations live here.
/// Eligibility, order and complete synthetic shapes come from the shared driver.
struct MacroSynthesisAdapter<'a> {
    language: &'a LanguageDef,
}

impl mettail_prattail::wpda_rule_analysis::synthetic::SynthesisAdapter
    for MacroSynthesisAdapter<'_>
{
    type SourceUser = GrammarRule;
    type SourceType = mettail_ast::language::LangType;
    type RulePayload = GrammarRule;
    type CollectionKind = CollectionType;

    fn clone_user(&mut self, rule: &GrammarRule) -> GrammarRule {
        rule.clone()
    }

    fn normalize_user(&mut self, rule: &mut GrammarRule) {
        mettail_ast::grammar::convert_items_to_term_context(rule);
    }

    fn first_item_is_var(&mut self, rule: &GrammarRule) -> bool {
        rule.items
            .first()
            .map(|item| matches!(item, GrammarItem::NonTerminal { kind: NonTerminalKind::Var, .. }))
            .unwrap_or(false)
    }

    fn materialize_synthetic(
        &mut self,
        rule: mettail_prattail::wpda_rule_analysis::synthetic::SyntheticRule<CollectionType>,
    ) -> GrammarRule {
        materialize_synthetic_rule(rule)
    }

    fn has_literal_block(&mut self, ty: &Self::SourceType) -> bool {
        let cat_name = ty.name.to_string();
        self.language.token_defs.iter().any(|td| {
            td.from_literals
                && td
                    .category
                    .as_ref()
                    .map(|c| c.to_string() == cat_name)
                    .unwrap_or(false)
        })
    }

    fn literal_label(&mut self, ty: &Self::SourceType) -> String {
        crate::gen::generate_literal_label(
            ty.native_type
                .as_ref()
                .expect("native_type checked by shared synthesis gate"),
        )
        .to_string()
    }

    fn collection(
        &mut self,
        ty: &Self::SourceType,
    ) -> mettail_prattail::wpda_rule_analysis::synthetic::CollectionRecipe<CollectionType> {
        use mettail_prattail::wpda_rule_analysis::synthetic::CollectionRecipe;
        let coll_kind = ty
            .collection_kind
            .as_ref()
            .expect("collection_kind checked by shared synthesis gate");
        let d = coll_kind.delimiters();
        let kind = coll_kind.coll_type();
        let label = mettail_grammar_core::collection_declaration::declared_collection_literal_label(
            super::authored_capture::collection_kind(&kind),
        );
        let (open, close, separator) = (d.open.clone(), d.close.clone(), d.sep.clone());
        let element_category = self
            .language
            .collection_element_type_for_category(&ty.name)
            .map(|i| i.to_string())
            .unwrap_or_else(|| ty.name.to_string());
        CollectionRecipe {
            kind,
            label: label.to_string(),
            element_category,
            open,
            close,
            separator,
        }
    }

    fn var_label(&mut self, ty: &Self::SourceType) -> String {
        crate::gen::generate_var_label(&ty.name).to_string()
    }

    fn declares_binder(&mut self) -> bool {
        mettail_ast::grammar_shapes::declares_binder(self.language)
    }
}

/// Materialize only the bounded shapes synthesized by the original algorithm.
/// User rules never pass through this function; their entire original metadata
/// stays in the owned payload. Runtime adapters consume recipes without syn.
fn materialize_synthetic_rule(
    rule: mettail_prattail::wpda_rule_analysis::synthetic::SyntheticRule<CollectionType>,
) -> GrammarRule {
    use mettail_ast::grammar::{PatternOp, SyntaxExpr, TermParam};
    use mettail_ast::types::TypeExpr;
    use mettail_prattail::wpda_rule_analysis::{
        atomic::{LegacyAtomicItem, LegacyAtomicKind},
        synthetic::{SyntheticParam, SyntheticType},
        InfixSyntaxShape,
    };
    let ident = |name: &str| Ident::new(name, Span::call_site());
    let materialize_type = |ty| match ty {
        SyntheticType::Base(name) => TypeExpr::Base(ident(&name)),
        SyntheticType::Collection { kind, element } => TypeExpr::Collection {
            coll_type: kind,
            element: Box::new(TypeExpr::Base(ident(&element))),
        },
    };
    // Original synthesis validates the category/domain before derived labels.
    // Native and Var label helpers have already run at their original sites.
    // Generated parameter names are fixed; Lam's domain equals its home category.
    let category = ident(&rule.category);
    let term_context = rule.term_context.map(|params| {
        params
            .into_iter()
            .map(|param| match param {
                SyntheticParam::Simple { name, ty } => TermParam::Simple {
                    name: ident(&name),
                    ty: materialize_type(ty),
                },
                SyntheticParam::Abstraction { binder, body, domain, codomain } => {
                    TermParam::Abstraction {
                        binder: ident(&binder),
                        body: ident(&body),
                        ty: TypeExpr::Arrow {
                            domain: Box::new(TypeExpr::Base(ident(&domain))),
                            codomain: Box::new(TypeExpr::Base(ident(&codomain))),
                        },
                    }
                },
            })
            .collect()
    });
    let label = ident(&rule.label);
    GrammarRule {
        label,
        category,
        items: rule
            .items
            .into_iter()
            .map(|item| match item {
                LegacyAtomicItem::Terminal(text) => GrammarItem::Terminal(text),
                LegacyAtomicItem::NonTerminal { kind, ident: name } => GrammarItem::NonTerminal {
                    ident: ident(&name),
                    kind: match kind {
                        LegacyAtomicKind::Integer => NonTerminalKind::Integer,
                        LegacyAtomicKind::Boolean => NonTerminalKind::Boolean,
                        LegacyAtomicKind::StringLiteral => NonTerminalKind::StringLiteral,
                        LegacyAtomicKind::FloatLiteral => NonTerminalKind::FloatLiteral,
                        LegacyAtomicKind::Var => NonTerminalKind::Var,
                        LegacyAtomicKind::Ident => NonTerminalKind::Ident,
                        LegacyAtomicKind::Category => NonTerminalKind::Category,
                    },
                },
                LegacyAtomicItem::Other => {
                    unreachable!("original synthesis emits no unsupported legacy item")
                },
            })
            .collect(),
        bindings: Vec::new(),
        term_context,
        syntax_pattern: rule.syntax_pattern.map(|syntax| {
            syntax
                .into_iter()
                .map(|item| match item {
                    InfixSyntaxShape::Literal(text) => SyntaxExpr::Literal(text),
                    InfixSyntaxShape::Param(name) => SyntaxExpr::Param(ident(&name)),
                    InfixSyntaxShape::Sep { collection, separator } => {
                        SyntaxExpr::Op(PatternOp::Sep {
                            collection: ident(&collection),
                            separator,
                            source: None,
                        })
                    },
                    InfixSyntaxShape::Other => {
                        unreachable!("original synthesis emits no unsupported syntax")
                    },
                })
                .collect()
        }),
        rust_code: None,
        eval_mode: None,
        is_right_assoc: false,
        shares_level_with_previous: false,
        prefix_bp: None,
        tier_directive: None,
        is_auto_injected: false,
        doc_comment: None,
        is_canonical_synonym: false,
    }
}

#[cfg(test)]
mod tests {
    include!("../../../../tests/support/owned_synthesis_reuse.rs");

    use super::*;
    use mettail_ast::grammar::{rule_fixture, PatternOp, SyntaxExpr, TermParam};
    use mettail_ast::language::{CategoryRole, CollectionDelimiters, LangType, TokenDef};
    use mettail_ast::types::TypeExpr;
    use proc_macro2::Span;
    use syn::{parse_quote, Ident};

    fn lang_with_int_and_bool_literals() -> LanguageDef {
        LanguageDef {
            name: Ident::new("Test", Span::call_site()),
            options: Default::default(),
            extends_names: Vec::new(),
            include_names: Vec::new(),
            mixin_names: Vec::new(),
            types: vec![
                LangType {
                    name: Ident::new("Int", Span::call_site()),
                    role: Default::default(),
                    native_type: Some(parse_quote!(i32)),
                    collection_kind: None,
                },
                LangType {
                    name: Ident::new("Bool", Span::call_site()),
                    role: Default::default(),
                    native_type: Some(parse_quote!(bool)),
                    collection_kind: None,
                },
            ],
            refinement_types: Vec::new(),
            token_defs: vec![
                TokenDef {
                    name: Ident::new("Integer", Span::call_site()),
                    pattern: r"[0-9]+".to_string(),
                    category: Some(Ident::new("Int", Span::call_site())),
                    rust_code: Some(quote::quote! { Ok(0i32) }),
                    priority: None,
                    push_mode: None,
                    is_pop: false,
                    stream: None,
                    from_literals: true,
                },
                TokenDef {
                    name: Ident::new("Boolean", Span::call_site()),
                    pattern: r"true|false".to_string(),
                    category: Some(Ident::new("Bool", Span::call_site())),
                    rust_code: Some(quote::quote! { Ok(false) }),
                    priority: None,
                    push_mode: None,
                    is_pop: false,
                    stream: None,
                    from_literals: true,
                },
            ],
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

    #[test]
    fn synthesizes_literal_patterned_rule_per_literal_category() {
        let lang = lang_with_int_and_bool_literals();
        let categories = vec!["Int".to_string(), "Bool".to_string()];
        let per_cat = build_per_category_rules(&lang, &categories);
        assert_eq!(per_cat.len(), 2);
        // Stage 3.20 / Commit 4 part 2 (Plan agent Fix A, 2026-05-06):
        // native-typed categories now also get a synthetic Var rule
        // (matching the unconditional `gen/types/enums.rs:113-118`
        // emission of `IVar`/`BVar` AST variants), so per_cat[i] has
        // BOTH the literal-patterned rule AND the synthetic Var rule.
        // Int: literal-patterned "NumLit" + synthetic Var "IVar".
        assert_eq!(per_cat[0].len(), 2);
        assert_eq!(per_cat[0][0].label.to_string(), "NumLit");
        assert_eq!(per_cat[0][0].category.to_string(), "Int");
        assert_eq!(per_cat[0][1].label.to_string(), "IVar");
        // Bool: literal-patterned "BoolLit" + synthetic Var "BVar".
        assert_eq!(per_cat[1].len(), 2);
        assert_eq!(per_cat[1][0].label.to_string(), "BoolLit");
        assert_eq!(per_cat[1][1].label.to_string(), "BVar");
    }

    #[test]
    fn synthesizes_for_native_type_without_literal_block() {
        // Stage 4 fix: categories with `native_type` are synthesized
        // regardless of whether they have a `from_literals` TokenDef.
        // Cross-cat projection rules referring to these as source
        // categories need a parseable target — without synthesis, the
        // cross-cat dispatch falls back to recursing into the result
        // category (e.g., Proc → Proc) and fails.
        //
        // Stage 3.20 / Commit 4 part 2 (Plan agent Fix A, 2026-05-06):
        // native-typed categories also get a synthetic Var rule
        // (matching the unconditional AST `IVar`/`BVar` emission).
        let mut lang = lang_with_int_and_bool_literals();
        lang.token_defs.clear(); // Remove all literal blocks.
        let categories = vec!["Int".to_string(), "Bool".to_string()];
        let per_cat = build_per_category_rules(&lang, &categories);
        // Both Int and Bool have native_type so each gets a synthetic
        // literal-patterned rule even after removing token_defs PLUS a
        // synthetic Var rule.
        assert_eq!(per_cat[0].len(), 2, "Int should have 2 synthetic rules (NumLit + IVar)");
        assert_eq!(per_cat[1].len(), 2, "Bool should have 2 synthetic rules (BoolLit + BVar)");
        assert_eq!(per_cat[0][0].label.to_string(), "NumLit");
        assert_eq!(per_cat[1][0].label.to_string(), "BoolLit");
        assert_eq!(per_cat[0][1].label.to_string(), "IVar");
        assert_eq!(per_cat[1][1].label.to_string(), "BVar");
    }

    fn synthesis_baseline_ident(name: &str) -> Ident {
        Ident::new(name, Span::call_site())
    }

    fn synthesis_baseline_user(label: &str, category: &str) -> GrammarRule {
        GrammarRule {
            items: vec![GrammarItem::Terminal(label.into())],
            ..rule_fixture(synthesis_baseline_ident(label), synthesis_baseline_ident(category))
        }
    }

    fn synthesis_baseline_labels(rules: &[GrammarRule]) -> Vec<String> {
        rules.iter().map(|rule| rule.label.to_string()).collect()
    }

    fn synthesis_baseline_collection(open: &str) -> LangType {
        LangType {
            name: synthesis_baseline_ident("Seq"),
            role: CategoryRole::Object,
            native_type: Some(parse_quote!(Vec<Int>)),
            collection_kind: Some(CollectionCategory::List(CollectionDelimiters {
                open: open.into(),
                close: "]end".into(),
                sep: ";;".into(),
                key_val_sep: None,
            })),
        }
    }

    fn synthesis_baseline_binder_language() -> LanguageDef {
        let mut language = lang_with_int_and_bool_literals();
        let binder = TermParam::Abstraction {
            binder: synthesis_baseline_ident("x"),
            body: synthesis_baseline_ident("p"),
            ty: TypeExpr::Arrow {
                domain: Box::new(TypeExpr::Base(synthesis_baseline_ident("Bool"))),
                codomain: Box::new(TypeExpr::Base(synthesis_baseline_ident("Int"))),
            },
        };
        language.terms.push(GrammarRule {
            term_context: Some(vec![binder]),
            syntax_pattern: Some(vec![
                SyntaxExpr::Literal("bind".into()),
                SyntaxExpr::Param(synthesis_baseline_ident("p")),
            ]),
            ..rule_fixture(
                synthesis_baseline_ident("DeclaredBinder"),
                synthesis_baseline_ident("Int"),
            )
        });
        language
    }

    #[test]
    fn synthesis_baseline_exact_user_literal_collection_var_phase_order() {
        let mut language = lang_with_int_and_bool_literals();
        language.types.push(synthesis_baseline_collection("seq("));
        language.terms = vec![
            synthesis_baseline_user("BoolFirst", "Bool"),
            synthesis_baseline_user("IntFirst", "Int"),
            synthesis_baseline_user("SeqFirst", "Seq"),
            synthesis_baseline_user("IntSecond", "Int"),
        ];
        let categories = vec!["Seq".into(), "Bool".into(), "Int".into()];
        let rules = build_per_category_rules(&language, &categories);
        assert_eq!(rules.len(), 3);
        assert_eq!(synthesis_baseline_labels(&rules[0]), ["SeqFirst", "ListLit", "SVar"]);
        assert_eq!(synthesis_baseline_labels(&rules[1]), ["BoolFirst", "BoolLit", "BVar"]);
        assert_eq!(
            synthesis_baseline_labels(&rules[2]),
            ["IntFirst", "IntSecond", "NumLit", "IVar"]
        );
        for (category, entries) in categories.iter().zip(&rules) {
            assert!(entries
                .iter()
                .all(|rule| rule.category.to_string() == *category));
        }
        assert_eq!(format!("{:?}", rules[2][0]), format!("{:?}", language.terms[1]));
        assert_eq!(format!("{:?}", rules[2][1]), format!("{:?}", language.terms[3]));
    }

    #[test]
    fn synthesis_baseline_explicit_first_item_var_suppresses_native_and_collection_vars() {
        let mut language = lang_with_int_and_bool_literals();
        language.types.push(synthesis_baseline_collection("["));
        for (label, category) in [("ExplicitIntVar", "Int"), ("ExplicitSeqVar", "Seq")] {
            language.terms.push(GrammarRule {
                // Suppression observes first-item kind, not arity or ident equality.
                items: vec![
                    GrammarItem::NonTerminal {
                        ident: synthesis_baseline_ident("not_the_category"),
                        kind: NonTerminalKind::Var,
                    },
                    GrammarItem::Terminal("suffix".into()),
                ],
                ..rule_fixture(synthesis_baseline_ident(label), synthesis_baseline_ident(category))
            });
        }
        language.terms.push(GrammarRule {
            items: vec![
                GrammarItem::Terminal("prefix".into()),
                GrammarItem::NonTerminal {
                    ident: synthesis_baseline_ident("Bool"),
                    kind: NonTerminalKind::Var,
                },
            ],
            ..rule_fixture(synthesis_baseline_ident("LaterVar"), synthesis_baseline_ident("Bool"))
        });
        let rules =
            build_per_category_rules(&language, &["Int".into(), "Seq".into(), "Bool".into()]);
        assert_eq!(synthesis_baseline_labels(&rules[0]), ["ExplicitIntVar", "NumLit"]);
        assert_eq!(synthesis_baseline_labels(&rules[1]), ["ExplicitSeqVar", "ListLit"]);
        assert_eq!(synthesis_baseline_labels(&rules[2]), ["LaterVar", "BoolLit", "BVar"]);
    }

    #[test]
    fn synthesis_baseline_binder_pair_order_and_one_lambda_per_home() {
        let language = synthesis_baseline_binder_language();
        let rules = build_per_category_rules(&language, &["Bool".into(), "Int".into()]);
        assert_eq!(
            synthesis_baseline_labels(&rules[0]),
            ["BoolLit", "BVar", "ApplyInt", "MApplyInt", "ApplyBool", "MApplyBool", "LamBool",]
        );
        assert_eq!(
            synthesis_baseline_labels(&rules[1]),
            [
                "DeclaredBinder",
                "NumLit",
                "IVar",
                "ApplyInt",
                "MApplyInt",
                "ApplyBool",
                "MApplyBool",
                "LamInt",
            ]
        );
        let expected_apply = GrammarRule {
            term_context: Some(vec![
                TermParam::Simple {
                    name: synthesis_baseline_ident("f"),
                    ty: TypeExpr::Base(synthesis_baseline_ident("Int")),
                },
                TermParam::Simple {
                    name: synthesis_baseline_ident("x"),
                    ty: TypeExpr::Base(synthesis_baseline_ident("Bool")),
                },
            ]),
            syntax_pattern: Some(vec![
                SyntaxExpr::Literal("$bool".into()),
                SyntaxExpr::Literal("(".into()),
                SyntaxExpr::Param(synthesis_baseline_ident("f")),
                SyntaxExpr::Literal(",".into()),
                SyntaxExpr::Param(synthesis_baseline_ident("x")),
                SyntaxExpr::Literal(")".into()),
            ]),
            ..rule_fixture(synthesis_baseline_ident("ApplyBool"), synthesis_baseline_ident("Int"))
        };
        assert_eq!(format!("{:?}", rules[1][5]), format!("{expected_apply:?}"));
        let expected_mapply = GrammarRule {
            term_context: Some(vec![
                TermParam::Simple {
                    name: synthesis_baseline_ident("f"),
                    ty: TypeExpr::Base(synthesis_baseline_ident("Int")),
                },
                TermParam::Simple {
                    name: synthesis_baseline_ident("xs"),
                    ty: TypeExpr::Collection {
                        coll_type: CollectionType::Vec,
                        element: Box::new(TypeExpr::Base(synthesis_baseline_ident("Bool"))),
                    },
                },
            ]),
            syntax_pattern: Some(vec![
                SyntaxExpr::Literal("$$bool(".into()),
                SyntaxExpr::Param(synthesis_baseline_ident("f")),
                SyntaxExpr::Literal(",".into()),
                SyntaxExpr::Op(PatternOp::Sep {
                    collection: synthesis_baseline_ident("xs"),
                    separator: ",".into(),
                    source: None,
                }),
                SyntaxExpr::Literal(")".into()),
            ]),
            ..rule_fixture(synthesis_baseline_ident("MApplyBool"), synthesis_baseline_ident("Int"))
        };
        assert_eq!(format!("{:?}", rules[1][6]), format!("{expected_mapply:?}"));
        let expected_lam = GrammarRule {
            term_context: Some(vec![TermParam::Abstraction {
                binder: synthesis_baseline_ident("x"),
                body: synthesis_baseline_ident("p"),
                ty: TypeExpr::Arrow {
                    domain: Box::new(TypeExpr::Base(synthesis_baseline_ident("Int"))),
                    codomain: Box::new(TypeExpr::Base(synthesis_baseline_ident("Int"))),
                },
            }]),
            syntax_pattern: Some(vec![
                SyntaxExpr::Literal("^".into()),
                SyntaxExpr::Param(synthesis_baseline_ident("x")),
                SyntaxExpr::Literal(".".into()),
                SyntaxExpr::Literal("{".into()),
                SyntaxExpr::Param(synthesis_baseline_ident("p")),
                SyntaxExpr::Literal("}".into()),
            ]),
            ..rule_fixture(synthesis_baseline_ident("LamInt"), synthesis_baseline_ident("Int"))
        };
        assert_eq!(format!("{:?}", rules[1][7]), format!("{expected_lam:?}"));
    }

    #[test]
    fn synthesis_baseline_data_categories_keep_only_declared_rules() {
        let mut language = synthesis_baseline_binder_language();
        language.types[1].role = CategoryRole::Data;
        let mut collection = synthesis_baseline_collection("seq(");
        collection.role = CategoryRole::Data;
        language.types.push(collection);
        language
            .terms
            .push(synthesis_baseline_user("ClosedBool", "Bool"));
        language
            .terms
            .push(synthesis_baseline_user("ClosedSeq", "Seq"));
        let rules =
            build_per_category_rules(&language, &["Int".into(), "Bool".into(), "Seq".into()]);
        assert_eq!(
            synthesis_baseline_labels(&rules[0]),
            ["DeclaredBinder", "NumLit", "IVar", "ApplyInt", "MApplyInt", "LamInt",]
        );
        assert_eq!(synthesis_baseline_labels(&rules[1]), ["ClosedBool"]);
        assert_eq!(synthesis_baseline_labels(&rules[2]), ["ClosedSeq"]);
    }

    #[test]
    fn synthesis_baseline_duplicate_and_missing_parse_categories() {
        let language = synthesis_baseline_binder_language();
        let duplicate =
            build_per_category_rules(&language, &["Int".into(), "Bool".into(), "Int".into()]);
        assert!(duplicate[0].is_empty(), "the original category map chooses the last duplicate");
        assert_eq!(
            synthesis_baseline_labels(&duplicate[2]),
            [
                "DeclaredBinder",
                "NumLit",
                "IVar",
                "ApplyInt",
                "MApplyInt",
                "ApplyBool",
                "MApplyBool",
                "LamInt",
            ]
        );
        let missing = build_per_category_rules(&language, &["Int".into(), "Unknown".into()]);
        assert!(missing[1].is_empty());
        // Missing Bool home does not remove Bool from the declared-domain loop.
        assert_eq!(
            synthesis_baseline_labels(&missing[0]),
            [
                "DeclaredBinder",
                "NumLit",
                "IVar",
                "ApplyInt",
                "MApplyInt",
                "ApplyBool",
                "MApplyBool",
                "LamInt",
            ]
        );
        assert!(build_per_category_rules(&language, &[]).is_empty());
    }

    #[test]
    fn synthesis_baseline_duplicate_declarations_keep_two_binder_passes() {
        let mut language = synthesis_baseline_binder_language();
        language.types.push(language.types[0].clone());
        let rules = build_per_category_rules(&language, &["Int".into(), "Bool".into()]);
        assert_eq!(
            synthesis_baseline_labels(&rules[0]),
            [
                "DeclaredBinder", "NumLit", "NumLit", "IVar",
                "ApplyInt", "MApplyInt", "ApplyBool", "MApplyBool", "ApplyInt", "MApplyInt",
                "ApplyInt", "MApplyInt", "ApplyBool", "MApplyBool", "ApplyInt", "MApplyInt",
                "LamInt", "LamInt",
            ],
            "duplicate type visits append literals and application pairs, suppress the second Var, and defer both lambdas to the final pass",
        );
        assert_eq!(
            synthesis_baseline_labels(&rules[1]),
            [
                "BoolLit",
                "BVar",
                "ApplyInt",
                "MApplyInt",
                "ApplyBool",
                "MApplyBool",
                "ApplyInt",
                "MApplyInt",
                "LamBool"
            ],
        );
    }

    #[test]
    fn synthesis_original_invalid_name_order_follows_declarations_not_output_buckets() {
        // Observe the original rejection in a child: this checks first-error
        // ordering without depending on the compiler backend's unwind support.
        const CHILD: &str = "METTAIL_SYNTHESIS_INVALID_NAME_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let output = std::process::Command::new(
                std::env::current_exe().expect("the test executable has a path"),
            )
            .args([
                "--exact",
                "gen::runtime::wpda_codegen::synthetic::tests::synthesis_original_invalid_name_order_follows_declarations_not_output_buckets",
                "--nocapture",
                "--test-threads=1",
            ])
            .env(CHILD, "1")
            .output()
            .expect("run the isolated invalid-name synthesis test");
            assert!(!output.status.success(), "raw category spellings must be rejected");
            let diagnostic = String::from_utf8_lossy(&output.stderr);
            assert!(
                diagnostic.contains("\"r#type\" is not a valid Ident"),
                "original native synthesis visits declarations before output buckets: {diagnostic}",
            );
            assert!(!diagnostic.contains("\"r#match\" is not a valid Ident"));
            return;
        }
        let mut language = lang_with_int_and_bool_literals();
        language.types[0].name = Ident::new_raw("type", Span::call_site());
        language.types[1].name = Ident::new_raw("match", Span::call_site());
        build_per_category_rules(&language, &["r#match".into(), "r#type".into()]);
    }

    #[test]
    fn synthesis_baseline_collection_trims_all_trailing_opens_but_splits_once() {
        for (open, expected_prefix) in [
            ("[", vec!["["]),
            ("seq(", vec!["seq", "("]),
            ("seq(((", vec!["seq", "("]),
            ("(", vec!["", "("]),
            ("", vec![""]),
            ("seq(x(", vec!["seq(x", "("]),
        ] {
            let mut language = lang_with_int_and_bool_literals();
            language.types.push(synthesis_baseline_collection(open));
            let rules = build_per_category_rules(&language, &["Seq".into()]);
            assert_eq!(synthesis_baseline_labels(&rules[0]), ["ListLit", "SVar"]);
            let mut syntax: Vec<SyntaxExpr> = expected_prefix
                .into_iter()
                .map(|text| SyntaxExpr::Literal(text.into()))
                .collect();
            syntax.push(SyntaxExpr::Op(PatternOp::Sep {
                collection: synthesis_baseline_ident("elems"),
                separator: ";;".into(),
                source: None,
            }));
            syntax.push(SyntaxExpr::Literal("]end".into()));
            let expected = GrammarRule {
                term_context: Some(vec![TermParam::Simple {
                    name: synthesis_baseline_ident("elems"),
                    ty: TypeExpr::Collection {
                        coll_type: CollectionType::Vec,
                        element: Box::new(TypeExpr::Base(synthesis_baseline_ident("Int"))),
                    },
                }]),
                syntax_pattern: Some(syntax),
                ..rule_fixture(synthesis_baseline_ident("ListLit"), synthesis_baseline_ident("Seq"))
            };
            assert_eq!(format!("{:?}", rules[0][0]), format!("{expected:?}"), "open={open:?}");
        }
        // No native element descriptor uses the original category-name fallback.
        let mut language = lang_with_int_and_bool_literals();
        let mut category = synthesis_baseline_collection("[");
        category.native_type = None;
        language.types.push(category);
        let rules = build_per_category_rules(&language, &["Seq".into()]);
        let context = rules[0][0]
            .term_context
            .as_ref()
            .expect("collection has explicit context");
        match &context[0] {
            TermParam::Simple {
                ty: TypeExpr::Collection { element, .. }, ..
            } => {
                assert!(matches!(element.as_ref(), TypeExpr::Base(name) if name == "Seq"));
            },
            _ => panic!("expected the original single collection parameter"),
        }
    }
}
