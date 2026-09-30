//! Whole-walker parity on a complete original object-category routing domain.
//! The grammar is captured by the real macro, not reconstructed by the adapter.

use mettail_grammar_core as core;
use mettail_prattail::runtime_backend::{
    compile_parser_image, RUNTIME_COMPILER_ABI, RUNTIME_UNICODE_ABI,
};
use mettail_prattail::wpda_owned::absorption::derive_absorption_rows;
use mettail_prattail::wpda_owned::actions::{OwnedActionProvider, OwnedTerm};
use mettail_prattail::wpda_owned::engine::{AbsorptionRows, OwnedWpdaEngine};
use mettail_prattail::wpda_owned::source::{OwnedTokenSource, SourceAdapterLimits};
use mettail_prattail::wpda_rule_analysis::authored_descriptors::{
    derive_authored_descriptors, DescriptorOptions,
};
use mettail_prattail::wpda_rule_analysis::authored_synthesis::derive_authored_rules;
use mettail_prattail::wpda_runtime::WpdaResolveResult;
use mettail_prattail::wpda_walker::{RealizeRequestMode, WpdaWalker};
use mettail_runtime::Language;
use std::convert::Infallible;

mod fixture {
    mettail_macros::language! {
        name: OwnedEngineParity,
        options { emit_tests: false, emit_simulator: false, emit_blockly: false },
        types { Expr },
        terms {
            A . |- "A" : Expr;
            B . |- "B" : Expr;
            Wrap . a:Expr |- "w" "(" a ")" : Expr;
            Pair . a:Expr, b:Expr |- "pair" "(" a "," b ")" : Expr;
            Add . a:Expr, b:Expr |- a "+" b : Expr;
            Star . a:Expr |- a "*" : Expr;
            Choose . c:Expr, t:Expr, e:Expr |- c "?" t ":" e : Expr;
            Group . a:Expr |- "(" a ")" : Expr;
        },
        equations {},
        rewrites {},
    }
}

mod native_scalar_fixture {
    mettail_macros::language! {
        name: GeneratedNativeScalar,
        options { emit_tests: false, emit_simulator: false, emit_blockly: false },
        types { Pattern ![String] as Scalar },
        literals {
            Scalar {
                pattern: r"[A-Za-z0-9\u{80}-\u{10FFFF}]";
                eval: ![ { Ok::<String, ()>(text.to_owned()) } ]
            }
        },
        terms {
            PLiteral . scalar:Scalar |- scalar : Pattern;
            PAlt . p:Pattern, q:Pattern |- p "|" q : Pattern;
            PConcat . p:Pattern, q:Pattern |- p q : Pattern;
            PStar . p:Pattern |- p "*" : Pattern;
        },
        equations {},
        rewrites {},
    }
}

/// Original generated consumer witness for Regex's variable-admitting native
/// Scalar and its transparent Pattern projection. The two variable derivations
/// have the same exact semantic key, while the scalar literal remains distinct.
/// The original generated lexer strips StringLit quotes even for this custom
/// unquoted pattern; use the existing lexical-session token-source boundary,
/// not a rewritten lexer or an assertion of generated-lexer compatibility.
#[test]
fn generated_native_scalar_preserves_original_semantic_equivalence() {
    use mettail_prattail::wpda_owned::engine::OwnedEngineActions;
    use mettail_prattail::wpda_walker::WpdaEngine;
    use native_scalar_fixture::{Pattern, Scalar};

    let variable = mettail_runtime::OrdVar(mettail_runtime::Var::Free(
        core::native_variable::get_or_create_var("a"),
    ));
    let engine = native_scalar_fixture::GeneratedNativeScalarWpdaEngine;
    let mut cache = mettail_runtime::exact_semantic_key::ContentKeyCache::with_limits(64, 4096);
    let candidates: [std::sync::Arc<dyn std::any::Any + Send + Sync>; 4] = [
        std::sync::Arc::new(Pattern::PVar(variable.clone())),
        std::sync::Arc::new(Pattern::PLiteral(std::sync::Arc::new(Scalar::SVar(variable.clone())))),
        std::sync::Arc::new(Pattern::PLiteral(std::sync::Arc::new(Scalar::StringLit("a".into())))),
        std::sync::Arc::new(Scalar::SVar(variable.clone())),
    ];
    let keys: Vec<_> = candidates
        .iter()
        .map(|term| {
            engine
                .semantic_content_key(term, &mut cache)
                .expect("bounded original key construction")
                .expect("original generated category key")
        })
        .collect();
    assert_eq!(keys[0], keys[1], "transparent variable projection is observationally equal");
    assert_ne!(keys[0], keys[2], "a literal is not a variable with the same spelling");
    assert_ne!(keys[0], keys[3], "root-category tags separate equal descendant streams");
    for (term, key) in candidates.iter().zip(&keys) {
        assert_eq!(
            key.as_bytes(),
            engine
                .semantic_fingerprint(term)
                .expect("original framed byte stream"),
            "cached persistent keys reproduce the complete original write stream"
        );
    }
    assert_eq!(
        engine.semantic_fingerprint(&candidates[0]),
        engine.semantic_fingerprint(&candidates[1]),
        "persistent keys agree with the original byte-stream observation"
    );
    assert_ne!(
        engine.semantic_fingerprint(&candidates[0]),
        engine.semantic_fingerprint(&candidates[2])
    );

    let metadata = native_scalar_fixture::GeneratedNativeScalarLanguage.metadata();
    let artifacts = metadata
        .generated_semantic_artifacts_v1()
        .expect("captured native fixture");
    let grammar: core::GrammarCoreV1 = postcard::from_bytes(artifacts.grammar_core_postcard)
        .expect("exact captured native grammar");
    assert!(
        grammar
            .categories
            .iter()
            .find(|category| category.name == "Scalar")
            .expect("captured String-native Scalar declaration")
            .admits_variables
    );
    let image = compile_parser_image(&grammar).expect("existing runtime lexical image");
    let observations = grammar
        .wpda_token_observations
        .as_ref()
        .expect("captured original token observations");
    let scalar_token = grammar
        .tokens
        .iter()
        .find(|token| {
            matches!(
                observations.get(token.id.0 as usize),
                Some(Some(core::WpdaTokenObservation::StringLit))
            )
        })
        .expect("original String literal token family");
    assert_eq!(
        scalar_token.category, None,
        "original builtin tokens carry no Core category tag; source rules supply admission"
    );
    let host = FixtureHost(grammar.fingerprint().expect("native fixture fingerprint"));
    let parser = core::RuntimeParser::new(
        &grammar,
        &image,
        RUNTIME_COMPILER_ABI,
        RUNTIME_UNICODE_ABI,
        &host,
    )
    .expect("existing host admission; native actions remain generated Rust");
    let receipt = grammar
        .wpda_original_occurrences
        .as_ref()
        .expect("real macro producer retains its original occurrence receipt");
    assert_eq!(
        receipt,
        &[
            core::ProductionId(0),
            core::ProductionId(1),
            core::ProductionId(2),
            core::ProductionId(3)
        ]
    );
    let occurrences: Vec<_> = receipt.iter().map(|id| id.0 as usize).collect();
    let synthesis = derive_authored_rules(&grammar, &occurrences, |_| Ok::<_, Infallible>(()))
        .expect("original native fixture synthesis");
    let descriptors = derive_authored_descriptors(
        &grammar,
        &occurrences,
        synthesis,
        DescriptorOptions {
            crosscat_lex_compat_gate: true,
            prefix_factoring: false,
            mixfix_factoring: false,
            accept_continue: false,
            recovery_base: 0xFE00,
            max_mixfix_slice: usize::MAX,
        },
        |_, _, _, _| Ok::<_, Infallible>(()),
        |_, _| Ok::<_, Infallible>(false),
    )
    .expect("complete captured native descriptor domain");
    let absorption = derive_absorption_rows(&grammar, &descriptors)
        .expect("original native absorption observations");
    let collect = |input: &str| {
        let session = parser
            .lexical_session(input)
            .expect("existing original lexical session");
        let source = OwnedTokenSource::from_admitted_session(
            &session,
            SourceAdapterLimits {
                nodes: 1024,
                edges: 4096,
                text_bytes: 65536,
            },
        )
        .expect("original token-kind observations");
        let mut walker = WpdaWalker::new_for_category(
            native_scalar_fixture::GeneratedNativeScalarWpdaEngine,
            0,
            0,
        );
        walker
            .run_to_end_of_input(10_000, &source)
            .expect("original generated engine walk");
        let resolved = walker.resolve_at_end_of_input(&source);
        let WpdaResolveResult::Accepted { roots, .. } = resolved else {
            panic!("generated engine must accept {input:?}: {resolved:?}");
        };
        assert!(!roots.is_empty());
        let mut terms = Vec::new();
        let mut weights = Vec::new();
        let mut generated_family = Vec::new();
        let mut key_cache = mettail_runtime::exact_semantic_key::ContentKeyCache::default();
        for root in roots {
            let readings = walker
                .realize_root_to_terms_with_weights(
                    root,
                    Some(256),
                    RealizeRequestMode::BoundedEnumeration,
                )
                .expect("original generated semantic actions");
            assert!(readings.len() < 256, "root {root:?} exhausted for {input:?}");
            for (term, weight) in readings {
                let key = native_scalar_fixture::GeneratedNativeScalarWpdaEngine
                    .semantic_content_key(&term, &mut key_cache)
                    .expect("bounded original native key")
                    .expect("generated native category has an exact key");
                generated_family.push((key.as_bytes().to_vec(), weight));
                terms.push(
                    term.downcast_ref::<Pattern>()
                        .expect("generated Pattern carrier")
                        .clone(),
                );
                weights.push(weight);
            }
        }
        assert!(!terms.is_empty(), "acceptance realizes original generated terms for {input:?}");
        let actions = OwnedActionProvider::new(&source, &descriptors, |_| Ok(()))
            .expect("complete owned native actions");
        let owned_engine =
            OwnedWpdaEngine::new(&descriptors, &actions, 0, &[], &absorption, |_| Ok(()))
                .expect("original native routing for owned carrier");
        let mut owned_walker = WpdaWalker::new_for_category(owned_engine, 0, 0);
        owned_walker
            .run_to_end_of_input(10_000, &source)
            .expect("owned consumer of the same native source");
        let resolved = owned_walker.resolve_at_end_of_input(&source);
        let WpdaResolveResult::Accepted { roots, .. } = resolved else {
            panic!("owned engine must accept native input {input:?}: {resolved:?}");
        };
        assert!(!roots.is_empty());
        let mut owned_family = Vec::new();
        let mut owned_cache = mettail_runtime::exact_semantic_key::ContentKeyCache::default();
        for root in roots {
            let readings = owned_walker
                .realize_root_to_terms_with_weights(
                    root,
                    Some(256),
                    RealizeRequestMode::BoundedEnumeration,
                )
                .expect("owned native semantic actions");
            assert!(readings.len() < 256, "owned root {root:?} exhausted for {input:?}");
            for (value, weight) in readings {
                let term = value
                    .downcast_ref::<OwnedTerm>()
                    .expect("owned native carrier");
                assert_eq!(term.syntax, term.value, "native identity carrier for {input:?}");
                let key = actions
                    .semantic_content_key(&value, &mut owned_cache)
                    .expect("bounded owned native key")
                    .expect("captured native profile has an exact key");
                owned_family.push((key.as_bytes().to_vec(), weight));
            }
        }
        // Compare complete finite observations, including native variables and
        // transparent projections. Reuse the original exact-key worker rather
        // than inventing a second serializer or filtering a ground sublanguage.
        generated_family.sort();
        generated_family.dedup();
        owned_family.sort();
        owned_family.dedup();
        assert_eq!(owned_family, generated_family, "complete native weighted family for {input:?}");
        (terms, weights)
    };
    // This macro fixture has no explicit precedence for category-leading
    // concatenation: its original binder RHS starts at floor zero. Preserve
    // that baseline independently of the actual DDL's explicit precedence
    // acceptance test, which requires Alt(Concat(a, Star(b)), c).
    let (terms, weights) = collect("ab*|c");
    assert_eq!(terms.len(), weights.len());
    let literal = |term: &Pattern, text: &str| {
        matches!(term,
        Pattern::PLiteral(scalar) if matches!(scalar.as_ref(), Scalar::StringLit(value) if value == text))
    };
    assert!(
        terms.iter().any(|term| matches!(term,
        Pattern::PConcat(first, rest) if literal(first, "a") && matches!(rest.as_ref(),
            Pattern::PAlt(second, third) if literal(third, "c") && matches!(second.as_ref(),
                Pattern::PStar(body) if literal(body, "b"))))),
        "original unranked binder behavior must remain unchanged: {terms:?}"
    );

    let (terms, weights) = collect("a");
    assert_eq!(terms.len(), weights.len(), "each original reading retains its full weight");
    assert_eq!(terms.len(), 2, "literal and the original variable equivalence class: {terms:?}");
    let expected_variable = mettail_runtime::OrdVar(mettail_runtime::Var::Free(
        core::native_variable::get_or_create_var("a"),
    ));
    let mut counts = [0; 3];
    for term in &terms {
        match term {
            Pattern::PVar(variable) => {
                assert_eq!(variable, &expected_variable, "actual shared native identity");
                counts[0] += 1;
            },
            Pattern::PLiteral(scalar) => match scalar.as_ref() {
                Scalar::SVar(variable) => {
                    assert_eq!(
                        variable, &expected_variable,
                        "projection preserves native identity"
                    );
                    counts[1] += 1;
                },
                Scalar::StringLit(text) => {
                    assert_eq!(text, "a");
                    counts[2] += 1;
                },
            },
            other => panic!("unexpected original reading of a: {other:?}"),
        }
    }
    assert_eq!(counts[0] + counts[1], 1, "one representative of the proved variable class");
    assert_eq!(counts[2], 1, "the distinct literal class must survive");
    let (terms, _) = collect("a|aa");
    assert!(terms.iter().any(|term| matches!(term,
        Pattern::PAlt(left, right) if literal(left, "a") && matches!(right.as_ref(),
            Pattern::PConcat(first, second) if literal(first, "a") && literal(second, "a")))),
        "generated and owned parsers must retain the outer alternation when its RHS begins with a category-leading concatenation: {terms:?}"
    );
    for input in ["a*", "abc", "a|b|c", "a|ab", "aa|a", "(a*)*"] {
        collect(input);
    }
}

mod postfix_fixture {
    mettail_macros::language! {
        name: OwnedGroupingPostfix,
        options { emit_tests: false, emit_simulator: false, emit_blockly: false },
        types { Expr },
        terms {
            A . |- "A" : Expr;
            Star . a:Expr |- a "*" : Expr;
        },
        equations {},
        rewrites {},
    }
}

/// Check the original generated lexer/parser, independently of owned admission.
#[test]
fn generated_postfix_facade_parses_a_and_a_star() {
    use postfix_fixture::Expr;
    assert!(matches!(Expr::parse("A").expect("generated leaf parser"), Expr::A));
    let term = Expr::parse("A*").expect("generated postfix parser");
    assert!(matches!(&term, Expr::Star(child) if matches!(child.as_ref(), Expr::A)));
}

/// This is explicitly owned semantic-admission coverage, not generated parity:
/// the static Boolean surface has no NonAssociative declaration. The captured
/// source rule stays unchanged while Core's runtime precedence metadata selects
/// the existing strict postfix contract.
#[test]
fn owned_grouping_boundary_admits_grouped_nonassociative_postfix() {
    let metadata = postfix_fixture::OwnedGroupingPostfixLanguage.metadata();
    let artifacts = metadata
        .generated_semantic_artifacts_v1()
        .expect("captured postfix fixture");
    let mut grammar: core::GrammarCoreV1 = postcard::from_bytes(artifacts.grammar_core_postcard)
        .expect("decode captured postfix grammar");
    let star = grammar
        .productions
        .iter_mut()
        .find(|production| production.label == "Star")
        .expect("actual Star production");
    star.precedence.binding_power = Some(10);
    star.precedence.associativity = core::Associativity::NonAssociative;
    let occurrences: Vec<_> = (0..grammar.productions.len()).collect();
    let synthesis = derive_authored_rules(&grammar, &occurrences, |_| Ok::<_, Infallible>(()))
        .expect("original synthesis of complete fixture");
    let descriptors = derive_authored_descriptors(
        &grammar,
        &occurrences,
        synthesis,
        DescriptorOptions {
            crosscat_lex_compat_gate: true,
            prefix_factoring: false,
            mixfix_factoring: false,
            accept_continue: false,
            recovery_base: 0xFE00,
            max_mixfix_slice: usize::MAX,
        },
        |_, _, _, _| Ok::<_, Infallible>(()),
        |_, _| Ok::<_, Infallible>(false),
    )
    .expect("lossless postfix descriptors");
    let image = compile_parser_image(&grammar).expect("strict postfix runtime image");
    let host = FixtureHost(grammar.fingerprint().expect("fixture fingerprint"));
    let parser = core::RuntimeParser::new(
        &grammar,
        &image,
        RUNTIME_COMPILER_ABI,
        RUNTIME_UNICODE_ABI,
        &host,
    )
    .expect("admitted strict postfix fixture");
    let absorption = AbsorptionRows::new();
    for (input, expected, top_ranked) in [
        ("A*", true, true),
        ("A**", false, true),
        ("(A*)", true, false),
        ("(A*)*", true, true),
        ("((A*))", true, false),
    ] {
        let session = parser.lexical_session(input).expect("postfix corpus lexes");
        let source = OwnedTokenSource::from_admitted_session(
            &session,
            SourceAdapterLimits {
                nodes: 1024,
                edges: 4096,
                text_bytes: 65536,
            },
        )
        .expect("retained token bindings");
        let actions = OwnedActionProvider::new(&source, &descriptors, |_| Ok(()))
            .expect("complete original action domain");
        let engine = OwnedWpdaEngine::new(&descriptors, &actions, 0, &[], &absorption, |_| Ok(()))
            .expect("postfix owned routing");
        let mut walker = WpdaWalker::new_for_category(engine, 0, 0);
        walker
            .run_to_end_of_input(10_000, &source)
            .expect("bounded postfix walk");
        let mut terms = Vec::new();
        if let WpdaResolveResult::Accepted { roots, .. } = walker.resolve_at_end_of_input(&source) {
            for root in roots {
                for (value, _) in walker
                    .realize_root_to_terms_with_weights(
                        root,
                        Some(16),
                        RealizeRequestMode::BoundedEnumeration,
                    )
                    .expect("postfix realization protocol")
                {
                    terms.push(
                        value
                            .downcast_ref::<OwnedTerm>()
                            .expect("owned carrier")
                            .clone(),
                    );
                }
            }
        }
        assert_eq!(!terms.is_empty(), expected, "declared strictness for {input:?}");
        for term in terms {
            assert_eq!(term.production.is_some(), top_ranked, "grouping boundary at {input:?}");
            assert_eq!(term.syntax, term.value, "grouping changes no constructor value");
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum TreeNode {
    Constructor(String, usize),
    Variable(mettail_runtime::OrdVar),
}

type Tree = Vec<TreeNode>;

struct FixtureHost([u8; 32]);
impl core::RuntimeHost for FixtureHost {
    fn capability_manifest(
        &self,
        key: &core::RuntimeCapabilityKey,
    ) -> Option<core::RuntimeCapabilityManifest> {
        (key.language_fingerprint == self.0).then(|| core::RuntimeCapabilityManifest {
            key: key.clone(),
            code_commitment: [1; 32],
            abi: "owned-keyword-parity-test/1".into(),
            effects: [core::RuntimeEffect::Reduce].into_iter().collect(),
            cost: core::RuntimeLogicalCost {
                base: 1,
                per_input_byte: 1,
                per_value: 1,
                maximum: 1024,
            },
        })
    }
    fn decode_token(&self, _: &str, _: &str) -> Result<core::DynamicValue, String> {
        panic!("keyword/term-only fixture must not invoke a capability decoder")
    }
    fn evaluate(
        &self,
        _: &core::NativeEvaluation,
        _: &[core::DynamicValue],
        _: core::SourceSpan,
    ) -> Result<core::DynamicValue, String> {
        panic!("constructor-only fixture must not invoke native evaluation")
    }
}

fn generated_tree(term: &fixture::Expr) -> Tree {
    let mut out = Vec::new();
    let mut pending = vec![term];
    while let Some(term) = pending.pop() {
        match term {
            fixture::Expr::A => out.push(TreeNode::Constructor("A".into(), 0)),
            fixture::Expr::B => out.push(TreeNode::Constructor("B".into(), 0)),
            fixture::Expr::Wrap(child) => {
                out.push(TreeNode::Constructor("Wrap".into(), 1));
                pending.push(child);
            },
            fixture::Expr::Group(child) => {
                out.push(TreeNode::Constructor("Group".into(), 1));
                pending.push(child);
            },
            fixture::Expr::Pair(left, right) => {
                out.push(TreeNode::Constructor("Pair".into(), 2));
                pending.push(right);
                pending.push(left);
            },
            fixture::Expr::Add(left, right) => {
                out.push(TreeNode::Constructor("Add".into(), 2));
                pending.push(right);
                pending.push(left);
            },
            fixture::Expr::Star(child) => {
                out.push(TreeNode::Constructor("Star".into(), 1));
                pending.push(child);
            },
            fixture::Expr::Choose(condition, then_branch, else_branch) => {
                out.push(TreeNode::Constructor("Choose".into(), 3));
                pending.push(else_branch);
                pending.push(then_branch);
                pending.push(condition);
            },
            fixture::Expr::EVar(variable) => out.push(TreeNode::Variable(variable.clone())),
        }
    }
    out
}

fn owned_tree(grammar: &core::GrammarCoreV1, value: &core::DynamicValue) -> Tree {
    let mut out = Vec::new();
    let mut pending = vec![value];
    while let Some(value) = pending.pop() {
        if let core::DynamicValue::NativeVariable { category, variable } = value {
            assert_eq!(*category, core::CategoryId(0));
            out.push(TreeNode::Variable(mettail_runtime::OrdVar(mettail_runtime::Var::Free(
                variable.clone(),
            ))));
            continue;
        }
        let core::DynamicValue::Term(term) = value else {
            panic!("fixture readings contain only constructors and actual native variables")
        };
        let production = grammar
            .productions
            .iter()
            .find(|production| production.constructor == term.constructor)
            .expect("every realized constructor belongs to this captured fixture");
        out.push(TreeNode::Constructor(production.label.clone(), term.fields.len()));
        pending.extend(term.fields.iter().rev());
    }
    out
}

#[test]
fn owned_and_generated_engines_drive_the_same_walker_to_real_terms() {
    let metadata = fixture::OwnedEngineParityLanguage.metadata();
    let artifacts = metadata
        .generated_semantic_artifacts_v1()
        .expect("fixture embeds its exact captured grammar");
    let grammar: core::GrammarCoreV1 =
        postcard::from_bytes(artifacts.grammar_core_postcard).expect("captured grammar decodes");
    let source_occurrences = [0, 1, 2, 3, 4, 5, 6, 7];
    assert_eq!(
        grammar.wpda_original_occurrences,
        Some(
            source_occurrences
                .iter()
                .map(|id| core::ProductionId(*id as u32))
                .collect()
        )
    );
    assert_eq!(
        grammar
            .productions
            .iter()
            .map(|production| production.label.as_str())
            .collect::<Vec<_>>(),
        ["A", "B", "Wrap", "Pair", "Add", "Star", "Choose", "Group"]
    );
    let synthesis =
        derive_authored_rules(&grammar, &source_occurrences, |_| Ok::<_, Infallible>(()))
            .expect("original synthesis handles the complete explicit fixture roster");
    assert_eq!(
        synthesis.per_category[0].len(),
        9,
        "object category retains the original synthesized variable rule"
    );
    let descriptors = derive_authored_descriptors(
        &grammar,
        &source_occurrences,
        synthesis,
        DescriptorOptions {
            crosscat_lex_compat_gate: true,
            prefix_factoring: false,
            mixfix_factoring: false,
            accept_continue: false,
            recovery_base: 0xFE00,
            max_mixfix_slice: usize::MAX,
        },
        |_, _, _, _| Ok::<_, Infallible>(()),
        |_, _| Ok::<_, Infallible>(false),
    )
    .expect("original descriptors cover the fixture without collection/cast/factoring rows");
    let image = compile_parser_image(&grammar).expect("existing runtime compiler handles fixture");
    let host = FixtureHost(grammar.fingerprint().expect("fixture fingerprint"));
    let parser = core::RuntimeParser::new(
        &grammar,
        &image,
        RUNTIME_COMPILER_ABI,
        RUNTIME_UNICODE_ABI,
        &host,
    )
    .expect("existing runtime parser admits fixture lexer and semantic workers");
    let absorption = derive_absorption_rows(&grammar, &descriptors)
        .expect("original iterative eligibility queries produce explicit receipts");
    for label in ["Add", "Choose"] {
        let &(result, rule) = descriptors
            .label_index
            .get(&("Expr".into(), label.into()))
            .expect("original operator coordinates");
        assert_eq!(
            absorption.get(&(0, result, rule)),
            Some(&None),
            "nonnative Expr has an original None answer, not a missing receipt"
        );
    }

    // Both low-level walkers deliberately share the original variable-cache
    // epoch. Compare actual FreeVar identity, never a displayed name or ID.
    // Exercise the original binary, postfix, and mixfix transition callbacks,
    // including composed weights across grouping and nested operators.
    for input in [
        "A",
        "(A)",
        "(A*)*",
        "B",
        "w(A)",
        "pair(A,B)",
        "w(pair(A,w(B)))",
        "(pair(B,A))",
        "x",
        "w(x)",
        "A+B",
        "A*",
        "A?B:A",
        "A+B*",
        "(A+B)*",
        "A?B:(A+B)",
        "w(A?B:A)*",
    ] {
        let session = parser
            .lexical_session(input)
            .expect("existing lexer accepts corpus bytes");
        let source = OwnedTokenSource::from_admitted_session(
            &session,
            SourceAdapterLimits {
                nodes: 1_024,
                edges: 4_096,
                text_bytes: 65_536,
            },
        )
        .expect("exact retained token bindings cover the fixture lattice");
        let actions = OwnedActionProvider::new(&source, &descriptors, |_| Ok(()))
            .expect("actual action provider admits every original fixture rule");
        let engine = OwnedWpdaEngine::new(&descriptors, &actions, 0, &[], &absorption, |_| Ok(()))
            .expect("owned engine admits the entire fixture");
        // Match the actual generated parse_Expr facade's category seed.
        let mut walker = WpdaWalker::new_for_category(engine, 0, 0);
        walker
            .run_to_end_of_input(10_000, &source)
            .expect("owned walker finishes corpus input");
        let resolved = walker.resolve_at_end_of_input(&source);
        let WpdaResolveResult::Accepted { roots, .. } = resolved else {
            panic!("owned engine must accept complete corpus input {input:?}: {resolved:?}");
        };
        assert!(!roots.is_empty(), "acceptance must carry actual forest roots");
        let mut actual = Vec::new();
        for root in roots {
            let terms = walker
                .realize_root_to_terms_with_weights(
                    root,
                    Some(16),
                    RealizeRequestMode::BoundedEnumeration,
                )
                .expect("real reducer workers realize the owned forest");
            assert!(terms.len() < 16, "owned root {root:?} exhausted below the cap for {input:?}");
            for (value, weight) in terms {
                let value = value
                    .downcast_ref::<OwnedTerm>()
                    .expect("provider publishes the explicit category carrier");
                assert_eq!(value.category, 0);
                assert_eq!(
                    value.syntax, value.value,
                    "non-native fixture retains constructor semantics"
                );
                actual.push((owned_tree(&grammar, &value.syntax), weight));
            }
        }
        actual.sort();
        actual.dedup();
        assert!(!actual.is_empty(), "owned realization must produce terms for {input:?}");
        let mut generated_walker =
            WpdaWalker::new_for_category(fixture::OwnedEngineParityWpdaEngine, 0, 0);
        generated_walker
            .run_to_end_of_input(10000, &source)
            .expect("generated walker");
        let WpdaResolveResult::Accepted { roots, .. } =
            generated_walker.resolve_at_end_of_input(&source)
        else {
            panic!("generated engine must accept the exact same source {input:?}");
        };
        let mut generated = Vec::new();
        for root in roots {
            let terms = generated_walker
                .realize_root_to_terms_with_weights(
                    root,
                    Some(16),
                    RealizeRequestMode::BoundedEnumeration,
                )
                .expect("generated readings");
            assert!(
                terms.len() < 16,
                "generated root {root:?} exhausted below the cap for {input:?}"
            );
            for (term, weight) in terms {
                let term = term
                    .downcast_ref::<fixture::Expr>()
                    .expect("generated carrier");
                generated.push((generated_tree(term), weight));
            }
        }
        generated.sort();
        generated.dedup();
        assert!(!generated.is_empty(), "generated realization must produce terms for {input:?}");
        // Authored paren syntax does not replace the original universal
        // grouping branch. Both consumer families must retain BOTH readings;
        // their full composed weights are compared immediately below.
        if matches!(input, "(A)" | "(A*)*") {
            let node = |label: &str, arity| TreeNode::Constructor(label.into(), arity);
            let mut expected = if input == "(A)" {
                vec![vec![node("A", 0)], vec![node("Group", 1), node("A", 0)]]
            } else {
                vec![
                    vec![node("Star", 1), node("Star", 1), node("A", 0)],
                    vec![node("Star", 1), node("Group", 1), node("Star", 1), node("A", 0)],
                ]
            };
            expected.sort();
            for (label, family) in [("generated", &generated), ("owned", &actual)] {
                let mut trees: Vec<_> = family.iter().map(|(tree, _)| tree.clone()).collect();
                trees.sort();
                assert_eq!(
                    trees, expected,
                    "{label} retains exactly both grouping branches for {input:?}"
                );
            }
        }
        assert_eq!(
            actual, generated,
            "all bounded corpus trees and full composed weights for {input:?}"
        );
    }

    // The retained authored object declaration still contributes its real
    // synthetic Var row. Final Core category authority must independently
    // refuse that row when variables are forbidden; do not filter it out.
    {
        let mut forbidden = grammar.clone();
        forbidden.categories[0].admits_variables = false;
        let forbidden_image = compile_parser_image(&forbidden)
            .expect("compile the category-authority counterexample");
        let forbidden_host =
            FixtureHost(forbidden.fingerprint().expect("counterexample fingerprint"));
        let forbidden_parser = core::RuntimeParser::new(
            &forbidden,
            &forbidden_image,
            RUNTIME_COMPILER_ABI,
            RUNTIME_UNICODE_ABI,
            &forbidden_host,
        )
        .expect("category-authority counterexample retains the original lexer");
        let session = forbidden_parser
            .lexical_session("x")
            .expect("identifier still lexes");
        let source = OwnedTokenSource::from_admitted_session(
            &session,
            SourceAdapterLimits {
                nodes: 1024,
                edges: 4096,
                text_bytes: 65536,
            },
        )
        .expect("counterexample retains actual token bindings");
        assert!(
            matches!(
                OwnedActionProvider::new(&source, &descriptors, |_| Ok(())),
                Err(mettail_prattail::wpda_owned::actions::OwnedActionBuildError::Unsupported {
                    category: 0,
                    rule: 8,
                    feature: "declared category forbids variables",
                })
            ),
            "provider must reject the retained variable row before any action executes"
        );
    }

    // Structural input uses the same complete owned engine and provider. The
    // original Core parser is the hole oracle; generated text APIs cannot
    // represent structural template holes and are not used as a fake oracle.
    for (prefix, suffix) in [("", ""), ("w(", ")"), ("pair(", ",A)")] {
        for declared in [None, Some(core::CategoryId(0))] {
            let mut pieces = Vec::new();
            if !prefix.is_empty() {
                pieces.push(core::RuntimeTemplatePiece::Text(prefix.into()));
            }
            pieces.push(core::RuntimeTemplatePiece::Hole(0));
            if !suffix.is_empty() {
                pieces.push(core::RuntimeTemplatePiece::Text(suffix.into()));
            }
            let holes = [core::RuntimeTemplateHole { id: 0, category: declared }];
            let session = parser
                .lexical_template_session(&pieces, &holes)
                .expect("original structural lexer");
            let source = OwnedTokenSource::from_admitted_session(
                &session,
                SourceAdapterLimits {
                    nodes: 1024,
                    edges: 4096,
                    text_bytes: 65536,
                },
            )
            .expect("structural source");
            let actions = OwnedActionProvider::new(&source, &descriptors, |_| Ok(()))
                .expect("whole provider");
            let engine =
                OwnedWpdaEngine::new(&descriptors, &actions, 0, &[], &absorption, |_| Ok(()))
                    .expect("whole engine");
            let mut walker = WpdaWalker::new_for_category(engine, 0, 0);
            walker
                .run_to_end_of_input(10000, &source)
                .expect("structural category continuation");
            let WpdaResolveResult::Accepted { roots, .. } = walker.resolve_at_end_of_input(&source)
            else {
                panic!("structural input {prefix:?},hole,{suffix:?} must complete");
            };
            for mode in
                [RealizeRequestMode::SingleResultElection, RealizeRequestMode::BoundedEnumeration]
            {
                let mut actual = Vec::new();
                for &root in &roots {
                    let terms = walker
                        .realize_root_to_terms_with_weights(root, Some(16), mode)
                        .expect("structural action in each reader");
                    if matches!(mode, RealizeRequestMode::BoundedEnumeration) {
                        assert!(
                            terms.len() < 16,
                            "structural root {root:?} exhausted below the cap"
                        );
                    }
                    for (value, _) in terms {
                        let term = value
                            .downcast_ref::<OwnedTerm>()
                            .expect("owned structural carrier");
                        assert_eq!(term.category, 0);
                        let mut pending = vec![&term.syntax];
                        let mut count = 0;
                        while let Some(value) = pending.pop() {
                            match value {
                                core::DynamicValue::TemplateHole { id, category } => {
                                    assert_eq!((*id, *category), (0, core::CategoryId(0)));
                                    count += 1;
                                },
                                core::DynamicValue::Term(value) => {
                                    pending.extend(value.fields.iter())
                                },
                                _ => panic!("unexpected template payload"),
                            }
                        }
                        assert_eq!(count, 1);
                        actual.push(term.syntax.clone());
                    }
                }
                assert!(!actual.is_empty(), "acceptance must realize structural values");
                let expected = parser
                    .parse_template(&pieces, &holes, Some(core::CategoryId(0)))
                    .expect("original category-hole parser");
                assert!(
                    actual
                        .iter()
                        .all(|value| expected.iter().any(|result| &result.syntax == value)),
                    "owned category seed retains original hole construction and surrounding suffix"
                );
                if matches!(mode, RealizeRequestMode::BoundedEnumeration) {
                    assert!(
                        expected
                            .iter()
                            .all(|result| actual.contains(&result.syntax)),
                        "bounded owned readings retain every original fixture result"
                    );
                }
            }
        }
    }
}
