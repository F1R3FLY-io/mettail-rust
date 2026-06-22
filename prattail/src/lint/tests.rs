use super::*;
use crate::binding_power::{BindingPowerTable, InfixOperator};
use crate::grammar::ir::RDRuleInfo;
use crate::grammar::ir::{CastRule, CrossCategoryRule};
use crate::pipeline::CategoryInfo;
use crate::prediction::{FirstItem, FirstSet, FollowSetInput, RuleInfo};
use crate::recovery::RecoveryConfig;

// ── Helper constructors ──

fn cat_info(name: &str, native_type: Option<&str>, is_primary: bool) -> CategoryInfo {
    CategoryInfo {
        name: name.to_string(),
        native_type: native_type.map(|s| s.to_string()),
        is_primary,
        has_var: true,
    }
}

fn make_rule_info(
    label: &str,
    category: &str,
    first_items: Vec<FirstItem>,
    is_infix: bool,
) -> RuleInfo {
    RuleInfo {
        label: label.to_string(),
        category: category.to_string(),
        first_items,
        is_infix,
        is_var: false,
        is_literal: false,
        is_cross_category: false,
        is_cast: false,
    }
}

/// Minimal context builder for quick tests.
struct CtxBuilder {
    grammar_name: String,
    rule_locations: HashMap<(String, String), crate::SourceLocation>,
    categories: Vec<CategoryInfo>,
    rules: Vec<RuleInfo>,
    rd_rules: Vec<RDRuleInfo>,
    first_sets: HashMap<String, FirstSet>,
    follow_sets: HashMap<String, FirstSet>,
    bp_table: BindingPowerTable,
    prediction_wfsts: HashMap<String, PredictionWfst>,
    recovery_wfsts: Vec<RecoveryWfst>,
    cast_rules: Vec<CastRule>,
    cross_rules: Vec<CrossCategoryRule>,
    nfa_spillover_categories: HashSet<String>,
    recovery_config: RecoveryConfig,
    all_syntax: Vec<(String, String, Vec<SyntaxItemSpec>)>,
    follow_inputs: Vec<FollowSetInput>,
    semantic_dependency_groups: Vec<HashSet<String>>,
    pre_collected_diagnostics: Vec<LintDiagnostic>,
    decision_trees: HashMap<String, CategoryDecisionTree>,
    token_id_map: TokenIdMap,
    dead_rule_warnings: Vec<crate::pipeline::DeadRuleWarning>,
    dead_rule_ignore_labels: HashSet<String>,
    refinement_types_data: Vec<crate::RefinementTypeSpec>,
    grammar_profile_data: Option<crate::cost_benefit::GrammarProfile>,
    wpds_analysis_data: Option<crate::wpds::WpdsAnalysis>,
    wpds_elapsed_data: Option<std::time::Duration>,
    // ── Mathematical analysis result fields ──
    safety_result_data:
        Option<crate::verify::SafetyResult<crate::automata::semiring::BooleanWeight>>,
    cegar_result_data: Option<crate::cegar::CegarLog>,
    algebraic_result_data: Option<crate::algebraic::AlgebraicSummary>,
    math_analysis_elapsed_data: Option<std::time::Duration>,
    confluence_result_data: Option<crate::confluence::ConfluenceAnalysis>,
    termination_result_data: Option<crate::termination::TerminationResult>,
    vpa_result_data: Option<crate::vpa::VpaAnalysis>,
    wta_result_data: Option<crate::tree_automaton::WtaAnalysis>,
    ewpds_result_data: Option<crate::ewpds::EwpdsAnalysis>,
    ara_result_data: Option<crate::ara::AraAnalysis>,
    petri_result_data: Option<crate::petri::PetriAnalysis>,
    nominal_result_data: Option<crate::nominal::NominalAnalysis>,
    alternating_result_data: Option<crate::alternating::AlternatingAnalysis>,
    ltl_results_data: Option<Vec<crate::ltl::LtlCheckResult>>,
    provenance_result_data: Option<crate::provenance::ProvenanceAnalysis>,
    cra_result_data: Option<crate::cra::CraAnalysis>,
    morphism_result_data: Option<crate::morphism::MorphismCheck>,
    kat_result_data: Option<crate::kat::KatCheck>,
    // ── Advanced automata analysis result fields ──
    symbolic_result_data: Option<crate::symbolic::SymbolicAnalysis>,
    buchi_result_data: Option<crate::buchi::BuchiAnalysis>,
    mso_result_data: Option<crate::weighted_mso::MsoAnalysis>,
    probabilistic_result_data: Option<crate::probabilistic::ProbabilisticAnalysis>,
    register_result_data: Option<crate::register_automata::RegisterAnalysis>,
    parity_tree_result_data: Option<crate::parity_tree::ParityTreeAnalysis>,
    multi_tape_result_data: Option<crate::multi_tape::MultiTapeAnalysis>,
    multiset_result_data: Option<crate::multiset_automata::MultisetAnalysisResult>,
    two_way_result_data: Option<crate::two_way_transducer::TwoWayAnalysis>,
    sft_result_data: Option<crate::sft::SftAnalysis>,
    egraph_result_data: Option<crate::egraph::EGraphAnalysis>,
    dispatch_diagnostics_data: Option<crate::predicate_dispatch::DispatchDiagnostics>,
    // ── Constraint theory analysis result fields ──
    presburger_result_data: Option<crate::presburger::PresburgerAnalysis>,
    unification_result_data: Option<crate::unification::UnificationAnalysis>,
    lattice_result_data: Option<crate::lattice_theory::LatticeAnalysis>,
    // ── Refinement type analysis result fields ──
    refinement_analysis_data: Option<crate::pipeline::RefinementAnalysisResult>,
}

impl CtxBuilder {
    fn new() -> Self {
        CtxBuilder {
            grammar_name: "TestGrammar".to_string(),
            rule_locations: HashMap::new(),
            categories: Vec::new(),
            rules: Vec::new(),
            rd_rules: Vec::new(),
            first_sets: HashMap::new(),
            follow_sets: HashMap::new(),
            bp_table: BindingPowerTable::new(),
            prediction_wfsts: HashMap::new(),
            recovery_wfsts: Vec::new(),
            cast_rules: Vec::new(),
            cross_rules: Vec::new(),
            nfa_spillover_categories: HashSet::new(),
            recovery_config: RecoveryConfig::default(),
            all_syntax: Vec::new(),
            follow_inputs: Vec::new(),
            semantic_dependency_groups: Vec::new(),
            pre_collected_diagnostics: Vec::new(),
            decision_trees: HashMap::new(),
            token_id_map: TokenIdMap::new(),
            dead_rule_warnings: Vec::new(),
            dead_rule_ignore_labels: HashSet::new(),
            refinement_types_data: Vec::new(),
            grammar_profile_data: None,
            wpds_analysis_data: None,
            wpds_elapsed_data: None,
            // ── Mathematical analysis result fields ──
            safety_result_data: None,
            cegar_result_data: None,
            algebraic_result_data: None,
            math_analysis_elapsed_data: None,
            confluence_result_data: None,
            termination_result_data: None,
            vpa_result_data: None,
            wta_result_data: None,
            ewpds_result_data: None,
            ara_result_data: None,
            petri_result_data: None,
            nominal_result_data: None,
            alternating_result_data: None,
            ltl_results_data: None,
            provenance_result_data: None,
            cra_result_data: None,
            morphism_result_data: None,
            kat_result_data: None,
            // ── Advanced automata analysis result fields ──
            symbolic_result_data: None,
            buchi_result_data: None,
            mso_result_data: None,
            probabilistic_result_data: None,
            register_result_data: None,
            parity_tree_result_data: None,
            multi_tape_result_data: None,
            multiset_result_data: None,
            two_way_result_data: None,
            sft_result_data: None,
            egraph_result_data: None,
            dispatch_diagnostics_data: None,
            // ── Constraint theory analysis result fields ──
            presburger_result_data: None,
            unification_result_data: None,
            lattice_result_data: None,
            // ── Refinement type analysis result fields ──
            refinement_analysis_data: None,
        }
    }

    fn ctx(&self) -> LintContext<'_> {
        LintContext {
            grammar_name: &self.grammar_name,
            rule_locations: &self.rule_locations,
            categories: &self.categories,
            rules: &self.rules,
            rd_rules: &self.rd_rules,
            first_sets: &self.first_sets,
            follow_sets: &self.follow_sets,
            bp_table: &self.bp_table,
            prediction_wfsts: &self.prediction_wfsts,
            recovery_wfsts: &self.recovery_wfsts,
            cast_rules: &self.cast_rules,
            cross_rules: &self.cross_rules,
            nfa_spillover_categories: &self.nfa_spillover_categories,
            recovery_config: &self.recovery_config,
            all_syntax: &self.all_syntax,
            follow_inputs: &self.follow_inputs,
            semantic_dependency_groups: &self.semantic_dependency_groups,
            pre_collected_diagnostics: &self.pre_collected_diagnostics,
            decision_trees: &self.decision_trees,
            token_id_map: &self.token_id_map,
            dead_rule_warnings: &self.dead_rule_warnings,
            dead_rule_ignore_labels: &self.dead_rule_ignore_labels,
            refinement_types: &self.refinement_types_data,
            grammar_profile: self.grammar_profile_data.as_ref(),
            wpds_analysis: self.wpds_analysis_data.as_ref(),
            wpds_elapsed: self.wpds_elapsed_data,
            // ── Mathematical analysis results ──
            safety_result: self.safety_result_data.as_ref(),
            cegar_result: self.cegar_result_data.as_ref(),
            algebraic_result: self.algebraic_result_data.as_ref(),
            math_analysis_elapsed: self.math_analysis_elapsed_data,
            confluence_result: self.confluence_result_data.as_ref(),
            termination_result: self.termination_result_data.as_ref(),
            vpa_result: self.vpa_result_data.as_ref(),
            wta_result: self.wta_result_data.as_ref(),
            ewpds_result: self.ewpds_result_data.as_ref(),
            ara_result: self.ara_result_data.as_ref(),
            petri_result: self.petri_result_data.as_ref(),
            nominal_result: self.nominal_result_data.as_ref(),
            alternating_result: self.alternating_result_data.as_ref(),
            ltl_results: self.ltl_results_data.as_ref(),
            provenance_result: self.provenance_result_data.as_ref(),
            cra_result: self.cra_result_data.as_ref(),
            morphism_result: self.morphism_result_data.as_ref(),
            kat_result: self.kat_result_data.as_ref(),
            // ── Advanced automata analysis results ──
            symbolic_result: self.symbolic_result_data.as_ref(),
            buchi_result: self.buchi_result_data.as_ref(),
            mso_result: self.mso_result_data.as_ref(),
            probabilistic_result: self.probabilistic_result_data.as_ref(),
            register_result: self.register_result_data.as_ref(),
            parity_tree_result: self.parity_tree_result_data.as_ref(),
            multi_tape_result: self.multi_tape_result_data.as_ref(),
            multiset_result: self.multiset_result_data.as_ref(),
            two_way_result: self.two_way_result_data.as_ref(),
            sft_result: self.sft_result_data.as_ref(),
            egraph_result: self.egraph_result_data.as_ref(),
            dispatch_diagnostics: self.dispatch_diagnostics_data.as_ref(),
            // ── Constraint theory analysis results ──
            presburger_result: self.presburger_result_data.as_ref(),
            unification_result: self.unification_result_data.as_ref(),
            lattice_result: self.lattice_result_data.as_ref(),
            // ── Refinement type analysis results ──
            refinement_analysis: self.refinement_analysis_data.as_ref(),
        }
    }
}

// ══════════════════════════════════════════════════════════════════════
// G01: Left Recursion
// ══════════════════════════════════════════════════════════════════════

#[test]
fn g01_fires_on_left_recursive_rd_rule() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    b.all_syntax.push((
        "BadRule".to_string(),
        "Int".to_string(),
        vec![
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "a".to_string(),
            },
            SyntaxItemSpec::Terminal("@".to_string()),
            SyntaxItemSpec::Terminal("#".to_string()),
        ],
    ));

    let mut diags = Vec::new();
    lint_g01_left_recursion(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::G01);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
}

#[test]
fn g01_skips_infix_pattern() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    b.all_syntax.push((
        "Add".to_string(),
        "Int".to_string(),
        vec![
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "a".to_string(),
            },
            SyntaxItemSpec::Terminal("+".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "b".to_string(),
            },
        ],
    ));

    let mut diags = Vec::new();
    lint_g01_left_recursion(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// G02: Unused Category
// ══════════════════════════════════════════════════════════════════════

#[test]
fn g02_fires_on_unreferenced_category() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    b.categories.push(cat_info("Unused", None, false));
    b.all_syntax
        .push(("NumLit".to_string(), "Int".to_string(), vec![]));

    let mut diags = Vec::new();
    lint_g02_unused_category(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::G02);
    assert!(diags[0].message.contains("Unused"));
}

#[test]
fn g02_does_not_fire_when_referenced() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    b.all_syntax
        .push(("NumLit".to_string(), "Int".to_string(), vec![]));

    let mut diags = Vec::new();
    lint_g02_unused_category(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// G03: Ambiguous Prefix
// ══════════════════════════════════════════════════════════════════════

#[test]
fn g03_fires_on_same_terminal() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    b.rules
        .push(make_rule_info("Foo", "Int", vec![FirstItem::Terminal("!".to_string())], false));
    b.rules
        .push(make_rule_info("Bar", "Int", vec![FirstItem::Terminal("!".to_string())], false));

    let mut diags = Vec::new();
    lint_g03_ambiguous_prefix(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::G03);
}

#[test]
fn g03_skips_infix_rules() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    b.rules
        .push(make_rule_info("Add", "Int", vec![FirstItem::Terminal("+".to_string())], true));
    b.rules
        .push(make_rule_info("Pos", "Int", vec![FirstItem::Terminal("+".to_string())], false));

    let mut diags = Vec::new();
    lint_g03_ambiguous_prefix(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// G04: Duplicate Rule Label
// ══════════════════════════════════════════════════════════════════════

#[test]
fn g04_fires_on_duplicate_label() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    b.all_syntax
        .push(("Add".to_string(), "Int".to_string(), vec![]));
    b.all_syntax
        .push(("Add".to_string(), "Int".to_string(), vec![]));

    let mut diags = Vec::new();
    lint_g04_duplicate_rule_label(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::G04);
    assert_eq!(diags[0].severity, LintSeverity::Error);
}

#[test]
fn g04_allows_same_label_different_category() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    b.categories.push(cat_info("Float", None, false));
    b.all_syntax
        .push(("Add".to_string(), "Int".to_string(), vec![]));
    b.all_syntax
        .push(("Add".to_string(), "Float".to_string(), vec![]));

    let mut diags = Vec::new();
    lint_g04_duplicate_rule_label(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// G05: Empty Category
// ══════════════════════════════════════════════════════════════════════

#[test]
fn g05_fires_on_empty_category() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    b.categories.push(cat_info("Empty", None, false));
    b.all_syntax
        .push(("NumLit".to_string(), "Int".to_string(), vec![]));

    let mut diags = Vec::new();
    lint_g05_empty_category(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::G05);
    assert!(diags[0].message.contains("Empty"));
}

#[test]
fn g05_does_not_fire_when_has_rules() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    b.all_syntax
        .push(("NumLit".to_string(), "Int".to_string(), vec![]));

    let mut diags = Vec::new();
    lint_g05_empty_category(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

#[test]
fn g05_does_not_fire_for_native_type_category() {
    let mut b = CtxBuilder::new();
    // Category with native_type but zero explicit rules — should NOT trigger G05.
    b.categories.push(cat_info("Int", Some("i64"), true));

    let mut diags = Vec::new();
    lint_g05_empty_category(&b.ctx(), &mut diags);
    assert!(diags.is_empty(), "G05 should not fire for native-type categories");
}

#[test]
fn g05_does_not_fire_for_binding_sort_category() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Proc", None, true));
    b.categories.push(cat_info("Name", None, false));
    b.all_syntax.push((
        "PNew".to_string(),
        "Proc".to_string(),
        vec![
            SyntaxItemSpec::Terminal("new".to_string()),
            SyntaxItemSpec::Binder {
                param_name: "x".to_string(),
                category: "Name".to_string(),
                is_multi: false,
            },
            SyntaxItemSpec::NonTerminal {
                category: "Proc".to_string(),
                param_name: "p".to_string(),
            },
        ],
    ));

    let mut diags = Vec::new();
    lint_g05_empty_category(&b.ctx(), &mut diags);

    assert!(diags.is_empty(), "binding-sort categories should not trigger G05: {:?}", diags);
}

// ══════════════════════════════════════════════════════════════════════
// G07: Identical Rules
// ══════════════════════════════════════════════════════════════════════

#[test]
fn g07_fires_on_identical_syntax() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    let syntax = vec![
        SyntaxItemSpec::Terminal("(".to_string()),
        SyntaxItemSpec::NonTerminal {
            category: "Int".to_string(),
            param_name: "a".to_string(),
        },
        SyntaxItemSpec::Terminal(")".to_string()),
    ];
    b.all_syntax
        .push(("Group1".to_string(), "Int".to_string(), syntax.clone()));
    b.all_syntax
        .push(("Group2".to_string(), "Int".to_string(), syntax));

    let mut diags = Vec::new();
    lint_g07_identical_rules(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::G07);
}

#[test]
fn g07_does_not_fire_on_different_syntax() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    b.all_syntax.push((
        "Neg".to_string(),
        "Int".to_string(),
        vec![
            SyntaxItemSpec::Terminal("-".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "a".to_string(),
            },
        ],
    ));
    b.all_syntax.push((
        "Not".to_string(),
        "Int".to_string(),
        vec![
            SyntaxItemSpec::Terminal("~".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "a".to_string(),
            },
        ],
    ));

    let mut diags = Vec::new();
    lint_g07_identical_rules(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// G08: Missing Cast to Root
// ══════════════════════════════════════════════════════════════════════

#[test]
fn g08_fires_when_no_cast_path() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Proc", None, true));
    b.categories.push(cat_info("Int", None, false));
    // No cast rules from Int to Proc

    let mut diags = Vec::new();
    lint_g08_missing_cast_to_root(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::G08);
    assert!(diags[0].message.contains("Int"));
}

#[test]
fn g08_does_not_fire_with_cast_path() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Proc", None, true));
    b.categories.push(cat_info("Int", None, false));
    b.cast_rules.push(CastRule {
        label: "IntToProc".to_string(),
        source_category: "Int".to_string(),
        target_category: "Proc".to_string(),
        shares_infix_with_target: false,
    });

    let mut diags = Vec::new();
    lint_g08_missing_cast_to_root(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

#[test]
fn g08_does_not_fire_when_primary_rule_embeds_category() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    b.categories.push(cat_info("Bool", None, false));
    b.all_syntax.push((
        "IfElse".to_string(),
        "Int".to_string(),
        vec![
            SyntaxItemSpec::Terminal("if".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Bool".to_string(),
                param_name: "cond".to_string(),
            },
            SyntaxItemSpec::Terminal("then".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "then_branch".to_string(),
            },
        ],
    ));

    let mut diags = Vec::new();
    lint_g08_missing_cast_to_root(&b.ctx(), &mut diags);

    assert!(
        diags.is_empty(),
        "categories embedded by primary rules should not trigger G08: {:?}",
        diags
    );
}

#[test]
fn g08_skips_declared_refinement_categories() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", Some("i32"), true));
    b.categories.push(cat_info("PosInt", None, false));
    b.refinement_types_data.push(crate::RefinementTypeSpec {
        name: "PosInt".to_string(),
        base_category: "Int".to_string(),
        variable_name: "x".to_string(),
        predicate_kind: crate::RefinementPredKind::Presburger,
        predicate_repr: "x > 0".to_string(),
    });

    let mut diags = Vec::new();
    lint_g08_missing_cast_to_root(&b.ctx(), &mut diags);

    assert!(diags.is_empty(), "refinement categories should not trigger G08: {:?}", diags);
}

#[test]
fn g08_skips_single_binding_sort_categories() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Proc", None, true));
    b.categories.push(cat_info("Name", None, false));
    b.all_syntax.push((
        "PNew".to_string(),
        "Proc".to_string(),
        vec![
            SyntaxItemSpec::Terminal("new".to_string()),
            SyntaxItemSpec::Binder {
                param_name: "x".to_string(),
                category: "Name".to_string(),
                is_multi: false,
            },
            SyntaxItemSpec::NonTerminal {
                category: "Proc".to_string(),
                param_name: "p".to_string(),
            },
        ],
    ));

    let mut diags = Vec::new();
    lint_g08_missing_cast_to_root(&b.ctx(), &mut diags);

    assert!(diags.is_empty(), "binding-sort categories should not trigger G08: {:?}", diags);
}

#[test]
fn g08_skips_zip_binding_sort_categories() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Proc", None, true));
    b.categories.push(cat_info("Name", None, false));
    b.all_syntax.push((
        "PInputs".to_string(),
        "Proc".to_string(),
        vec![SyntaxItemSpec::Sep {
            body: Box::new(SyntaxItemSpec::Zip {
                left_name: "ns".to_string(),
                right_name: "xs".to_string(),
                left_category: "Name".to_string(),
                right_category: "Name".to_string(),
                body: Box::new(SyntaxItemSpec::Map {
                    body_items: vec![SyntaxItemSpec::IdentCapture { param_name: "x".to_string() }],
                }),
            }),
            separator: ",".to_string(),
            kind: crate::CollectionKind::Vec,
        }],
    ));

    let mut diags = Vec::new();
    lint_g08_missing_cast_to_root(&b.ctx(), &mut diags);

    assert!(
        diags.is_empty(),
        "class-3 zip binding-sort categories should not trigger G08: {:?}",
        diags
    );
}

// ══════════════════════════════════════════════════════════════════════
// G09: Unbalanced Delimiters
// ══════════════════════════════════════════════════════════════════════

#[test]
fn g09_fires_on_unbalanced() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    b.all_syntax.push((
        "Bad".to_string(),
        "Int".to_string(),
        vec![
            SyntaxItemSpec::Terminal("(".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "a".to_string(),
            },
            // Missing ")"
        ],
    ));

    let mut diags = Vec::new();
    lint_g09_unbalanced_delimiters(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::G09);
}

#[test]
fn g09_does_not_fire_on_balanced() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    b.all_syntax.push((
        "Group".to_string(),
        "Int".to_string(),
        vec![
            SyntaxItemSpec::Terminal("(".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "a".to_string(),
            },
            SyntaxItemSpec::Terminal(")".to_string()),
        ],
    ));

    let mut diags = Vec::new();
    lint_g09_unbalanced_delimiters(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

#[test]
fn g09_compound_terminal_no_false_positive() {
    // "in(" contributes 1 open paren; paired with standalone ")" → balanced
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Proc", None, true));
    b.all_syntax.push((
        "PIn".to_string(),
        "Proc".to_string(),
        vec![
            SyntaxItemSpec::Terminal("in(".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Proc".to_string(),
                param_name: "x".to_string(),
            },
            SyntaxItemSpec::Terminal(")".to_string()),
        ],
    ));

    let mut diags = Vec::new();
    lint_g09_unbalanced_delimiters(&b.ctx(), &mut diags);
    assert!(
        diags.is_empty(),
        "compound terminal `in(` paired with `)` should be balanced: {:?}",
        diags,
    );
}

#[test]
fn g09_compound_terminal_true_positive() {
    // "in(" with no closing paren → unbalanced
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Proc", None, true));
    b.all_syntax.push((
        "PIn".to_string(),
        "Proc".to_string(),
        vec![
            SyntaxItemSpec::Terminal("in(".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Proc".to_string(),
                param_name: "x".to_string(),
            },
        ],
    ));

    let mut diags = Vec::new();
    lint_g09_unbalanced_delimiters(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1, "compound terminal `in(` without `)` should be unbalanced");
    assert_eq!(diags[0].id, DiagnosticId::G09);
}

#[test]
fn g09_self_balanced_terminal() {
    // "()" is self-balanced — 1 open + 1 close = balanced
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Proc", None, true));
    b.all_syntax.push((
        "PNil".to_string(),
        "Proc".to_string(),
        vec![SyntaxItemSpec::Terminal("()".to_string())],
    ));

    let mut diags = Vec::new();
    lint_g09_unbalanced_delimiters(&b.ctx(), &mut diags);
    assert!(
        diags.is_empty(),
        "self-balanced `()` terminal should not trigger G09: {:?}",
        diags,
    );
}

// ══════════════════════════════════════════════════════════════════════
// G10: Ambiguous Associativity
// ══════════════════════════════════════════════════════════════════════

#[test]
fn g10_fires_on_mixed_associativity() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    b.bp_table.operators.push(InfixOperator {
        terminal: "+".to_string(),
        category: "Int".to_string(),
        result_category: "Int".to_string(),
        left_bp: 2,
        right_bp: 3,
        label: "Add".to_string(),
        is_cross_category: false,
        is_postfix: false,
        is_mixfix: false,
        mixfix_parts: vec![],
    });
    b.bp_table.operators.push(InfixOperator {
        terminal: "-".to_string(),
        category: "Int".to_string(),
        result_category: "Int".to_string(),
        left_bp: 2,
        right_bp: 1, // Right-associative at same left_bp
        label: "Sub".to_string(),
        is_cross_category: false,
        is_postfix: false,
        is_mixfix: false,
        mixfix_parts: vec![],
    });

    let mut diags = Vec::new();
    lint_g10_ambiguous_associativity(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::G10);
}

#[test]
fn g10_does_not_fire_on_same_associativity() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    b.bp_table.operators.push(InfixOperator {
        terminal: "+".to_string(),
        category: "Int".to_string(),
        result_category: "Int".to_string(),
        left_bp: 2,
        right_bp: 3,
        label: "Add".to_string(),
        is_cross_category: false,
        is_postfix: false,
        is_mixfix: false,
        mixfix_parts: vec![],
    });
    b.bp_table.operators.push(InfixOperator {
        terminal: "-".to_string(),
        category: "Int".to_string(),
        result_category: "Int".to_string(),
        left_bp: 2,
        right_bp: 3, // Same left-assoc
        label: "Sub".to_string(),
        is_cross_category: false,
        is_postfix: false,
        is_mixfix: false,
        mixfix_parts: vec![],
    });

    let mut diags = Vec::new();
    lint_g10_ambiguous_associativity(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// R06: Inverted Recovery Costs
// ══════════════════════════════════════════════════════════════════════

#[test]
fn r06_fires_on_inverted_costs() {
    let mut b = CtxBuilder::new();
    b.recovery_config.skip_per_token = 3.0; // Higher than insert!
    b.recovery_config.insert_cost = 1.0;

    let mut diags = Vec::new();
    lint_r06_inverted_recovery_costs(&b.ctx(), &mut diags);

    assert!(diags.iter().any(|d| d.id == DiagnosticId::R06));
}

#[test]
fn r06_does_not_fire_on_default_config() {
    let b = CtxBuilder::new();

    let mut diags = Vec::new();
    lint_r06_inverted_recovery_costs(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// R07: Transposition Candidate
// ══════════════════════════════════════════════════════════════════════

#[test]
fn r07_fires_on_edit_distance_one() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    b.all_syntax.push((
        "Add".to_string(),
        "Int".to_string(),
        vec![SyntaxItemSpec::Terminal("+".to_string())],
    ));
    b.all_syntax.push((
        "Inc".to_string(),
        "Int".to_string(),
        vec![SyntaxItemSpec::Terminal("++".to_string())],
    ));

    let mut diags = Vec::new();
    lint_r07_transposition_candidate(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1, "R07 should emit exactly 1 summary note");
    assert_eq!(diags[0].id, DiagnosticId::R07);
    assert!(diags[0].message.contains("1 operator pair(s)"));
    assert!(diags[0].message.contains("`+`"));
    assert!(diags[0].message.contains("`++`"));
}

#[test]
fn r07_does_not_fire_on_distant_operators() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    b.all_syntax.push((
        "Add".to_string(),
        "Int".to_string(),
        vec![SyntaxItemSpec::Terminal("++".to_string())],
    ));
    b.all_syntax.push((
        "Arrow".to_string(),
        "Int".to_string(),
        vec![SyntaxItemSpec::Terminal("->".to_string())],
    ));

    let mut diags = Vec::new();
    lint_r07_transposition_candidate(&b.ctx(), &mut diags);
    assert!(diags.is_empty(), "operators `++` and `->` differ by 2 chars: {:?}", diags);
}

#[test]
fn r07_many_single_char_operators_single_summary() {
    // 9 single-char operators → C(9,2)=36 pairs all at distance 1 (all single-char
    // operators differ by exactly 1 substitution). Should emit exactly 1 summary.
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    for (i, op) in ["!", "@", "#", "$", "%", "^", "&", "*", "~"]
        .iter()
        .enumerate()
    {
        b.all_syntax.push((
            format!("Op{}", i),
            "Int".to_string(),
            vec![SyntaxItemSpec::Terminal(op.to_string())],
        ));
    }

    let mut diags = Vec::new();
    lint_r07_transposition_candidate(&b.ctx(), &mut diags);

    assert_eq!(
        diags.len(),
        1,
        "R07 should emit exactly 1 summary note, not {} individual notes",
        diags.len(),
    );
    assert_eq!(diags[0].id, DiagnosticId::R07);
    // The summary should mention the total count (36 pairs)
    assert!(
        diags[0].message.contains("36 operator pair(s)"),
        "message should contain total pair count: {}",
        diags[0].message,
    );
}

// ══════════════════════════════════════════════════════════════════════
// C01: Cast Cycle
// ══════════════════════════════════════════════════════════════════════

#[test]
fn c01_fires_on_cycle() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    b.categories.push(cat_info("Proc", None, false));
    b.cast_rules.push(CastRule {
        label: "IntToProc".to_string(),
        source_category: "Int".to_string(),
        target_category: "Proc".to_string(),
        shares_infix_with_target: false,
    });
    b.cast_rules.push(CastRule {
        label: "ProcToInt".to_string(),
        source_category: "Proc".to_string(),
        target_category: "Int".to_string(),
        shares_infix_with_target: false,
    });

    let mut diags = Vec::new();
    lint_c01_cast_cycle(&b.ctx(), &mut diags);

    assert!(diags
        .iter()
        .any(|d| d.id == DiagnosticId::C01 && d.severity == LintSeverity::Error));
}

#[test]
fn c01_does_not_fire_on_dag() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Proc", None, true));
    b.categories.push(cat_info("Int", None, false));
    b.categories.push(cat_info("Bool", None, false));
    b.cast_rules.push(CastRule {
        label: "IntToProc".to_string(),
        source_category: "Int".to_string(),
        target_category: "Proc".to_string(),
        shares_infix_with_target: false,
    });
    b.cast_rules.push(CastRule {
        label: "BoolToProc".to_string(),
        source_category: "Bool".to_string(),
        target_category: "Proc".to_string(),
        shares_infix_with_target: false,
    });

    let mut diags = Vec::new();
    lint_c01_cast_cycle(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// C02: Transitive Cast Redundancy
// ══════════════════════════════════════════════════════════════════════

#[test]
fn c02_fires_on_redundant_direct_cast() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Proc", None, true));
    b.categories.push(cat_info("Int", None, false));
    b.categories.push(cat_info("Bool", None, false));
    // Int → Bool → Proc (transitive) AND Int → Proc (direct)
    b.cast_rules.push(CastRule {
        label: "IntToBool".to_string(),
        source_category: "Int".to_string(),
        target_category: "Bool".to_string(),
        shares_infix_with_target: false,
    });
    b.cast_rules.push(CastRule {
        label: "BoolToProc".to_string(),
        source_category: "Bool".to_string(),
        target_category: "Proc".to_string(),
        shares_infix_with_target: false,
    });
    b.cast_rules.push(CastRule {
        label: "IntToProc".to_string(),
        source_category: "Int".to_string(),
        target_category: "Proc".to_string(),
        shares_infix_with_target: false,
    });

    let mut diags = Vec::new();
    lint_c02_transitive_cast_redundancy(&b.ctx(), &mut diags);

    assert!(diags.iter().any(|d| d.id == DiagnosticId::C02));
}

#[test]
fn c02_does_not_fire_without_indirect_path() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Proc", None, true));
    b.categories.push(cat_info("Int", None, false));
    b.cast_rules.push(CastRule {
        label: "IntToProc".to_string(),
        source_category: "Int".to_string(),
        target_category: "Proc".to_string(),
        shares_infix_with_target: false,
    });

    let mut diags = Vec::new();
    lint_c02_transitive_cast_redundancy(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// Stage 10c (2026-05-04): P02 (high-nfa-spillover) tests DELETED
// alongside the lint function and DiagnosticId variant.
// ══════════════════════════════════════════════════════════════════════

// ══════════════════════════════════════════════════════════════════════
// P03: Deep Cast Nesting
// ══════════════════════════════════════════════════════════════════════

#[test]
fn p03_fires_on_deep_chain() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("A", None, true));
    b.categories.push(cat_info("B", None, false));
    b.categories.push(cat_info("C", None, false));
    b.categories.push(cat_info("D", None, false));
    b.categories.push(cat_info("E", None, false));
    // A → B → C → D → E (depth 4)
    b.cast_rules.push(CastRule {
        label: "AtoB".to_string(),
        source_category: "A".to_string(),
        target_category: "B".to_string(),
        shares_infix_with_target: false,
    });
    b.cast_rules.push(CastRule {
        label: "BtoC".to_string(),
        source_category: "B".to_string(),
        target_category: "C".to_string(),
        shares_infix_with_target: false,
    });
    b.cast_rules.push(CastRule {
        label: "CtoD".to_string(),
        source_category: "C".to_string(),
        target_category: "D".to_string(),
        shares_infix_with_target: false,
    });
    b.cast_rules.push(CastRule {
        label: "DtoE".to_string(),
        source_category: "D".to_string(),
        target_category: "E".to_string(),
        shares_infix_with_target: false,
    });

    let mut diags = Vec::new();
    lint_p03_deep_cast_nesting(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::P03);
}

#[test]
fn p03_does_not_fire_on_shallow() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("A", None, true));
    b.categories.push(cat_info("B", None, false));
    b.cast_rules.push(CastRule {
        label: "AtoB".to_string(),
        source_category: "A".to_string(),
        target_category: "B".to_string(),
        shares_infix_with_target: false,
    });

    let mut diags = Vec::new();
    lint_p03_deep_cast_nesting(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// Display formatting
// ══════════════════════════════════════════════════════════════════════

#[test]
fn lint_display_format() {
    let diag = LintDiagnostic {
        id: DiagnosticId::C01,
        name: "cast-cycle",
        severity: LintSeverity::Error,
        category: None,
        rule: None,
        message: "cast cycle detected: Int -> Proc -> Int".to_string(),
        hint: Some("break the cycle by removing one cast direction".to_string()),
        grammar_name: Some("TestGrammar".to_string()),
        source_location: None,
    };
    let s = format!("{}", diag);
    assert!(s.contains("error[C01]"));
    assert!(s.contains("cast cycle detected"));
    assert!(s.contains("= hint:"));
}

#[test]
fn lint_display_no_hint() {
    let diag = LintDiagnostic {
        id: DiagnosticId::G06,
        name: "shadowed-operator",
        severity: LintSeverity::Note,
        category: Some("Int".to_string()),
        rule: None,
        message: "operator `-` is both infix and prefix".to_string(),
        hint: None,
        grammar_name: Some("TestGrammar".to_string()),
        source_location: None,
    };
    let s = format!("{}", diag);
    assert!(s.contains("note[G06]"));
    // Display now includes a context line for category-only lints
    assert!(s.contains("= in category `Int`"));
    assert!(!s.contains("hint"));
}

#[test]
fn lint_display_with_source_location() {
    let diag = LintDiagnostic {
        id: DiagnosticId::G09,
        name: "unbalanced-delimiters",
        severity: LintSeverity::Warning,
        category: Some("Proc".to_string()),
        rule: Some("PIn".to_string()),
        message: "rule `PIn` in category `Proc` has unbalanced delimiters: 0 `(` vs 1 `)`"
            .to_string(),
        hint: Some("add the missing `(` delimiter".to_string()),
        grammar_name: Some("RhoPi".to_string()),
        source_location: Some(crate::SourceLocation { line: 42, column: 9 }),
    };
    let s = format!("{}", diag);
    assert!(s.contains("warning[G09]"));
    assert!(s.contains("--> <macro>:42:9"));
    assert!(s.contains("= in category `Proc`, rule `PIn`"));
    assert!(s.contains("= hint:"));
}

#[test]
fn lint_display_no_location_when_line_zero() {
    let diag = LintDiagnostic {
        id: DiagnosticId::G01,
        name: "left-recursion",
        severity: LintSeverity::Warning,
        category: Some("Int".to_string()),
        rule: Some("Bad".to_string()),
        message: "left-recursive rule".to_string(),
        hint: None,
        grammar_name: Some("Test".to_string()),
        source_location: Some(crate::SourceLocation { line: 0, column: 0 }),
    };
    let s = format!("{}", diag);
    // line=0 means unknown, should not show --> line
    assert!(!s.contains("-->"));
    // But should show category/rule context
    assert!(s.contains("= in category `Int`, rule `Bad`"));
}

// ══════════════════════════════════════════════════════════════════════
// char_edit_distance_is_one
// ══════════════════════════════════════════════════════════════════════

#[test]
fn edit_distance_one_substitution() {
    assert!(char_edit_distance_is_one("+", "*")); // single char sub
    assert!(char_edit_distance_is_one("<=", ">="));
}

#[test]
fn edit_distance_one_insertion() {
    assert!(char_edit_distance_is_one("+", "++")); // insertion
    assert!(char_edit_distance_is_one("<", "<="));
}

#[test]
fn edit_distance_not_one() {
    assert!(!char_edit_distance_is_one("+", "---")); // too different
    assert!(char_edit_distance_is_one("==", "!=")); // 1 sub (first char)
    assert!(!char_edit_distance_is_one("+", "+")); // zero distance
    assert!(!char_edit_distance_is_one("<<", ">>")); // 2 subs
}

// ── A8: Nearly-dead path W07 integration ──

#[test]
fn test_a8_w07_not_emitted_for_well_connected_grammar() {
    // A8: W07 should not fire for a normal 2-category grammar where both
    // categories are well-connected via bidirectional cast rules.
    let mut b = CtxBuilder::new();
    b.categories = vec![cat_info("Proc", None, true), cat_info("Int", Some("i64"), false)];
    let mut cast1 =
        make_rule_info("IntToProc", "Proc", vec![FirstItem::NonTerminal("Int".to_string())], false);
    cast1.is_cast = true;
    let mut cast2 =
        make_rule_info("ProcToInt", "Int", vec![FirstItem::NonTerminal("Proc".to_string())], false);
    cast2.is_cast = true;
    let prefix1 =
        make_rule_info("Par", "Proc", vec![FirstItem::Terminal("Pipe".to_string())], false);
    let prefix2 =
        make_rule_info("NumLit", "Int", vec![FirstItem::Terminal("Integer".to_string())], false);
    b.rules = vec![cast1, cast2, prefix1, prefix2];
    b.first_sets = [
        (
            "Proc".to_string(),
            FirstSet {
                tokens: ["Pipe".to_string()].into(),
                nullable: false,
            },
        ),
        (
            "Int".to_string(),
            FirstSet {
                tokens: ["Integer".to_string()].into(),
                nullable: false,
            },
        ),
    ]
    .into();

    let diags = run_lints(&b.ctx());
    let w07_diags: Vec<_> = diags.iter().filter(|d| d.id == DiagnosticId::W07).collect();
    assert!(
        w07_diags.is_empty(),
        "well-connected grammar should not emit W07: {:?}",
        w07_diags
    );
}

#[test]
fn test_a8_w07_uses_note_severity() {
    // A8: NearlyDeadPath warnings must use Note severity (not Warning)
    // to distinguish from truly dead rules.
    // This test verifies the mapping at the LintDiagnostic construction level.
    let w = crate::pipeline::DeadRuleWarning::NearlyDeadPath {
        rule_label: "TestRule".to_string(),
        category: "TestCat".to_string(),
        derivation_count: 1,
        total_count: 200,
    };
    // Verify display format
    let msg = format!("{}", w);
    assert!(msg.contains("nearly-dead"));
    assert!(msg.contains("1/200"));
}

// ══════════════════════════════════════════════════════════════════════
// Composition Lints (X01–X05)
// ══════════════════════════════════════════════════════════════════════

use crate::automata::semiring::TropicalWeight;
use crate::prediction::DispatchAction;
use crate::token_id::TokenIdMap;
use crate::wfst::{PredictionWfst, WeightedAction, WeightedTransition, WfstState};

/// Build a minimal PredictionWfst with a single start state that dispatches
/// on the given `(token_name, rule_label, weight)` triples.
fn make_prediction_wfst(category: &str, entries: &[(&str, &str, f64)]) -> PredictionWfst {
    let mut token_map = TokenIdMap::new();
    let mut actions = Vec::new();
    let mut transitions = Vec::new();

    for &(token_name, rule_label, weight) in entries {
        let token_id = token_map.get_or_insert(token_name);
        let action_idx = actions.len() as u32;
        actions.push(WeightedAction {
            action: DispatchAction::Direct {
                rule_label: rule_label.to_string(),
                parse_fn: format!("parse_{}", rule_label),
            },
            weight: TropicalWeight::new(weight),
        });
        transitions.push(WeightedTransition {
            from: 0,
            input: token_id,
            action_idx,
            to: 0,
            weight: TropicalWeight::new(weight),
        });
    }

    let start_state = WfstState {
        id: 0,
        is_final: true,
        final_weight: TropicalWeight::new(0.0),
        transitions,
    };

    PredictionWfst {
        category: category.to_string(),
        states: vec![start_state],
        start: 0,
        actions,
        token_map,
        beam_width: None,
        context_labels: HashMap::new(),
    }
}

fn make_comp_ctx<'a>(
    first_sets_a: &'a HashMap<String, FirstSet>,
    first_sets_b: &'a HashMap<String, FirstSet>,
    first_sets_merged: &'a HashMap<String, FirstSet>,
    prediction_wfsts_a: &'a HashMap<String, PredictionWfst>,
    prediction_wfsts_b: &'a HashMap<String, PredictionWfst>,
    shared_categories: &'a [String],
    dead_rules_a: &'a HashSet<String>,
    dead_rules_b: &'a HashSet<String>,
    dead_rules_merged: &'a HashSet<String>,
    rules_a: &'a [RuleInfo],
    rules_b: &'a [RuleInfo],
    terminal_semantics_a: &'a HashMap<String, Vec<(String, String)>>,
    terminal_semantics_b: &'a HashMap<String, Vec<(String, String)>>,
) -> CompositionLintContext<'a> {
    CompositionLintContext {
        first_sets_a,
        first_sets_b,
        first_sets_merged,
        prediction_wfsts_a,
        prediction_wfsts_b,
        shared_categories,
        dead_rules_a,
        dead_rules_b,
        dead_rules_merged,
        rules_a,
        rules_b,
        terminal_semantics_a,
        terminal_semantics_b,
    }
}

// ── X01: Composition Ambiguity Introduction ──

#[test]
fn x01_fires_when_merged_has_new_tokens() {
    // Composition introduces a new token "Star" in the merged FIRST set
    // that was NOT present in either source grammar's FIRST set.
    // This indicates new derivation paths created by the composition.
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));

    let first_a: HashMap<String, FirstSet> = [(
        "Expr".to_string(),
        FirstSet {
            tokens: ["Plus".to_string(), "Ident".to_string()].into(),
            nullable: false,
        },
    )]
    .into();

    let first_b: HashMap<String, FirstSet> = [(
        "Expr".to_string(),
        FirstSet {
            tokens: ["Minus".to_string(), "Ident".to_string()].into(),
            nullable: false,
        },
    )]
    .into();

    // Merged has "Star" which is NOT in A ∪ B = {Plus, Minus, Ident}
    let first_merged: HashMap<String, FirstSet> = [(
        "Expr".to_string(),
        FirstSet {
            tokens: [
                "Plus".to_string(),
                "Minus".to_string(),
                "Ident".to_string(),
                "Star".to_string(),
            ]
            .into(),
            nullable: false,
        },
    )]
    .into();

    let shared = vec!["Expr".to_string()];
    let empty_dead: HashSet<String> = HashSet::new();
    let empty_wfsts: HashMap<String, PredictionWfst> = HashMap::new();
    let empty_rules: Vec<RuleInfo> = Vec::new();
    let empty_sem: HashMap<String, Vec<(String, String)>> = HashMap::new();

    let comp_ctx = make_comp_ctx(
        &first_a,
        &first_b,
        &first_merged,
        &empty_wfsts,
        &empty_wfsts,
        &shared,
        &empty_dead,
        &empty_dead,
        &empty_dead,
        &empty_rules,
        &empty_rules,
        &empty_sem,
        &empty_sem,
    );

    let mut diags = Vec::new();
    lint_x01_composition_ambiguity_introduction(&b.ctx(), &comp_ctx, &mut diags);

    assert_eq!(diags.len(), 1, "expected 1 ambiguity lint for new token Star: {:?}", diags);
    assert_eq!(diags[0].id, DiagnosticId::X01);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
    assert!(
        diags[0].message.contains("Star"),
        "message should mention the new token: {}",
        diags[0].message
    );
}

#[test]
fn x01_does_not_fire_when_merged_is_exact_union() {
    // Merged FIRST set is exactly A ∪ B — no new tokens introduced.
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));

    let first_a: HashMap<String, FirstSet> = [(
        "Expr".to_string(),
        FirstSet {
            tokens: ["Plus".to_string(), "Ident".to_string()].into(),
            nullable: false,
        },
    )]
    .into();

    let first_b: HashMap<String, FirstSet> = [(
        "Expr".to_string(),
        FirstSet {
            tokens: ["Minus".to_string(), "Ident".to_string()].into(),
            nullable: false,
        },
    )]
    .into();

    // Merged = A ∪ B = {Plus, Minus, Ident}
    let first_merged: HashMap<String, FirstSet> = [(
        "Expr".to_string(),
        FirstSet {
            tokens: ["Plus".to_string(), "Minus".to_string(), "Ident".to_string()].into(),
            nullable: false,
        },
    )]
    .into();

    let shared = vec!["Expr".to_string()];
    let empty_dead: HashSet<String> = HashSet::new();
    let empty_wfsts: HashMap<String, PredictionWfst> = HashMap::new();
    let empty_rules: Vec<RuleInfo> = Vec::new();
    let empty_sem: HashMap<String, Vec<(String, String)>> = HashMap::new();

    let comp_ctx = make_comp_ctx(
        &first_a,
        &first_b,
        &first_merged,
        &empty_wfsts,
        &empty_wfsts,
        &shared,
        &empty_dead,
        &empty_dead,
        &empty_dead,
        &empty_rules,
        &empty_rules,
        &empty_sem,
        &empty_sem,
    );

    let mut diags = Vec::new();
    lint_x01_composition_ambiguity_introduction(&b.ctx(), &comp_ctx, &mut diags);

    assert!(diags.is_empty(), "exact union should not trigger ambiguity lint: {:?}", diags);
}

// ── X02: Composition Priority Shadowing ──

#[test]
fn x02_fires_when_a_rule_shadowed_by_b() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));

    let wfst_a: HashMap<String, PredictionWfst> =
        [("Expr".to_string(), make_prediction_wfst("Expr", &[("Plus", "AddA", 0.5)]))].into();

    let wfst_b: HashMap<String, PredictionWfst> =
        [("Expr".to_string(), make_prediction_wfst("Expr", &[("Plus", "AddB", 0.1)]))].into();

    let shared = vec!["Expr".to_string()];
    let first_a: HashMap<String, FirstSet> = [(
        "Expr".to_string(),
        FirstSet {
            tokens: ["Plus".to_string()].into(),
            nullable: false,
        },
    )]
    .into();
    let first_b: HashMap<String, FirstSet> = [(
        "Expr".to_string(),
        FirstSet {
            tokens: ["Plus".to_string()].into(),
            nullable: false,
        },
    )]
    .into();
    let first_merged: HashMap<String, FirstSet> = first_a.clone();
    let empty_dead: HashSet<String> = HashSet::new();
    let empty_rules: Vec<RuleInfo> = Vec::new();
    let empty_sem: HashMap<String, Vec<(String, String)>> = HashMap::new();

    let comp_ctx = make_comp_ctx(
        &first_a,
        &first_b,
        &first_merged,
        &wfst_a,
        &wfst_b,
        &shared,
        &empty_dead,
        &empty_dead,
        &empty_dead,
        &empty_rules,
        &empty_rules,
        &empty_sem,
        &empty_sem,
    );

    let mut diags = Vec::new();
    lint_x02_composition_priority_shadowing(&b.ctx(), &comp_ctx, &mut diags);

    assert_eq!(diags.len(), 1, "expected 1 shadowing lint: {:?}", diags);
    assert_eq!(diags[0].id, DiagnosticId::X02);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
    assert!(diags[0].message.contains("AddA"));
    assert!(diags[0].message.contains("AddB"));
    assert!(diags[0].message.contains("Plus"));
}

#[test]
fn x02_does_not_fire_when_weights_equal() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));

    let wfst_a: HashMap<String, PredictionWfst> =
        [("Expr".to_string(), make_prediction_wfst("Expr", &[("Plus", "AddA", 0.3)]))].into();

    let wfst_b: HashMap<String, PredictionWfst> =
        [("Expr".to_string(), make_prediction_wfst("Expr", &[("Plus", "AddB", 0.3)]))].into();

    let shared = vec!["Expr".to_string()];
    let first_a: HashMap<String, FirstSet> = [(
        "Expr".to_string(),
        FirstSet {
            tokens: ["Plus".to_string()].into(),
            nullable: false,
        },
    )]
    .into();
    let first_b = first_a.clone();
    let first_merged = first_a.clone();
    let empty_dead: HashSet<String> = HashSet::new();
    let empty_rules: Vec<RuleInfo> = Vec::new();
    let empty_sem: HashMap<String, Vec<(String, String)>> = HashMap::new();

    let comp_ctx = make_comp_ctx(
        &first_a,
        &first_b,
        &first_merged,
        &wfst_a,
        &wfst_b,
        &shared,
        &empty_dead,
        &empty_dead,
        &empty_dead,
        &empty_rules,
        &empty_rules,
        &empty_sem,
        &empty_sem,
    );

    let mut diags = Vec::new();
    lint_x02_composition_priority_shadowing(&b.ctx(), &comp_ctx, &mut diags);

    assert!(diags.is_empty(), "equal weights should not trigger shadowing: {:?}", diags);
}

// ── X03: Composition Dead Rule Creation ──

#[test]
fn x03_fires_on_newly_dead_rule() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));

    let dead_a: HashSet<String> = HashSet::new();
    let dead_b: HashSet<String> = HashSet::new();
    let dead_merged: HashSet<String> = ["Foo".to_string()].into();

    let rules_a =
        vec![make_rule_info("Foo", "Expr", vec![FirstItem::Terminal("+".to_string())], false)];

    let empty_first: HashMap<String, FirstSet> = HashMap::new();
    let empty_wfsts: HashMap<String, PredictionWfst> = HashMap::new();
    let empty_sem: HashMap<String, Vec<(String, String)>> = HashMap::new();
    let shared = vec!["Expr".to_string()];

    let comp_ctx = make_comp_ctx(
        &empty_first,
        &empty_first,
        &empty_first,
        &empty_wfsts,
        &empty_wfsts,
        &shared,
        &dead_a,
        &dead_b,
        &dead_merged,
        &rules_a,
        &[],
        &empty_sem,
        &empty_sem,
    );

    let mut diags = Vec::new();
    lint_x03_composition_dead_rule_creation(&b.ctx(), &comp_ctx, &mut diags);

    assert_eq!(diags.len(), 1, "expected 1 newly-dead lint: {:?}", diags);
    assert_eq!(diags[0].id, DiagnosticId::X03);
    assert!(diags[0].message.contains("Foo"));
    assert!(diags[0].message.contains("grammar A"));
}

#[test]
fn x03_does_not_fire_for_already_dead_rules() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));

    let dead_a: HashSet<String> = ["Bar".to_string()].into();
    let dead_b: HashSet<String> = HashSet::new();
    let dead_merged: HashSet<String> = ["Bar".to_string()].into();

    let empty_first: HashMap<String, FirstSet> = HashMap::new();
    let empty_wfsts: HashMap<String, PredictionWfst> = HashMap::new();
    let empty_sem: HashMap<String, Vec<(String, String)>> = HashMap::new();
    let shared = vec!["Expr".to_string()];
    let empty_rules: Vec<RuleInfo> = Vec::new();

    let comp_ctx = make_comp_ctx(
        &empty_first,
        &empty_first,
        &empty_first,
        &empty_wfsts,
        &empty_wfsts,
        &shared,
        &dead_a,
        &dead_b,
        &dead_merged,
        &empty_rules,
        &empty_rules,
        &empty_sem,
        &empty_sem,
    );

    let mut diags = Vec::new();
    lint_x03_composition_dead_rule_creation(&b.ctx(), &comp_ctx, &mut diags);

    assert!(diags.is_empty(), "already-dead rule should not trigger: {:?}", diags);
}

// ── X04: Composition Cast Chain Break ──

#[test]
fn x04_fires_when_cast_chain_broken() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("A", None, true));
    b.categories.push(cat_info("B", None, false));
    b.categories.push(cat_info("C", None, false));

    // Merged grammar has NO cast rules (simulating a broken chain)
    // Source A has a chain: A -> B -> C
    let rules_a = vec![
        {
            let mut r =
                make_rule_info("AtoB", "B", vec![FirstItem::NonTerminal("A".to_string())], false);
            r.is_cast = true;
            r
        },
        {
            let mut r =
                make_rule_info("BtoC", "C", vec![FirstItem::NonTerminal("B".to_string())], false);
            r.is_cast = true;
            r
        },
    ];

    let empty_first: HashMap<String, FirstSet> = HashMap::new();
    let empty_wfsts: HashMap<String, PredictionWfst> = HashMap::new();
    let empty_dead: HashSet<String> = HashSet::new();
    let empty_sem: HashMap<String, Vec<(String, String)>> = HashMap::new();
    let shared: Vec<String> = Vec::new();

    let comp_ctx = make_comp_ctx(
        &empty_first,
        &empty_first,
        &empty_first,
        &empty_wfsts,
        &empty_wfsts,
        &shared,
        &empty_dead,
        &empty_dead,
        &empty_dead,
        &rules_a,
        &[],
        &empty_sem,
        &empty_sem,
    );

    let mut diags = Vec::new();
    lint_x04_composition_cast_chain_break(&b.ctx(), &comp_ctx, &mut diags);

    // Source A has reachability: A->B, A->C (transitive), B->C
    // Merged has NO casts → reachability = {}
    // Broken: {(A,B), (A,C), (B,C)}
    assert_eq!(diags.len(), 3, "expected 3 broken cast chain lints: {:?}", diags);
    assert!(diags.iter().all(|d| d.id == DiagnosticId::X04));
    assert!(diags.iter().all(|d| d.severity == LintSeverity::Error));
}

#[test]
fn x04_does_not_fire_when_chain_preserved() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("A", None, true));
    b.categories.push(cat_info("B", None, false));

    // Merged grammar preserves the cast A -> B
    b.cast_rules.push(CastRule {
        label: "AtoB".to_string(),
        source_category: "A".to_string(),
        target_category: "B".to_string(),
        shares_infix_with_target: false,
    });

    let rules_a = vec![{
        let mut r =
            make_rule_info("AtoB", "B", vec![FirstItem::NonTerminal("A".to_string())], false);
        r.is_cast = true;
        r
    }];

    let empty_first: HashMap<String, FirstSet> = HashMap::new();
    let empty_wfsts: HashMap<String, PredictionWfst> = HashMap::new();
    let empty_dead: HashSet<String> = HashSet::new();
    let empty_sem: HashMap<String, Vec<(String, String)>> = HashMap::new();
    let shared: Vec<String> = Vec::new();

    let comp_ctx = make_comp_ctx(
        &empty_first,
        &empty_first,
        &empty_first,
        &empty_wfsts,
        &empty_wfsts,
        &shared,
        &empty_dead,
        &empty_dead,
        &empty_dead,
        &rules_a,
        &[],
        &empty_sem,
        &empty_sem,
    );

    let mut diags = Vec::new();
    lint_x04_composition_cast_chain_break(&b.ctx(), &comp_ctx, &mut diags);

    assert!(diags.is_empty(), "preserved chain should not trigger: {:?}", diags);
}

// ── X05: Composition Terminal Collision ──

#[test]
fn x05_fires_on_different_semantic_roles() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));

    let sem_a: HashMap<String, Vec<(String, String)>> =
        [("+".to_string(), vec![("Int".to_string(), "infix".to_string())])].into();

    let sem_b: HashMap<String, Vec<(String, String)>> =
        [("+".to_string(), vec![("Str".to_string(), "prefix".to_string())])].into();

    let empty_first: HashMap<String, FirstSet> = HashMap::new();
    let empty_wfsts: HashMap<String, PredictionWfst> = HashMap::new();
    let empty_dead: HashSet<String> = HashSet::new();
    let empty_rules: Vec<RuleInfo> = Vec::new();
    let shared: Vec<String> = Vec::new();

    let comp_ctx = make_comp_ctx(
        &empty_first,
        &empty_first,
        &empty_first,
        &empty_wfsts,
        &empty_wfsts,
        &shared,
        &empty_dead,
        &empty_dead,
        &empty_dead,
        &empty_rules,
        &empty_rules,
        &sem_a,
        &sem_b,
    );

    let mut diags = Vec::new();
    lint_x05_composition_terminal_collision(&b.ctx(), &comp_ctx, &mut diags);

    assert_eq!(diags.len(), 1, "expected 1 terminal collision lint: {:?}", diags);
    assert_eq!(diags[0].id, DiagnosticId::X05);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
    assert!(diags[0].message.contains("+"));
    assert!(diags[0].message.contains("infix"));
    assert!(diags[0].message.contains("prefix"));
}

#[test]
fn x05_does_not_fire_on_same_roles() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));

    let sem_a: HashMap<String, Vec<(String, String)>> =
        [("+".to_string(), vec![("Int".to_string(), "infix".to_string())])].into();

    let sem_b: HashMap<String, Vec<(String, String)>> =
        [("+".to_string(), vec![("Float".to_string(), "infix".to_string())])].into();

    let empty_first: HashMap<String, FirstSet> = HashMap::new();
    let empty_wfsts: HashMap<String, PredictionWfst> = HashMap::new();
    let empty_dead: HashSet<String> = HashSet::new();
    let empty_rules: Vec<RuleInfo> = Vec::new();
    let shared: Vec<String> = Vec::new();

    let comp_ctx = make_comp_ctx(
        &empty_first,
        &empty_first,
        &empty_first,
        &empty_wfsts,
        &empty_wfsts,
        &shared,
        &empty_dead,
        &empty_dead,
        &empty_dead,
        &empty_rules,
        &empty_rules,
        &sem_a,
        &sem_b,
    );

    let mut diags = Vec::new();
    lint_x05_composition_terminal_collision(&b.ctx(), &comp_ctx, &mut diags);

    assert!(diags.is_empty(), "same roles should not trigger collision: {:?}", diags);
}

// ── Integration: run_composition_lints ──

#[test]
fn run_composition_lints_collects_all_categories() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));

    // Set up data that triggers X02 (shadowing) and X05 (collision)
    let wfst_a: HashMap<String, PredictionWfst> =
        [("Expr".to_string(), make_prediction_wfst("Expr", &[("Plus", "AddA", 0.8)]))].into();
    let wfst_b: HashMap<String, PredictionWfst> =
        [("Expr".to_string(), make_prediction_wfst("Expr", &[("Plus", "AddB", 0.1)]))].into();

    let shared = vec!["Expr".to_string()];
    let first_a: HashMap<String, FirstSet> = [(
        "Expr".to_string(),
        FirstSet {
            tokens: ["Plus".to_string()].into(),
            nullable: false,
        },
    )]
    .into();
    let first_b = first_a.clone();
    let first_merged = first_a.clone();

    let sem_a: HashMap<String, Vec<(String, String)>> =
        [("*".to_string(), vec![("Int".to_string(), "infix".to_string())])].into();
    let sem_b: HashMap<String, Vec<(String, String)>> =
        [("*".to_string(), vec![("Str".to_string(), "repeat".to_string())])].into();

    let dead_merged: HashSet<String> = ["Orphan".to_string()].into();
    let rules_a = vec![make_rule_info(
        "Orphan",
        "Expr",
        vec![FirstItem::Terminal("~".to_string())],
        false,
    )];
    let empty_dead: HashSet<String> = HashSet::new();

    let comp_ctx = make_comp_ctx(
        &first_a,
        &first_b,
        &first_merged,
        &wfst_a,
        &wfst_b,
        &shared,
        &empty_dead,
        &empty_dead,
        &dead_merged,
        &rules_a,
        &[],
        &sem_a,
        &sem_b,
    );

    let diags = run_composition_lints(&b.ctx(), &comp_ctx);

    // Should have at least X02 (shadowing on Plus) and X05 (collision on *)
    // and X03 (Orphan newly dead)
    let x02_count = diags.iter().filter(|d| d.id == DiagnosticId::X02).count();
    let x03_count = diags.iter().filter(|d| d.id == DiagnosticId::X03).count();
    let x05_count = diags.iter().filter(|d| d.id == DiagnosticId::X05).count();

    assert!(x02_count >= 1, "expected X02 shadowing lint: {:?}", diags);
    assert_eq!(x03_count, 1, "expected 1 X03 dead-rule lint: {:?}", diags);
    assert_eq!(x05_count, 1, "expected 1 X05 collision lint: {:?}", diags);
}

// ── G24: Alpha-Equivalent Rules ──

#[test]
fn test_g24_variable_renamed_rules_deferred_to_g07() {
    // Two rules with different variable names but identical structure:
    //   AddA: x "+" y   (uses vars x, y)
    //   AddB: a "+" b   (uses vars a, b)
    // G07's syntax_signature drops param_names, so these have identical
    // signatures → G07 catches them. G24 should NOT double-report.
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    b.all_syntax.push((
        "AddA".to_string(),
        "Expr".to_string(),
        vec![
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "x".to_string(),
            },
            SyntaxItemSpec::Terminal("+".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "y".to_string(),
            },
        ],
    ));
    b.all_syntax.push((
        "AddB".to_string(),
        "Expr".to_string(),
        vec![
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "a".to_string(),
            },
            SyntaxItemSpec::Terminal("+".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "b".to_string(),
            },
        ],
    ));
    let mut diagnostics = Vec::new();
    lint_g24_alpha_equivalent_rules(&b.ctx(), &mut diagnostics);
    assert!(diagnostics.is_empty(), "G07 covers these; G24 should not double-report");
}

#[test]
fn test_g24_g07_false_positive_different_binding_structure() {
    // G07 incorrectly groups these because it drops param_names:
    //   SelfEq: x "==" x   (same variable used twice — requires both sides identical)
    //   AnyEq:  a "==" b   (different variables — accepts any two sides)
    // G07 signature for both: NT(Expr)|T(==)|NT(Expr) → groups them as "identical"
    // G24 De Bruijn encoding distinguishes them:
    //   SelfEq: [NewVar, ..., VarRef(0), ...]
    //   AnyEq:  [NewVar, ..., NewVar, ...]
    // So G24 should NOT report these as α-equivalent (they genuinely differ).
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    b.all_syntax.push((
        "SelfEq".to_string(),
        "Expr".to_string(),
        vec![
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "x".to_string(),
            },
            SyntaxItemSpec::Terminal("==".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "x".to_string(),
            },
        ],
    ));
    b.all_syntax.push((
        "AnyEq".to_string(),
        "Expr".to_string(),
        vec![
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "a".to_string(),
            },
            SyntaxItemSpec::Terminal("==".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "b".to_string(),
            },
        ],
    ));
    let mut diagnostics = Vec::new();
    lint_g24_alpha_equivalent_rules(&b.ctx(), &mut diagnostics);
    assert!(
        diagnostics.is_empty(),
        "SelfEq and AnyEq have different binding structure; G24 should not group them"
    );
}

#[test]
fn test_g24_structurally_different_rules_not_flagged() {
    // Two rules with different structure — G24 should NOT fire.
    //   Add: x "+" y     (binary infix)
    //   Neg: "-" x       (unary prefix)
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    b.all_syntax.push((
        "Add".to_string(),
        "Expr".to_string(),
        vec![
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "x".to_string(),
            },
            SyntaxItemSpec::Terminal("+".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "y".to_string(),
            },
        ],
    ));
    b.all_syntax.push((
        "Neg".to_string(),
        "Expr".to_string(),
        vec![
            SyntaxItemSpec::Terminal("-".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "x".to_string(),
            },
        ],
    ));
    let mut diagnostics = Vec::new();
    lint_g24_alpha_equivalent_rules(&b.ctx(), &mut diagnostics);
    assert!(diagnostics.is_empty(), "no G24 for structurally different rules");
}

#[test]
fn test_g24_same_vars_different_structure_not_flagged() {
    // Two rules with same variable names but different structure — G24 should NOT fire.
    //   Pair: x "," y
    //   Add:  x "+" y
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    b.all_syntax.push((
        "Pair".to_string(),
        "Expr".to_string(),
        vec![
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "x".to_string(),
            },
            SyntaxItemSpec::Terminal(",".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "y".to_string(),
            },
        ],
    ));
    b.all_syntax.push((
        "Add".to_string(),
        "Expr".to_string(),
        vec![
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "x".to_string(),
            },
            SyntaxItemSpec::Terminal("+".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "y".to_string(),
            },
        ],
    ));
    let mut diagnostics = Vec::new();
    lint_g24_alpha_equivalent_rules(&b.ctx(), &mut diagnostics);
    assert!(diagnostics.is_empty(), "no G24 for rules with different terminals");
}

#[test]
fn test_g24_exact_duplicates_deferred_to_g07() {
    // Two rules with IDENTICAL syntax (including variable names) — G07 territory.
    // G24 should NOT fire because sigs.len() == 1 (exact match).
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    let syntax = vec![
        SyntaxItemSpec::NonTerminal {
            category: "Expr".to_string(),
            param_name: "x".to_string(),
        },
        SyntaxItemSpec::Terminal("+".to_string()),
        SyntaxItemSpec::NonTerminal {
            category: "Expr".to_string(),
            param_name: "y".to_string(),
        },
    ];
    b.all_syntax
        .push(("Add1".to_string(), "Expr".to_string(), syntax.clone()));
    b.all_syntax
        .push(("Add2".to_string(), "Expr".to_string(), syntax));
    let mut diagnostics = Vec::new();
    lint_g24_alpha_equivalent_rules(&b.ctx(), &mut diagnostics);
    assert!(diagnostics.is_empty(), "exact duplicates should be left to G07, not G24");
}

#[test]
fn test_debruijn_encoding_alpha_equivalence() {
    // Direct test of the De Bruijn encoding: α-equivalent syntax items
    // must produce identical byte sequences.
    let syntax_a = vec![
        SyntaxItemSpec::NonTerminal {
            category: "Expr".to_string(),
            param_name: "x".to_string(),
        },
        SyntaxItemSpec::Terminal("+".to_string()),
        SyntaxItemSpec::NonTerminal {
            category: "Expr".to_string(),
            param_name: "y".to_string(),
        },
    ];
    let syntax_b = vec![
        SyntaxItemSpec::NonTerminal {
            category: "Expr".to_string(),
            param_name: "a".to_string(),
        },
        SyntaxItemSpec::Terminal("+".to_string()),
        SyntaxItemSpec::NonTerminal {
            category: "Expr".to_string(),
            param_name: "b".to_string(),
        },
    ];
    assert_eq!(
        syntax_item_debruijn_bytes(&syntax_a),
        syntax_item_debruijn_bytes(&syntax_b),
        "α-equivalent syntax must produce identical De Bruijn bytes"
    );
}

#[test]
fn test_debruijn_encoding_different_structure() {
    // Structurally different syntax items must produce DIFFERENT byte sequences.
    let syntax_a = vec![
        SyntaxItemSpec::NonTerminal {
            category: "Expr".to_string(),
            param_name: "x".to_string(),
        },
        SyntaxItemSpec::Terminal("+".to_string()),
        SyntaxItemSpec::NonTerminal {
            category: "Expr".to_string(),
            param_name: "y".to_string(),
        },
    ];
    let syntax_b = vec![
        SyntaxItemSpec::Terminal("-".to_string()),
        SyntaxItemSpec::NonTerminal {
            category: "Expr".to_string(),
            param_name: "x".to_string(),
        },
    ];
    assert_ne!(
        syntax_item_debruijn_bytes(&syntax_a),
        syntax_item_debruijn_bytes(&syntax_b),
        "structurally different syntax must produce different De Bruijn bytes"
    );
}

#[test]
fn test_debruijn_var_reuse_same_slot() {
    // When the same variable appears twice, both references should use the same slot.
    // x "?" x   vs   a "?" a   should be identical
    let syntax_a = vec![
        SyntaxItemSpec::NonTerminal {
            category: "Expr".to_string(),
            param_name: "x".to_string(),
        },
        SyntaxItemSpec::Terminal("?".to_string()),
        SyntaxItemSpec::NonTerminal {
            category: "Expr".to_string(),
            param_name: "x".to_string(),
        },
    ];
    let syntax_b = vec![
        SyntaxItemSpec::NonTerminal {
            category: "Expr".to_string(),
            param_name: "a".to_string(),
        },
        SyntaxItemSpec::Terminal("?".to_string()),
        SyntaxItemSpec::NonTerminal {
            category: "Expr".to_string(),
            param_name: "a".to_string(),
        },
    ];
    let bytes_a = syntax_item_debruijn_bytes(&syntax_a);
    let bytes_b = syntax_item_debruijn_bytes(&syntax_b);
    assert_eq!(bytes_a, bytes_b, "same-var-reuse must produce identical bytes");

    // x "?" y  should differ from  x "?" x  (different binding structure)
    let syntax_c = vec![
        SyntaxItemSpec::NonTerminal {
            category: "Expr".to_string(),
            param_name: "x".to_string(),
        },
        SyntaxItemSpec::Terminal("?".to_string()),
        SyntaxItemSpec::NonTerminal {
            category: "Expr".to_string(),
            param_name: "y".to_string(),
        },
    ];
    assert_ne!(
        bytes_a,
        syntax_item_debruijn_bytes(&syntax_c),
        "different binding structure must produce different bytes"
    );
}

// ══════════════════════════════════════════════════════════════════════
// Info severity and format_diagnostic_colored tests
// ══════════════════════════════════════════════════════════════════════

#[test]
fn info_severity_display() {
    assert_eq!(format!("{}", LintSeverity::Info), "info");
}

#[test]
fn info_severity_ord() {
    assert!(LintSeverity::Info < LintSeverity::Note);
    assert!(LintSeverity::Note < LintSeverity::Warning);
    assert!(LintSeverity::Warning < LintSeverity::Error);
}

#[test]
fn format_diagnostic_colored_info_with_grammar_name() {
    let diag = LintDiagnostic {
        id: DiagnosticId::I01,
        name: "transducer-cascade",
        severity: LintSeverity::Info,
        category: None,
        rule: None,
        message: "transducer cascade: 8 change(s) across 3 categories".to_string(),
        hint: None,
        grammar_name: Some("Ambient".to_string()),
        source_location: None,
    };
    let output = format_diagnostic_colored(&diag);
    // Should contain the severity, lint code, grammar name, and message
    assert!(output.contains("info"), "should contain 'info' severity");
    assert!(output.contains("I01"), "should contain lint code I01");
    assert!(output.contains("(Ambient)"), "should contain grammar name in parens");
    assert!(output.contains("transducer cascade"), "should contain message");
}

#[test]
fn format_diagnostic_colored_no_grammar_name() {
    let diag = LintDiagnostic {
        id: DiagnosticId::I08,
        name: "env-override-active",
        severity: LintSeverity::Warning,
        category: None,
        rule: None,
        message: "PRATTAIL_AUTO_OPTIMIZE override active".to_string(),
        hint: Some("unset PRATTAIL_AUTO_OPTIMIZE".to_string()),
        grammar_name: None,
        source_location: None,
    };
    let output = format_diagnostic_colored(&diag);
    // Should NOT contain grammar name parens
    assert!(!output.contains("()"), "should not contain empty parens");
    assert!(output.contains("warning"), "should contain 'warning' severity");
    assert!(output.contains("I08"), "should contain lint code I08");
    assert!(output.contains("hint:"), "should contain hint");
}

#[test]
fn format_diagnostic_colored_info_with_hint() {
    let diag = LintDiagnostic {
        id: DiagnosticId::I04,
        name: "beam-feature-required",
        severity: LintSeverity::Warning,
        category: None,
        rule: None,
        message: "beam_width: auto requires `wfst-log`".to_string(),
        hint: Some("enable `wfst-log` feature or use explicit beam_width".to_string()),
        grammar_name: Some("TestGrammar".to_string()),
        source_location: None,
    };
    let output = format_diagnostic_colored(&diag);
    assert!(output.contains("I04"), "should contain lint code");
    assert!(output.contains("(TestGrammar)"), "should contain grammar name");
    assert!(output.contains("hint:"), "should contain hint line");
    assert!(output.contains("wfst-log"), "hint should mention wfst-log");
}

// ══════════════════════════════════════════════════════════════════════
// Diagnostic Grouping Tests
// ══════════════════════════════════════════════════════════════════════

fn make_diag(
    id: DiagnosticId,
    name: &'static str,
    severity: LintSeverity,
    category: Option<&str>,
    rule: Option<&str>,
    message: &str,
    hint: Option<&str>,
) -> LintDiagnostic {
    LintDiagnostic {
        id,
        name,
        severity,
        category: category.map(|s| s.to_string()),
        rule: rule.map(|s| s.to_string()),
        message: message.to_string(),
        hint: hint.map(|s| s.to_string()),
        grammar_name: Some("TestGrammar".to_string()),
        source_location: None,
    }
}

#[test]
fn group_empty_input() {
    let result = group_diagnostics(Vec::new());
    assert!(result.is_empty());
}

#[test]
fn group_w01_single_passes_through() {
    let diag = make_diag(
        DiagnosticId::W01,
        "dead-rule",
        LintSeverity::Warning,
        Some("Int"),
        Some("FloatToStr"),
        "rule `FloatToStr` in category `Int` is unreachable",
        Some("remove the rule or add a unique dispatch token"),
    );
    let result = group_diagnostics(vec![diag.clone()]);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].id, DiagnosticId::W01);
    assert_eq!(result[0].category.as_deref(), Some("Int"));
}

#[test]
fn group_w01_multiple_same_type() {
    let hint = "remove the rule or add a unique dispatch token";
    let diags = vec![
        make_diag(
            DiagnosticId::W01,
            "dead-rule",
            LintSeverity::Warning,
            Some("Str"),
            Some("FloatToStr"),
            "rule `FloatToStr` unreachable",
            Some(hint),
        ),
        make_diag(
            DiagnosticId::W01,
            "dead-rule",
            LintSeverity::Warning,
            Some("Str"),
            Some("BoolToStr"),
            "rule `BoolToStr` unreachable",
            Some(hint),
        ),
        make_diag(
            DiagnosticId::W01,
            "dead-rule",
            LintSeverity::Warning,
            Some("Bool"),
            Some("IntToBool"),
            "rule `IntToBool` unreachable",
            Some(hint),
        ),
        make_diag(
            DiagnosticId::W01,
            "dead-rule",
            LintSeverity::Warning,
            Some("Int"),
            Some("FloatToInt"),
            "rule `FloatToInt` unreachable",
            Some(hint),
        ),
        make_diag(
            DiagnosticId::W01,
            "dead-rule",
            LintSeverity::Warning,
            Some("Int"),
            Some("StrToInt"),
            "rule `StrToInt` unreachable",
            Some(hint),
        ),
    ];
    let result = group_diagnostics(diags);
    assert_eq!(result.len(), 1, "5 W01 with same hint should become 1 grouped diagnostic");
    assert_eq!(result[0].id, DiagnosticId::W01);
    assert!(
        result[0].message.contains("5 rules are unreachable"),
        "message: {}",
        result[0].message
    );
    assert!(
        result[0].message.contains("Str: FloatToStr, BoolToStr"),
        "should list Str rules: {}",
        result[0].message
    );
    assert!(
        result[0].message.contains("Bool: IntToBool"),
        "should list Bool rules: {}",
        result[0].message
    );
    assert!(
        result[0].message.contains("Int: FloatToInt, StrToInt"),
        "should list Int rules: {}",
        result[0].message
    );
    assert!(result[0].category.is_none(), "grouped diagnostic has no single category");
}

#[test]
fn group_w01_mixed_types_separate() {
    let diags = vec![
        make_diag(
            DiagnosticId::W01,
            "dead-rule",
            LintSeverity::Warning,
            Some("Str"),
            Some("FloatToStr"),
            "rule unreachable",
            Some("hint A"),
        ),
        make_diag(
            DiagnosticId::W01,
            "dead-rule",
            LintSeverity::Warning,
            Some("Str"),
            Some("BoolToStr"),
            "rule unreachable",
            Some("hint A"),
        ),
        make_diag(
            DiagnosticId::W01,
            "dead-rule",
            LintSeverity::Warning,
            Some("Int"),
            Some("BadRule"),
            "rule unreachable",
            Some("hint B"),
        ),
    ];
    let result = group_diagnostics(diags);
    // Two different hints → two groups (one grouped, one pass-through)
    assert_eq!(result.len(), 2, "different hints produce separate groups");
    assert_eq!(result[0].id, DiagnosticId::W01);
    assert_eq!(result[1].id, DiagnosticId::W01);
}

#[test]
fn group_g03_multiple_categories() {
    let diags = vec![
        make_diag(
            DiagnosticId::G03,
            "ambiguous-prefix",
            LintSeverity::Warning,
            Some("Int"),
            None,
            "ambiguous prefix for token `kw` in Int",
            Some("add unique dispatch tokens"),
        ),
        make_diag(
            DiagnosticId::G03,
            "ambiguous-prefix",
            LintSeverity::Warning,
            Some("Float"),
            None,
            "ambiguous prefix for token `kw` in Float",
            Some("add unique dispatch tokens"),
        ),
    ];
    let result = group_diagnostics(diags);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].id, DiagnosticId::G03);
    assert!(
        result[0].message.contains("2 ambiguous prefix dispatch"),
        "message: {}",
        result[0].message
    );
    assert!(result[0].message.contains("2 categories"), "message: {}", result[0].message);
}

#[test]
fn group_g08_all_merged() {
    let diags = vec![
        make_diag(
            DiagnosticId::G08,
            "missing-cast-to-root",
            LintSeverity::Warning,
            Some("Float"),
            None,
            "no value-flow path from category `Float` to primary category `Proc`",
            Some("add a value-flow edge"),
        ),
        make_diag(
            DiagnosticId::G08,
            "missing-cast-to-root",
            LintSeverity::Warning,
            Some("Bool"),
            None,
            "no value-flow path from category `Bool` to primary category `Proc`",
            Some("add a value-flow edge"),
        ),
        make_diag(
            DiagnosticId::G08,
            "missing-cast-to-root",
            LintSeverity::Warning,
            Some("Str"),
            None,
            "no value-flow path from category `Str` to primary category `Proc`",
            Some("add a value-flow edge"),
        ),
    ];
    let result = group_diagnostics(diags);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].id, DiagnosticId::G08);
    assert!(
        result[0]
            .message
            .contains("3 categories have no value-flow path"),
        "message: {}",
        result[0].message
    );
    assert!(
        result[0].message.contains("isolated: Float, Bool, Str"),
        "message: {}",
        result[0].message
    );
}

#[test]
fn group_preserves_non_grouped_ids() {
    let diags = vec![
        make_diag(
            DiagnosticId::G01,
            "left-recursion",
            LintSeverity::Warning,
            Some("Int"),
            Some("Bad"),
            "left recursive",
            None,
        ),
        make_diag(
            DiagnosticId::C01,
            "cast-cycle",
            LintSeverity::Error,
            None,
            None,
            "cycle detected",
            None,
        ),
    ];
    let result = group_diagnostics(diags);
    assert_eq!(result.len(), 2);
    assert_eq!(result[0].id, DiagnosticId::G01);
    assert_eq!(result[1].id, DiagnosticId::C01);
}

#[test]
fn group_mixed_ids_preserves_order() {
    let diags = vec![
        make_diag(
            DiagnosticId::G01,
            "left-recursion",
            LintSeverity::Warning,
            Some("Int"),
            None,
            "left recursive",
            None,
        ),
        make_diag(
            DiagnosticId::W01,
            "dead-rule",
            LintSeverity::Warning,
            Some("Str"),
            Some("R1"),
            "dead",
            Some("hint"),
        ),
        make_diag(DiagnosticId::C01, "cast-cycle", LintSeverity::Error, None, None, "cycle", None),
        make_diag(
            DiagnosticId::W01,
            "dead-rule",
            LintSeverity::Warning,
            Some("Str"),
            Some("R2"),
            "dead",
            Some("hint"),
        ),
    ];
    let result = group_diagnostics(diags);
    // G01 at index 0, W01 grouped at index 1 (first occurrence position), C01 at index 2
    assert_eq!(result.len(), 3);
    assert_eq!(result[0].id, DiagnosticId::G01);
    assert_eq!(result[1].id, DiagnosticId::W01);
    assert!(result[1].message.contains("2 rules are unreachable"), "W01 should be grouped");
    assert_eq!(result[2].id, DiagnosticId::C01);
}

#[test]
fn group_g27_by_general_rule() {
    let diags = vec![
        make_diag(
            DiagnosticId::G27,
            "rule-subsumption-candidate",
            LintSeverity::Warning,
            None,
            None,
            "rule `AmbNew` may be subsumed by more general rule `AmbCong`",
            Some("review"),
        ),
        make_diag(
            DiagnosticId::G27,
            "rule-subsumption-candidate",
            LintSeverity::Warning,
            None,
            None,
            "rule `OutRule` may be subsumed by more general rule `AmbCong`",
            Some("review"),
        ),
        make_diag(
            DiagnosticId::G27,
            "rule-subsumption-candidate",
            LintSeverity::Warning,
            None,
            None,
            "rule `FooRule` may be subsumed by more general rule `AmbCong`",
            Some("review"),
        ),
    ];
    let result = group_diagnostics(diags);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].id, DiagnosticId::G27);
    assert!(
        result[0].message.contains("3 rules may be subsumed"),
        "message: {}",
        result[0].message
    );
    assert!(
        result[0]
            .message
            .contains("candidates: AmbNew, OutRule, FooRule"),
        "message: {}",
        result[0].message
    );
}

#[test]
fn group_g27_different_generals() {
    let diags = vec![
        make_diag(
            DiagnosticId::G27,
            "rule-subsumption-candidate",
            LintSeverity::Warning,
            None,
            None,
            "rule `A` may be subsumed by more general rule `Gen1`",
            Some("review"),
        ),
        make_diag(
            DiagnosticId::G27,
            "rule-subsumption-candidate",
            LintSeverity::Warning,
            None,
            None,
            "rule `B` may be subsumed by more general rule `Gen2`",
            Some("review"),
        ),
    ];
    let result = group_diagnostics(diags);
    // Two different general rules → each passes through individually (single-item groups)
    assert_eq!(result.len(), 2);
    assert_eq!(result[0].id, DiagnosticId::G27);
    assert_eq!(result[1].id, DiagnosticId::G27);
}

#[test]
fn group_w05_by_category() {
    let diags: Vec<LintDiagnostic> = (0..5)
            .map(|i| make_diag(DiagnosticId::W05, "composed-dispatch-ambiguity", LintSeverity::Warning,
                Some("Float"), None,
                &format!(
                    "2-way ambiguity at DFA state {}: 2 derivations\n\
                     \x20 - Token::KwFn → rule FnFloat (weight 1.00)\n\
                     \x20 - Token::KwFn → rule Ident (weight 11.00)\n\
                     \x20 Resolved by tropical shortest path → FnFloat",
                    i
                ),
                Some("WFST weights are auto-assigned by rule specificity and declaration order; restructure rules to have distinct first tokens, or reorder rule declarations to change priority"),
            ))
            .chain((0..3).map(|i| make_diag(DiagnosticId::W05, "composed-dispatch-ambiguity", LintSeverity::Warning,
                Some("Int"), None,
                &format!(
                    "2-way ambiguity at DFA state {}: 2 derivations\n\
                     \x20 - Token::KwInt → rule IntCast (weight 1.00)\n\
                     \x20 - Token::KwInt → rule Ident (weight 11.00)\n\
                     \x20 Resolved by tropical shortest path → IntCast",
                    i + 10
                ),
                Some("WFST weights are auto-assigned by rule specificity and declaration order; restructure rules to have distinct first tokens, or reorder rule declarations to change priority"),
            )))
            .collect();
    let result = group_diagnostics(diags);
    assert_eq!(
        result.len(),
        1,
        "8 W05 should become 1 grouped: {:#?}",
        result.iter().map(|d| &d.message).collect::<Vec<_>>()
    );
    assert_eq!(result[0].id, DiagnosticId::W05);
    assert!(
        result[0].message.contains("8 ambiguities resolved"),
        "message: {}",
        result[0].message
    );
    assert!(result[0].message.contains("Float:"), "should list Float: {}", result[0].message);
    assert!(result[0].message.contains("Int:"), "should list Int: {}", result[0].message);
}

#[test]
fn group_w05_single_passes_through() {
    let diag = make_diag(
        DiagnosticId::W05,
        "composed-dispatch-ambiguity",
        LintSeverity::Warning,
        Some("Float"),
        None,
        "2-way ambiguity at DFA state 0",
        Some("hint"),
    );
    let result = group_diagnostics(vec![diag]);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].category.as_deref(), Some("Float"));
}

#[test]
fn group_w07_multiple() {
    let diags = vec![
        make_diag(
            DiagnosticId::W07,
            "nearly-dead-path",
            LintSeverity::Note,
            Some("Str"),
            Some("R1"),
            "nearly dead",
            Some("hint"),
        ),
        make_diag(
            DiagnosticId::W07,
            "nearly-dead-path",
            LintSeverity::Note,
            Some("Str"),
            Some("R2"),
            "nearly dead",
            Some("hint"),
        ),
        make_diag(
            DiagnosticId::W07,
            "nearly-dead-path",
            LintSeverity::Note,
            Some("Bool"),
            Some("R3"),
            "nearly dead",
            Some("hint"),
        ),
    ];
    let result = group_diagnostics(diags);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].id, DiagnosticId::W07);
    assert!(
        result[0].message.contains("3 rules on nearly-dead paths"),
        "message: {}",
        result[0].message
    );
    assert!(result[0].message.contains("Bool: R3"), "message: {}", result[0].message);
    assert!(result[0].message.contains("Str: R1, R2"), "message: {}", result[0].message);
}

// ══════════════════════════════════════════════════════════════════════
// S01: Safety Violation
// ══════════════════════════════════════════════════════════════════════

#[test]
fn s01_fires_on_unsafe() {
    let mut b = CtxBuilder::new();
    b.safety_result_data = Some(crate::verify::SafetyResult {
        safe: false,
        initial_weight: crate::automata::semiring::BooleanWeight(true),
        witness_trace: vec![],
    });
    let mut diags = Vec::new();
    lint_s01_safety_violation(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::S01);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
}

#[test]
fn s01_silent_when_safe() {
    let mut b = CtxBuilder::new();
    b.safety_result_data = Some(crate::verify::SafetyResult {
        safe: true,
        initial_weight: crate::automata::semiring::BooleanWeight(true),
        witness_trace: vec![],
    });
    let mut diags = Vec::new();
    lint_s01_safety_violation(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// S02: Safety Verified
// ══════════════════════════════════════════════════════════════════════

#[test]
fn s02_fires_when_safe() {
    let mut b = CtxBuilder::new();
    b.safety_result_data = Some(crate::verify::SafetyResult {
        safe: true,
        initial_weight: crate::automata::semiring::BooleanWeight(true),
        witness_trace: vec![],
    });
    let mut diags = Vec::new();
    lint_s02_safety_verified(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::S02);
    assert_eq!(diags[0].severity, LintSeverity::Note);
}

#[test]
fn s02_silent_when_unsafe() {
    let mut b = CtxBuilder::new();
    b.safety_result_data = Some(crate::verify::SafetyResult {
        safe: false,
        initial_weight: crate::automata::semiring::BooleanWeight(true),
        witness_trace: vec![],
    });
    let mut diags = Vec::new();
    lint_s02_safety_verified(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// S03: CEGAR Refinement
// ══════════════════════════════════════════════════════════════════════

#[test]
fn s03_fires_with_cegar_log() {
    let mut b = CtxBuilder::new();
    b.cegar_result_data = Some(crate::cegar::CegarLog {
        steps: vec![crate::cegar::RefinementStep {
            level: crate::cegar::AbstractionLevel::Boolean,
            verdict: crate::verify::Verdict::Verified,
            counterexample: None,
            is_spurious: false,
            refinement_action: "none".to_string(),
        }],
    });
    let mut diags = Vec::new();
    lint_s03_cegar_refinement(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::S03);
    assert_eq!(diags[0].severity, LintSeverity::Note);
}

#[test]
fn s03_silent_when_none() {
    let b = CtxBuilder::new();
    let mut diags = Vec::new();
    lint_s03_cegar_refinement(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// S06: Algebraic Summary
// ══════════════════════════════════════════════════════════════════════

#[test]
fn s06_fires_with_summary() {
    let mut b = CtxBuilder::new();
    b.algebraic_result_data = Some(crate::algebraic::AlgebraicSummary {
        scc_count: 3,
        path_expression_count: 2,
        scc_summaries: vec!["SCC0".to_string()],
    });
    let mut diags = Vec::new();
    lint_s06_algebraic_summary(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::S06);
    assert_eq!(diags[0].severity, LintSeverity::Note);
}

#[test]
fn s06_silent_when_none() {
    let b = CtxBuilder::new();
    let mut diags = Vec::new();
    lint_s06_algebraic_summary(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// P06: Analysis Pipeline Cost
// ══════════════════════════════════════════════════════════════════════

#[test]
fn p06_fires_on_meaningful_elapsed() {
    let mut b = CtxBuilder::new();
    b.math_analysis_elapsed_data = Some(std::time::Duration::from_millis(5));
    let mut diags = Vec::new();
    lint_p06_analysis_pipeline_cost(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::P06);
    assert_eq!(diags[0].severity, LintSeverity::Note);
}

#[test]
fn p06_silent_on_trivial_elapsed() {
    let mut b = CtxBuilder::new();
    b.math_analysis_elapsed_data = Some(std::time::Duration::from_micros(10));
    let mut diags = Vec::new();
    lint_p06_analysis_pipeline_cost(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// T01-T04: TRS Analysis (feature = "trs-analysis")
// ══════════════════════════════════════════════════════════════════════

#[test]
fn t01_fires_on_non_joinable() {
    use crate::confluence::{ConfluenceAnalysis, CriticalPair, JoinabilityResult, Term};
    let mut b = CtxBuilder::new();
    b.confluence_result_data = Some(ConfluenceAnalysis {
        is_confluent: false,
        critical_pairs: vec![CriticalPair {
            term1: Term::var("x"),
            term2: Term::var("y"),
            rule1_index: 0,
            rule2_index: 1,
            overlap_position: vec![0],
        }],
        joinability_results: vec![JoinabilityResult::NotJoinable {
            normal_form1: Term::var("x"),
            normal_form2: Term::var("y"),
        }],
        non_joinable_count: 1,
        unknown_count: 0,
    });
    let mut diags = Vec::new();
    lint_t01_non_joinable_critical_pair(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::T01);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
}

#[test]
fn t01_silent_when_none() {
    let b = CtxBuilder::new();
    let mut diags = Vec::new();
    lint_t01_non_joinable_critical_pair(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

#[test]
fn t02_fires_when_confluent() {
    use crate::confluence::ConfluenceAnalysis;
    let mut b = CtxBuilder::new();
    b.confluence_result_data = Some(ConfluenceAnalysis {
        is_confluent: true,
        critical_pairs: vec![],
        joinability_results: vec![],
        non_joinable_count: 0,
        unknown_count: 0,
    });
    let mut diags = Vec::new();
    lint_t02_confluence_verified(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::T02);
    assert_eq!(diags[0].severity, LintSeverity::Note);
}

#[test]
fn t02_silent_when_not_confluent() {
    use crate::confluence::ConfluenceAnalysis;
    let mut b = CtxBuilder::new();
    b.confluence_result_data = Some(ConfluenceAnalysis {
        is_confluent: false,
        critical_pairs: vec![],
        joinability_results: vec![],
        non_joinable_count: 0,
        unknown_count: 0,
    });
    let mut diags = Vec::new();
    lint_t02_confluence_verified(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

#[test]
fn t03_fires_on_non_terminating() {
    use crate::termination::TerminationResult;
    let mut b = CtxBuilder::new();
    b.termination_result_data = Some(TerminationResult::PotentiallyNonTerminating {
        reason: "cycle in SCC".to_string(),
        problematic_sccs: vec![0],
    });
    let mut diags = Vec::new();
    lint_t03_non_terminating_cycle(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::T03);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
}

#[test]
fn t03_silent_when_terminating() {
    use crate::termination::TerminationResult;
    let mut b = CtxBuilder::new();
    b.termination_result_data = Some(TerminationResult::Terminating);
    let mut diags = Vec::new();
    lint_t03_non_terminating_cycle(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

#[test]
fn t04_fires_when_terminating() {
    use crate::termination::TerminationResult;
    let mut b = CtxBuilder::new();
    b.termination_result_data = Some(TerminationResult::Terminating);
    let mut diags = Vec::new();
    lint_t04_termination_verified(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::T04);
    assert_eq!(diags[0].severity, LintSeverity::Note);
}

#[test]
fn t04_silent_when_not_terminating() {
    use crate::termination::TerminationResult;
    let mut b = CtxBuilder::new();
    b.termination_result_data = Some(TerminationResult::PotentiallyNonTerminating {
        reason: "cycle".to_string(),
        problematic_sccs: vec![0],
    });
    let mut diags = Vec::new();
    lint_t04_termination_verified(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// V01-V02: VPA (feature = "vpa")
// ══════════════════════════════════════════════════════════════════════

#[test]
fn v01_fires_when_determinizable() {
    let mut b = CtxBuilder::new();
    b.vpa_result_data = Some(crate::vpa::VpaAnalysis {
        is_determinizable: true,
        alphabet_mismatches: vec![],
        state_count: 5,
        max_nesting_bound: 5,
    });
    let mut diags = Vec::new();
    lint_v01_vpa_determinizable(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::V01);
    assert_eq!(diags[0].severity, LintSeverity::Note);
}

#[test]
fn v01_silent_when_not_determinizable() {
    let mut b = CtxBuilder::new();
    b.vpa_result_data = Some(crate::vpa::VpaAnalysis {
        is_determinizable: false,
        alphabet_mismatches: vec![],
        state_count: 5,
        max_nesting_bound: 5,
    });
    let mut diags = Vec::new();
    lint_v01_vpa_determinizable(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

#[test]
fn v02_fires_on_mismatch() {
    let mut b = CtxBuilder::new();
    b.vpa_result_data = Some(crate::vpa::VpaAnalysis {
        is_determinizable: false,
        alphabet_mismatches: vec!["|".to_string()],
        state_count: 3,
        max_nesting_bound: 3,
    });
    let mut diags = Vec::new();
    lint_v02_vpa_alphabet_mismatch(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::V02);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
}

#[test]
fn v02_silent_when_no_mismatch() {
    let mut b = CtxBuilder::new();
    b.vpa_result_data = Some(crate::vpa::VpaAnalysis {
        is_determinizable: true,
        alphabet_mismatches: vec![],
        state_count: 3,
        max_nesting_bound: 3,
    });
    let mut diags = Vec::new();
    lint_v02_vpa_alphabet_mismatch(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// V03-V04: WTA (feature = "tree-automata")
// ══════════════════════════════════════════════════════════════════════

#[test]
fn v03_fires_on_unrecognized() {
    let mut b = CtxBuilder::new();
    b.wta_result_data = Some(crate::tree_automaton::WtaAnalysis {
        unrecognized_terms: vec!["BadTerm".to_string()],
        hot_paths: vec![],
        state_count: 3,
        transition_count: 2,
    });
    let mut diags = Vec::new();
    lint_v03_wta_unrecognized_term(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::V03);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
}

#[test]
fn v03_silent_when_all_recognized() {
    let mut b = CtxBuilder::new();
    b.wta_result_data = Some(crate::tree_automaton::WtaAnalysis {
        unrecognized_terms: vec![],
        hot_paths: vec![],
        state_count: 3,
        transition_count: 2,
    });
    let mut diags = Vec::new();
    lint_v03_wta_unrecognized_term(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

#[test]
fn v04_fires_on_hot_path() {
    let mut b = CtxBuilder::new();
    b.wta_result_data = Some(crate::tree_automaton::WtaAnalysis {
        unrecognized_terms: vec![],
        hot_paths: vec!["Add→Int".to_string()],
        state_count: 3,
        transition_count: 2,
    });
    let mut diags = Vec::new();
    lint_v04_wta_hot_path(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::V04);
    assert_eq!(diags[0].severity, LintSeverity::Note);
}

#[test]
fn v04_silent_when_no_hot_paths() {
    let mut b = CtxBuilder::new();
    b.wta_result_data = Some(crate::tree_automaton::WtaAnalysis {
        unrecognized_terms: vec![],
        hot_paths: vec![],
        state_count: 3,
        transition_count: 2,
    });
    let mut diags = Vec::new();
    lint_v04_wta_hot_path(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// S04: EWPDS Merge Site (feature = "wpds-extended")
// ══════════════════════════════════════════════════════════════════════

#[test]
fn s04_fires_with_merge_sites() {
    let mut b = CtxBuilder::new();
    b.ewpds_result_data = Some(crate::ewpds::EwpdsAnalysis {
        merge_site_count: 2,
        merge_site_labels: vec!["PNew".to_string(), "Match".to_string()],
    });
    let mut diags = Vec::new();
    lint_s04_ewpds_merge_site(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::S04);
    assert_eq!(diags[0].severity, LintSeverity::Note);
}

#[test]
fn s04_silent_when_no_sites() {
    let mut b = CtxBuilder::new();
    b.ewpds_result_data = Some(crate::ewpds::EwpdsAnalysis {
        merge_site_count: 0,
        merge_site_labels: vec![],
    });
    let mut diags = Vec::new();
    lint_s04_ewpds_merge_site(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// S05: ARA Invariant (feature = "wpds-ara")
// ══════════════════════════════════════════════════════════════════════

#[test]
fn s05_fires_with_ara() {
    let mut b = CtxBuilder::new();
    b.ara_result_data = Some(crate::ara::AraAnalysis {
        dimension: 3,
        invariant_count: 2,
        invariants: vec![
            ("Cat_A".to_string(), "x >= 0".to_string()),
            ("Cat_B".to_string(), "y <= 1".to_string()),
        ],
    });
    let mut diags = Vec::new();
    lint_s05_ara_invariant(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::S05);
    assert_eq!(diags[0].severity, LintSeverity::Note);
}

#[test]
fn s05_silent_when_none() {
    let b = CtxBuilder::new();
    let mut diags = Vec::new();
    lint_s05_ara_invariant(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// N01-N02: Petri Net (feature = "petri")
// ══════════════════════════════════════════════════════════════════════

#[test]
fn n01_fires_on_deadlock() {
    let mut b = CtxBuilder::new();
    b.petri_result_data = Some(crate::petri::PetriAnalysis {
        has_deadlock_risk: true,
        unbounded_places: vec![],
        place_count: 4,
        transition_count: 3,
    });
    let mut diags = Vec::new();
    lint_n01_deadlock_risk(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::N01);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
}

#[test]
fn n01_silent_when_no_deadlock() {
    let mut b = CtxBuilder::new();
    b.petri_result_data = Some(crate::petri::PetriAnalysis {
        has_deadlock_risk: false,
        unbounded_places: vec![],
        place_count: 4,
        transition_count: 3,
    });
    let mut diags = Vec::new();
    lint_n01_deadlock_risk(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

#[test]
fn n02_fires_on_unbounded() {
    let mut b = CtxBuilder::new();
    b.petri_result_data = Some(crate::petri::PetriAnalysis {
        has_deadlock_risk: false,
        unbounded_places: vec!["channel_in".to_string()],
        place_count: 4,
        transition_count: 3,
    });
    let mut diags = Vec::new();
    lint_n02_unbounded_channel(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::N02);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
}

#[test]
fn n02_silent_when_bounded() {
    let mut b = CtxBuilder::new();
    b.petri_result_data = Some(crate::petri::PetriAnalysis {
        has_deadlock_risk: false,
        unbounded_places: vec![],
        place_count: 4,
        transition_count: 3,
    });
    let mut diags = Vec::new();
    lint_n02_unbounded_channel(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// N03-N04: Nominal (feature = "nominal")
// ══════════════════════════════════════════════════════════════════════

#[test]
fn n03_fires_on_scope_violation() {
    let mut b = CtxBuilder::new();
    b.nominal_result_data = Some(crate::nominal::NominalAnalysis {
        scope_violations: vec![("x".to_string(), "rule Y".to_string())],
        narrowing_candidates: vec![],
        orbit_count: 1,
    });
    let mut diags = Vec::new();
    lint_n03_scope_violation(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::N03);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
}

#[test]
fn n03_silent_when_no_violations() {
    let mut b = CtxBuilder::new();
    b.nominal_result_data = Some(crate::nominal::NominalAnalysis {
        scope_violations: vec![],
        narrowing_candidates: vec![],
        orbit_count: 1,
    });
    let mut diags = Vec::new();
    lint_n03_scope_violation(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

#[test]
fn n04_fires_on_narrowing() {
    let mut b = CtxBuilder::new();
    b.nominal_result_data = Some(crate::nominal::NominalAnalysis {
        scope_violations: vec![],
        narrowing_candidates: vec![("x".to_string(), "narrow to inner scope".to_string())],
        orbit_count: 1,
    });
    let mut diags = Vec::new();
    lint_n04_scope_narrowing(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::N04);
    assert_eq!(diags[0].severity, LintSeverity::Note);
}

#[test]
fn n04_silent_when_no_candidates() {
    let mut b = CtxBuilder::new();
    b.nominal_result_data = Some(crate::nominal::NominalAnalysis {
        scope_violations: vec![],
        narrowing_candidates: vec![],
        orbit_count: 1,
    });
    let mut diags = Vec::new();
    lint_n04_scope_narrowing(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// N05: Alternating Bisimulation (feature = "alternating")
// ══════════════════════════════════════════════════════════════════════

#[test]
fn n05_fires_on_non_bisimilar() {
    let mut b = CtxBuilder::new();
    b.alternating_result_data = Some(crate::alternating::AlternatingAnalysis {
        non_bisimilar_pairs: vec![("Proc".to_string(), "Name".to_string())],
        state_count: 4,
    });
    let mut diags = Vec::new();
    lint_n05_non_bisimilar(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::N05);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
}

#[test]
fn n05_silent_when_bisimilar() {
    let mut b = CtxBuilder::new();
    b.alternating_result_data = Some(crate::alternating::AlternatingAnalysis {
        non_bisimilar_pairs: vec![],
        state_count: 4,
    });
    let mut diags = Vec::new();
    lint_n05_non_bisimilar(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// L01-L02: LTL (feature = "ltl")
// ══════════════════════════════════════════════════════════════════════

#[test]
fn l01_fires_on_violated() {
    let mut b = CtxBuilder::new();
    b.ltl_results_data = Some(vec![crate::ltl::LtlCheckResult::Violated {
        prefix: vec!["cat_A".to_string()],
        lasso: vec!["loop".to_string()],
    }]);
    let mut diags = Vec::new();
    lint_l01_ltl_violated(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::L01);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
}

#[test]
fn l01_silent_when_satisfied() {
    let mut b = CtxBuilder::new();
    b.ltl_results_data = Some(vec![crate::ltl::LtlCheckResult::Satisfied]);
    let mut diags = Vec::new();
    lint_l01_ltl_violated(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

#[test]
fn l02_fires_when_satisfied() {
    let mut b = CtxBuilder::new();
    b.ltl_results_data = Some(vec![crate::ltl::LtlCheckResult::Satisfied]);
    let mut diags = Vec::new();
    lint_l02_ltl_verified(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::L02);
    assert_eq!(diags[0].severity, LintSeverity::Note);
}

#[test]
fn l02_silent_when_violated() {
    let mut b = CtxBuilder::new();
    b.ltl_results_data = Some(vec![crate::ltl::LtlCheckResult::Violated {
        prefix: vec!["cat_A".to_string()],
        lasso: vec!["loop".to_string()],
    }]);
    let mut diags = Vec::new();
    lint_l02_ltl_verified(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// E01: Provenance Trace (feature = "provenance")
// ══════════════════════════════════════════════════════════════════════

#[test]
fn e01_fires_with_traces() {
    let mut b = CtxBuilder::new();
    b.provenance_result_data = Some(crate::provenance::ProvenanceAnalysis {
        provenance_traces: vec![("rule1".to_string(), "x + y".to_string())],
    });
    let mut diags = Vec::new();
    lint_e01_provenance_trace(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::E01);
    assert_eq!(diags[0].severity, LintSeverity::Note);
}

#[test]
fn e01_silent_when_no_traces() {
    let mut b = CtxBuilder::new();
    b.provenance_result_data =
        Some(crate::provenance::ProvenanceAnalysis { provenance_traces: vec![] });
    let mut diags = Vec::new();
    lint_e01_provenance_trace(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// E02: CRA Cost Anomaly (feature = "cra")
// ══════════════════════════════════════════════════════════════════════

#[test]
fn e02_fires_on_anomaly() {
    let mut b = CtxBuilder::new();
    b.cra_result_data = Some(crate::cra::CraAnalysis {
        cost_anomalies: vec![("register_0".to_string(), "999".to_string())],
        state_count: 3,
        register_count: 2,
    });
    let mut diags = Vec::new();
    lint_e02_cra_cost_anomaly(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::E02);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
}

#[test]
fn e02_silent_when_no_anomalies() {
    let mut b = CtxBuilder::new();
    b.cra_result_data = Some(crate::cra::CraAnalysis {
        cost_anomalies: vec![],
        state_count: 3,
        register_count: 2,
    });
    let mut diags = Vec::new();
    lint_e02_cra_cost_anomaly(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// M01-M02: Morphism (feature = "morphisms")
// ══════════════════════════════════════════════════════════════════════

#[test]
fn m01_fires_on_gap() {
    let mut b = CtxBuilder::new();
    b.morphism_result_data = Some(crate::morphism::MorphismCheck {
        gaps: vec![crate::morphism::MorphismGap {
            kind: crate::morphism::GapKind::MissingSort,
            source_name: "Bool".to_string(),
            description: "no target sort for Bool".to_string(),
        }],
        preservation_failures: vec![],
        is_complete: false,
    });
    let mut diags = Vec::new();
    lint_m01_morphism_gap(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::M01);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
}

#[test]
fn m01_silent_when_complete() {
    let mut b = CtxBuilder::new();
    b.morphism_result_data = Some(crate::morphism::MorphismCheck {
        gaps: vec![],
        preservation_failures: vec![],
        is_complete: true,
    });
    let mut diags = Vec::new();
    lint_m01_morphism_gap(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

#[test]
fn m02_fires_on_failure() {
    let mut b = CtxBuilder::new();
    b.morphism_result_data = Some(crate::morphism::MorphismCheck {
        gaps: vec![],
        preservation_failures: vec!["eq1 not preserved".to_string()],
        is_complete: true,
    });
    let mut diags = Vec::new();
    lint_m02_morphism_preservation_failure(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::M02);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
}

#[test]
fn m02_silent_when_preserved() {
    let mut b = CtxBuilder::new();
    b.morphism_result_data = Some(crate::morphism::MorphismCheck {
        gaps: vec![],
        preservation_failures: vec![],
        is_complete: true,
    });
    let mut diags = Vec::new();
    lint_m02_morphism_preservation_failure(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// K01-K02: KAT (feature = "kat")
// ══════════════════════════════════════════════════════════════════════

#[test]
fn k01_fires_on_hoare_failure() {
    let mut b = CtxBuilder::new();
    b.kat_result_data = Some(crate::kat::KatCheck {
        hoare_results: vec![("triple1".to_string(), false)],
        equivalence_results: vec![],
    });
    let mut diags = Vec::new();
    lint_k01_hoare_failure(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::K01);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
}

#[test]
fn k01_silent_when_hoare_passes() {
    let mut b = CtxBuilder::new();
    b.kat_result_data = Some(crate::kat::KatCheck {
        hoare_results: vec![("triple1".to_string(), true)],
        equivalence_results: vec![],
    });
    let mut diags = Vec::new();
    lint_k01_hoare_failure(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

#[test]
fn k02_fires_with_equivalence() {
    let mut b = CtxBuilder::new();
    b.kat_result_data = Some(crate::kat::KatCheck {
        hoare_results: vec![],
        equivalence_results: vec![("e1".to_string(), "e2".to_string(), true)],
    });
    let mut diags = Vec::new();
    lint_k02_kat_equivalence(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::K02);
    assert_eq!(diags[0].severity, LintSeverity::Note);
}

#[test]
fn k02_silent_when_none() {
    let b = CtxBuilder::new();
    let mut diags = Vec::new();
    lint_k02_kat_equivalence(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// A01: Fixpoint Non-Convergence
// ══════════════════════════════════════════════════════════════════════

#[test]
fn a01_fires_on_depth_growth_pattern() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Proc", None, true));
    // Rule with 2 self-referential NTs and <=1 terminal (depth-growth pattern)
    b.all_syntax.push((
        "Wrap".to_string(),
        "Proc".to_string(),
        vec![
            SyntaxItemSpec::NonTerminal {
                category: "Proc".to_string(),
                param_name: "a".to_string(),
            },
            SyntaxItemSpec::Terminal("|".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Proc".to_string(),
                param_name: "b".to_string(),
            },
        ],
    ));

    let mut diags = Vec::new();
    lint_a01_fixpoint_non_convergence(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::A01);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
    assert!(diags[0].message.contains("Wrap"));
}

#[test]
fn a01_silent_on_normal_infix() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    // Standard infix: 2 self-refs but 2 terminals => terminal_count > 1, no fire
    b.all_syntax.push((
        "Add".to_string(),
        "Int".to_string(),
        vec![
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "a".to_string(),
            },
            SyntaxItemSpec::Terminal("+".to_string()),
            SyntaxItemSpec::Terminal("+".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "b".to_string(),
            },
        ],
    ));

    let mut diags = Vec::new();
    lint_a01_fixpoint_non_convergence(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// A05: Self-Referential Equation
// ══════════════════════════════════════════════════════════════════════

#[test]
fn a05_fires_on_trivial_identity() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    // Rule with a single self-referential NT
    b.all_syntax.push((
        "Identity".to_string(),
        "Int".to_string(),
        vec![SyntaxItemSpec::NonTerminal {
            category: "Int".to_string(),
            param_name: "x".to_string(),
        }],
    ));

    let mut diags = Vec::new();
    lint_a05_self_referential_equation(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::A05);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
    assert!(diags[0].message.contains("Identity"));
}

#[test]
fn a05_silent_on_multi_item_rule() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    b.all_syntax.push((
        "Neg".to_string(),
        "Int".to_string(),
        vec![
            SyntaxItemSpec::Terminal("-".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Int".to_string(),
                param_name: "x".to_string(),
            },
        ],
    ));

    let mut diags = Vec::new();
    lint_a05_self_referential_equation(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// A09: Ascent Struct Size
// ══════════════════════════════════════════════════════════════════════

#[test]
fn a09_fires_on_large_grammar() {
    let mut b = CtxBuilder::new();
    // 10 categories with many rules => rule_estimate = 60 * 2 = 120 > 100
    for i in 0..10 {
        let name = format!("Cat{}", i);
        b.categories.push(cat_info(&name, None, i == 0));
        // 6 rules per category
        for j in 0..6 {
            b.all_syntax.push((
                format!("Rule{}_{}", i, j),
                name.clone(),
                vec![SyntaxItemSpec::Terminal(format!("t{}_{}", i, j))],
            ));
        }
    }

    let mut diags = Vec::new();
    lint_a09_ascent_struct_size(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::A09);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
    assert!(diags[0].message.contains("Ascent rules"));
}

#[test]
fn a09_silent_on_small_grammar() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    b.all_syntax.push((
        "NumLit".to_string(),
        "Int".to_string(),
        vec![SyntaxItemSpec::Terminal("42".to_string())],
    ));

    let mut diags = Vec::new();
    lint_a09_ascent_struct_size(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// LEX01: Overlapping Token Definitions
// ══════════════════════════════════════════════════════════════════════

#[test]
fn lex01_fires_on_keyword_like_terminal_across_categories() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    b.categories.push(cat_info("Pattern", None, false));
    b.all_syntax.push((
        "ExprLet".to_string(),
        "Expr".to_string(),
        vec![SyntaxItemSpec::Terminal("let".to_string())],
    ));
    b.all_syntax.push((
        "PatternLet".to_string(),
        "Pattern".to_string(),
        vec![SyntaxItemSpec::Terminal("let".to_string())],
    ));

    let mut diags = Vec::new();
    lint_lex01_overlapping_token_defs(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::LEX01);
    assert!(diags[0].message.contains("Expr"));
    assert!(diags[0].message.contains("Pattern"));
}

#[test]
fn lex01_ignores_shared_punctuation() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    b.categories.push(cat_info("Type", None, false));
    b.all_syntax.push((
        "ExprGroup".to_string(),
        "Expr".to_string(),
        vec![SyntaxItemSpec::Terminal("(".to_string())],
    ));
    b.all_syntax.push((
        "TypeGroup".to_string(),
        "Type".to_string(),
        vec![SyntaxItemSpec::Terminal("(".to_string())],
    ));

    let mut diags = Vec::new();
    lint_lex01_overlapping_token_defs(&b.ctx(), &mut diags);

    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// LEX05: Float-Integer Ambiguity
// ══════════════════════════════════════════════════════════════════════

#[test]
fn lex05_fires_when_both_present() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", Some("i64"), true));
    b.categories.push(cat_info("Float", Some("f64"), false));

    let mut diags = Vec::new();
    lint_lex05_float_integer_ambiguity(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::LEX05);
    assert_eq!(diags[0].severity, LintSeverity::Note);
}

#[test]
fn lex05_silent_when_only_integer() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", Some("i64"), true));

    let mut diags = Vec::new();
    lint_lex05_float_integer_ambiguity(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// PAR01: Deep RD Chain
// ══════════════════════════════════════════════════════════════════════

#[test]
fn par01_fires_on_deep_chain() {
    let mut b = CtxBuilder::new();
    // Create a chain: A -> B -> C -> D -> E -> F -> G (depth 6)
    let cats = ["A", "B", "C", "D", "E", "F", "G"];
    for (i, &cat) in cats.iter().enumerate() {
        b.categories.push(cat_info(cat, None, i == 0));
        if i + 1 < cats.len() {
            b.all_syntax.push((
                format!("Rule{}", cat),
                cat.to_string(),
                vec![
                    SyntaxItemSpec::Terminal("(".to_string()),
                    SyntaxItemSpec::NonTerminal {
                        category: cats[i + 1].to_string(),
                        param_name: "x".to_string(),
                    },
                    SyntaxItemSpec::Terminal(")".to_string()),
                ],
            ));
        }
    }

    let mut diags = Vec::new();
    lint_par01_deep_rd_chain(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::PAR01);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
    assert!(diags[0].message.contains("A"));
}

#[test]
fn par01_silent_on_shallow_chain() {
    let mut b = CtxBuilder::new();
    // A -> B -> C (depth 2)
    for (i, cat) in ["A", "B", "C"].iter().enumerate() {
        b.categories.push(cat_info(cat, None, i == 0));
    }
    b.all_syntax.push((
        "RuleA".to_string(),
        "A".to_string(),
        vec![SyntaxItemSpec::NonTerminal {
            category: "B".to_string(),
            param_name: "x".to_string(),
        }],
    ));
    b.all_syntax.push((
        "RuleB".to_string(),
        "B".to_string(),
        vec![SyntaxItemSpec::NonTerminal {
            category: "C".to_string(),
            param_name: "x".to_string(),
        }],
    ));

    let mut diags = Vec::new();
    lint_par01_deep_rd_chain(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// DIS03: Decision Tree Depth
// ══════════════════════════════════════════════════════════════════════

#[test]
fn dis03_fires_on_deep_tree() {
    use crate::decision_tree::TreeStats;

    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    b.decision_trees.insert(
        "Expr".to_string(),
        CategoryDecisionTree {
            category: "Expr".to_string(),
            segments: vec![pathmap::PathMap::new()],
            stats: TreeStats { max_depth: 12, ..Default::default() },
        },
    );

    let mut diags = Vec::new();
    lint_dis03_decision_tree_depth(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1);
    assert_eq!(diags[0].id, DiagnosticId::DIS03);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
    assert!(diags[0].message.contains("Expr"));
    assert!(diags[0].message.contains("12"));
}

#[test]
fn dis03_silent_on_shallow_tree() {
    use crate::decision_tree::TreeStats;

    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    b.decision_trees.insert(
        "Int".to_string(),
        CategoryDecisionTree {
            category: "Int".to_string(),
            segments: vec![pathmap::PathMap::new()],
            stats: TreeStats { max_depth: 3, ..Default::default() },
        },
    );

    let mut diags = Vec::new();
    lint_dis03_decision_tree_depth(&b.ctx(), &mut diags);
    assert!(diags.is_empty());
}

// ══════════════════════════════════════════════════════════════════════
// DB04: Cached Lint Results
// ══════════════════════════════════════════════════════════════════════

#[test]
fn db04_grammar_hash_deterministic() {
    let b = CtxBuilder::new();
    let ctx = b.ctx();
    let h1 = compute_grammar_hash(&ctx);
    let h2 = compute_grammar_hash(&ctx);
    assert_eq!(h1, h2, "same grammar spec must produce same hash");
}

#[test]
fn db04_grammar_hash_changes_with_category() {
    let mut b1 = CtxBuilder::new();
    b1.categories.push(cat_info("Expr", None, true));
    let h1 = compute_grammar_hash(&b1.ctx());

    let mut b2 = CtxBuilder::new();
    b2.categories.push(cat_info("Expr", None, true));
    b2.categories.push(cat_info("Stmt", None, false));
    let h2 = compute_grammar_hash(&b2.ctx());

    assert_ne!(h1, h2, "different category count must produce different hash");
}

#[test]
fn db04_run_lints_cached_no_cache_runs_lints() {
    // With use_cache=false, should behave like run_lints
    let b = CtxBuilder::new();
    let ctx = b.ctx();
    let diags_cached = run_lints_cached(&ctx, false);
    let diags_direct = run_lints(&ctx);
    // Both should produce the same number of diagnostics
    assert_eq!(diags_cached.len(), diags_direct.len());
}

#[test]
fn db04_run_lints_cached_returns_cache_hit_on_repeat() {
    // First call with cache enabled: should run lints and save cache
    let b = CtxBuilder::new();
    let ctx = b.ctx();
    let _ = run_lints_cached(&ctx, true);

    // Second call with same context: should hit cache
    let diags2 = run_lints_cached(&ctx, true);
    // On cache hit, we get a single I18 diagnostic
    let i18 = diags2.iter().filter(|d| d.id == DiagnosticId::I18).count();
    assert_eq!(i18, 1, "cache hit should emit exactly one I18 diagnostic");
}

// ══════════════════════════════════════════════════════════════════════
// Sprint 3: Grouping & Consolidation
// ══════════════════════════════════════════════════════════════════════

#[test]
fn group_a01_multiple_categories() {
    let diags = vec![
            make_diag(DiagnosticId::A01, "fixpoint-non-convergence", LintSeverity::Warning, Some("Proc"), Some("ApplyRw"), "rule `ApplyRw` has 2 self-referential nonterminals with 1 terminal(s) — potential unbounded term growth", Some("ensure complementary depth-reducing rules exist")),
            make_diag(DiagnosticId::A01, "fixpoint-non-convergence", LintSeverity::Warning, Some("Proc"), Some("EvalRw"), "rule `EvalRw` has 3 self-referential nonterminals with 0 terminal(s) — potential unbounded term growth", Some("ensure complementary depth-reducing rules exist")),
            make_diag(DiagnosticId::A01, "fixpoint-non-convergence", LintSeverity::Warning, Some("Name"), Some("NewRw"), "rule `NewRw` has 2 self-referential nonterminals with 1 terminal(s) — potential unbounded term growth", Some("ensure complementary depth-reducing rules exist")),
        ];
    let result = group_diagnostics(diags);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].id, DiagnosticId::A01);
    assert_eq!(result[0].name, "unbounded-term-growth");
    assert!(result[0].message.contains("3 rules"), "message: {}", result[0].message);
    assert!(result[0].message.contains("Name(NewRw)"), "message: {}", result[0].message);
    assert!(
        result[0].message.contains("Proc(ApplyRw, EvalRw)"),
        "message: {}",
        result[0].message
    );
}

#[test]
fn group_a04_multiple_constructors() {
    let diags = vec![
            make_diag(DiagnosticId::A04, "large-equivalence-class", LintSeverity::Warning, Some("Proc"), Some("PPar"), "constructor `PPar` appears in 4 dependency groups — potential exponential equivalence class blowup", Some("consider using HashBag")),
            make_diag(DiagnosticId::A04, "large-equivalence-class", LintSeverity::Warning, Some("Proc"), Some("PNew"), "constructor `PNew` appears in 3 dependency groups — potential exponential equivalence class blowup", Some("consider using HashBag")),
            make_diag(DiagnosticId::A04, "large-equivalence-class", LintSeverity::Warning, Some("Name"), Some("NQuote"), "constructor `NQuote` appears in 5 dependency groups — potential exponential equivalence class blowup", Some("consider using HashBag")),
        ];
    let result = group_diagnostics(diags);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].id, DiagnosticId::A04);
    assert_eq!(result[0].name, "high-dependency-constructors");
    assert!(result[0].message.contains("3 constructors"), "message: {}", result[0].message);
    assert!(result[0].message.contains("Name(NQuote)"), "message: {}", result[0].message);
    assert!(result[0].message.contains("Proc(PPar, PNew)"), "message: {}", result[0].message);
}

#[test]
fn group_a08_multiple_constructors() {
    let diags = vec![
            make_diag(DiagnosticId::A08, "equation-subsumes-rewrite", LintSeverity::Note, Some("Proc"), Some("PPar"), "constructor `PPar` appears in 2 dependency groups — an equation may subsume a rewrite", Some("check whether the rewrite is redundant")),
            make_diag(DiagnosticId::A08, "equation-subsumes-rewrite", LintSeverity::Note, Some("Proc"), Some("PNew"), "constructor `PNew` appears in 3 dependency groups — an equation may subsume a rewrite", Some("check whether the rewrite is redundant")),
            make_diag(DiagnosticId::A08, "equation-subsumes-rewrite", LintSeverity::Note, Some("Name"), Some("NQuote"), "constructor `NQuote` appears in 2 dependency groups — an equation may subsume a rewrite", Some("check whether the rewrite is redundant")),
        ];
    let result = group_diagnostics(diags);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].id, DiagnosticId::A08);
    assert_eq!(result[0].name, "equation-subsumed-rewrites");
    assert!(result[0].message.contains("3 constructors"), "message: {}", result[0].message);
    assert!(result[0].message.contains("Name(NQuote)"), "message: {}", result[0].message);
    assert!(result[0].message.contains("Proc(PPar, PNew)"), "message: {}", result[0].message);
}

#[test]
fn group_cap03_multiple_categories() {
    let diags = vec![
            make_diag(DiagnosticId::CAP03, "deep-congruence-chain", LintSeverity::Warning, None, None, "deep congruence chain: category `Proc` has a self-recursive constructor field — congruence chain depth is unbounded", Some("consider adding depth bounds")),
            make_diag(DiagnosticId::CAP03, "deep-congruence-chain", LintSeverity::Warning, None, None, "deep congruence chain: category `Name` has unbounded congruence chain depth (indirect cycle)", Some("consider adding depth bounds")),
        ];
    let result = group_diagnostics(diags);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].id, DiagnosticId::CAP03);
    assert_eq!(result[0].name, "deep-congruence-chains");
    assert!(result[0].message.contains("2 categories"), "message: {}", result[0].message);
    assert!(result[0].message.contains("Proc"), "message: {}", result[0].message);
    assert!(result[0].message.contains("Name"), "message: {}", result[0].message);
}

#[test]
fn group_cap05_multiple_constructors() {
    let diags = vec![
            make_diag(DiagnosticId::CAP05, "clone-storm-collection-field", LintSeverity::Warning, None, None, "clone storm: constructor `PPar` (category `Proc`) has a `HashBag(Proc)` collection field — congruence rules will clone the entire collection on every rule firing", Some("use reference counting")),
            make_diag(DiagnosticId::CAP05, "clone-storm-collection-field", LintSeverity::Warning, None, None, "clone storm: constructor `NSend` (category `Name`) has a `Vec(Proc)` collection field — congruence rules will clone the entire collection on every rule firing", Some("use reference counting")),
        ];
    let result = group_diagnostics(diags);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].id, DiagnosticId::CAP05);
    assert_eq!(result[0].name, "clone-storm-risk");
    assert!(result[0].message.contains("2 constructors"), "message: {}", result[0].message);
    assert!(result[0].message.contains("PPar(Proc)"), "message: {}", result[0].message);
    assert!(result[0].message.contains("NSend(Name)"), "message: {}", result[0].message);
}

#[test]
fn group_dis01_multiple_categories() {
    let diags = vec![
            make_diag(DiagnosticId::DIS01, "hot-path-misalignment", LintSeverity::Note, Some("Proc"), None, "category `Proc`: WFST action table first weight 3.00 != minimum weight 1.00 (codegen CD01 compensates)", Some("WFST builder should finalize in weight order")),
            make_diag(DiagnosticId::DIS01, "hot-path-misalignment", LintSeverity::Note, Some("Name"), None, "category `Name`: WFST action table first weight 5.00 != minimum weight 2.00 (codegen CD01 compensates)", Some("WFST builder should finalize in weight order")),
            make_diag(DiagnosticId::DIS01, "hot-path-misalignment", LintSeverity::Note, Some("Expr"), None, "category `Expr`: WFST action table first weight 4.00 != minimum weight 1.00 (codegen CD01 compensates)", Some("WFST builder should finalize in weight order")),
        ];
    let result = group_diagnostics(diags);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].id, DiagnosticId::DIS01);
    assert_eq!(result[0].name, "hot-path-misalignment");
    assert!(result[0].message.contains("3 categories"), "message: {}", result[0].message);
    assert!(result[0].message.contains("Proc"), "message: {}", result[0].message);
    assert!(result[0].message.contains("Name"), "message: {}", result[0].message);
    assert!(result[0].message.contains("Expr"), "message: {}", result[0].message);
}

// Stage 10c (2026-05-04): group_w10_multiple_categories test DELETED
// alongside W10's emit function and grouper helper.

#[test]
fn group_w12_multiple_categories() {
    let diags = vec![
            make_diag(DiagnosticId::W12, "training-would-improve", LintSeverity::Note, Some("Proc"), None, "category `Proc` has high dispatch entropy (3.21 bits, 2.22 nats) across 10 actions — WFST weight training would likely improve disambiguation quality", Some("use train_from_corrections")),
            make_diag(DiagnosticId::W12, "training-would-improve", LintSeverity::Note, Some("Name"), None, "category `Name` has high dispatch entropy (2.85 bits, 1.98 nats) across 7 actions — WFST weight training would likely improve disambiguation quality", Some("use SpilloverTrainer")),
        ];
    let result = group_diagnostics(diags);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].id, DiagnosticId::W12);
    assert_eq!(result[0].name, "dispatch-entropy");
    assert!(result[0].message.contains("2 categories"), "message: {}", result[0].message);
    assert!(result[0].message.contains("Proc(3.21 bits)"), "message: {}", result[0].message);
    assert!(result[0].message.contains("Name(2.85 bits)"), "message: {}", result[0].message);
}

// Stage 10c (2026-05-04): group_w14_multiple_categories test DELETED.
// The repurposed W14 (walker-fork-tight-margin) emits per-(category,
// token) diagnostics that are unique by construction; no grouper.

// ══════════════════════════════════════════════════════════════════════
// A-Series Analysis Lint Direct Tests (A02–A10)
// ══════════════════════════════════════════════════════════════════════

// ── A02: redundant-congruence ──

#[test]
fn test_a02_redundant_congruence_fires() {
    // A non-primary category with <=1 own rules that is referenced as a NT
    // field in another category should trigger A02.
    let mut b = CtxBuilder::new();
    b.categories = vec![
        cat_info("Expr", None, true),
        cat_info("Atom", None, false), // non-primary, will have <=1 own rule
    ];
    // Atom has exactly 1 own rule
    b.all_syntax = vec![
        (
            "Lit".to_string(),
            "Atom".to_string(),
            vec![SyntaxItemSpec::Terminal("integer".to_string())],
        ),
        // Expr references Atom as a NT field
        (
            "Wrap".to_string(),
            "Expr".to_string(),
            vec![SyntaxItemSpec::NonTerminal {
                category: "Atom".to_string(),
                param_name: "inner".to_string(),
            }],
        ),
    ];

    let mut diags = Vec::new();
    lint_a02_redundant_congruence(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1, "expected 1 A02 diagnostic, got: {:?}", diags);
    assert_eq!(diags[0].id, DiagnosticId::A02);
    assert_eq!(diags[0].category.as_deref(), Some("Atom"));
}

#[test]
fn test_a02_redundant_congruence_silent_primary() {
    // A primary category should NOT trigger A02 even with <=1 rules.
    let mut b = CtxBuilder::new();
    b.categories = vec![
        cat_info("Expr", None, true), // primary
    ];
    b.all_syntax = vec![(
        "Lit".to_string(),
        "Expr".to_string(),
        vec![SyntaxItemSpec::Terminal("integer".to_string())],
    )];

    let mut diags = Vec::new();
    lint_a02_redundant_congruence(&b.ctx(), &mut diags);
    assert!(diags.is_empty(), "primary category should not trigger A02: {:?}", diags);
}

#[test]
fn test_a02_redundant_congruence_silent_many_rules() {
    // A non-primary category with >1 own rules should NOT trigger A02.
    let mut b = CtxBuilder::new();
    b.categories = vec![cat_info("Expr", None, true), cat_info("Atom", None, false)];
    b.all_syntax = vec![
        (
            "Lit".to_string(),
            "Atom".to_string(),
            vec![SyntaxItemSpec::Terminal("integer".to_string())],
        ),
        (
            "Var".to_string(),
            "Atom".to_string(),
            vec![SyntaxItemSpec::Terminal("ident".to_string())],
        ),
        // Expr references Atom as a NT field
        (
            "Wrap".to_string(),
            "Expr".to_string(),
            vec![SyntaxItemSpec::NonTerminal {
                category: "Atom".to_string(),
                param_name: "inner".to_string(),
            }],
        ),
    ];

    let mut diags = Vec::new();
    lint_a02_redundant_congruence(&b.ctx(), &mut diags);
    assert!(diags.is_empty(), "category with >1 rules should not trigger A02: {:?}", diags);
}

// ── A03: eq-rw-category-mismatch ──

#[test]
fn test_a03_eq_rw_category_mismatch_fires() {
    // A non-primary category has parsing rules but none of its constructors
    // appear in any semantic_dependency_group.
    let mut b = CtxBuilder::new();
    b.categories = vec![
        cat_info("Expr", None, true),
        cat_info("Atom", None, false), // non-primary, has rules but no equations
    ];
    b.all_syntax = vec![
        (
            "Add".to_string(),
            "Expr".to_string(),
            vec![SyntaxItemSpec::Terminal("+".to_string())],
        ),
        (
            "Lit".to_string(),
            "Atom".to_string(),
            vec![SyntaxItemSpec::Terminal("integer".to_string())],
        ),
    ];
    // Only "Add" (an Expr rule) appears in dependency groups; Atom's "Lit" does not
    let mut group = HashSet::new();
    group.insert("Add".to_string());
    b.semantic_dependency_groups = vec![group];

    let mut diags = Vec::new();
    lint_a03_eq_rw_category_mismatch(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1, "expected 1 A03 diagnostic, got: {:?}", diags);
    assert_eq!(diags[0].id, DiagnosticId::A03);
    assert_eq!(diags[0].category.as_deref(), Some("Atom"));
}

#[test]
fn test_a03_eq_rw_category_mismatch_silent_no_groups() {
    // If there are no dependency groups at all, A03 should not fire.
    let mut b = CtxBuilder::new();
    b.categories = vec![cat_info("Atom", None, false)];
    b.all_syntax = vec![(
        "Lit".to_string(),
        "Atom".to_string(),
        vec![SyntaxItemSpec::Terminal("integer".to_string())],
    )];
    b.semantic_dependency_groups = vec![];

    let mut diags = Vec::new();
    lint_a03_eq_rw_category_mismatch(&b.ctx(), &mut diags);
    assert!(diags.is_empty(), "no dependency groups should suppress A03: {:?}", diags);
}

#[test]
fn test_a03_eq_rw_category_mismatch_silent_category_in_group() {
    // A non-primary category whose constructor label appears in a dependency
    // group should NOT trigger A03.
    let mut b = CtxBuilder::new();
    b.categories = vec![cat_info("Expr", None, true), cat_info("Atom", None, false)];
    b.all_syntax = vec![
        (
            "Add".to_string(),
            "Expr".to_string(),
            vec![SyntaxItemSpec::Terminal("+".to_string())],
        ),
        (
            "Lit".to_string(),
            "Atom".to_string(),
            vec![SyntaxItemSpec::Terminal("integer".to_string())],
        ),
    ];
    // Both Add and Lit in dependency groups
    let mut group = HashSet::new();
    group.insert("Add".to_string());
    group.insert("Lit".to_string());
    b.semantic_dependency_groups = vec![group];

    let mut diags = Vec::new();
    lint_a03_eq_rw_category_mismatch(&b.ctx(), &mut diags);
    assert!(
        diags.is_empty(),
        "category with label in group should not trigger A03: {:?}",
        diags
    );
}

// ── A04: large-equivalence-class ──

#[test]
fn test_a04_large_equivalence_class_fires() {
    // A constructor label appearing in 3+ dependency groups should trigger A04.
    let mut b = CtxBuilder::new();
    b.categories = vec![cat_info("Expr", None, true)];
    b.all_syntax = vec![(
        "Add".to_string(),
        "Expr".to_string(),
        vec![SyntaxItemSpec::Terminal("+".to_string())],
    )];
    // "Add" appears in 3 separate groups
    let g1: HashSet<String> = ["Add".to_string()].into();
    let g2: HashSet<String> = ["Add".to_string(), "Mul".to_string()].into();
    let g3: HashSet<String> = ["Add".to_string(), "Sub".to_string(), "Div".to_string()].into();
    b.semantic_dependency_groups = vec![g1, g2, g3];

    let mut diags = Vec::new();
    lint_a04_large_equivalence_class(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1, "expected 1 A04 diagnostic, got: {:?}", diags);
    assert_eq!(diags[0].id, DiagnosticId::A04);
    assert_eq!(diags[0].rule.as_deref(), Some("Add"));
}

#[test]
fn test_a04_large_equivalence_class_silent() {
    // A constructor label in fewer than 3 groups should NOT trigger A04.
    let mut b = CtxBuilder::new();
    b.categories = vec![cat_info("Expr", None, true)];
    b.all_syntax = vec![(
        "Add".to_string(),
        "Expr".to_string(),
        vec![SyntaxItemSpec::Terminal("+".to_string())],
    )];
    // "Add" only in 2 groups
    let g1: HashSet<String> = ["Add".to_string()].into();
    let g2: HashSet<String> = ["Add".to_string(), "Mul".to_string()].into();
    b.semantic_dependency_groups = vec![g1, g2];

    let mut diags = Vec::new();
    lint_a04_large_equivalence_class(&b.ctx(), &mut diags);
    assert!(diags.is_empty(), "label in <3 groups should not trigger A04: {:?}", diags);
}

// ── A06: missing-equation-congruence ──

#[test]
fn test_a06_missing_equation_congruence_fires() {
    // A constructor in a dependency group that has an NT field whose category
    // has NO constructors in any dependency group should trigger A06.
    let mut b = CtxBuilder::new();
    b.categories = vec![cat_info("Expr", None, true), cat_info("Atom", None, false)];
    b.all_syntax = vec![
        // "Wrap" is in Expr, references Atom as NT field
        (
            "Wrap".to_string(),
            "Expr".to_string(),
            vec![SyntaxItemSpec::NonTerminal {
                category: "Atom".to_string(),
                param_name: "inner".to_string(),
            }],
        ),
        // "Lit" is in Atom but NOT in any dependency group
        (
            "Lit".to_string(),
            "Atom".to_string(),
            vec![SyntaxItemSpec::Terminal("integer".to_string())],
        ),
    ];
    // Only "Wrap" in a dependency group
    let mut group = HashSet::new();
    group.insert("Wrap".to_string());
    b.semantic_dependency_groups = vec![group];

    let mut diags = Vec::new();
    lint_a06_missing_equation_congruence(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1, "expected 1 A06 diagnostic, got: {:?}", diags);
    assert_eq!(diags[0].id, DiagnosticId::A06);
    assert_eq!(diags[0].rule.as_deref(), Some("Wrap"));
    assert!(
        diags[0].message.contains("Atom"),
        "message should mention Atom: {}",
        diags[0].message
    );
}

#[test]
fn test_a06_missing_equation_congruence_silent_no_groups() {
    // No dependency groups => A06 should not fire.
    let mut b = CtxBuilder::new();
    b.categories = vec![cat_info("Expr", None, true)];
    b.all_syntax = vec![(
        "Wrap".to_string(),
        "Expr".to_string(),
        vec![SyntaxItemSpec::NonTerminal {
            category: "Atom".to_string(),
            param_name: "inner".to_string(),
        }],
    )];
    b.semantic_dependency_groups = vec![];

    let mut diags = Vec::new();
    lint_a06_missing_equation_congruence(&b.ctx(), &mut diags);
    assert!(diags.is_empty(), "no dependency groups should suppress A06: {:?}", diags);
}

#[test]
fn test_a06_missing_equation_congruence_silent_nt_category_has_equations() {
    // If the NT field's category also has constructors in dependency groups,
    // A06 should NOT fire.
    let mut b = CtxBuilder::new();
    b.categories = vec![cat_info("Expr", None, true), cat_info("Atom", None, false)];
    b.all_syntax = vec![
        (
            "Wrap".to_string(),
            "Expr".to_string(),
            vec![SyntaxItemSpec::NonTerminal {
                category: "Atom".to_string(),
                param_name: "inner".to_string(),
            }],
        ),
        (
            "Lit".to_string(),
            "Atom".to_string(),
            vec![SyntaxItemSpec::Terminal("integer".to_string())],
        ),
    ];
    // Both "Wrap" and "Lit" in dependency groups
    let mut group = HashSet::new();
    group.insert("Wrap".to_string());
    group.insert("Lit".to_string());
    b.semantic_dependency_groups = vec![group];

    let mut diags = Vec::new();
    lint_a06_missing_equation_congruence(&b.ctx(), &mut diags);
    assert!(
        diags.is_empty(),
        "NT category with equation constructors should suppress A06: {:?}",
        diags
    );
}

#[test]
fn test_a06_missing_equation_congruence_silent_same_category_nt() {
    // Self-referencing NT fields (same category) are skipped by A06.
    let mut b = CtxBuilder::new();
    b.categories = vec![cat_info("Expr", None, true)];
    b.all_syntax = vec![(
        "Add".to_string(),
        "Expr".to_string(),
        vec![
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "lhs".to_string(),
            },
            SyntaxItemSpec::Terminal("+".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "rhs".to_string(),
            },
        ],
    )];
    let mut group = HashSet::new();
    group.insert("Add".to_string());
    b.semantic_dependency_groups = vec![group];

    let mut diags = Vec::new();
    lint_a06_missing_equation_congruence(&b.ctx(), &mut diags);
    assert!(diags.is_empty(), "same-category NT should not trigger A06: {:?}", diags);
}

// ── A07: fixpoint-iteration-anomaly ──

#[test]
fn test_a07_fixpoint_iteration_anomaly_fires() {
    // >10 groups AND max group size >5 should trigger A07.
    let mut b = CtxBuilder::new();
    // Create 11 groups, one with 6 labels
    let mut groups = Vec::new();
    for i in 0..10 {
        let mut g = HashSet::new();
        g.insert(format!("Rule{}", i));
        groups.push(g);
    }
    // 11th group with 6 labels
    let mut big_group = HashSet::new();
    for j in 0..6 {
        big_group.insert(format!("Big{}", j));
    }
    groups.push(big_group);
    b.semantic_dependency_groups = groups;

    let mut diags = Vec::new();
    lint_a07_fixpoint_iteration_anomaly(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1, "expected 1 A07 diagnostic, got: {:?}", diags);
    assert_eq!(diags[0].id, DiagnosticId::A07);
    assert!(
        diags[0].message.contains("11 dependency groups"),
        "message: {}",
        diags[0].message
    );
}

#[test]
fn test_a07_fixpoint_iteration_anomaly_silent_few_groups() {
    // <=10 groups should NOT trigger A07.
    let mut b = CtxBuilder::new();
    let mut groups = Vec::new();
    for i in 0..10 {
        let mut g = HashSet::new();
        for j in 0..6 {
            g.insert(format!("Rule{}_{}", i, j));
        }
        groups.push(g);
    }
    b.semantic_dependency_groups = groups;

    let mut diags = Vec::new();
    lint_a07_fixpoint_iteration_anomaly(&b.ctx(), &mut diags);
    assert!(diags.is_empty(), "<=10 groups should not trigger A07: {:?}", diags);
}

#[test]
fn test_a07_fixpoint_iteration_anomaly_silent_small_groups() {
    // >10 groups but max group size <=5 should NOT trigger A07.
    let mut b = CtxBuilder::new();
    let mut groups = Vec::new();
    for i in 0..12 {
        let mut g = HashSet::new();
        for j in 0..5 {
            g.insert(format!("Rule{}_{}", i, j));
        }
        groups.push(g);
    }
    b.semantic_dependency_groups = groups;

    let mut diags = Vec::new();
    lint_a07_fixpoint_iteration_anomaly(&b.ctx(), &mut diags);
    assert!(diags.is_empty(), "max group size <=5 should not trigger A07: {:?}", diags);
}

// ── A08: equation-subsumes-rewrite ──

#[test]
fn test_a08_equation_subsumes_rewrite_fires() {
    // A label appearing in 2+ dependency groups should trigger A08.
    let mut b = CtxBuilder::new();
    b.categories = vec![cat_info("Expr", None, true)];
    b.all_syntax = vec![(
        "Add".to_string(),
        "Expr".to_string(),
        vec![SyntaxItemSpec::Terminal("+".to_string())],
    )];
    // "Add" in two separate groups
    let g1: HashSet<String> = ["Add".to_string()].into();
    let g2: HashSet<String> = ["Add".to_string(), "Mul".to_string()].into();
    b.semantic_dependency_groups = vec![g1, g2];

    let mut diags = Vec::new();
    lint_a08_equation_subsumes_rewrite(&b.ctx(), &mut diags);
    assert_eq!(diags.len(), 1, "expected 1 A08 diagnostic, got: {:?}", diags);
    assert_eq!(diags[0].id, DiagnosticId::A08);
    assert_eq!(diags[0].rule.as_deref(), Some("Add"));
}

#[test]
fn test_a08_equation_subsumes_rewrite_silent() {
    // A label appearing in only 1 group should NOT trigger A08.
    let mut b = CtxBuilder::new();
    b.categories = vec![cat_info("Expr", None, true)];
    b.all_syntax = vec![(
        "Add".to_string(),
        "Expr".to_string(),
        vec![SyntaxItemSpec::Terminal("+".to_string())],
    )];
    let g1: HashSet<String> = ["Add".to_string(), "Mul".to_string()].into();
    b.semantic_dependency_groups = vec![g1];

    let mut diags = Vec::new();
    lint_a08_equation_subsumes_rewrite(&b.ctx(), &mut diags);
    assert!(diags.is_empty(), "label in only 1 group should not trigger A08: {:?}", diags);
}

// ── A10: unreachable-equation-variable ──

#[test]
fn test_a10_unreachable_equation_variable_fires() {
    // A rule with 2+ IdentCapture/Binder params where one capture name
    // appears only once and does not match any NT param_name triggers A10.
    let mut b = CtxBuilder::new();
    b.categories = vec![cat_info("Expr", None, true)];
    b.all_syntax = vec![(
        "LetIn".to_string(),
        "Expr".to_string(),
        vec![
            SyntaxItemSpec::Terminal("let".to_string()),
            SyntaxItemSpec::IdentCapture { param_name: "x".to_string() },
            SyntaxItemSpec::Terminal("=".to_string()),
            SyntaxItemSpec::IdentCapture { param_name: "y".to_string() },
            SyntaxItemSpec::Terminal("in".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "body".to_string(),
            },
        ],
    )];

    let mut diags = Vec::new();
    lint_a10_unreachable_equation_variable(&b.ctx(), &mut diags);
    // Both "x" and "y" appear once, neither matches NT param "body", and captures.len() > 1
    assert_eq!(diags.len(), 2, "expected 2 A10 diagnostics, got: {:?}", diags);
    assert!(diags.iter().all(|d| d.id == DiagnosticId::A10));
    let var_names: HashSet<_> = diags.iter().map(|d| d.message.clone()).collect();
    assert!(var_names.iter().any(|m| m.contains("`x`")), "should mention x: {:?}", var_names);
    assert!(var_names.iter().any(|m| m.contains("`y`")), "should mention y: {:?}", var_names);
}

#[test]
fn test_a10_unreachable_equation_variable_silent_matching_nt() {
    // If a capture name matches an NT param_name, it should NOT trigger A10.
    let mut b = CtxBuilder::new();
    b.categories = vec![cat_info("Expr", None, true)];
    b.all_syntax = vec![(
        "Lambda".to_string(),
        "Expr".to_string(),
        vec![
            SyntaxItemSpec::Terminal("\\".to_string()),
            SyntaxItemSpec::IdentCapture { param_name: "x".to_string() },
            SyntaxItemSpec::Terminal(".".to_string()),
            SyntaxItemSpec::IdentCapture { param_name: "y".to_string() },
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                // NT param_name matches capture "x"
                param_name: "x".to_string(),
            },
        ],
    )];

    let mut diags = Vec::new();
    lint_a10_unreachable_equation_variable(&b.ctx(), &mut diags);
    // "x" matches NT param so should not fire; "y" does not match but is alone
    // => only "y" could fire but "x" is in NT set so x is silent.
    // Actually: captures = ["x", "y"], nt_params = {"x"}.
    // "x": count=1, not in nt_params? No, "x" IS in nt_params => skip.
    // "y": count=1, not in nt_params, captures.len()=2>1 => fires.
    assert_eq!(diags.len(), 1, "expected 1 A10 diagnostic for y, got: {:?}", diags);
    assert_eq!(diags[0].id, DiagnosticId::A10);
    assert!(diags[0].message.contains("`y`"), "should flag y: {}", diags[0].message);
}

#[test]
fn test_a10_unreachable_equation_variable_silent_single_capture() {
    // A rule with only 1 capture should NOT trigger A10 (captures.len() > 1 required).
    let mut b = CtxBuilder::new();
    b.categories = vec![cat_info("Expr", None, true)];
    b.all_syntax = vec![(
        "Var".to_string(),
        "Expr".to_string(),
        vec![SyntaxItemSpec::IdentCapture { param_name: "name".to_string() }],
    )];

    let mut diags = Vec::new();
    lint_a10_unreachable_equation_variable(&b.ctx(), &mut diags);
    assert!(diags.is_empty(), "single capture should not trigger A10: {:?}", diags);
}

#[test]
fn test_a10_unreachable_equation_variable_silent_duplicate_captures() {
    // If a capture name appears more than once, it should NOT trigger A10.
    let mut b = CtxBuilder::new();
    b.categories = vec![cat_info("Expr", None, true)];
    b.all_syntax = vec![(
        "Eq".to_string(),
        "Expr".to_string(),
        vec![
            SyntaxItemSpec::IdentCapture { param_name: "x".to_string() },
            SyntaxItemSpec::Terminal("==".to_string()),
            SyntaxItemSpec::IdentCapture {
                param_name: "x".to_string(), // duplicate
            },
        ],
    )];

    let mut diags = Vec::new();
    lint_a10_unreachable_equation_variable(&b.ctx(), &mut diags);
    assert!(diags.is_empty(), "duplicate captures should not trigger A10: {:?}", diags);
}

// ══════════════════════════════════════════════════════════════════════
// G06: Shadowed Operator
// ══════════════════════════════════════════════════════════════════════

fn make_infix_op(terminal: &str, category: &str) -> InfixOperator {
    InfixOperator {
        terminal: terminal.to_string(),
        category: category.to_string(),
        result_category: category.to_string(),
        left_bp: 10,
        right_bp: 11,
        label: format!("Op_{}", terminal),
        is_cross_category: false,
        is_postfix: false,
        is_mixfix: false,
        mixfix_parts: Vec::new(),
    }
}

#[test]
fn g06_fires_on_infix_and_prefix_sharing_terminal() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    // Infix operator "-" registered in the binding power table
    b.bp_table.operators.push(make_infix_op("-", "Expr"));
    // Prefix rule that also starts with "-"
    b.rules.push(make_rule_info(
        "Neg",
        "Expr",
        vec![FirstItem::Terminal("-".to_string())],
        false, // not infix
    ));

    let mut diags = Vec::new();
    lint_g06_shadowed_operator(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1, "expected exactly one G06 diagnostic");
    assert_eq!(diags[0].id, DiagnosticId::G06);
    assert_eq!(diags[0].severity, LintSeverity::Note);
    assert!(diags[0].message.contains("`-`"), "message should mention `-`");
    assert!(diags[0].message.contains("Expr"), "message should mention category");
}

#[test]
fn g06_silent_when_no_overlap() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    // Infix "+" only
    b.bp_table.operators.push(make_infix_op("+", "Expr"));
    // Prefix rule starts with "!" (no overlap with "+")
    b.rules
        .push(make_rule_info("Not", "Expr", vec![FirstItem::Terminal("!".to_string())], false));

    let mut diags = Vec::new();
    lint_g06_shadowed_operator(&b.ctx(), &mut diags);
    assert!(diags.is_empty(), "no overlap means no G06: {:?}", diags);
}

// ══════════════════════════════════════════════════════════════════════
// G32: Prefix Isomorphism
// ══════════════════════════════════════════════════════════════════════

#[test]
fn g32_fires_on_isomorphic_decision_trees() {
    use crate::decision_tree::{DecisionAction, TreeStats};

    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    b.categories.push(cat_info("Type", None, false));

    // Both categories get structurally identical decision trees:
    // same stats, same path structure, same action shapes.
    let tok_id = b.token_id_map.get_or_insert("Plus");

    let mut seg_a = pathmap::PathMap::new();
    seg_a.insert(
        &[tok_id as u8],
        DecisionAction::Commit {
            rule_label: "AddExpr".to_string(),
            category: "Expr".to_string(),
            weight: 0.0,
        },
    );
    let stats = TreeStats {
        total_states: 1,
        ambiguous_nodes: 0,
        max_depth: 1,
        ..Default::default()
    };
    b.decision_trees.insert(
        "Expr".to_string(),
        CategoryDecisionTree {
            category: "Expr".to_string(),
            segments: vec![seg_a],
            stats: stats.clone(),
        },
    );

    let mut seg_b = pathmap::PathMap::new();
    seg_b.insert(
        &[tok_id as u8],
        DecisionAction::Commit {
            rule_label: "AddType".to_string(),
            category: "Type".to_string(),
            weight: 0.0,
        },
    );
    b.decision_trees.insert(
        "Type".to_string(),
        CategoryDecisionTree {
            category: "Type".to_string(),
            segments: vec![seg_b],
            stats,
        },
    );

    let mut diags = Vec::new();
    lint_g32_prefix_isomorphism(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1, "expected one G32 diagnostic");
    assert_eq!(diags[0].id, DiagnosticId::G32);
    assert!(diags[0].message.contains("Expr"), "message: {}", diags[0].message);
    assert!(diags[0].message.contains("Type"), "message: {}", diags[0].message);
}

#[test]
fn g32_silent_on_structurally_different_trees() {
    use crate::decision_tree::{DecisionAction, TreeStats};

    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    b.categories.push(cat_info("Type", None, false));

    let tok_plus = b.token_id_map.get_or_insert("Plus");
    let tok_star = b.token_id_map.get_or_insert("Star");

    // Expr tree uses Plus
    let mut seg_a = pathmap::PathMap::new();
    seg_a.insert(
        &[tok_plus as u8],
        DecisionAction::Commit {
            rule_label: "AddExpr".to_string(),
            category: "Expr".to_string(),
            weight: 0.0,
        },
    );
    b.decision_trees.insert(
        "Expr".to_string(),
        CategoryDecisionTree {
            category: "Expr".to_string(),
            segments: vec![seg_a],
            stats: TreeStats {
                total_states: 1,
                max_depth: 1,
                ..Default::default()
            },
        },
    );

    // Type tree uses Star (different structure)
    let mut seg_b = pathmap::PathMap::new();
    seg_b.insert(
        &[tok_star as u8],
        DecisionAction::Commit {
            rule_label: "PtrType".to_string(),
            category: "Type".to_string(),
            weight: 0.0,
        },
    );
    b.decision_trees.insert(
        "Type".to_string(),
        CategoryDecisionTree {
            category: "Type".to_string(),
            segments: vec![seg_b],
            stats: TreeStats {
                total_states: 1,
                max_depth: 1,
                ..Default::default()
            },
        },
    );

    let mut diags = Vec::new();
    lint_g32_prefix_isomorphism(&b.ctx(), &mut diags);
    assert!(diags.is_empty(), "different structures should not trigger G32: {:?}", diags);
}

// ══════════════════════════════════════════════════════════════════════
// R01: Empty Sync Set
// ══════════════════════════════════════════════════════════════════════

#[test]
fn r01_fires_on_empty_sync_set() {
    use crate::recovery::RecoveryWfst;

    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    // RecoveryWfst with NO sync tokens
    let rwfst = RecoveryWfst::new("Expr".to_string(), &[], &b.token_id_map);
    b.recovery_wfsts.push(rwfst);

    let mut diags = Vec::new();
    lint_r01_empty_sync_set(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1, "expected one R01 diagnostic");
    assert_eq!(diags[0].id, DiagnosticId::R01);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
    assert!(diags[0].message.contains("Expr"), "message: {}", diags[0].message);
    assert!(diags[0].message.contains("no sync tokens"), "message: {}", diags[0].message);
}

#[test]
fn r01_silent_when_sync_set_nonempty() {
    use crate::recovery::RecoveryWfst;

    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    let tok = "RParen".to_string();
    b.token_id_map.get_or_insert("RParen");
    let rwfst = RecoveryWfst::new("Expr".to_string(), &[tok], &b.token_id_map);
    b.recovery_wfsts.push(rwfst);

    let mut diags = Vec::new();
    lint_r01_empty_sync_set(&b.ctx(), &mut diags);
    assert!(diags.is_empty(), "nonempty sync set should not trigger R01: {:?}", diags);
}

// ══════════════════════════════════════════════════════════════════════
// R02: Sparse Recovery
// ══════════════════════════════════════════════════════════════════════

#[test]
fn r02_fires_on_single_sync_token() {
    use crate::recovery::RecoveryWfst;

    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    let tok = "Eof".to_string();
    b.token_id_map.get_or_insert("Eof");
    let rwfst = RecoveryWfst::new("Expr".to_string(), &[tok], &b.token_id_map);
    b.recovery_wfsts.push(rwfst);

    let mut diags = Vec::new();
    lint_r02_sparse_recovery(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1, "expected one R02 diagnostic");
    assert_eq!(diags[0].id, DiagnosticId::R02);
    assert_eq!(diags[0].severity, LintSeverity::Note);
    assert!(diags[0].message.contains("Expr"), "message: {}", diags[0].message);
    assert!(diags[0].message.contains("only 1"), "message: {}", diags[0].message);
}

#[test]
fn r02_silent_on_multiple_sync_tokens() {
    use crate::recovery::RecoveryWfst;

    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    b.token_id_map.get_or_insert("RParen");
    b.token_id_map.get_or_insert("Eof");
    let toks = vec!["RParen".to_string(), "Eof".to_string()];
    let rwfst = RecoveryWfst::new("Expr".to_string(), &toks, &b.token_id_map);
    b.recovery_wfsts.push(rwfst);

    let mut diags = Vec::new();
    lint_r02_sparse_recovery(&b.ctx(), &mut diags);
    assert!(diags.is_empty(), "2+ sync tokens should not trigger R02: {:?}", diags);
}

// ══════════════════════════════════════════════════════════════════════
// R05: Missing Bracket Sync
// ══════════════════════════════════════════════════════════════════════

#[test]
fn r05_fires_when_open_bracket_without_close_in_sync() {
    use crate::recovery::RecoveryWfst;

    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    // Rule that uses "(" terminal
    b.all_syntax.push((
        "Parens".to_string(),
        "Expr".to_string(),
        vec![
            SyntaxItemSpec::Terminal("(".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "inner".to_string(),
            },
            SyntaxItemSpec::Terminal(")".to_string()),
        ],
    ));
    // Recovery WFST has sync tokens but NOT "RParen"
    b.token_id_map.get_or_insert("Eof");
    b.token_id_map.get_or_insert("RParen");
    let rwfst = RecoveryWfst::new(
        "Expr".to_string(),
        &["Eof".to_string()], // missing RParen
        &b.token_id_map,
    );
    b.recovery_wfsts.push(rwfst);

    let mut diags = Vec::new();
    lint_r05_missing_bracket_sync(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1, "expected one R05 diagnostic");
    assert_eq!(diags[0].id, DiagnosticId::R05);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
    assert!(diags[0].message.contains("`(`"), "message: {}", diags[0].message);
    assert!(diags[0].message.contains("RParen"), "message: {}", diags[0].message);
}

#[test]
fn r05_silent_when_close_bracket_in_sync() {
    use crate::recovery::RecoveryWfst;

    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    // Rule that uses "(" terminal
    b.all_syntax.push((
        "Parens".to_string(),
        "Expr".to_string(),
        vec![
            SyntaxItemSpec::Terminal("(".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: "Expr".to_string(),
                param_name: "inner".to_string(),
            },
            SyntaxItemSpec::Terminal(")".to_string()),
        ],
    ));
    // Recovery WFST includes RParen in sync set
    b.token_id_map.get_or_insert("RParen");
    let rwfst = RecoveryWfst::new("Expr".to_string(), &["RParen".to_string()], &b.token_id_map);
    b.recovery_wfsts.push(rwfst);

    let mut diags = Vec::new();
    lint_r05_missing_bracket_sync(&b.ctx(), &mut diags);
    assert!(
        diags.is_empty(),
        "close bracket in sync set should not trigger R05: {:?}",
        diags
    );
}

// ══════════════════════════════════════════════════════════════════════
// C04: Wide Cross Overlap
// ══════════════════════════════════════════════════════════════════════

#[test]
fn c04_fires_on_high_first_set_overlap() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    b.categories.push(cat_info("Type", None, false));

    // Both categories share 4 of 4 tokens (100% overlap, >= 80% threshold)
    let mut fs_expr = FirstSet::new();
    fs_expr.insert("Ident");
    fs_expr.insert("Integer");
    fs_expr.insert("LParen");
    fs_expr.insert("Minus");

    let mut fs_type = FirstSet::new();
    fs_type.insert("Ident");
    fs_type.insert("Integer");
    fs_type.insert("LParen");
    fs_type.insert("Minus");

    b.first_sets.insert("Expr".to_string(), fs_expr);
    b.first_sets.insert("Type".to_string(), fs_type);

    let mut diags = Vec::new();
    lint_c04_wide_cross_overlap(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1, "expected one C04 diagnostic");
    assert_eq!(diags[0].id, DiagnosticId::C04);
    assert_eq!(diags[0].severity, LintSeverity::Note);
    assert!(diags[0].message.contains("Expr"), "message: {}", diags[0].message);
    assert!(diags[0].message.contains("Type"), "message: {}", diags[0].message);
    assert!(
        diags[0].message.contains("100%"),
        "message should show 100%: {}",
        diags[0].message
    );
}

#[test]
fn c04_silent_on_low_overlap() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    b.categories.push(cat_info("Type", None, false));

    // Only 1 of 5 overlaps (20%, well below 80% threshold)
    let mut fs_expr = FirstSet::new();
    fs_expr.insert("Ident");
    fs_expr.insert("Integer");
    fs_expr.insert("LParen");
    fs_expr.insert("Minus");
    fs_expr.insert("Bang");

    let mut fs_type = FirstSet::new();
    fs_type.insert("Ident");
    fs_type.insert("Star");
    fs_type.insert("Ampersand");
    fs_type.insert("Arrow");
    fs_type.insert("Bracket");

    b.first_sets.insert("Expr".to_string(), fs_expr);
    b.first_sets.insert("Type".to_string(), fs_type);

    let mut diags = Vec::new();
    lint_c04_wide_cross_overlap(&b.ctx(), &mut diags);
    assert!(diags.is_empty(), "low overlap should not trigger C04: {:?}", diags);
}

// ══════════════════════════════════════════════════════════════════════
// D10: Lookahead Waste
// ══════════════════════════════════════════════════════════════════════

#[test]
fn d10_fires_when_most_tokens_resolve_at_depth_1() {
    use crate::decision_tree::{DecisionAction, TreeStats};

    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));

    // Build a decision tree with max_depth=4, but all dispatch tokens
    // resolve at depth 0 (Singleton strategy).
    let tok_a = b.token_id_map.get_or_insert("Ident");
    let tok_b = b.token_id_map.get_or_insert("Integer");
    let tok_c = b.token_id_map.get_or_insert("LParen");
    let tok_d = b.token_id_map.get_or_insert("Minus");
    let tok_e = b.token_id_map.get_or_insert("If");

    let mut seg = pathmap::PathMap::new();
    // 5 tokens, each with a single Commit at depth 1
    seg.insert(
        &[tok_a as u8],
        DecisionAction::Commit {
            rule_label: "Var".to_string(),
            category: "Expr".to_string(),
            weight: 0.0,
        },
    );
    seg.insert(
        &[tok_b as u8],
        DecisionAction::Commit {
            rule_label: "Lit".to_string(),
            category: "Expr".to_string(),
            weight: 0.0,
        },
    );
    seg.insert(
        &[tok_c as u8],
        DecisionAction::Commit {
            rule_label: "Parens".to_string(),
            category: "Expr".to_string(),
            weight: 0.0,
        },
    );
    seg.insert(
        &[tok_d as u8],
        DecisionAction::Commit {
            rule_label: "Neg".to_string(),
            category: "Expr".to_string(),
            weight: 0.0,
        },
    );
    // One deep path to give max_depth > 2
    seg.insert(
        &[tok_e as u8, tok_a as u8, tok_b as u8, tok_c as u8],
        DecisionAction::Commit {
            rule_label: "IfThenElse".to_string(),
            category: "Expr".to_string(),
            weight: 0.0,
        },
    );

    b.decision_trees.insert(
        "Expr".to_string(),
        CategoryDecisionTree {
            category: "Expr".to_string(),
            segments: vec![seg],
            stats: TreeStats {
                total_states: 8,
                max_depth: 4,
                ..Default::default()
            },
        },
    );

    let mut diags = Vec::new();
    lint_d10_lookahead_waste(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1, "expected one D10 diagnostic");
    assert_eq!(diags[0].id, DiagnosticId::D10);
    assert_eq!(diags[0].severity, LintSeverity::Note);
    assert!(diags[0].message.contains("Expr"), "message: {}", diags[0].message);
    assert!(
        diags[0].message.contains("4-token max lookahead"),
        "message: {}",
        diags[0].message
    );
}

#[test]
fn d10_silent_on_shallow_tree() {
    use crate::decision_tree::TreeStats;

    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));

    // max_depth <= 2, so D10 should not fire
    b.decision_trees.insert(
        "Expr".to_string(),
        CategoryDecisionTree {
            category: "Expr".to_string(),
            segments: vec![pathmap::PathMap::new()],
            stats: TreeStats {
                total_states: 3,
                max_depth: 2,
                ..Default::default()
            },
        },
    );

    let mut diags = Vec::new();
    lint_d10_lookahead_waste(&b.ctx(), &mut diags);
    assert!(diags.is_empty(), "shallow tree should not trigger D10: {:?}", diags);
}

// ══════════════════════════════════════════════════════════════════════
// D13: Parsed-But-Unrewritten (Ascent Trie Correlation)
// ══════════════════════════════════════════════════════════════════════

#[test]
fn d13_fires_on_parsed_but_unrewritten_rule() {
    use crate::decision_tree::{DecisionAction, TreeStats};

    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));

    let tok_a = b.token_id_map.get_or_insert("Ident");
    let tok_b = b.token_id_map.get_or_insert("Integer");

    // Decision tree has two reachable rules: "Var" and "Lit"
    let mut seg = pathmap::PathMap::new();
    seg.insert(
        &[tok_a as u8],
        DecisionAction::Commit {
            rule_label: "Var".to_string(),
            category: "Expr".to_string(),
            weight: 0.0,
        },
    );
    seg.insert(
        &[tok_b as u8],
        DecisionAction::Commit {
            rule_label: "Lit".to_string(),
            category: "Expr".to_string(),
            weight: 0.0,
        },
    );
    b.decision_trees.insert(
        "Expr".to_string(),
        CategoryDecisionTree {
            category: "Expr".to_string(),
            segments: vec![seg],
            stats: TreeStats::default(),
        },
    );

    // Semantic dependency groups only reference "Var" -- "Lit" is an orphan
    let mut group = HashSet::new();
    group.insert("Var".to_string());
    b.semantic_dependency_groups.push(group);

    let mut diags = Vec::new();
    lint_d13_ascent_trie_correlation(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1, "expected one D13 for orphan 'Lit'");
    assert_eq!(diags[0].id, DiagnosticId::D13);
    assert_eq!(diags[0].severity, LintSeverity::Note);
    assert!(diags[0].message.contains("Lit"), "message: {}", diags[0].message);
}

#[test]
fn d13_silent_when_all_rules_consumed() {
    use crate::decision_tree::{DecisionAction, TreeStats};

    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));

    let tok_a = b.token_id_map.get_or_insert("Ident");

    let mut seg = pathmap::PathMap::new();
    seg.insert(
        &[tok_a as u8],
        DecisionAction::Commit {
            rule_label: "Var".to_string(),
            category: "Expr".to_string(),
            weight: 0.0,
        },
    );
    b.decision_trees.insert(
        "Expr".to_string(),
        CategoryDecisionTree {
            category: "Expr".to_string(),
            segments: vec![seg],
            stats: TreeStats::default(),
        },
    );

    // All trie-reachable rules appear in a semantic group
    let mut group = HashSet::new();
    group.insert("Var".to_string());
    b.semantic_dependency_groups.push(group);

    let mut diags = Vec::new();
    lint_d13_ascent_trie_correlation(&b.ctx(), &mut diags);
    assert!(diags.is_empty(), "all rules consumed should not trigger D13: {:?}", diags);
}

// ══════════════════════════════════════════════════════════════════════
// D14: WPDS Complexity Report
// ══════════════════════════════════════════════════════════════════════

#[test]
fn d14_fires_when_wpds_analysis_present() {
    use crate::wpds::{DepthBounds, WpdsAnalysis, WpdsCallGraph};

    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    b.categories.push(cat_info("Type", None, false));

    let mut reachable = HashSet::new();
    reachable.insert("Expr".to_string());

    let mut categories = HashSet::new();
    categories.insert("Expr".to_string());
    categories.insert("Type".to_string());

    let mut depth_bounds = HashMap::new();
    depth_bounds.insert(
        "Expr".to_string(),
        DepthBounds {
            min_depth: 0,
            max_depth: None,
            is_recursive: true,
        },
    );

    b.wpds_analysis_data = Some(WpdsAnalysis {
        grammar_name: "TestGrammar".to_string(),
        num_symbols: 5,
        num_rules: 8,
        reachable_categories: reachable,
        unreachable_rules: Vec::new(),
        category_weights: HashMap::new(),
        call_graph: WpdsCallGraph {
            edges: Vec::new(),
            fan_out: HashMap::new(),
            fan_in: HashMap::new(),
            sccs: vec![vec!["Expr".to_string()]],
            categories,
        },
        depth_bounds,
        cycles: Vec::new(),
        calling_contexts: HashMap::new(),
        context_rule_tables: HashMap::new(),
        cross_category_bp: HashMap::new(),
        context_unambiguous: HashMap::new(),
        cek_bijection: crate::wpds::CekWpdsBijection::default(),
        pautomaton: crate::wpds::PAutomaton::new(0),
    });

    let mut diags = Vec::new();
    lint_d14_wpds_complexity_report(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1, "expected one D14 diagnostic");
    assert_eq!(diags[0].id, DiagnosticId::D14);
    assert_eq!(diags[0].severity, LintSeverity::Info);
    assert!(diags[0].message.contains("WPDS analysis"), "message: {}", diags[0].message);
    assert!(
        diags[0].message.contains("|Γ|=5"),
        "message should show symbol count: {}",
        diags[0].message
    );
}

#[test]
fn d14_silent_when_no_wpds_analysis() {
    let b = CtxBuilder::new();
    // wpds_analysis_data is None by default

    let mut diags = Vec::new();
    lint_d14_wpds_complexity_report(&b.ctx(), &mut diags);
    assert!(diags.is_empty(), "no WPDS analysis should not trigger D14: {:?}", diags);
}

// ══════════════════════════════════════════════════════════════════════
// P04: Many Alternatives
// ══════════════════════════════════════════════════════════════════════

#[test]
fn p04_fires_on_token_with_many_dispatch_actions() {
    use crate::automata::semiring::TropicalWeight;
    use crate::prediction::DispatchAction;
    use crate::wfst::PredictionWfstBuilder;

    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));

    // Build a PredictionWfst with 5 actions for "Ident" token (> 4 threshold)
    let mut builder = PredictionWfstBuilder::new("Expr", b.token_id_map.clone());
    for i in 0..5 {
        builder.add_action(
            "Ident",
            DispatchAction::Direct {
                rule_label: format!("Rule{}", i),
                parse_fn: format!("parse_rule_{}", i),
            },
            TropicalWeight::new(i as f64),
        );
    }
    let pwfst = builder.build();
    // Update our token_id_map from the builder's map
    b.token_id_map = pwfst.token_map.clone();
    b.prediction_wfsts.insert("Expr".to_string(), pwfst);

    // FIRST set must include "Ident" for P04 to iterate over it
    let mut fs = FirstSet::new();
    fs.insert("Ident");
    b.first_sets.insert("Expr".to_string(), fs);

    let mut diags = Vec::new();
    lint_p04_many_alternatives(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1, "expected one P04 diagnostic");
    assert_eq!(diags[0].id, DiagnosticId::P04);
    assert!(diags[0].message.contains("Ident"), "message: {}", diags[0].message);
    assert!(diags[0].message.contains("5 rules"), "message: {}", diags[0].message);
}

#[test]
fn p04_silent_on_few_alternatives() {
    use crate::automata::semiring::TropicalWeight;
    use crate::prediction::DispatchAction;
    use crate::wfst::PredictionWfstBuilder;

    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));

    // Only 2 actions for "Ident" (below threshold of > 4)
    let mut builder = PredictionWfstBuilder::new("Expr", b.token_id_map.clone());
    for i in 0..2 {
        builder.add_action(
            "Ident",
            DispatchAction::Direct {
                rule_label: format!("Rule{}", i),
                parse_fn: format!("parse_rule_{}", i),
            },
            TropicalWeight::new(i as f64),
        );
    }
    let pwfst = builder.build();
    b.token_id_map = pwfst.token_map.clone();
    b.prediction_wfsts.insert("Expr".to_string(), pwfst);

    let mut fs = FirstSet::new();
    fs.insert("Ident");
    b.first_sets.insert("Expr".to_string(), fs);

    let mut diags = Vec::new();
    lint_p04_many_alternatives(&b.ctx(), &mut diags);
    assert!(diags.is_empty(), "2 alternatives should not trigger P04: {:?}", diags);
}

// ══════════════════════════════════════════════════════════════════════
// P05: WPDS Pipeline Cost
// ══════════════════════════════════════════════════════════════════════

#[test]
fn p05_fires_when_wpds_elapsed_present() {
    use crate::wpds::{WpdsAnalysis, WpdsCallGraph};

    let mut b = CtxBuilder::new();

    let mut reachable = HashSet::new();
    reachable.insert("Expr".to_string());

    b.wpds_elapsed_data = Some(std::time::Duration::from_millis(42));
    b.wpds_analysis_data = Some(WpdsAnalysis {
        grammar_name: "TestGrammar".to_string(),
        num_symbols: 3,
        num_rules: 6,
        reachable_categories: reachable,
        unreachable_rules: Vec::new(),
        category_weights: HashMap::new(),
        call_graph: WpdsCallGraph {
            edges: Vec::new(),
            fan_out: HashMap::new(),
            fan_in: HashMap::new(),
            sccs: Vec::new(),
            categories: HashSet::new(),
        },
        depth_bounds: HashMap::new(),
        cycles: Vec::new(),
        calling_contexts: HashMap::new(),
        context_rule_tables: HashMap::new(),
        cross_category_bp: HashMap::new(),
        context_unambiguous: HashMap::new(),
        cek_bijection: crate::wpds::CekWpdsBijection::default(),
        pautomaton: crate::wpds::PAutomaton::new(0),
    });

    let mut diags = Vec::new();
    lint_p05_wpds_pipeline_cost(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1, "expected one P05 diagnostic");
    assert_eq!(diags[0].id, DiagnosticId::P05);
    assert_eq!(diags[0].severity, LintSeverity::Info);
    assert!(
        diags[0].message.contains("WPDS analysis completed"),
        "message: {}",
        diags[0].message
    );
    assert!(diags[0].message.contains("|Γ|=3"), "message: {}", diags[0].message);
}

#[test]
fn p05_silent_when_no_wpds_elapsed() {
    let b = CtxBuilder::new();
    // wpds_elapsed_data and wpds_analysis_data are None by default

    let mut diags = Vec::new();
    lint_p05_wpds_pipeline_cost(&b.ctx(), &mut diags);
    assert!(diags.is_empty(), "no WPDS data should not trigger P05: {:?}", diags);
}

// ══════════════════════════════════════════════════════════════════════
// Phase 5A: WFST Lint Function Unit Tests
// ══════════════════════════════════════════════════════════════════════

/// Helper to build a minimal WpdsAnalysis with sensible defaults.
fn make_wpds_analysis_empty() -> crate::wpds::WpdsAnalysis {
    use crate::wpds::{WpdsAnalysis, WpdsCallGraph};
    WpdsAnalysis {
        grammar_name: "TestGrammar".to_string(),
        num_symbols: 0,
        num_rules: 0,
        reachable_categories: HashSet::new(),
        unreachable_rules: Vec::new(),
        category_weights: HashMap::new(),
        call_graph: WpdsCallGraph {
            edges: Vec::new(),
            fan_out: HashMap::new(),
            fan_in: HashMap::new(),
            sccs: Vec::new(),
            categories: HashSet::new(),
        },
        depth_bounds: HashMap::new(),
        cycles: Vec::new(),
        calling_contexts: HashMap::new(),
        context_rule_tables: HashMap::new(),
        cross_category_bp: HashMap::new(),
        context_unambiguous: HashMap::new(),
        cek_bijection: crate::wpds::CekWpdsBijection::default(),
        pautomaton: crate::wpds::PAutomaton::new(0),
    }
}

// ── W01: Dead Rule (via pre-computed dead_rule_warnings) ──

#[test]
fn w01_fires_on_wfst_unreachable() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    b.dead_rule_warnings
        .push(crate::pipeline::DeadRuleWarning::WfstUnreachable {
            rule_label: "BadRule".to_string(),
            category: "Int".to_string(),
        });

    let mut diags = Vec::new();
    lint_w01_dead_rule(&b.ctx(), &mut diags);

    assert!(
        diags
            .iter()
            .any(|d| d.id == DiagnosticId::W01 && d.severity == LintSeverity::Warning),
        "W01 should fire for WfstUnreachable warning: {:?}",
        diags,
    );
    assert!(
        diags.iter().any(|d| d.message.contains("BadRule")),
        "W01 message should mention the dead rule label",
    );
}

#[test]
fn w01_fires_on_literal_no_native_type() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    b.dead_rule_warnings
        .push(crate::pipeline::DeadRuleWarning::LiteralNoNativeType {
            rule_label: "NumLit".to_string(),
            category: "Int".to_string(),
        });

    let mut diags = Vec::new();
    lint_w01_dead_rule(&b.ctx(), &mut diags);

    assert!(
        diags
            .iter()
            .any(|d| d.id == DiagnosticId::W01 && d.severity == LintSeverity::Warning),
        "W01 should fire for LiteralNoNativeType: {:?}",
        diags,
    );
}

#[test]
fn w01_fires_on_unreachable_category() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Orphan", None, false));
    b.dead_rule_warnings
        .push(crate::pipeline::DeadRuleWarning::UnreachableCategory {
            rule_label: "InfixOp".to_string(),
            category: "Orphan".to_string(),
        });

    let mut diags = Vec::new();
    lint_w01_dead_rule(&b.ctx(), &mut diags);

    assert!(
        diags.iter().any(|d| d.id == DiagnosticId::W01),
        "W01 should fire for UnreachableCategory: {:?}",
        diags,
    );
}

#[test]
fn w01_emits_w07_for_nearly_dead_path() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    b.dead_rule_warnings
        .push(crate::pipeline::DeadRuleWarning::NearlyDeadPath {
            rule_label: "RareRule".to_string(),
            category: "Int".to_string(),
            derivation_count: 1,
            total_count: 500,
        });

    let mut diags = Vec::new();
    lint_w01_dead_rule(&b.ctx(), &mut diags);

    // NearlyDeadPath should emit W07 with Note severity, not W01
    assert!(
        diags
            .iter()
            .any(|d| d.id == DiagnosticId::W07 && d.severity == LintSeverity::Note),
        "NearlyDeadPath should emit W07 Note, not W01 Warning: {:?}",
        diags,
    );
    assert!(
        !diags.iter().any(|d| d.id == DiagnosticId::W01),
        "NearlyDeadPath should NOT emit W01",
    );
}

#[test]
fn w01_silent_when_no_warnings() {
    let b = CtxBuilder::new();

    let mut diags = Vec::new();
    lint_w01_dead_rule(&b.ctx(), &mut diags);

    // W01 also computes A4/A8 warnings internally, but with empty
    // categories/rules/syntax/first_sets those should produce nothing.
    let w01_count = diags.iter().filter(|d| d.id == DiagnosticId::W01).count();
    assert_eq!(w01_count, 0, "W01 should not fire with no warnings: {:?}", diags);
}

// ── W03: High Ambiguity Token ──

#[test]
fn w03_fires_on_three_way_ambiguity() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    // Build a WFST where token "Ident" dispatches to 3 rules
    b.prediction_wfsts.insert(
        "Expr".to_string(),
        make_prediction_wfst(
            "Expr",
            &[("Ident", "VarExpr", 1.0), ("Ident", "FnCall", 2.0), ("Ident", "TypeRef", 3.0)],
        ),
    );
    b.first_sets.insert(
        "Expr".to_string(),
        FirstSet {
            tokens: ["Ident".to_string()].into(),
            nullable: false,
        },
    );

    let mut diags = Vec::new();
    lint_w03_high_ambiguity_token(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1, "expected 1 W03 diagnostic: {:?}", diags);
    assert_eq!(diags[0].id, DiagnosticId::W03);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
    assert!(
        diags[0].message.contains("Ident"),
        "message should mention token: {}",
        diags[0].message
    );
    assert!(
        diags[0].message.contains("3"),
        "message should mention count: {}",
        diags[0].message
    );
}

#[test]
fn w03_silent_on_two_way_ambiguity() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    // Only 2 actions — threshold is 3
    b.prediction_wfsts.insert(
        "Expr".to_string(),
        make_prediction_wfst("Expr", &[("Ident", "VarExpr", 1.0), ("Ident", "FnCall", 2.0)]),
    );
    b.first_sets.insert(
        "Expr".to_string(),
        FirstSet {
            tokens: ["Ident".to_string()].into(),
            nullable: false,
        },
    );

    let mut diags = Vec::new();
    lint_w03_high_ambiguity_token(&b.ctx(), &mut diags);

    assert!(diags.is_empty(), "2-way ambiguity should not trigger W03: {:?}", diags);
}

#[test]
fn w03_silent_when_no_wfst() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    b.first_sets.insert(
        "Expr".to_string(),
        FirstSet {
            tokens: ["Ident".to_string()].into(),
            nullable: false,
        },
    );
    // No prediction_wfsts

    let mut diags = Vec::new();
    lint_w03_high_ambiguity_token(&b.ctx(), &mut diags);

    assert!(diags.is_empty(), "no WFST should not trigger W03");
}

// ── W04: Weight Gap Anomaly ──

#[test]
fn w04_fires_on_large_weight_gap() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    // Best rule weight=1.0, second weight=7.0 — gap=6.0 > 5.0
    b.prediction_wfsts.insert(
        "Expr".to_string(),
        make_prediction_wfst("Expr", &[("Plus", "AddExpr", 1.0), ("Plus", "ConcatExpr", 7.0)]),
    );
    b.first_sets.insert(
        "Expr".to_string(),
        FirstSet {
            tokens: ["Plus".to_string()].into(),
            nullable: false,
        },
    );

    let mut diags = Vec::new();
    lint_w04_weight_gap_anomaly(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1, "expected 1 W04 diagnostic: {:?}", diags);
    assert_eq!(diags[0].id, DiagnosticId::W04);
    assert_eq!(diags[0].severity, LintSeverity::Note);
    assert!(
        diags[0].message.contains("Plus"),
        "message should mention token: {}",
        diags[0].message
    );
    assert!(
        diags[0].message.contains("AddExpr"),
        "message should mention best rule: {}",
        diags[0].message
    );
    assert!(
        diags[0].message.contains("ConcatExpr"),
        "message should mention second rule: {}",
        diags[0].message
    );
}

#[test]
fn w04_silent_on_small_weight_gap() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    // Best=1.0, second=3.0 — gap=2.0 < 5.0
    b.prediction_wfsts.insert(
        "Expr".to_string(),
        make_prediction_wfst("Expr", &[("Plus", "AddExpr", 1.0), ("Plus", "ConcatExpr", 3.0)]),
    );
    b.first_sets.insert(
        "Expr".to_string(),
        FirstSet {
            tokens: ["Plus".to_string()].into(),
            nullable: false,
        },
    );

    let mut diags = Vec::new();
    lint_w04_weight_gap_anomaly(&b.ctx(), &mut diags);

    assert!(diags.is_empty(), "gap of 2.0 should not trigger W04: {:?}", diags);
}

#[test]
fn w04_silent_when_single_action() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    b.prediction_wfsts
        .insert("Expr".to_string(), make_prediction_wfst("Expr", &[("Plus", "AddExpr", 1.0)]));
    b.first_sets.insert(
        "Expr".to_string(),
        FirstSet {
            tokens: ["Plus".to_string()].into(),
            nullable: false,
        },
    );

    let mut diags = Vec::new();
    lint_w04_weight_gap_anomaly(&b.ctx(), &mut diags);

    assert!(diags.is_empty(), "single action should not trigger W04");
}

// ── W06: Weight Inversion ──

#[test]
fn w06_fires_on_specificity_inversion() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    // Rule "Short" has 1 syntax item (less specific)
    // Rule "Long" has 3 syntax items (more specific)
    // But "Short" has lower (better) weight than "Long" — inversion
    b.all_syntax.push((
        "Short".to_string(),
        "Expr".to_string(),
        vec![SyntaxItemSpec::Terminal("x".to_string())],
    ));
    b.all_syntax.push((
        "Long".to_string(),
        "Expr".to_string(),
        vec![
            SyntaxItemSpec::Terminal("x".to_string()),
            SyntaxItemSpec::Terminal("y".to_string()),
            SyntaxItemSpec::Terminal("z".to_string()),
        ],
    ));
    b.prediction_wfsts.insert(
        "Expr".to_string(),
        make_prediction_wfst(
            "Expr",
            &[
                ("KwX", "Short", 1.0), // less-specific has lower (better) weight
                ("KwX", "Long", 5.0),  // more-specific has higher (worse) weight
            ],
        ),
    );
    b.first_sets.insert(
        "Expr".to_string(),
        FirstSet {
            tokens: ["KwX".to_string()].into(),
            nullable: false,
        },
    );

    let mut diags = Vec::new();
    lint_w06_weight_inversion(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1, "expected 1 W06 diagnostic: {:?}", diags);
    assert_eq!(diags[0].id, DiagnosticId::W06);
    assert_eq!(diags[0].severity, LintSeverity::Note);
    assert!(
        diags[0].message.contains("Short"),
        "message should mention less-specific rule: {}",
        diags[0].message
    );
    assert!(
        diags[0].message.contains("Long"),
        "message should mention more-specific rule: {}",
        diags[0].message
    );
}

#[test]
fn w06_silent_when_correctly_ordered() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    // "Long" (3 items, more specific) has lower weight — correct order
    b.all_syntax.push((
        "Short".to_string(),
        "Expr".to_string(),
        vec![SyntaxItemSpec::Terminal("x".to_string())],
    ));
    b.all_syntax.push((
        "Long".to_string(),
        "Expr".to_string(),
        vec![
            SyntaxItemSpec::Terminal("x".to_string()),
            SyntaxItemSpec::Terminal("y".to_string()),
            SyntaxItemSpec::Terminal("z".to_string()),
        ],
    ));
    b.prediction_wfsts.insert(
        "Expr".to_string(),
        make_prediction_wfst(
            "Expr",
            &[
                ("KwX", "Long", 1.0),  // more-specific has lower (better) weight
                ("KwX", "Short", 5.0), // less-specific has higher (worse) weight
            ],
        ),
    );
    b.first_sets.insert(
        "Expr".to_string(),
        FirstSet {
            tokens: ["KwX".to_string()].into(),
            nullable: false,
        },
    );

    let mut diags = Vec::new();
    lint_w06_weight_inversion(&b.ctx(), &mut diags);

    assert!(
        diags.is_empty(),
        "correctly ordered weights should not trigger W06: {:?}",
        diags
    );
}

// ── W13: WPDS-Unreachable Rule ──

#[test]
fn w13_fires_on_wpds_unreachable() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    b.categories.push(cat_info("Orphan", None, false));

    let mut analysis = make_wpds_analysis_empty();
    analysis.reachable_categories.insert("Expr".to_string());
    analysis
        .unreachable_rules
        .push(crate::wpds::WpdsUnreachableRule {
            rule_label: "OrphanRule".to_string(),
            category: "Orphan".to_string(),
            missing_contexts: vec!["Expr".to_string()],
            witness_trace: vec!["Expr -> Orphan".to_string()],
        });
    b.wpds_analysis_data = Some(analysis);

    let mut diags = Vec::new();
    lint_w13_wpds_unreachable(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1, "expected 1 W13 diagnostic: {:?}", diags);
    assert_eq!(diags[0].id, DiagnosticId::W13);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
    assert!(diags[0].message.contains("OrphanRule"), "message: {}", diags[0].message);
    assert!(diags[0].message.contains("Orphan"), "message: {}", diags[0].message);
    assert!(
        diags[0].message.contains("Expr"),
        "should mention missing caller: {}",
        diags[0].message
    );
    assert!(
        diags[0].message.contains("witness trace"),
        "should include witness: {}",
        diags[0].message
    );
}

#[test]
fn w13_ignores_dead_rule_ignore_labels() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    b.categories.push(cat_info("Refined", None, false));

    let mut analysis = make_wpds_analysis_empty();
    analysis.reachable_categories.insert("Expr".to_string());
    analysis
        .unreachable_rules
        .push(crate::wpds::WpdsUnreachableRule {
            rule_label: "ExprToRefined".to_string(),
            category: "Refined".to_string(),
            missing_contexts: vec!["Expr".to_string()],
            witness_trace: Vec::new(),
        });
    b.wpds_analysis_data = Some(analysis);
    b.dead_rule_ignore_labels
        .insert("ExprToRefined".to_string());

    let mut diags = Vec::new();
    lint_w13_wpds_unreachable(&b.ctx(), &mut diags);

    assert!(diags.is_empty(), "ignored W13 labels should be silent: {:?}", diags);
}

#[test]
fn w13_silent_when_no_unreachable() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));

    let mut analysis = make_wpds_analysis_empty();
    analysis.reachable_categories.insert("Expr".to_string());
    b.wpds_analysis_data = Some(analysis);

    let mut diags = Vec::new();
    lint_w13_wpds_unreachable(&b.ctx(), &mut diags);

    assert!(diags.is_empty(), "no unreachable rules should not trigger W13");
}

#[test]
fn w13_silent_when_no_wpds_analysis() {
    let b = CtxBuilder::new();

    let mut diags = Vec::new();
    lint_w13_wpds_unreachable(&b.ctx(), &mut diags);

    assert!(diags.is_empty(), "absent WPDS analysis should not trigger W13");
}

// ── W14: Walker-Fork Tight Margin (Stage 10c repurpose, 2026-05-04) ──
//
// The 4 old W14 tests (wpds-confirmed-ambiguity) were deleted alongside
// the rewrite. Below: 3 new tests for the repurposed semantics.

#[test]
fn w14_fires_on_tight_margin() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    let mut fs = FirstSet::new();
    fs.insert("Plus");
    b.first_sets.insert("Expr".to_string(), fs);
    b.prediction_wfsts.insert(
        "Expr".to_string(),
        make_prediction_wfst(
            "Expr",
            &[
                ("Plus", "AddExpr", 1.0),
                ("Plus", "ConcatExpr", 1.05), // margin = 0.05 < 0.1
            ],
        ),
    );

    let mut diags = Vec::new();
    lint_w14_wpds_confirmed_ambiguity(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1, "expected 1 W14 diagnostic: {:?}", diags);
    assert_eq!(diags[0].id, DiagnosticId::W14);
    assert_eq!(diags[0].name, "walker-fork-tight-margin");
    assert!(
        diags[0].message.contains("margin"),
        "message should mention margin: {}",
        diags[0].message,
    );
}

#[test]
fn w14_silent_on_wide_gap() {
    // Wide gap (4.0) is W04 territory, not W14.
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    let mut fs = FirstSet::new();
    fs.insert("Plus");
    b.first_sets.insert("Expr".to_string(), fs);
    b.prediction_wfsts.insert(
        "Expr".to_string(),
        make_prediction_wfst(
            "Expr",
            &[
                ("Plus", "AddExpr", 1.0),
                ("Plus", "ConcatExpr", 5.0), // margin = 4.0 >= 0.1
            ],
        ),
    );

    let mut diags = Vec::new();
    lint_w14_wpds_confirmed_ambiguity(&b.ctx(), &mut diags);

    assert!(
        diags.is_empty(),
        "wide-gap weights should not trigger W14 (W04 territory): {:?}",
        diags,
    );
}

#[test]
fn w14_silent_on_singleton_dispatch() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    let mut fs = FirstSet::new();
    fs.insert("Plus");
    b.first_sets.insert("Expr".to_string(), fs);
    b.prediction_wfsts
        .insert("Expr".to_string(), make_prediction_wfst("Expr", &[("Plus", "AddExpr", 1.0)]));

    let mut diags = Vec::new();
    lint_w14_wpds_confirmed_ambiguity(&b.ctx(), &mut diags);

    assert!(diags.is_empty(), "singleton dispatch should not trigger W14: {:?}", diags,);
}

// ── W16: WPDS Weight Inversion ──

#[test]
fn w16_silent_when_no_wpds_analysis() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    b.prediction_wfsts.insert(
        "Expr".to_string(),
        make_prediction_wfst("Expr", &[("Plus", "AddExpr", 1.0), ("Plus", "ConcatExpr", 5.0)]),
    );

    let mut diags = Vec::new();
    lint_w16_wpds_weight_inversion(&b.ctx(), &mut diags);

    assert!(diags.is_empty(), "absent WPDS analysis should not trigger W16");
}

#[test]
fn w16_silent_when_no_prediction_wfsts() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));

    let mut analysis = make_wpds_analysis_empty();
    analysis.reachable_categories.insert("Expr".to_string());
    analysis.category_weights.insert("Expr".to_string(), 1.0);
    b.wpds_analysis_data = Some(analysis);

    let mut diags = Vec::new();
    lint_w16_wpds_weight_inversion(&b.ctx(), &mut diags);

    assert!(diags.is_empty(), "no prediction WFSTs should not trigger W16");
}

#[test]
fn w16_silent_when_wpds_weights_agree() {
    // When WPDS weight is the same for both rules (same category), the
    // condition `wpds_a_weight > wpds_b_weight + 0.5` is never true
    // because both values come from the same category_weights entry.
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Expr", None, true));
    b.prediction_wfsts.insert(
        "Expr".to_string(),
        make_prediction_wfst("Expr", &[("Plus", "AddExpr", 1.0), ("Plus", "ConcatExpr", 5.0)]),
    );

    let mut analysis = make_wpds_analysis_empty();
    analysis.reachable_categories.insert("Expr".to_string());
    analysis.category_weights.insert("Expr".to_string(), 2.0);
    analysis.calling_contexts.insert(
        "Expr".to_string(),
        vec![crate::wpds::CallingContext {
            caller_category: "Root".to_string(),
            caller_rule: "Start".to_string(),
            caller_position: 0,
            weight: 1.0,
        }],
    );
    b.wpds_analysis_data = Some(analysis);

    let mut diags = Vec::new();
    lint_w16_wpds_weight_inversion(&b.ctx(), &mut diags);

    // W16 compares wpds_a_weight vs wpds_b_weight, but both come from
    // the same category_weights entry, so they are always equal. The
    // condition `wpds_a_weight > wpds_b_weight + 0.5` is never met
    // for same-category comparisons.
    assert!(
        diags.is_empty(),
        "same-category WPDS weights should not trigger W16: {:?}",
        diags,
    );
}

// ══════════════════════════════════════════════════════════════════════
// RT01–RT06: Refinement Type Lints
// ══════════════════════════════════════════════════════════════════════

fn make_refinement_analysis() -> crate::pipeline::RefinementAnalysisResult {
    crate::pipeline::RefinementAnalysisResult::default()
}

#[test]
fn rt01_fires_on_unsatisfiable_refinement() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    let mut analysis = make_refinement_analysis();
    analysis
        .unsatisfiable
        .push(("NeverInt".to_string(), "predicate is trivially false".to_string()));
    b.refinement_analysis_data = Some(analysis);

    let mut diags = Vec::new();
    lint_rt01_unsatisfiable_refinement(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1, "expected 1 RT01 diagnostic: {:?}", diags);
    assert_eq!(diags[0].id, DiagnosticId::RT01);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
    assert!(diags[0].message.contains("NeverInt"), "message: {}", diags[0].message);
}

#[test]
fn rt01_silent_when_no_analysis() {
    let b = CtxBuilder::new();
    let mut diags = Vec::new();
    lint_rt01_unsatisfiable_refinement(&b.ctx(), &mut diags);
    assert!(diags.is_empty(), "absent analysis should not trigger RT01");
}

#[test]
fn rt02_fires_on_tautological_refinement() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    let mut analysis = make_refinement_analysis();
    analysis
        .tautological
        .push(("AnyInt".to_string(), "predicate is trivially true".to_string()));
    b.refinement_analysis_data = Some(analysis);

    let mut diags = Vec::new();
    lint_rt02_tautological_refinement(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1, "expected 1 RT02 diagnostic: {:?}", diags);
    assert_eq!(diags[0].id, DiagnosticId::RT02);
    assert_eq!(diags[0].severity, LintSeverity::Note);
}

#[test]
fn rt03_fires_on_empty_intersection() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    let mut analysis = make_refinement_analysis();
    analysis.empty_intersections.push((
        "PosInt".to_string(),
        "NegInt".to_string(),
        "contradictory predicates".to_string(),
    ));
    b.refinement_analysis_data = Some(analysis);

    let mut diags = Vec::new();
    lint_rt03_empty_intersection(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1, "expected 1 RT03 diagnostic: {:?}", diags);
    assert_eq!(diags[0].id, DiagnosticId::RT03);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
    assert!(diags[0].message.contains("PosInt"), "message: {}", diags[0].message);
    assert!(diags[0].message.contains("NegInt"), "message: {}", diags[0].message);
}

/// The `.1` structural path enriches the RT03 hint with an inhabitation witness
/// for the disjoint pair's shared base category (sourced from
/// `structural_witnesses`). This mirrors the `RefinementAnalysisResult` the
/// `sym-tree-structural` pipeline produces: an `empty_intersections` entry, a
/// `dispatch_analysis.base_type_groups` mapping the two refinements to their base
/// category, and a `structural_witnesses` entry for that category.
#[test]
fn rt03_structural_hint_includes_base_witness() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("List", None, true));
    let mut analysis = make_refinement_analysis();
    analysis.empty_intersections.push((
        "One".to_string(),
        "TwoPlus".to_string(),
        "structural refinement patterns are disjoint".to_string(),
    ));
    let mut dispatch = crate::type_system::RefinementDispatchAnalysis::default();
    dispatch
        .base_type_groups
        .insert("List".to_string(), vec!["One".to_string(), "TwoPlus".to_string()]);
    analysis.dispatch_analysis = Some(dispatch);
    analysis
        .structural_witnesses
        .push(("List".to_string(), "Nil".to_string()));
    b.refinement_analysis_data = Some(analysis);

    let mut diags = Vec::new();
    lint_rt03_empty_intersection(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1, "expected 1 RT03 diagnostic: {:?}", diags);
    let hint = diags[0].hint.as_deref().unwrap_or("");
    assert!(
        hint.contains("List") && hint.contains("Nil"),
        "RT03 hint should mention the base category 'List' and its witness 'Nil': {hint}"
    );
}

#[test]
fn rt04_fires_on_subtype_pair() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    let mut analysis = make_refinement_analysis();
    analysis
        .subtype_pairs
        .push(("StrictPosInt".to_string(), "PosInt".to_string()));
    b.refinement_analysis_data = Some(analysis);

    let mut diags = Vec::new();
    lint_rt04_subtype_detected(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1, "expected 1 RT04 diagnostic: {:?}", diags);
    assert_eq!(diags[0].id, DiagnosticId::RT04);
    assert_eq!(diags[0].severity, LintSeverity::Note);
}

#[test]
fn rt05_fires_on_decidability_tier() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    let mut analysis = make_refinement_analysis();
    analysis
        .decidability_tiers
        .push(("PosInt".to_string(), "T2 (decidable, automata-based)".to_string()));
    b.refinement_analysis_data = Some(analysis);

    let mut diags = Vec::new();
    lint_rt05_decidability_tier(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1, "expected 1 RT05 diagnostic: {:?}", diags);
    assert_eq!(diags[0].id, DiagnosticId::RT05);
    assert_eq!(diags[0].severity, LintSeverity::Note);
    assert!(diags[0].message.contains("T2"), "message: {}", diags[0].message);
}

#[test]
fn rt06_fires_on_name_shadow() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    let mut analysis = make_refinement_analysis();
    analysis
        .name_shadows
        .push(("Int".to_string(), "Int".to_string()));
    b.refinement_analysis_data = Some(analysis);

    let mut diags = Vec::new();
    lint_rt06_name_shadow(&b.ctx(), &mut diags);

    assert_eq!(diags.len(), 1, "expected 1 RT06 diagnostic: {:?}", diags);
    assert_eq!(diags[0].id, DiagnosticId::RT06);
    assert_eq!(diags[0].severity, LintSeverity::Warning);
    assert!(diags[0].message.contains("shadows"), "message: {}", diags[0].message);
}

#[test]
fn rt_lints_run_in_run_lints() {
    let mut b = CtxBuilder::new();
    b.categories.push(cat_info("Int", None, true));
    let mut analysis = make_refinement_analysis();
    analysis
        .unsatisfiable
        .push(("DeadType".to_string(), "predicate is trivially false".to_string()));
    analysis
        .decidability_tiers
        .push(("PosInt".to_string(), "T2 (decidable, automata-based)".to_string()));
    b.refinement_analysis_data = Some(analysis);

    let diags = run_lints(&b.ctx());
    let rt_diags: Vec<_> = diags.iter().filter(|d| d.id.is_runtime()).collect();
    assert_eq!(rt_diags.len(), 2, "expected 2 RT diagnostics (RT01 + RT05): {:?}", rt_diags);
}

// ═════════════════════════════════════════════════════════════════════
// Lint-E: Tests for the refined linter output
// ═════════════════════════════════════════════════════════════════════
//
// These tests live in a nested module so the local `make_diag`
// helper does not collide with the outer `tests` module's helper
// of the same name but different signature.
mod lint_e {
    use super::super::*;

    fn make_diag(
        id: DiagnosticId,
        grammar: &str,
        message: &str,
        severity: LintSeverity,
    ) -> LintDiagnostic {
        LintDiagnostic {
            id,
            name: "test",
            severity,
            category: None,
            rule: None,
            message: message.to_string(),
            hint: None,
            grammar_name: Some(grammar.to_string()),
            source_location: None,
        }
    }

    #[test]
    fn lint_e_m01_is_groupable() {
        assert!(DiagnosticId::M01.is_groupable());
        assert!(DiagnosticId::K01.is_groupable());
        assert!(DiagnosticId::SYM02.is_groupable());
        assert!(DiagnosticId::N02.is_groupable());
        assert!(DiagnosticId::N05.is_groupable());
    }

    #[test]
    fn lint_e_group_m01_collapses_identical_messages() {
        // Three identical M01 warnings — should collapse to 1.
        let diags = vec![
            make_diag(
                DiagnosticId::M01,
                "Calc",
                "theory morphism incomplete — missing constructor mapping: \
                 [MissingOperation] Int::Tern: Source operation 'Int::Tern' \
                 (Int::Tern: Int x Int x Int -> Int) has no translation case",
                LintSeverity::Warning,
            ),
            make_diag(
                DiagnosticId::M01,
                "Calc",
                "theory morphism incomplete — missing constructor mapping: \
                 [MissingOperation] Int::Tern: Source operation 'Int::Tern' \
                 (Int::Tern: Int x Int x Int -> Int) has no translation case",
                LintSeverity::Warning,
            ),
            make_diag(
                DiagnosticId::M01,
                "Calc",
                "theory morphism incomplete — missing constructor mapping: \
                 [MissingOperation] Int::Tern: Source operation 'Int::Tern' \
                 (Int::Tern: Int x Int x Int -> Int) has no translation case",
                LintSeverity::Warning,
            ),
        ];
        let grouped = group_m01(diags);
        assert_eq!(grouped.len(), 1);
        assert!(grouped[0].message.starts_with("3 theory morphism gap"));
        // Single-unique-message path reports the specific identifier.
        assert!(grouped[0].message.contains("Int::Tern"));
    }

    #[test]
    fn lint_e_group_m01_multiple_uniques() {
        // Three M01 warnings with 2 unique messages — should collapse to 1
        // summary that lists both unique identifiers.
        let diags = vec![
            make_diag(
                DiagnosticId::M01,
                "Calc",
                "theory morphism incomplete — missing constructor mapping: \
                 [MissingOperation] Num::NegNum: ...",
                LintSeverity::Warning,
            ),
            make_diag(
                DiagnosticId::M01,
                "Calc",
                "theory morphism incomplete — missing constructor mapping: \
                 [MissingOperation] Num::FactNum: ...",
                LintSeverity::Warning,
            ),
            make_diag(
                DiagnosticId::M01,
                "Calc",
                "theory morphism incomplete — missing constructor mapping: \
                 [MissingOperation] Num::NegNum: ...",
                LintSeverity::Warning,
            ),
        ];
        let grouped = group_m01(diags);
        assert_eq!(grouped.len(), 1);
        assert!(grouped[0].message.contains("3"));
        assert!(grouped[0].message.contains("2 unique"));
        assert!(grouped[0].message.contains("Num::NegNum"));
        assert!(grouped[0].message.contains("Num::FactNum"));
    }

    #[test]
    fn lint_e_group_k01_extracts_type_pairs() {
        let diags = vec![
            make_diag(
                DiagnosticId::K01,
                "Calc",
                "Hoare triple failed: [Str -> Bool] {Str_reachable} call_Str_Bool {Bool_reachable}",
                LintSeverity::Warning,
            ),
            make_diag(
                DiagnosticId::K01,
                "Calc",
                "Hoare triple failed: [Int -> Str] {Int_reachable} call_Int_Str {Str_reachable}",
                LintSeverity::Warning,
            ),
        ];
        let grouped = group_k01(diags);
        assert_eq!(grouped.len(), 1);
        assert!(grouped[0].message.contains("2 KAT Hoare-triple failures"));
        assert!(grouped[0].message.contains("Str→Bool"));
        assert!(grouped[0].message.contains("Int→Str"));
    }

    #[test]
    fn lint_e_group_n02_extracts_place_names() {
        let diags = vec![
            LintDiagnostic {
                id: DiagnosticId::N02,
                name: "test",
                severity: LintSeverity::Warning,
                category: None,
                rule: None,
                message: "place `Float` has unbounded token capacity".to_string(),
                hint: None,
                grammar_name: Some("Calc".to_string()),
                source_location: None,
            },
            LintDiagnostic {
                id: DiagnosticId::N02,
                name: "test",
                severity: LintSeverity::Warning,
                category: None,
                rule: None,
                message: "place `Str` has unbounded token capacity".to_string(),
                hint: None,
                grammar_name: Some("Calc".to_string()),
                source_location: None,
            },
            LintDiagnostic {
                id: DiagnosticId::N02,
                name: "test",
                severity: LintSeverity::Warning,
                category: None,
                rule: None,
                message: "place `Int` has unbounded token capacity".to_string(),
                hint: None,
                grammar_name: Some("Calc".to_string()),
                source_location: None,
            },
        ];
        let grouped = group_n02(diags);
        assert_eq!(grouped.len(), 1);
        assert!(grouped[0].message.contains("3 places with unbounded"));
        assert!(grouped[0].message.contains("Float"));
        assert!(grouped[0].message.contains("Str"));
        assert!(grouped[0].message.contains("Int"));
    }

    #[test]
    fn lint_e_group_n05_extracts_category_pairs() {
        let diags = vec![
            LintDiagnostic {
                id: DiagnosticId::N05,
                name: "test",
                severity: LintSeverity::Warning,
                category: None,
                rule: None,
                message: "categories `Int` and `Float` are not bisimilar (attacker wins game)"
                    .to_string(),
                hint: None,
                grammar_name: Some("Calc".to_string()),
                source_location: None,
            },
            LintDiagnostic {
                id: DiagnosticId::N05,
                name: "test",
                severity: LintSeverity::Warning,
                category: None,
                rule: None,
                message: "categories `Bool` and `Str` are not bisimilar (attacker wins game)"
                    .to_string(),
                hint: None,
                grammar_name: Some("Calc".to_string()),
                source_location: None,
            },
        ];
        let grouped = group_n05(diags);
        assert_eq!(grouped.len(), 1);
        assert!(grouped[0].message.contains("2 category pairs"));
        assert!(grouped[0].message.contains("(Int,Float)"));
        assert!(grouped[0].message.contains("(Bool,Str)"));
    }

    #[test]
    fn lint_e_group_sym02_aggregates_by_category() {
        let diags = vec![
            LintDiagnostic {
                id: DiagnosticId::SYM02,
                name: "test",
                severity: LintSeverity::Note,
                category: Some("Proc".to_string()),
                rule: None,
                message: "SFA overlap 1".to_string(),
                hint: None,
                grammar_name: Some("Rho".to_string()),
                source_location: None,
            },
            LintDiagnostic {
                id: DiagnosticId::SYM02,
                name: "test",
                severity: LintSeverity::Note,
                category: Some("Proc".to_string()),
                rule: None,
                message: "SFA overlap 2".to_string(),
                hint: None,
                grammar_name: Some("Rho".to_string()),
                source_location: None,
            },
            LintDiagnostic {
                id: DiagnosticId::SYM02,
                name: "test",
                severity: LintSeverity::Note,
                category: Some("Name".to_string()),
                rule: None,
                message: "SFA overlap 3".to_string(),
                hint: None,
                grammar_name: Some("Rho".to_string()),
                source_location: None,
            },
        ];
        let grouped = group_sym02(diags);
        assert_eq!(grouped.len(), 1);
        assert!(grouped[0].message.contains("3"));
        assert!(grouped[0].message.contains("Name:1"));
        assert!(grouped[0].message.contains("Proc:2"));
    }

    #[test]
    fn lint_e_single_item_passes_through_unchanged() {
        // Groupers should not modify single-item groups.
        for id in [
            DiagnosticId::M01,
            DiagnosticId::K01,
            DiagnosticId::SYM02,
            DiagnosticId::N02,
            DiagnosticId::N05,
        ] {
            let diag = make_diag(id, "G", "unique message", LintSeverity::Warning);
            let grouped = group_diagnostics(vec![diag.clone()]);
            assert_eq!(grouped.len(), 1);
            assert_eq!(grouped[0].message, "unique message");
        }
    }

    #[test]
    fn lint_e_grammar_lint_state_coalesces_headers() {
        reset_grammar_lint_state();

        let diag1 = make_diag(DiagnosticId::A01, "TestLang", "first", LintSeverity::Warning);
        let diag2 = make_diag(DiagnosticId::A01, "TestLang", "second", LintSeverity::Warning);

        // Two emit calls for the same grammar: the thread-local should
        // record exactly one header-printed flag and accumulate counts.
        emit_diagnostics_for_grammar("TestLang", &[diag1]);
        emit_diagnostics_for_grammar("TestLang", &[diag2]);

        GRAMMAR_LINT_STATE.with(|cell| {
            let state = cell.borrow();
            let entry = state.get("TestLang").expect("entry should exist");
            assert!(entry.header_printed);
            assert_eq!(entry.warning_count, 2);
        });

        reset_grammar_lint_state();
    }

    #[test]
    fn lint_e_finalize_grammar_summary_noop_when_no_diagnostics() {
        reset_grammar_lint_state();
        // Never called emit_diagnostics_for_grammar — finalize should
        // be a no-op without touching state.
        finalize_grammar_summary("UnknownLang");
        GRAMMAR_LINT_STATE.with(|cell| {
            assert!(cell.borrow().get("UnknownLang").is_none());
        });
    }

    #[test]
    fn lint_e_finalize_aggregates_across_passes() {
        reset_grammar_lint_state();

        // Simulate two passes (one warning each).
        let pass1 = vec![make_diag(DiagnosticId::A01, "MultiPass", "p1", LintSeverity::Warning)];
        let pass2 = vec![make_diag(DiagnosticId::A01, "MultiPass", "p2", LintSeverity::Warning)];
        emit_diagnostics_for_grammar("MultiPass", &pass1);
        emit_diagnostics_for_grammar("MultiPass", &pass2);

        // Verify accumulated counts.
        GRAMMAR_LINT_STATE.with(|cell| {
            let state = cell.borrow();
            let entry = state.get("MultiPass").expect("entry exists");
            assert_eq!(entry.warning_count, 2);
            assert!(entry.header_printed);
        });

        // finalize is idempotent / non-destructive.
        finalize_grammar_summary("MultiPass");
        GRAMMAR_LINT_STATE.with(|cell| {
            let state = cell.borrow();
            let entry = state.get("MultiPass").expect("entry still exists");
            assert_eq!(entry.warning_count, 2);
        });

        reset_grammar_lint_state();
    }

    // ── Property tests ───────────────────────────────────────────────────
    use proptest::prelude::*;

    proptest! {
        /// For any N >= 1 identical M01 diagnostics, the grouper
        /// produces exactly 1 output diagnostic whose message begins
        /// with "N theory morphism gap".
        #[test]
        fn proptest_lint_e_m01_collapses_to_one(n in 1usize..32) {
            let diags: Vec<LintDiagnostic> = (0..n)
                .map(|_| make_diag(
                    DiagnosticId::M01,
                    "G",
                    "theory morphism incomplete — missing constructor mapping: \
                     [MissingOperation] Int::Tern: ...",
                    LintSeverity::Warning,
                ))
                .collect();
            let grouped = group_m01(diags);
            if n == 1 {
                // Single-item passes through unchanged.
                prop_assert_eq!(grouped.len(), 1);
            } else {
                prop_assert_eq!(grouped.len(), 1);
                let expected_prefix = format!("{} theory morphism gap", n);
                prop_assert!(grouped[0].message.starts_with(&expected_prefix));
            }
        }

        /// For any N >= 1 identical K01 diagnostics with the same type
        /// pair, the grouper produces exactly 1 output diagnostic.
        #[test]
        fn proptest_lint_e_k01_collapses_to_one(n in 1usize..32) {
            let diags: Vec<LintDiagnostic> = (0..n)
                .map(|_| make_diag(
                    DiagnosticId::K01,
                    "G",
                    "Hoare triple failed: [A -> B] ...",
                    LintSeverity::Warning,
                ))
                .collect();
            let grouped = group_k01(diags);
            prop_assert_eq!(grouped.len(), 1);
        }
    }
} // end of `mod lint_e`

// ══════════════════════════════════════════════════════════════════════
// Phase 13 (predicated types): coverage for advanced-automata lints
// ══════════════════════════════════════════════════════════════════════

mod predicated_types_lint_coverage {
    use super::*;
    use crate::multi_tape::MultiTapeAnalysis;
    use crate::parity_tree::ParityTreeAnalysis;
    use crate::symbolic::{DecidabilityTier, SymbolicAnalysis};
    use crate::two_way_transducer::TwoWayAnalysis;
    use crate::weighted_mso::{MsoAnalysis, MsoFormulaClass};

    // ── DiagnosticId identity tests for the new IDs ──

    #[test]
    fn strat01_id_string() {
        assert_eq!(DiagnosticId::STRAT01.as_str(), "STRAT01");
        assert_eq!(format!("{}", DiagnosticId::STRAT01), "STRAT01");
    }

    #[test]
    fn tier01_id_string() {
        assert_eq!(DiagnosticId::TIER01.as_str(), "TIER01");
        assert_eq!(format!("{}", DiagnosticId::TIER01), "TIER01");
    }

    #[test]
    fn dnf01_id_string() {
        assert_eq!(DiagnosticId::DNF01.as_str(), "DNF01");
    }

    #[test]
    fn tok01_id_string() {
        assert_eq!(DiagnosticId::TOK01.as_str(), "TOK01");
    }

    // ── SYM01: unsatisfiable guard ──

    #[test]
    fn sym01_fires_when_guard_unsatisfiable() {
        let mut b = CtxBuilder::new();
        b.symbolic_result_data = Some(SymbolicAnalysis {
            num_states: 2,
            num_transitions: 1,
            guard_satisfiability: vec![("dead_guard".to_string(), false)],
            overlapping_guards: vec![],
            subsumed_guards: vec![],
            unsatisfiable_rule_labels: vec![],
        });
        let mut diags = Vec::new();
        lint_sym01_unsatisfiable_guard(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, DiagnosticId::SYM01);
    }

    #[test]
    fn sym01_clean_when_all_guards_satisfiable() {
        let mut b = CtxBuilder::new();
        b.symbolic_result_data = Some(SymbolicAnalysis {
            num_states: 2,
            num_transitions: 1,
            guard_satisfiability: vec![("g".to_string(), true)],
            overlapping_guards: vec![],
            subsumed_guards: vec![],
            unsatisfiable_rule_labels: vec![],
        });
        let mut diags = Vec::new();
        lint_sym01_unsatisfiable_guard(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ── SYM02: overlapping guards ──

    #[test]
    fn sym02_fires_on_overlapping_guards() {
        let mut b = CtxBuilder::new();
        b.symbolic_result_data = Some(SymbolicAnalysis {
            num_states: 2,
            num_transitions: 2,
            guard_satisfiability: vec![],
            overlapping_guards: vec![("g1".to_string(), "g2".to_string())],
            subsumed_guards: vec![],
            unsatisfiable_rule_labels: vec![],
        });
        let mut diags = Vec::new();
        lint_sym02_overlapping_guards(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, DiagnosticId::SYM02);
    }

    #[test]
    fn sym02_clean_when_no_overlap() {
        let mut b = CtxBuilder::new();
        b.symbolic_result_data = Some(SymbolicAnalysis {
            num_states: 2,
            num_transitions: 2,
            guard_satisfiability: vec![],
            overlapping_guards: vec![],
            subsumed_guards: vec![],
            unsatisfiable_rule_labels: vec![],
        });
        let mut diags = Vec::new();
        lint_sym02_overlapping_guards(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ── SYM03: subsumed guard ──

    #[test]
    fn sym03_fires_on_subsumption() {
        let mut b = CtxBuilder::new();
        b.symbolic_result_data = Some(SymbolicAnalysis {
            num_states: 2,
            num_transitions: 2,
            guard_satisfiability: vec![],
            overlapping_guards: vec![],
            subsumed_guards: vec![("sub".to_string(), "sup".to_string())],
            unsatisfiable_rule_labels: vec![],
        });
        let mut diags = Vec::new();
        lint_sym03_subsumed_guard(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, DiagnosticId::SYM03);
    }

    // ── SYM04: non-minimal guards ──

    #[test]
    fn sym04_fires_on_large_subsumption_set() {
        let mut b = CtxBuilder::new();
        b.symbolic_result_data = Some(SymbolicAnalysis {
            num_states: 12, // > 10 threshold
            num_transitions: 20,
            guard_satisfiability: vec![],
            overlapping_guards: vec![],
            subsumed_guards: vec![("sub".to_string(), "sup".to_string())],
            unsatisfiable_rule_labels: vec![],
        });
        let mut diags = Vec::new();
        lint_sym04_non_minimal_guards(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, DiagnosticId::SYM04);
    }

    #[test]
    fn sym04_clean_for_small_automaton() {
        let mut b = CtxBuilder::new();
        b.symbolic_result_data = Some(SymbolicAnalysis {
            num_states: 5, // < 10 threshold
            num_transitions: 4,
            guard_satisfiability: vec![],
            overlapping_guards: vec![],
            subsumed_guards: vec![("a".to_string(), "b".to_string())],
            unsatisfiable_rule_labels: vec![],
        });
        let mut diags = Vec::new();
        lint_sym04_non_minimal_guards(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ── MSO01: full MSO unrestricted ∀X ──

    #[test]
    fn mso01_fires_on_full_mso() {
        let mut b = CtxBuilder::new();
        b.mso_result_data = Some(MsoAnalysis {
            formula_class: MsoFormulaClass::Full,
            decidability: DecidabilityTier::Undecidable,
            free_vars: HashSet::new(),
            free_set_vars: HashSet::new(),
            is_sentence: true,
        });
        let mut diags = Vec::new();
        lint_mso01_unrestricted_universal_set(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, DiagnosticId::MSO01);
    }

    #[test]
    fn mso01_clean_for_restricted() {
        let mut b = CtxBuilder::new();
        b.mso_result_data = Some(MsoAnalysis {
            formula_class: MsoFormulaClass::Restricted,
            decidability: DecidabilityTier::CompileTimeDecidable,
            free_vars: HashSet::new(),
            free_set_vars: HashSet::new(),
            is_sentence: true,
        });
        let mut diags = Vec::new();
        lint_mso01_unrestricted_universal_set(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ── MSO02: non-recognizable step ──

    #[test]
    fn mso02_fires_on_semi_decidable() {
        let mut b = CtxBuilder::new();
        b.mso_result_data = Some(MsoAnalysis {
            formula_class: MsoFormulaClass::RestrictedExistential,
            decidability: DecidabilityTier::SemiDecidable,
            free_vars: HashSet::new(),
            free_set_vars: HashSet::new(),
            is_sentence: true,
        });
        let mut diags = Vec::new();
        lint_mso02_non_recognizable_step(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, DiagnosticId::MSO02);
    }

    // ── MT01: multi-channel overlap ──

    #[test]
    fn mt01_fires_on_overlapping_tapes() {
        let mut b = CtxBuilder::new();
        b.multi_tape_result_data = Some(MultiTapeAnalysis {
            num_states: 4,
            num_tapes: 2,
            disconnected_tapes: vec![],
            overlapping_tapes: vec![(0, 1)],
        });
        let mut diags = Vec::new();
        lint_mt01_multi_channel_overlap(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, DiagnosticId::MT01);
    }

    #[test]
    fn mt01_clean_when_tapes_distinct() {
        let mut b = CtxBuilder::new();
        b.multi_tape_result_data = Some(MultiTapeAnalysis {
            num_states: 4,
            num_tapes: 2,
            disconnected_tapes: vec![],
            overlapping_tapes: vec![],
        });
        let mut diags = Vec::new();
        lint_mt01_multi_channel_overlap(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ── MT02: disconnected multi-tape ──

    #[test]
    fn mt02_fires_on_disconnected_tape() {
        let mut b = CtxBuilder::new();
        b.multi_tape_result_data = Some(MultiTapeAnalysis {
            num_states: 4,
            num_tapes: 2,
            disconnected_tapes: vec![1],
            overlapping_tapes: vec![],
        });
        let mut diags = Vec::new();
        lint_mt02_multi_tape_disconnected(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, DiagnosticId::MT02);
    }

    // ── TW01: circular channel dependency ──

    #[test]
    fn tw01_fires_on_deadlock_cycle() {
        let mut b = CtxBuilder::new();
        b.two_way_result_data = Some(TwoWayAnalysis {
            num_states: 4,
            num_forward: 2,
            num_backward: 2,
            is_one_way_equivalent: false,
            deadlock_cycles: vec![vec!["ch1".to_string(), "ch2".to_string()]],
        });
        let mut diags = Vec::new();
        lint_tw01_circular_channel_dependency(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, DiagnosticId::TW01);
    }

    #[test]
    fn tw01_clean_without_cycles() {
        let mut b = CtxBuilder::new();
        b.two_way_result_data = Some(TwoWayAnalysis {
            num_states: 4,
            num_forward: 2,
            num_backward: 2,
            is_one_way_equivalent: false,
            deadlock_cycles: vec![],
        });
        let mut diags = Vec::new();
        lint_tw01_circular_channel_dependency(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }

    // ── TW02: one-way sufficient ──

    #[test]
    fn tw02_fires_when_one_way_equivalent() {
        let mut b = CtxBuilder::new();
        b.two_way_result_data = Some(TwoWayAnalysis {
            num_states: 4,
            num_forward: 4,
            num_backward: 0,
            is_one_way_equivalent: true,
            deadlock_cycles: vec![],
        });
        let mut diags = Vec::new();
        lint_tw02_one_way_sufficient(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, DiagnosticId::TW02);
    }

    // ── TW03: constraint propagation divergent ──

    #[test]
    fn tw03_fires_with_backward_and_cycles() {
        let mut b = CtxBuilder::new();
        b.two_way_result_data = Some(TwoWayAnalysis {
            num_states: 4,
            num_forward: 2,
            num_backward: 2,
            is_one_way_equivalent: false,
            deadlock_cycles: vec![vec!["a".to_string(), "b".to_string()]],
        });
        let mut diags = Vec::new();
        lint_tw03_constraint_propagation_divergent(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, DiagnosticId::TW03);
    }

    // ── PT01: PATA emptiness violation ──

    #[test]
    fn pt01_fires_on_empty_pata() {
        let mut b = CtxBuilder::new();
        b.parity_tree_result_data = Some(ParityTreeAnalysis {
            num_states: 0,
            max_priority: 0,
            is_empty: true,
            priority_depth: 0,
        });
        let mut diags = Vec::new();
        lint_pt01_pata_emptiness_violation(&b.ctx(), &mut diags);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].id, DiagnosticId::PT01);
    }

    #[test]
    fn pt01_clean_for_non_empty_pata() {
        let mut b = CtxBuilder::new();
        b.parity_tree_result_data = Some(ParityTreeAnalysis {
            num_states: 5,
            max_priority: 2,
            is_empty: false,
            priority_depth: 2,
        });
        let mut diags = Vec::new();
        lint_pt01_pata_emptiness_violation(&b.ctx(), &mut diags);
        assert!(diags.is_empty());
    }
}
