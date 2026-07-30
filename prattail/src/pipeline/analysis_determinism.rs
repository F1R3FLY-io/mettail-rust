//! Work item #173: the analysis-result **determinism gate**.
//!
//! # What this file is for
//!
//! Every analysis in [`MathAnalysisResults`] is a *pure function of the grammar*.
//! Two calls on the same bundle must therefore produce the same value — not the
//! same value "up to ordering", the same value. When they do not, the cause is
//! always the same shape: a result field was materialised by iterating a
//! `HashSet`/`HashMap`, whose iteration order `std`'s `RandomState` deliberately
//! randomises per map instance.
//!
//! That shape has reached *published bytes* four times in this repository's
//! history (`44` reify, `9994a75b` order-sensitive `==` residual, `0fcfef00`
//! genesis post-state hash, `f5b2e820` pathmap ordering), so the class is
//! treated as live rather than theoretical.
//!
//! # Why this is a derivation and not a list
//!
//! The naive gate is a hand-written list of the fields known to be unordered.
//! Such a list is a mirror of a computable domain, and it rots the moment an
//! analysis grows a field. This gate instead **derives** the offending set from
//! the code under test: it runs the whole analysis phase [`DETERMINISM_REPEATS`]
//! times, renders each result with `{:#?}`, and reports every rendered line the
//! phase cannot reproduce against itself — attributed to a **field path** by
//! walking the pretty-printer's own indentation back to the root.
//!
//! Consequences of deriving rather than listing:
//!
//! - a newly nondeterministic field fails this gate with **no edit here**;
//! - the failure message *names the field*, so the report is the diagnosis;
//! - the gate cannot pass vacuously: [`NON_VACUITY_FLOOR`] asserts the render is
//!   large enough to have contained the defect this gate was written for.
//!
//! # Why repetition is required
//!
//! A single run cannot detect nondeterminism. Within one process each
//! `HashMap`/`HashSet` gets a *different* `RandomState` seed (the per-thread key
//! is bumped for every map created), so two calls in the same test process
//! already disagree. With `k` equally likely orders, `n` runs miss the
//! instability with probability `k^(1-n)`; at `k = 2`, `n = 8` that is `1/128`,
//! and the gate under guard here has `k = 3! = 6`.

use std::collections::{BTreeSet, HashMap, HashSet};

use super::*;

/// Runs of the analysis phase per grammar. See the module docs for the
/// miss-probability argument.
const DETERMINISM_REPEATS: usize = 8;

/// Minimum rendered lines the fixture must produce for this gate to be evidence.
///
/// Without a floor a gate over "the lines that disagree" passes trivially when
/// there are no lines — e.g. if every analysis were to start returning `None`.
/// The fixture below renders far more than this; the floor only has to exceed
/// the size of the structure that carried #173 (`PetriAnalysis`, ~8 lines).
const NON_VACUITY_FLOOR: usize = 100;

// ══════════════════════════════════════════════════════════════════════════════
// Fixture
// ══════════════════════════════════════════════════════════════════════════════
//
// Deliberately built here rather than reused from `analysis.rs`'s
// `spawn_ledger_guards`: a gate that shares a fixture with another guard can be
// silently weakened by an edit made for that other guard's reasons.

fn category(name: &str, is_primary: bool) -> CategoryInfo {
    CategoryInfo {
        name: name.to_string(),
        native_type: None,
        is_primary,
        has_var: true,
    }
}

fn nt(category: &str, param: &str) -> SyntaxItemSpec {
    SyntaxItemSpec::NonTerminal {
        category: category.to_string(),
        param_name: param.to_string(),
    }
}

fn term(text: &str) -> SyntaxItemSpec {
    SyntaxItemSpec::Terminal(text.to_string())
}

/// A grammar **wide enough that unordered carriers are detectable**.
///
/// Detectability is the design constraint, and it is a property of *width*: a
/// one-element set renders identically under every permutation, so a fixture
/// whose analyses each see one category proves nothing. Six categories give the
/// place set of `petri` `6! = 720` renderings, and the rules below reference
/// every category from at least one other so the cross-category analyses see a
/// non-trivial relation too.
///
/// `|` appears as a terminal because that is what `petri::analyze_from_bundle`
/// reads as a Petri **transition**; without one the net has no transitions.
fn wide_bundle() -> ParserBundle {
    let categories = vec![
        category("Proc", true),
        category("Name", false),
        category("Int", false),
        category("Str", false),
        category("Bool", false),
        category("Chan", false),
    ];
    let all_syntax = vec![
        (
            "PPar".to_string(),
            "Proc".to_string(),
            vec![nt("Proc", "l"), term("|"), nt("Proc", "r")],
        ),
        (
            "PSend".to_string(),
            "Proc".to_string(),
            vec![nt("Chan", "c"), term("!"), term("("), nt("Int", "v"), term(")")],
        ),
        (
            "PRecv".to_string(),
            "Proc".to_string(),
            vec![
                term("for"),
                term("("),
                SyntaxItemSpec::Binder {
                    param_name: "x".to_string(),
                    category: "Name".to_string(),
                    is_multi: false,
                },
                term("<-"),
                nt("Chan", "c"),
                term(")"),
                nt("Proc", "body"),
            ],
        ),
        (
            "PList".to_string(),
            "Proc".to_string(),
            vec![
                term("["),
                SyntaxItemSpec::Collection {
                    param_name: "elems".to_string(),
                    element_category: "Name".to_string(),
                    separator: ",".to_string(),
                    key_val_separator: None,
                    kind: crate::grammar::ir::CollectionKind::Vec,
                },
                term("]"),
            ],
        ),
        (
            "PIf".to_string(),
            "Proc".to_string(),
            vec![term("if"), nt("Bool", "c"), nt("Proc", "t"), term("else"), nt("Proc", "e")],
        ),
        ("NQuote".to_string(), "Name".to_string(), vec![term("@"), nt("Proc", "p")]),
        ("CName".to_string(), "Chan".to_string(), vec![nt("Name", "n")]),
        ("Add".to_string(), "Int".to_string(), vec![nt("Int", "a"), term("+"), nt("Int", "b")]),
        ("Cat".to_string(), "Str".to_string(), vec![nt("Str", "a"), term("++"), nt("Str", "b")]),
        ("Lt".to_string(), "Bool".to_string(), vec![nt("Int", "a"), term("<"), nt("Int", "b")]),
        ("And".to_string(), "Bool".to_string(), vec![nt("Bool", "a"), term("&&"), nt("Bool", "b")]),
    ];

    ParserBundle {
        grammar_name: "DeterminismGate".to_string(),
        categories,
        bp_table: crate::binding_power::BindingPowerTable { operators: Vec::new() },
        rule_infos: Vec::new(),
        follow_inputs: Vec::new(),
        rd_rules: Vec::new(),
        cross_rules: Vec::new(),
        cast_rules: Vec::new(),
        has_binders: true,
        beam_width: crate::BeamWidthConfig::default(),
        recovery_config: crate::recovery::RecoveryConfig::default(),
        all_syntax,
        rule_locations: HashMap::new(),
        dead_rule_ignore_labels: HashSet::new(),
        semantic_dependency_groups: Vec::new(),
        custom_tokens: Vec::new(),
        refinement_types: Vec::new(),
    }
}

/// The WPDS analysis the WPDS-dependent analyses need in order to run at all.
///
/// Passing `None` here would make roughly a third of [`MathAnalysisResults`]
/// `None` — the gate would then be silent about exactly the analyses that see
/// the most structure. An empty `prediction_wfsts` map is what the real pipeline
/// passes when no WFST was built for a category.
fn wpds_for(bundle: &ParserBundle) -> crate::wpds::WpdsAnalysis {
    let cats: Vec<crate::wpds::WpdsCategoryInfo> = bundle
        .categories
        .iter()
        .map(|c| crate::wpds::WpdsCategoryInfo {
            name: c.name.clone(),
            is_primary: c.is_primary,
        })
        .collect();
    crate::wpds::analyze_wpds_from_bundle(
        &bundle.grammar_name,
        &cats,
        &bundle.all_syntax,
        &HashMap::new(),
    )
}

// ══════════════════════════════════════════════════════════════════════════════
// Derivation
// ══════════════════════════════════════════════════════════════════════════════

/// Indentation width of a rendered line, in leading spaces.
fn indent_of(line: &str) -> usize {
    line.len() - line.trim_start().len()
}

/// The `{:#?}` field path enclosing rendered line `index`, e.g.
/// `petri_result.unbounded_places`.
///
/// `{:#?}` indents strictly by nesting depth, so the enclosing field of a line
/// is the nearest preceding line at *smaller* indentation, and its enclosing
/// field is the nearest line smaller still. Walking that staircase to column
/// zero yields the whole path, which is why this needs no knowledge of the
/// struct being rendered and cannot fall behind it.
fn field_path(lines: &[String], index: usize) -> String {
    let mut depth = indent_of(&lines[index]);
    let mut segments: Vec<&str> = Vec::new();
    // The line itself names a field when it is of the form `name: ...`.
    if let Some(name) = field_name(&lines[index]) {
        segments.push(name);
    }
    for line in lines[..index].iter().rev() {
        let candidate = indent_of(line);
        if candidate >= depth {
            continue;
        }
        depth = candidate;
        match field_name(line) {
            Some(name) => segments.push(name),
            None => {},
        }
        if depth == 0 {
            break;
        }
    }
    segments.reverse();
    match segments.is_empty() {
        true => format!("<line {index}>"),
        false => segments.join("."),
    }
}

/// The field name a rendered line introduces, if it introduces one.
///
/// Matches `identifier:` at the start of the trimmed line. A `Vec` element, a
/// closing bracket, and a tuple field all correctly yield `None`.
fn field_name(line: &str) -> Option<&str> {
    let trimmed = line.trim_start();
    let colon = trimmed.find(':')?;
    let name = &trimmed[..colon];
    match !name.is_empty()
        && name.starts_with(|c: char| c.is_ascii_alphabetic() || c == '_')
        && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
    {
        true => Some(name),
        false => None,
    }
}

/// Renders one analysis phase as lines.
///
/// Nothing is masked. This gate compares a path against *itself*, so every
/// field — including the ones #164's cross-path guard has to exclude — is
/// in scope here.
fn render(results: MathAnalysisResults) -> Vec<String> {
    format!("{results:#?}").lines().map(str::to_string).collect()
}

/// The field paths the analysis phase could not reproduce, with the distinct
/// renderings observed for each.
fn irreproducible(runs: &[Vec<String>]) -> BTreeSet<(String, String)> {
    let reference = &runs[0];
    let mut findings = BTreeSet::new();
    for index in 0..reference.len() {
        let variants: BTreeSet<&str> = runs
            .iter()
            .filter(|run| run.len() == reference.len())
            .map(|run| run[index].trim())
            .collect();
        if variants.len() > 1 {
            findings.insert((
                field_path(reference, index),
                variants.into_iter().collect::<Vec<_>>().join(" | "),
            ));
        }
    }
    findings
}

// ══════════════════════════════════════════════════════════════════════════════
// The codegen-visible argmax
// ══════════════════════════════════════════════════════════════════════════════
//
// `PipelineAnalysis::per_category_entropy` is the one analysis result found in
// this campaign whose iteration order demonstrably reaches **generated bytes**:
//
//     prattail  build_pipeline_analysis  →  per_category_entropy
//     macros    simulation_tests.rs:36   →  .iter().max_by(..)  →  primary_cat
//     macros    simulation_tests.rs:321  →  fn sim_<lang>_proptest_campaign(
//                                              term in arb_<primary_cat>(3u32))
//     target/generated/<lang>/tests_prop.rs
//
// `Iterator::max_by` returns the LAST maximal element, so a tie is resolved by
// iteration order. The gate below pins the tie-break; the fix is the carrier type
// of the field, in `lib.rs`, because the consumer is in another crate and cannot
// be asked to know an ordering rule it has no way to discover.

/// Two categories with **identical rule profiles**, so their Shannon entropies
/// are bit-identical and the argmax over them is a tie.
fn symmetric_tie_bundle() -> ParserBundle {
    let mut bundle = wide_bundle();
    bundle.grammar_name = "SymmetricTie".to_string();
    bundle.categories = vec![category("Alpha", true), category("Beta", false)];
    bundle.all_syntax = vec![
        ("A1".to_string(), "Alpha".to_string(), vec![term("a1"), nt("Alpha", "x")]),
        ("A2".to_string(), "Alpha".to_string(), vec![term("a2"), nt("Alpha", "x")]),
        ("A3".to_string(), "Alpha".to_string(), vec![term("a3"), nt("Alpha", "x")]),
        ("B1".to_string(), "Beta".to_string(), vec![term("b1"), nt("Beta", "x")]),
        ("B2".to_string(), "Beta".to_string(), vec![term("b2"), nt("Beta", "x")]),
        ("B3".to_string(), "Beta".to_string(), vec![term("b3"), nt("Beta", "x")]),
    ];
    bundle
}

/// The category name codegen would emit for `bundle`, computed the way codegen
/// computes it.
///
/// Deliberately a **copy** of the consumer's expression rather than a call into
/// it: `macros` depends on `prattail`, so this crate cannot call that function,
/// and a paraphrase would let the two drift. The shape mirrors
/// `macros/src/gen/test_gen/simulation_tests.rs:36-42` line for line.
fn codegen_primary_category(bundle: &ParserBundle) -> Option<String> {
    // Recomputed per call: the real pipeline computes this once per build, and a
    // *fresh* collection is what gets a fresh `RandomState` seed. Reusing one
    // instance across runs would make any hash-ordered carrier look stable.
    let prob = crate::probabilistic::analyze_from_bundle(&bundle.all_syntax, &bundle.categories);
    let advanced = AdvancedAnalysisBundle {
        symbolic: None,
        alternating: None,
        bisimulation: None,
        vpa: None,
        register: None,
        probabilistic: Some(&prob),
        multi_tape: None,
        buchi: None,
        _phantom: std::marker::PhantomData,
    };
    let analysis = build_pipeline_analysis(
        &HashSet::new(),
        &HashMap::new(),
        &bundle.categories,
        &[],
        HashMap::new(),
        &advanced,
    );
    analysis
        .per_category_entropy
        .iter()
        .max_by(|a, b| a.1.partial_cmp(b.1).unwrap_or(std::cmp::Ordering::Equal))
        .map(|(name, _)| name.clone())
}

/// The category name that reaches generated source is a function of the grammar,
/// **including when the entropy maximum is a tie**.
///
/// # Why the tie fixture is the whole test
///
/// On a grammar with a strict entropy maximum this is stable no matter what the
/// carrier is, so a "realistic" fixture would pass with the defect present — the
/// exact vacuity this campaign keeps producing. [`symmetric_tie_bundle`] instead
/// makes two categories' entropies bit-identical, which is the *only* condition
/// under which iteration order decides, and therefore the only fixture that
/// tests anything.
///
/// Ties are not exotic: two categories with the same multiset of rule weights are
/// exactly tied, and every single-rule category has entropy exactly `0.0`.
///
/// With `per_category_entropy` reverted to a `HashMap` this fails: measured
/// 2 distinct winners over 20 runs, `Alpha` and `Beta`.
#[test]
fn codegen_visible_argmax_is_stable_under_an_entropy_tie() {
    /// With `k = 2` tied winners, `n` runs miss the instability with probability
    /// `2^(1-n)`; at `n = 20` that is under one in half a million.
    const REPEATS: usize = 20;
    let bundle = symmetric_tie_bundle();

    let winners: BTreeSet<Option<String>> = (0..REPEATS)
        .map(|_| codegen_primary_category(&bundle))
        .collect();

    assert_eq!(
        winners.len(),
        1,
        "the category codegen names in `arb_<cat>(3u32)` varied across {REPEATS} runs of the \
         same grammar: {winners:?}. `Iterator::max_by` returns the LAST maximal element, so \
         when two categories' entropies are equal the winner is whichever the map yields \
         last — and generated source therefore differs between builds. Fix the carrier of \
         `PipelineAnalysis::per_category_entropy`, not the consumer: the consumer is in \
         `macros`, which cannot be asked to know an ordering rule this crate never states.",
    );

    // Non-vacuity: a fixture that produced no entropy entries at all would make
    // the set above a single `None` and say nothing.
    assert!(
        winners.contains(&Some("Beta".to_string())),
        "expected the tie to resolve to `Beta` — the last of the two tied categories in key \
         order — but the single winner was {winners:?}. If this fixture stopped producing \
         two tied categories it is no longer testing a tie-break.",
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// The gate
// ══════════════════════════════════════════════════════════════════════════════

/// Every field of [`MathAnalysisResults`] must be reproducible across repeated
/// runs of the analysis phase on one grammar.
///
/// # ⚠ Reverting the producer-side fix must turn this red
///
/// Two guards written in this campaign stayed green with their own fix reverted,
/// because the census and the gate moved together. This one cannot: it derives
/// the offending set *from the rendered results*, not from any list here. Put
/// `HashSet` back in `petri::analyze_from_bundle` and `petri_result.unbounded_places`
/// reappears in the message below with no edit to this file.
#[test]
fn analysis_results_are_reproducible_across_runs() {
    let bundle = wide_bundle();
    let wpds = wpds_for(&bundle);
    let runs: Vec<Vec<String>> = (0..DETERMINISM_REPEATS)
        .map(|_| render(run_math_analyses_sequential(&bundle, Some(&wpds), true)))
        .collect();

    let line_count = runs[0].len();
    for (attempt, run) in runs.iter().enumerate() {
        assert_eq!(
            run.len(),
            line_count,
            "run {attempt} rendered {} lines and run 0 rendered {line_count} — the analysis \
             phase is not even producing the same SHAPE twice, so some result's element \
             COUNT is nondeterministic, not merely its order",
            run.len(),
        );
    }

    assert!(
        line_count >= NON_VACUITY_FLOOR,
        "the fixture rendered only {line_count} result lines, under the non-vacuity floor of \
         {NON_VACUITY_FLOOR}: this gate would pass without having examined enough of the \
         analysis phase to have caught #173. Either the fixture stopped reaching the \
         analyses or the analyses stopped returning results.",
    );

    // Coverage affordance: this gate is silent about any analysis that returned
    // `None`, so being able to see the render is part of reading its result.
    if std::env::var("PRATTAIL_DETERMINISM_DUMP").is_ok() {
        println!("{}", runs[0].join("\n"));
    }

    let findings = irreproducible(&runs);
    let report: Vec<String> = findings
        .iter()
        .map(|(path, variants)| format!("    {path}\n        {variants}"))
        .collect();
    assert!(
        findings.is_empty(),
        "{} analysis result field(s) are NOT reproducible across {DETERMINISM_REPEATS} runs \
         of the same grammar. Each is a value materialised by iterating a `HashSet`/`HashMap`, \
         whose order `std` randomises per instance; fix each at the PRODUCER, where the \
         collection is built, not at its consumers.\n{}",
        findings.len(),
        report.join("\n"),
    );
}
