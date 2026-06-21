use super::*;

// ═══════════════════════════════════════════════════════════════════════════════
// §7  GrammarDispatchPlan — per-grammar classification and module schedule
// ═══════════════════════════════════════════════════════════════════════════════

/// Dispatch plan for a grammar: aggregate signature, per-predicate profiles,
/// and an ordered module schedule.
#[derive(Debug, Clone)]
pub struct GrammarDispatchPlan {
    /// Union of all predicate signatures in the grammar.
    pub aggregate_signature: PredicateSignature,
    /// Profile for each predicate found in the grammar.
    pub predicate_profiles: Vec<PredicateProfile>,
    /// Modules to invoke, ordered by estimated cost (cheapest first).
    pub module_schedule: Vec<ModuleId>,
    /// Number of modules that would have run unconditionally but are now skipped.
    pub modules_skipped: u32,
}

impl GrammarDispatchPlan {
    /// Check if a module is needed by this grammar.
    pub fn requires(&self, module: ModuleId) -> bool {
        self.aggregate_signature.contains(module.bit())
    }

    /// Modules that are NOT needed (for diagnostic reporting).
    pub fn skipped_modules(&self) -> Vec<ModuleId> {
        ModuleId::ALL
            .iter()
            .copied()
            .filter(|m| !self.requires(*m))
            .collect()
    }
}

/// Classify a grammar to build a `GrammarDispatchPlan`.
///
/// Scans `all_syntax` for predicate-bearing rules, extracts channel context
/// from multi-category references, computes per-predicate profiles, and unions
/// into an aggregate signature that controls Phase 7 module spawning.
///
/// Currently, since predicates are not yet parsed from grammar rules (they come
/// from the forthcoming predicated-types codegen pipeline), this function
/// constructs a base plan from grammar structure heuristics:
/// - Cross-category rules → multi-tape / two-way potential
/// - Multiple categories → channel context richness
/// - Collection patterns → multiset potential
pub fn classify_grammar(
    all_syntax: &[(String, String, Vec<SyntaxItemSpec>)],
    categories: &[CategoryInfo],
) -> GrammarDispatchPlan {
    classify_grammar_with_config(all_syntax, categories, None)
}

/// Classify a grammar with optional `GuardConfigSpec` for data-driven dispatch.
///
/// When `guard_config` is `Some`, theory registrations and channel
/// declarations override the heuristic keyword/structural inference for
/// the corresponding modules:
///
/// - Theory `PresburgerAlgebra` → activates M12 (Linear Arithmetic)
/// - Theory `UnificationTheory` → activates M13 (Unification)
/// - Theory `LatticeTheory` → activates M14 (Subtype Lattice)
/// - Channel categories present → activates M8 (Multi-Tape) when ≥2 join
///   pattern channel parameters exist; M11 (Two-Way) when ≥2 distinct
///   channel categories appear across joins
///
/// All other module activations (M2 Büchi, M3 AWA, M4 VPA, etc.) remain
/// structural and are inferred from the grammar shape regardless of
/// guard config.
///
/// When `guard_config` is `None`, behavior is identical to the original
/// `classify_grammar` (full heuristic inference).
pub fn classify_grammar_with_config(
    all_syntax: &[(String, String, Vec<SyntaxItemSpec>)],
    _categories: &[CategoryInfo],
    guard_config: Option<&crate::GuardConfigSpec>,
) -> GrammarDispatchPlan {
    let mut aggregate = PredicateSignature::new();
    let profiles = Vec::new();

    // ── Build category reference graph for recursion/cycle detection ──────
    let mut category_refs: HashMap<&str, HashSet<&str>> = HashMap::new();
    let mut rules_per_category: HashMap<&str, usize> = HashMap::new();
    let mut has_binders = false;
    let mut has_branching = false;

    // Terminal symbol sets for bracket detection
    let mut terminals: HashSet<&str> = HashSet::new();

    // Build channel context: each category acts as a "channel"
    let mut ctx = ChannelContext::new();
    for (_label, category, syntax) in all_syntax {
        *rules_per_category.entry(category.as_str()).or_default() += 1;

        // Collect non-terminal references from this rule
        let mut nt_count = 0usize;
        for item in syntax {
            match item {
                SyntaxItemSpec::NonTerminal { category: ref cat, param_name } => {
                    ctx.bind(param_name.clone(), cat.clone());
                    category_refs
                        .entry(category.as_str())
                        .or_default()
                        .insert(cat.as_str());
                    nt_count += 1;
                },
                SyntaxItemSpec::Binder { param_name, category: ref cat, .. } => {
                    ctx.bind(param_name.clone(), cat.clone());
                    category_refs
                        .entry(category.as_str())
                        .or_default()
                        .insert(cat.as_str());
                    has_binders = true;
                    nt_count += 1;
                },
                SyntaxItemSpec::Collection { param_name, element_category, .. } => {
                    ctx.bind(param_name.clone(), element_category.clone());
                    category_refs
                        .entry(category.as_str())
                        .or_default()
                        .insert(element_category.as_str());
                },
                SyntaxItemSpec::Terminal(value) => {
                    terminals.insert(value.as_str());
                },
                _ => {},
            }
        }

        // Track branching: ≥3 non-terminal children in a single rule
        if nt_count >= 3 {
            has_branching = true;
        }

        // ── Layer 3 cleanup: gate the structural cross-category heuristic ──
        // When the language declares an explicit `channels { }` block, those
        // declarations are the sole authority for M8/M11 activation. The
        // heuristic only runs when no explicit channels are declared,
        // preserving backward compatibility for languages without
        // `guards { channels { } }`.
        //
        // See: docs/design/dispatch/predicate-dispatch-integration.md
        let explicit_channels = guard_config
            .map(|gc| gc.channel_categories.is_some())
            .unwrap_or(false);
        if !explicit_channels {
            // Heuristic: cross-category rules suggest multi-tape / two-way patterns
            let referenced_categories: HashSet<&str> = syntax
                .iter()
                .filter_map(|item| match item {
                    SyntaxItemSpec::NonTerminal { category: cat, .. } => Some(cat.as_str()),
                    SyntaxItemSpec::Binder { category: cat, .. } => Some(cat.as_str()),
                    SyntaxItemSpec::Collection { element_category, .. } => {
                        Some(element_category.as_str())
                    },
                    _ => None,
                })
                .collect();

            if referenced_categories.len() >= 2 {
                aggregate.set(PredicateSignature::M8_MULTI_TAPE);
                // Only set two-way if there's a cross-category reference that differs from rule's category
                let has_cross = referenced_categories
                    .iter()
                    .any(|cat| *cat != category.as_str());
                if has_cross {
                    aggregate.set(PredicateSignature::M11_TWO_WAY);
                }
            }
        }

        // Collection patterns → multiset potential
        let has_collection = syntax.iter().any(|item| {
            matches!(item, SyntaxItemSpec::Collection { .. } | SyntaxItemSpec::Sep { .. })
        });
        if has_collection {
            aggregate.set(PredicateSignature::M9_MULTISET);
        }
    }

    // ── M2 Büchi: Recursive category detection ───────────────────────────
    // A category C is recursive if C ∈ refs(C) (direct self-reference).
    let has_recursion = category_refs.iter().any(|(cat, refs)| refs.contains(cat));
    if has_recursion {
        aggregate.set(PredicateSignature::M2_BUCHI);
    }

    // ── M3 AWA: Multi-branch universal rules ─────────────────────────────
    // Rules with ≥3 non-terminal children suggest universal branching.
    if has_branching {
        aggregate.set(PredicateSignature::M3_AWA);
    }

    // ── M4 VPA: Bracket/delimiter detection ──────────────────────────────
    // Paired call/return terminals indicate visible pushdown structure.
    let call_symbols = ["(", "{", "[", "begin", "do"];
    let return_symbols = [")", "}", "]", "end", "done"];
    let has_call = call_symbols.iter().any(|s| terminals.contains(s));
    let has_return = return_symbols.iter().any(|s| terminals.contains(s));
    if has_call && has_return {
        aggregate.set(PredicateSignature::M4_VPA);
    }

    // ── M5 Parity Tree: Recursive AST with ranked branching ──────────────
    // Recursive category + branching children = tree structure needing
    // mu-calculus fixpoint analysis. Neither alone suffices.
    if has_recursion && has_branching {
        aggregate.set(PredicateSignature::M5_PARITY_TREE);
    }

    // ── M6 Register: Binder/name patterns ────────────────────────────────
    // Binder items introduce variable scopes requiring register automata
    // for scope-correctness and freshness tracking.
    if has_binders {
        aggregate.set(PredicateSignature::M6_REGISTER);
    }

    // ── M7 Probabilistic: Ambiguous rules ────────────────────────────────
    // ≥3 rules in the same category suggest parse ambiguity needing
    // statistical disambiguation. Binary choice is deterministic.
    let has_ambiguity = rules_per_category.values().any(|&count| count >= 3);
    if has_ambiguity {
        aggregate.set(PredicateSignature::M7_PROBABILISTIC);
    }

    // ── M12 Linear Arithmetic: Numeric terminal patterns ──────────────
    // Heuristic fallback: grammars with arithmetic operators suggest
    // numeric guard predicates that benefit from Presburger analysis.
    // Bypassed when an explicit `theories { … = PresburgerAlgebra for [...]; }`
    // registration is present — see Phase 6 explicit-theory activation below.
    if !theory_registered(guard_config, TheoryKind::Presburger) {
        let arithmetic_terminals = ["+", "-", "*", "/", "%", "mod", "div"];
        let has_arithmetic = arithmetic_terminals.iter().any(|s| terminals.contains(s));
        if has_arithmetic {
            aggregate.set(PredicateSignature::M12_LINEAR_ARITHMETIC);
        }
    }

    // ── M13 Unification: Pattern matching terminals ──────────────────
    // Heuristic fallback: grammars with match/case constructs suggest
    // structural pattern guards needing unification for satisfiability
    // analysis. Bypassed when an explicit `UnificationTheory` registration
    // is present.
    if !theory_registered(guard_config, TheoryKind::Unification) {
        let unification_terminals = ["match", "case", "with", "=>", "->", "|"];
        let has_pattern_match = unification_terminals.iter().any(|s| terminals.contains(s));
        if has_pattern_match {
            aggregate.set(PredicateSignature::M13_UNIFICATION);
        }
    }

    // ── M14 Subtype Lattice: Type hierarchy terminals ─────────────────
    // Heuristic fallback: grammars with subtype/extends/implements
    // constructs suggest type hierarchy guards needing lattice analysis.
    // Bypassed when an explicit `LatticeTheory` registration is present.
    if !theory_registered(guard_config, TheoryKind::Lattice) {
        let subtype_terminals = ["extends", "implements", ":", "::", ":<", "is"];
        let has_type_hierarchy = subtype_terminals.iter().any(|s| terminals.contains(s));
        if has_type_hierarchy {
            aggregate.set(PredicateSignature::M14_SUBTYPE_LATTICE);
        }
    }

    // ── M15 SFT: Output-producing transductions ─────────────────────
    // Activated when the grammar has both cross-category references and
    // recursion, suggesting guard-driven term transformations that
    // benefit from SFT composition analysis.
    if has_recursion && aggregate.contains(PredicateSignature::M11_TWO_WAY) {
        aggregate.set(PredicateSignature::M15_SFT);
    }

    // ── Data-driven overrides from `guards { }` configuration ────────
    // Design doc §2A: when an explicit `theories {}` or `channels {}`
    // sub-block is present, prefer it over heuristic inference for the
    // affected modules.
    if let Some(gc) = guard_config {
        // ── Theory-driven module activation ────────────────────────────
        // Each registered theory's `theory_type` is matched against known
        // theory names to determine which automaton module to activate.
        // The match is on the *quoted* type name, which is what the macro
        // bridge produces (e.g., "PresburgerAlgebra", "UnificationTheory").
        for theory in &gc.theories {
            match theory.theory_type.as_str() {
                "PresburgerAlgebra" | "Presburger" | "PresburgerTheory" => {
                    aggregate.set(PredicateSignature::M12_LINEAR_ARITHMETIC);
                },
                "UnificationTheory" | "Unification" => {
                    aggregate.set(PredicateSignature::M13_UNIFICATION);
                },
                "LatticeTheory" | "Lattice" => {
                    aggregate.set(PredicateSignature::M14_SUBTYPE_LATTICE);
                },
                _ => {
                    // Unknown theory type — fall through to heuristic
                    // (which already ran above). Future theories can
                    // register here.
                },
            }
        }

        // ── Channel-driven M8/M11 activation ───────────────────────────
        // Explicit channel declarations replace heuristic cross-category
        // inference. The activation rules are deterministic:
        //   M8 fires when any join pattern has ≥2 channel params.
        //   M11 fires additionally when ≥2 distinct channel categories
        //   appear across all join patterns.
        if gc.channel_categories.is_some() {
            // Reset heuristic activation and rely on explicit declarations.
            // (This is a no-op when the heuristic also fired; it ensures
            // determinism when the heuristic over-activated.)
            let mut m8_active = false;
            let mut distinct_cats: HashSet<&str> = HashSet::new();
            for jp in &gc.join_patterns {
                if jp.channel_categories.len() >= 2 {
                    m8_active = true;
                }
                for cat in &jp.channel_categories {
                    distinct_cats.insert(cat.as_str());
                }
            }
            if m8_active {
                aggregate.set(PredicateSignature::M8_MULTI_TAPE);
            }
            if m8_active && distinct_cats.len() >= 2 {
                aggregate.set(PredicateSignature::M11_TWO_WAY);
            }
        }
    }

    // Build module schedule from aggregate signature
    let mut schedule: Vec<ModuleId> = ModuleId::ALL
        .iter()
        .copied()
        .filter(|m| aggregate.contains(m.bit()))
        .collect();
    schedule.sort_by_key(|m| m.estimated_cost());

    let skipped = PredicateSignature::NUM_MODULES - aggregate.count();

    GrammarDispatchPlan {
        aggregate_signature: aggregate,
        predicate_profiles: profiles,
        module_schedule: schedule,
        modules_skipped: skipped,
    }
}
