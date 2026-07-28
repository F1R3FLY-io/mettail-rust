use super::*;

/// Produced by `analyze_wpds()` and consumed by:
/// - `lint.rs`: Stack-aware dead-rule detection (W13), complexity report (D14)
/// - `cost_benefit.rs`: Ambiguity refinement (A5)
/// - Pipeline diagnostics (P05)
#[derive(Debug, Clone)]
pub struct WpdsAnalysis {
    /// Grammar name.
    pub grammar_name: String,
    /// Number of stack symbols.
    pub num_symbols: usize,
    /// Number of PDS rules.
    pub num_rules: usize,
    /// Stack-aware reachability: which category entry symbols are reachable from root.
    pub reachable_categories: HashSet<String>,
    /// Stack-aware unreachable rule labels with witness info.
    pub unreachable_rules: Vec<WpdsUnreachableRule>,
    /// Per-category weight from poststar (TropicalWeight).
    pub category_weights: HashMap<String, f64>,
    /// G33: Directed call graph extracted from Push rules.
    pub call_graph: WpdsCallGraph,
    /// G34: Per-category recursion depth bounds.
    pub depth_bounds: HashMap<String, DepthBounds>,
    /// G35: Classified cycles (direct, mutual, left-recursive).
    pub cycles: Vec<CycleInfo>,
    /// G36: Calling contexts per category (who calls each category and from where).
    pub calling_contexts: HashMap<String, Vec<CallingContext>>,
    /// CS-01: Context-sensitive rule tables per category.
    /// Maps `category → ContextRuleTable`.
    /// Empty if no category benefits from context narrowing.
    pub context_rule_tables: HashMap<String, ContextRuleTable>,
    /// CS-04: Per-call-site effective binding power.
    /// Maps `(caller_cat, callee_cat) → min_bp`.
    /// When different callers use different min_bp values, CS-04 threads
    /// the caller-specific BP through cross-category dispatch.
    pub cross_category_bp: HashMap<(String, String), Vec<u8>>,
    /// CS-05: Per-context ambiguity status for categories.
    /// Maps `category → is_unambiguous_in_all_contexts`.
    /// When true, NFA try-all can commit to the first success (skip save/restore).
    pub context_unambiguous: HashMap<String, bool>,
    /// CEK-3: Bidirectional mapping between trampoline Frame_Cat variants
    /// and WPDS StackSymbol triples. Enables transfer of WPDS analysis
    /// results to runtime frame structure.
    pub cek_bijection: CekWpdsBijection,
    /// CEK-4: Retained P-automaton from poststar (TropicalWeight).
    /// Used by dead frame elimination to determine which frame variants
    /// are unreachable in valid stack contexts.
    pub pautomaton: PAutomaton<TropicalWeight>,
}

impl WpdsAnalysis {
    /// Create a minimal WpdsAnalysis for use in tests.
    #[cfg(test)]
    pub fn empty_for_test() -> Self {
        WpdsAnalysis {
            grammar_name: String::new(),
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
            cek_bijection: CekWpdsBijection::new(),
            pautomaton: PAutomaton::new(0),
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// CS-01: Context-Sensitive Rule Tables
// ══════════════════════════════════════════════════════════════════════════════

/// A context entry mapping a calling context tag to a set of valid rule indices.
#[derive(Debug, Clone)]
pub struct ContextEntry {
    /// The calling context tag (caller category name or "top-level").
    pub context_tag: String,
    /// Indices of rules valid in this context (into the category's rule list).
    pub valid_rules: Vec<String>,
}

/// Per-category context-sensitive rule table.
///
/// Maps calling contexts to valid rule sets. When all contexts yield the same
/// rule set, the table is trivial (no benefit from context-sensitive dispatch).
#[derive(Debug, Clone)]
pub struct ContextRuleTable {
    /// Category this table serves.
    pub category: String,
    /// One entry per calling context.
    pub entries: Vec<ContextEntry>,
    /// Whether the table is non-trivial (at least one context has a reduced rule set).
    pub is_nontrivial: bool,
    /// Number of contexts where the rule set becomes a singleton (direct dispatch).
    pub singleton_contexts: usize,
}

/// Build context-sensitive rule tables from WPDS analysis.
///
/// For each category with calling contexts, determines which rules are reachable
/// from each calling context. If different contexts yield different rule sets,
/// the table is non-trivial and can be used for context-sensitive dispatch.
pub fn build_context_rule_tables(
    calling_contexts: &HashMap<String, Vec<CallingContext>>,
    reachable_categories: &HashSet<String>,
    all_rules: &[(String, String)], // (rule_label, category) pairs
) -> HashMap<String, ContextRuleTable> {
    let mut tables = HashMap::new();

    // Group rules by category
    let mut rules_by_cat: HashMap<&str, Vec<&str>> = HashMap::new();
    for (label, cat) in all_rules {
        rules_by_cat
            .entry(cat.as_str())
            .or_default()
            .push(label.as_str());
    }

    for (cat, contexts) in calling_contexts {
        if !reachable_categories.contains(cat) || contexts.is_empty() {
            continue;
        }

        let all_rules_for_cat: Vec<String> = rules_by_cat
            .get(cat.as_str())
            .map(|v| v.iter().map(|s| s.to_string()).collect())
            .unwrap_or_default();

        if all_rules_for_cat.is_empty() {
            continue;
        }

        // Group calling contexts by caller category
        let mut contexts_by_caller: HashMap<&str, Vec<&CallingContext>> = HashMap::new();
        for ctx in contexts {
            contexts_by_caller
                .entry(ctx.caller_category.as_str())
                .or_default()
                .push(ctx);
        }

        let mut entries = Vec::new();
        let mut is_nontrivial = false;
        let mut singleton_count = 0usize;

        for (caller_cat, _caller_contexts) in &contexts_by_caller {
            // For now, all rules are valid from any calling context.
            // Full rule filtering requires poststar per-rule-per-context reachability,
            // which is expensive. Here we record the structure for downstream use.
            // The actual filtering happens when we have per-rule reachability data.
            let valid = all_rules_for_cat.clone();

            if valid.len() < all_rules_for_cat.len() {
                is_nontrivial = true;
            }
            if valid.len() == 1 {
                singleton_count += 1;
            }

            entries.push(ContextEntry {
                context_tag: caller_cat.to_string(),
                valid_rules: valid,
            });
        }

        // Also add a "top-level" entry if this is the primary category
        // (called directly, not via Push)
        entries.push(ContextEntry {
            context_tag: "top-level".to_string(),
            valid_rules: all_rules_for_cat,
        });

        tables.insert(
            cat.clone(),
            ContextRuleTable {
                category: cat.clone(),
                entries,
                is_nontrivial,
                singleton_contexts: singleton_count,
            },
        );
    }

    tables
}

// ══════════════════════════════════════════════════════════════════════════════
// CS-04: Cross-Category BP Analysis
// ══════════════════════════════════════════════════════════════════════════════

/// Analyze cross-category binding power usage from WPDS Push rules.
///
/// Returns `(caller_cat, callee_cat) → [min_bp_values]`. When different callers
/// use different min_bp values, CS-04 can thread caller-specific BP through
/// cross-category dispatch instead of hardcoded 0.
///
/// Current implementation records structural information; actual BP values
/// require integration with the binding power table.
pub fn analyze_cross_category_bp<W: Semiring>(
    wpds: &Wpds<W>,
) -> HashMap<(String, String), Vec<u8>> {
    let mut bp_map: HashMap<(String, String), Vec<u8>> = HashMap::new();

    for rule in &wpds.rules {
        if let WpdsRule::Push { from_gamma, to_gamma_top, .. } = rule {
            let caller = &from_gamma.category;
            let callee = &to_gamma_top.category;
            if !caller.is_empty() && !callee.is_empty() && caller != callee {
                // Record call position as a proxy for BP context
                // Position 0 = prefix context (min_bp typically 0)
                // Position > 0 = could be infix context (min_bp > 0)
                let bp_hint = if from_gamma.position == 0 { 0u8 } else { 1u8 };
                bp_map
                    .entry((caller.clone(), callee.clone()))
                    .or_default()
                    .push(bp_hint);
            }
        }
    }

    // Deduplicate BP values per edge
    for values in bp_map.values_mut() {
        values.sort_unstable();
        values.dedup();
    }

    bp_map
}

// ══════════════════════════════════════════════════════════════════════════════
// CS-05: Context-Aware Ambiguity Resolution
// ══════════════════════════════════════════════════════════════════════════════

/// Determine per-category context ambiguity status.
///
/// A category is "context-unambiguous" if it has exactly one calling context
/// and the WPDS shows it is fully determined in that context. For such
/// categories, NFA try-all can commit to the first success.
pub fn analyze_context_ambiguity(
    calling_contexts: &HashMap<String, Vec<CallingContext>>,
    reachable_categories: &HashSet<String>,
) -> HashMap<String, bool> {
    let mut result = HashMap::new();

    for cat in reachable_categories {
        let context_count = calling_contexts
            .get(cat)
            .map(|c| {
                // Count unique caller categories
                let unique_callers: HashSet<&str> =
                    c.iter().map(|x| x.caller_category.as_str()).collect();
                unique_callers.len()
            })
            .unwrap_or(0);

        // A category is unambiguous if it has 0 or 1 calling context
        // (0 = top-level only, 1 = called from exactly one category)
        result.insert(cat.clone(), context_count <= 1);
    }

    result
}

/// A rule determined unreachable by WPDS stack-aware analysis.
#[derive(Debug, Clone)]
pub struct WpdsUnreachableRule {
    /// Rule label.
    pub rule_label: String,
    /// Category.
    pub category: String,
    /// Witness: which calling contexts are missing.
    pub missing_contexts: Vec<String>,
    /// D15: Witness trace — shortest hypothetical Push chain that would make this
    /// rule reachable. Computed via BFS on the call graph (G33).
    pub witness_trace: Vec<String>,
}

impl fmt::Display for WpdsUnreachableRule {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "rule `{}` in `{}` is WPDS-unreachable", self.rule_label, self.category)?;
        if !self.missing_contexts.is_empty() {
            write!(f, " (missing callers: {})", self.missing_contexts.join(", "))?;
        }
        Ok(())
    }
}

/// Minimal category info for WPDS construction from pipeline bundles.
pub struct WpdsCategoryInfo {
    pub name: String,
    pub is_primary: bool,
}

/// Run full WPDS analysis from pipeline bundle data.
///
/// This entry point is used by `pipeline.rs` where the full `LanguageSpec`
/// is not available — only the extracted `ParserBundle` data.
pub fn analyze_wpds_from_bundle(
    grammar_name: &str,
    categories: &[WpdsCategoryInfo],
    all_syntax: &[(String, String, Vec<SyntaxItemSpec>)],
    prediction_wfsts: &HashMap<String, PredictionWfst>,
) -> WpdsAnalysis {
    // Reconstruct a minimal LanguageSpec for the WPDS builder
    let types: Vec<crate::CategorySpec> = categories
        .iter()
        .map(|c| crate::CategorySpec {
            name: c.name.clone(),
            native_type: None,
            is_primary: c.is_primary,
            has_var: true,
        })
        .collect();

    // Reconstruct RuleSpecInputs from all_syntax
    let inputs: Vec<crate::RuleSpecInput> = all_syntax
        .iter()
        .map(|(label, category, syntax)| crate::RuleSpecInput {
            label: label.clone(),
            category: category.clone(),
            syntax: syntax.clone(),
            associativity: crate::binding_power::Associativity::Left,
            // Reconstructed from a syntax-only triple, which carries neither the DSL's
            // `right` nor its `same` annotation — the same provenance loss noted for
            // `is_auto_injected` below. Both default to the unannotated reading.
            shares_level_with_previous: false,
            prefix_precedence: None,
            has_rust_code: false,
            rust_code: None,
            eval_mode: None,
            source_location: None,
            // Reconstructed input from all_syntax loses provenance — assume
            // user-written. Stage 3.13b filter consumes is_auto_injected on
            // RuleSpec, but cek-bridge's reconstruction operates on a
            // syntax-only triple, so we conservatively mark these false.
            is_auto_injected: false,
        })
        .collect();

    let spec = LanguageSpec::new(grammar_name.to_string(), types, inputs);
    analyze_wpds(&spec, prediction_wfsts)
}

/// Run full WPDS analysis on a grammar.
///
/// Builds the WPDS, runs poststar with `BooleanWeight` for reachability,
/// and optionally runs with `TropicalWeight` for weight extraction.
pub fn analyze_wpds(
    spec: &LanguageSpec,
    prediction_wfsts: &HashMap<String, PredictionWfst>,
) -> WpdsAnalysis {
    // Build WPDS with BooleanWeight for reachability
    let bool_wpds = build_wpds(spec, prediction_wfsts, |_| BooleanWeight::one());

    // Run poststar
    let post = poststar(&bool_wpds);

    // Determine reachable categories: a category is reachable if its entry symbol
    // appears in any configuration reachable from the start (not just as a single-element stack)
    let mut reachable_categories = HashSet::new();
    for cat in &spec.types {
        let sym = StackSymbol::category_entry(&cat.name);
        if post.is_symbol_reachable(&sym) {
            reachable_categories.insert(cat.name.clone());
        }
    }

    // Also check reachability from all reachable symbols (rule positions referencing categories)
    for (sym, w) in post.reachable_symbols() {
        if !w.is_zero() && !sym.category.is_empty() {
            reachable_categories.insert(sym.category.clone());
        }
    }

    // The initial category is always reachable
    if let Some(primary) = spec.types.iter().find(|t| t.is_primary) {
        reachable_categories.insert(primary.name.clone());
    }

    // G33: Extract call graph from the WPDS
    let call_graph = extract_call_graph(&bool_wpds);

    // G34: Compute recursion depth bounds
    let primary_cat = spec
        .types
        .iter()
        .find(|t| t.is_primary)
        .map(|t| t.name.as_str())
        .unwrap_or("");
    let depth_bounds = compute_depth_bounds(&call_graph, primary_cat);

    // G35: Classify cycles
    let cycles = classify_cycles(&call_graph, &bool_wpds);

    // G36: Compute calling contexts
    let calling_contexts = compute_calling_contexts(&bool_wpds);

    // Find unreachable rules
    let mut unreachable_rules = Vec::new();
    for rule in &spec.rules {
        let rule_entry = StackSymbol::rule_position(&rule.category, &rule.label, 0);
        // Liveness, not one-symbol acceptance: a rule entry reached by a
        // cross-category PUSH sits on a transition into poststar's fresh
        // intermediate state, so `symbol_weight` (which requires an ACCEPTING
        // target) is zero for it and would call the rule dead.
        let rule_weight = post.stack_top_weight(&rule_entry);

        if rule_weight.is_zero() && !reachable_categories.contains(&rule.category) {
            // Find which calling contexts are missing
            let missing = find_missing_callers(spec, &rule.category, &reachable_categories);
            // D15: Compute witness trace via shortest path in call graph
            let witness_trace =
                shortest_path_witness(&call_graph, &reachable_categories, &rule.category);
            unreachable_rules.push(WpdsUnreachableRule {
                rule_label: rule.label.clone(),
                category: rule.category.clone(),
                missing_contexts: missing,
                witness_trace,
            });
        }
    }

    // Build TropicalWeight WPDS for weight extraction
    let trop_wpds = build_wpds(spec, prediction_wfsts, TropicalWeight::new);
    let trop_post = poststar(&trop_wpds);

    let mut category_weights = HashMap::new();
    for cat in &spec.types {
        let sym = StackSymbol::category_entry(&cat.name);
        // Liveness: a called category is pushed, so its entry is the top of a
        // longer stack rather than a one-symbol configuration.
        let w = trop_post.stack_top_weight(&sym);
        if !w.is_zero() {
            category_weights.insert(cat.name.clone(), w.value());
        }
    }

    // CS-01: Build context-sensitive rule tables
    let all_rules: Vec<(String, String)> = spec
        .rules
        .iter()
        .map(|r| (r.label.clone(), r.category.clone()))
        .collect();
    let context_rule_tables =
        build_context_rule_tables(&calling_contexts, &reachable_categories, &all_rules);

    // CS-04: Analyze cross-category binding power interactions
    let cross_category_bp = analyze_cross_category_bp(&bool_wpds);

    // CS-05: Analyze per-category context ambiguity
    let context_unambiguous = analyze_context_ambiguity(&calling_contexts, &reachable_categories);

    // CEK-3: Build bidirectional mapping between trampoline frames and WPDS stack symbols
    let cek_bijection = build_cek_bijection(spec);

    WpdsAnalysis {
        grammar_name: spec.name.clone(),
        num_symbols: bool_wpds.num_symbols(),
        num_rules: bool_wpds.num_rules(),
        reachable_categories,
        unreachable_rules,
        category_weights,
        call_graph,
        depth_bounds,
        cycles,
        calling_contexts,
        context_rule_tables,
        cross_category_bp,
        context_unambiguous,
        cek_bijection,
        pautomaton: trop_post,
    }
}

/// Find which categories could call the given category but don't.
fn find_missing_callers(
    spec: &LanguageSpec,
    target_cat: &str,
    reachable: &HashSet<String>,
) -> Vec<String> {
    let mut callers = HashSet::new();
    let mut actual_callers = HashSet::new();

    // Find all categories that reference target_cat in their syntax
    for rule in &spec.rules {
        for item in &rule.syntax {
            if references_category(item, target_cat) {
                callers.insert(rule.category.clone());
                if reachable.contains(&rule.category) {
                    actual_callers.insert(rule.category.clone());
                }
            }
        }
    }

    // Missing callers are those in `callers` but not in `actual_callers`
    callers.difference(&actual_callers).cloned().collect()
}

/// Check if a syntax item references a given category.
fn references_category(item: &SyntaxItemSpec, target: &str) -> bool {
    match item {
        SyntaxItemSpec::NonTerminal { category, .. } => category == target,
        SyntaxItemSpec::Binder { category, .. } => category == target,
        SyntaxItemSpec::Collection { element_category, .. } => element_category == target,
        SyntaxItemSpec::Sep { body, .. } => references_category(body, target),
        SyntaxItemSpec::Map { body_items } => {
            body_items.iter().any(|i| references_category(i, target))
        },
        SyntaxItemSpec::Zip { left_category, right_category, body, .. } => {
            left_category == target || right_category == target || references_category(body, target)
        },
        SyntaxItemSpec::Optional { inner } => inner.iter().any(|i| references_category(i, target)),
        _ => false,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// CEK-3: WPDS ↔ Frame Bijection
// ══════════════════════════════════════════════════════════════════════════════

/// CEK-3: Bidirectional mapping between WPDS `StackSymbol` triples and
/// trampoline `Frame_Cat` variant names.
///
/// The trampoline parser's `Frame_Cat` enum and the WPDS's `StackSymbol`
/// alphabet represent the same pushdown automaton from different angles:
/// - `StackSymbol::rule_position(cat, label, wpds_pos+1)` ↔ `RD_{label}_{segment_index}`
///   where `wpds_pos` is the WPDS position of the same-category NonTerminal
/// - `InfixRHS` ↔ intra-rule Replace transitions for infix operators
/// - `CollectionElem_{label}` ↔ collection element loops
/// - `UnaryPrefix_{label}` ↔ prefix unary rules
///
/// This bijection enables WPDS analysis results (reachability, dead rules,
/// context-sensitive FIRST sets) to be transferred directly to the runtime
/// trampoline frame structure.
///
/// ## WPDS vs Trampoline Position Numbering
///
/// The WPDS increments its position counter for **every** `SyntaxItemSpec` item
/// (terminals, cross-category NTs, etc.), while the trampoline only creates
/// segment split points at **same-category** NonTerminal boundaries. The
/// bijection builder walks the syntax items in parallel, tracking both counters,
/// to establish the correct correspondence between `segment_index` and
/// `wpds_pos + 1` (the continuation position after the NT parse).
#[derive(Debug, Clone, Default)]
pub struct CekWpdsBijection {
    /// Map from frame variant name to the corresponding WPDS stack symbol.
    pub frame_to_symbol: HashMap<String, StackSymbol>,
    /// Map from WPDS stack symbol to the corresponding frame variant name.
    pub symbol_to_frame: HashMap<StackSymbol, String>,
}

impl CekWpdsBijection {
    /// Create a new empty bijection.
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert a bidirectional mapping.
    pub fn insert(&mut self, frame_variant: String, symbol: StackSymbol) {
        self.symbol_to_frame
            .insert(symbol.clone(), frame_variant.clone());
        self.frame_to_symbol.insert(frame_variant, symbol);
    }

    /// Insert a convenience alias: adds frame→symbol lookup only, without
    /// overwriting the canonical symbol→frame reverse mapping.
    fn insert_alias(&mut self, frame_variant: String, symbol: StackSymbol) {
        self.frame_to_symbol.insert(frame_variant, symbol);
    }

    /// Look up the WPDS stack symbol for a frame variant name.
    pub fn frame_variant_to_stack_symbol(&self, frame_variant: &str) -> Option<&StackSymbol> {
        self.frame_to_symbol.get(frame_variant)
    }

    /// Look up the frame variant name for a WPDS stack symbol.
    pub fn stack_symbol_to_frame_variant(&self, symbol: &StackSymbol) -> Option<&String> {
        self.symbol_to_frame.get(symbol)
    }

    /// Check that the bijection is complete: every frame variant has a symbol
    /// and every relevant symbol has a frame variant.
    pub fn is_complete(&self) -> bool {
        // Every frame→symbol entry must have a corresponding symbol→frame entry.
        // Aliases (unprefixed convenience names) are valid if the symbol maps back
        // to *any* frame name that resolves to the same symbol.
        self.frame_to_symbol
            .iter()
            .all(|(_frame, sym)| self.symbol_to_frame.contains_key(sym))
    }

    /// Number of mappings in the bijection.
    pub fn len(&self) -> usize {
        self.frame_to_symbol.len()
    }

    /// Whether the bijection is empty.
    pub fn is_empty(&self) -> bool {
        self.frame_to_symbol.is_empty()
    }
}

/// CEK-3: Build the bidirectional mapping between trampoline frame variants
/// and WPDS stack symbols.
///
/// Walks the grammar's rules in parallel with the WPDS stack alphabet
/// to establish correspondences:
///
/// | Frame Variant | WPDS StackSymbol |
/// |---|---|
/// | `RD_{label}_{seg_idx}` | `rule_position(cat, label, wpds_continuation_pos)` |
/// | `InfixRHS` | `rule_position(cat, "__infix__", 1)` |
/// | `GroupClose` | `rule_position(cat, "__group__", 1)` |
/// | `UnaryPrefix_{label}` | `rule_position(cat, label, 1)` (unary prefix) |
/// | `CollectionElem_{label}` | `rule_position(cat, label, 1)` (collection) |
/// | `Mixfix_{label}_{pos}` | `rule_position(cat, label, wpds_continuation_pos)` (mixfix) |
///
/// ## Position Tracking
///
/// The WPDS assigns a position to every `SyntaxItemSpec` in a rule (incrementing
/// for terminals, cross-category NTs, etc.), while the trampoline only creates
/// frame segments at same-category NonTerminal boundaries. This function walks
/// each rule's syntax items, maintaining both the WPDS position counter and the
/// trampoline segment index, emitting a mapping entry when a same-category
/// NonTerminal is encountered.
///
/// The bijection is built from the `LanguageSpec` which is the single source
/// of truth for both the trampoline and the WPDS.
pub fn build_cek_bijection(spec: &LanguageSpec) -> CekWpdsBijection {
    let mut bijection = CekWpdsBijection::new();

    // Group rules by category for efficient lookup
    let mut rules_by_category: HashMap<&str, Vec<&crate::RuleSpec>> = HashMap::new();
    for rule in &spec.rules {
        rules_by_category
            .entry(&rule.category)
            .or_default()
            .push(rule);
    }

    for cat_spec in &spec.types {
        let cat = &cat_spec.name;

        let empty_rules = Vec::new();
        let cat_rules = rules_by_category.get(cat.as_str()).unwrap_or(&empty_rules);

        // InfixRHS: one per category (if has infix operators)
        let has_infix = cat_rules.iter().any(|r| r.is_infix);
        if has_infix {
            let frame = "InfixRHS".to_string();
            let symbol = StackSymbol::rule_position(cat, "__infix__", 1);
            bijection.insert(format!("{}::{}", cat, frame), symbol.clone());
            // Also add unprefixed alias for convenience (first category wins).
            // Uses insert_alias to avoid overwriting the canonical symbol→frame mapping.
            if !bijection.frame_to_symbol.contains_key(&frame) {
                bijection.insert_alias(frame, symbol);
            }
        }

        // GroupClose: one per category
        {
            let frame = "GroupClose".to_string();
            let symbol = StackSymbol::rule_position(cat, "__group__", 1);
            bijection.insert(format!("{}::{}", cat, frame), symbol.clone());
            if !bijection.frame_to_symbol.contains_key(&frame) {
                bijection.insert_alias(frame, symbol);
            }
        }

        for rule_spec in cat_rules {
            let label = &rule_spec.label;

            // UnaryPrefix rules: the terminal is consumed inline, then a single
            // same-category NT triggers the frame push. The WPDS models this as
            // position 0 (terminal) → position 1 (NT). The continuation is at
            // position 2 (after the NT), but for unary prefix the frame captures
            // the state before the NT parse, which maps to the transition at
            // position 1 in the WPDS.
            if rule_spec.is_unary_prefix {
                let frame = format!("UnaryPrefix_{}", label);
                // Walk syntax to find the WPDS position of the same-category NT
                let mut wpds_pos: u32 = 0;
                for item in &rule_spec.syntax {
                    if let SyntaxItemSpec::NonTerminal { category: ref nt_cat, .. } = item {
                        if nt_cat == cat {
                            // Continuation is at wpds_pos + 1
                            let symbol = StackSymbol::rule_position(cat, label, wpds_pos + 1);
                            bijection.insert(frame.clone(), symbol);
                            break;
                        }
                    }
                    wpds_pos += 1;
                }
                continue;
            }

            // Collection rules
            if rule_spec.is_collection {
                let frame = format!("CollectionElem_{}", label);
                // The collection element parse is at the first same-category or
                // element-category NT position. Walk to find it.
                let mut wpds_pos: u32 = 0;
                for item in &rule_spec.syntax {
                    match item {
                        SyntaxItemSpec::Collection { .. } => {
                            // Collection item maps to position wpds_pos + 1
                            let symbol = StackSymbol::rule_position(cat, label, wpds_pos + 1);
                            bijection.insert(frame.clone(), symbol);
                            break;
                        },
                        _ => {},
                    }
                    wpds_pos += 1;
                }
                continue;
            }

            // Mixfix rules: detected by having 3+ NonTerminals and 2+ terminals
            let nt_count = rule_spec
                .syntax
                .iter()
                .filter(|item| matches!(item, SyntaxItemSpec::NonTerminal { .. }))
                .count();
            let terminal_count = rule_spec
                .syntax
                .iter()
                .filter(|item| matches!(item, SyntaxItemSpec::Terminal(_)))
                .count();
            let is_mixfix = nt_count >= 3 && terminal_count >= 2;

            if is_mixfix {
                // Mixfix rules: walk syntax items, tracking WPDS position.
                // Skip the first NT (lhs, already parsed) and first terminal (trigger).
                // Each subsequent NT that is same-category gets a Mixfix frame.
                let mut wpds_pos: u32 = 0;
                let mut skipped_first_nt = false;
                let mut skipped_first_terminal = false;
                let mut mixfix_index = 0;

                for item in &rule_spec.syntax {
                    match item {
                        SyntaxItemSpec::NonTerminal { category: ref nt_cat, .. } => {
                            if !skipped_first_nt {
                                skipped_first_nt = true;
                            } else if nt_cat == cat {
                                // This is a mixfix operand step
                                let frame = format!("Mixfix_{}_{}", label, mixfix_index);
                                let symbol = StackSymbol::rule_position(cat, label, wpds_pos + 1);
                                bijection.insert(frame, symbol);
                                mixfix_index += 1;
                            }
                        },
                        SyntaxItemSpec::Terminal(_) => {
                            if !skipped_first_terminal && skipped_first_nt {
                                skipped_first_terminal = true;
                            }
                        },
                        _ => {},
                    }
                    wpds_pos += 1;
                }
                continue;
            }

            // RD rules: walk syntax items, tracking both WPDS position and
            // trampoline segment index. Only same-category NonTerminals create
            // split points in the trampoline.
            let mut wpds_pos: u32 = 0;
            let mut segment_index = 0;

            for item in &rule_spec.syntax {
                if let SyntaxItemSpec::NonTerminal { category: ref nt_cat, .. } = item {
                    if nt_cat == cat {
                        // Same-category NT: creates a trampoline split point
                        let frame = format!("RD_{}_{}", label, segment_index);
                        // The continuation in WPDS is at wpds_pos + 1
                        let symbol = StackSymbol::rule_position(cat, label, wpds_pos + 1);
                        bijection.insert(frame, symbol);
                        segment_index += 1;
                    }
                }
                wpds_pos += 1;
            }
        }
    }

    bijection
}
