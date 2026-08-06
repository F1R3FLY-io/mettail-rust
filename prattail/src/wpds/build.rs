use super::*;

// ══════════════════════════════════════════════════════════════════════════════
// Grammar → WPDS construction
// ══════════════════════════════════════════════════════════════════════════════

/// Build a WPDS from a `LanguageSpec` and prediction WFST data.
///
/// The construction maps PraTTaIL's grammar structure to PDS rules:
///
/// - **Category entry** (`⟨Cat⟩`): Each category has an entry stack symbol
/// - **Replace**: Terminals + same-category NTs (intraprocedural, per Reps et al. 2007)
/// - **Push**: Cross-category NTs only (interprocedural calls)
/// - **Pop**: Rule completion (return to caller)
/// - **Synthetic Pop**: Category entry for zero-rule categories (e.g. Ambient's Name)
///
/// Weights come from the `PredictionWfst` for each category.
pub fn build_wpds<W: Semiring>(
    spec: &LanguageSpec,
    prediction_wfsts: &HashMap<String, PredictionWfst>,
    weight_fn: impl Fn(f64) -> W,
) -> Wpds<W> {
    let primary_cat = spec
        .types
        .iter()
        .find(|t| t.is_primary)
        .map(|t| t.name.as_str())
        .unwrap_or_else(|| spec.types.first().map(|t| t.name.as_str()).unwrap_or(""));

    let initial_symbol = StackSymbol::category_entry(primary_cat);

    let mut wpds = Wpds {
        stack_symbols: Vec::new(),
        symbol_index: HashMap::new(),
        rules: Vec::new(),
        rules_by_source: HashMap::new(),
        initial_symbol: initial_symbol.clone(),
        grammar_name: spec.name.clone(),
    };

    // Register initial symbol
    wpds.ensure_symbol(initial_symbol.clone());

    // Note: Multi-type language reachability is handled by compute_dead_frames()
    // in pipeline.rs, which exempts non-primary categories that have rules
    // (they are independently parseable). The WPDS reachability analysis is
    // strictly from the primary category, preserving orphan detection.

    // Group rules by category
    let mut rules_by_category: HashMap<&str, Vec<&crate::RuleSpec>> = HashMap::new();
    for rule in &spec.rules {
        rules_by_category
            .entry(&rule.category)
            .or_default()
            .push(rule);
    }

    // For each category and its rules, build PDS rules
    for cat_spec in &spec.types {
        let cat = &cat_spec.name;
        let cat_entry = StackSymbol::category_entry(cat);
        wpds.ensure_symbol(cat_entry.clone());

        let empty_rules = Vec::new();
        let cat_rules = rules_by_category.get(cat.as_str()).unwrap_or(&empty_rules);

        // Look up WFST weights for rules in this category
        let wfst = prediction_wfsts.get(cat);

        for rule_spec in cat_rules {
            let label = &rule_spec.label;

            // Get weight from WFST or default to one()
            let rule_weight = wfst
                .and_then(|w| {
                    w.actions
                        .iter()
                        .find(|a| a.action.rule_label() == *label)
                        .map(|a| a.weight.value())
                })
                .unwrap_or(0.0);

            let w = weight_fn(rule_weight);

            // Create rule entry point
            let rule_entry = StackSymbol::rule_position(cat, label, 0);
            wpds.ensure_symbol(rule_entry.clone());

            // Category entry → rule entry (Replace): dispatching to this rule
            wpds.add_rule(WpdsRule::Replace {
                from_gamma: cat_entry.clone(),
                to_gamma: rule_entry.clone(),
                weight: w,
            });

            // Walk syntax items, creating transitions for each position.
            //
            // Same-category NTs use Replace (intraprocedural per Reps et al.
            // 2007). Only cross-category NTs use Push (interprocedural calls).
            // The Pratt LHS distinction is kept for documentation but all
            // same-cat NTs are Replace regardless.
            let mut pos: u32 = 0;
            let mut skipped_pratt_lhs = false;
            for (_idx, item) in rule_spec.syntax.iter().enumerate() {
                let current = StackSymbol::rule_position(cat, label, pos);
                wpds.ensure_symbol(current.clone());
                let next_pos = pos + 1;

                match item {
                    SyntaxItemSpec::Terminal(_) => {
                        // Intraprocedural: consume terminal (Replace)
                        let next = StackSymbol::rule_position(cat, label, next_pos);
                        wpds.ensure_symbol(next.clone());
                        wpds.add_rule(WpdsRule::Replace {
                            from_gamma: current,
                            to_gamma: next,
                            weight: W::one(),
                        });
                    },
                    SyntaxItemSpec::NonTerminal { category: ref nt_cat, .. } => {
                        let continuation = StackSymbol::rule_position(cat, label, next_pos);
                        wpds.ensure_symbol(continuation.clone());

                        if nt_cat == cat {
                            // Same-category recursion: Replace to continuation.
                            // Matches Reps et al. (2007) — intraprocedural transitions
                            // use Replace; only cross-category calls use Push.
                            if (rule_spec.is_infix || rule_spec.is_postfix) && !skipped_pratt_lhs {
                                skipped_pratt_lhs = true;
                            }
                            wpds.add_rule(WpdsRule::Replace {
                                from_gamma: current,
                                to_gamma: continuation,
                                weight: W::one(),
                            });
                        } else {
                            // Cross-category call: Push (callee entry on top, continuation on bottom)
                            let callee_entry = StackSymbol::category_entry(nt_cat);
                            wpds.ensure_symbol(callee_entry.clone());
                            wpds.add_rule(WpdsRule::Push {
                                from_gamma: current,
                                to_gamma_bottom: continuation,
                                to_gamma_top: callee_entry,
                                weight: W::one(),
                            });
                        }
                    },
                    SyntaxItemSpec::Binder { category: ref b_cat, .. } => {
                        if b_cat == cat {
                            let next = StackSymbol::rule_position(cat, label, next_pos);
                            wpds.ensure_symbol(next.clone());
                            wpds.add_rule(WpdsRule::Replace {
                                from_gamma: current,
                                to_gamma: next,
                                weight: W::one(),
                            });
                        } else {
                            let continuation = StackSymbol::rule_position(cat, label, next_pos);
                            let callee_entry = StackSymbol::category_entry(b_cat);
                            wpds.ensure_symbol(continuation.clone());
                            wpds.ensure_symbol(callee_entry.clone());
                            wpds.add_rule(WpdsRule::Push {
                                from_gamma: current,
                                to_gamma_bottom: continuation,
                                to_gamma_top: callee_entry,
                                weight: W::one(),
                            });
                        }
                    },
                    SyntaxItemSpec::Collection { element_category: ref e_cat, .. } => {
                        if e_cat == cat {
                            // Same-category collection: Replace (intraprocedural).
                            let next = StackSymbol::rule_position(cat, label, next_pos);
                            wpds.ensure_symbol(next.clone());
                            wpds.add_rule(WpdsRule::Replace {
                                from_gamma: current,
                                to_gamma: next,
                                weight: W::one(),
                            });
                        } else {
                            let continuation = StackSymbol::rule_position(cat, label, next_pos);
                            let callee_entry = StackSymbol::category_entry(e_cat);
                            wpds.ensure_symbol(continuation.clone());
                            wpds.ensure_symbol(callee_entry.clone());
                            wpds.add_rule(WpdsRule::Push {
                                from_gamma: current,
                                to_gamma_bottom: continuation,
                                to_gamma_top: callee_entry,
                                weight: W::one(),
                            });
                        }
                    },
                    SyntaxItemSpec::IdentCapture { .. }
                    | SyntaxItemSpec::TokenKindCapture { .. }
                    | SyntaxItemSpec::BinderCollection { .. } => {
                        // These consume a single token (ident / custom kind) —
                        // intraprocedural (Replace, one GSS position forward).
                        let next = StackSymbol::rule_position(cat, label, next_pos);
                        wpds.ensure_symbol(next.clone());
                        wpds.add_rule(WpdsRule::Replace {
                            from_gamma: current,
                            to_gamma: next,
                            weight: W::one(),
                        });
                    },
                    SyntaxItemSpec::Sep { body, .. } => {
                        // Separated list: model as single cross-category or replace
                        build_syntax_item_rules(&mut wpds, cat, label, &current, pos, body);
                        // After Sep, continue to next position
                        let next = StackSymbol::rule_position(cat, label, next_pos);
                        wpds.ensure_symbol(next.clone());
                        // The Sep body may loop, but we model a single traversal
                        wpds.add_rule(WpdsRule::Replace {
                            from_gamma: current,
                            to_gamma: next,
                            weight: W::one(),
                        });
                    },
                    SyntaxItemSpec::Map { .. } => {
                        // Structured body: summarize nested cross-category calls
                        // at this rule position, then continue to the next item.
                        let next = StackSymbol::rule_position(cat, label, next_pos);
                        wpds.ensure_symbol(next.clone());
                        for ref_cat in cross_category_refs(item, cat) {
                            let callee_entry = StackSymbol::category_entry(&ref_cat);
                            wpds.ensure_symbol(callee_entry.clone());
                            wpds.add_rule(WpdsRule::Push {
                                from_gamma: current.clone(),
                                to_gamma_bottom: next.clone(),
                                to_gamma_top: callee_entry,
                                weight: W::one(),
                            });
                        }
                        wpds.add_rule(WpdsRule::Replace {
                            from_gamma: current,
                            to_gamma: next,
                            weight: W::one(),
                        });
                    },
                    SyntaxItemSpec::Zip { .. } => {
                        // Dual-accumulator: model all nested cross-category calls
                        // without expanding the collection into extra WPDS states.
                        let continuation = StackSymbol::rule_position(cat, label, next_pos);
                        wpds.ensure_symbol(continuation.clone());

                        for ref_cat in cross_category_refs(item, cat) {
                            let callee_entry = StackSymbol::category_entry(&ref_cat);
                            wpds.ensure_symbol(callee_entry.clone());
                            wpds.add_rule(WpdsRule::Push {
                                from_gamma: current.clone(),
                                to_gamma_bottom: continuation.clone(),
                                to_gamma_top: callee_entry,
                                weight: W::one(),
                            });
                        }
                        // Also allow intraprocedural transition (same-category or completed)
                        wpds.add_rule(WpdsRule::Replace {
                            from_gamma: current,
                            to_gamma: continuation,
                            weight: W::one(),
                        });
                    },
                    SyntaxItemSpec::Optional { .. } => {
                        // Optional group: both skip and enter paths
                        let next = StackSymbol::rule_position(cat, label, next_pos);
                        wpds.ensure_symbol(next.clone());
                        // Skip path
                        wpds.add_rule(WpdsRule::Replace {
                            from_gamma: current.clone(),
                            to_gamma: next.clone(),
                            weight: W::one(),
                        });
                        // Enter path: model cross-category references inside optional
                        for ref_cat in cross_category_refs(item, cat) {
                            let callee_entry = StackSymbol::category_entry(&ref_cat);
                            wpds.ensure_symbol(callee_entry.clone());
                            wpds.add_rule(WpdsRule::Push {
                                from_gamma: current.clone(),
                                to_gamma_bottom: next.clone(),
                                to_gamma_top: callee_entry,
                                weight: W::one(),
                            });
                        }
                    },
                    SyntaxItemSpec::GuardExpression { .. } => {
                        // Phase 2F: guard expressions are self-contained
                        // (consumed by the predicate sublanguage parser).
                        // From the WPDS perspective this is an intraprocedural
                        // Replace — no cross-category call.
                        let next = StackSymbol::rule_position(cat, label, next_pos);
                        wpds.ensure_symbol(next.clone());
                        wpds.add_rule(WpdsRule::Replace {
                            from_gamma: current,
                            to_gamma: next,
                            weight: W::one(),
                        });
                    },
                }
                pos = next_pos;
            }

            // Rule completion: Pop (return to caller)
            let final_pos = StackSymbol::rule_position(cat, label, pos);
            wpds.ensure_symbol(final_pos.clone());
            wpds.add_rule(WpdsRule::Pop { from_gamma: final_pos, weight: W::one() });
        }
    }

    // Ensure every category can complete in poststar. Categories with zero
    // parsing rules (e.g., Ambient's Name) need a synthetic Pop from their
    // entry point so that Push/Pop cycles through those categories can
    // complete. Without this, continuation positions after cross-category
    // calls to empty categories are unreachable in the P-automaton, causing
    // false-positive dead frame elimination.
    for cat_spec in &spec.types {
        let cat = &cat_spec.name;
        let has_rules = rules_by_category
            .get(cat.as_str())
            .map_or(false, |rules| !rules.is_empty());
        if !has_rules {
            let cat_entry = StackSymbol::category_entry(cat);
            wpds.ensure_symbol(cat_entry.clone());
            wpds.add_rule(WpdsRule::Pop { from_gamma: cat_entry, weight: W::one() });
        }
    }

    wpds
}

/// Collect cross-category references from a syntax item, including nested
/// Sep/Map/Zip/Optional bodies summarized at the enclosing WPDS position.
fn collect_cross_category_refs(
    item: &SyntaxItemSpec,
    current_cat: &str,
    refs: &mut HashSet<String>,
) {
    for item in crate::syntax_item::preorder(std::slice::from_ref(item)) {
        match item {
            SyntaxItemSpec::NonTerminal { category, .. }
            | SyntaxItemSpec::Binder { category, .. } => {
                if category != current_cat {
                    refs.insert(category.clone());
                }
            },
            SyntaxItemSpec::Collection { element_category, .. } => {
                if element_category != current_cat {
                    refs.insert(element_category.clone());
                }
            },
            SyntaxItemSpec::Zip { left_category, right_category, .. } => {
                if left_category != current_cat {
                    refs.insert(left_category.clone());
                }
                if right_category != current_cat {
                    refs.insert(right_category.clone());
                }
            },
            SyntaxItemSpec::Terminal(_)
            | SyntaxItemSpec::IdentCapture { .. }
            | SyntaxItemSpec::TokenKindCapture { .. }
            | SyntaxItemSpec::BinderCollection { .. }
            | SyntaxItemSpec::GuardExpression { .. }
            | SyntaxItemSpec::Sep { .. }
            | SyntaxItemSpec::Map { .. }
            | SyntaxItemSpec::Optional { .. } => {},
        }
    }
}

fn cross_category_refs(item: &SyntaxItemSpec, current_cat: &str) -> Vec<String> {
    let mut refs = HashSet::new();
    collect_cross_category_refs(item, current_cat, &mut refs);
    let mut refs: Vec<String> = refs.into_iter().collect();
    refs.sort();
    refs
}

/// Build WPDS rules for a nested syntax item (e.g., Sep body).
fn build_syntax_item_rules<W: Semiring>(
    wpds: &mut Wpds<W>,
    cat: &str,
    label: &str,
    current: &StackSymbol,
    pos: u32,
    item: &SyntaxItemSpec,
) {
    for ref_cat in cross_category_refs(item, cat) {
        let continuation = StackSymbol::rule_position(cat, label, pos + 1);
        let callee_entry = StackSymbol::category_entry(&ref_cat);
        wpds.ensure_symbol(continuation.clone());
        wpds.ensure_symbol(callee_entry.clone());
        wpds.add_rule(WpdsRule::Push {
            from_gamma: current.clone(),
            to_gamma_bottom: continuation,
            to_gamma_top: callee_entry,
            weight: W::one(),
        });
    }
}
