use super::*;

// ══════════════════════════════════════════════════════════════════════════════
// poststar: Forward reachability saturation (Reps et al. 2007)
// ══════════════════════════════════════════════════════════════════════════════

/// Compute poststar (forward reachability) for a WPDS.
///
/// Given an initial P-automaton `A₀` encoding the start configuration
/// `⟨p, γ₀⟩`, computes `A_post*` — the weighted P-automaton accepting
/// all configurations reachable from A₀ with MOVP weights.
///
/// **Algorithm** (Reps et al. 2007, Figure 3):
/// For each PDS rule `r: ⟨p, γ⟩ ↪ ⟨p', u⟩` with weight `f(r)`:
///
/// - Pop (`|u|=0`): If `(p, γ, q)` in A with weight w, add nothing (config accepted)
/// - Replace (`|u|=1`): If `(p, γ, q)` with w, add `(p', γ', q)` with `f(r) ⊗ w`
/// - Push (`|u|=2`): If `(p, γ, q)` with w, add fresh state `q_r`,
///   add `(p', γ', q_r)` with `f(r)` and `(q_r, γ'', q)` with `w`
///
/// Saturation terminates when no new transitions can be added. For bounded
/// idempotent semirings, this converges in finite steps.
///
/// **Complexity:** O_s(|P||Δ|(|Q₀|+|Δ|)H) where H = weight domain height.
pub fn poststar<W: Semiring>(wpds: &Wpds<W>) -> PAutomaton<W> {
    // Initial P-automaton: state p (=0), transition (p, γ₀, q_f) with weight one()
    let p_state: PAutomatonStateId = 0;
    let mut automaton = PAutomaton::new(p_state);
    let q_final = automaton.add_state();
    automaton.mark_final(q_final);

    // Initial transition: (p, initial_symbol, q_final) with weight one()
    automaton.add_transition(p_state, wpds.initial_symbol.clone(), q_final, W::one());
    automaton
        .symbol_to_state
        .insert(wpds.initial_symbol.clone(), q_final);

    // Worklist of transitions to process: (from, symbol, to, weight)
    let mut worklist: VecDeque<(PAutomatonStateId, StackSymbol, PAutomatonStateId, W)> =
        VecDeque::new();
    worklist.push_back((p_state, wpds.initial_symbol.clone(), q_final, W::one()));

    // Track existing transitions for convergence: (from, symbol, to) → weight
    let mut existing: HashMap<(PAutomatonStateId, StackSymbol, PAutomatonStateId), W> =
        HashMap::new();
    existing.insert((p_state, wpds.initial_symbol.clone(), q_final), W::one());

    // Fresh state allocation for push rules: from_gamma → fresh_state
    let mut push_states: HashMap<StackSymbol, PAutomatonStateId> = HashMap::new();

    // Track intermediate states reached via Pop. When Pop fires from
    // (p, γ, q_r) where q_r is an intermediate state created by Push,
    // q_r's outgoing transitions must be propagated to p_state so that
    // continuation symbols (the "bottom" of Push rules) become reachable.
    let mut pop_reached: HashSet<PAutomatonStateId> = HashSet::new();

    // Saturation loop
    while let Some((_from, gamma, to, w)) = worklist.pop_front() {
        // Find all rules with source gamma
        let rule_indices: Vec<usize> = wpds.rules_for(&gamma).to_vec();

        for rule_idx in rule_indices {
            let rule = &wpds.rules[rule_idx];

            match rule {
                WpdsRule::Pop { weight: w_r, .. } => {
                    // Pop: ⟨p, γ⟩ → ⟨p', ε⟩
                    // When `to` is an intermediate state (created by a Push rule),
                    // propagate its outgoing transitions to p_state. This makes
                    // continuation symbols from nested Push rules reachable.
                    pop_reached.insert(to);
                    let pop_weight = w_r.times(&w);

                    let outgoing: Vec<(StackSymbol, PAutomatonStateId, W)> = automaton
                        .transitions_by_source
                        .get(&to)
                        .map(|indices| {
                            indices
                                .iter()
                                .map(|&idx| {
                                    let t = &automaton.transitions[idx];
                                    (t.symbol.clone(), t.to, t.weight)
                                })
                                .collect()
                        })
                        .unwrap_or_default();

                    for (sym, target, w_b) in outgoing {
                        let prop_weight = pop_weight.times(&w_b);
                        let key = (p_state, sym.clone(), target);

                        let should_add = match existing.get(&key) {
                            Some(old_w) => {
                                let combined = old_w.plus(&prop_weight);
                                if !combined.approx_eq(old_w, 1e-10) {
                                    existing.insert(key.clone(), combined);
                                    true
                                } else {
                                    false
                                }
                            },
                            None => {
                                existing.insert(key.clone(), prop_weight);
                                true
                            },
                        };

                        if should_add {
                            let combined = existing.get(&key).expect("just inserted").clone();
                            automaton.add_transition(p_state, sym.clone(), target, combined);
                            automaton
                                .symbol_to_state
                                .entry(sym.clone())
                                .or_insert(target);
                            worklist.push_back((p_state, sym, target, combined));
                        }
                    }
                },
                WpdsRule::Replace { to_gamma, weight, .. } => {
                    // Replace: ⟨p, γ⟩ → ⟨p', γ'⟩
                    // Add transition (p, γ', to) with weight f(r) ⊗ w
                    let new_weight = weight.times(&w);
                    let key = (p_state, to_gamma.clone(), to);

                    let should_add = match existing.get(&key) {
                        Some(old_w) => {
                            let combined = old_w.plus(&new_weight);
                            if !combined.approx_eq(old_w, 1e-10) {
                                existing.insert(key.clone(), combined);
                                true
                            } else {
                                false
                            }
                        },
                        None => {
                            existing.insert(key.clone(), new_weight);
                            true
                        },
                    };

                    if should_add {
                        let combined = existing.get(&key).expect("just inserted").clone();
                        automaton.add_transition(p_state, to_gamma.clone(), to, combined);
                        automaton
                            .symbol_to_state
                            .entry(to_gamma.clone())
                            .or_insert(to);
                        worklist.push_back((p_state, to_gamma.clone(), to, combined));
                    }
                },
                WpdsRule::Push {
                    to_gamma_bottom, to_gamma_top, weight, ..
                } => {
                    // Push: ⟨p, γ⟩ → ⟨p', γ_bottom γ_top⟩
                    // Need: (p, γ_top, q_r) and (q_r, γ_bottom, to)
                    // where q_r is a fresh state for this push rule's source
                    let q_r = *push_states
                        .entry(gamma.clone())
                        .or_insert_with(|| automaton.add_state());

                    // Add (q_r, γ_bottom, to) with weight w
                    let bottom_key = (q_r, to_gamma_bottom.clone(), to);
                    let bottom_new = match existing.get(&bottom_key) {
                        Some(old_w) => {
                            let combined = old_w.plus(&w);
                            if !combined.approx_eq(old_w, 1e-10) {
                                existing.insert(bottom_key.clone(), combined);
                                true
                            } else {
                                false
                            }
                        },
                        None => {
                            existing.insert(bottom_key.clone(), w.clone());
                            true
                        },
                    };

                    if bottom_new {
                        let bw = existing.get(&bottom_key).expect("just inserted").clone();
                        automaton.add_transition(q_r, to_gamma_bottom.clone(), to, bw);

                        // If q_r has been Pop-reached, propagate this new bottom
                        // transition to p_state immediately so continuation symbols
                        // from nested Push rules become reachable.
                        if pop_reached.contains(&q_r) {
                            let prop_key = (p_state, to_gamma_bottom.clone(), to);
                            let should_prop = match existing.get(&prop_key) {
                                Some(old_w) => {
                                    let combined = old_w.plus(&bw);
                                    if !combined.approx_eq(old_w, 1e-10) {
                                        existing.insert(prop_key.clone(), combined);
                                        true
                                    } else {
                                        false
                                    }
                                },
                                None => {
                                    existing.insert(prop_key.clone(), bw.clone());
                                    true
                                },
                            };
                            if should_prop {
                                let pw = existing.get(&prop_key).expect("just inserted").clone();
                                automaton.add_transition(p_state, to_gamma_bottom.clone(), to, pw);
                                automaton
                                    .symbol_to_state
                                    .entry(to_gamma_bottom.clone())
                                    .or_insert(to);
                                worklist.push_back((p_state, to_gamma_bottom.clone(), to, pw));
                            }
                        }
                    }

                    // Add (p, γ_top, q_r) with weight f(r)
                    let top_key = (p_state, to_gamma_top.clone(), q_r);
                    let top_new = match existing.get(&top_key) {
                        Some(old_w) => {
                            let combined = old_w.plus(weight);
                            if !combined.approx_eq(old_w, 1e-10) {
                                existing.insert(top_key.clone(), combined);
                                true
                            } else {
                                false
                            }
                        },
                        None => {
                            existing.insert(top_key.clone(), *weight);
                            true
                        },
                    };

                    if top_new {
                        let tw = existing.get(&top_key).expect("just inserted").clone();
                        automaton.add_transition(p_state, to_gamma_top.clone(), q_r, tw);
                        automaton
                            .symbol_to_state
                            .entry(to_gamma_top.clone())
                            .or_insert(q_r);
                        worklist.push_back((p_state, to_gamma_top.clone(), q_r, tw));
                    }
                },
            }
        }
    }

    automaton
}

/// Compute prestar (backward reachability) for a WPDS.
///
/// Given a target P-automaton encoding configurations we want to reach,
/// computes `A_pre*` — the weighted P-automaton accepting all configurations
/// from which the target is reachable.
///
/// **Algorithm** (Reps et al. 2007, Figure 2):
/// For each PDS rule `r: ⟨p, γ⟩ ↪ ⟨p', u⟩` with weight `f(r)`:
///
/// - Pop (`|u|=0`): Add `(p, γ, p')` with `f(r)`
/// - Replace (`|u|=1`): If `(p', γ', q)` with w, add `(p, γ, q)` with `f(r) ⊗ w`
/// - Push (`|u|=2`): If `(p', γ', q')` with w₁ and `(q', γ'', q)` with w₂,
///   add `(p, γ, q)` with `f(r) ⊗ w₁ ⊗ w₂`
pub fn prestar<W: Semiring>(wpds: &Wpds<W>, target: &PAutomaton<W>) -> PAutomaton<W> {
    let p_state: PAutomatonStateId = 0;
    let mut automaton = target.clone();

    // Worklist: process transitions until convergence
    let mut worklist: VecDeque<(PAutomatonStateId, StackSymbol, PAutomatonStateId, W)> =
        VecDeque::new();

    let mut existing: HashMap<(PAutomatonStateId, StackSymbol, PAutomatonStateId), W> =
        HashMap::new();
    for trans in &automaton.transitions {
        let key = (trans.from, trans.symbol.clone(), trans.to);
        let entry = existing.entry(key).or_insert(W::zero());
        *entry = entry.plus(&trans.weight);
    }

    // Phase 1: Initialize pop rules (processed once, not per-worklist-item).
    // Pop rule ⟨p, γ⟩ → ⟨p', ε⟩ means: if at state p with γ on stack, transition
    // to p' with empty stack. In prestar terms: add (p, γ, p') unconditionally.
    for rule in &wpds.rules {
        if let WpdsRule::Pop { from_gamma, weight } = rule {
            let key = (p_state, from_gamma.clone(), p_state);
            let new_weight = *weight;
            let changed = match existing.get(&key) {
                Some(old_w) => {
                    let combined = old_w.plus(&new_weight);
                    if !combined.approx_eq(old_w, 1e-10) {
                        existing.insert(key.clone(), combined);
                        true
                    } else {
                        false
                    }
                },
                None => {
                    existing.insert(key.clone(), new_weight);
                    true
                },
            };
            if changed {
                let cw = *existing.get(&key).expect("just inserted");
                automaton.add_transition(p_state, from_gamma.clone(), p_state, cw);
                worklist.push_back((p_state, from_gamma.clone(), p_state, cw));
            }
        }
    }

    // Also seed worklist with all existing target transitions (after pop init,
    // so replace/push rules can chain off both target and pop transitions).
    for trans in &target.transitions {
        worklist.push_back((trans.from, trans.symbol.clone(), trans.to, trans.weight));
    }

    // Phase 2: Worklist saturation for replace and push rules only.
    // When we dequeue transition (from, gamma, to), we check replace/push rules
    // whose RHS produces gamma.
    while let Some((_from, gamma, _to, _w)) = worklist.pop_front() {
        for rule in &wpds.rules {
            match rule {
                WpdsRule::Pop { .. } => {
                    // Pop rules are already handled in Phase 1.
                },
                WpdsRule::Replace { from_gamma, to_gamma, weight } => {
                    // Replace: ⟨p, from_gamma⟩ → ⟨p', to_gamma⟩
                    // If (p', to_gamma, q) exists, add (p, from_gamma, q) with f(r) ⊗ w
                    if *to_gamma == gamma {
                        // Find all transitions (p_state, to_gamma, q)
                        let targets: Vec<(PAutomatonStateId, W)> = existing
                            .iter()
                            .filter(|((f, s, _), _)| *f == p_state && *s == *to_gamma)
                            .map(|((_, _, t), w)| (*t, *w))
                            .collect();

                        for (q, w) in targets {
                            let new_weight = weight.times(&w);
                            let key = (p_state, from_gamma.clone(), q);
                            let should_add = match existing.get(&key) {
                                Some(old_w) => {
                                    let combined = old_w.plus(&new_weight);
                                    if !combined.approx_eq(old_w, 1e-10) {
                                        existing.insert(key.clone(), combined);
                                        true
                                    } else {
                                        false
                                    }
                                },
                                None => {
                                    existing.insert(key.clone(), new_weight);
                                    true
                                },
                            };
                            if should_add {
                                let cw = *existing.get(&key).expect("just inserted");
                                automaton.add_transition(p_state, from_gamma.clone(), q, cw);
                                worklist.push_back((p_state, from_gamma.clone(), q, cw));
                            }
                        }
                    }
                },
                WpdsRule::Push {
                    from_gamma,
                    to_gamma_bottom,
                    to_gamma_top,
                    weight,
                } => {
                    // Push: ⟨p, from_gamma⟩ → ⟨p', γ_bottom γ_top⟩
                    // If (p', γ_top, q') and (q', γ_bottom, q) exist,
                    // add (p, from_gamma, q) with f(r) ⊗ w₁ ⊗ w₂
                    if *to_gamma_top == gamma || *to_gamma_bottom == gamma {
                        // Find (p_state, γ_top, q')
                        let top_targets: Vec<(PAutomatonStateId, W)> = existing
                            .iter()
                            .filter(|((f, s, _), _)| *f == p_state && *s == *to_gamma_top)
                            .map(|((_, _, t), w)| (*t, *w))
                            .collect();

                        for (q_prime, w1) in &top_targets {
                            // Find (q', γ_bottom, q)
                            let bottom_targets: Vec<(PAutomatonStateId, W)> = existing
                                .iter()
                                .filter(|((f, s, _), _)| *f == *q_prime && *s == *to_gamma_bottom)
                                .map(|((_, _, t), w)| (*t, *w))
                                .collect();

                            for (q, w2) in bottom_targets {
                                let new_weight = weight.times(w1).times(&w2);
                                let key = (p_state, from_gamma.clone(), q);
                                let should_add = match existing.get(&key) {
                                    Some(old_w) => {
                                        let combined = old_w.plus(&new_weight);
                                        if !combined.approx_eq(old_w, 1e-10) {
                                            existing.insert(key.clone(), combined);
                                            true
                                        } else {
                                            false
                                        }
                                    },
                                    None => {
                                        existing.insert(key.clone(), new_weight);
                                        true
                                    },
                                };
                                if should_add {
                                    let cw = *existing.get(&key).expect("just inserted");
                                    automaton.add_transition(p_state, from_gamma.clone(), q, cw);
                                    worklist.push_back((p_state, from_gamma.clone(), q, cw));
                                }
                            }
                        }
                    }
                },
            }
        }
    }

    automaton
}

// ══════════════════════════════════════════════════════════════════════════════
// Stringsum: Butoi et al. (2022) per-input ambiguity analysis
// ══════════════════════════════════════════════════════════════════════════════

/// Token representation for stringsum computation.
///
/// Maps PraTTaIL terminal tokens to indices for the DP tables.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct StringsumInput {
    /// Token sequence as terminal strings.
    pub tokens: Vec<String>,
}

/// Result of stringsum computation for a single input.
#[derive(Debug, Clone)]
pub struct StringsumResult<W: Semiring> {
    /// The input that was analyzed.
    pub input: StringsumInput,
    /// Total weight of all accepting runs (parse derivations).
    pub total_weight: W,
    /// Per-position weights (weight of all runs at each input position).
    pub position_weights: Vec<W>,
}

/// Compute stringsum over a WPDS for a given input string.
///
/// This implements a simplified version of Butoi et al. (2022) stringsum
/// adapted for PraTTaIL's grammar structure. Rather than the full O(n³|Q|³|Γ|³)
/// algorithm, we exploit PraTTaIL's deterministic dispatch to reduce to
/// a poststar-based computation:
///
/// 1. Build poststar P-automaton from the WPDS
/// 2. For each token in the input, find matching rules and accumulate weights
/// 3. The total weight is the product of per-position weights
///
/// For ambiguity detection, use `CountingWeight`: if result > 1, the input
/// has multiple parse derivations.
pub fn stringsum<W: Semiring>(
    _wpds: &Wpds<W>,
    post_automaton: &PAutomaton<W>,
    input: &StringsumInput,
    spec: &LanguageSpec,
) -> StringsumResult<W> {
    // For each token in the input, find which rules can consume it
    // and accumulate the total weight across all possible parse paths.
    //
    // This is a simplified approach that leverages the poststar P-automaton
    // to determine reachable rules at each position.

    let mut position_weights = Vec::with_capacity(input.tokens.len());
    let mut total = W::one();

    // Group rules by their first terminal
    let mut rules_by_first_terminal: HashMap<&str, Vec<(&str, &str, W)>> = HashMap::new();
    for rule in &spec.rules {
        if let Some(SyntaxItemSpec::Terminal(ref tok)) = rule.syntax.first() {
            let sym = StackSymbol::category_entry(&rule.category);
            // Liveness of the category entry anywhere on a reachable stack — a
            // called category is PUSHED, so it is not a one-symbol configuration.
            let sym_weight = post_automaton.stack_top_weight(&sym);
            if !sym_weight.is_zero() {
                rules_by_first_terminal
                    .entry(tok.as_str())
                    .or_default()
                    .push((&rule.category, &rule.label, sym_weight));
            }
        }
    }

    for token in &input.tokens {
        let mut pos_weight = W::zero();

        // Find all rules that could consume this token
        if let Some(matching_rules) = rules_by_first_terminal.get(token.as_str()) {
            for (_cat, _label, w) in matching_rules {
                pos_weight = pos_weight.plus(w);
            }
        }

        // Also check non-terminal starts (ident, integer, etc.)
        for rule in &spec.rules {
            if rule.is_var || rule.is_literal {
                let sym = StackSymbol::category_entry(&rule.category);
                // Liveness (see above): pushed category entries are stack tops.
                let sym_weight = post_automaton.stack_top_weight(&sym);
                if !sym_weight.is_zero() {
                    // Check if this token could match a variable/literal pattern
                    let matches = match token.as_str() {
                        t if t.chars().all(|c| c.is_ascii_digit()) && rule.is_literal => true,
                        t if t.starts_with('"') && rule.is_literal => true,
                        t if t
                            .chars()
                            .next()
                            .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
                            && rule.is_var =>
                        {
                            true
                        },
                        _ => false,
                    };
                    if matches {
                        pos_weight = pos_weight.plus(&sym_weight);
                    }
                }
            }
        }

        // If no rule matches, this position has zero weight (parse fails)
        if pos_weight.is_zero() {
            pos_weight = W::zero();
        }

        total = total.times(&pos_weight);
        position_weights.push(pos_weight);
    }

    StringsumResult {
        input: input.clone(),
        total_weight: total,
        position_weights,
    }
}
