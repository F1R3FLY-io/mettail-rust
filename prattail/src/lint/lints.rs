use super::*;

impl DiagnosticId {
    /// True if this is a runtime (RT) diagnostic.
    #[inline]
    pub const fn is_runtime(&self) -> bool {
        matches!(
            self,
            DiagnosticId::RT01
                | DiagnosticId::RT02
                | DiagnosticId::RT03
                | DiagnosticId::RT04
                | DiagnosticId::RT05
                | DiagnosticId::RT06
                | DiagnosticId::RT07
        )
    }

    /// True if this diagnostic ID is groupable by [`group_diagnostics`].
    ///
    /// Must cover every ID with a dedicated grouper arm in the match at
    /// `group_diagnostics` — otherwise groupable diagnostics leak through
    /// the `non_groupable` path and the per-ID grouper is never called.
    #[inline]
    pub const fn is_groupable(&self) -> bool {
        matches!(
            self,
            DiagnosticId::W01  | DiagnosticId::W02  | DiagnosticId::W03  |
            DiagnosticId::W05  | DiagnosticId::W07  |
            DiagnosticId::W12  |
            DiagnosticId::G03  | DiagnosticId::G08  | DiagnosticId::G27  |
            DiagnosticId::D01  | DiagnosticId::D02  | DiagnosticId::D03  |
            DiagnosticId::D08  | DiagnosticId::D09  |
            DiagnosticId::A01  | DiagnosticId::A04  | DiagnosticId::A08  |
            DiagnosticId::CAP03 | DiagnosticId::CAP05 |
            DiagnosticId::DIS01 |
            // Lint-B cleanup: high-volume IDs that produce many
            // near-identical duplicates in unconfigured languages.
            DiagnosticId::M01  | DiagnosticId::K01  |
            DiagnosticId::SYM02 |
            DiagnosticId::N02  | DiagnosticId::N05
        )
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G01: Left Recursion (migrated from prediction.rs)
// ══════════════════════════════════════════════════════════════════════════════

pub(crate) fn lint_g01_left_recursion(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    for (label, category, syntax) in ctx.all_syntax {
        if let Some(SyntaxItemSpec::NonTerminal { category: ref first_cat, .. }) = syntax.first() {
            if first_cat == category {
                // Skip infix, postfix, mixfix — handled by Pratt
                let terminal_count = syntax
                    .iter()
                    .filter(|i| matches!(i, SyntaxItemSpec::Terminal(_)))
                    .count();
                let nt_count = syntax
                    .iter()
                    .filter(|i| matches!(i, SyntaxItemSpec::NonTerminal { .. }))
                    .count();

                let is_infix_pattern = nt_count == 2
                    && terminal_count >= 1
                    && syntax.len() >= 3
                    && matches!(
                        syntax.last(),
                        Some(SyntaxItemSpec::NonTerminal { category: ref last_cat, .. })
                        if last_cat == category
                    );
                let is_postfix_pattern = nt_count == 1 && terminal_count == 1 && syntax.len() == 2;
                let is_mixfix_pattern = nt_count >= 3 && terminal_count >= 2;

                if !is_infix_pattern && !is_postfix_pattern && !is_mixfix_pattern {
                    diagnostics.push(LintDiagnostic {
                        id: DiagnosticId::G01,
                        name: "left-recursion",
                        severity: LintSeverity::Warning,
                        category: Some(category.clone()),
                        rule: Some(label.clone()),
                        message: format!(
                            "left-recursive rule `{}` in category `{}` \
                             (first item is NonTerminal of same category)",
                            label, category,
                        ),
                        hint: Some(
                            "convert to infix/postfix pattern for Pratt handling, \
                             or restructure to avoid same-category leading NonTerminal"
                                .to_string(),
                        ),
                        grammar_name: Some(ctx.grammar_name.to_string()),
                        source_location: ctx
                            .rule_locations
                            .get(&(label.clone(), category.clone()))
                            .copied(),
                    });
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G02: Unused Category (migrated from prediction.rs)
// ══════════════════════════════════════════════════════════════════════════════

pub(crate) fn lint_g02_unused_category(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let mut referenced: HashSet<String> = HashSet::new();

    for (_, _, syntax) in ctx.all_syntax {
        collect_referenced_categories(syntax, &mut referenced);
    }

    // Categories with rules targeting them are "used"
    for (_, category, _) in ctx.all_syntax {
        referenced.insert(category.clone());
    }

    let category_names: Vec<&str> = ctx.categories.iter().map(|c| c.name.as_str()).collect();
    for cat_name in &category_names {
        if !referenced.contains(*cat_name) {
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::G02,
                name: "unused-category",
                severity: LintSeverity::Warning,
                category: Some(cat_name.to_string()),
                rule: None,
                message: format!(
                    "category `{}` declared but never referenced in any rule syntax",
                    cat_name,
                ),
                hint: Some("remove the unused category or add rules that reference it".to_string()),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

/// Recursively collect all category names referenced in syntax items.
fn collect_referenced_categories(items: &[SyntaxItemSpec], referenced: &mut HashSet<String>) {
    for item in items {
        match item {
            SyntaxItemSpec::NonTerminal { category, .. } => {
                referenced.insert(category.clone());
            },
            SyntaxItemSpec::Collection { element_category, .. } => {
                referenced.insert(element_category.clone());
            },
            SyntaxItemSpec::Sep { body, .. } => {
                collect_referenced_categories(std::slice::from_ref(body.as_ref()), referenced);
            },
            SyntaxItemSpec::Map { body_items } => {
                collect_referenced_categories(body_items, referenced);
            },
            SyntaxItemSpec::Zip { left_category, right_category, body, .. } => {
                referenced.insert(left_category.clone());
                referenced.insert(right_category.clone());
                collect_referenced_categories(std::slice::from_ref(body.as_ref()), referenced);
            },
            SyntaxItemSpec::Optional { inner } => {
                collect_referenced_categories(inner, referenced);
            },
            SyntaxItemSpec::Binder { category, .. } => {
                referenced.insert(category.clone());
            },
            _ => {},
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G03: Ambiguous Prefix (migrated from prediction.rs)
// ══════════════════════════════════════════════════════════════════════════════

pub(crate) fn lint_g03_ambiguous_prefix(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    use crate::prediction::FirstItem;

    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        // Collect non-infix, non-var, non-literal rules for this category
        let prefix_rules: Vec<&RuleInfo> = ctx
            .rules
            .iter()
            .filter(|r| r.category == *cat && !r.is_infix && !r.is_var && !r.is_literal)
            .collect();

        let mut terminal_to_rules: HashMap<String, Vec<String>> = HashMap::new();

        for rule in &prefix_rules {
            for item in &rule.first_items {
                if let FirstItem::Terminal(t) = item {
                    terminal_to_rules
                        .entry(t.clone())
                        .or_default()
                        .push(rule.label.clone());
                }
            }
        }

        for (token, rule_labels) in &terminal_to_rules {
            if rule_labels.len() > 1 {
                // Classify root cause via decision tree if available
                let root_cause = classify_ambiguity_root_cause(ctx, cat, token);

                let message = if let Some(cause) = &root_cause {
                    format!(
                        "ambiguous prefix on `{}` in category `{}`: rules [{}] — {}",
                        token,
                        cat,
                        rule_labels.join(", "),
                        cause,
                    )
                } else {
                    format!(
                        "ambiguous prefix dispatch for token `{}` in category `{}`: \
                         rules [{}] all match",
                        token,
                        cat,
                        rule_labels.join(", "),
                    )
                };

                diagnostics.push(LintDiagnostic {
                    id: DiagnosticId::G03,
                    name: "ambiguous-prefix",
                    severity: LintSeverity::Warning,
                    category: Some(cat.clone()),
                    rule: None,
                    message,
                    hint: Some(
                        "add unique dispatch tokens to disambiguate; \
                         WFST auto-assigns weights by declaration order when prefixes overlap"
                            .to_string(),
                    ),
                    grammar_name: Some(ctx.grammar_name.to_string()),
                    source_location: None,
                });
            }
        }
    }
}

/// Classify the root cause of a G03 ambiguity using the decision tree.
///
/// Returns a human-readable classification:
/// - FIRST token clash (branch at byte 0)
/// - Shared terminal prefix diverging at suffix (branch at byte N>0)
/// - Nonterminal boundary
/// - Cross-category overlap (cast collision)
fn classify_ambiguity_root_cause(ctx: &LintContext, category: &str, token: &str) -> Option<String> {
    let tree = ctx.decision_trees.get(category)?;
    let strategy = tree.dispatch_strategy(token, ctx.token_id_map);

    match strategy {
        crate::decision_tree::DispatchStrategy::AmbiguousFanout {
            rule_labels,
            shared_prefix_len,
            shared_terminals,
            ..
        } => {
            if shared_prefix_len == 0 && shared_terminals.is_empty() {
                // Branch at byte 0 — FIRST token clash
                Some(format!(
                    "FIRST token clash: {} rules share dispatch token with no distinguishing prefix",
                    rule_labels.len()
                ))
            } else {
                // Check if any shared byte is an NT boundary marker
                let has_nt_boundary = shared_terminals.iter().any(|&b| b >= 0x82 && b < 0xC0);
                let has_optional = shared_terminals.iter().any(|&b| b == 0xC0 || b == 0xC1);

                if has_nt_boundary {
                    Some(format!(
                        "nonterminal boundary divergence after {}-token shared prefix",
                        shared_prefix_len
                    ))
                } else if has_optional {
                    Some(format!(
                        "optional group nesting divergence after {}-token shared prefix",
                        shared_prefix_len
                    ))
                } else {
                    // Shared terminal prefix diverging at suffix
                    let shared_names: Vec<String> = shared_terminals
                        .iter()
                        .filter_map(|&b| {
                            ctx.token_id_map.name(b as u16).map(|n| format!("`{}`", n))
                        })
                        .collect();
                    if shared_names.is_empty() {
                        Some(format!(
                            "shared {}-token prefix diverges at suffix",
                            shared_prefix_len
                        ))
                    } else {
                        Some(format!(
                            "shared prefix [{}] ({} tokens) diverges at suffix",
                            shared_names.join(" "),
                            shared_prefix_len
                        ))
                    }
                }
            }
        },
        crate::decision_tree::DispatchStrategy::DisjointSuffix { .. } => {
            // Disjoint suffix = resolved, not actually ambiguous at runtime
            Some("resolved by disjoint suffix dispatch (no runtime ambiguity)".to_string())
        },
        _ => None,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G04: Duplicate Rule Label
// ══════════════════════════════════════════════════════════════════════════════

pub(crate) fn lint_g04_duplicate_rule_label(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let mut seen: HashMap<(&str, &str), &str> = HashMap::new();
    for (label, category, _) in ctx.all_syntax {
        let key = (category.as_str(), label.as_str());
        if let Some(&_existing) = seen.get(&key) {
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::G04,
                name: "duplicate-rule-label",
                severity: LintSeverity::Error,
                category: Some(category.clone()),
                rule: Some(label.clone()),
                message: format!(
                    "duplicate rule label `{}` in category `{}` — codegen will produce \
                     conflicting constructor names",
                    label, category,
                ),
                hint: Some("rename one of the rules to a unique label".to_string()),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: ctx
                    .rule_locations
                    .get(&(label.clone(), category.clone()))
                    .copied(),
            });
        } else {
            seen.insert(key, label.as_str());
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G05: Empty Category
// ══════════════════════════════════════════════════════════════════════════════

fn collect_binding_sort_categories(item: &SyntaxItemSpec, out: &mut HashSet<String>) {
    match item {
        SyntaxItemSpec::Binder { category, .. } => {
            out.insert(category.clone());
        },
        SyntaxItemSpec::Sep { body, .. } => collect_binding_sort_categories(body, out),
        SyntaxItemSpec::Map { body_items } => {
            for item in body_items {
                collect_binding_sort_categories(item, out);
            }
        },
        SyntaxItemSpec::Zip { left_category, right_category, body, .. } => {
            out.insert(left_category.clone());
            out.insert(right_category.clone());
            collect_binding_sort_categories(body, out);
        },
        SyntaxItemSpec::Optional { inner } => {
            for item in inner {
                collect_binding_sort_categories(item, out);
            }
        },
        SyntaxItemSpec::Terminal(_)
        | SyntaxItemSpec::NonTerminal { .. }
        | SyntaxItemSpec::IdentCapture { .. }
        | SyntaxItemSpec::BinderCollection { .. }
        | SyntaxItemSpec::Collection { .. }
        | SyntaxItemSpec::GuardExpression { .. } => {},
    }
}

fn binding_sort_categories(ctx: &LintContext) -> HashSet<String> {
    let mut categories = HashSet::new();
    for (_, _, syntax) in ctx.all_syntax {
        for item in syntax {
            collect_binding_sort_categories(item, &mut categories);
        }
    }
    categories
}

pub(crate) fn lint_g05_empty_category(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let binding_sorts = binding_sort_categories(ctx);
    for cat in ctx.categories.iter() {
        // Native-type categories (e.g., ![i64] as Int) are parsed via auto-generated
        // Pratt prefix match arms — they don't need explicit grammar rules.
        if cat.native_type.is_some() {
            continue;
        }
        if binding_sorts.contains(&cat.name) {
            continue;
        }
        let has_rules = ctx
            .all_syntax
            .iter()
            .any(|(_, category, _)| category.as_str() == cat.name);
        if !has_rules {
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::G05,
                name: "empty-category",
                severity: LintSeverity::Warning,
                category: Some(cat.name.clone()),
                rule: None,
                message: format!("category `{}` has zero rules — cannot be parsed", cat.name,),
                hint: Some("add at least one rule or remove the category declaration".to_string()),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G06: Shadowed Operator
// ══════════════════════════════════════════════════════════════════════════════

pub(crate) fn lint_g06_shadowed_operator(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    use crate::prediction::FirstItem;

    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        // Collect terminals from infix rules
        let infix_terminals: HashSet<String> = ctx
            .bp_table
            .operators_for_category(cat)
            .iter()
            .map(|op| op.terminal.clone())
            .collect();

        // Collect terminals from prefix rules (non-infix, non-var, non-literal)
        let mut prefix_terminals: HashSet<String> = HashSet::new();
        for rule in ctx
            .rules
            .iter()
            .filter(|r| r.category == *cat && !r.is_infix && !r.is_var && !r.is_literal)
        {
            for item in &rule.first_items {
                if let FirstItem::Terminal(t) = item {
                    prefix_terminals.insert(t.clone());
                }
            }
        }

        // Check for unary prefix rules specifically
        let unary_prefix_terminals: HashSet<String> = ctx
            .rules
            .iter()
            .filter(|r| r.category == *cat && !r.is_infix && !r.is_var && !r.is_literal)
            .flat_map(|r| {
                r.first_items.iter().filter_map(|fi| match fi {
                    FirstItem::Terminal(t) => Some(t.clone()),
                    _ => None,
                })
            })
            .collect();

        let overlap: Vec<&String> = infix_terminals
            .intersection(&unary_prefix_terminals)
            .collect();

        for terminal in overlap {
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::G06,
                name: "shadowed-operator",
                severity: LintSeverity::Note,
                category: Some(cat.clone()),
                rule: None,
                message: format!(
                    "operator `{}` is both infix and prefix in category `{}`",
                    terminal, cat,
                ),
                hint: Some(
                    "this is intentional — prefix_bp = max_infix_bp + 2, so `-5!` = `-(5!)`"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G07: Identical Rules
// ══════════════════════════════════════════════════════════════════════════════

/// Normalize a syntax item sequence to a comparable string for G07.
fn syntax_signature(syntax: &[SyntaxItemSpec]) -> String {
    let mut parts = Vec::with_capacity(syntax.len());
    for item in syntax {
        match item {
            SyntaxItemSpec::Terminal(t) => parts.push(format!("T({})", t)),
            SyntaxItemSpec::NonTerminal { category, .. } => parts.push(format!("NT({})", category)),
            SyntaxItemSpec::IdentCapture { .. } => parts.push("IDENT".to_string()),
            SyntaxItemSpec::Binder { category, is_multi, .. } => {
                parts.push(format!("BIND({},{})", category, is_multi))
            },
            SyntaxItemSpec::Collection { element_category, separator, kind, .. } => {
                parts.push(format!("COL({},{},{:?})", element_category, separator, kind))
            },
            SyntaxItemSpec::Sep { body, separator, .. } => {
                let body_sig = syntax_signature(std::slice::from_ref(body.as_ref()));
                parts.push(format!("SEP({},{})", body_sig, separator))
            },
            SyntaxItemSpec::Map { body_items } => {
                let inner = syntax_signature(body_items);
                parts.push(format!("MAP({})", inner))
            },
            SyntaxItemSpec::Zip { left_category, right_category, body, .. } => {
                let body_sig = syntax_signature(std::slice::from_ref(body.as_ref()));
                parts.push(format!("ZIP({},{},{})", left_category, right_category, body_sig))
            },
            SyntaxItemSpec::BinderCollection { separator, .. } => {
                parts.push(format!("BCOL({})", separator))
            },
            SyntaxItemSpec::Optional { inner } => {
                let inner_sig = syntax_signature(inner);
                parts.push(format!("OPT({})", inner_sig))
            },
            SyntaxItemSpec::GuardExpression { param_name } => {
                parts.push(format!("GUARD({})", param_name))
            },
        }
    }
    parts.join("|")
}

pub(crate) fn lint_g07_identical_rules(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        let cat_syntax: Vec<(&str, &[SyntaxItemSpec])> = ctx
            .all_syntax
            .iter()
            .filter(|(_, c, _)| c == cat)
            .map(|(label, _, syntax)| (label.as_str(), syntax.as_slice()))
            .collect();

        let mut sig_to_labels: HashMap<String, Vec<&str>> = HashMap::new();
        for (label, syntax) in &cat_syntax {
            let sig = syntax_signature(syntax);
            sig_to_labels.entry(sig).or_default().push(label);
        }

        for (_, labels) in &sig_to_labels {
            if labels.len() > 1 {
                diagnostics.push(LintDiagnostic {
                    id: DiagnosticId::G07,
                    name: "identical-rules",
                    severity: LintSeverity::Warning,
                    category: Some(cat.clone()),
                    rule: None,
                    message: format!(
                        "rules [{}] in category `{}` have identical syntax item sequences",
                        labels.join(", "),
                        cat,
                    ),
                    hint: Some(
                        "these rules are structurally identical — consider merging or \
                         differentiating their syntax"
                            .to_string(),
                    ),
                    grammar_name: Some(ctx.grammar_name.to_string()),
                    source_location: None,
                });
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G24: Alpha-Equivalent Rules (Sprint C: C1)
// ══════════════════════════════════════════════════════════════════════════════

/// De Bruijn encoding environment for canonical variable renaming.
///
/// Variables are assigned sequential slots in encounter order. The first
/// occurrence of a variable gets tag `0xC0` (NewVar), subsequent occurrences
/// get tag `0x80 | slot` (VarRef). Two rules with different variable names
/// but identical structure produce identical byte sequences.
struct DebruijnEnv {
    var_slots: HashMap<String, u8>,
    next_slot: u8,
}

impl DebruijnEnv {
    fn new() -> Self {
        Self { var_slots: HashMap::new(), next_slot: 0 }
    }

    /// Resolve a variable name to its De Bruijn encoding byte.
    ///
    /// - First occurrence: emits `0xC0` (NewVar) and assigns a slot
    /// - Subsequent occurrences: emits `0x80 | slot` (VarRef)
    fn resolve(&mut self, name: &str) -> u8 {
        if let Some(&slot) = self.var_slots.get(name) {
            // VarRef: seen before at this slot
            0x80 | slot
        } else {
            // NewVar: first encounter — assign next sequential slot.
            // The slot index is implicit from encounter order, making
            // the encoding independent of the concrete variable name.
            let slot = self.next_slot;
            self.next_slot = self.next_slot.saturating_add(1);
            self.var_slots.insert(name.to_string(), slot);
            0xC0
        }
    }
}

/// Encode a `SyntaxItemSpec` sequence to De Bruijn canonical bytes.
///
/// Two syntax sequences that differ only in variable naming (α-equivalent)
/// produce identical byte sequences. Terminals and category names are
/// encoded literally; variable references use De Bruijn encounter-order slots.
///
/// Tag layout (compatible with but independent of `pattern_codec.rs`):
/// - `0xC0` — NewVar (first occurrence of a variable)
/// - `0x80 | slot` — VarRef (subsequent reference to variable at slot)
/// - `0x01` — NonTerminal tag
/// - `0x02` — Binder tag
/// - `0x03` — Collection tag
/// - `0x04` — IdentCapture tag
/// - `0x05` — Sep tag
/// - `0x06` — Map tag
/// - `0x07` — Zip tag
/// - `0x08` — BinderCollection tag
/// - `0x09` — Optional tag
/// - `0x0A` — Terminal tag
/// - `0x0B` — End tag (closes Optional/Map/Sep)
pub(crate) fn syntax_item_debruijn_bytes(items: &[SyntaxItemSpec]) -> Vec<u8> {
    let mut env = DebruijnEnv::new();
    let mut buf = Vec::with_capacity(items.len() * 4);
    for item in items {
        encode_syntax_item(item, &mut env, &mut buf);
    }
    buf
}

/// Encode a single `SyntaxItemSpec` into the De Bruijn byte buffer.
fn encode_syntax_item(item: &SyntaxItemSpec, env: &mut DebruijnEnv, buf: &mut Vec<u8>) {
    match item {
        SyntaxItemSpec::Terminal(token) => {
            buf.push(0x0A); // Terminal tag
            let bytes = token.as_bytes();
            buf.push(bytes.len() as u8);
            buf.extend_from_slice(bytes);
        },
        SyntaxItemSpec::NonTerminal { category, param_name } => {
            // Variable reference for the param_name (De Bruijn encoded)
            buf.push(env.resolve(param_name));
            buf.push(0x01); // NonTerminal tag
            let cat_bytes = category.as_bytes();
            buf.push(cat_bytes.len() as u8);
            buf.extend_from_slice(cat_bytes);
        },
        SyntaxItemSpec::IdentCapture { param_name } => {
            buf.push(env.resolve(param_name));
            buf.push(0x04); // IdentCapture tag
        },
        SyntaxItemSpec::Binder { param_name, category, is_multi } => {
            buf.push(env.resolve(param_name));
            buf.push(0x02); // Binder tag
            buf.push(if *is_multi { 1 } else { 0 });
            let cat_bytes = category.as_bytes();
            buf.push(cat_bytes.len() as u8);
            buf.extend_from_slice(cat_bytes);
        },
        SyntaxItemSpec::Collection {
            param_name,
            element_category,
            separator,
            key_val_separator: _,
            kind,
        } => {
            buf.push(env.resolve(param_name));
            buf.push(0x03); // Collection tag
            let cat_bytes = element_category.as_bytes();
            buf.push(cat_bytes.len() as u8);
            buf.extend_from_slice(cat_bytes);
            let sep_bytes = separator.as_bytes();
            buf.push(sep_bytes.len() as u8);
            buf.extend_from_slice(sep_bytes);
            buf.push(*kind as u8);
        },
        SyntaxItemSpec::Sep { body, separator, kind } => {
            buf.push(0x05); // Sep tag
            let sep_bytes = separator.as_bytes();
            buf.push(sep_bytes.len() as u8);
            buf.extend_from_slice(sep_bytes);
            buf.push(*kind as u8);
            encode_syntax_item(body, env, buf);
            buf.push(0x0B); // End tag
        },
        SyntaxItemSpec::Map { body_items } => {
            buf.push(0x06); // Map tag
            for sub in body_items {
                encode_syntax_item(sub, env, buf);
            }
            buf.push(0x0B); // End tag
        },
        SyntaxItemSpec::Zip {
            left_name,
            right_name,
            left_category,
            right_category,
            body,
        } => {
            buf.push(env.resolve(left_name));
            buf.push(env.resolve(right_name));
            buf.push(0x07); // Zip tag
            let lc = left_category.as_bytes();
            buf.push(lc.len() as u8);
            buf.extend_from_slice(lc);
            let rc = right_category.as_bytes();
            buf.push(rc.len() as u8);
            buf.extend_from_slice(rc);
            encode_syntax_item(body, env, buf);
            buf.push(0x0B); // End tag
        },
        SyntaxItemSpec::BinderCollection { param_name, separator } => {
            buf.push(env.resolve(param_name));
            buf.push(0x08); // BinderCollection tag
            let sep_bytes = separator.as_bytes();
            buf.push(sep_bytes.len() as u8);
            buf.extend_from_slice(sep_bytes);
        },
        SyntaxItemSpec::Optional { inner } => {
            buf.push(0x09); // Optional tag
            for sub in inner {
                encode_syntax_item(sub, env, buf);
            }
            buf.push(0x0B); // End tag
        },
        SyntaxItemSpec::GuardExpression { param_name } => {
            buf.push(env.resolve(param_name));
            buf.push(0x0C); // GuardExpression tag (Phase 2F)
        },
    }
}

/// G24: Alpha-equivalent grammar rules.
///
/// Detects rules within the same category whose syntax item sequences are
/// identical up to variable renaming (α-equivalence). Uses De Bruijn
/// encounter-order encoding so that `rule A: x "+" y` and `rule B: a "+" b`
/// produce identical byte sequences, even though G07's string signatures differ.
///
/// Runs after G07 to avoid double-reporting: any pair already flagged by G07
/// (exact string match) is excluded from G24 results.
pub(crate) fn lint_g24_alpha_equivalent_rules(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        let cat_syntax: Vec<(&str, &[SyntaxItemSpec])> = ctx
            .all_syntax
            .iter()
            .filter(|(_, c, _)| c == cat)
            .map(|(label, _, syntax)| (label.as_str(), syntax.as_slice()))
            .collect();

        // Group by De Bruijn bytes
        let mut debruijn_groups: HashMap<Vec<u8>, Vec<&str>> = HashMap::new();
        for (label, syntax) in &cat_syntax {
            let bytes = syntax_item_debruijn_bytes(syntax);
            debruijn_groups.entry(bytes).or_default().push(label);
        }

        for (_, labels) in &debruijn_groups {
            if labels.len() < 2 {
                continue;
            }

            // Check if this group has identical string signatures — if so,
            // G07 already reports it. G24 only fires for groups where the
            // De Bruijn bytes match but the string signatures differ (true
            // α-equivalence that G07 misses: different variable names, same structure).
            let sigs: HashSet<String> = labels
                .iter()
                .map(|label| {
                    let syntax = cat_syntax
                        .iter()
                        .find(|(l, _)| l == label)
                        .map(|(_, s)| *s)
                        .expect("label must exist in cat_syntax");
                    syntax_signature(syntax)
                })
                .collect();
            if sigs.len() == 1 {
                // All have identical string signatures → G07 covers this
                continue;
            }

            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::G24,
                name: "alpha-equivalent-rules",
                severity: LintSeverity::Warning,
                category: Some(cat.clone()),
                rule: None,
                message: format!(
                    "rules [{}] in category `{}` are α-equivalent \
                     (identical up to variable renaming)",
                    labels.join(", "),
                    cat,
                ),
                hint: Some(
                    "these rules differ only in variable names — consider merging \
                     or differentiating their syntax structure"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G08: Missing Cast to Root
// ══════════════════════════════════════════════════════════════════════════════

/// G08: Checks **directed** value-flow graph reachability (source->target
/// edges). A category that has no directed value-flow path *from itself to the
/// primary* is flagged. Cast rules, cross-category rules, and syntax embeddings
/// all add value-flow edges.
///
/// **Relationship with A4 (W01 InterCategoryDeadPath)**: A4 uses a richer
/// **undirected** graph over structural references. G08 keeps edge direction,
/// so it can distinguish "the primary mentions this category" from "values of
/// this category can flow into the primary". The two analyses are
/// complementary, not redundant.
pub(crate) fn lint_g08_missing_cast_to_root(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    // Find primary (root) category
    let primary = match ctx.categories.iter().find(|c| c.is_primary) {
        Some(c) => &c.name,
        None => return,
    };

    // Build directed value-flow graph. Cast rules start as source -> target.
    let mut adjacency: HashMap<&str, HashSet<&str>> = HashMap::new();
    for cast in ctx.cast_rules {
        adjacency
            .entry(cast.source_category.as_str())
            .or_default()
            .insert(cast.target_category.as_str());
    }

    // Cross-category rules transport source values into result values.
    for cross in ctx.cross_rules {
        adjacency
            .entry(cross.source_category.as_str())
            .or_default()
            .insert(cross.result_category.as_str());
    }

    for (_, target_category, syntax) in ctx.all_syntax {
        for item in syntax {
            add_g08_syntax_value_edges(item, target_category.as_str(), &mut adjacency);
        }
    }

    // A non-primary category is integrated if values produced by that category
    // can flow into the primary parse result through directed source -> target
    // edges. Cast/cross rules and primary syntax embeddings all use this same
    // orientation.

    let category_names: Vec<&str> = ctx.categories.iter().map(|c| c.name.as_str()).collect();
    let non_native_binding_sorts: HashSet<&str> = {
        let binding_sorts = binding_sort_categories(ctx);
        ctx.categories
            .iter()
            .filter(|cat| cat.native_type.is_none() && binding_sorts.contains(&cat.name))
            .map(|cat| cat.name.as_str())
            .collect()
    };
    let refinement_categories: HashSet<&str> = ctx
        .refinement_types
        .iter()
        .map(|rt| rt.name.as_str())
        .collect();

    for cat_name in &category_names {
        if *cat_name == primary.as_str() {
            continue;
        }
        if refinement_categories.contains(cat_name) {
            continue;
        }
        if non_native_binding_sorts.contains(cat_name) {
            continue;
        }

        // DFS from cat_name following source->target edges to see if we reach primary.
        let mut visited = HashSet::new();
        let mut stack = vec![*cat_name];
        let mut found = false;

        while let Some(node) = stack.pop() {
            if node == primary.as_str() {
                found = true;
                break;
            }
            if !visited.insert(node) {
                continue;
            }
            if let Some(neighbors) = adjacency.get(node) {
                for &next in neighbors {
                    stack.push(next);
                }
            }
        }

        if !found {
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::G08,
                name: "missing-cast-to-root",
                severity: LintSeverity::Warning,
                category: Some(cat_name.to_string()),
                rule: None,
                message: format!(
                    "no value-flow path from category `{}` to primary category `{}`",
                    cat_name, primary,
                ),
                hint: Some(format!(
                    "add a cast/cross-category rule or syntax embedding from `{}` to `{}` or an intermediate category",
                    cat_name, primary,
                )),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

fn add_g08_syntax_value_edges<'a>(
    item: &'a SyntaxItemSpec,
    target_category: &'a str,
    adjacency: &mut HashMap<&'a str, HashSet<&'a str>>,
) {
    match item {
        SyntaxItemSpec::NonTerminal { category, .. } => {
            adjacency
                .entry(category.as_str())
                .or_default()
                .insert(target_category);
        },
        SyntaxItemSpec::Collection { element_category, .. } => {
            adjacency
                .entry(element_category.as_str())
                .or_default()
                .insert(target_category);
        },
        SyntaxItemSpec::Sep { body, .. } => {
            add_g08_syntax_value_edges(body, target_category, adjacency);
        },
        SyntaxItemSpec::Map { body_items } => {
            for item in body_items {
                add_g08_syntax_value_edges(item, target_category, adjacency);
            }
        },
        SyntaxItemSpec::Zip { left_category, right_category, body, .. } => {
            adjacency
                .entry(left_category.as_str())
                .or_default()
                .insert(target_category);
            adjacency
                .entry(right_category.as_str())
                .or_default()
                .insert(target_category);
            add_g08_syntax_value_edges(body, target_category, adjacency);
        },
        SyntaxItemSpec::Optional { inner } => {
            for item in inner {
                add_g08_syntax_value_edges(item, target_category, adjacency);
            }
        },
        SyntaxItemSpec::Terminal(_)
        | SyntaxItemSpec::IdentCapture { .. }
        | SyntaxItemSpec::Binder { .. }
        | SyntaxItemSpec::BinderCollection { .. }
        | SyntaxItemSpec::GuardExpression { .. } => {},
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G09: Unbalanced Delimiters
// ══════════════════════════════════════════════════════════════════════════════

pub(crate) fn lint_g09_unbalanced_delimiters(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let pairs = [('(', ')'), ('{', '}'), ('[', ']')];

    for (label, category, syntax) in ctx.all_syntax {
        let terminals = collect_terminals_flat(syntax);

        for &(open_char, close_char) in &pairs {
            // Count character occurrences across all terminals, not exact matches.
            // This correctly handles compound terminals like "in(" contributing 1
            // to the open-paren count, and self-balanced terminals like "()" contributing
            // 1 to each.
            let open_count: usize = terminals
                .iter()
                .map(|t| t.chars().filter(|&c| c == open_char).count())
                .sum();
            let close_count: usize = terminals
                .iter()
                .map(|t| t.chars().filter(|&c| c == close_char).count())
                .sum();

            if open_count != close_count {
                diagnostics.push(LintDiagnostic {
                    id: DiagnosticId::G09,
                    name: "unbalanced-delimiters",
                    severity: LintSeverity::Warning,
                    category: Some(category.clone()),
                    rule: Some(label.clone()),
                    message: format!(
                        "rule `{}` in category `{}` has unbalanced delimiters: \
                         {} `{}` vs {} `{}`",
                        label, category, open_count, open_char, close_count, close_char,
                    ),
                    hint: Some(format!(
                        "add the missing `{}` delimiter",
                        if open_count > close_count {
                            close_char
                        } else {
                            open_char
                        },
                    )),
                    grammar_name: Some(ctx.grammar_name.to_string()),
                    source_location: ctx
                        .rule_locations
                        .get(&(label.clone(), category.clone()))
                        .copied(),
                });
            }
        }
    }
}

/// Collect all terminal strings from syntax items (flat, including nested).
fn collect_terminals_flat(items: &[SyntaxItemSpec]) -> Vec<String> {
    let mut terminals = Vec::new();
    for item in items {
        match item {
            SyntaxItemSpec::Terminal(t) => terminals.push(t.clone()),
            SyntaxItemSpec::Collection { separator, .. }
            | SyntaxItemSpec::BinderCollection { separator, .. } => {
                terminals.push(separator.clone());
            },
            SyntaxItemSpec::Sep { body, separator, .. } => {
                terminals.extend(collect_terminals_flat(std::slice::from_ref(body.as_ref())));
                terminals.push(separator.clone());
            },
            SyntaxItemSpec::Map { body_items } => {
                terminals.extend(collect_terminals_flat(body_items));
            },
            SyntaxItemSpec::Zip { body, .. } => {
                terminals.extend(collect_terminals_flat(std::slice::from_ref(body.as_ref())));
            },
            SyntaxItemSpec::Optional { inner } => {
                terminals.extend(collect_terminals_flat(inner));
            },
            _ => {},
        }
    }
    terminals
}

/// Get rule labels dispatched by a token in a category using the decision tree.
fn tree_rules_for_token(ctx: &LintContext, category: &str, token: &str) -> Vec<String> {
    let tree = match ctx.decision_trees.get(category) {
        Some(t) => t,
        None => return Vec::new(),
    };
    let variant = crate::automata::codegen::terminal_to_variant_name(token);
    let strategy = tree.dispatch_strategy(&variant, ctx.token_id_map);
    match strategy {
        crate::decision_tree::DispatchStrategy::Singleton { rule_label } => vec![rule_label],
        crate::decision_tree::DispatchStrategy::AmbiguousFanout { rule_labels, .. } => rule_labels,
        crate::decision_tree::DispatchStrategy::DisjointSuffix { suffix_map, .. } => {
            suffix_map.values().cloned().collect()
        },
        _ => Vec::new(),
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G10: Ambiguous Associativity
// ══════════════════════════════════════════════════════════════════════════════

pub(crate) fn lint_g10_ambiguous_associativity(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        let ops = ctx.bp_table.operators_for_category(cat);

        // Group by left_bp (same precedence level)
        let mut bp_to_ops: HashMap<u8, Vec<&crate::binding_power::InfixOperator>> = HashMap::new();
        for op in &ops {
            bp_to_ops.entry(op.left_bp).or_default().push(op);
        }

        for (left_bp, group) in &bp_to_ops {
            if group.len() < 2 {
                continue;
            }

            let first_assoc = group[0].associativity();
            let has_mixed = group.iter().any(|op| op.associativity() != first_assoc);
            if has_mixed {
                let op_names: Vec<&str> = group.iter().map(|op| op.terminal.as_str()).collect();
                diagnostics.push(LintDiagnostic {
                    id: DiagnosticId::G10,
                    name: "ambiguous-associativity",
                    severity: LintSeverity::Warning,
                    category: Some(cat.clone()),
                    rule: None,
                    message: format!(
                        "same-precedence operators [{}] in category `{}` (left_bp={}) \
                         have different associativity",
                        op_names.join(", "),
                        cat,
                        left_bp,
                    ),
                    hint: Some(
                        "use explicit precedence levels to separate operators with \
                         different associativity"
                            .to_string(),
                    ),
                    grammar_name: Some(ctx.grammar_name.to_string()),
                    source_location: None,
                });
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// W01: Dead Rule (migrated from pipeline.rs)
// ══════════════════════════════════════════════════════════════════════════════

pub(crate) fn lint_w01_dead_rule(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    // Use pre-computed dead-rule warnings from the pipeline (cached in LintContext).
    // This avoids re-invoking detect_dead_rules() which was previously called 3x
    // with identical inputs.
    //
    // A4 (inter-category dead-path) and A8 (nearly-dead path) are still computed
    // here because they are lint-only analyses not needed by the pipeline codegen.
    let mut warnings: Vec<crate::pipeline::DeadRuleWarning> = ctx.dead_rule_warnings.to_vec();

    // A4: Inter-category dead-path detection via forward-backward analysis
    // on an undirected inter-category graph including all syntax references
    // (NonTerminal, Binder, Collection). See also G08 which checks directed
    // value-flow reachability. G08 fires on categories whose values cannot flow
    // to the primary; A4 fires on categories structurally isolated via the
    // richer undirected graph. The two are complementary.
    let inter_cat_warnings = crate::pipeline::detect_inter_category_dead_paths(
        ctx.rules,
        ctx.categories,
        ctx.first_sets,
        ctx.all_syntax,
    );
    // Only add inter-category warnings for rules not already flagged by Tier 1-3
    let existing_rules: std::collections::HashSet<String> = warnings
        .iter()
        .map(|w| match w {
            crate::pipeline::DeadRuleWarning::LiteralNoNativeType { rule_label, .. }
            | crate::pipeline::DeadRuleWarning::UnreachableCategory { rule_label, .. }
            | crate::pipeline::DeadRuleWarning::WfstUnreachable { rule_label, .. }
            | crate::pipeline::DeadRuleWarning::InterCategoryDeadPath { rule_label, .. }
            | crate::pipeline::DeadRuleWarning::NearlyDeadPath { rule_label, .. } => {
                rule_label.clone()
            },
        })
        .collect();
    for w in inter_cat_warnings {
        match &w {
            crate::pipeline::DeadRuleWarning::InterCategoryDeadPath { rule_label, .. } => {
                if !existing_rules.contains(rule_label) {
                    warnings.push(w);
                }
            },
            _ => warnings.push(w),
        }
    }

    // A8: Nearly-dead inter-category path detection via ProductWeight<BooleanWeight, CountingWeight>.
    // Only flags rules whose categories are reachable (not already flagged by A4) but have
    // very few derivation paths relative to the total (< 1% of max count).
    let nearly_dead_warnings = crate::pipeline::detect_nearly_dead_paths(
        ctx.rules,
        ctx.categories,
        ctx.first_sets,
        ctx.all_syntax,
    );
    // Collect all already-flagged rules to avoid duplicate diagnostics
    let all_flagged: std::collections::HashSet<String> = warnings
        .iter()
        .map(|w| match w {
            crate::pipeline::DeadRuleWarning::LiteralNoNativeType { rule_label, .. }
            | crate::pipeline::DeadRuleWarning::UnreachableCategory { rule_label, .. }
            | crate::pipeline::DeadRuleWarning::WfstUnreachable { rule_label, .. }
            | crate::pipeline::DeadRuleWarning::InterCategoryDeadPath { rule_label, .. }
            | crate::pipeline::DeadRuleWarning::NearlyDeadPath { rule_label, .. } => {
                rule_label.clone()
            },
        })
        .collect();
    for w in nearly_dead_warnings {
        if let crate::pipeline::DeadRuleWarning::NearlyDeadPath { ref rule_label, .. } = w {
            if !all_flagged.contains(rule_label) {
                warnings.push(w);
            }
        }
    }

    for w in &warnings {
        let (rule_label, category, hint_msg) = match &w {
            crate::pipeline::DeadRuleWarning::LiteralNoNativeType {
                rule_label,
                category,
            } => (
                rule_label.clone(),
                category.clone(),
                "add a native_type to the category or remove the literal rule",
            ),
            crate::pipeline::DeadRuleWarning::UnreachableCategory {
                rule_label,
                category,
            } => (
                rule_label.clone(),
                category.clone(),
                "add a prefix rule to make the category reachable",
            ),
            crate::pipeline::DeadRuleWarning::WfstUnreachable {
                rule_label,
                category,
            } => (
                rule_label.clone(),
                category.clone(),
                "remove the rule or add a unique dispatch token",
            ),
            crate::pipeline::DeadRuleWarning::InterCategoryDeadPath {
                rule_label,
                category,
                ..
            } => (
                rule_label.clone(),
                category.clone(),
                "check inter-category connections; this category may be isolated",
            ),
            crate::pipeline::DeadRuleWarning::NearlyDeadPath {
                rule_label,
                category,
                ..
            } => (
                rule_label.clone(),
                category.clone(),
                "this category has very few derivation paths; consider simplifying or removing rules",
            ),
        };

        // A8: NearlyDeadPath gets its own lint ID (W07, note-level) since the rule is
        // technically reachable — this is a diagnostic hint, not a dead-code warning.
        let (lint_id, lint_name, severity) = match &w {
            crate::pipeline::DeadRuleWarning::NearlyDeadPath { .. } => {
                (DiagnosticId::W07, "nearly-dead-path", LintSeverity::Note)
            },
            _ => (DiagnosticId::W01, "dead-rule", LintSeverity::Warning),
        };

        diagnostics.push(LintDiagnostic {
            id: lint_id,
            name: lint_name,
            severity,
            category: Some(category.clone()),
            rule: Some(rule_label.clone()),
            message: format!("{}", w),
            hint: Some(hint_msg.to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: ctx
                .rule_locations
                .get(&(rule_label.clone(), category.clone()))
                .copied(),
        });
    }

    // Dead prefix detection: use the shared detect_dead_prefixes() function
    // (also used by the pipeline to increase recovery WFST weights).
    let dead_prefixes =
        crate::pipeline::detect_dead_prefixes(&warnings, ctx.decision_trees, ctx.token_id_map);
    for (cat_name, prefix_tokens) in &dead_prefixes {
        for token_variant in prefix_tokens {
            // Look up which rules this prefix reaches, for the diagnostic message
            if let Some(tree) = ctx.decision_trees.get(cat_name) {
                let strategy = tree.dispatch_strategy(token_variant, ctx.token_id_map);
                let rule_labels = match &strategy {
                    crate::decision_tree::DispatchStrategy::Singleton { rule_label } => {
                        vec![rule_label.clone()]
                    },
                    crate::decision_tree::DispatchStrategy::AmbiguousFanout {
                        rule_labels, ..
                    } => rule_labels.clone(),
                    crate::decision_tree::DispatchStrategy::DisjointSuffix {
                        suffix_map, ..
                    } => suffix_map.values().cloned().collect(),
                    crate::decision_tree::DispatchStrategy::NotPresent => Vec::new(),
                };
                diagnostics.push(LintDiagnostic {
                    id: DiagnosticId::W01,
                    name: "dead-prefix",
                    severity: LintSeverity::Note,
                    category: Some(cat_name.clone()),
                    rule: None,
                    message: format!(
                        "prefix `{}` in category `{}` leads only to dead rules [{}]; \
                         entire prefix subtrie is unreachable",
                        token_variant,
                        cat_name,
                        rule_labels.join(", "),
                    ),
                    hint: Some(
                        "all rules reachable from this prefix are dead — \
                         the dispatch arm is unreachable"
                            .to_string(),
                    ),
                    grammar_name: Some(ctx.grammar_name.to_string()),
                    source_location: None,
                });
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// W02: NFA Ambiguous Prefix (migrated from pipeline.rs)
// ══════════════════════════════════════════════════════════════════════════════

pub(crate) fn lint_w02_nfa_ambiguous_prefix(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    for cat_name in ctx.nfa_spillover_categories {
        let rd_by_token =
            crate::rd_analysis::group_rd_by_dispatch_token_pub(ctx.rd_rules, cat_name);
        if let Some(wfst) = ctx.prediction_wfsts.get(cat_name.as_str()) {
            for (token, rules) in &rd_by_token {
                if rules.len() <= 1 {
                    continue;
                }
                let labels: Vec<&str> = rules.iter().map(|r| r.label.as_str()).collect();
                let ordered = wfst.nfa_alternative_order(token, &labels);
                let weights: Vec<f64> = ordered.iter().map(|(_, w)| w.0).collect();
                let all_equal = weights.windows(2).all(|w| (w[0] - w[1]).abs() < 1e-12);

                // Sprint 4: Compute ContextWeight narrowing for this dispatch token.
                // If the WFST has context labels, report the narrowed count.
                let (_ctx_narrowed, narrowed_count) = wfst.context_narrowing(&[token]);
                let original_count = rules.len();

                let mut message = format!(
                    "ambiguous prefix dispatch for token `{}` in category `{}`: \
                     rules [{}] all match",
                    token,
                    cat_name,
                    labels.join(", "),
                );

                if narrowed_count > 0 && (narrowed_count as usize) < original_count {
                    message.push_str(&format!(
                        " (ContextWeight narrows to {}/{} candidates)",
                        narrowed_count, original_count,
                    ));
                }

                if all_equal {
                    message.push_str(&format!(
                        " — all {} alternatives have equal weight ({:.1}); \
                         resolution deferred to semantic disambiguation",
                        original_count,
                        weights.first().copied().unwrap_or(0.5),
                    ));
                }

                // When ContextWeight narrows to singleton, downgrade to Note
                let severity = if narrowed_count == 1 {
                    LintSeverity::Note
                } else {
                    LintSeverity::Warning
                };

                diagnostics.push(LintDiagnostic {
                    id: DiagnosticId::W02,
                    name: "nfa-ambiguous-prefix",
                    severity,
                    category: Some(cat_name.clone()),
                    rule: None,
                    message,
                    hint: Some(
                        "add distinguishing syntax to resolve the ambiguity; \
                         WFST auto-assigns weights by rule specificity and declaration order"
                            .to_string(),
                    ),
                    grammar_name: Some(ctx.grammar_name.to_string()),
                    source_location: None,
                });
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// W03: High Ambiguity Token
// ══════════════════════════════════════════════════════════════════════════════

pub(crate) fn lint_w03_high_ambiguity_token(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        if let Some(wfst) = ctx.prediction_wfsts.get(cat.as_str()) {
            if let Some(first_set) = ctx.first_sets.get(cat) {
                for token in first_set.sorted_tokens() {
                    let predictions = wfst.predict_with_confidence(&token);
                    if let Some((_, count_weight)) = predictions.first() {
                        if count_weight.count() >= 3 {
                            let action_labels: Vec<String> = predictions
                                .iter()
                                .map(|(a, _)| a.action.rule_label().to_string())
                                .collect();
                            diagnostics.push(LintDiagnostic {
                                id: DiagnosticId::W03,
                                name: "high-ambiguity-token",
                                severity: LintSeverity::Warning,
                                category: Some(cat.clone()),
                                rule: None,
                                message: format!(
                                    "token `{}` dispatches to {} rules in category `{}`: [{}]",
                                    token,
                                    predictions.len(),
                                    cat,
                                    action_labels.join(", "),
                                ),
                                hint: Some(
                                    "high branching factor — consider adding unique \
                                     dispatch tokens to reduce ambiguity"
                                        .to_string(),
                                ),
                                grammar_name: Some(ctx.grammar_name.to_string()),
                                source_location: None,
                            });
                        }
                    }
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// W04: Weight Gap Anomaly
// ══════════════════════════════════════════════════════════════════════════════

pub(crate) fn lint_w04_weight_gap_anomaly(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        if let Some(wfst) = ctx.prediction_wfsts.get(cat.as_str()) {
            if let Some(first_set) = ctx.first_sets.get(cat) {
                for token in first_set.sorted_tokens() {
                    let actions = wfst.predict(&token);
                    if actions.len() >= 2 {
                        let best = actions[0].weight.value();
                        let second = actions[1].weight.value();
                        let gap = second - best;

                        if gap > 5.0 {
                            diagnostics.push(LintDiagnostic {
                                id: DiagnosticId::W04,
                                name: "weight-gap-anomaly",
                                severity: LintSeverity::Note,
                                category: Some(cat.clone()),
                                rule: None,
                                message: format!(
                                    "token `{}` in category `{}`: gap of {:.1} between best \
                                     rule `{}` (weight {:.1}) and second-best `{}` (weight {:.1}) \
                                     — near-deterministic treated as ambiguous",
                                    token,
                                    cat,
                                    gap,
                                    actions[0].action.rule_label(),
                                    best,
                                    actions[1].action.rule_label(),
                                    second,
                                ),
                                hint: Some(
                                    "the large weight gap suggests this token is effectively \
                                     unambiguous — the second alternative is very unlikely"
                                        .to_string(),
                                ),
                                grammar_name: Some(ctx.grammar_name.to_string()),
                                source_location: None,
                            });
                        }
                    }
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// W06: Weight Inversion
// ══════════════════════════════════════════════════════════════════════════════

pub(crate) fn lint_w06_weight_inversion(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    // Build a map from rule label → syntax item count (specificity)
    let specificity: HashMap<&str, usize> = ctx
        .all_syntax
        .iter()
        .map(|(label, _, syntax)| (label.as_str(), syntax.len()))
        .collect();

    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        if let Some(wfst) = ctx.prediction_wfsts.get(cat.as_str()) {
            if let Some(first_set) = ctx.first_sets.get(cat) {
                for token in first_set.sorted_tokens() {
                    let actions = wfst.predict(&token);
                    // Check each pair: if less-specific rule has lower weight (better)
                    // than more-specific rule, that's an inversion
                    for i in 0..actions.len() {
                        for j in (i + 1)..actions.len() {
                            let label_i = actions[i].action.rule_label();
                            let label_j = actions[j].action.rule_label();
                            let spec_i = specificity.get(label_i.as_str()).copied().unwrap_or(0);
                            let spec_j = specificity.get(label_j.as_str()).copied().unwrap_or(0);
                            let w_i = actions[i].weight.value();
                            let w_j = actions[j].weight.value();

                            // Inversion: less-specific (lower spec) has lower weight (better priority)
                            // than more-specific (higher spec)
                            if spec_i < spec_j && w_i < w_j {
                                diagnostics.push(LintDiagnostic {
                                    id: DiagnosticId::W06,
                                    name: "weight-inversion",
                                    severity: LintSeverity::Note,
                                    category: Some(cat.clone()),
                                    rule: None,
                                    message: format!(
                                        "weight inversion for token `{}` in category `{}`: \
                                         less-specific rule `{}` ({} items, weight {:.2}) has \
                                         better priority than more-specific `{}` ({} items, \
                                         weight {:.2})",
                                        token, cat, label_i, spec_i, w_i, label_j, spec_j, w_j,
                                    ),
                                    hint: Some(
                                        "more-specific rules should typically have lower \
                                         (better) weights — check rule declaration order (WFST auto-assigns by specificity and order)"
                                            .to_string(),
                                    ),
                                    grammar_name: Some(ctx.grammar_name.to_string()),
                                    source_location: None,
                                });
                            }
                        }
                    }
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Stage 10c (2026-05-04): W10 (spillover-eliminable-by-lookahead) DELETED.
// Iterated `nfa_spillover_categories` checking k-token narrowability; the
// enforcement target — NFA spillover infrastructure used by trampoline.rs and
// parse_preserving_vars — was excised in Stage 10b. Walker+WPDS subsumes the
// dispatch; any narrow-by-lookahead win is collected by the WFST/WPDS path.
// (Function body, grouper helper `group_w10`, and grouper test all removed.)
// ══════════════════════════════════════════════════════════════════════════════

// ══════════════════════════════════════════════════════════════════════════════
// Stage 10c (2026-05-04): W11 (context-narrowing-deterministic) DELETED.
// Stage 10/T11 (2026-05-05): `DispatchStrategy::NfaTryAll` renamed to
// `AmbiguousFanout` (the trampoline-era runtime mechanism is gone; the
// variant survives because static analyses still want to enumerate the
// ambiguous prefix-overlap set for diagnostics — Walker emits Forks for
// these very same fanout sets).
// Per `analysis-nfa-spillover-coverage-gaps.md` Gap 2: NFA spillover lints
// have no enforcement target post-Stage-10b parse_preserving_vars excision.
// ══════════════════════════════════════════════════════════════════════════════

// ══════════════════════════════════════════════════════════════════════════════
// W12: Training Would Improve (Sprint 6, wfst-log gated)
// ══════════════════════════════════════════════════════════════════════════════

/// W12: Compute Shannon entropy at each dispatch point. High entropy suggests
/// training would improve weight assignment.
pub(crate) fn lint_w12_training_would_improve(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    for (cat_name, wfst) in ctx.prediction_wfsts {
        let (entropy_nats, entropy_bits) = wfst.compute_entropy();

        // High entropy threshold: > 2.0 bits (near-uniform distribution)
        if entropy_bits > 2.0 {
            let num_actions = wfst.num_actions();
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::W12,
                name: "training-would-improve",
                severity: LintSeverity::Note,
                category: Some(cat_name.clone()),
                rule: None,
                message: format!(
                    "category `{}` has high dispatch entropy ({:.2} bits, {:.2} nats) \
                     across {} actions — WFST weight training would likely improve \
                     disambiguation quality",
                    cat_name, entropy_bits, entropy_nats, num_actions,
                ),
                hint: Some(
                    "use `train_from_corrections()` to \
                     learn better weights from parse examples"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// W13: WPDS-Unreachable Rule (stack-aware dead-rule verification)
// ══════════════════════════════════════════════════════════════════════════════

/// W13: WPDS stack-aware dead-rule detection.
///
/// Uses poststar saturation results to identify rules that are unreachable
/// when stack context (call/return matching) is considered. This is strictly
/// more precise than the finite-state W01 tier: a rule may be reachable in
/// the WFST projection but unreachable in the WPDS because no valid calling
/// context exists.
pub(crate) fn lint_w13_wpds_unreachable(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let analysis = match ctx.wpds_analysis {
        Some(a) => a,
        None => return,
    };

    for unreachable in &analysis.unreachable_rules {
        if ctx
            .dead_rule_ignore_labels
            .contains(&unreachable.rule_label)
        {
            continue;
        }

        let missing_ctx = if unreachable.missing_contexts.is_empty() {
            String::new()
        } else {
            format!(" (missing callers: {})", unreachable.missing_contexts.join(", "))
        };

        // D15: Append witness trace if available
        let witness = if unreachable.witness_trace.is_empty() {
            String::new()
        } else {
            format!("\n  witness trace:\n    {}", unreachable.witness_trace.join("\n    "))
        };

        let source_location = ctx
            .rule_locations
            .get(&(unreachable.rule_label.clone(), unreachable.category.clone()))
            .copied();

        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::W13,
            name: "wpds-unreachable",
            severity: LintSeverity::Warning,
            category: Some(unreachable.category.clone()),
            rule: Some(unreachable.rule_label.clone()),
            message: format!(
                "rule `{}` in category `{}` is unreachable via WPDS stack-aware analysis{}{}",
                unreachable.rule_label, unreachable.category, missing_ctx, witness,
            ),
            hint: Some(
                "this rule's category is not reachable from the root via any \
                 valid call/return path; consider adding a cross-category \
                 reference or removing the rule"
                    .to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location,
        });
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// D14: WPDS Complexity Report
// ══════════════════════════════════════════════════════════════════════════════

/// Emit an Info diagnostic summarizing WPDS analysis complexity:
/// `|Γ|` (stack symbols), `|Δ|` (rules), SCC count, reachable categories.
pub(crate) fn lint_d14_wpds_complexity_report(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let analysis = match ctx.wpds_analysis {
        Some(a) => a,
        None => return,
    };

    let scc_count = analysis.call_graph.sccs.len();
    let nontrivial_sccs: Vec<_> = analysis
        .call_graph
        .sccs
        .iter()
        .filter(|scc| {
            scc.len() > 1
                || (scc.len() == 1
                    && analysis
                        .call_graph
                        .edges
                        .iter()
                        .any(|e| e.caller_cat == scc[0] && e.callee_cat == scc[0]))
        })
        .collect();

    let edge_count = analysis.call_graph.edges.len();
    let reachable = analysis.reachable_categories.len();
    let total_cats = analysis.call_graph.categories.len();

    let cycle_count = analysis.cycles.len();
    let recursive_cats: usize = analysis
        .depth_bounds
        .values()
        .filter(|db| db.is_recursive)
        .count();

    let mut msg = format!(
        "WPDS analysis: |Γ|={}, |Δ|={}, {} SCCs, {} call edges, {}/{} reachable categories, {} cycles, {} recursive",
        analysis.num_symbols, analysis.num_rules, scc_count, edge_count, reachable, total_cats,
        cycle_count, recursive_cats,
    );

    if !nontrivial_sccs.is_empty() {
        let scc_desc: Vec<String> = nontrivial_sccs
            .iter()
            .map(|scc| format!("{{{}}}", scc.join(", ")))
            .collect();
        msg.push_str(&format!("; recursive SCCs: {}", scc_desc.join(", ")));
    }

    // Include depth bounds summary
    let bounded: Vec<_> = analysis
        .depth_bounds
        .iter()
        .filter(|(_, db)| db.max_depth.is_some())
        .map(|(cat, db)| format!("{}={}", cat, db.max_depth.expect("filtered")))
        .collect();
    if !bounded.is_empty() {
        msg.push_str(&format!("; max_depth: {}", bounded.join(", ")));
    }

    diagnostics.push(LintDiagnostic {
        id: DiagnosticId::D14,
        name: "wpds-complexity-report",
        severity: LintSeverity::Info,
        category: None,
        rule: None,
        message: msg,
        hint: None,
        grammar_name: Some(ctx.grammar_name.to_string()),
        source_location: None,
    });
}

// ══════════════════════════════════════════════════════════════════════════════
// P05: WPDS Pipeline Cost Report
// ══════════════════════════════════════════════════════════════════════════════

/// Emit an Info diagnostic reporting WPDS analysis wall-clock time.
pub(crate) fn lint_p05_wpds_pipeline_cost(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let elapsed = match ctx.wpds_elapsed {
        Some(d) => d,
        None => return,
    };

    let analysis = match ctx.wpds_analysis {
        Some(a) => a,
        None => return,
    };

    diagnostics.push(LintDiagnostic {
        id: DiagnosticId::P05,
        name: "wpds-pipeline-cost",
        severity: LintSeverity::Info,
        category: None,
        rule: None,
        message: format!(
            "WPDS analysis completed in {:.2}ms (|Γ|={}, |Δ|={}, {} unreachable rules)",
            elapsed.as_secs_f64() * 1000.0,
            analysis.num_symbols,
            analysis.num_rules,
            analysis.unreachable_rules.len(),
        ),
        hint: None,
        grammar_name: Some(ctx.grammar_name.to_string()),
        source_location: None,
    });
}

// ══════════════════════════════════════════════════════════════════════════════
// W14: Walker-Fork Tight Margin (Stage 10c repurpose, 2026-05-04)
// ══════════════════════════════════════════════════════════════════════════════

/// **Stage 10c (2026-05-04)** repurposed W14 from `wpds-confirmed-ambiguity`
/// (which depended on `nfa_spillover_categories`) to `walker-fork-tight-margin`.
/// Symmetric to W04 (which fires on gap > 5.0 = near-deterministic):
/// W14 fires when the top-2 prediction-WFST actions for a dispatch token
/// have a primary-weight margin < `TIGHT_MARGIN_THRESHOLD` (= 0.1). At
/// runtime the Walker's `LexicographicWeight (primary, src_idx, rule_idx)`
/// lex-min decides the Fork winner; when the primary margin is near zero,
/// the resolution depends purely on `src_idx`/`rule_idx` tiebreaks — a
/// brittle, ordering-dependent outcome that grammar authors should be
/// aware of.
///
/// W14 reads only `prediction_wfsts` and `first_sets`.
pub(crate) fn lint_w14_wpds_confirmed_ambiguity(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    /// Margin under which Walker lex-min Fork resolution depends on
    /// `src_idx`/`rule_idx` tiebreaks rather than principled weight order.
    const TIGHT_MARGIN_THRESHOLD: f64 = 0.1;

    for (cat_name, wfst) in ctx.prediction_wfsts {
        let first_set = match ctx.first_sets.get(cat_name) {
            Some(fs) => fs,
            None => continue,
        };

        for token in first_set.sorted_tokens() {
            let actions = wfst.predict(&token);
            if actions.len() < 2 {
                continue;
            }
            let margin = actions[1].weight.value() - actions[0].weight.value();
            if margin < TIGHT_MARGIN_THRESHOLD {
                let top_label = actions[0].action.rule_label();
                let runner_label = actions[1].action.rule_label();
                diagnostics.push(LintDiagnostic {
                    id: DiagnosticId::W14,
                    name: "walker-fork-tight-margin",
                    severity: LintSeverity::Note,
                    category: Some(cat_name.clone()),
                    rule: None,
                    message: format!(
                        "category `{}`, token `{}`: top-2 actions (`{}` vs `{}`) have \
                         primary-weight margin {:.3} (Walker lex-min Fork resolution \
                         will be src_idx/rule_idx-dependent)",
                        cat_name, token, top_label, runner_label, margin,
                    ),
                    hint: Some(
                        "consider increasing weight specificity for one of the rules, \
                         or audit codegen ordering — current Fork resolution depends on \
                         rule_idx tiebreak rather than principled weight order"
                            .to_string(),
                    ),
                    grammar_name: Some(ctx.grammar_name.to_string()),
                    source_location: None,
                });
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// COMP-08: Grammar Refactoring Suggestions
// ══════════════════════════════════════════════════════════════════════════════

/// Emit Note-level suggestions for grammar restructuring based on WPDS analysis.
///
/// Heuristics from G33/G34/G35/G36:
/// - High fan-in AND fan-out (>5 each) → suggest splitting hub category
/// - Fan-in=1, ≤3 rules, fan-out=0 → suggest inlining (J03 candidate)
/// - SCC with >2 members → suggest cycle-breaking via intermediate category
/// - Single calling context → suggest moving rule to caller category
pub(crate) fn lint_comp08_refactoring_suggestions(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let analysis = match ctx.wpds_analysis {
        Some(a) => a,
        None => return,
    };

    let cg = &analysis.call_graph;

    // Hub detection: high fan-in AND fan-out
    for cat in &cg.categories {
        let fi = cg.fan_in.get(cat).copied().unwrap_or(0);
        let fo = cg.fan_out.get(cat).copied().unwrap_or(0);
        if fi > 5 && fo > 5 {
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::COMP08,
                name: "wpds-refactoring-suggestion",
                severity: LintSeverity::Note,
                category: Some(cat.clone()),
                rule: None,
                message: format!(
                    "category `{}` is a hub (fan-in={}, fan-out={}); \
                     consider splitting into smaller categories",
                    cat, fi, fo,
                ),
                hint: Some(
                    "hub categories can cause cascading ambiguity; splitting \
                     may improve dispatch determinism and parse performance"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }

    // Inline candidate: fan-in=1, ≤3 rules, fan-out=0
    for cat in &cg.categories {
        let fi = cg.fan_in.get(cat).copied().unwrap_or(0);
        let fo = cg.fan_out.get(cat).copied().unwrap_or(0);
        let rule_count = ctx.rules.iter().filter(|r| r.category == *cat).count();

        if fi == 1 && rule_count <= 3 && fo == 0 {
            // Find the sole caller
            let caller = cg
                .edges
                .iter()
                .find(|e| e.callee_cat == *cat)
                .map(|e| e.caller_cat.as_str())
                .unwrap_or("unknown");

            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::COMP08,
                name: "wpds-refactoring-suggestion",
                severity: LintSeverity::Note,
                category: Some(cat.clone()),
                rule: None,
                message: format!(
                    "category `{}` has 1 caller (`{}`), {} rules, no outgoing calls; \
                     consider inlining into `{}`",
                    cat, caller, rule_count, caller,
                ),
                hint: Some(
                    "inlining small leaf categories eliminates cross-category \
                     Push/Pop overhead in the WPDS and simplifies the call graph"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }

    // Large SCC: >2 members → suggest cycle-breaking
    for cycle in &analysis.cycles {
        if cycle.categories.len() > 2 {
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::COMP08,
                name: "wpds-refactoring-suggestion",
                severity: LintSeverity::Note,
                category: None,
                rule: None,
                message: format!(
                    "mutual recursion cycle with {} categories: {{{}}}; \
                     consider introducing an intermediate category to break the cycle",
                    cycle.categories.len(),
                    cycle.categories.join(", "),
                ),
                hint: Some(
                    "large mutual-recursion cycles increase WPDS saturation time \
                     and can obscure dead-rule detection"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// W16: WPDS Weight Inversion Across Contexts
// ══════════════════════════════════════════════════════════════════════════════

/// Warning when WPDS-derived optimal weight order contradicts WFST dispatch weight.
///
/// If rule A has lower WFST weight (higher priority) than rule B, but WPDS
/// shows B is more reachable across stack contexts, this is a weight inversion.
pub(crate) fn lint_w16_wpds_weight_inversion(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let analysis = match ctx.wpds_analysis {
        Some(a) => a,
        None => return,
    };

    for (cat, wfst) in ctx.prediction_wfsts {
        // Get WPDS weight for this category
        let wpds_cat_weight = analysis.category_weights.get(cat).copied();
        if wpds_cat_weight.is_none() {
            continue;
        }

        // Check pairs of actions for inversions: WFST says A < B but WPDS says B < A
        // We compare using the WPDS calling context weights for each rule's category.
        // If the rule's own category has a lower WPDS weight than other rules' categories,
        // but WFST gives it a higher weight, that's an inversion.
        for i in 0..wfst.actions.len() {
            for j in (i + 1)..wfst.actions.len() {
                let a = &wfst.actions[i];
                let b = &wfst.actions[j];

                // Only compare if they share a category (same dispatch context)
                let a_label = a.action.rule_label();
                let b_label = b.action.rule_label();

                // Check if WFST weight order disagrees with WPDS weight
                let wfst_a_better = a.weight.value() < b.weight.value();
                let wpds_a_weight = analysis
                    .category_weights
                    .get(cat)
                    .copied()
                    .unwrap_or(f64::INFINITY);
                let wpds_b_weight = wpds_a_weight; // Same category, but we need per-rule weights

                // Per-rule WPDS weight check: use calling contexts if available
                let a_context_count = analysis
                    .calling_contexts
                    .get(cat)
                    .map(|ctxs| ctxs.len())
                    .unwrap_or(0);

                // Only flag inversions when we have meaningful weight differences
                if wfst_a_better
                    && a.weight.value() + 1.0 < b.weight.value()
                    && a_context_count > 0
                    && wpds_a_weight > wpds_b_weight + 0.5
                {
                    diagnostics.push(LintDiagnostic {
                        id: DiagnosticId::W16,
                        name: "wpds-weight-inversion",
                        severity: LintSeverity::Warning,
                        category: Some(cat.clone()),
                        rule: Some(a_label.clone()),
                        message: format!(
                            "rule `{}` has WFST weight {:.1} but WPDS weight {:.1} — \
                             consider reordering (WPDS suggests `{}` is more reachable)",
                            a_label,
                            a.weight.value(),
                            wpds_a_weight,
                            b_label,
                        ),
                        hint: Some(
                            "WPDS stack-aware analysis suggests a different optimal dispatch \
                             order than the WFST prediction weights"
                                .to_string(),
                        ),
                        grammar_name: Some(ctx.grammar_name.to_string()),
                        source_location: None,
                    });
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// R01: Empty Sync Set
// ══════════════════════════════════════════════════════════════════════════════

pub(crate) fn lint_r01_empty_sync_set(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    for rwfst in ctx.recovery_wfsts {
        if rwfst.sync_tokens().is_empty() {
            // Suggest good sync token candidates from the decision tree
            let suggestion = suggest_sync_tokens_from_trie(ctx, rwfst.category());
            let hint = if suggestion.is_empty() {
                "add structural delimiters or ensure the category has FOLLOW set tokens".to_string()
            } else {
                format!(
                    "add structural delimiters or FOLLOW set tokens. \
                     Decision tree suggests shallow tokens: [{}]",
                    suggestion,
                )
            };

            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::R01,
                name: "empty-sync-set",
                severity: LintSeverity::Warning,
                category: Some(rwfst.category().to_string()),
                rule: None,
                message: format!(
                    "category `{}` has no sync tokens — recovery always skips to EOF",
                    rwfst.category(),
                ),
                hint: Some(hint),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

/// Suggest sync token candidates based on trie depth (shallower = better recovery target).
fn suggest_sync_tokens_from_trie(ctx: &LintContext, category: &str) -> String {
    let tree = match ctx.decision_trees.get(category) {
        Some(t) => t,
        None => return String::new(),
    };
    let dispatch_tokens = tree.dispatch_tokens(ctx.token_id_map);
    // Tokens at depth 0 (direct root children) are excellent sync targets
    let mut shallow_tokens: Vec<String> = Vec::new();
    for token_variant in &dispatch_tokens {
        let strategy = tree.dispatch_strategy(token_variant, ctx.token_id_map);
        match strategy {
            crate::decision_tree::DispatchStrategy::Singleton { .. } => {
                shallow_tokens.push(token_variant.clone());
            },
            _ => {},
        }
    }
    shallow_tokens.sort();
    shallow_tokens.truncate(5);
    shallow_tokens.join(", ")
}

// ══════════════════════════════════════════════════════════════════════════════
// R02: Sparse Recovery
// ══════════════════════════════════════════════════════════════════════════════

pub(crate) fn lint_r02_sparse_recovery(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    for rwfst in ctx.recovery_wfsts {
        let count = rwfst.sync_tokens().len();
        if count > 0 && count < 2 {
            // Assess sync token quality via decision tree depth
            let quality_notes = assess_sync_quality(ctx, rwfst);

            let hint = if quality_notes.is_empty() {
                "add more structural delimiters to improve error recovery quality".to_string()
            } else {
                format!(
                    "add more structural delimiters to improve error recovery quality. {}",
                    quality_notes,
                )
            };

            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::R02,
                name: "sparse-recovery",
                severity: LintSeverity::Note,
                category: Some(rwfst.category().to_string()),
                rule: None,
                message: format!(
                    "category `{}` has only {} sync token — limited recovery options",
                    rwfst.category(),
                    count,
                ),
                hint: Some(hint),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

/// Assess sync token quality via decision tree depth.
fn assess_sync_quality(ctx: &LintContext, rwfst: &crate::recovery::RecoveryWfst) -> String {
    let tree = match ctx.decision_trees.get(rwfst.category()) {
        Some(t) => t,
        None => return String::new(),
    };

    let mut quality_parts = Vec::new();
    for &token_id in rwfst.sync_tokens() {
        let token_name = match rwfst.token_name(token_id) {
            Some(n) => n.to_string(),
            None => continue,
        };
        let strategy = tree.dispatch_strategy(&token_name, ctx.token_id_map);
        let quality = match &strategy {
            crate::decision_tree::DispatchStrategy::Singleton { .. } => "excellent (depth 0)",
            crate::decision_tree::DispatchStrategy::DisjointSuffix {
                shared_prefix_len, ..
            } => {
                if *shared_prefix_len <= 1 {
                    "good (shallow)"
                } else {
                    "fair (deep prefix)"
                }
            },
            crate::decision_tree::DispatchStrategy::AmbiguousFanout {
                shared_prefix_len, ..
            } => {
                if *shared_prefix_len == 0 {
                    "fair (ambiguous at root)"
                } else {
                    "poor (deep + ambiguous)"
                }
            },
            crate::decision_tree::DispatchStrategy::NotPresent => "N/A (not in trie)",
        };
        quality_parts.push(format!("`{}`: {}", token_name, quality));
    }
    if quality_parts.is_empty() {
        String::new()
    } else {
        format!("Sync token quality: {}", quality_parts.join(", "))
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// R05: Missing Bracket Sync
// ══════════════════════════════════════════════════════════════════════════════

pub(crate) fn lint_r05_missing_bracket_sync(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let bracket_pairs = [("(", "RParen"), ("{", "RBrace"), ("[", "RBracket")];

    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        // Collect terminals used by rules in this category
        let mut cat_terminals: HashSet<String> = HashSet::new();
        for (_, category, syntax) in ctx.all_syntax {
            if category == cat {
                for t in collect_terminals_flat(syntax) {
                    cat_terminals.insert(t);
                }
            }
        }

        // Find the recovery WFST for this category
        let rwfst = match ctx.recovery_wfsts.iter().find(|r| r.category() == cat) {
            Some(r) => r,
            None => continue,
        };

        for &(open, close_variant) in &bracket_pairs {
            if cat_terminals.contains(open) {
                // Check if closing bracket is in sync set
                // The sync set uses TokenIds — we need to check by variant name
                // The TokenIdMap resolves names. Check if the closing variant
                // appears in any sync token name.
                let has_close_sync = rwfst.sync_tokens().iter().any(|&id| {
                    rwfst
                        .token_name(id)
                        .map_or(false, |name| name == close_variant)
                });

                if !has_close_sync {
                    diagnostics.push(LintDiagnostic {
                        id: DiagnosticId::R05,
                        name: "missing-bracket-sync",
                        severity: LintSeverity::Warning,
                        category: Some(cat.clone()),
                        rule: None,
                        message: format!(
                            "category `{}` uses `{}` delimiter but closing `{}` is \
                             absent from sync set",
                            cat, open, close_variant,
                        ),
                        hint: Some(
                            "ensure the closing bracket is in the category's FOLLOW set \
                             or structural delimiters"
                                .to_string(),
                        ),
                        grammar_name: Some(ctx.grammar_name.to_string()),
                        source_location: None,
                    });
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// R06: Inverted Recovery Costs
// ══════════════════════════════════════════════════════════════════════════════

pub(crate) fn lint_r06_inverted_recovery_costs(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let config = ctx.recovery_config;

    // Expected hierarchy: skip < delete < swap < substitute < insert
    let expected_order = [
        ("skip_per_token", config.skip_per_token),
        ("delete_cost", config.delete_cost),
        ("swap_cost", config.swap_cost),
        ("substitute_cost", config.substitute_cost),
        ("insert_cost", config.insert_cost),
    ];

    for i in 0..expected_order.len() {
        for j in (i + 1)..expected_order.len() {
            let (name_i, cost_i) = expected_order[i];
            let (name_j, cost_j) = expected_order[j];

            if cost_i > cost_j {
                diagnostics.push(LintDiagnostic {
                    id: DiagnosticId::R06,
                    name: "inverted-recovery-costs",
                    severity: LintSeverity::Warning,
                    category: None,
                    rule: None,
                    message: format!(
                        "RecoveryConfig cost hierarchy violated: {} ({:.2}) > {} ({:.2})",
                        name_i, cost_i, name_j, cost_j,
                    ),
                    hint: Some(format!(
                        "expected hierarchy: skip < delete < swap < substitute < insert; \
                         adjust {} or {} to restore the hierarchy",
                        name_i, name_j,
                    )),
                    grammar_name: Some(ctx.grammar_name.to_string()),
                    source_location: None,
                });
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// R07: Transposition Candidate
// ══════════════════════════════════════════════════════════════════════════════

pub(crate) fn lint_r07_transposition_candidate(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    // Collect all unique operator terminals from the grammar
    let mut all_operators: Vec<String> = Vec::new();
    for (_, _, syntax) in ctx.all_syntax {
        for item in syntax {
            if let SyntaxItemSpec::Terminal(t) = item {
                // Skip structural delimiters
                if !matches!(t.as_str(), "(" | ")" | "{" | "}" | "[" | "]" | "," | ";") {
                    all_operators.push(t.clone());
                }
            }
        }
    }
    all_operators.sort();
    all_operators.dedup();

    // Collect all pairs with Levenshtein distance = 1 into a single list
    let mut pairs: Vec<(String, String)> = Vec::new();
    for i in 0..all_operators.len() {
        for j in (i + 1)..all_operators.len() {
            let a = &all_operators[i];
            let b = &all_operators[j];
            if char_edit_distance_is_one(a, b) {
                pairs.push((a.clone(), b.clone()));
            }
        }
    }

    if pairs.is_empty() {
        return;
    }

    // Emit a single summary note instead of O(n²) individual notes
    let total = pairs.len();
    let max_samples = 8;
    let samples: Vec<String> = pairs
        .iter()
        .take(max_samples)
        .map(|(a, b)| format!("`{}`\u{2194}`{}`", a, b))
        .collect();

    let mut message = format!(
        "{} operator pair(s) differ by 1 character (SwapTokens repair candidates): {}",
        total,
        samples.join(", "),
    );
    if total > max_samples {
        message.push_str(&format!(" ({} more)", total - max_samples));
    }

    diagnostics.push(LintDiagnostic {
        id: DiagnosticId::R07,
        name: "transposition-candidate",
        severity: LintSeverity::Note,
        category: None,
        rule: None,
        message,
        hint: Some(
            "the error recovery system can detect and fix common \
             typos between these operators via SwapTokens"
                .to_string(),
        ),
        grammar_name: Some(ctx.grammar_name.to_string()),
        source_location: None,
    });
}

/// Check if two strings have Levenshtein distance exactly 1.
pub(crate) fn char_edit_distance_is_one(a: &str, b: &str) -> bool {
    let a_chars: Vec<char> = a.chars().collect();
    let b_chars: Vec<char> = b.chars().collect();
    let len_a = a_chars.len();
    let len_b = b_chars.len();

    match (len_a as isize) - (len_b as isize) {
        0 => {
            // Same length: exactly one substitution
            let mut diffs = 0;
            for i in 0..len_a {
                if a_chars[i] != b_chars[i] {
                    diffs += 1;
                    if diffs > 1 {
                        return false;
                    }
                }
            }
            diffs == 1
        },
        1 => {
            // a is one longer: one insertion in a (= one deletion from a to get b)
            one_insertion_away(&a_chars, &b_chars)
        },
        -1 => {
            // b is one longer: one insertion in b
            one_insertion_away(&b_chars, &a_chars)
        },
        _ => false,
    }
}

/// Check if `longer` can become `shorter` by removing exactly one character.
fn one_insertion_away(longer: &[char], shorter: &[char]) -> bool {
    let mut i = 0;
    let mut j = 0;
    let mut skipped = false;
    while i < longer.len() && j < shorter.len() {
        if longer[i] != shorter[j] {
            if skipped {
                return false;
            }
            skipped = true;
            i += 1;
        } else {
            i += 1;
            j += 1;
        }
    }
    true
}

// ══════════════════════════════════════════════════════════════════════════════
// C01: Cast Cycle
// ══════════════════════════════════════════════════════════════════════════════

pub(crate) fn lint_c01_cast_cycle(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    // Build adjacency list from cast rules
    let mut adjacency: HashMap<&str, Vec<&str>> = HashMap::new();
    for cast in ctx.cast_rules {
        adjacency
            .entry(cast.source_category.as_str())
            .or_default()
            .push(cast.target_category.as_str());
    }

    // DFS with coloring: White (unvisited), Gray (in stack), Black (done)
    #[derive(Clone, Copy, PartialEq)]
    enum Color {
        White,
        Gray,
        Black,
    }

    let category_names: Vec<&str> = ctx.categories.iter().map(|c| c.name.as_str()).collect();
    let mut color: HashMap<&str, Color> =
        category_names.iter().map(|&c| (c, Color::White)).collect();
    let mut path: Vec<&str> = Vec::new();

    fn dfs<'a>(
        node: &'a str,
        adjacency: &HashMap<&'a str, Vec<&'a str>>,
        color: &mut HashMap<&'a str, Color>,
        path: &mut Vec<&'a str>,
        diagnostics: &mut Vec<LintDiagnostic>,
        grammar_name: &str,
    ) {
        color.insert(node, Color::Gray);
        path.push(node);

        if let Some(neighbors) = adjacency.get(node) {
            for &next in neighbors {
                match color.get(next) {
                    Some(Color::Gray) => {
                        // Found a cycle — extract the cycle path
                        let cycle_start = path.iter().position(|&n| n == next).unwrap_or(0);
                        let mut cycle_path: Vec<&str> = path[cycle_start..].to_vec();
                        cycle_path.push(next);
                        let cycle_str = cycle_path.join(" -> ");

                        diagnostics.push(LintDiagnostic {
                            id: DiagnosticId::C01,
                            name: "cast-cycle",
                            severity: LintSeverity::Error,
                            category: None,
                            rule: None,
                            message: format!("cast cycle detected: {}", cycle_str),
                            hint: Some(
                                "break the cycle by removing one cast direction".to_string(),
                            ),
                            grammar_name: Some(grammar_name.to_string()),
                            source_location: None,
                        });
                    },
                    Some(Color::White) | None => {
                        dfs(next, adjacency, color, path, diagnostics, grammar_name);
                    },
                    Some(Color::Black) => {
                        // Already fully explored, no cycle through this node
                    },
                }
            }
        }

        path.pop();
        color.insert(node, Color::Black);
    }

    for &cat in &category_names {
        if color.get(cat) == Some(&Color::White) {
            dfs(cat, &adjacency, &mut color, &mut path, diagnostics, ctx.grammar_name);
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// C02: Transitive Cast Redundancy
// ══════════════════════════════════════════════════════════════════════════════

pub(crate) fn lint_c02_transitive_cast_redundancy(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    // Build adjacency list
    let mut adjacency: HashMap<&str, HashSet<&str>> = HashMap::new();
    for cast in ctx.cast_rules {
        adjacency
            .entry(cast.source_category.as_str())
            .or_default()
            .insert(cast.target_category.as_str());
    }

    let category_names: Vec<&str> = ctx.categories.iter().map(|c| c.name.as_str()).collect();

    // Compute transitive closure via Floyd-Warshall-style approach
    let mut reachable: HashMap<(&str, &str), bool> = HashMap::new();
    for &src in &category_names {
        for &dst in &category_names {
            reachable.insert(
                (src, dst),
                adjacency
                    .get(src)
                    .map_or(false, |neighbors| neighbors.contains(dst)),
            );
        }
    }

    for &mid in &category_names {
        for &src in &category_names {
            for &dst in &category_names {
                if reachable[&(src, mid)] && reachable[&(mid, dst)] {
                    reachable.insert((src, dst), true);
                }
            }
        }
    }

    // Check for direct cast A→C alongside transitive A→...→C (path length ≥ 2)
    for cast in ctx.cast_rules {
        let src = cast.source_category.as_str();
        let dst = cast.target_category.as_str();

        // Is there a path of length ≥ 2 from src to dst?
        let has_indirect = adjacency.get(src).map_or(false, |neighbors| {
            neighbors
                .iter()
                .any(|&mid| mid != dst && reachable.get(&(mid, dst)).copied().unwrap_or(false))
        });

        if has_indirect {
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::C02,
                name: "transitive-cast-redundancy",
                severity: LintSeverity::Note,
                category: None,
                rule: Some(cast.label.clone()),
                message: format!(
                    "direct cast `{}` → `{}` (rule `{}`) is redundant — a transitive \
                     path already exists",
                    src, dst, cast.label,
                ),
                hint: Some(
                    "the transitive path handles this cast — the direct rule may be \
                     intentional for performance or explicitness"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// C04: Wide Cross Overlap
// ══════════════════════════════════════════════════════════════════════════════

pub(crate) fn lint_c04_wide_cross_overlap(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for i in 0..category_names.len() {
        for j in (i + 1)..category_names.len() {
            let cat_a = &category_names[i];
            let cat_b = &category_names[j];

            let first_a = match ctx.first_sets.get(cat_a) {
                Some(fs) => fs,
                None => continue,
            };
            let first_b = match ctx.first_sets.get(cat_b) {
                Some(fs) => fs,
                None => continue,
            };

            let overlap = first_a.intersection(first_b);
            let overlap_count = overlap.tokens.len();

            if first_a.tokens.is_empty() || first_b.tokens.is_empty() {
                continue;
            }

            // Check overlap relative to the smaller FIRST set
            let min_size = first_a.tokens.len().min(first_b.tokens.len());
            let ratio = overlap_count as f64 / min_size as f64;

            if ratio >= 0.8 && overlap_count >= 2 {
                // Build token-level breakdown using decision trees
                let mut token_breakdown: Vec<String> = Vec::new();
                for token in overlap.sorted_tokens() {
                    let rules_a = tree_rules_for_token(ctx, cat_a, &token);
                    let rules_b = tree_rules_for_token(ctx, cat_b, &token);
                    if !rules_a.is_empty() || !rules_b.is_empty() {
                        token_breakdown.push(format!(
                            "`{}` ({}:{} vs {}:{})",
                            token,
                            cat_a,
                            if rules_a.is_empty() {
                                "cast".to_string()
                            } else {
                                rules_a.join("/")
                            },
                            cat_b,
                            if rules_b.is_empty() {
                                "cast".to_string()
                            } else {
                                rules_b.join("/")
                            },
                        ));
                    }
                }

                let message =
                    if token_breakdown.is_empty() {
                        format!(
                            "cross-category overlap between `{}` and `{}`: {}/{} tokens ({:.0}%) \
                         — mostly save/restore dispatch",
                            cat_a,
                            cat_b,
                            overlap_count,
                            min_size,
                            ratio * 100.0,
                        )
                    } else {
                        format!(
                        "cross-category overlap between `{}` and `{}`: {}/{} tokens ({:.0}%): [{}]",
                        cat_a, cat_b, overlap_count, min_size, ratio * 100.0,
                        token_breakdown.join(", "),
                    )
                    };

                diagnostics.push(LintDiagnostic {
                    id: DiagnosticId::C04,
                    name: "wide-cross-overlap",
                    severity: LintSeverity::Note,
                    category: None,
                    rule: None,
                    message,
                    hint: Some(
                        "high FIRST-set overlap means many tokens need save/restore \
                         backtracking in cross-category dispatch"
                            .to_string(),
                    ),
                    grammar_name: Some(ctx.grammar_name.to_string()),
                    source_location: None,
                });
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Stage 10c (2026-05-04): P02 (high-nfa-spillover) DELETED.
// Message described per-cat thread-local bindings (NFA_PREFIX_SPILL_<CAT>,
// NFA_FORCED_PREFIX_<CAT>, NFA_PRIMARY_WEIGHT_<CAT>) that Stage 10b already
// removed from `language.rs:1840-1932`. With those TLS bindings gone, the
// hint about reducing categories with NFA spillover refers to overhead that
// no longer exists. Lint deleted with no replacement.
// ══════════════════════════════════════════════════════════════════════════════

// ══════════════════════════════════════════════════════════════════════════════
// P03: Deep Cast Nesting
// ══════════════════════════════════════════════════════════════════════════════

pub(crate) fn lint_p03_deep_cast_nesting(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    // Build cast DAG adjacency list
    let mut adjacency: HashMap<&str, Vec<&str>> = HashMap::new();
    for cast in ctx.cast_rules {
        adjacency
            .entry(cast.source_category.as_str())
            .or_default()
            .push(cast.target_category.as_str());
    }

    let category_names: Vec<&str> = ctx.categories.iter().map(|c| c.name.as_str()).collect();

    // Topological sort + DP to find longest path (only valid for DAGs — C01 catches cycles)
    let mut longest_path: HashMap<&str, usize> = HashMap::new();

    fn dp_longest<'a>(
        node: &'a str,
        adjacency: &HashMap<&'a str, Vec<&'a str>>,
        memo: &mut HashMap<&'a str, usize>,
        visited: &mut HashSet<&'a str>,
    ) -> usize {
        if let Some(&cached) = memo.get(node) {
            return cached;
        }
        // Cycle guard (C01 should catch this, but be defensive)
        if !visited.insert(node) {
            return 0;
        }

        let max_child = adjacency.get(node).map_or(0, |neighbors| {
            neighbors
                .iter()
                .map(|&next| dp_longest(next, adjacency, memo, visited) + 1)
                .max()
                .unwrap_or(0)
        });

        visited.remove(node);
        memo.insert(node, max_child);
        max_child
    }

    let mut visited = HashSet::new();
    for &cat in &category_names {
        dp_longest(cat, &adjacency, &mut longest_path, &mut visited);
    }

    let max_depth = longest_path.values().copied().max().unwrap_or(0);
    if max_depth > 3 {
        let deepest = longest_path
            .iter()
            .filter(|(_, &d)| d == max_depth)
            .map(|(&name, _)| name)
            .collect::<Vec<_>>();

        // Modulate severity: tiny grammars (<10 categories) → Note, larger → Warning
        let severity = if ctx
            .grammar_profile
            .map_or(false, |p| p.category_count >= 10)
        {
            LintSeverity::Warning
        } else {
            LintSeverity::Note
        };
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::P03,
            name: "deep-cast-nesting",
            severity,
            category: None,
            rule: None,
            message: format!(
                "cast chain depth is {} (starting from [{}]) — each level adds \
                 Box::new() wrapper overhead",
                max_depth,
                deepest.join(", "),
            ),
            hint: Some(
                "consider adding direct cast rules to bypass intermediate categories".to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// P04: Many Alternatives
// ══════════════════════════════════════════════════════════════════════════════

pub(crate) fn lint_p04_many_alternatives(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let category_names: Vec<String> = ctx.categories.iter().map(|c| c.name.clone()).collect();

    for cat in &category_names {
        if let Some(wfst) = ctx.prediction_wfsts.get(cat.as_str()) {
            if let Some(first_set) = ctx.first_sets.get(cat) {
                for token in first_set.sorted_tokens() {
                    let actions = wfst.predict(&token);
                    if actions.len() > 4 {
                        // Modulate severity: tiny grammars (<10 categories) → Note, larger → Warning
                        let severity = if ctx
                            .grammar_profile
                            .map_or(false, |p| p.category_count >= 10)
                        {
                            LintSeverity::Warning
                        } else {
                            LintSeverity::Note
                        };
                        diagnostics.push(LintDiagnostic {
                            id: DiagnosticId::P04,
                            name: "many-alternatives",
                            severity,
                            category: Some(cat.clone()),
                            rule: None,
                            message: format!(
                                "token `{}` dispatches to {} rules in category `{}` — \
                                 save/restore overhead",
                                token,
                                actions.len(),
                                cat,
                            ),
                            hint: Some(
                                "reduce prefix ambiguity or use beam pruning to limit \
                                 alternatives"
                                    .to_string(),
                            ),
                            grammar_name: Some(ctx.grammar_name.to_string()),
                            source_location: None,
                        });
                    }
                }
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Composition-specific lints (X01–X05)
// ══════════════════════════════════════════════════════════════════════════════

/// Pre/post composition data needed for composition-specific lints.
///
/// Captures the FIRST sets, prediction WFSTs, dead rules, and terminal semantics
/// for two grammars (A and B) before and after composition (merged). The
/// `shared_categories` field lists categories that exist in both source grammars.
pub struct CompositionLintContext<'a> {
    /// FIRST sets from grammar A (before merge).
    pub first_sets_a: &'a HashMap<String, FirstSet>,
    /// FIRST sets from grammar B (before merge).
    pub first_sets_b: &'a HashMap<String, FirstSet>,
    /// FIRST sets from the merged grammar.
    pub first_sets_merged: &'a HashMap<String, FirstSet>,
    /// Prediction WFSTs from grammar A.
    pub prediction_wfsts_a: &'a HashMap<String, PredictionWfst>,
    /// Prediction WFSTs from grammar B.
    pub prediction_wfsts_b: &'a HashMap<String, PredictionWfst>,
    /// Categories present in both grammars.
    pub shared_categories: &'a [String],
    /// Dead rules in grammar A (rule labels).
    pub dead_rules_a: &'a HashSet<String>,
    /// Dead rules in grammar B (rule labels).
    pub dead_rules_b: &'a HashSet<String>,
    /// Dead rules in the merged grammar (rule labels).
    pub dead_rules_merged: &'a HashSet<String>,
    /// Rules from grammar A.
    pub rules_a: &'a [RuleInfo],
    /// Rules from grammar B.
    pub rules_b: &'a [RuleInfo],
    /// Terminal semantics in grammar A: terminal name -> [(category, semantic role)].
    pub terminal_semantics_a: &'a HashMap<String, Vec<(String, String)>>,
    /// Terminal semantics in grammar B: terminal name -> [(category, semantic role)].
    pub terminal_semantics_b: &'a HashMap<String, Vec<(String, String)>>,
}

/// Run all composition-specific lints and return structured diagnostics.
///
/// These lints detect issues that arise when two grammars are composed
/// (merged). They compare the pre-composition state of each source grammar
/// against the merged result to detect ambiguity introduction, priority
/// shadowing, newly-dead rules, broken cast chains, and terminal collisions.
pub fn run_composition_lints(
    base_ctx: &LintContext,
    comp_ctx: &CompositionLintContext,
) -> Vec<LintDiagnostic> {
    let mut diagnostics = Vec::new();

    lint_x01_composition_ambiguity_introduction(base_ctx, comp_ctx, &mut diagnostics);
    lint_x02_composition_priority_shadowing(base_ctx, comp_ctx, &mut diagnostics);
    lint_x03_composition_dead_rule_creation(base_ctx, comp_ctx, &mut diagnostics);
    lint_x04_composition_cast_chain_break(base_ctx, comp_ctx, &mut diagnostics);
    lint_x05_composition_terminal_collision(base_ctx, comp_ctx, &mut diagnostics);

    diagnostics
}

// ──────────────────────────────────────────────────────────────────────────────
// X01: Composition Ambiguity Introduction
// ──────────────────────────────────────────────────────────────────────────────

/// Detects FIRST set ambiguity growth after merge for shared categories.
///
/// Two sources of composition-introduced ambiguity are detected:
///
/// 1. **New FIRST set overlap:** Tokens that appear in the merged FIRST set
///    but not in the union of A's and B's FIRST sets. These represent new
///    derivation paths created by composition (e.g., through cross-category
///    casts that only exist in the merged grammar).
///
/// 2. **Pre-existing overlap amplification:** The FIRST set overlap between
///    A and B (tokens in both) is checked against the merged FIRST set. If
///    the merged set contains the same overlapping tokens plus additional
///    tokens from new derivation paths, the ambiguity has grown.
pub(crate) fn lint_x01_composition_ambiguity_introduction(
    base_ctx: &LintContext,
    comp_ctx: &CompositionLintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    for cat in comp_ctx.shared_categories {
        let first_a = match comp_ctx.first_sets_a.get(cat) {
            Some(fs) => fs,
            None => continue,
        };
        let first_b = match comp_ctx.first_sets_b.get(cat) {
            Some(fs) => fs,
            None => continue,
        };
        let first_merged = match comp_ctx.first_sets_merged.get(cat) {
            Some(fs) => fs,
            None => continue,
        };

        // Pre-composition overlap: tokens in BOTH A and B for this category.
        let pre_overlap = first_a.intersection(first_b);

        // Union of A's and B's FIRST sets.
        let mut pre_union = first_a.clone();
        pre_union.union(first_b);

        // Tokens in the merged FIRST set that are NOT in the pre-composition
        // union represent new derivation paths introduced by the composition.
        let new_tokens: Vec<&str> = first_merged
            .tokens
            .iter()
            .filter(|t| !pre_union.contains(t))
            .map(|s| s.as_str())
            .collect();

        // Also check: did the pre-existing overlap (tokens in both A and B)
        // grow in the merged result? This can happen when composition adds
        // new nonterminal edges that make previously non-overlapping tokens
        // now reachable from both source grammars.
        //
        // Merged overlap = tokens in merged that appear in BOTH the original
        // A first set AND the original B first set. Since A and B are fixed
        // source sets, this is bounded by |A ∩ B|. However, the merged set
        // may also have tokens that create NEW overlap between different
        // rules within the composed grammar. We detect this via new_tokens.

        let pre_overlap_count = pre_overlap.tokens.len();

        if !new_tokens.is_empty() {
            let mut sorted_new = new_tokens;
            sorted_new.sort_unstable();

            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::X01,
                name: "composition-ambiguity-introduction",
                severity: LintSeverity::Warning,
                category: Some(cat.clone()),
                rule: None,
                message: format!(
                    "composition introduces {} new FIRST set token(s) in category `{}` \
                     not in either source grammar: [{}] \
                     (pre-composition overlap: {} token(s))",
                    sorted_new.len(),
                    cat,
                    sorted_new.join(", "),
                    pre_overlap_count,
                ),
                hint: Some(
                    "add unique prefix tokens to disambiguate; \
                     WFST auto-assigns weights by declaration order when prefixes overlap"
                        .to_string(),
                ),
                grammar_name: Some(base_ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

// ──────────────────────────────────────────────────────────────────────────────
// X02: Composition Priority Shadowing
// ──────────────────────────────────────────────────────────────────────────────

/// Detects when a rule from grammar A is shadowed (has lower priority) by a
/// rule from grammar B for the same token in a shared category.
///
/// For each shared category, queries the prediction WFSTs from A and B for
/// each token in the merged FIRST set. If both A and B have predictions for
/// the same token and A's best weight is strictly greater (worse) than B's
/// best weight, A's rule is shadowed by B's.
pub(crate) fn lint_x02_composition_priority_shadowing(
    base_ctx: &LintContext,
    comp_ctx: &CompositionLintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    for cat in comp_ctx.shared_categories {
        let wfst_a = match comp_ctx.prediction_wfsts_a.get(cat) {
            Some(w) => w,
            None => continue,
        };
        let wfst_b = match comp_ctx.prediction_wfsts_b.get(cat) {
            Some(w) => w,
            None => continue,
        };

        // Collect all tokens from both FIRST sets for this category
        let mut all_tokens: HashSet<&str> = HashSet::new();
        if let Some(fs_a) = comp_ctx.first_sets_a.get(cat) {
            all_tokens.extend(fs_a.tokens.iter().map(|s| s.as_str()));
        }
        if let Some(fs_b) = comp_ctx.first_sets_b.get(cat) {
            all_tokens.extend(fs_b.tokens.iter().map(|s| s.as_str()));
        }

        let mut sorted_tokens: Vec<&str> = all_tokens.into_iter().collect();
        sorted_tokens.sort_unstable();

        for token in sorted_tokens {
            let actions_a = wfst_a.predict(token);
            let actions_b = wfst_b.predict(token);

            if let (Some(best_a), Some(best_b)) = (actions_a.first(), actions_b.first()) {
                // A is shadowed by B: A's best weight is strictly worse (higher)
                if best_a.weight > best_b.weight {
                    diagnostics.push(LintDiagnostic {
                        id: DiagnosticId::X02,
                        name: "composition-priority-shadowing",
                        severity: LintSeverity::Warning,
                        category: Some(cat.clone()),
                        rule: Some(best_a.action.rule_label()),
                        message: format!(
                            "rule `{}` from grammar A is shadowed by `{}` from grammar B \
                             for token `{}` in category `{}` \
                             (weight {:.3} vs {:.3})",
                            best_a.action.rule_label(),
                            best_b.action.rule_label(),
                            token,
                            cat,
                            best_a.weight.value(),
                            best_b.weight.value(),
                        ),
                        hint: Some(
                            "rename rules or reorder declarations to avoid unintended \
                             priority override (WFST auto-assigns weights by declaration order)"
                                .to_string(),
                        ),
                        grammar_name: Some(base_ctx.grammar_name.to_string()),
                        source_location: None,
                    });
                }
            }
        }
    }
}

// ──────────────────────────────────────────────────────────────────────────────
// X03: Composition Dead Rule Creation
// ──────────────────────────────────────────────────────────────────────────────

/// Detects rules that were live in their source grammar but became dead
/// after composition.
///
/// Computes `dead_rules_merged \ (dead_rules_a ∪ dead_rules_b)` — rules that
/// are dead in the merged grammar but were NOT dead in either source. These
/// represent rules that the merge rendered unreachable.
pub(crate) fn lint_x03_composition_dead_rule_creation(
    base_ctx: &LintContext,
    comp_ctx: &CompositionLintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    // Rules dead in merged but not dead in either source
    let pre_dead: HashSet<&String> = comp_ctx
        .dead_rules_a
        .iter()
        .chain(comp_ctx.dead_rules_b.iter())
        .collect();

    let mut newly_dead: Vec<&String> = comp_ctx
        .dead_rules_merged
        .iter()
        .filter(|r| !pre_dead.contains(r))
        .collect();

    // Sort for deterministic output
    newly_dead.sort();

    for rule_label in newly_dead {
        // Determine which source grammar the rule came from
        let source_grammar = if comp_ctx.rules_a.iter().any(|r| r.label == *rule_label) {
            "A"
        } else if comp_ctx.rules_b.iter().any(|r| r.label == *rule_label) {
            "B"
        } else {
            "unknown"
        };

        // Find the category for this rule
        let category = comp_ctx
            .rules_a
            .iter()
            .chain(comp_ctx.rules_b.iter())
            .find(|r| r.label == *rule_label)
            .map(|r| r.category.clone());

        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::X03,
            name: "composition-dead-rule-creation",
            severity: LintSeverity::Warning,
            category: category.clone(),
            rule: Some(rule_label.clone()),
            message: format!(
                "rule `{}` was live in grammar {} but became dead after composition{}",
                rule_label,
                source_grammar,
                category
                    .as_ref()
                    .map(|c| format!(" (category `{}`)", c))
                    .unwrap_or_default(),
            ),
            hint: Some(
                "the composed grammar may have a higher-priority rule that shadows \
                 this one — verify intent or adjust weights"
                    .to_string(),
            ),
            grammar_name: Some(base_ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ──────────────────────────────────────────────────────────────────────────────
// X04: Composition Cast Chain Break
// ──────────────────────────────────────────────────────────────────────────────

/// Detects cast chains that exist in a source grammar but are broken after
/// composition.
///
/// A cast chain is a path A -> B -> C -> ... in the cast rule graph. If
/// merging removes or overrides an intermediate cast, the chain breaks.
/// This lint checks that all cast chains present in base_ctx.cast_rules
/// can still be traversed in the merged grammar (using the same cast_rules
/// in base_ctx, which represents the merged state).
///
/// The check verifies that for every pair of categories (src, dst) reachable
/// via cast chains in either source grammar, the same reachability holds in
/// the merged cast graph.
pub(crate) fn lint_x04_composition_cast_chain_break(
    base_ctx: &LintContext,
    comp_ctx: &CompositionLintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    /// Compute reachability closure from a set of cast rules.
    fn reachability(cast_rules: &[CastRule]) -> HashSet<(String, String)> {
        // Build adjacency list
        let mut adjacency: HashMap<&str, HashSet<&str>> = HashMap::new();
        for cast in cast_rules {
            adjacency
                .entry(cast.source_category.as_str())
                .or_default()
                .insert(cast.target_category.as_str());
        }

        // Collect all categories
        let mut cats: HashSet<&str> = HashSet::new();
        for cast in cast_rules {
            cats.insert(cast.source_category.as_str());
            cats.insert(cast.target_category.as_str());
        }

        // Compute transitive closure via repeated BFS from each node
        let mut reachable = HashSet::new();
        for &src in &cats {
            let mut visited = HashSet::new();
            let mut queue = Vec::new();
            if let Some(neighbors) = adjacency.get(src) {
                queue.extend(neighbors.iter().copied());
            }
            while let Some(node) = queue.pop() {
                if visited.insert(node) {
                    reachable.insert((src.to_string(), node.to_string()));
                    if let Some(neighbors) = adjacency.get(node) {
                        for &next in neighbors {
                            if !visited.contains(next) {
                                queue.push(next);
                            }
                        }
                    }
                }
            }
        }
        reachable
    }

    // Build cast rules for each source grammar from their rule info
    // Source A casts: rules in A that are casts
    let casts_a: Vec<CastRule> = comp_ctx
        .rules_a
        .iter()
        .filter(|r| r.is_cast)
        .filter_map(|r| {
            // Cast rules have a NonTerminal first item pointing to the source category
            r.first_items.iter().find_map(|item| {
                if let crate::prediction::FirstItem::NonTerminal(ref source_cat) = item {
                    Some(CastRule {
                        label: r.label.clone(),
                        source_category: source_cat.clone(),
                        target_category: r.category.clone(),
                        shares_infix_with_target: false,
                    })
                } else {
                    None
                }
            })
        })
        .collect();

    let casts_b: Vec<CastRule> = comp_ctx
        .rules_b
        .iter()
        .filter(|r| r.is_cast)
        .filter_map(|r| {
            r.first_items.iter().find_map(|item| {
                if let crate::prediction::FirstItem::NonTerminal(ref source_cat) = item {
                    Some(CastRule {
                        label: r.label.clone(),
                        source_category: source_cat.clone(),
                        target_category: r.category.clone(),
                        shares_infix_with_target: false,
                    })
                } else {
                    None
                }
            })
        })
        .collect();

    let reachable_a = reachability(&casts_a);
    let reachable_b = reachability(&casts_b);
    let reachable_merged = reachability(base_ctx.cast_rules);

    // Any pair reachable in source A or B but not in merged = broken chain
    let source_reachable: HashSet<(String, String)> =
        reachable_a.union(&reachable_b).cloned().collect();

    let mut broken_chains: Vec<(String, String)> = source_reachable
        .iter()
        .filter(|pair| !reachable_merged.contains(pair))
        .cloned()
        .collect();

    // Sort for deterministic output
    broken_chains.sort();

    for (src, dst) in broken_chains {
        let source_grammar = if reachable_a.contains(&(src.clone(), dst.clone())) {
            "A"
        } else {
            "B"
        };

        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::X04,
            name: "composition-cast-chain-break",
            severity: LintSeverity::Error,
            category: Some(dst.clone()),
            rule: None,
            message: format!(
                "cast chain `{}` -> `{}` from grammar {} is broken after composition",
                src, dst, source_grammar,
            ),
            hint: Some(
                "ensure all intermediate cast rules are preserved in the composed \
                 grammar, or add explicit casts to restore the chain"
                    .to_string(),
            ),
            grammar_name: Some(base_ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ──────────────────────────────────────────────────────────────────────────────
// X05: Composition Terminal Collision
// ──────────────────────────────────────────────────────────────────────────────

/// Detects when the same terminal string is used in different categories with
/// different semantic roles across the two source grammars.
///
/// For example, if grammar A uses `+` as an infix operator in category `Int`
/// (role: "infix") and grammar B uses `+` as a prefix operator in category
/// `Str` (role: "prefix"), this is a terminal collision that may cause
/// confusion or dispatch errors in the composed grammar.
pub(crate) fn lint_x05_composition_terminal_collision(
    base_ctx: &LintContext,
    comp_ctx: &CompositionLintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    // Find terminals that appear in both grammars
    let terminals_a: HashSet<&str> = comp_ctx
        .terminal_semantics_a
        .keys()
        .map(|s| s.as_str())
        .collect();
    let terminals_b: HashSet<&str> = comp_ctx
        .terminal_semantics_b
        .keys()
        .map(|s| s.as_str())
        .collect();

    let mut shared_terminals: Vec<&str> = terminals_a.intersection(&terminals_b).copied().collect();
    shared_terminals.sort_unstable();

    for terminal in shared_terminals {
        let semantics_a = &comp_ctx.terminal_semantics_a[terminal];
        let semantics_b = &comp_ctx.terminal_semantics_b[terminal];

        // Collect all roles from A and B
        let roles_a: HashSet<&str> = semantics_a.iter().map(|(_, role)| role.as_str()).collect();
        let roles_b: HashSet<&str> = semantics_b.iter().map(|(_, role)| role.as_str()).collect();

        // Check if any role in B is not present in A (i.e., different semantic use)
        let diff_in_b: Vec<&str> = roles_b.difference(&roles_a).copied().collect();
        let diff_in_a: Vec<&str> = roles_a.difference(&roles_b).copied().collect();

        if !diff_in_a.is_empty() || !diff_in_b.is_empty() {
            let mut all_roles: Vec<&str> = roles_a.union(&roles_b).copied().collect();
            all_roles.sort_unstable();

            // Collect categories from both for context
            let cats_a: Vec<&str> = semantics_a.iter().map(|(cat, _)| cat.as_str()).collect();
            let cats_b: Vec<&str> = semantics_b.iter().map(|(cat, _)| cat.as_str()).collect();

            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::X05,
                name: "composition-terminal-collision",
                severity: LintSeverity::Warning,
                category: None,
                rule: None,
                message: format!(
                    "terminal `{}` has different semantic roles across grammars: \
                     A uses it as [{}] in [{}], B uses it as [{}] in [{}]",
                    terminal,
                    roles_a.iter().copied().collect::<Vec<_>>().join(", "),
                    cats_a.join(", "),
                    roles_b.iter().copied().collect::<Vec<_>>().join(", "),
                    cats_b.join(", "),
                ),
                hint: Some(
                    "consider renaming the terminal in one grammar to avoid \
                     semantic confusion in the composed grammar"
                        .to_string(),
                ),
                grammar_name: Some(base_ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// W03+: Cross-Category Ambiguity Hotspot Ranking
// ══════════════════════════════════════════════════════════════════════════════

/// After per-category W03 emissions, aggregate ambiguity counts across ALL
/// categories per token. Rank tokens by total ambiguity impact.
pub(crate) fn lint_w03_cross_category_hotspot(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    if ctx.decision_trees.is_empty() {
        return;
    }

    // Accumulate per-token ambiguity counts across categories
    let mut token_ambiguity: HashMap<String, Vec<(String, usize)>> = HashMap::new();

    for (cat_name, tree) in ctx.decision_trees {
        let dispatch_tokens = tree.dispatch_tokens(ctx.token_id_map);
        for token_variant in &dispatch_tokens {
            let strategy = tree.dispatch_strategy(token_variant, ctx.token_id_map);
            let count = match &strategy {
                crate::decision_tree::DispatchStrategy::AmbiguousFanout { rule_labels, .. } => {
                    rule_labels.len()
                },
                _ => 0,
            };
            if count >= 2 {
                token_ambiguity
                    .entry(token_variant.clone())
                    .or_default()
                    .push((cat_name.clone(), count));
            }
        }
    }

    // Only report tokens ambiguous in 2+ categories
    let mut hotspots: Vec<(String, usize, Vec<(String, usize)>)> = token_ambiguity
        .into_iter()
        .filter(|(_, cats)| cats.len() >= 2)
        .map(|(token, cats)| {
            let total: usize = cats.iter().map(|(_, c)| *c).sum();
            (token, total, cats)
        })
        .collect();
    hotspots.sort_by(|a, b| b.1.cmp(&a.1));

    for (rank, (token, total, cats)) in hotspots.iter().enumerate() {
        let breakdown: Vec<String> = cats
            .iter()
            .map(|(cat, count)| format!("{}: {}", cat, count))
            .collect();
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::W03,
            name: "cross-category-hotspot",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "token `{}` is #{} ambiguity hotspot: {} ambiguities across {} categories ({})",
                token,
                rank + 1,
                total,
                cats.len(),
                breakdown.join(", "),
            ),
            hint: Some(
                "consider left-factoring rules starting with this token to reduce cross-category ambiguity"
                    .to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G32: Prefix Structural Isomorphism
// ══════════════════════════════════════════════════════════════════════════════

/// Detect categories with structurally identical dispatch tries.
/// Uses content hashing of the trie structure for comparison.
pub(crate) fn lint_g32_prefix_isomorphism(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    if ctx.decision_trees.len() < 2 {
        return;
    }

    // Hash each category's trie structure by serializing stats + dispatch tokens + strategies
    let mut hash_to_cats: HashMap<u64, Vec<String>> = HashMap::new();

    for (cat_name, tree) in ctx.decision_trees {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut hasher = DefaultHasher::new();

        // Hash the trie structure via all (path, action) pairs
        let mut entries: Vec<(Vec<u8>, String)> = tree
            .segments
            .iter()
            .flat_map(|seg| seg.iter())
            .map(|(path, action)| {
                let action_str = match action {
                    crate::decision_tree::DecisionAction::Commit { rule_label, .. } => {
                        format!("C:{}", rule_label)
                    },
                    crate::decision_tree::DecisionAction::Ambiguous { candidates } => {
                        let mut labels: Vec<&str> =
                            candidates.iter().map(|c| c.rule_label.as_str()).collect();
                        labels.sort();
                        format!("A:{}", labels.join(","))
                    },
                    crate::decision_tree::DecisionAction::NonterminalBoundary { options } => {
                        format!("NT:{}", options.len())
                    },
                };
                (path, action_str)
            })
            .collect();
        entries.sort();

        // Hash the sorted entries (structure, not content) — compare shapes, not labels
        entries.len().hash(&mut hasher);
        for (path, _) in &entries {
            path.hash(&mut hasher);
        }
        tree.stats.total_states.hash(&mut hasher);
        tree.stats.ambiguous_nodes.hash(&mut hasher);
        tree.stats.max_depth.hash(&mut hasher);

        let hash = hasher.finish();
        hash_to_cats.entry(hash).or_default().push(cat_name.clone());
    }

    for cats in hash_to_cats.values() {
        if cats.len() >= 2 {
            let mut sorted = cats.clone();
            sorted.sort();
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::G32,
                name: "prefix-isomorphism",
                severity: LintSeverity::Note,
                category: None,
                rule: None,
                message: format!(
                    "categories [{}] have structurally identical dispatch tries; \
                     they could share parser code via parameterization",
                    sorted.join(", "),
                ),
                hint: Some(
                    "consider using a generic parser parameterized over the category type"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// D10: Lookahead Waste
// ══════════════════════════════════════════════════════════════════════════════

/// Detect when generated lookahead is deeper than necessary.
/// Compares TreeStats.max_depth vs per-token resolution depth.
pub(crate) fn lint_d10_lookahead_waste(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    for (cat_name, tree) in ctx.decision_trees {
        if tree.stats.total_states == 0 || tree.stats.max_depth <= 1 {
            continue;
        }

        let dispatch_tokens = tree.dispatch_tokens(ctx.token_id_map);
        let mut depth1_count = 0usize;
        let mut total_tokens = 0usize;

        for token_variant in &dispatch_tokens {
            total_tokens += 1;
            let strategy = tree.dispatch_strategy(token_variant, ctx.token_id_map);
            match &strategy {
                crate::decision_tree::DispatchStrategy::Singleton { .. } => {
                    depth1_count += 1;
                },
                crate::decision_tree::DispatchStrategy::DisjointSuffix {
                    shared_prefix_len,
                    ..
                } => {
                    if *shared_prefix_len == 0 {
                        depth1_count += 1;
                    }
                },
                _ => {},
            }
        }

        if total_tokens > 0 && tree.stats.max_depth > 2 {
            let depth1_pct = depth1_count as f64 / total_tokens as f64 * 100.0;
            if depth1_pct >= 80.0 {
                diagnostics.push(LintDiagnostic {
                    id: DiagnosticId::D10,
                    name: "lookahead-waste",
                    severity: LintSeverity::Note,
                    category: Some(cat_name.clone()),
                    rule: None,
                    message: format!(
                        "category `{}`: {}-token max lookahead generated but 1-token suffices \
                         for {:.0}% ({}/{}) of dispatch points",
                        cat_name, tree.stats.max_depth, depth1_pct, depth1_count, total_tokens,
                    ),
                    hint: Some(
                        "the few deep-lookahead tokens may be candidates for left-factoring"
                            .to_string(),
                    ),
                    grammar_name: Some(ctx.grammar_name.to_string()),
                    source_location: None,
                });
            }
        }
    }
}

/// 2e: Ascent equation x dispatch trie correlation.
///
/// Detects parsed-but-never-rewritten constructors: rules reachable in the
/// trie (they can be parsed) but never consumed by any Ascent equation
/// (semantic dependency groups). Such rules produce parse nodes that are
/// never processed by the semantic layer.
///
/// Severity: Note (informational — the rule may still be needed for pattern matching).
pub(crate) fn lint_d13_ascent_trie_correlation(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    if ctx.semantic_dependency_groups.is_empty() || ctx.decision_trees.is_empty() {
        return;
    }

    // Collect all rule labels referenced by any semantic dependency group
    let semantically_consumed: HashSet<&str> = ctx
        .semantic_dependency_groups
        .iter()
        .flat_map(|group| group.iter().map(|s| s.as_str()))
        .collect();

    if semantically_consumed.is_empty() {
        return;
    }

    // For each category, find trie-reachable rules not in any semantic group
    for (cat_name, tree) in ctx.decision_trees {
        let reachable = tree.reachable_rules();
        let mut orphans: Vec<&str> = reachable
            .iter()
            .filter(|label| !semantically_consumed.contains(label.as_str()))
            .map(|s| s.as_str())
            .collect();
        orphans.sort_unstable();

        for orphan in &orphans {
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::D13,
                name: "parsed-but-unrewritten",
                severity: LintSeverity::Note,
                category: Some(cat_name.clone()),
                rule: Some(orphan.to_string()),
                message: format!(
                    "rule `{}` is reachable in trie dispatch but appears in zero Ascent equations",
                    orphan,
                ),
                hint: Some(
                    "this constructor is parsed but never semantically consumed; \
                     verify it's needed or add an Ascent equation referencing it"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Mathematical Analysis Lints
// ══════════════════════════════════════════════════════════════════════════════

// ── TRS analysis lints (T01-T04) ────────────────────────────────────────────

pub(crate) fn lint_t01_non_joinable_critical_pair(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let analysis = match ctx.confluence_result {
        Some(a) => a,
        None => return,
    };
    for (i, cp) in analysis.critical_pairs.iter().enumerate() {
        if matches!(
            analysis.joinability_results.get(i),
            Some(crate::confluence::JoinabilityResult::NotJoinable { .. })
        ) {
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::T01,
                name: "non-joinable-critical-pair",
                severity: LintSeverity::Warning,
                category: None,
                rule: None,
                message: format!(
                    "critical pair (rules {}, {}) is not joinable — confluence failure: {} ≠ {}",
                    cp.rule1_index, cp.rule2_index, cp.term1, cp.term2,
                ),
                hint: Some(
                    "add an equation or oriented rewrite to make the terms joinable".to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

pub(crate) fn lint_t02_confluence_verified(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let analysis = match ctx.confluence_result {
        Some(a) => a,
        None => return,
    };
    if analysis.is_confluent {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::T02,
            name: "confluence-verified",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "all {} critical pairs are joinable — system is confluent",
                analysis.critical_pairs.len(),
            ),
            hint: None,
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_t03_non_terminating_cycle(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.termination_result {
        Some(r) => r,
        None => return,
    };
    if let crate::termination::TerminationResult::PotentiallyNonTerminating {
        reason,
        problematic_sccs,
    } = result
    {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::T03,
            name: "non-terminating-cycle",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "potential non-termination: {} ({} problematic SCC(s))",
                reason,
                problematic_sccs.len(),
            ),
            hint: Some("add a decreasing measure or simplify the rewrite cycle".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_t04_termination_verified(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.termination_result {
        Some(r) => r,
        None => return,
    };
    if matches!(result, crate::termination::TerminationResult::Terminating) {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::T04,
            name: "termination-verified",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: "all SCCs have decreasing measures — system terminates".to_string(),
            hint: None,
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── VPA lints (V01-V02) ─────────────────────────────────────────────────────

pub(crate) fn lint_v01_vpa_determinizable(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let analysis = match ctx.vpa_result {
        Some(a) => a,
        None => return,
    };
    if analysis.is_determinizable {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::V01,
            name: "vpa-determinizable",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "grammar's structured sublanguage admits zero-backtracking VPA ({} states)",
                analysis.state_count,
            ),
            hint: None,
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_v02_vpa_alphabet_mismatch(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let analysis = match ctx.vpa_result {
        Some(a) => a,
        None => return,
    };
    for mismatch in &analysis.alphabet_mismatches {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::V02,
            name: "vpa-alphabet-mismatch",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "delimiter classification inconsistency: token `{}` classified as both call and return",
                mismatch,
            ),
            hint: Some(
                "ensure each delimiter token is used consistently as either opening or closing"
                    .to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── WTA lints (V03-V04) ─────────────────────────────────────────────────────

pub(crate) fn lint_v03_wta_unrecognized_term(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let analysis = match ctx.wta_result {
        Some(a) => a,
        None => return,
    };
    for term in &analysis.unrecognized_terms {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::V03,
            name: "wta-unrecognized-term",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!("term pattern `{}` not in regular tree language", term,),
            hint: Some("add a rule or transition to recognize this term pattern".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_v04_wta_hot_path(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let analysis = match ctx.wta_result {
        Some(a) => a,
        None => return,
    };
    for path in &analysis.hot_paths {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::V04,
            name: "wta-hot-path",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "frequently weighted term pattern: {} — specialization candidate",
                path,
            ),
            hint: None,
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── Safety verification lints (S01-S06) ─────────────────────────────────────

pub(crate) fn lint_s01_safety_violation(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.safety_result {
        Some(r) => r,
        None => return,
    };
    if !result.safe {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::S01,
            name: "safety-violation",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "bad state reachable via WPDS prestar (initial weight: {})",
                result.initial_weight,
            ),
            hint: Some("review the grammar for unreachable-yet-dispatched rules".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_s02_safety_verified(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.safety_result {
        Some(r) => r,
        None => return,
    };
    if result.safe {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::S02,
            name: "safety-verified",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: "no bad states reachable — safety property verified".to_string(),
            hint: None,
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_s03_cegar_refinement(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let log = match ctx.cegar_result {
        Some(l) => l,
        None => return,
    };
    let final_verdict = log
        .steps
        .last()
        .map(|s| format!("{}", s.verdict))
        .unwrap_or_else(|| "unknown".to_string());
    diagnostics.push(LintDiagnostic {
        id: DiagnosticId::S03,
        name: "cegar-refinement",
        severity: LintSeverity::Note,
        category: None,
        rule: None,
        message: format!(
            "CEGAR loop: {} refinement step(s), final verdict: {}",
            log.steps.len(),
            final_verdict,
        ),
        hint: None,
        grammar_name: Some(ctx.grammar_name.to_string()),
        source_location: None,
    });
}

pub(crate) fn lint_s04_ewpds_merge_site(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.ewpds_result {
        Some(r) => r,
        None => return,
    };
    if result.merge_site_count > 0 {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::S04,
            name: "ewpds-merge-site",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "identified {} merge function site(s): {}",
                result.merge_site_count,
                result.merge_site_labels.join(", "),
            ),
            hint: None,
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_s05_ara_invariant(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.ara_result {
        Some(r) => r,
        None => return,
    };
    diagnostics.push(LintDiagnostic {
        id: DiagnosticId::S05,
        name: "ara-invariant",
        severity: LintSeverity::Note,
        category: None,
        rule: None,
        message: format!(
            "ARA weight domain: dimension={}, {} invariant(s) discovered",
            result.dimension, result.invariant_count,
        ),
        hint: None,
        grammar_name: Some(ctx.grammar_name.to_string()),
        source_location: None,
    });
}

pub(crate) fn lint_s06_algebraic_summary(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.algebraic_result {
        Some(r) => r,
        None => return,
    };
    diagnostics.push(LintDiagnostic {
        id: DiagnosticId::S06,
        name: "algebraic-summary",
        severity: LintSeverity::Note,
        category: None,
        rule: None,
        message: format!(
            "Tarjan path expression summary: {} SCC(s), {} expression(s)",
            result.scc_count, result.path_expression_count,
        ),
        hint: None,
        grammar_name: Some(ctx.grammar_name.to_string()),
        source_location: None,
    });
}

// ── Concurrency lints (N01-N05) ─────────────────────────────────────────────

pub(crate) fn lint_n01_deadlock_risk(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.petri_result {
        Some(r) => r,
        None => return,
    };
    if result.has_deadlock_risk {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::N01,
            name: "deadlock-risk",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "Petri net coverability detects potential deadlock ({} places, {} transitions)",
                result.place_count, result.transition_count,
            ),
            hint: Some(
                "review parallel composition operators for potential blocking patterns".to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_n02_unbounded_channel(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.petri_result {
        Some(r) => r,
        None => return,
    };
    for place in &result.unbounded_places {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::N02,
            name: "unbounded-channel",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!("place `{}` has unbounded token capacity", place,),
            hint: Some(
                "consider adding a capacity bound to prevent resource exhaustion".to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_n03_scope_violation(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.nominal_result {
        Some(r) => r,
        None => return,
    };
    for (name, context) in &result.scope_violations {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::N03,
            name: "scope-violation",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!("name `{}` used outside its binding scope ({})", name, context,),
            hint: Some("ensure the name is only used within the scope of its binder".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_n04_scope_narrowing(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.nominal_result {
        Some(r) => r,
        None => return,
    };
    for (binder, suggestion) in &result.narrowing_candidates {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::N04,
            name: "scope-narrowing",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "`PNew` scope for binder `{}` can be tightened: {}",
                binder, suggestion,
            ),
            hint: None,
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_n05_non_bisimilar(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.alternating_result {
        Some(r) => r,
        None => return,
    };
    for (cat_a, cat_b) in &result.non_bisimilar_pairs {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::N05,
            name: "non-bisimilar",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "categories `{}` and `{}` are not bisimilar (attacker wins game)",
                cat_a, cat_b,
            ),
            hint: Some(
                "these categories have structurally different observable behavior".to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── Temporal lints (L01-L02) ────────────────────────────────────────────────

pub(crate) fn lint_l01_ltl_violated(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let results = match ctx.ltl_results {
        Some(r) => r,
        None => return,
    };
    for (i, result) in results.iter().enumerate() {
        if let crate::ltl::LtlCheckResult::Violated { prefix, .. } = result {
            let desc = prefix.first().map(|s| s.as_str()).unwrap_or("unknown");
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::L01,
                name: "ltl-violated",
                severity: LintSeverity::Warning,
                category: None,
                rule: None,
                message: format!(
                    "LTL property #{} violated (Buchi product non-empty): {}",
                    i, desc,
                ),
                hint: Some(
                    "the grammar's execution traces can violate this temporal property".to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

pub(crate) fn lint_l02_ltl_verified(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let results = match ctx.ltl_results {
        Some(r) => r,
        None => return,
    };
    let satisfied_count = results
        .iter()
        .filter(|r| matches!(r, crate::ltl::LtlCheckResult::Satisfied))
        .count();
    if satisfied_count > 0 {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::L02,
            name: "ltl-verified",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "{} LTL propert{} satisfied",
                satisfied_count,
                if satisfied_count == 1 { "y" } else { "ies" },
            ),
            hint: None,
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── Extension lints (E01-E02) ───────────────────────────────────────────────

pub(crate) fn lint_e01_provenance_trace(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.provenance_result {
        Some(r) => r,
        None => return,
    };
    if !result.provenance_traces.is_empty() {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::E01,
            name: "provenance-trace",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "how-provenance: {} polynomial(s) computed",
                result.provenance_traces.len(),
            ),
            hint: None,
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_e02_cra_cost_anomaly(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.cra_result {
        Some(r) => r,
        None => return,
    };
    for (desc, value) in &result.cost_anomalies {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::E02,
            name: "cra-cost-anomaly",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!("CRA register value exceeds threshold: {} = {}", desc, value,),
            hint: Some("review the grammar's quantitative cost model".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── Morphism lints (M01-M02) ────────────────────────────────────────────────

pub(crate) fn lint_m01_morphism_gap(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.morphism_result {
        Some(r) => r,
        None => return,
    };
    for gap in &result.gaps {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::M01,
            name: "morphism-gap",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!("theory morphism incomplete — missing constructor mapping: {}", gap,),
            hint: Some(
                "add a cross-category rule or constructor to complete the morphism".to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_m02_morphism_preservation_failure(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.morphism_result {
        Some(r) => r,
        None => return,
    };
    for failure in &result.preservation_failures {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::M02,
            name: "morphism-preservation-failure",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!("equation not preserved under morphism: {}", failure,),
            hint: Some("the morphism does not preserve this algebraic equation".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── KAT lints (K01-K02) ────────────────────────────────────────────────────

pub(crate) fn lint_k01_hoare_failure(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.kat_result {
        Some(r) => r,
        None => return,
    };
    for (desc, passed) in &result.hoare_results {
        if !passed {
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::K01,
                name: "hoare-failure",
                severity: LintSeverity::Warning,
                category: None,
                rule: None,
                message: format!("Hoare triple failed: {}", desc,),
                hint: Some(
                    "p·e·¬q ≠ 0 — the program does not satisfy its specification".to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

pub(crate) fn lint_k02_kat_equivalence(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.kat_result {
        Some(r) => r,
        None => return,
    };
    for (expr1, expr2, equivalent) in &result.equivalence_results {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::K02,
            name: "kat-equivalence",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "KAT equivalence: {} {} {}",
                expr1,
                if *equivalent { "≡" } else { "≢" },
                expr2,
            ),
            hint: None,
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── Pipeline timing lint (P06) ──────────────────────────────────────────────

pub(crate) fn lint_p06_analysis_pipeline_cost(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let elapsed = match ctx.math_analysis_elapsed {
        Some(d) => d,
        None => return,
    };
    // Only emit if there's meaningful work done (> 100µs)
    if elapsed.as_micros() < 100 {
        return;
    }
    diagnostics.push(LintDiagnostic {
        id: DiagnosticId::P06,
        name: "analysis-pipeline-cost",
        severity: LintSeverity::Note,
        category: None,
        rule: None,
        message: format!(
            "mathematical analysis phase completed in {:.2}ms",
            elapsed.as_secs_f64() * 1000.0,
        ),
        hint: None,
        grammar_name: Some(ctx.grammar_name.to_string()),
        source_location: None,
    });
}

// ══════════════════════════════════════════════════════════════════════════════
// Ascent VM / Codegen Lints (A01-A10)
// ══════════════════════════════════════════════════════════════════════════════

/// A01: fixpoint-non-convergence — Warn when rewrite rules have positive depth delta.
pub(crate) fn lint_a01_fixpoint_non_convergence(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    // Analyze rewrite-like rules for depth increase patterns.
    // A rule has positive depth delta if RHS has more nesting levels than LHS.
    // Check: for each rule, if the syntax has NonTerminal items that wrap other NonTerminals
    // more deeply than the same category appears on the LHS, warn.
    for (label, category, syntax) in ctx.all_syntax {
        // Heuristic: if a rule has a NonTerminal to itself AND wraps it in another constructor,
        // it may cause unbounded depth growth.
        // Simple detection: count NonTerminal depth on each "side" of an infix operator.
        let nt_count = syntax
            .iter()
            .filter(|s| matches!(s, SyntaxItemSpec::NonTerminal { .. }))
            .count();
        let terminal_count = syntax
            .iter()
            .filter(|s| matches!(s, SyntaxItemSpec::Terminal(_)))
            .count();

        // Rules with more nonterminals than terminals that reference their own category
        // are potential depth-increasing rewrite targets
        let self_refs: Vec<_> = syntax
            .iter()
            .filter(
                |s| matches!(s, SyntaxItemSpec::NonTerminal { category: c, .. } if c == category),
            )
            .collect();

        // If a rule has 2+ self-referential NTs and only 1 terminal, it could be
        // creating depth growth (e.g., f(x) => f(f(x)) pattern when used as rewrite)
        if self_refs.len() >= 2 && terminal_count <= 1 && nt_count >= 2 {
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::A01,
                name: "fixpoint-non-convergence",
                severity: LintSeverity::Warning,
                category: Some(category.clone()),
                rule: Some(label.clone()),
                message: format!(
                    "rule `{}` has {} self-referential nonterminals with {} terminal(s) — \
                     potential unbounded term growth in fixpoint computation",
                    label,
                    self_refs.len(),
                    terminal_count
                ),
                hint: Some(
                    "ensure complementary depth-reducing rules exist, or add a depth bound"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: ctx
                    .rule_locations
                    .get(&(label.clone(), category.clone()))
                    .copied(),
            });
        }
    }
}

/// A02: redundant-congruence — Note when congruence is declared for a field category with no rewrites.
pub(crate) fn lint_a02_redundant_congruence(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    // Detect categories that are only referenced as nonterminal fields of other categories
    // but have no rules of their own that could trigger rewrites.
    // A category with no infix/prefix rules that only appears as a field in other
    // categories' constructors may have unnecessary congruence rules.
    for cat_info in ctx.categories {
        let own_rules: Vec<_> = ctx
            .all_syntax
            .iter()
            .filter(|(_, c, _)| c == &cat_info.name)
            .collect();

        // Referenced as NT in other categories
        let referenced_as_field = ctx.all_syntax.iter().any(|(_, c, syntax)| {
            c != &cat_info.name
                && syntax.iter().any(|s| {
                    matches!(s, SyntaxItemSpec::NonTerminal { category, .. } if category == &cat_info.name)
                })
        });

        if referenced_as_field && own_rules.len() <= 1 && !cat_info.is_primary {
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::A02,
                name: "redundant-congruence",
                severity: LintSeverity::Note,
                category: Some(cat_info.name.clone()),
                rule: None,
                message: format!(
                    "category `{}` has only {} rule(s) but is referenced as a field — \
                     congruence rules for this category may be redundant",
                    cat_info.name,
                    own_rules.len()
                ),
                hint: Some(
                    "consider whether equations/rewrites actually need congruence through this category"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

/// A03: eq-rw-category-mismatch — Note when a category has equations but no rewrites or vice versa.
pub(crate) fn lint_a03_eq_rw_category_mismatch(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    // This is purely informational: if semantic_dependency_groups reference some
    // categories but not others, there might be a mismatch.
    // With the info available in LintContext, we check for categories that appear
    // in dependency groups vs those that don't.
    if ctx.semantic_dependency_groups.is_empty() {
        return;
    }

    let categories_in_groups: HashSet<&str> = ctx
        .semantic_dependency_groups
        .iter()
        .flat_map(|g| g.iter().map(|s| s.as_str()))
        .collect();

    for cat_info in ctx.categories {
        let has_rules = ctx.all_syntax.iter().any(|(_, c, _)| c == &cat_info.name);
        if has_rules
            && !categories_in_groups.iter().any(|&label| {
                ctx.all_syntax
                    .iter()
                    .any(|(l, c, _)| l == label && c == &cat_info.name)
            })
            && !cat_info.is_primary
        {
            // Category has parsing rules but no equation/rewrite rules reference it
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::A03,
                name: "eq-rw-category-mismatch",
                severity: LintSeverity::Note,
                category: Some(cat_info.name.clone()),
                rule: None,
                message: format!(
                    "category `{}` has parsing rules but no equations or rewrites reference its constructors",
                    cat_info.name
                ),
                hint: Some(
                    "if this category should participate in equational reasoning, add equations or rewrites"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

/// A04: large-equivalence-class — Warn when commutativity + associativity on same constructor.
pub(crate) fn lint_a04_large_equivalence_class(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    // Detect constructors that appear in multiple dependency groups (potential exponential blowup).
    // A label appearing in 3+ dependency groups suggests heavy equational reasoning.
    let mut label_group_count: HashMap<&str, usize> = HashMap::new();
    for group in ctx.semantic_dependency_groups {
        for label in group {
            *label_group_count.entry(label.as_str()).or_insert(0) += 1;
        }
    }

    for (&label, &count) in &label_group_count {
        if count >= 3 {
            let category = ctx
                .all_syntax
                .iter()
                .find(|(l, _, _)| l == label)
                .map(|(_, c, _)| c.clone());

            // Build a compact summary of which group types reference this constructor
            let mut eq_count = 0usize;
            let mut rw_count = 0usize;
            for group in ctx.semantic_dependency_groups {
                if group.iter().any(|l| l.as_str() == label) {
                    // Heuristic: groups containing only this label are likely rewrites;
                    // groups with multiple labels are typically equation groups.
                    // Without richer metadata, count all as equation/rewrite groups.
                    if group.len() <= 2 {
                        rw_count += 1;
                    } else {
                        eq_count += 1;
                    }
                }
            }
            let group_desc = match (eq_count, rw_count) {
                (0, r) => format!("{} rewrite group(s)", r),
                (e, 0) => format!("{} equation group(s)", e),
                (e, r) => format!("{} equation group(s) and {} rewrite group(s)", e, r),
            };

            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::A04,
                name: "large-equivalence-class",
                severity: LintSeverity::Warning,
                category,
                rule: Some(label.to_string()),
                message: format!(
                    "constructor `{}` appears in {} equation/rewrite groups ({}) — \
                     potential equivalence class explosion during Ascent fixpoint evaluation",
                    label, count, group_desc,
                ),
                hint: Some(
                    "this constructor is referenced by many equations/rewrites, which can cause \
                     equivalence class explosion during Ascent fixpoint evaluation; consider \
                     reducing the number of equations involving this constructor, or simplifying \
                     equational axioms (e.g., removing redundant commutativity/associativity declarations)"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: ctx
                    .all_syntax
                    .iter()
                    .find(|(l, _, _)| l == label)
                    .and_then(|(l, c, _)| {
                        ctx.rule_locations
                            .get(&(l.clone(), c.clone()))
                            .copied()
                    }),
            });
        }
    }
}

/// A05: self-referential-equation — Warn when an equation's LHS and RHS are identical or RHS contains LHS.
pub(crate) fn lint_a05_self_referential_equation(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    // Detect rules where the syntax pattern is trivially self-referential.
    // Look for rules that have exactly one NonTerminal of their own category and nothing else.
    for (label, category, syntax) in ctx.all_syntax {
        if syntax.len() == 1 {
            if let Some(SyntaxItemSpec::NonTerminal { category: nt_cat, .. }) = syntax.first() {
                if nt_cat == category {
                    diagnostics.push(LintDiagnostic {
                        id: DiagnosticId::A05,
                        name: "self-referential-equation",
                        severity: LintSeverity::Warning,
                        category: Some(category.clone()),
                        rule: Some(label.clone()),
                        message: format!(
                            "rule `{}` is a trivial identity (single self-referential nonterminal) — \
                             if used as an equation, this is redundant",
                            label
                        ),
                        hint: Some(
                            "remove this rule if it serves no purpose, or verify it is intentional"
                                .to_string(),
                        ),
                        grammar_name: Some(ctx.grammar_name.to_string()),
                        source_location: ctx
                            .rule_locations
                            .get(&(label.clone(), category.clone()))
                            .copied(),
                    });
                }
            }
        }
    }
}

/// A06: missing-equation-congruence — Note when constructor in equation LHS has NT fields without congruence.
pub(crate) fn lint_a06_missing_equation_congruence(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    // For constructors in dependency groups (equation participants),
    // check if their NT fields' categories also have constructors in dependency groups.
    if ctx.semantic_dependency_groups.is_empty() {
        return;
    }

    let labels_in_equations: HashSet<&str> = ctx
        .semantic_dependency_groups
        .iter()
        .flat_map(|g| g.iter().map(|s| s.as_str()))
        .collect();

    for (label, category, syntax) in ctx.all_syntax {
        if !labels_in_equations.contains(label.as_str()) {
            continue;
        }
        // Check NT fields of this constructor
        for item in syntax {
            if let SyntaxItemSpec::NonTerminal { category: nt_cat, .. } = item {
                if nt_cat == category {
                    continue; // Same-category reference — congruence always generated
                }
                // Check if nt_cat has any constructors in equations
                let has_equation_constructors = ctx
                    .all_syntax
                    .iter()
                    .any(|(l, c, _)| c == nt_cat && labels_in_equations.contains(l.as_str()));

                if !has_equation_constructors {
                    diagnostics.push(LintDiagnostic {
                        id: DiagnosticId::A06,
                        name: "missing-equation-congruence",
                        severity: LintSeverity::Note,
                        category: Some(category.clone()),
                        rule: Some(label.clone()),
                        message: format!(
                            "constructor `{}` participates in equations but its field category `{}` has no equation-participating constructors",
                            label, nt_cat
                        ),
                        hint: Some(format!(
                            "congruence through `{}` fields may not propagate — consider adding equations for `{}`",
                            nt_cat, nt_cat
                        )),
                        grammar_name: Some(ctx.grammar_name.to_string()),
                        source_location: ctx
                            .rule_locations
                            .get(&(label.clone(), category.clone()))
                            .copied(),
                    });
                }
            }
        }
    }
}

/// A07: fixpoint-iteration-anomaly — Warn when grammar complexity suggests fixpoint may exceed 50 iterations.
pub(crate) fn lint_a07_fixpoint_iteration_anomaly(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    // Heuristic: grammars with many dependency groups and deep rule nesting
    // are more likely to have slow fixpoint convergence.
    let group_count = ctx.semantic_dependency_groups.len();
    let max_group_size = ctx
        .semantic_dependency_groups
        .iter()
        .map(|g| g.len())
        .max()
        .unwrap_or(0);

    if group_count > 10 && max_group_size > 5 {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::A07,
            name: "fixpoint-iteration-anomaly",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "{} dependency groups with max size {} — fixpoint may require many iterations",
                group_count, max_group_size
            ),
            hint: Some(
                "consider partitioning equations into independent strata or adding a depth bound"
                    .to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

/// A08: equation-subsumes-rewrite — Note when an equation's LHS pattern is more general than a rewrite's.
pub(crate) fn lint_a08_equation_subsumes_rewrite(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    // Detect rules that share a constructor label across multiple dependency groups.
    // If the same label appears as both equation and rewrite (in different groups),
    // the equation may subsume the rewrite.
    let mut label_groups: HashMap<&str, Vec<usize>> = HashMap::new();
    for (idx, group) in ctx.semantic_dependency_groups.iter().enumerate() {
        for label in group {
            label_groups.entry(label.as_str()).or_default().push(idx);
        }
    }

    for (&label, groups) in &label_groups {
        if groups.len() >= 2 {
            let category = ctx
                .all_syntax
                .iter()
                .find(|(l, _, _)| l == label)
                .map(|(_, c, _)| c.clone());
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::A08,
                name: "equation-subsumes-rewrite",
                severity: LintSeverity::Note,
                category,
                rule: Some(label.to_string()),
                message: format!(
                    "constructor `{}` appears in {} dependency groups — an equation may subsume a rewrite",
                    label,
                    groups.len()
                ),
                hint: Some(
                    "check whether the rewrite is redundant given the equation".to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: ctx
                    .all_syntax
                    .iter()
                    .find(|(l, _, _)| l == label)
                    .and_then(|(l, c, _)| {
                        ctx.rule_locations
                            .get(&(l.clone(), c.clone()))
                            .copied()
                    }),
            });
        }
    }
}

/// A09: ascent-struct-size — Note/Warning when generated Ascent struct is very large.
pub(crate) fn lint_a09_ascent_struct_size(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let relation_count = ctx.categories.len() * 3; // ~3 relations per category (cat, eq_cat, rw_cat)
    let rule_estimate = ctx.all_syntax.len() * 2; // ~2 rules per syntax entry (deconstruct + congruence)

    if rule_estimate > 100 {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::A09,
            name: "ascent-struct-size",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "estimated ~{} relations and ~{} Ascent rules — large struct may slow compilation",
                relation_count, rule_estimate
            ),
            hint: Some(
                "consider splitting categories into independent modules or enabling demand-driven population"
                    .to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    } else if relation_count > 50 {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::A09,
            name: "ascent-struct-size",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!("estimated ~{} relations in Ascent struct", relation_count),
            hint: None,
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

/// A10: unreachable-equation-variable — Note when an LHS variable is not referenced in RHS.
pub(crate) fn lint_a10_unreachable_equation_variable(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    // Detect rules with IdentCapture or Binder params that are never referenced
    // elsewhere in the syntax (potential typo in equation variable names).
    for (label, category, syntax) in ctx.all_syntax {
        let captures: Vec<&str> = syntax
            .iter()
            .filter_map(|s| match s {
                SyntaxItemSpec::IdentCapture { param_name } => Some(param_name.as_str()),
                SyntaxItemSpec::Binder { param_name, .. } => Some(param_name.as_str()),
                _ => None,
            })
            .collect();

        // Check if each capture name appears at least in one NonTerminal param_name
        let nt_params: HashSet<&str> = syntax
            .iter()
            .filter_map(|s| match s {
                SyntaxItemSpec::NonTerminal { param_name, .. } => Some(param_name.as_str()),
                _ => None,
            })
            .collect();

        for &capture in &captures {
            // If capture appears only once and doesn't match any NT param, it might be unused
            let capture_count = captures.iter().filter(|&&c| c == capture).count();
            if capture_count == 1 && !nt_params.contains(capture) && captures.len() > 1 {
                diagnostics.push(LintDiagnostic {
                    id: DiagnosticId::A10,
                    name: "unreachable-equation-variable",
                    severity: LintSeverity::Note,
                    category: Some(category.clone()),
                    rule: Some(label.clone()),
                    message: format!(
                        "variable `{}` in rule `{}` is captured but may not be referenced in RHS",
                        capture, label
                    ),
                    hint: Some(
                        "check for typos in variable names across equation LHS and RHS".to_string(),
                    ),
                    grammar_name: Some(ctx.grammar_name.to_string()),
                    source_location: ctx
                        .rule_locations
                        .get(&(label.clone(), category.clone()))
                        .copied(),
                });
            }
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Lexer Lints (LEX01-LEX05)
// ══════════════════════════════════════════════════════════════════════════════

/// LEX01: overlapping-token-defs — Warn when two terminals match the same string.
pub(crate) fn lint_lex01_overlapping_token_defs(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    use std::collections::{BTreeMap, BTreeSet};

    let mut terminal_occurrences: BTreeMap<String, Vec<(String, String)>> = BTreeMap::new();
    for (label, category, syntax) in ctx.all_syntax {
        for item in syntax {
            if let SyntaxItemSpec::Terminal(tok) = item {
                if tok
                    .chars()
                    .any(|ch| ch == '_' || ch.is_ascii_alphanumeric())
                {
                    terminal_occurrences
                        .entry(tok.clone())
                        .or_default()
                        .push((label.clone(), category.clone()));
                }
            }
        }
    }

    for (terminal, occurrences) in terminal_occurrences {
        let categories: BTreeSet<&str> = occurrences
            .iter()
            .map(|(_, category)| category.as_str())
            .collect();
        if categories.len() <= 1 {
            continue;
        }

        let examples: Vec<String> = occurrences
            .iter()
            .take(4)
            .map(|(label, category)| format!("{}::{}", category, label))
            .collect();
        let (first_label, first_category) = &occurrences[0];
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::LEX01,
            name: "overlapping-token-defs",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "terminal `{}` is used in multiple categories: {}",
                terminal,
                categories.into_iter().collect::<Vec<_>>().join(", ")
            ),
            hint: Some(format!(
                "shared keyword-like terminals can make lexer diagnostics ambiguous; seen in {}",
                examples.join(", ")
            )),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: ctx
                .rule_locations
                .get(&(first_label.clone(), first_category.clone()))
                .copied(),
        });
    }
}

/// LEX02: unreachable-token-pattern — Warn when a terminal is shadowed by a higher-priority pattern.
pub(crate) fn lint_lex02_unreachable_token_pattern(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    // Detect terminals that are prefixes of other terminals (e.g., "=" vs "==").
    // The lexer's longest-match semantics handle this, but it can be confusing.
    let mut all_terminals: Vec<String> = Vec::new();
    for (_, _, syntax) in ctx.all_syntax {
        for item in syntax {
            if let SyntaxItemSpec::Terminal(tok) = item {
                if !all_terminals.contains(tok) {
                    all_terminals.push(tok.clone());
                }
            }
        }
    }

    for i in 0..all_terminals.len() {
        for j in (i + 1)..all_terminals.len() {
            let (a, b) = (&all_terminals[i], &all_terminals[j]);
            // Only check proper prefix relationship for non-single-char tokens
            if a.len() > 1 && b.starts_with(a.as_str()) && b.len() > a.len() {
                diagnostics.push(LintDiagnostic {
                    id: DiagnosticId::LEX02,
                    name: "unreachable-token-pattern",
                    severity: LintSeverity::Note,
                    category: None,
                    rule: None,
                    message: format!(
                        "terminal `{}` is a prefix of `{}` — longest-match semantics apply",
                        a, b
                    ),
                    hint: Some(format!(
                        "input `{}` will always lex as `{}`, never as `{}`",
                        b, b, a
                    )),
                    grammar_name: Some(ctx.grammar_name.to_string()),
                    source_location: None,
                });
            }
        }
    }
}

/// LEX03: excessive-equiv-classes — Note when equivalence class count is unusually high.
pub(crate) fn lint_lex03_excessive_equiv_classes(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    // We detect this via the number of unique character patterns in terminals.
    // A proxy: count the number of distinct characters across all terminals.
    let mut distinct_chars: HashSet<char> = HashSet::new();
    for (_, _, syntax) in ctx.all_syntax {
        for item in syntax {
            if let SyntaxItemSpec::Terminal(tok) = item {
                for ch in tok.chars() {
                    distinct_chars.insert(ch);
                }
            }
        }
    }

    if distinct_chars.len() > 25 {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::LEX03,
            name: "excessive-equiv-classes",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "{} distinct characters across all terminals — grammar has unusually diverse character set",
                distinct_chars.len()
            ),
            hint: Some(
                "consider whether all terminals are necessary — large character sets increase DFA table size"
                    .to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

/// LEX04: dfa-state-explosion — Warn when DFA has many more states than minimized DFA.
pub(crate) fn lint_lex04_dfa_state_explosion(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    // This data isn't directly in LintContext. We approximate via category count and terminal count.
    // Full implementation would require LexerStats to be passed through.
    // This proxy fires when grammar-level token diversity is high enough to deserve inspection.
    let terminal_count = ctx
        .all_syntax
        .iter()
        .flat_map(|(_, _, s)| s.iter())
        .filter(|s| matches!(s, SyntaxItemSpec::Terminal(_)))
        .count();

    if terminal_count > 50 {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::LEX04,
            name: "dfa-state-explosion",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "{} terminal tokens — monitor DFA state count for potential explosion",
                terminal_count
            ),
            hint: Some(
                "consider keyword MPH (AL04) to reduce DFA states for keyword-heavy grammars"
                    .to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

/// LEX05: float-integer-ambiguity — Note when both float and integer types are present.
pub(crate) fn lint_lex05_float_integer_ambiguity(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let has_integer = ctx.categories.iter().any(|c| {
        c.native_type.as_deref() == Some("i64") || c.native_type.as_deref() == Some("i32")
    });
    let has_float = ctx.categories.iter().any(|c| {
        c.native_type.as_deref() == Some("f64") || c.native_type.as_deref() == Some("f32")
    });

    if has_integer && has_float {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::LEX05,
            name: "float-integer-ambiguity",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message:
                "both integer and float native types present — `123` always lexes as Integer, never Float"
                    .to_string(),
            hint: Some(
                "use `123.0` for float literals; the lexer uses longest-match with integer-first priority"
                    .to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Parser Lints (PAR01-PAR05)
// ══════════════════════════════════════════════════════════════════════════════

/// PAR01: deep-rd-chain — Warn when RD call chain depth exceeds 5.
pub(crate) fn lint_par01_deep_rd_chain(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    // Build a call graph from syntax: category A references category B via NonTerminal.
    // Find the longest chain depth.
    let mut call_graph: HashMap<&str, HashSet<&str>> = HashMap::new();
    for (_, category, syntax) in ctx.all_syntax {
        for item in syntax {
            if let SyntaxItemSpec::NonTerminal { category: nt_cat, .. } = item {
                if nt_cat != category {
                    call_graph
                        .entry(category.as_str())
                        .or_default()
                        .insert(nt_cat.as_str());
                }
            }
        }
    }

    // DFS to find max depth (with cycle detection)
    fn max_depth<'a>(
        cat: &'a str,
        graph: &HashMap<&'a str, HashSet<&'a str>>,
        visited: &mut HashSet<&'a str>,
    ) -> usize {
        if visited.contains(cat) {
            return 0; // Cycle — don't recurse
        }
        visited.insert(cat);
        let depth = graph
            .get(cat)
            .map(|callees| {
                callees
                    .iter()
                    .map(|&c| 1 + max_depth(c, graph, visited))
                    .max()
                    .unwrap_or(0)
            })
            .unwrap_or(0);
        visited.remove(cat);
        depth
    }

    for cat_info in ctx.categories {
        let mut visited = HashSet::new();
        let depth = max_depth(&cat_info.name, &call_graph, &mut visited);
        if depth > 5 {
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::PAR01,
                name: "deep-rd-chain",
                severity: LintSeverity::Warning,
                category: Some(cat_info.name.clone()),
                rule: None,
                message: format!(
                    "category `{}` has cross-category RD call chain depth {} (threshold: 5)",
                    cat_info.name, depth
                ),
                hint: Some(
                    "deep call chains stress the trampoline stack — consider flattening with cast rules"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

/// PAR02: unused-bp-level — Note when assigned BP levels have gaps.
pub(crate) fn lint_par02_unused_bp_level(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    // Check if the BP table has gaps (assigned levels with no operators).
    if ctx.bp_table.operators.is_empty() {
        return;
    }

    // Collect all used BP values
    let mut used_bps: HashSet<u8> = HashSet::new();
    for op in &ctx.bp_table.operators {
        used_bps.insert(op.left_bp);
        used_bps.insert(op.right_bp);
    }

    if let (Some(&min_bp), Some(&max_bp)) = (used_bps.iter().min(), used_bps.iter().max()) {
        let total_levels = (max_bp - min_bp + 1) as usize;
        let gap_count = total_levels.saturating_sub(used_bps.len());

        if gap_count > 3 && total_levels > 6 {
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::PAR02,
                name: "unused-bp-level",
                severity: LintSeverity::Note,
                category: None,
                rule: None,
                message: format!(
                    "BP range [{}, {}] has {} unused levels out of {} — BP table wider than necessary",
                    min_bp, max_bp, gap_count, total_levels
                ),
                hint: Some(
                    "consider compacting BP levels to reduce match arm range".to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

/// PAR03: postfix-prefix-collision — Warn when same token is both prefix and postfix in same category.
pub(crate) fn lint_par03_postfix_prefix_collision(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    // Collect prefix tokens per category from RuleInfo.
    let mut prefix_tokens: HashMap<&str, HashSet<String>> = HashMap::new();
    for rule in ctx.rules {
        if !rule.is_infix && !rule.is_var && !rule.is_literal {
            for item in &rule.first_items {
                if let crate::prediction::FirstItem::Terminal(tok) = item {
                    prefix_tokens
                        .entry(&rule.category)
                        .or_default()
                        .insert(tok.clone());
                }
            }
        }
    }

    // Collect postfix operator tokens per category from BP table
    let mut postfix_tokens: HashMap<&str, HashSet<String>> = HashMap::new();
    for op in &ctx.bp_table.operators {
        if op.is_postfix {
            postfix_tokens
                .entry(op.category.as_str())
                .or_default()
                .insert(op.terminal.clone());
        }
    }

    // Find collisions
    for (&category, prefix) in &prefix_tokens {
        if let Some(postfix) = postfix_tokens.get(category) {
            for token in prefix.intersection(postfix) {
                diagnostics.push(LintDiagnostic {
                    id: DiagnosticId::PAR03,
                    name: "postfix-prefix-collision",
                    severity: LintSeverity::Warning,
                    category: Some(category.to_string()),
                    rule: None,
                    message: format!(
                        "token `{}` is both prefix and postfix in category `{}` — surprising precedence",
                        token, category
                    ),
                    hint: Some(
                        "review whether the intended semantics are correct; the parser disambiguates by context"
                            .to_string(),
                    ),
                    grammar_name: Some(ctx.grammar_name.to_string()),
                    source_location: None,
                });
            }
        }
    }
}

/// PAR04: mixfix-ambiguous-delimiter — Warn when a mixfix middle delimiter is also used as infix.
pub(crate) fn lint_par04_mixfix_ambiguous_delimiter(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    // Collect infix operator tokens (non-postfix, non-mixfix)
    let infix_tokens: HashSet<&str> = ctx
        .bp_table
        .operators
        .iter()
        .filter(|op| !op.is_postfix && !op.is_mixfix)
        .map(|op| op.terminal.as_str())
        .collect();

    // Check mixfix middle delimiters
    for op in ctx.bp_table.operators.iter().filter(|op| op.is_mixfix) {
        for part in &op.mixfix_parts {
            // L12 follow-up B6 (2026-05-07): iterate vector terminals.
            // Lint each literal in following_terminals (preceding ones
            // are typically opening brackets which won't conflict with
            // infix; but iterate both for completeness).
            for following in &part.following_terminals {
                if infix_tokens.contains(following.as_str()) {
                    diagnostics.push(LintDiagnostic {
                        id: DiagnosticId::PAR04,
                        name: "mixfix-ambiguous-delimiter",
                        severity: LintSeverity::Warning,
                        category: Some(op.category.clone()),
                        rule: Some(op.label.clone()),
                        message: format!(
                            "mixfix delimiter `{}` in `{}` is also used as an infix operator",
                            following, op.label
                        ),
                        hint: Some(
                            "parsing may be ambiguous — consider using a unique delimiter"
                                .to_string(),
                        ),
                        grammar_name: Some(ctx.grammar_name.to_string()),
                        source_location: ctx
                            .rule_locations
                            .get(&(op.label.clone(), op.category.clone()))
                            .copied(),
                    });
                }
            }
        }
    }
}

// Stage 10.8 (2026-05-05): lint_par05_trampoline_frame_variant_count DELETED.
// Linted Frame_Cat enum size — Frame_Cat is gone with trampoline.rs (Stage 10.6).
// Walker uses WPDS stack symbols (rule_idx, src_idx), not named per-rule frame
// variants, so the lint's enforcement target no longer exists.

// ══════════════════════════════════════════════════════════════════════════════
// Dispatch Lints (DIS01-DIS05)
// ══════════════════════════════════════════════════════════════════════════════

/// DIS01: hot-path-misalignment — Warn when the WFST action table is not
/// weight-ordered.
///
/// The codegen (CD01) sorts dispatch arms by `predict()` output which is
/// always weight-ordered, so this lint primarily detects unsorted action
/// tables in the `PredictionWfst` builder.  A warning here does NOT mean
/// the emitted code is mis-ordered (CD01 handles that), but it may
/// indicate the builder did not finalize weights correctly.
pub(crate) fn lint_dis01_hot_path_misalignment(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    // DIS01 is verbose-only: codegen CD01 always compensates for hot-path misalignment
    if std::env::var("PRATTAIL_LINT_VERBOSE").is_err() {
        return;
    }
    for (cat, wfst) in ctx.prediction_wfsts {
        if wfst.actions.len() < 2 {
            continue;
        }
        // Find the lowest-weight action
        let min_weight = wfst
            .actions
            .iter()
            .map(|a| a.weight.value())
            .fold(f64::INFINITY, f64::min);

        // Check if the first action has the lowest weight
        if let Some(first) = wfst.actions.first() {
            if (first.weight.value() - min_weight).abs() > 0.01 {
                diagnostics.push(LintDiagnostic {
                    id: DiagnosticId::DIS01,
                    name: "hot-path-misalignment",
                    severity: LintSeverity::Note,
                    category: Some(cat.clone()),
                    rule: None,
                    message: format!(
                        "category `{}`: WFST action table first weight {:.2} != minimum weight {:.2} \
                         (codegen CD01 compensates via predict()-based ordering)",
                        cat,
                        first.weight.value(),
                        min_weight
                    ),
                    hint: Some(
                        "WFST builder should finalize actions in weight order; \
                         codegen dispatch arms are CD01-sorted regardless"
                            .to_string(),
                    ),
                    grammar_name: Some(ctx.grammar_name.to_string()),
                    source_location: None,
                });
            }
        }
    }
}

/// DIS02: cold-arm-ratio — Note when >80% of dispatch arms are cold.
pub(crate) fn lint_dis02_cold_arm_ratio(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    for (cat, wfst) in ctx.prediction_wfsts {
        let total = wfst.actions.len();
        if total < 3 {
            continue;
        }
        let cold = wfst
            .actions
            .iter()
            .filter(|a| a.weight.value() >= 1.0)
            .count();
        let ratio = cold as f64 / total as f64;

        if ratio > 0.8 {
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::DIS02,
                name: "cold-arm-ratio",
                severity: LintSeverity::Note,
                category: Some(cat.clone()),
                rule: None,
                message: format!(
                    "category `{}`: {}/{} dispatch arms ({:.0}%) are cold (weight >= 1.0)",
                    cat,
                    cold,
                    total,
                    ratio * 100.0
                ),
                hint: Some(
                    "most arms are rarely taken — hot/cold splitting (A2) may improve i-cache utilization"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

/// DIS03: decision-tree-depth — Warn when decision tree max_depth exceeds 8.
pub(crate) fn lint_dis03_decision_tree_depth(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    for (cat, tree) in ctx.decision_trees {
        if tree.stats.max_depth > 8 {
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::DIS03,
                name: "decision-tree-depth",
                severity: LintSeverity::Warning,
                category: Some(cat.clone()),
                rule: None,
                message: format!(
                    "category `{}` decision tree depth {} exceeds threshold of 8 — long shared prefixes",
                    cat, tree.stats.max_depth
                ),
                hint: Some(
                    "consider left-factoring rules or using segment merging (CD02)".to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

/// DIS04: backtrack-elimination-coverage — Note committed vs save/restore arms after G1.
pub(crate) fn lint_dis04_backtrack_elimination_coverage(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    for (cat, tree) in ctx.decision_trees {
        let det = tree.stats.deterministic_rules;
        let total = tree.stats.total_rules;
        if total == 0 {
            continue;
        }
        let ratio = det as f64 / total as f64;

        if ratio < 1.0 && total > 2 {
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::DIS04,
                name: "backtrack-elimination-coverage",
                severity: LintSeverity::Note,
                category: Some(cat.clone()),
                rule: None,
                message: format!(
                    "category `{}`: {}/{} rules ({:.0}%) have deterministic dispatch — \
                     remaining {} rules still use save/restore",
                    cat,
                    det,
                    total,
                    ratio * 100.0,
                    total - det
                ),
                hint: Some(
                    "non-deterministic rules share prefixes; consider left-factoring or multi-token lookahead (B1)"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

/// DIS05: nfa-try-all-set-size — Warn when NFA-ambiguous candidate set exceeds 5.
pub(crate) fn lint_dis05_nfa_try_all_set_size(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    for (cat, tree) in ctx.decision_trees {
        // Check ambiguous nodes for large candidate sets
        if tree.stats.ambiguous_nodes > 5 {
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::DIS05,
                name: "nfa-try-all-set-size",
                severity: LintSeverity::Warning,
                category: Some(cat.clone()),
                rule: None,
                message: format!(
                    "category `{}` has {} ambiguous dispatch points (threshold: 5) — poor prefix disambiguation",
                    cat, tree.stats.ambiguous_nodes
                ),
                hint: Some(
                    "add unique prefix tokens to rules or enable multi-token lookahead (B1)"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Advanced automata lints
// ══════════════════════════════════════════════════════════════════════════════

// ── Symbolic automata (SYM01-SYM04) ──────────────────────────────────────────

pub(crate) fn lint_sym01_unsatisfiable_guard(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.symbolic_result {
        Some(r) => r,
        None => return,
    };
    for (desc, sat) in &result.guard_satisfiability {
        if !sat {
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::SYM01,
                name: "unsatisfiable-guard",
                severity: LintSeverity::Warning,
                category: None,
                rule: None,
                message: format!("guard '{}' is unsatisfiable (dead receive)", desc),
                hint: Some("remove the unreachable guard or relax its predicate".to_string()),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

pub(crate) fn lint_sym02_overlapping_guards(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.symbolic_result {
        Some(r) => r,
        None => return,
    };
    for (g1, g2) in &result.overlapping_guards {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::SYM02,
            name: "overlapping-guards",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!("guards '{}' and '{}' overlap (non-disjoint)", g1, g2),
            hint: Some("add disambiguation predicates or merge the guards".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_sym03_subsumed_guard(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.symbolic_result {
        Some(r) => r,
        None => return,
    };
    for (sub, sup) in &result.subsumed_guards {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::SYM03,
            name: "subsumed-guard",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!("guard '{}' is subsumed by '{}' (redundant)", sub, sup),
            hint: Some("the subsumed guard can be removed without affecting behavior".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_sym04_non_minimal_guards(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.symbolic_result {
        Some(r) => r,
        None => return,
    };
    if result.num_states > 10 && !result.subsumed_guards.is_empty() {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::SYM04,
            name: "non-minimal-guards",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "SFA has {} states with {} subsumed guards; minimization would reduce state count",
                result.num_states,
                result.subsumed_guards.len()
            ),
            hint: Some("run SFA minimization to merge equivalent guard states".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── Weighted Büchi (O01-O02) ─────────────────────────────────────────────────

pub(crate) fn lint_o01_weighted_buchi_non_convergent(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.buchi_result {
        Some(r) => r,
        None => return,
    };
    // If the automaton has no accepting cycle, weight computation is trivially convergent.
    // Warn when the automaton structure suggests convergence issues.
    if !result.has_accepting_cycle && result.num_states > 1 {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::O01,
            name: "weighted-buchi-non-convergent",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "weighted Büchi automaton ({} states) has no accepting cycle — weight computation trivially converges to zero",
                result.num_states
            ),
            hint: Some("check that liveness properties are correctly specified".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_o02_weighted_buchi_heavy_cycle(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.buchi_result {
        Some(r) => r,
        None => return,
    };
    if result.has_accepting_cycle && result.num_accepting > result.num_states / 2 {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::O02,
            name: "weighted-buchi-heavy-cycle",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "accepting cycle weight is high ({}/{} states are accepting)",
                result.num_accepting, result.num_states
            ),
            hint: Some("consider whether all accepting states are intentional".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── Weighted Alternating (N06-N07) ───────────────────────────────────────────

pub(crate) fn lint_n06_weighted_parity_non_convergent(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.alternating_result {
        Some(r) => r,
        None => return,
    };
    // Flag when there are many non-bisimilar pairs relative to total categories,
    // suggesting the parity game value may not converge quickly due to structural
    // divergence across categories.
    let pair_count = result.non_bisimilar_pairs.len();
    if pair_count > 3 && result.state_count > 5 {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::N06,
            name: "weighted-parity-non-convergent",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "alternating automaton has {} non-bisimilar pairs across {} states — parity game value may not converge quickly",
                pair_count, result.state_count
            ),
            hint: Some("consider bounding the alternation depth or using a fixpoint iteration limit".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_n07_weighted_branching_imbalance(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.alternating_result {
        Some(r) => r,
        None => return,
    };
    // If every pair is non-bisimilar, the structure is purely adversarial —
    // no two categories behave equivalently.
    let total_pairs = if result.state_count > 1 {
        result.state_count * (result.state_count - 1) / 2
    } else {
        0
    };
    if total_pairs > 0 && result.non_bisimilar_pairs.len() == total_pairs {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::N07,
            name: "weighted-branching-imbalance",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "alternating automaton is purely adversarial ({} states, all pairs non-bisimilar)",
                result.state_count
            ),
            hint: Some("all categories have structurally different behavior; consider if some can be merged".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── Weighted VPA (V05-V06) ───────────────────────────────────────────────────

pub(crate) fn lint_v05_weighted_vpa_non_determinizable(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.vpa_result {
        Some(r) => r,
        None => return,
    };
    // A non-determinizable VPA with alphabet mismatches suggests
    // exponential blowup risk during determinization.
    if !result.is_determinizable && !result.alphabet_mismatches.is_empty() {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::V05,
            name: "weighted-vpa-non-determinizable",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "weighted VPA is non-determinizable with {} alphabet mismatches — determinization may cause exponential blowup",
                result.alphabet_mismatches.len()
            ),
            hint: Some("consider restricting call/return patterns to reduce nondeterminism".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_v06_weighted_vpa_inclusion_failure(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.vpa_result {
        Some(r) => r,
        None => return,
    };
    // Non-determinizable VPA with large state count suggests inclusion
    // checking will be expensive or may fail.
    if !result.is_determinizable && result.state_count > 20 {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::V06,
            name: "weighted-vpa-inclusion-failure",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "weighted VPA inclusion check may fail — {} states and non-determinizable",
                result.state_count
            ),
            hint: Some("tighten recovery predicates or increase cost thresholds".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── Parity Tree Automata (PT01-PT03) ─────────────────────────────────────────

pub(crate) fn lint_pt01_pata_emptiness_violation(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.parity_tree_result {
        Some(r) => r,
        None => return,
    };
    if result.is_empty {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::PT01,
            name: "pata-emptiness-violation",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: "parity tree automaton is empty — no AST can match this predicate".to_string(),
            hint: Some("check that the mu-calculus formula is not vacuously false".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_pt02_pata_subsumption(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.parity_tree_result {
        Some(r) => r,
        None => return,
    };
    if result.num_states > 0 && result.max_priority == 0 {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::PT02,
            name: "pata-subsumption",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "PATA has {} states but max_priority=0 — all states have trivial parity",
                result.num_states
            ),
            hint: Some("consider simplifying to a non-parity tree automaton".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_pt03_pata_high_priority(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.parity_tree_result {
        Some(r) => r,
        None => return,
    };
    if result.priority_depth > 4 {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::PT03,
            name: "pata-high-priority",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "PATA priority depth {} > 4 — exponential blowup in emptiness checking",
                result.priority_depth
            ),
            hint: Some("reduce fixpoint nesting to improve analysis performance".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── Register Automata (RA01-RA03) ────────────────────────────────────────────

pub(crate) fn lint_ra01_unbound_data_reference(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.register_result {
        Some(r) => r,
        None => return,
    };
    for (trans_idx, reg_idx) in &result.unbound_references {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::RA01,
            name: "unbound-data-reference",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "transition {} tests register {} which has no reachable Store operation",
                trans_idx, reg_idx
            ),
            hint: Some("ensure the register is stored before being tested".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_ra02_redundant_register(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.register_result {
        Some(r) => r,
        None => return,
    };
    for reg_idx in &result.dead_registers {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::RA02,
            name: "redundant-register",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!("register {} is written but never tested", reg_idx),
            hint: Some("remove the unused register to simplify the automaton".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_ra03_register_equivalence(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.register_result {
        Some(r) => r,
        None => return,
    };
    // Flag when all registers are dead — suggests the RA is effectively a plain FA.
    if result.num_registers > 0 && result.dead_registers.len() == result.num_registers {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::RA03,
            name: "register-equivalence",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "all {} registers are dead — automaton is equivalent to a plain FA",
                result.num_registers
            ),
            hint: Some("consider using a standard FA instead of a register automaton".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── Probabilistic Automata (PR01-PR04) ───────────────────────────────────────

pub(crate) fn lint_pr01_low_selectivity_rule(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.probabilistic_result {
        Some(r) => r,
        None => return,
    };
    for rule in &result.low_selectivity_rules {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::PR01,
            name: "low-selectivity-rule",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!("rule '{}' handles <1% of expected inputs", rule),
            hint: Some("consider removing or specializing this low-frequency rule".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_pr02_non_stochastic_state(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.probabilistic_result {
        Some(r) => r,
        None => return,
    };
    if !result.is_normalized {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::PR02,
            name: "non-stochastic-state",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: "probabilistic automaton has non-normalized transition weights".to_string(),
            hint: Some("call normalize() to ensure outgoing probabilities sum to 1".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_pr03_high_entropy_category(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.probabilistic_result {
        Some(r) => r,
        None => return,
    };
    // High entropy (> 2.0 nats ~ > 7 equally-likely alternatives) suggests ambiguity.
    if result.mean_entropy > 2.0 {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::PR03,
            name: "high-entropy-category",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "mean entropy {:.2} nats — many equally-likely alternatives suggest ambiguity",
                result.mean_entropy
            ),
            hint: Some(
                "add disambiguation weights or reduce the number of alternatives".to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_pr04_expected_depth_anomaly(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.probabilistic_result {
        Some(r) => r,
        None => return,
    };
    // Selectivity very close to 0 suggests the automaton barely accepts anything.
    if result.total_selectivity < 0.01 && result.num_states > 1 {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::PR04,
            name: "expected-depth-anomaly",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "total selectivity {:.4} — automaton barely accepts any inputs",
                result.total_selectivity
            ),
            hint: Some(
                "check that grammar rules cover the expected input distribution".to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── Multi-Tape Automata (MT01-MT02) ──────────────────────────────────────────

pub(crate) fn lint_mt01_multi_channel_overlap(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.multi_tape_result {
        Some(r) => r,
        None => return,
    };
    for (t1, t2) in &result.overlapping_tapes {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::MT01,
            name: "multi-channel-overlap",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "tapes {} and {} are constrained to identical patterns (redundant channel)",
                t1, t2
            ),
            hint: Some("merge the overlapping tapes into a single tape".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_mt02_multi_tape_disconnected(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.multi_tape_result {
        Some(r) => r,
        None => return,
    };
    for tape_idx in &result.disconnected_tapes {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::MT02,
            name: "multi-tape-disconnected",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "tape {} has no auto-intersection constraints (independent channel)",
                tape_idx
            ),
            hint: Some("the disconnected tape can be analyzed independently".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── Multiset Automata (MS01-MS02) ────────────────────────────────────────────

pub(crate) fn lint_ms01_unsatisfiable_cardinality(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.multiset_result {
        Some(r) => r,
        None => return,
    };
    for constraint in &result.unsatisfiable_constraints {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::MS01,
            name: "unsatisfiable-cardinality",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "cardinality constraint on feature '{}' ([{}, {}]) is unsatisfiable",
                constraint.feature,
                constraint.min.map_or("*".to_string(), |v| v.to_string()),
                constraint.max.map_or("*".to_string(), |v| v.to_string()),
            ),
            hint: Some(
                "relax the cardinality constraint or add more feature-producing rules".to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_ms02_redundant_feature_check(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.multiset_result {
        Some(r) => r,
        None => return,
    };
    // If there are no unsatisfiable constraints and no feature interactions,
    // the multiset analysis is trivially satisfied.
    if result.num_features > 0
        && result.feature_interactions.is_empty()
        && result.unsatisfiable_constraints.is_empty()
    {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::MS02,
            name: "redundant-feature-check",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "all {} features are independent with trivially satisfied constraints",
                result.num_features
            ),
            hint: Some("multiset analysis adds no value for independent features".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── Weighted MSO Logic (MSO01-MSO03) ─────────────────────────────────────────

pub(crate) fn lint_mso01_unrestricted_universal_set(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.mso_result {
        Some(r) => r,
        None => return,
    };
    use crate::weighted_mso::MsoFormulaClass;
    if matches!(result.formula_class, MsoFormulaClass::Full) {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::MSO01,
            name: "unrestricted-universal-set",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message:
                "formula uses unrestricted \u{2200}X (full MSO \u{2014} not recognizable, T3/T4)"
                    .to_string(),
            hint: Some(
                "restrict to \u{2203}X quantification or bounded \u{2200}x for decidability"
                    .to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_mso02_non_recognizable_step(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.mso_result {
        Some(r) => r,
        None => return,
    };
    use crate::symbolic::DecidabilityTier;
    if matches!(
        result.decidability,
        DecidabilityTier::SemiDecidable | DecidabilityTier::Undecidable
    ) {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::MSO02,
            name: "non-recognizable-step",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "formula decidability tier {} \u{2014} \u{2200}x body is not a recognizable step function",
                result.decidability
            ),
            hint: Some("provide a user proof/assertion or restrict to first-order fragment".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_mso03_equivalent_formulas(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.mso_result {
        Some(r) => r,
        None => return,
    };
    // If the formula is a sentence with no free variables, note it for potential optimization.
    if result.is_sentence && !result.free_vars.is_empty() {
        // This shouldn't happen (sentence = no free vars), but flag inconsistency.
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::MSO03,
            name: "equivalent-formulas",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: "MSO formula is marked as sentence but has free variables \u{2014} internal inconsistency".to_string(),
            hint: Some("check formula construction for variable binding errors".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── Two-Way Transducers (TW01-TW03) ─────────────────────────────────────────

pub(crate) fn lint_tw01_circular_channel_dependency(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.two_way_result {
        Some(r) => r,
        None => return,
    };
    for cycle in &result.deadlock_cycles {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::TW01,
            name: "circular-channel-dependency",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!("circular channel dependency detected: {}", cycle.join(" \u{2192} ")),
            hint: Some("break the circular dependency to prevent deadlock".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_tw02_one_way_sufficient(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.two_way_result {
        Some(r) => r,
        None => return,
    };
    if result.is_one_way_equivalent && result.num_backward == 0 {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::TW02,
            name: "one-way-sufficient",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "two-way transducer ({} states, 0 backward) is one-way equivalent \u{2014} one-way transducer suffices",
                result.num_states
            ),
            hint: Some("use a standard one-way transducer for simpler implementation".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_tw03_constraint_propagation_divergent(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.two_way_result {
        Some(r) => r,
        None => return,
    };
    // If there are backward states and deadlock cycles, constraint propagation may diverge.
    if result.num_backward > 0 && !result.deadlock_cycles.is_empty() {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::TW03,
            name: "constraint-propagation-divergent",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "backward constraint propagation may diverge: {} backward states with {} deadlock cycles",
                result.num_backward, result.deadlock_cycles.len()
            ),
            hint: Some("add a propagation depth limit or break the deadlock cycles".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── Symbolic Finite Transducers (SFT01-SFT04) ────────────────────────────────

/// SFT01: SFT has empty domain (dead transduction — no input ever triggers it).
pub(crate) fn lint_sft01_empty_domain(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.sft_result {
        Some(r) => r,
        None => return,
    };
    for label in &result.empty_domain_labels {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::SFT01,
            name: "empty-domain-transduction",
            severity: LintSeverity::Warning,
            category: None,
            rule: Some(label.clone()),
            message: format!(
                "SFT '{}' has empty domain \u{2014} no input word ever triggers this transduction",
                label
            ),
            hint: Some("remove the dead transduction or fix its guard predicates".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

/// SFT02: SFT always produces the same constant output (simplifiable).
pub(crate) fn lint_sft02_constant_output(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.sft_result {
        Some(r) => r,
        None => return,
    };
    for label in &result.constant_output_labels {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::SFT02,
            name: "constant-output-transduction",
            severity: LintSeverity::Note,
            category: None,
            rule: Some(label.clone()),
            message: format!(
                "SFT '{}' always produces the same constant output \u{2014} simplifiable to a constant function",
                label
            ),
            hint: Some("replace with a constant mapping to reduce transducer complexity".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

/// SFT03: SFT is not single-valued (nondeterministic output).
pub(crate) fn lint_sft03_nondeterministic(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.sft_result {
        Some(r) => r,
        None => return,
    };
    let nonfunctional_count = result
        .num_transducers
        .saturating_sub(result.functional_count);
    if nonfunctional_count > 0 {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::SFT03,
            name: "nondeterministic-transduction",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "{} SFT(s) are nondeterministic (not single-valued) \u{2014} some inputs may produce multiple outputs",
                nonfunctional_count
            ),
            hint: Some("ensure guard predicates are disjoint or merge overlapping transitions".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

/// SFT04: Two SFTs produce identical input-output behavior (dedup opportunity).
pub(crate) fn lint_sft04_equivalent_pair(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.sft_result {
        Some(r) => r,
        None => return,
    };
    for (a, b) in &result.equivalent_pairs {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::SFT04,
            name: "equivalent-transductions",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "SFTs '{}' and '{}' produce identical input-output behavior \u{2014} deduplication opportunity",
                a, b
            ),
            hint: Some("merge equivalent transducers to reduce analysis overhead".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// EG01–EG04: E-Graph Equality Saturation Lints
// ══════════════════════════════════════════════════════════════════════════════

/// EG01: E-graph saturation discovered non-obvious equivalences.
pub(crate) fn lint_eg01_discovered_equivalences(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.egraph_result {
        Some(r) => r,
        None => return,
    };
    for (a, b) in &result.discovered_equivalences {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::EG01,
            name: "discovered-equivalence",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "equality saturation discovered non-obvious equivalence: {} \u{2261} {}",
                a, b
            ),
            hint: Some(
                "review whether this equivalence is intentional; it may indicate redundant rules"
                    .to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

/// EG02: Guard expression simplifiable via equality saturation.
pub(crate) fn lint_eg02_simplifiable_guard(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.egraph_result {
        Some(r) => r,
        None => return,
    };
    for (original, simplified) in &result.simplified_guards {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::EG02,
            name: "simplifiable-guard",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "guard expression '{}' can be simplified to '{}' via equality saturation",
                original, simplified
            ),
            hint: Some("consider replacing with the simpler equivalent form".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

/// EG03: Saturation did not converge within iteration limit.
pub(crate) fn lint_eg03_saturation_non_convergence(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.egraph_result {
        Some(r) => r,
        None => return,
    };
    if !result.converged {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::EG03,
            name: "saturation-non-convergence",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "e-graph equality saturation did not converge after {} iterations ({} e-classes, {} e-nodes) \
                 \u{2014} results may be incomplete",
                result.saturation_iterations, result.num_eclasses, result.num_enodes
            ),
            hint: Some("increase iteration/node limits or simplify the rewrite system".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

/// EG04: E-graph found joinability witness for critical pair that normalization couldn't.
pub(crate) fn lint_eg04_joinability_witness(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.egraph_result {
        Some(r) => r,
        None => return,
    };
    for (pair_idx, witness) in &result.joinability_witnesses {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::EG04,
            name: "joinability-witness",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "e-graph found joinability witness for critical pair #{} that normalization could not: {}",
                pair_idx, witness
            ),
            hint: Some("this critical pair is joinable via equality saturation \u{2014} the TRS may be more confluent than normalization alone suggests".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// PD01–PD04: Predicate Dispatch Lints
// ══════════════════════════════════════════════════════════════════════════════

/// PD01: Predicate activates no specialized module beyond base (M1 + M10).
///
/// Indicates a trivially evaluable guard that may be removable.
pub(crate) fn lint_pd01_degenerate_predicate(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let diag = match ctx.dispatch_diagnostics {
        Some(d) => d,
        None => return,
    };
    for &idx in &diag.degenerate_predicates {
        let profile = &diag.profiles[idx];
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::PD01,
            name: "degenerate-predicate",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "predicate guard #{} activates no specialized module (signature = {})",
                idx, profile.signature
            ),
            hint: Some(
                "consider removing the trivially-true guard or adding a structural constraint"
                    .to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

/// PD02: Predicate activates all 11 modules (no dispatch benefit).
pub(crate) fn lint_pd02_all_modules_activated(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let diag = match ctx.dispatch_diagnostics {
        Some(d) => d,
        None => return,
    };
    for &idx in &diag.full_activation_predicates {
        let profile = &diag.profiles[idx];
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::PD02,
            name: "all-modules-activated",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!(
                "predicate guard #{} activates all {} modules — no dispatch benefit (signature = {})",
                idx,
                crate::predicate_dispatch::PredicateSignature::NUM_MODULES,
                profile.signature
            ),
            hint: Some("decompose the predicate into simpler sub-predicates for targeted dispatch".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

/// PD03: Dispatch savings report (informational).
pub(crate) fn lint_pd03_dispatch_savings(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let diag = match ctx.dispatch_diagnostics {
        Some(d) => d,
        None => return,
    };
    if diag.total_modules_skipped > 0 {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::PD03,
            name: "dispatch-savings",
            severity: LintSeverity::Info,
            category: None,
            rule: None,
            message: format!(
                "predicate dispatch skipped {} module invocation(s)",
                diag.total_modules_skipped
            ),
            hint: None,
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

/// PD04: Cross-channel predicate detected but `two-way-transducer` feature not enabled.
pub(crate) fn lint_pd04_missing_feature_gate(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let diag = match ctx.dispatch_diagnostics {
        Some(d) => d,
        None => return,
    };
    for &idx in &diag.cross_channel_without_two_way {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::PD04,
            name: "missing-feature-gate",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "predicate guard #{} has cross-channel constraints but `two-way-transducer` feature is not enabled",
                idx
            ),
            hint: Some("enable the `two-way-transducer` feature to analyze cross-channel constraint propagation".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ── Constraint theory lints (PB01–PB03, UN01–UN03, SL01–SL02, LT01) ─────────

pub(crate) fn lint_pb01_unsatisfiable_arithmetic_guard(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.presburger_result {
        Some(r) => r,
        None => return,
    };
    for (desc, rule) in &result.unsatisfiable_guards {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::PB01,
            name: "unsatisfiable-arithmetic-guard",
            severity: LintSeverity::Warning,
            category: None,
            rule: Some(rule.clone()),
            message: format!("arithmetic guard '{}' is unsatisfiable (dead code)", desc),
            hint: Some("remove the unreachable guard or relax its numeric constraint".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_pb02_tautological_arithmetic_guard(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.presburger_result {
        Some(r) => r,
        None => return,
    };
    for (desc, rule) in &result.tautological_guards {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::PB02,
            name: "tautological-arithmetic-guard",
            severity: LintSeverity::Note,
            category: None,
            rule: Some(rule.clone()),
            message: format!("arithmetic guard '{}' is always satisfied (tautological)", desc),
            hint: Some("remove the redundant guard to simplify the rule".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_pb03_subsumed_arithmetic_guard(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.presburger_result {
        Some(r) => r,
        None => return,
    };
    for (subsuming, subsumed, rule) in &result.subsumed_guards {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::PB03,
            name: "subsumed-arithmetic-guard",
            severity: LintSeverity::Note,
            category: None,
            rule: Some(rule.clone()),
            message: format!(
                "arithmetic guard '{}' is subsumed by '{}' (redundant)",
                subsumed, subsuming
            ),
            hint: Some("the subsuming guard already covers this constraint".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_un01_unsatisfiable_unification_guard(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.unification_result {
        Some(r) => r,
        None => return,
    };
    for (desc, rule) in &result.unsatisfiable_guards {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::UN01,
            name: "unsatisfiable-unification-guard",
            severity: LintSeverity::Warning,
            category: None,
            rule: Some(rule.clone()),
            message: format!(
                "unification guard '{}' is unsatisfiable (constructor clash or occurs check)",
                desc
            ),
            hint: Some("remove the unreachable guard or fix the structural pattern".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_un02_tautological_unification_guard(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.unification_result {
        Some(r) => r,
        None => return,
    };
    for (desc, rule) in &result.tautological_guards {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::UN02,
            name: "tautological-unification-guard",
            severity: LintSeverity::Note,
            category: None,
            rule: Some(rule.clone()),
            message: format!(
                "unification guard '{}' is trivially satisfiable (always matches)",
                desc
            ),
            hint: Some("remove the redundant unification guard".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_un03_subsumed_unification_guard(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.unification_result {
        Some(r) => r,
        None => return,
    };
    for (general, specific, rule) in &result.subsumed_guards {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::UN03,
            name: "subsumed-unification-guard",
            severity: LintSeverity::Note,
            category: None,
            rule: Some(rule.clone()),
            message: format!(
                "unification guard '{}' is subsumed by more general pattern '{}'",
                specific, general
            ),
            hint: Some("the more general pattern already covers this case".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_sl01_unsatisfiable_subtype_constraint(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.lattice_result {
        Some(r) => r,
        None => return,
    };
    for (desc, rule) in &result.unsatisfiable_constraints {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::SL01,
            name: "unsatisfiable-subtype-constraint",
            severity: LintSeverity::Warning,
            category: None,
            rule: Some(rule.clone()),
            message: format!(
                "subtype constraint '{}' is contradictory (unsatisfiable type hierarchy)",
                desc
            ),
            hint: Some("check subtype declarations for conflicting edges".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_sl02_redundant_subtype_constraint(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.lattice_result {
        Some(r) => r,
        None => return,
    };
    for (desc, rule) in &result.redundant_constraints {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::SL02,
            name: "redundant-subtype-constraint",
            severity: LintSeverity::Note,
            category: None,
            rule: Some(rule.clone()),
            message: format!("subtype constraint '{}' is already implied by transitivity", desc),
            hint: Some(
                "remove the redundant constraint \u{2014} it follows from existing edges"
                    .to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_lt01_search_bound_exceeded(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    // LT01 is emitted when LogicT search hits its depth limit.
    // Any ConstraintTheory with non-empty label() can trigger it.

    // Presburger: decidable theory — label() returns empty, search bound never exceeded.
    // Lattice theory: decidable — search bound never exceeded.

    // Unification: may exceed on deeply nested CustomMatch alternatives.
    if let Some(result) = ctx.unification_result {
        for desc in &result.search_bound_exceeded {
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::LT01,
                name: "logict-search-bound-exceeded",
                severity: LintSeverity::Warning,
                category: None,
                rule: None,
                message: format!("LogicT search bound exceeded while solving constraint: {}", desc),
                hint: Some("increase the search bound or simplify the constraint".to_string()),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

// ── Refinement type lints (RT01–RT06) ─────────────────────────────────────────

pub(crate) fn lint_rt01_unsatisfiable_refinement(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.refinement_analysis {
        Some(r) => r,
        None => return,
    };
    for (name, reason) in &result.unsatisfiable {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::RT01,
            name: "unsatisfiable-refinement-predicate",
            severity: LintSeverity::Warning,
            category: None,
            rule: Some(name.clone()),
            message: format!(
                "refinement type '{}' has unsatisfiable predicate: {} (dead type)",
                name, reason
            ),
            hint: Some("remove the unreachable refinement type or relax its predicate".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_rt02_tautological_refinement(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.refinement_analysis {
        Some(r) => r,
        None => return,
    };
    for (name, reason) in &result.tautological {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::RT02,
            name: "tautological-refinement-predicate",
            severity: LintSeverity::Note,
            category: None,
            rule: Some(name.clone()),
            message: format!(
                "refinement type '{}' is equivalent to its base type: {}",
                name, reason
            ),
            hint: Some(
                "remove the redundant refinement \u{2014} the predicate is always satisfied"
                    .to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_rt03_empty_intersection(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.refinement_analysis {
        Some(r) => r,
        None => return,
    };
    for (type_a, type_b, reason) in &result.empty_intersections {
        // When the structural recognizer (`.1`) supplied an inhabitation witness
        // for the base category these two refinements share, append it to the
        // hint: it concretely shows a term of the base category, contextualizing
        // *which* base-category terms the two disjoint patterns carve up.
        let base_witness = result
            .dispatch_analysis
            .as_ref()
            .and_then(|d| {
                d.base_type_groups.iter().find_map(|(base, names)| {
                    if names.iter().any(|n| n == type_a) && names.iter().any(|n| n == type_b) {
                        Some(base.clone())
                    } else {
                        None
                    }
                })
            })
            .and_then(|base| {
                result
                    .structural_witnesses
                    .iter()
                    .find(|(cat, _)| *cat == base)
                    .map(|(cat, w)| (cat.clone(), w.clone()))
            });
        let hint = match base_witness {
            Some((cat, w)) => format!(
                "no value can inhabit both types simultaneously (e.g. the base \
                 category '{cat}' is inhabited by '{w}')"
            ),
            None => "no value can inhabit both types simultaneously".to_string(),
        };
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::RT03,
            name: "empty-refinement-intersection",
            severity: LintSeverity::Warning,
            category: None,
            rule: None,
            message: format!(
                "refinement types '{}' and '{}' have empty intersection: {}",
                type_a, type_b, reason
            ),
            hint: Some(hint),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_rt04_subtype_detected(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.refinement_analysis {
        Some(r) => r,
        None => return,
    };
    for (sub, sup) in &result.subtype_pairs {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::RT04,
            name: "refinement-subtype-detected",
            severity: LintSeverity::Note,
            category: None,
            rule: None,
            message: format!("refinement type '{}' is a subtype of '{}'", sub, sup),
            hint: Some("this subtyping relationship is used for dispatch optimization".to_string()),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_rt05_decidability_tier(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.refinement_analysis {
        Some(r) => r,
        None => return,
    };
    for (name, tier) in &result.decidability_tiers {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::RT05,
            name: "refinement-decidability-tier",
            severity: LintSeverity::Note,
            category: None,
            rule: Some(name.clone()),
            message: format!("refinement type '{}' predicate classified as {}", name, tier),
            hint: None,
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

pub(crate) fn lint_rt06_name_shadow(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.refinement_analysis {
        Some(r) => r,
        None => return,
    };
    for (refinement_name, base_name) in &result.name_shadows {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::RT06,
            name: "refinement-type-shadows-base",
            severity: LintSeverity::Warning,
            category: None,
            rule: Some(refinement_name.clone()),
            message: format!(
                "refinement type '{}' shadows base type '{}'",
                refinement_name, base_name
            ),
            hint: Some(
                "rename the refinement type to avoid ambiguity with the base type".to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

/// RT07: Surface OSLF Phase-4 `.1` transducer dead-cast findings as RT-notes.
///
/// A cast rule `r : src → tgt` whose symbolic-tree-transducer pre-image has an
/// empty intersection with the source category's term automaton can never fire
/// (no source term is cast-reachable). [`analyze_refinement_types`](crate::pipeline::analysis::analyze_refinement_types)
/// records each such `(cast_label, reason)` in `RefinementAnalysisResult::dead_casts`;
/// this lint emits one informational note per finding. Mirrors the
/// `structural_witnesses` `.1` surfacing pattern.
///
/// Severity: Note (informational — the cast is dead code).
pub(crate) fn lint_rt07_dead_cast(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.refinement_analysis {
        Some(r) => r,
        None => return,
    };
    for (label, reason) in &result.dead_casts {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::RT07,
            name: "unreachable-cast",
            severity: LintSeverity::Note,
            category: None,
            rule: Some(label.clone()),
            message: format!("RT-note: cast `{label}` is unreachable (empty pre-image)"),
            hint: Some(format!("{reason}; remove the cast rule or relax its source pattern")),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

/// LP01: Surface OSLF Phase 5 `.1` dead behavioral types as RT-notes.
///
/// A `letprop` recursive behavioral predicate whose Parity Alternating Tree
/// Automaton (PATA) is EMPTY can never be satisfied by any AST — the behavioral
/// type is dead. [`analyze_recursive_predicates`](crate::parity_tree::analyze_recursive_predicates)
/// records each predicate's satisfiability (PATA non-emptiness) verdict in
/// [`ParityTreeAnalysis::fixpoint_decisions`](crate::parity_tree::ParityTreeAnalysis);
/// this lint emits one informational note per `false` (unsatisfiable) verdict.
/// Mirrors the RT07 transducer dead-cast surfacing pattern exactly.
///
/// On every current grammar `fixpoint_decisions` is EMPTY (no surface syntax
/// produces a `letprop` recursive predicate yet — a tracked follow-up touching
/// `ast/`), so this lint is inert and fires nothing.
///
/// Severity: Note (informational — the behavioral type is dead code).
pub(crate) fn lint_lp01_dead_behavioral_type(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let result = match ctx.parity_tree_result {
        Some(r) => r,
        None => return,
    };
    for (name, satisfiable) in &result.fixpoint_decisions {
        if !satisfiable {
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::LP01,
                name: "dead-behavioral-type",
                severity: LintSeverity::Note,
                category: None,
                rule: Some(name.clone()),
                message: format!(
                    "RT-note: recursive behavioral type `{name}` is unsatisfiable \
                     (its parity tree automaton is empty — no AST can match it)"
                ),
                hint: Some(
                    "the letprop fixpoint has no inhabiting AST; remove the predicate or \
                     add a reachable base case to its recursion"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}

/// HM01: Surface OSLF Phase 6 `.1` base-sort inconsistencies as HM-notes.
///
/// A grammar rule whose constructor's inferred result sort disagrees with its
/// declared category (a field references a category that cannot `unify` with its
/// use) is a base-sort inconsistency.
/// [`analyze_from_bundle`](crate::hindley_milner::analyze_from_bundle) records
/// each such `(rule_label, reason)` in
/// [`HmInferenceAnalysis::sort_mismatches`](crate::hindley_milner::HmInferenceAnalysis);
/// this lint emits one informational note per finding. Mirrors the RT07
/// transducer dead-cast / LP01 dead-behavioral-type surfacing pattern exactly.
///
/// On every well-formed grammar `sort_mismatches` is EMPTY (every field category
/// is declared ⇒ the inferred and declared constructor arrows unify), so this
/// lint is inert and fires nothing.
///
/// Severity: Note (informational — a base-sort inconsistency in the grammar).
pub(crate) fn lint_hm01_sort_mismatch(ctx: &LintContext, diagnostics: &mut Vec<LintDiagnostic>) {
    let result = match ctx.hindley_result {
        Some(r) => r,
        None => return,
    };
    for (label, reason) in &result.sort_mismatches {
        diagnostics.push(LintDiagnostic {
            id: DiagnosticId::HM01,
            name: "sort-mismatch",
            severity: LintSeverity::Note,
            category: None,
            rule: Some(label.clone()),
            message: format!(
                "HM-note: constructor `{label}` inferred sort disagrees with its \
                 declaration ({reason})"
            ),
            hint: Some(
                "a constructor field references a category that cannot unify with its \
                 declared use; correct the field's category or the rule's declared sort"
                    .to_string(),
            ),
            grammar_name: Some(ctx.grammar_name.to_string()),
            source_location: None,
        });
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// CEK Machine Lints
// ══════════════════════════════════════════════════════════════════════════════

/// CEK01: Detect frame variants carrying captures that are never referenced
/// by subsequent segments or the final constructor.
///
/// Severity: Note (informational — optimization opportunity).
pub(crate) fn lint_cek01_dead_capture_in_frame(
    ctx: &LintContext,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    use crate::rd_analysis::{
        capture_name, compute_live_captures, constructor_capture_names, split_rd_handler,
    };

    for rd_rule in ctx.rd_rules {
        let segments = split_rd_handler(rd_rule);
        if segments.len() < 2 {
            continue; // No multi-segment rules, no dead captures possible
        }

        let ctor_names = constructor_capture_names(rd_rule);
        let live_captures = compute_live_captures(&segments, &ctor_names);

        for (i, (seg, live)) in segments.iter().zip(live_captures.iter()).enumerate() {
            // Skip segments without nonterminals (no frame is pushed)
            if seg.nonterminal.is_none() {
                continue;
            }

            let dead_count = seg.accumulated_captures.len() - live.len();
            if dead_count > 0 {
                let dead_names: Vec<String> = seg
                    .accumulated_captures
                    .iter()
                    .filter(|cap| !live.iter().any(|l| capture_name(l) == capture_name(cap)))
                    .map(|cap| capture_name(cap))
                    .collect();

                diagnostics.push(LintDiagnostic {
                    id: DiagnosticId::CEK01,
                    name: "dead-capture-in-frame",
                    severity: LintSeverity::Note,
                    category: Some(rd_rule.category.clone()),
                    rule: Some(rd_rule.label.clone()),
                    message: format!(
                        "frame variant `{}` segment {} carries {} dead capture(s): {}",
                        seg.frame_variant,
                        i,
                        dead_count,
                        dead_names.join(", "),
                    ),
                    hint: Some(
                        "enable CEK01:EnvironmentTrimming to eliminate dead captures from frame variants"
                            .to_string(),
                    ),
                    grammar_name: Some(ctx.grammar_name.to_string()),
                    source_location: None,
                });
            }
        }
    }
}

/// CEK03: Unreachable frame variant detected by WPDS poststar analysis.
///
/// Reports frame variants that are unreachable in any valid stack context,
/// as determined by the P-automaton from WPDS poststar saturation.
/// When enabled, the codegen suppresses these variants, their prefix arms,
/// and their unwind handlers.
pub(crate) fn lint_cek03_unreachable_frame_variant(
    ctx: &LintContext<'_>,
    diagnostics: &mut Vec<LintDiagnostic>,
) {
    let analysis = match ctx.wpds_analysis {
        Some(a) => a,
        None => return,
    };

    for (frame_name, symbol) in &analysis.cek_bijection.frame_to_symbol {
        // Skip internal symbols
        if frame_name.starts_with("::") {
            continue;
        }
        if !analysis.pautomaton.is_symbol_in_any_configuration(symbol) {
            // Stage 3.27c (2026-05-04): WPDS-architecture renaming. Frame
            // enums no longer exist post-Stage-10 trampoline excision; the
            // CEK bijection now maps WPDS rule positions (StackSymbol) to
            // CEK reachability. The lint name and message reflect the
            // current architecture: "rule position" not "frame variant".
            // The diagnostic ID `CEK03` is preserved for stable consumer
            // wiring; only the human-readable name/message text changes.
            diagnostics.push(LintDiagnostic {
                id: DiagnosticId::CEK03,
                name: "unreachable-rule-position",
                severity: LintSeverity::Note,
                category: None,
                rule: None,
                message: format!(
                    "rule position '{}' is unreachable in all valid stack contexts",
                    frame_name,
                ),
                hint: Some(
                    "enable CEK03:DeadFrameElimination to suppress codegen for unreachable rule positions"
                        .to_string(),
                ),
                grammar_name: Some(ctx.grammar_name.to_string()),
                source_location: None,
            });
        }
    }
}
