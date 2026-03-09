//! Ascent antipattern detection (C-AP01 through C-AP05).
//!
//! These compile-time lint detectors fire during macro expansion to warn about
//! common Ascent Datalog performance antipatterns in user-defined `logic {}` blocks
//! and in the grammar's equations/rewrites/constructors.
//!
//! ## Detectors
//!
//! - **C-AP01**: Cubic transitivity blowup — `R(x,z) <-- R(x,y), R(y,z)`
//! - **C-AP02**: Quadratic extension-along-equality — join on equivalence relation
//! - **C-AP03**: Deep congruence chains — self-recursive constructor field graphs
//! - **C-AP04**: Unbounded term growth via rewrite feedback — positive depth delta
//! - **C-AP05**: Clone storm on large ASTs — collection fields in constructors

use crate::ast::grammar::{GrammarItem, TermParam};
use crate::ast::language::LanguageDef;
use crate::ast::types::{CollectionType, TypeExpr};
use std::collections::{HashMap, HashSet};

/// A compile-time antipattern warning.
#[derive(Debug, Clone)]
pub struct AntipatternWarning {
    /// Lint code: "C-AP01", "C-AP02", etc.
    pub code: &'static str,
    /// Human-readable diagnostic message.
    pub message: String,
    /// Optional hint/suggestion for remediation.
    pub hint: Option<String>,
}

/// Detect all Ascent antipatterns in a language definition.
///
/// Runs C-AP01 through C-AP05 and returns a collected list of warnings.
pub fn detect_antipatterns(lang: &LanguageDef) -> Vec<AntipatternWarning> {
    let mut warnings = Vec::new();

    // C-AP01: Cubic transitivity blowup (user logic blocks)
    warnings.extend(detect_cubic_transitivity(lang));

    // C-AP02: Quadratic extension-along-equality (user logic blocks)
    warnings.extend(detect_extension_along_equality(lang));

    // C-AP03: Deep congruence chains (grammar constructor fields)
    warnings.extend(detect_deep_congruence_chains(lang));

    // C-AP04: Unbounded term growth via rewrite feedback
    warnings.extend(detect_unbounded_rewrite_growth(lang));

    // C-AP05: Clone storm on large ASTs (collection fields)
    warnings.extend(detect_clone_storm(lang));

    warnings
}

// ══════════════════════════════════════════════════════════════════════════════
// C-AP01: Cubic Transitivity Blowup
// ══════════════════════════════════════════════════════════════════════════════

/// Detect transitivity-shaped rules in user-defined `logic {}` blocks.
///
/// Pattern: `R(x, z) <-- R(x, y), R(y, z)` where R appears in both head and
/// body with shared variables forming a chain. This creates O(n^3) intermediate
/// tuples in the worst case.
fn detect_cubic_transitivity(lang: &LanguageDef) -> Vec<AntipatternWarning> {
    let logic = match &lang.logic {
        Some(l) => l,
        None => return Vec::new(),
    };

    // Re-parse the logic block's token stream to get structured AST
    let program = match ascent_syntax_export::parse_ascent_program_tokens(logic.content.clone()) {
        Ok(p) => p,
        Err(_) => return Vec::new(), // parse error is handled elsewhere
    };

    let mut warnings = Vec::new();

    for rule in &program.rules {
        // Extract head relation names and their argument expressions
        let head_clauses: Vec<(String, Vec<String>)> = rule
            .head_clauses
            .iter()
            .filter_map(|h| {
                if let ascent_syntax_export::HeadItemNode::HeadClause(cl) = h {
                    let args: Vec<String> = cl.args.iter().map(|a| quote::quote!(#a).to_string()).collect();
                    Some((cl.rel.to_string(), args))
                } else {
                    None
                }
            })
            .collect();

        // Extract body clause relation names and their argument expressions
        let body_clauses: Vec<(String, Vec<String>)> = rule
            .body_items
            .iter()
            .filter_map(|bi| {
                if let ascent_syntax_export::BodyItemNode::Clause(cl) = bi {
                    let args: Vec<String> = cl
                        .args
                        .iter()
                        .map(|a| quote::quote!(#a).to_string())
                        .collect();
                    Some((cl.rel.to_string(), args))
                } else {
                    None
                }
            })
            .collect();

        // For each head clause, check if the same relation appears twice in the body
        // with a chain pattern: R(x,y), R(y,z) in body and R(x,z) in head
        for (head_rel, head_args) in &head_clauses {
            if head_args.len() < 2 {
                continue;
            }

            // Find body clauses with the same relation name
            let same_rel_body: Vec<&Vec<String>> = body_clauses
                .iter()
                .filter(|(rel, _)| rel == head_rel)
                .map(|(_, args)| args)
                .collect();

            if same_rel_body.len() < 2 {
                continue;
            }

            // Check all pairs of body clauses for the chain pattern:
            // body1 = R(a, b), body2 = R(b, c), head = R(a, c)
            // The "chain" is: the second arg of body1 == first arg of body2,
            // first arg of body1 == first arg of head, second arg of body2 == second arg of head
            for i in 0..same_rel_body.len() {
                for j in 0..same_rel_body.len() {
                    if i == j {
                        continue;
                    }
                    let b1 = &same_rel_body[i];
                    let b2 = &same_rel_body[j];
                    if b1.len() >= 2 && b2.len() >= 2 {
                        // Chain pattern: b1[1] == b2[0] (shared join variable)
                        // and b1[0] == head[0] and b2[1] == head[1]
                        if b1[1] == b2[0] && b1[0] == head_args[0] && b2[1] == head_args[1] {
                            warnings.push(AntipatternWarning {
                                code: "C-AP01",
                                message: format!(
                                    "cubic transitivity blowup: rule defines \
                                     `{rel}({x}, {z}) <-- {rel}({x}, {y}), {rel}({y}, {z})` \
                                     which produces O(n^3) intermediate tuples",
                                    rel = head_rel,
                                    x = b1[0],
                                    y = b1[1],
                                    z = b2[1],
                                ),
                                hint: Some(format!(
                                    "consider using `#[ds(crate::eqrel)]` on `{}` or a \
                                     transitive-closure operator to avoid cubic blowup",
                                    head_rel,
                                )),
                            });
                            // Only warn once per head clause
                            break;
                        }
                    }
                }
            }
        }
    }

    warnings
}

// ══════════════════════════════════════════════════════════════════════════════
// C-AP02: Quadratic Extension-Along-Equality
// ══════════════════════════════════════════════════════════════════════════════

/// Detect body clause patterns where a binary relation joins with an equivalence
/// relation on overlapping variables.
///
/// Pattern: `eq_cat(x, y), some_rel(y, z)` where `eq_cat` is recognized as an
/// equivalence relation (auto-generated `eq_*` or user-declared with `#[ds(eqrel)]`).
/// This produces a Cartesian product because equivalence classes can be large.
fn detect_extension_along_equality(lang: &LanguageDef) -> Vec<AntipatternWarning> {
    let logic = match &lang.logic {
        Some(l) => l,
        None => return Vec::new(),
    };

    let program = match ascent_syntax_export::parse_ascent_program_tokens(logic.content.clone()) {
        Ok(p) => p,
        Err(_) => return Vec::new(),
    };

    // Build set of known equivalence relation names:
    // 1. Auto-generated eq_<category> relations
    let mut eq_rels: HashSet<String> = lang
        .types
        .iter()
        .map(|t| format!("eq_{}", t.name.to_string().to_lowercase()))
        .collect();

    // 2. User-declared relations with `#[ds(...eqrel...)]` attribute
    for rel in &program.relations {
        for attr in &rel.attrs {
            let attr_str = quote::quote!(#attr).to_string();
            if attr_str.contains("eqrel") {
                eq_rels.insert(rel.name.to_string());
            }
        }
    }

    let mut warnings = Vec::new();

    for rule in &program.rules {
        let body_clauses: Vec<(String, Vec<String>)> = rule
            .body_items
            .iter()
            .filter_map(|bi| {
                if let ascent_syntax_export::BodyItemNode::Clause(cl) = bi {
                    let args: Vec<String> = cl
                        .args
                        .iter()
                        .map(|a| quote::quote!(#a).to_string())
                        .collect();
                    Some((cl.rel.to_string(), args))
                } else {
                    None
                }
            })
            .collect();

        // For each pair of body clauses: check if one is an eq relation and they
        // share a variable on the equality's output side joined with another relation
        for (i, (rel_a, args_a)) in body_clauses.iter().enumerate() {
            let a_is_eq = eq_rels.contains(rel_a);

            for (j, (rel_b, args_b)) in body_clauses.iter().enumerate() {
                if i == j {
                    continue;
                }

                // We want: eq relation with args (x, y), and another relation using y
                // The "extension" is: for every y equivalent to x, look up some_rel(y, z)
                if a_is_eq && args_a.len() == 2 {
                    // The output variable of the eq relation is the second argument
                    let eq_output = &args_a[1];
                    // Check if this output variable appears in args of the other relation
                    if args_b.contains(eq_output) && !eq_rels.contains(rel_b) {
                        warnings.push(AntipatternWarning {
                            code: "C-AP02",
                            message: format!(
                                "quadratic extension-along-equality: `{eq_rel}({x}, {y})` \
                                 joined with `{other_rel}(...)` on variable `{y}` — \
                                 iterates over the entire equivalence class of `{x}`",
                                eq_rel = rel_a,
                                x = args_a[0],
                                y = eq_output,
                                other_rel = rel_b,
                            ),
                            hint: Some(format!(
                                "consider inlining the equivalence test or using a \
                                 canonical representative to avoid iterating over \
                                 the equivalence class of `{}`",
                                args_a[0],
                            )),
                        });
                    }
                }
            }
        }
    }

    warnings
}

// ══════════════════════════════════════════════════════════════════════════════
// C-AP03: Deep Congruence Chains
// ══════════════════════════════════════════════════════════════════════════════

/// Compute the maximum congruence chain depth from the constructor field graph.
///
/// If a constructor's field refers to the same category (self-recursive),
/// the chain depth is unbounded. If the maximum chain depth exceeds the threshold
/// (default 10), warn about exponential rule application chains in congruence rules.
fn detect_deep_congruence_chains(lang: &LanguageDef) -> Vec<AntipatternWarning> {
    // Build a directed graph: category -> set of categories it references via fields
    let mut field_graph: HashMap<String, HashSet<String>> = HashMap::new();
    let category_set: HashSet<String> = lang.types.iter().map(|t| t.name.to_string()).collect();

    for rule in &lang.terms {
        let src_cat = rule.category.to_string();

        // Collect referenced categories from old-style items
        for item in &rule.items {
            match item {
                GrammarItem::NonTerminal(ident) => {
                    let target = ident.to_string();
                    if category_set.contains(&target) {
                        field_graph.entry(src_cat.clone()).or_default().insert(target);
                    }
                }
                GrammarItem::Binder { category } => {
                    let target = category.to_string();
                    if category_set.contains(&target) {
                        field_graph.entry(src_cat.clone()).or_default().insert(target);
                    }
                }
                GrammarItem::Collection { element_type, .. } => {
                    let target = element_type.to_string();
                    if category_set.contains(&target) {
                        field_graph.entry(src_cat.clone()).or_default().insert(target);
                    }
                }
                GrammarItem::Terminal(_) => {}
            }
        }

        // Collect referenced categories from new-style term_context
        if let Some(params) = &rule.term_context {
            for param in params {
                let targets = collect_category_refs_from_term_param(param, &category_set);
                field_graph.entry(src_cat.clone()).or_default().extend(targets);
            }
        }
    }

    let mut warnings = Vec::new();
    let depth_threshold = 10;

    // Check for self-loops (unbounded depth)
    for (cat, refs) in &field_graph {
        if refs.contains(cat) {
            warnings.push(AntipatternWarning {
                code: "C-AP03",
                message: format!(
                    "deep congruence chain: category `{}` has a self-recursive constructor field — \
                     congruence chain depth is unbounded",
                    cat,
                ),
                hint: Some(format!(
                    "congruence rules for `{}` will apply recursively at every nesting level; \
                     consider bounding the rewrite depth or using explicit recursion control",
                    cat,
                )),
            });
        }
    }

    // Compute maximum chain depth via DFS with cycle detection
    let mut max_depths: HashMap<String, u32> = HashMap::new();
    let mut visited: HashSet<String> = HashSet::new();
    let mut on_stack: HashSet<String> = HashSet::new();

    for cat in &category_set {
        if !max_depths.contains_key(cat) {
            compute_chain_depth(
                cat,
                &field_graph,
                &mut max_depths,
                &mut visited,
                &mut on_stack,
            );
        }
    }

    // Warn for non-self-referential categories that still have deep chains
    for (cat, &depth) in &max_depths {
        if depth > depth_threshold {
            // Skip if we already warned about self-recursion
            let already_warned = field_graph
                .get(cat)
                .map_or(false, |refs| refs.contains(cat));
            if !already_warned {
                let depth_display = if depth == u32::MAX {
                    "unbounded (indirect cycle)".to_string()
                } else {
                    format!("{}", depth)
                };
                warnings.push(AntipatternWarning {
                    code: "C-AP03",
                    message: if depth == u32::MAX {
                        format!(
                            "deep congruence chain: category `{}` has unbounded congruence \
                             chain depth (indirect cycle)",
                            cat,
                        )
                    } else {
                        format!(
                            "deep congruence chain: category `{}` has a maximum congruence \
                             chain depth of {} (threshold: {})",
                            cat, depth_display, depth_threshold,
                        )
                    },
                    hint: Some(format!(
                        "deep congruence chains (depth > {}) cause exponential rule \
                         application; consider flattening the category hierarchy",
                        depth_threshold,
                    )),
                });
            }
        }
    }

    warnings
}

/// Collect category references from a TermParam's type expression.
fn collect_category_refs_from_term_param(
    param: &TermParam,
    category_set: &HashSet<String>,
) -> Vec<String> {
    match param {
        TermParam::Simple { ty, .. } => collect_category_refs_from_type_expr(ty, category_set),
        TermParam::Abstraction { ty, .. } | TermParam::MultiAbstraction { ty, .. } => {
            collect_category_refs_from_type_expr(ty, category_set)
        }
    }
}

/// Collect category references from a TypeExpr.
fn collect_category_refs_from_type_expr(
    ty: &TypeExpr,
    category_set: &HashSet<String>,
) -> Vec<String> {
    match ty {
        TypeExpr::Base(ident) => {
            let name = ident.to_string();
            if category_set.contains(&name) {
                vec![name]
            } else {
                Vec::new()
            }
        }
        TypeExpr::Arrow { domain, codomain } => {
            let mut refs = collect_category_refs_from_type_expr(domain, category_set);
            refs.extend(collect_category_refs_from_type_expr(codomain, category_set));
            refs
        }
        TypeExpr::MultiBinder(inner) => {
            collect_category_refs_from_type_expr(inner, category_set)
        }
        TypeExpr::Collection { element, .. } => {
            collect_category_refs_from_type_expr(element, category_set)
        }
    }
}

/// DFS-based chain depth computation.
///
/// Returns `u32::MAX` for cycles (indicating unbounded depth), otherwise
/// the longest path from the given category to a leaf (category with no outgoing edges).
fn compute_chain_depth(
    cat: &str,
    field_graph: &HashMap<String, HashSet<String>>,
    max_depths: &mut HashMap<String, u32>,
    visited: &mut HashSet<String>,
    on_stack: &mut HashSet<String>,
) -> u32 {
    if let Some(&d) = max_depths.get(cat) {
        return d;
    }
    if on_stack.contains(cat) {
        // Cycle detected — depth is unbounded
        max_depths.insert(cat.to_string(), u32::MAX);
        return u32::MAX;
    }

    visited.insert(cat.to_string());
    on_stack.insert(cat.to_string());

    let depth = if let Some(refs) = field_graph.get(cat) {
        let max_child = refs
            .iter()
            .filter(|r| r.as_str() != cat) // skip self-loops (already handled)
            .map(|r| compute_chain_depth(r, field_graph, max_depths, visited, on_stack))
            .max()
            .unwrap_or(0);
        if max_child == u32::MAX {
            u32::MAX
        } else {
            1 + max_child
        }
    } else {
        0
    };

    on_stack.remove(cat);
    max_depths.insert(cat.to_string(), depth);
    depth
}

// ══════════════════════════════════════════════════════════════════════════════
// C-AP04: Unbounded Term Growth via Rewrite Feedback
// ══════════════════════════════════════════════════════════════════════════════

/// Analyze each rewrite rule's depth delta and warn when positive-delta rules
/// exist without complementary negative-delta rules that could bound the growth.
///
/// This is more targeted than the general A-RT05/A01 analysis: it specifically
/// flags *rewrite* rules (not equations) whose RHS is deeper than LHS, since
/// rewrites are directional and can cause unbounded term growth via feedback loops.
fn detect_unbounded_rewrite_growth(lang: &LanguageDef) -> Vec<AntipatternWarning> {
    if lang.rewrites.is_empty() {
        return Vec::new();
    }

    let results = crate::logic::rules::analyze_depth_delta(lang);
    let mut warnings = Vec::new();

    // Partition rewrite results by category (from rule name prefix or pattern category)
    let mut rewrite_deltas: HashMap<String, Vec<(String, i32)>> = HashMap::new();
    for r in &results {
        if r.is_equation {
            continue; // skip equations — handled by A-RT05/A01
        }

        // Try to determine category from the rewrite pattern (LHS first, then RHS)
        let category = lang
            .rewrites
            .iter()
            .find(|rw| rw.name.to_string() == r.rule_name)
            .and_then(|rw| rw.left.category(lang).or_else(|| rw.right.category(lang)))
            .map(|c| c.to_string())
            .unwrap_or_else(|| "unknown".to_string());

        rewrite_deltas
            .entry(category)
            .or_default()
            .push((r.rule_name.clone(), r.delta));
    }

    // For each category, check if there are positive-delta rewrites without
    // compensating negative-delta rewrites
    for (category, deltas) in &rewrite_deltas {
        let positive: Vec<&(String, i32)> = deltas.iter().filter(|(_, d)| *d > 0).collect();
        let has_negative = deltas.iter().any(|(_, d)| *d < 0);

        if positive.is_empty() {
            continue;
        }

        if !has_negative {
            for (rule_name, delta) in &positive {
                warnings.push(AntipatternWarning {
                    code: "C-AP04",
                    message: format!(
                        "unbounded term growth: rewrite `{}` (category `{}`) has depth \
                         delta +{} with no complementary depth-reducing rewrites in the \
                         same category",
                        rule_name, category, delta,
                    ),
                    hint: Some(format!(
                        "rewrite `{}` increases term depth by {} without any depth-reducing \
                         rewrite to bound growth; this may cause non-convergence in the \
                         Ascent fixpoint. Consider adding a depth-reducing rewrite or \
                         enabling a runtime depth bound",
                        rule_name, delta,
                    )),
                });
            }
        }
    }

    warnings
}

// ══════════════════════════════════════════════════════════════════════════════
// C-AP05: Clone Storm on Large ASTs
// ══════════════════════════════════════════════════════════════════════════════

/// Detect constructors with collection fields (Vec<T>, HashBag<T>, HashSet<T>).
///
/// Congruence rules clone the entire collection on every rule firing, which is
/// expensive for large ASTs. Suggest wrapping collection fields in Rc/Arc.
fn detect_clone_storm(lang: &LanguageDef) -> Vec<AntipatternWarning> {
    let mut warnings = Vec::new();
    // Track (constructor, category) pairs already warned about to avoid
    // duplicate warnings when both old-style GrammarItem::Collection fields
    // and new-style term_context collection expressions match.
    let mut warned: HashSet<(String, String)> = HashSet::new();

    for rule in &lang.terms {
        let constructor = rule.label.to_string();
        let category = rule.category.to_string();

        // Check old-style grammar items for collection fields
        for item in &rule.items {
            if let GrammarItem::Collection {
                coll_type,
                element_type,
                ..
            } = item
            {
                if warned.insert((constructor.clone(), category.clone())) {
                    let coll_name = match coll_type {
                        CollectionType::Vec => "Vec",
                        CollectionType::HashBag => "HashBag",
                        CollectionType::HashSet => "HashSet",
                    };
                    warnings.push(AntipatternWarning {
                        code: "C-AP05",
                        message: format!(
                            "clone storm: constructor `{}` (category `{}`) has a `{}({})` \
                             collection field — congruence rules will clone the entire \
                             collection on every rule firing",
                            constructor,
                            category,
                            coll_name,
                            element_type,
                        ),
                        hint: Some(format!(
                            "consider wrapping the collection field in `Rc<{}<{}>>` or \
                             `Arc<{}<{}>>` to reduce clone overhead in congruence rules",
                            coll_name, element_type, coll_name, element_type,
                        )),
                    });
                }
            }
        }

        // Check new-style term_context for collection type expressions
        if let Some(params) = &rule.term_context {
            for param in params {
                if let Some((coll_name, elem_name)) = extract_collection_from_param(param) {
                    if warned.insert((constructor.clone(), category.clone())) {
                        warnings.push(AntipatternWarning {
                            code: "C-AP05",
                            message: format!(
                                "clone storm: constructor `{}` (category `{}`) has a `{}({})` \
                                 collection field — congruence rules will clone the entire \
                                 collection on every rule firing",
                                constructor, category, coll_name, elem_name,
                            ),
                            hint: Some(format!(
                                "consider wrapping the collection field in `Rc<{}<{}>>` or \
                                 `Arc<{}<{}>>` to reduce clone overhead in congruence rules",
                                coll_name, elem_name, coll_name, elem_name,
                            )),
                        });
                    }
                }
            }
        }
    }

    warnings
}

/// Extract collection type info from a TermParam, if it contains a collection type.
///
/// Returns `Some((collection_type_name, element_type_name))` if the parameter
/// has a collection type at the top level.
fn extract_collection_from_param(param: &TermParam) -> Option<(String, String)> {
    let ty = match param {
        TermParam::Simple { ty, .. } => ty,
        TermParam::Abstraction { ty, .. } | TermParam::MultiAbstraction { ty, .. } => ty,
    };
    extract_collection_from_type_expr(ty)
}

/// Extract collection type info from a TypeExpr.
fn extract_collection_from_type_expr(ty: &TypeExpr) -> Option<(String, String)> {
    match ty {
        TypeExpr::Collection { coll_type, element } => {
            let coll_name = match coll_type {
                CollectionType::Vec => "Vec",
                CollectionType::HashBag => "HashBag",
                CollectionType::HashSet => "HashSet",
            };
            Some((coll_name.to_string(), element.to_string()))
        }
        _ => None,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::grammar::GrammarRule;
    use crate::ast::language::{LangType, LogicBlock, RelationDecl};
    use crate::ast::types::CollectionType;
    use proc_macro2::Span;
    use syn::Ident;

    fn make_ident(s: &str) -> Ident {
        Ident::new(s, Span::call_site())
    }

    /// Construct a minimal LanguageDef for testing.
    fn minimal_lang() -> LanguageDef {
        LanguageDef {
            name: make_ident("TestLang"),
            options: Default::default(),
            extends_names: Vec::new(),
            include_names: Vec::new(),
            mixin_names: Vec::new(),
            types: Vec::new(),
            terms: Vec::new(),
            equations: Vec::new(),
            rewrites: Vec::new(),
            logic: None,
        }
    }

    /// Construct a LanguageDef with a logic block containing the given Ascent source.
    fn lang_with_logic(logic_src: &str) -> LanguageDef {
        let tokens: proc_macro2::TokenStream = logic_src.parse().expect("valid tokens");
        let program = ascent_syntax_export::parse_ascent_program_tokens(tokens.clone())
            .expect("valid ascent program");
        let relations = program
            .relations
            .iter()
            .map(|rel| {
                let param_types = rel
                    .field_types
                    .iter()
                    .map(|ty| quote::quote!(#ty).to_string())
                    .collect();
                RelationDecl {
                    name: rel.name.clone(),
                    param_types,
                }
            })
            .collect();

        let mut lang = minimal_lang();
        lang.logic = Some(LogicBlock {
            relations,
            content: tokens,
        });
        lang
    }

    /// Construct a LanguageDef with types and logic.
    fn lang_with_types_and_logic(type_names: &[&str], logic_src: &str) -> LanguageDef {
        let mut lang = lang_with_logic(logic_src);
        lang.types = type_names
            .iter()
            .map(|n| LangType {
                name: make_ident(n),
                native_type: None,
            })
            .collect();
        lang
    }

    // ── C-AP01: Cubic Transitivity ──────────────────────────────────────────

    #[test]
    fn cap01_detects_transitive_closure_pattern() {
        let lang = lang_with_logic(
            r#"
            relation path(i32, i32);
            relation edge(i32, i32);

            path(x, y) <-- edge(x, y);
            path(x, z) <-- path(x, y), path(y, z);
        "#,
        );

        let warnings = detect_cubic_transitivity(&lang);
        assert!(
            !warnings.is_empty(),
            "should detect transitivity pattern in path relation"
        );
        assert!(warnings.iter().all(|w| w.code == "C-AP01"));
        assert!(warnings[0].message.contains("path"));
        assert!(warnings[0].message.contains("cubic transitivity"));
    }

    #[test]
    fn cap01_no_false_positive_for_non_transitive() {
        let lang = lang_with_logic(
            r#"
            relation edge(i32, i32);
            relation path(i32, i32);

            path(x, y) <-- edge(x, y);
            path(x, z) <-- path(x, y), edge(y, z);
        "#,
        );

        let warnings = detect_cubic_transitivity(&lang);
        // path(x,z) <-- path(x,y), edge(y,z) is NOT transitivity because
        // the two body relations are different (path vs edge)
        assert!(
            warnings.is_empty(),
            "should not detect transitivity pattern when body relations differ: {:?}",
            warnings
        );
    }

    #[test]
    fn cap01_no_warning_without_logic() {
        let lang = minimal_lang();
        let warnings = detect_cubic_transitivity(&lang);
        assert!(warnings.is_empty());
    }

    // ── C-AP02: Extension Along Equality ────────────────────────────────────

    #[test]
    fn cap02_detects_eq_join_pattern() {
        let lang = lang_with_types_and_logic(
            &["Proc"],
            r#"
            relation some_rel(i32, i32);

            some_rel(x, z) <-- eq_proc(x, y), some_rel(y, z);
        "#,
        );

        let warnings = detect_extension_along_equality(&lang);
        assert!(
            !warnings.is_empty(),
            "should detect extension-along-equality with eq_proc"
        );
        assert!(warnings.iter().all(|w| w.code == "C-AP02"));
        assert!(warnings[0].message.contains("eq_proc"));
    }

    #[test]
    fn cap02_no_false_positive_for_non_eq_relation() {
        let lang = lang_with_types_and_logic(
            &["Proc"],
            r#"
            relation foo(i32, i32);
            relation bar(i32, i32);

            bar(x, z) <-- foo(x, y), bar(y, z);
        "#,
        );

        let warnings = detect_extension_along_equality(&lang);
        assert!(
            warnings.is_empty(),
            "should not flag non-equivalence relation joins: {:?}",
            warnings,
        );
    }

    #[test]
    fn cap02_no_warning_without_logic() {
        let lang = minimal_lang();
        let warnings = detect_extension_along_equality(&lang);
        assert!(warnings.is_empty());
    }

    // ── C-AP03: Deep Congruence Chains ──────────────────────────────────────

    #[test]
    fn cap03_detects_self_recursive_category() {
        let mut lang = minimal_lang();
        lang.types = vec![
            LangType {
                name: make_ident("Expr"),
                native_type: None,
            },
        ];
        // Constructor: Add . Expr ::= Expr "+" Expr ;
        lang.terms = vec![GrammarRule {
            label: make_ident("Add"),
            category: make_ident("Expr"),
            items: vec![
                GrammarItem::NonTerminal(make_ident("Expr")),
                GrammarItem::Terminal("+".to_string()),
                GrammarItem::NonTerminal(make_ident("Expr")),
            ],
            bindings: Vec::new(),
            term_context: None,
            syntax_pattern: None,
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
        }];

        let warnings = detect_deep_congruence_chains(&lang);
        assert!(
            !warnings.is_empty(),
            "should detect self-recursive constructor field"
        );
        assert!(warnings.iter().any(|w| w.code == "C-AP03"));
        assert!(warnings[0].message.contains("self-recursive"));
    }

    #[test]
    fn cap03_no_warning_for_shallow_chain() {
        let mut lang = minimal_lang();
        lang.types = vec![
            LangType {
                name: make_ident("Stmt"),
                native_type: None,
            },
            LangType {
                name: make_ident("Expr"),
                native_type: None,
            },
        ];
        // Stmt references Expr, but Expr does not reference Stmt — depth 1
        lang.terms = vec![GrammarRule {
            label: make_ident("Assign"),
            category: make_ident("Stmt"),
            items: vec![
                GrammarItem::NonTerminal(make_ident("Expr")),
                GrammarItem::Terminal("=".to_string()),
                GrammarItem::NonTerminal(make_ident("Expr")),
            ],
            bindings: Vec::new(),
            term_context: None,
            syntax_pattern: None,
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
        }];

        let warnings = detect_deep_congruence_chains(&lang);
        assert!(
            warnings.is_empty(),
            "should not warn for shallow chain (depth <= 10): {:?}",
            warnings,
        );
    }

    // ── C-AP04: Unbounded Rewrite Growth ────────────────────────────────────

    #[test]
    fn cap04_detects_positive_delta_without_complement() {
        use crate::ast::pattern::{Pattern, PatternTerm};

        let mut lang = minimal_lang();
        lang.types = vec![LangType {
            name: make_ident("Proc"),
            native_type: None,
        }];
        lang.terms = vec![
            GrammarRule {
                label: make_ident("PNil"),
                category: make_ident("Proc"),
                items: vec![GrammarItem::Terminal("nil".to_string())],
                bindings: Vec::new(),
                term_context: None,
                syntax_pattern: None,
                rust_code: None,
                eval_mode: None,
                is_right_assoc: false,
                prefix_bp: None,
            },
            GrammarRule {
                label: make_ident("PWrap"),
                category: make_ident("Proc"),
                items: vec![
                    GrammarItem::Terminal("wrap".to_string()),
                    GrammarItem::NonTerminal(make_ident("Proc")),
                ],
                bindings: Vec::new(),
                term_context: None,
                syntax_pattern: None,
                rust_code: None,
                eval_mode: None,
                is_right_assoc: false,
                prefix_bp: None,
            },
        ];

        // Rewrite: P ~> (PWrap P) — depth delta +1, no complementary reduction
        lang.rewrites = vec![crate::ast::language::RewriteRule {
            name: make_ident("WrapAll"),
            type_context: Vec::new(),
            premises: Vec::new(),
            left: Pattern::Term(PatternTerm::Var(make_ident("P"))),
            right: Pattern::Term(PatternTerm::Apply {
                constructor: make_ident("PWrap"),
                args: vec![Pattern::Term(PatternTerm::Var(make_ident("P")))],
            }),
        }];

        let warnings = detect_unbounded_rewrite_growth(&lang);
        assert!(
            !warnings.is_empty(),
            "should detect unbounded term growth from depth-increasing rewrite"
        );
        assert!(warnings.iter().all(|w| w.code == "C-AP04"));
        assert!(warnings[0].message.contains("WrapAll"));
    }

    #[test]
    fn cap04_no_warning_when_complementary_reduction_exists() {
        use crate::ast::pattern::{Pattern, PatternTerm};

        let mut lang = minimal_lang();
        lang.types = vec![LangType {
            name: make_ident("Proc"),
            native_type: None,
        }];
        lang.terms = vec![
            GrammarRule {
                label: make_ident("PNil"),
                category: make_ident("Proc"),
                items: vec![GrammarItem::Terminal("nil".to_string())],
                bindings: Vec::new(),
                term_context: None,
                syntax_pattern: None,
                rust_code: None,
                eval_mode: None,
                is_right_assoc: false,
                prefix_bp: None,
            },
            GrammarRule {
                label: make_ident("PWrap"),
                category: make_ident("Proc"),
                items: vec![
                    GrammarItem::Terminal("wrap".to_string()),
                    GrammarItem::NonTerminal(make_ident("Proc")),
                ],
                bindings: Vec::new(),
                term_context: None,
                syntax_pattern: None,
                rust_code: None,
                eval_mode: None,
                is_right_assoc: false,
                prefix_bp: None,
            },
        ];

        // Rewrite 1: P ~> (PWrap P) — depth delta +1
        // Rewrite 2: (PWrap P) ~> P — depth delta -1 (complement)
        lang.rewrites = vec![
            crate::ast::language::RewriteRule {
                name: make_ident("WrapAll"),
                type_context: Vec::new(),
                premises: Vec::new(),
                left: Pattern::Term(PatternTerm::Var(make_ident("P"))),
                right: Pattern::Term(PatternTerm::Apply {
                    constructor: make_ident("PWrap"),
                    args: vec![Pattern::Term(PatternTerm::Var(make_ident("P")))],
                }),
            },
            crate::ast::language::RewriteRule {
                name: make_ident("UnwrapAll"),
                type_context: Vec::new(),
                premises: Vec::new(),
                left: Pattern::Term(PatternTerm::Apply {
                    constructor: make_ident("PWrap"),
                    args: vec![Pattern::Term(PatternTerm::Var(make_ident("P")))],
                }),
                right: Pattern::Term(PatternTerm::Var(make_ident("P"))),
            },
        ];

        let warnings = detect_unbounded_rewrite_growth(&lang);
        assert!(
            warnings.is_empty(),
            "should not warn when complementary depth-reducing rewrite exists: {:?}",
            warnings,
        );
    }

    // ── C-AP05: Clone Storm ─────────────────────────────────────────────────

    #[test]
    fn cap05_detects_collection_field() {
        let mut lang = minimal_lang();
        lang.types = vec![LangType {
            name: make_ident("Proc"),
            native_type: None,
        }];
        lang.terms = vec![GrammarRule {
            label: make_ident("PPar"),
            category: make_ident("Proc"),
            items: vec![GrammarItem::Collection {
                coll_type: CollectionType::HashBag,
                element_type: make_ident("Proc"),
                separator: "|".to_string(),
                delimiters: None,
            }],
            bindings: Vec::new(),
            term_context: None,
            syntax_pattern: None,
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
        }];

        let warnings = detect_clone_storm(&lang);
        assert!(
            !warnings.is_empty(),
            "should detect collection field in constructor"
        );
        assert!(warnings.iter().all(|w| w.code == "C-AP05"));
        assert!(warnings[0].message.contains("PPar"));
        assert!(warnings[0].message.contains("HashBag"));
    }

    #[test]
    fn cap05_no_warning_for_non_collection_constructor() {
        let mut lang = minimal_lang();
        lang.types = vec![
            LangType {
                name: make_ident("Proc"),
                native_type: None,
            },
            LangType {
                name: make_ident("Name"),
                native_type: None,
            },
        ];
        lang.terms = vec![GrammarRule {
            label: make_ident("POutput"),
            category: make_ident("Proc"),
            items: vec![
                GrammarItem::NonTerminal(make_ident("Name")),
                GrammarItem::Terminal("!".to_string()),
                GrammarItem::NonTerminal(make_ident("Proc")),
            ],
            bindings: Vec::new(),
            term_context: None,
            syntax_pattern: None,
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
        }];

        let warnings = detect_clone_storm(&lang);
        assert!(
            warnings.is_empty(),
            "should not warn for constructors without collection fields: {:?}",
            warnings,
        );
    }

    // ── Integration: detect_antipatterns ─────────────────────────────────────

    #[test]
    fn detect_antipatterns_runs_all_detectors() {
        // No logic, no terms, no rewrites — should produce no warnings
        let lang = minimal_lang();
        let warnings = detect_antipatterns(&lang);
        assert!(warnings.is_empty());
    }

    #[test]
    fn detect_antipatterns_collects_from_multiple_detectors() {
        let mut lang = lang_with_logic(
            r#"
            relation path(i32, i32);
            path(x, z) <-- path(x, y), path(y, z);
        "#,
        );

        // Add a collection constructor for C-AP05
        lang.types = vec![LangType {
            name: make_ident("Proc"),
            native_type: None,
        }];
        lang.terms = vec![GrammarRule {
            label: make_ident("PPar"),
            category: make_ident("Proc"),
            items: vec![GrammarItem::Collection {
                coll_type: CollectionType::Vec,
                element_type: make_ident("Proc"),
                separator: ",".to_string(),
                delimiters: None,
            }],
            bindings: Vec::new(),
            term_context: None,
            syntax_pattern: None,
            rust_code: None,
            eval_mode: None,
            is_right_assoc: false,
            prefix_bp: None,
        }];

        let warnings = detect_antipatterns(&lang);
        let codes: HashSet<&str> = warnings.iter().map(|w| w.code).collect();
        // Should have at least C-AP01 (transitivity) and C-AP05 (collection) and C-AP03 (self-recursive)
        assert!(
            codes.contains("C-AP01"),
            "should detect C-AP01 (transitivity): found {:?}",
            codes,
        );
        assert!(
            codes.contains("C-AP05"),
            "should detect C-AP05 (clone storm): found {:?}",
            codes,
        );
    }
}
