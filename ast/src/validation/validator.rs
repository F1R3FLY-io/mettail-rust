#![allow(
    clippy::cmp_owned,
    clippy::too_many_arguments,
    clippy::needless_borrow,
    clippy::for_kv_map,
    clippy::let_and_return,
    clippy::unused_enumerate_index,
    clippy::expect_fun_call,
    clippy::collapsible_match,
    clippy::unwrap_or_default,
    clippy::unnecessary_filter_map
)]

use super::TypeChecker;
use super::ValidationError;
use crate::{
    grammar::{GrammarItem, NonTerminalKind},
    language::RewriteRule,
    language::{Equation, FreshnessTarget, LanguageDef, Premise},
    pattern::{Pattern, PatternTerm},
};
use std::collections::HashSet;

/// S2 — THE reserved-reflect-namespace predicate, defined once.
///
/// The in-Rho runtime mints an unforgeable ABI tag `mettail.term.{fp}.{label}`
/// per constructor, and reserves a family of machinery labels in that same space:
/// the substitution TRS (`^subst`, `^shift`, `^shiftk`, `^cmp`, `^pred`, `^sb`,
/// `^shb`, `^lambda`, `^multilambda`, `^bound`, `^free`), the quiescence driver
/// (`^drive`, `^drive-err`, `^drive-fuel`, `^fired`, `^drive-ac:{Rule}`), the
/// respread walker (`^respread*`), the scope-extrusion float (`^float*`), the
/// hereditary-ground markers (`^gnd`, `^nog`), and the Peano numerals.
///
/// The whole reserved-namespace safety argument in this tree is one sentence,
/// asserted verbatim in `rho_net_lower.rs`, in `rho_net_subst_trs.rs`, and as a
/// stated adequacy premise of `formal/rocq/rho_bridge/theories/
/// BinderReflectionTotalOrReject.v`: *a user constructor is a Rust `Ident`, so it
/// cannot contain `^`.* Before S2 that sentence was asserted in three places and
/// EVALUATED IN NONE — `ast/src/validation/` contained no occurrence of the word
/// "reserved" at all.
///
/// This function is that sentence, executable. Deliberately, it is the ONLY
/// definition: the alternative — reserving a hand-written list of bare
/// identifiers — would make the rule "starts with `^`, *or* is one of these
/// magic words", a permanent special case in every future safety argument. The
/// namespace is a prefix, and it is checkable as one.
pub fn is_reserved_reflect_label(label: &str) -> bool {
    label.starts_with('^')
}

/// Reject any declared name that lands in the reserved reflect namespace.
///
/// Vacuous for names that reached the model as a `syn::Ident`, which is exactly
/// the intent: it costs nothing on the macro path and it fails loudly the moment
/// a name arrives from anywhere else.
pub fn validate_reserved_reflect_names(language: &LanguageDef) -> Result<(), ValidationError> {
    for ty in &language.types {
        let name = ty.name.to_string();
        if is_reserved_reflect_label(&name) {
            return Err(ValidationError::ReservedReflectLabel {
                label: name,
                kind: "category",
                span: ty.name.span(),
            });
        }
    }
    for rule in &language.terms {
        let label = rule.label.to_string();
        if is_reserved_reflect_label(&label) {
            return Err(ValidationError::ReservedReflectLabel {
                label,
                kind: "constructor",
                span: rule.label.span(),
            });
        }
    }
    for rewrite in &language.rewrites {
        let label = rewrite.name.to_string();
        if is_reserved_reflect_label(&label) {
            return Err(ValidationError::ReservedReflectLabel {
                label,
                kind: "rewrite rule",
                span: rewrite.name.span(),
            });
        }
    }
    // Every OTHER declaration that contributes a name. A partial sweep would be
    // worse than none: it would read as a complete fence while leaving the
    // uncovered clauses as the obvious way in.
    for equation in &language.equations {
        let label = equation.name.to_string();
        if is_reserved_reflect_label(&label) {
            return Err(ValidationError::ReservedReflectLabel {
                label,
                kind: "equation",
                span: equation.name.span(),
            });
        }
    }
    for refinement in &language.refinement_types {
        let label = refinement.name.to_string();
        if is_reserved_reflect_label(&label) {
            return Err(ValidationError::ReservedReflectLabel {
                label,
                kind: "refinement type",
                span: refinement.name.span(),
            });
        }
    }
    for relation in language
        .logic
        .iter()
        .flat_map(|logic| logic.relations.iter())
    {
        let label = relation.name.to_string();
        if is_reserved_reflect_label(&label) {
            return Err(ValidationError::ReservedReflectLabel {
                label,
                kind: "relation",
                span: relation.name.span(),
            });
        }
    }
    // Token and mode names, including the token defs nested inside each mode —
    // a mode-local token is as capable of naming a category as a top-level one.
    let nested_tokens = language
        .mode_defs
        .iter()
        .flat_map(|mode| mode.token_defs.iter());
    for token in language.token_defs.iter().chain(nested_tokens) {
        let label = token.name.to_string();
        if is_reserved_reflect_label(&label) {
            return Err(ValidationError::ReservedReflectLabel {
                label,
                kind: "token",
                span: token.name.span(),
            });
        }
    }
    for mode in &language.mode_defs {
        let label = mode.name.to_string();
        if is_reserved_reflect_label(&label) {
            return Err(ValidationError::ReservedReflectLabel {
                label,
                kind: "lexer mode",
                span: mode.name.span(),
            });
        }
    }
    Ok(())
}

pub fn validate_language(language: &LanguageDef) -> Result<(), ValidationError> {
    // S2: the reserved reflect namespace, checked before anything else — a name
    // that can shadow runtime machinery must never reach codegen.
    validate_reserved_reflect_names(language)?;

    // Build set of exported categories. Refinement types declared in the
    // types block (e.g. `PosInt = { x: Int | x > 0 }`) are also added to
    // `language.types` by the parser, so they're picked up here too.
    let lang_types: HashSet<_> = language.types.iter().map(|t| t.name.to_string()).collect();

    // Build set of all defined categories (result types from all rules)
    let defined: HashSet<_> = language
        .terms
        .iter()
        .map(|r| r.category.to_string())
        .collect();

    // Check each rule
    for rule in &language.terms {
        // Check that the rule's category is exported
        // (We require that constructor result types are exported)
        let cat_name = rule.category.to_string();
        if !lang_types.contains(&cat_name) {
            return Err(ValidationError::CategoryNotExported {
                category: cat_name,
                rule: rule.label.to_string(),
                span: rule.category.span(),
            });
        }

        // Check that all non-terminal items reference valid categories
        // Valid means: exported OR defined as a result type OR built-in (like Var)
        for item in &rule.items {
            match item {
                GrammarItem::NonTerminal { ident, kind } => {
                    // Built-in types (Var, Integer, Boolean, etc.) are always valid
                    if kind.is_builtin() {
                        continue;
                    }
                    // Must be either exported or defined (or both)
                    let ref_name = ident.to_string();
                    if !lang_types.contains(&ref_name) && !defined.contains(&ref_name) {
                        return Err(ValidationError::UndefinedCategoryReference {
                            category: ref_name,
                            rule: rule.label.to_string(),
                            span: ident.span(),
                        });
                    }
                },
                GrammarItem::Binder { category } => {
                    let ref_name = category.to_string();
                    // Built-in types are always valid
                    if NonTerminalKind::classify(&ref_name).is_builtin() {
                        continue;
                    }
                    // Binder categories must also be valid
                    if !lang_types.contains(&ref_name) && !defined.contains(&ref_name) {
                        return Err(ValidationError::UndefinedCategoryReference {
                            category: ref_name,
                            rule: rule.label.to_string(),
                            span: category.span(),
                        });
                    }
                },
                _ => {},
            }
        }
    }

    // Validate expressions in equations
    for eq in language.equations.iter() {
        validate_pattern(&eq.left, &language)?;
        validate_pattern(&eq.right, &language)?;

        // Validate freshness conditions
        validate_equation_freshness(eq)?;
    }

    // Validate expressions in rewrites
    for rw in language.rewrites.iter() {
        validate_pattern(&rw.left, &language)?;
        validate_pattern(&rw.right, &language)?;

        // Validate freshness conditions
        validate_rewrite_freshness(rw)?;
    }

    // Type-check equations
    let type_checker = TypeChecker::new(language);
    type_checker.validate_equations(&language.equations)?;

    // Type-check rewrite rules
    type_checker.validate_rewrites(&language.rewrites)?;

    // Validate guard configuration (design doc §2A)
    validate_guard_config(language)?;

    Ok(())
}

/// Validate the `guards { ... }` block (design doc §2A).
///
/// Emits hard errors for:
/// - CONN01: duplicate connective keyword across roles
/// - GUARD01: unknown predicate name in closed-world mode
/// - MT02: join pattern references undeclared channel category
/// - TW03: join pattern label has no matching `terms {}` constructor
///
/// When `language.guard_config` is `None`, validation is a no-op.
pub fn validate_guard_config(language: &LanguageDef) -> Result<(), ValidationError> {
    use crate::language::{BehavioralPred, ConnectiveMap, GuardConfig, Premise};

    let gc: &GuardConfig = match language.guard_config.as_ref() {
        Some(gc) => gc,
        None => return Ok(()),
    };

    // CONN01: Build the ConnectiveMap; if duplicate keywords exist across
    // roles, the constructor returns an error which we re-package as a
    // ValidationError so it surfaces with proper diagnostics.
    if let Some(decls) = gc.connectives.as_ref() {
        if let Err(e) = ConnectiveMap::from_decls(decls) {
            // Parse the error to extract role names; the message format is
            // "CONN01: keyword `<kw>` is mapped to multiple connective roles
            //  (<role_a> and <role_b>)".
            let msg = e.to_string();
            // Best-effort extraction of the keyword from the error string.
            let kw = msg
                .split('`')
                .nth(1)
                .map(String::from)
                .unwrap_or_else(|| "<unknown>".to_string());
            return Err(ValidationError::DuplicateConnectiveKeyword {
                keyword: kw,
                role_a: "(see error)".to_string(),
                role_b: "(see error)".to_string(),
                span: proc_macro2::Span::call_site(),
            });
        }
    }

    // GUARD01: Predicate name resolution in closed-world mode.
    // The closed-world resolution table is the union of:
    // - declared built-in predicate names from `guards {}` direct items
    // - user-defined relation names from `logic {}` declarations
    let has_explicit_predicates = gc.builtin_predicates.is_some();
    if has_explicit_predicates {
        let mut resolution_table: HashSet<String> = HashSet::new();
        if let Some(preds) = gc.builtin_predicates.as_ref() {
            for p in preds {
                resolution_table.insert(p.name.to_string());
            }
        }
        if let Some(logic) = language.logic.as_ref() {
            for r in &logic.relations {
                resolution_table.insert(r.name.to_string());
            }
        }

        // Walk all `BehavioralGuard` premises in equations and rewrites,
        // checking each `RelationQuery.relation_name` against the table.
        let walk = |pred: &BehavioralPred,
                    table: &HashSet<String>|
         -> Result<(), ValidationError> { walk_behavioral_pred(pred, table) };

        for eq in &language.equations {
            for premise in &eq.premises {
                if let Premise::BehavioralGuard(pred) = premise {
                    walk(pred, &resolution_table)?;
                }
            }
        }
        for rw in &language.rewrites {
            for premise in &rw.premises {
                if let Premise::BehavioralGuard(pred) = premise {
                    walk(pred, &resolution_table)?;
                }
            }
        }
    }

    // MT02: Join pattern references undeclared channel category.
    // TW03: Join pattern label has no matching constructor in `terms {}`.
    if let Some(channels) = gc.channels.as_ref() {
        let declared_categories: HashSet<String> = channels
            .channel_categories
            .iter()
            .map(|d| d.category.to_string())
            .collect();
        let known_constructors: HashSet<String> =
            language.terms.iter().map(|r| r.label.to_string()).collect();

        for jp in &channels.join_patterns {
            // TW03
            let label = jp.label.to_string();
            if !known_constructors.is_empty() && !known_constructors.contains(&label) {
                return Err(ValidationError::JoinPatternUnknownConstructor {
                    label,
                    span: jp.label.span(),
                });
            }
            // MT02
            for cp in &jp.channel_params {
                let cat = cp.category.to_string();
                if !declared_categories.contains(&cat) {
                    return Err(ValidationError::UndeclaredChannelReference {
                        category: cat,
                        join_label: jp.label.to_string(),
                        span: cp.category.span(),
                    });
                }
            }
        }
    }

    Ok(())
}

/// Recursively walk a `BehavioralPred` looking up each predicate name
/// in the closed-world resolution table.
fn walk_behavioral_pred(
    pred: &crate::language::BehavioralPred,
    table: &HashSet<String>,
) -> Result<(), ValidationError> {
    use crate::language::BehavioralPred;
    match pred {
        BehavioralPred::RelationQuery { relation_name, .. } => {
            let name = relation_name.to_string();
            if !table.contains(&name) {
                let mut available: Vec<String> = table.iter().cloned().collect();
                available.sort();
                return Err(ValidationError::UnknownGuardPredicate {
                    name,
                    available,
                    span: relation_name.span(),
                });
            }
            Ok(())
        },
        BehavioralPred::And(a, b) | BehavioralPred::Or(a, b) | BehavioralPred::Implies(a, b) => {
            walk_behavioral_pred(a, table)?;
            walk_behavioral_pred(b, table)
        },
        BehavioralPred::Not(inner) => walk_behavioral_pred(inner, table),
        BehavioralPred::Quantified { body, .. } => walk_behavioral_pred(body, table),
        BehavioralPred::AcMatch { .. } => {
            // AcMatch is a structural form, not a named predicate.
            Ok(())
        },
        BehavioralPred::Top => {
            // Always-true identity predicate; no named predicate to resolve.
            Ok(())
        },
    }
}

fn validate_pattern(pattern: &Pattern, language: &LanguageDef) -> Result<(), ValidationError> {
    match pattern {
        Pattern::Term(pt) => validate_pattern_term(pt, language),
        Pattern::Collection { elements, .. } => {
            // Validate collection pattern
            // NOTE: Collections no longer have constructors - they get context from
            // the enclosing PatternTerm::Apply. Validation of collection type
            // compatibility happens when we process the parent Apply.

            // Recursively validate element patterns
            for elem in elements {
                validate_pattern(elem, language)?;
            }

            Ok(())
        },
        Pattern::Map { collection, body, .. } => {
            validate_pattern(collection, language)?;
            validate_pattern(body, language)?;
            Ok(())
        },
        Pattern::Zip { first, second } => {
            validate_pattern(first, language)?;
            validate_pattern(second, language)?;
            Ok(())
        },
        Pattern::IndexedVec { element, .. } => validate_pattern(element, language),
    }
}

fn validate_pattern_term(pt: &PatternTerm, language: &LanguageDef) -> Result<(), ValidationError> {
    match pt {
        PatternTerm::Var(_) => Ok(()),
        PatternTerm::Apply { constructor, args } => {
            // Check that constructor references a known rule
            let constructor_name = constructor.to_string();
            let found = language
                .terms
                .iter()
                .any(|r| r.label.to_string() == constructor_name);

            if !found {
                return Err(ValidationError::UnknownConstructor {
                    name: constructor_name,
                    span: constructor.span(),
                });
            }

            // Recursively validate args (which are Patterns)
            for arg in args {
                validate_pattern(arg, language)?;
            }
            Ok(())
        },
        PatternTerm::Lambda { body, .. } => validate_pattern(body, language),
        PatternTerm::MultiLambda { body, .. } => validate_pattern(body, language),
        PatternTerm::Subst { term, replacement, .. } => {
            validate_pattern(term, language)?;
            validate_pattern(replacement, language)?;
            Ok(())
        },
        PatternTerm::MultiSubst { scope, replacements } => {
            validate_pattern(scope, language)?;
            for repl in replacements {
                validate_pattern(repl, language)?;
            }
            Ok(())
        },
    }
}

/// Validate a single premise against the known pattern variables.
/// `bound_vars` contains lambda-bound parameters (e.g. from ForAll) that
/// are in scope but don't need to appear in the pattern.
fn validate_premise(
    premise: &Premise,
    pattern_vars: &HashSet<String>,
    bound_vars: &HashSet<String>,
) -> Result<(), ValidationError> {
    match premise {
        Premise::Freshness(freshness) => {
            let var_name = freshness.var.to_string();
            let (term_name, term_span) = match &freshness.term {
                FreshnessTarget::Var(id) => (id.to_string(), id.span()),
                FreshnessTarget::CollectionRest(id) => (id.to_string(), id.span()),
            };

            let all_vars_in_scope =
                |name: &str| pattern_vars.contains(name) || bound_vars.contains(name);

            if !all_vars_in_scope(&var_name) {
                return Err(ValidationError::FreshnessVariableNotInEquation {
                    var: var_name,
                    span: freshness.var.span(),
                });
            }

            if !all_vars_in_scope(&term_name) {
                return Err(ValidationError::FreshnessTermNotInEquation {
                    var: var_name,
                    term: term_name,
                    span: term_span,
                });
            }

            if var_name == term_name {
                return Err(ValidationError::FreshnessSelfReference {
                    var: var_name,
                    span: freshness.var.span(),
                });
            }
        },
        Premise::ForAll { collection, param, body } => {
            let coll_name = collection.to_string();
            if !pattern_vars.contains(&coll_name) {
                return Err(ValidationError::FreshnessVariableNotInEquation {
                    var: coll_name,
                    span: collection.span(),
                });
            }
            let mut inner_bound = bound_vars.clone();
            inner_bound.insert(param.to_string());
            validate_premise(body, pattern_vars, &inner_bound)?;
        },
        // ★ (#195) The two congruence POLARITIES validate identically: both name a
        // source/target metavariable pair that the enclosing rule's own patterns bind,
        // so there is no additional scope obligation. They are listed as one arm rather
        // than defaulted, so a future obligation on either cannot be added to one and
        // forgotten on the other.
        Premise::Congruence { .. }
        | Premise::CongruenceWithheld { .. }
        | Premise::RelationQuery { .. } => {},
        // Phase A (2026-05-16): synthetic-injection guard is emitted
        // exclusively by codegen for auto-injected NormCast rules. It
        // references the auto-injected rule's inner_var (which IS in
        // pattern_vars by construction) and an exclusion list of
        // grammar-derived constructor labels. No user-facing validation
        // needed; codegen-emitted variant.
        Premise::SyntheticInjGuard { .. } => {},
        Premise::BehavioralGuard(_) => {
            // Behavioral guards are evaluated at runtime via LogicT;
            // no pattern-variable validation needed here.
        },
    }
    Ok(())
}

/// Validate freshness conditions in an equation
fn validate_equation_freshness(eq: &Equation) -> Result<(), ValidationError> {
    let mut equation_vars = HashSet::new();
    collect_pattern_vars(&eq.left, &mut equation_vars);
    collect_pattern_vars(&eq.right, &mut equation_vars);

    let empty_bound = HashSet::new();
    for cond in &eq.premises {
        validate_premise(cond, &equation_vars, &empty_bound)?;
    }

    Ok(())
}

/// Validate freshness conditions in a rewrite rule
fn validate_rewrite_freshness(rw: &RewriteRule) -> Result<(), ValidationError> {
    let mut rewrite_vars = HashSet::new();
    collect_pattern_vars(&rw.left, &mut rewrite_vars);
    collect_pattern_vars(&rw.right, &mut rewrite_vars);

    let empty_bound = HashSet::new();
    for cond in &rw.premises {
        validate_premise(cond, &rewrite_vars, &empty_bound)?;
    }

    Ok(())
}

/// Collect all variable names from a Pattern
fn collect_pattern_vars(pattern: &Pattern, vars: &mut HashSet<String>) {
    match pattern {
        Pattern::Term(pt) => collect_pattern_term_vars(pt, vars),
        Pattern::Collection { elements, rest, .. } => {
            for elem in elements {
                collect_pattern_vars(elem, vars);
            }
            if let Some(rest_var) = rest {
                vars.insert(rest_var.to_string());
            }
        },
        Pattern::Map { collection, params, body } => {
            collect_pattern_vars(collection, vars);
            // params are bound, so only collect from body excluding params
            let mut body_vars = HashSet::new();
            collect_pattern_vars(body, &mut body_vars);
            for param in params {
                body_vars.remove(&param.to_string());
            }
            vars.extend(body_vars);
        },
        Pattern::Zip { first, second } => {
            collect_pattern_vars(first, vars);
            collect_pattern_vars(second, vars);
        },
        Pattern::IndexedVec { collection, index, element } => {
            vars.insert(collection.to_string());
            vars.insert(index.to_string());
            collect_pattern_vars(element, vars);
        },
    }
}

/// Collect all variable names from a PatternTerm
fn collect_pattern_term_vars(pt: &PatternTerm, vars: &mut HashSet<String>) {
    match pt {
        PatternTerm::Var(ident) => {
            vars.insert(ident.to_string());
        },
        PatternTerm::Apply { args, .. } => {
            for arg in args {
                collect_pattern_vars(arg, vars);
            }
        },
        PatternTerm::Lambda { binder, body } => {
            // Include the binder as a valid pattern variable (for freshness conditions)
            vars.insert(binder.to_string());
            // Collect body vars, but remove binder from free vars (it's bound)
            let mut body_vars = HashSet::new();
            collect_pattern_vars(body, &mut body_vars);
            body_vars.remove(&binder.to_string());
            vars.extend(body_vars);
        },
        PatternTerm::MultiLambda { binders, body } => {
            // Include all binders as valid pattern variables (for freshness conditions)
            for binder in binders {
                vars.insert(binder.to_string());
            }
            // Collect body vars, but remove binders from free vars (they're bound)
            let mut body_vars = HashSet::new();
            collect_pattern_vars(body, &mut body_vars);
            for binder in binders {
                body_vars.remove(&binder.to_string());
            }
            vars.extend(body_vars);
        },
        PatternTerm::Subst { term, var, replacement } => {
            collect_pattern_vars(term, vars);
            vars.insert(var.to_string());
            collect_pattern_vars(replacement, vars);
        },
        PatternTerm::MultiSubst { scope, replacements } => {
            collect_pattern_vars(scope, vars);
            for repl in replacements {
                collect_pattern_vars(repl, vars);
            }
        },
    }
}
