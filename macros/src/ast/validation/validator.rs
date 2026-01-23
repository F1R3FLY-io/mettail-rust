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
use crate::ast::{language::{Equation, LanguageDef, LangType, FreshnessTarget, Condition, EnvAction, FreshnessCondition}, grammar::{GrammarItem, GrammarRule}, term::Term, language::RewriteRule, pattern::{Pattern, PatternTerm}};
use std::collections::HashSet;

pub fn validate_language(language: &LanguageDef) -> Result<(), ValidationError> {
    // Build set of exported categories
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
                GrammarItem::NonTerminal(ident) => {
                    let ref_name = ident.to_string();
                    // Built-in types are always valid
                    if ref_name == "Var" || ref_name == "Integer" {
                        continue;
                    }
                    // Must be either exported or defined (or both)
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
                    if ref_name == "Var" {
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

    Ok(())
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
        }
        Pattern::Map { collection, body, .. } => {
            validate_pattern(collection, language)?;
            validate_pattern(body, language)?;
            Ok(())
        }
        Pattern::Zip { first, second } => {
            validate_pattern(first, language)?;
            validate_pattern(second, language)?;
            Ok(())
        }
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
        }
        PatternTerm::Lambda { body, .. } => validate_pattern(body, language),
        PatternTerm::MultiLambda { body, .. } => validate_pattern(body, language),
        PatternTerm::Subst { term, replacement, .. } => {
            validate_pattern(term, language)?;
            validate_pattern(replacement, language)?;
            Ok(())
        }
        PatternTerm::MultiSubst { scope, replacements } => {
            validate_pattern(scope, language)?;
            for repl in replacements {
                validate_pattern(repl, language)?;
            }
            Ok(())
        }
    }
}

fn validate_expr(expr: &Term, language: &LanguageDef) -> Result<(), ValidationError> {
    match expr {
        Term::Var(_) => Ok(()), // Variables are always OK
        Term::Apply { constructor, args } => {
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

            // Recursively validate arguments
            for arg in args {
                validate_expr(arg, language)?;
            }

            Ok(())
        },
        Term::Subst { term, var: _, replacement } => {
            // Validate the term being substituted into
            validate_expr(term, language)?;

            // Validate the replacement expression
            validate_expr(replacement, language)?;

            // var is just an identifier, no validation needed
            Ok(())
        },

        // Lambda expressions - validate body
        Term::Lambda { body, .. } => validate_expr(body, language),
        Term::MultiLambda { body, .. } => validate_expr(body, language),
        
        // MultiSubst - validate scope and each replacement expression
        Term::MultiSubst { scope, replacements } => {
            validate_expr(scope, language)?;
            for repl in replacements {
                validate_expr(repl, language)?;
            }
            Ok(())
        },
    }
}

/// Validate freshness conditions in an equation
///
/// Checks that:
/// 1. Variables in freshness conditions actually appear in the equation
/// 2. The freshness constraint is semantically meaningful
///
/// Freshness condition `x # Q` means "x does not appear free in Q"
fn validate_equation_freshness(eq: &Equation) -> Result<(), ValidationError> {
    // Collect all variables that appear in the equation
    let mut equation_vars = HashSet::new();
    collect_pattern_vars(&eq.left, &mut equation_vars);
    collect_pattern_vars(&eq.right, &mut equation_vars);

    // Validate each freshness condition
    for cond in &eq.conditions {
        let var_name = cond.var.to_string();
        let (term_name, term_span) = match &cond.term {
            FreshnessTarget::Var(id) => (id.to_string(), id.span()),
            FreshnessTarget::CollectionRest(id) => (id.to_string(), id.span()),
        };

        // Check that the variable appears in the equation
        if !equation_vars.contains(&var_name) {
            return Err(ValidationError::FreshnessVariableNotInEquation {
                var: var_name,
                span: cond.var.span(),
            });
        }

        // Check that the term variable appears in the equation
        if !equation_vars.contains(&term_name) {
            return Err(ValidationError::FreshnessTermNotInEquation {
                var: var_name,
                term: term_name,
                span: term_span,
            });
        }

        // Check that x does not appear free in term
        // For now, we do a simple check: if term is a variable, x != term
        // More sophisticated checking will be added with scoping
        if var_name == term_name {
            return Err(ValidationError::FreshnessSelfReference {
                var: var_name,
                span: cond.var.span(),
            });
        }
    }

    Ok(())
}

/// Validate freshness conditions in a rewrite rule
/// Same logic as equations
fn validate_rewrite_freshness(rw: &RewriteRule) -> Result<(), ValidationError> {
    // Collect all variables that appear in the rewrite
    let mut rewrite_vars = HashSet::new();
    collect_pattern_vars(&rw.left, &mut rewrite_vars);
    collect_pattern_vars(&rw.right, &mut rewrite_vars);

    // Validate each condition
    for cond in &rw.conditions {
        match cond {
            Condition::Freshness(freshness) => {
                let var_name = freshness.var.to_string();
                let (term_name, term_span) = match &freshness.term {
                    FreshnessTarget::Var(id) => (id.to_string(), id.span()),
                    FreshnessTarget::CollectionRest(id) => (id.to_string(), id.span()),
                };

                // Check that the variable appears in the rewrite
                if !rewrite_vars.contains(&var_name) {
                    return Err(ValidationError::FreshnessVariableNotInEquation {
                        var: var_name,
                        span: freshness.var.span(),
                    });
                }

                // Check that the term variable appears in the rewrite
                if !rewrite_vars.contains(&term_name) {
                    return Err(ValidationError::FreshnessTermNotInEquation {
                        var: var_name,
                        term: term_name,
                        span: term_span,
                    });
                }

                // Check that x != term (can't be fresh in itself)
                if var_name == term_name {
                    return Err(ValidationError::FreshnessSelfReference {
                        var: var_name,
                        span: freshness.var.span(),
                    });
                }
            },
            Condition::EnvQuery { relation: _, args } => {
                // Validate that the first arg (variable name) appears in the rewrite
                // The second arg (value) is bound from the query, so it doesn't need to appear
                if let Some(first_arg) = args.first() {
                    let arg_name = first_arg.to_string();
                    if !rewrite_vars.contains(&arg_name) {
                        return Err(ValidationError::FreshnessVariableNotInEquation {
                            var: arg_name,
                            span: first_arg.span(),
                        });
                    }
                }
                // Other args (like the value) are bound from the query, so they don't need validation
            },
        }
    }

    // Validate environment actions
    for action in &rw.env_actions {
        let EnvAction::CreateFact { args, .. } = action;
        // All arguments in env_actions must be bound variables in the rewrite
        for arg in args {
            let arg_name = arg.to_string();
            if !rewrite_vars.contains(&arg_name) {
                return Err(ValidationError::FreshnessVariableNotInEquation {
                    var: arg_name,
                    span: arg.span(),
                });
            }
        }
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
        }
        Pattern::Map { collection, params, body } => {
            collect_pattern_vars(collection, vars);
            // params are bound, so only collect from body excluding params
            let mut body_vars = HashSet::new();
            collect_pattern_vars(body, &mut body_vars);
            for param in params {
                body_vars.remove(&param.to_string());
            }
            vars.extend(body_vars);
        }
        Pattern::Zip { first, second } => {
            collect_pattern_vars(first, vars);
            collect_pattern_vars(second, vars);
        }
    }
}

/// Collect all variable names from a PatternTerm
fn collect_pattern_term_vars(pt: &PatternTerm, vars: &mut HashSet<String>) {
    match pt {
        PatternTerm::Var(ident) => {
            vars.insert(ident.to_string());
        }
        PatternTerm::Apply { args, .. } => {
            for arg in args {
                collect_pattern_vars(arg, vars);
            }
        }
        PatternTerm::Lambda { binder, body } => {
            // Include the binder as a valid pattern variable (for freshness conditions)
            vars.insert(binder.to_string());
            // Collect body vars, but remove binder from free vars (it's bound)
            let mut body_vars = HashSet::new();
            collect_pattern_vars(body, &mut body_vars);
            body_vars.remove(&binder.to_string());
            vars.extend(body_vars);
        }
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
        }
        PatternTerm::Subst { term, var, replacement } => {
            collect_pattern_vars(term, vars);
            vars.insert(var.to_string());
            collect_pattern_vars(replacement, vars);
        }
        PatternTerm::MultiSubst { scope, replacements } => {
            collect_pattern_vars(scope, vars);
            for repl in replacements {
                collect_pattern_vars(repl, vars);
            }
        }
    }
}

/// Collect all variable names from an expression
fn collect_vars(expr: &Term, vars: &mut HashSet<String>) {
    match expr {
        Term::Var(ident) => {
            vars.insert(ident.to_string());
        },
        Term::Apply { args, .. } => {
            for arg in args {
                collect_vars(arg, vars);
            }
        },
        Term::Subst { term, var, replacement } => {
            // Collect from the term being substituted into
            collect_vars(term, vars);
            // The substitution variable itself
            vars.insert(var.to_string());
            // Collect from the replacement
            collect_vars(replacement, vars);
        },
        // Lambda expressions - collect from body, binder is bound not free
        Term::Lambda { binder, body } => {
            // Don't include the bound variable, only free vars in body
            let mut body_vars = HashSet::new();
            collect_vars(body, &mut body_vars);
            body_vars.remove(&binder.to_string());
            vars.extend(body_vars);
        },
        Term::MultiLambda { binders, body } => {
            let mut body_vars = HashSet::new();
            collect_vars(body, &mut body_vars);
            for binder in binders {
                body_vars.remove(&binder.to_string());
            }
            vars.extend(body_vars);
        },
        Term::MultiSubst { scope, replacements } => {
            // collect from scope and each replacement expression
            collect_vars(scope, vars);
            for repl in replacements {
                collect_vars(repl, vars);
            }
        },
    }
}