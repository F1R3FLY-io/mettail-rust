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
use crate::ast::{theory::{Equation, TheoryDef, Export, FreshnessTarget, Condition, EnvAction, FreshnessCondition}, grammar::{GrammarItem, GrammarRule}, term::Term, theory::RewriteRule, pattern::{Pattern, PatternTerm}};
use std::collections::HashSet;

pub fn validate_theory(theory: &TheoryDef) -> Result<(), ValidationError> {
    // Build set of exported categories
    let exported: HashSet<_> = theory.exports.iter().map(|e| e.name.to_string()).collect();

    // Build set of all defined categories (result types from all rules)
    let defined: HashSet<_> = theory
        .terms
        .iter()
        .map(|r| r.category.to_string())
        .collect();

    // Check each rule
    for rule in &theory.terms {
        // Check that the rule's category is exported
        // (We require that constructor result types are exported)
        let cat_name = rule.category.to_string();
        if !exported.contains(&cat_name) {
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
                    if !exported.contains(&ref_name) && !defined.contains(&ref_name) {
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
                    if !exported.contains(&ref_name) && !defined.contains(&ref_name) {
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
    for eq in theory.equations.iter() {
        validate_pattern(&eq.left, &theory)?;
        validate_pattern(&eq.right, &theory)?;

        // Validate freshness conditions
        validate_equation_freshness(eq)?;
    }

    // Validate expressions in rewrites
    for rw in theory.rewrites.iter() {
        validate_pattern(&rw.left, &theory)?;
        validate_pattern(&rw.right, &theory)?;

        // Validate freshness conditions
        validate_rewrite_freshness(rw)?;
    }

    // Type-check equations
    let type_checker = TypeChecker::new(theory);
    type_checker.validate_equations(&theory.equations)?;

    // Type-check rewrite rules
    type_checker.validate_rewrites(&theory.rewrites)?;

    Ok(())
}

fn validate_pattern(pattern: &Pattern, theory: &TheoryDef) -> Result<(), ValidationError> {
    match pattern {
        Pattern::Term(pt) => validate_pattern_term(pt, theory),
        Pattern::Collection { constructor, elements, rest: _ } => {
            // Validate collection pattern
            // 1. If constructor is specified, verify it's a known collection type
            if let Some(cons) = constructor {
                let rule = theory
                    .terms
                    .iter()
                    .find(|r| r.label == *cons)
                    .ok_or_else(|| ValidationError::UnknownConstructor {
                        name: cons.to_string(),
                        span: cons.span(),
                    })?;

                // Check that this constructor has a collection field
                let has_collection = rule
                    .items
                    .iter()
                    .any(|item| matches!(item, GrammarItem::Collection { .. }));

                if !has_collection {
                    // For now, just accept it - validation will happen later
                }
            }

            // 2. Recursively validate element patterns
            for elem in elements {
                validate_pattern(elem, theory)?;
            }

            // 3. Rest variable doesn't need special validation here
            Ok(())
        }
        Pattern::Map { collection, body, .. } => {
            validate_pattern(collection, theory)?;
            validate_pattern(body, theory)?;
            Ok(())
        }
        Pattern::Zip { collections } => {
            for coll in collections {
                validate_pattern(coll, theory)?;
            }
            Ok(())
        }
    }
}

fn validate_pattern_term(pt: &PatternTerm, theory: &TheoryDef) -> Result<(), ValidationError> {
    match pt {
        PatternTerm::Var(_) => Ok(()),
        PatternTerm::Apply { constructor, args } => {
            // Check that constructor references a known rule
            let constructor_name = constructor.to_string();
            let found = theory
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
                validate_pattern(arg, theory)?;
            }
            Ok(())
        }
        PatternTerm::Lambda { body, .. } => validate_pattern(body, theory),
        PatternTerm::MultiLambda { body, .. } => validate_pattern(body, theory),
        PatternTerm::Subst { term, replacement, .. } => {
            validate_pattern(term, theory)?;
            validate_pattern(replacement, theory)?;
            Ok(())
        }
        PatternTerm::MultiSubst { scope, replacements } => {
            validate_pattern(scope, theory)?;
            for repl in replacements {
                validate_pattern(repl, theory)?;
            }
            Ok(())
        }
    }
}

fn validate_expr(expr: &Term, theory: &TheoryDef) -> Result<(), ValidationError> {
    match expr {
        Term::Var(_) => Ok(()), // Variables are always OK
        Term::Apply { constructor, args } => {
            // Check that constructor references a known rule
            let constructor_name = constructor.to_string();
            let found = theory
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
                validate_expr(arg, theory)?;
            }

            Ok(())
        },
        Term::Subst { term, var: _, replacement } => {
            // Validate the term being substituted into
            validate_expr(term, theory)?;

            // Validate the replacement expression
            validate_expr(replacement, theory)?;

            // var is just an identifier, no validation needed
            Ok(())
        },

        // Lambda expressions - validate body
        Term::Lambda { body, .. } => validate_expr(body, theory),
        Term::MultiLambda { body, .. } => validate_expr(body, theory),
        
        // MultiSubst - validate scope and each replacement expression
        Term::MultiSubst { scope, replacements } => {
            validate_expr(scope, theory)?;
            for repl in replacements {
                validate_expr(repl, theory)?;
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
        Pattern::Zip { collections } => {
            for coll in collections {
                collect_pattern_vars(coll, vars);
            }
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


#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::*;
    use syn::parse_quote;

    #[test]
    fn test_valid_theory() {
        let theory = TheoryDef {
            name: parse_quote!(Test),
            params: vec![],
            exports: vec![Export {
                name: parse_quote!(Elem),
                native_type: None,
            }],
            terms: vec![GrammarRule {
                label: parse_quote!(Zero),
                category: parse_quote!(Elem),
                items: vec![GrammarItem::Terminal("0".to_string())],
                bindings: vec![],
                term_context: None,
                syntax_pattern: None,
            }],
            equations: vec![],
            rewrites: vec![],
            semantics: vec![],
        };

        assert!(validate_theory(&theory).is_ok());
    }

    #[test]
    fn test_invalid_category() {
        let theory = TheoryDef {
            name: parse_quote!(Test),
            params: vec![],
            exports: vec![Export {
                name: parse_quote!(Elem),
                native_type: None,
            }],
            terms: vec![GrammarRule {
                label: parse_quote!(Quote),
                category: parse_quote!(Name), // Not exported!
                items: vec![
                    GrammarItem::Terminal("@".to_string()),
                    GrammarItem::NonTerminal(parse_quote!(Elem)),
                ],
                bindings: vec![],
                term_context: None,
                syntax_pattern: None,
            }],
            equations: vec![],
            rewrites: vec![],
            semantics: vec![],
        };

        assert!(validate_theory(&theory).is_err());
    }

    #[test]
    fn test_invalid_reference() {
        let theory = TheoryDef {
            name: parse_quote!(Test),
            params: vec![],
            exports: vec![Export {
                name: parse_quote!(Elem),
                native_type: None,
            }],
            terms: vec![GrammarRule {
                label: parse_quote!(Quote),
                category: parse_quote!(Elem),
                items: vec![
                    GrammarItem::Terminal("@".to_string()),
                    GrammarItem::NonTerminal(parse_quote!(Name)), // Not exported!
                ],
                bindings: vec![],
                term_context: None,
                syntax_pattern: None,
            }],
            equations: vec![],
            rewrites: vec![],
            semantics: vec![],
        };

        let result = validate_theory(&theory);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().message();
        assert!(err_msg.contains("Name"));
    }

    #[test]
    fn test_freshness_valid() {
        // Valid freshness condition: if x # P then (@*(new x P)) == P
        // This is type-correct: both sides have type Proc
        let theory = TheoryDef {
            name: parse_quote!(Test),
            params: vec![],
            exports: vec![
                Export {
                    name: parse_quote!(Name),
                    native_type: None,
                },
                Export {
                    name: parse_quote!(Proc),
                    native_type: None,
                },
            ],
            terms: vec![
                GrammarRule {
                    label: parse_quote!(NQuote),
                    category: parse_quote!(Name),
                    items: vec![
                        GrammarItem::Terminal("@".to_string()),
                        GrammarItem::NonTerminal(parse_quote!(Proc)),
                    ],
                    bindings: vec![],
                    term_context: None,
                    syntax_pattern: None,
                },
                GrammarRule {
                    label: parse_quote!(PDrop),
                    category: parse_quote!(Proc),
                    items: vec![
                        GrammarItem::Terminal("*".to_string()),
                        GrammarItem::NonTerminal(parse_quote!(Name)),
                    ],
                    bindings: vec![],
                    term_context: None,
                    syntax_pattern: None,
                },
                GrammarRule {
                    label: parse_quote!(PNew),
                    category: parse_quote!(Proc),
                    items: vec![
                        GrammarItem::Terminal("new".to_string()),
                        GrammarItem::NonTerminal(parse_quote!(Name)),
                        GrammarItem::NonTerminal(parse_quote!(Proc)),
                    ],
                    bindings: vec![],
                    term_context: None,
                    syntax_pattern: None,
                },
            ],
            equations: vec![Equation {
                conditions: vec![FreshnessCondition {
                    var: parse_quote!(x),
                    term: FreshnessTarget::Var(parse_quote!(P)),
                }],
                // (PDrop (NQuote (PNew x P)))  -- has type Proc
                left: Pattern::Term(PatternTerm::Apply { 
                    constructor: parse_quote!(PDrop),
                    args: vec![Pattern::Term(PatternTerm::Apply { 
                        constructor: parse_quote!(NQuote),
                        args: vec![Pattern::Term(PatternTerm::Apply { 
                            constructor: parse_quote!(PNew),
                            args: vec![
                                Pattern::Term(PatternTerm::Var(parse_quote!(x))), 
                                Pattern::Term(PatternTerm::Var(parse_quote!(P)))
                            ] 
                        })] 
                    })] 
                }),
                // P  -- has type Proc
                right: Pattern::Term(PatternTerm::Var(parse_quote!(P))),
            }],
            rewrites: vec![],
            semantics: vec![],
        };

        // Should pass - x and P both appear in equation, types match
        let result = validate_theory(&theory);
        if let Err(e) = &result {
            eprintln!("Validation error: {}", e);
        }
        assert!(result.is_ok());
    }

    #[test]
    fn test_freshness_variable_not_in_equation() {
        // Invalid: freshness variable doesn't appear in equation
        let theory = TheoryDef {
            name: parse_quote!(Test),
            params: vec![],
            exports: vec![Export {
                name: parse_quote!(Name),
                native_type: None,
            }],
            terms: vec![GrammarRule {
                label: parse_quote!(NZero),
                category: parse_quote!(Name),
                items: vec![GrammarItem::Terminal("@0".to_string())],
                bindings: vec![],
                term_context: None,
                syntax_pattern: None,
            }],
            equations: vec![Equation {
                conditions: vec![FreshnessCondition {
                    var: parse_quote!(x), // x doesn't appear in equation!
                    term: FreshnessTarget::Var(parse_quote!(Q)),
                }],
                // (NZero) == (NZero) - no variables
                left: Pattern::Term(PatternTerm::Apply {
                    constructor: parse_quote!(NZero),
                    args: vec![],
                }),
                right: Pattern::Term(PatternTerm::Apply {
                    constructor: parse_quote!(NZero),
                    args: vec![],
                }),
            }],
            rewrites: vec![],
            semantics: vec![],
        };

        let result = validate_theory(&theory);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().message();
        assert!(err_msg.contains("does not appear in equation"));
    }

    #[test]
    fn test_freshness_self_reference() {
        // Invalid: x # x (variable fresh in itself)
        let theory = TheoryDef {
            name: parse_quote!(Test),
            params: vec![],
            exports: vec![Export {
                name: parse_quote!(Name),
                native_type: None,
            }],
            terms: vec![GrammarRule {
                label: parse_quote!(NVar),
                category: parse_quote!(Name),
                items: vec![GrammarItem::Terminal("var".to_string())],
                bindings: vec![],
                term_context: None,
                syntax_pattern: None,
            }],
            equations: vec![Equation {
                conditions: vec![FreshnessCondition {
                    var: parse_quote!(x),
                    term: FreshnessTarget::Var(parse_quote!(x)), // x # x is invalid
                }],
                // x == (NVar)
                left: Pattern::Term(PatternTerm::Var(parse_quote!(x))),
                right: Pattern::Term(PatternTerm::Apply {
                    constructor: parse_quote!(NVar),
                    args: vec![],
                }),
            }],
            rewrites: vec![],
            semantics: vec![],
        };

        let result = validate_theory(&theory);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().message();
        assert!(err_msg.contains("cannot be fresh in itself"));
    }
}
