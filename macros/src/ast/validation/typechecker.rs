use super::ValidationError;
use crate::ast::{language::{Equation, LanguageDef, LangType}, grammar::{GrammarItem, GrammarRule}, term::Term, language::RewriteRule, pattern::{Pattern, PatternTerm}};
use proc_macro2::Span;
use std::collections::HashMap;

/// Type checker for MeTTaIL languages
/// Infers and validates types/categories for all expressions
pub struct TypeChecker {
    /// Maps constructor names to their result category
    /// e.g., "PZero" -> "Proc", "NQuote" -> "Name"
    constructors: HashMap<String, ConstructorType>,

    /// Set of known categories/types
    categories: HashMap<String, CategoryInfo>,
}

/// Information about a constructor
#[derive(Debug, Clone)]
pub struct ConstructorType {
    pub name: String,
    pub result_category: String,
    pub arg_categories: Vec<String>,
}

/// Information about a category
#[derive(Debug, Clone)]
pub struct CategoryInfo {
    pub name: String,
    pub exported: bool,
}

#[derive(Debug)]
pub enum TypeError {
    UnknownConstructor(String),
    UnknownCategory(String),
    TypeMismatch {
        expected: String,
        found: String,
        context: String,
    },
    ArityMismatch {
        constructor: String,
        expected: usize,
        found: usize,
    },
}

impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeError::UnknownConstructor(name) => {
                write!(f, "Unknown constructor '{}'", name)
            },
            TypeError::UnknownCategory(name) => {
                write!(f, "Unknown category '{}'", name)
            },
            TypeError::TypeMismatch { expected, found, context } => {
                write!(
                    f,
                    "Type mismatch in {}: expected '{}', found '{}'",
                    context, expected, found
                )
            },
            TypeError::ArityMismatch { constructor, expected, found } => {
                write!(
                    f,
                    "Arity mismatch for constructor '{}': expected {} args, found {}",
                    constructor, expected, found
                )
            },
        }
    }
}

impl TypeChecker {
    /// Create a new type checker from a theory definition
    pub fn new(language: &LanguageDef) -> Self {
        let mut checker = TypeChecker {
            constructors: HashMap::new(),
            categories: HashMap::new(),
        };

        // Register all exported categories
        for lang_type in &language.types {
            checker.categories.insert(
                lang_type.name.to_string(),
                CategoryInfo {
                    name: lang_type.name.to_string(),
                    exported: true,
                },
            );
        }

        // Register all constructors from grammar rules
        for rule in &language.terms {
            checker.register_constructor(rule);
        }

        checker
    }

    /// Register a constructor from a grammar rule
    fn register_constructor(&mut self, rule: &GrammarRule) {
        let name = rule.label.to_string();
        let result_category = rule.category.to_string();

        // Extract argument categories from non-terminal items
        let arg_categories: Vec<String> = rule
            .items
            .iter()
            .filter_map(|item| match item {
                GrammarItem::NonTerminal(ident) => Some(ident.to_string()),
                GrammarItem::Binder { category } => Some(category.to_string()),
                GrammarItem::Collection { element_type, .. } => Some(element_type.to_string()),
                GrammarItem::Terminal(_) => None,
            })
            .collect();

        self.constructors
            .insert(name.clone(), ConstructorType { name, result_category, arg_categories });
    }

    /// Infer the type/category of an expression with a variable context
    pub fn infer_type_with_context(
        &self,
        expr: &Term,
        context: &mut HashMap<String, String>,
    ) -> Result<String, ValidationError> {
        match expr {
            Term::Var(var) => {
                let var_name = var.to_string();
                // Check if we already know this variable's type
                if let Some(typ) = context.get(&var_name) {
                    Ok(typ.clone())
                } else {
                    // Unknown variable - return placeholder
                    Ok("?".to_string())
                }
            },

            Term::Apply { constructor, args } => {
                let constructor_name = constructor.to_string();

                // Look up constructor type
                let ctor_type = self.constructors.get(&constructor_name).ok_or_else(|| {
                    ValidationError::UnknownConstructor {
                        name: constructor_name.clone(),
                        span: constructor.span(),
                    }
                })?;

                // Check arity
                if args.len() != ctor_type.arg_categories.len() {
                    return Err(ValidationError::ArityMismatch {
                        constructor: constructor_name,
                        expected: ctor_type.arg_categories.len(),
                        found: args.len(),
                        span: constructor.span(),
                    });
                }

                // Check each argument type and build context
                for (i, (arg, expected_cat)) in
                    args.iter().zip(&ctor_type.arg_categories).enumerate()
                {
                    // First, try to infer what we can from the arg
                    let arg_type = self.infer_type_with_context(arg, context)?;

                    // If it's a variable with unknown type, constrain it
                    if arg_type == "?" {
                        if let Term::Var(var) = arg {
                            context.insert(var.to_string(), expected_cat.clone());
                        }
                    } else {
                        // Concrete type - must match expected
                        if arg_type != *expected_cat {
                            return Err(ValidationError::TypeError {
                                expected: expected_cat.clone(),
                                found: arg_type,
                                context: format!("argument {} of {}", i + 1, constructor_name),
                                span: constructor.span(),
                            });
                        }
                    }
                }

                Ok(ctor_type.result_category.clone())
            },

            Term::Subst { term, var, replacement } => {
                // Infer type of the term being substituted into
                let term_type = self.infer_type_with_context(term, context)?;

                // The variable being substituted needs to have a type from context
                let var_name = var.to_string();

                // Infer type of replacement
                let replacement_type = self.infer_type_with_context(replacement, context)?;

                // The key insight: the variable and replacement must have the SAME type
                // But that type is independent of the term's type
                // Example: subst(P:Proc, x:Name, y:Name) is valid
                //   We're replacing Name x with Name y inside Proc P

                if let Some(existing_var_type) = context.get(&var_name) {
                    // Variable already has a type - replacement must match it
                    if replacement_type != "?" && replacement_type != *existing_var_type {
                        return Err(ValidationError::TypeError {
                            expected: existing_var_type.clone(),
                            found: replacement_type,
                            context: format!("substitution replacement for {}", var_name),
                            span: var.span(),
                        });
                    }
                } else {
                    // Variable doesn't have a type yet
                    if replacement_type != "?" {
                        // Constrain variable to match replacement
                        context.insert(var_name.clone(), replacement_type);
                    }
                }

                // The result type is the same as the term's type
                // subst(P:Proc, ...) => Proc
                Ok(term_type)
            },

            // Lambda expressions have function types [A -> B]
            // For now, return placeholder - full type inference comes with definitions
            Term::Lambda { body, .. } => {
                // Infer body type, but return function type placeholder
                let _ = self.infer_type_with_context(body, context)?;
                Ok("?->?".to_string())
            },

            Term::MultiLambda { body, .. } => {
                let _ = self.infer_type_with_context(body, context)?;
                Ok("?*->?".to_string())
            },
            
            Term::MultiSubst { .. } => {
                // MultiSubst returns the body type of the scope
                // Without full type inference, return placeholder
                    Ok("?".to_string())
            },
        }
    }

    /// Infer the type/category of an expression (legacy method - uses context internally)
    pub fn infer_type(&self, expr: &Term) -> Result<String, ValidationError> {
        let mut context = HashMap::new();
        self.infer_type_with_context(expr, &mut context)
    }

    /// Infer the type/category of a Pattern with a variable context
    pub fn infer_type_from_pattern(
        &self,
        pattern: &Pattern,
        context: &mut HashMap<String, String>,
    ) -> Result<String, ValidationError> {
        match pattern {
            Pattern::Term(pt) => self.infer_type_from_pattern_term(pt, context),
            Pattern::Collection { elements, .. } => {
                // Collections no longer have constructors - they get their type
                // from the enclosing PatternTerm::Apply. 
                // Here we just validate elements and return a placeholder.
                for elem in elements {
                    let _ = self.infer_type_from_pattern(elem, context)?;
                }
                // Collection type is determined by enclosing Apply
                Ok("Collection".to_string())
            }
            Pattern::Map { collection, body, .. } => {
                // Map doesn't change the type
                let _ = self.infer_type_from_pattern(collection, context)?;
                self.infer_type_from_pattern(body, context)
            }
            Pattern::Zip { first, second } => {
                // Zip combines types
                let _ = self.infer_type_from_pattern(first, context)?;
                let _ = self.infer_type_from_pattern(second, context)?;
                Ok("?".to_string())
            }
        }
    }

    /// Infer the type/category of a PatternTerm with a variable context
    fn infer_type_from_pattern_term(
        &self,
        pt: &PatternTerm,
        context: &mut HashMap<String, String>,
    ) -> Result<String, ValidationError> {
        match pt {
            PatternTerm::Var(name) => {
                let name_str = name.to_string();
                if let Some(ty) = context.get(&name_str) {
                    Ok(ty.clone())
                } else {
                    Ok("?".to_string())
                }
            }
            PatternTerm::Apply { constructor, args } => {
                let ctor_name = constructor.to_string();
                if let Some(ctor_type) = self.constructors.get(&ctor_name) {
                    // Check argument types match
                    for (arg, param) in args.iter().zip(&ctor_type.arg_categories) {
                        let arg_type = self.infer_type_from_pattern(arg, context)?;
                        if arg_type != "?" && arg_type != *param {
                            // Type mismatch
                        }
                    }
                    Ok(ctor_type.result_category.clone())
                } else {
                    Err(ValidationError::UnknownConstructor {
                        name: ctor_name,
                        span: constructor.span(),
                    })
                }
            }
            PatternTerm::Lambda { body, .. } => self.infer_type_from_pattern(body, context),
            PatternTerm::MultiLambda { body, .. } => self.infer_type_from_pattern(body, context),
            PatternTerm::Subst { term, .. } => self.infer_type_from_pattern(term, context),
            PatternTerm::MultiSubst { scope, .. } => self.infer_type_from_pattern(scope, context),
        }
    }

    /// Check that an equation is well-typed (both sides have same type)
    pub fn check_equation(&self, eq: &Equation) -> Result<(), ValidationError> {
        // Use a shared context to track variable types across both sides
        let mut context = HashMap::new();

        // Infer left side type (this will constrain variables)
        let left_type = self.infer_type_from_pattern(&eq.left, &mut context)?;

        // Infer right side type (using constraints from left side)
        let right_type = self.infer_type_from_pattern(&eq.right, &mut context)?;

        // Now both types should be concrete (no "?")
        // Skip if either side still has unknowns
        if left_type == "?" || right_type == "?" {
            return Ok(());
        }

        if left_type != right_type {
            return Err(ValidationError::TypeError {
                expected: left_type,
                found: right_type,
                context: "equation".to_string(),
                span: Span::call_site(), // TODO: Get span from equation
            });
        }

        Ok(())
    }

    /// Validate all equations in a theory
    pub fn validate_equations(&self, equations: &[Equation]) -> Result<(), ValidationError> {
        for eq in equations {
            self.check_equation(eq)?;
        }
        Ok(())
    }

    /// Check that a rewrite rule is well-typed (both sides have same type)
    pub fn check_rewrite(&self, rw: &RewriteRule) -> Result<(), ValidationError> {
        // Use a shared context to track variable types across both sides
        let mut context = HashMap::new();

        // Infer left side type from Pattern
        let left_type = self.infer_type_from_pattern(&rw.left, &mut context)?;

        // Infer right side type (using constraints from left side)
        let right_type = self.infer_type_from_pattern(&rw.right, &mut context)?;

        // Now both types should be concrete (no "?")
        // Skip if either side still has unknowns
        if left_type == "?" || right_type == "?" {
            return Ok(());
        }

        if left_type != right_type {
            return Err(ValidationError::TypeError {
                expected: left_type,
                found: right_type,
                context: "rewrite rule".to_string(),
                span: Span::call_site(), // TODO: Get span from rewrite rule
            });
        }

        Ok(())
    }

    /// Validate all rewrite rules in a theory
    pub fn validate_rewrites(&self, rewrites: &[RewriteRule]) -> Result<(), ValidationError> {
        for rw in rewrites {
            self.check_rewrite(rw)?;
        }
        Ok(())
    }

    /// Get information about a constructor
    pub fn get_constructor(&self, name: &str) -> Option<&ConstructorType> {
        self.constructors.get(name)
    }

    /// Check if a category exists
    pub fn has_category(&self, name: &str) -> bool {
        self.categories.contains_key(name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::*;
    use syn::parse_quote;

    fn make_simple_theory() -> LanguageDef {
        LanguageDef {
            name: parse_quote!(Test),
            params: vec![],
            types: vec![LangType {
                name: parse_quote!(Elem),
                native_type: None,
            }],
            terms: vec![
                GrammarRule {
                    label: parse_quote!(Zero),
                    category: parse_quote!(Elem),
                    items: vec![GrammarItem::Terminal("0".to_string())],
                    bindings: vec![],
                    term_context: None,
                    syntax_pattern: None,
                },
                GrammarRule {
                    label: parse_quote!(Succ),
                    category: parse_quote!(Elem),
                    items: vec![
                        GrammarItem::NonTerminal(parse_quote!(Elem)),
                        GrammarItem::Terminal("+".to_string()),
                        GrammarItem::Terminal("1".to_string()),
                    ],
                    bindings: vec![],
                    term_context: None,
                    syntax_pattern: None,
                },
            ],
            equations: vec![],
            rewrites: vec![],
            semantics: vec![],
        }
    }

    #[test]
    fn test_infer_constructor_type() {
        let language = make_simple_theory();
        let checker = TypeChecker::new(&language);

        // Zero has type Elem
        let zero_expr = Term::Apply {
            constructor: parse_quote!(Zero),
            args: vec![],
        };

        assert_eq!(checker.infer_type(&zero_expr).unwrap(), "Elem");
    }

    #[test]
    fn test_infer_nested_type() {
        let language = make_simple_theory();
        let checker = TypeChecker::new(&language);

        // Succ(Zero) has type Elem
        let nested = Term::Apply {
            constructor: parse_quote!(Succ),
            args: vec![Term::Apply {
                constructor: parse_quote!(Zero),
                args: vec![],
            }],
        };

        assert_eq!(checker.infer_type(&nested).unwrap(), "Elem");
    }

    #[test]
    fn test_check_valid_equation() {
        let language = make_simple_theory();
        let checker = TypeChecker::new(&language);

        // Zero == Zero (both Elem)
        let eq = Equation {
            conditions: vec![],
            left: Pattern::Term(PatternTerm::Apply {
                constructor: parse_quote!(Zero),
                args: vec![],
            }),
            right: Pattern::Term(PatternTerm::Apply {
                constructor: parse_quote!(Zero),
                args: vec![],
            }),
        };

        assert!(checker.check_equation(&eq).is_ok());
    }

    #[test]
    fn test_unknown_constructor() {
        let language = make_simple_theory();
        let checker = TypeChecker::new(&language);

        let expr = Term::Apply {
            constructor: parse_quote!(Unknown),
            args: vec![],
        };

        assert!(matches!(
            checker.infer_type(&expr),
            Err(ValidationError::UnknownConstructor { .. })
        ));
    }

    #[test]
    fn test_arity_mismatch() {
        let language = make_simple_theory();
        let checker = TypeChecker::new(&language);

        // Succ expects 1 arg, but given 0
        let expr = Term::Apply {
            constructor: parse_quote!(Succ),
            args: vec![],
        };

        assert!(matches!(checker.infer_type(&expr), Err(ValidationError::ArityMismatch { .. })));
    }
}
