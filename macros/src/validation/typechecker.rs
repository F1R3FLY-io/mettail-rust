use super::ValidationError;
use crate::ast::{Equation, Expr, GrammarItem, GrammarRule, RewriteRule, TheoryDef};
use proc_macro2::Span;
use std::collections::HashMap;

/// Type checker for MeTTaIL theories
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
    #[allow(dead_code)]
    pub name: String,
    pub result_category: String,
    pub arg_categories: Vec<String>,
}

/// Information about a category
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub struct CategoryInfo {
    pub name: String,
    pub exported: bool,
}

#[allow(dead_code)]
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
    pub fn new(theory: &TheoryDef) -> Self {
        let mut checker = TypeChecker {
            constructors: HashMap::new(),
            categories: HashMap::new(),
        };

        // Register all exported categories
        for export in &theory.exports {
            checker.categories.insert(
                export.name.to_string(),
                CategoryInfo {
                    name: export.name.to_string(),
                    exported: true,
                },
            );
        }

        // Register all constructors from grammar rules
        for rule in &theory.terms {
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
    #[allow(dead_code)]
    pub fn infer_type_with_context(
        &self,
        expr: &Expr,
        context: &mut HashMap<String, String>,
    ) -> Result<String, ValidationError> {
        match expr {
            Expr::Var(var) => {
                let var_name = var.to_string();
                // Check if we already know this variable's type
                if let Some(typ) = context.get(&var_name) {
                    Ok(typ.clone())
                } else {
                    // Unknown variable - return placeholder
                    Ok("?".to_string())
                }
            },

            Expr::Apply { constructor, args } => {
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
                        if let Expr::Var(var) = arg {
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

            Expr::Subst { term, var, replacement } => {
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

            Expr::CollectionPattern { constructor, elements, rest } => {
                // For collection patterns, we need to infer the constructor
                // and type-check the elements against the collection's element type

                // For now, return a placeholder
                // Full implementation will come when we generate Ascent code
                // TODO: Implement proper type inference for collection patterns

                // Type-check element patterns
                for elem in elements {
                    let _ = self.infer_type_with_context(elem, context)?;
                }

                // Rest variable gets bound to a collection type
                if let Some(rest_var) = rest {
                    // For now, don't add to context
                    // Will be handled during Ascent generation
                    let _ = rest_var;
                }

                // Return placeholder - will be refined during validation
                if let Some(cons) = constructor {
                    // Look up the constructor's result category
                    if let Some(ctor) = self.constructors.get(&cons.to_string()) {
                        Ok(ctor.result_category.clone())
                    } else {
                        Ok("?".to_string())
                    }
                } else {
                    Ok("?".to_string())
                }
            },

            // Lambda expressions have function types [A -> B]
            // For now, return placeholder - full type inference comes with definitions
            Expr::Lambda { body, .. } => {
                // Infer body type, but return function type placeholder
                let _ = self.infer_type_with_context(body, context)?;
                Ok("?->?".to_string())
            },

            Expr::MultiLambda { body, .. } => {
                let _ = self.infer_type_with_context(body, context)?;
                Ok("?*->?".to_string())
            },
        }
    }

    /// Infer the type/category of an expression (legacy method - uses context internally)
    #[allow(dead_code)]
    pub fn infer_type(&self, expr: &Expr) -> Result<String, ValidationError> {
        let mut context = HashMap::new();
        self.infer_type_with_context(expr, &mut context)
    }

    /// Check that an equation is well-typed (both sides have same type)
    pub fn check_equation(&self, eq: &Equation) -> Result<(), ValidationError> {
        // Use a shared context to track variable types across both sides
        let mut context = HashMap::new();

        // Infer left side type (this will constrain variables)
        let left_type = self.infer_type_with_context(&eq.left, &mut context)?;

        // Infer right side type (using constraints from left side)
        let right_type = self.infer_type_with_context(&eq.right, &mut context)?;

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

        // Infer left side type (this will constrain variables)
        let left_type = self.infer_type_with_context(&rw.left, &mut context)?;

        // Infer right side type (using constraints from left side)
        let right_type = self.infer_type_with_context(&rw.right, &mut context)?;

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
    #[allow(dead_code)]
    pub fn get_constructor(&self, name: &str) -> Option<&ConstructorType> {
        self.constructors.get(name)
    }

    /// Check if a category exists
    #[allow(dead_code)]
    pub fn has_category(&self, name: &str) -> bool {
        self.categories.contains_key(name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::*;
    use syn::parse_quote;

    fn make_simple_theory() -> TheoryDef {
        TheoryDef {
            name: parse_quote!(Test),
            params: vec![],
            exports: vec![Export {
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
        let theory = make_simple_theory();
        let checker = TypeChecker::new(&theory);

        // Zero has type Elem
        let zero_expr = Expr::Apply {
            constructor: parse_quote!(Zero),
            args: vec![],
        };

        assert_eq!(checker.infer_type(&zero_expr).unwrap(), "Elem");
    }

    #[test]
    fn test_infer_nested_type() {
        let theory = make_simple_theory();
        let checker = TypeChecker::new(&theory);

        // Succ(Zero) has type Elem
        let nested = Expr::Apply {
            constructor: parse_quote!(Succ),
            args: vec![Expr::Apply {
                constructor: parse_quote!(Zero),
                args: vec![],
            }],
        };

        assert_eq!(checker.infer_type(&nested).unwrap(), "Elem");
    }

    #[test]
    fn test_check_valid_equation() {
        let theory = make_simple_theory();
        let checker = TypeChecker::new(&theory);

        // Zero == Zero (both Elem)
        let eq = Equation {
            conditions: vec![],
            left: Expr::Apply {
                constructor: parse_quote!(Zero),
                args: vec![],
            },
            right: Expr::Apply {
                constructor: parse_quote!(Zero),
                args: vec![],
            },
        };

        assert!(checker.check_equation(&eq).is_ok());
    }

    #[test]
    fn test_unknown_constructor() {
        let theory = make_simple_theory();
        let checker = TypeChecker::new(&theory);

        let expr = Expr::Apply {
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
        let theory = make_simple_theory();
        let checker = TypeChecker::new(&theory);

        // Succ expects 1 arg, but given 0
        let expr = Expr::Apply {
            constructor: parse_quote!(Succ),
            args: vec![],
        };

        assert!(matches!(checker.infer_type(&expr), Err(ValidationError::ArityMismatch { .. })));
    }
}
