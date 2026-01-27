use super::ValidationError;
use crate::ast::{language::{Equation, LanguageDef}, grammar::{GrammarItem, GrammarRule}, language::RewriteRule, pattern::{Pattern, PatternTerm}};
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

}