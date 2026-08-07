use super::ValidationError;
use crate::{
    grammar::{GrammarItem, GrammarRule},
    language::RewriteRule,
    language::{Equation, LanguageDef},
    pattern::{Pattern, PatternTerm},
};
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
#[allow(dead_code)]
pub struct ConstructorType {
    pub name: String,
    pub result_category: String,
    pub arg_categories: Vec<String>,
}

/// Information about a category
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct CategoryInfo {
    pub name: String,
    pub exported: bool,
}

#[derive(Debug)]
#[allow(dead_code)]
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
                GrammarItem::NonTerminal { ident, .. } => Some(ident.to_string()),
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
        enum Task<'pattern> {
            Pattern(&'pattern Pattern),
            Term(&'pattern PatternTerm),
            AssemblePattern(&'pattern Pattern, usize),
            AssembleApply {
                result_category: String,
                value_base: usize,
            },
            PassThroughTerm(usize),
        }

        let mut tasks = vec![Task::Pattern(pattern)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Pattern(pattern) => match pattern {
                    Pattern::Term(term) => {
                        tasks.push(Task::AssemblePattern(pattern, values.len()));
                        tasks.push(Task::Term(term));
                    },
                    Pattern::Collection { elements, .. } => {
                        tasks.push(Task::AssemblePattern(pattern, values.len()));
                        tasks.extend(elements.iter().rev().map(Task::Pattern));
                    },
                    Pattern::Map { collection, body, .. } => {
                        tasks.push(Task::AssemblePattern(pattern, values.len()));
                        tasks.push(Task::Pattern(body));
                        tasks.push(Task::Pattern(collection));
                    },
                    Pattern::Zip { first, second } => {
                        tasks.push(Task::AssemblePattern(pattern, values.len()));
                        tasks.push(Task::Pattern(second));
                        tasks.push(Task::Pattern(first));
                    },
                    Pattern::IndexedVec { element, .. } => {
                        tasks.push(Task::AssemblePattern(pattern, values.len()));
                        tasks.push(Task::Pattern(element));
                    },
                },
                Task::Term(term) => match term {
                    PatternTerm::Var(name) => values.push(
                        context
                            .get(&name.to_string())
                            .cloned()
                            .unwrap_or_else(|| "?".to_string()),
                    ),
                    PatternTerm::Apply { constructor, args } => {
                        let constructor_name = constructor.to_string();
                        let Some(constructor_type) = self.constructors.get(&constructor_name)
                        else {
                            return Err(ValidationError::UnknownConstructor {
                                name: constructor_name,
                                span: constructor.span(),
                            });
                        };
                        tasks.push(Task::AssembleApply {
                            result_category: constructor_type.result_category.clone(),
                            value_base: values.len(),
                        });
                        let paired_arguments =
                            args.len().min(constructor_type.arg_categories.len());
                        tasks.extend(args[..paired_arguments].iter().rev().map(Task::Pattern));
                    },
                    PatternTerm::Lambda { body, .. } | PatternTerm::MultiLambda { body, .. } => {
                        tasks.push(Task::PassThroughTerm(values.len()));
                        tasks.push(Task::Pattern(body));
                    },
                    PatternTerm::Subst { term: value, .. } => {
                        tasks.push(Task::PassThroughTerm(values.len()));
                        tasks.push(Task::Pattern(value));
                    },
                    PatternTerm::MultiSubst { scope, .. } => {
                        tasks.push(Task::PassThroughTerm(values.len()));
                        tasks.push(Task::Pattern(scope));
                    },
                },
                Task::AssemblePattern(pattern, value_base) => {
                    let inferred = match pattern {
                        Pattern::Term(_) => values.pop().unwrap_or_else(|| "?".to_string()),
                        Pattern::Collection { .. } => "Collection".to_string(),
                        Pattern::Map { .. } => values.pop().unwrap_or_else(|| "?".to_string()),
                        Pattern::Zip { .. } | Pattern::IndexedVec { .. } => "?".to_string(),
                    };
                    values.truncate(value_base);
                    values.push(inferred);
                },
                Task::AssembleApply { result_category, value_base } => {
                    values.truncate(value_base);
                    values.push(result_category);
                },
                Task::PassThroughTerm(value_base) => {
                    let inferred = values.pop().unwrap_or_else(|| "?".to_string());
                    values.truncate(value_base);
                    values.push(inferred);
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        Ok(values.pop().unwrap_or_else(|| "?".to_string()))
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
                span: eq.name.span(),
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
                span: rw.name.span(),
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
