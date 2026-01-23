use proc_macro2::{Span, TokenStream};
use quote::quote_spanned;

/// Validation error with span information for better compile-time diagnostics
#[derive(Debug, Clone)]
pub enum ValidationError {
    UnknownCategory {
        name: String,
        span: Span,
    },
    UnknownConstructor {
        name: String,
        span: Span,
    },
    CategoryNotExported {
        category: String,
        rule: String,
        span: Span,
    },
    UndefinedCategoryReference {
        category: String,
        rule: String,
        span: Span,
    },
    FreshnessVariableNotInEquation {
        var: String,
        span: Span,
    },
    FreshnessTermNotInEquation {
        var: String,
        term: String,
        span: Span,
    },
    FreshnessSelfReference {
        var: String,
        span: Span,
    },
    TypeError {
        expected: String,
        found: String,
        context: String,
        span: Span,
    },
    ArityMismatch {
        constructor: String,
        expected: usize,
        found: usize,
        span: Span,
    },
}

impl ValidationError {
    /// Get the span associated with this error
    pub fn span(&self) -> Span {
        match self {
            ValidationError::UnknownCategory { span, .. } => *span,
            ValidationError::UnknownConstructor { span, .. } => *span,
            ValidationError::CategoryNotExported { span, .. } => *span,
            ValidationError::UndefinedCategoryReference { span, .. } => *span,
            ValidationError::FreshnessVariableNotInEquation { span, .. } => *span,
            ValidationError::FreshnessTermNotInEquation { span, .. } => *span,
            ValidationError::FreshnessSelfReference { span, .. } => *span,
            ValidationError::TypeError { span, .. } => *span,
            ValidationError::ArityMismatch { span, .. } => *span,
        }
    }

    /// Get the error message
    pub fn message(&self) -> String {
        match self {
            ValidationError::UnknownCategory { name, .. } => {
                format!("Unknown category: '{}'", name)
            },
            ValidationError::UnknownConstructor { name, .. } => {
                format!("Unknown constructor '{}' in equation", name)
            },
            ValidationError::CategoryNotExported { category, rule, .. } => {
                format!("Rule '{}' has category '{}' which is not exported", rule, category)
            },
            ValidationError::UndefinedCategoryReference { category, rule, .. } => {
                format!("Rule '{}' references category '{}' which is not exported", rule, category)
            },
            ValidationError::FreshnessVariableNotInEquation { var, .. } => {
                format!(
                    "Freshness condition references variable '{}' which does not appear in equation",
                    var
                )
            },
            ValidationError::FreshnessTermNotInEquation { var, term, .. } => {
                format!(
                    "Freshness condition '{}' # '{}': term variable '{}' does not appear in equation",
                    var, term, term
                )
            },
            ValidationError::FreshnessSelfReference { var, .. } => {
                format!(
                    "Invalid freshness condition: '{}' # '{}' (variable cannot be fresh in itself)",
                    var, var
                )
            },
            ValidationError::TypeError { expected, found, context, .. } => {
                format!("Type mismatch in {}: expected '{}', found '{}'", context, expected, found)
            },
            ValidationError::ArityMismatch { constructor, expected, found, .. } => {
                format!(
                    "Arity mismatch for constructor '{}': expected {} args, found {}",
                    constructor, expected, found
                )
            },
        }
    }

    /// Convert to a compile_error! token stream
    pub fn to_compile_error(&self) -> TokenStream {
        let span = self.span();
        let msg = self.message();
        quote_spanned!(span => compile_error!(#msg))
    }
}

impl std::fmt::Display for ValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message())
    }
}

impl std::error::Error for ValidationError {}

/// Convert from string error (legacy) to ValidationError
/// Uses call_site span since we don't have more specific information
impl From<String> for ValidationError {
    fn from(s: String) -> Self {
        // Try to parse the string to determine error type
        if s.contains("not exported") && s.contains("has category") {
            // Extract rule and category names
            ValidationError::CategoryNotExported {
                category: "Unknown".to_string(),
                rule: "Unknown".to_string(),
                span: Span::call_site(),
            }
        } else if s.contains("Unknown constructor") {
            ValidationError::UnknownConstructor {
                name: "Unknown".to_string(),
                span: Span::call_site(),
            }
        } else {
            // Generic error - use TypeError as catch-all
            ValidationError::TypeError {
                expected: "".to_string(),
                found: "".to_string(),
                context: s,
                span: Span::call_site(),
            }
        }
    }
}
