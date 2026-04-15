use proc_macro2::{Span, TokenStream};
use quote::quote_spanned;

/// Validation error with span information for better compile-time diagnostics
#[derive(Debug, Clone)]
#[allow(dead_code)]
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

    // ── Guard configuration lints (design doc §2A) ────────────────────────

    /// CONN01: a connective keyword is mapped to multiple roles.
    DuplicateConnectiveKeyword {
        keyword: String,
        role_a: String,
        role_b: String,
        span: Span,
    },

    /// CONN02: a guard expression uses a Rust-token connective (e.g.,
    /// `&&`, `||`, `~`, `!`, `=>`) that is not declared in the active
    /// `connectives { }` sub-block. Fires only when explicit connectives
    /// are present (closed-world mode).
    UnlistedConnectiveToken {
        token: String,
        role: String,
        span: Span,
    },

    /// GUARD01: a guard expression references a predicate name that is
    /// not declared in `guards { }` or `logic { }`.
    UnknownGuardPredicate {
        name: String,
        available: Vec<String>,
        span: Span,
    },

    /// MT01: a channel category is declared but never referenced in any
    /// `join` pattern. Warning, not error.
    UnusedChannelCategory {
        category: String,
        span: Span,
    },

    /// MT02: a `join` pattern references a category not declared as a
    /// channel.
    UndeclaredChannelReference {
        category: String,
        join_label: String,
        span: Span,
    },

    /// TW02: a `join` pattern has only one channel parameter (M8 fusion
    /// would not benefit). Warning, not error.
    SingleChannelJoin {
        label: String,
        span: Span,
    },

    /// TW03: a `join` pattern's label does not correspond to any constructor
    /// declared in the `terms { }` block.
    JoinPatternUnknownConstructor {
        label: String,
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
            ValidationError::DuplicateConnectiveKeyword { span, .. } => *span,
            ValidationError::UnlistedConnectiveToken { span, .. } => *span,
            ValidationError::UnknownGuardPredicate { span, .. } => *span,
            ValidationError::UnusedChannelCategory { span, .. } => *span,
            ValidationError::UndeclaredChannelReference { span, .. } => *span,
            ValidationError::SingleChannelJoin { span, .. } => *span,
            ValidationError::JoinPatternUnknownConstructor { span, .. } => *span,
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
            ValidationError::DuplicateConnectiveKeyword { keyword, role_a, role_b, .. } => {
                format!(
                    "CONN01: keyword `{}` is mapped to multiple connective roles ({} and {})",
                    keyword, role_a, role_b
                )
            },
            ValidationError::UnlistedConnectiveToken { token, role, .. } => {
                format!(
                    "CONN02: connective token `{}` (role `{}`) is not declared in the \
                     active `connectives {{}}` block",
                    token, role
                )
            },
            ValidationError::UnknownGuardPredicate { name, available, .. } => {
                if available.is_empty() {
                    format!(
                        "GUARD01: unknown predicate `{}` in guard expression \
                         (no predicates declared in `guards {{}}` or `logic {{}}`)",
                        name
                    )
                } else {
                    let preview: Vec<&str> =
                        available.iter().take(8).map(|s| s.as_str()).collect();
                    let suffix = if available.len() > 8 { ", ..." } else { "" };
                    format!(
                        "GUARD01: unknown predicate `{}` in guard expression \
                         (available: {}{})",
                        name,
                        preview.join(", "),
                        suffix
                    )
                }
            },
            ValidationError::UnusedChannelCategory { category, .. } => {
                format!(
                    "MT01: channel category `{}` is declared but never referenced \
                     in any `join` pattern",
                    category
                )
            },
            ValidationError::UndeclaredChannelReference { category, join_label, .. } => {
                format!(
                    "MT02: join pattern `{}` references undeclared channel \
                     category `{}`",
                    join_label, category
                )
            },
            ValidationError::SingleChannelJoin { label, .. } => {
                format!(
                    "TW02: join pattern `{}` has only one channel parameter \
                     (multi-tape fusion does not apply)",
                    label
                )
            },
            ValidationError::JoinPatternUnknownConstructor { label, .. } => {
                format!(
                    "TW03: join pattern `{}` has no corresponding term constructor \
                     in the `terms {{}}` block",
                    label
                )
            },
        }
    }

    /// Convert to a compile_error! token stream
    #[allow(dead_code)]
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
