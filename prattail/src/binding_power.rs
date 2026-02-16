//! Binding power analysis and table generation.
//!
//! Analyzes grammar rules to identify infix operators and assigns binding power
//! pairs for Pratt parsing. Binding power pairs `(left_bp, right_bp)` control
//! precedence and associativity:
//! - Left-associative: `left_bp < right_bp` (e.g., `(2, 3)` for `+`)
//! - Right-associative: `left_bp > right_bp` (e.g., `(7, 6)` for `^`)

use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use crate::automata::codegen::terminal_to_variant_name;

/// Associativity of an infix operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Associativity {
    Left,
    Right,
}

/// An infix operator with its binding power.
#[derive(Debug, Clone)]
pub struct InfixOperator {
    /// The terminal text of the operator (e.g., "+", "*", "==").
    /// For mixfix operators, this is the trigger terminal (e.g., "?" for ternary).
    pub terminal: String,
    /// The category this operator applies to (e.g., "Proc", "Int").
    pub category: String,
    /// The result category (usually same as `category` for same-type infix,
    /// but different for cross-category like `Int == Int -> Bool`).
    pub result_category: String,
    /// Left binding power.
    pub left_bp: u8,
    /// Right binding power.
    pub right_bp: u8,
    /// The constructor label for this operator (e.g., "Add", "PPar").
    pub label: String,
    /// Whether this is a cross-category operator (operands from one category,
    /// result in another).
    pub is_cross_category: bool,
    /// Whether this is a postfix operator (e.g., a!, a?, a++).
    /// Postfix operators have left_bp but no right recursive call.
    pub is_postfix: bool,
    /// Whether this is a mixfix operator (e.g., a ? b : c, with 3+ operands).
    /// Mixfix operators parse middle operands at min_bp=0 (reset like grouping)
    /// and the final operand at right_bp.
    pub is_mixfix: bool,
    /// Parts of a mixfix operator: the operand-separator pairs after the trigger.
    /// Empty for regular infix/postfix.
    pub mixfix_parts: Vec<MixfixPart>,
}

/// A part of a mixfix operator after the trigger terminal.
///
/// Each part describes an operand to parse, and optionally a terminal
/// separator that follows it (all parts except the last have a separator).
///
/// Example: `a "?" b ":" c` has parts:
/// - MixfixPart { category: "Int", param: "b", following: Some(":") }
/// - MixfixPart { category: "Int", param: "c", following: None }
#[derive(Debug, Clone)]
pub struct MixfixPart {
    /// Category of the operand to parse.
    pub operand_category: String,
    /// Parameter name (for AST construction).
    pub param_name: String,
    /// Terminal separator that follows this operand (None for the last operand).
    pub following_terminal: Option<String>,
}

impl InfixOperator {
    /// Returns the associativity of this operator.
    pub fn associativity(&self) -> Associativity {
        if self.left_bp < self.right_bp {
            Associativity::Left
        } else {
            Associativity::Right
        }
    }
}

/// A binding power table for a language.
#[derive(Debug, Clone)]
pub struct BindingPowerTable {
    /// All infix operators, grouped by result category.
    pub operators: Vec<InfixOperator>,
}

impl BindingPowerTable {
    /// Create a new empty binding power table.
    pub fn new() -> Self {
        BindingPowerTable {
            operators: Vec::new(),
        }
    }

    /// Get all regular infix operators for a given category (excludes postfix, mixfix, cross-category).
    pub fn operators_for_category(&self, category: &str) -> Vec<&InfixOperator> {
        self.operators
            .iter()
            .filter(|op| {
                op.category == category
                    && !op.is_cross_category
                    && !op.is_postfix
                    && !op.is_mixfix
            })
            .collect()
    }

    /// Get all postfix operators for a given category.
    pub fn postfix_operators_for_category(&self, category: &str) -> Vec<&InfixOperator> {
        self.operators
            .iter()
            .filter(|op| op.category == category && op.is_postfix)
            .collect()
    }

    /// Get all mixfix operators for a given category.
    pub fn mixfix_operators_for_category(&self, category: &str) -> Vec<&InfixOperator> {
        self.operators
            .iter()
            .filter(|op| op.category == category && op.is_mixfix)
            .collect()
    }

    /// Get all cross-category operators that produce results in the given category.
    pub fn cross_category_operators(&self, result_category: &str) -> Vec<&InfixOperator> {
        self.operators
            .iter()
            .filter(|op| op.result_category == result_category && op.is_cross_category)
            .collect()
    }

    /// Generate the `infix_bp` function for a specific category.
    pub fn generate_bp_function(&self, category: &str) -> TokenStream {
        let mut arms: Vec<TokenStream> = Vec::new();

        for op in self.operators_for_category(category) {
            let variant = format_ident!("{}", terminal_to_variant_name(&op.terminal));
            let left_bp = op.left_bp;
            let right_bp = op.right_bp;
            arms.push(quote! {
                Token::#variant => Some((#left_bp, #right_bp))
            });
        }

        arms.push(quote! { _ => None });

        quote! {
            /// Get the binding power pair for an infix operator in this category.
            fn infix_bp(token: &Token) -> Option<(u8, u8)> {
                match token {
                    #(#arms),*
                }
            }
        }
    }

    /// Generate the `make_infix` function for a specific category.
    pub fn generate_make_infix(&self, category: &str) -> TokenStream {
        let cat_ident = format_ident!("{}", category);
        let mut arms: Vec<TokenStream> = Vec::new();

        for op in self.operators_for_category(category) {
            let variant = format_ident!("{}", terminal_to_variant_name(&op.terminal));
            let label = format_ident!("{}", op.label);
            arms.push(quote! {
                Token::#variant => #cat_ident::#label(Box::new(lhs), Box::new(rhs))
            });
        }

        arms.push(quote! {
            _ => unreachable!("make_infix called with non-infix token")
        });

        quote! {
            /// Construct an infix AST node from an operator token and operands.
            fn make_infix(token: &Token, lhs: #cat_ident, rhs: #cat_ident) -> #cat_ident {
                match token {
                    #(#arms),*
                }
            }
        }
    }
}

impl Default for BindingPowerTable {
    fn default() -> Self {
        Self::new()
    }
}

/// Analyze grammar rules to build the binding power table.
///
/// Rules are classified as infix if:
/// - Old syntax: ≥3 items, first and last are NonTerminal matching the category,
///   with at least one Terminal in between
/// - New syntax: syntax_pattern is [Param, Literal, Param] with both params
///   having the same type as the result category
///
/// Precedence is assigned by declaration order: first-declared infix operator
/// gets the lowest precedence. Operators within the same precedence group
/// are left-associative by default.
///
/// Postfix operators are assigned binding powers above all non-postfix operators
/// in a second pass, ensuring they always bind tighter than infix operators
/// regardless of declaration order. This follows the standard convention that
/// postfix binds tighter than infix (e.g., `3 + 5!` = `3 + (5!)`), and unary
/// prefix binds between infix and postfix (e.g., `-5!` = `-(5!)`).
pub fn analyze_binding_powers(rules: &[InfixRuleInfo]) -> BindingPowerTable {
    let mut table = BindingPowerTable::new();

    // Group infix rules by category
    let mut by_category: std::collections::BTreeMap<String, Vec<&InfixRuleInfo>> =
        std::collections::BTreeMap::new();
    for rule in rules {
        by_category
            .entry(rule.category.clone())
            .or_default()
            .push(rule);
    }

    // Assign binding powers per category using two passes:
    // 1. Non-postfix (infix) operators in declaration order
    // 2. Postfix operators above the non-postfix range, leaving a gap for
    //    unary prefix (which gets max_non_postfix_bp + 2 in lib.rs)
    for cat_rules in by_category.values() {
        let mut precedence: u8 = 2; // Start at 2 to leave room for 0 (entry) and 1

        // First pass: non-postfix operators (regular infix + mixfix)
        for rule in cat_rules.iter().filter(|r| !r.is_postfix) {
            let (left_bp, right_bp) = match rule.associativity {
                Associativity::Left => {
                    let bp = (precedence, precedence + 1);
                    precedence += 2;
                    bp
                }
                Associativity::Right => {
                    let bp = (precedence + 1, precedence);
                    precedence += 2;
                    bp
                }
            };

            table.operators.push(InfixOperator {
                terminal: rule.terminal.clone(),
                category: rule.category.clone(),
                result_category: rule.result_category.clone(),
                left_bp,
                right_bp,
                label: rule.label.clone(),
                is_cross_category: rule.is_cross_category,
                is_postfix: false,
                is_mixfix: rule.is_mixfix,
                mixfix_parts: rule.mixfix_parts.clone(),
            });
        }

        // Second pass: postfix operators start above non-postfix + prefix gap.
        // Layout: [infix at 2..precedence-1] [prefix at precedence+0..+1] [postfix at precedence+2..]
        let mut postfix_prec = precedence + 2;
        for rule in cat_rules.iter().filter(|r| r.is_postfix) {
            table.operators.push(InfixOperator {
                terminal: rule.terminal.clone(),
                category: rule.category.clone(),
                result_category: rule.result_category.clone(),
                left_bp: postfix_prec + 1,
                right_bp: 0, // unused for postfix (no right recursive call)
                label: rule.label.clone(),
                is_cross_category: rule.is_cross_category,
                is_postfix: true,
                is_mixfix: false,
                mixfix_parts: Vec::new(),
            });
            postfix_prec += 2;
        }
    }

    table
}

/// Simplified infix rule info for binding power analysis.
#[derive(Debug, Clone)]
pub struct InfixRuleInfo {
    /// Constructor label (e.g., "Add", "Mul").
    pub label: String,
    /// Terminal operator text (e.g., "+", "*").
    /// For mixfix operators, this is the trigger terminal (e.g., "?" for ternary).
    pub terminal: String,
    /// Operand category (e.g., "Int").
    pub category: String,
    /// Result category (e.g., "Int" for same-category, "Bool" for cross-category).
    pub result_category: String,
    /// Associativity (default: Left).
    pub associativity: Associativity,
    /// Whether this is a cross-category operator.
    pub is_cross_category: bool,
    /// Whether this is a postfix operator.
    pub is_postfix: bool,
    /// Whether this is a mixfix operator (3+ operands, 2+ terminals).
    pub is_mixfix: bool,
    /// Mixfix parts (operand-separator pairs after the trigger). Empty for non-mixfix.
    pub mixfix_parts: Vec<MixfixPart>,
}
