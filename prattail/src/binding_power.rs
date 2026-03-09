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
        BindingPowerTable { operators: Vec::new() }
    }

    /// Get all regular infix operators for a given category (excludes postfix, mixfix, cross-category).
    pub fn operators_for_category(&self, category: &str) -> Vec<&InfixOperator> {
        self.operators
            .iter()
            .filter(|op| {
                op.category == category && !op.is_cross_category && !op.is_postfix && !op.is_mixfix
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
    ///
    /// Groups operators that share the same (left_bp, right_bp) pair into
    /// a single match arm with `|`-separated patterns for compact codegen.
    pub fn generate_bp_function(&self, category: &str) -> TokenStream {
        // Group operators by (left_bp, right_bp) pair
        let mut bp_groups: std::collections::BTreeMap<(u8, u8), Vec<proc_macro2::Ident>> =
            std::collections::BTreeMap::new();
        for op in self.operators_for_category(category) {
            let variant = format_ident!("{}", terminal_to_variant_name(&op.terminal));
            bp_groups
                .entry((op.left_bp, op.right_bp))
                .or_default()
                .push(variant);
        }

        let mut arms: Vec<TokenStream> = Vec::with_capacity(bp_groups.len() + 1);
        for ((left_bp, right_bp), variants) in &bp_groups {
            let left_bp = *left_bp;
            let right_bp = *right_bp;
            arms.push(quote! {
                #(Token::#variants)|* => Some((#left_bp, #right_bp))
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

    /// BP03: Generate the `infix_bp` function using a static array lookup.
    ///
    /// When the category has >= `threshold` operators and `variant_map` is provided,
    /// emits a `static` array indexed by `token_variant_id()` instead of a match.
    /// Falls back to `generate_bp_function()` when the threshold is not met.
    ///
    /// Requires that `token_variant_id()` is emitted elsewhere (e.g., by
    /// `write_token_variant_id()` in `codegen.rs`).
    pub fn generate_bp_function_array(
        &self,
        category: &str,
        variant_map: &crate::automata::codegen::TokenVariantMap,
        threshold: usize,
    ) -> TokenStream {
        let ops = self.operators_for_category(category);
        if ops.len() < threshold {
            return self.generate_bp_function(category);
        }

        let array_len = variant_map.count as usize;
        let cat_upper = format_ident!("INFIX_BP_{}", category.to_uppercase());

        // Build array entries
        let mut entries = vec![(0u8, 0u8); array_len];
        for op in &ops {
            let variant_name = terminal_to_variant_name(&op.terminal);
            if let Some(id) = variant_map.get_id(&variant_name) {
                entries[id as usize] = (op.left_bp, op.right_bp);
            }
        }

        let entry_tokens: Vec<TokenStream> = entries
            .iter()
            .map(|(l, r)| quote! { (#l, #r) })
            .collect();
        let len_lit = array_len;

        quote! {
            static #cat_upper: [(u8, u8); #len_lit] = [#(#entry_tokens),*];

            /// Get the binding power pair for an infix operator in this category.
            #[inline]
            fn infix_bp(token: &Token) -> Option<(u8, u8)> {
                let bp = #cat_upper[token_variant_id(token) as usize];
                if bp != (0, 0) { Some(bp) } else { None }
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
                },
                Associativity::Right => {
                    let bp = (precedence + 1, precedence);
                    precedence += 2;
                    bp
                },
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

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper to create an InfixRuleInfo with default flags (non-cross, non-postfix, non-mixfix).
    fn make_rule(label: &str, terminal: &str, category: &str, assoc: Associativity) -> InfixRuleInfo {
        InfixRuleInfo {
            label: label.to_string(),
            terminal: terminal.to_string(),
            category: category.to_string(),
            result_category: category.to_string(),
            associativity: assoc,
            is_cross_category: false,
            is_postfix: false,
            is_mixfix: false,
            mixfix_parts: Vec::new(),
        }
    }

    /// Helper to create an InfixOperator directly (for filter tests that bypass analyze).
    fn make_op(
        label: &str,
        terminal: &str,
        category: &str,
        result_category: &str,
        left_bp: u8,
        right_bp: u8,
        is_cross_category: bool,
        is_postfix: bool,
        is_mixfix: bool,
    ) -> InfixOperator {
        InfixOperator {
            terminal: terminal.to_string(),
            category: category.to_string(),
            result_category: result_category.to_string(),
            left_bp,
            right_bp,
            label: label.to_string(),
            is_cross_category,
            is_postfix,
            is_mixfix,
            mixfix_parts: Vec::new(),
        }
    }

    #[test]
    fn test_bp_table_new_empty() {
        let table = BindingPowerTable::new();
        assert!(table.operators.is_empty(), "new table should have zero operators");
    }

    #[test]
    fn test_operators_for_category_filter() {
        let mut table = BindingPowerTable::new();
        // Two Int operators, one Bool operator
        table.operators.push(make_op("Add", "+", "Int", "Int", 2, 3, false, false, false));
        table.operators.push(make_op("Mul", "*", "Int", "Int", 4, 5, false, false, false));
        table.operators.push(make_op("And", "&&", "Bool", "Bool", 2, 3, false, false, false));

        let int_ops = table.operators_for_category("Int");
        assert_eq!(int_ops.len(), 2, "should return only Int operators");
        assert_eq!(int_ops[0].label, "Add");
        assert_eq!(int_ops[1].label, "Mul");

        let bool_ops = table.operators_for_category("Bool");
        assert_eq!(bool_ops.len(), 1);
        assert_eq!(bool_ops[0].label, "And");

        let empty = table.operators_for_category("String");
        assert!(empty.is_empty(), "non-existent category should return empty");
    }

    #[test]
    fn test_postfix_operators_for_category() {
        let mut table = BindingPowerTable::new();
        table.operators.push(make_op("Add", "+", "Int", "Int", 2, 3, false, false, false));
        table.operators.push(make_op("Fact", "!", "Int", "Int", 10, 0, false, true, false));
        table.operators.push(make_op("Incr", "++", "Int", "Int", 12, 0, false, true, false));

        let postfix = table.postfix_operators_for_category("Int");
        assert_eq!(postfix.len(), 2, "should return only postfix operators");
        assert_eq!(postfix[0].label, "Fact");
        assert_eq!(postfix[1].label, "Incr");
    }

    #[test]
    fn test_mixfix_operators_for_category() {
        let mut table = BindingPowerTable::new();
        table.operators.push(make_op("Add", "+", "Int", "Int", 2, 3, false, false, false));
        let mut ternary = make_op("Ternary", "?", "Int", "Int", 2, 3, false, false, true);
        ternary.mixfix_parts = vec![
            MixfixPart {
                operand_category: "Int".to_string(),
                param_name: "b".to_string(),
                following_terminal: Some(":".to_string()),
            },
            MixfixPart {
                operand_category: "Int".to_string(),
                param_name: "c".to_string(),
                following_terminal: None,
            },
        ];
        table.operators.push(ternary);

        let mixfix = table.mixfix_operators_for_category("Int");
        assert_eq!(mixfix.len(), 1, "should return only mixfix operators");
        assert_eq!(mixfix[0].label, "Ternary");
        assert_eq!(mixfix[0].mixfix_parts.len(), 2);
    }

    #[test]
    fn test_cross_category_operators() {
        let mut table = BindingPowerTable::new();
        // Regular same-category op
        table.operators.push(make_op("Add", "+", "Int", "Int", 2, 3, false, false, false));
        // Cross-category: Int == Int -> Bool
        table.operators.push(make_op("Eq", "==", "Int", "Bool", 2, 3, true, false, false));
        // Cross-category: Int < Int -> Bool
        table.operators.push(make_op("Lt", "<", "Int", "Bool", 2, 3, true, false, false));

        let cross = table.cross_category_operators("Bool");
        assert_eq!(cross.len(), 2, "should return cross-cat ops producing Bool");
        assert_eq!(cross[0].label, "Eq");
        assert_eq!(cross[1].label, "Lt");

        let cross_int = table.cross_category_operators("Int");
        assert!(cross_int.is_empty(), "no cross-cat ops produce Int");
    }

    #[test]
    fn test_analyze_bp_left_assoc() {
        let rules = vec![
            make_rule("Add", "+", "Int", Associativity::Left),
            make_rule("Sub", "-", "Int", Associativity::Left),
        ];
        let table = analyze_binding_powers(&rules);
        assert_eq!(table.operators.len(), 2);

        for op in &table.operators {
            assert!(
                op.left_bp < op.right_bp,
                "left-assoc operator {} should have left_bp({}) < right_bp({})",
                op.label, op.left_bp, op.right_bp
            );
        }
    }

    #[test]
    fn test_analyze_bp_right_assoc() {
        let rules = vec![
            make_rule("Pow", "^", "Int", Associativity::Right),
            make_rule("Assign", "=", "Int", Associativity::Right),
        ];
        let table = analyze_binding_powers(&rules);
        assert_eq!(table.operators.len(), 2);

        for op in &table.operators {
            assert!(
                op.left_bp > op.right_bp,
                "right-assoc operator {} should have left_bp({}) > right_bp({})",
                op.label, op.left_bp, op.right_bp
            );
        }
    }

    #[test]
    fn test_analyze_bp_precedence_ordering() {
        // Add declared first (lower precedence), Mul declared second (higher precedence)
        let rules = vec![
            make_rule("Add", "+", "Int", Associativity::Left),
            make_rule("Mul", "*", "Int", Associativity::Left),
        ];
        let table = analyze_binding_powers(&rules);

        let add = table.operators.iter().find(|op| op.label == "Add").expect("Add not found");
        let mul = table.operators.iter().find(|op| op.label == "Mul").expect("Mul not found");

        // Mul should have strictly higher binding powers than Add
        assert!(
            mul.left_bp > add.left_bp,
            "Mul.left_bp({}) should be > Add.left_bp({})",
            mul.left_bp, add.left_bp
        );
        assert!(
            mul.right_bp > add.right_bp,
            "Mul.right_bp({}) should be > Add.right_bp({})",
            mul.right_bp, add.right_bp
        );
    }

    #[test]
    fn test_postfix_above_infix() {
        let rules = vec![
            make_rule("Add", "+", "Int", Associativity::Left),
            make_rule("Mul", "*", "Int", Associativity::Left),
            {
                let mut r = make_rule("Fact", "!", "Int", Associativity::Left);
                r.is_postfix = true;
                r
            },
        ];
        let table = analyze_binding_powers(&rules);

        let max_infix_bp = table
            .operators
            .iter()
            .filter(|op| !op.is_postfix)
            .map(|op| op.left_bp.max(op.right_bp))
            .max()
            .expect("should have infix operators");

        let fact = table.operators.iter().find(|op| op.label == "Fact").expect("Fact not found");
        assert!(fact.is_postfix, "Fact should be postfix");
        assert!(
            fact.left_bp > max_infix_bp,
            "postfix left_bp({}) should be > max infix bp({})",
            fact.left_bp, max_infix_bp
        );
    }

    #[test]
    fn test_associativity_method() {
        let left_op = InfixOperator {
            terminal: "+".to_string(),
            category: "Int".to_string(),
            result_category: "Int".to_string(),
            left_bp: 2,
            right_bp: 3,
            label: "Add".to_string(),
            is_cross_category: false,
            is_postfix: false,
            is_mixfix: false,
            mixfix_parts: Vec::new(),
        };
        assert_eq!(left_op.associativity(), Associativity::Left);

        let right_op = InfixOperator {
            terminal: "^".to_string(),
            category: "Int".to_string(),
            result_category: "Int".to_string(),
            left_bp: 3,
            right_bp: 2,
            label: "Pow".to_string(),
            is_cross_category: false,
            is_postfix: false,
            is_mixfix: false,
            mixfix_parts: Vec::new(),
        };
        assert_eq!(right_op.associativity(), Associativity::Right);

        // Equal BP should return Right (left_bp < right_bp is false)
        let equal_op = InfixOperator {
            terminal: "=".to_string(),
            category: "Int".to_string(),
            result_category: "Int".to_string(),
            left_bp: 5,
            right_bp: 5,
            label: "Eq".to_string(),
            is_cross_category: false,
            is_postfix: false,
            is_mixfix: false,
            mixfix_parts: Vec::new(),
        };
        assert_eq!(equal_op.associativity(), Associativity::Right);
    }
}
