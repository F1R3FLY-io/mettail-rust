//! Author-DX demo: render text railroad diagrams for a grammar.
//!
//! OSLF Phase 7a. Builds a small in-memory [`LanguageSpec`] (the same shape the
//! `railroad` module's own unit tests use) and prints the always-on text
//! railroad rendering produced by
//! [`mettail_prattail::railroad::render_grammar_railroad_text`].
//!
//! Run with:
//!
//! ```sh
//! cargo run -p prattail --example railroad
//! ```
//!
//! This example adds no caller to the default parser pipeline; it merely
//! exercises the author-facing diagram entrypoint.

use mettail_prattail::binding_power::Associativity;
use mettail_prattail::railroad::render_grammar_railroad_text;
use mettail_prattail::{
    BeamWidthConfig, CategorySpec, LanguageSpec, LiteralPatterns, RuleSpec, SyntaxItemSpec,
};

/// Build a minimal two-rule `Expr` grammar: integer literals plus `+`.
fn make_simple_spec() -> LanguageSpec {
    LanguageSpec {
        name: "Calc".to_string(),
        types: vec![CategorySpec {
            name: "Expr".to_string(),
            native_type: Some("i32".to_string()),
            is_primary: true,
            has_var: true,
        }],
        rules: vec![
            RuleSpec {
                label: "Lit".to_string(),
                category: "Expr".to_string(),
                syntax: vec![SyntaxItemSpec::Terminal("integer".to_string())],
                is_infix: false,
                associativity: Associativity::Left,
                is_var: false,
                is_literal: true,
                has_binder: false,
                has_multi_binder: false,
                is_collection: false,
                collection_type: None,
                separator: None,
                is_cross_category: false,
                cross_source_category: None,
                is_cast: false,
                cast_source_category: None,
                is_unary_prefix: false,
                prefix_precedence: None,
                is_postfix: false,
                has_rust_code: false,
                rust_code: None,
                eval_mode: None,
                source_location: None,
                is_auto_injected: false,
            },
            RuleSpec {
                label: "Add".to_string(),
                category: "Expr".to_string(),
                syntax: vec![
                    SyntaxItemSpec::NonTerminal {
                        category: "Expr".to_string(),
                        param_name: "a".to_string(),
                    },
                    SyntaxItemSpec::Terminal("+".to_string()),
                    SyntaxItemSpec::NonTerminal {
                        category: "Expr".to_string(),
                        param_name: "b".to_string(),
                    },
                ],
                is_infix: true,
                associativity: Associativity::Left,
                is_var: false,
                is_literal: false,
                has_binder: false,
                has_multi_binder: false,
                is_collection: false,
                collection_type: None,
                separator: None,
                is_cross_category: false,
                cross_source_category: None,
                is_cast: false,
                cast_source_category: None,
                is_unary_prefix: false,
                prefix_precedence: None,
                is_postfix: false,
                has_rust_code: false,
                rust_code: None,
                eval_mode: None,
                source_location: None,
                is_auto_injected: false,
            },
        ],
        beam_width: BeamWidthConfig::Disabled,
        log_semiring_model_path: None,
        literal_patterns: LiteralPatterns::default(),
        recovery_config: mettail_prattail::recovery::RecoveryConfig::default(),
        semantic_dependency_groups: Vec::new(),
        custom_tokens: Vec::new(),
        modes: Vec::new(),
        sync: None,
        tree_invariants: Vec::new(),
        refinement_types: Vec::new(),
        guard_config: None,
    }
}

fn main() {
    let spec = make_simple_spec();
    let diagrams = render_grammar_railroad_text(&spec);

    println!("Railroad diagrams for grammar `{}`:\n", spec.name);
    for (category, diagram) in &diagrams {
        println!("── {category} ──");
        println!("{diagram}\n");
    }
}
