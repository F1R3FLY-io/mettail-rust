//! Language specification builders and precomputed intermediates for benchmarks.
//!
//! Provides 5 realistic language specifications of varying complexity, plus a
//! `PreparedSpec` struct that precomputes all intermediate data structures by
//! replicating the pipeline from `generate_parser()`.

// Each benchmark file compiles this module independently and uses different subsets,
// so dead_code warnings are expected and harmless.
#![allow(dead_code)]

use std::collections::BTreeMap;
#[cfg(feature = "wfst")]
use std::collections::BTreeSet;

use mettail_prattail::automata::minimize::minimize_dfa;
use mettail_prattail::automata::nfa::build_nfa;
use mettail_prattail::automata::partition::{compute_equivalence_classes, AlphabetPartition};
use mettail_prattail::automata::subset::subset_construction;
use mettail_prattail::automata::{Dfa, Nfa, TokenKind};
use mettail_prattail::binding_power::{
    analyze_binding_powers, Associativity, BindingPowerTable, InfixRuleInfo,
};
use mettail_prattail::dispatch::{categories_needing_dispatch, CastRule, CrossCategoryRule};
use mettail_prattail::lexer::{extract_terminals, GrammarRuleInfo, LexerInput, TypeInfo};
use mettail_prattail::prediction::{
    analyze_cross_category_overlaps, build_dispatch_tables, compute_first_sets,
    CrossCategoryOverlap, DispatchTable, FirstItem, FirstSet, RuleInfo,
};
use mettail_prattail::pratt::{PrattConfig, PrefixHandler};
use mettail_prattail::recursive::{write_rd_handler, CollectionKind, RDRuleInfo, RDSyntaxItem};
use mettail_prattail::{BeamWidthConfig, CategorySpec, DispatchStrategy, LanguageSpec, RuleSpec, SyntaxItemSpec};

// proc_macro2::TokenStream no longer needed — all codegen is string-based

// ══════════════════════════════════════════════════════════════════════════════
// RuleSpec builder helpers
// ══════════════════════════════════════════════════════════════════════════════

fn base_rule(label: &str, category: &str, syntax: Vec<SyntaxItemSpec>) -> RuleSpec {
    RuleSpec {
        label: label.to_string(),
        category: category.to_string(),
        syntax,
        is_infix: false,
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
    }
}

fn infix_rule(label: &str, cat: &str, op: &str) -> RuleSpec {
    let mut r = base_rule(
        label,
        cat,
        vec![
            SyntaxItemSpec::NonTerminal {
                category: cat.to_string(),
                param_name: "a".to_string(),
            },
            SyntaxItemSpec::Terminal(op.to_string()),
            SyntaxItemSpec::NonTerminal {
                category: cat.to_string(),
                param_name: "b".to_string(),
            },
        ],
    );
    r.is_infix = true;
    r
}

fn infix_rule_right(label: &str, cat: &str, op: &str) -> RuleSpec {
    let mut r = infix_rule(label, cat, op);
    r.associativity = Associativity::Right;
    r
}

fn var_rule(label: &str, cat: &str) -> RuleSpec {
    let mut r = base_rule(
        label,
        cat,
        vec![SyntaxItemSpec::IdentCapture {
            param_name: "x".to_string(),
        }],
    );
    r.is_var = true;
    r
}

fn literal_rule(label: &str, cat: &str) -> RuleSpec {
    let mut r = base_rule(label, cat, vec![]);
    r.is_literal = true;
    r
}

fn prefix_rule(label: &str, cat: &str, op: &str) -> RuleSpec {
    let mut r = base_rule(
        label,
        cat,
        vec![
            SyntaxItemSpec::Terminal(op.to_string()),
            SyntaxItemSpec::NonTerminal {
                category: cat.to_string(),
                param_name: "a".to_string(),
            },
        ],
    );
    r.is_unary_prefix = true;
    r
}

fn cast_rule(label: &str, target: &str, source: &str) -> RuleSpec {
    let mut r = base_rule(
        label,
        target,
        vec![SyntaxItemSpec::NonTerminal {
            category: source.to_string(),
            param_name: "val".to_string(),
        }],
    );
    r.is_cast = true;
    r.cast_source_category = Some(source.to_string());
    r
}

fn cross_cat_rule(label: &str, result: &str, source: &str, op: &str) -> RuleSpec {
    let mut r = base_rule(
        label,
        result,
        vec![
            SyntaxItemSpec::NonTerminal {
                category: source.to_string(),
                param_name: "a".to_string(),
            },
            SyntaxItemSpec::Terminal(op.to_string()),
            SyntaxItemSpec::NonTerminal {
                category: source.to_string(),
                param_name: "b".to_string(),
            },
        ],
    );
    r.is_infix = true;
    r.is_cross_category = true;
    r.cross_source_category = Some(source.to_string());
    r
}

fn binder_rule(label: &str, cat: &str, kw: &str, binder_cat: &str) -> RuleSpec {
    let mut r = base_rule(
        label,
        cat,
        vec![
            SyntaxItemSpec::Terminal(kw.to_string()),
            SyntaxItemSpec::Binder {
                param_name: "x".to_string(),
                category: binder_cat.to_string(),
                is_multi: false,
            },
            SyntaxItemSpec::Terminal(".".to_string()),
            SyntaxItemSpec::NonTerminal {
                category: cat.to_string(),
                param_name: "body".to_string(),
            },
        ],
    );
    r.has_binder = true;
    r
}

fn collection_rule(
    label: &str,
    cat: &str,
    elem_cat: &str,
    sep: &str,
    kind: CollectionKind,
    open: &str,
    close: &str,
) -> RuleSpec {
    let mut r = base_rule(
        label,
        cat,
        vec![
            SyntaxItemSpec::Terminal(open.to_string()),
            SyntaxItemSpec::Collection {
                param_name: "elems".to_string(),
                element_category: elem_cat.to_string(),
                separator: sep.to_string(),
                kind,
            },
            SyntaxItemSpec::Terminal(close.to_string()),
        ],
    );
    r.is_collection = true;
    r.collection_type = Some(kind);
    r.separator = Some(sep.to_string());
    r
}

// ══════════════════════════════════════════════════════════════════════════════
// Spec constructors
// ══════════════════════════════════════════════════════════════════════════════

/// Minimal language (~Lambda calculus): 1 category, 3 rules.
pub fn minimal_spec() -> LanguageSpec {
    LanguageSpec {
        name: "Lambda".to_string(),
        types: vec![CategorySpec {
            name: "Term".to_string(),
            native_type: None,
            is_primary: true,
        }],
        rules: vec![
            var_rule("TVar", "Term"),
            binder_rule("Lam", "Term", "lam", "Term"),
            // Application: Term Term (implicit infix via juxtaposition,
            // but for simplicity we model it as a prefix rule with parens)
            base_rule(
                "App",
                "Term",
                vec![
                    SyntaxItemSpec::Terminal("@".to_string()),
                    SyntaxItemSpec::NonTerminal {
                        category: "Term".to_string(),
                        param_name: "func".to_string(),
                    },
                    SyntaxItemSpec::NonTerminal {
                        category: "Term".to_string(),
                        param_name: "arg".to_string(),
                    },
                ],
            ),
        ],
        beam_width: BeamWidthConfig::Disabled,
        log_semiring_model_path: None,
        dispatch_strategy: DispatchStrategy::Static,
    }
}

/// Small language (~Calculator): 3 categories, 12 rules.
pub fn small_spec() -> LanguageSpec {
    LanguageSpec {
        name: "Calculator".to_string(),
        types: vec![
            CategorySpec {
                name: "Int".to_string(),
                native_type: Some("i64".to_string()),
                is_primary: true,
            },
            CategorySpec {
                name: "Bool".to_string(),
                native_type: Some("bool".to_string()),
                is_primary: false,
            },
            CategorySpec {
                name: "Str".to_string(),
                native_type: Some("String".to_string()),
                is_primary: false,
            },
        ],
        rules: vec![
            // Int rules
            var_rule("IVar", "Int"),
            literal_rule("NumLit", "Int"),
            infix_rule("Add", "Int", "+"),
            infix_rule("Sub", "Int", "-"),
            infix_rule("Mul", "Int", "*"),
            infix_rule("Div", "Int", "/"),
            infix_rule_right("Pow", "Int", "^"),
            prefix_rule("Neg", "Int", "-"),
            // Bool rules
            var_rule("BVar", "Bool"),
            literal_rule("BoolLit", "Bool"),
            cross_cat_rule("Eq", "Bool", "Int", "=="),
            // Str rules
            var_rule("SVar", "Str"),
            literal_rule("StringLit", "Str"),
        ],
        beam_width: BeamWidthConfig::Disabled,
        log_semiring_model_path: None,
        dispatch_strategy: DispatchStrategy::Static,
    }
}

/// Medium language (~Ambient calculus): 2 categories, 7 rules.
pub fn medium_spec() -> LanguageSpec {
    LanguageSpec {
        name: "Ambient".to_string(),
        types: vec![
            CategorySpec {
                name: "Proc".to_string(),
                native_type: None,
                is_primary: true,
            },
            CategorySpec {
                name: "Name".to_string(),
                native_type: None,
                is_primary: false,
            },
        ],
        rules: vec![
            // Proc rules
            var_rule("PVar", "Proc"),
            base_rule(
                "PZero",
                "Proc",
                vec![SyntaxItemSpec::Terminal("0".to_string())],
            ),
            infix_rule("PPar", "Proc", "|"),
            binder_rule("PNew", "Proc", "new", "Name"),
            collection_rule("PBag", "Proc", "Proc", "|", CollectionKind::HashBag, "{", "}"),
            // Name rules
            var_rule("NVar", "Name"),
            base_rule(
                "NIn",
                "Name",
                vec![
                    SyntaxItemSpec::Terminal("in".to_string()),
                    SyntaxItemSpec::NonTerminal {
                        category: "Name".to_string(),
                        param_name: "n".to_string(),
                    },
                ],
            ),
        ],
        beam_width: BeamWidthConfig::Disabled,
        log_semiring_model_path: None,
        dispatch_strategy: DispatchStrategy::Static,
    }
}

/// Complex language (~RhoCalc): 3 categories, 10 rules.
pub fn complex_spec() -> LanguageSpec {
    LanguageSpec {
        name: "RhoCalc".to_string(),
        types: vec![
            CategorySpec {
                name: "Proc".to_string(),
                native_type: None,
                is_primary: true,
            },
            CategorySpec {
                name: "Name".to_string(),
                native_type: None,
                is_primary: false,
            },
            CategorySpec {
                name: "Int".to_string(),
                native_type: Some("i64".to_string()),
                is_primary: false,
            },
        ],
        rules: vec![
            // Proc rules
            var_rule("PVar", "Proc"),
            base_rule(
                "PZero",
                "Proc",
                vec![SyntaxItemSpec::Terminal("Nil".to_string())],
            ),
            infix_rule("PPar", "Proc", "|"),
            binder_rule("PNew", "Proc", "new", "Name"),
            cast_rule("PCastInt", "Proc", "Int"),
            // Name rules
            var_rule("NVar", "Name"),
            base_rule(
                "NQuote",
                "Name",
                vec![
                    SyntaxItemSpec::Terminal("@".to_string()),
                    SyntaxItemSpec::NonTerminal {
                        category: "Proc".to_string(),
                        param_name: "p".to_string(),
                    },
                ],
            ),
            // Int rules
            var_rule("IVar", "Int"),
            literal_rule("NumLit", "Int"),
            infix_rule("Add", "Int", "+"),
        ],
        beam_width: BeamWidthConfig::Disabled,
        log_semiring_model_path: None,
        dispatch_strategy: DispatchStrategy::Static,
    }
}

/// Synthetic language for scaling tests: 1 category, 3+N rules.
///
/// Creates a language with `n_ops` infix operators using distinct single-character
/// terminals. The base 3 rules are: Var, NumLit, and a prefix "~" operator.
pub fn synthetic_spec(n_ops: usize) -> LanguageSpec {
    // Generate distinct operator terminals: !, @, #, $, %, ^, &, *, +, -, =, <, >, ?, ~, ...
    // We use printable ASCII characters that are not alphanumeric or structural delimiters.
    let op_chars: Vec<char> = "!@#$%^&*+-=<>?~`\\|;:'"
        .chars()
        .cycle()
        .enumerate()
        .map(|(i, c)| {
            if i < 22 {
                c
            } else {
                // For overflow, create multi-char operators
                c
            }
        })
        .take(n_ops)
        .collect();

    let mut rules: Vec<RuleSpec> = Vec::with_capacity(3 + n_ops);
    rules.push(var_rule("EVar", "Expr"));
    rules.push(literal_rule("NumLit", "Expr"));
    rules.push(prefix_rule("Neg", "Expr", "~"));

    for (i, &ch) in op_chars.iter().enumerate() {
        let label = format!("Op{}", i);
        let op = if i < 22 {
            ch.to_string()
        } else {
            // Multi-char operators for large N
            format!("{}{}", ch, i)
        };
        rules.push(infix_rule(&label, "Expr", &op));
    }

    LanguageSpec {
        name: "Synthetic".to_string(),
        types: vec![CategorySpec {
            name: "Expr".to_string(),
            native_type: Some("i64".to_string()),
            is_primary: true,
        }],
        rules,
        beam_width: BeamWidthConfig::Disabled,
        log_semiring_model_path: None,
        dispatch_strategy: DispatchStrategy::Static,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// PreparedSpec — precomputed intermediates for per-phase benchmarking
// ══════════════════════════════════════════════════════════════════════════════

/// Precomputed intermediates from the parser generation pipeline.
///
/// Mirrors the logic of `generate_parser()` in `lib.rs:218-594`, capturing
/// every intermediate data structure so individual phases can be benchmarked
/// without including setup overhead.
pub struct PreparedSpec {
    pub spec: LanguageSpec,

    // Phase 1: Terminal extraction
    pub grammar_rules: Vec<GrammarRuleInfo>,
    pub type_infos: Vec<TypeInfo>,
    pub lexer_input: LexerInput,

    // Phase 1b: Automata pipeline
    pub nfa: Nfa,
    pub partition: AlphabetPartition,
    pub dfa: Dfa,
    pub min_dfa: Dfa,
    pub token_kinds: Vec<TokenKind>,

    // Phase 2: Binding power analysis
    pub infix_rules: Vec<InfixRuleInfo>,
    pub bp_table: BindingPowerTable,

    // Phase 3: FIRST sets and prediction
    pub categories: Vec<String>,
    pub rule_infos: Vec<RuleInfo>,
    pub first_sets: BTreeMap<String, FirstSet>,
    pub dispatch_tables: BTreeMap<String, DispatchTable>,
    pub overlaps: BTreeMap<(String, String), CrossCategoryOverlap>,
    pub max_infix_bp: BTreeMap<String, u8>,

    // Phase 4: RD handlers
    pub rd_rules: Vec<RDRuleInfo>,
    pub prefix_handlers: Vec<PrefixHandler>,

    // Phase 5: Cross-category and cast rules
    pub cross_rules: Vec<CrossCategoryRule>,
    pub cast_rules: Vec<CastRule>,
    pub dispatch_categories: Vec<String>,

    // Phase 5b: Pratt configs per category
    pub pratt_configs: Vec<PrattPerCategory>,
}

/// Per-category Pratt parser configuration and precomputed data.
pub struct PrattPerCategory {
    pub category: String,
    pub config: PrattConfig,
    pub handlers: Vec<PrefixHandler>,
}

/// Recursively collect all terminal strings from syntax items.
fn collect_terminals_recursive(items: &[SyntaxItemSpec]) -> Vec<String> {
    let mut terminals = Vec::new();
    for item in items {
        match item {
            SyntaxItemSpec::Terminal(t) => terminals.push(t.clone()),
            SyntaxItemSpec::Collection { separator, .. } => {
                terminals.push(separator.clone());
            }
            SyntaxItemSpec::ZipMapSep {
                body_items,
                separator,
                ..
            } => {
                terminals.extend(collect_terminals_recursive(body_items));
                terminals.push(separator.clone());
            }
            SyntaxItemSpec::Optional { inner } => {
                terminals.extend(collect_terminals_recursive(inner));
            }
            _ => {}
        }
    }
    terminals.sort();
    terminals.dedup();
    terminals
}

/// Convert a `SyntaxItemSpec` to an `RDSyntaxItem`.
fn convert_syntax_item_to_rd(item: &SyntaxItemSpec) -> RDSyntaxItem {
    match item {
        SyntaxItemSpec::Terminal(t) => RDSyntaxItem::Terminal(t.clone()),
        SyntaxItemSpec::NonTerminal {
            category,
            param_name,
        } => RDSyntaxItem::NonTerminal {
            category: category.clone(),
            param_name: param_name.clone(),
        },
        SyntaxItemSpec::IdentCapture { param_name } => RDSyntaxItem::IdentCapture {
            param_name: param_name.clone(),
        },
        SyntaxItemSpec::Binder {
            param_name,
            category,
            ..
        } => RDSyntaxItem::Binder {
            param_name: param_name.clone(),
            binder_category: category.clone(),
        },
        SyntaxItemSpec::Collection {
            param_name,
            element_category,
            separator,
            kind,
        } => RDSyntaxItem::Collection {
            param_name: param_name.clone(),
            element_category: element_category.clone(),
            separator: separator.clone(),
            kind: *kind,
        },
        SyntaxItemSpec::ZipMapSep {
            left_name,
            right_name,
            left_category,
            right_category,
            body_items,
            separator,
        } => RDSyntaxItem::ZipMapSep {
            left_name: left_name.clone(),
            right_name: right_name.clone(),
            left_category: left_category.clone(),
            right_category: right_category.clone(),
            body_items: body_items.iter().map(convert_syntax_item_to_rd).collect(),
            separator: separator.clone(),
        },
        SyntaxItemSpec::Optional { inner } => RDSyntaxItem::Optional {
            inner: inner.iter().map(convert_syntax_item_to_rd).collect(),
        },
    }
}

/// Run the full parser generation pipeline, capturing all intermediates.
///
/// Mirrors `generate_parser()` (lib.rs:218-594) but stores every intermediate
/// data structure for benchmarking individual phases.
pub fn prepare(spec: &LanguageSpec) -> PreparedSpec {
    // ── Phase 1: Extract terminals ──

    let grammar_rules: Vec<GrammarRuleInfo> = spec
        .rules
        .iter()
        .map(|r| GrammarRuleInfo {
            label: r.label.clone(),
            category: r.category.clone(),
            terminals: collect_terminals_recursive(&r.syntax),
            is_infix: r.is_infix,
        })
        .collect();

    let type_infos: Vec<TypeInfo> = spec
        .types
        .iter()
        .map(|t| TypeInfo {
            name: t.name.clone(),
            language_name: spec.name.clone(),
            native_type_name: t.native_type.clone(),
        })
        .collect();

    let has_binders = spec.rules.iter().any(|r| r.has_binder || r.has_multi_binder);
    let category_names: Vec<String> = spec.types.iter().map(|t| t.name.clone()).collect();
    let lexer_input = extract_terminals(&grammar_rules, &type_infos, has_binders, &category_names);

    // ── Phase 1b: Automata pipeline ──

    let nfa = build_nfa(&lexer_input.terminals, &lexer_input.needs);
    let partition = compute_equivalence_classes(&nfa);
    let dfa = subset_construction(&nfa, &partition);
    let min_dfa = minimize_dfa(&dfa);

    let mut token_kinds: Vec<TokenKind> = Vec::new();
    token_kinds.push(TokenKind::Eof);
    if lexer_input.needs.ident {
        token_kinds.push(TokenKind::Ident);
    }
    if lexer_input.needs.integer {
        token_kinds.push(TokenKind::Integer);
    }
    if lexer_input.needs.float {
        token_kinds.push(TokenKind::Float);
    }
    if lexer_input.needs.boolean {
        token_kinds.push(TokenKind::True);
        token_kinds.push(TokenKind::False);
    }
    if lexer_input.needs.string_lit {
        token_kinds.push(TokenKind::StringLit);
    }
    for terminal in &lexer_input.terminals {
        token_kinds.push(terminal.kind.clone());
    }

    // ── Phase 2: Binding power analysis ──

    let infix_rules: Vec<InfixRuleInfo> = spec
        .rules
        .iter()
        .filter(|r| r.is_infix)
        .map(|r| InfixRuleInfo {
            label: r.label.clone(),
            terminal: r
                .syntax
                .iter()
                .find_map(|item| {
                    if let SyntaxItemSpec::Terminal(t) = item {
                        Some(t.clone())
                    } else {
                        None
                    }
                })
                .unwrap_or_default(),
            category: r.category.clone(),
            result_category: r.category.clone(),
            associativity: r.associativity,
            is_cross_category: r.is_cross_category,
            is_postfix: r.is_postfix,
            is_mixfix: false,
            mixfix_parts: Vec::new(),
        })
        .collect();

    let bp_table = analyze_binding_powers(&infix_rules);

    // ── Phase 3: FIRST sets and prediction ──

    let categories: Vec<String> = spec.types.iter().map(|t| t.name.clone()).collect();

    let rule_infos: Vec<RuleInfo> = spec
        .rules
        .iter()
        .map(|r| RuleInfo {
            label: r.label.clone(),
            category: r.category.clone(),
            first_items: r
                .syntax
                .iter()
                .take(1)
                .map(|item| match item {
                    SyntaxItemSpec::Terminal(t) => FirstItem::Terminal(t.clone()),
                    SyntaxItemSpec::NonTerminal { category, .. } => {
                        if categories.contains(category) {
                            FirstItem::NonTerminal(category.clone())
                        } else {
                            FirstItem::Ident
                        }
                    }
                    SyntaxItemSpec::IdentCapture { .. } => FirstItem::Ident,
                    SyntaxItemSpec::Binder { .. } => FirstItem::Ident,
                    SyntaxItemSpec::Collection { .. } => FirstItem::Ident,
                    SyntaxItemSpec::ZipMapSep { .. } => FirstItem::Ident,
                    SyntaxItemSpec::Optional { .. } => FirstItem::Ident,
                })
                .collect(),
            is_infix: r.is_infix,
            is_var: r.is_var,
            is_literal: r.is_literal,
            is_cross_category: r.is_cross_category,
            is_cast: r.is_cast,
        })
        .collect();

    let mut first_sets = compute_first_sets(&rule_infos, &categories);

    // Augment FIRST sets with native literal tokens
    for cat_spec in &spec.types {
        if let Some(ref native_type) = cat_spec.native_type {
            if let Some(first_set) = first_sets.get_mut(&cat_spec.name) {
                match native_type.as_str() {
                    "i32" | "i64" | "u32" | "u64" | "isize" | "usize" => {
                        first_set.insert("Integer");
                    }
                    "f32" | "f64" => {
                        first_set.insert("Float");
                    }
                    "bool" => {
                        first_set.insert("Boolean");
                    }
                    "str" | "String" => {
                        first_set.insert("StringLit");
                    }
                    _ => {}
                }
            }
        }
    }

    let dispatch_tables = build_dispatch_tables(&rule_infos, &categories, &first_sets);
    let overlaps = analyze_cross_category_overlaps(&categories, &first_sets);

    // Phase 3b: Max infix bp per category
    let max_infix_bp: BTreeMap<String, u8> = {
        let mut map = BTreeMap::new();
        for op in &bp_table.operators {
            let max = map.entry(op.category.clone()).or_insert(0u8);
            *max = (*max).max(op.left_bp).max(op.right_bp);
        }
        map
    };

    // ── Phase 4: Generate RD handlers ──

    let mut rd_rules: Vec<RDRuleInfo> = Vec::new();
    let mut prefix_handlers: Vec<PrefixHandler> = Vec::new();
    let mut rd_buf = String::with_capacity(4096);

    for rule in &spec.rules {
        if rule.is_infix || rule.is_var || rule.is_literal {
            continue;
        }

        let prefix_bp = if rule.is_unary_prefix {
            let cat_max = max_infix_bp.get(&rule.category).copied().unwrap_or(0);
            Some(cat_max + 2)
        } else {
            None
        };

        let rd_rule = RDRuleInfo {
            label: rule.label.clone(),
            category: rule.category.clone(),
            items: rule.syntax.iter().map(convert_syntax_item_to_rd).collect(),
            has_binder: rule.has_binder,
            has_multi_binder: rule.has_multi_binder,
            is_collection: rule.is_collection,
            collection_type: rule.collection_type,
            separator: rule.separator.clone(),
            prefix_bp,
            eval_mode: rule.eval_mode.clone(),
        };

        let handler = write_rd_handler(&mut rd_buf, &rd_rule);
        rd_rules.push(rd_rule);
        prefix_handlers.push(handler);
    }

    // ── Phase 5a: Extract cross-category and cast rules ──

    let cross_rules: Vec<CrossCategoryRule> = spec
        .rules
        .iter()
        .filter(|r| r.is_cross_category)
        .map(|r| CrossCategoryRule {
            label: r.label.clone(),
            source_category: r.cross_source_category.clone().unwrap_or_default(),
            result_category: r.category.clone(),
            operator: r
                .syntax
                .iter()
                .find_map(|item| {
                    if let SyntaxItemSpec::Terminal(t) = item {
                        Some(t.clone())
                    } else {
                        None
                    }
                })
                .unwrap_or_default(),
            needs_backtrack: false,
        })
        .collect();

    let cast_rules_vec: Vec<CastRule> = spec
        .rules
        .iter()
        .filter(|r| r.is_cast)
        .map(|r| CastRule {
            label: r.label.clone(),
            source_category: r.cast_source_category.clone().unwrap_or_default(),
            target_category: r.category.clone(),
        })
        .collect();

    let dispatch_categories = categories_needing_dispatch(&cross_rules, &cast_rules_vec);

    // ── Phase 5b: Pratt configs per category ──

    let mut pratt_configs: Vec<PrattPerCategory> = Vec::with_capacity(categories.len());

    for (idx, cat) in categories.iter().enumerate() {
        let has_infix = !bp_table.operators_for_category(cat).is_empty();
        let needs_dispatch = dispatch_categories.contains(cat);

        let native_type = spec
            .types
            .iter()
            .find(|t| t.name == *cat)
            .and_then(|t| t.native_type.clone());

        let cat_cast_rules: Vec<CastRule> = cast_rules_vec
            .iter()
            .filter(|r| r.target_category == *cat)
            .cloned()
            .collect();

        let own_first = first_sets.get(cat).cloned().unwrap_or_default();

        let has_postfix = !bp_table.postfix_operators_for_category(cat).is_empty();

        let config = PrattConfig {
            category: cat.clone(),
            is_primary: idx == 0,
            has_infix,
            has_postfix,
            has_mixfix: false,
            all_categories: categories.clone(),
            needs_dispatch,
            native_type,
            cast_rules: cat_cast_rules,
            own_first_set: own_first,
            all_first_sets: first_sets.clone(),
            follow_set: mettail_prattail::prediction::FirstSet::new(),
        };

        let cat_handlers: Vec<PrefixHandler> = prefix_handlers
            .iter()
            .filter(|h| h.category == *cat)
            .cloned()
            .collect();

        pratt_configs.push(PrattPerCategory {
            category: cat.clone(),
            config,
            handlers: cat_handlers,
        });
    }

    PreparedSpec {
        spec: spec.clone(),
        grammar_rules,
        type_infos,
        lexer_input,
        nfa,
        partition,
        dfa,
        min_dfa,
        token_kinds,
        infix_rules,
        bp_table,
        categories,
        rule_infos,
        first_sets,
        dispatch_tables,
        overlaps,
        max_infix_bp,
        rd_rules,
        prefix_handlers,
        cross_rules,
        cast_rules: cast_rules_vec,
        dispatch_categories,
        pratt_configs,
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// WFST helpers (feature = "wfst")
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(feature = "wfst")]
use mettail_prattail::automata::semiring::TropicalWeight;
#[cfg(feature = "wfst")]
use mettail_prattail::lattice::TokenLattice;
#[cfg(feature = "wfst")]
use mettail_prattail::recovery::RecoveryWfst;
#[cfg(feature = "wfst")]
use mettail_prattail::token_id::{TokenId, TokenIdMap};
#[cfg(feature = "wfst")]
use mettail_prattail::wfst::{PredictionWfst, PredictionWfstBuilder};

#[cfg(feature = "wfst-log")]
use mettail_prattail::automata::semiring::{LogWeight, Semiring};

/// Precomputed WFST data structures built from a `PreparedSpec`.
#[cfg(feature = "wfst")]
pub struct WfstPreparedSpec {
    pub base: PreparedSpec,
    pub token_id_map: TokenIdMap,
    pub prediction_wfsts: BTreeMap<String, PredictionWfst>,
    pub recovery_wfsts: Vec<RecoveryWfst>,
    pub sample_token_names: Vec<String>,
}

/// Build WFST intermediates from a `PreparedSpec`.
///
/// Constructs TokenIdMap, PredictionWfst per category, RecoveryWfst per category,
/// and collects sample token names for prediction benchmarks.
#[cfg(feature = "wfst")]
pub fn prepare_wfst(spec: &LanguageSpec) -> WfstPreparedSpec {
    let base = prepare(spec);

    // ── TokenIdMap from token_kinds ──
    let token_names: Vec<String> = base
        .token_kinds
        .iter()
        .map(|kind| match kind {
            TokenKind::Eof => "Eof".to_string(),
            TokenKind::Ident => "Ident".to_string(),
            TokenKind::Integer => "Integer".to_string(),
            TokenKind::Float => "Float".to_string(),
            TokenKind::True => "True".to_string(),
            TokenKind::False => "False".to_string(),
            TokenKind::StringLit => "StringLit".to_string(),
            TokenKind::Fixed(s) => {
                mettail_prattail::automata::codegen::terminal_to_variant_name(s)
            }
            TokenKind::Dollar => "Dollar".to_string(),
            TokenKind::DoubleDollar => "DoubleDollar".to_string(),
        })
        .collect();

    let token_id_map = TokenIdMap::from_names(token_names.iter().cloned());

    // ── PredictionWfst per category ──
    // Build dispatch actions from dispatch_tables, then wrap with WFST builder
    let mut prediction_wfsts = BTreeMap::new();
    for (cat, dt) in &base.dispatch_tables {
        let mut builder = PredictionWfstBuilder::new(cat, token_id_map.clone());

        // Add entries from the dispatch table with declaration-order priority
        for (i, (token_name, action)) in dt.entries.iter().enumerate() {
            let weight = TropicalWeight::from_priority(i as u8);
            builder.add_action(token_name, action.clone(), weight);
        }

        // Add default/variable action with lowest priority
        if let Some(ref default_action) = dt.default_action {
            let weight = TropicalWeight::from_priority((dt.entries.len()) as u8);
            builder.add_action("Ident", default_action.clone(), weight);
        }

        prediction_wfsts.insert(cat.clone(), builder.build());
    }

    // ── RecoveryWfst per category ──
    // Sync tokens: structural delimiters that exist in the grammar + "Eof"
    let structural = ["(", ")", "{", "}", "[", "]", ","];
    let grammar_terminals: BTreeSet<String> = base
        .lexer_input
        .terminals
        .iter()
        .map(|t| match &t.kind {
            TokenKind::Fixed(s) => s.clone(),
            _ => String::new(),
        })
        .filter(|s| !s.is_empty())
        .collect();

    let mut recovery_wfsts = Vec::with_capacity(base.categories.len());
    for cat in &base.categories {
        let mut sync_names: Vec<String> = Vec::new();
        sync_names.push("Eof".to_string());
        for delim in &structural {
            if grammar_terminals.contains(*delim) {
                sync_names.push(
                    mettail_prattail::automata::codegen::terminal_to_variant_name(delim),
                );
            }
        }
        // Also add FOLLOW set tokens if available in first_sets for related categories
        if let Some(first_set) = base.first_sets.get(cat) {
            for token in &first_set.tokens {
                if !sync_names.contains(token) {
                    sync_names.push(token.clone());
                }
            }
        }
        recovery_wfsts.push(RecoveryWfst::new(
            cat.clone(),
            &sync_names,
            &token_id_map,
        ));
    }

    // ── Sample token names for prediction benchmarks ──
    let sample_token_names: Vec<String> = token_names
        .iter()
        .filter(|n| *n != "Eof")
        .take(5)
        .cloned()
        .collect();

    WfstPreparedSpec {
        base,
        token_id_map,
        prediction_wfsts,
        recovery_wfsts,
        sample_token_names,
    }
}

/// Build a synthetic token lattice DAG.
///
/// Creates a DAG with `n_nodes` nodes, each with up to `edges_per_node` forward
/// edges. Weights are deterministic (derived from node/edge indices) to ensure
/// reproducible benchmarks. Returns `(lattice, final_node_index)`.
#[cfg(feature = "wfst")]
pub fn build_synthetic_lattice(
    n_nodes: usize,
    edges_per_node: usize,
) -> (TokenLattice<String, (usize, usize)>, usize) {
    let mut lattice = TokenLattice::with_capacity(n_nodes);
    lattice.ensure_nodes(n_nodes);

    for from in 0..n_nodes.saturating_sub(1) {
        let max_target = n_nodes.min(from + edges_per_node + 1);
        for to in (from + 1)..max_target {
            // Deterministic weight: combine source and target for variety
            let w = ((from * 7 + to * 13) % 100) as f64 / 10.0;
            let token = format!("tok_{}_{}", from, to);
            let span = (from, to);
            lattice.add_edge(from, to, token, span, TropicalWeight::new(w));
        }
    }

    let final_node = n_nodes - 1;
    (lattice, final_node)
}

/// Build a synthetic DAG as adjacency list for forward-backward benchmarks.
///
/// Returns `edges[node] = [(target, weight), ...]` with `n_nodes` nodes.
/// Weight values are deterministic, derived from node/edge indices.
#[cfg(feature = "wfst-log")]
pub fn build_synthetic_dag<W: Semiring>(
    n_nodes: usize,
    edges_per_node: usize,
    weight_fn: fn(usize, usize) -> W,
) -> Vec<Vec<(usize, W)>> {
    let mut edges: Vec<Vec<(usize, W)>> = Vec::with_capacity(n_nodes);
    for _ in 0..n_nodes {
        edges.push(Vec::new());
    }

    for from in 0..n_nodes.saturating_sub(1) {
        let max_target = n_nodes.min(from + edges_per_node + 1);
        let cap = max_target.saturating_sub(from + 1);
        edges[from] = Vec::with_capacity(cap);
        for to in (from + 1)..max_target {
            edges[from].push((to, weight_fn(from, to)));
        }
    }

    edges
}

/// Deterministic TropicalWeight from node indices.
#[cfg(feature = "wfst")]
pub fn tropical_weight_fn(from: usize, to: usize) -> TropicalWeight {
    TropicalWeight::new(((from * 7 + to * 13) % 100) as f64 / 10.0)
}

/// Deterministic LogWeight from node indices.
#[cfg(feature = "wfst-log")]
pub fn log_weight_fn(from: usize, to: usize) -> LogWeight {
    // Avoid zero/negative values: use a positive range [0.1, 10.1]
    LogWeight::new(((from * 7 + to * 13) % 100) as f64 / 10.0 + 0.1)
}

/// Build a sample token ID sequence for recovery benchmarks.
///
/// Creates a deterministic sequence of `len` token IDs from the given map.
#[cfg(feature = "wfst")]
pub fn build_sample_token_ids(map: &TokenIdMap, len: usize) -> Vec<TokenId> {
    let all_ids: Vec<TokenId> = map.iter().map(|(_, id)| id).collect();
    if all_ids.is_empty() {
        return vec![0; len];
    }
    (0..len).map(|i| all_ids[i % all_ids.len()]).collect()
}
