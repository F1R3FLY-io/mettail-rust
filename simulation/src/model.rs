//! Model-Based Testing
//!
//! Derives a state machine from language metadata for property-based testing.
//! The `LanguageStateMachine` captures the language's categories, rewrite rules,
//! and equations as a testable model. Combined with proptest strategies, this
//! enables exhaustive exploration of operation sequences.
//!
//! ## Architecture
//!
//! ```text
//! LanguageMetadata  (including guards { } metadata when declared)
//!       │
//!       ▼
//! LanguageStateMachine::from_metadata()
//!       │
//!       ├── categories (type names)
//!       ├── rewrite_rules (ModelRewriteRule, is_guarded)
//!       ├── equations (ModelEquation, is_guarded)
//!       ├── builtin_predicates (ModelBuiltinPredicate)
//!       ├── theories (ModelTheory)
//!       ├── channels (ModelChannel)
//!       ├── join_patterns (ModelJoinPattern)
//!       └── connectives (ModelConnective)
//!             │
//!             ▼
//!       arb_model_ops() ──→ BoxedStrategy<Vec<ModelOp>>
//! ```
//!
//! ## Guard configuration ingestion (Sim-C)
//!
//! When a language declares a `guards { }` block, the macro emits guard
//! metadata via the `LanguageMetadata` trait (see `mettail_runtime::
//! metadata`). `LanguageStateMachine::from_metadata` reads every method,
//! so that simulator users can introspect declared theories, channels,
//! join patterns, built-in predicates, and connectives. Languages
//! without a `guards { }` block produce empty vectors for these fields
//! — the ingestion is fully backward compatible.

use mettail_runtime::LanguageMetadata;
use proptest::prelude::*;

/// A state machine derived from a language's metadata.
///
/// Captures the language's type categories, rewrite rules, and equations
/// as a testable model structure. This does not execute any language code;
/// it provides a static description of the language's operational semantics
/// suitable for model-based test generation.
pub struct LanguageStateMachine {
    /// Type category names (e.g., "Proc", "Name", "Int").
    pub categories: Vec<String>,
    /// All rewrite rules from the language definition.
    pub rewrite_rules: Vec<ModelRewriteRule>,
    /// All equations (axioms) from the language definition.
    pub equations: Vec<ModelEquation>,

    // ── Sim-C: Guard configuration (design doc §2A) ─────────────────────
    /// Built-in predicate declarations from `guards { }` (direct items).
    /// Empty when the language has no `guards { }` block.
    pub builtin_predicates: Vec<ModelBuiltinPredicate>,
    /// Constraint theory registrations from `guards { theories { } }`.
    /// Empty when no theories are registered.
    pub theories: Vec<ModelTheory>,
    /// Channel category declarations from `guards { channels { } }`.
    /// Empty when no `channels { }` sub-block is declared.
    pub channels: Vec<ModelChannel>,
    /// Join pattern declarations from `guards { channels { join … } }`.
    /// Empty when no join patterns are declared.
    pub join_patterns: Vec<ModelJoinPattern>,
    /// Logical connective declarations from `guards { connectives { } }`.
    /// Empty when no `connectives { }` sub-block is declared.
    pub connectives: Vec<ModelConnective>,
}

/// A rewrite rule extracted from language metadata.
#[derive(Debug, Clone)]
pub struct ModelRewriteRule {
    /// Optional rule name (e.g., "Comm", "Exec").
    pub name: Option<String>,
    /// Left-hand side display string.
    pub lhs_display: String,
    /// Right-hand side display string.
    pub rhs_display: String,
    /// Whether this is a congruence rule (has a premise S ~> T).
    pub is_congruence: bool,
    /// Whether this rule has a `BehavioralGuard` premise. Sim-C: set
    /// by the macro codegen when the rewrite's premise list contains
    /// a `Premise::BehavioralGuard(...)`. The `GuardSatisfaction`
    /// invariant uses this flag to identify guarded rewrites at runtime.
    pub is_guarded: bool,
}

/// An equation (axiom) extracted from language metadata.
#[derive(Debug, Clone)]
pub struct ModelEquation {
    /// Left-hand side display string.
    pub lhs_display: String,
    /// Right-hand side display string.
    pub rhs_display: String,
    /// Whether this equation has freshness/relation conditions.
    pub has_conditions: bool,
    /// Whether this equation has a `BehavioralGuard` premise (Sim-C).
    pub is_guarded: bool,
}

// ═════════════════════════════════════════════════════════════════════════
// Sim-C: Guard-configuration model types
// ═════════════════════════════════════════════════════════════════════════

/// A built-in predicate from `guards { }`.
///
/// Mirrors `mettail_runtime::BuiltinPredicateDef` but owns its strings
/// so the model can be passed around without lifetime parameters.
#[derive(Debug, Clone)]
pub struct ModelBuiltinPredicate {
    /// Predicate's canonical name (e.g., `"eq"`, `"gt"`, `"fresh"`).
    pub name: String,
    /// First surface-syntax form, rendered as a string.
    pub syntax: String,
    /// Optional `@[selectivity(s)]` annotation value.
    pub selectivity: Option<f64>,
    /// Optional `@[cost(c)]` annotation value.
    pub cost: Option<u32>,
}

/// A constraint-theory registration from `guards { theories { } }`.
#[derive(Debug, Clone)]
pub struct ModelTheory {
    /// Local registration name (e.g., `"arithmetic"`).
    pub name: String,
    /// Stringified Rust theory type (e.g., `"PresburgerAlgebra"`).
    pub theory_type: String,
    /// Grammar categories the theory handles; empty when the
    /// `for [...]` clause was omitted (meaning "all").
    pub handled_types: Vec<String>,
}

/// A channel category declaration.
#[derive(Debug, Clone)]
pub struct ModelChannel {
    /// The grammar category serving as a channel.
    pub category: String,
}

/// A join pattern declaration: a constructor with multiple
/// channel-binding parameters.
#[derive(Debug, Clone)]
pub struct ModelJoinPattern {
    /// The constructor label.
    pub label: String,
    /// The channel categories of the constructor's channel-binding
    /// parameters, in declaration order.
    pub channel_categories: Vec<String>,
}

/// A logical connective declaration from `guards { connectives { } }`.
#[derive(Debug, Clone)]
pub struct ModelConnective {
    /// Role identifier (`"and"`, `"or"`, `"not"`, `"entails"`,
    /// `"implied_by"`, `"iff"`, `"forall"`, `"exists"`).
    pub role: String,
    /// Surface keywords that spell this connective.
    pub keywords: Vec<String>,
}

impl LanguageStateMachine {
    /// Construct a state machine model from language metadata.
    ///
    /// Extracts type categories, rewrite rules, equations, and the full
    /// guard configuration (theories, channels, join patterns, built-in
    /// predicates, connectives) from the metadata, converting them into
    /// the model representation.
    ///
    /// Languages without a `guards { }` block produce empty vectors for
    /// the guard-related fields — this is fully backward compatible with
    /// every existing `LanguageMetadata` impl.
    pub fn from_metadata(metadata: &dyn LanguageMetadata) -> Self {
        let categories: Vec<String> = metadata
            .types()
            .iter()
            .map(|t| t.name.to_string())
            .collect();

        let rewrite_rules: Vec<ModelRewriteRule> = metadata
            .rewrites()
            .iter()
            .map(|rw| ModelRewriteRule {
                name: rw.name.map(|s| s.to_string()),
                lhs_display: rw.lhs.to_string(),
                rhs_display: rw.rhs.to_string(),
                is_congruence: rw.is_congruence(),
                is_guarded: rw.is_guarded,
            })
            .collect();

        let equations: Vec<ModelEquation> = metadata
            .equations()
            .iter()
            .map(|eq| ModelEquation {
                lhs_display: eq.lhs.to_string(),
                rhs_display: eq.rhs.to_string(),
                has_conditions: !eq.conditions.is_empty(),
                is_guarded: eq.is_guarded,
            })
            .collect();

        // ── Sim-C: ingest guard configuration metadata ──
        let builtin_predicates: Vec<ModelBuiltinPredicate> = metadata
            .builtin_predicates()
            .iter()
            .map(|p| ModelBuiltinPredicate {
                name: p.name.to_string(),
                syntax: p.syntax.to_string(),
                selectivity: p.selectivity,
                cost: p.cost,
            })
            .collect();

        let theories: Vec<ModelTheory> = metadata
            .theories()
            .iter()
            .map(|t| ModelTheory {
                name: t.name.to_string(),
                theory_type: t.theory_type.to_string(),
                handled_types: t.handled_types.iter().map(|s| s.to_string()).collect(),
            })
            .collect();

        let channels: Vec<ModelChannel> = metadata
            .channels()
            .iter()
            .map(|c| ModelChannel { category: c.category.to_string() })
            .collect();

        let join_patterns: Vec<ModelJoinPattern> = metadata
            .join_patterns()
            .iter()
            .map(|jp| ModelJoinPattern {
                label: jp.label.to_string(),
                channel_categories: jp
                    .channel_categories
                    .iter()
                    .map(|s| s.to_string())
                    .collect(),
            })
            .collect();

        let connectives: Vec<ModelConnective> = metadata
            .connectives()
            .iter()
            .map(|c| ModelConnective {
                role: c.role.to_string(),
                keywords: c.keywords.iter().map(|s| s.to_string()).collect(),
            })
            .collect();

        LanguageStateMachine {
            categories,
            rewrite_rules,
            equations,
            builtin_predicates,
            theories,
            channels,
            join_patterns,
            connectives,
        }
    }

    /// Count the base (non-congruence) rewrite rules.
    ///
    /// Base rewrites are the actual computational steps of the language
    /// (e.g., communication, execution). Congruence rules merely propagate
    /// rewrites into sub-expressions.
    pub fn base_rewrite_count(&self) -> usize {
        self.rewrite_rules
            .iter()
            .filter(|r| !r.is_congruence)
            .count()
    }

    /// Count the unconditional equations.
    ///
    /// These are equations without freshness or relation conditions,
    /// representing unconditional axioms of the language.
    pub fn unconditional_equation_count(&self) -> usize {
        self.equations.iter().filter(|e| !e.has_conditions).count()
    }

    /// Get all rewrite rule names (including None for unnamed rules).
    pub fn rule_names(&self) -> Vec<Option<&str>> {
        self.rewrite_rules
            .iter()
            .map(|r| r.name.as_deref())
            .collect()
    }

    /// Get all named rewrite rules as a flat list of name strings.
    pub fn named_rules(&self) -> Vec<&str> {
        self.rewrite_rules
            .iter()
            .filter_map(|r| r.name.as_deref())
            .collect()
    }

    // ─── Sim-C: Guard-awareness convenience methods ──────────────────────

    /// Iterator over guarded rewrite rules.
    ///
    /// A rewrite is "guarded" when it has a `BehavioralGuard` premise
    /// in its original `rewrites { }` block — this flag is set by the
    /// macro codegen based on whether the premise list contained a
    /// `Premise::BehavioralGuard(...)` entry. Used by the
    /// `GuardSatisfaction` invariant.
    pub fn guarded_rewrites(&self) -> impl Iterator<Item = &ModelRewriteRule> {
        self.rewrite_rules.iter().filter(|r| r.is_guarded)
    }

    /// Iterator over guarded equations.
    pub fn guarded_equations(&self) -> impl Iterator<Item = &ModelEquation> {
        self.equations.iter().filter(|e| e.is_guarded)
    }

    /// Whether the language declares any communication channels via
    /// `guards { channels { } }`.
    pub fn has_channels(&self) -> bool {
        !self.channels.is_empty()
    }

    /// Look up the first theory registration covering the given category.
    ///
    /// Returns `None` when no registered theory lists `category` in its
    /// `handled_types`, or when the theories slice is empty. A theory
    /// whose `handled_types` is empty (i.e., the `for [...]` clause was
    /// omitted in the source) is treated as handling *all* categories.
    pub fn theory_for(&self, category: &str) -> Option<&ModelTheory> {
        self.theories
            .iter()
            .find(|t| t.handled_types.is_empty() || t.handled_types.iter().any(|c| c == category))
    }

    /// Number of rewrite rules that are guarded.
    pub fn guarded_rewrite_count(&self) -> usize {
        self.guarded_rewrites().count()
    }

    /// Phase 15 (predicated types): construct a state machine model
    /// directly from a parsed `LanguageDef` AST, bypassing the
    /// `LanguageMetadata` runtime trait.
    ///
    /// This is the entry point for non-proc-macro consumers (REPL,
    /// LSP, doc-gen, fuzzers) that get a `LanguageDef` from
    /// `parse2::<LanguageDef>(quote!{...})`. The output is
    /// shape-equivalent to `from_metadata` — same `LanguageStateMachine`
    /// fields populated from the same source data — so downstream
    /// model-based testing infrastructure (proptest strategies,
    /// invariant checkers, simulators) doesn't need to distinguish
    /// the two construction paths.
    ///
    /// ## Mapping
    ///
    /// | LanguageDef field | LanguageStateMachine field |
    /// |-------------------|----------------------------|
    /// | `types[*].name` | `categories` |
    /// | `rewrites[*]` | `rewrite_rules` (LHS/RHS via `Display`) |
    /// | `equations[*]` | `equations` (LHS/RHS via `Display`) |
    /// | `guard_config.builtin_predicates` | `builtin_predicates` |
    /// | `guard_config.theories` | `theories` |
    /// | `guard_config.channels.channel_categories` | `channels` |
    /// | `guard_config.channels.join_patterns` | `join_patterns` |
    /// | `guard_config.connectives` | `connectives` |
    ///
    /// Languages without a `guards { }` block produce empty vectors
    /// for the guard-related fields — same as `from_metadata`.
    pub fn from_def(def: &mettail_ast::language::LanguageDef) -> Self {
        let categories: Vec<String> = def.types.iter().map(|t| t.name.to_string()).collect();

        let rewrite_rules: Vec<ModelRewriteRule> = def
            .rewrites
            .iter()
            .map(|rw| ModelRewriteRule {
                name: Some(rw.name.to_string()),
                lhs_display: format!("{:?}", rw.left),
                rhs_display: format!("{:?}", rw.right),
                // A LanguageDef rewrite is a pure rewrite — congruence
                // rules are auto-generated downstream by the macro
                // pipeline and never appear directly in `def.rewrites`.
                is_congruence: false,
                is_guarded: rw
                    .premises
                    .iter()
                    .any(|p| matches!(p, mettail_ast::language::Premise::BehavioralGuard(_))),
            })
            .collect();

        let equations: Vec<ModelEquation> = def
            .equations
            .iter()
            .map(|eq| ModelEquation {
                lhs_display: format!("{:?}", eq.left),
                rhs_display: format!("{:?}", eq.right),
                has_conditions: !eq.premises.is_empty(),
                is_guarded: eq
                    .premises
                    .iter()
                    .any(|p| matches!(p, mettail_ast::language::Premise::BehavioralGuard(_))),
            })
            .collect();

        // Guard configuration extraction. When `guard_config` is
        // None, all guard-related fields are empty (the no-guards
        // path mirrors `from_metadata`'s behavior).
        let (builtin_predicates, theories, channels, join_patterns, connectives) =
            if let Some(gc) = &def.guard_config {
                (
                    builtin_predicates_from_def(gc),
                    theories_from_def(gc),
                    channels_from_def(gc),
                    join_patterns_from_def(gc),
                    connectives_from_def(gc),
                )
            } else {
                (vec![], vec![], vec![], vec![], vec![])
            };

        LanguageStateMachine {
            categories,
            rewrite_rules,
            equations,
            builtin_predicates,
            theories,
            channels,
            join_patterns,
            connectives,
        }
    }
}

// ── Phase 15 helpers: GuardConfig field extractors ──────────────────

fn builtin_predicates_from_def(
    gc: &mettail_ast::language::GuardConfig,
) -> Vec<ModelBuiltinPredicate> {
    gc.builtin_predicates
        .as_ref()
        .map(|preds| {
            preds
                .iter()
                .map(|p| ModelBuiltinPredicate {
                    name: p.name.to_string(),
                    syntax: p
                        .syntax_forms
                        .first()
                        .map(|form| {
                            form.iter()
                                .map(|s| format!("{:?}", s))
                                .collect::<Vec<_>>()
                                .join(" ")
                        })
                        .unwrap_or_default(),
                    selectivity: p.annotations.selectivity,
                    cost: p.annotations.cost,
                })
                .collect()
        })
        .unwrap_or_default()
}

fn theories_from_def(gc: &mettail_ast::language::GuardConfig) -> Vec<ModelTheory> {
    gc.theories
        .iter()
        .map(|t| ModelTheory {
            name: t.name.to_string(),
            theory_type: format!("{:?}", t.theory_type),
            handled_types: t
                .handled_types
                .as_ref()
                .map(|types| types.iter().map(|i| i.to_string()).collect())
                .unwrap_or_default(),
        })
        .collect()
}

fn channels_from_def(gc: &mettail_ast::language::GuardConfig) -> Vec<ModelChannel> {
    gc.channels
        .as_ref()
        .map(|cc| {
            cc.channel_categories
                .iter()
                .map(|c| ModelChannel { category: c.category.to_string() })
                .collect()
        })
        .unwrap_or_default()
}

fn join_patterns_from_def(gc: &mettail_ast::language::GuardConfig) -> Vec<ModelJoinPattern> {
    gc.channels
        .as_ref()
        .map(|cc| {
            cc.join_patterns
                .iter()
                .map(|jp| ModelJoinPattern {
                    label: jp.label.to_string(),
                    channel_categories: jp
                        .channel_params
                        .iter()
                        .map(|p| p.category.to_string())
                        .collect(),
                })
                .collect()
        })
        .unwrap_or_default()
}

fn connectives_from_def(gc: &mettail_ast::language::GuardConfig) -> Vec<ModelConnective> {
    gc.connectives
        .as_ref()
        .map(|decls| {
            decls
                .iter()
                .map(|d| ModelConnective {
                    role: d.role.as_str().to_string(),
                    keywords: d.keywords.clone(),
                })
                .collect()
        })
        .unwrap_or_default()
}

/// Operations in the model that can be composed into test sequences.
///
/// Each variant represents a semantic action that can be applied during
/// model-based testing of a language.
#[derive(Debug, Clone)]
pub enum ModelOp {
    /// Apply a specific rewrite rule by index into the model's rewrite_rules.
    ApplyRewrite { rule_index: usize },
    /// Run the Ascent fixpoint engine.
    RunAscent,
    /// Check whether the current term is in normal form.
    CheckNormalForm,
    /// Normalize the current term (beta-reduce, flatten collections, etc.).
    Normalize,
}

/// Generate a proptest strategy for model operation sequences.
///
/// Produces random sequences of `ModelOp` values that reference valid rule
/// indices in the given model. The sequence length ranges from 1 to `max_ops`.
///
/// # Arguments
///
/// * `model` - The language state machine providing the set of valid rules.
/// * `max_ops` - Maximum number of operations in a generated sequence.
///
/// # Returns
///
/// A boxed proptest strategy producing `Vec<ModelOp>`.
pub fn arb_model_ops(model: &LanguageStateMachine, max_ops: usize) -> BoxedStrategy<Vec<ModelOp>> {
    let num_rules = model.rewrite_rules.len();

    // Build a strategy for a single ModelOp.
    // If there are rewrite rules, include ApplyRewrite as an option.
    let single_op: BoxedStrategy<ModelOp> = if num_rules > 0 {
        prop_oneof![
            3 => (0..num_rules).prop_map(|idx| ModelOp::ApplyRewrite { rule_index: idx }),
            1 => Just(ModelOp::RunAscent),
            1 => Just(ModelOp::CheckNormalForm),
            1 => Just(ModelOp::Normalize),
        ]
        .boxed()
    } else {
        prop_oneof![
            1 => Just(ModelOp::RunAscent),
            1 => Just(ModelOp::CheckNormalForm),
            1 => Just(ModelOp::Normalize),
        ]
        .boxed()
    };

    // Generate a Vec of 1..=max_ops operations.
    let clamped_max = max_ops.max(1);
    proptest::collection::vec(single_op, 1..=clamped_max).boxed()
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_runtime::{
        EquationDef, LanguageMetadata, LogicRelationDef, LogicRuleDef, RewriteDef, TermDef, TypeDef,
    };

    /// Stub metadata for Calculator-like language with known structure.
    struct CalculatorStubMetadata;

    impl LanguageMetadata for CalculatorStubMetadata {
        fn name(&self) -> &'static str {
            "Calculator"
        }

        fn types(&self) -> &'static [TypeDef] {
            &[
                TypeDef {
                    name: "Int",
                    native_type: Some("i32"),
                    is_primary: true,
                },
                TypeDef {
                    name: "Float",
                    native_type: Some("f64"),
                    is_primary: false,
                },
                TypeDef {
                    name: "Bool",
                    native_type: Some("bool"),
                    is_primary: false,
                },
                TypeDef {
                    name: "Str",
                    native_type: Some("str"),
                    is_primary: false,
                },
            ]
        }

        fn terms(&self) -> &'static [TermDef] {
            // Minimal subset for testing
            &[
                TermDef {
                    name: "AddInt",
                    type_name: "Int",
                    syntax: "a + b",
                    description: None,
                    fields: &[],
                },
                TermDef {
                    name: "SubInt",
                    type_name: "Int",
                    syntax: "a - b",
                    description: None,
                    fields: &[],
                },
            ]
        }

        fn equations(&self) -> &'static [EquationDef] {
            &[]
        }

        fn rewrites(&self) -> &'static [RewriteDef] {
            // Calculator has only congruence rewrites (all operations are fold/step).
            // For testing we include a mix of base and congruence.
            &[
                RewriteDef {
                    name: Some("AddIntCongL"),
                    conditions: &[],
                    premise: Some(("S", "T")),
                    lhs: "(AddInt S R)",
                    rhs: "(AddInt T R)",
                    is_guarded: false,
                },
                RewriteDef {
                    name: Some("AddIntCongR"),
                    conditions: &[],
                    premise: Some(("S", "T")),
                    lhs: "(AddInt L S)",
                    rhs: "(AddInt L T)",
                    is_guarded: false,
                },
                RewriteDef {
                    name: Some("NegCong"),
                    conditions: &[],
                    premise: Some(("S", "T")),
                    lhs: "(Neg S)",
                    rhs: "(Neg T)",
                    is_guarded: false,
                },
            ]
        }

        fn logic_relations(&self) -> &'static [LogicRelationDef] {
            &[]
        }

        fn logic_rules(&self) -> &'static [LogicRuleDef] {
            &[]
        }
    }

    /// Stub metadata for RhoCalc-like language with known structure.
    struct RhoCalcStubMetadata;

    impl LanguageMetadata for RhoCalcStubMetadata {
        fn name(&self) -> &'static str {
            "RhoCalc"
        }

        fn types(&self) -> &'static [TypeDef] {
            &[
                TypeDef {
                    name: "Proc",
                    native_type: None,
                    is_primary: true,
                },
                TypeDef {
                    name: "Name",
                    native_type: None,
                    is_primary: false,
                },
                TypeDef {
                    name: "Int",
                    native_type: Some("i64"),
                    is_primary: false,
                },
                TypeDef {
                    name: "Float",
                    native_type: Some("f64"),
                    is_primary: false,
                },
                TypeDef {
                    name: "Bool",
                    native_type: Some("bool"),
                    is_primary: false,
                },
                TypeDef {
                    name: "Str",
                    native_type: Some("str"),
                    is_primary: false,
                },
            ]
        }

        fn terms(&self) -> &'static [TermDef] {
            &[
                TermDef {
                    name: "PZero",
                    type_name: "Proc",
                    syntax: "{}",
                    description: None,
                    fields: &[],
                },
                TermDef {
                    name: "PDrop",
                    type_name: "Proc",
                    syntax: "*(n)",
                    description: None,
                    fields: &[],
                },
                TermDef {
                    name: "NQuote",
                    type_name: "Name",
                    syntax: "@(p)",
                    description: None,
                    fields: &[],
                },
            ]
        }

        fn equations(&self) -> &'static [EquationDef] {
            &[
                EquationDef {
                    conditions: &[],
                    lhs: "(PPar {P, {}})",
                    rhs: "P",
                    is_guarded: false,
                },
                EquationDef {
                    conditions: &["x # P"],
                    lhs: "(PNew ^x.(P))",
                    rhs: "P",
                    is_guarded: false,
                },
            ]
        }

        fn rewrites(&self) -> &'static [RewriteDef] {
            &[
                RewriteDef {
                    name: Some("Comm"),
                    conditions: &[],
                    premise: None,
                    lhs: "(PPar {(PInputs ns cont), ...})",
                    rhs: "(PPar {(eval cont ...), ...rest})",
                    is_guarded: false,
                },
                RewriteDef {
                    name: Some("Exec"),
                    conditions: &[],
                    premise: None,
                    lhs: "(PDrop (NQuote P))",
                    rhs: "P",
                    is_guarded: false,
                },
                RewriteDef {
                    name: Some("ParCong"),
                    conditions: &[],
                    premise: Some(("S", "T")),
                    lhs: "(PPar {S, ...rest})",
                    rhs: "(PPar {T, ...rest})",
                    is_guarded: false,
                },
                RewriteDef {
                    name: Some("NewCong"),
                    conditions: &[],
                    premise: Some(("S", "T")),
                    lhs: "(PNew ^[xs].S)",
                    rhs: "(PNew ^[xs].T)",
                    is_guarded: false,
                },
                RewriteDef {
                    name: Some("AddCongL"),
                    conditions: &[],
                    premise: Some(("S", "T")),
                    lhs: "(Add S X)",
                    rhs: "(Add T X)",
                    is_guarded: false,
                },
                RewriteDef {
                    name: Some("AddCongR"),
                    conditions: &[],
                    premise: Some(("S", "T")),
                    lhs: "(Add X S)",
                    rhs: "(Add X T)",
                    is_guarded: false,
                },
            ]
        }

        fn logic_relations(&self) -> &'static [LogicRelationDef] {
            &[]
        }

        fn logic_rules(&self) -> &'static [LogicRuleDef] {
            &[]
        }
    }

    #[test]
    fn test_model_from_calculator() {
        let metadata = CalculatorStubMetadata;
        let model = LanguageStateMachine::from_metadata(&metadata);

        // Verify categories
        assert_eq!(model.categories.len(), 4);
        assert_eq!(model.categories[0], "Int");
        assert_eq!(model.categories[1], "Float");
        assert_eq!(model.categories[2], "Bool");
        assert_eq!(model.categories[3], "Str");

        // Verify rewrite rules
        assert_eq!(model.rewrite_rules.len(), 3);

        // All three rules are congruence rules
        assert!(model.rewrite_rules.iter().all(|r| r.is_congruence));

        // Base rewrite count should be 0 (all congruence)
        assert_eq!(model.base_rewrite_count(), 0);

        // No equations in Calculator
        assert_eq!(model.equations.len(), 0);
        assert_eq!(model.unconditional_equation_count(), 0);

        // Rule names should match
        let names: Vec<Option<&str>> = model.rule_names();
        assert_eq!(names[0], Some("AddIntCongL"));
        assert_eq!(names[1], Some("AddIntCongR"));
        assert_eq!(names[2], Some("NegCong"));
    }

    #[test]
    fn test_model_from_rhocalc() {
        let metadata = RhoCalcStubMetadata;
        let model = LanguageStateMachine::from_metadata(&metadata);

        // Verify categories
        assert_eq!(model.categories.len(), 6);
        assert_eq!(model.categories[0], "Proc");
        assert_eq!(model.categories[1], "Name");

        // Verify all rewrite rules captured
        assert_eq!(model.rewrite_rules.len(), 6);

        // Base rewrites: Comm and Exec (no premise)
        assert_eq!(model.base_rewrite_count(), 2);

        // Congruence rewrites: ParCong, NewCong, AddCongL, AddCongR
        let cong_count = model
            .rewrite_rules
            .iter()
            .filter(|r| r.is_congruence)
            .count();
        assert_eq!(cong_count, 4);

        // Verify Comm and Exec are present and are base rules
        let comm = model
            .rewrite_rules
            .iter()
            .find(|r| r.name.as_deref() == Some("Comm"))
            .expect("Comm rule should exist");
        assert!(!comm.is_congruence);
        assert_eq!(comm.lhs_display, "(PPar {(PInputs ns cont), ...})");

        let exec = model
            .rewrite_rules
            .iter()
            .find(|r| r.name.as_deref() == Some("Exec"))
            .expect("Exec rule should exist");
        assert!(!exec.is_congruence);
        assert_eq!(exec.lhs_display, "(PDrop (NQuote P))");
        assert_eq!(exec.rhs_display, "P");

        // Verify equations
        assert_eq!(model.equations.len(), 2);

        // One unconditional equation: PPar identity
        assert_eq!(model.unconditional_equation_count(), 1);

        // The conditional equation has freshness condition
        let cond_eq = model
            .equations
            .iter()
            .find(|e| e.has_conditions)
            .expect("conditional equation should exist");
        assert_eq!(cond_eq.lhs_display, "(PNew ^x.(P))");
    }

    #[test]
    fn test_arb_model_ops_basic() {
        let metadata = RhoCalcStubMetadata;
        let model = LanguageStateMachine::from_metadata(&metadata);

        // Just verify the strategy can be created and produces valid ops
        let strategy = arb_model_ops(&model, 10);
        let mut runner = proptest::test_runner::TestRunner::default();

        for _ in 0..20 {
            let ops = strategy
                .new_tree(&mut runner)
                .expect("strategy should produce a tree")
                .current();

            assert!(!ops.is_empty());
            assert!(ops.len() <= 10);

            // All ApplyRewrite indices must be valid
            for op in &ops {
                if let ModelOp::ApplyRewrite { rule_index } = op {
                    assert!(
                        *rule_index < model.rewrite_rules.len(),
                        "rule_index {} out of bounds (max {})",
                        rule_index,
                        model.rewrite_rules.len()
                    );
                }
            }
        }
    }

    #[test]
    fn test_arb_model_ops_empty_rules() {
        // Model with no rewrite rules
        struct EmptyMetadata;
        impl LanguageMetadata for EmptyMetadata {
            fn name(&self) -> &'static str {
                "Empty"
            }
            fn types(&self) -> &'static [TypeDef] {
                &[TypeDef {
                    name: "T",
                    native_type: None,
                    is_primary: true,
                }]
            }
            fn terms(&self) -> &'static [TermDef] {
                &[]
            }
            fn equations(&self) -> &'static [EquationDef] {
                &[]
            }
            fn rewrites(&self) -> &'static [RewriteDef] {
                &[]
            }
        }

        let model = LanguageStateMachine::from_metadata(&EmptyMetadata);
        let strategy = arb_model_ops(&model, 5);
        let mut runner = proptest::test_runner::TestRunner::default();

        for _ in 0..10 {
            let ops = strategy
                .new_tree(&mut runner)
                .expect("strategy should produce a tree")
                .current();

            assert!(!ops.is_empty());
            // No ApplyRewrite should appear since there are no rules
            for op in &ops {
                assert!(
                    !matches!(op, ModelOp::ApplyRewrite { .. }),
                    "ApplyRewrite should not appear when there are no rules"
                );
            }
        }
    }

    #[test]
    fn test_named_rules() {
        let metadata = RhoCalcStubMetadata;
        let model = LanguageStateMachine::from_metadata(&metadata);

        let named = model.named_rules();
        assert_eq!(named.len(), 6);
        assert!(named.contains(&"Comm"));
        assert!(named.contains(&"Exec"));
        assert!(named.contains(&"ParCong"));
        assert!(named.contains(&"NewCong"));
    }

    // ═════════════════════════════════════════════════════════════════════
    // Sim-C: Guard-metadata ingestion tests
    // ═════════════════════════════════════════════════════════════════════

    use mettail_runtime::{
        BuiltinPredicateDef, ChannelDef, ConnectiveDef, JoinPatternDef, TheoryDef,
    };

    /// Stub metadata for a guard-enabled language. Exercises every
    /// `LanguageMetadata` guard method with non-empty data so the
    /// Sim-C ingestion path can be verified end-to-end.
    struct GuardedStubMetadata;

    static GUARDED_TYPE: TypeDef = TypeDef {
        name: "Proc",
        native_type: None,
        is_primary: true,
    };
    static GUARDED_TYPE2: TypeDef = TypeDef {
        name: "Name",
        native_type: None,
        is_primary: false,
    };
    static GUARDED_TYPES: &[TypeDef] = &[GUARDED_TYPE, GUARDED_TYPE2];

    static GUARDED_REWRITE: &[RewriteDef] = &[
        RewriteDef {
            name: Some("GuardedComm"),
            conditions: &["guard(path(x, y))"],
            premise: None,
            lhs: "(PGuardedInput ch pat cont)",
            rhs: "(eval cont)",
            is_guarded: true,
        },
        RewriteDef {
            name: Some("PlainCong"),
            conditions: &[],
            premise: Some(("S", "T")),
            lhs: "(PPar {S, ...})",
            rhs: "(PPar {T, ...})",
            is_guarded: false,
        },
    ];

    static GUARDED_EQ: &[EquationDef] = &[EquationDef {
        conditions: &["guard(fresh(n))"],
        lhs: "(PNew ^n.P)",
        rhs: "P",
        is_guarded: true,
    }];

    static GUARDED_PREDS: &[BuiltinPredicateDef] = &[
        BuiltinPredicateDef {
            name: "eq",
            syntax: "x \"==\" y",
            selectivity: Some(0.1),
            cost: Some(2),
        },
        BuiltinPredicateDef {
            name: "fresh",
            syntax: "\"fresh\" \"(\" x \")\"",
            selectivity: None,
            cost: None,
        },
    ];

    static GUARDED_THEORIES: &[TheoryDef] = &[
        TheoryDef {
            name: "arithmetic",
            theory_type: "PresburgerAlgebra",
            handled_types: &["Int"],
        },
        TheoryDef {
            name: "patterns",
            theory_type: "UnificationTheory",
            handled_types: &["Proc", "Name"],
        },
    ];

    static GUARDED_CHANNELS: &[ChannelDef] = &[ChannelDef { category: "Name" }];

    static GUARDED_JOINS: &[JoinPatternDef] = &[JoinPatternDef {
        label: "PGuardedInput",
        channel_categories: &["Name"],
    }];

    static GUARDED_CONNECTIVES: &[ConnectiveDef] = &[
        ConnectiveDef { role: "and", keywords: &["and", "∧"] },
        ConnectiveDef { role: "not", keywords: &["not", "¬"] },
    ];

    impl LanguageMetadata for GuardedStubMetadata {
        fn name(&self) -> &'static str {
            "GuardedRho"
        }
        fn types(&self) -> &'static [TypeDef] {
            GUARDED_TYPES
        }
        fn terms(&self) -> &'static [TermDef] {
            &[]
        }
        fn equations(&self) -> &'static [EquationDef] {
            GUARDED_EQ
        }
        fn rewrites(&self) -> &'static [RewriteDef] {
            GUARDED_REWRITE
        }
        fn builtin_predicates(&self) -> &'static [BuiltinPredicateDef] {
            GUARDED_PREDS
        }
        fn theories(&self) -> &'static [TheoryDef] {
            GUARDED_THEORIES
        }
        fn channels(&self) -> &'static [ChannelDef] {
            GUARDED_CHANNELS
        }
        fn join_patterns(&self) -> &'static [JoinPatternDef] {
            GUARDED_JOINS
        }
        fn connectives(&self) -> &'static [ConnectiveDef] {
            GUARDED_CONNECTIVES
        }
    }

    #[test]
    fn sim_c_state_machine_ingests_guard_metadata() {
        let metadata = GuardedStubMetadata;
        let model = LanguageStateMachine::from_metadata(&metadata);

        // Core model fields
        assert_eq!(model.categories, vec!["Proc".to_string(), "Name".to_string()]);
        assert_eq!(model.rewrite_rules.len(), 2);
        assert_eq!(model.equations.len(), 1);

        // Guarded rewrite flag
        assert!(model.rewrite_rules[0].is_guarded);
        assert!(!model.rewrite_rules[1].is_guarded);
        assert!(model.equations[0].is_guarded);
        assert_eq!(model.guarded_rewrite_count(), 1);

        // Built-in predicates
        assert_eq!(model.builtin_predicates.len(), 2);
        assert_eq!(model.builtin_predicates[0].name, "eq");
        assert_eq!(model.builtin_predicates[0].selectivity, Some(0.1));
        assert_eq!(model.builtin_predicates[0].cost, Some(2));
        assert_eq!(model.builtin_predicates[1].name, "fresh");
        assert_eq!(model.builtin_predicates[1].selectivity, None);
        assert_eq!(model.builtin_predicates[1].cost, None);

        // Theories
        assert_eq!(model.theories.len(), 2);
        assert_eq!(model.theories[0].name, "arithmetic");
        assert_eq!(model.theories[0].theory_type, "PresburgerAlgebra");
        assert_eq!(model.theories[0].handled_types, vec!["Int".to_string()]);
        assert_eq!(model.theories[1].name, "patterns");
        assert_eq!(model.theories[1].handled_types, vec!["Proc".to_string(), "Name".to_string()]);

        // Channels / joins
        assert_eq!(model.channels.len(), 1);
        assert_eq!(model.channels[0].category, "Name");
        assert!(model.has_channels());
        assert_eq!(model.join_patterns.len(), 1);
        assert_eq!(model.join_patterns[0].label, "PGuardedInput");
        assert_eq!(model.join_patterns[0].channel_categories, vec!["Name".to_string()]);

        // Connectives
        assert_eq!(model.connectives.len(), 2);
        assert_eq!(model.connectives[0].role, "and");
        assert_eq!(model.connectives[0].keywords, vec!["and".to_string(), "∧".to_string()]);
        assert_eq!(model.connectives[1].role, "not");
    }

    #[test]
    fn sim_c_theory_for_lookup() {
        let metadata = GuardedStubMetadata;
        let model = LanguageStateMachine::from_metadata(&metadata);

        // Int is handled by `arithmetic`
        assert_eq!(model.theory_for("Int").map(|t| t.name.as_str()), Some("arithmetic"));
        // Proc is handled by `patterns`
        assert_eq!(model.theory_for("Proc").map(|t| t.name.as_str()), Some("patterns"));
        // Category not in any `handled_types` returns None
        assert!(model.theory_for("Nonexistent").is_none());
    }

    #[test]
    fn sim_c_guarded_rewrites_iterator() {
        let metadata = GuardedStubMetadata;
        let model = LanguageStateMachine::from_metadata(&metadata);

        let names: Vec<&str> = model
            .guarded_rewrites()
            .filter_map(|r| r.name.as_deref())
            .collect();
        assert_eq!(names, vec!["GuardedComm"]);
    }

    #[test]
    fn sim_c_backward_compat_for_unguarded_languages() {
        // RhoCalcStubMetadata has no guard metadata — verify the model
        // reflects that with empty guard fields.
        let metadata = RhoCalcStubMetadata;
        let model = LanguageStateMachine::from_metadata(&metadata);

        assert!(model.builtin_predicates.is_empty());
        assert!(model.theories.is_empty());
        assert!(model.channels.is_empty());
        assert!(model.join_patterns.is_empty());
        assert!(model.connectives.is_empty());
        assert!(!model.has_channels());
        assert_eq!(model.guarded_rewrite_count(), 0);
        assert!(model.theory_for("Proc").is_none());
        // Existing rewrites are all unguarded — the new flag default propagates.
        for rw in &model.rewrite_rules {
            assert!(!rw.is_guarded);
        }
    }

    // ── Proptest: guard metadata round-trip ──────────────────────────
    //
    // For any random list of TheoryDef-shaped data, the simulation
    // model's Vec<ModelTheory> has the same length, names, theory
    // types, and handled-types lists in the same order. This verifies
    // the Sim-C ingestion path preserves the data faithfully.

    proptest! {
        /// The length of `model.theories` is equal to the length of the
        /// metadata slice passed in, and every entry's `name` round-trips.
        #[test]
        fn proptest_sim_c_theory_ingestion_preserves_count(
            theory_count in 0usize..8,
        ) {
            // We can't construct arbitrary `&'static [TheoryDef]` from
            // proptest input at runtime, so build a Vec<TheoryDef> with
            // owned &'static str references via Box::leak — acceptable
            // inside test code.
            let leaked: Vec<TheoryDef> = (0..theory_count)
                .map(|i| {
                    let name = Box::leak(format!("theory_{}", i).into_boxed_str());
                    let ty = Box::leak(format!("TheoryType{}", i).into_boxed_str());
                    TheoryDef {
                        name: &*name,
                        theory_type: &*ty,
                        handled_types: &[],
                    }
                })
                .collect();
            let static_slice: &'static [TheoryDef] = Box::leak(leaked.into_boxed_slice());

            struct Meta(&'static [TheoryDef]);
            impl LanguageMetadata for Meta {
                fn name(&self) -> &'static str { "PropMeta" }
                fn types(&self) -> &'static [TypeDef] { std::slice::from_ref(&GUARDED_TYPE) }
                fn terms(&self) -> &'static [TermDef] { &[] }
                fn equations(&self) -> &'static [EquationDef] { &[] }
                fn rewrites(&self) -> &'static [RewriteDef] { &[] }
                fn theories(&self) -> &'static [TheoryDef] { self.0 }
            }

            let meta = Meta(static_slice);
            let model = LanguageStateMachine::from_metadata(&meta);
            prop_assert_eq!(model.theories.len(), theory_count);
            for (i, t) in model.theories.iter().enumerate() {
                prop_assert_eq!(&t.name, &format!("theory_{}", i));
                prop_assert_eq!(&t.theory_type, &format!("TheoryType{}", i));
            }
        }
    }

    // ── Phase 15 (predicated types): from_def adapter tests ──

    mod phase15_from_def {
        use super::*;
        use mettail_ast::language::LanguageDef;
        use quote::quote;
        use syn::parse2;

        #[test]
        fn from_def_extracts_categories() {
            let input = quote! {
                name: TinyLang,
                types { Proc Name },
                terms {
                    PZero . |- "0" : Proc ;
                }
            };
            let def = parse2::<LanguageDef>(input).expect("parse ok");
            let model = LanguageStateMachine::from_def(&def);
            assert_eq!(model.categories.len(), 2);
            assert!(model.categories.contains(&"Proc".to_string()));
            assert!(model.categories.contains(&"Name".to_string()));
        }

        #[test]
        fn from_def_no_guards_yields_empty_guard_fields() {
            let input = quote! {
                name: NoGuards,
                types { Proc },
                terms {
                    PZero . |- "0" : Proc ;
                }
            };
            let def = parse2::<LanguageDef>(input).expect("parse ok");
            let model = LanguageStateMachine::from_def(&def);
            assert!(model.builtin_predicates.is_empty());
            assert!(model.theories.is_empty());
            assert!(model.channels.is_empty());
            assert!(model.join_patterns.is_empty());
            assert!(model.connectives.is_empty());
        }

        #[test]
        fn from_def_with_guards_block_extracts_connectives() {
            let input = quote! {
                name: WithGuards,
                types { Proc },
                guards {
                    connectives {
                        and = "&&";
                        or = "||";
                    }
                },
                terms {
                    PZero . |- "0" : Proc ;
                }
            };
            let def = parse2::<LanguageDef>(input).expect("parse ok");
            let model = LanguageStateMachine::from_def(&def);
            assert_eq!(model.connectives.len(), 2);
            let roles: Vec<&str> = model.connectives.iter().map(|c| c.role.as_str()).collect();
            assert!(roles.contains(&"and"));
            assert!(roles.contains(&"or"));
        }

        #[test]
        fn from_def_with_channels_extracts_channels() {
            let input = quote! {
                name: ChanLang,
                types { Proc Name },
                guards {
                    channels {
                        channel Name;
                    }
                },
                terms {
                    PZero . |- "0" : Proc ;
                    NQuote . p:Proc |- "@" "(" p ")" : Name ;
                }
            };
            let def = parse2::<LanguageDef>(input).expect("parse ok");
            let model = LanguageStateMachine::from_def(&def);
            assert_eq!(model.channels.len(), 1);
            assert_eq!(model.channels[0].category, "Name");
        }

        #[test]
        fn from_def_shape_matches_from_metadata_for_simple_lang() {
            // Both adapters should produce the same category count for
            // a minimal language. Since from_metadata requires a static
            // metadata impl and from_def reads a parsed LanguageDef, we
            // verify the *structural* invariant: empty guards → all
            // guard fields empty.
            let input = quote! {
                name: ShapeTest,
                types { Proc },
                terms { PZero . |- "0" : Proc ; }
            };
            let def = parse2::<LanguageDef>(input).expect("parse ok");
            let model = LanguageStateMachine::from_def(&def);
            assert_eq!(model.categories.len(), 1);
            assert_eq!(model.builtin_predicates.len(), 0);
            assert_eq!(model.theories.len(), 0);
            assert_eq!(model.channels.len(), 0);
            assert_eq!(model.join_patterns.len(), 0);
            assert_eq!(model.connectives.len(), 0);
        }
    }
}
