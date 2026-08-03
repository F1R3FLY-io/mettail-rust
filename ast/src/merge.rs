//! LanguageDef-level merge engine for language composition.
//!
//! Provides `merge_language_defs()` which merges two `LanguageDef`s at the AST level,
//! analogous to `prattail/src/compose.rs` which operates on `LanguageSpec`s.
//!
//! This operates on **raw, denormalized** `LanguageDef`s — before validation,
//! classification, FIRST/FOLLOW computation, WFST construction, or optimization.
//! The full pipeline runs exactly once on the merged result.
//!
//! ## Merge Strategies
//!
//! | Component | Merge Strategy |
//! |-----------|---------------|
//! | **types** | Union by name; native_type must match if both present; `is_primary` from extension |
//! | **terms** | `Error`: concatenate, reject same label. `Override`: extension label replaces base |
//! | **equations** | Same as terms (keyed by equation name) |
//! | **rewrites** | Same as terms (keyed by rewrite name) |
//! | **logic** | Relations: union by name, error if param types differ. Content: concatenate TokenStreams |
//! | **options** | Extension values override base for matching keys |

use std::collections::{HashMap, HashSet};
use std::fmt;

use crate::language::GuardSlotDecl;
use syn::Ident;

use super::language::{
    BuiltinPredicate, Equation, GuardConfig, LangType, LanguageDef, LogicBlock, ModeDef,
    PredicateAnnotations, RewriteRule, TheoryRegistration, TokenDef,
};

// ══════════════════════════════════════════════════════════════════════════════
// Error types
// ══════════════════════════════════════════════════════════════════════════════

/// Errors that can occur during LanguageDef-level merge.
#[derive(Debug, Clone)]
pub enum MergeError {
    /// Two categories share a name but have different native types.
    CategoryNativeTypeMismatch {
        category: String,
        type_a: Option<String>,
        type_b: Option<String>,
    },

    /// Two rules share a label (constructor name) and the strategy is `Error`.
    DuplicateRuleLabel {
        label: String,
        category_a: String,
        category_b: String,
    },

    /// Two equations share a name and the strategy is `Error`.
    DuplicateEquationName { name: String },

    /// Two rewrites share a name and the strategy is `Error`.
    DuplicateRewriteName { name: String },

    /// A logic block has conflicting relation declarations (same name, different param types).
    ConflictingLogicRelation {
        name: String,
        params_a: Vec<String>,
        params_b: Vec<String>,
    },

    /// Two `guards { }` blocks declare the same predicate name with
    /// incompatible signatures (different arity or parameter types).
    DuplicatePredicateName {
        name: String,
        arity_a: usize,
        arity_b: usize,
    },

    /// Two `guards { theories { } }` sub-blocks declare the same theory
    /// name but map it to different theory types.
    ConflictingTheoryRegistration {
        name: String,
        type_a: String,
        type_b: String,
    },
}

impl fmt::Display for MergeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MergeError::CategoryNativeTypeMismatch { category, type_a, type_b } => {
                write!(
                    f,
                    "category '{}' has conflicting native types: {:?} vs {:?}",
                    category, type_a, type_b
                )
            },
            MergeError::DuplicateRuleLabel { label, category_a, category_b } => {
                write!(
                    f,
                    "rule label '{}' appears in both grammars (categories: '{}' and '{}')",
                    label, category_a, category_b
                )
            },
            MergeError::DuplicateEquationName { name } => {
                write!(f, "equation '{}' appears in both grammars", name)
            },
            MergeError::DuplicateRewriteName { name } => {
                write!(f, "rewrite rule '{}' appears in both grammars", name)
            },
            MergeError::ConflictingLogicRelation { name, params_a, params_b } => {
                write!(
                    f,
                    "logic relation '{}' has conflicting parameter types: {:?} vs {:?}",
                    name, params_a, params_b
                )
            },
            MergeError::DuplicatePredicateName { name, arity_a, arity_b } => {
                write!(
                    f,
                    "guards predicate '{}' declared with conflicting arities ({} vs {})",
                    name, arity_a, arity_b
                )
            },
            MergeError::ConflictingTheoryRegistration { name, type_a, type_b } => {
                write!(
                    f,
                    "guards theory '{}' is registered with conflicting types: '{}' vs '{}'",
                    name, type_a, type_b
                )
            },
        }
    }
}

impl std::error::Error for MergeError {}

// ══════════════════════════════════════════════════════════════════════════════
// DuplicateStrategy
// ══════════════════════════════════════════════════════════════════════════════

/// Strategy for handling duplicate labels/names across merged grammars.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DuplicateStrategy {
    /// Reject duplicate labels — used by `extends` (additive only).
    Error,
    /// Later definition wins — used by `includes` and `mixins` (override).
    Override,
}

// ══════════════════════════════════════════════════════════════════════════════
// merge_language_defs — the main entry point
// ══════════════════════════════════════════════════════════════════════════════

/// Merge two `LanguageDef`s into a single merged definition.
///
/// `base` is the inherited/imported grammar, `extension` is the consumer grammar.
/// The extension's values take priority for options and (with `Override` strategy) for
/// duplicate rule labels.
///
/// The result is a **raw, denormalized** `LanguageDef` ready for the full pipeline
/// (validation, classification, FIRST/FOLLOW, WFST, optimization).
///
/// # Errors
///
/// Returns a `Vec<MergeError>` if any invariant is violated.
pub fn merge_language_defs(
    base: &LanguageDef,
    extension: &LanguageDef,
    strategy: DuplicateStrategy,
) -> Result<LanguageDef, Vec<MergeError>> {
    let mut errors: Vec<MergeError> = Vec::new();

    // 1. Merge types (categories)
    let merged_types = merge_types(&base.types, &extension.types, &mut errors);

    // 2. Merge token definitions (extension overrides base by name)
    let merged_token_defs = merge_token_defs(&base.token_defs, &extension.token_defs, strategy);

    // 3. Merge mode definitions (union by name; tokens within same-named mode are merged)
    let merged_mode_defs = merge_mode_defs(&base.mode_defs, &extension.mode_defs, strategy);

    // 4. Merge sync constraints (extension replaces base entirely)
    let merged_sync_constraints = if extension.sync_constraints.is_empty() {
        base.sync_constraints.clone()
    } else {
        extension.sync_constraints.clone()
    };

    // 5. Merge tree invariants (extension replaces base entirely)
    let merged_tree_invariants = if extension.tree_invariants.is_empty() {
        base.tree_invariants.clone()
    } else {
        extension.tree_invariants.clone()
    };

    // 6. Merge terms (grammar rules)
    let merged_terms = merge_terms(&base.terms, &extension.terms, strategy, &mut errors);

    // 7. Merge equations
    let merged_equations =
        merge_equations(&base.equations, &extension.equations, strategy, &mut errors);

    // 8. Merge rewrites
    let merged_rewrites =
        merge_rewrites(&base.rewrites, &extension.rewrites, strategy, &mut errors);

    // 9. Merge logic blocks
    let merged_logic = merge_logic(&base.logic, &extension.logic, &mut errors);

    // 10. Merge guard configuration (design doc §2A composition semantics)
    let merged_guard_config =
        merge_guard_config(&base.guard_config, &extension.guard_config, &mut errors);

    // 11. Merge options (extension overrides base)
    let merged_options = merge_options(&base.options, &extension.options);

    if !errors.is_empty() {
        return Err(errors);
    }

    Ok(LanguageDef {
        // Use the extension's name (the consuming language)
        name: extension.name.clone(),
        options: merged_options,
        // Composition clauses are consumed during merge; the merged result has none
        extends_names: Vec::new(),
        include_names: Vec::new(),
        mixin_names: Vec::new(),
        types: merged_types,
        refinement_types: Vec::new(),
        token_defs: merged_token_defs,
        mode_defs: merged_mode_defs,
        sync_constraints: merged_sync_constraints,
        tree_invariants: merged_tree_invariants,
        terms: merged_terms,
        equations: merged_equations,
        rewrites: merged_rewrites,
        logic: merged_logic,
        guard_config: merged_guard_config,
    })
}

// ══════════════════════════════════════════════════════════════════════════════
// Guard configuration merging (design doc §2A "Composition Semantics")
// ══════════════════════════════════════════════════════════════════════════════
//
// | Sub-block    | Strategy                                |
// |--------------|-----------------------------------------|
// | Predicates   | Union by name; error on arity conflict; |
// |              | annotations: extension wins per-field   |
// | Connectives  | Extension replaces base entirely        |
// | Theories     | Union by name; error on type conflict   |
// | Channels     | Extension replaces base entirely        |

/// Merge two optional `GuardConfig`s following the §2A composition rules.
///
/// - `(None, None)` → `None`
/// - `(Some, None)` → clone of base
/// - `(None, Some)` → clone of extension
/// - `(Some, Some)` → merged according to per-sub-block rules above
pub(crate) fn merge_guard_config(
    base: &Option<GuardConfig>,
    extension: &Option<GuardConfig>,
    errors: &mut Vec<MergeError>,
) -> Option<GuardConfig> {
    match (base, extension) {
        (None, None) => None,
        (Some(b), None) => Some(b.clone()),
        (None, Some(e)) => Some(e.clone()),
        (Some(b), Some(e)) => Some(GuardConfig {
            builtin_predicates: merge_builtin_predicates(
                &b.builtin_predicates,
                &e.builtin_predicates,
                errors,
            ),
            // Connectives: extension replaces base entirely (when present).
            connectives: match (&b.connectives, &e.connectives) {
                (_, Some(extension_decls)) => Some(extension_decls.clone()),
                (Some(base_decls), None) => Some(base_decls.clone()),
                (None, None) => None,
            },
            theories: merge_theory_registrations(&b.theories, &e.theories, errors),
            // Channels: extension replaces base entirely (when present).
            channels: match (&b.channels, &e.channels) {
                (_, Some(extension_ch)) => Some(extension_ch.clone()),
                (Some(base_ch), None) => Some(base_ch.clone()),
                (None, None) => None,
            },
            // Guard slots: UNION, deduplicated by `(label, param)`.
            //
            // Union rather than replace, because a guard slot is a fact about ONE rule: an
            // extension that declares a slot on its own new rule must not silently drop the
            // base's declaration on a rule it never mentioned. There is nothing to conflict
            // over — the declaration carries no payload beyond the pair itself — so dedup is
            // the whole merge.
            guard_slots: merge_guard_slots(&b.guard_slots, &e.guard_slots),
        }),
    }
}

/// Union two guard-slot declaration lists, deduplicated by `(label, param)`.
fn merge_guard_slots(base: &[GuardSlotDecl], extension: &[GuardSlotDecl]) -> Vec<GuardSlotDecl> {
    let mut out: Vec<GuardSlotDecl> = Vec::with_capacity(base.len() + extension.len());
    let mut seen: std::collections::BTreeSet<(String, String)> = std::collections::BTreeSet::new();
    for decl in base.iter().chain(extension.iter()) {
        let key = (decl.label.to_string(), decl.param.to_string());
        if seen.insert(key) {
            out.push(decl.clone());
        }
    }
    out
}

/// Merge two optional builtin predicate lists.
///
/// Union by name. When the same predicate name appears in both:
/// - Arity must match (else `DuplicatePredicateName` error).
/// - Annotations: extension wins per-field (extension's `selectivity` overrides
///   base's; if extension's `cost` is `None`, base's `cost` is inherited).
fn merge_builtin_predicates(
    base: &Option<Vec<BuiltinPredicate>>,
    extension: &Option<Vec<BuiltinPredicate>>,
    errors: &mut Vec<MergeError>,
) -> Option<Vec<BuiltinPredicate>> {
    match (base, extension) {
        (None, None) => None,
        (Some(b), None) => Some(b.clone()),
        (None, Some(e)) => Some(e.clone()),
        (Some(base_preds), Some(ext_preds)) => {
            let mut merged: Vec<BuiltinPredicate> =
                Vec::with_capacity(base_preds.len() + ext_preds.len());
            // Index extension predicates by name for lookup
            let mut ext_by_name: HashMap<String, &BuiltinPredicate> =
                HashMap::with_capacity(ext_preds.len());
            for p in ext_preds {
                ext_by_name.insert(p.name.to_string(), p);
            }
            let mut consumed: std::collections::HashSet<String> = std::collections::HashSet::new();

            // Walk base predicates; if extension has a same-named one,
            // merge annotations field-by-field.
            for base_pred in base_preds {
                let name = base_pred.name.to_string();
                if let Some(ext_pred) = ext_by_name.get(name.as_str()) {
                    if base_pred.params.len() != ext_pred.params.len() {
                        errors.push(MergeError::DuplicatePredicateName {
                            name: name.clone(),
                            arity_a: base_pred.params.len(),
                            arity_b: ext_pred.params.len(),
                        });
                        continue;
                    }
                    // Merge annotations: extension's value wins per-field.
                    let merged_annotations = PredicateAnnotations {
                        selectivity: ext_pred
                            .annotations
                            .selectivity
                            .or(base_pred.annotations.selectivity),
                        cost: ext_pred.annotations.cost.or(base_pred.annotations.cost),
                    };
                    merged.push(BuiltinPredicate {
                        name: ext_pred.name.clone(),
                        params: ext_pred.params.clone(),
                        syntax_forms: ext_pred.syntax_forms.clone(),
                        annotations: merged_annotations,
                    });
                    consumed.insert(name);
                } else {
                    merged.push(base_pred.clone());
                }
            }

            // Append extension-only predicates (not consumed above).
            for ext_pred in ext_preds {
                let name = ext_pred.name.to_string();
                if !consumed.contains(&name) {
                    merged.push(ext_pred.clone());
                }
            }

            Some(merged)
        },
    }
}

/// Merge two theory registration lists.
///
/// Union by name. Same name with different `theory_type` is an error.
fn merge_theory_registrations(
    base: &[TheoryRegistration],
    extension: &[TheoryRegistration],
    errors: &mut Vec<MergeError>,
) -> Vec<TheoryRegistration> {
    let mut merged: Vec<TheoryRegistration> = Vec::with_capacity(base.len() + extension.len());
    let mut by_name: HashMap<String, &TheoryRegistration> = HashMap::with_capacity(base.len());

    for t in base {
        let name = t.name.to_string();
        by_name.insert(name, t);
        merged.push(t.clone());
    }

    for t in extension {
        let name = t.name.to_string();
        if let Some(existing) = by_name.get(name.as_str()) {
            // Same name — types must match (compared as token-stream strings).
            let ty_a = {
                let ty = &existing.theory_type;
                quote::quote!(#ty).to_string()
            };
            let ty_b = {
                let ty = &t.theory_type;
                quote::quote!(#ty).to_string()
            };
            if ty_a != ty_b {
                errors.push(MergeError::ConflictingTheoryRegistration {
                    name,
                    type_a: ty_a,
                    type_b: ty_b,
                });
            }
            // No insert — base wins on identical types (idempotent).
        } else {
            merged.push(t.clone());
        }
    }

    merged
}

// ══════════════════════════════════════════════════════════════════════════════
// Type (category) merging
// ══════════════════════════════════════════════════════════════════════════════

/// Merge two type (category) vectors.
///
/// Categories from `base` come first; categories unique to `extension` are appended.
/// If both define the same category name, their native types must match.
fn merge_types(
    base: &[LangType],
    extension: &[LangType],
    errors: &mut Vec<MergeError>,
) -> Vec<LangType> {
    let mut by_name: HashMap<String, &LangType> = HashMap::with_capacity(base.len());
    let mut result: Vec<LangType> = Vec::with_capacity(base.len() + extension.len());

    // Add all categories from base
    for t in base {
        let name = t.name.to_string();
        by_name.insert(name, t);
        result.push(t.clone());
    }

    // Merge categories from extension
    for t in extension {
        let name = t.name.to_string();
        if let Some(existing) = by_name.get(&name) {
            // Category exists — verify native type matches
            let existing_native = existing
                .native_type
                .as_ref()
                .map(|ty| quote::quote!(#ty).to_string());
            let new_native = t
                .native_type
                .as_ref()
                .map(|ty| quote::quote!(#ty).to_string());
            if existing_native != new_native {
                errors.push(MergeError::CategoryNativeTypeMismatch {
                    category: name,
                    type_a: existing_native,
                    type_b: new_native,
                });
            }
            // Skip (already present from base)
        } else {
            result.push(t.clone());
            by_name.insert(name, t);
        }
    }

    result
}

// ══════════════════════════════════════════════════════════════════════════════
// Term (grammar rule) merging
// ══════════════════════════════════════════════════════════════════════════════

/// Merge two term (grammar rule) vectors.
///
/// With `DuplicateStrategy::Error`, duplicate labels produce an error.
/// With `DuplicateStrategy::Override`, the extension's rule replaces the base's.
fn merge_terms(
    base: &[super::grammar::GrammarRule],
    extension: &[super::grammar::GrammarRule],
    strategy: DuplicateStrategy,
    errors: &mut Vec<MergeError>,
) -> Vec<super::grammar::GrammarRule> {
    let mut labels: HashMap<String, String> = HashMap::with_capacity(base.len());
    let mut result: Vec<super::grammar::GrammarRule> =
        Vec::with_capacity(base.len() + extension.len());

    // Add all rules from base
    for rule in base {
        let label = rule.label.to_string();
        labels.insert(label, rule.category.to_string());
        result.push(rule.clone());
    }

    // Merge rules from extension
    for rule in extension {
        let label = rule.label.to_string();
        if let Some(existing_cat) = labels.get(&label) {
            match strategy {
                DuplicateStrategy::Error => {
                    errors.push(MergeError::DuplicateRuleLabel {
                        label,
                        category_a: existing_cat.clone(),
                        category_b: rule.category.to_string(),
                    });
                },
                DuplicateStrategy::Override => {
                    // Remove the base rule and add the extension's
                    result.retain(|r| r.label != label);
                    labels.insert(label, rule.category.to_string());
                    result.push(rule.clone());
                },
            }
        } else {
            labels.insert(label, rule.category.to_string());
            result.push(rule.clone());
        }
    }

    result
}

// ══════════════════════════════════════════════════════════════════════════════
// Equation merging
// ══════════════════════════════════════════════════════════════════════════════

/// Merge two equation vectors.
fn merge_equations(
    base: &[Equation],
    extension: &[Equation],
    strategy: DuplicateStrategy,
    errors: &mut Vec<MergeError>,
) -> Vec<Equation> {
    // A `HashMap<String, ()>` is a SET spelled as a map: nothing ever reads the unit
    // value. Saying so directly drops the dead payload and is why `clippy::map_entry`
    // no longer applies — the entry API it wants would force a `slot.key().clone()`
    // in the `Error` arm below, which needs the name by VALUE.
    let mut names: HashSet<String> = HashSet::with_capacity(base.len());
    let mut result: Vec<Equation> = Vec::with_capacity(base.len() + extension.len());

    for eq in base {
        let name = eq.name.to_string();
        names.insert(name);
        result.push(eq.clone());
    }

    for eq in extension {
        let name = eq.name.to_string();
        if names.contains(&name) {
            match strategy {
                DuplicateStrategy::Error => {
                    errors.push(MergeError::DuplicateEquationName { name });
                },
                DuplicateStrategy::Override => {
                    result.retain(|e| e.name != name);
                    names.insert(name);
                    result.push(eq.clone());
                },
            }
        } else {
            names.insert(name);
            result.push(eq.clone());
        }
    }

    result
}

// ══════════════════════════════════════════════════════════════════════════════
// Rewrite merging
// ══════════════════════════════════════════════════════════════════════════════

/// Merge two rewrite rule vectors.
fn merge_rewrites(
    base: &[RewriteRule],
    extension: &[RewriteRule],
    strategy: DuplicateStrategy,
    errors: &mut Vec<MergeError>,
) -> Vec<RewriteRule> {
    // Same as `merge_equations`: a set, not a map. See the note there for why the
    // entry API `clippy::map_entry` suggests is the wrong shape for this loop.
    let mut names: HashSet<String> = HashSet::with_capacity(base.len());
    let mut result: Vec<RewriteRule> = Vec::with_capacity(base.len() + extension.len());

    for rw in base {
        let name = rw.name.to_string();
        names.insert(name);
        result.push(rw.clone());
    }

    for rw in extension {
        let name = rw.name.to_string();
        if names.contains(&name) {
            match strategy {
                DuplicateStrategy::Error => {
                    errors.push(MergeError::DuplicateRewriteName { name });
                },
                DuplicateStrategy::Override => {
                    result.retain(|r| r.name != name);
                    names.insert(name);
                    result.push(rw.clone());
                },
            }
        } else {
            names.insert(name);
            result.push(rw.clone());
        }
    }

    result
}

// ══════════════════════════════════════════════════════════════════════════════
// Logic block merging
// ══════════════════════════════════════════════════════════════════════════════

/// Merge two optional logic blocks.
///
/// Relations are unioned by name; conflicting param types produce an error.
/// Content TokenStreams are concatenated.
fn merge_logic(
    base: &Option<LogicBlock>,
    extension: &Option<LogicBlock>,
    errors: &mut Vec<MergeError>,
) -> Option<LogicBlock> {
    match (base, extension) {
        (None, None) => None,
        (Some(b), None) => Some(b.clone()),
        (None, Some(e)) => Some(e.clone()),
        (Some(b), Some(e)) => {
            // Union relations by name
            let mut relations = b.relations.clone();
            let base_rel_names: HashMap<String, &Vec<String>> = b
                .relations
                .iter()
                .map(|r| (r.name.to_string(), &r.param_types))
                .collect();

            for rel in &e.relations {
                let name = rel.name.to_string();
                if let Some(existing_params) = base_rel_names.get(&name) {
                    // Check param types match
                    if **existing_params != rel.param_types {
                        errors.push(MergeError::ConflictingLogicRelation {
                            name,
                            params_a: (*existing_params).clone(),
                            params_b: rel.param_types.clone(),
                        });
                    }
                    // Skip duplicate (already present from base)
                } else {
                    relations.push(rel.clone());
                }
            }

            // Concatenate content TokenStreams
            let base_content = &b.content;
            let ext_content = &e.content;
            let merged_content = quote::quote! {
                #base_content
                #ext_content
            };

            Some(LogicBlock { relations, content: merged_content })
        },
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Options merging
// ══════════════════════════════════════════════════════════════════════════════

/// Merge two option maps. Extension values override base values for matching keys.
fn merge_options(
    base: &HashMap<String, super::language::AttributeValue>,
    extension: &HashMap<String, super::language::AttributeValue>,
) -> HashMap<String, super::language::AttributeValue> {
    let mut result = base.clone();
    for (key, value) in extension {
        result.insert(key.clone(), value.clone());
    }
    result
}

// ══════════════════════════════════════════════════════════════════════════════
// Token definition merging
// ══════════════════════════════════════════════════════════════════════════════

/// Merge two token definition vectors.
///
/// With `DuplicateStrategy::Error`, duplicate names produce an error.
/// With `DuplicateStrategy::Override`, the extension's definition replaces the base's.
fn merge_token_defs(
    base: &[TokenDef],
    extension: &[TokenDef],
    strategy: DuplicateStrategy,
) -> Vec<TokenDef> {
    // Membership is the ONLY question asked of this structure, so it is a set. It was a
    // `HashMap<String, usize>` whose index no reader consumed — and could not have,
    // because the `Override` arm below rewrites `result` without updating the index,
    // leaving every overridden entry's position stale. Storing a value that is both dead
    // and wrong invites a future `by_name[&name]` to be silently incorrect; the set
    // cannot be misread. It is also why `clippy::map_entry` no longer applies.
    let mut names: HashSet<String> = HashSet::with_capacity(base.len());
    let mut result: Vec<TokenDef> = Vec::with_capacity(base.len() + extension.len());

    for td in base {
        let name = td.name.to_string();
        names.insert(name);
        result.push(td.clone());
    }

    for td in extension {
        let name = td.name.to_string();
        if names.contains(&name) {
            match strategy {
                DuplicateStrategy::Error => {
                    // Token name conflicts are non-fatal in extends mode;
                    // the base definition is kept (same behavior as types).
                },
                DuplicateStrategy::Override => {
                    result.retain(|t| t.name != name);
                    result.push(td.clone());
                },
            }
        } else {
            names.insert(name);
            result.push(td.clone());
        }
    }

    result
}

// ══════════════════════════════════════════════════════════════════════════════
// Mode definition merging
// ══════════════════════════════════════════════════════════════════════════════

/// Merge two mode definition vectors.
///
/// Modes are merged by name: tokens within same-named modes are union'd.
/// With `DuplicateStrategy::Override`, extension tokens replace base tokens
/// within the same mode when names collide.
fn merge_mode_defs(
    base: &[ModeDef],
    extension: &[ModeDef],
    strategy: DuplicateStrategy,
) -> Vec<ModeDef> {
    let mut by_name: HashMap<String, usize> = HashMap::with_capacity(base.len());
    let mut result: Vec<ModeDef> = Vec::with_capacity(base.len() + extension.len());

    for (idx, md) in base.iter().enumerate() {
        let name = md.name.to_string();
        by_name.insert(name, idx);
        result.push(md.clone());
    }

    for md in extension {
        let name = md.name.to_string();
        if let Some(&idx) = by_name.get(&name) {
            // Same-named mode: merge token definitions within
            let merged_tokens = merge_token_defs(&result[idx].token_defs, &md.token_defs, strategy);
            // L9-4: a merged mode is RAW if either contributor declared it raw
            // (same-named modes should agree; OR is the conservative union).
            let merged_raw = result[idx].raw || md.raw;
            result[idx] = ModeDef {
                name: md.name.clone(),
                token_defs: merged_tokens,
                raw: merged_raw,
            };
        } else {
            by_name.insert(name, result.len());
            result.push(md.clone());
        }
    }

    result
}

// ══════════════════════════════════════════════════════════════════════════════
// Composition application functions
// ══════════════════════════════════════════════════════════════════════════════

/// Apply `extends: [Base1, Base2]` — full language inheritance.
///
/// Uses `DuplicateStrategy::Error` because extends is additive-only.
/// Merges types, terms, equations, rewrites, and logic from each base.
pub fn apply_extends(def: &mut LanguageDef) -> Result<(), String> {
    let extends_names: Vec<Ident> = def.extends_names.clone();
    for base_name in &extends_names {
        let base_def =
            super::registry::lookup_language_def(&base_name.to_string()).ok_or_else(|| {
                format!(
                    "Language '{}' not found in registry. Was `language! {{ name: {} }}` \
                 defined in a module compiled before this one?",
                    base_name, base_name
                )
            })?;
        // Base is the inherited grammar; current def is the extension
        let merged =
            merge_language_defs(&base_def, def, DuplicateStrategy::Error).map_err(|errs| {
                errs.iter()
                    .map(|e| format!("  - {}", e))
                    .collect::<Vec<_>>()
                    .join("\n")
            })?;
        *def = merged;
    }
    Ok(())
}

/// Apply `includes: [Calc, BoolLogic]` — grammar-only import (types + terms).
///
/// Uses `DuplicateStrategy::Override` so local rules win over imported ones.
/// Strips equations, rewrites, and logic from the imported grammar.
pub fn apply_includes(def: &mut LanguageDef) -> Result<(), String> {
    let include_names: Vec<Ident> = def.include_names.clone();
    for name in &include_names {
        let mut imported =
            super::registry::lookup_language_def(&name.to_string()).ok_or_else(|| {
                format!(
                    "Language '{}' not found in registry. Was `language! {{ name: {} }}` \
                 defined in a module compiled before this one?",
                    name, name
                )
            })?;
        // Strip non-grammar components — import grammar only
        imported.equations.clear();
        imported.rewrites.clear();
        imported.logic = None;
        // Imported is base, current def is extension (local rules win)
        let merged =
            merge_language_defs(&imported, def, DuplicateStrategy::Override).map_err(|errs| {
                errs.iter()
                    .map(|e| format!("  - {}", e))
                    .collect::<Vec<_>>()
                    .join("\n")
            })?;
        *def = merged;
    }
    Ok(())
}

/// Apply `mixins: [ArithOps, BoolOps]` — fragment import (types + terms only).
///
/// Uses `DuplicateStrategy::Override` so local rules win over fragment rules.
/// Fragments only contain types + terms (no equations/rewrites/logic).
pub fn apply_mixins(def: &mut LanguageDef) -> Result<(), String> {
    let mixin_names: Vec<Ident> = def.mixin_names.clone();
    if mixin_names.is_empty() {
        return Ok(());
    }

    let local_def = def.clone();
    let mut merged_mixins: Option<LanguageDef> = None;

    for mixin_name in &mixin_names {
        let mixin_def =
            super::registry::lookup_language_def(&mixin_name.to_string()).ok_or_else(|| {
                format!(
                    "Fragment '{}' not found in registry. Was `language_fragment! {{ name: {} }}` \
                 defined in a module compiled before this one?",
                    mixin_name, mixin_name
                )
            })?;

        merged_mixins = Some(match merged_mixins {
            Some(accumulated) => {
                // Preserve declared mixin order: earlier mixins stay first,
                // later mixins override duplicate fragment definitions.
                merge_language_defs(&accumulated, &mixin_def, DuplicateStrategy::Override).map_err(
                    |errs| {
                        errs.iter()
                            .map(|e| format!("  - {}", e))
                            .collect::<Vec<_>>()
                            .join("\n")
                    },
                )?
            },
            None => mixin_def,
        });
    }

    if let Some(mixins_def) = merged_mixins {
        // Fragments are the base, local definition is the final extension so
        // user-written rules/options override fragment rules/options.
        let merged = merge_language_defs(&mixins_def, &local_def, DuplicateStrategy::Override)
            .map_err(|errs| {
                errs.iter()
                    .map(|e| format!("  - {}", e))
                    .collect::<Vec<_>>()
                    .join("\n")
            })?;
        *def = merged;
    }

    Ok(())
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::super::grammar::GrammarRule;
    use super::super::language::{AttributeValue, ConnectiveDecl, RelationDecl};
    use super::*;
    use proc_macro2::{Span, TokenStream};

    fn make_lang(name: &str) -> LanguageDef {
        LanguageDef {
            name: Ident::new(name, Span::call_site()),
            options: HashMap::new(),
            extends_names: Vec::new(),
            include_names: Vec::new(),
            mixin_names: Vec::new(),
            types: Vec::new(),
            refinement_types: Vec::new(),
            token_defs: Vec::new(),
            mode_defs: Vec::new(),
            sync_constraints: Vec::new(),
            tree_invariants: Vec::new(),
            terms: Vec::new(),
            equations: Vec::new(),
            rewrites: Vec::new(),
            logic: None,
            guard_config: None,
        }
    }

    fn make_type(name: &str) -> LangType {
        LangType {
            name: Ident::new(name, Span::call_site()),
            native_type: None,
            collection_kind: None,
        }
    }

    /// Merge tests care only about a rule's IDENTITY (label + category) — what merging
    /// collides on. Every other field takes its documented default from `rule_fixture`
    /// (`grammar.rs`), so this helper is exactly that constructor with `&str` spelling.
    fn make_rule(label: &str, category: &str) -> GrammarRule {
        crate::grammar::rule_fixture(
            Ident::new(label, Span::call_site()),
            Ident::new(category, Span::call_site()),
        )
    }

    #[test]
    fn merge_disjoint_categories() {
        let mut a = make_lang("A");
        a.types.push(make_type("Proc"));

        let mut b = make_lang("B");
        b.types.push(make_type("Name"));

        let result = merge_language_defs(&a, &b, DuplicateStrategy::Error)
            .expect("disjoint merge should succeed");
        assert_eq!(result.types.len(), 2);
        assert_eq!(result.types[0].name.to_string(), "Proc");
        assert_eq!(result.types[1].name.to_string(), "Name");
    }

    #[test]
    fn merge_shared_category_same_native() {
        let mut a = make_lang("A");
        a.types.push(make_type("Proc"));

        let mut b = make_lang("B");
        b.types.push(make_type("Proc")); // same name, same (no) native type

        let result = merge_language_defs(&a, &b, DuplicateStrategy::Error)
            .expect("same native type merge should succeed");
        assert_eq!(result.types.len(), 1); // deduplicated
        assert_eq!(result.types[0].name.to_string(), "Proc");
    }

    #[test]
    fn merge_shared_category_different_native_error() {
        let mut a = make_lang("A");
        a.types.push(LangType {
            name: Ident::new("Int", Span::call_site()),
            native_type: Some(syn::parse_quote!(i32)),
            collection_kind: None,
        });

        let mut b = make_lang("B");
        b.types.push(LangType {
            name: Ident::new("Int", Span::call_site()),
            native_type: Some(syn::parse_quote!(i64)),
            collection_kind: None,
        });

        let err = merge_language_defs(&a, &b, DuplicateStrategy::Error).unwrap_err();
        assert!(err
            .iter()
            .any(|e| matches!(e, MergeError::CategoryNativeTypeMismatch { .. })));
    }

    #[test]
    fn merge_duplicate_rule_label_error_strategy() {
        let mut a = make_lang("A");
        a.types.push(make_type("Proc"));
        a.terms.push(make_rule("PZero", "Proc"));

        let mut b = make_lang("B");
        b.types.push(make_type("Proc"));
        b.terms.push(make_rule("PZero", "Proc"));

        let err = merge_language_defs(&a, &b, DuplicateStrategy::Error).unwrap_err();
        assert!(err.iter().any(
            |e| matches!(e, MergeError::DuplicateRuleLabel { label, .. } if label == "PZero")
        ));
    }

    #[test]
    fn merge_duplicate_rule_label_override_strategy() {
        let mut a = make_lang("A");
        a.types.push(make_type("Proc"));
        a.terms.push(make_rule("PZero", "Proc"));

        let mut b = make_lang("B");
        b.types.push(make_type("Proc"));
        b.terms.push(make_rule("PZero", "Proc")); // should replace A's

        let result = merge_language_defs(&a, &b, DuplicateStrategy::Override)
            .expect("override should succeed");
        // Only one PZero rule (from B)
        let pzero_count = result.terms.iter().filter(|r| r.label == "PZero").count();
        assert_eq!(pzero_count, 1);
    }

    #[test]
    fn merge_terms_concatenated() {
        let mut a = make_lang("A");
        a.types.push(make_type("Proc"));
        a.terms.push(make_rule("PZero", "Proc"));

        let mut b = make_lang("B");
        b.types.push(make_type("Proc"));
        b.terms.push(make_rule("POutput", "Proc"));

        let result = merge_language_defs(&a, &b, DuplicateStrategy::Error)
            .expect("disjoint rules should merge");
        assert_eq!(result.terms.len(), 2);
    }

    #[test]
    fn merge_options_extension_overrides() {
        let mut a = make_lang("A");
        a.options
            .insert("beam_width".to_string(), AttributeValue::Float(1.5));

        let mut b = make_lang("B");
        b.options
            .insert("beam_width".to_string(), AttributeValue::Float(2.0));

        let result = merge_language_defs(&a, &b, DuplicateStrategy::Error)
            .expect("options merge should succeed");
        match result.options.get("beam_width") {
            Some(AttributeValue::Float(v)) => assert!((v - 2.0).abs() < f64::EPSILON),
            other => panic!("expected Float(2.0), got {:?}", other),
        }
    }

    #[test]
    fn merge_logic_blocks() {
        let mut a = make_lang("A");
        a.logic = Some(LogicBlock {
            relations: vec![RelationDecl {
                name: Ident::new("path", Span::call_site()),
                param_types: vec!["Proc".to_string(), "Proc".to_string()],
                doc_comment: None,
            }],
            content: quote::quote! { path(x, y) <-- edge(x, y); },
        });

        let mut b = make_lang("B");
        b.logic = Some(LogicBlock {
            relations: vec![RelationDecl {
                name: Ident::new("reachable", Span::call_site()),
                param_types: vec!["Name".to_string()],
                doc_comment: None,
            }],
            content: quote::quote! { reachable(n) <-- start(n); },
        });

        let result = merge_language_defs(&a, &b, DuplicateStrategy::Error)
            .expect("disjoint logic should merge");
        let logic = result.logic.expect("logic should be present");
        assert_eq!(logic.relations.len(), 2);
    }

    #[test]
    fn merge_conflicting_logic_relation_error() {
        let mut a = make_lang("A");
        a.logic = Some(LogicBlock {
            relations: vec![RelationDecl {
                name: Ident::new("path", Span::call_site()),
                param_types: vec!["Proc".to_string(), "Proc".to_string()],
                doc_comment: None,
            }],
            content: TokenStream::new(),
        });

        let mut b = make_lang("B");
        b.logic = Some(LogicBlock {
            relations: vec![RelationDecl {
                name: Ident::new("path", Span::call_site()),
                param_types: vec!["Name".to_string()], // different params
                doc_comment: None,
            }],
            content: TokenStream::new(),
        });

        let err = merge_language_defs(&a, &b, DuplicateStrategy::Error).unwrap_err();
        assert!(err
            .iter()
            .any(|e| matches!(e, MergeError::ConflictingLogicRelation { .. })));
    }

    #[test]
    fn merge_uses_extension_name() {
        let a = make_lang("Base");
        let b = make_lang("Extended");

        let result = merge_language_defs(&a, &b, DuplicateStrategy::Error)
            .expect("empty merge should succeed");
        assert_eq!(result.name.to_string(), "Extended");
    }

    #[test]
    fn merge_clears_composition_fields() {
        let mut a = make_lang("A");
        a.extends_names
            .push(Ident::new("SomeBase", Span::call_site()));

        let b = make_lang("B");

        let result =
            merge_language_defs(&a, &b, DuplicateStrategy::Error).expect("merge should succeed");
        assert!(result.extends_names.is_empty());
        assert!(result.include_names.is_empty());
        assert!(result.mixin_names.is_empty());
    }

    #[test]
    fn apply_mixins_preserves_declared_type_order_and_local_override() {
        super::super::registry::register_fragment(
            "OrderFragInt",
            &quote::quote! {
                name: OrderFragInt,
                types {
                    ![i32] as Int
                },
                terms {
                    AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
                    Shared . a:Int |- a : Int;
                }
            },
        )
        .expect("OrderFragInt is registered once");
        super::super::registry::register_fragment(
            "OrderFragBool",
            &quote::quote! {
                name: OrderFragBool,
                types {
                    ![bool] as Bool
                },
                terms {
                    Not . a:Bool |- "not" a : Bool ![!a] step;
                    Shared . b:Bool |- b : Bool;
                }
            },
        )
        .expect("OrderFragBool is registered once");

        let mut def = make_lang("MixedOrder");
        def.mixin_names
            .push(Ident::new("OrderFragInt", Span::call_site()));
        def.mixin_names
            .push(Ident::new("OrderFragBool", Span::call_site()));
        def.terms.push(make_rule("Shared", "Int"));

        apply_mixins(&mut def).expect("mixins should apply");

        let type_names: Vec<String> = def.types.iter().map(|ty| ty.name.to_string()).collect();
        assert_eq!(type_names, vec!["Int".to_string(), "Bool".to_string()]);
        assert!(def.mixin_names.is_empty());

        let shared: Vec<&GrammarRule> = def
            .terms
            .iter()
            .filter(|rule| rule.label == "Shared")
            .collect();
        assert_eq!(shared.len(), 1);
        assert_eq!(shared[0].category.to_string(), "Int");
    }

    // ══════════════════════════════════════════════════════════════════════════
    // Phase 3: Guard configuration merge tests (design doc §2A)
    // ══════════════════════════════════════════════════════════════════════════

    use super::super::language::{
        ChannelConfig, ChannelDecl, ChannelParam, ConnectiveRole, GuardConfig, JoinPatternDecl,
        ParamType, PredicateParam,
    };

    fn make_pred(
        name: &str,
        arity: usize,
        sel: Option<f64>,
        cost: Option<u32>,
    ) -> BuiltinPredicate {
        let params = (0..arity)
            .map(|i| PredicateParam {
                name: Ident::new(&format!("p{}", i), Span::call_site()),
                ty: None,
                quantifier: None,
            })
            .collect();
        BuiltinPredicate {
            name: Ident::new(name, Span::call_site()),
            params,
            syntax_forms: Vec::new(),
            annotations: PredicateAnnotations { selectivity: sel, cost },
        }
    }

    fn make_theory(name: &str, theory_type_str: &str) -> TheoryRegistration {
        TheoryRegistration {
            name: Ident::new(name, Span::call_site()),
            theory_type: syn::parse_str(theory_type_str).expect("valid type"),
            handled_types: None,
        }
    }

    #[test]
    fn merge_guard_config_both_none() {
        let mut errors: Vec<MergeError> = Vec::new();
        let result = merge_guard_config(&None, &None, &mut errors);
        assert!(result.is_none());
        assert!(errors.is_empty());
    }

    #[test]
    fn merge_guard_config_base_only() {
        let base = Some(GuardConfig {
            builtin_predicates: Some(vec![make_pred("eq", 2, Some(0.1), Some(2))]),
            connectives: None,
            theories: vec![],
            channels: None,
            guard_slots: Vec::new(),
        });
        let mut errors = Vec::new();
        let result = merge_guard_config(&base, &None, &mut errors).expect("Some");
        assert_eq!(result.builtin_predicates.as_ref().expect("present").len(), 1);
    }

    #[test]
    fn merge_guard_config_predicate_union() {
        let base = Some(GuardConfig {
            builtin_predicates: Some(vec![
                make_pred("eq", 2, Some(0.1), Some(2)),
                make_pred("gt", 2, Some(0.5), Some(2)),
            ]),
            connectives: None,
            theories: vec![],
            channels: None,
            guard_slots: Vec::new(),
        });
        let extension = Some(GuardConfig {
            builtin_predicates: Some(vec![
                make_pred("lt", 2, Some(0.5), None), // new predicate
            ]),
            connectives: None,
            theories: vec![],
            channels: None,
            guard_slots: Vec::new(),
        });
        let mut errors = Vec::new();
        let result = merge_guard_config(&base, &extension, &mut errors).expect("Some");
        assert!(errors.is_empty());
        let preds = result.builtin_predicates.as_ref().expect("present");
        assert_eq!(preds.len(), 3);
        let names: Vec<String> = preds.iter().map(|p| p.name.to_string()).collect();
        assert!(names.contains(&"eq".to_string()));
        assert!(names.contains(&"gt".to_string()));
        assert!(names.contains(&"lt".to_string()));
    }

    #[test]
    fn merge_guard_config_annotation_override() {
        // Base: gt @[selectivity(0.5), cost(2)]
        // Extension: gt @[selectivity(0.7)]  (cost omitted → inherited)
        let base = Some(GuardConfig {
            builtin_predicates: Some(vec![make_pred("gt", 2, Some(0.5), Some(2))]),
            connectives: None,
            theories: vec![],
            channels: None,
            guard_slots: Vec::new(),
        });
        let extension = Some(GuardConfig {
            builtin_predicates: Some(vec![make_pred("gt", 2, Some(0.7), None)]),
            connectives: None,
            theories: vec![],
            channels: None,
            guard_slots: Vec::new(),
        });
        let mut errors = Vec::new();
        let result = merge_guard_config(&base, &extension, &mut errors).expect("Some");
        assert!(errors.is_empty());
        let preds = result.builtin_predicates.as_ref().expect("present");
        assert_eq!(preds.len(), 1);
        assert_eq!(preds[0].annotations.selectivity, Some(0.7), "extension wins");
        assert_eq!(preds[0].annotations.cost, Some(2), "base inherited");
    }

    #[test]
    fn merge_guard_config_predicate_arity_conflict() {
        let base = Some(GuardConfig {
            builtin_predicates: Some(vec![make_pred("eq", 2, None, None)]),
            connectives: None,
            theories: vec![],
            channels: None,
            guard_slots: Vec::new(),
        });
        let extension = Some(GuardConfig {
            builtin_predicates: Some(vec![make_pred("eq", 3, None, None)]),
            connectives: None,
            theories: vec![],
            channels: None,
            guard_slots: Vec::new(),
        });
        let mut errors = Vec::new();
        let _ = merge_guard_config(&base, &extension, &mut errors);
        assert_eq!(errors.len(), 1);
        match &errors[0] {
            MergeError::DuplicatePredicateName { name, arity_a, arity_b } => {
                assert_eq!(name, "eq");
                assert_eq!(*arity_a, 2);
                assert_eq!(*arity_b, 3);
            },
            other => panic!("expected DuplicatePredicateName, got {:?}", other),
        }
    }

    #[test]
    fn merge_guard_config_connective_replacement() {
        let base = Some(GuardConfig {
            builtin_predicates: None,
            connectives: Some(vec![
                ConnectiveDecl {
                    role: ConnectiveRole::And,
                    keywords: vec!["and".into(), "∧".into()],
                },
                ConnectiveDecl {
                    role: ConnectiveRole::Or,
                    keywords: vec!["or".into(), "∨".into()],
                },
                ConnectiveDecl {
                    role: ConnectiveRole::Not,
                    keywords: vec!["not".into(), "¬".into()],
                },
            ]),
            theories: vec![],
            channels: None,
            guard_slots: Vec::new(),
        });
        let extension = Some(GuardConfig {
            builtin_predicates: None,
            connectives: Some(vec![
                ConnectiveDecl {
                    role: ConnectiveRole::And,
                    keywords: vec!["&&".into()],
                },
                ConnectiveDecl {
                    role: ConnectiveRole::Not,
                    keywords: vec!["~".into()],
                },
            ]),
            theories: vec![],
            channels: None,
            guard_slots: Vec::new(),
        });
        let mut errors = Vec::new();
        let result = merge_guard_config(&base, &extension, &mut errors).expect("Some");
        assert!(errors.is_empty());
        // Extension replaces base entirely — only `&&` and `~` remain.
        let conns = result.connectives.as_ref().expect("present");
        assert_eq!(conns.len(), 2, "extension fully replaces base connectives");
        // Verify the base's `or` is GONE.
        assert!(!conns.iter().any(|c| matches!(c.role, ConnectiveRole::Or)));
        // Verify the extension's `and` keyword is `&&`, not `and`.
        let and = conns
            .iter()
            .find(|c| c.role == ConnectiveRole::And)
            .expect("present");
        assert_eq!(and.keywords, vec!["&&".to_string()]);
    }

    #[test]
    fn merge_guard_config_theory_union() {
        let base = Some(GuardConfig {
            builtin_predicates: None,
            connectives: None,
            theories: vec![make_theory("arithmetic", "PresburgerAlgebra")],
            channels: None,
            guard_slots: Vec::new(),
        });
        let extension = Some(GuardConfig {
            builtin_predicates: None,
            connectives: None,
            theories: vec![make_theory("patterns", "UnificationTheory")],
            channels: None,
            guard_slots: Vec::new(),
        });
        let mut errors = Vec::new();
        let result = merge_guard_config(&base, &extension, &mut errors).expect("Some");
        assert!(errors.is_empty());
        assert_eq!(result.theories.len(), 2);
    }

    #[test]
    fn merge_guard_config_theory_conflict() {
        let base = Some(GuardConfig {
            builtin_predicates: None,
            connectives: None,
            theories: vec![make_theory("arithmetic", "PresburgerAlgebra")],
            channels: None,
            guard_slots: Vec::new(),
        });
        let extension = Some(GuardConfig {
            builtin_predicates: None,
            connectives: None,
            theories: vec![make_theory("arithmetic", "FloatTheory")], // different type!
            channels: None,
            guard_slots: Vec::new(),
        });
        let mut errors = Vec::new();
        let _ = merge_guard_config(&base, &extension, &mut errors);
        assert_eq!(errors.len(), 1);
        match &errors[0] {
            MergeError::ConflictingTheoryRegistration { name, .. } => {
                assert_eq!(name, "arithmetic");
            },
            other => panic!("expected ConflictingTheoryRegistration, got {:?}", other),
        }
    }

    #[test]
    fn merge_guard_config_channel_replacement() {
        let base = Some(GuardConfig {
            builtin_predicates: None,
            connectives: None,
            theories: vec![],
            channels: Some(ChannelConfig {
                channel_categories: vec![ChannelDecl {
                    category: Ident::new("Name", Span::call_site()),
                }],
                join_patterns: vec![JoinPatternDecl {
                    label: Ident::new("PGuardedInput", Span::call_site()),
                    channel_params: vec![ChannelParam {
                        param_name: Ident::new("ch", Span::call_site()),
                        category: Ident::new("Name", Span::call_site()),
                    }],
                }],
            }),
            guard_slots: Vec::new(),
        });
        let extension = Some(GuardConfig {
            builtin_predicates: None,
            connectives: None,
            theories: vec![],
            channels: Some(ChannelConfig {
                channel_categories: vec![ChannelDecl {
                    category: Ident::new("Place", Span::call_site()),
                }],
                join_patterns: vec![],
            }),
            guard_slots: Vec::new(),
        });
        let mut errors = Vec::new();
        let result = merge_guard_config(&base, &extension, &mut errors).expect("Some");
        assert!(errors.is_empty());
        let ch = result.channels.as_ref().expect("present");
        assert_eq!(ch.channel_categories.len(), 1);
        assert_eq!(ch.channel_categories[0].category.to_string(), "Place");
        assert!(ch.join_patterns.is_empty(), "extension fully replaces");
    }

    // Suppress dead code warning for the unused import — the helper test
    // uses several but not all of the imported types.
    #[allow(dead_code)]
    fn _use_param_type() -> ParamType {
        ParamType::Single(Ident::new("Int", Span::call_site()))
    }
}
