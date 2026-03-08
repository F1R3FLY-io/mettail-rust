//! Theory morphisms for cross-theory translation and proof transfer.
//!
//! A theory morphism is a structure-preserving map between two formal theories.
//! Given theories `T₁` and `T₂` with their respective sorts, operations, and
//! axioms, a morphism `φ: T₁ → T₂` maps sorts to sorts, operations to
//! operations, and preserves the axioms (every axiom of `T₁` becomes a theorem
//! of `T₂` under translation). This enables:
//! - **Proof transfer**: a theorem proved in `T₁` can be transferred to `T₂`
//! - **Module composition**: building complex theories from simpler ones
//! - **Refinement**: verifying that an implementation satisfies a specification
//!
//! ## Theoretical Foundations
//!
//! - **Goguen & Burstall (1992)** — "Institutions: abstract model theory for
//!   specification and programming." Introduces institutions as a framework
//!   for abstract model theory, with morphisms as the structure-preserving maps.
//! - **Mossakowski (2005)** — "Heterogeneous specification and the heterogeneous
//!   tool set." Shows how theory morphisms enable composition of specifications
//!   written in different logics.
//! - **Rabe & Kohlhase (2013)** — "A scalable module system." Practical module
//!   systems based on theory morphisms for the Mmt framework.
//! - **Farmer (2000)** — "An infrastructure for intertheory reasoning." Theory
//!   morphisms for cross-theory reasoning in IMPS.
//!
//! ## Architecture
//!
//! ```text
//! Theory T₁ (source)          Theory T₂ (target)
//!       │                           │
//!       └──→ construct_morphism() ──┘
//!                    │
//!                    ▼
//!            TheoryMorphism
//!                    │
//!      ┌─────────────┼───────────────┐
//!      │             │               │
//!      ▼             ▼               ▼
//! translate_term() verify_       cross-theory
//!                  preservation() reasoning
//! ```
//!
//! ## PraTTaIL Integration
//!
//! Theory morphisms enable cross-grammar translation in PraTTaIL. When two
//! grammars share structural similarities (e.g., a source language and its
//! desugared form), a morphism maps constructors and sorts between them.
//! This supports:
//! - Verified desugaring: proving that desugaring preserves semantics
//! - Grammar embedding: showing one grammar is a sub-grammar of another
//! - AST migration: translating parse trees between grammar versions

use std::collections::HashMap;
use std::fmt;

use crate::repair::{RepairAction, RepairKind, RepairSet, RepairSuggestion};

// ══════════════════════════════════════════════════════════════════════════════
// Core types
// ══════════════════════════════════════════════════════════════════════════════

/// A sort (type) in a theory.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Sort {
    /// Sort name (e.g., "Expr", "Type", "Nat").
    pub name: String,
}

impl Sort {
    /// Create a new sort.
    pub fn new(name: impl Into<String>) -> Self {
        Sort { name: name.into() }
    }
}

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

/// An operation (function symbol) in a theory.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Operation {
    /// Operation name (e.g., "Add", "Zero", "Succ").
    pub name: String,
    /// Argument sorts.
    pub arg_sorts: Vec<String>,
    /// Result sort.
    pub result_sort: String,
}

impl Operation {
    /// Create a constant (nullary operation).
    pub fn constant(name: impl Into<String>, sort: impl Into<String>) -> Self {
        Operation {
            name: name.into(),
            arg_sorts: Vec::new(),
            result_sort: sort.into(),
        }
    }

    /// Create an operation with arguments.
    pub fn new(
        name: impl Into<String>,
        args: Vec<String>,
        result: impl Into<String>,
    ) -> Self {
        Operation {
            name: name.into(),
            arg_sorts: args,
            result_sort: result.into(),
        }
    }

    /// Arity of the operation.
    pub fn arity(&self) -> usize {
        self.arg_sorts.len()
    }
}

impl fmt::Display for Operation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.arg_sorts.is_empty() {
            write!(f, "{}: {}", self.name, self.result_sort)
        } else {
            write!(
                f,
                "{}: {} -> {}",
                self.name,
                self.arg_sorts.join(" x "),
                self.result_sort,
            )
        }
    }
}

/// A case in the translation map of a theory morphism.
///
/// Specifies how a source operation is translated to a target term pattern.
/// Simple cases map one operation to another; complex cases involve
/// term-building (e.g., desugaring `if-then-else` to `case` + `bool`).
#[derive(Debug, Clone)]
pub enum TranslationCase {
    /// Direct mapping: source operation maps to a single target operation.
    Direct {
        /// Target operation name.
        target_op: String,
    },
    /// Compound mapping: source operation maps to a term built from
    /// multiple target operations.
    Compound {
        /// Description of the translation (for diagnostics).
        description: String,
        /// Target term template as a string expression.
        template: String,
    },
    /// Identity: the operation is preserved unchanged.
    Identity,
}

impl fmt::Display for TranslationCase {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TranslationCase::Direct { target_op } => write!(f, "-> {}", target_op),
            TranslationCase::Compound { description, .. } => {
                write!(f, "-> [{}]", description)
            }
            TranslationCase::Identity => write!(f, "-> (identity)"),
        }
    }
}

/// A theory morphism `phi: T_source -> T_target`.
///
/// Maps sorts to sorts and operations to operations/term patterns, preserving
/// the axioms of the source theory.
#[derive(Debug, Clone)]
pub struct TheoryMorphism {
    /// Name of the morphism (for diagnostics).
    pub name: String,
    /// Source theory name.
    pub source_theory: String,
    /// Target theory name.
    pub target_theory: String,
    /// Sort mapping: source sort name -> target sort name.
    pub sort_map: HashMap<String, String>,
    /// Operation mapping: source operation name -> translation case.
    pub operation_map: HashMap<String, TranslationCase>,
    /// Source sorts.
    pub source_sorts: Vec<Sort>,
    /// Target sorts.
    pub target_sorts: Vec<Sort>,
    /// Source operations.
    pub source_operations: Vec<Operation>,
    /// Target operations.
    pub target_operations: Vec<Operation>,
}

impl TheoryMorphism {
    /// Create a new theory morphism.
    pub fn new(
        name: impl Into<String>,
        source: impl Into<String>,
        target: impl Into<String>,
    ) -> Self {
        TheoryMorphism {
            name: name.into(),
            source_theory: source.into(),
            target_theory: target.into(),
            sort_map: HashMap::new(),
            operation_map: HashMap::new(),
            source_sorts: Vec::new(),
            target_sorts: Vec::new(),
            source_operations: Vec::new(),
            target_operations: Vec::new(),
        }
    }

    /// Add a sort mapping.
    pub fn map_sort(&mut self, source: impl Into<String>, target: impl Into<String>) {
        self.sort_map.insert(source.into(), target.into());
    }

    /// Add a direct operation mapping.
    pub fn map_operation(&mut self, source: impl Into<String>, target: impl Into<String>) {
        self.operation_map.insert(
            source.into(),
            TranslationCase::Direct {
                target_op: target.into(),
            },
        );
    }

    /// Add an identity operation mapping.
    pub fn map_identity(&mut self, operation: impl Into<String>) {
        self.operation_map
            .insert(operation.into(), TranslationCase::Identity);
    }

    /// Add a compound operation mapping.
    pub fn map_compound(
        &mut self,
        source: impl Into<String>,
        description: impl Into<String>,
        template: impl Into<String>,
    ) {
        self.operation_map.insert(
            source.into(),
            TranslationCase::Compound {
                description: description.into(),
                template: template.into(),
            },
        );
    }

    /// Check whether all source sorts are mapped.
    pub fn is_sort_complete(&self) -> bool {
        self.source_sorts.iter().all(|s| self.sort_map.contains_key(&s.name))
    }

    /// Check whether all source operations are mapped.
    pub fn is_operation_complete(&self) -> bool {
        self.source_operations
            .iter()
            .all(|op| self.operation_map.contains_key(&op.name))
    }
}

impl fmt::Display for TheoryMorphism {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Morphism {} : {} -> {} (sorts: {}, ops: {})",
            self.name,
            self.source_theory,
            self.target_theory,
            self.sort_map.len(),
            self.operation_map.len(),
        )
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Core functions
// ══════════════════════════════════════════════════════════════════════════════

/// Construct a theory morphism from sort and operation mappings.
///
/// Validates that:
/// - All mapped source sorts exist in the source theory
/// - All mapped target sorts exist in the target theory
/// - Operation arities are preserved by the mapping
///
/// # Arguments
///
/// * `name` - Name of the morphism.
/// * `source_sorts` - Sorts of the source theory.
/// * `target_sorts` - Sorts of the target theory.
/// * `source_ops` - Operations of the source theory.
/// * `target_ops` - Operations of the target theory.
/// * `sort_map` - Sort translation map.
/// * `op_map` - Operation translation map.
///
/// # Returns
///
/// A validated `TheoryMorphism`, or an error if validation fails.
pub fn construct_morphism(
    name: &str,
    source_sorts: Vec<Sort>,
    target_sorts: Vec<Sort>,
    source_ops: Vec<Operation>,
    target_ops: Vec<Operation>,
    sort_map: HashMap<String, String>,
    op_map: HashMap<String, TranslationCase>,
) -> Result<TheoryMorphism, String> {
    let target_sort_names: std::collections::HashSet<&str> =
        target_sorts.iter().map(|s| s.name.as_str()).collect();
    let target_ops_by_name: HashMap<&str, &Operation> =
        target_ops.iter().map(|op| (op.name.as_str(), op)).collect();

    // (1) Every source sort must map to a target sort.
    for src_sort in &source_sorts {
        match sort_map.get(&src_sort.name) {
            None => {
                return Err(format!(
                    "Source sort '{}' has no mapping in the sort map",
                    src_sort.name,
                ));
            }
            Some(tgt_name) => {
                if !target_sort_names.contains(tgt_name.as_str()) {
                    return Err(format!(
                        "Sort map maps '{}' to '{}', but '{}' is not a target sort",
                        src_sort.name, tgt_name, tgt_name,
                    ));
                }
            }
        }
    }

    // (2) Every source operation must map to a target operation.
    for src_op in &source_ops {
        match op_map.get(&src_op.name) {
            None => {
                return Err(format!(
                    "Source operation '{}' has no mapping in the operation map",
                    src_op.name,
                ));
            }
            Some(translation) => {
                // (3) Arity preservation: for Direct mappings, check that the
                // target operation has the same number of argument sorts.
                if let TranslationCase::Direct { target_op } = translation {
                    match target_ops_by_name.get(target_op.as_str()) {
                        None => {
                            return Err(format!(
                                "Operation map maps '{}' to '{}', but '{}' is not a target operation",
                                src_op.name, target_op, target_op,
                            ));
                        }
                        Some(tgt_op) => {
                            if src_op.arity() != tgt_op.arity() {
                                return Err(format!(
                                    "Arity mismatch: source '{}' has arity {} but target '{}' has arity {}",
                                    src_op.name, src_op.arity(), tgt_op.name, tgt_op.arity(),
                                ));
                            }
                        }
                    }
                }
            }
        }
    }

    // (4) Translation cases must cover all source operations (already checked
    // in step 2 above).

    let mut morphism = TheoryMorphism::new(name, "source", "target");
    morphism.source_sorts = source_sorts;
    morphism.target_sorts = target_sorts;
    morphism.source_operations = source_ops;
    morphism.target_operations = target_ops;
    morphism.sort_map = sort_map;
    morphism.operation_map = op_map;

    Ok(morphism)
}

/// Verify that a theory morphism preserves axioms.
///
/// For each axiom `A` of the source theory, checks that `phi(A)` is a theorem
/// of the target theory. This is the fundamental correctness property of a
/// theory morphism.
///
/// # Arguments
///
/// * `morphism` - The theory morphism to verify.
/// * `source_axioms` - Axioms of the source theory (as string representations).
///
/// # Returns
///
/// `true` if all axioms are preserved, `false` if any axiom's translation
/// is not valid in the target theory.
/// Verify that the morphism preserves axioms.
///
/// Axioms are expressed as term pairs encoded in a single string with `" = "`
/// separating the left-hand side from the right-hand side
/// (e.g., `"Add(Zero, x) = x"`). For each axiom, both sides are translated
/// through the morphism's operation map and checked for syntactic equality in
/// the target theory.
///
/// Returns `true` if every translated axiom pair is syntactically equal.
pub fn verify_preservation(
    morphism: &TheoryMorphism,
    source_axioms: &[String],
) -> bool {
    for axiom in source_axioms {
        // Split on " = " to get lhs and rhs of the equation.
        let parts: Vec<&str> = axiom.splitn(2, " = ").collect();
        if parts.len() != 2 {
            // Malformed axiom — cannot verify; treat as not preserved.
            return false;
        }
        let lhs = parts[0].trim();
        let rhs = parts[1].trim();

        let translated_lhs = match translate_term(morphism, lhs) {
            Ok(t) => t,
            Err(_) => return false,
        };
        let translated_rhs = match translate_term(morphism, rhs) {
            Ok(t) => t,
            Err(_) => return false,
        };

        if translated_lhs != translated_rhs {
            return false;
        }
    }
    true
}

/// Translate a term from the source theory to the target theory.
///
/// Applies the morphism's sort and operation maps to transform a source
/// term into a target term. Compound translations may expand a single
/// source operation into a complex target term.
///
/// # Arguments
///
/// * `morphism` - The theory morphism.
/// * `term` - The source term as `(operation, args)` recursive structure.
///
/// # Returns
///
/// The translated term as a string representation, or an error if the
/// term contains unmapped operations.
/// Recursively translate a term from the source theory to the target theory.
///
/// Terms are represented as strings with the syntax `Op(arg1, arg2, ...)`
/// for applications, or bare identifiers for constants/variables. The function
/// parses the term structure, looks up each operation in the morphism's
/// operation map, and recursively translates the arguments.
///
/// Variables (lowercase identifiers not in the operation map) are passed
/// through unchanged.
pub fn translate_term(
    morphism: &TheoryMorphism,
    term: &str,
) -> Result<String, String> {
    let term = term.trim();
    if term.is_empty() {
        return Err("Empty term".to_string());
    }

    // Check if the term is of the form `Op(arg1, arg2, ...)`.
    if let Some(paren_pos) = term.find('(') {
        // Ensure the term ends with ')'.
        if !term.ends_with(')') {
            return Err(format!("Malformed term: '{}'", term));
        }

        let op_name = &term[..paren_pos];
        let args_str = &term[paren_pos + 1..term.len() - 1];

        // Parse the comma-separated arguments, respecting nested parentheses.
        let args = split_args(args_str);

        // Recursively translate each argument.
        let translated_args: Result<Vec<String>, String> = args
            .iter()
            .map(|arg| translate_term(morphism, arg))
            .collect();
        let translated_args = translated_args?;

        // Look up the operation in the morphism's operation map.
        match morphism.operation_map.get(op_name) {
            Some(TranslationCase::Direct { target_op }) => {
                if translated_args.is_empty() {
                    Ok(format!("{}()", target_op))
                } else {
                    Ok(format!("{}({})", target_op, translated_args.join(", ")))
                }
            }
            Some(TranslationCase::Identity) => {
                if translated_args.is_empty() {
                    Ok(format!("{}()", op_name))
                } else {
                    Ok(format!("{}({})", op_name, translated_args.join(", ")))
                }
            }
            Some(TranslationCase::Compound { template, .. }) => {
                // Substitute $1, $2, etc. with the translated arguments.
                let mut result = template.clone();
                for (i, arg) in translated_args.iter().enumerate() {
                    let placeholder = format!("${}", i + 1);
                    result = result.replace(&placeholder, arg);
                }
                Ok(result)
            }
            None => {
                // Not in the operation map — pass through as-is (e.g., a
                // variable or an operation from the target theory).
                if translated_args.is_empty() {
                    Ok(format!("{}()", op_name))
                } else {
                    Ok(format!("{}({})", op_name, translated_args.join(", ")))
                }
            }
        }
    } else {
        // Bare identifier (constant or variable).
        // Check if it is a nullary operation in the map.
        match morphism.operation_map.get(term) {
            Some(TranslationCase::Direct { target_op }) => Ok(target_op.clone()),
            Some(TranslationCase::Identity) => Ok(term.to_string()),
            Some(TranslationCase::Compound { template, .. }) => Ok(template.clone()),
            None => {
                // Variable or unmapped constant — pass through unchanged.
                Ok(term.to_string())
            }
        }
    }
}

/// Split a comma-separated argument list, respecting nested parentheses.
fn split_args(s: &str) -> Vec<String> {
    let mut args = Vec::new();
    let mut depth = 0usize;
    let mut start = 0;

    for (i, ch) in s.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => {
                depth = depth.saturating_sub(1);
            }
            ',' if depth == 0 => {
                args.push(s[start..i].trim().to_string());
                start = i + 1;
            }
            _ => {}
        }
    }

    let last = s[start..].trim();
    if !last.is_empty() {
        args.push(last.to_string());
    }

    args
}

// ══════════════════════════════════════════════════════════════════════════════
// Gap detection and completion suggestions
// ══════════════════════════════════════════════════════════════════════════════

/// Classification of a gap in a theory morphism.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GapKind {
    /// A source sort has no mapping to a target sort.
    MissingSort,
    /// A source operation has no mapping in the operation map.
    MissingOperation,
    /// An axiom's translation fails to hold in the target theory.
    FailedPreservation,
}

impl fmt::Display for GapKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GapKind::MissingSort => write!(f, "MissingSort"),
            GapKind::MissingOperation => write!(f, "MissingOperation"),
            GapKind::FailedPreservation => write!(f, "FailedPreservation"),
        }
    }
}

/// A gap (incompleteness) detected in a theory morphism.
///
/// Gaps indicate places where the morphism fails to be total or fails to
/// preserve structure.  Each gap carries enough information for
/// [`suggest_morphism_completion`] to synthesise a concrete repair.
#[derive(Debug, Clone)]
pub struct MorphismGap {
    /// What kind of gap this is.
    pub kind: GapKind,
    /// The sort or operation name in the source theory that is unmapped or
    /// whose preservation failed.
    pub source_name: String,
    /// Human-readable description of the gap.
    pub description: String,
}

impl fmt::Display for MorphismGap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}] {}: {}", self.kind, self.source_name, self.description)
    }
}

/// Detect gaps in a theory morphism.
///
/// A *gap* is any place where the morphism is incomplete or fails to preserve
/// structure:
///
/// 1. **Missing sort** — a source sort with no entry in `sort_map`.
/// 2. **Missing operation** — a source operation with no entry in
///    `operation_map`.
/// 3. **Failed preservation** — an axiom whose translation does not hold
///    syntactically in the target theory.  To check this the caller must
///    supply `axioms`; when no axioms are provided only sorts and operations
///    are checked.
///
/// # Arguments
///
/// * `morphism` — the morphism to inspect.
/// * `axioms`  — optional slice of source-theory axioms expressed as
///   `"lhs = rhs"` strings (same format accepted by
///   [`verify_preservation`]).
///
/// # Returns
///
/// A (possibly empty) vector of [`MorphismGap`]s, one per detected gap.
pub fn detect_gaps(
    morphism: &TheoryMorphism,
    axioms: Option<&[String]>,
) -> Vec<MorphismGap> {
    let mut gaps = Vec::new();

    // (1) Missing sort mappings.
    for sort in &morphism.source_sorts {
        if !morphism.sort_map.contains_key(&sort.name) {
            gaps.push(MorphismGap {
                kind: GapKind::MissingSort,
                source_name: sort.name.clone(),
                description: format!(
                    "Source sort '{}' has no mapping to a target sort",
                    sort.name,
                ),
            });
        }
    }

    // (2) Missing operation mappings.
    for op in &morphism.source_operations {
        if !morphism.operation_map.contains_key(&op.name) {
            gaps.push(MorphismGap {
                kind: GapKind::MissingOperation,
                source_name: op.name.clone(),
                description: format!(
                    "Source operation '{}' ({}) has no translation case",
                    op.name, op,
                ),
            });
        }
    }

    // (3) Preservation failures.
    if let Some(axioms) = axioms {
        for axiom in axioms {
            let parts: Vec<&str> = axiom.splitn(2, " = ").collect();
            if parts.len() != 2 {
                gaps.push(MorphismGap {
                    kind: GapKind::FailedPreservation,
                    source_name: axiom.clone(),
                    description: format!(
                        "Malformed axiom '{}' — expected 'lhs = rhs' form",
                        axiom,
                    ),
                });
                continue;
            }
            let lhs = parts[0].trim();
            let rhs = parts[1].trim();

            let translated_lhs = translate_term(morphism, lhs);
            let translated_rhs = translate_term(morphism, rhs);

            match (translated_lhs, translated_rhs) {
                (Ok(tl), Ok(tr)) if tl == tr => {
                    // Axiom is preserved — no gap.
                }
                (Ok(tl), Ok(tr)) => {
                    gaps.push(MorphismGap {
                        kind: GapKind::FailedPreservation,
                        source_name: axiom.clone(),
                        description: format!(
                            "Axiom '{}' translates to '{} = {}' which does not hold",
                            axiom, tl, tr,
                        ),
                    });
                }
                (Err(e), _) | (_, Err(e)) => {
                    gaps.push(MorphismGap {
                        kind: GapKind::FailedPreservation,
                        source_name: axiom.clone(),
                        description: format!(
                            "Axiom '{}' cannot be translated: {}",
                            axiom, e,
                        ),
                    });
                }
            }
        }
    }

    gaps
}

/// Generate repair suggestions that would close the gaps in a morphism.
///
/// For each gap returned by [`detect_gaps`]:
///
/// * **MissingSort** — suggest adding a sort mapping.  If the target theory
///   contains a sort with the same name it is proposed as the target;
///   otherwise the suggestion uses a placeholder.
/// * **MissingOperation** — suggest adding an operation mapping.  Candidate
///   target operations are selected by matching arity; when no arity-
///   compatible candidate exists a `Description` action is emitted instead.
/// * **FailedPreservation** — suggest adding the translated equation to the
///   target theory as a new axiom.
///
/// Every suggestion uses [`RepairKind::CompleteMorphism`].
pub fn suggest_morphism_completion(
    gaps: &[MorphismGap],
    morphism: &TheoryMorphism,
) -> RepairSet {
    let mut repairs = RepairSet::new();

    for gap in gaps {
        match gap.kind {
            GapKind::MissingSort => {
                // Look for a target sort with the same name.
                let candidate = morphism
                    .target_sorts
                    .iter()
                    .find(|s| s.name == gap.source_name)
                    .map(|s| s.name.clone());

                let (description, action, confidence) = match candidate {
                    Some(ref tgt_name) => (
                        format!(
                            "Map source sort '{}' to target sort '{}'",
                            gap.source_name, tgt_name,
                        ),
                        RepairAction::Description(format!(
                            "sort_map.insert(\"{}\".into(), \"{}\".into());",
                            gap.source_name, tgt_name,
                        )),
                        0.9,
                    ),
                    None => (
                        format!(
                            "Map source sort '{}' to a target sort (no same-name candidate found)",
                            gap.source_name,
                        ),
                        RepairAction::Description(format!(
                            "sort_map.insert(\"{}\".into(), \"<TARGET_SORT>\".into());",
                            gap.source_name,
                        )),
                        0.5,
                    ),
                };

                repairs.add(
                    RepairSuggestion::new(
                        RepairKind::CompleteMorphism,
                        description,
                        action,
                    )
                    .with_confidence(confidence)
                    .with_edit_cost(1),
                );
            }

            GapKind::MissingOperation => {
                // Find the source operation to know its arity.
                let source_op = morphism
                    .source_operations
                    .iter()
                    .find(|op| op.name == gap.source_name);

                let arity = source_op.map_or(0, |op| op.arity());

                // Find target operations with matching arity.
                let candidates: Vec<&Operation> = morphism
                    .target_operations
                    .iter()
                    .filter(|op| op.arity() == arity)
                    .collect();

                if candidates.is_empty() {
                    repairs.add(
                        RepairSuggestion::new(
                            RepairKind::CompleteMorphism,
                            format!(
                                "Add translation for source operation '{}' (arity {}) \
                                 — no arity-matching target operation found",
                                gap.source_name, arity,
                            ),
                            RepairAction::Description(format!(
                                "operation_map.insert(\"{}\".into(), \
                                 TranslationCase::Direct {{ target_op: \"<TARGET_OP>\".into() }});",
                                gap.source_name,
                            )),
                        )
                        .with_confidence(0.3)
                        .with_edit_cost(2),
                    );
                } else {
                    // When multiple candidates exist, report
                    // `alternative_count` so the caller knows there are
                    // choices.
                    let alt_count = candidates.len() as u64;
                    let best = candidates[0];
                    repairs.add(
                        RepairSuggestion::new(
                            RepairKind::CompleteMorphism,
                            format!(
                                "Map source operation '{}' to target operation '{}' \
                                 (arity {})",
                                gap.source_name, best.name, arity,
                            ),
                            RepairAction::Description(format!(
                                "operation_map.insert(\"{}\".into(), \
                                 TranslationCase::Direct {{ target_op: \"{}\".into() }});",
                                gap.source_name, best.name,
                            )),
                        )
                        .with_confidence(if alt_count == 1 { 0.85 } else { 0.6 })
                        .with_edit_cost(1)
                        .with_alternatives(alt_count),
                    );
                }
            }

            GapKind::FailedPreservation => {
                // Attempt to translate both sides so the suggestion can
                // include the translated equation that should be added to
                // the target theory.
                let parts: Vec<&str> = gap.source_name.splitn(2, " = ").collect();
                if parts.len() == 2 {
                    let tl = translate_term(morphism, parts[0].trim())
                        .unwrap_or_else(|_| parts[0].trim().to_string());
                    let tr = translate_term(morphism, parts[1].trim())
                        .unwrap_or_else(|_| parts[1].trim().to_string());

                    repairs.add(
                        RepairSuggestion::new(
                            RepairKind::CompleteMorphism,
                            format!(
                                "Add equation '{} = {}' to target theory '{}'",
                                tl, tr, morphism.target_theory,
                            ),
                            RepairAction::AddEquation {
                                lhs: tl,
                                rhs: tr,
                            },
                        )
                        .with_confidence(0.7)
                        .with_edit_cost(2),
                    );
                } else {
                    repairs.add(
                        RepairSuggestion::new(
                            RepairKind::CompleteMorphism,
                            format!(
                                "Fix malformed axiom '{}' (expected 'lhs = rhs')",
                                gap.source_name,
                            ),
                            RepairAction::Description(format!(
                                "Rewrite axiom '{}' in 'lhs = rhs' form",
                                gap.source_name,
                            )),
                        )
                        .with_confidence(0.4)
                        .with_edit_cost(3),
                    );
                }
            }
        }
    }

    repairs
}

// ══════════════════════════════════════════════════════════════════════════════
// Pipeline bridge
// ══════════════════════════════════════════════════════════════════════════════

/// Pipeline-level morphism check result.
#[derive(Debug, Clone)]
pub struct MorphismCheck {
    /// Gaps in theory morphism (missing constructor mappings).
    pub gaps: Vec<MorphismGap>,
    /// Equations not preserved under morphism.
    pub preservation_failures: Vec<String>,
    /// Whether the morphism is complete (no gaps).
    pub is_complete: bool,
}

/// Pipeline bridge: detect multi-theory grammars and verify morphism preservation.
///
/// Treats each grammar category as a "theory" whose sorts and operations are
/// derived from the syntax rules declared for that category.  When two or more
/// categories exist, a morphism is constructed from the first category (source)
/// to each subsequent category (target) and checked for completeness and
/// preservation.
///
/// Returns `None` when fewer than two categories are present (nothing to check).
pub fn check_from_bundle(
    all_syntax: &[(String, String, Vec<crate::SyntaxItemSpec>)],
    categories: &[crate::pipeline::CategoryInfo],
) -> Option<MorphismCheck> {
    if categories.len() < 2 {
        return None; // Need at least 2 theories to check morphisms
    }

    // Build per-category operation inventories from the syntax rules.
    // Each (rule_name, variant, items) triple produces an Operation whose
    // argument sorts are the nonterminal references found among its items.
    let mut cat_operations: HashMap<String, Vec<Operation>> = HashMap::new();
    for (rule_name, variant, items) in all_syntax {
        let arg_sorts: Vec<String> = items
            .iter()
            .filter_map(|item| {
                if let crate::SyntaxItemSpec::NonTerminal { category, .. } = item {
                    Some(category.clone())
                } else {
                    None
                }
            })
            .collect();
        let op = Operation::new(
            format!("{}::{}", variant, rule_name),
            arg_sorts,
            variant.clone(),
        );
        cat_operations
            .entry(variant.clone())
            .or_default()
            .push(op);
    }

    let mut all_gaps = Vec::new();
    let mut preservation_failures = Vec::new();

    // Use the first category as the source theory.
    let source_cat = &categories[0];
    let source_sorts: Vec<Sort> = vec![Sort::new(&source_cat.name)];
    let source_ops = cat_operations
        .get(&source_cat.name)
        .cloned()
        .unwrap_or_default();

    for target_cat in &categories[1..] {
        let target_sorts: Vec<Sort> = vec![Sort::new(&target_cat.name)];
        let target_ops = cat_operations
            .get(&target_cat.name)
            .cloned()
            .unwrap_or_default();

        // Build a morphism with identity sort mapping and match operations
        // by name/arity where possible.
        let mut morphism = TheoryMorphism::new(
            format!("{}_to_{}", source_cat.name, target_cat.name),
            &source_cat.name,
            &target_cat.name,
        );
        morphism.source_sorts = source_sorts.clone();
        morphism.target_sorts = target_sorts;
        morphism.source_operations = source_ops.clone();
        morphism.target_operations = target_ops.clone();

        // Map the source sort to the target sort.
        morphism.map_sort(&source_cat.name, &target_cat.name);

        // Attempt to match operations by arity: for each source operation,
        // find a target operation with the same arity and map it.
        let target_by_arity: HashMap<usize, Vec<&Operation>> = {
            let mut m: HashMap<usize, Vec<&Operation>> = HashMap::new();
            for op in &target_ops {
                m.entry(op.arity()).or_default().push(op);
            }
            m
        };

        for src_op in &source_ops {
            if let Some(candidates) = target_by_arity.get(&src_op.arity()) {
                // Prefer a same-name match, then fall back to the first candidate.
                let best = candidates
                    .iter()
                    .find(|c| c.name == src_op.name)
                    .unwrap_or(&candidates[0]);
                morphism.map_operation(&src_op.name, &best.name);
            }
            // If no arity-matching candidate exists, leave unmapped → detect_gaps
            // will report it.
        }

        // Detect structural gaps.
        let gaps = detect_gaps(&morphism, None);
        all_gaps.extend(gaps);

        // Build axioms from source operations: trivial self-equations
        // (Op = Op) to verify that the mapping is at least consistent.
        let axioms: Vec<String> = source_ops
            .iter()
            .filter(|op| morphism.operation_map.contains_key(&op.name))
            .map(|op| {
                if op.arity() == 0 {
                    format!("{} = {}", op.name, op.name)
                } else {
                    let args: Vec<String> =
                        (0..op.arity()).map(|i| format!("x{}", i)).collect();
                    let arg_str = args.join(", ");
                    format!("{}({}) = {}({})", op.name, arg_str, op.name, arg_str)
                }
            })
            .collect();

        if !verify_preservation(&morphism, &axioms) {
            preservation_failures.push(format!(
                "Morphism {} -> {} does not preserve all equations",
                source_cat.name, target_cat.name,
            ));
        }
    }

    let is_complete = all_gaps.is_empty() && preservation_failures.is_empty();
    Some(MorphismCheck {
        gaps: all_gaps,
        preservation_failures,
        is_complete,
    })
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn morphism_construction_and_display() {
        let mut m = TheoryMorphism::new("desugar", "SurfaceLang", "CoreLang");
        m.map_sort("Expr", "CoreExpr");
        m.map_sort("Type", "CoreType");
        m.map_operation("IfThenElse", "CaseExpr");
        m.map_identity("Var");

        assert_eq!(m.sort_map.len(), 2);
        assert_eq!(m.operation_map.len(), 2);
        assert!(m.to_string().contains("desugar"));
        assert!(m.to_string().contains("SurfaceLang -> CoreLang"));
    }

    #[test]
    fn operation_display() {
        let constant = Operation::constant("Zero", "Nat");
        assert_eq!(constant.to_string(), "Zero: Nat");

        let binary = Operation::new(
            "Add",
            vec!["Nat".to_string(), "Nat".to_string()],
            "Nat",
        );
        assert_eq!(binary.to_string(), "Add: Nat x Nat -> Nat");
    }

    #[test]
    fn translation_case_display() {
        let direct = TranslationCase::Direct {
            target_op: "CoreAdd".to_string(),
        };
        assert_eq!(direct.to_string(), "-> CoreAdd");

        let identity = TranslationCase::Identity;
        assert_eq!(identity.to_string(), "-> (identity)");

        let compound = TranslationCase::Compound {
            description: "desugar if-then-else".to_string(),
            template: "case(bool_to_option($1), $2, $3)".to_string(),
        };
        assert!(compound.to_string().contains("desugar if-then-else"));
    }

    // ── construct_morphism tests ────────────────────────────────────────

    #[test]
    fn construct_morphism_valid() {
        let source_sorts = vec![Sort::new("Nat"), Sort::new("Bool")];
        let target_sorts = vec![Sort::new("Int"), Sort::new("Bit")];
        let source_ops = vec![
            Operation::constant("Zero", "Nat"),
            Operation::new("Add", vec!["Nat".into(), "Nat".into()], "Nat"),
        ];
        let target_ops = vec![
            Operation::constant("IntZero", "Int"),
            Operation::new("IntAdd", vec!["Int".into(), "Int".into()], "Int"),
        ];

        let mut sort_map = HashMap::new();
        sort_map.insert("Nat".into(), "Int".into());
        sort_map.insert("Bool".into(), "Bit".into());

        let mut op_map: HashMap<String, TranslationCase> = HashMap::new();
        op_map.insert("Zero".into(), TranslationCase::Direct { target_op: "IntZero".into() });
        op_map.insert("Add".into(), TranslationCase::Direct { target_op: "IntAdd".into() });

        let result = construct_morphism(
            "nat_to_int",
            source_sorts,
            target_sorts,
            source_ops,
            target_ops,
            sort_map,
            op_map,
        );
        assert!(result.is_ok(), "Expected Ok, got {:?}", result);
        let m = result.expect("valid morphism");
        assert_eq!(m.sort_map.len(), 2);
        assert_eq!(m.operation_map.len(), 2);
    }

    #[test]
    fn construct_morphism_missing_sort_mapping() {
        let source_sorts = vec![Sort::new("Nat"), Sort::new("Bool")];
        let target_sorts = vec![Sort::new("Int")];
        let source_ops = vec![];
        let target_ops = vec![];

        let mut sort_map = HashMap::new();
        sort_map.insert("Nat".into(), "Int".into());
        // "Bool" is not mapped.

        let result = construct_morphism(
            "bad",
            source_sorts,
            target_sorts,
            source_ops,
            target_ops,
            sort_map,
            HashMap::new(),
        );
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Bool"));
    }

    #[test]
    fn construct_morphism_arity_mismatch() {
        let source_sorts = vec![Sort::new("Nat")];
        let target_sorts = vec![Sort::new("Int")];
        let source_ops = vec![
            Operation::new("Add", vec!["Nat".into(), "Nat".into()], "Nat"),
        ];
        // Target Add has arity 1, not 2.
        let target_ops = vec![
            Operation::new("IntAdd", vec!["Int".into()], "Int"),
        ];

        let mut sort_map = HashMap::new();
        sort_map.insert("Nat".into(), "Int".into());

        let mut op_map: HashMap<String, TranslationCase> = HashMap::new();
        op_map.insert("Add".into(), TranslationCase::Direct { target_op: "IntAdd".into() });

        let result = construct_morphism(
            "bad",
            source_sorts,
            target_sorts,
            source_ops,
            target_ops,
            sort_map,
            op_map,
        );
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Arity mismatch"));
    }

    // ── translate_term tests ────────────────────────────────────────────

    #[test]
    fn translate_term_direct() {
        let mut m = TheoryMorphism::new("test", "src", "tgt");
        m.map_operation("Add", "IntAdd");
        m.map_operation("Zero", "IntZero");

        // Add(Zero, Zero) -> IntAdd(IntZero, IntZero)
        let result = translate_term(&m, "Add(Zero, Zero)").expect("translation succeeded");
        assert_eq!(result, "IntAdd(IntZero, IntZero)");
    }

    #[test]
    fn translate_term_nested() {
        let mut m = TheoryMorphism::new("test", "src", "tgt");
        m.map_operation("Add", "Plus");
        m.map_operation("Succ", "Inc");
        m.map_operation("Zero", "Z");

        // Add(Succ(Zero), Zero) -> Plus(Inc(Z), Z)
        // Both occurrences of "Zero" (bare identifiers) are translated to "Z".
        let result = translate_term(&m, "Add(Succ(Zero), Zero)").expect("translation succeeded");
        assert_eq!(result, "Plus(Inc(Z), Z)");

        // Bare identifier translation:
        let result2 = translate_term(&m, "Zero").expect("translation succeeded");
        assert_eq!(result2, "Z");
    }

    #[test]
    fn translate_term_identity() {
        let mut m = TheoryMorphism::new("test", "src", "tgt");
        m.map_identity("Var");

        let result = translate_term(&m, "Var(x)").expect("translation succeeded");
        assert_eq!(result, "Var(x)");
    }

    // ── verify_preservation tests ───────────────────────────────────────

    #[test]
    fn verify_preservation_holds() {
        let mut m = TheoryMorphism::new("test", "src", "tgt");
        m.map_operation("Add", "Plus");
        m.map_operation("Zero", "Z");

        // Axiom: Add(Zero, x) = x  =>  translated: Plus(Z, x) = x
        // This holds only if Plus(Z, x) == x, which it does not syntactically.
        // Use an axiom that DOES hold after translation:
        // Zero = Zero  =>  Z = Z  (trivially true)
        let axioms = vec!["Zero = Zero".to_string()];
        assert!(verify_preservation(&m, &axioms));
    }

    #[test]
    fn verify_preservation_fails() {
        let mut m = TheoryMorphism::new("test", "src", "tgt");
        m.map_operation("A", "X");
        m.map_operation("B", "Y");

        // Axiom: A = B  =>  translated: X = Y  (X != Y -> false)
        let axioms = vec!["A = B".to_string()];
        assert!(!verify_preservation(&m, &axioms));
    }

    // ── detect_gaps tests ─────────────────────────────────────────────────

    #[test]
    fn detect_gaps_missing_sorts_and_operations() {
        let mut m = TheoryMorphism::new("partial", "src", "tgt");
        m.source_sorts = vec![Sort::new("Nat"), Sort::new("Bool")];
        m.source_operations = vec![
            Operation::constant("Zero", "Nat"),
            Operation::new("Add", vec!["Nat".into(), "Nat".into()], "Nat"),
        ];
        // Map only one sort and one operation.
        m.map_sort("Nat", "Int");
        m.map_operation("Zero", "IntZero");

        let gaps = detect_gaps(&m, None);
        assert_eq!(gaps.len(), 2, "Expected 2 gaps, got {:?}", gaps);

        // One MissingSort (Bool) and one MissingOperation (Add).
        let sort_gaps: Vec<_> = gaps.iter().filter(|g| g.kind == GapKind::MissingSort).collect();
        let op_gaps: Vec<_> = gaps.iter().filter(|g| g.kind == GapKind::MissingOperation).collect();
        assert_eq!(sort_gaps.len(), 1);
        assert_eq!(sort_gaps[0].source_name, "Bool");
        assert_eq!(op_gaps.len(), 1);
        assert_eq!(op_gaps[0].source_name, "Add");
    }

    #[test]
    fn detect_gaps_preservation_failure() {
        let mut m = TheoryMorphism::new("test", "src", "tgt");
        m.map_operation("A", "X");
        m.map_operation("B", "Y");

        let axioms = vec![
            "A = A".to_string(),   // X = X — preserved
            "A = B".to_string(),   // X = Y — NOT preserved
        ];
        let gaps = detect_gaps(&m, Some(&axioms));
        assert_eq!(gaps.len(), 1, "Expected 1 gap, got {:?}", gaps);
        assert_eq!(gaps[0].kind, GapKind::FailedPreservation);
        assert!(gaps[0].description.contains("X = Y"));
    }

    #[test]
    fn detect_gaps_no_gaps_on_complete_morphism() {
        let mut m = TheoryMorphism::new("complete", "src", "tgt");
        m.source_sorts = vec![Sort::new("Nat")];
        m.target_sorts = vec![Sort::new("Int")];
        m.source_operations = vec![Operation::constant("Zero", "Nat")];
        m.target_operations = vec![Operation::constant("IntZero", "Int")];
        m.map_sort("Nat", "Int");
        m.map_operation("Zero", "IntZero");

        let axioms = vec!["Zero = Zero".to_string()];
        let gaps = detect_gaps(&m, Some(&axioms));
        assert!(gaps.is_empty(), "Expected no gaps, got {:?}", gaps);
    }

    // ── suggest_morphism_completion tests ──────────────────────────────────

    #[test]
    fn suggest_completion_for_mixed_gaps() {
        let mut m = TheoryMorphism::new("partial", "src", "tgt");
        m.source_sorts = vec![Sort::new("Nat"), Sort::new("Bool")];
        // Target has a "Bool" sort with the same name — should be suggested
        // with high confidence.
        m.target_sorts = vec![Sort::new("Int"), Sort::new("Bool")];
        m.source_operations = vec![
            Operation::constant("Zero", "Nat"),
            Operation::new("Add", vec!["Nat".into(), "Nat".into()], "Nat"),
            Operation::new("Not", vec!["Bool".into()], "Bool"),
        ];
        // Two target operations: IntAdd (arity 2) and Negate (arity 1).
        m.target_operations = vec![
            Operation::constant("IntZero", "Int"),
            Operation::new("IntAdd", vec!["Int".into(), "Int".into()], "Int"),
            Operation::new("Negate", vec!["Bool".into()], "Bool"),
        ];
        m.map_sort("Nat", "Int");
        m.map_operation("Zero", "IntZero");
        // "Bool" sort, "Add" operation, and "Not" operation are unmapped.

        // Also include a failed preservation axiom.
        let axioms = vec!["Zero = Zero".to_string(), "Zero = Add(Zero, Zero)".to_string()];

        let gaps = detect_gaps(&m, Some(&axioms));
        // Expect: 1 MissingSort (Bool), 2 MissingOperation (Add, Not),
        //         1 FailedPreservation (Zero = Add(Zero, Zero)).
        assert_eq!(gaps.len(), 4, "Expected 4 gaps, got {:?}", gaps);

        let repairs = suggest_morphism_completion(&gaps, &m);
        assert_eq!(
            repairs.suggestions.len(),
            4,
            "Expected 4 repair suggestions, got {:?}",
            repairs.suggestions,
        );

        // Verify the MissingSort repair for "Bool" — same-name match should
        // give confidence 0.9.
        let sort_repair = repairs
            .suggestions
            .iter()
            .find(|r| r.description.contains("source sort 'Bool'"))
            .expect("should have a sort repair for Bool");
        assert_eq!(sort_repair.kind, RepairKind::CompleteMorphism);
        assert!((sort_repair.confidence - 0.9).abs() < f64::EPSILON);

        // Verify the MissingOperation repair for "Add" — arity 2 candidate
        // is "IntAdd".
        let add_repair = repairs
            .suggestions
            .iter()
            .find(|r| r.description.contains("source operation 'Add'"))
            .expect("should have an operation repair for Add");
        assert!(add_repair.description.contains("IntAdd"));

        // Verify the MissingOperation repair for "Not" — arity 1 candidate
        // is "Negate".
        let not_repair = repairs
            .suggestions
            .iter()
            .find(|r| r.description.contains("source operation 'Not'"))
            .expect("should have an operation repair for Not");
        assert!(not_repair.description.contains("Negate"));

        // Verify the FailedPreservation repair emits an AddEquation action.
        let pres_repair = repairs
            .suggestions
            .iter()
            .find(|r| r.description.contains("Add equation"))
            .expect("should have a preservation repair");
        assert_eq!(pres_repair.kind, RepairKind::CompleteMorphism);
        match &pres_repair.action {
            RepairAction::AddEquation { lhs, rhs } => {
                assert_eq!(lhs, "IntZero");
                // rhs should be the translated form of Add(Zero, Zero)
                // which remains as Add(IntZero, IntZero) because Add is
                // unmapped — it passes through unchanged.
                assert_eq!(rhs, "Add(IntZero, IntZero)");
            }
            other => panic!("Expected AddEquation, got {:?}", other),
        }
    }

    #[test]
    fn test_check_from_bundle_basic() {
        let syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![
            (
                "Add".to_string(),
                "Expr".to_string(),
                vec![
                    crate::SyntaxItemSpec::NonTerminal {
                        category: "Expr".to_string(),
                        param_name: "a".to_string(),
                    },
                    crate::SyntaxItemSpec::Terminal("+".to_string()),
                    crate::SyntaxItemSpec::NonTerminal {
                        category: "Expr".to_string(),
                        param_name: "b".to_string(),
                    },
                ],
            ),
            (
                "IntAdd".to_string(),
                "IntExpr".to_string(),
                vec![
                    crate::SyntaxItemSpec::NonTerminal {
                        category: "IntExpr".to_string(),
                        param_name: "a".to_string(),
                    },
                    crate::SyntaxItemSpec::Terminal("+".to_string()),
                    crate::SyntaxItemSpec::NonTerminal {
                        category: "IntExpr".to_string(),
                        param_name: "b".to_string(),
                    },
                ],
            ),
        ];
        let cats = vec![
            crate::pipeline::CategoryInfo {
                name: "Expr".to_string(),
                native_type: None,
                is_primary: true,
            },
            crate::pipeline::CategoryInfo {
                name: "IntExpr".to_string(),
                native_type: None,
                is_primary: false,
            },
        ];
        let result = check_from_bundle(&syntax, &cats);
        assert!(result.is_some(), "should produce morphism check for >= 2 categories");
    }

    #[test]
    fn test_check_from_bundle_single_category() {
        let syntax: Vec<(String, String, Vec<crate::SyntaxItemSpec>)> = vec![(
            "Add".to_string(),
            "Expr".to_string(),
            vec![crate::SyntaxItemSpec::Terminal("+".to_string())],
        )];
        let cats = vec![crate::pipeline::CategoryInfo {
            name: "Expr".to_string(),
            native_type: None,
            is_primary: true,
        }];
        let result = check_from_bundle(&syntax, &cats);
        assert!(result.is_none(), "should return None for < 2 categories");
    }
}
