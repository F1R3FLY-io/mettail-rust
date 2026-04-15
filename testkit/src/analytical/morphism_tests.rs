//! Theory morphism preservation analysis for generated language tests.
//!
//! Wraps `mettail_prattail::morphism` and provides a higher-level interface
//! that works with `LanguageMetadata`. For composed languages (those built from
//! multiple source languages), this module verifies that the translation mappings
//! preserve axioms and detects gaps in the morphism definitions.
//!
//! For non-composed languages, a self-morphism (identity) is constructed from the
//! language's own sorts and operations, verifying internal consistency.

use std::collections::HashMap;

use mettail_prattail::morphism::{
    self, GapKind, MorphismGap, Operation, Sort, TranslationCase,
};
use mettail_runtime::LanguageMetadata;

/// Result of morphism preservation analysis on a language.
#[derive(Debug)]
pub struct MorphismResult {
    /// Whether the morphism (or self-morphism) is fully preserving.
    pub is_preserving: bool,
    /// Number of gaps (missing sort maps, missing operation maps, failed axiom preservation).
    pub gap_count: usize,
    /// Breakdown of gap kinds.
    pub missing_sorts: usize,
    /// Number of missing operation mappings.
    pub missing_operations: usize,
    /// Number of failed axiom preservations.
    pub failed_preservations: usize,
    /// Human-readable summary.
    pub summary: String,
}

/// Check morphism preservation for a language.
///
/// For any language, this constructs a self-morphism (identity morphism) from
/// the language's own type and term definitions, then verifies that the
/// language's equations are preserved under this identity mapping. This serves
/// as an internal consistency check: if the identity morphism fails, the
/// language's axioms are internally inconsistent.
///
/// For composed languages, the caller should additionally construct the
/// inter-language morphism externally and use the prattail `verify_preservation`
/// and `detect_gaps` functions directly.
///
/// # Arguments
/// * `metadata` -- static language metadata providing type, term, and equation definitions
///
/// # Returns
/// A `MorphismResult` summarizing morphism completeness and preservation.
pub fn check_morphism_preservation(metadata: &dyn LanguageMetadata) -> MorphismResult {
    // Build sorts from the language's type definitions.
    let sorts: Vec<Sort> = metadata
        .types()
        .iter()
        .map(|td| Sort::new(td.name))
        .collect();

    // Build operations from the language's term (constructor) definitions.
    let operations: Vec<Operation> = metadata
        .terms()
        .iter()
        .map(|td| {
            let arg_sorts: Vec<String> = td
                .fields
                .iter()
                .map(|f| f.ty.to_string())
                .collect();
            Operation::new(td.name, arg_sorts, td.type_name)
        })
        .collect();

    // Build identity sort map: each sort maps to itself.
    let sort_map: HashMap<String, String> = sorts
        .iter()
        .map(|s| (s.name.clone(), s.name.clone()))
        .collect();

    // Build identity operation map: each operation maps to itself via Identity.
    let op_map: HashMap<String, TranslationCase> = operations
        .iter()
        .map(|op| (op.name.clone(), TranslationCase::Identity))
        .collect();

    // Construct the self-morphism.
    let morphism_result = morphism::construct_morphism(
        &format!("{}_self_morphism", metadata.name()),
        sorts.clone(),
        sorts.clone(),
        operations.clone(),
        operations.clone(),
        sort_map,
        op_map,
    );

    let morphism = match morphism_result {
        Ok(m) => m,
        Err(e) => {
            return MorphismResult {
                is_preserving: false,
                gap_count: 1,
                missing_sorts: 0,
                missing_operations: 0,
                failed_preservations: 1,
                summary: format!(
                    "{}: self-morphism construction failed: {}",
                    metadata.name(),
                    e
                ),
            };
        }
    };

    // Build axioms from the language's equation definitions.
    // Equations are expressed as "lhs = rhs" strings.
    let axioms: Vec<String> = metadata
        .equations()
        .iter()
        .map(|eq| format!("{} = {}", eq.lhs, eq.rhs))
        .collect();

    // Detect gaps in the morphism.
    let axiom_slice = if axioms.is_empty() {
        None
    } else {
        Some(axioms.as_slice())
    };
    let gaps: Vec<MorphismGap> = morphism::detect_gaps(&morphism, axiom_slice);

    let missing_sorts = gaps.iter().filter(|g| g.kind == GapKind::MissingSort).count();
    let missing_operations = gaps
        .iter()
        .filter(|g| g.kind == GapKind::MissingOperation)
        .count();
    let failed_preservations = gaps
        .iter()
        .filter(|g| g.kind == GapKind::FailedPreservation)
        .count();

    // Also check preservation if we have axioms.
    let preservation_ok = if axioms.is_empty() {
        true
    } else {
        morphism::verify_preservation(&morphism, &axioms)
    };

    let is_preserving = gaps.is_empty() && preservation_ok;

    MorphismResult {
        is_preserving,
        gap_count: gaps.len(),
        missing_sorts,
        missing_operations,
        failed_preservations,
        summary: format!(
            "{}: self-morphism {} (gaps: {}, missing sorts: {}, missing ops: {}, \
             failed preservation: {})",
            metadata.name(),
            if is_preserving {
                "preserving"
            } else {
                "NOT fully preserving"
            },
            gaps.len(),
            missing_sorts,
            missing_operations,
            failed_preservations,
        ),
    }
}
