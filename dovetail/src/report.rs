//! Runtime-facing Dovetail extraction reports.
//!
//! This module is deliberately substrate-neutral: it has no dependency on the
//! MeTTaIL runtime, Rholang, RSpace, or Ascent. Its job is to turn checked
//! Dovetail extraction output into a stable artifact boundary that downstream
//! adapters can consume without losing the properties the extractor proves:
//! exact [`ContentKey`] identity, deterministic root order, derivation-tree
//! structure, and terminal [`ExtractionCompleteness`].

use std::collections::HashMap;
use std::rc::Rc;

use crate::egraph::EClassId;
use crate::extract::{Derivation, Extraction, ExtractionCompleteness};
use crate::key::ContentKey;
use crate::rules::RuleFiring;

/// One unique derivation node in a Dovetail report.
///
/// `ordinal` is the first-seen position in a deterministic pre-order traversal
/// of the extracted root derivations. `key` remains the exact identity; callers
/// must not treat the ordinal as a semantic key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DovetailTermRecord<L, W> {
    pub ordinal: usize,
    pub class: EClassId,
    pub key: ContentKey,
    pub op: L,
    pub weight: W,
    pub is_root: bool,
}

/// A parent-to-child edge inside an extracted derivation tree.
///
/// These are derivation-dependency edges, not operational rewrite steps. The
/// edge list preserves multiplicity and child order, which matters for adapters
/// whose target representation distinguishes repeated operands.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DovetailDerivationEdge {
    pub ordinal: usize,
    pub parent_key: ContentKey,
    pub child_key: ContentKey,
    pub child_index: usize,
}

/// Checked, runtime-facing artifact for an extraction run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DovetailRunReport<L, W> {
    /// Root derivation keys in the exact order emitted by the extractor.
    pub roots: Vec<ContentKey>,
    /// Positions of each root in [`terms`](Self::terms), also in extractor order.
    pub root_ordinals: Vec<usize>,
    /// Unique derivation records, deduplicated by exact `ContentKey`.
    pub terms: Vec<DovetailTermRecord<L, W>>,
    /// Ordered derivation-tree edges, preserving repeated child uses.
    pub derivation_edges: Vec<DovetailDerivationEdge>,
    /// Aggregated labels for Dovetail rules that produced at least one merge
    /// before extraction.
    pub rule_firings: Vec<RuleFiring>,
    /// Whether the extraction is exhaustive or bounded by a detected cycle.
    pub completeness: ExtractionCompleteness,
}

impl<L, W> DovetailRunReport<L, W> {
    /// True exactly when the report is known to be exhaustive.
    pub fn is_complete(&self) -> bool {
        self.completeness == ExtractionCompleteness::Complete
    }

    /// Return `Ok(())` only for exhaustive reports.
    pub fn assert_complete(&self) -> Result<(), ExtractionCompleteness> {
        if self.is_complete() {
            Ok(())
        } else {
            Err(self.completeness)
        }
    }

    /// Look up a reported term by its exact Dovetail key.
    pub fn term_by_key(&self, key: &ContentKey) -> Option<&DovetailTermRecord<L, W>> {
        self.terms.iter().find(|term| term.key == *key)
    }
}

/// Convert checked extracted derivations into a substrate-neutral report.
///
/// The conversion is structure-preserving:
///
/// - root key order is exactly the input vector order;
/// - term identity is exact `ContentKey` identity;
/// - duplicate derivation nodes are shared in `terms` but repeated child edges
///   are retained;
/// - the terminal completeness status is copied unchanged.
pub fn report_from_extraction<L, W>(
    extraction: Extraction<Vec<Rc<Derivation<L, W>>>>,
) -> DovetailRunReport<L, W>
where
    L: Clone,
    W: Clone,
{
    report_from_extraction_with_rule_firings(extraction, Vec::new())
}

/// Convert checked extracted derivations plus saturation provenance into a
/// substrate-neutral report.
pub fn report_from_extraction_with_rule_firings<L, W>(
    extraction: Extraction<Vec<Rc<Derivation<L, W>>>>,
    rule_firings: Vec<RuleFiring>,
) -> DovetailRunReport<L, W>
where
    L: Clone,
    W: Clone,
{
    let mut report = DovetailRunReport {
        roots: Vec::with_capacity(extraction.value.len()),
        root_ordinals: Vec::with_capacity(extraction.value.len()),
        terms: Vec::new(),
        derivation_edges: Vec::new(),
        rule_firings,
        completeness: extraction.completeness,
    };
    let mut seen: HashMap<ContentKey, usize> = HashMap::new();

    for root in &extraction.value {
        report.roots.push(root.key.clone());
        let ordinal = record_derivation(root, true, &mut report, &mut seen);
        report.root_ordinals.push(ordinal);
    }

    report
}

fn record_derivation<L, W>(
    derivation: &Rc<Derivation<L, W>>,
    is_root: bool,
    report: &mut DovetailRunReport<L, W>,
    seen: &mut HashMap<ContentKey, usize>,
) -> usize
where
    L: Clone,
    W: Clone,
{
    let ordinal = match seen.get(&derivation.key).copied() {
        Some(ordinal) => {
            if is_root {
                report.terms[ordinal].is_root = true;
            }
            ordinal
        },
        None => {
            let ordinal = report.terms.len();
            seen.insert(derivation.key.clone(), ordinal);
            report.terms.push(DovetailTermRecord {
                ordinal,
                class: derivation.class,
                key: derivation.key.clone(),
                op: derivation.op.clone(),
                weight: derivation.weight.clone(),
                is_root,
            });
            ordinal
        },
    };

    for (child_index, child) in derivation.children.iter().enumerate() {
        let edge_ordinal = report.derivation_edges.len();
        report.derivation_edges.push(DovetailDerivationEdge {
            ordinal: edge_ordinal,
            parent_key: derivation.key.clone(),
            child_key: child.key.clone(),
            child_index,
        });
        record_derivation(child, false, report, seen);
    }

    ordinal
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use rigail::TropicalWeight;

    use super::*;
    use crate::egraph::{EGraph, ENode};
    use crate::extract::Extractor;

    fn weigh(node: &ENode<String>) -> TropicalWeight {
        match node.op.as_str() {
            "a" => TropicalWeight(5.0),
            "b" => TropicalWeight(3.0),
            "c" => TropicalWeight(3.0),
            "x" => TropicalWeight(1.0),
            "y" => TropicalWeight(2.0),
            "pair" => TropicalWeight(1.0),
            "base" => TropicalWeight(1.0),
            "g" => TropicalWeight(1.0),
            _ => TropicalWeight(0.0),
        }
    }

    #[test]
    fn complete_report_preserves_root_order_and_exact_keys() {
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let b = eg.add(ENode::leaf("b".into()));
        let c = eg.add(ENode::leaf("c".into()));
        eg.merge(a, b);
        eg.merge(b, c);
        eg.rebuild();

        let mut extractor = Extractor::new(&eg, weigh);
        let extracted = extractor.derivations(eg.find(a)).collect_checked();
        let expected_keys: Vec<_> = extracted.value.iter().map(|d| d.key.clone()).collect();

        let report = report_from_extraction(extracted);

        assert_eq!(report.completeness, ExtractionCompleteness::Complete);
        assert!(report.is_complete());
        assert_eq!(report.assert_complete(), Ok(()));
        assert_eq!(report.roots, expected_keys);
        assert_eq!(report.root_ordinals, vec![0, 1, 2]);
        assert_eq!(report.terms.len(), 3);
        assert!(report.derivation_edges.is_empty());
        assert!(report.terms.iter().all(|term| term.is_root));

        let distinct_keys: HashSet<_> = report.terms.iter().map(|term| term.key.clone()).collect();
        assert_eq!(distinct_keys.len(), report.terms.len());
        for root_key in &report.roots {
            assert_eq!(
                report.term_by_key(root_key).map(|term| term.key.clone()),
                Some(root_key.clone())
            );
        }
    }

    #[test]
    fn report_records_derivation_edges_with_child_order() {
        let mut eg = EGraph::<String>::new();
        let x = eg.add(ENode::leaf("x".into()));
        let y = eg.add(ENode::leaf("y".into()));
        let pair = eg.add(ENode::new("pair".into(), vec![x, y]));

        let mut extractor = Extractor::new(&eg, weigh);
        let report = report_from_extraction(extractor.derivations(pair).collect_checked());

        assert_eq!(report.completeness, ExtractionCompleteness::Complete);
        assert_eq!(report.root_ordinals, vec![0]);
        assert_eq!(report.terms.len(), 3);
        assert_eq!(report.terms[0].op, "pair");
        assert_eq!(report.terms[1].op, "x");
        assert_eq!(report.terms[2].op, "y");
        assert_eq!(report.derivation_edges.len(), 2);

        let root_key = report.terms[0].key.clone();
        let x_key = report.terms[1].key.clone();
        let y_key = report.terms[2].key.clone();
        assert_eq!(
            report.derivation_edges[0],
            DovetailDerivationEdge {
                ordinal: 0,
                parent_key: root_key.clone(),
                child_key: x_key,
                child_index: 0,
            }
        );
        assert_eq!(
            report.derivation_edges[1],
            DovetailDerivationEdge {
                ordinal: 1,
                parent_key: root_key,
                child_key: y_key,
                child_index: 1,
            }
        );
    }

    #[test]
    fn report_preserves_rule_firing_provenance() {
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));

        let mut extractor = Extractor::new(&eg, weigh);
        let extracted = extractor.derivations(a).collect_checked();
        let firing = RuleFiring {
            label: Some("rewrite::a_to_b".to_string()),
            count: 3,
        };
        let report = report_from_extraction_with_rule_firings(extracted, vec![firing.clone()]);

        assert_eq!(report.rule_firings, vec![firing]);
    }

    #[test]
    fn bounded_report_cannot_be_asserted_complete() {
        let mut eg = EGraph::<String>::new();
        let base = eg.add(ENode::leaf("base".into()));
        let g = eg.add(ENode::new("g".into(), vec![base]));
        eg.merge(base, g);
        eg.rebuild();

        let mut extractor = Extractor::new(&eg, weigh);
        let report = report_from_extraction(extractor.derivations(eg.find(base)).collect_checked());

        assert_eq!(report.completeness, ExtractionCompleteness::BoundedByCycleCut);
        assert!(!report.is_complete());
        assert_eq!(report.assert_complete(), Err(ExtractionCompleteness::BoundedByCycleCut));
        assert!(!report.roots.is_empty(), "acyclic evidence is still reported");
    }
}
