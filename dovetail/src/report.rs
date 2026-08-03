//! Runtime-facing Dovetail extraction reports.
//!
//! This module is deliberately substrate-neutral: it has no dependency on the
//! MeTTaIL runtime, Rholang, RSpace, or Ascent. Its job is to turn checked
//! Dovetail extraction output into a stable artifact boundary that downstream
//! adapters can consume without losing the properties the extractor proves:
//! exact [`ContentKey`] identity, deterministic root order, derivation-tree
//! structure, and terminal [`ExtractionCompleteness`].

use crate::hash::HashMap;
use std::rc::Rc;

use crate::egraph::{EClassId, EGraph, ENode};
use crate::extract::{
    Derivation, Extraction, ExtractionCompleteness, Extractor, MonotoneBestOrder,
};
use crate::key::{ContentKey, SemanticHash};
use crate::rules::{RewriteJustification, RuleFiring};

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

/// A σ sub-term extracted to funded-best structural form: the operator label
/// (`L` — the same op label the e-graph carries, e.g. a `"Lang::Cat::Ctor"`
/// String) and the extracted child sub-terms in child order. This is the
/// substrate-neutral image of one [`Derivation`] node with weights and keys
/// dropped, retaining only what a downstream reflector needs to rebuild the term.
pub struct JustifiedSubterm<L> {
    pub op: L,
    pub children: Vec<JustifiedSubterm<L>>,
}

impl<L> Drop for JustifiedSubterm<L> {
    fn drop(&mut self) {
        let mut pending = std::mem::take(&mut self.children);
        while let Some(mut child) = pending.pop() {
            pending.append(&mut child.children);
        }
    }
}

impl<L: Clone> Clone for JustifiedSubterm<L> {
    fn clone(&self) -> Self {
        enum Task<'a, L> {
            Visit(&'a JustifiedSubterm<L>),
            Assemble { op: L, child_count: usize },
        }
        let mut tasks = vec![Task::Visit(self)];
        let mut values = Vec::<JustifiedSubterm<L>>::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(node) => {
                    tasks.push(Task::Assemble {
                        op: node.op.clone(),
                        child_count: node.children.len(),
                    });
                    for child in node.children.iter().rev() {
                        tasks.push(Task::Visit(child));
                    }
                },
                Task::Assemble { op, child_count } => {
                    let first = values
                        .len()
                        .checked_sub(child_count)
                        .expect("JustifiedSubterm clone PDA lost a child");
                    let children = values.split_off(first);
                    values.push(JustifiedSubterm { op, children });
                },
            }
        }
        values
            .pop()
            .expect("JustifiedSubterm clone PDA must produce a root")
    }
}

impl<L: PartialEq> PartialEq for JustifiedSubterm<L> {
    fn eq(&self, other: &Self) -> bool {
        let mut pending = vec![(self, other)];
        while let Some((left, right)) = pending.pop() {
            if left.op != right.op || left.children.len() != right.children.len() {
                return false;
            }
            pending.extend(left.children.iter().zip(&right.children));
        }
        true
    }
}

impl<L: Eq> Eq for JustifiedSubterm<L> {}

impl<L: std::fmt::Debug> std::fmt::Debug for JustifiedSubterm<L> {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        enum Task<'a, L> {
            Node(&'a JustifiedSubterm<L>),
            Separator,
            Close,
        }
        let mut tasks = vec![Task::Node(self)];
        while let Some(task) = tasks.pop() {
            match task {
                Task::Node(node) => {
                    write!(formatter, "JustifiedSubterm {{ op: {:?}, children: [", node.op)?;
                    tasks.push(Task::Close);
                    for (index, child) in node.children.iter().enumerate().rev() {
                        tasks.push(Task::Node(child));
                        if index > 0 {
                            tasks.push(Task::Separator);
                        }
                    }
                },
                Task::Separator => formatter.write_str(", ")?,
                Task::Close => formatter.write_str("] }")?,
            }
        }
        Ok(())
    }
}

/// A rewrite firing's justification with each σ variable resolved to its
/// funded-best extracted sub-term.
///
/// Where [`crate::rules::RewriteJustification`] carries σ as bare e-class ids
/// (cheap to capture during saturation), this carries the RESOLVED sub-terms —
/// produced by [`resolve_rewrite_justifications`] while the e-graph is still
/// live. `sigma` is ordered deterministically by variable name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolvedRewriteJustification<L> {
    /// Human-readable rule label (`None` for an anonymous rule).
    pub rule_label: Option<String>,
    /// σ resolved to funded-best sub-terms, ordered by variable name.
    pub sigma: Vec<(String, JustifiedSubterm<L>)>,
    /// The firing's ROOT resolved to its funded-best sub-term — the **contractum**
    /// this firing produced (`RHS[σ]` after the host applied the rule, incl.
    /// capture-avoiding substitution for a β-style `Subst`/`MultiSubst` RHS). This
    /// is the reduct a binder-rewrite σ-injection hands to its σ-receiver: the host
    /// computes the substitution (model-b) and the reduced term reflects to a ground
    /// σ slot the receiver fires (Stage 3c). Extracted under the SAME
    /// `funded_best` cost model the report roots use, so for a whole-term root redex
    /// it equals the whole normal form and for a nested redex the local reduct.
    /// `None` only if the root class has no funded-best derivation (defensive; a
    /// fired class always has at least one node). Additive: base/AC/contextual
    /// injection arms ignore it and stay byte-identical.
    pub contractum: Option<JustifiedSubterm<L>>,
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
    /// Per-firing σ justifications with each σ variable resolved to its
    /// funded-best sub-term. Empty unless populated by
    /// [`resolve_rewrite_justifications`] (additive; existing producers leave it
    /// empty and stay byte-identical downstream).
    pub rewrite_justifications: Vec<ResolvedRewriteJustification<L>>,
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
        // Additive, empty by default: a producer that wants σ provenance sets
        // this via `resolve_rewrite_justifications` where the e-graph is live.
        rewrite_justifications: Vec::new(),
        completeness: extraction.completeness,
    };
    let mut seen: HashMap<ContentKey, usize> = HashMap::default();

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
    enum Task<'a, L, W> {
        Visit {
            derivation: &'a Rc<Derivation<L, W>>,
            is_root: bool,
        },
        Child {
            parent_key: ContentKey,
            child: &'a Rc<Derivation<L, W>>,
            child_index: usize,
        },
    }

    let mut tasks = vec![Task::Visit { derivation, is_root }];
    let mut root_ordinal = None;
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit { derivation, is_root } => {
                let (ordinal, fresh) = match seen.get(&derivation.key).copied() {
                    Some(ordinal) => {
                        if is_root {
                            report.terms[ordinal].is_root = true;
                        }
                        (ordinal, false)
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
                        (ordinal, true)
                    },
                };
                root_ordinal.get_or_insert(ordinal);
                if fresh {
                    for (child_index, child) in derivation.children.iter().enumerate().rev() {
                        tasks.push(Task::Child {
                            parent_key: derivation.key.clone(),
                            child,
                            child_index,
                        });
                    }
                }
            },
            Task::Child { parent_key, child, child_index } => {
                let ordinal = report.derivation_edges.len();
                report.derivation_edges.push(DovetailDerivationEdge {
                    ordinal,
                    parent_key,
                    child_key: child.key.clone(),
                    child_index,
                });
                tasks.push(Task::Visit { derivation: child, is_root: false });
            },
        }
    }
    root_ordinal.expect("record_derivation always visits its root")
}

/// A funded-best [`Derivation`] tree projected to a [`JustifiedSubterm`]: keep
/// the op label and child structure, drop weights and keys.
fn derivation_to_subterm<L, W>(derivation: &Derivation<L, W>) -> JustifiedSubterm<L>
where
    L: Clone,
{
    enum Task<'a, L, W> {
        Visit(&'a Derivation<L, W>),
        Assemble { op: L, child_count: usize },
    }
    let mut tasks = vec![Task::Visit(derivation)];
    let mut values = Vec::<JustifiedSubterm<L>>::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(node) => {
                tasks.push(Task::Assemble {
                    op: node.op.clone(),
                    child_count: node.children.len(),
                });
                for child in node.children.iter().rev() {
                    tasks.push(Task::Visit(child));
                }
            },
            Task::Assemble { op, child_count } => {
                let first = values
                    .len()
                    .checked_sub(child_count)
                    .expect("derivation projection PDA lost a child");
                let children = values.split_off(first);
                values.push(JustifiedSubterm { op, children });
            },
        }
    }
    values
        .pop()
        .expect("derivation projection PDA must produce one root")
}

/// Resolve the substrate-level [`RewriteJustification`]s captured during
/// saturation into [`ResolvedRewriteJustification`]s, extracting each σ e-class
/// to its funded-best sub-term.
///
/// This MUST run while `eg` is still live (extraction walks the e-graph). It
/// reuses the exact same [`Extractor::funded_best`] machinery the runtime report
/// uses for root normal forms, so no new extraction path is introduced. `weigh`
/// is the same cost model the caller extracts roots under (e.g. the constant-zero
/// weight the generated report producer uses); it only orders equal-cost
/// alternatives, never prunes. Each firing's `sigma` is ordered deterministically
/// by variable name. A σ variable whose class has no funded-best derivation
/// (defensive; a matched class always has at least one node) is omitted rather
/// than fabricated.
pub fn resolve_rewrite_justifications<L, W, F>(
    eg: &EGraph<L>,
    justifications: &[RewriteJustification],
    weigh: F,
) -> Vec<ResolvedRewriteJustification<L>>
where
    L: Clone + Eq + std::hash::Hash + SemanticHash,
    W: MonotoneBestOrder + crate::wta::CommutativeStarSemiring,
    F: Fn(&ENode<L>) -> W,
{
    let mut extractor = Extractor::new(eg, weigh);
    let mut resolved = Vec::with_capacity(justifications.len());
    for justification in justifications {
        // Deterministic σ order (the source `Subst` is a HashMap): sort by name.
        let mut bindings: Vec<(&String, EClassId)> = justification
            .subst
            .iter()
            .map(|(name, &class)| (name, class))
            .collect();
        bindings.sort_by(|a, b| a.0.cmp(b.0));

        let mut sigma = Vec::with_capacity(bindings.len());
        for (name, class) in bindings {
            if let Some(derivation) = extractor.funded_best(eg.find(class)).value {
                sigma.push((name.clone(), derivation_to_subterm(&derivation)));
            }
        }
        // The contractum: the firing's ROOT resolved to its funded-best sub-term —
        // the reduct `RHS[σ]` the host produced (incl. capture-avoiding substitution
        // for a β-style `Subst`/`MultiSubst` RHS, applied during saturation and
        // merged into `root`). Extracted with the SAME `funded_best` cost model the
        // report roots use, so it is the local normal form the extractor would
        // report for this class (the appsubst/lambda `dovetail_normal_term` tests
        // witness that this reliably yields the contractum, not the un-reduced redex).
        let contractum = extractor
            .funded_best(eg.find(justification.root))
            .value
            .map(|derivation| derivation_to_subterm(&derivation));
        resolved.push(ResolvedRewriteJustification {
            rule_label: justification.rule_label.clone(),
            sigma,
            contractum,
        });
    }
    resolved
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
    fn swap_step_captures_and_resolves_sigma_justification() {
        use crate::rules::{Pattern, RewriteRule};

        // The Swap→Pair demo: `SwapStep . |- (Swap x y) ~> (Pair y x)` over the
        // ground redex `Swap(A, B)`. This is the exact shape of
        // `SWAP_DEMO_FRAGMENT` in the Epic-4 runtime demo, lowered by hand as
        // e-nodes (bare op labels A/B/Swap/Pair).
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("A".into()));
        let b = eg.add(ENode::leaf("B".into()));
        let swap = eg.add(ENode::new("Swap".into(), vec![a, b]));

        let rule = RewriteRule {
            lhs: Pattern::app("Swap".into(), vec![Pattern::var("x"), Pattern::var("y")]),
            rhs: Pattern::app("Pair".into(), vec![Pattern::var("y"), Pattern::var("x")]),
            label: Some("SwapStep".into()),
        };
        let sat = eg.saturate(&[rule], 64);

        // The firing is captured additively, one justification, with σ carrying
        // the matched e-classes (x ↦ A, y ↦ B) — NOT collapsed to a count.
        assert_eq!(sat.rule_firings, vec![RuleFiring { label: Some("SwapStep".into()), count: 1 }]);
        assert_eq!(sat.rewrite_justifications.len(), 1);
        let justification = &sat.rewrite_justifications[0];
        assert_eq!(justification.rule_label, Some("SwapStep".to_string()));
        assert_eq!(eg.find(justification.root), eg.find(swap));
        assert_eq!(justification.subst.get("x").map(|&c| eg.find(c)), Some(eg.find(a)));
        assert_eq!(justification.subst.get("y").map(|&c| eg.find(c)), Some(eg.find(b)));

        // Resolving σ against the live e-graph extracts each variable's
        // funded-best sub-term (the nullary A / B constructors), ordered by name.
        let resolved = resolve_rewrite_justifications(&eg, &sat.rewrite_justifications, |_| {
            TropicalWeight(0.0)
        });
        assert_eq!(resolved.len(), 1);
        let resolved = &resolved[0];
        assert_eq!(resolved.rule_label, Some("SwapStep".to_string()));
        assert_eq!(
            resolved.sigma,
            vec![
                (
                    "x".to_string(),
                    JustifiedSubterm {
                        op: "A".to_string(),
                        children: Vec::new()
                    }
                ),
                (
                    "y".to_string(),
                    JustifiedSubterm {
                        op: "B".to_string(),
                        children: Vec::new()
                    }
                ),
            ]
        );
    }

    #[test]
    fn report_without_firings_has_empty_rewrite_justifications() {
        // Additivity guard at the dovetail level: an extraction with no rewrites
        // carries no σ justifications, so the new field defaults empty.
        let mut eg = EGraph::<String>::new();
        let x = eg.add(ENode::leaf("x".into()));
        let y = eg.add(ENode::leaf("y".into()));
        let pair = eg.add(ENode::new("pair".into(), vec![x, y]));
        let sat = eg.saturate(&[], 16);
        assert!(sat.rewrite_justifications.is_empty());

        let mut extractor = Extractor::new(&eg, weigh);
        let report = report_from_extraction(extractor.derivations(pair).collect_checked());
        assert!(report.rewrite_justifications.is_empty());
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
