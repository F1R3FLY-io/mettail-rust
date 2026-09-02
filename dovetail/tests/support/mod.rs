#![allow(dead_code)]

use std::collections::BTreeSet;
use std::rc::Rc;

use dovetail::egraph::{EClassId, EGraph, EGraphConfig, ENode};
use dovetail::extract::{Derivation, ExtractionCompleteness, Extractor};
use dovetail::key::{write_ordered_framed, ContentKey, ContentKeyMap, SemanticHash};
use rigail::{Semiring, TropicalWeight};

#[derive(Clone, Debug)]
pub struct EdgeSpec {
    pub op: String,
    pub weight: u32,
    pub children: Vec<usize>,
}

#[derive(Clone, Debug)]
pub struct AcyclicSpec {
    pub classes: Vec<Vec<EdgeSpec>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Observation {
    pub weight: TropicalWeight,
    pub key: ContentKey,
    pub op: String,
}

#[derive(Clone, Debug)]
struct OracleDerivation {
    weight: TropicalWeight,
    key: ContentKey,
    op: String,
}

pub fn weighted_op(op: impl AsRef<str>, weight: u32) -> String {
    format!("{}@{}", op.as_ref(), weight)
}

pub fn op_name(op: &str) -> &str {
    op.rsplit_once('@').map_or(op, |(name, _)| name)
}

pub fn label_weight(node: &ENode<String>) -> TropicalWeight {
    let Some((_, raw_weight)) = node.op.rsplit_once('@') else {
        return TropicalWeight::new(1.0);
    };
    if raw_weight == "inf" {
        return TropicalWeight::zero();
    }
    TropicalWeight::new(
        raw_weight
            .parse::<f64>()
            .unwrap_or_else(|_| panic!("invalid test weight in label {:?}", node.op)),
    )
}

pub fn semantic_weight(node: &ENode<String>) -> TropicalWeight {
    let op = op_name(&node.op);
    if matches!(op, "result" | "value" | "beta_result")
        || op.starts_with("Int(")
        || op.starts_with("Bool(")
        || op.starts_with("Name(")
        || op.starts_with("Proc(")
    {
        TropicalWeight::new(0.0)
    } else if op == "dead" {
        TropicalWeight::zero()
    } else {
        TropicalWeight::new(1.0)
    }
}

pub fn build_acyclic(spec: &AcyclicSpec) -> (EGraph<String>, Vec<EClassId>) {
    build_acyclic_with_config(spec, EGraphConfig::default())
}

pub fn build_acyclic_with_config(
    spec: &AcyclicSpec,
    config: EGraphConfig,
) -> (EGraph<String>, Vec<EClassId>) {
    let mut eg = EGraph::<String>::with_config(config);
    let mut roots = Vec::with_capacity(spec.classes.len());
    for (class_idx, edges) in spec.classes.iter().enumerate() {
        assert!(!edges.is_empty(), "test class {class_idx} must contain at least one edge");
        let mut ids = Vec::with_capacity(edges.len());
        for (edge_idx, edge) in edges.iter().enumerate() {
            let children: Vec<EClassId> = edge
                .children
                .iter()
                .map(|&child_idx| {
                    assert!(
                        child_idx < roots.len(),
                        "edge {class_idx}.{edge_idx} references non-previous class {child_idx}"
                    );
                    roots[child_idx]
                })
                .collect();
            ids.push(eg.add(ENode::new(weighted_op(&edge.op, edge.weight), children)));
        }
        let representative = ids[0];
        for id in ids.into_iter().skip(1) {
            eg.merge(representative, id);
        }
        eg.rebuild();
        roots.push(eg.find(representative));
    }
    (eg, roots)
}

pub fn generated_acyclic_spec(mut seed: u64, class_count: usize) -> AcyclicSpec {
    fn next(seed: &mut u64) -> u64 {
        *seed ^= *seed << 13;
        *seed ^= *seed >> 7;
        *seed ^= *seed << 17;
        *seed
    }

    let class_count = class_count.max(1);
    let mut classes = Vec::with_capacity(class_count);
    for class_idx in 0..class_count {
        let edge_count = 1 + (next(&mut seed) as usize % 2);
        let mut edges = Vec::with_capacity(edge_count);
        for edge_idx in 0..edge_count {
            let max_arity = if class_idx == 0 { 0 } else { 2 };
            let arity = if max_arity == 0 {
                0
            } else {
                next(&mut seed) as usize % (max_arity + 1)
            };
            let mut children = Vec::with_capacity(arity);
            for _ in 0..arity {
                children.push(next(&mut seed) as usize % class_idx);
            }
            let raw_weight = next(&mut seed) as u32;
            let weight = 1 + raw_weight % 9;
            edges.push(EdgeSpec {
                op: format!("c{class_idx}_e{edge_idx}_s{:x}", raw_weight & 0xff),
                weight,
                children,
            });
        }
        classes.push(edges);
    }
    AcyclicSpec { classes }
}

pub fn generated_bounded_acyclic_spec(
    seed: u64,
    class_count: usize,
    max_derivations: usize,
) -> AcyclicSpec {
    let mut candidate_seed = seed;
    for _ in 0..128 {
        let spec = generated_acyclic_spec(candidate_seed, class_count);
        if derivation_count_upper_bound(&spec, max_derivations) <= max_derivations {
            return spec;
        }
        candidate_seed = candidate_seed.wrapping_add(0x9e37_79b9_7f4a_7c15);
    }

    narrow_chain_spec(class_count)
}

pub fn derivation_count_upper_bound(spec: &AcyclicSpec, limit: usize) -> usize {
    let limit = limit.max(1);
    let mut class_counts = Vec::with_capacity(spec.classes.len());
    for edges in &spec.classes {
        let mut total = 0usize;
        for edge in edges {
            let mut edge_total = 1usize;
            for &child in &edge.children {
                edge_total = edge_total.saturating_mul(class_counts[child]);
                if edge_total > limit {
                    break;
                }
            }
            total = total.saturating_add(edge_total);
            if total > limit {
                total = limit + 1;
                break;
            }
        }
        class_counts.push(total);
    }
    class_counts.last().copied().unwrap_or(0)
}

fn narrow_chain_spec(class_count: usize) -> AcyclicSpec {
    let class_count = class_count.max(1);
    let mut classes = Vec::with_capacity(class_count);
    for class_idx in 0..class_count {
        let children = if class_idx == 0 {
            Vec::new()
        } else {
            vec![class_idx - 1]
        };
        classes.push(vec![EdgeSpec {
            op: format!("bounded_fallback_c{class_idx}"),
            weight: 1,
            children,
        }]);
    }
    AcyclicSpec { classes }
}

pub fn extractor_observations(eg: &EGraph<String>, root: EClassId) -> Vec<Observation> {
    let mut extractor = Extractor::new(eg, label_weight);
    collect_observations(&mut extractor, root)
}

pub fn extractor_observations_with_heuristic(
    eg: &EGraph<String>,
    root: EClassId,
) -> Vec<Observation> {
    let mut extractor = Extractor::new(eg, label_weight).with_heuristic();
    collect_observations(&mut extractor, root)
}

pub fn collect_observations<F>(
    extractor: &mut Extractor<'_, String, TropicalWeight, F>,
    root: EClassId,
) -> Vec<Observation>
where
    F: Fn(&ENode<String>) -> TropicalWeight,
{
    let extracted = extractor.derivations(root).collect_checked();
    assert_eq!(
        extracted.completeness,
        ExtractionCompleteness::Complete,
        "generated acyclic observation helpers require complete extraction"
    );
    extracted
        .value
        .into_iter()
        .map(|d| Observation {
            weight: d.weight,
            key: d.key.clone(),
            op: d.op.clone(),
        })
        .collect()
}

pub fn oracle_observations(eg: &EGraph<String>, root: EClassId) -> Vec<Observation> {
    oracle_derivations(eg, root)
        .into_iter()
        .map(|d| Observation { weight: d.weight, key: d.key, op: d.op })
        .collect()
}

pub fn assert_observations_eq(actual: &[Observation], expected: &[Observation], context: &str) {
    assert_eq!(actual.len(), expected.len(), "{context}: derivation count mismatch");
    for (idx, (left, right)) in actual.iter().zip(expected).enumerate() {
        assert_eq!(left, right, "{context}: first derivation mismatch at index {idx}");
    }
}

fn oracle_derivations(eg: &EGraph<String>, root: EClassId) -> Vec<OracleDerivation> {
    let mut stack = BTreeSet::new();
    let mut derivations = oracle_class(eg, eg.find(root), &mut stack);
    derivations.sort_by(|left, right| {
        left.weight
            .cmp(&right.weight)
            .then_with(|| left.key.cmp(&right.key))
    });
    derivations
}

fn oracle_class(
    eg: &EGraph<String>,
    class: EClassId,
    stack: &mut BTreeSet<EClassId>,
) -> Vec<OracleDerivation> {
    let class = eg.find(class);
    if !stack.insert(class) {
        return Vec::new();
    }

    let mut by_key = ContentKeyMap::default();
    for node in eg.nodes(class) {
        for derivation in oracle_node(eg, node, stack) {
            if !derivation.weight.is_zero() && by_key.get(&derivation.key).is_none() {
                by_key.insert(derivation.key.clone(), derivation);
            }
        }
    }

    stack.remove(&class);
    by_key.into_values().collect()
}

fn oracle_node(
    eg: &EGraph<String>,
    node: &ENode<String>,
    stack: &mut BTreeSet<EClassId>,
) -> Vec<OracleDerivation> {
    let mut partials = vec![(label_weight(node), Vec::<Rc<OracleDerivation>>::new())];

    for &child in &node.children {
        let child_derivations = oracle_class(eg, child, stack);
        if child_derivations.is_empty() {
            return Vec::new();
        }
        let child_derivations: Vec<_> = child_derivations.into_iter().map(Rc::new).collect();
        let mut next_partials = Vec::new();
        for (weight, children) in &partials {
            for child_derivation in &child_derivations {
                let mut next_children = children.clone();
                next_children.push(Rc::clone(child_derivation));
                next_partials.push((weight.times(&child_derivation.weight), next_children));
            }
        }
        partials = next_partials;
    }

    partials
        .into_iter()
        .map(|(weight, children)| {
            let mut op_bytes = Vec::new();
            node.op.write_content(&mut op_bytes);
            let mut key_bytes = Vec::new();
            write_ordered_framed(&mut key_bytes, &op_bytes);
            key_bytes.extend_from_slice(&(children.len() as u64).to_be_bytes());
            for child in &children {
                key_bytes.extend_from_slice(child.key.as_bytes());
            }
            OracleDerivation {
                weight,
                key: ContentKey::from_bytes(key_bytes),
                op: node.op.clone(),
            }
        })
        .collect()
}

pub fn derivation_size(d: &Derivation<String, TropicalWeight>) -> usize {
    1 + d
        .children
        .iter()
        .map(|child| derivation_size(child))
        .sum::<usize>()
}
