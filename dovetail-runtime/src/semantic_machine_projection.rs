//! One-way bridge from the checked grammar-core semantic machine carrier into
//! Dovetail's existing exact-keyed e-graph.
//!
//! This module does not parse, evaluate, or install a language. It validates a
//! flat backward-reference arena, canonicalizes only explicitly unordered
//! child sets by Dovetail's exact class keys, and inserts through the existing
//! bounded e-graph API.

use dovetail::egraph::{EClassId, EGraph, EGraphConfig, ENode};
use dovetail::key::{ContentKey, FramedSemanticOperator};
use mettail_grammar_core::{
    MachineChildOrderV1, SemanticMachineAdmissionLimits, SemanticMachineImageError,
    SemanticMachineImageV1, SemanticMachineProjectionContext, SemanticMachineTermV1,
    SemanticTermImageV1,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemanticEGraphProjectionError {
    LimitExceeded(&'static str),
    Reference { node: u32, target: u32 },
    Root(u32),
    DiscriminantLabelConflict(u32),
    NodeBudget { node: u32 },
    LengthOverflow,
    Allocation,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SemanticTermEGraphError {
    Machine(SemanticMachineImageError),
    EGraph(SemanticEGraphProjectionError),
}

/// Reusable, immutable bridge from one installed semantic-machine image into
/// fresh bounded Dovetail e-graphs.
///
/// The grammar-core projection context keeps the signature, grammar,
/// capability bindings, and limits inseparable. Cache and scheduling layers
/// may reuse this projector, but each call creates a fresh e-graph and grants
/// no authority beyond the supplied checked context.
pub struct SemanticEGraphProjector<'a> {
    image: &'a SemanticMachineImageV1,
    context: SemanticMachineProjectionContext<'a>,
    egraph_config: EGraphConfig,
}

impl<'a> SemanticEGraphProjector<'a> {
    pub fn new(
        image: &'a SemanticMachineImageV1,
        context: SemanticMachineProjectionContext<'a>,
        egraph_config: EGraphConfig,
    ) -> Self {
        Self { image, context, egraph_config }
    }

    pub fn project(
        &self,
        term: &SemanticTermImageV1,
    ) -> Result<SemanticEGraphProjection, SemanticTermEGraphError> {
        let machine = self
            .image
            .project(term, self.context)
            .map_err(SemanticTermEGraphError::Machine)?;
        load_semantic_machine_term(
            &machine,
            self.egraph_config.clone(),
            self.context.machine_limits(),
        )
        .map_err(SemanticTermEGraphError::EGraph)
    }
}

/// Result of loading one semantic-machine forest into Dovetail. The e-graph is
/// the existing production engine; this wrapper only keeps the source-node and
/// root class correspondence needed by later rule/report stages.
pub struct SemanticEGraphProjection {
    egraph: EGraph<FramedSemanticOperator>,
    node_classes: Vec<EClassId>,
    roots: Vec<EClassId>,
    operator_labels: Vec<(u32, String)>,
}

impl SemanticEGraphProjection {
    pub fn egraph(&self) -> &EGraph<FramedSemanticOperator> {
        &self.egraph
    }

    pub fn egraph_mut(&mut self) -> &mut EGraph<FramedSemanticOperator> {
        &mut self.egraph
    }

    pub fn node_classes(&self) -> &[EClassId] {
        &self.node_classes
    }

    pub fn roots(&self) -> &[EClassId] {
        &self.roots
    }

    pub fn operator_label(&self, stable_discriminant: u32) -> Option<&str> {
        self.operator_labels
            .binary_search_by_key(&stable_discriminant, |(discriminant, _)| *discriminant)
            .ok()
            .map(|index| self.operator_labels[index].1.as_str())
    }

    pub fn canonical_root_keys(&self) -> Vec<ContentKey> {
        self.roots
            .iter()
            .map(|root| self.egraph.canonical_class_key(*root))
            .collect()
    }
}

/// Insert a checked, source-neutral machine term through Dovetail's bounded
/// `try_add_with_budget` seam. References are resolved iteratively and must
/// point backward, matching [`SemanticMachineTermV1`]'s flat-arena contract.
pub fn load_semantic_machine_term(
    term: &SemanticMachineTermV1,
    egraph_config: EGraphConfig,
    limits: SemanticMachineAdmissionLimits,
) -> Result<SemanticEGraphProjection, SemanticEGraphProjectionError> {
    enforce_limit(term.nodes.len(), limits.max_projected_nodes, "projected nodes")?;
    let operator_labels = validated_discriminant_labels(term)?;
    let mut egraph = EGraph::with_config(egraph_config);
    let mut node_classes = empty_vec(term.nodes.len())?;
    let mut child_count = 0usize;
    let mut payload_bytes = 0usize;

    for (node_index, node) in term.nodes.iter().enumerate() {
        let node_index = u32::try_from(node_index)
            .map_err(|_| SemanticEGraphProjectionError::LimitExceeded("projected nodes"))?;
        for segment in &node.operator.payload_segments {
            enforce_limit(segment.len(), limits.max_segment_bytes, "projected segment bytes")?;
            payload_bytes = payload_bytes
                .checked_add(segment.len())
                .ok_or(SemanticEGraphProjectionError::LengthOverflow)?;
            enforce_limit(
                payload_bytes,
                limits.max_projected_payload_bytes,
                "projected payload bytes",
            )?;
        }
        child_count = child_count
            .checked_add(node.children.len())
            .ok_or(SemanticEGraphProjectionError::LengthOverflow)?;
        enforce_limit(child_count, limits.max_projected_children, "projected children")?;
        let mut children = empty_vec(node.children.len())?;
        for target in &node.children {
            let child = node_classes.get(*target as usize).copied().ok_or(
                SemanticEGraphProjectionError::Reference { node: node_index, target: *target },
            )?;
            children.push(child);
        }
        if node.child_order == MachineChildOrderV1::CanonicalExactKey {
            children = canonicalize_children(&egraph, children)?;
        }
        let operator = FramedSemanticOperator::new(
            node.operator.stable_discriminant,
            copy_segments(&node.operator.payload_segments)?,
        );
        let class = egraph
            .try_add_with_budget(ENode::new(operator, children))
            .ok_or(SemanticEGraphProjectionError::NodeBudget { node: node_index })?;
        node_classes.push(class);
    }

    let mut roots = empty_vec(term.roots.len())?;
    for root in &term.roots {
        roots.push(
            node_classes
                .get(*root as usize)
                .copied()
                .ok_or(SemanticEGraphProjectionError::Root(*root))?,
        );
    }
    Ok(SemanticEGraphProjection {
        egraph,
        node_classes,
        roots,
        operator_labels,
    })
}

fn validated_discriminant_labels(
    term: &SemanticMachineTermV1,
) -> Result<Vec<(u32, String)>, SemanticEGraphProjectionError> {
    let mut labels = empty_vec(term.nodes.len())?;
    for node in &term.nodes {
        labels.push((node.operator.stable_discriminant, node.operator.label.as_str()));
    }
    labels.sort_unstable();
    for adjacent in labels.windows(2) {
        if adjacent[0].0 == adjacent[1].0 && adjacent[0].1 != adjacent[1].1 {
            return Err(SemanticEGraphProjectionError::DiscriminantLabelConflict(adjacent[0].0));
        }
    }
    let mut unique = empty_vec(labels.len())?;
    for (discriminant, label) in labels {
        if unique
            .last()
            .is_some_and(|(existing, _)| *existing == discriminant)
        {
            continue;
        }
        unique.push((discriminant, copy_string(label)?));
    }
    Ok(unique)
}

/// End-to-end source-neutral seam used by runtime-defined languages: verify the
/// canonical term and its fingerprint-bound projection image, compile the flat
/// machine arena, then load it into the existing bounded Dovetail e-graph.
pub fn project_semantic_term_to_egraph(
    projector: &SemanticEGraphProjector<'_>,
    term: &SemanticTermImageV1,
) -> Result<SemanticEGraphProjection, SemanticTermEGraphError> {
    projector.project(term)
}

fn canonicalize_children(
    egraph: &EGraph<FramedSemanticOperator>,
    children: Vec<EClassId>,
) -> Result<Vec<EClassId>, SemanticEGraphProjectionError> {
    let mut keyed = empty_vec(children.len())?;
    for child in children {
        keyed.push((egraph.canonical_class_key(child), child));
    }
    keyed.sort_unstable_by(|(left_key, left_class), (right_key, right_class)| {
        left_key
            .cmp(right_key)
            .then_with(|| left_class.cmp(right_class))
    });
    let mut ordered = empty_vec(keyed.len())?;
    ordered.extend(keyed.into_iter().map(|(_, child)| child));
    Ok(ordered)
}

fn copy_segments(segments: &[Vec<u8>]) -> Result<Vec<Vec<u8>>, SemanticEGraphProjectionError> {
    let mut output = empty_vec(segments.len())?;
    for segment in segments {
        let mut copied = empty_vec(segment.len())?;
        copied.extend_from_slice(segment);
        output.push(copied);
    }
    Ok(output)
}

fn copy_string(value: &str) -> Result<String, SemanticEGraphProjectionError> {
    let mut output = String::new();
    output
        .try_reserve_exact(value.len())
        .map_err(|_| SemanticEGraphProjectionError::Allocation)?;
    output.push_str(value);
    Ok(output)
}

fn empty_vec<T>(capacity: usize) -> Result<Vec<T>, SemanticEGraphProjectionError> {
    let mut values = Vec::new();
    values
        .try_reserve_exact(capacity)
        .map_err(|_| SemanticEGraphProjectionError::Allocation)?;
    Ok(values)
}

fn enforce_limit(
    actual: usize,
    limit: usize,
    name: &'static str,
) -> Result<(), SemanticEGraphProjectionError> {
    if actual > limit {
        return Err(SemanticEGraphProjectionError::LimitExceeded(name));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_grammar_core::{SemanticMachineNodeV1, SemanticMachineOperatorV1};

    fn node(
        discriminant: u32,
        payload: &[u8],
        label: &str,
        children: Vec<u32>,
        child_order: MachineChildOrderV1,
    ) -> SemanticMachineNodeV1 {
        SemanticMachineNodeV1 {
            operator: SemanticMachineOperatorV1 {
                stable_discriminant: discriminant,
                payload_segments: vec![payload.to_vec()],
                label: label.into(),
            },
            children,
            child_order,
        }
    }

    #[test]
    fn unordered_children_use_exact_class_key_order() {
        let term = SemanticMachineTermV1 {
            nodes: vec![
                node(1, b"b", "leaf", Vec::new(), MachineChildOrderV1::Ordered),
                node(1, b"a", "leaf", Vec::new(), MachineChildOrderV1::Ordered),
                node(2, b"bag", "bag", vec![0, 1], MachineChildOrderV1::CanonicalExactKey),
                node(2, b"bag", "bag", vec![1, 0], MachineChildOrderV1::CanonicalExactKey),
            ],
            roots: vec![2, 3],
        };
        let projection = load_semantic_machine_term(
            &term,
            EGraphConfig { max_nodes: 8 },
            SemanticMachineAdmissionLimits::default(),
        )
        .expect("projection");
        assert_eq!(projection.roots()[0], projection.roots()[1]);
        assert_eq!(projection.canonical_root_keys()[0], projection.canonical_root_keys()[1]);
        assert_eq!(projection.operator_label(2), Some("bag"));
    }

    #[test]
    fn malformed_backward_reference_fails_closed() {
        let term = SemanticMachineTermV1 {
            nodes: vec![node(1, b"bad", "bad", vec![0], MachineChildOrderV1::Ordered)],
            roots: vec![0],
        };
        assert!(matches!(
            load_semantic_machine_term(
                &term,
                EGraphConfig { max_nodes: 2 },
                SemanticMachineAdmissionLimits::default(),
            ),
            Err(SemanticEGraphProjectionError::Reference { node: 0, target: 0 })
        ));
    }

    #[test]
    fn egraph_budget_fails_without_partial_result() {
        let term = SemanticMachineTermV1 {
            nodes: vec![
                node(1, b"a", "leaf", Vec::new(), MachineChildOrderV1::Ordered),
                node(1, b"b", "leaf", Vec::new(), MachineChildOrderV1::Ordered),
            ],
            roots: vec![1],
        };
        assert!(matches!(
            load_semantic_machine_term(
                &term,
                EGraphConfig { max_nodes: 1 },
                SemanticMachineAdmissionLimits::default(),
            ),
            Err(SemanticEGraphProjectionError::NodeBudget { node: 1 })
        ));
    }

    #[test]
    fn pathmap_empty_modes_keep_distinct_exact_root_keys() {
        let mut nodes = Vec::new();
        let mut roots = Vec::new();
        for tag in [0, 1, 2] {
            let mode = u32::try_from(nodes.len()).expect("small mode node");
            nodes.push(node(108, &[tag], "pathmap-mode", Vec::new(), MachineChildOrderV1::Ordered));
            let root = u32::try_from(nodes.len()).expect("small root node");
            nodes.push(node(13, b"pathmap", "pathmap", vec![mode], MachineChildOrderV1::Ordered));
            roots.push(root);
        }
        let projection = load_semantic_machine_term(
            &SemanticMachineTermV1 { nodes, roots },
            EGraphConfig { max_nodes: 8 },
            SemanticMachineAdmissionLimits::default(),
        )
        .expect("mode-preserving PathMap projection");
        let keys = projection.canonical_root_keys();
        assert_ne!(keys[0], keys[1]);
        assert_ne!(keys[0], keys[2]);
        assert_ne!(keys[1], keys[2]);
    }
}
