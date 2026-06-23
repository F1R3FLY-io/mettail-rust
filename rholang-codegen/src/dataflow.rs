//! E3 — value-level Rholang **dataflow** assembler for nested native-fold scalar expressions.
//!
//! The single-op path ([`crate::invocation`] / the macro `rho_invocation`) lowers ONE scalar rule
//! whose operands are ground literals to a single contract call `@"L"!(a, b, @ret)`. This module
//! generalizes that to a NESTED expression tree (`(2+3)*(4-1)`) by composing one contract call per
//! internal node, wiring each node's result to its parent through a fresh intermediate channel —
//! a Rholang **dataflow graph** whose evaluation order is enforced purely by data dependencies.
//!
//! It is RUNTIME-FREE (depends only on `models` + the codegen ABI types), so the `Par` construction
//! is unit-testable here without the f1r3node Rho runtime. The per-language tree WALK that produces
//! the [`RhoDataflowNode`] list lives in the macro emitter (`macros/.../rho_dataflow.rs`), which
//! downcasts the concrete typed AST; this module only assembles the `Par` from that node list.
//!
//! ## Shape (for `(2+3)*(4-1)`, contracts `@"AddInt"`/`@"SubInt"`/`@"MulInt"` already installed)
//! ```text
//!   @"AddInt"!(2, 3, @"__e3_c0")                       // leaf-only node → bare producer send
//! | @"SubInt"!(4, 1, @"__e3_c1")
//! | for (l <- @"__e3_c0" & r <- @"__e3_c1") {          // node with node-operands → multi-bind JOIN
//!       @"MulInt"!(*l, *r, @"OUT")                     //   …whose body calls the parent contract
//!   }
//! ```
//! The persistent `@"<Label>"` contracts (emitted by [`crate::lower::lower_language_def`]) are
//! parallel-composed with this `call` `Par` at run time via `Par::append` — this module never
//! re-emits them. The result rides the existing `RunWithCallAndObserve{Ints,Bools,Strings}` path.
//!
//! ## Why this construction is sound + simple
//! * **Intermediate channels are quoted ground names** `@"__e3_c<i>"` (not `new`-bound), so they
//!   carry no de-Bruijn index — the ONLY bound variables are a JOIN's received values, local to its
//!   own body. The send-channel↔receive-source rendezvous works exactly as the proven `@"OUT"`
//!   return channel of the single-op path (a gstring name passed as the contract's `ret` argument).
//! * **Multi-bind JOIN** (one [`ReceiveBind`] per node-operand, `bind_count = m`) mirrors rhocalc's
//!   `PInputs` lowering verbatim; the k-th joined channel's received value is `BoundVar(m-1-k)`
//!   (the `extend_env` convention: binder `i` of `m` ↦ index `m-1-i`).
//! * Every operand is either ground (a leaf literal `Par`) or a JOIN-bound value filtered out by
//!   `bind_count`, so **`locally_free` is empty on every component** — the assembled `call` is a
//!   closed term (required for `inj`), asserted structurally (NOT via `debug_assert!`, which is
//!   compiled out in release).

use models::create_bit_vector;
use models::rhoapi::{Par, Receive, ReceiveBind, Send};
use models::rust::utils::{new_boundvar_par, new_freevar_par, new_gstring_par, new_send_par};

use crate::ast::RhoAstLiteral;
use crate::lower::RhoScalarType;

/// Prefix for the quoted ground names used as intermediate dataflow channels. Distinct from any
/// contract label (`@"AddInt"`) and from the output channel (`@"OUT"`); a fresh in-memory runtime
/// per `exec` keeps each channel linear (one send, one receive).
const CHANNEL_PREFIX: &str = "__e3_c";

/// An operand of a dataflow node: either a ground leaf literal, or a reference (by post-order index)
/// to another internal node whose contract result flows in on an intermediate channel.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RhoDataflowChild {
    /// A ground scalar literal operand (emitted inline in the producer/consumer send).
    Leaf(RhoAstLiteral),
    /// A reference to internal node `nodes[index]`; its result arrives on `@"__e3_c<index>"`.
    Node(usize),
}

/// One internal node of the dataflow = one scalar-contract call. `label` is the contract channel
/// name (the rule label, the constructor name); `operands` are its arguments in declared order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RhoDataflowNode {
    pub label: String,
    pub operands: Vec<RhoDataflowChild>,
}

/// A compiled dataflow invocation: the closed `call` `Par`, the channel the root result is observed
/// on, and the root's scalar type (selects the `RunWithCallAndObserve{Ints,Bools,Strings}` variant).
#[derive(Debug, Clone, PartialEq)]
pub struct RhoFoldDataflowInvocation {
    pub call: Par,
    pub out_channel: String,
    pub result_type: RhoScalarType,
}

/// The three-valued outcome of attempting to lower a fold expression to a Rho dataflow. `Defer` is
/// NOT an error: it means "this term must run on Dovetail instead" (a non-scalar / free-variable /
/// `÷0` / overflow term whose Rho contract would hard-error where Dovetail safely defers). The
/// macro emitter maps `Defer ↦ RhoBackendInvocation::DeferToDovetailReport`, `Run ↦
/// RunWithCallAndObserve*`.
#[derive(Debug, Clone, PartialEq)]
pub enum RhoFoldDataflowDisposition {
    Run(RhoFoldDataflowInvocation),
    Defer,
}

/// A structural inconsistency in a [`RhoDataflowNode`] list — a generator bug, surfaced as a hard
/// error (never silently producing a malformed `Par` that would hard-error inside `inj`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RhoDataflowError {
    /// The root is `Node(i)` but the node list is empty, or `i` is out of range.
    RootIndexOutOfRange { root: usize, node_count: usize },
    /// A node operand references `Node(j)` with `j` out of range.
    ChildIndexOutOfRange { node: usize, child: usize, node_count: usize },
    /// A node operand references `Node(j)` with `j >= i` (not strictly post-order — would deadlock,
    /// since a node may only consume channels produced by EARLIER nodes).
    NonPostOrderChild { node: usize, child: usize },
    /// A node has no operands (a nullary contract is not part of the scalar ABI).
    EmptyOperands { node: usize },
    /// The empty channel name (would be an invalid send/receive source).
    EmptyChannelName,
    /// A leaf literal could not be lowered to a `Par` (only the scalar trio is expected, which is
    /// infallible; any other literal is a generator bug).
    LiteralBuildError(String),
}

impl core::fmt::Display for RhoDataflowError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            RhoDataflowError::RootIndexOutOfRange { root, node_count } => {
                write!(f, "dataflow root Node({root}) out of range (node_count={node_count})")
            },
            RhoDataflowError::ChildIndexOutOfRange { node, child, node_count } => write!(
                f,
                "dataflow node {node} operand Node({child}) out of range (node_count={node_count})"
            ),
            RhoDataflowError::NonPostOrderChild { node, child } => write!(
                f,
                "dataflow node {node} references non-earlier Node({child}) (must be strictly post-order)"
            ),
            RhoDataflowError::EmptyOperands { node } => {
                write!(f, "dataflow node {node} has no operands")
            },
            RhoDataflowError::EmptyChannelName => write!(f, "dataflow channel name is empty"),
            RhoDataflowError::LiteralBuildError(reason) => {
                write!(f, "dataflow leaf literal could not be lowered: {reason}")
            },
        }
    }
}

/// The quoted ground name `@"__e3_c<index>"` used to carry node `index`'s result to its parent.
fn intermediate_channel(index: usize) -> String {
    format!("{CHANNEL_PREFIX}{index}")
}

/// Lower one leaf literal to its ground `Par` (infallible for the scalar trio; any failure is a
/// generator bug surfaced as a hard error rather than a malformed `Par`).
fn leaf_par(lit: &RhoAstLiteral) -> Result<Par, RhoDataflowError> {
    lit.try_to_par()
        .map_err(|err| RhoDataflowError::LiteralBuildError(format!("{err:?}")))
}

/// Build the producer/consumer process `Par` for one internal node: a bare producer `Send`
/// (leaf-only operands) or a multi-bind JOIN `Receive` whose body is the contract call (≥1 node
/// operand). `ret_channel` is where this node publishes its result (`out_channel` for the root,
/// `@"__e3_c<self>"` otherwise).
fn build_node_process(
    node_index: usize,
    node: &RhoDataflowNode,
    ret_channel: &str,
    node_count: usize,
) -> Result<Par, RhoDataflowError> {
    if node.operands.is_empty() {
        return Err(RhoDataflowError::EmptyOperands { node: node_index });
    }
    if ret_channel.is_empty() {
        return Err(RhoDataflowError::EmptyChannelName);
    }

    // Node-operand references (each needs a JOIN bind); validate they are strictly earlier.
    let node_operands: Vec<usize> = node
        .operands
        .iter()
        .filter_map(|c| match c {
            RhoDataflowChild::Node(j) => Some(*j),
            RhoDataflowChild::Leaf(_) => None,
        })
        .collect();
    for &child in &node_operands {
        if child >= node_count {
            return Err(RhoDataflowError::ChildIndexOutOfRange {
                node: node_index,
                child,
                node_count,
            });
        }
        if child >= node_index {
            return Err(RhoDataflowError::NonPostOrderChild { node: node_index, child });
        }
    }
    let bind_count = node_operands.len();

    // The contract call's data = each operand in declared order, then the return channel last.
    // A node operand at JOIN-bind position k (0-based among node operands, in operand order) is the
    // received value `BoundVar(bind_count - 1 - k)`; a leaf operand is its ground literal `Par`.
    let mut data: Vec<Par> = Vec::with_capacity(node.operands.len() + 1);
    let mut bound_indices: Vec<usize> = Vec::with_capacity(bind_count);
    let mut next_bind: usize = 0;
    for operand in &node.operands {
        match operand {
            RhoDataflowChild::Leaf(lit) => data.push(leaf_par(lit)?),
            RhoDataflowChild::Node(_) => {
                let debruijn = bind_count - 1 - next_bind;
                next_bind += 1;
                bound_indices.push(debruijn);
                data.push(new_boundvar_par(debruijn as i32, Vec::new(), false));
            },
        }
    }
    // The return channel is a ground quoted name (no de-Bruijn shift even inside the JOIN body).
    data.push(new_gstring_par(ret_channel.to_string(), Vec::new(), false));

    let channel = new_gstring_par(node.label.clone(), Vec::new(), false);
    // The send's locally_free is exactly the JOIN-bound indices it references (none for a bare send).
    let body_lf = create_bit_vector(&bound_indices);
    let send_par =
        new_send_par(channel, data, false, body_lf.clone(), false, body_lf.clone(), false);

    if bind_count == 0 {
        // Leaf-only node: a bare producer send (closed — all operands ground).
        Ok(send_par)
    } else {
        // Node with node-operands: a multi-bind JOIN consuming each node-operand's channel, whose
        // body is the contract-call send. One ReceiveBind per node operand (free_count 1 each); the
        // receive's locally_free is empty (the body's bound indices are < bind_count → all filtered,
        // and the ground sources contribute nothing). Mirrors `lower::contract_ast` + rhocalc PInputs.
        let binds: Vec<ReceiveBind> = node_operands
            .iter()
            .map(|&child| ReceiveBind {
                patterns: vec![new_freevar_par(0, Vec::new())],
                source: Some(new_gstring_par(intermediate_channel(child), Vec::new(), false)),
                remainder: None,
                free_count: 1,
            })
            .collect();
        let receive = Receive {
            binds,
            body: Some(send_par),
            persistent: false,
            peek: false,
            bind_count: bind_count as i32,
            locally_free: Vec::new(),
            connective_used: false,
            condition: None,
        };
        Ok(Par::default().with_receives(vec![receive]))
    }
}

/// Assemble the closed dataflow `call` `Par` from a post-order node list and the root operand.
///
/// `root` is the whole expression's top operand: a bare `Leaf` (the term is already a single
/// literal → emit `@"<out>"!(lit)`), or `Node(root_index)` (the root contract publishes to
/// `out_channel` directly; every other node publishes to its `@"__e3_c<i>"`). All node processes
/// compose in parallel; the result is a closed term (empty top-level `locally_free`), validated
/// structurally with hard `Result` checks.
pub fn build_dataflow_call_par(
    nodes: &[RhoDataflowNode],
    root: &RhoDataflowChild,
    out_channel: &str,
) -> Result<Par, RhoDataflowError> {
    if out_channel.is_empty() {
        return Err(RhoDataflowError::EmptyChannelName);
    }

    let root_index = match root {
        RhoDataflowChild::Leaf(lit) => {
            // The whole expression is a single literal: observe it directly on the output channel.
            let send = new_send_par(
                new_gstring_par(out_channel.to_string(), Vec::new(), false),
                vec![leaf_par(lit)?],
                false,
                Vec::new(),
                false,
                Vec::new(),
                false,
            );
            return Ok(send);
        },
        RhoDataflowChild::Node(i) => *i,
    };
    if root_index >= nodes.len() {
        return Err(RhoDataflowError::RootIndexOutOfRange {
            root: root_index,
            node_count: nodes.len(),
        });
    }

    // Each node lowers to one parallel component (a producer send or a JOIN receive); collect them
    // into a single closed `Par`. (A send-`Par` contributes `.sends`; a JOIN-`Par` `.receives`.)
    let mut sends: Vec<Send> = Vec::new();
    let mut receives: Vec<Receive> = Vec::new();
    for (index, node) in nodes.iter().enumerate() {
        let ret = if index == root_index {
            out_channel.to_string()
        } else {
            intermediate_channel(index)
        };
        let mut process = build_node_process(index, node, &ret, nodes.len())?;
        sends.append(&mut process.sends);
        receives.append(&mut process.receives);
    }

    Ok(Par::default().with_sends(sends).with_receives(receives))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn int(v: i64) -> RhoDataflowChild {
        RhoDataflowChild::Leaf(RhoAstLiteral::Int(v))
    }

    /// `(2+3)*(4-1)` → 2 producer sends + 1 JOIN whose body calls `@"MulInt"` to `@"OUT"`.
    #[test]
    fn nested_two_level_dataflow_par_shape() {
        let nodes = vec![
            RhoDataflowNode { label: "AddInt".into(), operands: vec![int(2), int(3)] },
            RhoDataflowNode { label: "SubInt".into(), operands: vec![int(4), int(1)] },
            RhoDataflowNode {
                label: "MulInt".into(),
                operands: vec![RhoDataflowChild::Node(0), RhoDataflowChild::Node(1)],
            },
        ];
        let par = build_dataflow_call_par(&nodes, &RhoDataflowChild::Node(2), "OUT")
            .expect("well-formed nested dataflow must build");

        // Two leaf-only producers (AddInt, SubInt) + one JOIN (MulInt over both children).
        assert_eq!(par.sends.len(), 2, "two bare producer sends");
        assert_eq!(par.receives.len(), 1, "one multi-bind JOIN for the root MulInt");
        assert!(par.locally_free.is_empty(), "the assembled call must be a closed term");

        let join = &par.receives[0];
        assert_eq!(join.bind_count, 2, "JOIN binds both child channels");
        assert_eq!(join.binds.len(), 2, "one ReceiveBind per node-operand");
        assert!(join.binds.iter().all(|b| b.free_count == 1), "each bind binds one value");
        assert!(join.locally_free.is_empty(), "the JOIN is closed");
        let sources: Vec<&Par> = join.binds.iter().filter_map(|b| b.source.as_ref()).collect();
        assert_eq!(sources.len(), 2, "two intermediate-channel sources");

        // The JOIN body is the MulInt call: data = [BoundVar(1), BoundVar(0), @"OUT"].
        let body = join.body.as_ref().expect("JOIN has a body");
        assert_eq!(body.sends.len(), 1, "JOIN body is the parent contract call");
        assert_eq!(body.sends[0].data.len(), 3, "MulInt(lhs, rhs, ret)");
    }

    /// A single-literal term (`exec 15`) → a direct `@"OUT"!(15)`, no contract call.
    #[test]
    fn single_literal_emits_direct_output_send() {
        let par = build_dataflow_call_par(&[], &int(15), "OUT").expect("literal must build");
        assert_eq!(par.sends.len(), 1);
        assert!(par.receives.is_empty());
        assert!(par.locally_free.is_empty());
    }

    /// `not(1 < 2)`-shaped right-nesting: a leaf-only child feeding a unary parent.
    #[test]
    fn unary_over_internal_node_joins_one_channel() {
        let nodes = vec![
            RhoDataflowNode { label: "LtInt".into(), operands: vec![int(1), int(2)] },
            RhoDataflowNode { label: "NotBool".into(), operands: vec![RhoDataflowChild::Node(0)] },
        ];
        let par = build_dataflow_call_par(&nodes, &RhoDataflowChild::Node(1), "OUT")
            .expect("unary-over-node must build");
        assert_eq!(par.sends.len(), 1, "the LtInt producer");
        assert_eq!(par.receives.len(), 1, "the NotBool JOIN over one channel");
        assert_eq!(par.receives[0].bind_count, 1);
    }

    #[test]
    fn forward_child_reference_is_rejected() {
        // Node 0 referencing Node(1) is not post-order (would deadlock) → hard error.
        let nodes = vec![
            RhoDataflowNode { label: "AddInt".into(), operands: vec![RhoDataflowChild::Node(1)] },
            RhoDataflowNode { label: "SubInt".into(), operands: vec![int(4), int(1)] },
        ];
        let err = build_dataflow_call_par(&nodes, &RhoDataflowChild::Node(1), "OUT")
            .expect_err("forward reference must be rejected");
        assert_eq!(err, RhoDataflowError::NonPostOrderChild { node: 0, child: 1 });
    }

    #[test]
    fn out_of_range_root_is_rejected() {
        let err = build_dataflow_call_par(&[], &RhoDataflowChild::Node(0), "OUT")
            .expect_err("empty node list with a Node root must error");
        assert_eq!(err, RhoDataflowError::RootIndexOutOfRange { root: 0, node_count: 0 });
    }

    #[test]
    fn empty_out_channel_is_rejected() {
        let err = build_dataflow_call_par(&[], &int(1), "")
            .expect_err("empty out channel must error");
        assert_eq!(err, RhoDataflowError::EmptyChannelName);
    }
}
