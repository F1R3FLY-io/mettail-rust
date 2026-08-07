//! Static channel-deadlock analysis for generated Rho communication networks.
//!
//! This is a conservative compile-time gate for M-RHO.4. It does not try to
//! prove semantic convergence; the Rocq bridge owns that. The analyzer checks
//! the generated communication shape for two structural hazards before a
//! language can flip to the Rho backend by default:
//!
//! - a contract waits on a static channel that is neither externally provided
//!   nor emitted by any generated contract;
//! - a set of contracts can only enable each other through a closed wait cycle,
//!   with no external or seed channel entering the set.

use std::collections::{BTreeMap, BTreeSet};

/// A generated contract's static channel footprint.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContractFlow {
    pub name: String,
    pub waits_on: Vec<String>,
    pub emits: Vec<String>,
}

impl ContractFlow {
    pub fn new(
        name: impl Into<String>,
        waits_on: impl IntoIterator<Item = impl Into<String>>,
        emits: impl IntoIterator<Item = impl Into<String>>,
    ) -> Self {
        Self {
            name: name.into(),
            waits_on: waits_on.into_iter().map(Into::into).collect(),
            emits: emits.into_iter().map(Into::into).collect(),
        }
    }

    /// A Rho service contract whose entry channel is intentionally supplied by
    /// the caller. Static response channels, if any, can be listed in `emits`.
    pub fn exported_service(
        name: impl Into<String>,
        emits: impl IntoIterator<Item = impl Into<String>>,
    ) -> Self {
        let name = name.into();
        Self::new(name.clone(), [name], emits)
    }
}

/// Static communication network used by the analyzer.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ChannelNetwork {
    pub contracts: Vec<ContractFlow>,
    pub external_channels: BTreeSet<String>,
    pub seed_channels: BTreeSet<String>,
}

impl ChannelNetwork {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_contract(mut self, contract: ContractFlow) -> Self {
        self.contracts.push(contract);
        self
    }

    pub fn with_external(mut self, channel: impl Into<String>) -> Self {
        self.external_channels.insert(channel.into());
        self
    }

    pub fn with_seed(mut self, channel: impl Into<String>) -> Self {
        self.seed_channels.insert(channel.into());
        self
    }
}

/// A structural issue that blocks `NoNewDeadlocks`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ChannelDeadlockDiagnostic {
    MissingProducer {
        contract: String,
        channel: String,
    },
    ClosedWaitCycle {
        contracts: Vec<String>,
        channels: Vec<String>,
    },
}

/// Full analyzer output suitable for pgmcp/task logs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ChannelDeadlockReport {
    pub diagnostics: Vec<ChannelDeadlockDiagnostic>,
    pub waiting_channels: BTreeSet<String>,
    pub emitted_channels: BTreeSet<String>,
    pub external_channels: BTreeSet<String>,
    pub seed_channels: BTreeSet<String>,
}

impl ChannelDeadlockReport {
    pub fn no_new_deadlocks(&self) -> bool {
        self.diagnostics.is_empty()
    }
}

fn channel_producers(network: &ChannelNetwork) -> BTreeMap<String, BTreeSet<usize>> {
    let mut producers: BTreeMap<String, BTreeSet<usize>> = BTreeMap::new();
    for (idx, contract) in network.contracts.iter().enumerate() {
        for channel in &contract.emits {
            producers.entry(channel.clone()).or_default().insert(idx);
        }
    }
    producers
}

fn channel_consumers(network: &ChannelNetwork) -> BTreeMap<String, BTreeSet<usize>> {
    let mut consumers: BTreeMap<String, BTreeSet<usize>> = BTreeMap::new();
    for (idx, contract) in network.contracts.iter().enumerate() {
        for channel in &contract.waits_on {
            consumers.entry(channel.clone()).or_default().insert(idx);
        }
    }
    consumers
}

fn can_enter_from_outside(
    component: &BTreeSet<usize>,
    network: &ChannelNetwork,
    producers: &BTreeMap<String, BTreeSet<usize>>,
) -> bool {
    for &idx in component {
        for channel in &network.contracts[idx].waits_on {
            if network.external_channels.contains(channel)
                || network.seed_channels.contains(channel)
            {
                return true;
            }
            let Some(channel_producers) = producers.get(channel) else {
                continue;
            };
            if channel_producers
                .iter()
                .any(|producer| !component.contains(producer))
            {
                return true;
            }
        }
    }
    false
}

fn component_wait_channels(component: &BTreeSet<usize>, network: &ChannelNetwork) -> Vec<String> {
    let mut channels = BTreeSet::new();
    for &idx in component {
        channels.extend(network.contracts[idx].waits_on.iter().cloned());
    }
    channels.into_iter().collect()
}

fn component_names(component: &BTreeSet<usize>, network: &ChannelNetwork) -> Vec<String> {
    component
        .iter()
        .map(|idx| network.contracts[*idx].name.clone())
        .collect()
}

fn strongly_connected_components(edges: &[BTreeSet<usize>]) -> Vec<BTreeSet<usize>> {
    struct SccDfs<'a> {
        edges: &'a [Vec<usize>],
        index: usize,
        stack: Vec<usize>,
        on_stack: Vec<bool>,
        indices: Vec<Option<usize>>,
        lowlinks: Vec<usize>,
        components: Vec<BTreeSet<usize>>,
    }

    impl<'a> SccDfs<'a> {
        fn new(edges: &'a [Vec<usize>]) -> Self {
            Self {
                edges,
                index: 0,
                stack: Vec::new(),
                on_stack: vec![false; edges.len()],
                indices: vec![None; edges.len()],
                lowlinks: vec![0; edges.len()],
                components: Vec::new(),
            }
        }

        fn enter(&mut self, node: usize) {
            self.indices[node] = Some(self.index);
            self.lowlinks[node] = self.index;
            self.index += 1;
            self.stack.push(node);
            self.on_stack[node] = true;
        }

        fn visit(&mut self, root: usize) {
            // The frame's successor index is the return address of recursive Tarjan DFS. Keeping
            // adjacency in sorted vectors preserves BTreeSet iteration and component emission order
            // while visiting every vertex and edge once.
            let mut work = vec![(root, 0usize)];
            self.enter(root);
            while let Some((node, next_index)) = work.last_mut() {
                if let Some(&next) = self.edges[*node].get(*next_index) {
                    *next_index += 1;
                    if self.indices[next].is_none() {
                        self.enter(next);
                        work.push((next, 0));
                    } else if self.on_stack[next] {
                        self.lowlinks[*node] = self.lowlinks[*node]
                            .min(self.indices[next].expect("indexed stack node"));
                    }
                    continue;
                }

                let node = *node;
                work.pop();
                if let Some((parent, _)) = work.last() {
                    self.lowlinks[*parent] = self.lowlinks[*parent].min(self.lowlinks[node]);
                }
                if self.lowlinks[node] == self.indices[node].expect("current node indexed") {
                    let mut component = BTreeSet::new();
                    loop {
                        let item = self.stack.pop().expect("SCC root must have stack entries");
                        self.on_stack[item] = false;
                        component.insert(item);
                        if item == node {
                            break;
                        }
                    }
                    self.components.push(component);
                }
            }
        }
    }

    let adjacency = edges
        .iter()
        .map(|successors| successors.iter().copied().collect::<Vec<_>>())
        .collect::<Vec<_>>();
    let mut dfs = SccDfs::new(&adjacency);

    for node in 0..edges.len() {
        if dfs.indices[node].is_none() {
            dfs.visit(node);
        }
    }

    dfs.components
}

/// Analyze generated static channel flow for structural deadlock hazards.
pub fn analyze_channel_deadlocks(network: &ChannelNetwork) -> ChannelDeadlockReport {
    let producers = channel_producers(network);
    let consumers = channel_consumers(network);
    let waiting_channels = consumers.keys().cloned().collect::<BTreeSet<_>>();
    let emitted_channels = producers.keys().cloned().collect::<BTreeSet<_>>();
    let mut diagnostics = Vec::new();

    for contract in &network.contracts {
        for channel in &contract.waits_on {
            if network.external_channels.contains(channel)
                || network.seed_channels.contains(channel)
            {
                continue;
            }
            if !producers.contains_key(channel) {
                diagnostics.push(ChannelDeadlockDiagnostic::MissingProducer {
                    contract: contract.name.clone(),
                    channel: channel.clone(),
                });
            }
        }
    }

    let mut edges = vec![BTreeSet::new(); network.contracts.len()];
    for (producer, contract) in network.contracts.iter().enumerate() {
        for channel in &contract.emits {
            if let Some(channel_consumers) = consumers.get(channel) {
                edges[producer].extend(channel_consumers.iter().copied());
            }
        }
    }

    for component in strongly_connected_components(&edges) {
        let cyclic = component.len() > 1 || component.iter().any(|idx| edges[*idx].contains(idx));
        if !cyclic || can_enter_from_outside(&component, network, &producers) {
            continue;
        }
        diagnostics.push(ChannelDeadlockDiagnostic::ClosedWaitCycle {
            contracts: component_names(&component, network),
            channels: component_wait_channels(&component, network),
        });
    }

    ChannelDeadlockReport {
        diagnostics,
        waiting_channels,
        emitted_channels,
        external_channels: network.external_channels.clone(),
        seed_channels: network.seed_channels.clone(),
    }
}

#[cfg(test)]
#[path = "../tests/support/deadlock_scc_recursive_oracle.rs"]
mod scc_recursive_oracle;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exported_scalar_services_are_not_deadlocks() {
        let network = ChannelNetwork::new()
            .with_external("AddInt")
            .with_external("SubInt")
            .with_contract(ContractFlow::exported_service("AddInt", std::iter::empty::<&str>()))
            .with_contract(ContractFlow::exported_service("SubInt", std::iter::empty::<&str>()));

        let report = analyze_channel_deadlocks(&network);
        assert_eq!(report.diagnostics, Vec::new());
        assert!(report.no_new_deadlocks());
    }

    #[test]
    fn missing_internal_producer_blocks_gate() {
        let network =
            ChannelNetwork::new().with_contract(ContractFlow::new("needs_b", ["b"], ["out"]));

        let report = analyze_channel_deadlocks(&network);
        assert_eq!(
            report.diagnostics,
            vec![ChannelDeadlockDiagnostic::MissingProducer {
                contract: "needs_b".to_string(),
                channel: "b".to_string(),
            }]
        );
        assert!(!report.no_new_deadlocks());
    }

    #[test]
    fn closed_wait_cycle_blocks_gate() {
        let network = ChannelNetwork::new()
            .with_contract(ContractFlow::new("left", ["from_right"], ["from_left"]))
            .with_contract(ContractFlow::new("right", ["from_left"], ["from_right"]));

        let report = analyze_channel_deadlocks(&network);
        assert_eq!(
            report.diagnostics,
            vec![ChannelDeadlockDiagnostic::ClosedWaitCycle {
                contracts: vec!["left".to_string(), "right".to_string()],
                channels: vec!["from_left".to_string(), "from_right".to_string()],
            }]
        );
        assert!(!report.no_new_deadlocks());
    }

    #[test]
    fn seed_breaks_wait_cycle() {
        let network = ChannelNetwork::new()
            .with_seed("from_right")
            .with_contract(ContractFlow::new("left", ["from_right"], ["from_left"]))
            .with_contract(ContractFlow::new("right", ["from_left"], ["from_right"]));

        let report = analyze_channel_deadlocks(&network);
        assert_eq!(report.diagnostics, Vec::new());
        assert!(report.no_new_deadlocks());
    }

    #[test]
    fn outside_producer_breaks_wait_cycle() {
        let network = ChannelNetwork::new()
            .with_contract(ContractFlow::new("source", ["start"], ["from_right"]))
            .with_contract(ContractFlow::new("left", ["from_right"], ["from_left"]))
            .with_contract(ContractFlow::new("right", ["from_left"], ["from_right"]))
            .with_external("start");

        let report = analyze_channel_deadlocks(&network);
        assert_eq!(report.diagnostics, Vec::new());
        assert!(report.no_new_deadlocks());
    }
}
