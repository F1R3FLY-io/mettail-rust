use super::*;

// ══════════════════════════════════════════════════════════════════════════════
// Analysis results (consumed by lint and cost_benefit)
// ══════════════════════════════════════════════════════════════════════════════

/// WPDS analysis results for a grammar.
///
// ══════════════════════════════════════════════════════════════════════════════
// G33: WPDS Call Graph
// ══════════════════════════════════════════════════════════════════════════════

/// A directed edge in the WPDS call graph representing a cross-category call.
#[derive(Debug, Clone)]
pub struct CallEdge {
    /// Category initiating the call.
    pub caller_cat: String,
    /// Category being called.
    pub callee_cat: String,
    /// Number of distinct call sites (Push rules) for this edge.
    pub call_sites: usize,
    /// Sum of weights across all call sites (TropicalWeight → min, Counting → sum).
    pub total_weight: f64,
}

/// Directed, weighted call graph extracted from WPDS Push rules.
///
/// Each edge `(caller → callee)` represents one or more cross-category Push
/// rules. The graph includes SCC decomposition (Tarjan) for recursion analysis.
#[derive(Debug, Clone)]
pub struct WpdsCallGraph {
    /// All directed edges.
    pub edges: Vec<CallEdge>,
    /// Fan-out: number of distinct callees per category.
    pub fan_out: HashMap<String, usize>,
    /// Fan-in: number of distinct callers per category.
    pub fan_in: HashMap<String, usize>,
    /// Strongly connected components (Tarjan). Each SCC is a set of category names.
    /// SCCs of size > 1 indicate mutual recursion; size 1 with self-edge = direct recursion.
    pub sccs: Vec<Vec<String>>,
    /// All category names present in the graph (as caller or callee).
    pub categories: HashSet<String>,
}

/// Extract a directed call graph from WPDS Push rules.
///
/// Linear scan of Push rules produces `CallEdge`s with call-site multiplicity
/// and weight aggregation. Tarjan SCC decomposition identifies recursion.
pub fn extract_call_graph<W: Semiring>(wpds: &Wpds<W>) -> WpdsCallGraph {
    // Aggregate Push rules into edges: (caller_cat, callee_cat) → (count, weight_sum)
    let mut edge_map: HashMap<(String, String), (usize, f64)> = HashMap::new();
    let mut categories: HashSet<String> = HashSet::new();

    for rule in &wpds.rules {
        if let WpdsRule::Push { from_gamma, to_gamma_top, .. } = rule {
            let caller = &from_gamma.category;
            let callee = &to_gamma_top.category;
            // Same-category NTs are Replace (not Push), so no self-edges
            // appear here. Only cross-category Push rules produce call edges.
            if !caller.is_empty() && !callee.is_empty() && caller != callee {
                categories.insert(caller.clone());
                categories.insert(callee.clone());
                let entry = edge_map
                    .entry((caller.clone(), callee.clone()))
                    .or_insert((0, 0.0));
                entry.0 += 1;
                // Use a simple numeric proxy for weight aggregation
                if !rule.weight().is_zero() {
                    entry.1 += 1.0;
                }
            }
        }
    }

    // Also include categories from Replace rules (for categories with no cross-category calls)
    for rule in &wpds.rules {
        let cat = &rule.from_gamma().category;
        if !cat.is_empty() {
            categories.insert(cat.clone());
        }
    }

    let edges: Vec<CallEdge> = edge_map
        .into_iter()
        .map(|((caller, callee), (count, weight))| CallEdge {
            caller_cat: caller,
            callee_cat: callee,
            call_sites: count,
            total_weight: weight,
        })
        .collect();

    // Compute fan-in and fan-out
    let mut fan_out: HashMap<String, usize> = HashMap::new();
    let mut fan_in: HashMap<String, usize> = HashMap::new();
    for edge in &edges {
        *fan_out.entry(edge.caller_cat.clone()).or_insert(0) += 1;
        *fan_in.entry(edge.callee_cat.clone()).or_insert(0) += 1;
    }

    // Tarjan SCC decomposition
    let sccs = tarjan_scc(&categories, &edges);

    WpdsCallGraph { edges, fan_out, fan_in, sccs, categories }
}

/// Tarjan's strongly connected components algorithm on the call graph.
fn tarjan_scc(categories: &HashSet<String>, edges: &[CallEdge]) -> Vec<Vec<String>> {
    let category_list: Vec<String> = categories.iter().cloned().collect();
    let category_index: HashMap<&str, usize> = category_list
        .iter()
        .enumerate()
        .map(|(index, category)| (category.as_str(), index))
        .collect();
    let mut adjacency = vec![Vec::new(); category_list.len()];
    for edge in edges {
        if let (Some(&caller), Some(&callee)) = (
            category_index.get(edge.caller_cat.as_str()),
            category_index.get(edge.callee_cat.as_str()),
        ) {
            adjacency[caller].push(callee);
        }
    }

    crate::graph_algorithms::tarjan_scc(&adjacency)
        .into_iter()
        .map(|component| {
            component
                .into_iter()
                .map(|index| category_list[index].clone())
                .collect()
        })
        .collect()
}

/// Compute the shortest path from any reachable category to a target category
/// in the call graph. Returns a witness trace (list of steps) or empty vec
/// if no path exists.
pub fn shortest_path_witness(
    call_graph: &WpdsCallGraph,
    reachable: &HashSet<String>,
    target_cat: &str,
) -> Vec<String> {
    // BFS from all reachable categories to target
    // Build reverse adjacency: callee → callers
    let mut reverse_adj: HashMap<&str, Vec<&str>> = HashMap::new();
    for edge in &call_graph.edges {
        reverse_adj
            .entry(edge.callee_cat.as_str())
            .or_default()
            .push(edge.caller_cat.as_str());
    }

    // BFS backwards from target_cat to find a reachable category
    let mut visited: HashSet<&str> = HashSet::new();
    let mut parent: HashMap<&str, &str> = HashMap::new();
    let mut queue: VecDeque<&str> = VecDeque::new();

    visited.insert(target_cat);
    queue.push_back(target_cat);

    let mut found_source: Option<&str> = None;

    // If target itself is reachable, no path needed (shouldn't happen for dead rules)
    if reachable.contains(target_cat) {
        return vec![format!("{} (reachable)", target_cat)];
    }

    while let Some(current) = queue.pop_front() {
        if let Some(callers) = reverse_adj.get(current) {
            for &caller in callers {
                if !visited.contains(caller) {
                    visited.insert(caller);
                    parent.insert(caller, current);
                    if reachable.contains(caller) {
                        found_source = Some(caller);
                        break;
                    }
                    queue.push_back(caller);
                }
            }
        }
        if found_source.is_some() {
            break;
        }
    }

    match found_source {
        Some(source) => {
            // Reconstruct path from source to target
            let mut path = Vec::new();
            let mut current = source;
            path.push(format!("{} (reachable)", current));
            while current != target_cat {
                if let Some(&next) = parent.get(current) {
                    path.push(format!("  → Push to {} (missing)", next));
                    current = next;
                } else {
                    break;
                }
            }
            path
        },
        None => {
            // No path exists from any reachable category
            vec![format!("{} has no path from any reachable category", target_cat)]
        },
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// G34: Recursion Depth Bounds
// ══════════════════════════════════════════════════════════════════════════════

/// Per-category recursion depth bounds derived from WPDS analysis.
#[derive(Debug, Clone)]
pub struct DepthBounds {
    /// Minimum nesting depth at which this category appears (0 = top-level).
    pub min_depth: u32,
    /// Maximum nesting depth (`None` = unbounded, i.e. recursive).
    pub max_depth: Option<u32>,
    /// Whether this category participates in recursion (SCC member or self-loop).
    pub is_recursive: bool,
}

/// Compute per-category depth bounds from the call graph and P-automaton.
///
/// Uses BFS from the primary category on the call graph to determine min depth.
/// Categories in non-trivial SCCs (|SCC|>1 or self-loop) get `max_depth = None`.
/// Non-recursive categories get `max_depth = min_depth` (only reachable at a fixed depth).
pub fn compute_depth_bounds(
    call_graph: &WpdsCallGraph,
    primary_cat: &str,
) -> HashMap<String, DepthBounds> {
    let mut result = HashMap::new();

    // Build adjacency list for BFS
    let mut adj: HashMap<&str, Vec<&str>> = HashMap::new();
    for edge in &call_graph.edges {
        adj.entry(edge.caller_cat.as_str())
            .or_default()
            .push(edge.callee_cat.as_str());
    }

    // Identify recursive categories (in non-trivial SCCs)
    let mut recursive_cats: HashSet<&str> = HashSet::new();
    for scc in &call_graph.sccs {
        if scc.len() > 1 {
            // Mutual recursion
            for cat in scc {
                recursive_cats.insert(cat.as_str());
            }
        } else if scc.len() == 1 {
            // Check for self-loop
            let cat = &scc[0];
            if call_graph
                .edges
                .iter()
                .any(|e| e.caller_cat == *cat && e.callee_cat == *cat)
            {
                recursive_cats.insert(cat.as_str());
            }
        }
    }

    // BFS from primary to compute min_depth
    let mut visited: HashMap<&str, u32> = HashMap::new();
    let mut queue: VecDeque<(&str, u32)> = VecDeque::new();
    visited.insert(primary_cat, 0);
    queue.push_back((primary_cat, 0));

    while let Some((cat, depth)) = queue.pop_front() {
        if let Some(callees) = adj.get(cat) {
            for &callee in callees {
                if !visited.contains_key(callee) {
                    visited.insert(callee, depth + 1);
                    queue.push_back((callee, depth + 1));
                }
            }
        }
    }

    for cat in &call_graph.categories {
        let min_depth = visited.get(cat.as_str()).copied().unwrap_or(u32::MAX);
        let is_recursive = recursive_cats.contains(cat.as_str());
        let max_depth = if is_recursive || min_depth == u32::MAX {
            None
        } else {
            Some(min_depth)
        };
        result.insert(
            cat.clone(),
            DepthBounds {
                min_depth: if min_depth == u32::MAX { 0 } else { min_depth },
                max_depth,
                is_recursive,
            },
        );
    }

    result
}

// ══════════════════════════════════════════════════════════════════════════════
// G35: Cycle Classification
// ══════════════════════════════════════════════════════════════════════════════

/// Classification of a cycle in the call graph.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CycleKind {
    /// Single category with a self-loop (e.g., Expr calls itself cross-category).
    Direct,
    /// Multiple categories forming a cycle (e.g., Expr → Type → Expr).
    Mutual,
}

/// Information about a cycle in the WPDS call graph.
#[derive(Debug, Clone)]
pub struct CycleInfo {
    /// Categories involved in the cycle.
    pub categories: Vec<String>,
    /// Type of cycle.
    pub kind: CycleKind,
    /// Whether any cycle member has a left-recursive Replace from position-0
    /// reaching itself without consuming input.
    pub is_left_recursive: bool,
}

/// Classify all cycles from the call graph SCCs and WPDS rules.
///
/// Direct = |SCC|=1 with self-edge. Mutual = |SCC|>1.
/// Left-recursion check: a category is left-recursive if it has a Replace rule
/// from position-0 back to its own category entry.
pub fn classify_cycles<W: Semiring>(call_graph: &WpdsCallGraph, wpds: &Wpds<W>) -> Vec<CycleInfo> {
    let mut cycles = Vec::new();

    for scc in &call_graph.sccs {
        if scc.len() > 1 {
            // Mutual recursion
            let is_left_recursive = scc.iter().any(|cat| has_left_recursion(cat, wpds));
            cycles.push(CycleInfo {
                categories: scc.clone(),
                kind: CycleKind::Mutual,
                is_left_recursive,
            });
        } else if scc.len() == 1 {
            let cat = &scc[0];
            // Check for self-loop in call graph
            let has_self_edge = call_graph
                .edges
                .iter()
                .any(|e| e.caller_cat == *cat && e.callee_cat == *cat);
            if has_self_edge {
                let is_left_recursive = has_left_recursion(cat, wpds);
                cycles.push(CycleInfo {
                    categories: scc.clone(),
                    kind: CycleKind::Direct,
                    is_left_recursive,
                });
            }
        }
    }

    cycles
}

/// Check if a category has left-recursion in the WPDS: a Replace rule from
/// position-0 of any rule back to its own category entry without consuming input.
fn has_left_recursion<W: Semiring>(category: &str, wpds: &Wpds<W>) -> bool {
    let entry = StackSymbol::category_entry(category);
    // Check if any Replace from category entry goes to a rule@0,
    // and that rule@0 has a Replace back to category entry (or to another rule@0
    // that eventually reaches entry).
    // Simplified check: any Replace rule from entry symbol to a rule@0 that
    // then has a Replace back to entry or another position-0.
    for rule in &wpds.rules {
        if let WpdsRule::Replace { from_gamma, to_gamma, .. } = rule {
            if *from_gamma == entry && to_gamma.category == category && to_gamma.position == 0 {
                // Entry dispatches to rule@0; now check if rule@0 can reach entry
                // without consuming input (another Replace chain to entry)
                if has_replace_path_to_entry(wpds, to_gamma, &entry) {
                    return true;
                }
            }
        }
    }
    false
}

/// Check if there's a Replace-only path from `start` back to `target` (left-recursion).
fn has_replace_path_to_entry<W: Semiring>(
    wpds: &Wpds<W>,
    start: &StackSymbol,
    target: &StackSymbol,
) -> bool {
    let mut visited: HashSet<StackSymbol> = HashSet::new();
    let mut queue: VecDeque<StackSymbol> = VecDeque::new();
    queue.push_back(start.clone());
    visited.insert(start.clone());

    while let Some(current) = queue.pop_front() {
        for rule in &wpds.rules {
            if let WpdsRule::Replace { from_gamma, to_gamma, .. } = rule {
                if *from_gamma == current {
                    if *to_gamma == *target {
                        return true;
                    }
                    if !visited.contains(to_gamma) {
                        visited.insert(to_gamma.clone());
                        queue.push_back(to_gamma.clone());
                    }
                }
            }
        }
    }
    false
}

// ══════════════════════════════════════════════════════════════════════════════
// G36: Prestar "Who Calls Me?" Analysis
// ══════════════════════════════════════════════════════════════════════════════

/// A calling context for a category: who calls it, from which rule, at what position.
#[derive(Debug, Clone)]
pub struct CallingContext {
    /// Category that initiates the call.
    pub caller_category: String,
    /// Rule label in the caller that contains the cross-category reference.
    pub caller_rule: String,
    /// Position within the caller's rule where the call occurs.
    pub caller_position: u32,
    /// Weight on the Push rule.
    pub weight: f64,
}

/// Compute calling contexts for each category by scanning WPDS Push rules.
///
/// For each category, returns all `(caller, rule, position)` triples that
/// reference it via Push rules. This is the WPDS-precise version of
/// `find_missing_callers`.
pub fn compute_calling_contexts<W: Semiring>(
    wpds: &Wpds<W>,
) -> HashMap<String, Vec<CallingContext>> {
    let mut contexts: HashMap<String, Vec<CallingContext>> = HashMap::new();

    for rule in &wpds.rules {
        if let WpdsRule::Push { from_gamma, to_gamma_top, weight, .. } = rule {
            if !from_gamma.category.is_empty() && !to_gamma_top.category.is_empty() {
                contexts
                    .entry(to_gamma_top.category.clone())
                    .or_default()
                    .push(CallingContext {
                        caller_category: from_gamma.category.clone(),
                        caller_rule: from_gamma.rule_label.clone(),
                        caller_position: from_gamma.position,
                        weight: if weight.is_zero() { 0.0 } else { 1.0 },
                    });
            }
        }
    }

    contexts
}
