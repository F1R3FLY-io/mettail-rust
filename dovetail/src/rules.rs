//! Rules-as-data: rewrite rules over the e-graph + an equality-saturation driver.
//!
//! Rules are DATA (`RewriteRule<L>`), not macro-generated code — a language's
//! reduction rules are loaded and run, not compiled in. Saturation grows the
//! e-graph of equalities (every rewrite adds an equality, never replacing a
//! term); the weighted [`crate::extract`] extractor then enumerates normal forms
//! best-first. **Nothing is pruned during saturation**; budget overflow is
//! REPORTED (`node_limit_reached`), never silent (carries the b56e1e5 budget
//! discipline).

use std::collections::HashMap;

use crate::egraph::{EClassId, EGraph, ENode};

/// A pattern over operator labels `L` with named pattern variables.
#[derive(Clone, Debug)]
pub enum Pattern<L> {
    /// A pattern variable, binding to an e-class.
    Var(String),
    /// An operator applied to argument patterns.
    App { op: L, args: Vec<Pattern<L>> },
}

impl<L> Pattern<L> {
    pub fn var(name: impl Into<String>) -> Self {
        Pattern::Var(name.into())
    }
    pub fn leaf(op: L) -> Self {
        Pattern::App { op, args: Vec::new() }
    }
    pub fn app(op: L, args: Vec<Pattern<L>>) -> Self {
        Pattern::App { op, args }
    }
}

/// A substitution from pattern-variable name to e-class.
pub type Subst = HashMap<String, EClassId>;

/// A rewrite rule `lhs -> rhs` (rules ARE data). RHS variables must be a subset
/// of LHS variables (every RHS var is bound by the match).
#[derive(Clone, Debug)]
pub struct RewriteRule<L> {
    pub lhs: Pattern<L>,
    pub rhs: Pattern<L>,
    pub label: Option<String>,
}

/// Outcome of equality saturation.
#[derive(Clone, Debug, Default)]
pub struct SatReport {
    /// A fixpoint was reached (an iteration produced no new merges).
    pub converged: bool,
    /// The node budget was hit (saturation stopped early; REPORTED not silent).
    pub node_limit_reached: bool,
    /// Iterations performed.
    pub iterations: usize,
    /// Total merges applied.
    pub total_merges: usize,
}

impl<L: Clone + Eq + std::hash::Hash> EGraph<L> {
    /// All `(root e-class, substitution)` matches of `pattern` across the graph.
    pub fn search(&self, pattern: &Pattern<L>) -> Vec<(EClassId, Subst)> {
        let mut out = Vec::new();
        for q in self.classes() {
            self.collect_matches(pattern, q, &Subst::new(), &mut out);
        }
        out
    }

    fn collect_matches(
        &self,
        pattern: &Pattern<L>,
        class: EClassId,
        subst: &Subst,
        out: &mut Vec<(EClassId, Subst)>,
    ) {
        let class = self.find(class);
        match pattern {
            Pattern::Var(name) => match subst.get(name) {
                Some(&existing) if self.find(existing) == class => out.push((class, subst.clone())),
                Some(_) => {}, // bound to a different class — no match
                None => {
                    let mut s = subst.clone();
                    s.insert(name.clone(), class);
                    out.push((class, s));
                },
            },
            Pattern::App { op, args } => {
                for enode in self.nodes(class) {
                    if enode.op == *op && enode.children.len() == args.len() {
                        self.match_children(args, &enode.children, subst, class, out);
                    }
                }
            },
        }
    }

    fn match_children(
        &self,
        patterns: &[Pattern<L>],
        children: &[EClassId],
        subst: &Subst,
        root: EClassId,
        out: &mut Vec<(EClassId, Subst)>,
    ) {
        if patterns.is_empty() {
            out.push((root, subst.clone()));
            return;
        }
        let mut child_matches = Vec::new();
        self.collect_matches(&patterns[0], children[0], subst, &mut child_matches);
        for (_, cs) in child_matches {
            self.match_children(&patterns[1..], &children[1..], &cs, root, out);
        }
    }

    /// Instantiate a RHS pattern under a substitution, adding nodes within the
    /// node budget. Returns `None` if a variable is unbound (ill-formed rule) or
    /// the budget refused a fresh node (then `node_limit_reached()` is set).
    fn instantiate(&mut self, pattern: &Pattern<L>, subst: &Subst) -> Option<EClassId> {
        match pattern {
            Pattern::Var(name) => subst.get(name).map(|&id| self.find(id)),
            Pattern::App { op, args } => {
                let mut children = Vec::with_capacity(args.len());
                for a in args {
                    children.push(self.instantiate(a, subst)?);
                }
                self.try_add_with_budget(ENode::new(op.clone(), children))
            },
        }
    }

    /// Equality saturation: apply `rules` to a fixpoint, or until the node budget
    /// or `max_iters` is hit. Every fired rule ADDS an equality (merge); nothing
    /// is pruned. Budget overflow is reported via `SatReport::node_limit_reached`.
    pub fn saturate(&mut self, rules: &[RewriteRule<L>], max_iters: usize) -> SatReport {
        let mut report = SatReport::default();
        for iteration in 0..max_iters {
            report.iterations = iteration + 1;
            let mut iter_merges = 0usize;
            for rule in rules {
                let matches = self.search(&rule.lhs);
                let mut rule_merges = 0usize;
                let mut budget_hit = false;
                for (root, subst) in matches {
                    if let Some(rhs_id) = self.instantiate(&rule.rhs, &subst) {
                        if self.find(root) != self.find(rhs_id) {
                            self.merge(root, rhs_id);
                            rule_merges += 1;
                        }
                    } else if self.node_limit_reached() {
                        budget_hit = true;
                        break;
                    }
                    // else: ill-formed rule (unbound RHS var) — skip this match.
                }
                if rule_merges > 0 {
                    self.rebuild();
                }
                iter_merges += rule_merges;
                report.total_merges += rule_merges;
                if budget_hit {
                    report.node_limit_reached = true;
                    return report;
                }
            }
            if iter_merges == 0 {
                report.converged = true;
                return report;
            }
        }
        report
    }
}

// ════════════════════════════════════════════════════════════════════════════
// EP-P6a DV-0 PROBE (measurement-only; 2026-06-12)
// ════════════════════════════════════════════════════════════════════════════
//
// Binding contract: docs/design/evidence-pruning/02-staged-implementation-plan.md
// §P6a. This is a MEASUREMENT-ONLY probe deciding the DV-1 gate; it implements
// NOTHING beyond the counters. It does not alter any production code path (the
// 39 baseline tests are untouched).
//
// Counters required by the contract:
//   - `enodes_added_total`            : e-nodes created DURING saturation
//                                       (post-saturation live node_count minus
//                                       the pre-saturation seed node_count).
//   - `enodes_in_extracted_derivations`: distinct e-nodes (by exact ContentKey of
//                                       the canonical (op, child-classes) node)
//                                       that appear in the chosen best derivation
//                                       trees of the demanded roots — MARKED by
//                                       walking those derivations.
//   - saturation share of eval wall-time (saturation ns / (saturation+extraction) ns).
//
// GATE: untouched-share = 1 - (in_extracted / added_total) ≥ 50% AND
//       saturation ≥ 20% of eval wall-time  →  recommend DV-1; else record the non-goal.
//
// CORPUS CAVEAT (recorded in findings.md): the rhocalc eval corpus does NOT route
// through dovetail today — `mettail-rho-runtime` runs f1r3node's RhoRuntime
// directly (run.rs) and the `dovetail` reference in its lib.rs is a doc comment;
// dovetail is M-E.0 (inert), no live caller. So this probe measures the LARGEST
// EXISTING dovetail workload: a saturate→extract arithmetic-rewrite system that
// mirrors the equality-saturation shape the flip would create. The
// corpus-representativeness caveat carries to the flip epic.
#[cfg(test)]
mod dv0_probe {
    use std::collections::HashSet;
    use std::time::Instant;

    use rigail::TropicalWeight;

    use crate::egraph::{EClassId, EGraph, ENode};
    use crate::extract::{Derivation, Extractor};
    use crate::key::ContentKey;
    use crate::rules::{Pattern, RewriteRule};

    /// Cost model: leaf digits cost their value, structural ops a flat 1, and the
    /// `h`-nesting "expander" (an unbounded-growth rule, mirroring the saturation
    /// blow-up the budget guards) costs 1 so the cheaper non-expanded form wins.
    fn weigh(n: &ENode<String>) -> TropicalWeight {
        match n.op.as_str() {
            "add" | "mul" => TropicalWeight(1.0),
            "h" => TropicalWeight(1.0),
            s => match s.parse::<f64>() {
                Ok(v) => TropicalWeight(v.max(1.0)),
                Err(_) => TropicalWeight(1.0),
            },
        }
    }

    /// The exact ContentKey of a node's CANONICAL (op, child-classes) identity —
    /// the same identity the e-graph hashconses on. Used to MARK e-nodes reached
    /// by the extracted derivations.
    fn node_key(op: &str, child_classes: &[EClassId]) -> ContentKey {
        let mut bytes = Vec::new();
        crate::key::SemanticHash::write_content(&op.to_string(), &mut bytes);
        for c in child_classes {
            crate::key::write_framed(&mut bytes, &c.0.to_le_bytes());
        }
        ContentKey::from_bytes(bytes)
    }

    /// Walk a chosen derivation tree, inserting each node's canonical key into
    /// `marked`. A derivation node carries `class` (its e-class) and `children`
    /// (the chosen child derivations), so the canonical (op, child-class) key is
    /// reconstructable and matches the e-graph's hashcons identity.
    fn mark_derivation(
        eg: &EGraph<String>,
        d: &Derivation<String, TropicalWeight>,
        marked: &mut HashSet<ContentKey>,
    ) {
        let child_classes: Vec<EClassId> =
            d.children.iter().map(|c| eg.find(c.class)).collect();
        marked.insert(node_key(&d.op, &child_classes));
        for c in &d.children {
            mark_derivation(eg, c, marked);
        }
    }

    /// Build a saturate→extract workload, returning
    /// (enodes_added_total, enodes_in_extracted_derivations, sat_ns, extract_ns,
    ///  total_live_nodes, demanded_roots, nf_count).
    #[allow(clippy::type_complexity)]
    fn run_workload(
        seed: &str,
        depth_terms: usize,
        kbest: usize,
    ) -> (usize, usize, u128, u128, usize, usize, usize) {
        // ── Build the e-graph + seed a small batch of distinct arithmetic terms.
        let mut eg = EGraph::<String>::new();
        let mut roots: Vec<EClassId> = Vec::new();
        // A pool of leaves shared across the seeded terms (so saturation/congruence
        // has cross-term structure to grow, like a real reduction corpus).
        let leaves: Vec<EClassId> = (0..6)
            .map(|i| eg.add(ENode::leaf(format!("{}", i + 1))))
            .collect();
        for t in 0..depth_terms {
            // add(mul(a,b), c)  with a/b/c rotating through the leaf pool.
            let a = leaves[t % leaves.len()];
            let b = leaves[(t + 1) % leaves.len()];
            let c = leaves[(t + 2) % leaves.len()];
            let m = eg.add(ENode::new("mul".into(), vec![a, b]));
            let r = eg.add(ENode::new("add".into(), vec![m, c]));
            roots.push(r);
        }
        let _ = seed; // (seed label reserved for diagnostic naming)
        eg.rebuild();
        let seed_nodes = eg.node_count();

        // ── Rewrite system that GROWS the e-graph with equivalent-but-costlier
        //    forms (the off-Ascent reduction analog: every rule adds an equality,
        //    nothing is pruned). `x -> add(x, h(x))`-style expanders plus
        //    commutativity create many materialized e-nodes that extraction will
        //    NOT choose (the cheaper original wins), which is exactly the
        //    "added but untouched" share DV-0 quantifies.
        let rules = vec![
            // commutativity of mul: mul(x,y) ~ mul(y,x)
            RewriteRule {
                lhs: Pattern::app("mul".into(), vec![Pattern::var("x"), Pattern::var("y")]),
                rhs: Pattern::app("mul".into(), vec![Pattern::var("y"), Pattern::var("x")]),
                label: Some("mul_comm".into()),
            },
            // commutativity of add
            RewriteRule {
                lhs: Pattern::app("add".into(), vec![Pattern::var("x"), Pattern::var("y")]),
                rhs: Pattern::app("add".into(), vec![Pattern::var("y"), Pattern::var("x")]),
                label: Some("add_comm".into()),
            },
            // an expander that introduces costlier equivalent structure:
            //   add(x,y) ~ add(x, mul(1, y))   (identity-via-mul, costlier ⇒ unchosen)
            RewriteRule {
                lhs: Pattern::app("add".into(), vec![Pattern::var("x"), Pattern::var("y")]),
                rhs: Pattern::app(
                    "add".into(),
                    vec![
                        Pattern::var("x"),
                        Pattern::app("mul".into(), vec![Pattern::leaf("1".into()), Pattern::var("y")]),
                    ],
                ),
                label: Some("add_mul_ident".into()),
            },
        ];

        // ── SATURATION (timed). Bounded iters so commutativity doesn't ping-pong
        //    forever; the expander grows structure each pass.
        let t0 = Instant::now();
        let _report = eg.saturate(&rules, 6);
        let sat_ns = t0.elapsed().as_nanos();
        let total_live_nodes = eg.node_count();
        let enodes_added_total = total_live_nodes.saturating_sub(seed_nodes);

        // ── EXTRACTION (timed): exact lazy k-best with the admissible 0̄-inside
        //    skip, over EVERY demanded root. MARK the touched e-nodes.
        let t1 = Instant::now();
        let mut marked: HashSet<ContentKey> = HashSet::new();
        let mut nf_count = 0usize;
        {
            let mut ex = Extractor::new(&eg, weigh).with_heuristic();
            for &root in &roots {
                for k in 0..kbest {
                    match ex.kth(root, k) {
                        Some(d) => {
                            mark_derivation(&eg, &d, &mut marked);
                            nf_count += 1;
                        },
                        None => break,
                    }
                }
            }
        }
        let extract_ns = t1.elapsed().as_nanos();
        let enodes_in_extracted = marked.len();

        (
            enodes_added_total,
            enodes_in_extracted,
            sat_ns,
            extract_ns,
            total_live_nodes,
            roots.len(),
            nf_count,
        )
    }

    #[test]
    fn dv0_saturation_vs_extraction_reach_report() {
        // Three workload sizes so the share is observed across scale, not a single
        // point. Printed for the ledger; the test ASSERTS only the invariants the
        // measurement relies on (it refutes nothing — DV-0 is measurement-only).
        println!("\n=== EP-P6a DV-0 PROBE (dovetail saturate→extract) ===");
        println!(
            "{:<10} {:>10} {:>12} {:>14} {:>10} {:>10} {:>9} {:>10} {:>11}",
            "workload", "live_nodes", "added(sat)", "in_extracted",
            "untouched%", "sat_ns", "ext_ns", "sat%wall", "roots/nf"
        );
        // 1-best (k=1) is the normal-form extraction the flip would use.
        for (name, depth, kbest) in [
            ("small_k1", 4usize, 1usize),
            ("med_k1", 12, 1),
            ("large_k1", 32, 1),
            // a k=3 variant: pulling more alternatives touches MORE nodes, the
            // honest upper bound on extraction reach.
            ("large_k3", 32, 3),
        ] {
            let (added, in_ex, sat_ns, ext_ns, live, roots, nf) =
                run_workload(name, depth, kbest);
            let untouched_pct = if added == 0 {
                0.0
            } else {
                100.0 * (added.saturating_sub(in_ex.min(added)) as f64) / (added as f64)
            };
            let total_ns = sat_ns + ext_ns;
            let sat_pct = if total_ns == 0 {
                0.0
            } else {
                100.0 * (sat_ns as f64) / (total_ns as f64)
            };
            println!(
                "{:<10} {:>10} {:>12} {:>14} {:>9.1}% {:>10} {:>10} {:>8.1}% {:>5}/{:<5}",
                name, live, added, in_ex, untouched_pct, sat_ns, ext_ns, sat_pct, roots, nf
            );

            // Measurement-soundness invariants (NOT pruning assertions):
            assert!(live >= added, "live nodes ≥ saturation-added (sanity)");
            assert!(in_ex >= 1, "extraction touched at least one e-node");
        }
        println!(
            "GATE: DV-1 iff untouched-share ≥ 50% AND sat ≥ 20% of eval wall-time.\n\
             (See /tmp/p6_probes/findings.md for the verdict + corpus caveat.)\n"
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::egraph::EGraphConfig;

    #[test]
    fn search_finds_matches() {
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let _fa = eg.add(ENode::new("f".into(), vec![a]));
        let pat = Pattern::app("f".to_string(), vec![Pattern::var("x")]);
        let matches = eg.search(&pat);
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].1.get("x"), Some(&eg.find(a)));
    }

    #[test]
    fn saturate_simple_rewrite_to_fixpoint() {
        // f(x) -> x. Seed f(a). After saturation: f(a) ~ a.
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let fa = eg.add(ENode::new("f".into(), vec![a]));
        let rule = RewriteRule {
            lhs: Pattern::app("f".to_string(), vec![Pattern::var("x")]),
            rhs: Pattern::var("x"),
            label: Some("unwrap_f".into()),
        };
        let rep = eg.saturate(&[rule], 20);
        assert!(rep.converged, "reaches a fixpoint");
        assert!(eg.equiv(fa, a), "f(a) ~ a after saturation");
    }

    #[test]
    fn saturate_congruence_via_rule() {
        // a -> b, and f(a), f(b): after a~b, congruence gives f(a)~f(b).
        let mut eg = EGraph::<String>::new();
        let a = eg.add(ENode::leaf("a".into()));
        let b = eg.add(ENode::leaf("b".into()));
        let fa = eg.add(ENode::new("f".into(), vec![a]));
        let fb = eg.add(ENode::new("f".into(), vec![b]));
        let rule = RewriteRule {
            lhs: Pattern::leaf("a".to_string()),
            rhs: Pattern::leaf("b".to_string()),
            label: None,
        };
        let rep = eg.saturate(&[rule], 20);
        assert!(rep.converged);
        assert!(eg.equiv(a, b));
        assert!(eg.equiv(fa, fb), "congruence: f(a) ~ f(b) after a ~ b");
    }

    #[test]
    fn saturate_reports_node_limit_without_overshoot() {
        // f(x) -> f(h(x)) grows UNBOUNDEDLY: each iteration introduces a fresh
        // `h`-nesting depth that cannot collapse (unlike f(x)->f(f(x)), which
        // converges because f(f(a)) = f(class-of-f(a)) dedups). The budget caps
        // the growth and REPORTS it.
        let mut eg = EGraph::<String>::with_config(EGraphConfig { max_nodes: 5 });
        let a = eg.add(ENode::leaf("a".into()));
        let _fa = eg.add(ENode::new("f".into(), vec![a]));
        let rule = RewriteRule {
            lhs: Pattern::app("f".to_string(), vec![Pattern::var("x")]),
            rhs: Pattern::app(
                "f".to_string(),
                vec![Pattern::app("h".to_string(), vec![Pattern::var("x")])],
            ),
            label: None,
        };
        let rep = eg.saturate(&[rule], 100);
        assert!(rep.node_limit_reached, "budget overflow REPORTED, not silent");
        assert!(eg.node_count() <= 5, "no overshoot past the budget");
    }
}
