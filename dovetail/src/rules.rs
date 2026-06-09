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
