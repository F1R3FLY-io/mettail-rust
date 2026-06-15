//! Order-insensitive collection algebras: [`BagAlgebra`] (multisets) and
//! [`MapAlgebra`] (key→value maps).
//!
//! Ordered sequences use the regex/SFA list algebra
//! ([`crate::regex_sfa::ListAlgebra`]); bags and maps are unordered and are
//! decided by **counting** rather than by automaton structure.
//!
//! ## Bag decision procedure (exact)
//!
//! A bag predicate is a boolean combination of cardinality atoms
//! `Count{class, [lo, hi]}` = "the number of elements satisfying `class` lies in
//! `[lo, hi]`". To decide satisfiability exactly:
//!
//! 1. Take the **minterms** of all classes appearing in the predicate (maximal
//!    satisfiable conjunctions of the classes and their negations, computed over
//!    the element algebra). Every element falls in exactly one minterm, so a bag
//!    is fully characterized by its per-minterm count vector `(c_0, …, c_{k-1})`.
//! 2. Each `Count{class, [lo,hi]}` becomes a linear constraint
//!    `Σ_{m ⊆ class} c_m ∈ [lo, hi]` on that vector.
//! 3. Feasibility is integer-linear over `ℕ^k`; since every threshold is below
//!    `B = 1 + max(all lo, all finite hi)`, counts `≥ B` are indistinguishable,
//!    so a bounded search over `[0, B]^k` is **exact**.
//!
//! `evaluate` uses the bag's actual counts (uncapped); `witness` materializes a
//! bag from a feasible count vector. The search is exponential in the number of
//! minterms (≤ `2^(#classes)`), which is small for real guards — correctness
//! holds regardless of cost.

use std::collections::HashMap;

use crate::symbolic::BooleanAlgebra;

// ══════════════════════════════════════════════════════════════════════════════
// Minterms (shared helper)
// ══════════════════════════════════════════════════════════════════════════════

/// The satisfiable minterms of a set of element predicates: maximal satisfiable
/// conjunctions of each predicate or its negation. Every domain element
/// satisfies exactly one minterm.
fn minterms<A: BooleanAlgebra>(elem: &A, classes: &[A::Predicate]) -> Vec<A::Predicate> {
    let mut ms = vec![elem.true_pred()];
    for c in classes {
        let nc = elem.not(c);
        let mut next = Vec::with_capacity(ms.len() * 2);
        for m in &ms {
            let pos = elem.and(m, c);
            if elem.is_satisfiable(&pos) {
                next.push(pos);
            }
            let neg = elem.and(m, &nc);
            if elem.is_satisfiable(&neg) {
                next.push(neg);
            }
        }
        ms = next;
    }
    ms
}

// ══════════════════════════════════════════════════════════════════════════════
// BagAlgebra
// ══════════════════════════════════════════════════════════════════════════════

/// A bag predicate: a boolean combination of cardinality atoms over an element
/// predicate type `P`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum BagPred<P> {
    /// Satisfied by every bag.
    True,
    /// Satisfied by no bag.
    False,
    /// `lo ≤ #{ e ∈ bag : e ⊨ class } ≤ hi` (`hi = None` is unbounded above).
    Count { class: P, lo: u64, hi: Option<u64> },
    /// Conjunction.
    And(Box<BagPred<P>>, Box<BagPred<P>>),
    /// Disjunction.
    Or(Box<BagPred<P>>, Box<BagPred<P>>),
    /// Negation.
    Not(Box<BagPred<P>>),
}

/// The effective Boolean algebra of multisets (bags) over an element algebra.
#[derive(Clone, Debug)]
pub struct BagAlgebra<A: BooleanAlgebra> {
    /// The element algebra.
    pub elem: A,
}

impl<A: BooleanAlgebra> BagAlgebra<A> {
    /// Construct the bag algebra over the given element algebra.
    pub fn new(elem: A) -> Self {
        BagAlgebra { elem }
    }

    /// `∀ e ∈ bag. e ⊨ p` — equivalently, zero elements satisfy `¬p`.
    pub fn all(&self, p: A::Predicate) -> BagPred<A::Predicate> {
        BagPred::Count { class: self.elem.not(&p), lo: 0, hi: Some(0) }
    }

    /// `∃ e ∈ bag. e ⊨ p` — at least one element satisfies `p`.
    pub fn any_elem(&self, p: A::Predicate) -> BagPred<A::Predicate> {
        BagPred::Count { class: p, lo: 1, hi: None }
    }

    /// `lo ≤ |bag| ≤ hi` (total cardinality).
    pub fn size(&self, lo: u64, hi: Option<u64>) -> BagPred<A::Predicate> {
        BagPred::Count { class: self.elem.true_pred(), lo, hi }
    }

    /// Collect every distinct `class` appearing in `Count` atoms.
    fn collect_classes(&self, pred: &BagPred<A::Predicate>, out: &mut Vec<A::Predicate>) {
        match pred {
            BagPred::Count { class, .. } => {
                if !out.iter().any(|c| c == class) {
                    out.push(class.clone());
                }
            },
            BagPred::And(a, b) | BagPred::Or(a, b) => {
                self.collect_classes(a, out);
                self.collect_classes(b, out);
            },
            BagPred::Not(x) => self.collect_classes(x, out),
            BagPred::True | BagPred::False => {},
        }
    }

    /// For each `Count` class, the indices of the minterms it covers.
    fn covering(&self, classes: &[A::Predicate], ms: &[A::Predicate]) -> HashMap<A::Predicate, Vec<usize>> {
        let mut map = HashMap::new();
        for class in classes {
            let cover: Vec<usize> = ms
                .iter()
                .enumerate()
                // A minterm is atomic w.r.t. `class`: it is wholly inside or
                // wholly outside. Inside iff (minterm ∧ class) is satisfiable.
                .filter(|(_, m)| self.elem.is_satisfiable(&self.elem.and(m, class)))
                .map(|(i, _)| i)
                .collect();
            map.insert(class.clone(), cover);
        }
        map
    }

    /// Evaluate the predicate against a per-minterm count vector.
    fn eval_counts(
        &self,
        pred: &BagPred<A::Predicate>,
        counts: &[u64],
        cover: &HashMap<A::Predicate, Vec<usize>>,
    ) -> bool {
        match pred {
            BagPred::True => true,
            BagPred::False => false,
            BagPred::Count { class, lo, hi } => {
                let sum: u64 = cover
                    .get(class)
                    .map(|idxs| idxs.iter().map(|&i| counts[i]).sum())
                    .unwrap_or(0);
                sum >= *lo && hi.map(|h| sum <= h).unwrap_or(true)
            },
            BagPred::And(a, b) => {
                self.eval_counts(a, counts, cover) && self.eval_counts(b, counts, cover)
            },
            BagPred::Or(a, b) => {
                self.eval_counts(a, counts, cover) || self.eval_counts(b, counts, cover)
            },
            BagPred::Not(x) => !self.eval_counts(x, counts, cover),
        }
    }

    /// The smallest count cap `B` such that counts `≥ B` are indistinguishable
    /// from `B` for every atom (`1 + max threshold`).
    fn count_cap(&self, pred: &BagPred<A::Predicate>) -> u64 {
        fn go<P>(pred: &BagPred<P>, acc: &mut u64) {
            match pred {
                BagPred::Count { lo, hi, .. } => {
                    *acc = (*acc).max(*lo);
                    if let Some(h) = hi {
                        *acc = (*acc).max(*h);
                    }
                },
                BagPred::And(a, b) | BagPred::Or(a, b) => {
                    go(a, acc);
                    go(b, acc);
                },
                BagPred::Not(x) => go(x, acc),
                BagPred::True | BagPred::False => {},
            }
        }
        let mut acc = 0;
        go(pred, &mut acc);
        acc + 1
    }

    /// Search for a feasible count vector; returns it if one exists.
    fn feasible_counts(&self, pred: &BagPred<A::Predicate>) -> Option<(Vec<A::Predicate>, Vec<u64>)> {
        let mut classes = Vec::new();
        self.collect_classes(pred, &mut classes);
        let ms = minterms(&self.elem, &classes);
        let cover = self.covering(&classes, &ms);
        let k = ms.len();
        let cap = self.count_cap(pred);

        // Bounded search over [0, cap]^k.
        let mut counts = vec![0u64; k];
        loop {
            if self.eval_counts(pred, &counts, &cover) {
                return Some((ms, counts));
            }
            // Increment the mixed-radix counter (base cap+1).
            let mut i = 0;
            loop {
                if i == k {
                    return None; // exhausted
                }
                if counts[i] < cap {
                    counts[i] += 1;
                    break;
                }
                counts[i] = 0;
                i += 1;
            }
        }
    }
}

impl<A: BooleanAlgebra> BooleanAlgebra for BagAlgebra<A> {
    type Predicate = BagPred<A::Predicate>;
    type Domain = Vec<A::Domain>;

    fn true_pred(&self) -> Self::Predicate {
        BagPred::True
    }

    fn false_pred(&self) -> Self::Predicate {
        BagPred::False
    }

    fn and(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate {
        match (a, b) {
            (BagPred::False, _) | (_, BagPred::False) => BagPred::False,
            (BagPred::True, x) | (x, BagPred::True) => x.clone(),
            _ => BagPred::And(Box::new(a.clone()), Box::new(b.clone())),
        }
    }

    fn or(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate {
        match (a, b) {
            (BagPred::True, _) | (_, BagPred::True) => BagPred::True,
            (BagPred::False, x) | (x, BagPred::False) => x.clone(),
            _ => BagPred::Or(Box::new(a.clone()), Box::new(b.clone())),
        }
    }

    fn not(&self, a: &Self::Predicate) -> Self::Predicate {
        BagPred::Not(Box::new(a.clone()))
    }

    fn is_satisfiable(&self, a: &Self::Predicate) -> bool {
        self.feasible_counts(a).is_some()
    }

    fn witness(&self, a: &Self::Predicate) -> Option<Self::Domain> {
        let (ms, counts) = self.feasible_counts(a)?;
        let mut bag = Vec::new();
        for (i, &count) in counts.iter().enumerate() {
            if count == 0 {
                continue;
            }
            let elem = self.elem.witness(&ms[i])?;
            for _ in 0..count {
                bag.push(elem.clone());
            }
        }
        Some(bag)
    }

    fn evaluate(&self, pred: &Self::Predicate, elem: &Self::Domain) -> bool {
        match pred {
            BagPred::True => true,
            BagPred::False => false,
            BagPred::Count { class, lo, hi } => {
                let count = elem.iter().filter(|e| self.elem.evaluate(class, e)).count() as u64;
                count >= *lo && hi.map(|h| count <= h).unwrap_or(true)
            },
            BagPred::And(a, b) => self.evaluate(a, elem) && self.evaluate(b, elem),
            BagPred::Or(a, b) => self.evaluate(a, elem) || self.evaluate(b, elem),
            BagPred::Not(x) => !self.evaluate(x, elem),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbolic::{IntervalAlgebra, IntervalPred};

    fn bag_alg() -> BagAlgebra<IntervalAlgebra> {
        BagAlgebra::new(IntervalAlgebra::new(0, 100))
    }

    #[test]
    fn count_and_size() {
        let alg = bag_alg();
        // at least 2 elements in [50,100)
        let p = BagPred::Count { class: IntervalPred::Range(50, 100), lo: 2, hi: None };
        assert!(alg.evaluate(&p, &vec![60, 70, 1]));
        assert!(!alg.evaluate(&p, &vec![60, 1]));
        assert!(alg.is_satisfiable(&p));
        let w = alg.witness(&p).expect("nonempty");
        assert!(alg.evaluate(&p, &w));
    }

    #[test]
    fn all_and_any() {
        let alg = bag_alg();
        let all_small = alg.all(IntervalPred::Range(0, 10));
        assert!(alg.evaluate(&all_small, &vec![])); // vacuous
        assert!(alg.evaluate(&all_small, &vec![1, 5, 9]));
        assert!(!alg.evaluate(&all_small, &vec![1, 50]));

        let any_big = alg.any_elem(IntervalPred::Range(50, 100));
        assert!(!alg.evaluate(&any_big, &vec![]));
        assert!(!alg.evaluate(&any_big, &vec![1, 2]));
        assert!(alg.evaluate(&any_big, &vec![1, 60]));
        assert!(alg.is_satisfiable(&any_big));
    }

    #[test]
    fn overlapping_classes_minterm_feasibility() {
        let alg = bag_alg();
        // at least 1 in [0,60) AND at least 1 in [40,100); the overlap [40,60)
        // could satisfy both with a single element, or two disjoint elements.
        let p = alg.and(
            &BagPred::Count { class: IntervalPred::Range(0, 60), lo: 1, hi: None },
            &BagPred::Count { class: IntervalPred::Range(40, 100), lo: 1, hi: None },
        );
        assert!(alg.is_satisfiable(&p));
        assert!(alg.evaluate(&p, &vec![50])); // single element covers both
        assert!(alg.evaluate(&p, &vec![10, 80])); // two disjoint
        assert!(!alg.evaluate(&p, &vec![10])); // misses [40,100)
        let w = alg.witness(&p).expect("nonempty");
        assert!(alg.evaluate(&p, &w));
    }

    #[test]
    fn unsatisfiable_count() {
        let alg = bag_alg();
        // exactly 0 AND at least 1 in the same class → unsat
        let p = alg.and(
            &BagPred::Count { class: IntervalPred::Range(0, 100), lo: 0, hi: Some(0) },
            &BagPred::Count { class: IntervalPred::Range(0, 100), lo: 1, hi: None },
        );
        assert!(!alg.is_satisfiable(&p));
    }

    #[test]
    fn negation() {
        let alg = bag_alg();
        let any_big = alg.any_elem(IntervalPred::Range(50, 100));
        let none_big = alg.not(&any_big);
        assert!(alg.evaluate(&none_big, &vec![1, 2, 3]));
        assert!(!alg.evaluate(&none_big, &vec![1, 60]));
        assert!(!alg.is_satisfiable(&alg.and(&any_big, &none_big)));
    }
}
