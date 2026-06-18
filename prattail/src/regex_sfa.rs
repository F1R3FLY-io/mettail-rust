//! Generic symbolic-regex engine: an effective Boolean algebra of **symbolic
//! regular languages over any element algebra** `A: BooleanAlgebra`.
//!
//! A [`RegexPred<P>`] (with `P = A::Predicate`) is a symbolic regex whose
//! character class is an element predicate of `A`. It compiles — via a Thompson
//! epsilon-NFA, epsilon-eliminated — to a [`SymbolicAutomaton<A>`], so the
//! decision procedures are exact regular-language operations:
//!
//! - `and`/`or`/`not` = `Inter`/`Alt`/`Compl`, realized by the SFA's
//!   `intersect`/`union`/`complement`;
//! - `is_satisfiable` = SFA non-emptiness;
//! - `witness` = shortest accepted word ([`SymbolicAutomaton::shortest_accepted`]);
//! - `evaluate(p, xs)` = SFA simulation on the sequence `xs`.
//!
//! [`RegexAlgebra<A>`] is therefore the **list algebra**: its domain is
//! `Vec<A::Domain>` (sequences of elements). It is what the string algebra
//! ([`crate::string_algebra`]) instantiates at `A = CharClassAlgebra`, and what
//! the collection layer uses for `List`. Bags/maps (order-insensitive) use a
//! separate multiset model.

use std::collections::HashSet;
use std::fmt::Debug;
use std::hash::Hash;

use crate::symbolic::{BooleanAlgebra, SymbolicAutomaton};

// ══════════════════════════════════════════════════════════════════════════════
// RegexPred — symbolic regex over element predicates of type P
// ══════════════════════════════════════════════════════════════════════════════

/// A symbolic regular expression whose character class is an element predicate
/// `P` (`= A::Predicate`).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum RegexPred<P> {
    /// `∅` — matches no sequence.
    Empty,
    /// `{ [] }` — matches only the empty sequence.
    Epsilon,
    /// One element drawn from the element predicate.
    Elem(P),
    /// A length constraint `lo ≤ len ≤ hi` (`hi = None` is unbounded above).
    Length(usize, Option<usize>),
    /// Concatenation.
    Concat(Box<RegexPred<P>>, Box<RegexPred<P>>),
    /// Alternation (union).
    Alt(Box<RegexPred<P>>, Box<RegexPred<P>>),
    /// Kleene star.
    Star(Box<RegexPred<P>>),
    /// Intersection.
    Inter(Box<RegexPred<P>>, Box<RegexPred<P>>),
    /// Complement (relative to `Σ*`).
    Compl(Box<RegexPred<P>>),
}

// ══════════════════════════════════════════════════════════════════════════════
// Epsilon-NFA over element predicates (compilation target)
// ══════════════════════════════════════════════════════════════════════════════

struct EpsNfa<P> {
    n: usize,
    eps: Vec<(usize, usize)>,
    chr: Vec<(usize, P, usize)>,
    initials: Vec<usize>,
    accepts: Vec<usize>,
}

impl<P: Clone> EpsNfa<P> {
    fn empty() -> Self {
        EpsNfa {
            n: 1,
            eps: Vec::new(),
            chr: Vec::new(),
            initials: vec![0],
            accepts: Vec::new(),
        }
    }

    fn epsilon() -> Self {
        EpsNfa {
            n: 1,
            eps: Vec::new(),
            chr: Vec::new(),
            initials: vec![0],
            accepts: vec![0],
        }
    }

    fn elem(class: P) -> Self {
        EpsNfa {
            n: 2,
            eps: Vec::new(),
            chr: vec![(0, class, 1)],
            initials: vec![0],
            accepts: vec![1],
        }
    }

    fn concat(a: EpsNfa<P>, b: EpsNfa<P>) -> Self {
        let off = a.n;
        let mut eps: Vec<(usize, usize)> = a.eps.clone();
        eps.extend(b.eps.iter().map(|&(x, y)| (x + off, y + off)));
        let mut chr = a.chr.clone();
        chr.extend(b.chr.iter().map(|(x, g, y)| (x + off, g.clone(), y + off)));
        for &ai in &a.accepts {
            for &bi in &b.initials {
                eps.push((ai, bi + off));
            }
        }
        let accepts = b.accepts.iter().map(|&s| s + off).collect();
        EpsNfa {
            n: a.n + b.n,
            eps,
            chr,
            initials: a.initials.clone(),
            accepts,
        }
    }

    fn alt(a: EpsNfa<P>, b: EpsNfa<P>) -> Self {
        let off = a.n;
        let mut eps = a.eps.clone();
        eps.extend(b.eps.iter().map(|&(x, y)| (x + off, y + off)));
        let mut chr = a.chr.clone();
        chr.extend(b.chr.iter().map(|(x, g, y)| (x + off, g.clone(), y + off)));
        let mut initials = a.initials.clone();
        initials.extend(b.initials.iter().map(|&s| s + off));
        let mut accepts = a.accepts.clone();
        accepts.extend(b.accepts.iter().map(|&s| s + off));
        EpsNfa {
            n: a.n + b.n,
            eps,
            chr,
            initials,
            accepts,
        }
    }

    fn star(a: EpsNfa<P>) -> Self {
        let q = a.n;
        let mut eps = a.eps.clone();
        for &ai in &a.initials {
            eps.push((q, ai));
        }
        for &acc in &a.accepts {
            eps.push((acc, q));
        }
        EpsNfa {
            n: a.n + 1,
            eps,
            chr: a.chr.clone(),
            initials: vec![q],
            accepts: vec![q],
        }
    }

    fn from_sfa<A>(sfa: &SymbolicAutomaton<A>) -> Self
    where
        A: BooleanAlgebra<Predicate = P>,
    {
        let chr = sfa
            .transitions
            .iter()
            .map(|t| (t.from, t.guard.clone(), t.to))
            .collect();
        let mut initials: Vec<usize> = sfa.initial_states.iter().copied().collect();
        initials.sort_unstable();
        let mut accepts: Vec<usize> = sfa.accepting_states.iter().copied().collect();
        accepts.sort_unstable();
        EpsNfa {
            n: sfa.states.len().max(1),
            eps: Vec::new(),
            chr,
            initials,
            accepts,
        }
    }

    fn eclosure(&self, seeds: &[usize]) -> HashSet<usize> {
        let mut seen: HashSet<usize> = seeds.iter().copied().collect();
        let mut stack: Vec<usize> = seeds.to_vec();
        while let Some(s) = stack.pop() {
            for &(a, b) in &self.eps {
                if a == s && seen.insert(b) {
                    stack.push(b);
                }
            }
        }
        seen
    }

    fn to_sfa<A>(&self, algebra: A) -> SymbolicAutomaton<A>
    where
        A: BooleanAlgebra<Predicate = P>,
    {
        let accept_set: HashSet<usize> = self.accepts.iter().copied().collect();
        let ecl: Vec<HashSet<usize>> = (0..self.n).map(|s| self.eclosure(&[s])).collect();
        let mut sfa = SymbolicAutomaton::new(algebra);
        for i in 0..self.n {
            let is_acc = ecl[i].iter().any(|s| accept_set.contains(s));
            sfa.add_state(is_acc, None);
        }
        for &init in &self.initials {
            sfa.set_initial(init);
        }
        for (u, g, v) in &self.chr {
            for (s, closure) in ecl.iter().enumerate() {
                if closure.contains(u) {
                    sfa.add_transition(s, *v, g.clone());
                }
            }
        }
        sfa
    }
}

/// Compile a [`RegexPred`] to an epsilon-NFA over `A`'s element predicates.
fn compile_eps<A>(algebra: &A, p: &RegexPred<A::Predicate>) -> EpsNfa<A::Predicate>
where
    A: BooleanAlgebra,
{
    match p {
        RegexPred::Empty => EpsNfa::empty(),
        RegexPred::Epsilon => EpsNfa::epsilon(),
        RegexPred::Elem(c) => EpsNfa::elem(c.clone()),
        RegexPred::Length(lo, hi) => {
            let sigma = || EpsNfa::elem(algebra.true_pred());
            let mut acc = EpsNfa::epsilon();
            for _ in 0..*lo {
                acc = EpsNfa::concat(acc, sigma());
            }
            match hi {
                None => EpsNfa::concat(acc, EpsNfa::star(sigma())),
                Some(h) => {
                    for _ in 0..h.saturating_sub(*lo) {
                        acc = EpsNfa::concat(acc, EpsNfa::alt(EpsNfa::epsilon(), sigma()));
                    }
                    acc
                },
            }
        },
        RegexPred::Concat(a, b) => EpsNfa::concat(compile_eps(algebra, a), compile_eps(algebra, b)),
        RegexPred::Alt(a, b) => EpsNfa::alt(compile_eps(algebra, a), compile_eps(algebra, b)),
        RegexPred::Star(a) => EpsNfa::star(compile_eps(algebra, a)),
        RegexPred::Inter(a, b) => {
            let sa = compile_eps(algebra, a).to_sfa(algebra.clone());
            let sb = compile_eps(algebra, b).to_sfa(algebra.clone());
            EpsNfa::from_sfa(&sa.intersect(&sb))
        },
        RegexPred::Compl(a) => {
            let sa = compile_eps(algebra, a).to_sfa(algebra.clone());
            EpsNfa::from_sfa(&sa.complement())
        },
    }
}

/// Compile a [`RegexPred`] to an SFA over `A`.
pub fn compile<A>(algebra: &A, p: &RegexPred<A::Predicate>) -> SymbolicAutomaton<A>
where
    A: BooleanAlgebra,
{
    compile_eps(algebra, p).to_sfa(algebra.clone())
}

// ══════════════════════════════════════════════════════════════════════════════
// RegexAlgebra (= the list algebra over A)
// ══════════════════════════════════════════════════════════════════════════════

/// The effective Boolean algebra of symbolic regular languages over `A` — i.e.
/// the **list algebra** over sequences of `A`'s domain.
#[derive(Clone, Debug)]
pub struct RegexAlgebra<A: BooleanAlgebra> {
    /// The element algebra.
    pub elem: A,
}

/// Alias: the list algebra is the symbolic-regular-language algebra over the
/// element algebra.
pub type ListAlgebra<A> = RegexAlgebra<A>;

impl<A: BooleanAlgebra> RegexAlgebra<A> {
    /// Construct the list/regex algebra over the given element algebra.
    pub fn new(elem: A) -> Self {
        RegexAlgebra { elem }
    }

    /// `Σ*` — every sequence.
    pub fn any(&self) -> RegexPred<A::Predicate> {
        RegexPred::Star(Box::new(RegexPred::Elem(self.elem.true_pred())))
    }

    /// `∀ e ∈ xs. e ⊨ p` — every element satisfies `p` (includes the empty list).
    pub fn all(&self, p: A::Predicate) -> RegexPred<A::Predicate> {
        RegexPred::Star(Box::new(RegexPred::Elem(p)))
    }

    /// `∃ e ∈ xs. e ⊨ p` — some element satisfies `p`.
    pub fn any_elem(&self, p: A::Predicate) -> RegexPred<A::Predicate> {
        let sigma_star = self.any();
        RegexPred::Concat(
            Box::new(sigma_star.clone()),
            Box::new(RegexPred::Concat(Box::new(RegexPred::Elem(p)), Box::new(sigma_star))),
        )
    }
}

impl<A: BooleanAlgebra> BooleanAlgebra for RegexAlgebra<A> {
    type Predicate = RegexPred<A::Predicate>;
    type Domain = Vec<A::Domain>;

    fn true_pred(&self) -> Self::Predicate {
        self.any()
    }

    fn false_pred(&self) -> Self::Predicate {
        RegexPred::Empty
    }

    fn and(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate {
        RegexPred::Inter(Box::new(a.clone()), Box::new(b.clone()))
    }

    fn or(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate {
        RegexPred::Alt(Box::new(a.clone()), Box::new(b.clone()))
    }

    fn not(&self, a: &Self::Predicate) -> Self::Predicate {
        RegexPred::Compl(Box::new(a.clone()))
    }

    fn is_satisfiable(&self, a: &Self::Predicate) -> bool {
        !compile(&self.elem, a).is_empty()
    }

    fn witness(&self, a: &Self::Predicate) -> Option<Self::Domain> {
        compile(&self.elem, a).shortest_accepted()
    }

    fn evaluate(&self, pred: &Self::Predicate, elem: &Self::Domain) -> bool {
        compile(&self.elem, pred).accepts(elem)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbolic::{IntervalAlgebra, IntervalPred};

    fn list_alg() -> RegexAlgebra<IntervalAlgebra> {
        RegexAlgebra::new(IntervalAlgebra::new(0, 100))
    }

    #[test]
    fn all_elements_in_range() {
        let alg = list_alg();
        let all_small = alg.all(IntervalPred::Range(0, 10));
        assert!(alg.evaluate(&all_small, &vec![])); // empty list, vacuous
        assert!(alg.evaluate(&all_small, &vec![1, 5, 9]));
        assert!(!alg.evaluate(&all_small, &vec![1, 50]));
        assert!(alg.is_satisfiable(&all_small));
    }

    #[test]
    fn some_element_satisfies() {
        let alg = list_alg();
        let some_big = alg.any_elem(IntervalPred::Range(50, 100));
        assert!(!alg.evaluate(&some_big, &vec![])); // empty has no element
        assert!(!alg.evaluate(&some_big, &vec![1, 2, 3]));
        assert!(alg.evaluate(&some_big, &vec![1, 60, 3]));
    }

    #[test]
    fn length_and_content_intersection_exact() {
        let alg = list_alg();
        // exactly 2 elements AND all in [0,10) AND some in [5,10)
        let p = alg.and(
            &alg.and(&RegexPred::Length(2, Some(2)), &alg.all(IntervalPred::Range(0, 10))),
            &alg.any_elem(IntervalPred::Range(5, 10)),
        );
        assert!(alg.is_satisfiable(&p));
        assert!(alg.evaluate(&p, &vec![3, 7]));
        assert!(!alg.evaluate(&p, &vec![3, 4])); // none in [5,10)
        assert!(!alg.evaluate(&p, &vec![7])); // length 1
        assert!(!alg.evaluate(&p, &vec![3, 7, 8])); // length 3
        let w = alg.witness(&p).expect("nonempty");
        assert!(alg.evaluate(&p, &w));
        assert_eq!(w.len(), 2);
    }

    #[test]
    fn complement_and_laws() {
        let alg = list_alg();
        let all_small = alg.all(IntervalPred::Range(0, 10));
        let not_all_small = alg.not(&all_small);
        assert!(!alg.evaluate(&not_all_small, &vec![1, 2])); // all small → not in complement
        assert!(alg.evaluate(&not_all_small, &vec![1, 50])); // has a big one
        assert!(!alg.is_satisfiable(&alg.and(&all_small, &not_all_small)));
        // unsatisfiable conjunction of disjoint length constraints
        let p = alg.and(&RegexPred::Length(1, Some(1)), &RegexPred::Length(2, Some(2)));
        assert!(!alg.is_satisfiable(&p));
    }

    #[test]
    fn empty_and_top() {
        let alg = list_alg();
        assert!(!alg.is_satisfiable(&alg.false_pred()));
        assert!(alg.is_satisfiable(&alg.true_pred()));
        assert!(alg.evaluate(&alg.true_pred(), &vec![1, 2, 3]));
    }
}
