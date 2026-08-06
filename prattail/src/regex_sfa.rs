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

use std::fmt::Debug;

use crate::symbolic::{BooleanAlgebra, SymbolicAutomaton};

// ══════════════════════════════════════════════════════════════════════════════
// RegexPred — symbolic regex over element predicates of type P
// ══════════════════════════════════════════════════════════════════════════════

/// A symbolic regular expression whose character class is an element predicate
/// `P` (`= A::Predicate`).
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

pub(crate) enum RegexNode<P> {
    Empty,
    Epsilon,
    Elem(P),
    Length(usize, Option<usize>),
    Concat(Box<RegexPred<P>>, Box<RegexPred<P>>),
    Alt(Box<RegexPred<P>>, Box<RegexPred<P>>),
    Star(Box<RegexPred<P>>),
    Inter(Box<RegexPred<P>>, Box<RegexPred<P>>),
    Compl(Box<RegexPred<P>>),
}

impl<P> RegexPred<P> {
    pub(crate) fn into_node(self) -> RegexNode<P> {
        let predicate = std::mem::ManuallyDrop::new(self);
        // SAFETY: `ManuallyDrop` suppresses the source destructor. The match
        // selects its active variant, and every non-Copy field in that variant
        // is moved exactly once into the corresponding owned node.
        unsafe {
            match &*predicate {
                RegexPred::Empty => RegexNode::Empty,
                RegexPred::Epsilon => RegexNode::Epsilon,
                RegexPred::Elem(value) => RegexNode::Elem(std::ptr::read(value)),
                RegexPred::Length(lower, upper) => RegexNode::Length(*lower, *upper),
                RegexPred::Concat(left, right) => {
                    RegexNode::Concat(std::ptr::read(left), std::ptr::read(right))
                },
                RegexPred::Alt(left, right) => {
                    RegexNode::Alt(std::ptr::read(left), std::ptr::read(right))
                },
                RegexPred::Star(value) => RegexNode::Star(std::ptr::read(value)),
                RegexPred::Inter(left, right) => {
                    RegexNode::Inter(std::ptr::read(left), std::ptr::read(right))
                },
                RegexPred::Compl(value) => RegexNode::Compl(std::ptr::read(value)),
            }
        }
    }
}

#[path = "regex_sfa/lifecycle.rs"]
mod lifecycle;

// ══════════════════════════════════════════════════════════════════════════════
// Epsilon-NFA over element predicates (compilation target)
// ══════════════════════════════════════════════════════════════════════════════

pub(crate) struct EpsNfa<P> {
    n: usize,
    eps: Vec<(usize, usize)>,
    chr: Vec<(usize, P, usize)>,
    initials: Vec<usize>,
    accepts: Vec<usize>,
}

impl<P: Clone> EpsNfa<P> {
    pub(crate) fn from_parts(
        n: usize,
        eps: Vec<(usize, usize)>,
        chr: Vec<(usize, P, usize)>,
        initials: Vec<usize>,
        accepts: Vec<usize>,
    ) -> Self {
        Self { n, eps, chr, initials, accepts }
    }

    #[allow(clippy::type_complexity)]
    pub(crate) fn into_parts(
        self,
    ) -> (usize, Vec<(usize, usize)>, Vec<(usize, P, usize)>, Vec<usize>, Vec<usize>) {
        (self.n, self.eps, self.chr, self.initials, self.accepts)
    }

    pub(crate) fn empty() -> Self {
        EpsNfa {
            n: 1,
            eps: Vec::new(),
            chr: Vec::new(),
            initials: vec![0],
            accepts: Vec::new(),
        }
    }

    pub(crate) fn epsilon() -> Self {
        EpsNfa {
            n: 1,
            eps: Vec::new(),
            chr: Vec::new(),
            initials: vec![0],
            accepts: vec![0],
        }
    }

    pub(crate) fn elem(class: P) -> Self {
        EpsNfa {
            n: 2,
            eps: Vec::new(),
            chr: vec![(0, class, 1)],
            initials: vec![0],
            accepts: vec![1],
        }
    }

    pub(crate) fn concat(a: EpsNfa<P>, b: EpsNfa<P>) -> Self {
        let EpsNfa {
            n: a_n,
            eps: a_eps,
            chr: a_chr,
            initials: a_initials,
            accepts: a_accepts,
        } = a;
        let EpsNfa {
            n: b_n,
            eps: b_eps,
            chr: b_chr,
            initials: b_initials,
            accepts: b_accepts,
        } = b;

        if a_n >= b_n {
            let offset = a_n;
            let mut eps = a_eps;
            eps.reserve(b_eps.len() + a_accepts.len() * b_initials.len());
            eps.extend(
                b_eps
                    .into_iter()
                    .map(|(from, to)| (from + offset, to + offset)),
            );
            for accept in a_accepts {
                for initial in &b_initials {
                    eps.push((accept, initial + offset));
                }
            }
            let mut chr = a_chr;
            chr.reserve(b_chr.len());
            chr.extend(
                b_chr
                    .into_iter()
                    .map(|(from, guard, to)| (from + offset, guard, to + offset)),
            );
            EpsNfa {
                n: a_n + b_n,
                eps,
                chr,
                initials: a_initials,
                accepts: b_accepts.into_iter().map(|state| state + offset).collect(),
            }
        } else {
            // State numbers are observationally irrelevant. Keeping the larger
            // right graph in place means only the smaller left graph is offset.
            let offset = b_n;
            let mut eps = b_eps;
            eps.reserve(a_eps.len() + a_accepts.len() * b_initials.len());
            eps.extend(
                a_eps
                    .into_iter()
                    .map(|(from, to)| (from + offset, to + offset)),
            );
            for accept in a_accepts {
                for initial in &b_initials {
                    eps.push((accept + offset, *initial));
                }
            }
            let mut chr = b_chr;
            chr.reserve(a_chr.len());
            chr.extend(
                a_chr
                    .into_iter()
                    .map(|(from, guard, to)| (from + offset, guard, to + offset)),
            );
            EpsNfa {
                n: a_n + b_n,
                eps,
                chr,
                initials: a_initials.into_iter().map(|state| state + offset).collect(),
                accepts: b_accepts,
            }
        }
    }

    pub(crate) fn alt(a: EpsNfa<P>, b: EpsNfa<P>) -> Self {
        let EpsNfa {
            n: a_n,
            eps: a_eps,
            chr: a_chr,
            initials: a_initials,
            accepts: a_accepts,
        } = a;
        let EpsNfa {
            n: b_n,
            eps: b_eps,
            chr: b_chr,
            initials: b_initials,
            accepts: b_accepts,
        } = b;

        if a_n >= b_n {
            let offset = a_n;
            let mut eps = a_eps;
            eps.reserve(b_eps.len());
            eps.extend(
                b_eps
                    .into_iter()
                    .map(|(from, to)| (from + offset, to + offset)),
            );
            let mut chr = a_chr;
            chr.reserve(b_chr.len());
            chr.extend(
                b_chr
                    .into_iter()
                    .map(|(from, guard, to)| (from + offset, guard, to + offset)),
            );
            let mut initials = a_initials;
            initials.extend(b_initials.into_iter().map(|state| state + offset));
            let mut accepts = a_accepts;
            accepts.extend(b_accepts.into_iter().map(|state| state + offset));
            EpsNfa {
                n: a_n + b_n,
                eps,
                chr,
                initials,
                accepts,
            }
        } else {
            let offset = b_n;
            let mut eps = b_eps;
            eps.reserve(a_eps.len());
            eps.extend(
                a_eps
                    .into_iter()
                    .map(|(from, to)| (from + offset, to + offset)),
            );
            let mut chr = b_chr;
            chr.reserve(a_chr.len());
            chr.extend(
                a_chr
                    .into_iter()
                    .map(|(from, guard, to)| (from + offset, guard, to + offset)),
            );
            let mut initials = b_initials;
            initials.extend(a_initials.into_iter().map(|state| state + offset));
            let mut accepts = b_accepts;
            accepts.extend(a_accepts.into_iter().map(|state| state + offset));
            EpsNfa {
                n: a_n + b_n,
                eps,
                chr,
                initials,
                accepts,
            }
        }
    }

    pub(crate) fn star(a: EpsNfa<P>) -> Self {
        let EpsNfa { n, mut eps, chr, initials, accepts } = a;
        eps.reserve(initials.len() + accepts.len());
        for initial in &initials {
            eps.push((n, *initial));
        }
        for accept in accepts {
            eps.push((accept, n));
        }
        EpsNfa {
            n: n + 1,
            eps,
            chr,
            initials: vec![n],
            accepts: vec![n],
        }
    }

    fn from_sfa<A>(sfa: SymbolicAutomaton<A>) -> Self
    where
        A: BooleanAlgebra<Predicate = P>,
    {
        let chr = sfa
            .transitions
            .into_iter()
            .map(|transition| (transition.from, transition.guard, transition.to))
            .collect();
        let mut initials: Vec<usize> = sfa.initial_states.into_iter().collect();
        initials.sort_unstable();
        let mut accepts: Vec<usize> = sfa.accepting_states.into_iter().collect();
        accepts.sort_unstable();
        EpsNfa {
            n: sfa.states.len().max(1),
            eps: Vec::new(),
            chr,
            initials,
            accepts,
        }
    }

    pub(crate) fn epsilon_closures(&self) -> Vec<Vec<usize>> {
        let mut adjacency = vec![Vec::new(); self.n];
        for &(from, to) in &self.eps {
            adjacency[from].push(to);
        }

        let mut closures = Vec::with_capacity(self.n);
        let mut seen_at = vec![usize::MAX; self.n];
        let mut stack = Vec::new();
        for source in 0..self.n {
            let mut closure = Vec::new();
            stack.push(source);
            seen_at[source] = source;
            while let Some(state) = stack.pop() {
                closure.push(state);
                for &next in &adjacency[state] {
                    if seen_at[next] != source {
                        seen_at[next] = source;
                        stack.push(next);
                    }
                }
            }
            closures.push(closure);
        }
        closures
    }

    fn into_sfa<A>(self, algebra: A) -> SymbolicAutomaton<A>
    where
        A: BooleanAlgebra<Predicate = P>,
    {
        let mut accept_set = vec![false; self.n];
        for accept in &self.accepts {
            accept_set[*accept] = true;
        }
        let closures = self.epsilon_closures();
        let mut character_adjacency = vec![Vec::new(); self.n];
        for (index, (from, _, _)) in self.chr.iter().enumerate() {
            character_adjacency[*from].push(index);
        }
        let mut sfa = SymbolicAutomaton::new(algebra);
        for i in 0..self.n {
            let is_acc = closures[i].iter().any(|state| accept_set[*state]);
            sfa.add_state(is_acc, None);
        }
        for init in self.initials {
            sfa.set_initial(init);
        }
        for (source, closure) in closures.iter().enumerate() {
            for state in closure {
                for index in &character_adjacency[*state] {
                    let (_, guard, to) = &self.chr[*index];
                    sfa.add_transition(source, *to, guard.clone());
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
    enum Task<'pred, P> {
        Visit(&'pred RegexPred<P>),
        Concat,
        Alt,
        Star,
        Inter,
        Compl,
    }

    let mut tasks = vec![Task::Visit(p)];
    let mut values = Vec::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(RegexPred::Empty) => values.push(EpsNfa::empty()),
            Task::Visit(RegexPred::Epsilon) => values.push(EpsNfa::epsilon()),
            Task::Visit(RegexPred::Elem(class)) => values.push(EpsNfa::elem(class.clone())),
            Task::Visit(RegexPred::Length(lo, hi)) => {
                let sigma = || EpsNfa::elem(algebra.true_pred());
                let mut nfa = EpsNfa::epsilon();
                for _ in 0..*lo {
                    nfa = EpsNfa::concat(nfa, sigma());
                }
                match hi {
                    None => nfa = EpsNfa::concat(nfa, EpsNfa::star(sigma())),
                    Some(upper) => {
                        for _ in 0..upper.saturating_sub(*lo) {
                            nfa = EpsNfa::concat(nfa, EpsNfa::alt(EpsNfa::epsilon(), sigma()));
                        }
                    },
                }
                values.push(nfa);
            },
            Task::Visit(RegexPred::Concat(left, right)) => {
                tasks.push(Task::Concat);
                tasks.push(Task::Visit(right));
                tasks.push(Task::Visit(left));
            },
            Task::Visit(RegexPred::Alt(left, right)) => {
                tasks.push(Task::Alt);
                tasks.push(Task::Visit(right));
                tasks.push(Task::Visit(left));
            },
            Task::Visit(RegexPred::Inter(left, right)) => {
                tasks.push(Task::Inter);
                tasks.push(Task::Visit(right));
                tasks.push(Task::Visit(left));
            },
            Task::Visit(RegexPred::Star(body)) => {
                tasks.push(Task::Star);
                tasks.push(Task::Visit(body));
            },
            Task::Visit(RegexPred::Compl(body)) => {
                tasks.push(Task::Compl);
                tasks.push(Task::Visit(body));
            },
            Task::Concat => {
                let right = values
                    .pop()
                    .expect("regex compilation lost right concatenand");
                let left = values
                    .pop()
                    .expect("regex compilation lost left concatenand");
                values.push(EpsNfa::concat(left, right));
            },
            Task::Alt => {
                let right = values
                    .pop()
                    .expect("regex compilation lost right alternative");
                let left = values
                    .pop()
                    .expect("regex compilation lost left alternative");
                values.push(EpsNfa::alt(left, right));
            },
            Task::Star => {
                let body = values.pop().expect("regex compilation lost star body");
                values.push(EpsNfa::star(body));
            },
            Task::Inter => {
                let right = values
                    .pop()
                    .expect("regex compilation lost right intersection");
                let left = values
                    .pop()
                    .expect("regex compilation lost left intersection");
                let left = left.into_sfa(algebra.clone());
                let right = right.into_sfa(algebra.clone());
                values.push(EpsNfa::from_sfa(left.intersect(&right)));
            },
            Task::Compl => {
                let body = values
                    .pop()
                    .expect("regex compilation lost complement body");
                values.push(EpsNfa::from_sfa(body.into_sfa(algebra.clone()).complement()));
            },
        }
    }
    debug_assert_eq!(values.len(), 1);
    values.pop().expect("regex compilation produced no NFA")
}

/// Compile a [`RegexPred`] to an SFA over `A`.
pub fn compile<A>(algebra: &A, p: &RegexPred<A::Predicate>) -> SymbolicAutomaton<A>
where
    A: BooleanAlgebra,
{
    compile_eps(algebra, p).into_sfa(algebra.clone())
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
