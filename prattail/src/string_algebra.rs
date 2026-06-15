//! `StringAlgebra` — an effective Boolean algebra over **strings**, whose
//! predicates are symbolic regular languages.
//!
//! A string predicate ([`StrPred`]) is a symbolic regex AST over Unicode
//! character classes (`CharClassPred`): `∅`, `ε`, a character class, literal,
//! length bound, concatenation, alternation, Kleene star, intersection, and
//! complement. The AST derives `Eq + Hash` (so it can be an [`AnyPred`] leaf and
//! participate in minterm/determinization hashing), while the decision
//! procedures are **exact**: the AST compiles (Glushkov-free, via a small
//! epsilon-NFA) to a [`SymbolicAutomaton<CharClassAlgebra>`], and
//!
//! - `and`/`or`/`not` are the regular-language operations `Inter`/`Alt`/`Compl`,
//!   realized at decision time by the SFA's `intersect`/`union`/`complement`;
//! - `is_satisfiable` is SFA non-emptiness;
//! - `witness` is the SFA's shortest accepted word;
//! - `evaluate(p, s)` simulates the SFA on `s`'s characters.
//!
//! Regular languages are closed under all boolean operations and have decidable
//! emptiness/membership, so this is a genuine (exact, decidable) effective
//! Boolean algebra — not a lossy length×content approximation. Length and
//! literal predicates are conveniences that desugar into the core operators.
//!
//! [`AnyPred`]: crate::any_algebra::AnyPred

use std::collections::HashSet;

use crate::symbolic::{BooleanAlgebra, CharClassAlgebra, CharClassPred, SymbolicAutomaton};

// ══════════════════════════════════════════════════════════════════════════════
// StrPred — symbolic regex AST
// ══════════════════════════════════════════════════════════════════════════════

/// A string predicate: a symbolic regular language over character classes.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum StrPred {
    /// The empty language `∅` (matches no string).
    Empty,
    /// The language `{ "" }` (matches only the empty string).
    Epsilon,
    /// A single character drawn from the given class.
    Class(CharClassPred),
    /// An exact literal string (each character matched positionally).
    Literal(String),
    /// A length constraint `lo ≤ |s| ≤ hi` (`hi = None` means unbounded above).
    Length(usize, Option<usize>),
    /// Concatenation.
    Concat(Box<StrPred>, Box<StrPred>),
    /// Alternation (union).
    Alt(Box<StrPred>, Box<StrPred>),
    /// Kleene star.
    Star(Box<StrPred>),
    /// Intersection.
    Inter(Box<StrPred>, Box<StrPred>),
    /// Complement (relative to `Σ*`).
    Compl(Box<StrPred>),
}

impl StrPred {
    /// `Σ*` — every string.
    pub fn any() -> StrPred {
        StrPred::Star(Box::new(StrPred::Class(CharClassPred::True)))
    }

    /// A single character class `[lo-hi]`.
    pub fn char_range(lo: char, hi: char) -> StrPred {
        StrPred::Class(CharClassPred::Range(lo, hi))
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Epsilon-NFA over character classes (compilation target)
// ══════════════════════════════════════════════════════════════════════════════

/// A Thompson-style epsilon-NFA whose character edges are guarded by
/// `CharClassPred`. Compiled from [`StrPred`] and then epsilon-eliminated into a
/// [`SymbolicAutomaton<CharClassAlgebra>`].
struct EpsNfa {
    n: usize,
    eps: Vec<(usize, usize)>,
    chr: Vec<(usize, CharClassPred, usize)>,
    initials: Vec<usize>,
    accepts: Vec<usize>,
}

impl EpsNfa {
    /// `∅` — one state, no accepting state.
    fn empty() -> Self {
        EpsNfa { n: 1, eps: Vec::new(), chr: Vec::new(), initials: vec![0], accepts: Vec::new() }
    }

    /// `ε` — one state, initial and accepting.
    fn epsilon() -> Self {
        EpsNfa { n: 1, eps: Vec::new(), chr: Vec::new(), initials: vec![0], accepts: vec![0] }
    }

    /// A single character drawn from `class`.
    fn class(class: CharClassPred) -> Self {
        EpsNfa { n: 2, eps: Vec::new(), chr: vec![(0, class, 1)], initials: vec![0], accepts: vec![1] }
    }

    /// Shift every state index by `off`.
    fn shifted(&self, off: usize) -> (Vec<(usize, usize)>, Vec<(usize, CharClassPred, usize)>, Vec<usize>, Vec<usize>) {
        let eps = self.eps.iter().map(|&(a, b)| (a + off, b + off)).collect();
        let chr = self.chr.iter().map(|(a, g, b)| (a + off, g.clone(), b + off)).collect();
        let initials = self.initials.iter().map(|&s| s + off).collect();
        let accepts = self.accepts.iter().map(|&s| s + off).collect();
        (eps, chr, initials, accepts)
    }

    /// Concatenation `a · b`.
    fn concat(a: EpsNfa, b: EpsNfa) -> Self {
        let off = a.n;
        let (mut eps, mut chr, _b_init, b_accepts) = b.shifted(off);
        let b_initials: Vec<usize> = b.initials.iter().map(|&s| s + off).collect();
        eps.extend(a.eps.iter().cloned());
        chr.extend(a.chr.iter().cloned());
        // ε-link each accepting state of `a` to each initial state of `b`.
        for &ai in &a.accepts {
            for &bi in &b_initials {
                eps.push((ai, bi));
            }
        }
        EpsNfa { n: a.n + b.n, eps, chr, initials: a.initials.clone(), accepts: b_accepts }
    }

    /// Alternation `a | b`.
    fn alt(a: EpsNfa, b: EpsNfa) -> Self {
        let off = a.n;
        let (b_eps, b_chr, b_init, b_acc) = b.shifted(off);
        let mut eps = a.eps.clone();
        eps.extend(b_eps);
        let mut chr = a.chr.clone();
        chr.extend(b_chr);
        let mut initials = a.initials.clone();
        initials.extend(b_init);
        let mut accepts = a.accepts.clone();
        accepts.extend(b_acc);
        EpsNfa { n: a.n + b.n, eps, chr, initials, accepts }
    }

    /// Kleene star `a*` (includes the empty word).
    fn star(a: EpsNfa) -> Self {
        let q = a.n;
        let mut eps = a.eps.clone();
        for &ai in &a.initials {
            eps.push((q, ai));
        }
        for &acc in &a.accepts {
            eps.push((acc, q));
        }
        EpsNfa { n: a.n + 1, eps, chr: a.chr.clone(), initials: vec![q], accepts: vec![q] }
    }

    /// Wrap an (epsilon-free) SFA as an `EpsNfa` so it can be embedded in further
    /// regex structure.
    fn from_sfa(sfa: &SymbolicAutomaton<CharClassAlgebra>) -> Self {
        let chr = sfa
            .transitions
            .iter()
            .map(|t| (t.from, t.guard.clone(), t.to))
            .collect();
        let mut initials: Vec<usize> = sfa.initial_states.iter().copied().collect();
        initials.sort_unstable();
        let mut accepts: Vec<usize> = sfa.accepting_states.iter().copied().collect();
        accepts.sort_unstable();
        EpsNfa { n: sfa.states.len().max(1), eps: Vec::new(), chr, initials, accepts }
    }

    /// Epsilon-closure of a state set.
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

    /// Epsilon-eliminate into an SFA over `CharClassAlgebra`.
    fn to_sfa(&self) -> SymbolicAutomaton<CharClassAlgebra> {
        let accept_set: HashSet<usize> = self.accepts.iter().copied().collect();
        let ecl: Vec<HashSet<usize>> = (0..self.n).map(|s| self.eclosure(&[s])).collect();

        let mut sfa = SymbolicAutomaton::new(CharClassAlgebra::new());
        for i in 0..self.n {
            let is_acc = ecl[i].iter().any(|s| accept_set.contains(s));
            sfa.add_state(is_acc, None);
        }
        for &init in &self.initials {
            sfa.set_initial(init);
        }
        // For each char edge u --g--> v, every state s with u in eclosure(s)
        // gains the transition s --g--> v.
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

/// Compile a [`StrPred`] to an epsilon-NFA (recursively; `Inter`/`Compl` route
/// through the SFA's product/complement and are wrapped back in).
fn compile_eps(p: &StrPred) -> EpsNfa {
    match p {
        StrPred::Empty => EpsNfa::empty(),
        StrPred::Epsilon => EpsNfa::epsilon(),
        StrPred::Class(c) => EpsNfa::class(c.clone()),
        StrPred::Literal(s) => {
            let mut acc = EpsNfa::epsilon();
            for ch in s.chars() {
                acc = EpsNfa::concat(acc, EpsNfa::class(CharClassPred::Range(ch, ch)));
            }
            acc
        },
        StrPred::Length(lo, hi) => {
            let sigma = || EpsNfa::class(CharClassPred::True);
            let mut acc = EpsNfa::epsilon();
            for _ in 0..*lo {
                acc = EpsNfa::concat(acc, sigma());
            }
            match hi {
                None => EpsNfa::concat(acc, EpsNfa::star(sigma())),
                Some(h) => {
                    // (lo) mandatory + (h - lo) optional Σ.
                    let optional = h.saturating_sub(*lo);
                    for _ in 0..optional {
                        acc = EpsNfa::concat(acc, EpsNfa::alt(EpsNfa::epsilon(), sigma()));
                    }
                    acc
                },
            }
        },
        StrPred::Concat(a, b) => EpsNfa::concat(compile_eps(a), compile_eps(b)),
        StrPred::Alt(a, b) => EpsNfa::alt(compile_eps(a), compile_eps(b)),
        StrPred::Star(a) => EpsNfa::star(compile_eps(a)),
        StrPred::Inter(a, b) => {
            let sfa = compile_eps(a).to_sfa().intersect(&compile_eps(b).to_sfa());
            EpsNfa::from_sfa(&sfa)
        },
        StrPred::Compl(a) => {
            let sfa = compile_eps(a).to_sfa().complement();
            EpsNfa::from_sfa(&sfa)
        },
    }
}

/// Compile a [`StrPred`] to an SFA over character classes.
fn compile(p: &StrPred) -> SymbolicAutomaton<CharClassAlgebra> {
    compile_eps(p).to_sfa()
}

// ══════════════════════════════════════════════════════════════════════════════
// StringAlgebra
// ══════════════════════════════════════════════════════════════════════════════

/// The effective Boolean algebra of symbolic regular languages over strings.
#[derive(Clone, Debug, Default)]
pub struct StringAlgebra;

impl StringAlgebra {
    /// Construct the algebra.
    pub fn new() -> Self {
        StringAlgebra
    }
}

impl BooleanAlgebra for StringAlgebra {
    type Predicate = StrPred;
    type Domain = String;

    fn true_pred(&self) -> StrPred {
        StrPred::any()
    }

    fn false_pred(&self) -> StrPred {
        StrPred::Empty
    }

    fn and(&self, a: &StrPred, b: &StrPred) -> StrPred {
        StrPred::Inter(Box::new(a.clone()), Box::new(b.clone()))
    }

    fn or(&self, a: &StrPred, b: &StrPred) -> StrPred {
        StrPred::Alt(Box::new(a.clone()), Box::new(b.clone()))
    }

    fn not(&self, a: &StrPred) -> StrPred {
        StrPred::Compl(Box::new(a.clone()))
    }

    fn is_satisfiable(&self, a: &StrPred) -> bool {
        !compile(a).is_empty()
    }

    fn witness(&self, a: &StrPred) -> Option<String> {
        compile(a).shortest_accepted().map(|chars| chars.into_iter().collect())
    }

    fn evaluate(&self, pred: &StrPred, elem: &String) -> bool {
        let word: Vec<char> = elem.chars().collect();
        compile(pred).accepts(&word)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn digit() -> StrPred {
        StrPred::char_range('0', '9')
    }

    #[test]
    fn literal_match() {
        let alg = StringAlgebra::new();
        let ab = StrPred::Literal("ab".to_string());
        assert!(alg.evaluate(&ab, &"ab".to_string()));
        assert!(!alg.evaluate(&ab, &"a".to_string()));
        assert!(!alg.evaluate(&ab, &"abc".to_string()));
        assert!(alg.is_satisfiable(&ab));
        assert_eq!(alg.witness(&ab), Some("ab".to_string()));
    }

    #[test]
    fn digit_star() {
        let alg = StringAlgebra::new();
        let digits = StrPred::Star(Box::new(digit()));
        assert!(alg.evaluate(&digits, &"".to_string()));
        assert!(alg.evaluate(&digits, &"123".to_string()));
        assert!(!alg.evaluate(&digits, &"12a".to_string()));
    }

    #[test]
    fn length_and_content_intersection() {
        let alg = StringAlgebra::new();
        // exactly two characters, all digits
        let two_digits = alg.and(&StrPred::Length(2, Some(2)), &StrPred::Star(Box::new(digit())));
        assert!(alg.evaluate(&two_digits, &"42".to_string()));
        assert!(!alg.evaluate(&two_digits, &"4".to_string()));
        assert!(!alg.evaluate(&two_digits, &"423".to_string()));
        assert!(!alg.evaluate(&two_digits, &"ab".to_string()));
        assert!(alg.is_satisfiable(&two_digits));
        let w = alg.witness(&two_digits).expect("nonempty");
        assert!(alg.evaluate(&two_digits, &w));
        assert_eq!(w.chars().count(), 2);
    }

    #[test]
    fn length_bounds() {
        let alg = StringAlgebra::new();
        let two_to_four = StrPred::Length(2, Some(4));
        assert!(!alg.evaluate(&two_to_four, &"a".to_string()));
        assert!(alg.evaluate(&two_to_four, &"ab".to_string()));
        assert!(alg.evaluate(&two_to_four, &"abcd".to_string()));
        assert!(!alg.evaluate(&two_to_four, &"abcde".to_string()));

        let at_least_three = StrPred::Length(3, None);
        assert!(!alg.evaluate(&at_least_three, &"ab".to_string()));
        assert!(alg.evaluate(&at_least_three, &"abcdef".to_string()));
    }

    #[test]
    fn complement_and_boolean_laws() {
        let alg = StringAlgebra::new();
        let digits = StrPred::Star(Box::new(digit()));
        let not_digits = alg.not(&digits);
        // "12" is all digits → not in the complement.
        assert!(!alg.evaluate(&not_digits, &"12".to_string()));
        // "1a" is not all-digits → in the complement.
        assert!(alg.evaluate(&not_digits, &"1a".to_string()));
        assert!(alg.evaluate(&not_digits, &"a".to_string()));

        // a ∧ ¬a is unsatisfiable.
        assert!(!alg.is_satisfiable(&alg.and(&digits, &not_digits)));
        // ¬∅ = Σ* is satisfiable (e.g. accepts the empty string).
        assert!(alg.is_satisfiable(&alg.not(&StrPred::Empty)));
        // ¬Σ* = ∅ is unsatisfiable.
        assert!(!alg.is_satisfiable(&alg.not(&StrPred::any())));
    }

    #[test]
    fn empty_and_top() {
        let alg = StringAlgebra::new();
        assert!(!alg.is_satisfiable(&alg.false_pred()));
        assert!(alg.is_satisfiable(&alg.true_pred()));
        assert!(alg.evaluate(&alg.true_pred(), &"anything".to_string()));
        assert!(!alg.evaluate(&alg.false_pred(), &"".to_string()));
    }
}
