//! `StringAlgebra` — an effective Boolean algebra over **strings**, whose
//! predicates are symbolic regular languages.
//!
//! This is the `A = CharClassAlgebra` instantiation of the generic
//! symbolic-regex engine [`crate::regex_sfa`], with a `String` (rather than
//! `Vec<char>`) domain and char-oriented conveniences (`Literal`, `Length`).
//!
//! A string predicate ([`StrPred`]) is a symbolic regex AST over Unicode
//! character classes; it desugars to a [`RegexPred<CharClassPred>`] and is
//! decided exactly by compiling to a `SymbolicAutomaton<CharClassAlgebra>`:
//! `and`/`or`/`not` are `Inter`/`Alt`/`Compl`, `is_satisfiable` is SFA
//! non-emptiness, `witness` is the shortest accepted word, and `evaluate(p, s)`
//! simulates the SFA on `s`'s characters. Regular languages are closed under all
//! boolean ops with decidable emptiness/membership, so this is a genuine,
//! exact EBA.

use crate::regex_sfa::{RegexAlgebra, RegexPred};
use crate::symbolic::{BooleanAlgebra, CharClassAlgebra, CharClassPred};

// ══════════════════════════════════════════════════════════════════════════════
// StrPred — char-oriented symbolic regex AST
// ══════════════════════════════════════════════════════════════════════════════

/// A string predicate: a symbolic regular language over character classes.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum StrPred {
    /// The empty language `∅`.
    Empty,
    /// `{ "" }`.
    Epsilon,
    /// A single character drawn from the class.
    Class(CharClassPred),
    /// An exact literal string.
    Literal(String),
    /// A length constraint `lo ≤ |s| ≤ hi` (`hi = None` is unbounded above).
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

    /// Desugar to the generic regex over character-class predicates.
    fn to_regex(&self) -> RegexPred<CharClassPred> {
        match self {
            StrPred::Empty => RegexPred::Empty,
            StrPred::Epsilon => RegexPred::Epsilon,
            StrPred::Class(c) => RegexPred::Elem(c.clone()),
            StrPred::Literal(s) => {
                let mut acc = RegexPred::Epsilon;
                for ch in s.chars() {
                    acc = RegexPred::Concat(
                        Box::new(acc),
                        Box::new(RegexPred::Elem(CharClassPred::Range(ch, ch))),
                    );
                }
                acc
            },
            StrPred::Length(lo, hi) => RegexPred::Length(*lo, *hi),
            StrPred::Concat(a, b) => {
                RegexPred::Concat(Box::new(a.to_regex()), Box::new(b.to_regex()))
            },
            StrPred::Alt(a, b) => RegexPred::Alt(Box::new(a.to_regex()), Box::new(b.to_regex())),
            StrPred::Star(a) => RegexPred::Star(Box::new(a.to_regex())),
            StrPred::Inter(a, b) => {
                RegexPred::Inter(Box::new(a.to_regex()), Box::new(b.to_regex()))
            },
            StrPred::Compl(a) => RegexPred::Compl(Box::new(a.to_regex())),
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// StringAlgebra
// ══════════════════════════════════════════════════════════════════════════════

/// The effective Boolean algebra of symbolic regular languages over strings.
#[derive(Clone, Debug)]
pub struct StringAlgebra {
    inner: RegexAlgebra<CharClassAlgebra>,
}

impl StringAlgebra {
    /// Construct the algebra.
    pub fn new() -> Self {
        StringAlgebra { inner: RegexAlgebra::new(CharClassAlgebra::new()) }
    }
}

impl Default for StringAlgebra {
    fn default() -> Self {
        StringAlgebra::new()
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
        self.inner.is_satisfiable(&a.to_regex())
    }

    fn witness(&self, a: &StrPred) -> Option<String> {
        self.inner.witness(&a.to_regex()).map(|chars| chars.into_iter().collect())
    }

    fn evaluate(&self, pred: &StrPred, elem: &String) -> bool {
        let word: Vec<char> = elem.chars().collect();
        self.inner.evaluate(&pred.to_regex(), &word)
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
        assert!(!alg.evaluate(&not_digits, &"12".to_string()));
        assert!(alg.evaluate(&not_digits, &"1a".to_string()));
        assert!(alg.evaluate(&not_digits, &"a".to_string()));
        assert!(!alg.is_satisfiable(&alg.and(&digits, &not_digits)));
        assert!(alg.is_satisfiable(&alg.not(&StrPred::Empty)));
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
