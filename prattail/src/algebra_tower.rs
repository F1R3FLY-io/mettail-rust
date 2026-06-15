//! The algebra tower: `RejectSafeAlgebra` ⊃ `HeytingAlgebra` ⊃ (classical)
//! `BooleanAlgebra` — the type-level discipline that keeps a **semi-decidable**
//! algebra from ever being mistaken for a classical one.
//!
//! ## Why a tower
//!
//! Structural predicates (over the shape of data) are decided exactly: their
//! algebras are classical [`BooleanAlgebra`](crate::symbolic::BooleanAlgebra)s
//! with an involutive complement and decidable satisfiability. Behavioral
//! predicates (over the dynamics — reachability, modal/temporal properties) are
//! only **semi-decidable**: their complement is unsound to treat classically
//! (a bounded "no witness found" is not a proof of unsatisfiability). Such an
//! algebra is a *Heyting* algebra (intuitionistic: no excluded middle, no
//! involutive `¬¬`), and its satisfiability is three-valued ([`Sat3`]).
//!
//! The tower makes this a compile-time guarantee:
//! - [`RejectSafeAlgebra`] — weakest: `and`/`or`/`pseudo_complement` +
//!   three-valued `is_satisfiable_3v`. Laws: SAT-soundness and
//!   double-negation-soundness only. **No involutive complement, no excluded
//!   middle.**
//! - [`HeytingAlgebra`] `: RejectSafeAlgebra` — adds intuitionistic `implies`
//!   (`→`) and `regularize` (`¬¬`).
//! - [`BooleanAlgebra`](crate::symbolic::BooleanAlgebra) — the classical tier
//!   (unchanged), with the involutive `not` and 2-valued `is_satisfiable` that
//!   the symbolic-automaton complement/determinization/equivalence require.
//!
//! ## Realization (coherence-safe, non-invasive)
//!
//! `BooleanAlgebra` and its ~13 implementors are left **untouched**. A classical
//! algebra is lifted into the reject-safe / Heyting tiers by wrapping it in
//! [`Classical`], whose impls delegate to the classical operations
//! (`pseudo_complement = not`, `regularize = id`, `is_satisfiable_3v` only ever
//! `Sat`/`Unsat`, `implies = ¬a ∨ b`). A genuinely semi-decidable algebra (e.g.
//! the forthcoming `BehavioralAlgebra`) implements [`HeytingAlgebra`] **directly
//! and does not implement [`BooleanAlgebra`]** — so any operation bounded on
//! `BooleanAlgebra` (every SFA complement/determinize/equivalence) is statically
//! unavailable on it. That is the load-bearing safety property.
//!
//! This avoids both pitfalls of a literal Rust supertrait chain: it neither
//! requires moving method bodies across all 13 existing impls, nor introduces
//! method-name ambiguity on the many unqualified `.and()`/`.or()` calls in the
//! existing combinators.

use std::fmt::Debug;
use std::hash::Hash;

use crate::symbolic::BooleanAlgebra;

// ══════════════════════════════════════════════════════════════════════════════
// Sat3 — three-valued satisfiability
// ══════════════════════════════════════════════════════════════════════════════

/// A three-valued satisfiability result. Classical algebras only ever produce
/// `Sat`/`Unsat`; a semi-decidable algebra may produce `DontKnow` (e.g. a
/// bounded reachability check that neither found a witness nor proved emptiness).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Sat3 {
    /// Definitely satisfiable (a witness exists / was found).
    Sat,
    /// Definitely unsatisfiable (proven empty).
    Unsat,
    /// Undecided within the available budget / procedure.
    DontKnow,
}

impl Sat3 {
    /// Kleene strong conjunction (`Unsat` annihilates; `Sat ∧ Sat = Sat`).
    pub fn and(self, other: Sat3) -> Sat3 {
        use Sat3::*;
        match (self, other) {
            (Unsat, _) | (_, Unsat) => Unsat,
            (Sat, Sat) => Sat,
            _ => DontKnow,
        }
    }

    /// Kleene strong disjunction (`Sat` annihilates; `Unsat ∨ Unsat = Unsat`).
    pub fn or(self, other: Sat3) -> Sat3 {
        use Sat3::*;
        match (self, other) {
            (Sat, _) | (_, Sat) => Sat,
            (Unsat, Unsat) => Unsat,
            _ => DontKnow,
        }
    }

    /// Three-valued negation (`DontKnow` is the fixpoint).
    pub fn not(self) -> Sat3 {
        match self {
            Sat3::Sat => Sat3::Unsat,
            Sat3::Unsat => Sat3::Sat,
            Sat3::DontKnow => Sat3::DontKnow,
        }
    }

    /// Collapse to a classical `bool` only when sound: `DontKnow → None` forces
    /// the caller to handle the undecided case rather than silently treating it
    /// as `false`.
    pub fn into_safe_bool(self) -> Option<bool> {
        match self {
            Sat3::Sat => Some(true),
            Sat3::Unsat => Some(false),
            Sat3::DontKnow => None,
        }
    }

    /// Bridge from a decidable boolean.
    pub fn from_decidable(b: bool) -> Sat3 {
        if b {
            Sat3::Sat
        } else {
            Sat3::Unsat
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// RejectSafeAlgebra — the weakest tier
// ══════════════════════════════════════════════════════════════════════════════

/// The weakest algebra tier: a bounded (`∧`, `∨`) structure with a
/// *pseudo*-complement and a three-valued satisfiability oracle. No involutive
/// complement and no excluded middle, so it is sound for a semi-decidable
/// (behavioral) algebra to inhabit.
pub trait RejectSafeAlgebra: Clone + Debug + Send + Sync + 'static {
    /// Guard predicate type.
    type Predicate: Clone + Debug + Eq + Hash + Send + Sync + 'static;
    /// Concrete domain element type.
    type Domain: Clone + Debug + Send + Sync + 'static;

    /// The everywhere-true predicate.
    fn true_pred(&self) -> Self::Predicate;
    /// The everywhere-false predicate.
    fn false_pred(&self) -> Self::Predicate;
    /// Conjunction.
    fn and(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate;
    /// Disjunction.
    fn or(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate;

    /// Pseudo-complement — *a* sound refutation, not required to be involutive.
    fn pseudo_complement(&self, a: &Self::Predicate) -> Self::Predicate;

    /// Three-valued satisfiability (the core semi-decision procedure).
    fn is_satisfiable_3v(&self, a: &Self::Predicate) -> Sat3;

    /// Evaluate a predicate on a concrete element (always a finite check).
    fn evaluate(&self, pred: &Self::Predicate, elem: &Self::Domain) -> bool;

    /// `¬¬`-regularization. Default = `pseudo_complement ∘ pseudo_complement`
    /// (sound intuitionistic double negation, using only this tier's ops). A
    /// classical algebra overrides this to the identity.
    fn regularize(&self, a: &Self::Predicate) -> Self::Predicate {
        self.pseudo_complement(&self.pseudo_complement(a))
    }

    /// Best-effort witness; defaults to `None` (a reject-safe algebra need not
    /// synthesize witnesses).
    fn witness(&self, _a: &Self::Predicate) -> Option<Self::Domain> {
        None
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// HeytingAlgebra — the middle tier
// ══════════════════════════════════════════════════════════════════════════════

/// A Heyting algebra: a reject-safe algebra with a genuine intuitionistic
/// implication `a → b` (relative pseudo-complement). Still no excluded middle and
/// no involutive complement. The law `pseudo_complement(a) ≡ implies(a, ⊥)`
/// relates the two.
pub trait HeytingAlgebra: RejectSafeAlgebra {
    /// Intuitionistic implication `a → b`.
    fn implies(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate;

    /// Heyting negation `a → ⊥` (provided; coincides with `pseudo_complement`).
    fn heyting_not(&self, a: &Self::Predicate) -> Self::Predicate {
        self.implies(a, &self.false_pred())
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Classical<A> — lift a BooleanAlgebra into the tower
// ══════════════════════════════════════════════════════════════════════════════

/// Wraps a classical [`BooleanAlgebra`] so it can be used where a
/// [`RejectSafeAlgebra`] / [`HeytingAlgebra`] is expected (e.g. the structural
/// leg of a mixed structural×behavioral product). All tier operations delegate
/// to the classical ones, so the result is exact (`is_satisfiable_3v` never
/// returns `DontKnow`, `regularize` is the identity, `pseudo_complement` is the
/// involutive complement).
#[derive(Clone, Debug)]
pub struct Classical<A: BooleanAlgebra>(pub A);

impl<A: BooleanAlgebra> Classical<A> {
    /// Wrap a classical algebra.
    pub fn new(algebra: A) -> Self {
        Classical(algebra)
    }
}

impl<A: BooleanAlgebra> RejectSafeAlgebra for Classical<A> {
    type Predicate = A::Predicate;
    type Domain = A::Domain;

    fn true_pred(&self) -> Self::Predicate {
        self.0.true_pred()
    }
    fn false_pred(&self) -> Self::Predicate {
        self.0.false_pred()
    }
    fn and(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate {
        self.0.and(a, b)
    }
    fn or(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate {
        self.0.or(a, b)
    }
    fn pseudo_complement(&self, a: &Self::Predicate) -> Self::Predicate {
        self.0.not(a)
    }
    fn is_satisfiable_3v(&self, a: &Self::Predicate) -> Sat3 {
        Sat3::from_decidable(self.0.is_satisfiable(a))
    }
    fn evaluate(&self, pred: &Self::Predicate, elem: &Self::Domain) -> bool {
        self.0.evaluate(pred, elem)
    }
    fn regularize(&self, a: &Self::Predicate) -> Self::Predicate {
        a.clone() // classical: ¬¬a = a
    }
    fn witness(&self, a: &Self::Predicate) -> Option<Self::Domain> {
        self.0.witness(a)
    }
}

impl<A: BooleanAlgebra> HeytingAlgebra for Classical<A> {
    fn implies(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate {
        // classical material implication ¬a ∨ b
        self.0.or(&self.0.not(a), b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbolic::{IntervalAlgebra, IntervalPred};

    #[test]
    fn sat3_kleene() {
        use Sat3::*;
        assert_eq!(Sat.and(Unsat), Unsat);
        assert_eq!(Sat.and(DontKnow), DontKnow);
        assert_eq!(Sat.and(Sat), Sat);
        assert_eq!(Unsat.or(DontKnow), DontKnow);
        assert_eq!(Sat.or(DontKnow), Sat);
        assert_eq!(DontKnow.not(), DontKnow);
        assert_eq!(Sat.into_safe_bool(), Some(true));
        assert_eq!(DontKnow.into_safe_bool(), None);
    }

    /// A classical algebra lifted into the tower behaves exactly (no DontKnow,
    /// involutive complement, identity regularization).
    #[test]
    fn classical_wrapper_is_exact() {
        let alg = Classical::new(IntervalAlgebra::new(0, 100));
        let p = IntervalPred::Range(10, 20);
        assert_eq!(alg.is_satisfiable_3v(&p), Sat3::Sat);
        assert_eq!(alg.is_satisfiable_3v(&IntervalPred::False), Sat3::Unsat);
        // ¬¬ is the identity classically.
        assert_eq!(alg.regularize(&p), p);
        // pseudo_complement = involutive complement.
        let pc = alg.pseudo_complement(&p);
        assert!(alg.evaluate(&pc, &5));
        assert!(!alg.evaluate(&pc, &15));
        // implies = ¬a ∨ b, with a non-tautological b = [15,100).
        let imp = alg.implies(&p, &IntervalPred::Range(15, 100));
        assert!(alg.evaluate(&imp, &17)); // a true (∈[10,20)), b true (∈[15,100))
        assert!(alg.evaluate(&imp, &5)); // a false at 5 → vacuously true
        assert!(!alg.evaluate(&imp, &12)); // a true (∈[10,20)) but b false (∉[15,100))
    }

    // ── A genuine Heyting-not-Boolean algebra: the 3-element chain ⊥ < M < ⊤ ──
    // (Used to confirm the middle tier admits non-classical algebras: ¬¬M = ⊤ ≠ M,
    //  so it has no involutive complement and cannot be a BooleanAlgebra.)

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
    enum H3 {
        Bot,
        Mid,
        Top,
    }

    #[derive(Clone, Debug)]
    struct Chain3;

    impl RejectSafeAlgebra for Chain3 {
        type Predicate = H3;
        type Domain = H3;
        fn true_pred(&self) -> H3 {
            H3::Top
        }
        fn false_pred(&self) -> H3 {
            H3::Bot
        }
        fn and(&self, a: &H3, b: &H3) -> H3 {
            *a.min(b)
        }
        fn or(&self, a: &H3, b: &H3) -> H3 {
            *a.max(b)
        }
        fn pseudo_complement(&self, a: &H3) -> H3 {
            self.implies(a, &H3::Bot)
        }
        fn is_satisfiable_3v(&self, a: &H3) -> Sat3 {
            // satisfiable iff some d ≤ a, i.e. a > Bot (Bot is satisfied only by Bot,
            // which is "below" — model membership as d ≤ a, so Bot has a witness Bot).
            Sat3::from_decidable(matches!(a, H3::Bot | H3::Mid | H3::Top))
        }
        fn evaluate(&self, pred: &H3, elem: &H3) -> bool {
            elem <= pred
        }
    }

    impl HeytingAlgebra for Chain3 {
        fn implies(&self, a: &H3, b: &H3) -> H3 {
            // relative pseudo-complement in a chain: a→b = ⊤ if a ≤ b, else b.
            if a <= b {
                H3::Top
            } else {
                *b
            }
        }
    }

    #[test]
    fn chain3_is_intuitionistic_not_boolean() {
        let h = Chain3;
        // ¬Mid = Mid→⊥ = ⊥ (since Mid ≰ ⊥).
        assert_eq!(h.pseudo_complement(&H3::Mid), H3::Bot);
        // ¬¬Mid = ¬⊥ = ⊥→⊥ = ⊤  ≠ Mid  → no involutive complement → NOT Boolean.
        assert_eq!(h.regularize(&H3::Mid), H3::Top);
        assert_ne!(h.regularize(&H3::Mid), H3::Mid);
        // Excluded middle fails: Mid ∨ ¬Mid = Mid ∨ ⊥ = Mid ≠ ⊤.
        let em = h.or(&H3::Mid, &h.pseudo_complement(&H3::Mid));
        assert_ne!(em, H3::Top);
        // It is a valid Heyting algebra (adjunction holds on the chain).
        assert_eq!(h.implies(&H3::Mid, &H3::Top), H3::Top);
        assert_eq!(h.implies(&H3::Top, &H3::Mid), H3::Mid);
    }

    /// The safety property at the type level: a function bounded on the classical
    /// `BooleanAlgebra` accepts `IntervalAlgebra` but not the Heyting-only
    /// `Chain3`. (The negative case is a `compile_fail` doctest on the crate;
    /// here we just confirm the positive case and that `Chain3` is usable purely
    /// through the Heyting tier.)
    #[test]
    fn safety_property_positive() {
        fn classical_complement<A: BooleanAlgebra>(alg: &A, p: &A::Predicate) -> A::Predicate {
            alg.not(p)
        }
        let ia = IntervalAlgebra::new(0, 10);
        let _ = classical_complement(&ia, &IntervalPred::Range(1, 5)); // ✅ Boolean

        // Chain3 is reachable only through the Heyting/RejectSafe tiers:
        fn heyting_neg<A: HeytingAlgebra>(alg: &A, p: &A::Predicate) -> A::Predicate {
            alg.heyting_not(p)
        }
        assert_eq!(heyting_neg(&Chain3, &H3::Mid), H3::Bot);
        // `classical_complement(&Chain3, &H3::Mid)` would NOT compile:
        // `Chain3: BooleanAlgebra` is unsatisfied — the load-bearing guarantee.
    }
}
