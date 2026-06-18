//! N-ary product and sum (coproduct) effective Boolean algebras — the
//! combinators that close the algebra family over the *structured* type
//! constructors:
//!
//! - [`NaryProductAlgebra`] — tuples / records: a value is a fixed-arity tuple
//!   `(x_0, …, x_{k-1})`, each component drawn from its own field algebra. The
//!   fields are **independent** (no shared variable), so satisfiability factors
//!   per field. Generalizes the 2-ary
//!   [`ProductAlgebra`](crate::symbolic::ProductAlgebra).
//! - [`SumAlgebra`] — variants / enums / grammar alternation: a value is a
//!   tagged payload `(tag, payload)`, the payload drawn from variant `tag`'s
//!   algebra.
//!
//! Both are generic over the element algebra `A: BooleanAlgebra`. Instantiating
//! at `A = AnyAlgebra` (the uniform recursive carrier) gives heterogeneous
//! tuples/variants (each field/variant a different sort). The predicate types
//! are parameterized by the *inner predicate type* `P = A::Predicate` rather
//! than `A`, so `derive(Eq, Hash)` works without spurious `A: Eq` bounds.

use crate::symbolic::BooleanAlgebra;

// ══════════════════════════════════════════════════════════════════════════════
// N-ary product (tuples / records)
// ══════════════════════════════════════════════════════════════════════════════

/// A predicate over a tuple whose components have inner-predicate type `P`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum NaryProductPred<P> {
    /// Satisfied by every tuple.
    True,
    /// Satisfied by no tuple.
    False,
    /// Component `i` satisfies the inner predicate.
    Field(usize, P),
    /// Conjunction.
    And(Box<NaryProductPred<P>>, Box<NaryProductPred<P>>),
    /// Disjunction.
    Or(Box<NaryProductPred<P>>, Box<NaryProductPred<P>>),
    /// Negation.
    Not(Box<NaryProductPred<P>>),
}

/// The effective Boolean algebra of fixed-arity tuples with independent fields.
#[derive(Clone, Debug)]
pub struct NaryProductAlgebra<A: BooleanAlgebra> {
    /// One algebra per tuple position; `fields.len()` is the arity.
    pub fields: Vec<A>,
}

impl<A: BooleanAlgebra> NaryProductAlgebra<A> {
    /// Construct an algebra over tuples of the given field algebras.
    pub fn new(fields: Vec<A>) -> Self {
        NaryProductAlgebra { fields }
    }

    /// The tuple arity.
    pub fn arity(&self) -> usize {
        self.fields.len()
    }

    /// Negation-normal form: push `Not` down to the field leaves using each
    /// field algebra's `not`. Out-of-range field indices are treated as the
    /// unsatisfiable atom (so a positive occurrence is `False`, a negated one is
    /// `True`).
    fn nnf(
        &self,
        p: &NaryProductPred<A::Predicate>,
        negate: bool,
    ) -> NaryProductPred<A::Predicate> {
        use NaryProductPred::*;
        match p {
            True => {
                if negate {
                    False
                } else {
                    True
                }
            },
            False => {
                if negate {
                    True
                } else {
                    False
                }
            },
            Field(i, pi) => {
                if *i >= self.fields.len() {
                    return if negate { True } else { False };
                }
                if negate {
                    Field(*i, self.fields[*i].not(pi))
                } else {
                    Field(*i, pi.clone())
                }
            },
            And(a, b) => {
                if negate {
                    Or(Box::new(self.nnf(a, true)), Box::new(self.nnf(b, true)))
                } else {
                    And(Box::new(self.nnf(a, false)), Box::new(self.nnf(b, false)))
                }
            },
            Or(a, b) => {
                if negate {
                    And(Box::new(self.nnf(a, true)), Box::new(self.nnf(b, true)))
                } else {
                    Or(Box::new(self.nnf(a, false)), Box::new(self.nnf(b, false)))
                }
            },
            Not(x) => self.nnf(x, !negate),
        }
    }

    /// Disjunctive normal form over a `Not`-free predicate: a list of disjuncts,
    /// each a list of `(field, predicate)` atoms.
    fn to_dnf(&self, p: &NaryProductPred<A::Predicate>) -> Vec<Vec<(usize, A::Predicate)>> {
        use NaryProductPred::*;
        match p {
            True => vec![Vec::new()], // one disjunct, no constraints
            False => Vec::new(),      // no disjuncts
            Field(i, pi) => vec![vec![(*i, pi.clone())]],
            Or(a, b) => {
                let mut out = self.to_dnf(a);
                out.extend(self.to_dnf(b));
                out
            },
            And(a, b) => {
                let da = self.to_dnf(a);
                let db = self.to_dnf(b);
                let mut out = Vec::with_capacity(da.len() * db.len());
                for ca in &da {
                    for cb in &db {
                        let mut conj = ca.clone();
                        conj.extend(cb.iter().cloned());
                        out.push(conj);
                    }
                }
                out
            },
            Not(_) => unreachable!("to_dnf expects NNF (no Not)"),
        }
    }

    /// Collapse a disjunct's atoms into a per-field conjoined predicate
    /// (`None` for unconstrained fields). Returns `None` if any field is
    /// unsatisfiable (so the whole disjunct is unsatisfiable).
    fn field_constraints(
        &self,
        disjunct: &[(usize, A::Predicate)],
    ) -> Option<Vec<Option<A::Predicate>>> {
        let mut acc: Vec<Option<A::Predicate>> = vec![None; self.fields.len()];
        for (i, pi) in disjunct {
            if *i >= self.fields.len() {
                return None; // out-of-range atom never holds
            }
            acc[*i] = Some(match acc[*i].take() {
                Some(prev) => self.fields[*i].and(&prev, pi),
                None => pi.clone(),
            });
        }
        Some(acc)
    }
}

impl<A: BooleanAlgebra> BooleanAlgebra for NaryProductAlgebra<A> {
    type Predicate = NaryProductPred<A::Predicate>;
    type Domain = Vec<A::Domain>;

    fn true_pred(&self) -> Self::Predicate {
        NaryProductPred::True
    }

    fn false_pred(&self) -> Self::Predicate {
        NaryProductPred::False
    }

    fn and(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate {
        match (a, b) {
            (NaryProductPred::False, _) | (_, NaryProductPred::False) => NaryProductPred::False,
            (NaryProductPred::True, x) | (x, NaryProductPred::True) => x.clone(),
            _ => NaryProductPred::And(Box::new(a.clone()), Box::new(b.clone())),
        }
    }

    fn or(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate {
        match (a, b) {
            (NaryProductPred::True, _) | (_, NaryProductPred::True) => NaryProductPred::True,
            (NaryProductPred::False, x) | (x, NaryProductPred::False) => x.clone(),
            _ => NaryProductPred::Or(Box::new(a.clone()), Box::new(b.clone())),
        }
    }

    fn not(&self, a: &Self::Predicate) -> Self::Predicate {
        NaryProductPred::Not(Box::new(a.clone()))
    }

    fn is_satisfiable(&self, a: &Self::Predicate) -> bool {
        let nnf = self.nnf(a, false);
        for disjunct in self.to_dnf(&nnf) {
            if let Some(constraints) = self.field_constraints(&disjunct) {
                let all_sat = constraints.iter().enumerate().all(|(i, c)| match c {
                    Some(pred) => self.fields[i].is_satisfiable(pred),
                    None => true, // unconstrained field — satisfiable if its domain is nonempty
                });
                // An unconstrained field needs a witness of its universe; if the
                // field's domain is empty the tuple is unsatisfiable. Check via
                // true_pred satisfiability.
                let universe_ok = constraints.iter().enumerate().all(|(i, c)| {
                    c.is_some() || self.fields[i].is_satisfiable(&self.fields[i].true_pred())
                });
                if all_sat && universe_ok {
                    return true;
                }
            }
        }
        false
    }

    fn witness(&self, a: &Self::Predicate) -> Option<Self::Domain> {
        let nnf = self.nnf(a, false);
        for disjunct in self.to_dnf(&nnf) {
            let Some(constraints) = self.field_constraints(&disjunct) else {
                continue;
            };
            let mut tuple = Vec::with_capacity(self.fields.len());
            let mut ok = true;
            for (i, c) in constraints.iter().enumerate() {
                let pred = match c {
                    Some(pred) => pred.clone(),
                    None => self.fields[i].true_pred(),
                };
                match self.fields[i].witness(&pred) {
                    Some(v) => tuple.push(v),
                    None => {
                        ok = false;
                        break;
                    },
                }
            }
            if ok {
                return Some(tuple);
            }
        }
        None
    }

    fn evaluate(&self, pred: &Self::Predicate, elem: &Self::Domain) -> bool {
        match pred {
            NaryProductPred::True => true,
            NaryProductPred::False => false,
            NaryProductPred::Field(i, pi) => match (self.fields.get(*i), elem.get(*i)) {
                (Some(field), Some(value)) => field.evaluate(pi, value),
                _ => false,
            },
            NaryProductPred::And(a, b) => self.evaluate(a, elem) && self.evaluate(b, elem),
            NaryProductPred::Or(a, b) => self.evaluate(a, elem) || self.evaluate(b, elem),
            NaryProductPred::Not(x) => !self.evaluate(x, elem),
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════
// Sum (coproduct / variants)
// ══════════════════════════════════════════════════════════════════════════════

/// A tagged value: variant `tag`, carrying `payload` of variant `tag`'s domain.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SumValue<D> {
    /// Which variant.
    pub tag: usize,
    /// The variant's payload.
    pub payload: D,
}

/// A predicate over a tagged value.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SumPred<P> {
    /// Satisfied by every value.
    True,
    /// Satisfied by no value.
    False,
    /// `tag == i` and the payload satisfies the inner predicate.
    InVariant(usize, P),
    /// `tag == i` (payload unconstrained).
    TagIs(usize),
    /// Conjunction.
    And(Box<SumPred<P>>, Box<SumPred<P>>),
    /// Disjunction.
    Or(Box<SumPred<P>>, Box<SumPred<P>>),
    /// Negation.
    Not(Box<SumPred<P>>),
}

/// The effective Boolean algebra of tagged unions.
#[derive(Clone, Debug)]
pub struct SumAlgebra<A: BooleanAlgebra> {
    /// One algebra per variant; `variants.len()` is the number of tags.
    pub variants: Vec<A>,
}

impl<A: BooleanAlgebra> SumAlgebra<A> {
    /// Construct an algebra over a tagged union of the given variant algebras.
    pub fn new(variants: Vec<A>) -> Self {
        SumAlgebra { variants }
    }

    /// The number of variants.
    pub fn num_variants(&self) -> usize {
        self.variants.len()
    }

    /// Project a predicate onto variant `tag`, yielding an inner predicate for
    /// `variants[tag]`. (Mirrors the per-sort fold of the many-sorted carrier.)
    fn project(&self, p: &SumPred<A::Predicate>, tag: usize) -> A::Predicate {
        let alg = &self.variants[tag];
        match p {
            SumPred::True => alg.true_pred(),
            SumPred::False => alg.false_pred(),
            SumPred::InVariant(i, pi) => {
                if *i == tag {
                    pi.clone()
                } else {
                    alg.false_pred()
                }
            },
            SumPred::TagIs(i) => {
                if *i == tag {
                    alg.true_pred()
                } else {
                    alg.false_pred()
                }
            },
            SumPred::And(a, b) => alg.and(&self.project(a, tag), &self.project(b, tag)),
            SumPred::Or(a, b) => alg.or(&self.project(a, tag), &self.project(b, tag)),
            SumPred::Not(x) => alg.not(&self.project(x, tag)),
        }
    }
}

impl<A: BooleanAlgebra> BooleanAlgebra for SumAlgebra<A> {
    type Predicate = SumPred<A::Predicate>;
    type Domain = SumValue<A::Domain>;

    fn true_pred(&self) -> Self::Predicate {
        SumPred::True
    }

    fn false_pred(&self) -> Self::Predicate {
        SumPred::False
    }

    fn and(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate {
        match (a, b) {
            (SumPred::False, _) | (_, SumPred::False) => SumPred::False,
            (SumPred::True, x) | (x, SumPred::True) => x.clone(),
            _ => SumPred::And(Box::new(a.clone()), Box::new(b.clone())),
        }
    }

    fn or(&self, a: &Self::Predicate, b: &Self::Predicate) -> Self::Predicate {
        match (a, b) {
            (SumPred::True, _) | (_, SumPred::True) => SumPred::True,
            (SumPred::False, x) | (x, SumPred::False) => x.clone(),
            _ => SumPred::Or(Box::new(a.clone()), Box::new(b.clone())),
        }
    }

    fn not(&self, a: &Self::Predicate) -> Self::Predicate {
        SumPred::Not(Box::new(a.clone()))
    }

    fn is_satisfiable(&self, a: &Self::Predicate) -> bool {
        (0..self.variants.len()).any(|tag| {
            let projected = self.project(a, tag);
            self.variants[tag].is_satisfiable(&projected)
        })
    }

    fn witness(&self, a: &Self::Predicate) -> Option<Self::Domain> {
        for tag in 0..self.variants.len() {
            let projected = self.project(a, tag);
            if let Some(payload) = self.variants[tag].witness(&projected) {
                return Some(SumValue { tag, payload });
            }
        }
        None
    }

    fn evaluate(&self, pred: &Self::Predicate, elem: &Self::Domain) -> bool {
        match pred {
            SumPred::True => true,
            SumPred::False => false,
            SumPred::InVariant(i, pi) => {
                *i == elem.tag
                    && self
                        .variants
                        .get(elem.tag)
                        .is_some_and(|alg| alg.evaluate(pi, &elem.payload))
            },
            SumPred::TagIs(i) => *i == elem.tag,
            SumPred::And(a, b) => self.evaluate(a, elem) && self.evaluate(b, elem),
            SumPred::Or(a, b) => self.evaluate(a, elem) || self.evaluate(b, elem),
            SumPred::Not(x) => !self.evaluate(x, elem),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbolic::{IntervalAlgebra, IntervalPred};

    fn field(lo: i64, hi: i64) -> NaryProductPred<IntervalPred> {
        NaryProductPred::Field(0, IntervalPred::Range(lo, hi))
    }

    #[test]
    fn product_independent_fields() {
        let alg = NaryProductAlgebra::new(vec![
            IntervalAlgebra::new(0, 100),
            IntervalAlgebra::new(0, 100),
        ]);
        // component 0 in [10,50) AND component 1 in [30,70)
        let p = alg.and(
            &NaryProductPred::Field(0, IntervalPred::Range(10, 50)),
            &NaryProductPred::Field(1, IntervalPred::Range(30, 70)),
        );
        assert!(alg.is_satisfiable(&p));
        assert!(alg.evaluate(&p, &vec![20, 40]));
        assert!(!alg.evaluate(&p, &vec![20, 10])); // field 1 fails
        assert!(!alg.evaluate(&p, &vec![5, 40])); // field 0 fails
        let w = alg.witness(&p).expect("nonempty");
        assert!(alg.evaluate(&p, &w));
        assert_eq!(w.len(), 2);
    }

    #[test]
    fn product_negation_distributes_into_fields() {
        let alg = NaryProductAlgebra::new(vec![IntervalAlgebra::new(0, 100)]);
        let p = field(10, 20);
        let np = alg.not(&p);
        assert!(!alg.evaluate(&np, &vec![15]));
        assert!(alg.evaluate(&np, &vec![5]));
        assert!(alg.evaluate(&np, &vec![25]));
        // p ∧ ¬p unsat
        assert!(!alg.is_satisfiable(&alg.and(&p, &np)));
    }

    #[test]
    fn product_arity_mismatch_rejected() {
        let alg = NaryProductAlgebra::new(vec![
            IntervalAlgebra::new(0, 100),
            IntervalAlgebra::new(0, 100),
        ]);
        // A tuple shorter than a referenced field position is not satisfied.
        let p = NaryProductPred::Field(1, IntervalPred::True);
        assert!(alg.evaluate(&p, &vec![5, 7])); // component 1 present
        assert!(!alg.evaluate(&p, &vec![5])); // no component 1 → false
                                              // out-of-range field reference is never satisfied
        let oob = NaryProductPred::Field(5, IntervalPred::True);
        assert!(!alg.is_satisfiable(&oob));
        assert!(!alg.evaluate(&oob, &vec![1, 2]));
    }

    #[test]
    fn sum_per_variant_projection() {
        let alg = SumAlgebra::new(vec![IntervalAlgebra::new(0, 100), IntervalAlgebra::new(0, 100)]);
        // variant 0 with payload in [10,20), OR variant 1 (any payload)
        let p = alg.or(&SumPred::InVariant(0, IntervalPred::Range(10, 20)), &SumPred::TagIs(1));
        assert!(alg.is_satisfiable(&p));
        assert!(alg.evaluate(&p, &SumValue { tag: 0, payload: 15 }));
        assert!(!alg.evaluate(&p, &SumValue { tag: 0, payload: 25 }));
        assert!(alg.evaluate(&p, &SumValue { tag: 1, payload: 99 }));
        let w = alg.witness(&p).expect("nonempty");
        assert!(alg.evaluate(&p, &w));
    }

    #[test]
    fn sum_unsatisfiable_variant() {
        let alg = SumAlgebra::new(vec![IntervalAlgebra::new(0, 100)]);
        // variant 0 payload in empty range → unsat
        let p = SumPred::InVariant(0, IntervalPred::Range(50, 50));
        assert!(!alg.is_satisfiable(&p));
        // reference to a nonexistent tag → unsat
        let p2 = SumPred::TagIs(7);
        assert!(!alg.is_satisfiable(&p2));
    }

    #[test]
    fn sum_negation() {
        let alg = SumAlgebra::new(vec![IntervalAlgebra::new(0, 100), IntervalAlgebra::new(0, 100)]);
        let tag0 = SumPred::TagIs(0);
        let not_tag0 = alg.not(&tag0);
        // not-tag0 is satisfiable (variant 1 witnesses it).
        assert!(alg.is_satisfiable(&not_tag0));
        assert!(alg.evaluate(&not_tag0, &SumValue { tag: 1, payload: 5 }));
        assert!(!alg.evaluate(&not_tag0, &SumValue { tag: 0, payload: 5 }));
        // tag0 ∧ ¬tag0 unsat
        assert!(!alg.is_satisfiable(&alg.and(&tag0, &not_tag0)));
    }
}
