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

#[path = "product_nary/lifecycle.rs"]
mod lifecycle;

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

    /// Disjunctive normal form: a list of disjuncts, each a list of
    /// `(field, predicate)` atoms. Negation polarity is propagated directly to
    /// leaves, avoiding an intermediate NNF tree.
    fn to_dnf(&self, p: &NaryProductPred<A::Predicate>) -> Vec<Vec<(usize, A::Predicate)>> {
        enum Task<'pred, P> {
            Visit {
                pred: &'pred NaryProductPred<P>,
                negated: bool,
            },
            And,
            Or,
        }

        let mut tasks = vec![Task::Visit { pred: p, negated: false }];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit {
                    pred: NaryProductPred::True,
                    negated: false,
                }
                | Task::Visit {
                    pred: NaryProductPred::False,
                    negated: true,
                } => {
                    values.push(vec![Vec::new()]);
                },
                Task::Visit {
                    pred: NaryProductPred::False,
                    negated: false,
                }
                | Task::Visit {
                    pred: NaryProductPred::True,
                    negated: true,
                } => {
                    values.push(Vec::new());
                },
                Task::Visit {
                    pred: NaryProductPred::Field(index, predicate),
                    negated,
                } => {
                    if *index >= self.fields.len() {
                        values.push(if negated {
                            vec![Vec::new()]
                        } else {
                            Vec::new()
                        });
                    } else {
                        let predicate = if negated {
                            self.fields[*index].not(predicate)
                        } else {
                            predicate.clone()
                        };
                        values.push(vec![vec![(*index, predicate)]]);
                    }
                },
                Task::Visit {
                    pred: NaryProductPred::Not(body),
                    negated,
                } => {
                    tasks.push(Task::Visit { pred: body, negated: !negated });
                },
                Task::Visit {
                    pred: NaryProductPred::And(left, right),
                    negated,
                } => {
                    tasks.push(if negated { Task::Or } else { Task::And });
                    tasks.push(Task::Visit { pred: right, negated });
                    tasks.push(Task::Visit { pred: left, negated });
                },
                Task::Visit {
                    pred: NaryProductPred::Or(left, right),
                    negated,
                } => {
                    tasks.push(if negated { Task::And } else { Task::Or });
                    tasks.push(Task::Visit { pred: right, negated });
                    tasks.push(Task::Visit { pred: left, negated });
                },
                Task::And => {
                    let mut right = values
                        .pop()
                        .expect("N-ary product DNF lost right conjunction");
                    let mut left = values
                        .pop()
                        .expect("N-ary product DNF lost left conjunction");
                    if left.is_empty() || right.is_empty() {
                        values.push(Vec::new());
                        continue;
                    }
                    if left.len() == 1 && right.len() == 1 {
                        let mut conjunction = left.pop().expect("singleton left conjunction");
                        let mut right_conjunction =
                            right.pop().expect("singleton right conjunction");
                        conjunction.append(&mut right_conjunction);
                        values.push(vec![conjunction]);
                        continue;
                    }
                    let capacity = left
                        .len()
                        .checked_mul(right.len())
                        .expect("N-ary product DNF exceeds addressable memory");
                    let mut result = Vec::with_capacity(capacity);
                    for left_conjunction in &left {
                        for right_conjunction in &right {
                            let mut conjunction = Vec::with_capacity(
                                left_conjunction.len() + right_conjunction.len(),
                            );
                            conjunction.extend(left_conjunction.iter().cloned());
                            conjunction.extend(right_conjunction.iter().cloned());
                            result.push(conjunction);
                        }
                    }
                    values.push(result);
                },
                Task::Or => {
                    let mut right = values
                        .pop()
                        .expect("N-ary product DNF lost right disjunction");
                    let mut left = values
                        .pop()
                        .expect("N-ary product DNF lost left disjunction");
                    left.append(&mut right);
                    values.push(left);
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("N-ary product DNF produced no value")
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
        for disjunct in self.to_dnf(a) {
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
        for disjunct in self.to_dnf(a) {
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
        enum Task<'pred, P> {
            Visit(&'pred NaryProductPred<P>),
            Not,
            AndRight(&'pred NaryProductPred<P>),
            OrRight(&'pred NaryProductPred<P>),
        }

        let mut tasks = vec![Task::Visit(pred)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(NaryProductPred::True) => values.push(true),
                Task::Visit(NaryProductPred::False) => values.push(false),
                Task::Visit(NaryProductPred::Field(index, predicate)) => {
                    values.push(match (self.fields.get(*index), elem.get(*index)) {
                        (Some(field), Some(value)) => field.evaluate(predicate, value),
                        _ => false,
                    })
                },
                Task::Visit(NaryProductPred::Not(body)) => {
                    tasks.push(Task::Not);
                    tasks.push(Task::Visit(body));
                },
                Task::Visit(NaryProductPred::And(left, right)) => {
                    tasks.push(Task::AndRight(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(NaryProductPred::Or(left, right)) => {
                    tasks.push(Task::OrRight(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Not => {
                    let value = values
                        .pop()
                        .expect("N-ary product evaluation lost negated value");
                    values.push(!value);
                },
                Task::AndRight(right) => {
                    let left = values
                        .pop()
                        .expect("N-ary product evaluation lost left value");
                    if left {
                        tasks.push(Task::Visit(right));
                    } else {
                        values.push(false);
                    }
                },
                Task::OrRight(right) => {
                    let left = values
                        .pop()
                        .expect("N-ary product evaluation lost left value");
                    if left {
                        values.push(true);
                    } else {
                        tasks.push(Task::Visit(right));
                    }
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values
            .pop()
            .expect("N-ary product evaluation produced no value")
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
        enum Task<'pred, P> {
            Visit(&'pred SumPred<P>),
            And,
            Or,
            Not,
        }

        let mut tasks = vec![Task::Visit(p)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(SumPred::True) => values.push(alg.true_pred()),
                Task::Visit(SumPred::False) => values.push(alg.false_pred()),
                Task::Visit(SumPred::InVariant(index, predicate)) => {
                    values.push(if *index == tag {
                        predicate.clone()
                    } else {
                        alg.false_pred()
                    })
                },
                Task::Visit(SumPred::TagIs(index)) => values.push(if *index == tag {
                    alg.true_pred()
                } else {
                    alg.false_pred()
                }),
                Task::Visit(SumPred::And(left, right)) => {
                    tasks.push(Task::And);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(SumPred::Or(left, right)) => {
                    tasks.push(Task::Or);
                    tasks.push(Task::Visit(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(SumPred::Not(body)) => {
                    tasks.push(Task::Not);
                    tasks.push(Task::Visit(body));
                },
                Task::And => {
                    let right = values.pop().expect("sum projection lost right conjunction");
                    let left = values.pop().expect("sum projection lost left conjunction");
                    values.push(alg.and(&left, &right));
                },
                Task::Or => {
                    let right = values.pop().expect("sum projection lost right disjunction");
                    let left = values.pop().expect("sum projection lost left disjunction");
                    values.push(alg.or(&left, &right));
                },
                Task::Not => {
                    let body = values.pop().expect("sum projection lost negated body");
                    values.push(alg.not(&body));
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("sum projection produced no predicate")
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
        enum Task<'pred, P> {
            Visit(&'pred SumPred<P>),
            Not,
            AndRight(&'pred SumPred<P>),
            OrRight(&'pred SumPred<P>),
        }

        let mut tasks = vec![Task::Visit(pred)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(SumPred::True) => values.push(true),
                Task::Visit(SumPred::False) => values.push(false),
                Task::Visit(SumPred::InVariant(index, predicate)) => values.push(
                    *index == elem.tag
                        && self
                            .variants
                            .get(elem.tag)
                            .is_some_and(|alg| alg.evaluate(predicate, &elem.payload)),
                ),
                Task::Visit(SumPred::TagIs(index)) => values.push(*index == elem.tag),
                Task::Visit(SumPred::Not(body)) => {
                    tasks.push(Task::Not);
                    tasks.push(Task::Visit(body));
                },
                Task::Visit(SumPred::And(left, right)) => {
                    tasks.push(Task::AndRight(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Visit(SumPred::Or(left, right)) => {
                    tasks.push(Task::OrRight(right));
                    tasks.push(Task::Visit(left));
                },
                Task::Not => {
                    let value = values.pop().expect("sum evaluation lost negated value");
                    values.push(!value);
                },
                Task::AndRight(right) => {
                    let left = values.pop().expect("sum evaluation lost left conjunction");
                    if left {
                        tasks.push(Task::Visit(right));
                    } else {
                        values.push(false);
                    }
                },
                Task::OrRight(right) => {
                    let left = values.pop().expect("sum evaluation lost left disjunction");
                    if left {
                        values.push(true);
                    } else {
                        tasks.push(Task::Visit(right));
                    }
                },
            }
        }
        debug_assert_eq!(values.len(), 1);
        values.pop().expect("sum evaluation produced no value")
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
