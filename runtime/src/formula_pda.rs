//! Representation-independent pushdown traversal for spatial-formula facts.
//!
//! Generated languages can have very large syntax modules, but the formula
//! control machine depends on only eight abstract shapes. Keeping that machine
//! here makes the executable and formal-verification boundary the small,
//! production implementation itself. A language adapter supplies:
//!
//! 1. a total classifier from its generated term type to [`FormulaShape`]; and
//! 2. the positive-only host verdict for an ordinary term-pattern leaf.
//!
//! The machine performs one post-order traversal. `Visit` instructions expose
//! children, while `Build` instructions combine their facts. Both instruction
//! and value stacks live on the heap, so native-stack use is constant in the
//! formula depth. Results are memoized by the address of each borrowed node;
//! addresses are cache keys only and never become semantic identity.

use std::collections::HashMap;

/// The representation-independent formula reading of a generated term node.
#[derive(Debug)]
pub enum FormulaShape<'formula, Term> {
    /// Logical truth.
    Verum,
    /// Logical falsehood.
    Falsum,
    /// Ordinary conjunction over the whole target term.
    Conjunction(&'formula Term, &'formula Term),
    /// Ordinary disjunction.
    Disjunction(&'formula Term, &'formula Term),
    /// Logical negation.
    Negation(&'formula Term),
    /// Logical implication.
    Implication(&'formula Term, &'formula Term),
    /// Separating conjunction over an arbitrary number of parts.
    Separation(Vec<&'formula Term>),
    /// A representation-specific term pattern.
    Term,
}

/// Conservative syntactic truth facts for one formula.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct StaticFacts {
    /// No target can satisfy this formula by the syntactic rules.
    pub is_false: bool,
    /// Every target satisfies this formula by the syntactic rules.
    pub is_true: bool,
}

/// All facts produced for one formula node in the shared traversal.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FormulaFacts {
    /// Conservative truth/falsehood facts.
    pub static_facts: StaticFacts,
    /// Strong-Kleene host verdict; `None` means that the host declines.
    pub host_verdict: Option<bool>,
}

#[derive(Clone, Copy)]
enum Build {
    Conjunction,
    Disjunction,
    Negation,
    Implication,
    Separation(usize),
}

impl Build {
    fn arity(self) -> usize {
        match self {
            Self::Negation => 1,
            Self::Conjunction | Self::Disjunction | Self::Implication => 2,
            Self::Separation(arity) => arity,
        }
    }
}

enum Work<'formula, Term> {
    Visit(&'formula Term),
    Build { key: *const Term, op: Build },
}

/// Analyze static truth and the optional host verdict in one explicit PDA.
///
/// `classify` must be total for `Term`. `term_verdict` is invoked only for a
/// [`FormulaShape::Term`] leaf; it may lazily canonicalize a target and return a
/// positive-only match result. Passing a closure that always returns `None`
/// computes static facts without performing any host matching.
///
/// # Machine invariant
///
/// Every `Visit` or `Build` produces exactly one [`FormulaFacts`] value. A
/// `Build` consumes its declared arity and produces one replacement, so a
/// successful traversal ends with exactly one value: the root facts.
pub fn analyze_formula<'formula, Term, Classify, TermVerdict>(
    root: &'formula Term,
    mut classify: Classify,
    mut term_verdict: TermVerdict,
) -> FormulaFacts
where
    Classify: FnMut(&'formula Term) -> FormulaShape<'formula, Term>,
    TermVerdict: FnMut(&'formula Term) -> Option<bool>,
{
    let mut work = vec![Work::Visit(root)];
    let mut values = Vec::<FormulaFacts>::new();
    let mut by_node = HashMap::<*const Term, FormulaFacts>::new();

    while let Some(step) = work.pop() {
        match step {
            Work::Visit(formula) => {
                let key = formula as *const Term;
                if let Some(facts) = by_node.get(&key).copied() {
                    values.push(facts);
                    continue;
                }

                match classify(formula) {
                    FormulaShape::Verum => {
                        let facts = FormulaFacts {
                            static_facts: StaticFacts { is_false: false, is_true: true },
                            host_verdict: Some(true),
                        };
                        by_node.insert(key, facts);
                        values.push(facts);
                    },
                    FormulaShape::Falsum => {
                        let facts = FormulaFacts {
                            static_facts: StaticFacts { is_false: true, is_true: false },
                            host_verdict: Some(false),
                        };
                        by_node.insert(key, facts);
                        values.push(facts);
                    },
                    FormulaShape::Term => {
                        let facts = FormulaFacts {
                            static_facts: StaticFacts::default(),
                            host_verdict: term_verdict(formula),
                        };
                        by_node.insert(key, facts);
                        values.push(facts);
                    },
                    FormulaShape::Conjunction(left, right) => {
                        work.push(Work::Build { key, op: Build::Conjunction });
                        work.push(Work::Visit(right));
                        work.push(Work::Visit(left));
                    },
                    FormulaShape::Disjunction(left, right) => {
                        work.push(Work::Build { key, op: Build::Disjunction });
                        work.push(Work::Visit(right));
                        work.push(Work::Visit(left));
                    },
                    FormulaShape::Negation(inner) => {
                        work.push(Work::Build { key, op: Build::Negation });
                        work.push(Work::Visit(inner));
                    },
                    FormulaShape::Implication(antecedent, consequent) => {
                        work.push(Work::Build { key, op: Build::Implication });
                        work.push(Work::Visit(consequent));
                        work.push(Work::Visit(antecedent));
                    },
                    FormulaShape::Separation(parts) => {
                        work.push(Work::Build { key, op: Build::Separation(parts.len()) });
                        work.extend(parts.into_iter().rev().map(Work::Visit));
                    },
                }
            },
            Work::Build { key, op } => {
                let arity = op.arity();
                let split = values
                    .len()
                    .checked_sub(arity)
                    .expect("formula PDA: continuation underflow");
                let children = values.split_off(split);
                let (static_facts, unsettled_host_verdict) = match op {
                    Build::Conjunction => (
                        StaticFacts {
                            is_false: children[0].static_facts.is_false
                                || children[1].static_facts.is_false,
                            is_true: children[0].static_facts.is_true
                                && children[1].static_facts.is_true,
                        },
                        kleene_and(children[0].host_verdict, children[1].host_verdict),
                    ),
                    Build::Disjunction => (
                        StaticFacts {
                            is_false: children[0].static_facts.is_false
                                && children[1].static_facts.is_false,
                            is_true: children[0].static_facts.is_true
                                || children[1].static_facts.is_true,
                        },
                        kleene_or(children[0].host_verdict, children[1].host_verdict),
                    ),
                    Build::Negation => (
                        StaticFacts {
                            is_false: children[0].static_facts.is_true,
                            is_true: children[0].static_facts.is_false,
                        },
                        children[0].host_verdict.map(|value| !value),
                    ),
                    Build::Implication => (
                        StaticFacts {
                            is_false: children[0].static_facts.is_true
                                && children[1].static_facts.is_false,
                            is_true: children[0].static_facts.is_false
                                || children[1].static_facts.is_true,
                        },
                        kleene_or(
                            children[0].host_verdict.map(|value| !value),
                            children[1].host_verdict,
                        ),
                    ),
                    Build::Separation(_) => (
                        StaticFacts {
                            is_false: children.iter().any(|child| child.static_facts.is_false),
                            is_true: false,
                        },
                        None,
                    ),
                };
                let host_verdict = if static_facts.is_false {
                    Some(false)
                } else if static_facts.is_true {
                    Some(true)
                } else {
                    unsettled_host_verdict
                };
                let facts = FormulaFacts { static_facts, host_verdict };
                by_node.insert(key, facts);
                values.push(facts);
            },
        }
    }

    assert_eq!(values.len(), 1, "formula PDA: the final value stack must contain one result");
    values.pop().expect("formula PDA: missing root result")
}

fn kleene_and(left: Option<bool>, right: Option<bool>) -> Option<bool> {
    match (left, right) {
        (Some(false), _) | (_, Some(false)) => Some(false),
        (Some(true), Some(true)) => Some(true),
        _ => None,
    }
}

fn kleene_or(left: Option<bool>, right: Option<bool>) -> Option<bool> {
    match (left, right) {
        (Some(true), _) | (_, Some(true)) => Some(true),
        (Some(false), Some(false)) => Some(false),
        _ => None,
    }
}
