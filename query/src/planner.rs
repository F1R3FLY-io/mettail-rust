//! Planner: Query AST → execution Plan (scan, join, filter, difference, project).

use crate::ast::{BodyAtom, CompareOp, IfExpr, Term};
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct Plan {
    pub steps: Vec<Step>,
    pub projection: Vec<usize>,
}

#[derive(Debug, Clone)]
pub enum Step {
    Scan { relation: String },
    Join {
        relation: String,
        left_indices: Vec<usize>,
        right_indices: Vec<usize>,
    },
    Filter { condition: FilterOp },
    Difference {
        relation: String,
        join_indices: Vec<(usize, usize)>,
    },
}

#[derive(Debug, Clone)]
pub enum TermRef {
    Col(usize),
    Const(String),
}

#[derive(Debug, Clone)]
pub enum FilterOp {
    Compare {
        left: TermRef,
        op: CompareOp,
        right: TermRef,
    },
}

#[derive(Debug)]
pub enum PlanError {
    NoPositiveAtoms,
    UnboundVariable { name: String },
    InvalidNegation { message: String },
    InvalidComparison { message: String },
}

impl std::fmt::Display for PlanError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PlanError::NoPositiveAtoms => write!(f, "Query must have at least one positive atom"),
            PlanError::UnboundVariable { name } => {
                write!(f, "Variable '{}' used before being bound", name)
            }
            PlanError::InvalidNegation { message } => write!(f, "Invalid negation: {}", message),
            PlanError::InvalidComparison { message } => {
                write!(f, "Invalid comparison: {}", message)
            }
        }
    }
}

impl std::error::Error for PlanError {}

pub type PlanResult<T> = Result<T, PlanError>;

pub struct Planner {
    bindings: HashMap<String, usize>,
    next_col: usize,
    steps: Vec<Step>,
}

impl Planner {
    pub fn new() -> Self {
        Planner {
            bindings: HashMap::new(),
            next_col: 0,
            steps: Vec::new(),
        }
    }

    pub fn plan(query: &crate::ast::Query) -> PlanResult<Plan> {
        let mut planner = Planner::new();
        let mut positive_atoms = Vec::new();
        let mut negations = Vec::new();
        let mut if_clauses = Vec::new();

        for atom in &query.body {
            match atom {
                BodyAtom::Relation { .. } => positive_atoms.push(atom.clone()),
                BodyAtom::Negation(_) => negations.push(atom.clone()),
                BodyAtom::If(expr) => if_clauses.push(expr.clone()),
            }
        }

        if positive_atoms.is_empty() {
            return Err(PlanError::NoPositiveAtoms);
        }

        planner.plan_scan(&positive_atoms[0])?;
        for atom in &positive_atoms[1..] {
            planner.plan_join(atom)?;
        }
        for expr in &if_clauses {
            planner.plan_if_clause(expr)?;
        }
        for neg in &negations {
            planner.plan_negation(neg)?;
        }
        let projection = planner.compute_projection(&query.head)?;
        Ok(Plan {
            steps: planner.steps,
            projection,
        })
    }

    fn plan_scan(&mut self, atom: &BodyAtom) -> PlanResult<()> {
        let BodyAtom::Relation { name, terms } = atom else {
            unreachable!();
        };
        for term in terms {
            match term {
                Term::Variable(var) => {
                    if !self.bindings.contains_key(&var.name) {
                        self.bindings.insert(var.name.clone(), self.next_col);
                        self.next_col += 1;
                    }
                }
                Term::Constant(_) | Term::Wildcard => {
                    self.next_col += 1;
                }
            }
        }
        self.steps.push(Step::Scan {
            relation: name.clone(),
        });
        Ok(())
    }

    fn plan_join(&mut self, atom: &BodyAtom) -> PlanResult<()> {
        let BodyAtom::Relation { name, terms } = atom else {
            unreachable!();
        };
        let mut left_indices = Vec::new();
        let mut right_indices = Vec::new();
        let old_num_cols = self.bindings.values().max().map(|&v| v + 1).unwrap_or(0);

        for (right_idx, term) in terms.iter().enumerate() {
            match term {
                Term::Variable(var) => {
                    if let Some(&left_idx) = self.bindings.get(&var.name) {
                        left_indices.push(left_idx);
                        right_indices.push(right_idx);
                    } else {
                        self.bindings.insert(var.name.clone(), self.next_col);
                        self.next_col += 1;
                    }
                }
                Term::Constant(_) | Term::Wildcard => {
                    self.next_col += 1;
                }
            }
        }
        let num_join_keys = left_indices.len();

        let mut old_to_new = HashMap::new();
        for (new_pos, &old_pos) in left_indices.iter().enumerate() {
            old_to_new.insert(old_pos, new_pos);
        }
        let mut next_non_key = num_join_keys;
        for old_pos in 0..old_num_cols {
            if !old_to_new.contains_key(&old_pos) {
                old_to_new.insert(old_pos, next_non_key);
                next_non_key += 1;
            }
        }
        for col in self.bindings.values_mut() {
            if let Some(&new_idx) = old_to_new.get(col) {
                *col = new_idx;
            }
        }

        self.steps.push(Step::Join {
            relation: name.clone(),
            left_indices,
            right_indices,
        });
        Ok(())
    }

    fn plan_if_clause(&mut self, expr: &IfExpr) -> PlanResult<()> {
        let filter_op = match expr {
            IfExpr::Compare { left, op, right } => self.plan_comparison(left, *op, right)?,
            IfExpr::Call { .. } => {
                return Err(PlanError::InvalidComparison {
                    message: "Predicate calls in if not yet supported".into(),
                });
            }
        };
        self.steps.push(Step::Filter {
            condition: filter_op,
        });
        Ok(())
    }

    fn term_to_ref(&self, term: &Term) -> PlanResult<TermRef> {
        match term {
            Term::Variable(var) => {
                let col = *self.bindings.get(&var.name).ok_or_else(|| {
                    PlanError::UnboundVariable {
                        name: var.name.clone(),
                    }
                })?;
                Ok(TermRef::Col(col))
            }
            Term::Constant(s) => Ok(TermRef::Const(s.clone())),
            Term::Wildcard => Err(PlanError::InvalidComparison {
                message: "Wildcard in comparison not supported".into(),
            }),
        }
    }

    fn plan_comparison(
        &self,
        left: &Term,
        op: CompareOp,
        right: &Term,
    ) -> PlanResult<FilterOp> {
        if matches!((left, right), (Term::Constant(_), Term::Constant(_))) {
            return Err(PlanError::InvalidComparison {
                message: "Constant-constant comparison not supported".into(),
            });
        }
        Ok(FilterOp::Compare {
            left: self.term_to_ref(left)?,
            op,
            right: self.term_to_ref(right)?,
        })
    }

    fn plan_negation(&mut self, atom: &BodyAtom) -> PlanResult<()> {
        let BodyAtom::Negation(inner) = atom else {
            unreachable!();
        };
        let BodyAtom::Relation { name, terms } = inner.as_ref() else {
            return Err(PlanError::InvalidNegation {
                message: "Can only negate relations".into(),
            });
        };
        let mut join_indices = Vec::new();
        for (right_idx, term) in terms.iter().enumerate() {
            if let Term::Variable(var) = term {
                if let Some(&left_idx) = self.bindings.get(&var.name) {
                    join_indices.push((left_idx, right_idx));
                }
            }
        }
        self.steps.push(Step::Difference {
            relation: name.clone(),
            join_indices,
        });
        Ok(())
    }

    fn compute_projection(&self, head: &crate::ast::Atom) -> PlanResult<Vec<usize>> {
        let mut projection = Vec::new();
        for term in &head.terms {
            let col = match term {
                Term::Variable(var) => *self.bindings.get(&var.name).ok_or_else(|| {
                    PlanError::UnboundVariable {
                        name: var.name.clone(),
                    }
                })?,
                Term::Constant(_) | Term::Wildcard => {
                    return Err(PlanError::UnboundVariable {
                        name: "head must list variables only".into(),
                    });
                }
            };
            projection.push(col);
        }
        Ok(projection)
    }
}
