//! Query AST – Datalog-style rules with head and body.
//!
//! All term values are strings (query values = stringified terms).

use std::collections::HashSet;

/// A complete Datalog query: head(args) <-- body.
#[derive(Debug, Clone)]
pub struct Query {
    pub head: Atom,
    pub body: Vec<BodyAtom>,
}

/// Head or body atom: relation name and arguments.
#[derive(Debug, Clone)]
pub struct Atom {
    pub relation: String,
    pub terms: Vec<Term>,
}

/// Body atom: relation, negation, or if-clause. (FunctionCall reserved for later.)
#[derive(Debug, Clone)]
pub enum BodyAtom {
    Relation { name: String, terms: Vec<Term> },
    Negation(Box<BodyAtom>),
    If(IfExpr),
}

/// Boolean expression in an `if` clause.
#[derive(Debug, Clone)]
pub enum IfExpr {
    Compare { left: Term, op: CompareOp, right: Term },
    Call { function: String, args: Vec<Term> },
}

/// Comparison operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CompareOp {
    Eq,
    Neq,
    Gt,
    Lt,
    Gte,
    Lte,
}

impl CompareOp {
    pub fn symbol(&self) -> &'static str {
        match self {
            CompareOp::Eq => "==",
            CompareOp::Neq => "!=",
            CompareOp::Gt => ">",
            CompareOp::Lt => "<",
            CompareOp::Gte => ">=",
            CompareOp::Lte => "<=",
        }
    }

    pub fn from_symbol(s: &str) -> Option<Self> {
        match s {
            "==" => Some(CompareOp::Eq),
            "!=" => Some(CompareOp::Neq),
            ">" => Some(CompareOp::Gt),
            "<" => Some(CompareOp::Lt),
            ">=" => Some(CompareOp::Gte),
            "<=" => Some(CompareOp::Lte),
            _ => None,
        }
    }

    /// Evaluate on two string values (lexicographic order for ordering ops).
    pub fn eval_str(&self, left: &str, right: &str) -> bool {
        match self {
            CompareOp::Eq => left == right,
            CompareOp::Neq => left != right,
            CompareOp::Gt => left > right,
            CompareOp::Lt => left < right,
            CompareOp::Gte => left >= right,
            CompareOp::Lte => left <= right,
        }
    }
}

/// A term in an atom: variable, constant (string), or wildcard.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    Variable(Variable),
    Constant(String),
    Wildcard,
}

/// Logical variable (e.g. x, result).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Variable {
    pub name: String,
}

impl Variable {
    pub fn new(name: impl Into<String>) -> Self {
        Variable { name: name.into() }
    }

    pub fn is_valid_name(s: &str) -> bool {
        if s.is_empty() || s == "_" {
            return false;
        }
        let first = s.chars().next().unwrap();
        first.is_lowercase() || first == '_'
    }
}

impl Query {
    pub fn variables(&self) -> Vec<&Variable> {
        let mut vars = Vec::new();
        for t in &self.head.terms {
            if let Term::Variable(v) = t {
                vars.push(v);
            }
        }
        for atom in &self.body {
            vars.extend(atom.variables());
        }
        vars
    }

    /// Safe: every head variable appears in some positive body atom.
    pub fn is_safe(&self) -> Result<(), String> {
        let head_vars: HashSet<_> = self
            .head
            .terms
            .iter()
            .filter_map(|t| match t {
                Term::Variable(v) => Some(v),
                _ => None,
            })
            .collect();
        let mut body_vars = HashSet::new();
        fn collect_positive_vars<'a>(atom: &'a BodyAtom, vars: &mut HashSet<&'a Variable>) {
            match atom {
                BodyAtom::Relation { terms, .. } => {
                    for term in terms {
                        if let Term::Variable(var) = term {
                            vars.insert(var);
                        }
                    }
                },
                BodyAtom::Negation(_) => {},
                BodyAtom::If(_) => {},
            }
        }
        for atom in &self.body {
            collect_positive_vars(atom, &mut body_vars);
        }
        for var in head_vars {
            if !body_vars.contains(var) {
                return Err(format!(
                    "Unsafe query: variable '{}' in head but not in positive body atom",
                    var.name
                ));
            }
        }
        Ok(())
    }

    /// Stratified: head relation does not appear in a negated atom.
    pub fn check_stratification(&self) -> Result<(), String> {
        let mut negated = HashSet::new();
        fn collect_negated<'a>(atom: &'a BodyAtom, set: &mut HashSet<&'a str>) {
            if let BodyAtom::Negation(inner) = atom {
                if let BodyAtom::Relation { name, .. } = inner.as_ref() {
                    set.insert(name.as_str());
                }
            }
        }
        for atom in &self.body {
            collect_negated(atom, &mut negated);
        }
        if negated.contains(self.head.relation.as_str()) {
            return Err(format!(
                "Non-stratified query: '{}' appears in both head and negation",
                self.head.relation
            ));
        }
        Ok(())
    }
}

impl BodyAtom {
    pub fn variables(&self) -> Vec<&Variable> {
        match self {
            BodyAtom::Relation { terms, .. } => terms
                .iter()
                .filter_map(|t| match t {
                    Term::Variable(v) => Some(v),
                    _ => None,
                })
                .collect(),
            BodyAtom::Negation(inner) => inner.variables(),
            BodyAtom::If(expr) => expr.variables(),
        }
    }

    pub fn relation_name(&self) -> Option<&str> {
        match self {
            BodyAtom::Relation { name, .. } => Some(name.as_str()),
            BodyAtom::Negation(inner) => inner.relation_name(),
            BodyAtom::If(_) => None,
        }
    }
}

impl IfExpr {
    pub fn variables(&self) -> Vec<&Variable> {
        match self {
            IfExpr::Compare { left, right, .. } => {
                let mut v = Vec::new();
                if let Term::Variable(x) = left {
                    v.push(x);
                }
                if let Term::Variable(x) = right {
                    v.push(x);
                }
                v
            },
            IfExpr::Call { args, .. } => args
                .iter()
                .filter_map(|t| match t {
                    Term::Variable(v) => Some(v),
                    _ => None,
                })
                .collect(),
        }
    }
}
