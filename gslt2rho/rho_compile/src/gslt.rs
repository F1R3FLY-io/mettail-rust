//! Input AST for GSLT specifications.
//!
//! This mirrors the `rewrites { ... }` section of a MeTTaIL `language!`
//! macro invocation. We deliberately keep the AST shallow so that this
//! crate can be tested in isolation; downstream code can construct
//! `Gslt` values from MeTTaIL's own parsed representation via a small
//! adapter.

use std::fmt;

/// A complete GSLT specification, abridged to what the rho compiler needs.
#[derive(Clone, Debug)]
pub struct Gslt {
    /// The function-symbol signature: each constructor with its arity.
    pub signature: Vec<Constructor>,
    /// All rewrite rules, both direct and contextual.
    pub rewrites: Vec<Rewrite>,
}

/// A constructor declaration: a name and an arity.
///
/// We do not track the result type at the rho-compilation layer; the
/// upstream `language!` macro has already verified that all rules are
/// well-typed.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Constructor {
    pub name: String,
    pub arity: usize,
}

/// A rewrite rule.
#[derive(Clone, Debug)]
pub enum Rewrite {
    /// `lhs ~> rhs` --- a non-contextual rule.
    Direct { lhs: Pattern, rhs: Term },
    /// `if S_1 ~> T_1, ..., S_n ~> T_n then K(...) ~> K'(...)` ---
    /// a contextual rule with `n` premises.
    Contextual {
        premises: Vec<Premise>,
        outer_lhs: Pattern,
        outer_rhs: Term,
    },
}

/// A premise of a contextual rule: `var_in ~> var_out`.
///
/// The variables `var_in` and `var_out` appear at exactly one hole position
/// each in `outer_lhs` and `outer_rhs` respectively.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Premise {
    pub var_in: String,
    pub var_out: String,
}

/// A pattern: a tree of constructors, variables, and rest patterns.
///
/// In a contextual rule, the `Var` nodes whose names appear as `var_in` of
/// some premise are the **hole positions** of the outer context.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Pattern {
    /// `(name args ...)`
    Cons { name: String, args: Vec<Pattern> },
    /// A pattern variable (capital letter, e.g. `M`, `N`, or a hole-marker `S`).
    Var(String),
    /// A rest pattern `...rest` matching zero or more sibling patterns.
    Rest(String),
    /// A wildcard `_` matching anything.
    Wild,
}

/// A term: the right-hand side of a rule, possibly with metavariables.
///
/// Terms differ from patterns only in semantic intent (we keep them as a
/// distinct type to make compilation steps clearer). We use the same
/// constructors.
pub type Term = Pattern;

// ---------------------------------------------------------------------------
// Convenience constructors
// ---------------------------------------------------------------------------

impl Pattern {
    pub fn cons(name: &str, args: Vec<Pattern>) -> Self {
        Pattern::Cons { name: name.to_string(), args }
    }
    pub fn var(name: &str) -> Self {
        Pattern::Var(name.to_string())
    }
    pub fn rest(name: &str) -> Self {
        Pattern::Rest(name.to_string())
    }

    /// Head symbol, if this is a `Cons` node.
    pub fn head(&self) -> Option<&str> {
        match self {
            Pattern::Cons { name, .. } => Some(name.as_str()),
            _ => None,
        }
    }

    /// Children, if this is a `Cons` node.
    pub fn children(&self) -> &[Pattern] {
        match self {
            Pattern::Cons { args, .. } => args.as_slice(),
            _ => &[],
        }
    }

    /// Variables (and rest patterns) appearing in this pattern.
    pub fn free_vars(&self) -> Vec<&str> {
        let mut out = Vec::new();
        self.collect_free_vars(&mut out);
        out
    }

    fn collect_free_vars<'a>(&'a self, out: &mut Vec<&'a str>) {
        match self {
            Pattern::Cons { args, .. } => {
                for a in args {
                    a.collect_free_vars(out);
                }
            }
            Pattern::Var(v) | Pattern::Rest(v) => out.push(v.as_str()),
            Pattern::Wild => {}
        }
    }
}

impl fmt::Display for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Pattern::Cons { name, args } => {
                write!(f, "({}", name)?;
                for a in args {
                    write!(f, " {}", a)?;
                }
                write!(f, ")")
            }
            Pattern::Var(v) => write!(f, "{}", v),
            Pattern::Rest(v) => write!(f, "...{}", v),
            Pattern::Wild => write!(f, "_"),
        }
    }
}

impl Rewrite {
    /// All left-hand-side patterns reachable from this rule (the rule's
    /// own LHS for `Direct`; the outer LHS together with each premise's
    /// `var_in` position-pattern for `Contextual`).
    ///
    /// For automaton construction, the relevant set is in fact the union
    /// over all rules of: the principal LHS of `Direct`, and the *inner*
    /// patterns referenced by the premises of `Contextual`. The outer
    /// context contributes only its surface, not a new LHS.
    pub fn principal_lhs(&self) -> Vec<&Pattern> {
        match self {
            Rewrite::Direct { lhs, .. } => vec![lhs],
            // The principal LHSs of a contextual rule are the patterns
            // that the inner premises match against. In the GSLT surface
            // syntax these appear as the var_in's, which are bound to
            // hole positions of the outer LHS. The matchable LHSs are
            // therefore the patterns at those hole positions in the
            // *outer* LHS pattern --- which, by construction of a
            // contextual rule, are precisely the inner patterns.
            //
            // For our compilation, we treat the outer LHS itself as the
            // principal LHS for matching purposes; the inner premises
            // are dispatched via the channel structure.
            Rewrite::Contextual { outer_lhs, .. } => vec![outer_lhs],
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pattern_display() {
        let p = Pattern::cons(
            "PPar",
            vec![
                Pattern::cons("PInput", vec![
                    Pattern::var("n"),
                    Pattern::var("p"),
                ]),
                Pattern::rest("rest"),
            ],
        );
        assert_eq!(format!("{}", p), "(PPar (PInput n p) ...rest)");
    }

    #[test]
    fn free_vars() {
        let p = Pattern::cons("f", vec![
            Pattern::var("x"),
            Pattern::cons("g", vec![Pattern::var("y"), Pattern::var("x")]),
        ]);
        let vs = p.free_vars();
        assert_eq!(vs, vec!["x", "y", "x"]);
    }
}
