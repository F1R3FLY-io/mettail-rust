//! Elaborated presentations, and the lattice operations of D3.
//!
//! # Sharing
//!
//! D3 says `\/` is a join *over the shared parameter*: when two theories
//! descend from a common ancestor, their join must not duplicate what they
//! inherited. The mechanism is an origin token, [`ElemId`], stamped on every
//! element at the point it is introduced and carried unchanged through
//! inheritance.
//!
//! Two elements with the same `ElemId` are the same element, arrived at by two
//! routes, and the join keeps one. Two elements with different `ElemId`s but
//! the same label were introduced independently, and the join reports a
//! collision. `let pm = ParMonoid(cm) in (...)` elaborates `ParMonoid(cm)`
//! exactly once, so every consumer of `pm` sees the identical ids and the
//! pushout falls out.
//!
//! A `Replacements` block rewrites an element *in place*, preserving its
//! `ElemId`, so a replacement performed in a shared ancestor is likewise
//! shared rather than duplicated.

use crate::ast::*;
use crate::diag::{Diag, DiagKind};
use crate::lex::Span;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct ElemId(pub u64);

#[derive(Clone, Debug)]
pub struct CatEntry {
    pub id: ElemId,
    pub cat: Cat,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct TermEntry {
    pub id: ElemId,
    pub rule: TermRule,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct EqEntry {
    pub id: ElemId,
    pub eq: Equation,
}

#[derive(Clone, Debug)]
pub struct RwEntry {
    pub id: ElemId,
    pub rw: RewriteDecl,
}

#[derive(Clone, Debug, Default)]
pub struct Presentation {
    pub types: Vec<CatEntry>,
    /// (internal category, exported name)
    pub exports: Vec<(Cat, Cat)>,
    pub terms: Vec<TermEntry>,
    pub equations: Vec<EqEntry>,
    pub rewrites: Vec<RwEntry>,
}

impl Presentation {
    pub fn empty() -> Presentation {
        Presentation::default()
    }

    pub fn has_cat(&self, c: &str) -> bool {
        self.types.iter().any(|e| e.cat == c)
    }
    pub fn has_label(&self, l: &str) -> bool {
        self.terms.iter().any(|e| e.rule.label == l)
    }
    pub fn term(&self, l: &str) -> Option<&TermEntry> {
        self.terms.iter().find(|e| e.rule.label == l)
    }
    pub fn labels(&self) -> Vec<&str> {
        self.terms.iter().map(|e| e.rule.label.as_str()).collect()
    }

    /// Categories visible to a consumer, under their exported names. A theory
    /// with no `Exports` block exports everything `Types` declares (G1).
    pub fn visible_cats(&self) -> Vec<Cat> {
        if self.exports.is_empty() {
            self.types.iter().map(|e| e.cat.clone()).collect()
        } else {
            self.exports.iter().map(|(_, ext)| ext.clone()).collect()
        }
    }

    // ------------------------------------------------------------- lattice

    /// D3 join: union, identifying elements that share an `ElemId`.
    pub fn join(&self, other: &Presentation, span: Span) -> Result<Presentation, Diag> {
        let mut out = self.clone();

        for c in &other.types {
            match out.types.iter().find(|e| e.cat == c.cat) {
                Some(existing) if existing.id == c.id => {},
                Some(existing) => {
                    return Err(Diag::new(
                        DiagKind::JoinCollision,
                        format!(
                            "cannot join: category `{}` was introduced independently on \
                             both sides (elements {:?} and {:?}); they are distinct \
                             categories that happen to share a name",
                            c.cat, existing.id, c.id
                        ),
                        span,
                    ))
                },
                None => out.types.push(c.clone()),
            }
        }

        for t in &other.terms {
            match out.terms.iter().find(|e| e.id == t.id) {
                Some(existing) => {
                    if !same_rule(&existing.rule, &t.rule) {
                        return Err(Diag::new(
                            DiagKind::JoinCollision,
                            format!(
                                "cannot join: element {:?} was replaced differently on the \
                                 two sides (`{}` versus `{}`)",
                                t.id, existing.rule.label, t.rule.label
                            ),
                            span,
                        ));
                    }
                },
                None => {
                    if let Some(clash) = out.terms.iter().find(|e| e.rule.label == t.rule.label) {
                        return Err(Diag::new(
                            DiagKind::JoinCollision,
                            format!(
                                "cannot join: label `{}` was introduced independently on \
                                 both sides (elements {:?} and {:?})",
                                t.rule.label, clash.id, t.id
                            ),
                            span,
                        ));
                    }
                    out.terms.push(t.clone());
                },
            }
        }

        for e in &other.equations {
            if !out.equations.iter().any(|x| x.id == e.id) {
                out.equations.push(e.clone());
            }
        }
        for r in &other.rewrites {
            if !out.rewrites.iter().any(|x| x.id == r.id) {
                out.rewrites.push(r.clone());
            }
        }
        for ex in &other.exports {
            if !out.exports.contains(ex) {
                out.exports.push(ex.clone());
            }
        }
        Ok(out)
    }

    /// Meet: the common fragment, by origin.
    pub fn meet(&self, other: &Presentation) -> Presentation {
        let keep = |id: ElemId, ids: &[ElemId]| ids.contains(&id);
        let ot: Vec<ElemId> = other.types.iter().map(|e| e.id).collect();
        let om: Vec<ElemId> = other.terms.iter().map(|e| e.id).collect();
        let oe: Vec<ElemId> = other.equations.iter().map(|e| e.id).collect();
        let orw: Vec<ElemId> = other.rewrites.iter().map(|e| e.id).collect();
        Presentation {
            types: self
                .types
                .iter()
                .filter(|e| keep(e.id, &ot))
                .cloned()
                .collect(),
            terms: self
                .terms
                .iter()
                .filter(|e| keep(e.id, &om))
                .cloned()
                .collect(),
            equations: self
                .equations
                .iter()
                .filter(|e| keep(e.id, &oe))
                .cloned()
                .collect(),
            rewrites: self
                .rewrites
                .iter()
                .filter(|e| keep(e.id, &orw))
                .cloned()
                .collect(),
            exports: self
                .exports
                .iter()
                .filter(|x| other.exports.contains(x))
                .cloned()
                .collect(),
        }
    }

    /// Difference: everything in `self` whose origin is not in `other`.
    pub fn diff(&self, other: &Presentation) -> Presentation {
        let ot: Vec<ElemId> = other.types.iter().map(|e| e.id).collect();
        let om: Vec<ElemId> = other.terms.iter().map(|e| e.id).collect();
        let oe: Vec<ElemId> = other.equations.iter().map(|e| e.id).collect();
        let orw: Vec<ElemId> = other.rewrites.iter().map(|e| e.id).collect();
        Presentation {
            types: self
                .types
                .iter()
                .filter(|e| !ot.contains(&e.id))
                .cloned()
                .collect(),
            terms: self
                .terms
                .iter()
                .filter(|e| !om.contains(&e.id))
                .cloned()
                .collect(),
            equations: self
                .equations
                .iter()
                .filter(|e| !oe.contains(&e.id))
                .cloned()
                .collect(),
            rewrites: self
                .rewrites
                .iter()
                .filter(|e| !orw.contains(&e.id))
                .cloned()
                .collect(),
            exports: self
                .exports
                .iter()
                .filter(|x| !other.exports.contains(x))
                .cloned()
                .collect(),
        }
    }

    // ------------------------------------------------------------ rendering

    pub fn render(&self) -> String {
        let mut s = String::new();
        s.push_str("Presentation\n");
        s.push_str("  Types {");
        for t in &self.types {
            s.push_str(&format!(" {};", t.cat));
        }
        s.push_str(" }\n  Exports {");
        for (int, ext) in &self.exports {
            if int == ext {
                s.push_str(&format!(" {int};"));
            } else {
                s.push_str(&format!(" {int} => {ext};"));
            }
        }
        s.push_str(" }\n  Terms {\n");
        for t in &self.terms {
            s.push_str(&format!("    {}\n", render_rule(&t.rule)));
        }
        s.push_str("  }\n  Equations {\n");
        for e in &self.equations {
            let mut line = String::new();
            for (a, b) in &e.eq.freshness {
                line.push_str(&format!("if {a} # {b} then "));
            }
            line.push_str(&format!("{} == {};", render_ast(&e.eq.lhs), render_ast(&e.eq.rhs)));
            s.push_str(&format!("    {line}\n"));
        }
        s.push_str("  }\n  Rewrites {\n");
        for r in &self.rewrites {
            let mut line = format!("{} : ", r.rw.name);
            for (a, b) in &r.rw.premises {
                line.push_str(&format!("if {a} ~> {b} then "));
            }
            line.push_str(&format!("{} ~> {};", render_ast(&r.rw.lhs), render_ast(&r.rw.rhs)));
            s.push_str(&format!("    {line}\n"));
        }
        s.push_str("  }\n");
        s
    }
}

pub fn render_rule(r: &TermRule) -> String {
    let ctx: Vec<String> = r
        .context
        .iter()
        .map(|b| match b {
            Binding::Plain { name, sort, .. } => format!("{}:{}", name, sort.render()),
            Binding::Binder { binder, body, from, to, .. } => {
                format!("^{binder}.{body}:[{from} -> {to}]")
            },
        })
        .collect();
    let syn: Vec<String> = r
        .syntax
        .iter()
        .map(|i| match i {
            Item::Terminal(t) => format!("{t:?}"),
            Item::ArgRef(a) => a.clone(),
            Item::Projection { arg, sep } => format!("{arg}.*sep({sep:?})"),
        })
        .collect();
    format!("{} . {} |- {} : {};", r.label, ctx.join(", "), syn.join(" "), r.result)
}

pub fn render_ast(a: &Ast) -> String {
    match a {
        Ast::Var(n, _) => n.clone(),
        Ast::Remainder(n, _) => format!("...{n}"),
        Ast::Abs(b, body, _) => format!("^{b}.{}", render_ast(body)),
        Ast::Subst(abs, arg, _) => format!("(subst {} {})", render_ast(abs), render_ast(arg)),
        Ast::Coll(xs, _) => {
            let parts: Vec<String> = xs.iter().map(render_ast).collect();
            format!("{{{}}}", parts.join(", "))
        },
        Ast::SExp(l, args, _) => {
            if args.is_empty() {
                format!("({l})")
            } else {
                let parts: Vec<String> = args.iter().map(render_ast).collect();
                format!("({l} {})", parts.join(" "))
            }
        },
    }
}

fn same_rule(a: &TermRule, b: &TermRule) -> bool {
    a.label == b.label && a.result == b.result && render_rule(a) == render_rule(b)
}
