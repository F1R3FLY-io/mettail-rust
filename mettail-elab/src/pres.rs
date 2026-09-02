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
use crate::canonical::RhoValue;
use crate::diag::{Diag, DiagKind};
use crate::lex::Span;
use mettail_grammar_core::LanguageCoreV1;
use std::collections::BTreeSet;

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

#[derive(Clone, Debug)]
pub(crate) struct CanonicalFragment {
    pub id: ElemId,
    pub value: RhoValue,
}

#[derive(Clone, Debug, Default)]
pub struct Presentation {
    pub types: Vec<CatEntry>,
    /// (internal category, exported name)
    pub exports: Vec<(Cat, Cat)>,
    pub terms: Vec<TermEntry>,
    pub equations: Vec<EqEntry>,
    pub rewrites: Vec<RwEntry>,
    pub(crate) export_origins: Vec<ElemId>,
    pub(crate) canonical_fragments: Vec<CanonicalFragment>,
    pub(crate) data_derived: BTreeSet<ElemId>,
    pub(crate) data_derived_exports: BTreeSet<ElemId>,
    pub(crate) opaque_categories: BTreeSet<String>,
    pub(crate) opaque_labels: BTreeSet<String>,
    /// A completed language embedded by the closed exact-core `Data(v)` arm.
    /// It is an object boundary, not an open fragment: builders and unequal
    /// theory algebra cannot inspect or silently rewrite it.
    pub(crate) completed_core: Option<LanguageCoreV1>,
}

impl Presentation {
    pub fn empty() -> Presentation {
        Presentation::default()
    }

    pub(crate) fn is_initial_open(&self) -> bool {
        self.completed_core.is_none()
            && self.types.is_empty()
            && self.exports.is_empty()
            && self.terms.is_empty()
            && self.equations.is_empty()
            && self.rewrites.is_empty()
            && self.canonical_fragments.is_empty()
            && self.data_derived.is_empty()
            && self.data_derived_exports.is_empty()
            && self.opaque_categories.is_empty()
            && self.opaque_labels.is_empty()
    }

    pub(crate) fn completed_core(&self) -> Option<&LanguageCoreV1> {
        self.completed_core.as_ref()
    }

    pub fn has_cat(&self, c: &str) -> bool {
        self.types.iter().any(|e| e.cat == c) || self.opaque_categories.contains(c)
    }
    pub fn has_label(&self, l: &str) -> bool {
        self.terms.iter().any(|e| e.rule.label == l) || self.opaque_labels.contains(l)
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
        if let Some(core) = &self.completed_core {
            return core
                .grammar
                .categories
                .iter()
                .map(|category| category.name.clone())
                .collect();
        }
        if self.exports.is_empty() {
            self.types.iter().map(|e| e.cat.clone()).collect()
        } else {
            self.exports.iter().map(|(_, ext)| ext.clone()).collect()
        }
    }

    // ------------------------------------------------------------- lattice

    /// D3 join: union, identifying elements that share an `ElemId`.
    pub fn join(&self, other: &Presentation, span: Span) -> Result<Presentation, Diag> {
        match (&self.completed_core, &other.completed_core) {
            (Some(left), Some(right)) if left == right => return Ok(self.clone()),
            (Some(_), None) if other.is_initial_open() => return Ok(self.clone()),
            (None, Some(_)) if self.is_initial_open() => return Ok(other.clone()),
            (Some(_), _) | (_, Some(_)) => {
                return Err(Diag::new(
                    DiagKind::JoinCollision,
                    "a completed LanguageCore may join only with itself or Empty",
                    span,
                ))
            },
            (None, None) => {},
        }
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
            let index = other
                .exports
                .iter()
                .position(|value| value == ex)
                .unwrap_or(0);
            let origin = other
                .export_origins
                .get(index)
                .copied()
                .unwrap_or(ElemId(0));
            if let Some(existing) = out.exports.iter().position(|value| value == ex) {
                if out.export_origins.get(existing).copied() == Some(origin) {
                    continue;
                }
            }
            if !out.exports.contains(ex) {
                out.exports.push(ex.clone());
                out.export_origins.push(origin);
            }
        }
        for fragment in &other.canonical_fragments {
            match out
                .canonical_fragments
                .iter()
                .find(|value| value.id == fragment.id)
            {
                Some(existing) if existing.value == fragment.value => {},
                Some(_) => {
                    return Err(Diag::new(
                        DiagKind::JoinCollision,
                        format!(
                            "canonical fragment {:?} differs along the two join paths",
                            fragment.id
                        ),
                        span,
                    ))
                },
                None => out.canonical_fragments.push(fragment.clone()),
            }
        }
        out.data_derived.extend(other.data_derived.iter().copied());
        out.data_derived_exports
            .extend(other.data_derived_exports.iter().copied());
        out.opaque_categories
            .extend(other.opaque_categories.iter().cloned());
        out.opaque_labels
            .extend(other.opaque_labels.iter().cloned());
        Ok(out)
    }

    /// Meet: the common fragment, by origin.
    pub fn meet(&self, other: &Presentation, span: Span) -> Result<Presentation, Diag> {
        match (&self.completed_core, &other.completed_core) {
            (Some(left), Some(right)) if left == right => return Ok(self.clone()),
            (Some(_), None) if other.is_initial_open() => return Ok(Presentation::empty()),
            (None, Some(_)) if self.is_initial_open() => return Ok(Presentation::empty()),
            (Some(_), _) | (_, Some(_)) => {
                return Err(Diag::new(
                    DiagKind::JoinCollision,
                    "a completed LanguageCore has a meet only with itself or Empty",
                    span,
                ))
            },
            (None, None) => {},
        }
        let keep = |id: ElemId, ids: &[ElemId]| ids.contains(&id);
        let ot: Vec<ElemId> = other.types.iter().map(|e| e.id).collect();
        let om: Vec<ElemId> = other.terms.iter().map(|e| e.id).collect();
        let oe: Vec<ElemId> = other.equations.iter().map(|e| e.id).collect();
        let orw: Vec<ElemId> = other.rewrites.iter().map(|e| e.id).collect();
        let fragments: Vec<ElemId> = other
            .canonical_fragments
            .iter()
            .map(|entry| entry.id)
            .collect();
        Ok(Presentation {
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
            export_origins: self
                .export_origins
                .iter()
                .copied()
                .filter(|id| other.export_origins.contains(id))
                .collect(),
            canonical_fragments: self
                .canonical_fragments
                .iter()
                .filter(|entry| fragments.contains(&entry.id))
                .cloned()
                .collect(),
            data_derived: self
                .data_derived
                .intersection(&other.data_derived)
                .copied()
                .collect(),
            data_derived_exports: self
                .data_derived_exports
                .intersection(&other.data_derived_exports)
                .copied()
                .collect(),
            opaque_categories: self
                .opaque_categories
                .intersection(&other.opaque_categories)
                .cloned()
                .collect(),
            opaque_labels: self
                .opaque_labels
                .intersection(&other.opaque_labels)
                .cloned()
                .collect(),
            completed_core: None,
        })
    }

    /// Difference: everything in `self` whose origin is not in `other`.
    pub fn diff(&self, other: &Presentation, span: Span) -> Result<Presentation, Diag> {
        match (&self.completed_core, &other.completed_core) {
            (Some(left), Some(right)) if left == right => return Ok(Presentation::empty()),
            (Some(_), None) if other.is_initial_open() => return Ok(self.clone()),
            (None, Some(_)) if self.is_initial_open() => return Ok(Presentation::empty()),
            (Some(_), _) | (_, Some(_)) => {
                return Err(Diag::new(
                    DiagKind::JoinCollision,
                    "a completed LanguageCore has a difference only with itself or Empty",
                    span,
                ))
            },
            (None, None) => {},
        }
        let ot: Vec<ElemId> = other.types.iter().map(|e| e.id).collect();
        let om: Vec<ElemId> = other.terms.iter().map(|e| e.id).collect();
        let oe: Vec<ElemId> = other.equations.iter().map(|e| e.id).collect();
        let orw: Vec<ElemId> = other.rewrites.iter().map(|e| e.id).collect();
        let fragments: Vec<ElemId> = other
            .canonical_fragments
            .iter()
            .map(|entry| entry.id)
            .collect();
        Ok(Presentation {
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
            export_origins: self
                .export_origins
                .iter()
                .copied()
                .filter(|id| !other.export_origins.contains(id))
                .collect(),
            canonical_fragments: self
                .canonical_fragments
                .iter()
                .filter(|entry| !fragments.contains(&entry.id))
                .cloned()
                .collect(),
            data_derived: self
                .data_derived
                .difference(&other.data_derived)
                .copied()
                .collect(),
            data_derived_exports: self
                .data_derived_exports
                .difference(&other.data_derived_exports)
                .copied()
                .collect(),
            opaque_categories: self
                .opaque_categories
                .difference(&other.opaque_categories)
                .cloned()
                .collect(),
            opaque_labels: self
                .opaque_labels
                .difference(&other.opaque_labels)
                .cloned()
                .collect(),
            completed_core: None,
        })
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
    enum Task<'a> {
        Ast(&'a Ast),
        Text(&'a str),
    }

    let mut output = String::new();
    let mut tasks = vec![Task::Ast(a)];
    while let Some(task) = tasks.pop() {
        match task {
            Task::Text(text) => output.push_str(text),
            Task::Ast(Ast::Var(name, _)) => output.push_str(name),
            Task::Ast(Ast::Remainder(name, _)) => {
                output.push_str("...");
                output.push_str(name);
            },
            Task::Ast(Ast::Abs(binder, body, _)) => {
                output.push('^');
                output.push_str(binder);
                output.push('.');
                tasks.push(Task::Ast(body));
            },
            Task::Ast(Ast::Subst(abstraction, argument, _)) => {
                output.push_str("(subst ");
                tasks.push(Task::Text(")"));
                tasks.push(Task::Ast(argument));
                tasks.push(Task::Text(" "));
                tasks.push(Task::Ast(abstraction));
            },
            Task::Ast(Ast::Coll(elements, _)) => {
                output.push('{');
                tasks.push(Task::Text("}"));
                for (index, element) in elements.iter().enumerate().rev() {
                    tasks.push(Task::Ast(element));
                    if index > 0 {
                        tasks.push(Task::Text(", "));
                    }
                }
            },
            Task::Ast(Ast::SExp(label, arguments, _)) => {
                output.push('(');
                output.push_str(label);
                tasks.push(Task::Text(")"));
                for argument in arguments.iter().rev() {
                    tasks.push(Task::Ast(argument));
                    tasks.push(Task::Text(" "));
                }
            },
        }
    }
    output
}

fn same_rule(a: &TermRule, b: &TermRule) -> bool {
    a.label == b.label && a.result == b.result && render_rule(a) == render_rule(b)
}
