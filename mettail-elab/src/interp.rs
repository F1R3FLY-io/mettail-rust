//! The elaborator: evaluates a theory expression to a [`Presentation`].

use crate::ast::*;
use crate::diag::{Diag, DiagKind};
use crate::pres::*;
use crate::resolve::{ModuleRef, Program};
use std::collections::HashMap;

pub struct Interp<'a> {
    prog: &'a Program,
    next_id: u64,
}

/// Bindings in scope: `let`-bound names and theory parameters.
type Env = HashMap<String, Presentation>;

impl<'a> Interp<'a> {
    pub fn new(prog: &'a Program) -> Interp<'a> {
        Interp { prog, next_id: 1 }
    }

    fn fresh(&mut self) -> ElemId {
        let id = ElemId(self.next_id);
        self.next_id += 1;
        id
    }

    /// Elaborate the entry point: the last `theory ...` in the entry module.
    pub fn run(&mut self) -> Result<Presentation, Diag> {
        let entry = self.prog.entry_module();
        let inst = entry.instantiations.last().ok_or_else(|| {
            Diag::new(
                DiagKind::Resolution,
                format!("module `{}` has no `theory ...` instantiation to elaborate", entry.name),
                entry.span,
            )
        })?;
        let env = Env::new();
        self.eval(inst, &env, self.prog.entry_url())
    }

    pub fn eval(
        &mut self,
        e: &TheoryExpr,
        env: &Env,
        here: &ModuleRef,
    ) -> Result<Presentation, Diag> {
        match e {
            TheoryExpr::Empty(_) => Ok(Presentation::empty()),

            // `free(P)` - the free theory on P's categories: terms, equations
            // and rewrites dropped, categories retained.
            TheoryExpr::Free(path, span) => {
                let (decl, home) = self.prog.lookup(path, here, *span)?;
                let p = self.apply_decl(&decl, &[], env, &home, *span)?;
                Ok(Presentation {
                    types: p.types,
                    exports: p.exports,
                    terms: Vec::new(),
                    equations: Vec::new(),
                    rewrites: Vec::new(),
                })
            },

            TheoryExpr::Apply { head, args, span } => {
                // A bare simple name may be a `let`-bound or parameter binding.
                if head.is_simple() && args.is_empty() {
                    if let Some(p) = env.get(head.last()) {
                        return Ok(p.clone());
                    }
                }
                let (decl, home) = self.prog.lookup(head, here, *span)?;
                let mut evaled = Vec::new();
                for a in args {
                    evaled.push(self.eval(a, env, here)?);
                }
                self.apply_decl(&decl, &evaled, env, &home, *span)
            },

            // Elaborated once, so every consumer sees identical ElemIds. This
            // is what makes D3's pushout work.
            TheoryExpr::Let { name, bound, body, .. } => {
                let v = self.eval(bound, env, here)?;
                let mut env2 = env.clone();
                env2.insert(name.clone(), v);
                self.eval(body, &env2, here)
            },

            TheoryExpr::Build { base, builder, span } => {
                let p = self.eval(base, env, here)?;
                self.build(p, builder, *span)
            },

            TheoryExpr::Meet(a, b, _) => {
                let pa = self.eval(a, env, here)?;
                let pb = self.eval(b, env, here)?;
                Ok(pa.meet(&pb))
            },
            TheoryExpr::Join(a, b, span) => {
                let pa = self.eval(a, env, here)?;
                let pb = self.eval(b, env, here)?;
                pa.join(&pb, *span)
            },
            TheoryExpr::Diff(a, b, _) => {
                let pa = self.eval(a, env, here)?;
                let pb = self.eval(b, env, here)?;
                Ok(pa.diff(&pb))
            },
        }
    }

    fn apply_decl(
        &mut self,
        decl: &TheoryDecl,
        args: &[Presentation],
        _outer: &Env,
        home: &ModuleRef,
        span: crate::lex::Span,
    ) -> Result<Presentation, Diag> {
        if args.len() != decl.params.len() {
            return Err(Diag::new(
                DiagKind::Resolution,
                format!(
                    "theory `{}` expects {} argument(s), given {}",
                    decl.name,
                    decl.params.len(),
                    args.len()
                ),
                span,
            ));
        }
        // A theory body sees only its parameters. Lexical capture from the
        // call site would break the sharing discipline.
        let mut env = Env::new();
        for (p, a) in decl.params.iter().zip(args.iter()) {
            env.insert(p.name.clone(), a.clone());
        }
        self.eval(&decl.body, &env, home)
    }

    // ------------------------------------------------------------ builders

    fn build(
        &mut self,
        mut p: Presentation,
        b: &Builder,
        span: crate::lex::Span,
    ) -> Result<Presentation, Diag> {
        match b {
            // G1
            Builder::Types(decls) => {
                for d in decls {
                    if p.has_cat(&d.cat) {
                        return Err(Diag::new(
                            DiagKind::RepeatLabel,
                            format!("category `{}` is declared twice", d.cat),
                            d.span,
                        ));
                    }
                    let id = self.fresh();
                    p.types
                        .push(CatEntry { id, cat: d.cat.clone(), span: d.span });
                }
                Ok(p)
            },

            Builder::Exports(exports) => {
                for e in exports {
                    if !p.has_cat(&e.cat) {
                        // A category may be brought into being by being
                        // exported; record it, so `Empty Exports { Elem; }`
                        // still means something.
                        let id = self.fresh();
                        p.types
                            .push(CatEntry { id, cat: e.cat.clone(), span: e.span });
                    }
                    let ext = e.as_name.clone().unwrap_or_else(|| e.cat.clone());
                    // Rename-on-export renames the category everywhere.
                    if let Some(new) = &e.as_name {
                        rename_cat(&mut p, &e.cat, new);
                    }
                    let internal = ext.clone();
                    if !p.exports.iter().any(|(_, x)| *x == ext) {
                        p.exports.push((internal, ext));
                    }
                }
                Ok(p)
            },

            Builder::Terms(rules) => {
                for r in rules {
                    self.check_rule(&p, r)?;
                    if p.has_label(&r.label) {
                        return Err(Diag::new(
                            DiagKind::RepeatLabel,
                            format!("label `{}` is declared twice in this theory", r.label),
                            r.span,
                        ));
                    }
                    let id = self.fresh();
                    p.terms
                        .push(TermEntry { id, rule: r.clone(), span: r.span });
                }
                Ok(p)
            },

            Builder::Replacements(reps) => {
                for rep in reps {
                    let idx = match p.terms.iter().position(|e| e.rule.label == rep.target) {
                        Some(i) => i,
                        None => {
                            return Err(Diag::new(
                                DiagKind::UnknownReplacementTarget,
                                format!(
                                    "replacement target `{}` is not a label of this theory",
                                    rep.target
                                ),
                                rep.span,
                            ))
                        },
                    };
                    // `bad/ReplacementShadows.module`: the new label must not
                    // collide with a *different* existing label.
                    if rep.rule.label != rep.target && p.has_label(&rep.rule.label) {
                        return Err(Diag::new(
                            DiagKind::ReplacementShadows,
                            format!(
                                "replacement of `{}` introduces label `{}`, which already \
                                 exists in this theory",
                                rep.target, rep.rule.label
                            ),
                            rep.span,
                        ));
                    }
                    self.check_rule(&p, &rep.rule)?;
                    let old_label = p.terms[idx].rule.label.clone();
                    // The ElemId is preserved: a replacement performed in a
                    // shared ancestor stays shared (see pres.rs).
                    p.terms[idx].rule = rep.rule.clone();
                    relabel(&mut p, &old_label, &rep.rule.label);
                }
                Ok(p)
            },

            Builder::Equations(eqs) => {
                for eq in eqs {
                    let mut ls = Vec::new();
                    eq.lhs.labels(&mut ls);
                    eq.rhs.labels(&mut ls);
                    self.check_known(&p, &ls, "Equations", eq.span)?;
                    let id = self.fresh();
                    p.equations.push(EqEntry { id, eq: eq.clone() });
                }
                Ok(p)
            },

            Builder::Rewrites(rws) => {
                for rw in rws {
                    let mut ls = Vec::new();
                    rw.lhs.labels(&mut ls);
                    rw.rhs.labels(&mut ls);
                    self.check_known(&p, &ls, "Rewrites", rw.span)?;
                    if p.rewrites.iter().any(|e| e.rw.name == rw.name) {
                        return Err(Diag::new(
                            DiagKind::RepeatLabel,
                            format!("rewrite `{}` is declared twice in this theory", rw.name),
                            rw.span,
                        ));
                    }
                    let id = self.fresh();
                    p.rewrites.push(RwEntry { id, rw: rw.clone() });
                }
                Ok(p)
            },

            Builder::Data(value) => {
                let fragment = crate::canonical::partial_value_to_presentation(value)
                    .map_err(|error| Diag::new(DiagKind::Value, error.to_string(), span))?;
                let mut builders = Vec::new();
                if !fragment.types.is_empty() {
                    builders.push(Builder::Types(
                        fragment
                            .types
                            .into_iter()
                            .map(|entry| CatDecl { cat: entry.cat, span })
                            .collect(),
                    ));
                }
                if !fragment.exports.is_empty() {
                    builders.push(Builder::Exports(
                        fragment
                            .exports
                            .into_iter()
                            .map(|(cat, exported)| Export {
                                as_name: (cat != exported).then_some(exported),
                                cat,
                                span,
                            })
                            .collect(),
                    ));
                }
                if !fragment.terms.is_empty() {
                    builders.push(Builder::Terms(
                        fragment.terms.into_iter().map(|entry| entry.rule).collect(),
                    ));
                }
                if !fragment.equations.is_empty() {
                    builders.push(Builder::Equations(
                        fragment
                            .equations
                            .into_iter()
                            .map(|entry| entry.eq)
                            .collect(),
                    ));
                }
                if !fragment.rewrites.is_empty() {
                    builders.push(Builder::Rewrites(
                        fragment
                            .rewrites
                            .into_iter()
                            .map(|entry| entry.rw)
                            .collect(),
                    ));
                }
                for builder in builders {
                    p = self.build(p, &builder, span)?;
                }
                Ok(p)
            },
        }
        .map_err(|d: Diag| {
            if d.span.line == 0 {
                Diag::new(d.kind, d.msg, span)
            } else {
                d
            }
        })
    }

    /// The ordered builder chain (plan §3.2): a label must already exist.
    fn check_known(
        &self,
        p: &Presentation,
        labels: &[Label],
        block: &str,
        span: crate::lex::Span,
    ) -> Result<(), Diag> {
        for l in labels {
            if !p.has_label(l) {
                return Err(Diag::new(
                    DiagKind::ForwardReference,
                    format!(
                        "`{block}` mentions label `{l}`, which no preceding `Terms` block \
                         introduces; the builder chain is ordered, so move the `Terms` \
                         block ahead of this one"
                    ),
                    span,
                ));
            }
        }
        Ok(())
    }

    /// G1, G2 and G6 well-formedness for a single term rule.
    fn check_rule(&self, p: &Presentation, r: &TermRule) -> Result<(), Diag> {
        // The result category, and every argument's base category, must be
        // declared - either already present, or introduced by this same rule's
        // result (a rule may be the first mention of its own result category
        // only if `Types` declared it).
        if !p.has_cat(&r.result) {
            return Err(Diag::new(
                DiagKind::UndeclaredCategory,
                format!(
                    "term `{}` produces category `{}`, which no `Types` or `Exports` \
                     block declares",
                    r.label, r.result
                ),
                r.span,
            ));
        }
        for bnd in &r.context {
            let cats: Vec<&str> = match bnd {
                Binding::Plain { sort, .. } => vec![sort.base_cat()],
                Binding::Binder { from, to, .. } => vec![from.as_str(), to.as_str()],
            };
            for c in cats {
                if !p.has_cat(c) {
                    return Err(Diag::new(
                        DiagKind::UndeclaredCategory,
                        format!(
                            "term `{}` mentions category `{}`, which no `Types` or \
                             `Exports` block declares",
                            r.label, c
                        ),
                        bnd.span(),
                    ));
                }
            }
        }

        // G6: every argument referenced exactly once in the concrete syntax.
        let mut names: Vec<&str> = Vec::new();
        for b in &r.context {
            names.extend(b.names());
        }
        let mut used: Vec<&str> = Vec::new();
        for item in &r.syntax {
            match item {
                Item::Terminal(_) => {},
                Item::ArgRef(a) => used.push(a),
                Item::Projection { arg, .. } => used.push(arg),
            }
        }
        for u in &used {
            if !names.contains(u) {
                return Err(Diag::new(
                    DiagKind::ArgumentUse,
                    format!(
                        "term `{}` refers to `{u}` in its concrete syntax, but `{u}` is \
                         not in its context",
                        r.label
                    ),
                    r.span,
                ));
            }
        }
        for n in &names {
            let count = used.iter().filter(|u| *u == n).count();
            if count != 1 {
                return Err(Diag::new(
                    DiagKind::ArgumentUse,
                    format!(
                        "term `{}` binds `{n}` but references it {count} times in its \
                         concrete syntax; each argument must appear exactly once",
                        r.label
                    ),
                    r.span,
                ));
            }
        }

        // G2: a projection is meaningful only over a collection sort.
        for item in &r.syntax {
            if let Item::Projection { arg, .. } = item {
                let is_coll = r.context.iter().any(|b| match b {
                    Binding::Plain { name, sort, .. } => {
                        name == arg && matches!(sort, Sort::Coll { .. })
                    },
                    _ => false,
                });
                if !is_coll {
                    return Err(Diag::new(
                        DiagKind::ArgumentUse,
                        format!(
                            "term `{}` applies a separator projection to `{arg}`, which is \
                             not of a collection sort",
                            r.label
                        ),
                        r.span,
                    ));
                }
            }
        }
        Ok(())
    }
}

fn rename_cat(p: &mut Presentation, from: &str, to: &str) {
    for c in p.types.iter_mut() {
        if c.cat == from {
            c.cat = to.to_string();
        }
    }
    for t in p.terms.iter_mut() {
        if t.rule.result == from {
            t.rule.result = to.to_string();
        }
        for b in t.rule.context.iter_mut() {
            match b {
                Binding::Plain { sort, .. } => match sort {
                    Sort::Cat(c) if c == from => *c = to.to_string(),
                    Sort::Coll { of, .. } if of == from => *of = to.to_string(),
                    _ => {},
                },
                Binding::Binder { from: f, to: t2, .. } => {
                    if f == from {
                        *f = to.to_string();
                    }
                    if t2 == from {
                        *t2 = to.to_string();
                    }
                },
            }
        }
    }
    for (int, ext) in p.exports.iter_mut() {
        if int == from {
            *int = to.to_string();
        }
        if ext == from {
            *ext = to.to_string();
        }
    }
}

/// After a replacement, occurrences of the old label in equations and rewrites
/// follow the new name.
fn relabel(p: &mut Presentation, from: &str, to: &str) {
    if from == to {
        return;
    }
    for e in p.equations.iter_mut() {
        relabel_ast(&mut e.eq.lhs, from, to);
        relabel_ast(&mut e.eq.rhs, from, to);
    }
    for r in p.rewrites.iter_mut() {
        relabel_ast(&mut r.rw.lhs, from, to);
        relabel_ast(&mut r.rw.rhs, from, to);
    }
}

fn relabel_ast(a: &mut Ast, from: &str, to: &str) {
    match a {
        Ast::SExp(l, args, _) => {
            if l == from {
                *l = to.to_string();
            }
            for x in args {
                relabel_ast(x, from, to);
            }
        },
        Ast::Subst(x, y, _) => {
            relabel_ast(x, from, to);
            relabel_ast(y, from, to);
        },
        Ast::Abs(_, b, _) => relabel_ast(b, from, to),
        Ast::Coll(xs, _) => {
            for x in xs {
                relabel_ast(x, from, to);
            }
        },
        Ast::Var(..) | Ast::Remainder(..) => {},
    }
}
