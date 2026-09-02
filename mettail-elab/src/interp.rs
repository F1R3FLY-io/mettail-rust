//! The elaborator: evaluates a theory expression to a [`Presentation`].

use crate::ast::*;
use crate::canonical::RhoValue;
use crate::diag::{Diag, DiagKind};
use crate::pres::*;
use crate::resolve::{ModuleRef, Program};
use std::collections::{HashMap, HashSet};

pub struct Interp<'a> {
    prog: &'a Program,
    next_id: u64,
}

/// Bindings in scope: `let`-bound names and theory parameters.
type Env = HashMap<String, Presentation>;

const MAX_THEORY_EVALUATION_STEPS: usize = 1_000_000;

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
        let inst = entry.entries().last().ok_or_else(|| {
            Diag::new(
                DiagKind::Resolution,
                format!("module `{}` has no `theory ...` instantiation to elaborate", entry.name),
                entry.span,
            )
        })?;
        let env = Env::new();
        self.eval(inst, &env, self.prog.entry_url())
    }

    /// Elaborate every `theory ...` entry in source order.
    ///
    /// Each entry gets a fresh interpreter so its presentation identities are
    /// independent of unrelated entries that happen to precede it. This is
    /// required for stable per-export canonical bytes and fingerprints.
    pub fn run_all(prog: &'a Program) -> Result<Vec<Presentation>, Diag> {
        Self::run_all_at(prog, prog.entry_url())
    }

    /// Elaborate every exported entry of any module in the already-resolved
    /// graph. This is used to prove that signed Registry projections agree
    /// with their source and exact dependency graph.
    pub(crate) fn run_all_at(
        prog: &'a Program,
        reference: &ModuleRef,
    ) -> Result<Vec<Presentation>, Diag> {
        let module = prog.module(reference).ok_or_else(|| {
            Diag::new(
                DiagKind::Resolution,
                format!("module `{reference}` is absent from the resolved graph"),
                crate::lex::Span { line: 0, col: 0 },
            )
        })?;
        let entry_count = module.entries().count();
        if entry_count == 0 {
            return Err(Diag::new(
                DiagKind::Resolution,
                format!("module `{}` has no `theory ...` instantiation to elaborate", module.name),
                module.span,
            ));
        }
        let mut presentations = Vec::with_capacity(entry_count);
        for expression in module.entries() {
            let mut interpreter = Self::new(prog);
            presentations.push(interpreter.eval(expression, &Env::new(), reference)?);
        }
        Ok(presentations)
    }

    pub fn eval(
        &mut self,
        e: &TheoryExpr,
        env: &Env,
        here: &ModuleRef,
    ) -> Result<Presentation, Diag> {
        enum Job {
            Eval {
                expression: TheoryExpr,
                env: Env,
                here: ModuleRef,
            },
            FinishCall {
                declaration: TheoryDecl,
                home: ModuleRef,
                span: crate::lex::Span,
                argument_count: usize,
                free: bool,
            },
            ExitCall((ModuleRef, String)),
            FinishFree,
            FinishLet {
                name: Ident,
                body: TheoryExpr,
                env: Env,
                here: ModuleRef,
            },
            FinishBuild {
                builder: Builder,
                span: crate::lex::Span,
            },
            FinishMeet(crate::lex::Span),
            FinishJoin(crate::lex::Span),
            FinishDiff(crate::lex::Span),
        }

        let mut jobs = vec![Job::Eval {
            expression: e.clone(),
            env: env.clone(),
            here: here.clone(),
        }];
        let mut values = Vec::<Presentation>::new();
        let mut active_calls = HashSet::<(ModuleRef, String)>::new();
        let mut steps = 0usize;

        while let Some(job) = jobs.pop() {
            steps = steps.checked_add(1).ok_or_else(|| {
                Diag::new(
                    DiagKind::ResourceLimit,
                    "theory evaluation step counter overflowed",
                    crate::lex::Span { line: 0, col: 0 },
                )
            })?;
            if steps > MAX_THEORY_EVALUATION_STEPS {
                return Err(Diag::new(
                    DiagKind::ResourceLimit,
                    format!(
                        "theory evaluation exceeds the maximum of {MAX_THEORY_EVALUATION_STEPS} steps"
                    ),
                    crate::lex::Span { line: 0, col: 0 },
                ));
            }

            match job {
                Job::Eval { expression, env, here } => match expression {
                    TheoryExpr::Empty(_) => values.push(Presentation::empty()),
                    TheoryExpr::Free(path, span) => {
                        let (declaration, home) = self.prog.lookup(&path, &here, span)?;
                        jobs.push(Job::FinishCall {
                            declaration,
                            home,
                            span,
                            argument_count: 0,
                            free: true,
                        });
                    },
                    TheoryExpr::Apply { head, args, span } => {
                        if head.is_simple() && args.is_empty() {
                            if let Some(presentation) = env.get(head.last()) {
                                values.push(presentation.clone());
                                continue;
                            }
                        }
                        let (declaration, home) = self.prog.lookup(&head, &here, span)?;
                        let argument_count = args.len();
                        jobs.push(Job::FinishCall {
                            declaration,
                            home,
                            span,
                            argument_count,
                            free: false,
                        });
                        for argument in args.into_iter().rev() {
                            jobs.push(Job::Eval {
                                expression: argument,
                                env: env.clone(),
                                here: here.clone(),
                            });
                        }
                    },
                    TheoryExpr::Let { name, bound, body, .. } => {
                        jobs.push(Job::FinishLet {
                            name,
                            body: *body,
                            env: env.clone(),
                            here: here.clone(),
                        });
                        jobs.push(Job::Eval { expression: *bound, env, here });
                    },
                    TheoryExpr::Build { base, builder, span } => {
                        jobs.push(Job::FinishBuild { builder, span });
                        jobs.push(Job::Eval { expression: *base, env, here });
                    },
                    TheoryExpr::Meet(left, right, span) => {
                        jobs.push(Job::FinishMeet(span));
                        jobs.push(Job::Eval {
                            expression: *right,
                            env: env.clone(),
                            here: here.clone(),
                        });
                        jobs.push(Job::Eval { expression: *left, env, here });
                    },
                    TheoryExpr::Join(left, right, span) => {
                        jobs.push(Job::FinishJoin(span));
                        jobs.push(Job::Eval {
                            expression: *right,
                            env: env.clone(),
                            here: here.clone(),
                        });
                        jobs.push(Job::Eval { expression: *left, env, here });
                    },
                    TheoryExpr::Diff(left, right, span) => {
                        jobs.push(Job::FinishDiff(span));
                        jobs.push(Job::Eval {
                            expression: *right,
                            env: env.clone(),
                            here: here.clone(),
                        });
                        jobs.push(Job::Eval { expression: *left, env, here });
                    },
                },
                Job::FinishCall {
                    declaration,
                    home,
                    span,
                    argument_count,
                    free,
                } => {
                    if argument_count != declaration.params.len() {
                        return Err(Diag::new(
                            DiagKind::Resolution,
                            format!(
                                "theory `{}` expects {} argument(s), given {}",
                                declaration.name,
                                declaration.params.len(),
                                argument_count
                            ),
                            span,
                        ));
                    }
                    let first_argument =
                        values.len().checked_sub(argument_count).ok_or_else(|| {
                            Diag::new(
                                DiagKind::Resolution,
                                "theory evaluator lost an argument value",
                                span,
                            )
                        })?;
                    let arguments: Vec<_> = values.drain(first_argument..).collect();
                    let call_key = (home.clone(), declaration.name.clone());
                    if !active_calls.insert(call_key.clone()) {
                        return Err(Diag::new(
                            DiagKind::Resolution,
                            format!(
                                "recursive theory application is not admissible: {}::{}",
                                home, declaration.name
                            ),
                            span,
                        ));
                    }

                    // A declaration body sees only its parameters. Lexical
                    // capture from the call site would break pushout sharing.
                    let mut body_env = Env::new();
                    for (parameter, argument) in
                        declaration.params.into_iter().zip(arguments.into_iter())
                    {
                        body_env.insert(parameter.name, argument);
                    }
                    if free {
                        jobs.push(Job::FinishFree);
                    }
                    jobs.push(Job::ExitCall(call_key));
                    jobs.push(Job::Eval {
                        expression: declaration.body,
                        env: body_env,
                        here: home,
                    });
                },
                Job::ExitCall(call) => {
                    active_calls.remove(&call);
                },
                Job::FinishFree => {
                    let presentation = values.pop().ok_or_else(|| {
                        Diag::new(
                            DiagKind::Resolution,
                            "theory evaluator lost a free-theory value",
                            crate::lex::Span { line: 0, col: 0 },
                        )
                    })?;
                    if let Some(core) = presentation.completed_core {
                        values.push(Presentation {
                            opaque_categories: core
                                .grammar
                                .categories
                                .into_iter()
                                .map(|category| category.name)
                                .collect(),
                            ..Presentation::default()
                        });
                    } else {
                        values.push(Presentation {
                            types: presentation.types,
                            exports: presentation.exports,
                            terms: Vec::new(),
                            equations: Vec::new(),
                            rewrites: Vec::new(),
                            export_origins: presentation.export_origins,
                            opaque_categories: presentation.opaque_categories,
                            ..Presentation::default()
                        });
                    }
                },
                Job::FinishLet { name, body, mut env, here } => {
                    let bound = values.pop().ok_or_else(|| {
                        Diag::new(
                            DiagKind::Resolution,
                            "theory evaluator lost a let-bound value",
                            body.span(),
                        )
                    })?;
                    // Evaluated once: every consumer receives the same
                    // element identities, preserving categorical sharing.
                    env.insert(name, bound);
                    jobs.push(Job::Eval { expression: body, env, here });
                },
                Job::FinishBuild { builder, span } => {
                    let base = values.pop().ok_or_else(|| {
                        Diag::new(DiagKind::Resolution, "theory evaluator lost a base", span)
                    })?;
                    values.push(self.build(base, &builder, span)?);
                },
                Job::FinishMeet(span) => {
                    let right = values.pop().expect("meet right value is scheduled");
                    let left = values.pop().expect("meet left value is scheduled");
                    values.push(left.meet(&right, span)?);
                },
                Job::FinishJoin(span) => {
                    let right = values.pop().expect("join right value is scheduled");
                    let left = values.pop().expect("join left value is scheduled");
                    values.push(left.join(&right, span)?);
                },
                Job::FinishDiff(span) => {
                    let right = values.pop().expect("difference right value is scheduled");
                    let left = values.pop().expect("difference left value is scheduled");
                    values.push(left.diff(&right, span)?);
                },
            }
        }

        if values.len() != 1 {
            return Err(Diag::new(
                DiagKind::Resolution,
                "theory evaluator produced an invalid value stack",
                e.span(),
            ));
        }
        Ok(values.pop().expect("checked one theory value"))
    }

    // ------------------------------------------------------------ builders

    fn build(
        &mut self,
        mut p: Presentation,
        b: &Builder,
        span: crate::lex::Span,
    ) -> Result<Presentation, Diag> {
        enum Job {
            Apply(Builder),
            FinishData {
                fragment: Presentation,
                fragment_id: ElemId,
                value: RhoValue,
            },
        }

        let result = (|| -> Result<Presentation, Diag> {
            let mut jobs = vec![Job::Apply(b.clone())];
            while let Some(job) = jobs.pop() {
                let Job::Apply(builder) = job else {
                    let Job::FinishData { mut fragment, fragment_id, value } = job else {
                        unreachable!()
                    };
                    p.opaque_categories.append(&mut fragment.opaque_categories);
                    p.opaque_labels.append(&mut fragment.opaque_labels);
                    p.data_derived.extend(
                        p.types
                            .iter()
                            .map(|entry| entry.id)
                            .chain(p.terms.iter().map(|entry| entry.id))
                            .chain(p.equations.iter().map(|entry| entry.id))
                            .chain(p.rewrites.iter().map(|entry| entry.id))
                            .filter(|id| id.0 > fragment_id.0),
                    );
                    p.data_derived_exports.extend(
                        p.export_origins
                            .iter()
                            .copied()
                            .filter(|id| id.0 > fragment_id.0),
                    );
                    p.canonical_fragments
                        .push(CanonicalFragment { id: fragment_id, value });
                    crate::canonical::presentation_to_value("DataFragment", &p)
                        .map_err(|error| Diag::new(DiagKind::Value, error.to_string(), span))?;
                    continue;
                };
                if p.completed_core().is_some() {
                    return Err(Diag::new(
                        DiagKind::Value,
                        "a completed LanguageCore cannot accept another builder",
                        span,
                    ));
                }
                p = match &builder {
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
                                let id = self.fresh();
                                p.exports.push((internal, ext));
                                p.export_origins.push(id);
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
                            let idx = match p.terms.iter().position(|e| e.rule.label == rep.target)
                            {
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
                                    format!(
                                        "rewrite `{}` is declared twice in this theory",
                                        rw.name
                                    ),
                                    rw.span,
                                ));
                            }
                            let id = self.fresh();
                            p.rewrites.push(RwEntry { id, rw: rw.clone() });
                        }
                        Ok(p)
                    },

                    Builder::Data(value) => {
                        if let Some(core) = crate::core_value::decode_language_core_data_fragment(
                            value,
                        )
                        .map_err(|error| Diag::new(DiagKind::Value, error.to_string(), span))?
                        {
                            if !p.is_initial_open() {
                                return Err(Diag::new(
                                    DiagKind::Value,
                                    "an exact LanguageCore Data fragment may be applied only to Empty",
                                    span,
                                ));
                            }
                            p.opaque_categories.extend(
                                core.grammar
                                    .categories
                                    .iter()
                                    .map(|category| category.name.clone()),
                            );
                            p.opaque_labels.extend(
                                core.grammar
                                    .productions
                                    .iter()
                                    .map(|production| production.label.clone()),
                            );
                            p.completed_core = Some(core);
                            Ok(p)
                        } else {
                            let mut fragment = crate::canonical::partial_value_to_presentation(
                                value,
                            )
                            .map_err(|error| Diag::new(DiagKind::Value, error.to_string(), span))?;
                            let fragment_id = self.fresh();
                            let mut builders = Vec::new();
                            if !fragment.types.is_empty() {
                                builders.push(Builder::Types(
                                    std::mem::take(&mut fragment.types)
                                        .into_iter()
                                        .map(|entry| CatDecl { cat: entry.cat, span })
                                        .collect(),
                                ));
                            }
                            if !fragment.exports.is_empty() {
                                builders.push(Builder::Exports(
                                    std::mem::take(&mut fragment.exports)
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
                                    std::mem::take(&mut fragment.terms)
                                        .into_iter()
                                        .map(|entry| entry.rule)
                                        .collect(),
                                ));
                            }
                            if !fragment.equations.is_empty() {
                                builders.push(Builder::Equations(
                                    std::mem::take(&mut fragment.equations)
                                        .into_iter()
                                        .map(|entry| entry.eq)
                                        .collect(),
                                ));
                            }
                            if !fragment.rewrites.is_empty() {
                                builders.push(Builder::Rewrites(
                                    std::mem::take(&mut fragment.rewrites)
                                        .into_iter()
                                        .map(|entry| entry.rw)
                                        .collect(),
                                ));
                            }
                            jobs.push(Job::FinishData {
                                fragment,
                                fragment_id,
                                value: value.clone(),
                            });
                            for builder in builders.into_iter().rev() {
                                jobs.push(Job::Apply(builder));
                            }
                            Ok(p)
                        }
                    },
                }?;
            }
            Ok(p)
        })();
        result.map_err(|d: Diag| {
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
    let mut work = vec![a];
    while let Some(ast) = work.pop() {
        match ast {
            Ast::SExp(label, arguments, _) => {
                if label == from {
                    *label = to.to_string();
                }
                work.extend(arguments.iter_mut().rev());
            },
            Ast::Subst(abstraction, argument, _) => {
                work.push(argument);
                work.push(abstraction);
            },
            Ast::Abs(_, body, _) => work.push(body),
            Ast::Coll(elements, _) => work.extend(elements.iter_mut().rev()),
            Ast::Var(..) | Ast::Remainder(..) => {},
        }
    }
}
