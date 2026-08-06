//! A-S5.6 (F6) — display-side DE-REFLECTION of runtime observation values into the
//! current language's SURFACE SYNTAX.
//!
//! The in-Rho quiescence driver rests a REFLECTED normal form on OUT: binder scopes are
//! α-erased to the reserved `^lambda(body)` shape with de Bruijn `^bound(S^k(Z))` leaves,
//! free variables are `^free(<moniker FreeVar debug>)` leaves, and AC soups decode as
//! multiset [`RuntimeObservationValue::Bag`]s. The raw constructor rendering
//! (`^lambda(^bound(S(Z)))`) is neither the language's syntax nor parseable, so `exec`
//! display de-reflects (plan v2 §6.3, v1 §6.3):
//!
//! * `^lambda(body)` → the language's UNIQUE binder constructor, rendered with a
//!   GENERATED FRESH surface name (α-correct by construction — never byte-identical to
//!   the pre-flip hints, which is exactly why the goldens are α-equivalence, F6);
//! * `^bound(S^k(Z))` → the surface name of the k-th enclosing generated binder;
//! * `^free(debug)` → the variable's `pretty_name` (collision-freshened — AM-6c: a
//!   rendered NF may contain a bound binder whose hint collides with a DISTINCT free
//!   variable; blind hint rendering would re-capture it at parse time, so every
//!   generated binder name avoids every rendered free name, and distinct free variables
//!   sharing one hint get disambiguating suffixes);
//! * `Bag` soups → the language's unique `HashBag` production syntax, elements rendered
//!   then SORTED (byte order) — the deterministic print-order pin. ⚠ Canonical-NF
//!   display claims ride the NewComm ≤6 canonical-ordering cap
//!   (`binder_congruence.rs` — binder permutations are canonically ordered exhaustively
//!   only up to 6 consecutive `new`s; encounter order beyond), so sorted BAG rendering
//!   pins element order, not binder-permutation order;
//! * every other constructor node → its grammar production, terminals emitted verbatim.
//!
//! The output is PARSEABLE surface syntax by construction (it follows the language's own
//! grammar productions), which is what lets the F6 goldens parse it back and compare
//! α-aware (`BoundTerm::term_eq`) against the Dovetail-era terms.
//!
//! Fail-loud, fall-back-raw: any shape outside the language's productions (a foreign
//! constructor, a multi-binder `^multilambda`, an ambiguous binder/bag production) is a
//! typed `Err` — the REPL then falls back to the raw constructor rendering, never a
//! wrong surface string.

use mettail_ast::grammar::{GrammarItem, GrammarRule, SyntaxExpr, TermParam};
use mettail_ast::language::LanguageDef;
use mettail_rholang_codegen::{
    reconstruct_language_def, BOUND_VAR_REFLECT_LABEL, FREE_VAR_REFLECT_LABEL,
    LAMBDA_REFLECT_LABEL, MULTILAMBDA_REFLECT_LABEL, PEANO_SUCC_REFLECT_LABEL,
    PEANO_ZERO_REFLECT_LABEL,
};
use mettail_runtime::RuntimeObservationValue;
use std::borrow::Cow;
use std::collections::{BTreeMap, BTreeSet};

/// A reconstructed-grammar surface renderer for one language's observation values.
pub struct SurfaceRenderer {
    def: LanguageDef,
}

/// The free-variable surface-name table of one value: every distinct `^free` debug
/// string mapped to a collision-free surface name, plus the set of all names in use
/// (fresh binder names must avoid them — AM-6c).
#[derive(Default)]
struct FreeNameTable {
    by_debug: BTreeMap<String, String>,
    used: BTreeSet<String>,
}

impl FreeNameTable {
    /// Assign (or return) the surface name for one `^free` debug string. First choice is
    /// the moniker `pretty_name` hint; a hint already claimed by a DIFFERENT variable
    /// (or an absent hint) gets a deterministic disambiguating suffix.
    fn assign(&mut self, debug: &str) -> String {
        if let Some(existing) = self.by_debug.get(debug) {
            return existing.clone();
        }
        let hint = parse_pretty_name(debug).unwrap_or_else(|| "v".to_string());
        let name = if self.used.contains(&hint) {
            let mut counter = 1usize;
            loop {
                let candidate = format!("{hint}_{counter}");
                if !self.used.contains(&candidate) {
                    break candidate;
                }
                counter += 1;
            }
        } else {
            hint
        };
        self.used.insert(name.clone());
        self.by_debug.insert(debug.to_string(), name.clone());
        name
    }
}

/// Extract the `pretty_name` hint from a moniker `FreeVar` DEBUG string
/// (`FreeVar { unique_id: UniqueId(7), pretty_name: Some("x") }` — the exact shape the
/// generated `__mettail_rho_net_to_ground` reflects via `format!("{:?}", fv)`).
fn parse_pretty_name(debug: &str) -> Option<String> {
    let start = debug.find("pretty_name: Some(\"")? + "pretty_name: Some(\"".len();
    let rest = &debug[start..];
    let end = rest.find('"')?;
    Some(rest[..end].to_string())
}

/// Deterministic fresh-binder-name generator: `x0`, `x1`, … skipping every name already
/// in use (free names and earlier binders).
struct FreshNames {
    used: BTreeSet<String>,
    next: usize,
}

impl FreshNames {
    fn new(used: BTreeSet<String>) -> Self {
        Self { used, next: 0 }
    }

    fn generate(&mut self) -> String {
        loop {
            let candidate = format!("x{}", self.next);
            self.next += 1;
            if !self.used.contains(&candidate) {
                // `next` never repeats, so only the names reserved before generation (the free
                // names) need membership storage. Retaining every emitted binder here would add
                // O(depth) tree nodes and O(log depth) insertion work without changing freshness.
                return candidate;
            }
        }
    }
}

type RenderId = usize;

/// Flat ownership arena for a rendered output DAG.
///
/// A nested constructor must not repeatedly copy the complete string rendered by its child: a
/// unary spine would make that recurrence quadratic. Nodes therefore refer to earlier nodes by
/// integer index, and the completed DAG is streamed into one exactly-sized `String` by an
/// explicit work stack. The arena is also important on the error path: it contains no recursively
/// owned Rust value, so abandoning a partially rendered observation cannot recurse through Drop.
struct RenderArena<'a> {
    nodes: Vec<RenderNode<'a>>,
}

struct RenderNode<'a> {
    kind: RenderNodeKind<'a>,
    byte_len: usize,
}

enum RenderNodeKind<'a> {
    Text(Cow<'a, str>),
    Concat(Vec<RenderId>),
}

impl<'a> RenderArena<'a> {
    fn new() -> Self {
        Self { nodes: Vec::new() }
    }

    fn text(&mut self, text: impl Into<Cow<'a, str>>) -> RenderId {
        let text = text.into();
        let id = self.nodes.len();
        self.nodes.push(RenderNode {
            byte_len: text.len(),
            kind: RenderNodeKind::Text(text),
        });
        id
    }

    fn concat(&mut self, parts: Vec<RenderId>) -> RenderId {
        if let [only] = parts.as_slice() {
            return *only;
        }
        let byte_len = parts
            .iter()
            .map(|id| self.nodes[*id].byte_len)
            .try_fold(0usize, usize::checked_add)
            .expect("a rendered observation cannot exceed addressable memory");
        let id = self.nodes.len();
        self.nodes.push(RenderNode {
            kind: RenderNodeKind::Concat(parts),
            byte_len,
        });
        id
    }

    fn join(&mut self, parts: Vec<RenderId>, separator: Cow<'a, str>) -> RenderId {
        if parts.is_empty() {
            return self.text("");
        }
        if parts.len() == 1 {
            return parts[0];
        }
        let mut joined = Vec::with_capacity(parts.len().saturating_mul(2).saturating_sub(1));
        let mut parts = parts.into_iter();
        joined.push(parts.next().expect("nonempty parts checked above"));
        for part in parts {
            joined.push(self.text(separator.clone()));
            joined.push(part);
        }
        self.concat(joined)
    }

    fn materialize(&self, root: RenderId) -> String {
        let mut output = String::with_capacity(self.nodes[root].byte_len);
        let mut work = vec![root];
        while let Some(id) = work.pop() {
            match &self.nodes[id].kind {
                RenderNodeKind::Text(text) => output.push_str(text),
                RenderNodeKind::Concat(parts) => work.extend(parts.iter().rev().copied()),
            }
        }
        output
    }
}

/// One continuation of the surface-rendering pushdown automaton.
///
/// The context and old-style grammar continuations deliberately advance one child at a time.
/// That preserves the recursive implementation's left-to-right failure order: an invalid earlier
/// child still wins over a malformed later grammar slot.
enum RenderJob<'a> {
    Visit(&'a RuntimeObservationValue),
    FinishLambda {
        rule: &'a GrammarRule,
        binder: String,
        body_ident: String,
        fresh_name: String,
    },
    ContinueBag {
        entries: &'a [(RuntimeObservationValue, usize)],
        index: usize,
        rendered: Vec<String>,
        pending_count: Option<usize>,
        separator: &'a str,
        delimiters: Option<&'a (String, String)>,
    },
    ContinueContext {
        constructor: &'a str,
        children: &'a [RuntimeObservationValue],
        context: &'a [TermParam],
        pattern: &'a [SyntaxExpr],
        param_index: usize,
        child_index: usize,
        slots: BTreeMap<String, RenderId>,
        pending_name: Option<String>,
    },
    ContinueOldStyle {
        constructor: &'a str,
        children: &'a [RuntimeObservationValue],
        items: &'a [GrammarItem],
        item_index: usize,
        child_index: usize,
        tokens: Vec<RenderId>,
        pending_child: bool,
    },
}

impl SurfaceRenderer {
    /// Build the renderer from a language's `definition_source()` (the same
    /// reconstruction the generated invocation bodies use).
    pub fn for_definition_source(source: &str) -> Result<Self, String> {
        let def = reconstruct_language_def(source)
            .map_err(|err| format!("definition source did not reconstruct: {err:?}"))?;
        Ok(Self { def })
    }

    /// Render one observation value as parseable surface syntax.
    pub fn render(&self, value: &RuntimeObservationValue) -> Result<String, String> {
        let mut free_names = FreeNameTable::default();
        collect_free_names(value, &mut free_names)?;
        let mut fresh = FreshNames::new(free_names.used.clone());
        self.render_value(value, &mut Vec::new(), &free_names, &mut fresh)
    }

    /// The language's UNIQUE single-binder production (the `^lambda` de-reflection
    /// target): a judgement-style rule whose term context is exactly one `Abstraction`
    /// parameter (Lambda's `Lam`, Ambient's `PNew`). Ambiguity or absence is a typed
    /// error — `^lambda` erases which constructor it was, so only a unique target is
    /// sound.
    fn unique_binder_rule(&self) -> Result<&GrammarRule, String> {
        let mut candidates = self.def.terms.iter().filter(|rule| {
            matches!(rule.term_context.as_deref(), Some([TermParam::Abstraction { .. }]))
        });
        let first = candidates.next().ok_or_else(|| {
            format!(
                "language {} has no single-abstraction production to de-reflect ^lambda into",
                self.def.name
            )
        })?;
        if let Some(second) = candidates.next() {
            return Err(format!(
                "language {} has multiple single-abstraction productions ({} and {}) — \
                 ^lambda erases the constructor, so de-reflection is ambiguous",
                self.def.name, first.label, second.label
            ));
        }
        Ok(first)
    }

    /// The language's UNIQUE `HashBag` collection production (the bag-soup
    /// de-reflection target, e.g. Ambient's `PPar`).
    fn unique_bag_rule(&self) -> Result<(&GrammarRule, &str, Option<&(String, String)>), String> {
        let mut candidates = self
            .def
            .terms
            .iter()
            .filter_map(|rule| match rule.items.as_slice() {
                [GrammarItem::Collection {
                    coll_type: mettail_ast::types::CollectionType::HashBag,
                    separator,
                    delimiters,
                    ..
                }] => Some((rule, separator.as_str(), delimiters.as_ref())),
                _ => None,
            });
        let first = candidates.next().ok_or_else(|| {
            format!(
                "language {} has no HashBag production to de-reflect a bag soup into",
                self.def.name
            )
        })?;
        if let Some((second, _, _)) = candidates.next() {
            return Err(format!(
                "language {} has multiple HashBag productions ({} and {}) — bag de-reflection \
                 is ambiguous",
                self.def.name, first.0.label, second.label
            ));
        }
        Ok(first)
    }

    /// Render one value under `binders` (the generated fresh names of the enclosing
    /// `^lambda` scopes, outermost first).
    fn render_value<'a>(
        &'a self,
        value: &'a RuntimeObservationValue,
        binders: &mut Vec<String>,
        free_names: &FreeNameTable,
        fresh: &mut FreshNames,
    ) -> Result<String, String> {
        let mut arena = RenderArena::new();
        let mut results = Vec::<RenderId>::new();
        let mut jobs = vec![RenderJob::Visit(value)];

        while let Some(job) = jobs.pop() {
            match job {
                RenderJob::Visit(value) => match value {
                    RuntimeObservationValue::Term { constructor, children } => {
                        match constructor.as_str() {
                            FREE_VAR_REFLECT_LABEL => {
                                let [leaf] = children.as_slice() else {
                                    return Err(format!(
                                        "^free carries one debug leaf: {children:?}"
                                    ));
                                };
                                let RuntimeObservationValue::Term {
                                    constructor: debug,
                                    children: none,
                                } = leaf
                                else {
                                    return Err(format!("^free leaf is a nullary tag: {leaf:?}"));
                                };
                                if !none.is_empty() {
                                    return Err(format!("^free leaf is nullary: {leaf:?}"));
                                }
                                let name =
                                    free_names.by_debug.get(debug).cloned().ok_or_else(|| {
                                        format!(
                                            "^free({debug}) missed the collection pass — renderer \
                                             defect"
                                        )
                                    })?;
                                results.push(arena.text(Cow::Owned(name)));
                            },
                            BOUND_VAR_REFLECT_LABEL => {
                                let [peano] = children.as_slice() else {
                                    return Err(format!(
                                        "^bound carries one Peano leaf: {children:?}"
                                    ));
                                };
                                let depth = peano_value(peano)?;
                                let name = depth
                                    .checked_add(1)
                                    .and_then(|offset| binders.len().checked_sub(offset))
                                    .and_then(|index| binders.get(index))
                                    .cloned()
                                    .ok_or_else(|| {
                                        format!(
                                            "^bound({depth}) exceeds the {} enclosing binder \
                                             scope(s) — a dangling de Bruijn index",
                                            binders.len()
                                        )
                                    })?;
                                results.push(arena.text(Cow::Owned(name)));
                            },
                            LAMBDA_REFLECT_LABEL => {
                                let [body] = children.as_slice() else {
                                    return Err(format!("^lambda carries one body: {children:?}"));
                                };
                                let rule = self.unique_binder_rule()?;
                                let Some([TermParam::Abstraction { binder, body: body_ident, .. }]) =
                                    rule.term_context.as_deref()
                                else {
                                    unreachable!("unique_binder_rule guarantees the shape");
                                };
                                let fresh_name = fresh.generate();
                                binders.push(fresh_name.clone());
                                jobs.push(RenderJob::FinishLambda {
                                    rule,
                                    binder: binder.to_string(),
                                    body_ident: body_ident.to_string(),
                                    fresh_name,
                                });
                                jobs.push(RenderJob::Visit(body));
                            },
                            MULTILAMBDA_REFLECT_LABEL => {
                                return Err(
                                    "^multilambda de-reflection is not supported (no production \
                                     language reflects multi-binder scopes yet)"
                                        .to_string(),
                                );
                            },
                            _ => {
                                let rule = self
                                    .def
                                    .terms
                                    .iter()
                                    .find(|rule| rule.label == *constructor)
                                    .ok_or_else(|| {
                                        format!(
                                            "constructor {constructor} has no production in \
                                             language {}",
                                            self.def.name
                                        )
                                    })?;
                                if let (Some(context), Some(pattern)) =
                                    (rule.term_context.as_deref(), rule.syntax_pattern.as_deref())
                                {
                                    jobs.push(RenderJob::ContinueContext {
                                        constructor,
                                        children,
                                        context,
                                        pattern,
                                        param_index: 0,
                                        child_index: 0,
                                        slots: BTreeMap::new(),
                                        pending_name: None,
                                    });
                                } else {
                                    jobs.push(RenderJob::ContinueOldStyle {
                                        constructor,
                                        children,
                                        items: &rule.items,
                                        item_index: 0,
                                        child_index: 0,
                                        tokens: Vec::with_capacity(rule.items.len()),
                                        pending_child: false,
                                    });
                                }
                            },
                        }
                    },
                    RuntimeObservationValue::Bag(entries) => {
                        let (_rule, separator, delimiters) = self.unique_bag_rule()?;
                        jobs.push(RenderJob::ContinueBag {
                            entries,
                            index: 0,
                            rendered: Vec::with_capacity(entries.len()),
                            pending_count: None,
                            separator,
                            delimiters,
                        });
                    },
                    RuntimeObservationValue::Int(value) => {
                        results.push(arena.text(Cow::Owned(value.to_string())));
                    },
                    RuntimeObservationValue::Bool(value) => {
                        results.push(arena.text(Cow::Owned(value.to_string())));
                    },
                    other => {
                        return Err(format!(
                            "observation shape has no surface de-reflection: {other:?}"
                        ));
                    },
                },
                RenderJob::FinishLambda { rule, binder, body_ident, fresh_name } => {
                    let body = results
                        .pop()
                        .expect("a completed lambda body leaves one render result");
                    binders
                        .pop()
                        .expect("a completed lambda body has one enclosing binder");
                    let pattern = rule.syntax_pattern.as_deref().ok_or_else(|| {
                        format!("binder production {} has no syntax pattern", rule.label)
                    })?;
                    let mut tokens = Vec::with_capacity(pattern.len());
                    for item in pattern {
                        match item {
                            SyntaxExpr::Literal(text) => {
                                tokens.push(arena.text(Cow::Borrowed(text.trim())));
                            },
                            SyntaxExpr::Param(ident) if ident.to_string() == binder => {
                                tokens.push(arena.text(Cow::Owned(fresh_name.clone())));
                            },
                            SyntaxExpr::Param(ident) if ident.to_string() == body_ident => {
                                tokens.push(body);
                            },
                            SyntaxExpr::Param(other) => {
                                return Err(format!(
                                    "binder production {} references unknown parameter {other}",
                                    rule.label
                                ));
                            },
                            SyntaxExpr::Op(_) => {
                                return Err(format!(
                                    "binder production {} uses pattern ops — unsupported for \
                                     de-reflection",
                                    rule.label
                                ));
                            },
                            SyntaxExpr::TokenKind { .. } | SyntaxExpr::GuestBody { .. } => {
                                return Err(format!(
                                    "binder production {} uses a token/guest-body capture — \
                                     unsupported for de-reflection",
                                    rule.label
                                ));
                            },
                        }
                    }
                    results.push(arena.join(tokens, Cow::Borrowed(" ")));
                },
                RenderJob::ContinueBag {
                    entries,
                    index,
                    mut rendered,
                    pending_count,
                    separator,
                    delimiters,
                } => {
                    if let Some(count) = pending_count {
                        let element = arena.materialize(
                            results
                                .pop()
                                .expect("a completed bag element leaves one render result"),
                        );
                        rendered.extend(std::iter::repeat_n(element, count));
                    }
                    if index == entries.len() {
                        rendered.sort();
                        let joined = rendered.join(&format!(" {separator} "));
                        let text = match delimiters {
                            Some((open, close)) if rendered.is_empty() => {
                                format!("{open}{close}")
                            },
                            Some((open, close)) => format!("{open} {joined} {close}"),
                            None => joined,
                        };
                        results.push(arena.text(Cow::Owned(text)));
                    } else {
                        let (element, count) = &entries[index];
                        jobs.push(RenderJob::ContinueBag {
                            entries,
                            index: index + 1,
                            rendered,
                            pending_count: Some(*count),
                            separator,
                            delimiters,
                        });
                        jobs.push(RenderJob::Visit(element));
                    }
                },
                RenderJob::ContinueContext {
                    constructor,
                    children,
                    context,
                    pattern,
                    mut param_index,
                    mut child_index,
                    mut slots,
                    pending_name,
                } => {
                    if let Some(name) = pending_name {
                        slots.insert(
                            name,
                            results
                                .pop()
                                .expect("a completed constructor child leaves one render result"),
                        );
                    }
                    loop {
                        if param_index == context.len() {
                            if child_index != children.len() {
                                return Err(format!(
                                    "{constructor} has more children than production parameters \
                                     ({})",
                                    children.len()
                                ));
                            }
                            let mut tokens = Vec::with_capacity(pattern.len());
                            for item in pattern {
                                match item {
                                    SyntaxExpr::Literal(text) => {
                                        tokens.push(arena.text(Cow::Borrowed(text.trim())));
                                    },
                                    SyntaxExpr::Param(ident) => {
                                        let key = ident.to_string();
                                        let rendered =
                                            slots.get(&key).copied().ok_or_else(|| {
                                                format!(
                                                    "{constructor} pattern references unknown \
                                                 parameter {ident}"
                                                )
                                            })?;
                                        tokens.push(rendered);
                                    },
                                    SyntaxExpr::Op(_) => {
                                        return Err(format!(
                                            "{constructor} uses pattern ops — unsupported for \
                                             de-reflection"
                                        ));
                                    },
                                    SyntaxExpr::TokenKind { .. } | SyntaxExpr::GuestBody { .. } => {
                                        return Err(format!(
                                            "{constructor} uses a token/guest-body capture — \
                                             unsupported for de-reflection"
                                        ));
                                    },
                                }
                            }
                            results.push(arena.join(tokens, Cow::Borrowed(" ")));
                            break;
                        }

                        match &context[param_index] {
                            TermParam::Simple { name, .. } => {
                                let child = children.get(child_index).ok_or_else(|| {
                                    format!("{constructor} is missing a child for parameter {name}")
                                })?;
                                param_index += 1;
                                child_index += 1;
                                jobs.push(RenderJob::ContinueContext {
                                    constructor,
                                    children,
                                    context,
                                    pattern,
                                    param_index,
                                    child_index,
                                    slots,
                                    pending_name: Some(name.to_string()),
                                });
                                jobs.push(RenderJob::Visit(child));
                                break;
                            },
                            other => {
                                return Err(format!(
                                    "{constructor} carries a non-simple parameter {other:?} — \
                                     such constructors reflect as ^lambda, never by label"
                                ));
                            },
                        }
                    }
                },
                RenderJob::ContinueOldStyle {
                    constructor,
                    children,
                    items,
                    mut item_index,
                    child_index,
                    mut tokens,
                    pending_child,
                } => {
                    if pending_child {
                        tokens.push(
                            results
                                .pop()
                                .expect("a completed old-style child leaves one render result"),
                        );
                    }
                    loop {
                        if item_index == items.len() {
                            if child_index != children.len() {
                                return Err(format!(
                                    "{constructor} has more children than production slots ({})",
                                    children.len()
                                ));
                            }
                            results.push(arena.join(tokens, Cow::Borrowed(" ")));
                            break;
                        }

                        match &items[item_index] {
                            GrammarItem::Terminal(text) => {
                                tokens.push(arena.text(Cow::Borrowed(text.trim())));
                                item_index += 1;
                            },
                            GrammarItem::NonTerminal { .. } => {
                                let child = children.get(child_index).ok_or_else(|| {
                                    format!(
                                        "{constructor} is missing a child for a nonterminal slot"
                                    )
                                })?;
                                jobs.push(RenderJob::ContinueOldStyle {
                                    constructor,
                                    children,
                                    items,
                                    item_index: item_index + 1,
                                    child_index: child_index + 1,
                                    tokens,
                                    pending_child: true,
                                });
                                jobs.push(RenderJob::Visit(child));
                                break;
                            },
                            GrammarItem::Binder { .. } => {
                                return Err(format!(
                                    "{constructor} declares an old-style binder item — such \
                                     constructors reflect as ^lambda, never by label"
                                ));
                            },
                            GrammarItem::Collection { .. } => {
                                let child = children.get(child_index).ok_or_else(|| {
                                    format!("{constructor} is missing its collection child")
                                })?;
                                jobs.push(RenderJob::ContinueOldStyle {
                                    constructor,
                                    children,
                                    items,
                                    item_index: item_index + 1,
                                    child_index: child_index + 1,
                                    tokens,
                                    pending_child: true,
                                });
                                jobs.push(RenderJob::Visit(child));
                                break;
                            },
                        }
                    }
                },
            }
        }

        let [root] = results.as_slice() else {
            panic!("surface renderer PDA ended with {} result(s), expected one", results.len());
        };
        debug_assert!(binders.is_empty(), "surface renderer leaked binder frames");
        Ok(arena.materialize(*root))
    }
}

/// Decode a reflected Peano numeral `S^n(Z)`.
fn peano_value(value: &RuntimeObservationValue) -> Result<usize, String> {
    let mut cursor = value;
    let mut depth = 0usize;
    loop {
        match cursor {
            RuntimeObservationValue::Term { constructor, children }
                if constructor == PEANO_ZERO_REFLECT_LABEL && children.is_empty() =>
            {
                return Ok(depth);
            },
            RuntimeObservationValue::Term { constructor, children }
                if constructor == PEANO_SUCC_REFLECT_LABEL && children.len() == 1 =>
            {
                depth += 1;
                cursor = &children[0];
            },
            other => return Err(format!("not a reflected Peano numeral: {other:?}")),
        }
    }
}

/// Pass 1 — assign a collision-free surface name to every distinct `^free` variable in
/// the value (AM-6c: the fresh-binder generator then avoids ALL of them, so a bound
/// binder can never re-capture a free variable at parse time).
fn collect_free_names(
    value: &RuntimeObservationValue,
    table: &mut FreeNameTable,
) -> Result<(), String> {
    let mut work = vec![value];
    while let Some(value) = work.pop() {
        match value {
            RuntimeObservationValue::Term { constructor, children }
                if constructor == FREE_VAR_REFLECT_LABEL =>
            {
                let [RuntimeObservationValue::Term { constructor: debug, children: none }] =
                    children.as_slice()
                else {
                    return Err(format!("^free carries one nullary debug leaf: {children:?}"));
                };
                if !none.is_empty() {
                    return Err(format!("^free debug leaf is nullary: {children:?}"));
                }
                table.assign(debug);
            },
            RuntimeObservationValue::Term { children, .. } => {
                work.extend(children.iter().rev());
            },
            RuntimeObservationValue::List(items)
            | RuntimeObservationValue::Tuple(items)
            | RuntimeObservationValue::Set(items) => {
                work.extend(items.iter().rev());
            },
            RuntimeObservationValue::Bag(entries) => {
                work.extend(entries.iter().rev().map(|(element, _)| element));
            },
            RuntimeObservationValue::Map(entries) => {
                for (key, value) in entries.iter().rev() {
                    work.push(value);
                    work.push(key);
                }
            },
            _ => {},
        }
    }
    Ok(())
}

/// Whether de-reflection applies to this observation value at all: constructor terms and
/// bag soups have surface productions; scalar/opaque observations keep the raw display.
pub fn is_surface_renderable_shape(value: &RuntimeObservationValue) -> bool {
    matches!(value, RuntimeObservationValue::Term { .. } | RuntimeObservationValue::Bag(_))
}

#[cfg(test)]
#[path = "../tests/support/observation_surface_recursive_oracle.rs"]
mod recursive_oracle;
