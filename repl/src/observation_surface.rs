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
                self.used.insert(candidate.clone());
                return candidate;
            }
        }
    }
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
            matches!(
                rule.term_context.as_deref(),
                Some([TermParam::Abstraction { .. }])
            )
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
        let mut candidates = self.def.terms.iter().filter_map(|rule| match rule.items.as_slice() {
            [GrammarItem::Collection {
                coll_type: mettail_ast::types::CollectionType::HashBag,
                separator,
                delimiters,
                ..
            }] => Some((rule, separator.as_str(), delimiters.as_ref())),
            _ => None,
        });
        let first = candidates.next().ok_or_else(|| {
            format!("language {} has no HashBag production to de-reflect a bag soup into", self.def.name)
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
    fn render_value(
        &self,
        value: &RuntimeObservationValue,
        binders: &mut Vec<String>,
        free_names: &FreeNameTable,
        fresh: &mut FreshNames,
    ) -> Result<String, String> {
        match value {
            RuntimeObservationValue::Term { constructor, children } => {
                match constructor.as_str() {
                    FREE_VAR_REFLECT_LABEL => {
                        let [leaf] = children.as_slice() else {
                            return Err(format!("^free carries one debug leaf: {children:?}"));
                        };
                        let RuntimeObservationValue::Term { constructor: debug, children: none } =
                            leaf
                        else {
                            return Err(format!("^free leaf is a nullary tag: {leaf:?}"));
                        };
                        if !none.is_empty() {
                            return Err(format!("^free leaf is nullary: {leaf:?}"));
                        }
                        free_names.by_debug.get(debug).cloned().ok_or_else(|| {
                            format!("^free({debug}) missed the collection pass — renderer defect")
                        })
                    },
                    BOUND_VAR_REFLECT_LABEL => {
                        let [peano] = children.as_slice() else {
                            return Err(format!("^bound carries one Peano leaf: {children:?}"));
                        };
                        let depth = peano_value(peano)?;
                        binders
                            .iter()
                            .rev()
                            .nth(depth)
                            .cloned()
                            .ok_or_else(|| {
                                format!(
                                    "^bound({depth}) exceeds the {} enclosing binder scope(s) — \
                                     a dangling de Bruijn index",
                                    binders.len()
                                )
                            })
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
                        let body_text = self.render_value(body, binders, free_names, fresh)?;
                        binders.pop();
                        let pattern = rule.syntax_pattern.as_deref().ok_or_else(|| {
                            format!("binder production {} has no syntax pattern", rule.label)
                        })?;
                        let mut tokens = Vec::with_capacity(pattern.len());
                        for item in pattern {
                            match item {
                                SyntaxExpr::Literal(text) => tokens.push(text.trim().to_string()),
                                SyntaxExpr::Param(ident) if ident == binder => {
                                    tokens.push(fresh_name.clone())
                                },
                                SyntaxExpr::Param(ident) if ident == body_ident => {
                                    tokens.push(body_text.clone())
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
                            }
                        }
                        Ok(tokens.join(" "))
                    },
                    MULTILAMBDA_REFLECT_LABEL => Err(
                        "^multilambda de-reflection is not supported (no production language \
                         reflects multi-binder scopes yet)"
                            .to_string(),
                    ),
                    _ => self.render_constructor(constructor, children, binders, free_names, fresh),
                }
            },
            RuntimeObservationValue::Bag(entries) => {
                let (rule, separator, delimiters) = self.unique_bag_rule()?;
                let _ = rule;
                let mut rendered = Vec::with_capacity(entries.len());
                for (element, count) in entries {
                    let text = self.render_value(element, binders, free_names, fresh)?;
                    for _ in 0..*count {
                        rendered.push(text.clone());
                    }
                }
                // The deterministic print-order pin: multiset iteration order is
                // hash-dependent, so rendered elements are SORTED (byte order).
                rendered.sort();
                let joined = rendered.join(&format!(" {separator} "));
                match delimiters {
                    Some((open, close)) => {
                        if rendered.is_empty() {
                            Ok(format!("{open}{close}"))
                        } else {
                            Ok(format!("{open} {joined} {close}"))
                        }
                    },
                    None => Ok(joined),
                }
            },
            RuntimeObservationValue::Int(value) => Ok(value.to_string()),
            RuntimeObservationValue::Bool(value) => Ok(value.to_string()),
            other => Err(format!("observation shape has no surface de-reflection: {other:?}")),
        }
    }

    /// Render an ordinary constructor node through its grammar production.
    fn render_constructor(
        &self,
        constructor: &str,
        children: &[RuntimeObservationValue],
        binders: &mut Vec<String>,
        free_names: &FreeNameTable,
        fresh: &mut FreshNames,
    ) -> Result<String, String> {
        let rule = self
            .def
            .terms
            .iter()
            .find(|rule| rule.label == constructor)
            .ok_or_else(|| {
                format!("constructor {constructor} has no production in language {}", self.def.name)
            })?;

        // Judgement-style production: map term-context parameters to children
        // positionally, then emit the syntax pattern.
        if let (Some(context), Some(pattern)) =
            (rule.term_context.as_deref(), rule.syntax_pattern.as_deref())
        {
            let mut slots: BTreeMap<String, String> = BTreeMap::new();
            let mut child_iter = children.iter();
            for param in context {
                match param {
                    TermParam::Simple { name, .. } => {
                        let child = child_iter.next().ok_or_else(|| {
                            format!("{constructor} is missing a child for parameter {name}")
                        })?;
                        let text = self.render_value(child, binders, free_names, fresh)?;
                        slots.insert(name.to_string(), text);
                    },
                    other => {
                        return Err(format!(
                            "{constructor} carries a non-simple parameter {other:?} — such \
                             constructors reflect as ^lambda, never by label"
                        ));
                    },
                }
            }
            if child_iter.next().is_some() {
                return Err(format!(
                    "{constructor} has more children than production parameters ({})",
                    children.len()
                ));
            }
            let mut tokens = Vec::with_capacity(pattern.len());
            for item in pattern {
                match item {
                    SyntaxExpr::Literal(text) => tokens.push(text.trim().to_string()),
                    SyntaxExpr::Param(ident) => {
                        let text = slots.get(&ident.to_string()).ok_or_else(|| {
                            format!("{constructor} pattern references unknown parameter {ident}")
                        })?;
                        tokens.push(text.clone());
                    },
                    SyntaxExpr::Op(_) => {
                        return Err(format!(
                            "{constructor} uses pattern ops — unsupported for de-reflection"
                        ));
                    },
                }
            }
            return Ok(tokens.join(" "));
        }

        // Old-style (BNFC) production: emit terminals verbatim; each NonTerminal consumes
        // the next child.
        let mut tokens = Vec::with_capacity(rule.items.len());
        let mut child_iter = children.iter();
        for item in &rule.items {
            match item {
                GrammarItem::Terminal(text) => tokens.push(text.trim().to_string()),
                GrammarItem::NonTerminal { .. } => {
                    let child = child_iter.next().ok_or_else(|| {
                        format!("{constructor} is missing a child for a nonterminal slot")
                    })?;
                    tokens.push(self.render_value(child, binders, free_names, fresh)?);
                },
                GrammarItem::Binder { .. } => {
                    return Err(format!(
                        "{constructor} declares an old-style binder item — such constructors \
                         reflect as ^lambda, never by label"
                    ));
                },
                GrammarItem::Collection { .. } => {
                    let child = child_iter.next().ok_or_else(|| {
                        format!("{constructor} is missing its collection child")
                    })?;
                    tokens.push(self.render_value(child, binders, free_names, fresh)?);
                },
            }
        }
        if child_iter.next().is_some() {
            return Err(format!(
                "{constructor} has more children than production slots ({})",
                children.len()
            ));
        }
        Ok(tokens.join(" "))
    }
}

/// Decode a reflected Peano numeral `S^n(Z)`.
fn peano_value(value: &RuntimeObservationValue) -> Result<usize, String> {
    match value {
        RuntimeObservationValue::Term { constructor, children }
            if constructor == PEANO_ZERO_REFLECT_LABEL && children.is_empty() =>
        {
            Ok(0)
        },
        RuntimeObservationValue::Term { constructor, children }
            if constructor == PEANO_SUCC_REFLECT_LABEL && children.len() == 1 =>
        {
            Ok(1 + peano_value(&children[0])?)
        },
        other => Err(format!("not a reflected Peano numeral: {other:?}")),
    }
}

/// Pass 1 — assign a collision-free surface name to every distinct `^free` variable in
/// the value (AM-6c: the fresh-binder generator then avoids ALL of them, so a bound
/// binder can never re-capture a free variable at parse time).
fn collect_free_names(
    value: &RuntimeObservationValue,
    table: &mut FreeNameTable,
) -> Result<(), String> {
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
            Ok(())
        },
        RuntimeObservationValue::Term { children, .. } => {
            children.iter().try_for_each(|child| collect_free_names(child, table))
        },
        RuntimeObservationValue::List(items)
        | RuntimeObservationValue::Tuple(items)
        | RuntimeObservationValue::Set(items) => {
            items.iter().try_for_each(|item| collect_free_names(item, table))
        },
        RuntimeObservationValue::Bag(entries) => entries
            .iter()
            .try_for_each(|(element, _)| collect_free_names(element, table)),
        RuntimeObservationValue::Map(entries) => entries.iter().try_for_each(|(key, value)| {
            collect_free_names(key, table)?;
            collect_free_names(value, table)
        }),
        _ => Ok(()),
    }
}

/// Whether de-reflection applies to this observation value at all: constructor terms and
/// bag soups have surface productions; scalar/opaque observations keep the raw display.
pub fn is_surface_renderable_shape(value: &RuntimeObservationValue) -> bool {
    matches!(
        value,
        RuntimeObservationValue::Term { .. } | RuntimeObservationValue::Bag(_)
    )
}
