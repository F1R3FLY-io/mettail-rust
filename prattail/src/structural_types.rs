//! Structural-type recognizer (OSLF substrate, Phase 2 `.0`-inert): compile a
//! grammar's ranked-tree constructor alphabet into a
//! [`SymbolicTreeAutomaton<AnyAlgebra>`](crate::sym_tree::SymbolicTreeAutomaton)
//! so structural refinement-type questions — *is this category inhabited?*, *do
//! these two structural patterns intersect / subtype?* — are decided **precisely**
//! by the tree-EBA (`sym_tree`) rather than by the string heuristic in
//! [`type_system::dispatch`](crate::type_system::dispatch).
//!
//! ## What this module is, and is not
//!
//! The live `tree_automaton::analyze_from_bundle` (category-reachability, no
//! payloads) and `type_system::SetTheoreticTypeSystem` (finite constructor-ranked
//! alphabet, `TreeAutomaton<BooleanWeight>`) both model a grammar's terms as a
//! *regular tree language*. `SetTheoreticTypeSystem` already decides emptiness /
//! intersection / subtype over that finite alphabet — but it has **no live
//! pipeline caller**, and its payloads are a single Boolean weight (a scalar leaf
//! is just "present"). This module is the `sym_tree` *generalization* of that
//! finite engine: the ranked alphabet is identical (rule label = constructor,
//! arity = number of structural children), but a scalar (payloaded) leaf now
//! carries a **symbolic payload guard** (an [`AnyPred`](crate::any_algebra::AnyPred)
//! over the leaf's [`Sort`](crate::any_algebra::Sort)), so the recognizer extends
//! cleanly from finite alphabets to infinite symbolic payloads.
//!
//! ## `.0`-inert contract
//!
//! At `.0` this module is **always compiled** but has **no live caller** — it
//! produces a [`StructuralVerdict`] (per-category emptiness + a minimal witness
//! term) that is proven, by `prattail/tests/sym_tree_structural_snapshot.rs`, to
//! **agree category-for-category** with `SetTheoreticTypeSystem`'s `is_empty`
//! verdict over the *same* ranked alphabet. The live flip — routing structural
//! refinement dispatch through this recognizer and firing RT03 — is `.1`
//! (`type_system::dispatch::analyze_refinement_dispatch_structural`, gated on
//! `sym-tree-structural`).
//!
//! ## Payload partition (why the verdict agrees)
//!
//! A payloaded leaf carries the guard `Some(elem.true_pred())` (the whole sort)
//! and a structural constructor carries `None`. The `True` payload is *always*
//! satisfiable, so it never prunes a derivation — emptiness of a category is
//! decided purely by the constructor reachability, exactly as in the finite
//! engine. This is the single-class (`True`) payload partition under which the
//! Coq `SymTreeWiringSound.v` proves sym_tree's verdict equals the
//! finite-tree-automaton verdict.

use std::collections::{HashMap, HashSet};

use crate::any_algebra::{AnyAlgebra, AnyDomain, SortRegistry};
use crate::sym_tree::{SymTerm, SymbolicTreeAutomaton, TreeAlgebra, TreeTrans};
use crate::symbolic::BooleanAlgebra;
use crate::pipeline::CategoryInfo;
use crate::SyntaxItemSpec;

/// A grammar syntax rule: `(label, category, syntax_items)` — the same shape the
/// rest of the pipeline carries (`ParserBundle::all_syntax`).
pub type SyntaxRule = (String, String, Vec<SyntaxItemSpec>);

// ══════════════════════════════════════════════════════════════════════════════
// Ranked alphabet
// ══════════════════════════════════════════════════════════════════════════════

/// The ranked-tree alphabet derived from a grammar: each rule's `label` is a
/// constructor whose arity is the number of **structural** (non-terminal /
/// binder / collection-element) children in its body, and whose category is the
/// category that owns the rule. A constructor is *payloaded* iff its owning
/// category resolves to a scalar [`Sort`](crate::any_algebra::Sort) (an integer,
/// bool, string, float, big-int, big-rat, or fixed-point leaf) — such a leaf
/// carries a symbolic payload guard; every other constructor is structural.
#[derive(Clone, Debug, Default)]
pub struct RankedAlphabet {
    /// Constructor → arity (number of structural children).
    pub arities: HashMap<String, usize>,
    /// Constructor → owning category.
    pub category_of: HashMap<String, String>,
    /// Constructor → the categories of its structural children, in order.
    pub child_categories: HashMap<String, Vec<String>>,
    /// Constructors whose owning category is a scalar (payloaded) sort.
    pub payloaded: HashSet<String>,
    /// Every category name that owns at least one rule or is referenced.
    pub categories: HashSet<String>,
}

/// Collect the categories of the **structural** children of a rule body, in
/// left-to-right order.
///
/// This mirrors `tree_automaton::collect_nonterminal_children`
/// (tree_automaton.rs:1016) — the single source of truth for "what counts as a
/// structural child of a constructor" — but returns the child *category names*
/// (rather than tree-automaton state ids), because this module indexes states by
/// category. `Terminal`, `IdentCapture`, and `BinderCollection` contribute no
/// child; `NonTerminal` / `Binder` / `Collection` (element category) and the
/// nesting wrappers (`Optional` / `Sep` / `Map` / `Zip`) recurse exactly as the
/// finite engine does, so the two alphabets are arity-identical.
///
/// Exposed (`pub`) so the agreement snapshot
/// (`prattail/tests/sym_tree_structural_snapshot.rs`) can build the finite
/// `SetTheoreticTypeSystem` bridge over the *same* arity logic as this
/// recognizer — the agreement is only meaningful if both sides derive the
/// alphabet identically.
pub fn collect_structural_child_categories(
    items: &[SyntaxItemSpec],
    out: &mut Vec<String>,
) {
    for item in items {
        match item {
            SyntaxItemSpec::NonTerminal { category, .. } => out.push(category.clone()),
            SyntaxItemSpec::Binder { category, .. } => out.push(category.clone()),
            SyntaxItemSpec::Collection { element_category, .. } => {
                out.push(element_category.clone())
            },
            SyntaxItemSpec::Optional { inner } => {
                collect_structural_child_categories(inner, out)
            },
            SyntaxItemSpec::Sep { body, .. } => {
                collect_structural_child_categories(std::slice::from_ref(body.as_ref()), out)
            },
            SyntaxItemSpec::Map { body_items } => {
                collect_structural_child_categories(body_items, out)
            },
            SyntaxItemSpec::Zip { body, .. } => {
                collect_structural_child_categories(std::slice::from_ref(body.as_ref()), out)
            },
            // Terminal, IdentCapture, BinderCollection — no structural child.
            _ => {},
        }
    }
}

/// Whether a category resolves to a scalar [`Sort`](crate::any_algebra::Sort)
/// (and hence its constructors are payloaded leaves).
///
/// Under the `any-algebra-carrier` feature this defers to
/// [`any_algebra::sort_of_category`](crate::any_algebra::sort_of_category) — the
/// *exact* `NativeKind::from_syn_type` classification the parser uses — so the
/// scalar/structural split tracks the parser precisely. Without that feature the
/// module is still always compiled, so it falls back to a syntactic classifier
/// over the stored `native_type` path string that mirrors the same `NativeKind`
/// → scalar mapping (last path segment).
fn category_is_scalar(ci: &CategoryInfo) -> bool {
    #[cfg(feature = "any-algebra-carrier")]
    {
        crate::any_algebra::sort_of_category(ci).is_some()
    }
    #[cfg(not(feature = "any-algebra-carrier"))]
    {
        category_is_scalar_by_string(ci)
    }
}

/// Feature-free scalar classifier over the stored `native_type` path string.
///
/// `CategoryInfo::native_type` is the bridge's full-path string
/// (`native_type_to_full_string` — e.g. `"i32"`,
/// `"mettail_runtime::CanonicalBigRat"`, `"Vec < Proc >"`). A category is scalar
/// iff its type's **last path segment** is one of the known scalar leaves — the
/// same segments `NativeKind::from_syn_type` recognizes (every bounded-integer
/// width, `bool`, `str`, `f32`/`f64`, and the three canonical numeric wrappers).
/// A container/`None`/user-ADT category is structural. This is only the
/// `cfg(not(any-algebra-carrier))` fallback; the carrier path is authoritative.
#[cfg(not(feature = "any-algebra-carrier"))]
fn category_is_scalar_by_string(ci: &CategoryInfo) -> bool {
    let type_str = match ci.native_type.as_deref() {
        Some(s) => s,
        None => return false,
    };
    // Take the last `::`-separated segment, then the bare identifier (drop any
    // generic args / whitespace the full-string form may carry).
    let last_segment = type_str
        .rsplit("::")
        .next()
        .unwrap_or(type_str)
        .trim();
    let ident = last_segment
        .split(['<', ' ', '('])
        .next()
        .unwrap_or(last_segment)
        .trim();
    matches!(
        ident,
        "i8" | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "bool"
            | "str"
            | "String"
            | "f32"
            | "f64"
            | "CanonicalBigInt"
            | "CanonicalBigRat"
            | "CanonicalFixedPoint"
    )
}

/// Build the [`RankedAlphabet`] from a grammar's rules and categories.
///
/// Reuses [`collect_structural_child_categories`] (the shared arity logic with
/// the finite tree-automaton engine) so the alphabet is arity-identical, and
/// classifies each category's scalar-ness via [`category_is_scalar`].
pub fn ranked_alphabet(all_syntax: &[SyntaxRule], categories: &[CategoryInfo]) -> RankedAlphabet {
    let mut alpha = RankedAlphabet {
        arities: HashMap::with_capacity(all_syntax.len()),
        category_of: HashMap::with_capacity(all_syntax.len()),
        child_categories: HashMap::with_capacity(all_syntax.len()),
        payloaded: HashSet::new(),
        categories: HashSet::with_capacity(categories.len()),
    };

    let scalar_categories: HashSet<String> = categories
        .iter()
        .filter(|ci| category_is_scalar(ci))
        .map(|ci| ci.name.clone())
        .collect();

    for ci in categories {
        alpha.categories.insert(ci.name.clone());
    }

    for (label, category, items) in all_syntax {
        let mut child_cats = Vec::new();
        collect_structural_child_categories(items, &mut child_cats);
        // Track any referenced child categories too (defensive: a child category
        // that has no rules of its own is an empty category, and must still be a
        // state so its emptiness is decided).
        for c in &child_cats {
            alpha.categories.insert(c.clone());
        }
        alpha.categories.insert(category.clone());
        let arity = child_cats.len();
        alpha.arities.insert(label.clone(), arity);
        alpha.category_of.insert(label.clone(), category.clone());
        alpha.child_categories.insert(label.clone(), child_cats);
        if scalar_categories.contains(category) {
            alpha.payloaded.insert(label.clone());
        }
    }

    alpha
}

// ══════════════════════════════════════════════════════════════════════════════
// Tree algebra + per-category automaton
// ══════════════════════════════════════════════════════════════════════════════

/// The canonical scalar leaf decider for structural recognition.
///
/// Every payloaded leaf carries the trivially-satisfiable `True` guard, so the
/// concrete scalar algebra used to *decide* it is immaterial (all scalar leaves
/// decide `True ↦ satisfiable` and `False ↦ unsatisfiable` identically). We use
/// the `Bool` (KAT) leaf as the canonical decider — exactly as
/// `symbolic::analyze_from_bundle_carrier` (symbolic.rs:1974) does — built from
/// the default scalar [`SortRegistry`]. The empty `bool_atoms` list is
/// sufficient because `True`/`False` need no atoms.
fn canonical_leaf_decider() -> AnyAlgebra {
    let registry = SortRegistry::scalars(i64::MIN / 2, i64::MAX / 2, Vec::new());
    registry
        .get(crate::any_algebra::Sort::Bool)
        .expect("scalar registry always contains Sort::Bool")
        .clone()
}

/// Build the [`TreeAlgebra<AnyAlgebra>`] over a grammar's ranked alphabet, with
/// the canonical scalar leaf decider as its element algebra.
///
/// The resulting [`AnyAlgebra::Tree`] is the OSLF carrier's structural-type
/// algebra: tree predicates ([`TreePred`](crate::sym_tree::TreePred)) over this
/// algebra are decided (SAT / witness / intersect / complement) by the
/// deterministic bottom-up tree automaton in `sym_tree`.
pub fn build_tree_algebra(alpha: &RankedAlphabet) -> AnyAlgebra {
    let elem = canonical_leaf_decider();
    let arities = alpha.arities.clone();
    let payloaded = alpha.payloaded.clone();
    AnyAlgebra::Tree(Box::new(TreeAlgebra::new(elem, arities, payloaded)))
}

/// Build the [`SymbolicTreeAutomaton<AnyAlgebra>`] recognizing the terms of
/// `target_cat` over the grammar's ranked alphabet.
///
/// One automaton state is allocated per category (so a child slot's required
/// state is the child category's state); the `target_cat` state is the single
/// accepting state. Each rule `label : cat = body` becomes a transition
/// `label(child_states...) → cat` whose `payload_guard` is `Some(true_pred())`
/// for a payloaded (scalar) leaf and `None` for a structural constructor. The
/// `True` guard is always satisfiable, so emptiness of `target_cat` is decided
/// purely by constructor reachability — agreeing with the finite engine.
pub fn category_automaton(
    target_cat: &str,
    alpha: &RankedAlphabet,
    elem: &AnyAlgebra,
) -> SymbolicTreeAutomaton<AnyAlgebra> {
    let mut auto = SymbolicTreeAutomaton::new(elem.clone());

    // One state per category, deterministically indexed by a sorted category
    // list (stable across runs — no `HashSet` iteration order leaks into state
    // ids, so the witness term a category yields is reproducible).
    let mut cats: Vec<&String> = alpha.categories.iter().collect();
    cats.sort();
    let mut state_of: HashMap<&str, usize> = HashMap::with_capacity(cats.len());
    for c in &cats {
        let id = auto.add_state();
        state_of.insert(c.as_str(), id);
    }

    // The ranked alphabet (constructor → arity) is recorded on the automaton so
    // determinization / complement (used at `.1`) enumerate the right alphabet.
    for (label, &arity) in &alpha.arities {
        auto.register(label.clone(), arity);
    }

    if let Some(&acc) = state_of.get(target_cat) {
        auto.set_accepting(acc);
    }

    for (label, &arity) in &alpha.arities {
        let owning = match alpha.category_of.get(label) {
            Some(c) => c.as_str(),
            None => continue,
        };
        let target = match state_of.get(owning) {
            Some(&t) => t,
            None => continue,
        };
        let child_cats = match alpha.child_categories.get(label) {
            Some(cs) => cs,
            None => continue,
        };
        debug_assert_eq!(child_cats.len(), arity, "arity mismatch for `{label}`");
        // Map each structural child category to its state; if a child category is
        // unknown (never declared and never owns a rule) the rule cannot fire, so
        // skip the transition (its target stays unreachable via this rule).
        let mut child_states = Vec::with_capacity(arity);
        let mut resolvable = true;
        for cc in child_cats {
            match state_of.get(cc.as_str()) {
                Some(&s) => child_states.push(s),
                None => {
                    resolvable = false;
                    break;
                },
            }
        }
        if !resolvable {
            continue;
        }
        let payload_guard = if alpha.payloaded.contains(label) {
            // A payloaded (scalar) leaf carries the whole-sort guard.
            Some(elem.true_pred())
        } else {
            None
        };
        auto.add_transition(TreeTrans {
            constructor: label.clone(),
            payload_guard,
            child_states,
            target,
        });
    }

    auto
}

// ══════════════════════════════════════════════════════════════════════════════
// Verdict
// ══════════════════════════════════════════════════════════════════════════════

/// The structural-type verdict for a grammar: which categories are *empty*
/// (uninhabited — no well-formed term exists), and a minimal inhabiting witness
/// term for each *inhabited* category.
#[derive(Clone, Debug, Default)]
pub struct StructuralVerdict {
    /// Categories whose tree language is empty (uninhabited), sorted by name.
    pub empty_categories: Vec<String>,
    /// `(category, witness)` for each inhabited category, sorted by category.
    pub witnesses: Vec<(String, SymTerm<AnyDomain>)>,
}

/// Decide, for every category in the grammar, whether it is inhabited, returning
/// the [`StructuralVerdict`] (empty categories + a minimal witness per inhabited
/// category).
///
/// This is the `.0`-inert entry point: it is proven (by
/// `sym_tree_structural_snapshot`) to agree category-for-category with
/// [`SetTheoreticTypeSystem`](crate::type_system::SetTheoreticTypeSystem)'s
/// `is_empty` over the same ranked alphabet.
pub fn structural_verdict(
    all_syntax: &[SyntaxRule],
    categories: &[CategoryInfo],
) -> StructuralVerdict {
    let alpha = ranked_alphabet(all_syntax, categories);
    let elem = build_tree_algebra(&alpha);

    let mut cats: Vec<String> = alpha.categories.iter().cloned().collect();
    cats.sort();

    let mut empty_categories = Vec::new();
    let mut witnesses = Vec::new();
    for cat in &cats {
        let auto = category_automaton(cat, &alpha, &elem);
        if auto.is_empty() {
            empty_categories.push(cat.clone());
        } else if let Some(w) = auto.witness() {
            witnesses.push((cat.clone(), w));
        }
    }

    StructuralVerdict { empty_categories, witnesses }
}

// ══════════════════════════════════════════════════════════════════════════════
// Structural-pattern parsing + refined automata (the `.1` dispatch substrate)
// ══════════════════════════════════════════════════════════════════════════════

use crate::sym_tree::{SymbolicTreeAutomaton as StAuto, TreePred};
use crate::any_algebra::AnyPred;

/// Parse a refinement-type `predicate_repr` (the `Display` of a
/// [`RefinementPredicate`](mettail_ast)) for a `Structural` (term-pattern)
/// refinement into the structural tree pattern it constrains the refined
/// variable to, as a [`TreePred<AnyPred>`].
///
/// The supported structural surface forms are exactly what the macro AST can
/// render for a `TermEq`/`TermNeq` (`a == b` / `a != b`) plus the nested
/// constructor-application term syntax a refinement may use, e.g.
/// `l == cons(x, cons(y, t))`:
///
///   - `c(arg1, …, argN)`  → `TreePred::Node { constructor: c, payload_guard:
///     None, children: [parse(arg1), …, parse(argN)] }` (a structural node;
///     payload guards are not part of the surface term syntax, so children are
///     matched structurally and scalar leaves fall through to `Wild`);
///   - a bare identifier that is a **nullary constructor** of the grammar (per
///     `alpha`, arity 0) → the nullary `TreePred::Node` for it (e.g. `nil`);
///   - any other bare identifier (a pattern variable like `x`, `t`) →
///     `TreePred::Wild` (matches any subterm of the slot's category).
///
/// The pattern is taken from the **non-trivial side** of the (in)equality: the
/// side that is a constructor application or a known nullary constructor (the
/// refined variable itself is a bare variable, which is `Wild` and carries no
/// shape). For `a == b`, if exactly one side is a structural pattern it is used;
/// if both/neither are, parsing fails (returns `None`) and the caller falls back
/// to today's `Overlapping` — never worse than the status quo.
///
/// Returns `(pattern, is_equality)`: `is_equality = true` for `==`
/// (the refined set is *exactly* the pattern), `false` for `!=` (the refined set
/// is the *complement* of the pattern within the base category).
pub fn parse_structural_predicate(
    predicate_repr: &str,
    alpha: &RankedAlphabet,
) -> Option<(TreePred<AnyPred>, bool)> {
    // Split on the top-level `==` / `!=` relation. The `Display` form always
    // renders these with surrounding spaces (` == ` / ` != `), and TermEq/TermNeq
    // sides are atoms or constructor applications (no nested top-level relation),
    // so a simple find of the first relation token is unambiguous.
    let (lhs, rhs, is_equality) = if let Some(idx) = predicate_repr.find(" == ") {
        (&predicate_repr[..idx], &predicate_repr[idx + 4..], true)
    } else if let Some(idx) = predicate_repr.find(" != ") {
        (&predicate_repr[..idx], &predicate_repr[idx + 4..], false)
    } else {
        return None;
    };

    let lhs_pat = parse_term_pattern(lhs.trim(), alpha);
    let rhs_pat = parse_term_pattern(rhs.trim(), alpha);

    // Pick the structural (shape-bearing) side: a `Node` carries shape; a `Wild`
    // (a bare variable) does not. Exactly one structural side is the well-formed
    // refinement form `var == pattern`.
    let pattern = match (is_shaped(&lhs_pat), is_shaped(&rhs_pat)) {
        (true, false) => lhs_pat?,
        (false, true) => rhs_pat?,
        // Both shaped or both variables: ambiguous shape ⇒ defer to heuristic.
        _ => return None,
    };
    Some((pattern, is_equality))
}

/// Whether a parsed pattern carries structural shape (a `Node`), as opposed to a
/// bare variable (`Wild`) or `None` (parse failure).
fn is_shaped(p: &Option<TreePred<AnyPred>>) -> bool {
    matches!(p, Some(TreePred::Node { .. }))
}

/// Parse a single term-pattern token (`c(args)` / nullary `c` / variable) into a
/// [`TreePred<AnyPred>`]. Returns `None` on any malformed input (unbalanced
/// parens, empty token).
fn parse_term_pattern(s: &str, alpha: &RankedAlphabet) -> Option<TreePred<AnyPred>> {
    let s = s.trim();
    if s.is_empty() {
        return None;
    }
    match s.find('(') {
        Some(open) => {
            // Constructor application `c(args)`: the matching close must be the
            // final char, and `args` is a comma-split at depth 0.
            if !s.ends_with(')') {
                return None;
            }
            let ctor_token = s[..open].trim();
            if ctor_token.is_empty() || !is_ident(ctor_token) {
                return None;
            }
            let inner = &s[open + 1..s.len() - 1];
            let arg_strs = split_top_level_commas(inner)?;
            // The applied constructor token MUST resolve to a grammar rule label
            // (else the pattern cannot match any well-formed term — fall back to
            // the heuristic). The resolved label is the alphabet constructor used
            // by `category_automaton`, so the pattern automaton and the category
            // automaton share constructor identity.
            let ctor = resolve_constructor(ctor_token, alpha)?;
            // Arity agreement guards against a malformed pattern (`cons(x)`).
            if alpha.arities.get(&ctor).copied() != Some(arg_strs.len()) {
                return None;
            }
            let mut children = Vec::with_capacity(arg_strs.len());
            for a in &arg_strs {
                children.push(parse_term_pattern(a, alpha)?);
            }
            Some(TreePred::Node {
                constructor: ctor,
                payload_guard: None,
                children,
            })
        },
        None => {
            // Bare identifier: a nullary constructor of the grammar ⇒ Node;
            // otherwise a pattern variable ⇒ Wild.
            if !is_ident(s) {
                return None;
            }
            match resolve_constructor(s, alpha) {
                Some(ctor) if alpha.arities.get(&ctor).copied() == Some(0) => {
                    Some(TreePred::Node {
                        constructor: ctor,
                        payload_guard: None,
                        children: Vec::new(),
                    })
                },
                // A non-nullary constructor used as a bare atom is malformed;
                // anything that resolves to no constructor is a pattern variable.
                Some(_) => None,
                None => Some(TreePred::Wild),
            }
        },
    }
}

/// Resolve a refinement-predicate constructor *token* to the grammar's actual
/// rule-label constructor (an `alpha.arities` key).
///
/// Refinement predicates are written in the user's surface syntax, where a
/// constructor may be spelled differently from its grammar **rule label** — most
/// commonly a lower-cased form (`cons` for the rule labeled `Cons`). Because the
/// `category_automaton` keys transitions by rule label, the pattern automaton
/// MUST use the same labels for the product (intersection / complement) to align.
/// Resolution tries, in order:
///   1. an exact match (`Cons` → `Cons`);
///   2. a unique case-insensitive match (`cons` → `Cons`).
/// A token that matches no constructor (a pattern variable), or matches more than
/// one case-insensitively (ambiguous), returns `None`.
fn resolve_constructor(token: &str, alpha: &RankedAlphabet) -> Option<String> {
    if alpha.arities.contains_key(token) {
        return Some(token.to_string());
    }
    let mut found: Option<&String> = None;
    for label in alpha.arities.keys() {
        if label.eq_ignore_ascii_case(token) {
            if found.is_some() {
                return None; // ambiguous — refuse rather than guess
            }
            found = Some(label);
        }
    }
    found.cloned()
}

/// Whether `s` is a single identifier token (no internal whitespace, parens, or
/// commas — those are handled by the caller's structure).
fn is_ident(s: &str) -> bool {
    !s.is_empty()
        && s.chars()
            .all(|c| c.is_alphanumeric() || c == '_' || c == ':')
}

/// Split `inner` (the contents between a constructor's parens) on the
/// *top-level* commas (depth-0 w.r.t. nested parens), trimming each piece.
/// Returns `None` on unbalanced parens.
fn split_top_level_commas(inner: &str) -> Option<Vec<String>> {
    let inner = inner.trim();
    if inner.is_empty() {
        return Some(Vec::new());
    }
    let mut parts = Vec::new();
    let mut depth: i32 = 0;
    let mut start = 0usize;
    for (i, c) in inner.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth < 0 {
                    return None;
                }
            },
            ',' if depth == 0 => {
                parts.push(inner[start..i].trim().to_string());
                start = i + 1;
            },
            _ => {},
        }
    }
    if depth != 0 {
        return None;
    }
    parts.push(inner[start..].trim().to_string());
    Some(parts)
}

/// Build the [`SymbolicTreeAutomaton`] recognizing the terms of `base_cat` that
/// also match the structural pattern `pattern` — the *refined* language
/// `L(base_cat) ∩ L(pattern)`.
///
/// `Wild` slots in the pattern compile to the universal automaton over the
/// grammar's alphabet, so intersecting with the base-category automaton restricts
/// a `Wild` to exactly the well-formed terms of the slot's category. The result
/// shares the base category automaton's ranked alphabet, so it can be
/// complemented (for the subtype check) and tested for emptiness.
pub fn refined_automaton(
    base_cat: &str,
    pattern: &TreePred<AnyPred>,
    alpha: &RankedAlphabet,
    elem: &AnyAlgebra,
) -> Option<StAuto<AnyAlgebra>> {
    let base = category_automaton(base_cat, alpha, elem);
    // Compile the pattern over the SAME ranked alphabet (so `Wild`/`True` =
    // universal over this alphabet, and complement enumerates the same letters).
    let tree_alg = match elem {
        AnyAlgebra::Tree(g) => g.as_ref(),
        _ => return None,
    };
    let pat_auto = tree_alg.pattern_to_automaton(pattern);
    Some(base.intersect(&pat_auto))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn term(s: &str) -> SyntaxItemSpec {
        SyntaxItemSpec::Terminal(s.to_string())
    }
    fn nonterm(cat: &str, name: &str) -> SyntaxItemSpec {
        SyntaxItemSpec::NonTerminal {
            category: cat.to_string(),
            param_name: name.to_string(),
        }
    }
    fn scalar_cat(name: &str, native: &str) -> CategoryInfo {
        CategoryInfo {
            name: name.to_string(),
            native_type: Some(native.to_string()),
            is_primary: false,
            has_var: true,
        }
    }
    fn struct_cat(name: &str, primary: bool) -> CategoryInfo {
        CategoryInfo {
            name: name.to_string(),
            native_type: None,
            is_primary: primary,
            has_var: true,
        }
    }
    type Rule = SyntaxRule;
    fn rule(label: &str, cat: &str, syntax: Vec<SyntaxItemSpec>) -> Rule {
        (label.to_string(), cat.to_string(), syntax)
    }

    /// `List = Nil | Cons(Int, List)` is inhabited (Nil is a base case); an
    /// `Expr = App(Expr, Expr)` with no base case is empty.
    #[test]
    fn list_inhabited_expr_empty() {
        let categories = vec![
            struct_cat("Proc", true),
            scalar_cat("Int", "i64"),
            struct_cat("List", false),
            struct_cat("Expr", false),
        ];
        let all_syntax = vec![
            rule("IVar", "Int", vec![SyntaxItemSpec::IdentCapture { param_name: "x".to_string() }]),
            rule("Nil", "List", vec![term("nil")]),
            rule("Cons", "List", vec![nonterm("Int", "h"), nonterm("List", "t")]),
            // Expr has only a recursive rule — no base case ⇒ empty.
            rule("App", "Expr", vec![nonterm("Expr", "f"), nonterm("Expr", "a")]),
        ];
        let verdict = structural_verdict(&all_syntax, &categories);
        assert!(
            verdict.empty_categories.contains(&"Expr".to_string()),
            "Expr (no base case) must be empty: {:?}",
            verdict.empty_categories
        );
        assert!(
            !verdict.empty_categories.contains(&"List".to_string()),
            "List (Nil base case) must be inhabited"
        );
        assert!(
            !verdict.empty_categories.contains(&"Int".to_string()),
            "Int (IdentCapture leaf) must be inhabited"
        );
        // A witness for List exists and is accepted by the List automaton.
        let alpha = ranked_alphabet(&all_syntax, &categories);
        let elem = build_tree_algebra(&alpha);
        let list_auto = category_automaton("List", &alpha, &elem);
        let w = list_auto.witness().expect("List inhabited ⇒ witness");
        assert!(list_auto.accepts(&w), "witness must be accepted by its automaton");
    }

    /// The scalar/structural split: `Int` (i64) is payloaded; `List`/`Proc` are
    /// structural.
    #[test]
    fn scalar_split_marks_payloaded() {
        let categories = vec![
            struct_cat("Proc", true),
            scalar_cat("Int", "i64"),
            struct_cat("List", false),
        ];
        let all_syntax = vec![
            rule("ILit", "Int", vec![term("0")]),
            rule("Nil", "List", vec![term("nil")]),
            rule("PInt", "Proc", vec![nonterm("Int", "i")]),
        ];
        let alpha = ranked_alphabet(&all_syntax, &categories);
        assert!(alpha.payloaded.contains("ILit"), "Int leaf must be payloaded");
        assert!(!alpha.payloaded.contains("Nil"), "List ctor must be structural");
        assert!(!alpha.payloaded.contains("PInt"), "Proc ctor must be structural");
    }
}
