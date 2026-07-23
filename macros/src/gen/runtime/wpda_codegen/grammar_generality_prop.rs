//! Layer-A grammar-generality property harness (the permanent safeguard).
//!
//! This module is the durable, compile-free codegen-property gate proving the
//! prattail WPDA/WFST codegen is *uniformly general* across ARBITRARY grammars
//! — not overfit to the bundled ones (RhoCalc / Calculator / Lambda). It calls
//! the `pub(crate)` codegen functions directly on randomly-generated
//! `LanguageDef`s (no parser build, no `cargo` sub-process) and asserts the
//! seven generality invariants documented in
//! `scratchpad/prattail-generality-audit.md` §"FUZZ/PROPERTY HARNESS".
//!
//! ## Invariants (audit §Layer-A)
//!
//! | INV   | Property                                            | Catches  |
//! |-------|-----------------------------------------------------|----------|
//! | INV-1 | NO-LOSS symmetry (F5-2 cohort-aware; see fn doc)    | drift    |
//! | INV-2 | classifier totality (rule w/ ≥1 literal ⇒ Some)     | GAP-1,3  |
//! | INV-3 | goal-gate conservativeness (cross-cat edge ∈ reach) | GAP-1    |
//! | INV-4 | projection/extension complementarity (flag in gate) | GAP-4    |
//! | INV-5 | no single-winner UNLESS whole-slice cohort         | drift    |
//! | INV-6 | no hardcoded category/delimiter dispatch            | GAP-2    |
//! | INV-7 | 0-operand-per-kind classifies + dispatch arm        | GAP-3    |
//! | INV-8 | prefix-surface NO-LOSS (S1-factoring, amendment A5) | drift    |
//!
//! INV-8 (S1-FACTORING F0, 2026-07-11 — red-team amendment A5; NOT a
//! revision of INV-5, which gates the INFIX lex-alt lattice): for every
//! `(category, leading-literal)` prefix cohort, the factoring partition
//! loses no member — `Σ member leaves over spine groups + Σ members of
//! F5-deferred (ineligible) groups + |unfactored singletons| == the original
//! cohort size` — checked on BOTH the always-computed factoring model AND
//! the emission-effective partition; under `forks::S1_FACTORING == false`
//! the latter must additionally degenerate to the identity (every rule its
//! own singleton, zero groups).
//!
//! INV-1/INV-5 (S1-FACTORING F5-2, 2026-07-14 — board task #13 restatement, a
//! USER-signed-off named-invariant change): a factored mixfix cohort of `M`
//! members REPLACES its `M` per-member infix lex-alt entries with ONE spine
//! entry (`kind_dispatch.rs:2005-2036`), so a covered `(cat, terminal)` key
//! contributes `ops − M + 1` lattice entries and the aggregate lattice total is
//! `group_total − Σ_covered (M − 1)`. This RESTATES — never weakens — the
//! no-loss guarantee: the collapse is admitted ONLY when the surviving entry
//! carries the cohort's `spine_id`/`min_l_bp`/`result_src_idx` (:2023-2031) and
//! INV-8-mixfix proves `leaves == members`. It degenerates to the pre-F5-2 1:1
//! statement on every non-cohort grammar and whenever
//! `S1_FACTORING && S1F5_MIXFIX_COHORTS` is not satisfied (`mixfix_groups`
//! empty ⇒ byte-identical to the pre-F1 lattice).
//!
//! The harness draws delimiters from a NON-rhocalc alphabet (`«»`, `‹›`, `⟦⟧`,
//! `⟨⟩`, custom keywords, non-`;` separators) so the rhocalc-specific hardcodes
//! the audit flags (GAP-2's `#{ {| }# |}`, the bracket set, the `;` row
//! boundary) surface as foreign string literals in INV-6.
//!
//! DISCIPLINE: all assertions are over the AST / derived structures the codegen
//! produces (positive-AST), never over `Display` text.

#![cfg(test)]

use std::collections::{BTreeMap, BTreeSet, HashMap};

use mettail_ast::grammar::{
    convert_term_context_to_items, GrammarItem, GrammarRule, PatternOp, SyntaxExpr, TermParam,
};
use mettail_ast::language::{LangType, LanguageDef};
use mettail_ast::types::{CollectionType, TypeExpr};
use proc_macro2::{Span, TokenStream, TokenTree};
use proptest::prelude::*;
use quote::ToTokens;
use syn::Ident;

use super::infix::{build_bp_table, group_ops_by_cat_terminal};
use super::prefix::{classify_atomic, AtomicShape};

// ════════════════════════════════════════════════════════════════════════════
// Tiny AST builders (positive-AST; never Display-driven).
// ════════════════════════════════════════════════════════════════════════════

fn id(s: &str) -> Ident {
    Ident::new(s, Span::call_site())
}

fn simple(name: &str, cat: &str) -> TermParam {
    TermParam::Simple { name: id(name), ty: TypeExpr::Base(id(cat)) }
}

fn simple_coll(name: &str, coll: CollectionType, elem: &str) -> TermParam {
    TermParam::Simple {
        name: id(name),
        ty: TypeExpr::Collection { coll_type: coll, element: Box::new(TypeExpr::Base(id(elem))) },
    }
}

fn param(name: &str) -> SyntaxExpr {
    SyntaxExpr::Param(id(name))
}

fn lit(s: &str) -> SyntaxExpr {
    SyntaxExpr::Literal(s.to_string())
}

fn sep(coll: &str, separator: &str) -> SyntaxExpr {
    SyntaxExpr::Op(PatternOp::Sep { collection: id(coll), separator: separator.to_string(), source: None })
}

/// Build a judgement-style `GrammarRule` from term-context + syntax-pattern,
/// populating `items`/`bindings` exactly as the DSL parser does so downstream
/// emitters that read `rule.items` see a well-formed rule.
fn jrule(label: &str, category: &str, tc: Vec<TermParam>, sp: Vec<SyntaxExpr>) -> GrammarRule {
    let (items, bindings) = convert_term_context_to_items(&tc);
    GrammarRule {
        label: id(label),
        category: id(category),
        items,
        bindings,
        term_context: Some(tc),
        syntax_pattern: Some(sp),
        rust_code: None,
        eval_mode: None,
        is_right_assoc: false,
        prefix_bp: None,
        tier_directive: None,
        is_auto_injected: false,
        doc_comment: None,
    }
}

fn lang_type(name: &str, native: Option<&str>) -> LangType {
    LangType {
        name: id(name),
        native_type: native.map(|t| syn::parse_str::<syn::Type>(t).expect("native type parses")),
        collection_kind: None,
    }
}

fn mk_language(name: &str, types: Vec<LangType>, terms: Vec<GrammarRule>) -> LanguageDef {
    LanguageDef {
        name: id(name),
        options: Default::default(),
        extends_names: Vec::new(),
        include_names: Vec::new(),
        mixin_names: Vec::new(),
        types,
        refinement_types: Vec::new(),
        token_defs: Vec::new(),
        mode_defs: Vec::new(),
        sync_constraints: Vec::new(),
        tree_invariants: Vec::new(),
        terms,
        equations: Vec::new(),
        rewrites: Vec::new(),
        logic: None,
        guard_config: None,
    }
}

// ════════════════════════════════════════════════════════════════════════════
// Fixed category universe + NON-rhocalc delimiter alphabet.
//
// Native categories use distinct names that do NOT collide with the reserved
// `NonTerminalKind` literals (`Var`/`Integer`/`Boolean`/`StringLiteral`/
// `FloatLiteral`) so their operand references classify as user categories.
// ════════════════════════════════════════════════════════════════════════════

/// (name, optional native rust type). Index = `CatRef`.
const CATS: &[(&str, Option<&str>)] = &[
    ("Expr", None),         // 0 — primary host category
    ("Tee", None),          // 1 — host
    ("Pred", None),         // 2 — host
    ("Num", Some("i64")),   // 3 — native int
    ("Txt", Some("String")), // 4 — native string
    ("Boo", Some("bool")),  // 5 — native bool
];

fn cat_name(r: usize) -> &'static str {
    CATS[r].0
}

/// NON-rhocalc bracket pairs. Deliberately avoid `( ) [ ] { } #{ }# {| |}`.
const DELIMS: &[(&str, &str)] = &[("«", "»"), ("‹", "›"), ("⟦", "⟧"), ("⟨", "⟩")];

/// Operator / trigger pool. Avoid `;`.
const OPS: &[&str] = &["plus", "star", "as", "is", "cmp", "join", "++", "<>", "amb", "meet"];

/// Element separators. Avoid `;`.
const SEPS: &[&str] = &[",", "·"];

/// Nullary keyword pool.
const KWS: &[&str] = &["nil", "unit", "epsilon", "zero"];

const COLLS: &[CollectionType] = &[CollectionType::Vec, CollectionType::HashBag, CollectionType::HashSet];

// ════════════════════════════════════════════════════════════════════════════
// Random grammar strategy.
// ════════════════════════════════════════════════════════════════════════════

// `NullaryMulti` (the GAP-3 / `Map()` shape) — LANDED 2026-06-28. Its
// downstream is a prefix-site N-literal-run consume + arity-0 fire that REUSES
// the B-1 `MixfixLiteralRun { kind: 2, parts_len == 0 }` runtime arm, entered
// from the PREFIX site instead of the InfixLoop (5 codegen edits, no prattail
// change). It is now drawn by `arb_rule_spec`, present in `witness_spine`, and
// the two GAP-3 deterministic tests below are un-`#[ignore]`d. `classify_atomic`
// classifies it as `AtomicShape::NullaryLiteralRun`, so INV-2/INV-7 pass.
#[derive(Debug, Clone)]
enum RuleSpec {
    /// `a:C op b:C |- :C` — homogeneous binary infix.
    InfixHomo { cat: usize, op: usize },
    /// `a:A op b:B |- :R` with A≠B — heterogeneous binary infix (GAP-1 shape).
    InfixHetero { lhs: usize, rhs: usize, result: usize, op: usize },
    /// `a:C op |- :C` — unary postfix.
    Postfix { cat: usize, op: usize },
    /// `op a:C |- :C` — same-cat unary prefix.
    PrefixUnary { cat: usize, op: usize },
    /// `op s:S |- :R` with S≠R — cross-cat prefix unary.
    CrossCatPrefix { src: usize, result: usize, op: usize },
    /// `|- kw : R` — nullary single literal.
    NullaryOne { result: usize, kw: usize },
    /// `|- kw open close : R` — nullary MULTI literal (GAP-3 shape).
    NullaryMulti { result: usize, kw: usize, delim: usize },
    /// `x:S |- x : R` with S≠R — transparent projection.
    Projection { src: usize, result: usize },
    /// `a:A op b:A |- :R` with A≠R — cross-cat-LHS infix (homogeneous operands).
    CrossCatLhsInfix { lhs: usize, result: usize, op: usize },
    /// `a:C op1 b:C op2 d:C |- :C` — strict-alternating mixfix ternary.
    MixfixTernary { cat: usize, op1: usize, op2: usize },
    /// `xs:Coll(E) |- open xs.sep close : R` — collection literal.
    Collection { result: usize, elem: usize, coll: usize, delim: usize, sep: usize },
}

fn arb_rule_spec() -> impl Strategy<Value = RuleSpec> {
    let c = || 0usize..CATS.len();
    let o = || 0usize..OPS.len();
    let d = || 0usize..DELIMS.len();
    let s = || 0usize..SEPS.len();
    let k = || 0usize..KWS.len();
    let cl = || 0usize..COLLS.len();
    prop_oneof![
        (c(), o()).prop_map(|(cat, op)| RuleSpec::InfixHomo { cat, op }),
        (c(), c(), c(), o()).prop_map(|(lhs, rhs, result, op)| RuleSpec::InfixHetero { lhs, rhs, result, op }),
        (c(), o()).prop_map(|(cat, op)| RuleSpec::Postfix { cat, op }),
        (c(), o()).prop_map(|(cat, op)| RuleSpec::PrefixUnary { cat, op }),
        (c(), c(), o()).prop_map(|(src, result, op)| RuleSpec::CrossCatPrefix { src, result, op }),
        (c(), k()).prop_map(|(result, kw)| RuleSpec::NullaryOne { result, kw }),
        // GAP-3 (2026-06-28, LANDED): `RuleSpec::NullaryMulti` (the `Map()`
        // shape) is now drawn — the nullary multi-literal keyword run is wired.
        (c(), k(), d()).prop_map(|(result, kw, delim)| RuleSpec::NullaryMulti { result, kw, delim }),
        (c(), c()).prop_map(|(src, result)| RuleSpec::Projection { src, result }),
        (c(), c(), o()).prop_map(|(lhs, result, op)| RuleSpec::CrossCatLhsInfix { lhs, result, op }),
        (c(), o(), o()).prop_map(|(cat, op1, op2)| RuleSpec::MixfixTernary { cat, op1, op2 }),
        (c(), c(), cl(), d(), s()).prop_map(|(result, elem, coll, delim, sep)| RuleSpec::Collection { result, elem, coll, delim, sep }),
    ]
}

/// Realize a list of `RuleSpec`s into a `LanguageDef`, assigning unique rule
/// labels by index. Always declares all six fixed categories.
fn realize(specs: &[RuleSpec]) -> LanguageDef {
    let types: Vec<LangType> = CATS.iter().map(|(n, nt)| lang_type(n, *nt)).collect();
    let mut terms: Vec<GrammarRule> = Vec::with_capacity(specs.len());
    for (i, spec) in specs.iter().enumerate() {
        let l = |tag: &str| format!("R{}{}", i, tag);
        let rule = match *spec {
            RuleSpec::InfixHomo { cat, op } => {
                let c = cat_name(cat);
                jrule(&l("Ih"), c, vec![simple("a", c), simple("b", c)], vec![param("a"), lit(OPS[op]), param("b")])
            }
            RuleSpec::InfixHetero { lhs, rhs, result, op } => {
                // Ensure heterogeneity (lhs != rhs); skip-degenerate by nudging.
                let (a, b) = if lhs == rhs { (lhs, (rhs + 1) % CATS.len()) } else { (lhs, rhs) };
                let (an, bn, rn) = (cat_name(a), cat_name(b), cat_name(result));
                jrule(&l("Ix"), rn, vec![simple("a", an), simple("b", bn)], vec![param("a"), lit(OPS[op]), param("b")])
            }
            RuleSpec::Postfix { cat, op } => {
                let c = cat_name(cat);
                jrule(&l("Pf"), c, vec![simple("a", c)], vec![param("a"), lit(OPS[op])])
            }
            RuleSpec::PrefixUnary { cat, op } => {
                let c = cat_name(cat);
                jrule(&l("Pu"), c, vec![simple("a", c)], vec![lit(OPS[op]), param("a")])
            }
            RuleSpec::CrossCatPrefix { src, result, op } => {
                let (s, r) = if src == result { (src, (result + 1) % CATS.len()) } else { (src, result) };
                let (sn, rn) = (cat_name(s), cat_name(r));
                jrule(&l("Cp"), rn, vec![simple("a", sn)], vec![lit(OPS[op]), param("a")])
            }
            RuleSpec::NullaryOne { result, kw } => {
                jrule(&l("N1"), cat_name(result), vec![], vec![lit(KWS[kw])])
            }
            RuleSpec::NullaryMulti { result, kw, delim } => {
                let (o, c) = DELIMS[delim];
                jrule(&l("Nm"), cat_name(result), vec![], vec![lit(KWS[kw]), lit(o), lit(c)])
            }
            RuleSpec::Projection { src, result } => {
                let (s, r) = if src == result { (src, (result + 1) % CATS.len()) } else { (src, result) };
                jrule(&l("Pj"), cat_name(r), vec![simple("a", cat_name(s))], vec![param("a")])
            }
            RuleSpec::CrossCatLhsInfix { lhs, result, op } => {
                let (a, r) = if lhs == result { (lhs, (result + 1) % CATS.len()) } else { (lhs, result) };
                let (an, rn) = (cat_name(a), cat_name(r));
                jrule(&l("Cl"), rn, vec![simple("a", an), simple("b", an)], vec![param("a"), lit(OPS[op]), param("b")])
            }
            RuleSpec::MixfixTernary { cat, op1, op2 } => {
                let c = cat_name(cat);
                // Distinct triggers so the two-literal mixfix is well-formed.
                let t1 = OPS[op1];
                let t2 = OPS[(op2 + 1) % OPS.len()];
                let t2 = if t2 == t1 { OPS[(op2 + 2) % OPS.len()] } else { t2 };
                jrule(
                    &l("Mx"),
                    c,
                    vec![simple("a", c), simple("b", c), simple("d", c)],
                    vec![param("a"), lit(t1), param("b"), lit(t2), param("d")],
                )
            }
            RuleSpec::Collection { result, elem, coll, delim, sep: sep_idx } => {
                let (o, c) = DELIMS[delim];
                jrule(
                    &l("Co"),
                    cat_name(result),
                    vec![simple_coll("xs", COLLS[coll].clone(), cat_name(elem))],
                    vec![lit(o), sep("xs", SEPS[sep_idx]), lit(c)],
                )
            }
        };
        terms.push(rule);
    }
    mk_language("GenLang", types, terms)
}

/// The witness spine: gap-exercising rules ALWAYS present in `arb_language_def`.
/// These guarantee the gap-catching invariants fire in the red state.
fn witness_spine() -> Vec<GrammarRule> {
    vec![
        // GAP-1 witness: heterogeneous binary infix, cross result (edge Expr→Pred).
        jrule("HetAs", "Pred", vec![simple("a", "Expr"), simple("b", "Tee")], vec![param("a"), lit("as"), param("b")]),
        // GAP-3 witness (LANDED 2026-06-28): nullary MULTI-literal keyword run
        // (the `Map()` shape) — empty term-context, all-literal `kw open close`.
        // Classifies as `AtomicShape::NullaryLiteralRun`; dispatches via the
        // prefix-site marker + reused `MixfixLiteralRun(kind=2, parts_len==0)`
        // arm. Non-rhocalc delimiters keep INV-6 satisfied.
        jrule("NmW", "Num", vec![], vec![lit("unit"), lit("«"), lit("»")]),
        // INV-5 witness: trigger collision — two ops sharing (Num, "amb").
        jrule("AmbA", "Num", vec![simple("a", "Num"), simple("b", "Num")], vec![param("a"), lit("amb"), param("b")]),
        jrule("AmbB", "Boo", vec![simple("a", "Num"), simple("b", "Num")], vec![param("a"), lit("amb"), param("b")]),
        // Plain homogeneous infix + transparent projection (baseline edges).
        jrule("PlusN", "Num", vec![simple("a", "Num"), simple("b", "Num")], vec![param("a"), lit("plus"), param("b")]),
        jrule("ProjNE", "Expr", vec![simple("a", "Num")], vec![param("a")]),
    ]
}

fn arb_language_def() -> impl Strategy<Value = LanguageDef> {
    prop::collection::vec(arb_rule_spec(), 0..6).prop_map(|specs| {
        let mut lang = realize(&specs);
        // Prepend the witness spine, keeping labels unique (spine labels are
        // non-`R<idx>` so they never collide with realized labels).
        let mut terms = witness_spine();
        terms.extend(lang.terms.drain(..));
        lang.terms = terms;
        lang
    })
}

// ════════════════════════════════════════════════════════════════════════════
// Shared helpers: per-cat materialization, label index, edge extraction.
// ════════════════════════════════════════════════════════════════════════════

fn categories_and_per_cat(lang: &LanguageDef) -> (Vec<String>, Vec<Vec<GrammarRule>>) {
    let categories = super::collect_category_names_with_literals(lang);
    let per_cat = super::synthetic::build_per_category_rules(lang, &categories);
    (categories, per_cat)
}

fn local_label_index(
    categories: &[String],
    per_cat: &[Vec<GrammarRule>],
) -> HashMap<(String, String), (u16, u16)> {
    let mut idx = HashMap::new();
    for (ci, rules) in per_cat.iter().enumerate() {
        for (ri, rule) in rules.iter().enumerate() {
            idx.insert((categories[ci].clone(), rule.label.to_string()), (ci as u16, ri as u16));
        }
    }
    idx
}

/// True iff `rule` is a Param-leading, literal-trigger-bearing shape (the domain
/// that `infix::classify_rule_public` is supposed to cover): binary infix,
/// postfix, or postfix-mixfix. Used by the INDEPENDENT edge extractor for INV-3
/// so it does not depend on the (buggy in red state) classifier.
fn crosscat_lhs_edge(rule: &GrammarRule) -> Option<(String, String)> {
    let tc = rule.term_context.as_ref()?;
    let sp = rule.syntax_pattern.as_ref()?;
    // First syntax element must be a Param naming the first Simple param.
    let SyntaxExpr::Param(p0) = sp.first()? else { return None };
    let TermParam::Simple { name, ty } = tc.first()? else { return None };
    if name != p0 {
        return None;
    }
    let TypeExpr::Base(lhs_ident) = ty else { return None };
    // Must carry at least one literal trigger (else it is a transparent
    // projection / non-operator shape handled elsewhere).
    if !sp.iter().any(|e| matches!(e, SyntaxExpr::Literal(_))) {
        return None;
    }
    let lhs = lhs_ident.to_string();
    let result = rule.category.to_string();
    if lhs == result {
        return None; // self-cat: vacuous (operand cat == result), no edge.
    }
    Some((lhs, result))
}

// ════════════════════════════════════════════════════════════════════════════
// Robust TokenStream / AST counters (visit-mut based — `visit` feature is off).
// ════════════════════════════════════════════════════════════════════════════

/// Count occurrences of an identifier in a raw token stream (recursing into
/// groups). Required because `LexAltRuleInfo` constructions live INSIDE the
/// `vec![…]` macro of each lattice arm, and syn's AST visitors do not descend
/// into macro token streams.
fn count_ident_in_tokens(ts: TokenStream, name: &str) -> usize {
    let mut n = 0;
    for tt in ts {
        match tt {
            TokenTree::Ident(i) => {
                if i == name {
                    n += 1;
                }
            }
            TokenTree::Group(g) => n += count_ident_in_tokens(g.stream(), name),
            _ => {}
        }
    }
    n
}

struct TupleCounter {
    count: usize,
}
impl syn::visit_mut::VisitMut for TupleCounter {
    fn visit_expr_tuple_mut(&mut self, node: &mut syn::ExprTuple) {
        self.count += 1;
        syn::visit_mut::visit_expr_tuple_mut(self, node);
    }
}

fn parse_fns(ts: TokenStream) -> Vec<syn::ItemFn> {
    let file: syn::File = syn::parse2(ts).expect("emitted codegen parses as a Rust file");
    file.items
        .into_iter()
        .filter_map(|it| match it {
            syn::Item::Fn(f) => Some(f),
            _ => None,
        })
        .collect()
}

/// Count tuple expressions inside every function whose name starts with one of
/// `prefixes` (the per-tier BP slice functions emit one tuple per slice entry).
fn count_tuples_in_prefixed_fns(fns: &[syn::ItemFn], prefixes: &[&str]) -> usize {
    let mut total = 0;
    for f in fns {
        let name = f.sig.ident.to_string();
        if prefixes.iter().any(|p| name.starts_with(p)) {
            let mut c = TupleCounter { count: 0 };
            let mut owned = f.clone();
            syn::visit_mut::VisitMut::visit_item_fn_mut(&mut c, &mut owned);
            total += c.count;
        }
    }
    total
}

/// Extract `(cat_src_idx, terminal) -> info_count` from `lex_alt_rules_for_infix`'s
/// match arms. The arm shape is
/// `(C, TokenKind::Fixed(__t)) if __t == "term" => vec![infos]`.
fn lattice_infix_counts_per_group(fns: &[syn::ItemFn]) -> BTreeMap<(u16, String), usize> {
    let mut out: BTreeMap<(u16, String), usize> = BTreeMap::new();
    for f in fns {
        if f.sig.ident != "lex_alt_rules_for_infix" {
            continue;
        }
        // Body: `match (cat_src_idx, kind) { arms }` (possibly the last expr).
        for stmt in &f.block.stmts {
            let expr = match stmt {
                syn::Stmt::Expr(e, _) => e,
                _ => continue,
            };
            if let syn::Expr::Match(m) = expr {
                for arm in &m.arms {
                    let Some(cat) = arm_cat_lit(&arm.pat) else { continue };
                    let Some(term) = arm_guard_string(arm) else { continue };
                    // The `LexAltRuleInfo`s live inside the arm's `vec![…]` macro,
                    // so count the ident in the raw token stream.
                    let n = count_ident_in_tokens(arm.body.to_token_stream(), "LexAltRuleInfo");
                    *out.entry((cat, term)).or_insert(0) += n;
                }
            }
        }
    }
    out
}

/// Companion to [`lattice_infix_counts_per_group`] (S1-FACTORING F5-2): collect
/// every integer-literal value present in each `lex_alt_rules_for_infix` arm
/// body, keyed by `(cat_src_idx, terminal)`. Used by the cohort-aware INV-1
/// restatement to prove a covered key's ONE surviving lex-alt entry is the
/// DESIGNATED spine entry — its `rule_idx` (= `spine_id`), `l_bp`
/// (= `min_l_bp`) and `result_src_idx` literals (`kind_dispatch.rs:2023-2031`)
/// must all appear in the arm. Parsing is suffix-agnostic (`63488u16`, `0u8`
/// both parse via `syn::LitInt::base10_parse`).
fn lattice_infix_arm_ints_per_group(fns: &[syn::ItemFn]) -> BTreeMap<(u16, String), BTreeSet<u64>> {
    let mut out: BTreeMap<(u16, String), BTreeSet<u64>> = BTreeMap::new();
    for f in fns {
        if f.sig.ident != "lex_alt_rules_for_infix" {
            continue;
        }
        for stmt in &f.block.stmts {
            let expr = match stmt {
                syn::Stmt::Expr(e, _) => e,
                _ => continue,
            };
            if let syn::Expr::Match(m) = expr {
                for arm in &m.arms {
                    let Some(cat) = arm_cat_lit(&arm.pat) else { continue };
                    let Some(term) = arm_guard_string(arm) else { continue };
                    let set = out.entry((cat, term)).or_default();
                    collect_int_literals(arm.body.to_token_stream(), set);
                }
            }
        }
    }
    out
}

/// Recursively collect every integer-literal value (suffix-stripped) in a
/// TokenStream (descending into groups, mirroring [`count_ident_in_tokens`]).
fn collect_int_literals(ts: TokenStream, out: &mut BTreeSet<u64>) {
    for tt in ts {
        match tt {
            TokenTree::Literal(l) => {
                if let Ok(li) = syn::parse_str::<syn::LitInt>(&l.to_string()) {
                    if let Ok(v) = li.base10_parse::<u64>() {
                        out.insert(v);
                    }
                }
            }
            TokenTree::Group(g) => collect_int_literals(g.stream(), out),
            _ => {}
        }
    }
}

/// From a tuple pattern `(C, TokenKind::Fixed(__t))`, extract the leading u16
/// literal `C`.
fn arm_cat_lit(pat: &syn::Pat) -> Option<u16> {
    let syn::Pat::Tuple(t) = pat else { return None };
    let first = t.elems.first()?;
    if let syn::Pat::Lit(plit) = first {
        if let syn::Lit::Int(li) = &plit.lit {
            return li.base10_parse::<u16>().ok();
        }
    }
    None
}

/// From an arm guard `if __t == "term"`, extract the string literal `term`.
fn arm_guard_string(arm: &syn::Arm) -> Option<String> {
    let (_, guard) = arm.guard.as_ref()?;
    if let syn::Expr::Binary(b) = &**guard {
        if let syn::Expr::Lit(el) = &*b.right {
            if let syn::Lit::Str(s) = &el.lit {
                return Some(s.value());
            }
        }
    }
    None
}

/// Recursively collect every (unescaped) string-literal value in a TokenStream.
fn collect_str_literals(ts: TokenStream, out: &mut BTreeSet<String>) {
    for tt in ts {
        match tt {
            TokenTree::Literal(l) => {
                let rendered = l.to_string();
                if rendered.starts_with('"') {
                    if let Ok(syn::Lit::Str(s)) = syn::parse_str::<syn::Lit>(&rendered) {
                        out.insert(s.value());
                    }
                }
            }
            TokenTree::Group(g) => collect_str_literals(g.stream(), out),
            _ => {}
        }
    }
}

/// Bracket / structural delimiter characters. A short string literal made up
/// ENTIRELY of these is a "structural delimiter". Deliberately excludes
/// arithmetic-operator chars (`+ * = < >`) so declared operator triggers are
/// not mistaken for delimiters.
const STRUCT_CHARS: &[char] =
    &['(', ')', '[', ']', '{', '}', '#', '|', ';', '«', '»', '‹', '›', '⟦', '⟧', '⟨', '⟩'];

fn is_delim_shaped(s: &str) -> bool {
    let n = s.chars().count();
    // A `format!`/`write!`/`panic!` placeholder (`{}`, and by extension any
    // balanced `{…}`) is NOT a structural delimiter — real delimiters are
    // single open/close tokens, never a balanced brace pair in one literal.
    // Excluding strings that contain BOTH `{` and `}` filters the format
    // placeholder `"{}"` (the lone all-bracket format spell) without masking a
    // genuine single `{` or `}` delimiter.
    if s.contains('{') && s.contains('}') {
        return false;
    }
    n >= 1 && n <= 3 && s.chars().all(|c| STRUCT_CHARS.contains(&c))
}

/// Build the grammar's derived delimiter / terminal vocabulary `V`. Any
/// structural delimiter the emitted engine references that is NOT in `V` is a
/// hardcode leak (INV-6).
fn allowed_vocab(lang: &LanguageDef, per_cat: &[Vec<GrammarRule>]) -> BTreeSet<String> {
    let mut v = BTreeSet::new();
    // Grouping is universal — emitted for every parseable category.
    v.insert("(".to_string());
    v.insert(")".to_string());

    fn walk_sp(sp: &[SyntaxExpr], v: &mut BTreeSet<String>) {
        for e in sp {
            match e {
                SyntaxExpr::Literal(s) => {
                    v.insert(s.clone());
                }
                SyntaxExpr::Op(op) => walk_op(op, v),
                SyntaxExpr::Param(_) => {}
                // L9-3: a custom-kind capture matches variable token text — it
                // contributes no FIXED terminal to the allowed vocabulary.
                SyntaxExpr::TokenKind { .. } => {}
            }
        }
    }
    fn walk_op(op: &PatternOp, v: &mut BTreeSet<String>) {
        match op {
            PatternOp::Sep { separator, source, .. } => {
                v.insert(separator.clone());
                if let Some(s) = source {
                    walk_op(s, v);
                }
            }
            PatternOp::Map { source, body, .. } => {
                walk_op(source, v);
                walk_sp(body, v);
            }
            PatternOp::Opt { inner } => walk_sp(inner, v),
            PatternOp::Zip { .. } | PatternOp::Var(_) => {}
        }
    }

    for rule in &lang.terms {
        if let Some(sp) = &rule.syntax_pattern {
            walk_sp(sp, &mut v);
        }
        for it in &rule.items {
            match it {
                GrammarItem::Terminal(t) => {
                    v.insert(t.clone());
                }
                GrammarItem::Collection { separator, delimiters, .. } => {
                    v.insert(separator.clone());
                    if let Some((o, c)) = delimiters {
                        v.insert(o.clone());
                        v.insert(c.clone());
                    }
                }
                _ => {}
            }
        }
    }
    // The structural-delimiter collector the codegen itself uses.
    let (opens, closes) = super::collection::collect_structural_delimiters(lang, per_cat);
    v.extend(opens);
    v.extend(closes);
    // Declared collection-category delimiters.
    for t in &lang.types {
        if let Some(ck) = &t.collection_kind {
            let d = ck.delimiters();
            v.insert(d.open.clone());
            v.insert(d.close.clone());
            v.insert(d.sep.clone());
            if let Some(kv) = &d.key_val_sep {
                v.insert(kv.clone());
            }
        }
    }
    v
}

/// Parse `emit_cat_can_reach`'s output (`false` or `matches!((from,goal), (a,b)|…)`)
/// into the emitted non-reflexive reachable pair set.
fn parse_reach_pairs(ts: TokenStream) -> BTreeSet<(u16, u16)> {
    let mut out = BTreeSet::new();
    let expr: syn::Expr = match syn::parse2(ts) {
        Ok(e) => e,
        Err(_) => return out,
    };
    let syn::Expr::Macro(m) = expr else { return out };
    // mac.tokens = `(from, goal), (a, b) | (c, d) | …`
    for tt in m.mac.tokens {
        if let TokenTree::Group(g) = tt {
            if g.delimiter() == proc_macro2::Delimiter::Parenthesis {
                let ints: Vec<u16> = g
                    .stream()
                    .into_iter()
                    .filter_map(|t| match t {
                        // quote renders `u16` literals WITH the `u16` suffix
                        // (e.g. `0u16`), so parse via `syn::LitInt::base10_parse`
                        // which strips the suffix; a bare `parse::<u16>()` fails.
                        TokenTree::Literal(l) => syn::parse_str::<syn::LitInt>(&l.to_string())
                            .ok()
                            .and_then(|li| li.base10_parse::<u16>().ok()),
                        _ => None,
                    })
                    .collect();
                if ints.len() == 2 {
                    out.insert((ints[0], ints[1]));
                }
            }
        }
    }
    out
}

// ════════════════════════════════════════════════════════════════════════════
// The seven invariants. Each returns Ok(()) on success, Err(reason) on failure.
// ════════════════════════════════════════════════════════════════════════════

/// INV-1 + INV-5: NO-LOSS symmetry (cohort-aware since S1-FACTORING F5-2,
/// board task #13). For every `(cat, terminal)` trigger group the per-tier
/// slice entries and the group size agree with the emitted lattice lex-alt
/// arm — EXCEPT that a factored mixfix cohort of `M` members collapses to ONE
/// spine entry, so a COVERED key contributes `ops − M + 1` lattice entries
/// (`kind_dispatch.rs:2005-2036`, the DESIGNED N→1 replacement) and the
/// aggregate lattice total is `group_total − Σ_covered (M − 1)`. No
/// single-winner truncation of a GENUINE multi-winner; no tier mis-partition.
///
/// This is a RESTATEMENT, not a relaxation. What INV-1 protects is
/// REPRESENTATION NO-LOSS: no census op is silently absent from the lex-fork
/// dispatch surface, each carrying its own `rule_idx`/`l_bp`. The non-mixfix
/// ops stay reachable through their own entries; the cohort members stay
/// reachable THROUGH the spine entry whose runtime fan re-expands them — an
/// integrity the restatement REQUIRES via three receipts: (a) the D-5
/// whole-slice assert (`kind_dispatch.rs:1999`) + the leaf-count assert
/// (`:1582`), which panic codegen on membership drift; (b) the surviving
/// entry carrying the cohort's `spine_id` / `min_l_bp` / `result_src_idx`
/// (`:2023-2031`, parsed and checked here); and (c) INV-8-mixfix's
/// `leaves == members` (cross-referenced here whenever any cohort exists). It
/// DEGENERATES exactly to the pre-F5-2 1:1 statement when no cohort covers a
/// key — every non-cohort grammar, and the whole OFF stance (`mixfix_groups`
/// is EMPTY unless `S1_FACTORING && S1F5_MIXFIX_COHORTS`, `forks.rs`).
fn inv1_inv5_noloss(lang: &LanguageDef) -> Result<(), String> {
    let (categories, per_cat) = categories_and_per_cat(lang);
    let bp_table = build_bp_table(lang);
    let label_index = local_label_index(&categories, &per_cat);
    let grouped = group_ops_by_cat_terminal(&bp_table, &categories, &label_index);

    let mut group_total = 0usize;
    let mut max_group_tier = 0usize;
    let mut multi_winner_groups = 0usize;
    for ((cat, terminal), ops) in grouped.iter() {
        group_total += ops.len();
        // Tier partition: each op is exactly ONE of infix / postfix / mixfix.
        let infix = ops.iter().filter(|g| !g.op.is_postfix && !g.op.is_mixfix).count();
        let postfix = ops.iter().filter(|g| g.op.is_postfix).count();
        let mixfix = ops.iter().filter(|g| g.op.is_mixfix).count();
        if infix + postfix + mixfix != ops.len() {
            return Err(format!(
                "INV-1 tier mis-partition at (cat {cat}, '{terminal}'): \
                 infix={infix}+postfix={postfix}+mixfix={mixfix} != group {}",
                ops.len()
            ));
        }
        max_group_tier = max_group_tier.max(infix).max(postfix).max(mixfix);
        if ops.len() >= 2 {
            multi_winner_groups += 1;
        }
    }
    // No slice truncation: the per-tier cap must cover the largest tier group.
    // `GEN1_MAX_SLICE` is currently `usize::MAX` (uncapped), so this defensive
    // INV-1 guard is vacuously false today. It is retained (and the
    // clippy::absurd_extreme_comparisons lint allowed) so it still fires if the
    // slice cap is ever reduced below a real tier-group size.
    #[allow(clippy::absurd_extreme_comparisons)]
    if max_group_tier > super::infix::GEN1_MAX_SLICE {
        return Err(format!(
            "INV-1 slice truncation: GEN1_MAX_SLICE={} < largest tier group {max_group_tier}",
            super::infix::GEN1_MAX_SLICE
        ));
    }

    // Lattice arms: parse the emitted infix lex-alt table and compare per group.
    // S1-FACTORING F1: thread the emission-effective spine bundle exactly as
    // the engine assembly does (empty under `S1_FACTORING == false`; INV-5 is
    // the INFIX lattice, untouched by prefix-surface factoring either way).
    let s1_spine = super::factoring::build_spine_emission(lang, &categories, &per_cat);
    let lattice_ts =
        super::kind_dispatch::emit_lex_alt_rule_for_fn(lang, &per_cat, &categories, &s1_spine);
    let lattice_fns = parse_fns(lattice_ts);
    let lattice_counts = lattice_infix_counts_per_group(&lattice_fns);
    // F5-2 strengthening: the integer literals in each arm (spine-identity
    // proof for covered cohort keys).
    let lattice_arm_ints = lattice_infix_arm_ints_per_group(&lattice_fns);
    let lattice_total: usize = lattice_counts.values().sum();

    // ════════════════════════════════════════════════════════════════════════
    // PRE-F5-2 statement (SUPERSEDED; retained per comment-out-never-delete).
    // The 1:1 arm↔op correspondence held before S1-FACTORING F5-2. The DESIGNED
    // N→1 lex-alt replacement (kind_dispatch.rs:2005-2036) collapses a mixfix
    // cohort's M per-member entries into ONE spine entry, so this block fired
    // "lattice arm has 1 infos, group has 2 ops" on every factorable cohort
    // (board task #13). The cohort-aware RESTATEMENT follows (USER sign-off).
    // ────────────────────────────────────────────────────────────────────────
    // for ((cat, terminal), ops) in grouped.iter() {
    //     let got = lattice_counts.get(&(*cat, terminal.clone())).copied().unwrap_or(0);
    //     if got != ops.len() {
    //         return Err(format!(
    //             "INV-1 lattice/group mismatch at (cat {cat}, '{terminal}'): \
    //              lattice arm has {got} infos, group has {} ops",
    //             ops.len()
    //         ));
    //     }
    //     // INV-5: an N≥2 group must NOT collapse to a single winner.
    //     if ops.len() >= 2 && got < 2 {
    //         return Err(format!(
    //             "INV-5 single-winner collapse at (cat {cat}, '{terminal}'): \
    //              group {} but only {got} lattice entries",
    //             ops.len()
    //         ));
    //     }
    // }
    // if lattice_total != group_total {
    //     return Err(format!(
    //         "INV-1 lattice total {lattice_total} != group total {group_total}"
    //     ));
    // }
    // ════════════════════════════════════════════════════════════════════════

    // F5-2 cohort census: index the emission-effective mixfix cohorts by their
    // dispatch key. `dispatch_cat_src_idx` is the SAME
    // `collect_category_names_with_literals` coordinate `group_ops_by_cat_terminal`
    // keys on (factoring.rs:1268), and `mixfix_groups` is EMPTY unless
    // `S1_FACTORING && S1F5_MIXFIX_COHORTS` — so every branch below degenerates
    // to the pre-F5-2 statement on non-cohort grammars and under the OFF stance.
    let mut cohort_by_key: BTreeMap<(u16, String), &super::factoring::MixfixGroupEmission> =
        BTreeMap::new();
    for group in &s1_spine.mixfix_groups {
        // D-5 whole-slice: at most ONE cohort per dispatch key (pinned in
        // codegen at kind_dispatch.rs:1999 and by INV-8-mixfix). A second group
        // at one key would silently over-reduce the expected count — surface it.
        if cohort_by_key
            .insert((group.dispatch_cat_src_idx, group.trigger.clone()), group)
            .is_some()
        {
            return Err(format!(
                "INV-1 cohort drift at (cat {}, '{}'): two mixfix cohorts share one \
                 dispatch key (D-5 whole-slice ⇒ at most one)",
                group.dispatch_cat_src_idx, group.trigger
            ));
        }
    }

    // The cohort-adjusted expected lattice total, accumulated per key (== the
    // AM-1 aggregate `group_total − Σ_covered (members − 1)`, computed WITHOUT a
    // global subtraction so an impossible over-reduction is caught per key).
    let mut expected_lattice_total = 0usize;
    for ((cat, terminal), ops) in grouped.iter() {
        let got = lattice_counts.get(&(*cat, terminal.clone())).copied().unwrap_or(0);
        let key = (*cat, terminal.clone());
        let cohort = cohort_by_key.get(&key).copied();
        // A cohort collapses its `members` per-member entries into ONE spine
        // entry ⇒ its key contributes `ops − members + 1` lattice entries
        // (== `ops` when no cohort covers the key: `reduction == 0`).
        let members = cohort.map(|g| g.member_rule_idxs.len()).unwrap_or(0);
        let reduction = members.saturating_sub(1);
        let Some(expected) = ops.len().checked_sub(reduction) else {
            return Err(format!(
                "INV-1 cohort over-reduction at (cat {cat}, '{terminal}'): cohort claims \
                 {members} members but the census group has only {} ops",
                ops.len()
            ));
        };
        expected_lattice_total += expected;

        // INV-1 (RESTATED, cohort-aware). Protects representation no-loss: the
        // emitted arm's entry count equals the cohort-adjusted census.
        if got != expected {
            return Err(format!(
                "INV-1 lattice/group mismatch at (cat {cat}, '{terminal}'): lattice arm \
                 has {got} infos, cohort-adjusted expectation is {expected} (group has {} \
                 ops, {members} in a mixfix cohort)",
                ops.len()
            ));
        }

        // INV-1 STRENGTHENING: a covered key's ONE surviving entry must be the
        // DESIGNATED spine entry — its spine_id / min_l_bp / result_src_idx
        // (kind_dispatch.rs:2023-2031) must appear in the emitted arm. This is
        // what makes the restatement a STRENGTHENING, not a relaxation: dropping
        // an identity field, or letting an arbitrary member survive instead of
        // the spine entry, fails here.
        if let Some(group) = cohort {
            let carries =
                |v: u64| lattice_arm_ints.get(&key).is_some_and(|s| s.contains(&v));
            if !carries(u64::from(group.spine_id)) {
                return Err(format!(
                    "INV-1 spine-identity loss at (cat {cat}, '{terminal}'): the collapsed \
                     lattice arm does not carry the cohort spine_id {:#06x}",
                    group.spine_id
                ));
            }
            if !carries(u64::from(group.min_l_bp)) {
                return Err(format!(
                    "INV-1 spine-identity loss at (cat {cat}, '{terminal}'): the collapsed \
                     lattice arm does not carry the cohort min_l_bp {}",
                    group.min_l_bp
                ));
            }
            if !carries(u64::from(group.result_src_idx)) {
                return Err(format!(
                    "INV-1 spine-identity loss at (cat {cat}, '{terminal}'): the collapsed \
                     lattice arm does not carry the cohort result_src_idx {}",
                    group.result_src_idx
                ));
            }
        }

        // INV-5 (RESTATED, cohort-aware, N-6). An N≥2 group must not collapse to
        // a single winner UNLESS a whole-slice cohort accounts for it: while the
        // cohort-adjusted expectation is still ≥2 (a genuine multi-winner
        // remains — non-cohort ops share the key, or the cohort is partial) the
        // arm must keep ≥2 entries. When `expected == 1` the sole entry is the
        // LEGITIMATE spine entry, proven no-loss by the identity fields above
        // and the INV-8 cross-reference below.
        if expected >= 2 && got < 2 {
            return Err(format!(
                "INV-5 single-winner collapse at (cat {cat}, '{terminal}'): cohort-adjusted \
                 expectation {expected} (group {} ops, {members} in a cohort) but only {got} \
                 lattice entries",
                ops.len()
            ));
        }
    }

    // INV-1 AGGREGATE (RESTATED, AM-1). Pre-F5-2 this was
    // `lattice_total == group_total`; every covered key over-counts the raw
    // total by `members − 1`, so the faithful total subtracts them.
    if lattice_total != expected_lattice_total {
        let total_reduction = group_total.saturating_sub(expected_lattice_total);
        return Err(format!(
            "INV-1 lattice total {lattice_total} != cohort-adjusted group total \
             {expected_lattice_total} (raw group total {group_total}, sum cohort(members-1) \
             {total_reduction})"
        ));
    }

    // INV-1 NO-LOSS cross-reference (INV-8-mixfix). When cohorts exist the
    // collapse is loss-free ONLY IF every cohort's leaves == its member count;
    // INV-8-mixfix proves exactly that on BOTH the factoring model and the
    // emission partition. Requiring it here makes the analytic INV-1 witnesses
    // (fed to THIS fn directly) enforce the no-loss half too. Degenerates to a
    // no-op when no cohort covers any key.
    if !cohort_by_key.is_empty() {
        inv8_mixfix_surface_noloss(lang)
            .map_err(|e| format!("INV-1 no-loss cross-reference (INV-8-mixfix) failed: {e}"))?;
    }

    // Slice aggregate: per-tier BP tables emit exactly one tuple per grouped op.
    let slice_ts = super::infix::emit_bp_tables(lang, &categories, &per_cat);
    let slice_fns = parse_fns(slice_ts);
    let slice_total = count_tuples_in_prefixed_fns(&slice_fns, &["infix_bp_", "postfix_bp_", "mixfix_bp_"]);
    if slice_total != group_total {
        return Err(format!(
            "INV-1 slice total {slice_total} != group total {group_total}"
        ));
    }

    // INV-5 sanity: deliberate trigger collisions must actually produce ≥1
    // multi-winner group (otherwise the harness is not exercising forking).
    let _ = multi_winner_groups;
    Ok(())
}

/// INV-2: classifier totality. Every per-cat rule carrying ≥1 literal must be
/// classified by at least one codegen classifier (atomic / infix / binder /
/// collection).
fn inv2_totality(lang: &LanguageDef) -> Result<(), String> {
    let (_categories, per_cat) = categories_and_per_cat(lang);
    for rules in &per_cat {
        for rule in rules {
            let has_literal = rule
                .syntax_pattern
                .as_ref()
                .map(|sp| sp.iter().any(|e| matches!(e, SyntaxExpr::Literal(_))))
                .unwrap_or_else(|| rule.items.iter().any(|i| matches!(i, GrammarItem::Terminal(_))));
            if !has_literal {
                continue;
            }
            let atomic = !matches!(classify_atomic(rule, lang), AtomicShape::NonAtomic);
            let infix = super::infix::classify_rule_public(rule).is_some();
            let binder = super::binder::classify_binder_in(rule, lang).is_some();
            let collection = super::collection::classify_collection(rule, lang).is_some();
            if !(atomic || infix || binder || collection) {
                return Err(format!(
                    "INV-2 totality: rule `{}` (cat `{}`) carries ≥1 literal yet no classifier \
                     accepts it (atomic/infix/binder/collection all reject)",
                    rule.label, rule.category
                ));
            }
        }
    }
    Ok(())
}

/// INV-3: goal-gate conservativeness. Every cross-cat LHS edge found by the
/// INDEPENDENT extractor must be in the emitted `cat_can_reach` relation.
fn inv3_goal_gate(lang: &LanguageDef) -> Result<(), String> {
    let (categories, per_cat) = categories_and_per_cat(lang);
    let idx_of = |name: &str| -> Option<u16> {
        categories.iter().position(|c| c == name).map(|i| i as u16)
    };
    let reach = parse_reach_pairs(super::kind_dispatch::emit_cat_can_reach(lang, &per_cat, &categories));
    // Independent edge extraction directly from the rules (does NOT use the
    // classifier under test).
    for rules in &per_cat {
        for rule in rules {
            if let Some((lhs, result)) = crosscat_lhs_edge(rule) {
                let (Some(from), Some(to)) = (idx_of(&lhs), idx_of(&result)) else { continue };
                if from == to {
                    continue;
                }
                if !reach.contains(&(from, to)) {
                    return Err(format!(
                        "INV-3 goal-gate non-conservative: cross-cat edge {lhs}({from})→{result}({to}) \
                         (rule `{}`) is absent from cat_can_reach",
                        rule.label
                    ));
                }
            }
        }
    }
    Ok(())
}

/// INV-4: projection/extension complementarity. In the (grammar-independent)
/// prefix lex-fork, every `CrossCatProjection` match arm must set its survival
/// flag (`__primary_survived` / `__secondary_survived`) INSIDE the
/// `if __proj_keep …` gate — never as a sibling statement after it (which would
/// keep a suppressed projection alive and re-introduce the futile branch).
fn inv4_fork_symmetry() -> Result<(), String> {
    // S1-FACTORING F1: OFF-shape lex fork (no factored groups in this probe).
    let fork_ts = super::forks::emit_lex_fork_at_prefix_dispatch(0u16, false);
    let probe: syn::ItemFn = syn::parse2(quote::quote! { fn __probe() { #fork_ts } })
        .expect("fork code parses inside a probe fn");
    let mut inspector = ForkArmInspector { violations: Vec::new() };
    let mut owned = probe;
    syn::visit_mut::VisitMut::visit_item_fn_mut(&mut inspector, &mut owned);
    if inspector.violations.is_empty() {
        Ok(())
    } else {
        Err(format!("INV-4 survival-flag outside gate: {:?}", inspector.violations))
    }
}

struct ForkArmInspector {
    violations: Vec<String>,
}
impl syn::visit_mut::VisitMut for ForkArmInspector {
    fn visit_arm_mut(&mut self, arm: &mut syn::Arm) {
        if pat_last_ident(&arm.pat).as_deref() == Some("CrossCatProjection") {
            if let syn::Expr::Block(b) = &*arm.body {
                for stmt in &b.block.stmts {
                    if let Some(flag) = top_level_survival_assign(stmt) {
                        self.violations.push(format!(
                            "`{flag} = true` set at CrossCatProjection arm top level (outside `if __proj_keep` gate)"
                        ));
                    }
                }
            }
        }
        syn::visit_mut::visit_arm_mut(self, arm);
    }
}

fn pat_last_ident(pat: &syn::Pat) -> Option<String> {
    match pat {
        syn::Pat::Struct(p) => p.path.segments.last().map(|s| s.ident.to_string()),
        syn::Pat::TupleStruct(p) => p.path.segments.last().map(|s| s.ident.to_string()),
        _ => None,
    }
}

/// If `stmt` is a top-level `__primary_survived = true;` / `__secondary_survived = true;`
/// assignment, return the flag name.
fn top_level_survival_assign(stmt: &syn::Stmt) -> Option<String> {
    let syn::Stmt::Expr(syn::Expr::Assign(a), _) = stmt else { return None };
    let syn::Expr::Path(p) = &*a.left else { return None };
    let name = p.path.segments.last()?.ident.to_string();
    if name == "__primary_survived" || name == "__secondary_survived" {
        Some(name)
    } else {
        None
    }
}

/// INV-6: no hardcoded category/delimiter dispatch. No structural-delimiter
/// string literal in the emitted engine module may fall outside the grammar's
/// derived vocabulary `V`.
fn inv6_no_hardcoded_delims(lang: &LanguageDef) -> Result<(), String> {
    let (_categories, per_cat) = categories_and_per_cat(lang);
    let v = allowed_vocab(lang, &per_cat);
    let module = super::generate_wpda_engine_module(lang);
    let mut lits = BTreeSet::new();
    collect_str_literals(module, &mut lits);
    let suspects: Vec<String> = lits
        .into_iter()
        .filter(|s| is_delim_shaped(s) && !v.contains(s))
        .collect();
    if suspects.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "INV-6 hardcoded delimiters: structural literals not in grammar vocab: {suspects:?}"
        ))
    }
}

/// INV-7: 0-operand-per-kind. Every nullary rule (empty term-context, all
/// literals) — single OR multi literal — must classify (and therefore get a
/// dispatch arm).
fn inv7_nullary_per_kind(lang: &LanguageDef) -> Result<(), String> {
    let (_categories, per_cat) = categories_and_per_cat(lang);
    for rules in &per_cat {
        for rule in rules {
            let Some(tc) = rule.term_context.as_ref() else { continue };
            let Some(sp) = rule.syntax_pattern.as_ref() else { continue };
            let is_nullary_literal_run =
                tc.is_empty() && !sp.is_empty() && sp.iter().all(|e| matches!(e, SyntaxExpr::Literal(_)));
            if !is_nullary_literal_run {
                continue;
            }
            let classified = !matches!(classify_atomic(rule, lang), AtomicShape::NonAtomic)
                || super::infix::classify_rule_public(rule).is_some()
                || super::binder::classify_binder_in(rule, lang).is_some();
            if !classified {
                return Err(format!(
                    "INV-7 nullary rule `{}` (cat `{}`, {} literals) unclassified",
                    rule.label,
                    rule.category,
                    sp.len()
                ));
            }
        }
    }
    Ok(())
}

/// INV-8: prefix-surface NO-LOSS (S1-FACTORING F0, amendment A5). For every
/// `(category, leading-literal)` prefix cohort discovered by the factoring
/// member scan (BinderPrefix + NullaryLiteralRun descriptors — the same
/// insertion conditions as the `prefix.rs` unified bucket), the partition
/// accounts for every member exactly once:
///
/// ```text
/// Σ leaves(groups) + Σ |members(ineligible)| + |singletons| == cohort_size
/// ```
///
/// Checked on BOTH [`super::factoring::build_prefix_factoring`] (the
/// always-computed model — the real trie math, meaningful in F0 already) and
/// [`super::factoring::emission_partition`] (the F1 integration surface).
/// Under `forks::S1_FACTORING == false` the emission-effective partition must
/// ALSO be the identity: zero groups, zero deferrals, every member a
/// `FactoringDisabled` singleton. Under `forks::S1F5_ACCEPT_CONTINUE` (F5-1,
/// with S1 on) the `InteriorAccept` deferral must be UNREACHABLE — former
/// proper-prefix deferrals are absorbed into groups as sibling accept
/// leaves, and the no-loss formula counts them as leaves.
fn inv8_prefix_surface_noloss(lang: &LanguageDef) -> Result<(), String> {
    let (categories, per_cat) = categories_and_per_cat(lang);
    let models = [
        ("factoring model", super::factoring::build_prefix_factoring(lang, &categories, &per_cat)),
        ("emission partition", super::factoring::emission_partition(lang, &categories, &per_cat)),
    ];
    for (which, model) in &models {
        for cat in model {
            for bucket in &cat.buckets {
                let leaves: usize = bucket.groups.iter().map(|g| g.leaf_count()).sum();
                let deferred: usize =
                    bucket.ineligible.iter().map(|g| g.member_rule_idxs.len()).sum();
                let total = leaves + deferred + bucket.singletons.len();
                if total != bucket.cohort_size {
                    return Err(format!(
                        "INV-8 no-loss violated in the {which} at (cat {}, {:?}): \
                         {leaves} leaves + {deferred} deferred + {} singletons != cohort {}",
                        cat.category_src_idx,
                        bucket.leading_literal,
                        bucket.singletons.len(),
                        bucket.cohort_size,
                    ));
                }
            }
        }
    }
    if super::forks::S1_FACTORING && super::forks::S1F5_ACCEPT_CONTINUE {
        // F5-1 ON-branch census: proper-prefix members are absorbed as
        // sibling accept leaves ([`super::factoring::build_tree`]), so the
        // `InteriorAccept` deferral is UNREACHABLE in both models — a
        // surviving instance means the admission predicate drifted.
        for (which, model) in &models {
            for cat in model {
                for bucket in &cat.buckets {
                    for group in &bucket.ineligible {
                        if matches!(
                            group.reason,
                            super::factoring::IneligibleReason::InteriorAccept { .. }
                        ) {
                            return Err(format!(
                                "INV-8 F5-1 violated in the {which} at (cat {}, {:?}): \
                                 InteriorAccept deferral {:?} survives with \
                                 S1F5_ACCEPT_CONTINUE on",
                                cat.category_src_idx, bucket.leading_literal, group,
                            ));
                        }
                    }
                }
            }
        }
    }
    if !super::forks::S1_FACTORING {
        let (_, effective) = &models[1];
        for cat in effective {
            for bucket in &cat.buckets {
                if !bucket.groups.is_empty() || !bucket.ineligible.is_empty() {
                    return Err(format!(
                        "INV-8 identity violated: S1_FACTORING is OFF yet (cat {}, {:?}) \
                         emits {} groups / {} deferrals",
                        cat.category_src_idx,
                        bucket.leading_literal,
                        bucket.groups.len(),
                        bucket.ineligible.len(),
                    ));
                }
                if bucket.singletons.len() != bucket.cohort_size {
                    return Err(format!(
                        "INV-8 identity violated at (cat {}, {:?}): {} singletons != cohort {}",
                        cat.category_src_idx,
                        bucket.leading_literal,
                        bucket.singletons.len(),
                        bucket.cohort_size,
                    ));
                }
            }
        }
    }
    Ok(())
}

/// INV-8-mixfix: mixfix-surface NO-LOSS (S1-FACTORING F5-2, plan
/// `f5_mixfix_cohorts_plan.md` §2.3 INV-8-analog). For every
/// `(dispatch category, trigger)` mixfix cohort discovered by the factoring
/// slice scan (the SAME `group_ops_by_cat_terminal` grouping +
/// `GEN1_MAX_SLICE` window as the `mixfix_bp_<cat>` emitters), the partition
/// accounts for every slice member exactly once:
///
/// ```text
/// Σ leaves(groups) + Σ |members(ineligible)| + |singletons| == slice.len()
/// ```
///
/// D-5 (whole-slice eligibility) additionally requires: at most ONE group
/// per bucket, and a factored bucket has NO ineligible/singleton residue
/// (its group's leaves == the whole slice). Checked on BOTH
/// [`super::factoring::build_mixfix_factoring`] (the always-computed model)
/// and [`super::factoring::mixfix_emission_partition`] (the F5-2 integration
/// surface); with `forks::S1_FACTORING && forks::S1F5_MIXFIX_COHORTS` not
/// both `true`, the latter must degenerate to the identity (every member a
/// `FactoringDisabled` singleton, zero groups, zero deferrals).
fn inv8_mixfix_surface_noloss(lang: &LanguageDef) -> Result<(), String> {
    let (categories, per_cat) = categories_and_per_cat(lang);
    let prefix = super::factoring::build_prefix_factoring(lang, &categories, &per_cat);
    let models = [
        (
            "mixfix factoring model",
            super::factoring::build_mixfix_factoring(lang, &categories, &per_cat, &prefix),
        ),
        (
            "mixfix emission partition",
            super::factoring::mixfix_emission_partition(lang, &categories, &per_cat),
        ),
    ];
    for (which, model) in &models {
        for fact in model {
            for bucket in &fact.buckets {
                let leaves: usize = bucket.groups.iter().map(|g| g.leaves().len()).sum();
                let deferred: usize =
                    bucket.ineligible.iter().map(|g| g.member_rule_idxs.len()).sum();
                let total = leaves + deferred + bucket.singletons.len();
                if total != bucket.slice.len() {
                    return Err(format!(
                        "INV-8-mixfix no-loss violated in the {which} at (cat {}, {:?}): \
                         {leaves} leaves + {deferred} deferred + {} singletons != slice {}",
                        fact.dispatch_cat_src_idx,
                        bucket.trigger,
                        bucket.singletons.len(),
                        bucket.slice.len(),
                    ));
                }
                if bucket.groups.len() > 1 {
                    return Err(format!(
                        "INV-8-mixfix D-5 violated in the {which} at (cat {}, {:?}): \
                         {} groups in one bucket (whole-slice ⇒ at most one)",
                        fact.dispatch_cat_src_idx,
                        bucket.trigger,
                        bucket.groups.len(),
                    ));
                }
                if let Some(group) = bucket.groups.first() {
                    if group.leaves().len() != bucket.slice.len()
                        || !bucket.ineligible.is_empty()
                        || !bucket.singletons.is_empty()
                    {
                        return Err(format!(
                            "INV-8-mixfix D-5 violated in the {which} at (cat {}, {:?}): \
                             a factored bucket must cover the WHOLE slice ({} leaves, \
                             slice {}, {} ineligible, {} singletons)",
                            fact.dispatch_cat_src_idx,
                            bucket.trigger,
                            group.leaves().len(),
                            bucket.slice.len(),
                            bucket.ineligible.len(),
                            bucket.singletons.len(),
                        ));
                    }
                }
            }
        }
    }
    if !(super::forks::S1_FACTORING && super::forks::S1F5_MIXFIX_COHORTS) {
        let (_, effective) = &models[1];
        for fact in effective {
            for bucket in &fact.buckets {
                if !bucket.groups.is_empty() || !bucket.ineligible.is_empty() {
                    return Err(format!(
                        "INV-8-mixfix identity violated: the consts are OFF yet \
                         (cat {}, {:?}) emits {} groups / {} deferrals",
                        fact.dispatch_cat_src_idx,
                        bucket.trigger,
                        bucket.groups.len(),
                        bucket.ineligible.len(),
                    ));
                }
                if bucket.singletons.len() != bucket.slice.len()
                    || bucket.singletons.iter().any(|s| {
                        s.reason != super::factoring::SingletonReason::FactoringDisabled
                    })
                {
                    return Err(format!(
                        "INV-8-mixfix identity violated at (cat {}, {:?}): every slice \
                         member must be a FactoringDisabled singleton",
                        fact.dispatch_cat_src_idx, bucket.trigger,
                    ));
                }
            }
        }
    }
    Ok(())
}

// ════════════════════════════════════════════════════════════════════════════
// Deterministic witness tests — one clear RED signal per gap.
// ════════════════════════════════════════════════════════════════════════════

/// Minimal heterogeneous-infix grammar — RED before GAP-1 (INV-2 + INV-3).
fn het_infix_lang() -> LanguageDef {
    let types = vec![
        lang_type("Expr", None),
        lang_type("Tee", None),
        lang_type("Pred", None),
    ];
    let terms = vec![
        // Atoms so categories are inhabited.
        jrule("EVar", "Expr", vec![], vec![lit("e")]),
        jrule("TVar", "Tee", vec![], vec![lit("t")]),
        // Heterogeneous binary infix: Expr `as` Tee  →  Pred  (edge Expr→Pred).
        jrule("AsCast", "Pred", vec![simple("a", "Expr"), simple("b", "Tee")], vec![param("a"), lit("as"), param("b")]),
    ];
    mk_language("HetLang", types, terms)
}

#[test]
fn grammar_generality_inv2_heterogeneous_infix_classifies() {
    let lang = het_infix_lang();
    inv2_totality(&lang).expect("INV-2: heterogeneous infix must classify (GAP-1)");
}

#[test]
fn grammar_generality_inv3_heterogeneous_edge_in_reach() {
    let lang = het_infix_lang();
    inv3_goal_gate(&lang).expect("INV-3: heterogeneous cross-cat edge must be in cat_can_reach (GAP-1)");
}

/// Minimal nullary multi-literal grammar (Map()-shape) — RED before GAP-3.
fn nullary_multi_lang() -> LanguageDef {
    let types = vec![lang_type("Expr", None)];
    let terms = vec![
        // `EmptyMap |- "Map" "(" ")" : Expr` — uses ( ) which ARE in vocab, so
        // INV-7 is about classification, not delimiter shape.
        jrule("EmptyMap", "Expr", vec![], vec![lit("Map"), lit("("), lit(")")]),
    ];
    mk_language("NullaryLang", types, terms)
}

/// GAP-3 (`Map()` / nullary multi-literal keyword run) — LANDED 2026-06-28. Its
/// downstream is a prefix-site N-literal-run consume + arity-0 fire that REUSES
/// the B-1 `MixfixLiteralRun { kind: 2, parts_len == 0 }` runtime arm, entered
/// from the PREFIX site (the binder classifier still defers pure-literal rules
/// to the atomic classifiers per binder.rs:935-937; `classify_atomic` now
/// recognizes the multi-literal case as `AtomicShape::NullaryLiteralRun`). No
/// prattail change — 5 codegen edits.
#[test]
fn grammar_generality_inv7_nullary_multi_literal_classifies() {
    let lang = nullary_multi_lang();
    inv7_nullary_per_kind(&lang).expect("INV-7: nullary multi-literal keyword run must classify (GAP-3)");
}

#[test]
fn grammar_generality_inv2_nullary_multi_literal_total() {
    let lang = nullary_multi_lang();
    inv2_totality(&lang).expect("INV-2: nullary multi-literal carries literals and must classify (GAP-3)");
}

#[test]
fn grammar_generality_inv4_fork_survival_flag_inside_gate() {
    inv4_fork_symmetry().expect("INV-4: CrossCatProjection survival flag must be inside the gate (GAP-4)");
}

/// Clean non-rhocalc grammar (no unclassified rules) — RED before GAP-2.
fn non_rhocalc_lang() -> LanguageDef {
    let types = vec![
        lang_type("Expr", None),
        lang_type("Pred", None),
        lang_type("Num", Some("i64")),
    ];
    let terms = vec![
        jrule("EVar", "Expr", vec![], vec![lit("e")]),
        // Cross-cat-LHS infix so the scoped-lookahead (GAP-2 site) is exercised.
        jrule("Cmp", "Pred", vec![simple("a", "Num"), simple("b", "Num")], vec![param("a"), lit("cmp"), param("b")]),
        // Collection with NON-rhocalc brackets «…».
        jrule("Lst", "Expr", vec![simple_coll("xs", CollectionType::Vec, "Num")], vec![lit("«"), sep("xs", ","), lit("»")]),
        // Projection so Num inhabits Expr.
        jrule("ProjNE", "Expr", vec![simple("a", "Num")], vec![param("a")]),
    ];
    mk_language("NonRho", types, terms)
}

#[test]
fn grammar_generality_inv6_no_hardcoded_delimiters() {
    let lang = non_rhocalc_lang();
    inv6_no_hardcoded_delims(&lang)
        .expect("INV-6: emitted engine must not reference rhocalc-hardcoded delimiters (GAP-2)");
}

#[test]
fn grammar_generality_inv1_noloss_symmetry_with_collisions() {
    // A grammar with a deliberate (Num, "amb") trigger collision.
    let types = vec![lang_type("Num", Some("i64")), lang_type("Boo", Some("bool"))];
    let terms = vec![
        jrule("AmbA", "Num", vec![simple("a", "Num"), simple("b", "Num")], vec![param("a"), lit("amb"), param("b")]),
        jrule("AmbB", "Boo", vec![simple("a", "Num"), simple("b", "Num")], vec![param("a"), lit("amb"), param("b")]),
        jrule("PlusN", "Num", vec![simple("a", "Num"), simple("b", "Num")], vec![param("a"), lit("plus"), param("b")]),
    ];
    let lang = mk_language("NoLoss", types, terms);
    inv1_inv5_noloss(&lang).expect("INV-1/INV-5: slice == group == lattice for trigger collisions");
}

/// INV-1/INV-5 RESTATEMENT witness — Literal-root mixfix cohort (PERMANENT
/// regression pin, board task #13). This is `Inv8MixfixLang` (the
/// rhocalc-shaped POutput/POutputEmpty `!`+`«` send cohort), the CHEAPEST
/// decisive probe: an in-tree grammar already fed to
/// `inv8_mixfix_surface_noloss`, which by construction cannot catch the
/// INFIX-lattice defect. Hand-walk (red-team 2026-07-13) confirms it forms a
/// two-member mixfix cohort at (cat 0, '!'). Under the PRE-F5-2 INV-1
/// statement (1:1 arm↔op) this grammar Err'd with "lattice arm has 1 infos,
/// group has 2 ops" — the DESIGNED F5-2 N→1 lex-alt replacement
/// (kind_dispatch.rs:2005-2036) collapses the cohort's per-member
/// `MixfixFirstTrigger` entries into ONE spine entry. The cohort-aware
/// RESTATEMENT accepts that single spine entry (expected = ops − members + 1
/// = 1) while still proving no-loss via the spine-identity fields
/// (spine_id / min_l_bp / result_src_idx) and the INV-8 leaves==members
/// cross-reference — so this must now PASS.
#[test]
fn grammar_generality_inv1_cohort_litroot_witness() {
    let types = vec![lang_type("Expr", None)];
    let terms = vec![
        jrule("EAtom", "Expr", vec![], vec![lit("e")]),
        jrule(
            "MOne",
            "Expr",
            vec![simple("a", "Expr"), simple("b", "Expr")],
            vec![param("a"), lit("!"), lit("«"), param("b"), lit("»")],
        ),
        jrule(
            "MEmpty",
            "Expr",
            vec![simple("a", "Expr")],
            vec![param("a"), lit("!"), lit("«"), lit("»")],
        ),
    ];
    let lang = mk_language("Inv8MixfixLang", types, terms);
    inv1_inv5_noloss(&lang).expect(
        "INV-1/INV-5 (restated): a Literal-root mixfix send cohort collapses to ONE \
         spine entry with no member loss",
    );
}

/// INV-1/INV-5 RESTATEMENT witness — ParamParse-root mixfix cohort (PERMANENT
/// regression pin, board task #13). This is the exact shrunk shape of the
/// board-#13 proptest seed (entry 3, `cc f016bbb7…`): two `MixfixTernary`
/// rules `a "++" b "star" d` / `a "++" b "as" d` sharing the `++` trigger
/// with a NON-absorbable post-operand divergence ("star"/"as" are not
/// operator triggers of the operand cat Txt ⇒ A-M5 admits the cohort,
/// factoring.rs:1499-1528). Under the PRE-F5-2 INV-1 statement this Err'd
/// "lattice arm has 1 infos, group has 2 ops" at (cat 0, '++'); the
/// cohort-aware RESTATEMENT must PASS. This is the ParamParse-root class the
/// bundled census never exercises (rhocalc's `!` cohorts are Literal-root),
/// so it pins the restatement across BOTH root classes.
#[test]
fn grammar_generality_inv1_cohort_paramroot_witness() {
    let types = vec![lang_type("Txt", Some("String"))];
    let terms = vec![
        jrule("TAtom", "Txt", vec![], vec![lit("t")]),
        jrule(
            "R0Mx",
            "Txt",
            vec![simple("a", "Txt"), simple("b", "Txt"), simple("d", "Txt")],
            vec![param("a"), lit("++"), param("b"), lit("star"), param("d")],
        ),
        jrule(
            "R1Mx",
            "Txt",
            vec![simple("a", "Txt"), simple("b", "Txt"), simple("d", "Txt")],
            vec![param("a"), lit("++"), param("b"), lit("as"), param("d")],
        ),
    ];
    let lang = mk_language("MinLang", types, terms);
    inv1_inv5_noloss(&lang).expect(
        "INV-1/INV-5 (restated): a ParamParse-root mixfix cohort collapses to ONE \
         spine entry with no member loss",
    );
}

/// P-A4 receipt (board task #13): the census-vs-emission dump for the MinLang
/// ParamParse-root cohort — the restatement's receipt TRIPLE. Asserts (a) the
/// emission produces exactly ONE mixfix group at (cat 0, '++') with two
/// members and a `SPINE_RULE_BASE` (0xF800)-based spine_id; (b) the parsed
/// infix lattice count at that key is 1 (the N→1 collapse the restatement now
/// EXPECTS); (c) the `mixfix_bp_*` slice still emits 2 tuples (the per-member
/// weight rows are NOT collapsed — the census side stays complete). The
/// restated INV-1 reconciles lattice(1) against slice(2)/census(2) exactly by
/// the cohort adjustment.
#[test]
fn grammar_generality_inv1_cohort_paramroot_dump() {
    let types = vec![lang_type("Txt", Some("String"))];
    let terms = vec![
        jrule("TAtom", "Txt", vec![], vec![lit("t")]),
        jrule(
            "R0Mx",
            "Txt",
            vec![simple("a", "Txt"), simple("b", "Txt"), simple("d", "Txt")],
            vec![param("a"), lit("++"), param("b"), lit("star"), param("d")],
        ),
        jrule(
            "R1Mx",
            "Txt",
            vec![simple("a", "Txt"), simple("b", "Txt"), simple("d", "Txt")],
            vec![param("a"), lit("++"), param("b"), lit("as"), param("d")],
        ),
    ];
    let lang = mk_language("MinLang", types, terms);
    let (categories, per_cat) = categories_and_per_cat(&lang);

    // (a) emission: exactly one mixfix cohort at (0, "++"), two members.
    let s1 = super::factoring::build_spine_emission(&lang, &categories, &per_cat);
    assert_eq!(s1.mixfix_groups.len(), 1, "expected exactly one mixfix cohort");
    let group = &s1.mixfix_groups[0];
    eprintln!(
        "P-A4 MinLang cohort: dispatch_cat={} trigger={:?} spine_id={:#06x} \
         min_l_bp={} result_src_idx={} members={:?}",
        group.dispatch_cat_src_idx,
        group.trigger,
        group.spine_id,
        group.min_l_bp,
        group.result_src_idx,
        group.member_rule_idxs,
    );
    assert_eq!(group.dispatch_cat_src_idx, 0);
    assert_eq!(group.trigger, "++");
    assert_eq!(group.member_rule_idxs.len(), 2, "R0Mx + R1Mx");
    assert!(
        group.spine_id >= super::factoring::SPINE_RULE_BASE,
        "spine_id {:#06x} must be in the 0xF800 base band",
        group.spine_id,
    );

    // (b) parsed infix lattice count at (0, "++") == 1 (the N→1 collapse).
    let lattice_ts =
        super::kind_dispatch::emit_lex_alt_rule_for_fn(&lang, &per_cat, &categories, &s1);
    let lattice_counts = lattice_infix_counts_per_group(&parse_fns(lattice_ts));
    eprintln!("P-A4 MinLang lattice_infix_counts = {lattice_counts:?}");
    assert_eq!(lattice_counts.get(&(0u16, "++".to_string())).copied(), Some(1));

    // (c) the mixfix_bp_* slice still emits 2 tuples (census stays complete).
    let slice_ts = super::infix::emit_bp_tables(&lang, &categories, &per_cat);
    let bp_tuples = count_tuples_in_prefixed_fns(&parse_fns(slice_ts), &["mixfix_bp_"]);
    eprintln!("P-A4 MinLang mixfix_bp tuple count = {bp_tuples}");
    assert_eq!(bp_tuples, 2, "per-member weight rows are NOT collapsed");
}

/// INV-8 witness: a deliberately factorable prefix cohort mixing BOTH
/// classifier sources (a BinderPrefix pair sharing `zero « Tee` plus a
/// NullaryLiteralRun member `zero « »`) alongside an unshared singleton —
/// the member accounting must balance, and with `S1_FACTORING` OFF the
/// emission partition must be the identity.
#[test]
fn grammar_generality_inv8_prefix_surface_noloss() {
    let types = vec![lang_type("Expr", None), lang_type("Tee", None)];
    let terms = vec![
        // Nullary multi-literal member (the `mixfix_nullary_literals` source).
        jrule("NZero", "Expr", vec![], vec![lit("zero"), lit("«"), lit("»")]),
        // Two binder members sharing the « Tee spine, diverging at »/·.
        jrule(
            "BClose",
            "Expr",
            vec![simple("a", "Tee")],
            vec![lit("zero"), lit("«"), param("a"), lit("»")],
        ),
        jrule(
            "BSep",
            "Expr",
            vec![simple("a", "Tee"), simple("b", "Tee")],
            vec![lit("zero"), lit("«"), param("a"), lit("·"), param("b"), lit("»")],
        ),
        // A lone cohort elsewhere (singleton accounting).
        jrule("Lone", "Expr", vec![simple("a", "Tee")], vec![lit("unit"), param("a")]),
        jrule("TAtom", "Tee", vec![], vec![lit("epsilon")]),
    ];
    let lang = mk_language("Inv8Lang", types, terms);
    inv8_prefix_surface_noloss(&lang)
        .expect("INV-8: prefix-surface member accounting must balance (A5)");
}

/// INV-8-mixfix witness: a deliberately factorable mixfix send cohort — two
/// `!`-triggered postfix-mixfix rules sharing the `«` opener (an
/// operand-bearing member `a ! « b »` and a nullary member `a ! « »`,
/// the rhocalc POutput/POutputEmpty shape on a foreign alphabet) — the
/// slice accounting must balance in both models, and with the F5-2 consts
/// not both on the emission partition must be the identity.
#[test]
fn grammar_generality_inv8_mixfix_surface_noloss() {
    let types = vec![lang_type("Expr", None)];
    let terms = vec![
        jrule("EAtom", "Expr", vec![], vec![lit("e")]),
        jrule(
            "MOne",
            "Expr",
            vec![simple("a", "Expr"), simple("b", "Expr")],
            vec![param("a"), lit("!"), lit("«"), param("b"), lit("»")],
        ),
        jrule(
            "MEmpty",
            "Expr",
            vec![simple("a", "Expr")],
            vec![param("a"), lit("!"), lit("«"), lit("»")],
        ),
    ];
    let lang = mk_language("Inv8MixfixLang", types, terms);
    inv8_mixfix_surface_noloss(&lang)
        .expect("INV-8-mixfix: mixfix-surface slice accounting must balance (D-5)");
}

// ════════════════════════════════════════════════════════════════════════════
// Property tests over random grammars (breadth).
// ════════════════════════════════════════════════════════════════════════════

proptest! {
    #![proptest_config(ProptestConfig { cases: 96, max_shrink_iters: 4096, ..ProptestConfig::default() })]

    /// All structure-level invariants (INV-1/2/3/5/7/8) over random grammars.
    #[test]
    fn grammar_generality_props_structure(lang in arb_language_def()) {
        prop_assert!(inv1_inv5_noloss(&lang).is_ok(), "{}", inv1_inv5_noloss(&lang).unwrap_err());
        prop_assert!(inv2_totality(&lang).is_ok(), "{}", inv2_totality(&lang).unwrap_err());
        prop_assert!(inv3_goal_gate(&lang).is_ok(), "{}", inv3_goal_gate(&lang).unwrap_err());
        prop_assert!(inv7_nullary_per_kind(&lang).is_ok(), "{}", inv7_nullary_per_kind(&lang).unwrap_err());
        prop_assert!(inv8_prefix_surface_noloss(&lang).is_ok(), "{}", inv8_prefix_surface_noloss(&lang).unwrap_err());
        prop_assert!(inv8_mixfix_surface_noloss(&lang).is_ok(), "{}", inv8_mixfix_surface_noloss(&lang).unwrap_err());
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 48, max_shrink_iters: 2048, ..ProptestConfig::default() })]

    /// INV-6 (full-module generation) over random grammars. Guarded by
    /// catch_unwind so that — only in the pre-GAP-1/3 red state — a grammar
    /// containing an *unclassified* witness rule (which can make
    /// `generate_wpda_engine_module` panic) is skipped rather than masking the
    /// delimiter signal. Once the totality gaps are closed no rule is
    /// unclassified and the guard is a no-op.
    #[test]
    fn grammar_generality_props_inv6(lang in arb_language_def()) {
        let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| inv6_no_hardcoded_delims(&lang)));
        if let Ok(check) = res {
            prop_assert!(check.is_ok(), "{}", check.unwrap_err());
        }
    }
}
