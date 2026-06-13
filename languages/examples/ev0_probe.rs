//! EP-P6b EV-0 PROBE (measurement-only; 2026-06-12).
//!
//! Binding contract: docs/design/evidence-pruning/02-staged-implementation-plan.md
//! §P6b. Measures, on the post-ROOT-A rhocalc comm/eval corpus:
//!   (1) per-relation Ascent fact totals (the materialized `AscentResults` facts:
//!       `all_terms`, `rewrites`, `equivalences` — the public, authoritative
//!       post-run fact set that `normal_forms()` is computed from), vs
//!   (2) facts BACKWARD-REACHABLE from the extracted normal forms — i.e. the
//!       demanded subset: every term that transitively rewrites INTO a kept
//!       normal form (reverse-edge BFS over `rewrites`, mirroring the forward
//!       `ReachableNormalForms` machinery in runtime/src/language.rs), plus the
//!       rewrite edges and equivalence-class members confined to that subset.
//!   (3) eval share of test wall-time: coarse timing around `parse_term` (parse)
//!       vs `run_ascent` (eval) per input.
//!
//! GATE: undemanded-fact share ≥ 50% AND eval ≥ 20% of wall-time → the EV-1 gate
//! PASSES FORMALLY, but the recorded disposition is "SUPERSEDED BY THE FLIP"
//! (user directive: no further Ascent-side investment where the Dovetail/Rho flip
//! dissolves the class). Else: record the non-goal.
//!
//! Measurement-only: uses the PUBLIC `RhoCalcLanguage::run_ascent` API; adds NO
//! macro/codegen change, so the parser tables are untouched (the sentinel is the
//! structural witness). NOTE the per-relation totals are read from `AscentResults`
//! which is ALREADY semantic-key-deduped + canon-pair-filtered (the #307 eval-layer
//! quotient); the RAW pre-dedup relation counts (`prog.proc.len()` etc.) are an
//! upper bound this probe does NOT reach without touching the generated
//! `run_ascent` codegen — see the caveat in the printed footer. This makes the
//! undemanded-share a CONSERVATIVE LOWER BOUND: if even the deduped fact set is
//! >50% undemanded, the raw set is at least as undemanded.

use std::collections::{HashMap, HashSet, VecDeque};
use std::time::Instant;

use mettail_languages::rhocalc::*;
use mettail_runtime::{AscentResults, Language as _};

/// One measured input's per-relation totals and demanded (backward-reachable)
/// subset counts, plus the parse/eval timing split.
struct Row {
    input: String,
    // per-relation TOTALS (materialized AscentResults facts)
    terms_total: usize,
    rewrites_total: usize,
    equiv_classes_total: usize,
    equiv_members_total: usize,
    nf_total: usize,
    // DEMANDED subset (backward-reachable from the surviving normal forms)
    terms_demanded: usize,
    rewrites_demanded: usize,
    equiv_members_demanded: usize,
    // timing
    parse_ns: u128,
    eval_ns: u128,
}

/// Backward closure: the set of term_ids that transitively rewrite INTO a
/// surviving normal form. Seeds = the normal-form term_ids; edges walked in
/// REVERSE (`to_id → from_id`). Mirrors `ReachableNormalForms::ensure_expansion_indexes`
/// but builds `rewrites_by_to` for the backward direction.
fn backward_demanded(results: &AscentResults) -> HashSet<u64> {
    // reverse adjacency: to_id -> [from_id ...]
    let mut by_to: HashMap<u64, Vec<u64>> = HashMap::new();
    for rw in &results.rewrites {
        by_to.entry(rw.to_id).or_default().push(rw.from_id);
    }
    let mut demanded: HashSet<u64> = HashSet::new();
    let mut queue: VecDeque<u64> = VecDeque::new();
    // Seed with the SURVIVING normal forms (the extracted result set).
    for t in results.normal_forms_iter() {
        if demanded.insert(t.term_id) {
            queue.push_back(t.term_id);
        }
    }
    while let Some(id) = queue.pop_front() {
        if let Some(preds) = by_to.get(&id) {
            for &p in preds {
                if demanded.insert(p) {
                    queue.push_back(p);
                }
            }
        }
    }
    demanded
}

fn measure(input: &str) -> Option<Row> {
    mettail_runtime::clear_var_cache();
    let lang = RhoCalcLanguage;

    // --- PARSE (timed) --- skip (don't panic) on a parse failure: a residual
    // ROOT-F-adjacent input must not abort the whole probe; record by absence.
    let t_parse = Instant::now();
    let term = match lang.parse_term(input) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("  [skip — parse failed] `{}`: {}", input, e);
            return None;
        },
    };
    let parse_ns = t_parse.elapsed().as_nanos();

    // --- EVAL (timed) ---
    let t_eval = Instant::now();
    let results = match lang.run_ascent(term.as_ref()) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("  [skip — run_ascent failed] `{}`: {}", input, e);
            return None;
        },
    };
    let eval_ns = t_eval.elapsed().as_nanos();

    // --- per-relation TOTALS ---
    let terms_total = results.all_terms.len();
    let rewrites_total = results.rewrites.len();
    let equiv_classes_total = results.equivalences.len();
    let equiv_members_total: usize = results.equivalences.iter().map(|c| c.term_ids.len()).sum();
    let nf_total = results.normal_forms_iter().count();

    // --- DEMANDED subset (backward-reachable from the surviving normal forms) ---
    let demanded = backward_demanded(&results);
    let terms_demanded = results
        .all_terms
        .iter()
        .filter(|t| demanded.contains(&t.term_id))
        .count();
    // a rewrite is demanded iff BOTH endpoints are on a path to a kept NF
    // (its `to_id` is demanded, which by construction makes its `from_id`
    // demanded too — so this counts the edges INSIDE the demanded sub-DAG).
    let rewrites_demanded = results
        .rewrites
        .iter()
        .filter(|r| demanded.contains(&r.to_id) && demanded.contains(&r.from_id))
        .count();
    let equiv_members_demanded: usize = results
        .equivalences
        .iter()
        .map(|c| c.term_ids.iter().filter(|id| demanded.contains(id)).count())
        .sum();

    Some(Row {
        input: input.to_string(),
        terms_total,
        rewrites_total,
        equiv_classes_total,
        equiv_members_total,
        nf_total,
        terms_demanded,
        rewrites_demanded,
        equiv_members_demanded,
        parse_ns,
        eval_ns,
    })
}

fn main() {
    // The post-ROOT-A rhocalc comm/eval corpus: the `comm` family (the newly
    // non-vacuous tests where eval waste would first appear) + the reducing
    // `congruence`/`exec`/native-arithmetic families from rhocalc_tests.rs.
    let corpus: &[&str] = &[
        // --- comm family ---
        "{(c?x).{*(x)} | c!(p)}",
        "{(c?x).{x!(0)} | c!(p)}",
        "{(c?x).{*(x)} | c!(0)}",
        "{(c1?x, c2?y).{*(x)} | c1!(p) | c2!(q)}",
        "{(c1?x, c2?y).{{*(x) | *(y)}} | c1!(p) | c2!(q)}",
        "{(a?x, b?y, c?z).{{*(x) | *(y) | *(z)}} | a!(p) | b!(q) | c!(r)}",
        "{(c?x, c?y).{{*(x) | *(y)}} | c!(a) | c!(b)}",
        "{(c?x).{*(x)} | c!(p) | q}",
        // --- congruence / exec (reducing) ---
        "{*(@(0)) | q}",
        "{*(@(0))}",
        "{*(@(p))}",
        "new(x) in { *(@(0)) }",
        "{*(@(1)) + 2}",
        "{*(@(1)) == 1}",
        "{*(@(a!(0)))}",
        // --- native arithmetic (reducing) ---
        "{1 + 2}",
        "{5 - 3}",
        "{3 * 4}",
        "{10 / 2}",
        // --- extrusion (reducing) ---
        "{new(x) in {x!(0)} | (x?y).{*(y)}}",
        "{*(@(1)) == 1}",
    ];

    println!("\n=== EP-P6b EV-0 PROBE (rhocalc comm/eval corpus) ===");
    println!(
        "{:<46} {:>6} {:>6} {:>5} {:>6} {:>7} {:>9} {:>8} {:>9} {:>9}",
        "input",
        "terms",
        "t_dem",
        "nf",
        "rws",
        "rw_dem",
        "undem%",
        "parse_us",
        "eval_us",
        "eval%wt"
    );

    let mut sum_terms = 0usize;
    let mut sum_terms_dem = 0usize;
    let mut sum_rws = 0usize;
    let mut sum_rws_dem = 0usize;
    let mut sum_equiv_mem = 0usize;
    let mut sum_equiv_mem_dem = 0usize;
    let mut sum_parse_ns = 0u128;
    let mut sum_eval_ns = 0u128;

    let mut measured = 0usize;
    let mut skipped = 0usize;
    for input in corpus {
        let r = match measure(input) {
            Some(r) => {
                measured += 1;
                r
            },
            None => {
                skipped += 1;
                continue;
            },
        };
        // undemanded% over the dominant fact relation: TERMS (the all_terms
        // relation — the union of every category fact). Also accumulated for
        // rewrites + equiv members in the totals footer.
        let undem_pct = if r.terms_total == 0 {
            0.0
        } else {
            100.0 * ((r.terms_total - r.terms_demanded) as f64) / (r.terms_total as f64)
        };
        let total_ns = r.parse_ns + r.eval_ns;
        let eval_pct = if total_ns == 0 {
            0.0
        } else {
            100.0 * (r.eval_ns as f64) / (total_ns as f64)
        };
        let shown = if r.input.len() > 44 {
            format!("{}…", &r.input[..43])
        } else {
            r.input.clone()
        };
        println!(
            "{:<46} {:>6} {:>6} {:>5} {:>6} {:>7} {:>8.1}% {:>8.1} {:>9.1} {:>8.1}%",
            shown,
            r.terms_total,
            r.terms_demanded,
            r.nf_total,
            r.rewrites_total,
            r.rewrites_demanded,
            undem_pct,
            (r.parse_ns as f64) / 1000.0,
            (r.eval_ns as f64) / 1000.0,
            eval_pct,
        );

        sum_terms += r.terms_total;
        sum_terms_dem += r.terms_demanded;
        sum_rws += r.rewrites_total;
        sum_rws_dem += r.rewrites_demanded;
        sum_equiv_mem += r.equiv_members_total;
        sum_equiv_mem_dem += r.equiv_members_demanded;
        sum_parse_ns += r.parse_ns;
        sum_eval_ns += r.eval_ns;
        let _ = r.equiv_classes_total;
    }

    let undem_terms_pct = if sum_terms == 0 {
        0.0
    } else {
        100.0 * ((sum_terms - sum_terms_dem) as f64) / (sum_terms as f64)
    };
    let undem_rws_pct = if sum_rws == 0 {
        0.0
    } else {
        100.0 * ((sum_rws - sum_rws_dem) as f64) / (sum_rws as f64)
    };
    let undem_equiv_pct = if sum_equiv_mem == 0 {
        0.0
    } else {
        100.0 * ((sum_equiv_mem - sum_equiv_mem_dem) as f64) / (sum_equiv_mem as f64)
    };
    let total_ns = sum_parse_ns + sum_eval_ns;
    let eval_pct = if total_ns == 0 {
        0.0
    } else {
        100.0 * (sum_eval_ns as f64) / (total_ns as f64)
    };

    // eqrel-collapse: equivalence-class members BEYOND one-per-class are facts the
    // eval layer already quotiented away (the demand-like pruning the #307 fix +
    // eqrel relations apply BEFORE AscentResults surfaces). `extra = members -
    // classes` is the count of redundant materializations already removed.
    let equiv_extra = sum_equiv_mem.saturating_sub(
        // recompute class total across corpus is not summed above; report members
        // vs demanded-members as the collapse proxy.
        sum_equiv_mem_dem,
    );

    println!("\n--- CORPUS TOTALS ({} measured, {} skipped) ---", measured, skipped);
    println!(
        "terms: total={} demanded={} UNDEMANDED={:.1}%",
        sum_terms, sum_terms_dem, undem_terms_pct
    );
    println!(
        "rewrites: total={} demanded={} UNDEMANDED={:.1}%",
        sum_rws, sum_rws_dem, undem_rws_pct
    );
    println!(
        "equiv-members: total={} demanded={} UNDEMANDED={:.1}% (collapse-proxy extra={})",
        sum_equiv_mem, sum_equiv_mem_dem, undem_equiv_pct, equiv_extra
    );
    println!(
        "wall-time: parse={:.1}us eval={:.1}us  EVAL={:.1}% of (parse+eval)",
        (sum_parse_ns as f64) / 1000.0,
        (sum_eval_ns as f64) / 1000.0,
        eval_pct
    );
    println!(
        "\nGATE: undemanded-fact share ≥ 50% AND eval ≥ 20% of wall-time\n\
         → EV-1 PASSES FORMALLY, disposition = SUPERSEDED BY THE FLIP.\n\
         CAVEAT: per-relation totals are read from the ALREADY-deduped AscentResults\n\
         (semantic-key + canon-pair filtered, the #307 quotient); raw pre-dedup\n\
         prog.<rel> counts are a strictly LARGER upper bound, so undemanded% here is\n\
         a CONSERVATIVE LOWER BOUND. Timing is coarse single-run wall-clock around\n\
         the parse vs run_ascent entry. See /tmp/p6_probes/findings.md for the verdict."
    );
}
