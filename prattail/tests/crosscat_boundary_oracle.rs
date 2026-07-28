//! ★ O1 — THE MODEL AS AN EXECUTABLE ORACLE.
//!
//! # The gap this file closes
//!
//! `prattail/src/wpda_walker.rs::cgll_pure_crosscat_boundaries` walks the caller chain from an
//! operand frame looking for an enclosing projection whose floor should take the pending
//! operator. It has a VERIFIED MODEL —
//! `formal/rocq/prattail_wpda_runtime/theories/CollectionElementProjectionBoundary.v` — whose
//! `walk` is eight lines and whose theorems (`collelem_stops_walk`, `grouping_stops_walk`,
//! `collelem_no_handoff`) are proved with no admits.
//!
//! **The theorems were proved and the walk drifted from them twice anyway**, because nothing
//! executable connected the two. Both drifts were found as production parse failures, weeks apart:
//!
//! | # | drift | measured symptom |
//! |---|---|---|
//! | 1 | `GroupingMarker` absent from the stop set | `@(@@Nil!().subtract(a!(Nil)))!(Nil)` FAILED while its `{}`-delimited twin parsed |
//! | 2 | the stop test gated on `slot.xcat == 0` | a `(`-group (stamped `xcat = 3`) did not shield its interior from an outer `@`-projection floor |
//!
//! A proof is not a test. This file is the bridge: it transcribes the model INDEPENDENTLY —
//! straight from the Rocq source, in the model's own vocabulary — and property-tests
//! [`prattail::crosscat_boundary::classify_hop`], the single function the walker now uses, against
//! it over random caller chains.
//!
//! # Why the two sides are genuinely different computations
//!
//! The oracle side never calls `classify_hop`, `kind_is_rescoping` or `hop_has_explicit_target`.
//! It carries its own copies of the two facts those functions encode, written from the theory:
//!
//! * [`STOP_KINDS`] — the `SymbolKind ↦ Edge` table. `GroupingMarker ↦ Grouping`,
//!   `CollectionMarker ↦ CollElem`, `MixfixMarker`/`RuleAt(k>0) ↦ RuleSlot`, everything else
//!   `Pass`. **Removing `GroupingMarker` from the walker's stop set now fails
//!   [`the_walk_agrees_with_its_verified_model`] instead of shipping** — that is drift 1.
//! * [`oracle_hop_has_explicit_target`] — *"the target is INTRINSIC to the hop"*, i.e. `xcat == 4`
//!   (target = the hop's own `pushed_cat`) or `xcat == 3` with a recorded wrap. The inferred rows
//!   `xcat ∈ {1,2}` read their target OFF THE CALLER, so they are not intrinsic and must stop at a
//!   re-scoping caller. **Re-widening the exemption to `xcat != 0` fails the same test** — that is
//!   drift 2.
//!
//! # The correspondence, and the one refinement
//!
//! ```text
//!   walk []                = None_
//!   walk (Proj t   :: _)   = Found t
//!   walk (CollElem :: _)   = None_
//!   walk (Grouping :: _)   = None_
//!   walk (RuleSlot :: _)   = None_
//!   walk (Pass :: rest)    = walk rest
//! ```
//!
//! A hop contributes `Proj(floor)` when it resolves a target the engine RECOGNIZES the operator
//! at, and `Pass` otherwise; a re-scoping CALLER contributes a stop edge AFTER that hop's own
//! edge, which is exactly the model's `walk (Proj t :: Grouping :: rest) = Found t` — the hop
//! reports its own target and the walk goes no further. When the hop has no intrinsic evidence,
//! the stop edge comes FIRST and the hop contributes nothing: `walk (Pass :: Grouping :: _) =
//! None_`.
//!
//! The "recognizes" predicate has no counterpart in the model (which returns the first `Proj`
//! unconditionally), so it is threaded through both sides as an oracle-supplied function — the
//! same one — leaving the STOP/EVIDENCE/TARGET decisions as the only thing under test.

use mettail_prattail::crosscat_boundary::{classify_hop, HopFacts};
use mettail_prattail::wpda_runtime::SymbolKind;

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  THE MODEL — transcribed from `CollectionElementProjectionBoundary.v`, in its own vocabulary.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// `Inductive Edge` of the Rocq model.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Edge {
    /// `Proj : nat -> Edge` — a projection target frame, carrying `target_floor`.
    Proj(u16),
    /// `CollElem` — a `CollectionElement` frame (the 2026-07-25 addition to the stop set).
    CollElem,
    /// `Grouping` — a `GroupingMarker` (the pre-existing stop `grouping_stops_walk` names).
    Grouping,
    /// `RuleSlot` — `PrefixRuleEntry{ip>0}` / `MixfixMarker`.
    RuleSlot,
    /// `Pass` — a transparent edge the walk passes through.
    Pass,
}

/// `Inductive Target` of the Rocq model.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Target {
    Found(u16),
    NoneT,
}

/// `Fixpoint walk (es : list Edge) : Target` — transcribed line for line.
fn model_walk(es: &[Edge]) -> Target {
    match es.first() {
        None => Target::NoneT,
        Some(Edge::Proj(t)) => Target::Found(*t),
        Some(Edge::CollElem) => Target::NoneT,
        Some(Edge::Grouping) => Target::NoneT,
        Some(Edge::RuleSlot) => Target::NoneT,
        Some(Edge::Pass) => model_walk(&es[1..]),
    }
}

/// ★ THE `SymbolKind ↦ Edge` TABLE — the oracle's own copy of the stop set, written from the
/// Rocq file's `{ Grouping, CollElem, RuleSlot }` and NOT from the walker's `kind_is_rescoping`.
///
/// `None` means the caller is transparent, so the chain may ascend past it.
fn stop_edge_of(kind: SymbolKind) -> Option<Edge> {
    match kind {
        SymbolKind::GroupingMarker => Some(Edge::Grouping),
        SymbolKind::CollectionMarker => Some(Edge::CollElem),
        SymbolKind::MixfixMarker => Some(Edge::RuleSlot),
        SymbolKind::RuleAt(k) if k > 0 => Some(Edge::RuleSlot),
        _ => None,
    }
}

/// The oracle's own copy of *"the hop's target is INTRINSIC to the hop"*.
fn oracle_hop_has_explicit_target(xcat: u8, xcat_wrap: u16) -> bool {
    match xcat {
        // `CrossCatProjection`: the target is `pushed_cat`, the projection's OWN result category.
        4 => true,
        // `CrossCatLhsReentry` WITH a recorded wrap: the wrap is stored on the hop.
        3 => xcat_wrap != u16::MAX,
        // Everything else reads its target off the CALLER (or has none), so it is not intrinsic.
        _ => false,
    }
}

/// The oracle's own boundary-target resolution, from the same three rows the model's `Proj`
/// carries.
fn oracle_target(hop: &HopFacts) -> Option<(u16, u16)> {
    match hop.xcat {
        4 => Some((hop.pushed_cat, hop.xcat_bp)),
        1 | 2 => hop.caller_kind.map(|_| (hop.caller_cat, hop.xcat_bp)),
        3 if hop.xcat_wrap != u16::MAX => Some((hop.xcat_wrap, hop.xcat_bp)),
        _ => None,
    }
}

/// Build the model's edge list from a caller chain, using ONLY the oracle's own tables.
///
/// Per hop: if the caller re-scopes and the hop has no intrinsic evidence, the stop edge comes
/// first and terminates the list. Otherwise the hop contributes `Proj(floor)` (when it resolves a
/// target the operator is recognized at) or `Pass`, and then — if the caller re-scopes — the stop
/// edge, which terminates the list.
fn oracle_edges(chain: &[HopFacts], recognized: &dyn Fn(u16) -> bool) -> Vec<Edge> {
    let mut es = Vec::with_capacity(chain.len() * 2);
    for hop in chain {
        let stop = hop.caller_kind.and_then(stop_edge_of);
        let explicit = oracle_hop_has_explicit_target(hop.xcat, hop.xcat_wrap);
        if stop.is_some() && !explicit {
            es.push(stop.expect("checked is_some"));
            return es;
        }
        match oracle_target(hop) {
            Some((cat, floor)) if recognized(cat) => es.push(Edge::Proj(normalise_floor(floor))),
            _ => es.push(Edge::Pass),
        }
        if let Some(stop) = stop {
            es.push(stop);
            return es;
        }
    }
    es
}

/// `u16::MAX` is the walker's "no floor" sentinel and maps to floor 0 (the walk's own
/// `if target_floor == u16::MAX { 0 }`).
fn normalise_floor(floor: u16) -> u16 {
    if floor == u16::MAX {
        0
    } else {
        floor
    }
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  THE SUBJECT — the walker's own loop, in linear-chain form, driven by `classify_hop`.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// The `cgll_pure_crosscat_boundaries` loop restricted to a LINEAR caller chain (one parent per
/// frame), which is the shape the model quantifies over. The GSS fan is a union of such chains,
/// and the loop's per-chain behaviour is exactly this.
fn walker_walk(chain: &[HopFacts], recognized: &dyn Fn(u16) -> bool) -> Target {
    for hop in chain {
        let verdict = classify_hop(hop);
        if verdict.dies_before_mapping {
            return Target::NoneT;
        }
        if let Some((cat, floor)) = verdict.target {
            if recognized(cat) {
                return Target::Found(normalise_floor(floor));
            }
            // Target does not recognize the token — continue the walk.
        }
        if verdict.stops_after_mapping {
            return Target::NoneT;
        }
    }
    Target::NoneT
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  0 — TEETH. The oracle must be able to fail, and the model must have the shape it claims.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// The three theorems this oracle exists to keep true, transcribed as concrete rows so a reader
/// can check the correspondence by eye before trusting the property test.
#[test]
fn the_transcribed_model_reproduces_its_own_theorems() {
    // `collelem_stops_walk` / `grouping_stops_walk`: a stop edge at the head returns `None_`.
    assert_eq!(model_walk(&[Edge::CollElem, Edge::Proj(7)]), Target::NoneT);
    assert_eq!(model_walk(&[Edge::Grouping, Edge::Proj(7)]), Target::NoneT);
    assert_eq!(model_walk(&[Edge::RuleSlot, Edge::Proj(7)]), Target::NoneT);
    // `collelem_stops_walk_through_pass`: through any transparent lineage.
    assert_eq!(model_walk(&[Edge::Pass, Edge::CollElem, Edge::Proj(7)]), Target::NoneT);
    // The hop's OWN evidence terminates the walk: `walk (Proj t :: Grouping :: rest) = Found t`.
    assert_eq!(model_walk(&[Edge::Proj(3), Edge::Grouping]), Target::Found(3));
    // And the empty chain has no handoff.
    assert_eq!(model_walk(&[]), Target::NoneT);
}

/// The subject and the oracle must DISAGREE on a deliberately corrupted chain, or agreement
/// proves nothing. Here the corruption is the oracle's: it is asked to treat a `GroupingMarker`
/// as transparent, which is exactly drift 1, and the walker must then differ from it.
#[test]
fn the_oracle_separates() {
    // A `Grouping` caller above a hop with NO intrinsic evidence: the walker must stop.
    let chain = vec![
        HopFacts {
            xcat: 1,
            xcat_bp: 5,
            xcat_wrap: u16::MAX,
            pushed_cat: 9,
            caller_kind: Some(SymbolKind::GroupingMarker),
            caller_cat: 4,
        },
        HopFacts {
            xcat: 4,
            xcat_bp: 2,
            xcat_wrap: u16::MAX,
            pushed_cat: 8,
            caller_kind: Some(SymbolKind::Return),
            caller_cat: 4,
        },
    ];
    let rec = |_: u16| true;
    assert_eq!(
        walker_walk(&chain, &rec),
        Target::NoneT,
        "a re-scoping caller must stop a hop that carries no intrinsic evidence"
    );
    // The DRIFT-1 model (grouping treated as transparent) reaches the outer projection instead.
    fn drifted_edges(chain: &[HopFacts], recognized: &dyn Fn(u16) -> bool) -> Vec<Edge> {
        let mut es = Vec::new();
        for hop in chain {
            match oracle_target(hop) {
                Some((cat, floor)) if recognized(cat) => {
                    es.push(Edge::Proj(normalise_floor(floor)))
                },
                _ => es.push(Edge::Pass),
            }
        }
        es
    }
    assert_ne!(
        model_walk(&drifted_edges(&chain, &rec)),
        walker_walk(&chain, &rec),
        "★ the oracle cannot observe drift 1 at all — it agrees with a model that treats a \
         `GroupingMarker` as transparent, so this whole file would be vacuous"
    );
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  1 — THE PROPERTY. Over random chains, the walk agrees with its verified model.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// A small deterministic PRNG, so a failure is reproducible from the printed seed without a
/// proptest dependency in this crate.
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0 >> 11
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

/// The caller kinds a chain may carry — every stop kind, plus transparent representatives.
const KINDS: [SymbolKind; 8] = [
    SymbolKind::GroupingMarker,
    SymbolKind::CollectionMarker,
    SymbolKind::MixfixMarker,
    SymbolKind::RuleAt(0), // ip == 0 ⇒ NOT a stop (the `k > 0` conjunct)
    SymbolKind::RuleAt(2), // ip  > 0 ⇒ a stop
    SymbolKind::CategoryEntry,
    SymbolKind::InfixContinuation,
    SymbolKind::Return,
];

fn random_chain(rng: &mut Lcg) -> Vec<HopFacts> {
    let len = 1 + rng.below(6) as usize;
    (0..len)
        .map(|_| {
            let has_caller = rng.below(10) > 0; // 1-in-10 seed frames (no caller)
            HopFacts {
                // Every stamp the walker can see, including the two the drifts turned on.
                xcat: rng.below(5) as u8,
                xcat_bp: match rng.below(4) {
                    0 => u16::MAX,
                    n => n as u16,
                },
                xcat_wrap: match rng.below(3) {
                    0 => u16::MAX,
                    n => 10 + n as u16,
                },
                pushed_cat: rng.below(4) as u16,
                caller_kind: if has_caller {
                    Some(KINDS[rng.below(KINDS.len() as u64) as usize])
                } else {
                    None
                },
                caller_cat: rng.below(4) as u16,
            }
        })
        .collect()
}

/// ★ THE ORACLE. For every random caller chain and every "recognizes" oracle, the walker's own
/// per-hop decision composes to exactly the model's `walk`.
#[test]
fn the_walk_agrees_with_its_verified_model() {
    let mut rng = Lcg(0x5EED_0000_0000_0001);
    let mut mismatches: Vec<String> = Vec::new();
    let mut found = 0usize;
    let mut none = 0usize;
    const CASES: usize = 20_000;
    for case in 0..CASES {
        let chain = random_chain(&mut rng);
        // Two recognition oracles: everything recognized, and a category-parity oracle, so a
        // "continue past an unrecognized target" path is exercised as well as the direct hit.
        for (rec_name, rec) in [
            ("all", &(|_: u16| true) as &dyn Fn(u16) -> bool),
            ("even", &(|c: u16| c % 2 == 0) as &dyn Fn(u16) -> bool),
        ] {
            let subject = walker_walk(&chain, rec);
            let model = model_walk(&oracle_edges(&chain, rec));
            match subject {
                Target::Found(_) => found += 1,
                Target::NoneT => none += 1,
            }
            if subject != model {
                mismatches.push(format!(
                    "  case {case} (recognizes={rec_name}):\n      chain   {chain:?}\n      \
                     walker  {subject:?}\n      model   {model:?}\n      edges   {:?}",
                    oracle_edges(&chain, rec)
                ));
                if mismatches.len() >= 5 {
                    break;
                }
            }
        }
        if mismatches.len() >= 5 {
            break;
        }
    }
    assert!(
        mismatches.is_empty(),
        "★ the cross-category boundary walk diverged from `CollectionElementProjectionBoundary.v` \
         on {} chain(s). The model is the specification; the walk drifted from it twice before \
         this oracle existed (`GroupingMarker` missing from the stop set; the stop test gated on \
         `xcat == 0`), each time shipping and each time found as a production parse \
         failure.\n{}",
        mismatches.len(),
        mismatches.join("\n"),
    );
    // NON-VACUITY: the corpus must exercise BOTH outcomes, or "agreement" could mean "both sides
    // always say None_".
    assert!(
        found > CASES / 20,
        "the random corpus produced only {found} `Found` outcomes out of {} — the generator is \
         not reaching the projection-target path and the agreement is close to vacuous",
        CASES * 2
    );
    assert!(none > CASES / 20, "the random corpus produced only {none} `None_` outcomes");
}
