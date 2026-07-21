//! E-3 T-INCR — incremental single-rewrite append over the memoized in-Rho
//! compilation artifacts (pgmcp experiment 146, H3v2; design §4.3 + red-team
//! amendments EM-2/EM-3/EM-4; bench-only extension surface per user decision D3).
//!
//! Runtime rule extension used to mean: new definition source → new cache key →
//! WHOLESALE re-derivation (full `syn` reconstruct + full ruleset compile — which
//! itself RE-RUNS the entire lowering pipeline through `rho_net_injection_sites`,
//! EM-4). [`extend_in_rho_artifacts`] derives the EXTENDED source's
//! [`CompiledInRhoArtifacts`] from the BASE artifacts instead:
//!
//! 1. **Fragment parse + source splice (EM-3)** — the appended rewrite is parsed
//!    by the production fragment parser
//!    ([`mettail_ast::language::parse_rewrite_fragment`]) and spliced into the
//!    base source's sole `rewrites { … }` block
//!    ([`mettail_ast::language::splice_rewrite_into_source`]), producing the
//!    extended source STRING — the memo key AND the batch arm's input. The whole
//!    source is never re-parsed on the incremental path.
//! 2. **Auto-inject ordering repair (EM-2)** — `reconstruct_language_def` appends
//!    auto-injected rewrites AFTER user rewrites, and both the definition
//!    fingerprint (`identity.rs`, order-sensitive) and every plan row
//!    (`rho_net.rs::add_rewrites`, declaration-index-embedding) depend on that
//!    order. A naive `clone def + push` would yield `[user…, auto…, new]` where
//!    batch derivation yields `[user…, new, auto…]`. The repair: strip EVERY
//!    `is_auto_injected` term AND rewrite (stripping only rewrites is
//!    insufficient — the auto-injected TERMS satisfy
//!    `classify_simple_projection_shape` and would land in
//!    `emit_auto_injection_rules`'s user-injection skip-list, suppressing the
//!    re-emission entirely), push the new USER rewrite, re-run
//!    [`emit_auto_injection_rules`], and re-extend — the exact batch replay, so
//!    `def_incremental ≡ reconstruct(extended_source)` as a value, which is what
//!    reduces the FULL Par re-emission's byte-equality to pure-function identity.
//! 3. **Ruleset bypass (EM-4b)** — the extended
//!    [`InRhoMatchingRuleset`] is assembled WITHOUT
//!    [`compile_in_rho_matching_ruleset`] (whose internal
//!    `rho_net_injection_sites` re-runs the whole lowering — the win would
//!    collapse): the base automaton is CLONED and [`SetAutomaton::extend`]ed with
//!    only the new rule's converted pattern (append-only interning, StateId
//!    prefix-stable), and the new rule's accept channel is derived PER-RULE from
//!    its LHS pattern content ([`crate::rho_net::lhs_pattern_trace_channel`] —
//!    fingerprint- and index-independent, EM-6).
//! 4. **FULL Par re-emission (the fingerprint constraint)** — the incremental
//!    artifacts' `lowered`/`installed_par` cells start UNSET; forcing them runs
//!    the SAME pure pipeline on the EM-2-identical extended def, re-emitting every
//!    Par artifact wholesale under the new whole-definition fingerprint. This is
//!    the pre-registered CEILING (`1 − Par-emission share`), measured — not an
//!    oversight.
//!
//! ## Fail-closed family admission (the coordinator pin)
//!
//! The incremental path admits EXACTLY the frozen H3v2 family: a SINGLE appended
//! base-shape rewrite (premise-free, structurally convertible, AC-free — the W-B
//! extension-ladder shape) over a base language whose ruleset has no
//! native/AC/structural-AC/nested-AC dispatch families (those families embed the
//! fingerprint in pre-built receiver `Par`s, or occupy declaration-index-derived
//! `PatternId`s that SHIFT on append — reusing them would be silently wrong, and
//! recomputing them re-runs the full lowering). Everything else takes the typed
//! [`IncrementalUnsupported`] → full re-derive FALLBACK (the batch path), with
//! the reason recorded — proven equivalent (not assumed) by the standing
//! equivalence-gate tests. Extending admission to further families is a RECORDED
//! follow-up candidate (EM-4c style), out of this leg's scope.
//!
//! Contextual (congruence) dispatch entries ARE reused: they are keyed by rule
//! label + premise-content hash + LHS hole paths — fingerprint- and
//! index-independent — and the auto-injected congruence rewrites (the EM-2
//! anti-vacuity case) land exactly there.

use std::sync::Arc;

use dovetail::set_automaton::PatternId;
use mettail_ast::auto_inject::emit_auto_injection_rules;
use mettail_ast::identity::language_definition_fingerprint;
use mettail_ast::language::{parse_rewrite_fragment, splice_rewrite_into_source, RewriteRule};

use crate::rho_net::lhs_pattern_trace_channel;
use crate::rho_net_cache::{
    cached_in_rho_artifacts, insert_in_rho_artifacts, CompiledInRhoArtifacts,
};
use crate::rho_net_lower::{
    is_top_level_substitution, lower_lhs_vars, lower_rhs, rewrite_pattern_unsupported,
};
use crate::rho_net_ruleset::{convert_lhs_pattern, InRhoMatchingRuleset};

/// Why an append is NOT admitted by the incremental path (fail-closed → the full
/// re-derive fallback; design §4.3 "only append-of-rewrite admitted"). Every
/// variant names the violated admission condition so a fallback is a RECORDED
/// disposition, never a silent scope-down.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IncrementalUnsupported {
    /// The fragment parsed to zero or more than one rewrite — the frozen H3v2
    /// scope is a SINGLE-rewrite append.
    NotASingleRewrite { parsed: usize },
    /// The appended rewrite carries premises (congruence / behavioral / relational
    /// / freshness / …) — outside the base-shape family (premise lowering spans
    /// consistency inputs, semantic guards, and whole other rule families).
    PremisedRewrite,
    /// The appended rewrite carries a type context — outside the W-B base shape.
    TypeContextedRewrite,
    /// The appended rewrite's name collides with an existing rewrite — the
    /// label-keyed correlation surfaces would become ambiguous; conservative
    /// fail-close.
    DuplicateRuleName { name: String },
    /// The LHS has no structural set-automaton image (binder / subst /
    /// collection-search), per [`convert_lhs_pattern`]'s typed reject.
    UnconvertibleLhs { reject: String },
    /// The LHS converts but contains an `AcApp` — the AC path, not an automaton
    /// entry.
    AcLhs,
    /// The rewrite would NOT lower to a `BaseRewrite` σ-receiver (subst-RHS /
    /// unsupported LHS-var or RHS family) — it would have no injection site, so
    /// the batch ruleset would DEFER it while the bypass would have admitted it.
    NotBaseRewriteLowering { family: String },
    /// The base ruleset carries native match entries, whose `PatternId`s are
    /// `def.rewrites.len() + i` and SHIFT on append (the extend would collide with
    /// or mis-order the batch automaton).
    BaseHasNativeDispatch,
    /// The base ruleset carries AC dispatch entries, whose pre-built RHS `Par`s
    /// embed the (now stale) fingerprint.
    BaseHasAcDispatch,
    /// The base ruleset carries structural-AC dispatch entries (fingerprint-bearing
    /// receiver shapes).
    BaseHasStructuralAcDispatch,
    /// The base ruleset carries nested structural-AC dispatch entries
    /// (fingerprint-bearing receiver shapes).
    BaseHasNestedStructuralAcDispatch,
    /// An auto-injected rewrite IS an automaton entry in the base ruleset — the
    /// EM-2 positional hazard (the appended user rule takes the first auto's
    /// declaration index, so a positional auto entry would break StateId/PatternId
    /// prefix parity). Asserted-not-assumed per the frozen registration.
    AutoInjectedAutomatonEntry { rule_label: String },
    /// The base definition's auto-injected rewrites are not a suffix of its
    /// rewrite list — stripping them would shift the surviving user rewrites'
    /// declaration indices, invalidating every base automaton `PatternId`.
    AutoInjectedNotASuffix,
}

impl std::fmt::Display for IncrementalUnsupported {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotASingleRewrite { parsed } => {
                write!(f, "the fragment parsed to {parsed} rewrites (exactly 1 admitted)")
            },
            Self::PremisedRewrite => write!(f, "the appended rewrite carries premises"),
            Self::TypeContextedRewrite => write!(f, "the appended rewrite carries a type context"),
            Self::DuplicateRuleName { name } => {
                write!(f, "the appended rewrite's name `{name}` already exists")
            },
            Self::UnconvertibleLhs { reject } => {
                write!(f, "the LHS has no structural automaton image: {reject}")
            },
            Self::AcLhs => write!(f, "the LHS is an AC pattern (no positional automaton image)"),
            Self::NotBaseRewriteLowering { family } => {
                write!(f, "the rewrite would not lower to a BaseRewrite σ-receiver: {family}")
            },
            Self::BaseHasNativeDispatch => {
                write!(f, "the base ruleset has native match entries (PatternIds shift on append)")
            },
            Self::BaseHasAcDispatch => {
                write!(f, "the base ruleset has AC dispatch entries (fingerprint-embedded RHS Pars)")
            },
            Self::BaseHasStructuralAcDispatch => {
                write!(f, "the base ruleset has structural-AC dispatch entries")
            },
            Self::BaseHasNestedStructuralAcDispatch => {
                write!(f, "the base ruleset has nested structural-AC dispatch entries")
            },
            Self::AutoInjectedAutomatonEntry { rule_label } => {
                write!(f, "auto-injected rewrite `{rule_label}` is an automaton entry")
            },
            Self::AutoInjectedNotASuffix => {
                write!(f, "the base definition's auto-injected rewrites are not a suffix")
            },
        }
    }
}

/// The outcome of [`extend_in_rho_artifacts`]: which path derived the extended
/// artifacts. Both variants carry artifacts derived for (and memoized under) the
/// SAME extended source, so a consumer's behavior never depends on the path — only
/// its cost does (which is exactly what H3 measures).
pub enum IncrementalExtendOutcome {
    /// The incremental path ran: fragment parse + EM-2 def rebuild + fingerprint
    /// recompute + automaton extend + per-rule accept channel; the ruleset cell is
    /// seeded, the emission cells derive on demand (the FULL Par re-emission).
    Incremental(Arc<CompiledInRhoArtifacts>),
    /// The append was outside the admitted family: the full re-derive fallback ran
    /// (the batch path, via the source-keyed cache), with the refusing condition
    /// recorded.
    FellBack {
        artifacts: Arc<CompiledInRhoArtifacts>,
        reason: IncrementalUnsupported,
    },
}

impl IncrementalExtendOutcome {
    /// The derived artifacts, whichever path produced them.
    pub fn artifacts(&self) -> &Arc<CompiledInRhoArtifacts> {
        match self {
            Self::Incremental(artifacts) => artifacts,
            Self::FellBack { artifacts, .. } => artifacts,
        }
    }

    /// `Some(reason)` iff the fail-closed fallback ran.
    pub fn fallback_reason(&self) -> Option<&IncrementalUnsupported> {
        match self {
            Self::Incremental(_) => None,
            Self::FellBack { reason, .. } => Some(reason),
        }
    }
}

/// Derive the artifacts of `base`'s definition source EXTENDED by one appended
/// rewrite fragment (a `Name . |- lhs ~> rhs ;` line), and memoize them under the
/// extended source's hash — the incremental analogue of
/// [`cached_in_rho_artifacts`] on the spliced source.
///
/// Returns `Err` only when no artifacts can be derived AT ALL (the fragment does
/// not parse, the base source has no unambiguous `rewrites { … }` block to splice
/// into, or the extended source fails the fallback's reconstruction) — the same
/// failures the batch path reports for the same input. An append outside the
/// admitted family is NOT an error: it is the recorded fail-closed
/// [`IncrementalExtendOutcome::FellBack`] (full re-derivation).
///
/// **Bench-only extension surface (D3):** no production entry point, generated
/// body, or macro references this function; the E-3 harness and the equivalence
/// gate are its only consumers. It lives here (not in the harness) because the
/// admission checks and the ruleset assembly need this crate's crate-private
/// pipeline seams.
///
/// In debug builds every INCREMENTAL derivation is cross-checked field-by-field
/// against the full batch derivation of the extended source (design §4.3
/// "debug builds cross-check byte-equality") — a drift panics the test, it never
/// ships a wrong artifact silently.
pub fn extend_in_rho_artifacts(
    base: &Arc<CompiledInRhoArtifacts>,
    rewrite_fragment: &str,
) -> Result<IncrementalExtendOutcome, String> {
    // EM-3: the extended source STRING — the memo key and the batch arm's input.
    let extended_source = splice_rewrite_into_source(&base.definition_source, rewrite_fragment)
        .map_err(|err| format!("cannot splice the rewrite fragment: {err}"))?;
    let parsed = parse_rewrite_fragment(rewrite_fragment)
        .map_err(|err| format!("the rewrite fragment does not parse: {err}"))?;

    match admit_and_extend(base, &extended_source, parsed) {
        Ok(artifacts) => {
            #[cfg(debug_assertions)]
            cross_check_against_batch(&artifacts, &extended_source);
            insert_in_rho_artifacts(&artifacts);
            Ok(IncrementalExtendOutcome::Incremental(artifacts))
        },
        Err(reason) => {
            // Fail-closed fallback: the batch path on the identical extended source
            // (memoized under the same key the incremental path would have used).
            let artifacts = cached_in_rho_artifacts(&extended_source)?;
            Ok(IncrementalExtendOutcome::FellBack { artifacts, reason })
        },
    }
}

/// The admission checks + the incremental derivation itself. `Err` is an admission
/// refusal (→ fallback), never a derivation failure.
fn admit_and_extend(
    base: &Arc<CompiledInRhoArtifacts>,
    extended_source: &str,
    mut parsed: Vec<RewriteRule>,
) -> Result<Arc<CompiledInRhoArtifacts>, IncrementalUnsupported> {
    // ── Family admission: a SINGLE base-shape rewrite (the frozen H3v2 scope). ──
    if parsed.len() != 1 {
        return Err(IncrementalUnsupported::NotASingleRewrite { parsed: parsed.len() });
    }
    let new_rewrite = parsed.pop().expect("length checked to be exactly one");
    if !new_rewrite.premises.is_empty() {
        return Err(IncrementalUnsupported::PremisedRewrite);
    }
    if !new_rewrite.type_context.is_empty() {
        return Err(IncrementalUnsupported::TypeContextedRewrite);
    }
    let new_name = new_rewrite.name.to_string();
    if base.def.rewrites.iter().any(|rewrite| rewrite.name == new_rewrite.name) {
        return Err(IncrementalUnsupported::DuplicateRuleName { name: new_name });
    }

    // ── Base-ruleset admission (the fail-closed dispatch-family matrix). ──
    let base_ruleset = base.ruleset();
    if !base_ruleset.native_dispatch.is_empty() {
        return Err(IncrementalUnsupported::BaseHasNativeDispatch);
    }
    if !base_ruleset.ac_dispatch.is_empty() {
        return Err(IncrementalUnsupported::BaseHasAcDispatch);
    }
    if !base_ruleset.structural_ac_dispatch.is_empty() {
        return Err(IncrementalUnsupported::BaseHasStructuralAcDispatch);
    }
    if !base_ruleset.nested_structural_ac_dispatch.is_empty() {
        return Err(IncrementalUnsupported::BaseHasNestedStructuralAcDispatch);
    }
    // EM-2 (asserted, not assumed): no auto-injected rewrite is an automaton entry
    // — with the native emptiness above, every entry's `PatternId` is a rewrite
    // declaration index, and it must name a USER rewrite (the appended rule takes
    // the first auto's index, shifting every auto by one).
    let base_view = base_ruleset.automaton.view();
    for entry in 0..base_view.entry_count() {
        let id = base_view.entry_id(entry);
        match base.def.rewrites.get(id.0) {
            Some(rewrite) if !rewrite.is_auto_injected => {},
            Some(rewrite) => {
                return Err(IncrementalUnsupported::AutoInjectedAutomatonEntry {
                    rule_label: rewrite.name.to_string(),
                });
            },
            None => return Err(IncrementalUnsupported::BaseHasNativeDispatch),
        }
    }
    // The strip below compacts rewrite indices; the base automaton's `PatternId`s
    // stay valid only if the auto-injected rewrites are a SUFFIX (every
    // reconstruct-produced def satisfies this — `emit_auto_injection_rules` output
    // is appended after the user rewrites — but it is CHECKED, never assumed).
    let user_rewrite_count =
        base.def.rewrites.iter().take_while(|rewrite| !rewrite.is_auto_injected).count();
    if base.def.rewrites[user_rewrite_count..].iter().any(|rewrite| !rewrite.is_auto_injected) {
        return Err(IncrementalUnsupported::AutoInjectedNotASuffix);
    }

    // ── EM-2: the auto-inject ordering repair (the exact batch replay). ──
    // Strip EVERY auto-injected term AND rewrite (module docs: stripping only
    // rewrites leaves the auto TERMS acting as emit-skip-list entries), push the
    // new USER rewrite at the batch position, re-run the auto-injection, and
    // re-extend — producing the SAME value `reconstruct(extended_source)` yields.
    let mut def = base.def.clone();
    def.terms.retain(|term| !term.is_auto_injected);
    def.rewrites.retain(|rewrite| !rewrite.is_auto_injected);
    debug_assert_eq!(def.rewrites.len(), user_rewrite_count);
    let new_index = def.rewrites.len();
    def.rewrites.push(new_rewrite.clone());
    let auto = emit_auto_injection_rules(&def);
    def.terms.extend(auto.terms);
    def.rewrites.extend(auto.rewrites);

    // The whole-definition fingerprint (user decision D1: KEEP whole-def FNV —
    // recomputed, never patched).
    let language_fingerprint = language_definition_fingerprint(&def);

    // ── Deep admission: the appended rule must be a BATCH automaton entry. ──
    // `convert_lhs_pattern` is total (typed reject); the premise-free reduction of
    // `lower_base_rewrite` is: LHS σ-vars collect ∧ RHS is not a top-level subst ∧
    // RHS reflects ∧ the defensive pattern-tree detector agrees. (With empty
    // premises, `is_lossless_cast_congruence` — which keys on a
    // `SyntheticInjGuard` premise — and the premise-safety check are vacuous.)
    let pattern = match convert_lhs_pattern(&new_rewrite.left) {
        Ok(pattern) => pattern,
        Err(reject) => {
            return Err(IncrementalUnsupported::UnconvertibleLhs { reject: format!("{reject:?}") });
        },
    };
    let sigma_vars = match lower_lhs_vars(&new_rewrite.left) {
        Ok(vars) => vars,
        Err(family) => {
            return Err(IncrementalUnsupported::NotBaseRewriteLowering {
                family: format!("{family:?}"),
            });
        },
    };
    if is_top_level_substitution(&new_rewrite.right) {
        return Err(IncrementalUnsupported::NotBaseRewriteLowering {
            family: "SubstitutionRhs".to_string(),
        });
    }
    if let Err(family) =
        lower_rhs(&new_rewrite.right, &sigma_vars, sigma_vars.len(), &language_fingerprint)
    {
        return Err(IncrementalUnsupported::NotBaseRewriteLowering {
            family: format!("{family:?}"),
        });
    }
    if let Some(family) = rewrite_pattern_unsupported(&new_rewrite.left, &new_rewrite.right) {
        return Err(IncrementalUnsupported::NotBaseRewriteLowering {
            family: format!("{family:?}"),
        });
    }

    // ── EM-4b: the ruleset bypass — extend, never recompile. ──
    // The batch entry sequence for this def is [user entries by index…, new] (the
    // autos are never entries — asserted above — and there are no natives), which
    // is EXACTLY the base automaton's sequence plus one append: StateId assignment
    // is prefix-identical to batch by the dovetail extend invariant.
    let mut automaton = base_ruleset.automaton.clone();
    if automaton.extend([(PatternId(new_index), pattern)]).is_err() {
        // Unreachable in practice (`convert_lhs_pattern` produced it and the AC
        // shape was not taken), kept total + fail-closed.
        return Err(IncrementalUnsupported::AcLhs);
    }
    let mut accept_channels = Vec::with_capacity(base_ruleset.accept_channels.len() + 1);
    accept_channels.extend(base_ruleset.accept_channels.iter().cloned());
    // The per-rule accept channel (EM-6): pattern-content-hashed, the SAME
    // derivation `add_rewrites` embeds as the rule's first input channel and
    // `rho_net_injection_sites` surfaces as the σ-receiver site.
    accept_channels.push((PatternId(new_index), lhs_pattern_trace_channel(&new_rewrite.left).name));

    let ruleset = InRhoMatchingRuleset {
        automaton,
        accept_channels,
        language_fingerprint,
        // Deferred rewrites are label+reason records (index-free); the appended
        // rule is NOT deferred (it is the new entry), and the base's deferrals are
        // unchanged by the append.
        deferred: base_ruleset.deferred.clone(),
        // Empty by the admission matrix above.
        native_dispatch: Vec::new(),
        ac_dispatch: Vec::new(),
        structural_ac_dispatch: Vec::new(),
        nested_structural_ac_dispatch: Vec::new(),
        // Reused: label + premise-content-hash + LHS-path keyed (fingerprint- and
        // index-independent) — this is where the EM-2 auto-injected congruence
        // rewrites live.
        contextual_dispatch: base_ruleset.contextual_dispatch.clone(),
    };

    Ok(Arc::new(CompiledInRhoArtifacts::from_incremental_parts(
        extended_source.to_string(),
        def,
        ruleset,
    )))
}

/// Debug-build cross-check (design §4.3): the incremental artifacts must equal the
/// FULL batch derivation of the extended source, field by field. Panics on drift —
/// the fail-closed alternative to silently serving a diverged artifact. Release
/// builds (every measurement run) skip this entirely.
#[cfg(debug_assertions)]
fn cross_check_against_batch(incremental: &Arc<CompiledInRhoArtifacts>, extended_source: &str) {
    let def = crate::reconstruct_language_def(extended_source)
        .expect("the extended source reconstructs (the incremental path derived from it)");
    assert_eq!(
        language_definition_fingerprint(&def),
        language_definition_fingerprint(&incremental.def),
        "T-INCR cross-check: the EM-2 def rebuild must fingerprint-match the batch reconstruct"
    );
    let batch = crate::rho_net_ruleset::compile_in_rho_matching_ruleset(&def);
    let ours = incremental.ruleset();
    assert_eq!(
        ours.language_fingerprint, batch.language_fingerprint,
        "T-INCR cross-check: ruleset fingerprint"
    );
    assert_eq!(ours.automaton, batch.automaton, "T-INCR cross-check: automaton (entries+states)");
    assert_eq!(
        ours.accept_channels, batch.accept_channels,
        "T-INCR cross-check: accept channels"
    );
    assert_eq!(ours.deferred, batch.deferred, "T-INCR cross-check: deferred set");
    assert_eq!(
        ours.contextual_dispatch, batch.contextual_dispatch,
        "T-INCR cross-check: contextual dispatch"
    );
    assert!(
        batch.native_dispatch.is_empty()
            && batch.ac_dispatch.is_empty()
            && batch.structural_ac_dispatch.is_empty()
            && batch.nested_structural_ac_dispatch.is_empty(),
        "T-INCR cross-check: the admission matrix admitted a base whose BATCH ruleset grows a \
         dispatch family the incremental ruleset left empty"
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rho_net_cache::cached_in_rho_artifacts;

    /// A minimal base-shape language (the SwapDemo-scale analogue of the W-B
    /// extension ladder's base).
    const BASE_SOURCE: &str = r#"
        name: IncrSmoke,
        types { Proc }
        terms {
            Wrap . x:Proc |- "wrap" "(" x ")" : Proc ;
            S . x:Proc |- "s" "(" x ")" : Proc ;
            R0 . x:Proc |- "r0" "(" x ")" : Proc ;
            R1 . x:Proc |- "r1" "(" x ")" : Proc ;
        }
        equations {}
        rewrites {
            M0 . |- (R0 (S x)) ~> (Wrap x) ;
            M1 . |- (R1 (S x)) ~> (Wrap x) ;
        }
    "#;

    /// The EM-2 anti-vacuity base: native Int/BigInt types make auto-injection
    /// emit the `IntToBigInt` term + the `IntToBigIntCong` congruence rewrite.
    const AUTO_INJECT_BASE_SOURCE: &str = r#"
        name: IncrAutoInject,
        types {
            Proc
            ![i32] as Int
            ![mettail_runtime::CanonicalBigInt] as BigInt
        }
        terms {
            Wrap . x:Proc |- "wrap" "(" x ")" : Proc ;
            S . x:Proc |- "s" "(" x ")" : Proc ;
            R0 . x:Proc |- "r0" "(" x ")" : Proc ;
        }
        equations {}
        rewrites {
            M0 . |- (R0 (S x)) ~> (Wrap x) ;
        }
    "#;

    const APPEND_FRAGMENT: &str = "MX0 . |- (R0 (S (S x))) ~> (Wrap x) ;";

    #[test]
    fn incremental_append_takes_the_incremental_path_and_matches_batch() {
        // On a fresh thread (fresh artifact cache): base derive → incremental
        // extend. The debug cross-check inside `extend_in_rho_artifacts` compares
        // the whole ruleset against the batch derivation; here we pin the
        // OBSERVABLE contract on top.
        std::thread::spawn(|| {
            let base = cached_in_rho_artifacts(BASE_SOURCE).expect("the base derives");
            let outcome =
                extend_in_rho_artifacts(&base, APPEND_FRAGMENT).expect("the append derives");
            let artifacts = match outcome {
                IncrementalExtendOutcome::Incremental(artifacts) => artifacts,
                IncrementalExtendOutcome::FellBack { reason, .. } => {
                    panic!("a base-shape append must take the incremental path, fell back: {reason}")
                },
            };
            // The extended def gained exactly the appended user rewrite, at the
            // batch position (after the existing user rewrites).
            let names: Vec<String> =
                artifacts.def.rewrites.iter().map(|r| r.name.to_string()).collect();
            assert_eq!(names, ["M0", "M1", "MX0"]);
            // The ruleset cell is SEEDED (the bypass) — no ruleset compile ran.
            assert!(artifacts.ruleset_forced(), "the incremental ruleset cell is seeded");
            assert!(!artifacts.lowered_forced(), "the lowering derives on demand");
            assert!(!artifacts.installed_par_forced(), "the emission derives on demand");
            let view = artifacts.ruleset().automaton.view();
            assert_eq!(view.entry_count(), 3, "two base entries + the append");
            assert_eq!(view.entry_id(2), dovetail::set_automaton::PatternId(2));
            // The FULL Par re-emission (the fingerprint constraint) still installs.
            assert!(
                artifacts.installed_par().is_ok(),
                "the extended σ-receiver program installs: {:?}",
                artifacts.installed_par().as_ref().err()
            );
            // The memo slot serves the extended source now (same Arc).
            let again = cached_in_rho_artifacts(&artifacts.definition_source)
                .expect("the extended source is memoized");
            assert!(Arc::ptr_eq(&artifacts, &again), "memoized under the extended source's hash");
        })
        .join()
        .expect("the fresh-thread probe completes");
    }

    #[test]
    fn incremental_fingerprint_and_install_match_the_batch_arm() {
        // The pure-function reduction made observable WITHOUT relying on the debug
        // cross-check: derive batch on one thread, incremental on another, compare
        // the Send-safe observables (fingerprint + installed-par debug bytes).
        let batch = std::thread::spawn(|| {
            let extended = splice_rewrite_into_source(BASE_SOURCE, APPEND_FRAGMENT)
                .expect("the base splices");
            let artifacts = cached_in_rho_artifacts(&extended).expect("the batch arm derives");
            (
                artifacts.ruleset().language_fingerprint.clone(),
                artifacts.ruleset().automaton.view().state_count(),
                format!("{:?}", artifacts.installed_par()),
            )
        })
        .join()
        .expect("the batch thread completes");
        let incremental = std::thread::spawn(|| {
            let base = cached_in_rho_artifacts(BASE_SOURCE).expect("the base derives");
            let outcome =
                extend_in_rho_artifacts(&base, APPEND_FRAGMENT).expect("the append derives");
            assert!(outcome.fallback_reason().is_none(), "the incremental path ran");
            let artifacts = outcome.artifacts();
            (
                artifacts.ruleset().language_fingerprint.clone(),
                artifacts.ruleset().automaton.view().state_count(),
                format!("{:?}", artifacts.installed_par()),
            )
        })
        .join()
        .expect("the incremental thread completes");
        assert_eq!(incremental, batch, "fingerprint + state count + installed par agree");
    }

    #[test]
    fn auto_injected_rewrites_reorder_correctly_and_are_never_entries() {
        // EM-2 anti-vacuity: the base has a NON-EMPTY auto-injected rewrite set;
        // the incremental path must reproduce the batch ordering
        // [user…, new, auto…] (the debug cross-check enforces fingerprint + full
        // ruleset equality on top of these observable pins).
        std::thread::spawn(|| {
            let base =
                cached_in_rho_artifacts(AUTO_INJECT_BASE_SOURCE).expect("the base derives");
            let base_autos = base.def.rewrites.iter().filter(|r| r.is_auto_injected).count();
            assert!(base_autos >= 1, "EM-2 anti-vacuity: the auto-injected set is NON-EMPTY");

            let outcome =
                extend_in_rho_artifacts(&base, APPEND_FRAGMENT).expect("the append derives");
            let artifacts = match outcome {
                IncrementalExtendOutcome::Incremental(artifacts) => artifacts,
                IncrementalExtendOutcome::FellBack { reason, .. } => {
                    panic!("the auto-inject base is inside the admitted family, fell back: {reason}")
                },
            };
            let names: Vec<(String, bool)> = artifacts
                .def
                .rewrites
                .iter()
                .map(|r| (r.name.to_string(), r.is_auto_injected))
                .collect();
            assert_eq!(
                names.first().map(|(name, auto)| (name.as_str(), *auto)),
                Some(("M0", false)),
                "user rewrites first"
            );
            assert_eq!(
                names.get(1).map(|(name, auto)| (name.as_str(), *auto)),
                Some(("MX0", false)),
                "the appended USER rewrite sits at the batch position (before the autos)"
            );
            assert!(
                names[2..].iter().all(|(_, auto)| *auto),
                "the auto-injected rewrites follow as the suffix: {names:?}"
            );
            assert_eq!(
                names[2..].len(),
                base_autos,
                "the re-run emits the same auto set (the append is not a congruence)"
            );
            // EM-2's assert: no auto-injected rewrite is an automaton entry.
            let view = artifacts.ruleset().automaton.view();
            for entry in 0..view.entry_count() {
                let id = view.entry_id(entry);
                assert!(
                    !artifacts.def.rewrites[id.0].is_auto_injected,
                    "entry {entry} maps to auto-injected rewrite {:?}",
                    artifacts.def.rewrites[id.0].name.to_string()
                );
            }
            assert!(artifacts.installed_par().is_ok());
        })
        .join()
        .expect("the fresh-thread probe completes");
    }

    #[test]
    fn non_base_append_fails_closed_to_the_batch_fallback() {
        // The coordinator-pinned fallback-correctness case: a CONGRUENCE append is
        // outside the admitted family — the typed refusal is recorded and the
        // fallback derives batch-identical artifacts.
        std::thread::spawn(|| {
            let base = cached_in_rho_artifacts(BASE_SOURCE).expect("the base derives");
            let outcome = extend_in_rho_artifacts(
                &base,
                "WrapCong . | S ~> T |- (Wrap S) ~> (Wrap T) ;",
            )
            .expect("the fallback derives");
            match &outcome {
                IncrementalExtendOutcome::FellBack { reason, artifacts } => {
                    assert_eq!(*reason, IncrementalUnsupported::PremisedRewrite);
                    let names: Vec<String> =
                        artifacts.def.rewrites.iter().map(|r| r.name.to_string()).collect();
                    assert_eq!(names, ["M0", "M1", "WrapCong"]);
                    // The congruence is NOT an automaton entry — it defers or joins
                    // contextually, exactly as batch decides (these ARE the batch
                    // artifacts; the equivalence-gate test in the E-3 harness
                    // additionally proves them ≡ an independent batch derivation).
                    assert_eq!(artifacts.ruleset().automaton.view().entry_count(), 2);
                },
                IncrementalExtendOutcome::Incremental(_) => {
                    panic!("a premised rewrite must not take the incremental path")
                },
            }
        })
        .join()
        .expect("the fresh-thread probe completes");
    }

    #[test]
    fn chained_appends_stay_batch_identical() {
        // The W-B ladder's validity is INDUCTIVE (each step extends the previous
        // step's artifacts): chain three appends and compare the FINAL artifacts
        // against the batch derivation of the final source. (Each intermediate
        // step is also cross-checked in debug builds.)
        let fragments = [
            "MX0 . |- (R0 (S (S x))) ~> (Wrap x) ;",
            "MX1 . |- (R1 (S (S x))) ~> (Wrap x) ;",
            "MX2 . |- (R0 (S (S (S x)))) ~> (Wrap x) ;",
        ];
        let incremental = std::thread::spawn(move || {
            let mut current = cached_in_rho_artifacts(BASE_SOURCE).expect("the base derives");
            for fragment in fragments {
                let outcome =
                    extend_in_rho_artifacts(&current, fragment).expect("each append derives");
                assert!(outcome.fallback_reason().is_none(), "each append is base-shape");
                current = Arc::clone(outcome.artifacts());
            }
            (
                current.definition_source.clone(),
                current.ruleset().language_fingerprint.clone(),
                current.ruleset().automaton.view().state_count(),
                format!("{:?}", current.installed_par()),
            )
        })
        .join()
        .expect("the incremental thread completes");
        let batch = std::thread::spawn(move || {
            let mut source = BASE_SOURCE.to_string();
            for fragment in fragments {
                source =
                    splice_rewrite_into_source(&source, fragment).expect("each splice lands");
            }
            let artifacts = cached_in_rho_artifacts(&source).expect("the batch arm derives");
            (
                source,
                artifacts.ruleset().language_fingerprint.clone(),
                artifacts.ruleset().automaton.view().state_count(),
                format!("{:?}", artifacts.installed_par()),
            )
        })
        .join()
        .expect("the batch thread completes");
        assert_eq!(incremental, batch, "the chained ladder ends batch-identical");
    }

    #[test]
    fn duplicate_name_and_multi_rule_fragments_fail_closed() {
        std::thread::spawn(|| {
            let base = cached_in_rho_artifacts(BASE_SOURCE).expect("the base derives");
            let duplicate = extend_in_rho_artifacts(&base, "M0 . |- (R0 x) ~> (Wrap x) ;")
                .expect("the fallback derives");
            assert_eq!(
                duplicate.fallback_reason(),
                Some(&IncrementalUnsupported::DuplicateRuleName { name: "M0".to_string() })
            );
            let multi = extend_in_rho_artifacts(
                &base,
                "A0 . |- (R0 x) ~> (Wrap x) ; A1 . |- (R1 x) ~> (Wrap x) ;",
            )
            .expect("the fallback derives");
            assert_eq!(
                multi.fallback_reason(),
                Some(&IncrementalUnsupported::NotASingleRewrite { parsed: 2 })
            );
        })
        .join()
        .expect("the fresh-thread probe completes");
    }
}
