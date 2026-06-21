# V3 Design — Ambient Binder + Freshness (SOUND, VALIDATED, disposition-first)

> Round-2 convergent diagnosis: `/tmp/b0/ambient-binder-redteam-round2-convergent.md`. v3 CORRECTS one
> load-bearing round-2 fact (see Part A) by reading the generated code.

## Gating finding (Part A): the Ascent reference is PRESENT but UNTRUSTWORTHY on capturing witnesses
Round-2 #5 ("run_ascent emits NO ScopeExtrusion/NewComm rule for Ambient") is FALSE.
`target/generated/ambient/ascent.rs` emits ALL SIX binder equations as `eq_proc` rules, each with the
moniker `free_vars` freshness guard:
- NewComm `:128-163`; ScopeExtrusion `:163-198` (guard `:168-170`); InNew/OutNew/OpenNew/AmbNew
  `:199-232 / 232-265 / 265-298 / 298-331` (guards e.g. `:203-205`).
They are compiled by `generate_equation_rules` (`macros/src/logic/rules.rs:1047-1162`), NOT the
rho-COMM-hardcoded `generate_structural_comm_rule` (`:2358-2452`). Round-2 conflated this with the
eqrel-congruence SKIP at `equations.rs:271-274`, which lives in `generate_congruence_rules` and only
suppresses AUTO-congruence under binders, not the explicit user equations.

BUT the generated rules re-home subterms with `Scope::from_parts_unsafe` (`runtime/src/binding.rs:325-332`,
NO close/open) + structural `.normalize()` (binder arm `AssembleBind_Proc_PNew`,
`target/generated/ambient/normalize.rs:789-801`, also `from_parts_unsafe`), so they DO NOT recompute
de-Bruijn coordinates. Worked witness `new^z. in(z, new^x. 0)`: InNew fires (`x # 0` true), result reuses
`Bound{0,0}` (z) unshifted under `new^x` ⇒ z is CAPTURED ⇒ run_ascent yields a WRONG normal form.
moniker math confirming: `Scope::new`→`close_term` with `state.incr()` (`scope.rs:25-37,136-138`,
`bound/mod.rs:43-52`); `unbind`→`open_term` freshens (`scope.rs:40-57`); `free_vars` collects only
`Var::Free` (`bound/mod.rs:120-132`).

⇒ Trustworthy reference = moniker `unbind`+`free_vars`+`Scope::new` (re-close). v3's NativeHandler IS that.
Validation tiers: (1) hand-written moniker reference (primary, gold for capturing witnesses, uses
generated `is_fresh` `target/generated/ambient/freshness.rs:1-17`); (2) Ambient-calculus literature
vectors; (3) differential-vs-run_ascent on the NON-capturing corpus only + a NEGATIVE pin asserting
run_ascent and the moniker reference DISAGREE on `new^z.in(z,new^x.0)` (documents the ref's limitation).

## B. Moniker NativeHandler for the six binder congruences
Plugs in as a generated `try_direct_eval` override for Ambient (BEFORE the unsupported list in
`target/generated/ambient/dovetail_report.rs:25-40`; seam `complete_native_dovetail_report_for_language`
`dovetail-runtime/src/lib.rs:132-210`). New generator `macros/src/gen/runtime/binder_congruence.rs`
→ `binder_congruence_normal_form`. Alt-preserving (maps over `Ambiguous` like `normalize_term`
`language_trait_impl.rs:109-124`). Returns `Some` iff observable progress, else `None` (fail-closed kept).
Core primitive `float_one`: `unbind` (freshen + open) → structural move on the OPEN term → `Scope::new`
(re-close, recomputes ALL coordinates). Per-equation: InNew/Out/Open/Amb float prefix under the inner new;
ScopeExtrusion floats the member new over the rest-bag (multiset freshness, FULL-union `is_fresh`, ⊇);
NewComm orders the floated new-prefix by structural `Scope` `Ord` (`binding.rs:230-252`, coordinate/name-
stable, NOT unique_id). Termination: floats reduce Σ(new depth) potential, O(n²); prefix sorted to unique
order ⇒ deterministic NF. Witness `new^z.in(z,new^x.0)`: outer `unbind` opens z to a FreeVar; float; re-
close recomputes z to `Bound{1,0}` past `new^x` ⇒ NO capture.

## C. Composition with in-engine AC (float↔AC fixpoint inside try_direct_eval)
```
loop: T1 = binder_congruence_normal_form(T)        // float new's out, AC-normalize bodies
      peel top new-prefix P*, inner soup S
      build e-graph for S; saturate(InRule/OutRule/OpenRule); extract roots → S'set  (ambiguity-preserving)
      re-wrap each S'∈S'set under P* via Scope::new (re-close, capture-safe)
      T2 = canonical binder-NF of {new P*.S'}; if term_eq(T2,T) break else T=T2
```
AC reduction can re-expose new's (OpenRule surfaces nested new; In/OutRule move ambients) ⇒ re-float.
Bounded by max_iters/max_nodes (`EGraphConfig`) + new max_float_rounds ⇒ `BoundedByCycleCut` if not
converged (NOT `Complete` — honest; thread real `ExtractionCompleteness` through the seam, replacing the
hardcoded `Complete` at `lib.rs:204`). Mandates: ambiguity preserved (alt-map + AcApp every-selection +
dedup by exact_key only, never weight-prune); lazy (`LazyAcSelect` `rules.rs:73-`, no eager AC space);
WPDA/rigail (existing `Extractor`+`TropicalWeight` `dovetail_report.rs:630-631`).

## D. CUT the db::/fv:: alpha-as-ContentKey lowering
In v3 binders are NEVER rewritten in-engine (only AC soup rules InRule/OutRule/OpenRule, which match
PPar/PAmb/PIn/POpen/POut structurally and never select a bound-var leaf). Alpha-equivalence of new-terms
is decided in the NATIVE stage by moniker `term_eq` (`binding.rs:346-348`, ignores pretty_name). The
existing `binder_arm` (`dovetail_report.rs:198-249`) stays as-is and is INERT (no rewrite extracts a bound
leaf; `instantiate` rebuilds whole op-nodes). Strictly LESS proof than v2; removes the `new(x,z)≢new(x,w)`
blanket-erasure hazard. No other language depends on the cut change (never shipped).

## E. Disposition-gating (rhocalc stays host-routed; NO generic premise flip)
Keep `premise_supported Freshness => false` (`dovetail_report.rs:404`) AND Rocq `GPremFreshness => false`
(`GeneratedReportCompiler.v:90`) UNCHANGED. Native handler gated at codegen by
`has_binder_equations && has_no_host_disposition`: Ambient (no host) ⇒ emitted; rhocalc (Extrude
dispositioned `RhoNativeJoin`, `backend.rs:23-46`, `guard_quality.rs:131`) ⇒ NOT emitted, stays host-
routed, fails closed on an Extrude redex. NEW regression `rhocalc_dovetail_report_stays_host_routed_for_
extrude` (does not exist today — `dovetail_codegen_report.rs` covers only BaseMath + Lambda).

## F. Zero-admission Rocq — new `AmbientBinderHandler.v` (imports Stdlib + MeTTaILRewriteCoverage only)
Model `eterm := EVarF nat | EVarB nat nat | EPrefix nat eterm | EBind eterm | EPar (list eterm)` with
`open`/`close`/`free_vars` mirroring moniker. Theorems: (1) `float_preserves_denotation` (capture-safety,
close∘open round-trip) + `from_parts_unsafe_captures` (PROVES run_ascent unsound on the witness);
(2) `fresh`=free_vars-absence, `free_vars_no_bound_leak`, `fresh_bag_complement` (⊇/multiset; NO
filter_adjust); (3) `bound_leaf_inert_outside_binder` + `no_rewrite_selects_bound_leaf` (the CUT's
inertness); (4) coverage reuse `apply every_requirement_constructor_is_covered` (no new constructors);
(5) disposition routing `rhocalc_stays_host_routed`/`ambient_native_handler_emitted` + keeps
`GPremFreshness=false` so the existing `supported_premises_are_only_congruence` proof is untouched.
Honest `report_complete_iff_both_converge` + `binder_nf_idempotent` (true-fixpoint).

## G. Staged increments
0. Empirical pin + negative oracle (run_ascent captures, moniker ref does not) — Rocq Thm 1; valuable today.
1. NativeHandler InNew/Out/Open/Amb + NewComm float (no AC) — Rocq Thm 1,2,4; capture witnesses don't capture.
2. Compose float↔AC fixpoint + honest completeness — Rocq Thm 3 + idempotent/complete; re-float converges;
   non-terminating term ⇒ BoundedByCycleCut; ambiguity ≥2 roots across seam.
3. Disposition gate + rhocalc pin + flip `ambient_dovetail_flip.rs` expect_err→expect — Rocq Thm 5.
4. Differential oracle on NON-capturing corpus + clear var-cache once.

## H. Biggest threat: float↔AC fixpoint non-confluent/non-deterministic ⇒ ill-defined NF ⇒ exact_key
determinism (lib.rs:179-181 dedup, WPDA seed) breaks. Mitigation: stable structural `Scope` `Ord` (not
unique_id) ⇒ run-stable order (pin: twice ⇒ byte-identical root keys); full-float-before-AC + full-AC-
before-float (no sub-step interleave); e-graph confluent-by-congruence + deterministic extraction under
uniform weight; honest BoundedByCycleCut on divergence; Rocq `binder_nf_idempotent`. Secondary: ScopeExtrusion
multiset full-union is_fresh (reverse-blocks test); freshened unique_id never leaks into exact_key (re-close
erases it); oracle var-cache cleared once.
