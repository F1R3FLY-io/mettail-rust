# Ambient binder lowering — Round-2 red-team CONVERGED (v2 REFUTED). Corrected diagnosis + v3 constraints.

Two independent adversarial critics + the design's own §5 converged. v2 (in-engine de-Bruijn binder
lowering) is REFUTED. Below is the convergent diagnosis, a finding STRONGER than the critics reached,
and the binding constraints for v3.

## Convergent refutation of v2 (both critics, code-grounded)

1. **Capture via depth/coordinate change (the kill shot).** Critic-1 witness `new^w.{new^x.P, w[0]}`:
   ScopeExtrusion re-homes `w[0]` (a `db::0.0` leaf, hashconsed) under `new^x`, where `db::0.0` now
   denotes `x` → bound-variable capture; the resulting ContentKey ALIASES an unrelated term. The
   freshness guard `x # rest` PASSES (x is genuinely fresh for rest) ⇒ it provides ZERO protection.
   Root cause: the engine shares `db::s.b` leaves by coordinate across unrelated binder contexts at
   different depths; the corrective index-SHIFT has no finite confluent definition over an e-class DAG
   and needs an analysis framework that does not exist (`dovetail/src/egraph.rs` has none —
   `analysis|make_analysis|merge|modify` = 0 hits).
2. **The guard is broken as written.** The binder var `x` is anonymized (v2 §1.2), so it is never a
   `Pattern::Var` and never enters `Subst` ⇒ `subst[&g.var]` panics/vacuous. v2 §1.2 (anonymize binder)
   and §1.4 (guard keyed by `subst[binder-name]`) are mutually inconsistent.
3. **Over-generation onto rholang.** `rholang.rs:862 Extrude` is the SAME multi-binder scope-extrusion
   with freshness, dispositioned to HOST RSpace (`RhoNativeJoin`; `ambient_dovetail_flip.rs:13-16`,
   `guard_quality.rs:131`). The GENERIC `premise_supported(Freshness)=>true` + Lambda/MultiLambda flip
   is NOT language-conditioned `⇒` wrongly lowers rholang's Extrude in-engine. Silent (no test calls
   `RholangLanguage::dovetail_report_for`). Breaches the disposition-first invariant (P3/P5a).
4. **`free_fv_leaves` ≠ moniker `free_vars`.** It folds the UNION over e-class alternatives (nothing is
   pruned), a superset of any single term's free vars. Safe only as `⊇` with a FULL-union walk; the
   laziness mandate's canonical-representative shortcut would HIDE an `fv::x` alternative and ADMIT
   capture. v2's "= moniker free_vars" claim is false.
5. **The differential oracle is blind to binder equations.** `run_ascent` emits NO ScopeExtrusion/NewComm
   rule for Ambient (the `unbind`+`multi_substitute` generator is rho-COMM-HARDCODED, `rules.rs:2391-2403`;
   the eqrel SKIPS binders+collections, `equations.rs:271-283`). So there is no reference normal form to
   diff against; the Rocq model also omits the AcApp re-homing `⇒` the formal check is blind too.
6. **`RewriteRule{guards}` breaks ~30 struct literals** across `dovetail/src` + `dovetail/tests`
   (no smart constructor; `rules.rs:148-153`).

## STRONGER finding (beyond the critics): ALL SIX binder equations are depth/coordinate-changing

The Ambient equations (`languages/src/ambient.rs:30-35`):
- **NewComm** `(PNew ^x.(PNew ^y.P)) = (PNew ^y.(PNew ^x.P))` — swaps two binders ⇒ P's `db::0.b ↔ db::1.b`
  must swap. Coordinate-changing.
- **ScopeExtrusion** `{(PNew ^x.P), ...rest} = (PNew ^x.{P, ...rest})` — `rest` moves under `new^x` ⇒
  rest's free `db::` to outer binders shift +1. Depth-changing.
- **InNew/OutNew/OpenNew/AmbNew** `(Prefix N (PNew ^x.P)) = (PNew ^x.(Prefix N P))` — **N moves UNDER
  `new^x`** on the RHS. Critic-1's "N stays outside the binder on both sides" is WRONG. Witness
  `new^z. in(z, new^x.0)`: `N=z` is bound (`db::0.0`→`new^z`), `x # P`=`x # 0` holds ⇒ InNew fires ⇒
  `z` re-homed under `new^x` where `db::0.0` now denotes `x` ⇒ z CAPTURED. The freshness premise is
  `x # P` only — it does NOT guard `N` — so it cannot prevent this. Depth-changing.

⇒ **No binder equation can be realized as a sound in-engine rewrite over shared hashconsed `db::` leaves.**
This is not "4 safe, 2 unsafe"; it is the whole family. The reference (moniker) is correct precisely
because `unbind`/`Scope::new` recompute coordinates LOCALLY (never sharing leaves across binder contexts).

## The principled resolution = the campaign's OWN disposition-first decision rule

"Dovetail lowers a family in-engine IFF its matching is ambiguous AND no host layer preserves it;
otherwise it is dispositioned." The binder equations are DETERMINISTIC congruences (the extruded/commuted
form is unique up to alpha) `⇒` NOT ambiguous `⇒` they were NEVER supposed to go in-engine. They are a
**NativeHandler disposition**: a moniker-based native computation (`unbind`/`free_vars`/`Scope::new`),
capture-safe by construction, with LOCAL coordinate recomputation. Only the genuinely-ambiguous AC
reduction (InRule/OutRule/OpenRule — which rearrange the soup, not binders) stays in-engine (P4, DONE).

## v3 binding constraints
1. **NO binder equation is an in-engine rewrite.** All six go to a moniker-based NativeHandler (or are
   honestly dispositioned). The e-graph's role for binders is REPRESENTATION ONLY (lowering for
   interning/dedup/extraction) — and even that must be proven capture-safe-because-inert (no rewrite
   extracts a `db::` leaf).
2. **Resolve the reference-oracle question EMPIRICALLY.** Determine what `run_ascent` actually computes
   for an Ambient term WRT the binder equations (does it apply ScopeExtrusion/NewComm/*New at all?).
   Read the generated `ascent.rs` for Ambient + the equation→eqrel/rewrite compilation; note how to probe.
   That answer decides what "reference-correct" means and how the binder equations get VALIDATED if
   `run_ascent` doesn't exercise them (e.g. a hand-written moniker reference, Ambient-calculus literature
   test vectors, or the zero-admission Rocq model).
3. **Design the composition** of the moniker-native binder congruences with the in-engine AC reduction,
   preserving the three mandates (ambiguity end-to-end; laziness/no eager exponential; WPDA/`rigail`
   integration) AND reference-correctness. Candidate: float `new`s outward via the native handler
   (capture-safe), AC-saturate the soup in-engine (ambiguity-preserving), re-wrap; handle reduction that
   re-exposes `new`s. Specify the iteration/termination + how ambiguity crosses the native/in-engine seam.
4. **Disposition-gate, never generic-flip.** Keep `premise_supported(Freshness)=>false` generically;
   route freshness/binder handling through the disposition layer so rholang's Extrude STAYS host-routed.
   Add a regression pinning `RholangLanguage::dovetail_report_for(Extrude redex)` fail-closed.
5. **Keep the sound, useful pieces of v1/v2 IF they survive:** the `db::`/`fv::` alpha-as-ContentKey
   lowering (§1.1/§1.2) gives alpha-dedup of REPRESENTED terms for free and critic-2 found it compiles
   with no regression (already-flipped langs route through `complete_native_dovetail_report_for_language`
   first, never reaching the arm). Keep it ONLY if it is needed AND proven inert (constraint 1). If kept,
   `free_fv_leaves` (if used at all) folds the FULL union and is proven `⊇`, never `=`.
6. **Zero-admission Rocq** for whatever is implemented; NO false reuse of `RholangAstLowering.v`. Honest
   `Complete`: the report is `Complete` only when the binder-congruence native step + AC saturation both
   converge; otherwise surface a typed blocker. No silent dishonesty.
7. **Honest completion.** If full binder-congruence support is genuinely beyond a sound, validated single
   increment, say so explicitly and stage it — but do NOT ship an unsound in-engine rewrite or a
   `Complete` that lies. Per the user's no-deferral mandate, prefer implementing the moniker NativeHandler
   properly over fail-closing, unless the validation gap (constraint 2) makes correctness unprovable.

## Confirmed code facts
- `languages/src/ambient.rs:30-35` — the six equations (all depth/coordinate-changing) + `:37-53` the AC
  rewrite rules (InRule/OutRule/OpenRule — in-engine, done) + congruence rules ParCong/NewCong/AmbCong.
- `macros/src/logic/rules.rs:2391-2403` — binder-equation reference generator, rho-COMM-HARDCODED
  (POutput/NQuote/PPar bag) `⇒` does NOT emit Ambient ScopeExtrusion/NewComm.
- `macros/src/logic/rules.rs:959-990` — `generate_freshness_clause` (moniker `free_vars`, the real ref).
- `macros/src/logic/equations.rs:271-283` — eqrel skips binders + collections.
- `dovetail/src/egraph.rs` — no analysis framework; `add`/`rebuild`/`canonical_class_key` binder-blind.
- `dovetail/src/rules.rs:148-153` — `RewriteRule` (3 fields, struct-literal-constructed ~30×).
- `dovetail-runtime/src/lib.rs` — `complete_native_dovetail_report_for_language` (the native
  handler seam; `try_direct_eval` None for Ambient; `normalize_term` structural-only, no equations).
- `languages/src/rholang.rs:862` — `Extrude` (the over-generation target; must stay host-routed).
