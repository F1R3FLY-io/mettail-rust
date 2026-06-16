# Ambient binder lowering — Round-3 red-team findings (v3 Part A VERIFIED; composition REFUTED, fixable)

## Part A: VERIFIED AIRTIGHT (independent critic, traced end-to-end)
- `run_ascent` DOES emit all six binder equations (`target/generated/ambient/ascent.rs:128-331`) via
  `generate_equation_rules` (`macros/src/logic/rules.rs:1047-1162`); the `equations.rs:271-274` skip is in
  the AUTO-congruence path only. Earlier "emits none" was WRONG.
- The generated rules ARE capture-unsound: `from_parts_unsafe` + structural `normalize()` (9
  `from_parts_unsafe`, 0 `Scope::new` in `normalize.rs`), NO coordinate re-close. Witness
  `new^z.in(z,new^x.0)`: InNew fires (`x # 0` true), reuses `Bound{0,0}` for z under `new^x` ⇒ z CAPTURED
  (should be `Bound{1,0}`). `run_ascent` yields a WRONG NF here.
- moniker `unbind`(freshen+open)→move→`Scope::new`(re-close, `close_term` increments depth through nested
  scopes, `bound/mod.rs:32-35,43-52`) does NOT capture (z→`Bound{1,0}`). So the moniker handler is the
  trustworthy reference; the differential-vs-run_ascent oracle is valid ONLY on the non-capturing corpus +
  a negative pin documenting the disagreement. ⇒ v3's disposition-first architecture is SOUND.

## Composition REFUTED (5 holes, all with concrete fixes). Root cause of #3/#4a/#5-idempotence = ONE defect.

### #3 (GATING) — `unique_id` leaks into identity ⇒ run-varying NF
moniker `UniqueId` = process-global `NEXT_ID.fetch_add` counter (`unique_id.rs:12-17`), freshened by every
`FreeVar::fresh` (so every `unbind`, `scope.rs:50-52`), NOT reset by `clear_var_cache` (parse cache only,
`binding.rs:45-47`). It leaks into:
- (a) `Scope::cmp`/Ord — `binding.rs:244-250` hashes `unsafe_pattern` (Binder→FreeVar, derived Hash =
  unique_id only; the file's own comment at :238 says so). The NewComm float-prefix sort uses this.
- (c) `exact_key` — `semantic_hash` PNew arm `Hash::hash(&unsafe_pattern)` (`target/generated/ambient/
  semantic_hash.rs:51-58`) → `FramedSemanticKeyHasher` records the unique_id bytes
  (`semantic_key.rs:45-47`) → `extraction_semantic_fingerprint` (`term_wrapper.rs:242-247`).
- (d) e-graph `content_key` — binder leaf label `format!("{:?}", scope.unsafe_pattern())`
  (`dovetail_report.rs:111-128`); Binder Debug prints unique_id.
⇒ binder `exact_key`/`content_key` are run-varying; dedup (`lib.rs:179-181`) over/under-counts; WPDA seed
identity unstable. **FIX (gating):** make binder identity ALPHA-CANONICAL — hash/compare the de-Bruijn
BODY (already alpha-canonical: bound=BoundVar de-Bruijn, free=stable ids) + binder ARITY, and EXCLUDE the
binder's FreeVar identity, across (c) `semantic_hash` PNew arm [generated/macro], (d) e-graph binder label
[generated/macro], (a) `Scope::cmp`/Ord + `OrdVar::cmp` [runtime binding.rs]. This ALIGNS identity with
moniker `term_eq` (which already ignores binder names) — a genuine correctness fix, partly pre-existing.
Only Ambient exercises binder hashing today (Calculator has no binders; rhocalc routes binders to host) ⇒
no regression risk to flipped langs.

### #1 — InNew/OutNew/OpenNew/AmbNew under-guarded (`x # P` only, missing `x # N`)
These move the prefix name `N` under `new^x`; if `x ∈ fn(N)` (e.g. `new(x, x[P])` for AmbNew), the float
captures the name's x. The mettail equations (`ambient.rs:32-35`) state `x # P` only — under-guarded vs the
standard Ambient side condition `x ∉ fn(N)`. **FIX:** the native handler additionally checks `x # N`
(binder fresh in the name) before floating; refuses/alpha-renames otherwise. More correct than the
equation/reference; the divergence is documented (capturing terms go in the run_ascent-disagrees bucket).

### #2 — float↔AC oscillation / false Complete
`InRule` re-nests ambients (`ambient.rs:39-40`), increasing nesting depth and working against the float
potential; no joint termination measure. Inner AC `saturate` `SaturationOutcome::{IterationLimit,NodeLimit}`
(`rules.rs:163-169`) can be masked if the outer `term_eq(T2,T)` coincidentally holds ⇒ false `Complete`.
**FIX:** (1) provide a joint lexicographic rank (ambient-nesting, Σnew-depth) the moniker NF + AC provably
don't increase, OR (2) accept `BoundedByCycleCut` honestly AND propagate the inner `SaturationOutcome` so a
truncated AC sub-run can NEVER be reported `Complete`. Honesty about the bound is the central principle.

### #4 — ambiguity across the seam
Single-`P*` re-wrap can lose prefix-distinct alternatives (two extrusion orders → distinct prefixed NFs).
Dedup-by-`exact_key` over-counts under #3 (spurious duplicate roots) / can't dedup genuinely-equal alts.
NOT a weight-prune (all weights "0", `lib.rs:190`). **FIX:** after #3 makes exact_key canonical, dedup
works; fan `S'set` back into the full set of valid prefixes as additional `Ambiguous` roots.

### #5 — honest Complete threading is a contract change
Native seam (`complete_native_dovetail_report_for_language`, `lib.rs:132-210`) returns EARLY before the
(dead) e-graph branch, builds the report from `rewrite_seeds`, hardcodes `RuntimeDovetailCompleteness::
Complete` (`lib.rs:204`), never constructs `ExtractionCompleteness` (`extract.rs:77-82`, different crate,
only produced by the dead e-graph path). `RewriteSeed` (`language.rs:648-662`) carries only
`{term_id,exact_key,display}` — NO completeness field. **FIX:** add a completeness channel —
`Language::try_direct_eval`/the native handler returns an `ExtractionCompleteness`/`RuntimeDovetailComplete
ness`, threaded to `lib.rs:204` instead of the hardcoded `Complete`. Contract change, mechanical.
`binder_nf_idempotent` (Rocq) holds in the unique_id-erased model; fix #3 makes it hold in the artifact too.

## Convergence status
Architecture CONVERGED + Part A VERIFIED. v4 = v3 + the five fixes above, with the BOUNDED-HONEST
composition as the central principle (never claim `Complete` on a truncated/bounded run). The fixes are
concrete and mechanical; the only judgment call is #1's `x # N` (resolved: add it — capture is unsound).
