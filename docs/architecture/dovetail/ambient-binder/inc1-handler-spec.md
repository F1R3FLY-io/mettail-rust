# Inc 1 — Moniker NativeHandler Float for Ambient (implementable spec)

Converged design: `README.md` + `design-v4-converged.md`. Inc 0 (FIX-A) committed `4ba72e09`.
This spec is implemented foreground. NO AC composition (Inc 2). The pure binder-congruence NF is total,
so the seam's `Complete` is honest for Inc 1.

## Decision: hand-written Ambient instance, GENERATED into `target/generated/ambient/binder_congruence.rs`
via new macro generator `macros/src/gen/runtime/binder_congruence.rs`, gated by
`has_binder_equations && has_no_host_disposition`. Rationale: uniform-float ≠ NewComm (NewComm is a REORDER
of an adjacent new-run, not an outward float, so a single uniform rule is incomplete); validate the mechanism
on Ambient first (M*.0); keep the artifact in the generated tree (rebuilt with the AST, stays in sync with
constructor renames) while being a concrete per-constructor instance.

## Algorithm (capture-safe) — `binder_congruence_nf(p:&Proc)->Proc`, bottom-up to fixpoint
Skeleton for EVERY case: read the binder identity from `s.unsafe_pattern()` (PRE-freshen) for the freshness
GATE; `unbind` only to get the OPENED body for reassembly; reassemble around the opened body; re-close via
`Scope::new` (recomputes de-Bruijn coords locally; NEVER `from_parts_unsafe`).
- **NewComm (adjacent new-run reorder):** collect the maximal `PNew^{a1}…PNew^{ak}.core` run by repeated
  `unbind` (distinct fresh FreeVars, fully-opened core); order the `ai` by the FIX-A ALPHA-CANONICAL key
  (the per-binder occurrence-path-multiset in `core` — unique_id-free; NOT `Scope` Ord, which still leaks
  unique_id post-FIX-A); re-close innermost-first in canonical order.
- **ScopeExtrusion (float new out of a PPar bag):** partition bag into news + rest; for each `new` member,
  gate on `is_fresh(s.unsafe_pattern(), PPar(residual))` where residual = rest ∪ (other news); if fresh,
  result = `PNew^{x'}.( PPar({opened_body} ∪ residual) )`; re-enter float on the new inner PPar. Full-union
  multiset scan, no representative shortcut. Preserve HashBag multiplicities.
- **Prefix float (InNew/OutNew/OpenNew/AmbNew):** at `Prefix(N, PNew^x.P)`, **FIX-B gate
  `is_fresh(s.unsafe_pattern(), N)`** (the binder fresh in the NAME — the standard `x ∉ fn(N)` the equations
  omit); if fresh, result = `PNew^{x'}.( Prefix(N, opened_body) )`.
Termination: Φ = Σ over news of the non-`new` constructor nodes between the new and the root; each float
strictly decreases Φ ≥ 0; NewComm decreases the run-key and is fixpoint at the canonical rep. O(n²).

## CRITICAL correctness detail (biggest risk): freshened-vs-original binder
`is_fresh(Binder(x'), N)` with x' from `unbind` ALWAYS returns true (x' is brand-new, can't be in N) ⇒
silently DISABLES the guard ⇒ re-introduces capture (run_ascent's exact bug). MUST gate on
`is_fresh(s.unsafe_pattern(), N/residual)` (ORIGINAL binder). Test 4 (FIX-B blocked: `open(x, new(x, 0))`
same source name → NO float) is the required catch; Rocq T1' makes it machine-checked.

## Wiring
- `macros/src/gen/runtime/language.rs:3651-3664`: replace the non-native `else { quote!{} }` with a
  disposition-gated `try_direct_eval` override calling `#primary_type::binder_congruence_nf_term(&typed.0)`
  → `Some(Box::new(Term(progressed)))` or `None` (fail-closed preserved).
- Gate helpers (macro): `has_binder_equations(def)` = any equation pattern carries a Lambda/binder
  constructor; `has_no_host_disposition(def)` = no `RhoNativeJoin` obligation (Ambient: none; rhocalc Extrude:
  yes ⇒ NOT emitted). Use/expose `rholang-codegen::backend` (`collect_guard_obligations` /
  `rho_native_join_present`). Keep `premise_supported(Freshness)=>false` UNCHANGED.
- Alt-preserving wrapper `binder_congruence_nf_term(inner)`: map over `Ambiguous(alts)` (mirror
  `normalize_term`), `Proc(p)` → float, `Name` → None; `Some` iff observable progress (`!term_eq`).
- Seam: `complete_native_dovetail_report_for_language` (`dovetail-runtime/src/lib.rs:139-210`) calls
  `try_direct_eval` first → `Some(nf)` → `rewrite_seeds()` (FIX-A exact keys) → report `Complete` (honest for
  Inc 1). The flip test `ambient_dovetail_flip.rs` (`{open(n,0)|n[0]}`, no `new`) KEEPS PASSING (handler
  returns None) — flipped only in Inc 3.

## Rocq — `dovetail/formal/rocq/theories/Lowering/AmbientBinderHandler.v` (Stdlib + MeTTaILRewriteCoverage; 0 admits)
Model `eterm := EVarF nat | EVarB nat nat | EPrefix nat eterm | EBind eterm | EPar (list eterm)` with
moniker-faithful `open`/`close` (close incr scope-offset under EBind, mirroring `scope.rs:138`) + `free_vars`.
- T1 `float_prefix_preserves` (uses `open_close_id` + `x ∉ fn(N)`) + `from_parts_unsafe_captures` (no-reclose
  float on the z-witness diverges — formal twin of run_ascent capture).
- T1' `ambnew_requires_fresh_name`: float denotation-preserving IFF `x ∉ fn(N)`; exhibit capture when `x∈fn(N)`.
- T2 `fresh_iff_not_in_free_vars`, `free_vars_no_bound_leak`, `fresh_bag_complement` (flat_map; no filter_adjust).
- T4 `apply every_requirement_constructor_is_covered` (no new constructor). `Print Assumptions` all closed.

## Tests — `languages/tests/ambient_binder_handler.rs` (cfg ambient+dovetail-codegen)
1. Witness 1 `new(z,in(z,new(x,0)))` no-capture (semantic-key == gold-moniker-ref).
2. Witness 2 `new(w,{new(x,0)|w[0]})` no-capture.
3. `new(x,x)≡new(y,y)` equal key; `new(x,z)≢new(x,w)` distinct.
4. FIX-B BLOCKED: `open(x,new(x,0))` (same source name) → try_direct_eval None (no float); contrast
   `open(a,new(x,0))` → floats. + ScopeExtrusion blocked symmetric case.
5. Gold-moniker-reference equality over ~8-term corpus (each equation; hand-written `moniker_ref_float`).
6. rhocalc handler NOT emitted (try_direct_eval None for a rhocalc new/extrude term); determinism (twice ⇒
   identical exact_key).

## Critical files
- macros/src/gen/runtime/binder_congruence.rs (NEW generator) + language.rs:3651 (try_direct_eval gate)
- rholang-codegen/src/backend.rs (expose rho_native_join_present / collect_guard_obligations pub)
- dovetail/formal/rocq/theories/Lowering/AmbientBinderHandler.v (NEW) ; languages/tests/ambient_binder_handler.rs (NEW)
- READ: runtime/src/binding.rs (Scope::new/unbind/unsafe_pattern), target/generated/ambient/{freshness.rs,ast_enums.rs}, dovetail-runtime/src/lib.rs:139-210
