# E-1 leg W-D — Ambient scion prediction (re-derived per SM-1 under the DEMAND-DRIVEN M1)

> WRITTEN DOWN **before** any W-D measurement (task step 1; SM-1 locked re-derivation
> procedure; Fold 2 = re-derive the W-D prediction to Δ=0 under M1 BEFORE running).
> HEAD = `1d8b8bee` (feature/rho-native-set-automata); L1 = `08aab5b7`, L2 = `1d8b8bee`.
> Binding design: `e1_demand_driven_design_v2.md` §5 (re-measure) + §7 (Ambient residual);
> `a_s5_design/e1_scion_design_v1.md` §W-D; `a_s5_design/e1_delta_amendments.md` SM-1.

## 0. The subject rules (LANDED A-S5.5 arm/bag COMM shapes — C-G-aligned, `languages/src/ambient.rs`)

The three Ambient structural rewrites, verbatim (Cardelli–Gordon Mobile Ambients; USER MA mandate):

| rule | LHS root | RHS (skeleton) | landed lowering |
|---|---|---|---|
| `InRule`  | `PPar{…}` (bag) | `PPar {(PAmb M (PPar {(PAmb N (PPar {P, ...rest1})), R})), ...rest2}` | **NestedStructuralAcRewrite** |
| `OutRule` (post-AM-1) | `PAmb M{…}` | `PPar {(PAmb N (PPar {P, ...rest1})), (PAmb M (PPar {...rest2}))}` | **NestedStructuralAcRewrite** |
| `OpenRule` | `PPar{…}` (bag) | `PPar {P, Q, ...rest}` | **StructuralAcRewrite** |

`rho_net_inout_firing.rs:66-69` pins In+Out as the two *nested structural-AC* injection sites;
`OpenRule` is the flat structural-AC site (`amb-demo-runtime`). **All three are AC-family arms.**

## 1. SM-1 re-derivation UNDER M1 (the mechanism, from the LANDED L1 codegen)

SM-1 (eager design) locked `Δ(DriveTau)/firing = s − #non-Nil-rest-slot-drives (−1 chained)`,
giving canonical **In Δ=3**. That formula required **per-position recheck-not-redrive** (graft the
inert siblings of each Recheck position, recheck only the head). The LANDED demand-driven M1 does
**NOT** implement per-position recheck-not-redrive; it implements *maximal-recheck-subtree =
one drive-point* (v2 §1.2). Re-deriving under M1 from the landed arm shapes:

### 1a. The primary route — AC arms never scion (unconditional)
`fuel_gated_firing` (positional arms, `rho_net_drive.rs:2554`) is the ONLY site that may emit a
`ScionBundle`; it is reached **only** for `DriveArm::Positional` (`BaseRewrite`) arms. AC-family
arms route through `ac_fuel_gated_firing` (`:2597`), whose firing emission is
**hard-wired `FiringEmission::ContractumRedrive`** (`:2621`) — there is no scion branch. In/Out/Open
are all AC arms ⇒ **every Ambient firing re-drives the whole contractum under BOTH policies**
(`AllRedrive` and `StructuralScion`) ⇒ the treatment arm for those firings is byte-identical to
control.

### 1b. The secondary route — even a positional bag RHS fails closed
Were any Ambient rule positional, `scion_bundle_for_rule` (`:2453`) calls `scion_collect_slots`
(`:2464`) FIRST, which returns `Err("scion: non-positional RHS shape (binder / substitution /
**collection**) …")` for any `PPar{…}` HashBag / rest-slot (`...rest`) RHS (`:2223`). `Err ⇒
FiringEmission::ContractumRedrive` (`:2557`, fail-closed, SM-8). Every Ambient RHS is a `PPar`
collection with rest-slots, so this route ALSO yields ContractumRedrive.

### 1c. Why the task's "In 5/5 Recheck → redrive-whole → Δ=0" gives the SAME value
Even in the *idealized* M1 (scion applies to a positional In): In's mark table is 5/5 Recheck
(SM-1) — the outer `PPar` **root** is a Recheck position, so the *maximal recheck subtree at the
root IS THE WHOLE RHS* ⇒ M1 emits ONE drive-point covering the entire contractum ⇒ resubmit-whole
= redrive-whole ⇒ **ΔDriveTau = 0**. The landed L1 reaches this same Δ=0 by the STRONGER fail-closed
route (§1a/1b: the scion is never even emitted for AC / collection rules), so the treatment
installed program is BYTE-IDENTICAL to control — not merely equal-DriveTau.

## 2. FROZEN W-D predictions (never silently adjusted — a deviation is REPORTED)

| quantity | prediction | mechanism |
|---|---|---|
| `treatment_installed` vs `control_installed` | **BYTE-IDENTICAL** | no Ambient arm scions (§1a/1b) |
| `ΔDriveTau/firing` — **In** | **0** | AC arm redrives whole (task's "5/5 Recheck redrive-whole" value) |
| `ΔDriveTau/firing` — **Out** (post-AM-1) | **0** | AC arm redrives whole |
| `ΔDriveTau/firing` — **Open** | **0** | AC arm redrives whole |
| `Δ(accept / sa)` = `Δfiring_visible` | **0** | *refines design §5's "=1"*: no `ScionBundle` emitted ⇒ NO accept bypass |
| `Δ(transport bytes)` = `Δ encoded_len` | **0** | identical installed program |
| every other counter Δ (matching/subst/respread/ac_carrier/other/total) | **0** | byte-identical program |

`Δ(accept/sa)=0` is the honest re-derivation: design §5 predicted `Δ(accept/sa)=1` *assuming the
scion applies to In*; the landed L1 fails the Ambient arms closed, so the accept is NOT bypassed on
either arm. This is a re-pin of the design prediction against the LANDED arm shapes (SM-1's locked
procedure), not a silent adjustment.

### Δ ≥ 0 invariant + the honest-result clause
Δ=0 satisfies the v2 EFFICIENCY invariant `ΔDriveTau ≥ 0 unconditionally`. It is **NOT a failure**:
it is the honest M1 Ambient result (v2 §7). The `recheck-not-redrive Δ>0` (eager SM-1's In Δ=3) is
the **documented depth-d follow-on** (v2 §7: a bounded-depth `^drive-to-depth` receiver), explicitly
**NOT this leg** (Fold-4-adjacent: the depth-d Δ>0 refinement is a DOCUMENTED FOLLOW-ON).

## 3. Correctness gates (Ambient is NON-confluent ⇒ MEMBERSHIP, not strict A/B inequality)

* **valid-NF-set MEMBERSHIP** (SM-7 / R-4 / decision-3 / AM-5): the resting OUT value must be a
  member of the valid-NF-set. The three AM-3 subjects each contain **exactly one** redex pair
  (a single `OpenRule`), so the valid-NF-set is a **singleton** ⇒ membership degenerates to equality
  with the expected flat NF (computed below). Because treatment == control byte-identically, the two
  arms additionally produce IDENTICAL OUT (same program, same schedule).
* **fired-multiset / ledger consistency**: each AM-3 subject fires exactly `{OpenRule}` on BOTH arms.
* **err / fuel channels EMPTY** on both arms (fuel 1024 ≫ subject depth ≤ 5, SM-5).

## 4. The three AM-3 flattening subjects (acceptance gates, `rho_net_ambient_full.rs:749-841`)

| # | subject | expected flat NF | fired |
|---|---|---|---|
| g1 bag-bodied | `{open(n,{a[{0}]|b[{0}]}), n[{c[{0}]}]}` | `{a[{0}], b[{0}], c[{0}]}` | `[OpenRule]` |
| g2 empty-bag | `{open(n,{}), n[{c[{0}]}]}` | `{c[{0}]}` | `[OpenRule]` |
| g3 double-nested | `{open(n,{a[{0}]|{b[{0}]|{c[{0}]|d[{0}]}}}), n[{r[{0}]}]}` | `{a,b,c,d,r}[{0}]` (flat) | `[OpenRule]` |

Under the treatment arm (== control), each must fire `OpenRule` once, rest at the FLAT NF above
(the carrier's three-case splice + contractum re-drive AM-3 induction), with empty err/fuel.

## 5. Verdict rule for W-D (this leg)

W-D CONFIRMED iff: (a) `ΔDriveTau/firing = 0` on In/Out/Open (matches the re-derived prediction,
±0 — deterministic counters, exact); (b) `treatment_installed == control_installed` (byte-identical);
(c) every AM-3 subject fires `{OpenRule}` and rests at its flat NF on BOTH arms with empty err/fuel;
(d) valid-NF membership holds. A counter deviating from the above ⇒ STOP + report as a finding
(do NOT adjust). Δ=0 is the expected, honest result — it satisfies Δ≥0 and defers the depth-d Δ>0
to the documented follow-on.
