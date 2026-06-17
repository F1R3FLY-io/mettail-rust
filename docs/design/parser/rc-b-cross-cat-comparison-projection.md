# RC-B — Balanced comparison trees inside a cast delegate: cross-category projection scheduling

> **Status: DESIGN (awaiting implementation green-light).** Branch `feature/wfst-architecture`.
> Plan §4a (`~/.claude/plans/can-you-recover-and-buzzing-kite.md`) RC-B. BACKEND-ONLY — no
> grammar/regex/spec change is warranted (proven below). This document is the *design*; the
> implementation is gated on review per the user's "design first, then decide" choice.

## 1. Summary

The single remaining Calculator parse failure, `simulator_regression_cross_cat_dispatch_chaining`
(`languages/tests/calculator.rs:1365`), is **not** the chain-absorption / precedence bug the prior
analysis predicted. Two trace-driven investigations (≈220 min total) established, *by experiment*,
that:

1. the failing input has a **valid** parse (so this is a real parser bug, not an ill-typed input);
2. operator **precedence is correlated but not causal** — flattening all six comparisons to one
   shared non-associative precedence leaves the failure matrix **unchanged**; and
3. the defect is in the **cross-category projection scheduler**: it never schedules the outer
   comparison's full-body `wrap = (Bool, M)` cohort when the middle operator `M` is a
   *later-declared* comparison whose left operand is itself a comparison-result.

The fix (**Plan 2**) generalizes an already-shipped, zero-regression reentry mechanism
(`cast_result_hosting_reentry_source`) in the projection/evidence-gating layer, gated by a narrow
**type-witness predicate**, adding **+0 cursors** so it cannot regress any currently-passing input.

## 2. The bug

```
input:  int(b >= 2039068204 <= b >= -2074699644)
error:  1:4: ... no accepting branch reached end of input, found Fixed("(")
```

`Fixed("(")` is the correctly-lexed `(` **keyword** token (not the `CanonicalFixedPoint` literal
category — that distinction was the original red herring). The position is the `(` after `int`,
i.e. the cast `int(…)` could not form because its inner Bool expression reached no single
accepting parse, collapsing the cursor frontier to zero.

### 2.1 A valid parse exists (this is a bug, not an ill-typed input)

Comparisons in Calculator are typed **per category** with **no implicit `Int → Bool` coercion**
(`languages/src/calculator.rs`): `GtEqInt : a:Int, b:Int ⊢ … : Bool`,
`LtEqBool : a:Bool, b:Bool ⊢ … : Bool`, etc. The only well-typed reading of
`b >= 2039068204 <= b >= -2074699644` is therefore the **balanced tree**

```
            LtEqBool : Bool                 int( · ) : Int   (BoolToInt cross-cat cast)
           /             \                         │
   GtEqInt:Bool      GtEqInt:Bool        ──────────┘
   /      \           /       \
  b   2039068204     b    -2074699644
```

The **left-associative** infix loop instead greedily consumes the middle operand `b` into the left
spine — building `((b >= 2039068204) <= b) >= -2074699644` — which is **ill-typed**
(`Bool >= Int` has no rule) — and never completes the balanced reading. Empirically, all three of

```
int( (b >= …) <= (b >= …) )     int( b >= … <= (b >= …) )     int( (b >= …) <= b >= … )
```

parse; **only the fully-bare form fails.** So a valid AST exists and the WPDA must surface it.

### 2.2 Discriminators (experimentally established)

| probe family | result |
|---|---|
| `b S 2 M b S 3`, `M ∈ {==, >, <}` (declaration positions 1–3) | **OK** |
| `b S 2 M b S 3`, `M ∈ {<=, >=, !=}` (declaration positions 4–6) | **FAIL** (valid parse exists) |
| genuinely ill-typed, e.g. `int(2 <= b >= 3)` | **FAIL** (correct — must stay failing) |

The discriminator is **declaration order of the middle operator**, *not* its binding power:

- **Precedence falsification (decisive):** all six comparisons were flattened to a single shared
  **non-associative** precedence (`l_bp = r_bp = 2`, verified in the generated parser), derived
  generally from the rule category graph. The **6×6 failure matrix did not change.** Hence the
  textbook "make comparisons non-associative" fix has **zero** effect here, and **no spec or
  binding-power change is warranted.** The precedence ladder that the trace shows blocking the
  `l_bp >= cur_bp` gate is a *consequence* of which cohorts the cross-category projection scheduler
  builds, not the cause.

## 3. Root cause (precisely localized, binding-power-independent)

Inside the cast delegate `int( · )` (a cross-category `Bool → Int` cast via `BoolToInt`), the WPDA
parses the Bool body by spawning **projection cohorts**. The **cross-category projection scheduler**
fails to schedule the outer comparison's **full-body cohort** `wrap = (Bool, M)` exactly when:

- the middle operator `M` is a **later-declared** comparison (the `{<=, >=, !=}` half), **and**
- `M`'s left operand is itself a **comparison-result** (a `Bool` produced by an inner comparison).

Because that cohort is never scheduled, the balanced reading is never carried to the closing `)`,
and the frontier collapses → "no accepting branch". A secondary obstruction (observed when a
balanced cursor is force-spawned) is the **cast-wrap continuation**: a balanced multi-comparison
Bool body cannot transition to the outer `BoolToInt` wrap at `)` without the explicit-paren
`GroupingMarker` — see §5.2.

**Code surface** (to be confirmed by the §7 implementation trace, not re-derived from scratch):
the cross-category projection/cohort scheduler and the `cast_result_hosting_reentry_source`
mechanism in `prattail/src/wpda_walker.rs`; the canonical-iter / category-graph machinery in
`prattail/src/binding_power.rs`; the cross-cat dispatch codegen in
`macros/src/gen/runtime/wpda_codegen/{engine_impl.rs, forks.rs}`.

## 4. Why the prior analysis was wrong

The plan's analysis doc predicted an H3 `InfixChainIterative` chain-absorption divergence
(`chain_absorbed_intervals`, `wpda_walker.rs:8216-8222`). The trace shows
`chain_absorbed_intervals` is **empty throughout** — its `peek_binary_chain(.., 5)` gate needs ≥5
atoms, which this input never reaches. So **B-fix-1 / B-fix-2 from the analysis do not apply.** The
real mechanism is cohort *scheduling*, not chain *absorption*.

## 5. The fix — Plan 2: evidence-gated projection surfacing

The governing principle is the user's own: **evidence-driven disambiguation** — use the WPDA's
inherent ambiguity machinery plus **behavioral-semantic (type) evidence** to surface the balanced
reading *only* when the greedy left-associative spine is ill-typed, so we never over-fork.

### 5.1 Increment 1 — schedule the balanced full-body cohort (type-witness gated)

Generalize the **already-shipped** `cast_result_hosting_reentry_source` reentry mechanism (which
today re-hosts a cast result back into a continuation, with proven zero regression) so that, inside
a cross-category projection, it also schedules the outer comparison's full-body
`wrap = (Bool, M)` cohort. The scheduling is admitted **only** under a new narrow **type-witness
predicate**, keyed off the **rule category graph**:

```
admit_balanced_cohort(M, lhs)  ⟺
      lhs is a comparison-result (its result category is the comparison output, Bool), AND
      M has a same-result variant whose left operand category matches lhs's result
          (i.e. a well-typed M-over-(Bool, ·) exists in the category graph), AND
      the greedy left-associative spine reading at this point is ill-typed
          (no rule admits `spine-result M next-operand`).
```

The third conjunct is the decisive **evidence gate**: it fires the balanced fork **only** when the
greedy reading has no typing, so for every input that currently parses (greedy reading well-typed)
the predicate is false and **no new cohort is scheduled** → **+0 cursors** → parser identity for all
passing inputs is preserved by construction. This is *why* it cannot regress
`simulator_regression_cross_cat_with_strings` the way the earlier blanket RHS-fork did (§6).

### 5.2 Increment 2 (conditional) — cast-wrap continuation to `BoolToInt` at `)`

If, after Increment 1, the balanced cohort reaches `)` but still cannot transition to the outer
`BoolToInt` wrap without an explicit-paren `GroupingMarker`, a second, equally-narrow increment
extends the cast-delegate continuation to accept a balanced multi-comparison Bool body at the
delegate's close (synthesizing the same continuation the explicit-paren `GroupingMarker` provides).
Whether Increment 2 is needed is **determined empirically by the §7 confirming trace** (the bare vs.
parenthesized discriminator in §2.1 indicates it likely is); the design does not assume it away.

## 6. Non-regression argument

- **+0 cursors:** Increment 1 schedules the balanced cohort *only* when the greedy spine is
  ill-typed. Any input that parses today has a well-typed greedy reading, so the predicate is false
  and the cursor set is byte-for-byte unchanged → **parser identity** for the entire passing corpus.
- **Does not mask ill-typed inputs:** the predicate's first two conjuncts require a *well-typed*
  balanced M-over-`(Bool, ·)` to exist in the category graph; genuinely ill-typed inputs (e.g.
  `int(2 <= b >= 3)`) have no such variant, so they correctly **stay failing**.
- **No spec / binding-power change** (proven non-causal in §2.2), so the parser tables, the grammar,
  and the lexer regexes are untouched — the migration contract (parser identity) is honored.

## 7. Implementation plan (B → A)

1. **(B) Confirm the mechanism.** One targeted interning trace on the *correct* minimal failing
   input `int(b >= 2 <= b >= 3)` (an `RCB_TRACE`-style env-gated instrumentation, removed after),
   confirming exactly why the later-declared-`M` projection cohort is not scheduled, and whether
   Increment 2 is required. Build clean first (`systemd-run … cargo build … --example tern_probe`).
2. **(A) Implement** Increment 1 (+ Increment 2 if §7.1 shows it is needed), each a minimal,
   general change in `prattail/src/` (and codegen only if the change is genuinely in the generated
   walker — never hand-edit `target/generated/`).
3. **Remove** the temporary instrumentation; keep only the fix. Delete the throwaway
   `languages/examples/tern_probe.rs`.

## 8. Proof obligation (zero-admission)

Extend `formal/rocq/prattail_wpda_runtime/theories/ChainAbsorb.v` (or a new theory) with a
zero-admission lemma capturing the fix's correctness: under a cross-category cast delegate, the
type-witness-gated balanced-cohort scheduling converges to the single accepting cohort (no
>1-category divergence) **and** is admitted **iff** the greedy spine is ill-typed (so it neither
over-fires — preserving +0 cursors — nor masks an ill-typed body). End with `Print Assumptions`
reporting "Closed under the global context"; the full `rocq-prattail-wpda` target stays green
(capped build per the repo convention).

## 9. Verification plan (the gate)

- `simulator_regression_cross_cat_dispatch_chaining` passes → Calculator target **95/1 → 96/0**.
- Add explicit regressions: every `b S 2 M b S 3` for `M ∈ {<=, >=, !=}` (the true bug class) parses;
  the ill-typed controls (`int(2 <= b >= 3)`) **stay failing**; the explicit-paren controls keep
  parsing.
- **Zero regression** on the full gauntlet: `gen_calculator_{unit,analytical,rewrite}`
  (52/224/169), `gen_rhocalc_{unit,analytical,rewrite}` (52/126/86), `gen_ambient_*`,
  `edge_case_tests`, `wpda_parity_{calculator,calculator_cross_cat,rhocalc_collections}`,
  `simulator_regression_cross_cat_with_strings`, prattail `--lib` (3766/0). (Pre-existing
  `roundtrip_tests::idempotent_int_display` on the pinned `Fact(Neg(NumLit(0)))` `-0`→0
  lexer-canonicalization case is *not* in scope — it must not be hidden, nor counted as a
  regression.)

## 10. Alternatives considered and rejected (all trace-tested)

| Approach | Verdict |
|---|---|
| H3 chain-absorb suppression (analysis B-fix-1/2; `chain_absorbed_intervals`) | **Inapplicable** — never fires (needs ≥5 atoms; §4) |
| Make comparisons non-associative / re-ladder precedence (spec or backend) | **No effect** — precedence non-causal, proven by the flatten experiment (§2.2) |
| Orphan-revival of stranded InFlight members at the collapse boundary | **Falsified** — they re-dispatch / re-collide / re-strand |
| Broaden the cross-cat-LHS hosting gate (`cond5`) to admit Var operands | **Falsified** — the cond5-rejected cursor is a correctly-suppressed *invalid* continuation |
| Lower the cross-cat-comparison RHS binding-power floor + blanket Tomita fork | **Falsified** — balanced branch spawned but produced 0 EOI cursors **and** regressed `with_strings` (94/2); this is precisely why the real fix must be **evidence-gated / +0-cursors** |

## 11. Scope & risk

- **Surface:** `prattail/src/wpda_walker.rs` (the projection scheduler + `cast_result_hosting_reentry_source`
  generalization), a new predicate keyed off the category graph (`binding_power.rs`), possibly the
  cross-cat dispatch codegen; one Rocq lemma. Estimated **1–2 increments**, modest LOC, but in the
  historically-difficult cast-compare family — the risk is in *correct localization*, which §7.1's
  confirming trace de-risks before any code is written.
- **Confidence:** the root cause is experiment-grounded (precedence falsified; bug class isolated;
  valid-parse-exists verified); the fix reuses a proven zero-regression mechanism and is
  +0-cursors-by-construction. The main open question — whether Increment 2 is needed — is resolved
  by the first implementation step, not assumed.
