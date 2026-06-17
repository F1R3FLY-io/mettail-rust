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
3. the defect is **not** in scheduling — the balanced Bool body **is fully built**. A definitive
   InfixLoop+SPPF trace on the minimal failing input `int(b >= 2 <= b >= 3)` shows a cursor
   carrying the complete, correctly-typed SPPF symbol `nt=Bool, span=[2,12),
   rule=LtEqBool(GtEqInt(b,2), GtEqInt(b,3))` — the whole cast body — sitting in
   `InfixLoop{cur_bp:0}` at the closing `)` (pos 12). **No cursor ever advances past pos 12.**
   The full-span Bool body and the `int(`'s cast-wrap frame are on **different GSS lineages**, so
   the `BoolToInt` cast-wrap (which fires via the CrossCatProjection cohort-resolve at the pop
   site) never fires for a body assembled by InfixLoop chain-folding — the `)` is never consumed
   and the cast never forms.

The fix **reconciles** the InfixLoop-built full-span cross-cat-result body with the pending
cast-projection wrap **at the pop site** (`cursor_gss_pop_via_edge` / the CrossCatProjection
cohort-resolve), keyed off the rule **category graph** (fully general — no comparison/arity
coupling), so the wrap fires and `)` is consumed. An evidence gate keeps it **+0 cursors** (parser
identity) and non-masking.

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

## 3. Root cause (definitive, trace-proven, binding-power-independent)

Inside the cast delegate `int( · )` (a cross-category `Bool → Int` cast via `BoolToInt`), the
InfixLoop chain-folds the comparison body and **fully builds the balanced tree**. The
InfixLoop+SPPF trace shows a cursor carrying the SPPF symbol `nt=Bool, span=[2,12),
rule=LtEqBool(GtEqInt(b,2), GtEqInt(b,3))` — the complete, correctly-typed Bool spanning the
entire cast body — resting in `InfixLoop{cur_bp:0}` at the closing `)` (pos 12). So
scheduling/assembly is **not** the problem; the balanced reading exists as a live cursor.

The defect is that **the cast-wrap never fires on it.** The `int(` cast's `BoolToInt` wrap is
applied by the **CrossCatProjection cohort-resolve at the GSS pop site**, and that resolve fires
only for a body delivered on the **cast's own delegate lineage** — not for one assembled by the
InfixLoop chain-folding, which lands on a **different GSS lineage**. Because the wrap never fires,
`)` is never consumed, no cursor advances past pos 12, and the frontier collapses at EOI → "no
accepting branch". The `{<=,>=,!=}`-fail / `{==,>,<}`-pass split and the precedence correlation
are **downstream consequences** of which lineage the chain-fold lands on, not the cause (precedence
falsified, §2.2).

**Code surface** (trace-confirmed; the §7 confirming trace re-pins the exact lines before coding):
the GSS pop / cohort-resolve — `cursor_gss_pop_via_edge` and the CrossCatProjection cohort-resolve
at the pop site — in `prattail/src/wpda_walker.rs`; the rule **category graph** helpers in
`prattail/src/binding_power.rs` (for the general type-witness gate); the shipped
`cast_result_hosting_reentry_source` (a related, proven zero-regression reentry the fix's gate is
modeled on — it handles a cast-result *operand* at a category-changing infix; here the operand is
a *comparison-result* Bool); cross-cat dispatch codegen in
`macros/src/gen/runtime/wpda_codegen/{engine_impl.rs, forks.rs}` only if the change is genuinely in
the generated walker.

## 4. Why the prior analysis was wrong

The plan's analysis doc predicted an H3 `InfixChainIterative` chain-absorption divergence
(`chain_absorbed_intervals`, `wpda_walker.rs:8216-8222`). The trace shows
`chain_absorbed_intervals` is **empty throughout** — its `peek_binary_chain(.., 5)` gate needs ≥5
atoms, which this input never reaches. So **B-fix-1 / B-fix-2 from the analysis do not apply.** The
real mechanism is cohort *scheduling*, not chain *absorption*.

## 5. The fix — pop-site cast-wrap reconciliation (evidence-gated)

The governing principle is the user's own **evidence-driven disambiguation**: use the WPDA's
ambiguity machinery + **behavioral-semantic (type) evidence**, firing **only** on type-evidence so
we never over-fork. Because the balanced body is **already built and already rests at `)`** (§3),
there is **no cohort to schedule** — the single, narrow fix is at the **cohort-resolve / cast-wrap
pop site**.

### 5.1 The reconciliation (the whole fix)

At the CrossCatProjection cohort-resolve in `cursor_gss_pop_via_edge` (the pop site where a cast
delegate's `BoolToInt` wrap fires), generalize the resolve so it ALSO fires the cast-wrap on a
cross-cat-result body that was assembled by InfixLoop chain-folding on a *different* GSS lineage —
i.e. reconcile the two lineages so the `int(` frame's pending wrap is applied to the full-span
`Bool[lo,hi)` body resting at the delegate's `)`. This makes `)` consumable and forms
`BoolToInt(body)`. It **resolves an existing cursor**; it does **not** add cursors.

Admitted **only** under a narrow **type-witness predicate**, keyed off the rule **category graph**
(fully general — no comparison-family or arity coupling):

```
admit_wrap_on_chainfolded_body(delegate, body_cursor)  ⟺
      the delegate's pending wrap is a cast rule `C_in → C_out` in the category graph
          (here Bool → Int via BoolToInt), AND
      body_cursor's resting SPPF symbol has result category C_in (here Bool), spans the FULL
          delegate body, and rests at the delegate's close `)`, AND
      the wrap is genuinely PENDING/unfired for this delegate instance
          (no already-on-lineage body delivered it).
```

This is modeled on the shipped, proven-zero-regression `cast_result_hosting_reentry_source` (which
reconciles a cast-result **operand** at a category-changing infix); here we reconcile a
chain-folded cross-cat-result **body** at the cast delegate's close.

### 5.2 Why this is the right (and only) increment

The earlier framing assumed the cohort had to be *scheduled* and then *continued* (two increments).
The definitive trace (§3) shows the body is already built and already rests at `)`, so **scheduling
is moot** and the fix is exactly the pop-site reconciliation — one narrow change. The §7 confirming
trace re-verifies the lineage mismatch at the pop site (body-cursor lineage vs. the cast frame's
lineage) before any code is written.

## 6. Non-regression argument

- **+0 cursors:** the reconciliation **resolves an existing** body cursor (fires its pending
  cast-wrap); it schedules/forks **nothing**. It fires only under the type-witness predicate, whose
  "wrap genuinely pending/unfired" conjunct is false for every input that parses today (whose cast
  body is delivered on the cast's own lineage and whose wrap already fires) → the cursor set and
  firing order are unchanged → **parser identity** for the passing corpus.
- **Does not mask ill-typed inputs:** the predicate requires a body cursor whose resting symbol has
  result category `C_in`, spanning the FULL delegate body, resting at `)` (a *well-typed* `C_in`
  body). A genuinely ill-typed body (e.g. `int(2 <= b >= 3)`, whose inner `2 <= b` is `Int <= Bool`
  — no rule) never assembles such a full-span well-typed `C_in` cursor at `)`, so it correctly
  **stays failing**.
- **No spec / binding-power change** (proven non-causal in §2.2), so the parser tables, the grammar,
  and the lexer regexes are untouched — the migration contract (parser identity) is honored.

## 7. Implementation plan (B → A)

1. **(B) Re-pin the mechanism at the pop site.** One targeted interning trace on the minimal
   failing input `int(b >= 2 <= b >= 3)` (an `RCB_TRACE`-style env-gated instrumentation, removed
   after), re-verifying §3: the full-span `Bool[2,12)` body cursor's GSS lineage at the pop site
   vs. the `int(` cast frame's lineage, and the exact `cursor_gss_pop_via_edge` / cohort-resolve
   site where the wrap should but does not fire. Build clean first
   (`systemd-run … cargo build … --example tern_probe`).
2. **(A) Implement** the single pop-site reconciliation (§5.1) — a minimal, general change in
   `prattail/src/` (codegen only if the change is genuinely in the generated walker — never
   hand-edit `target/generated/`).
3. **Remove** the temporary instrumentation; keep only the fix. Delete the throwaway
   `languages/examples/tern_probe.rs`.

## 8. Proof obligation (zero-admission)

Extend `formal/rocq/prattail_wpda_runtime/theories/ChainAbsorb.v` (or a new theory) with a
zero-admission lemma capturing the fix's correctness: the pop-site reconciliation fires the
delegate's pending cast-wrap on a body cursor **iff** the type-witness predicate holds (a full-span
well-typed `C_in` body rests at `)`, a cast `C_in → C_out` exists in the category graph, and the
wrap is unfired) — so it (a) **resolves an existing cursor and adds none** (+0 cursors, hence parser
identity off the gate), and (b) does **not** mask an ill-typed body (none assembles the required
full-span well-typed `C_in` cursor at `)`). End with `Print Assumptions <lemma>` reporting "Closed
under the global context"; the full `rocq-prattail-wpda` target stays green (capped build per the
repo convention).

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

- **Surface:** `prattail/src/wpda_walker.rs` — the `cursor_gss_pop_via_edge` / CrossCatProjection
  cohort-resolve at the pop site; a type-witness predicate keyed off the category graph
  (`prattail/src/binding_power.rs`); possibly the cross-cat dispatch codegen; one zero-admission
  Rocq lemma. A **single** narrow increment (the definitive trace collapsed the earlier two-
  increment estimate), modest LOC — but it is the **GSS-lineage reconciliation at the pop site**,
  the fragile core of the historically-difficult cast-compare family where four adjacent-layer
  attempts failed/regressed. The risk is correct surgery at that one site; §7's confirming trace
  re-pins it first.
- **Confidence:** root cause is trace-proven — the full-span `Bool[2,12)` cursor resting at `)` is
  directly observed, and precedence + scheduling + chain-assembly are all falsified. The fix
  **resolves an existing cursor** (+0 cursors by construction) and is modeled on the shipped
  zero-regression `cast_result_hosting_reentry_source`.
