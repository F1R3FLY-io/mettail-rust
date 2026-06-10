# Evidence-Driven Early Pruning + Laziness for State-Space Control

> **Status:** research direction (user-directed 2026-06-10), to guide the next FV
> steps of the cast-compare cursor-merge research and the pipeline broadly. NOT an
> immediate course change — recorded so subsequent steps follow it.

## The principle (user, verbatim intent)

> "I am not describing premature disambiguation, but pulling in evidence into
> earlier stages of the pipeline to avoid generating superfluous alternatives that
> will ultimately be rejected." … "seek ways to intelligently produce transitions
> that do not result in state-space explosions and how to clean up the state-space
> throughout the pipeline. Consider ways to pull in additional evidence for how to
> disambiguate alternatives to safely prune alternatives, such as with lookaheads
> and how the types will be used. This should already be partially realized, but I
> feel it can be taken further advantage of."

Two distinct, both-sound levers — and one forbidden non-lever:

1. **Evidence-driven EARLY rejection (avoid generating).** Apply each evidence
   rule **as early as its inputs exist**, but ONLY evidence that is **monotone
   under continuation** (true now ⇒ true regardless of how the parse completes).
   Then a superfluous alternative is *never generated* rather than generated and
   later collapsed/rejected. This is the Phase EC principle (`EvidenceComplete.v`)
   and is **sound** — it removes only alternatives that *definite* evidence
   refutes/de-selects, never a still-viable one.
2. **Laziness / demand (defer generating).** Generate transitions on demand,
   best-first by weight, bounded by `[k]`/fuel — so the unrealized tail never
   costs memory. Relieves the memory pressure of any residual explosion.
3. **(FORBIDDEN) heuristic/premature disambiguation** — dropping an alternative
   that is *not* refuted by definite evidence. Excluded by Invariant 1/2 and
   `weight_drop_can_lose_valid_alternative`. The cohort **merge** is NOT this: it
   collapses *observationally-equivalent* cursors (a quotient), losing no parse.

**Relationship to the cohort merge (CastDelegateMergeBound.v):** the merge is the
*cleanup* lever (collapse the K-per-level delegate blowup to linear, after/at
generation). Evidence-gating is the *prevention* lever (don't dispatch the
delegate for an infix the lookahead/type-usage shows cannot apply). They compose:
prevention shrinks what is generated; the merge bounds whatever remains; laziness
defers realizing the tail.

## Evidence sources to pull earlier (the "take further" targets)

### A. Lookahead as monotone evidence for cross-cat-LHS delegate dispatch
The cast-then-compare blowup comes from dispatching the cross-cat-LHS delegate for
**every** category-changing infix whose source is the operand category (K per
level). But the **next token after the operand** is definite, monotone evidence:
- `int(3) == 3` — after `int(3)` (Int), the lookahead `==` is evidence that an
  Int-sourced category-changing infix (`EqInt`/…) applies ⇒ dispatch ONLY the
  delegate(s) whose infix trigger matches the lookahead, not all K.
- `int(3) + 3` — lookahead `+` is a same-category infix (no cross-cat-LHS delegate
  needed) ⇒ dispatch NO cross-cat-LHS delegate.
- `int(3)` at EOI / before a non-infix — no following infix ⇒ NO delegate.

This is **sound** (the infix's trigger literal is already in the input; matching it
is definite, not a guess) and **monotone** (a present trigger stays present). It
prunes the delegate fan-out *at the source* — the K-per-level factor drops to
"infixes whose trigger matches the actual lookahead token" (usually 0 or 1).
**This is the lever to model next** (an `evidence_gated_delegates` refinement of
`CastDelegateMergeBound.v`: dispatch a delegate only when the lookahead token is in
the FIRST set of a C-sourced category-changing infix; prove it (a) never drops a
parse the input actually has, (b) shrinks the frontier below the merged bound).

### B. Type-usage / sink-type evidence
How a sub-result will be **used** is monotone evidence for which interpretation to
generate. If a position's enclosing rule demands a specific category (the "sink
type"), interpretations of other categories are refuted early (the cross-cat
`into_term::<T>()→None` rejection at packing is the existing partial realization;
`packing_satisfies_min_terminal_span` is another). Pull the sink-type constraint
*forward* to the dispatch so off-type alternatives are not generated. Ties to the
predicated-type sieve story (`⊥`/refute-at-`0̄`) and the OSLF evidence functor.

### C. Already-realized evidence to extend further
- CD02 disjoint-FIRST deterministic dispatch (zero ambiguity ever constructed).
- `ContextWeight::is_zero()` branch elimination at dispatch.
- token-soundness (`packing_satisfies_min_terminal_span`) + cross-cat
  `into_term::<T>()→None` at packing/realize.
- the H3 chain-absorption / R4 suppression (don't dispatch inside an
  already-parsed interval).
These are evidence-driven early rejections already shipping; the directive is to
extend the *set* of monotone evidence applied at dispatch (add A and B).

## FV plan for the next steps (work backwards from the model)

1. **`evidence_gated_delegates` model** (extend `CastDelegateMergeBound.v` or a new
   theory): the cross-cat-LHS delegate for infix `op_i` is dispatched at a position
   ONLY if the lookahead token ∈ FIRST(`op_i` trigger). Prove:
   - *no-loss*: for every parse the input admits, the gated dispatch still
     generates the delegate that realizes it (the trigger is in the input ⇒ gate
     passes) — monotone-evidence soundness;
   - *frontier shrink*: gated frontier ≤ merged frontier ≤ `S d`, and for inputs
     with no following cross-cat infix, the cross-cat-LHS delegate count is 0;
   - compose with `merge_preserves_coverage` (the gated+merged delegate fires
     exactly the evidenced infixes).
2. **Type-usage gating model**: sink-type at a position refutes off-type
   interpretations at dispatch; prove sound (only refutes interpretations the
   enclosing rule cannot consume — `into_term::<T>()→None` monotone).
3. **Laziness accounting**: tie the bounded frontier to demand-bounded realization
   (the unrealized tail is not materialized) — memory bound, not just count bound.
4. **Then implement**: cohort-share the delegate (the merge) AND evidence-gate its
   dispatch by lookahead (and, where available, sink-type) — so the cast-compare
   family parses with a frontier that is both *small* (evidence-gated) and
   *bounded* (merged), each step paired with a zero-admission proof.

## Pipeline-wide cleanup (the "throughout the pipeline" directive)

Apply the same discipline at each stage seam, evidence permitting:
- **lex→parse**: lattice token source already prunes by lexical evidence; extend to
  defer lexically-ambiguous forks until a downstream dispatch demands the
  distinction (lazy token frontier, Phase 2L).
- **parse frontier**: evidence-gated dispatch (A,B) + cohort merge (cleanup) +
  demand-bounded realization (laziness).
- **parse→eval**: carry evidence rejections (`Err`/⊥) so eval never explores a
  refuted alternative; the e-graph/congruence quotient is the eval-side cleanup.
All cleanups are **quotients or evidence-refutations**, never weight-drops.
