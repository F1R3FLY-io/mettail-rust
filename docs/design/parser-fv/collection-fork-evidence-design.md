# #307 ROOT-F Fix Design — Evidence-Gated Collection Fork

> **Status:** DESIGN v2 (2026-06-11) — REVISED after red-team round 1 (two independent critics,
> both NOT-CONVERGED on v1; they **independently converged** on the fatal v1 transcription error:
> the close branch POPS, so `ConsumeAtAndReplace` was the wrong action). The spec
> `CollectionForkEvidence.v` was EXTENDED with the action-semantics section the critics demanded
> (A1-A4, all `Closed under the global context`). Round 2 next; implementation only after
> convergence. Investigation: /tmp/rootf/findings.md; pgmcp #307/#311.

## The defects (flip-evidenced; unchanged from v1)

- **F-2 generation:** the generated kv_phase=0 post-element fork
  (`macros/src/gen/runtime/wpda_codegen/collection.rs:401-472`) emits THREE branches
  unconditionally: BRANCH-1 close finalizes by consuming ANY token (pseudo-close: `{0|1}` → also
  `{0}`); BRANCH-2 sep·element (checked); BRANCH-3 bare element with NO separator (`{c d}`
  parses; `{c!(p)}` splits into `c`,`p`).
- **F-1 splice race:** POutput in `{c!(p)}` IS hosted+interned but the BRANCH-3 split cursors win
  the lex-min race. **Literal-arg `{x!(0)}` builds POutput 0 times — a DISTINCT residual** (see
  Scope below).
- **F-2 missing refutation:** `packing_satisfies_min_terminal_span` is a no-op for collections
  (min_terminal_span=0 + zero-width `[close,close]` span escape).

## The spec (CollectionForkEvidence.v — 13 theorems, all `Closed under the global context`)

Language layer (v1): `gated_run_iff_loop_lang` (gated machine = EXACTLY the collection
continuation language — no-loss), `shipped_contains_language` (pure over-generation),
`gated_subset_shipped`, `no_branch_no_word` (advance-or-die sound),
`gated_close_lands_on_real_edge`, `pseudo_close_overgenerates` + `bare_element_overgenerates`
(non-vacuous witnesses), `gated_accepts_valid_word`.

**Action layer (v2 — the round-1 critics' demanded extension):**
- `replace_close_cannot_finalize` / `replace_close_never_accepts` — a Replace-shaped close leaves
  the frame on the stack: NO collection word is ever accepted (the total regression v1 would have
  shipped — critic-2 BLOCKER 1);
- `alt0_close_lands_on_wrong_target` — the alt-0-hardwired pop (`ConsumeAndPop` via
  `child_next_pos`) advances to a NON-close target when the close edge is not alt-0 (the rhocalc
  Bag `"}#"`-vs-`"}"` lattice class — critic-2 BLOCKER 2, LIVE not latent);
- `consume_at_and_pop_sound` + `consume_at_and_pop_complete` — the REQUIRED new action
  (`gated_close_pops_and_finalizes`): pops exactly one frame AND lands exactly on the matched
  close target;
- `close_targets_in` / `sep_targets_in` — the membership discipline over the COMPLETE out-edge
  set, for BOTH the close and the sep gates (critic-2 MAJOR 4: the model used membership but v1's
  Rust kept primary-only `token_text ==` at the live gates);
- `advance_or_die_emits_error` — the gated branch BUILDER is empty exactly when no close-edge and
  no sep-edge exists: the transcription obligation is `empty ⇒ WpdaStepAction::Error` — NEVER an
  empty `Fork` (critic-2 BLOCKER 3: empty `ForkInto` silently deletes the cursor and pollutes
  `self.state`).

## The transcription (v2 — every row red-team-corrected)

| Gate | Spec theorem | Rust transcription |
|---|---|---|
| G1 close | `consume_at_and_pop_sound/complete`, `close_targets_in`, `replace_close_cannot_finalize` (why not Replace), `alt0_close_lands_on_wrong_target` (why not plain Pop) | **NEW action pair** `WpdaStepAction::ConsumeAtAndPop { weight, new_state, next_pos }` + `ForkActionKind::ConsumeAtAndPop { next_pos }`: arm = byte-identical to `ConsumeAndPop` (pop via `cursor_gss_pop_via_edge` + `apply_pop_body_to_cursor` finalize) except `child.pos = next_pos` replaces the alt-0 `child_next_pos` call. New-variant checklist per the 9fdaed68 precedent: execution arm (`apply_action_to_cursor` exhaustive match), `guard_category_changing_infix` suppression read, `action_size_bytes`, walker-stats classifiers (own bucket, NOT shared), `cohort_lazy` arms, `project_continuation_record_for_action`. A `__collection_close_targets(tokens, pos, close)` helper (the `__mixfix_literal_targets` shape: peek_text + peek_alternatives, deduped) supplies one branch per matching edge |
| G1 sites | same | **ALL THREE close sites** (critic-1 F-C): (1) the post-element kv_phase=0 fork (`collection.rs:425-434`, Bag/Set/List **and Map** — Map values re-enter kv_phase=0); (2) the **empty-collection bootstrap** (`engine_impl.rs:288-340` — currently `peek_text`-primary-only + alt-0 `ConsumeAndPop`: the `primary_equality_loses` trap); (3) the InfixLoop CollectionMarker close/sep filter (`engine_impl.rs:932` — primary-only `token_text == close \|\| sep`) |
| G2 sep | `sep_targets_in`, `gated_run_iff_loop_lang` (sep case) | **UPGRADED from v1's "unchanged"** (critic-2 MAJOR 4): the sep DETECTION gates get the same membership discipline (`__collection_sep_targets`); the sep consume branch itself stays structurally as-is. Live justification: rhocalc Bag's multi-char `"}#"`/`"#{"` delimiters are genuine lex-fork candidates TODAY |
| G3 bare element | `bare_element_overgenerates`, `gated_run_iff_loop_lang` (bare case) | emitted at CODEGEN time only when the **ENTRY separator** is empty: `CollectionShape.separator.is_empty()` for Class-5 collections (Map: the entry separator, NEVER `pair_separator`); **`CollectionSepInfo.separator` for binder-internal collections, with an audit of the `String::new()` default at binder.rs:523** (critic-1 F-D: an unset default must not silently license whitespace-joining). Empty-sep grammars EXIST (`ast/src/tests.rs:107` `sep ""`), so BRANCH-3 stays live for them |
| G4 advance-or-die | `no_branch_no_word`, `advance_or_die_emits_error` | the fork is built as a **dynamic vec** (push licensed branches only) + `if __branches.is_empty() { WpdaStepAction::Error(...) } else { Fork { branches } }` — the established `wpda_walker.rs` guard pattern; NEVER a static `vec![b1,b2,b3]` with members conditionally absent |
| Coverage backstop | — | **DEFERRED to a separate ticket** (both critics): on lattice sources the EOI span window is bypassed (`semantic_root_accepts_at_cursor` returns true unconditionally) and `CollectionId` carries no spans — the v1 backstop was a NO-OP on the only grammars exhibiting F-2, with an unmodeled intern-key blast radius. The gates alone make the machine generate EXACTLY the language (`gated_run_iff_loop_lang`), so there is no junk left to refute |

## Scope (critic-1 F-E — the headline-test honesty)

- The gates close **F-2 entirely** (`{0|1}` → 1 alt; `{c d}` → ERR) and **F-1's var-arg form**
  (`{c!(p)}` — the split cursors that win the race are no longer generated).
- **`{x!(0)}` (literal-arg) is NOT claimed**: the investigation proved POutput is built 0 times
  there — the host is starved BEFORE any splice race, a distinct mechanism (literal-arg cross-cat
  host starvation in element context). The implementation step includes a MANDATORY post-gate
  trace of `{x!(0)}`: if the host now assembles (the starvation was downstream of the split fan),
  record the win; if not, the residual is scoped as its own #307 sub-item with its own
  investigation — the gates are NOT claimed to close `parsing::send` until that trace says so.

## Verification plan

- Battery + **ambient_tests (27 multi-element collection sites) + guarded_rho + gen_ambient_op +
  gen_guardedrho_op** as REQUIRED re-baseline targets (critic-1 F-G; ledtest SENTINEL is immune —
  no collections — and must stay 220/0).
- **Recovery probe BEFORE implementation** (critic-1 F-H): run `recovery_bounded_dispatch` + the
  `gen_*_analytical` recovery tests with BRANCH-1 toggled unchecked→checked and diff verdicts —
  today's pseudo-close is an accidental error-tolerator (`{0 1` finalizes `{0}` instead of
  erroring); G4 hands those positions to the recovery engine, which may surface NEW repair
  behavior. Document whether pseudo-close is load-bearing for any recovery test.
- Flip experiments: `{c!(p)}` → contains `c!(p)`; `{0|1}` → exactly 1 alt; `{0|1|2}` → 1 alt;
  `{c d}` → ERR; `{(c?x).{*(x)} | c!(p)}` → comm shape correct; `{x!(0)}` → TRACED (see Scope);
  controls: `{(c!(p))}`, `{*(x)}`, `{(c?x).{*(x)}}`, top-level `x!(0)` stay green; empty `{}`
  collections unaffected (separate site, now also membership-checked).
- Splice-gate `Some(CategoryEntry) => true` (wpda_walker.rs:15691): NOT touched (smaller blast
  radius), recorded as *unproven-benign for cross-cat mixfix elements* (critic-1 F-F) — not
  claimed closed.

## Round-1 red-team record (convergence conditions → v2 disposition)

| Finding | Severity | v2 disposition |
|---|---|---|
| C1 F-A ⊕ C2 B1/B2: `ConsumeAtAndReplace` doesn't pop; `ConsumeAndPop` is alt-0-only | BLOCKER (convergent) | `ConsumeAtAndPop { next_pos }` specified + A1-A3 proven |
| C2 B3: empty Fork silently deletes the cursor | BLOCKER | dynamic-vec + `is_empty → Error` mandated + A4 proven |
| C1 F-C: three close sites share the defect (incl. Map kv_phase=0, empty-collection bootstrap) | MAJOR | all three sites in G1; shared helper |
| C2 M4: sep/close DETECTION gates are primary-only (`}#` live) | MAJOR | G2 upgraded to membership |
| C1 F-B ⊕ C2 M5: covering-span backstop is a lattice NO-OP with unmodeled blast radius | BLOCKER/MAJOR | backstop DEFERRED |
| C1 F-D: sep_empty oracle ambiguity (Map two separators; binder `String::new()` default) | MAJOR | entry-separator rule + binder audit |
| C1 F-E: `{x!(0)}` literal-arg starvation is a distinct root | MAJOR | scoped out with a mandatory post-gate trace |
| C1 F-G: ambient/guarded_rho re-baseline omitted | MINOR→MAJOR | added as required targets |
| C1 F-H: recovery masking by pseudo-close | MINOR | pre-implementation recovery probe mandated |
| C1 F-F: splice-gate CategoryEntry unconditional-true | MINOR | untouched, recorded unproven-benign |
| Failed attacks (recorded): G3-dead-code (refuted: `sep ""` exists); FV-vacuity (refuted); BRANCH-2-unchecked (refuted: consume is checked; detection was the gap); ledtest-regression (refuted: no collections); trailing-sep `{0\|1\|}` (refuted for the corpus; latent note added); nested-collection wrong-close (refuted: per-marker static lookup); weight-dependent winner on junk branches (not found); `{}` broken by gates (refuted: separate site) | — | — |
