# The Foreign Exchange — Lambda FLTs shipped, matched, and executed over RSpace

The debut demonstration of Rholang↔MeTTaIL Foreign Language Terms: a foreign term built by one
process, shipped over the tuplespace, destructured by a pattern with a typed hole, guard-vetoed
fail-closed, rebuilt from its captured holes, and executed to β-normal form — every step a
committed COMM on F1r3node's RSpace. Companion piece to `../rhocalc-settlement/` ("same machine,
same guards — now the *data* is a language").

> **The load-bearing fact**: the FLT FIP (2026-06-26, under review) predates the A-S5/A-S6 flip.
> Today every FLT runtime ingredient exists at the ABI level — the reflected-term wire format
> with per-language unforgeable tags, hole capture via spatial matching, hole fill via
> construction, fail-closed `where` guards at commit time, and in-Rho reduction to normal form —
> only the surface syntax is missing, and that is exactly the part still in flux. This demo
> shows the semantics and narrates the syntax (slides may show the FIP surface with a
> "proposed — in flux" banner; the terminal shows only landed notation).

**Vehicle**: a demo-local binary (`repl/src/bin/flt_demo.rs` proposed — decision D1), one beat
per invocation, fresh in-memory Rho machine per beat, deterministic seed. Zero production-code
changes; a pinning test twin (`rholang-runtime/tests/flt_abi_over_rspace.rs`) doubles as script
validation (the task-#8 integration-test pattern). Outputs marked **(to validate)** are pinned
in the build window before presenting.

**Notation** (display only): `⌜X⌝` = the unforgeable GPrivate tag for label X
(`mettail.term.{fp}.X` — deterministic per language fingerprint, unforgeable *from within the
tuplespace surface*: no syntax can spell a GPrivate and the matcher compares them by identity);
`⟦t⟧` = the reflected Par of term t. Demo constants: `id = lam x. x`;
`K = lam a. lam b. a` (the committed golden); subject `App(id, K)`; `Ω` (fuel witness).
**Hole convention (the honest bridge to `${x}`)**: a free variable in the guest pattern source
is a hole — parsed by the real Lambda parser, its `^free` leaf transformed to a match
FreeVar. Narrate: "`f` here is what the refined syntax spells `${f}` — same AST position,
different ink."

---

## Beat 0 — The wire format existed before the syntax (1 min, no run)

Print `id`, `K`, their reflected tagged-EList forms, and the literal tag string.

> "Every MeTTaIL language already ships with a canonical machine representation of its terms —
> a tagged list whose head is an unforgeable name minted per language. That IS the
> foreign-language-term wire format. Tonight we use it as one."

## Beat 1 — Ship a Lambda FLT; destructure it with a typed hole (3 min — THE CORE)

Program: `@"fltX"!(⟦App(id, K)⟧) | for( @[⌜App⌝, ${f}, ⟦K⟧] <- @"fltX" ){ @"OUT"!(f) }`
— the hole at the function position; a GROUND `⟦K⟧` subpattern at the argument position (exact
structural match including tags).

Expected **(to validate)**: `OUT: [⟦id⟧]`, de-reflected `lam x. x` (α-fresh binder).
Negative 1b: send `⟦K⟧` alone (not an App) — zero COMMs, `OUT` empty, the datum RESTS on
`fltX` (the guard-oracle discipline).

> "A process built a term of a different language, sent it over the tuplespace, and a
> for-comprehension took it apart by shape. The variable is a typed hole: it can only bind the
> subtree at that grammar position. And matching is fail-closed: a wrong-shaped term just sits
> on the book."

## Beat 2 — The where-guard vetoes on a foreign subterm (2 min)

Program: `for( @[⌜App⌝, ${f}, ${a}] <- @"fltX" where a == ⟦K⟧ ){ @"OUT"!(f) }` — the guard
rides `Receive.condition`, evaluated purely at commit.

- Send `⟦App(id, id)⟧`: expected **(to validate)** `OUT: []`, datum resting — veto, zero
  partial effects.
- Send `⟦App(id, K)⟧`: expected **(to validate)** `OUT: [⟦id⟧]`.

Inline fallback (D2): if `EEq` over reflected Pars misbehaves in validation, use the ground-
subpattern form from Beat 1 (`…${f}, ⟦K⟧]` vs `…${f}, ⟦id⟧]`) — the identical veto observable
through pure pattern shape.

> "The guard is a semantic predicate over a foreign AST — not text. It runs inside the
> machine's matcher before the COMM commits; a false guard consumes nothing and emits nothing.
> Same theorem-backed physics as the Settlement Desk."

## Beat 3 — The counterfeit is rejected: tags are unforgeable (1.5 min)

Send the string-tagged fake `["App", ⟦id⟧, ⟦K⟧]` (GString head) at the same receive.
Expected **(to validate)**: no match; the datum rests.

> "This is why FLTs are not string interpolation. A term claiming to be Lambda by *name*
> doesn't match — the language tag is an unforgeable private name compared by identity, not
> spelling. You cannot conjure a foreign term out of strings. That is the runtime face of the
> FIP's No-Injection property."

## Beat 4 — Fill the holes and RUN it: quotation to β-normal form (3 min — THE WOW)

Program: `@"fltX"!(⟦App(id, K)⟧) | for( @[⌜App⌝, ${f}, ${k}] <- @"fltX" ){
⌜^drive⌝!( [⌜App⌝, f, k], fuel, "OUT" ) }` — the continuation RE-QUOTES the term from its two
captured holes (construction-position fill, machine-side) and seeds the installed quiescence
driver.

Expected **(to validate)**: `OUT: [⟦K⟧]` de-reflected `lam a. lam b. a`; the `^fired` ledger
`["Beta"]`; `^drive-err`/`^drive-fuel` empty (the always-on cross-check).

Beat 4b — the live trace (`StepSession` + the τ-classifier): step 1 is the USER-level FLT
rendezvous COMM on `fltX`; every subsequent step classifies `[τ drive]`/`[τ subst]`; terminal
`[Rho output] OUT observes ⟦K⟧` **(to validate)**.

> "One visible communication — the foreign term changing hands — then a cascade of τ-steps: the
> driver matching, β firing through the substitution calculus, the contractum re-driving. The
> evaluator for the guest language is itself a set of processes in the same tuplespace. Nothing
> here is my laptop interpreting Lambda; it's all committed COMMs on real RSpace."

## Beat 5 — The behavioral predicate, honestly; the NF re-shipped (2.5 min)

Producer `@"fltX"!(⟦App(id,K)⟧)`; consumer 1 `for(@${t} <- @"fltX"){ ⌜^drive⌝!(t, fuel, "nf") }`;
consumer 2 `for( @[⌜^lambda⌝, ${b}] <- @"nf" ){ @"OUT"!([⌜^lambda⌝, b]) }`.

Expected **(to validate)**: `OUT: [⟦K⟧]`. Negative: producer sends `⟦Ω⟧` — the typed
`^drive-fuel` exhaustion datum; `nf` empty; consumer 2 never fires; `OUT: []`.

> "The prototype note asked for `where bar |= <behavioral predicate>`. Here is its first honest
> form: 'bar drives to a λ-value' — a diamond-modality check realized as drive-then-match. The
> formula language this grows into is the OSLF-generated Hennessy–Milner logic — the Knotted
> Topoi keystone says that logic is the internal logic of the model. And the second consumer:
> a normal form produced by one FLT interaction was re-shipped and pattern-matched by another.
> That is inter-FLT communication — the runtime mandate's second reason, live."

Total ~13–14 min (+ optional openers: the stock-RhoCalc "stringly-typed strawman" cameo that
Beat 3 then kills; the Settlement Desk Beat-2 bridge).

---

## Where the set automaton + scions/grafting fit (say it precisely)

1. The for-comprehension's FLT match is the machine's SPATIAL matcher on reflected shapes —
   not the set automaton; scions/grafting do not apply to that layer.
2. Executing the matched LAMBDA term gains nothing from scions — β's contractum is a computed
   substitution result; `ScionBundle ≡ ContractumRedrive` for SubstRewrite arms; Lambda's cells
   are pre-registered A/A nulls in the locked E-1 ledger (experiment 147). Beat 4 claims the
   driver, not grafting.
3. The set automaton IS the compilation substrate — "the language's rules were compiled into
   this driver's redex arms and dispatch network by an interned-pattern-DAG set automaton,
   provably size-optimal" (doc 21 §7.3 + the size pins).
4. THE DEEP RHYME (the phase-3 closing beat): **holes are buds; the quotation is the scion;
   filling a bud with an already-analyzed FLT is a graft** — two pre-explored configurations
   composed with zero re-scanning; scions grafted into scions' buds = the inter-FLT pipeline's
   formal backbone (soundness anchor: graft ⊑ completed). Honest caveat: today the spatial
   matcher re-scans per match — the bud/scion ECONOMY becomes real when graft machinery extends
   from the driver's firing seam (E-1; the `FiringEmission::ScionBundle` seam is landed,
   deliberately constructed nowhere) to the FLT matching layer: consumers holding
   CONFIGURATIONS, so a re-shipped hole-filled FLT costs only its genuinely-new material —
   novel beyond the thesis (grafting at the communication layer). With a STRUCTURAL guest
   (an Ambient FLT — In carries s=5 known constructors; locked prediction Δ=3 DriveTau/firing),
   grafting becomes measurably visible.
5. Timing: E-1's legs are queued behind the EPathMap fix; the phase-now demo runs WITHOUT
   scions; the graft beat drops in when E-1 lands.

Thread-line: "The set automaton compiled this language into the machine; the spatial matcher
destructures the foreign term; and the same theory's grafting chapter is how filled FLT holes
will re-enter matching incrementally once E-1 lands — today's demo needs none of that to run."

## Phases

- **Phase now (this sheet)**: the ABI-level demo bin + pinning test twin. ~1 build-window day
  to green beats; a second for validation + recording. No production crate touched.
- **Phase 2**: the smallest honest syntax — a RhoCalc `PFlt` literal (`L```…``` ` fence mode,
  `${x}` holes, construction + pattern positions) lowered through the guest parser + the
  reflected ABI; NOT a REPL text pre-pass (textual splice is the exact insecure path
  No-Injection rejects). 1–2 weeks honest; the guest-parser registry seam is a real design
  decision (D6).
- **Phase 3**: `|=` behavioral guards (the MVP ladder: structural shapes → condition
  expressions → drive-then-match ⇓-modalities; the OSLF/HML surface stays research, cited as
  destination); the two-languages-one-RSpace co-install spike (the one unvalidated inter-FLT
  prerequisite — D7); the graft beat when E-1 lands.

## Proof points (cite when asked "is that proven?")

| Claim | Backing |
|---|---|
| ABI shape + unforgeable tags | `rho_net_subst_trs.rs:15-33`; `rho_net_lower.rs` reflect_tag/reflected_tag_string; matcher identity compare |
| The match binds only the hole; ground rest exact | the spatial matcher's EList element-wise + FreeVar contract |
| Failed guard/match commits nothing; datum rests | `GuardedCommSoundness.v` + `RhoGuardedCommSoundness.v` (`comm_fires_iff`, `rho_complement_no_commit`); the 4-test guard oracle |
| Guards emit no COMM (INV-14) | `WholeGsltInRhoOpCorrespondence.v` `semantic_predicates_emit_no_comm` |
| The capstone correspondence incl. iterated driving | `whole_gslt_in_rho_opcorrespondence` + `…_iterated` |
| In-Rho β/subst correctness | `DeBruijnSubstTRS.v` (SN+CR+NF), `InRhoBetaCascadeWeakBisim.v`, `InRhoQuiescenceDriver.v` |
| Lambda → NF, zero Dovetail work; the K golden | `zero_dstage_exec.rs`; `rho_net_lambda_firing.rs` |
| Fuel exhaustion typed, fail-closed | the Ω test |
| Set-automaton substrate + size optimality | doc 21 §7.3; `TcChannelNamingQuotient.v`, `SymbolOnceInjective.v`; `set_automaton_size_optimal.rs` |
| Scion seam present, unconstructed; Lambda Δ=0 | `rho_net_drive.rs` FiringEmission; experiment 147 |

## f1r3Rho

Greenfield, docs-first (2 commits; roadmap/user stories; implementation language uncommitted).
Nothing to reuse for this demo; not a prerequisite; do not couple. Its role is productization:
the natural home for the raw-Rholang FLT host grammar once a standalone interpreter exists —
this demo + the FIP are the design input it should receive; if phase-2 sugar lands in RhoCalc
first, f1r3Rho adopts the settled surface rather than pioneering it.

## Decisions for Dylon (recommendations inline)

- **D1 vehicle**: `repl/src/bin/flt_demo.rs` (recommended — SurfaceRenderer de-reflection) vs a
  rholang-runtime bin.
- **D2 Beat-2 guard form**: `EEq` condition pending validation (recommended) vs pre-committing
  to the ground-subpattern fallback.
- **D3**: open with the stock-RhoCalc strawman cameo — yes (recommended; sets up Beat 3)/no.
- **D4**: show FIP surface on slides with the flux banner (recommended); narrate holes as
  `${f}` while the terminal shows `f` (recommended).
- **D5 name**: "The Foreign Exchange" (proposed; pairs with "The Guarded Settlement Desk").
- **D6 phase-2 home**: RhoCalc `PFlt` literal (recommended) vs REPL affordance vs waiting for
  f1r3Rho — plus the guest-parser registry-seam design.
- **D7**: authorize the two-languages-one-RSpace co-install spike (phase 3's one real risk).

## Logistics

Each beat is a fresh one-liner run — skippable, no state damage. Build + validate in the next
window that does not collide with the EPathMap E-6d measurements (everything here is
demo-local; the only f1r3node interaction is read-only linking already exercised by tests).
Record during validation (tmux + asciinema, `script` backup) so the recording IS the validated
run. If the window slips, Beats 0/1/4 narrate from committed test-pinned facts.
