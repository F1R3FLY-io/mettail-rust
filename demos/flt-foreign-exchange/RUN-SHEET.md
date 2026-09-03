# The Foreign Exchange — Lambda FLTs shipped, matched, and executed over RSpace

The debut demonstration of Rholang↔MeTTaIL Foreign Language Terms: a foreign term built by one
process, shipped over the tuplespace, destructured by a pattern with a typed hole, guard-vetoed
fail-closed, rebuilt from its captured holes, and executed to β-normal form — every step a
committed COMM on F1r3node's RSpace. Companion piece to `../rholang-settlement/` ("same machine,
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

---

## ★ What is committed today — added 2026-07-28

⚠ **This page's load-bearing premise has expired in the good direction.** It opens by saying the
runtime ingredients exist and "**only the surface syntax is missing**". The surface syntax has
since landed: `` lambda:Term`…` `` openers with `${x}` typed-AST holes, in both construction and
pattern position, and the interpreter binary — not a demo-local `flt_demo` bin — runs `.rho`
files directly. The beats below are still the design, and their `(to validate)` markers still
mean what they say at the **ABI** level. What follows is what a presenter can run *today*, in the
landed surface notation, measured.

Both files run through the same binary and setup line as the sibling desks:

```
cargo build -p rholang-runtime --bin rholang --features "rholang-runtime lambda-runtime calculator-runtime"
```

### `foreign-exchange.rho` — Beat 1's claim, in surface syntax

An FLT built by one process, shipped over a channel **the program mints** (`new flt in { … }`, so
no string in the source can name it), destructured by a pattern carrying **two** typed holes, and
rebuilt from the captured holes:

```
$ target/debug/rholang demos/flt-foreign-exchange/foreign-exchange.rho
```
```
mode: process → running to rest on the f1r3node reducer (observing @"OUT")
  @"OUT" observations (1):
    [0] ⟦(λ.0 λ.λ.1)⟧
```

`⟦(λ.0 λ.λ.1)⟧` is `(I, K)` in de Bruijn form: `λ.0` is `lam x. x` and `λ.λ.1` is
`lam a. lam b. a`. Both holes bound, both re-quoted, and the application rebuilt — this is
Beat 1's destructure plus Beat 4's construction-position fill, without the hand-built `Par`s.

### `k-combinator.rho` — Beat 4's claim, in surface syntax

`K I K` driven to β-normal form by the in-Rho quiescence driver, with the machine's own receipt:

```
$ target/debug/rholang demos/flt-foreign-exchange/k-combinator.rho
```
```
mode: term → reducing to normal form on the f1r3node reducer
  normal form on @"OUT" (1):
    [0] ⟦λ.0⟧
  ^fired ledger: ["Beta", "Beta"]   (2 in-Rho rewrite firing(s))
  ^drive-err: 0 datum(a) · ^drive-fuel: 0 datum(a)   (both empty ⟹ terminated by quiescence)
```

$`K\,I\,K \to (\lambda b.\,I)\,K \to I`$ — two $`\beta`$ steps, and the `^fired` ledger says
exactly two. The ledger is the answer to "did the *machine* do this?": a host-side reduction
would leave it empty. `^drive-err: 0 · ^drive-fuel: 0` says it stopped at a normal form rather
than at a budget.

> Measured 2026-07-28 against a binary built before that day's twenty-one defect fixes and one
> built after; both transcripts byte-identical modulo the binary's own name line. Neither file
> contains arithmetic, so the day's operator-precedence overhaul cannot reach them.

⚠ **Neither file is CI-gated.** `flt-church-desk`, `flt-assay-desk`, `flt-lookahead` and
`rholang-query-bind` each have a gate driving their run sheet's own command lines; this directory
has none, so the two transcripts above are pinned by this page alone and can rot. That is the gap
to close before this demo is presented from this page rather than from the sibling desks.

**Notation** (display only): `⌜X⌝` = the unforgeable GPrivate tag for label X
(`mettail.term.{fp}.X` — deterministic per language fingerprint, unforgeable *from within the
tuplespace surface*: no syntax can spell a GPrivate and the matcher compares them by identity);
`⟦t⟧` = the reflected Par of term t. **Groundness marker** (E-2-D, reflected-ABI v2 — landed
`d89e7421`): every *marked-object* reflected node — a user constructor like `App`, or a
binder/variable leaf `⌜^lambda⌝`/`⌜^bound⌝`/`⌜^free⌝` — carries a groundness marker at **index 1**,
immediately after the head tag: the layout `[⌜C⌝, ⌜mk⌝, ⟦t₀⟧, ⟦t₁⟧, …]`, where the marker `mk` is
either `⌜^gnd⌝` (ground) or `⌜^nog⌝` (not-ground).
The marker is `⌜^gnd⌝` iff the subtree is hereditarily `⌜^bound⌝`-free — equivalently, subst/shift is
the identity on it (`InRhoCreeperTrace.oground`); otherwise `⌜^nog⌝`. It is computed bottom-up in
one pass (`reflect_ground_term_marked`, `rho_net_lower.rs:2767`); machinery nodes (Peano `Z`/`S`,
`^subst`/`^shift`, the marker tokens themselves) carry none. Two demo-facing rules follow: **patterns
wildcard the marker slot** (`_` at index 1 — the paired match is over head + args, never the marker);
**constructions must emit `⌜^nog⌝` over any hole** (a hole may later be filled by a binder-carrying
term, so a hard-coded `⌜^gnd⌝` there would wrongly short-circuit subst — the semantic Beat-4/5 fix).
Because `id`, `K`, and `App(id, K)` are closed λ-terms (each hereditarily contains a bound variable),
their top marker is `⌜^nog⌝`. Demo constants: `id = lam x. x`;
`K = lam a. lam b. a` (the committed golden); subject `App(id, K)`; `Ω` (fuel witness).
**Hole convention (the honest bridge to `${x}`)**: a free variable in the guest pattern source
is a hole — parsed by the real Lambda parser, its `^free` leaf transformed to a match
FreeVar. Narrate: "`f` here is what the refined syntax spells `${f}` — same AST position,
different ink."

---

## Beat 0 — The wire format existed before the syntax (1 min, no run)

Print `id`, `K`, their reflected tagged-EList forms, and the literal tag string. Annotate the
structure to show the E-2-D marker slot: each marked-object node prints as `[⌜C⌝, ⌜mk⌝, args…]` —
head tag at index 0, groundness marker `mk` at index 1, reflected children from index 2. So
`⟦App(id, K)⟧ = [⌜App⌝, ⌜^nog⌝, ⟦id⟧, ⟦K⟧]` and `⟦id⟧ = [⌜^lambda⌝, ⌜^nog⌝, ⟦x⟧]` (both `⌜^nog⌝` at
index 1 — a closed λ hereditarily carries a bound variable). Point at the marker slot now: it is what
every pattern below wildcards (`_`) and every re-quote must re-emit (`⌜^nog⌝`).

> "Every MeTTaIL language already ships with a canonical machine representation of its terms —
> a tagged list whose head is an unforgeable name minted per language. That IS the
> foreign-language-term wire format. Tonight we use it as one."

## Beat 1 — Ship a Lambda FLT; destructure it with a typed hole (3 min — THE CORE)

Program: `@"fltX"!(⟦App(id, K)⟧) | for( @[⌜App⌝, _, ${f}, ⟦K⟧] <- @"fltX" ){ @"OUT"!(f) }`
— the `_` at index 1 wildcards the E-2-D groundness marker; the hole `${f}` at the function
position; a GROUND `⟦K⟧` subpattern at the argument position (exact structural match including tags —
and `⟦K⟧`, itself a marked node, carries its own `⌜^nog⌝` marker, so the ground compare stays
byte-exact).

Expected **(to validate)**: `OUT: [⟦id⟧]`, de-reflected `lam x. x` (α-fresh binder).
Negative 1b: send `⟦K⟧` alone (not an App) — zero COMMs, `OUT` empty, the datum RESTS on
`fltX` (the guard-oracle discipline).

> "A process built a term of a different language, sent it over the tuplespace, and a
> for-comprehension took it apart by shape. The variable is a typed hole: it can only bind the
> subtree at that grammar position. And matching is fail-closed: a wrong-shaped term just sits
> on the book."

## Beat 2 — The guard vetoes on a foreign subterm — honestly (2 min)

PRIMARY form (D2, the marker-wildcarded ground subpattern — LOAD-BEARING, not a hedge; see the
guard-note below):
`for( @[⌜App⌝, _, ${f}, ⟦K⟧] <- @"fltX" ){ @"OUT"!(f) }` — two structurally-valid Apps are
discriminated by the argument subterm alone.

- Send `⟦App(id, id)⟧`: the argument `⟦id⟧` fails the ground subpattern `⟦K⟧` → expected
  **(to validate)** `OUT: []`, datum resting — veto, zero partial effects.
- Send `⟦App(id, K)⟧`: the argument matches → expected **(to validate)** `OUT: [⟦id⟧]`.

> "The refined syntax spells this `where a == ⟦K⟧` — a semantic predicate over a foreign AST, not
> text; it runs inside the machine's matcher before the COMM commits, and a false guard consumes
> nothing and emits nothing. Same theorem-backed physics as the Settlement Desk. Here we realize
> that veto through the marker-wildcarded pattern shape, which is the *sound* v1 form."

**Guard-note — why D2 is primary, not a fallback (red-team NEW-2).** The real `where a == ⟦K⟧`
`EEq` guard is **marker-sensitive**: `EEq` over reflected Pars is a whole-value compare — it also
compares the index-1 groundness-marker byte. Beat 1's marker wildcard protects *patterns*, not an
`EEq` condition, so `a == ⟦K⟧` would be sound only if `⟦K⟧`'s markers were byte-identical to the
captured subterm's. The ground subpattern rides the marker-wildcarded *pattern* and is therefore
robust ⇒ the general `where φ` surface (with a marker-canonical guard-RHS) is deferred to the
guard-lowering work (phase-2/3). The observable veto — fail-closed, zero partial effects — is
identical either way, and is the same theorem-backed guard physics (`GuardedCommSoundness.v`).

## Beat 3 — The counterfeit is rejected: tags are unforgeable (1.5 min)

Send the string-tagged fake `["App", ⌜^nog⌝, ⟦id⟧, ⟦K⟧]` — a GString `"App"` head, but
otherwise byte-identical to `⟦App(id,K)⟧`: it matches the marked pattern's 4-element arity, its
wildcarded marker slot, and the ground `⟦K⟧` — at the same receive.
Expected **(to validate)**: no match; the datum rests. The mismatch is isolated to the head
tag — `⌜App⌝` is an unforgeable `GPrivate` compared by identity, and the GString `"App"` is a
different value; nothing else differs, so the rejection is a *pure* unforgeable-tag failure,
not an incidental arity mismatch.

> "This is why FLTs are not string interpolation. A term claiming to be Lambda by *name*
> doesn't match — the language tag is an unforgeable private name compared by identity, not
> spelling. You cannot conjure a foreign term out of strings. That is the runtime face of the
> FIP's No-Injection property."

## Beat 4 — Fill the holes and RUN it: quotation to β-normal form (3 min — THE WOW)

Program: `@"fltX"!(⟦App(id, K)⟧) | for( @[⌜App⌝, _, ${f}, ${k}] <- @"fltX" ){
⌜^drive⌝!( [⌜App⌝, ⌜^nog⌝, f, k], fuel, "OUT" ) }` — the pattern wildcards the marker slot (`_` at
index 1) and captures the two holes; the continuation RE-QUOTES the term from those holes
(construction-position fill, machine-side) with the marker slot forced to `⌜^nog⌝`, then seeds the
installed quiescence driver.

**The `⌜^nog⌝` in the re-quote is SEMANTIC, not cosmetic** (the E-2-D correctness fix). Two ways a
naive re-quote fails to β-fire: (1) a **3-element** re-quote `[⌜App⌝, f, k]` omits the index-1
marker slot, so it does not match the driver's App redex arm (`pat_tagged`, which expects the v2
marked layout `[tag, marker, args…]`) — the COMM never fires; (2) a re-quote that hard-codes
`⌜^gnd⌝` over the holes lets the hereditary-ground guard short-circuit subst to the identity, so β
silently will not fire on a binder-carrying fill. Forcing `⌜^nog⌝` over any hole is both necessary
and conservatively sound (a fill only ever makes a node *less* ground — `InRhoCreeperTrace.oground`).

Expected **(to validate)**: `OUT: [⟦K⟧]` de-reflected `lam a. lam b. a`; the `^fired` ledger
`["Beta"]`; `^drive-err`/`^drive-fuel` empty (the always-on cross-check).

> "One visible communication — the foreign term changing hands — then a cascade of τ-steps: the
> driver matching, β firing through the substitution calculus, the contractum re-driving. The
> evaluator for the guest language is itself a set of processes in the same tuplespace. Nothing
> here is my laptop interpreting Lambda; it's all committed COMMs on real RSpace."

**Beat 4b — DEFERRED (later / after the primary demo is complete, per decision 1).** The live trace
(`StepSession` + the τ-classifier): step 1 is the USER-level FLT rendezvous COMM on `fltX`; every
subsequent step classifies `[τ drive]`/`[τ subst]`; terminal `[Rho output] OUT observes ⟦K⟧`. This
is a *secondary* demo — built only once the primary beats (0 / 1 / 2-D2 / 3 / 4 / 5-positive) are
green and validated; until then Beat 4 presents from its pinned `OUT` / `^fired` facts.

## Beat 5 — The behavioral predicate, honestly; the NF re-shipped (2.5 min — IN the primary demo)

Producer `@"fltX"!(⟦App(id,K)⟧)`; consumer 1 `for(@${t} <- @"fltX"){ ⌜^drive⌝!(t, fuel, "nf") }`;
consumer 2 `for( @[⌜^lambda⌝, _, ${b}] <- @"nf" ){ @"OUT"!([⌜^lambda⌝, ⌜^nog⌝, b]) }` — consumer 2
wildcards the marker slot (`_`) in its `^lambda` pattern and re-emits `⌜^nog⌝` in the rebuild (same
E-2-D physics as Beat 4: a 3-element `[⌜^lambda⌝, b]` neither matches the marked `^lambda` layout nor
re-ships as a well-formed reflected λ).

Expected **(to validate)**: `OUT: [⟦K⟧]`. Negative: producer sends `⟦Ω⟧` — the typed
`^drive-fuel` exhaustion datum; `nf` empty; consumer 2 never fires; `OUT: []`.

All ingredients for this same-language inter-FLT re-ship have landed, so Beat 5 is **in the primary
demo**. Honest scope: this is a *same-language*, same-binder-depth re-wrap (an identity re-ship); the
hard *cross-language*, cross-context binder hole is the phase-3 co-install spike (D7), not this beat.

> "The prototype note asked for `where bar |= <behavioral predicate>`. Here is its first honest
> form: 'bar drives to a λ-value' — a diamond-modality check realized as drive-then-match. The
> formula language this grows into is the OSLF-generated Hennessy–Milner logic — the Knotted
> Topoi keystone says that logic is the internal logic of the model. And the second consumer:
> a normal form produced by one FLT interaction was re-shipped and pattern-matched by another.
> That is inter-FLT communication — the runtime mandate's second reason, live."

Total ~13–14 min for the primary demo (Beats 0 / 1 / 2-D2 / 3 / 4 / 5-positive). **Secondary /
deferred (later, after the primary demo is complete — decision 1):** the live-trace Beat 4b, and the
optional openers (the stock-Rholang "stringly-typed strawman" cameo that Beat 3 then kills; the
Settlement Desk Beat-2 bridge).

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
   provably size-optimal" (doc 21 §7.3 + the size pins). **The gap for FLT matching**: that set
   automaton interns a *FIXED* rule set at CODEGEN. Routing FLT destructuring through it (item 5)
   needs **runtime pattern interning** — interning a consumer's receive-patterns into the automaton
   at run time — a real, scheduled extension (phase-3), not a property the codegen automaton has.
4. THE DEEP RHYME (the phase-3 closing beat): **holes are buds; the quotation is the scion;
   filling a bud with an already-analyzed FLT is a graft** — two pre-explored configurations
   composed with zero re-scanning; scions grafted into scions' buds = the inter-FLT pipeline's
   formal backbone (soundness anchor: graft ⊑ completed = `InRhoScionGraft.v` L3.3
   `sdrives_included_in_gdrives`). Honest caveat: today the spatial matcher re-scans per match —
   the bud/scion ECONOMY becomes real when graft machinery extends from the driver's firing seam
   to the FLT matching layer: consumers holding CONFIGURATIONS, so a re-shipped hole-filled FLT
   costs only its genuinely-new material — novel beyond the thesis (grafting at the communication
   layer). With a STRUCTURAL guest (an Ambient FLT — In carries s=5 known constructors; locked
   prediction Δ=3 DriveTau/firing), grafting becomes measurably visible.
5. Timing (**corrected 2026-07-22 — the dependency is MET**). E-1's scion/graft has **landed**:
   `InRhoScionGraft.v` (L3.1–L3.7, zero-admission, `Print Assumptions`-clean) proves the seam
   sound, and it ships **dormant** — production always lowers under `ScionPolicy::AllRedrive`
   (`arm.scion == false`), byte-identical to pre-E-1 (`rho_net_drive.rs`; the a_s5_6 / a_s5_8
   pins). So the graft beat's **dependency is satisfied** — it is *not* "queued behind the EPathMap
   fix." What remains is a **new matching-layer mechanism**: route FLT destructuring through the set
   automaton with **runtime pattern interning** (item 3), *reusing* E-1's zero-admission proof kit
   (`graft ⊑ completed`). That mechanism — not E-1 itself — is the phase-3 deliverable. The
   phase-now demo runs WITHOUT scions; the graft beat drops in when the runtime-interning matching
   layer lands.

Thread-line: "The set automaton compiled this language into the machine; the spatial matcher
destructures the foreign term; and the same theory's grafting chapter — its soundness kit already
landed and dormant — is how filled FLT holes will re-enter matching incrementally once a
runtime-pattern-interning matching layer is built (phase-3). Today's demo needs none of that to run."

## Phases

- **Phase now (this sheet)**: the primary ABI demo bin (Beats 0 / 1 / 2-D2 / 3 / 4 / 5-positive,
  all marker-fixed to the E-2-D v2 layout) + the pinning-test twin. Deferred to *after* the primary
  is complete (decision 1): the live-trace Beat 4b and the secondary openers. Dependencies all met
  (the flip, the driver, de-reflection, and the E-2-D marker `d89e7421`). ~1 build-window day to
  green beats; a second for validation + recording. No production crate touched.
- **Phase 2**: the smallest honest syntax — a Rholang `PFlt` literal (the fixed-length backtick
  fence + inline backtick + reserved-tag `{`/`[` the demo needs — decision 3; `${x}` / `${x:Cat}`
  holes; construction + pattern positions) lowered through the guest parser + the reflected ABI;
  NOT a REPL text pre-pass (textual splice is the exact insecure path No-Injection rejects). Plus
  the **public reflector API** the phase-now demo hand-builds today — **P1** the `^free`→FreeVar
  *pattern* reflector (builds the receive-pattern, wildcards marked slots, maps non-linear holes to
  distinct FreeVars + a consistency guard), **P2** the construction-fill reflector (marker forced
  `⌜^nog⌝`), **P3** expose `ground_marker_tag_par` / `par_carries_ground_marker` (`pub`), **P4** the
  runtime-Peano de-Bruijn binder reflectors — and the guest-parser registry seam (a real design
  decision, D6). Tag REQUIRED; untagged inference is a later, budgeted feature (decision 4).
- **Phase 3**: the two-languages-one-RSpace co-install (D7 — sequenced after phase-now + phase-2,
  but planned + implemented PRINCIPLED, decision 5): **R2** per-child fingerprint-dispatch in the
  driver's congruence arm (an interior foreign subterm re-dispatches to its OWN fp driver — R1
  passthrough was refuted); the `^subst` / `^shift` **foreign-inert traversal** (a foreign child
  reads `⌜^nog⌝` for the host fp ⇒ the ground guard never short-circuits ⇒ subst / shift descend
  into it and SILENTLY STALL today, so binder-crossing needs a foreign-inert arm); **AC-carrier
  fp-keying** (`ac:{constructor}` → `ac:{fp}.{op}` — the one non-fp-keyed name,
  `rho_net_lower.rs:2819`); a **co-install harness**; and the cross-language op-correspondence
  corollary (separation lemma + Toyama modularity — confluence IS modular, [JACM 34(1):128–143,
  1987, doi:10.1145/7531.7534](https://doi.org/10.1145/7531.7534); termination is NOT modular,
  [IPL 25(3):141–143, 1987, doi:10.1016/0020-0190(87)90122-0](https://doi.org/10.1016/0020-0190(87)90122-0)
  ⇒ a cross-language fuel budget). **Set-automaton FLT matching + the graft economy** (§*Where the
  set automaton…* item 5): runtime pattern interning reusing E-1's `graft ⊑ completed`. And the
  `|=` behavioral guards (the MVP ladder: structural shapes → condition expressions →
  drive-then-match ⇓-modalities; the OSLF/HML surface stays research, cited as destination). The
  virtual-host bridge splits to a **sibling FIPS** (decision 2).

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
| Scion/graft seam landed + dormant; production `AllRedrive` byte-identical; Lambda Δ=0 | `InRhoScionGraft.v` L3.1–L3.7 (`Print Assumptions`-clean); `rho_net_drive.rs` `ScionPolicy::AllRedrive`; experiment 147 |

## f1r3Rho

Greenfield, docs-first (2 commits; roadmap/user stories; implementation language uncommitted).
Nothing to reuse for this demo; not a prerequisite; do not couple. Its role is productization:
the natural home for the raw-Rholang FLT host grammar once a standalone interpreter exists —
this demo + the FIP are the design input it should receive; if phase-2 sugar lands in Rholang
first, f1r3Rho adopts the settled surface rather than pioneering it.

## Decisions for Dylon (recommendations inline)

- **D1 vehicle**: `repl/src/bin/flt_demo.rs` (recommended — SurfaceRenderer de-reflection) vs a
  rholang-runtime bin.
- **D2 Beat-2 guard form** — **RESOLVED** (decision 1 + red-team NEW-2): the ground-subpattern form
  is PRIMARY (marker-wildcarded pattern; robust and LOAD-BEARING). The `EEq where a == ⟦K⟧` guard is
  marker-sensitive — a whole-value compare that includes the index-1 marker byte — so the general
  `where φ` surface (with a marker-canonical guard-RHS) is deferred to guard-lowering (phase-2/3).
- **D3** — **DEFERRED** (decision 1): the stock-Rholang strawman cameo is a *secondary* opener,
  built after the primary demo is complete (it still sets up Beat 3 when it lands).
- **D4**: show FIP surface on slides with the flux banner (recommended); narrate holes as
  `${f}` while the terminal shows `f` (recommended).
- **D5 name**: "The Foreign Exchange" (proposed; pairs with "The Guarded Settlement Desk").
- **D6 phase-2 home**: Rholang `PFlt` literal (recommended) vs REPL affordance vs waiting for
  f1r3Rho — plus the guest-parser registry-seam design.
- **D7** — **AUTHORIZED** (decision 5): the two-languages-one-RSpace co-install, sequenced after
  phase-now + phase-2 and implemented PRINCIPLED — R2 per-child fingerprint-dispatch, the
  `^subst` / `^shift` foreign-inert traversal, AC-carrier fp-keying (`ac:{constructor}` →
  `ac:{fp}.{op}`), a co-install harness, and the cross-language op-correspondence corollary
  (separation lemma + Toyama modularity).

## Logistics

Each beat is a fresh one-liner run — skippable, no state damage. Build + validate in the next
window that does not collide with the EPathMap E-6d measurements (everything here is
demo-local; the only f1r3node interaction is read-only linking already exercised by tests).
Record during validation (tmux + asciinema, `script` backup) so the recording IS the validated
run. If the window slips, Beats 0/1/4 narrate from committed test-pinned facts.
