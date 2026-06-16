# Documentation Enhancement Plan — Dovetail & Rho-Native Integration

Status: in progress. This is the working plan for bringing both architecture-doc suites
(`docs/architecture/dovetail/`, `docs/architecture/rho-native-integration/`) to a pedagogical,
diagram-rich, citation-verified standard. Derived from a full code-grounded survey (2026-06-16).

## Progress log

- **Phase 1 — DONE** (commit `a6032991`). Fixed `04-rules-and-saturation` (real
  `RewriteRule {lhs,rhs,label}`, the `AcApp` third `Pattern` variant, AcApp match
  arm, "Guards Are Discharged Upstream", new AC-matching section), `01-concepts-and-glossary`
  (guard entry + AC/binder/disposition terms + symbols), `03-data-model-and-exact-keys`
  (three e-graph keys + FIX-A α-canonical key). All citations/test/lemma names verified.
- **Phase 2 — DONE** (commit `a6032991`). New `11-binder-congruence-handler.md`
  (full pedagogical treatment; DOIs verified; grounded in `binder_congruence.rs` +
  `AmbientBinderHandler.v`). Registered in README index + `references.md`.
- **E-graph diagrams (the user's specific request) — 4 of 5 DONE** (commit `a6032991`):
  `03-egraph-term-dag` (saturation+congruence), `04-egraph-ac-openrule` (AC),
  `06-egraph-cyclic-closure` (Newton-SCC vs cycle-cut), `11-capture-safety` (binder).
  All render + well-formed + embedded. The 5th (base hashconsing) is subsumed by 03.
- **Phase 3 — DONE** (commit `029a93b9`). De-staled `00-executive-brief` (installed
  production backend, not inert M-E.0), `02-engine-architecture` ("Inert Milestone"
  → "Installation Status"), `10-runtime-facing-reports` (AC parallel-bag carve-out),
  `ambient-binder/README` (status banner → COMPLETE).
- **Phase 4 — DONE** (commit `029a93b9`). Rho suite `07-verification-and-rollout`
  retitled from "Current Verified Base: M-RHO.0" to "advanced through the P-series",
  plus a NEW per-language flip-status table. Rholang-code already present (doc 04).
- **Phase 5 — DONE** (commit `1dffd8f3`). `02-engine-lifecycle` redrawn with owner
  swimlanes; NEW `11-binder-float-ac-swimlane`, `04-disposition-decision-tree`,
  `05-extraction-sequence`. PlantUML deprecated-prefix + math-symbol fixes.
- **ALL FIVE PHASES COMPLETE.** Both suite `validate.sh` pass; 7 new figures + the
  lifecycle redraw. Optional future: richer README component actors; an end-to-end
  `MeTTaIL→Dovetail→Rho` actor sequence in the rho suite.

## The headline gap
The **Ambient binder NativeHandler (Inc 0–4), FIX-A alpha-canonical keys, the in-engine AC matcher,
and the float→AC composition** are fully implemented (`macros/src/gen/runtime/binder_congruence.rs`,
`macros/src/gen/runtime/dovetail_report.rs`, `dovetail/src/rules.rs` `AcApp`,
`dovetail/formal/rocq/theories/Lowering/AmbientBinderHandler.v`) but documented **nowhere** in the
26 published docs. Several docs are stale (see below).

## Load-bearing staleness to FIX (Phase 1)
1. **Ambient "fails closed" is now FLIPPED** — `dovetail_report.rs` floats `new`s then AC-reduces.
2. **`Pattern`/`RewriteRule` shapes are WRONG** in `01`/`04`: the real `Pattern` has a third variant
   `AcApp { op, fixed, rest }`; the real `RewriteRule` is `{ lhs, rhs, label }` — there is NO
   `guard`/`evidence` field, and the "guarded instantiation" pseudocode describes machinery that does
   not exist in `dovetail/src/rules.rs` (guards live UPSTREAM in `mettail-rho-codegen`).
3. **"M-E.0 inert / no caller"** framing is stale — the engine is installed as a runtime backend and
   P5b is actively flipping languages.

## Diagram plan — best type per concept (apply consistent per-concept color legend)
Color legend: inputs `#DBEAFE`; exact keys `#BBF7D0`; saturation `#DCFCE7`; automaton/weights `#FEF3C7`;
extraction `#FBCFE8`; report `#EDE9FE`; boundary `#FEE2E2`/`#FFEDD5`; host/RSpace `#FCE7F3`+`#CFFAFE`;
binder/freshness `#FAE8FF` (lilac).

| Concept | Best diagram | Why |
|---|---|---|
| Engine lifecycle | swimlane UML activity (lanes = Caller/egraph/wta/extract/report) | shows WHO owns each phase (existing is actorless) |
| e-graph + hashconsing + congruence | term-DAG / e-graph drawing (Graphviz) | a box diagram can't show class-merge / shared children |
| Equality saturation | UML activity w/ back-edge + `Fᵢ₊₁ = Fᵢ ∪ Δᵢ₊₁` | fixpoint loop w/ 3 terminal exits |
| WTA + complete best-first extraction | sequence (Extractor ↔ ClassState ↔ child) | the recursion into child classes is the no-miss heart |
| Cyclic closure / Newton-SCC | Graphviz SCC condensation + state machine | separates exact-inside-weight from enumeration-impossibility |
| Exact-key dedup | decision flowchart | the insert-by-exact-key decision |
| Runtime-report boundary | C4 component + sequence overlay | the projection seam + direct/Rho split |
| End-to-end `MeTTaIL→Dovetail→Rho` | actor-rich sequence (KEEP rho 02) | temporal handoff across actors |
| Dataflow lowering to Rholang | Kahn process-network dataflow | facts-as-messages, rules-as-contracts |
| RSpace COMM / scheduling | state machine + `par` sequence fragment | produce/match/commit cycle + true concurrency |
| Disposition decision rule | UML activity / decision tree | `ambiguous ∧ host-less` is a literal decision |
| **Ambient binder `float→AC`** | **swimlane activity (NativeHandler ‖ AC) w/ bounded loop** | the headline missing diagram |
| **Capture-safety** | **term-DAG before/after** (witness `new(z,in(z,new(x,0)))`) | makes T1/T1' visual |
| OSLF / guard-quality seam | C4 component fan-out | classification fan-out |

REDRAW with actors/lanes: `02-engine-lifecycle.puml`, `05-extraction-frontier.puml`, `README.puml`.
KEEP: `07-verification-dag.dot`, `08-production-readiness-dag.dot`, `05-rspace-parallel-scheduling.puml`,
`rho 02-end-to-end-architecture.puml`.

## Citation + DOI list (verified 2026-06-16)
| Key | Citation | DOI / URL |
|---|---|---|
| EGG-2021 | Willsey et al., "egg: Fast and Extensible Equality Saturation," PACMPL 5(POPL), 2021 | `10.1145/3434304` |
| TATA | Comon et al., *Tree Automata Techniques and Applications*, 2007 | `https://inria.hal.science/hal-03367725` |
| MOHRI-WFST | Mohri, Pereira, Riley, "Weighted FSTs in Speech Recognition," CSL 16(1), 2002 | `10.1006/csla.2001.0184` |
| HUANG-CHIANG-2005 | Huang & Chiang, "Better k-best Parsing," IWPT 2005 | `https://aclanthology.org/W05-1506/` (no DOI) |
| DEBRUIJN-1972 | de Bruijn, "Lambda calculus notation with nameless dummies," Indag. Math. 34, 1972 | `10.1016/1385-7258(72)90034-0` |
| PITTS-2003 | Pitts, "Nominal Logic," Inf. & Comput. 186(2), 2003 | `10.1016/S0890-5401(03)00138-X` |
| AC-MATCH-BKN | Benanav, Kapur, Narendran, "Complexity of matching problems," JSC 3, 1987 | `10.1016/S0747-7171(87)80027-5` |
| OSLF-2016 | Stay & Meredith, "Logic as a Distributive Law," 2016 | `https://arxiv.org/abs/1610.02247` |
| RHO-2005 | Meredith & Radestock, "A Reflective Higher-Order Calculus," ENTCS, 2005 | `10.1016/j.entcs.2005.05.016` |
| ESPARZA-KL-2010 | Esparza, Kiefer, Luttenberger, "Computing the LFP of Positive Polynomial Systems," 2010 | `https://arxiv.org/abs/1001.0340` |

## Execution ordering
- **Phase 1** (fix inaccuracies): `01-concepts-and-glossary`, `04-rules-and-saturation`, `03-data-model-and-exact-keys`.
- **Phase 2** (NEW binder work): `11-binder-congruence-handler` (this doc set's biggest gap), `09-worked-example`, `07-formal-verification-and-tests`.
- **Phase 3** (de-stale framing): `00-executive-brief`, `02-engine-architecture`, `00-requirements-traceability`, `README`.
- **Phase 4** (Rho suite): `rho 03-dovetail-rewrite-semantics`, `rho references`, `rho 01`/`00`, `rho 07`/`08`, `runtime-backend-spine`.
- **Phase 5** (diagrams): the 5 new headline figures + the actor/lane redraws; render `.puml`/`.dot`→`.svg`; run both `validate.sh`.
