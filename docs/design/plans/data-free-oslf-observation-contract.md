# Data-free observation of authored GSLT rewrite relations

Status: implementation contract. The primary Regex theory and application now
use the authored relation/query path without an `oslf` `Data` record. A
separately named v1 action-compatibility fixture retains that record for
regression tests. Node application acceptance and registry-backed retrieval
remain separate verification obligations. This design adds no Theory or Module
syntax.

## Vocabulary and existing boundary

A **GSLT** (graph-structured lambda theory) declares typed terms, equations,
and directed rewrites. A **relation normal form** is a term for which exhaustive
matching finds no further rewrite successor. A **terminal result** is a normal
form that the theory additionally admits as an answer to a query. A **receipt**
records the installed image identity, exact input/output keys, complete rewrite
hops, and charged work. An **installed handle** is the opaque authority for one
versioned language image; a fingerprint or a name alone is not authority.

The existing [normalization model](../../../formal/rocq/runtime_grammar/theories/SemanticNormalization.v)
requires an explicit terminal policy and rejects `StuckNonterminal`. The
[semantic kernel](../../../dovetail-runtime/src/semantic_transition_kernel.rs)
already has an actionless, fair, exact-keyed rewrite-relation execution path.
The [FLT semantic service](../../../rholang-runtime/src/semantic_service.rs)
uses that path for native Boolean predicates and uses the same installed
projection matcher for guest-to-host Boolean results. Its v1 wire selects a
named action/observation and returns an action receipt; its distinct v2 wire
selects the authored relation/query and retains the full proof roster.

The v1 compatibility record repeats six entry-rule names and four
terminal-constructor sets. It also labels those actions `Pure` and grants
`Reduce`. The primary Regex entry terms and directed rules are declared in
`Terms` and `Rewrites`. No source-defined host callback is permitted by the
closed intrinsic ABI. The six former operation names were aliases, not
additional guest reduction rules.

## Why a terminal policy cannot simply be inferred

Consider one fixed syntax and rewrite relation with an irreducible term `x`.
One observation policy accepts `x` and another rejects it. The two GSLTs have
identical `Terms`, `Equations`, and `Rewrites`, yet their public observation
results differ. Therefore a function of only those three fields cannot recover
both policies. Equating “no successor” with “successful answer” would accept
stuck internal states and break the existing action semantics.

The missing decision is an *observation query*, not another language-definition
action table. The query selects the exact result category, one typed terminal
judgment constructor, and one named guest-to-host Boolean projection. The
judgment and its reduction rules are ordinary `Terms` and `Rewrites`; no
mandatory `Data`, `Actions`, `Observations`, or `Exports` entries are added.
For Regex, four unary judgments distinguish the former `DoneBool`,
`DonePattern`, `DoneMatch`, and `DoneText` terminal sets. They all return a
separate guest `TerminalQuery` category, whose `TerminalYes` and optional
`TerminalNo` terms project through one `TerminalVerdict` relation to host
Boolean values. `FullMatch` and `Nullable` select the same Boolean judgment;
both replacement operations select the same text judgment.

The separate query category is necessary, not cosmetic. The existing
`CompletedBoolean : Computation ~> host::Bool` projects the *value* of
`DoneBool` for where-guards. The current where selector rejects more than one
matching Boolean projection for a guest category. Putting terminal projections
on `Computation` would make that selector ambiguous and could conflate
“the answer is false” with “this is not a terminal answer.” A
`TerminalQuery ~> host::Bool` projection does neither.

The terminal judgment and projection are closed under their installed images.
An exhaustive no-match is evidence that a normal form is not an admitted
result; an incomplete or resource-limited match is **undetermined**, never a
negative answer. Conflicting Boolean outcomes for one normal form make the
query undetermined rather than selecting the first or best-weight proof.

## Source and request correspondence

The source of truth remains the existing Greg/Mike surface:

```text
Types {
  noadmit Computation;
  noadmit TerminalQuery;
  noadmit Flag = bool;
}
Terms {
  DoneBool . b:Flag |- "doneBool(" b ")" : Computation;
  CheckBooleanTerminal . x:Computation
    |- "terminalBool(" x ")" : TerminalQuery;
  TerminalYes . |- "terminalYes" : TerminalQuery;
  TerminalNo . |- "terminalNo" : TerminalQuery;
}
Rewrites {
  BooleanTerminal(b:Flag):
    (CheckBooleanTerminal (DoneBool b)) ~> (TerminalYes);
  projection TerminalVerdict : TerminalQuery ~> host::Bool {
    Yes : (TerminalYes) ~> true;
    No : (TerminalNo) ~> false;
  }
}
```

The typed rewrite and projection rows above illustrate existing syntax. The
complete Regex row set adds judgments for each former terminal constructor,
and must be validated against the generated parser before fixture migration.
The request names `Computation`, the selected unary judgment, and
`TerminalVerdict`, and supplies a structurally parsed `Computation` FLT. It
does not send guest source text for reparsing.

| Former observation name | Input constructor | Unique entry rewrite | Required terminal root | Data-free judgment |
|---|---|---|---|---|
| `FullMatch` | `CallFullMatch` | `StartFullMatch` | `DoneBool` | `CheckBooleanTerminal` |
| `Search` | `CallSearch` | `StartSearch` | `DoneMatch` | `CheckMatchTerminal` |
| `ReplaceFirst` | `CallReplaceFirst` | `StartReplaceFirst` | `DoneText` | `CheckTextTerminal` |
| `ReplaceAll` | `CallReplaceAll` | `StartReplaceAll` | `DoneText` | `CheckTextTerminal` |
| `Nullable` | `CallNullable` | `StartNullable` | `DoneBool` | `CheckBooleanTerminal` |
| `Derivative` | `CallDerivative` | `StartDerivative` | `DonePattern` | `CheckPatternTerminal` |

The canonical language value retains its `types`, `terms`, `equations`,
`rewrites`, projections, and limits. For this authored route, the old
`oslf.actions` and `oslf.observations` arrays are *absent*, not synthesized
from naming conventions. The terminal judgments and guest rewrites compile to
the existing semantic image; `TerminalVerdict` compiles to the existing
projected image.
The v2 query is a separate canonical request value referencing their exact
installed coordinates. Removing `Data` intentionally changes the language
fingerprint; no old receipt is relabeled as a new image receipt. Programmatic
`language/3` definitions that explicitly retain action/observation records
continue to use the v1 route unchanged.

The internal semantic service has a distinct `RelationObservationRequest`. Its
version-two transport is a closed eight-field tuple:

```text
[2, installedHandle, relationCategory, terminalJudgment,
   terminalProjection, structuralInput, callerLimits, replyChannel]
```

The application-local Rholang helper accepts a judgment, structural FLT, and
reply channel; it fixes the category and named projection once, hiding the
internal transport from call sites. An empty limits tuple selects the service
defaults, which are still met with the host and installed-theory ceilings.
The eleven-field limits tuple remains available for explicit caller
attenuation. The six-field v1 action ABI remains
unchanged and fail-closed; neither version is guessed from a malformed tuple.
The v2 reply carries every published term, its direct-relation receipt, its
terminal-judgment relation receipt, and the complete terminal-projection proof
roster under a version-two envelope. The
existing fixed-depth v1 receipt codec is not falsely reused for a different
receipt type. Limits and usage remain explicit in the internal transport and
are the componentwise minimum of host, installed-theory, and caller bounds.

## Checked evaluation and publication

The following algorithm is a service adapter around the existing kernel and
projection matcher, not a second parser or evaluator.

```text
OBSERVE-RELATION(handle, sort, judgment, projection, input, limits):
  resolve the opaque handle and require Observe, Reduce, Construct,
    plus the selected projection's exact declared rights
  resolve all three names against the same installed image and host profile
  require judgment : sort -> querySort and projection : querySort -> host::Bool
  meet host, theory, and caller limits; retain one cancellation/budget state
  admit the structural input exactly once under sort
  run the shared fair rewrite relation to its complete normal-form roster
  validate each fresh relation receipt and preserve every distinct derivation
  for each normal form, construct judgment(normalForm) structurally,
    normalize it through the same kernel, then project all query normal forms:
    collect every Boolean proof without top-k or first-result selection
    true only    -> retain term and all supporting receipts
    false only or exhaustive no-match -> reject this candidate
    mixed, malformed, incomplete      -> make the whole query undetermined
  if any stage fails, publish no successful prefix
  recheck the whole right roster against the same handle at atomic publication
  return all retained results in canonical order with exact usage
```

The direct relation is pure because it executes only the image's directed
guest rewrites and closed trusted intrinsics. Any external effect remains a
separate authorized bridge; the absence of an effect table does not grant it.
The selected projection's declared authority is independently checked and
cannot be inferred from a shared carrier representation. Each normal form and
each proof is retained
until checked evidence rejects it. The kernel's complete result order is
preserved without sorting, deduplication, or disambiguation. All traversal,
reconstruction, encoding, cancellation,
and teardown paths use heap worklists and bounded resources.

## Refinement obligations

For each former Regex action, prove or check these conditions against the
compiled image, not merely its textual spelling:

1. The corresponding `Call*` root has the same one-step successor roster as
   the former named entry rule. If another root rewrite applies, preserve that
   ambiguity and refuse a claim of legacy-action equivalence.
2. The relation phase and former normalization phase use the same directed
   rules, intrinsic witnesses, exact keys, resource profile, and admissible
   normal-form candidates.
3. Each terminal judgment reduces to `TerminalYes` exactly on its former
   action's accepted terminal constructor. `TerminalVerdict` maps `TerminalYes`
   to host `true` and `TerminalNo` to host `false`. A judgment selected for the
   wrong operation must not silently admit a different result root.
4. Both paths preserve all successful alternatives and refuse incomplete
   enumeration. A deterministic old action and a fair relation are equivalent
   only when the reachable successor relation is deterministic; otherwise the
   fair relation is the ambiguity-preserving semantics and needs an explicit
   behavior-change review.
5. The v2 codec round-trips every field and duplicate proof, charges all
   allocations and visits, rejects noncanonical/malformed values, and never
   treats a decoded receipt as authorization or verified proof.

The first, third, and fourth obligations are substantive: passing six happy
path examples alone cannot establish them. Differential tests must include
invalid scalars, stuck intermediate states, overlapping rewrites, conflicting
terminal projections, empty/duplicate proof rosters, revocation races, exact
budget cuts, cancellation at each stage, deep terms on a small native stack,
and all six existing Regex operations through the public Node route.

## Ownership and dependencies

The generated Rholang frontend still parses each FLT once and routes its
structural term to the installed parser. `GrammarCore` and the existing
`TheorySemanticImageV1` remain the common compiled artifact. The service owns
operation selection and versioned transport; the shared semantic kernel owns
rewrite enumeration and the authored terminal judgment; the existing installed
projection matcher owns the terminal Boolean projection; the Rholang/RSpace
host owns atomic publication. The Registry identifies and supplies versioned
images but does not itself grant `Observe`, `Reduce`, or `Construct` rights,
nor any rights declared by the selected projection.

The [flow diagram](figures/data-free-oslf-observation.svg) identifies the
stage boundaries and the no-partial-publication rule. The old v1 action route
remains available for exact programmatic metadata while authored GSLTs no
longer require a `Data` block.
