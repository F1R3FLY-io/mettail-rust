# Regex GSLT application contract

This is the implementation and acceptance contract for an ordinary Rholang
application that defines a regular-expression language as a Generalised
Structured Language Theory (GSLT), then uses foreign-language terms
(FLTs) to match, search, replace, and guard receives. It is not a claim that the
application or the public-node integration is already runnable.

The existing [Regex fixture](../../rholang-runtime/tests/fixtures/regex_extension.rho)
installs a Module/Theory and executes three syntax-expansion rewrites. The
[installed semantic service](installed-flt-judgments.md#installed-semantic-system-processes)
already transports checked reductions and observations. Neither supplies the
practical rule families or direct installed-FLT `where` integration specified
here. The application must run through the isolated MeTTaIL-only F1r3node
public entrypoint; a library test is an intermediate check, not that result.

## One source, one semantic implementation

The entire application, including Greg/Mike `Module`, `Theory`, `Types`,
`Terms`, `Equations`, `Rewrites`, and canonical `Data` declarations, enters
through the generated parser for
[Rholang](../../languages/src/rholang.rs). Inline DDL is parsed structurally
once. Installing the resulting immutable language value produces an opaque
handle. Each explicitly qualified FLT selects that handle and a declared
category; its structural text-and-hole payload reaches the selected guest
parser for its first parse. Neither declaration nor guest payload is printed
and reparsed.

Regex semantics belong to declared GSLT rules, compiled by the existing theory
compiler and executed by the shared semantic transition kernel. The existing
closed intrinsics supply only equality, UTF-8 traversal/slicing, checked natural
addition, and ordered text concatenation. No regex-specific host function,
second evaluator, parser fallback, or application-side simulation of `where`
is part of this design.

## Pattern language

The regular core is capture-free and case-sensitive. Its familiar operators
are a PCRE-shaped subset, not a claim of PCRE engine compatibility. The existing
reference semantics explicitly choose leftmost-longest search and make dot
match any Unicode scalar, including newline. Grouping is not a capture.

| Guest surface | Declared constructor | Meaning |
|---|---|---|
| Literal scalar | `PLiteral(Scalar)` | Exactly that Unicode scalar |
| `.` | `PAny` | Any one scalar, including newline |
| `(?!)` | `PFail` | Empty language |
| `()` | `PEpsilon` | Empty text |
| `(p)` | `PGroup(Pattern)` | Transparent grouping |
| `p\|q` | `PAlt(Pattern, Pattern)` | Alternative |
| `pq` | `PConcat(Pattern, Pattern)` | Concatenation |
| `p*`, `p+`, `p?` | `PStar`, `PPlus`, `POptional` | Repetition and optionality |
| `p{m,n}` | `PRepeat(Pattern, Nat, Nat)` | Inclusive bounded repetition |

Postfix binds tighter than concatenation, which binds tighter than alternation.
An atom admits at most one unparenthesized postfix. Reject `a*?`, `a++`, and
`a?+`; explicit grouping, such as `(a*)?`, expresses nested regular operations.
The empty group `()` denotes epsilon without reserving an alphabetic word that
could also parse as a concatenation of literals. Preserve all remaining
readings until justified disambiguation; never elect the first epsilon reading.
Retain the fixture's explicit binding powers 30, 20, and 10 and left association
for the binary operators. Other DDL productions retain the agreed BNFC-derived
defaults unless explicitly overridden. Bounds are nonnegative integers; reversed
bounds denote `PFail`, as proved by `invalid_repeat_bounds_are_rejected`, rather
than an implementation-selected alternate interpretation.

The literal token accepts individual ASCII letters/digits and non-ASCII Unicode
scalars; the existing ASCII-only token must be expanded for the Unicode cases.
Arbitrary scalars, including metacharacters and whitespace, remain expressible
through typed `Scalar` holes. This first concrete surface does not promise an
escape sublanguage, character classes, anchors, captures, backreferences,
lookaround, flags, lazy/possessive operators, or PCRE replacement-string parsing.
These are not silently recognized with different meanings. Unsupported syntax
must be rejected, not routed to a native regex engine.

The required equations include alternative failure/idempotence, concatenation
failure/identity, and star of failure/epsilon. Plus, optionality, grouping and
bounded repetition elaborate through the existing reference expansions. The
rule implementation must establish correspondence to
[RegexGsltMatch](../../formal/rocq/runtime_grammar/theories/RegexGsltMatch.v),
not infer matching correctness from the three existing fixture rewrites.

## Sorts, carriers, and operation forms

The [existing constructor roster](installed-flt-judgments.md#regex-application-handoff)
remains authoritative for Pattern, Text, Scalar, Bool, Nat, MatchResult,
ReplacementTemplate, and the abstract computation states. The concrete
application adds an ordinary declared `Computation` sort for request,
continuation, and terminal constructors. This is a guest category, not a new
host language or a second machine.

| Operation | Request constructor and ordered fields | Guest request spelling | Declared observation | Terminal result |
|---|---|---|---|---|
| Nullable | `CallNullable(Pattern)` | `nullable(p)` | `Nullable` | `DoneBool(Bool)` |
| Derivative | `CallDerivative(Scalar, Pattern)` | `derivative(c,p)` | `Derivative` | `DonePattern(Pattern)` |
| Full match | `CallFullMatch(Pattern, Text)` | `fullMatch(p,t)` | `FullMatch` | `DoneBool(Bool)` |
| Search | `CallSearch(Pattern, Text)` | `search(p,t)` | `Search` | `DoneMatch(MatchResult)` |
| Replace first | `CallReplaceFirst(Pattern, ReplacementTemplate, Text)` | `replaceFirst(p,r,t)` | `ReplaceFirst` | `DoneText(Text)` |
| Replace all | `CallReplaceAll(Pattern, ReplacementTemplate, Text)` | `replaceAll(p,r,t)` | `ReplaceAll` | `DoneText(Text)` |

These are required guest productions, not source snippets claimed to execute
against the current fixture. Action IDs are respectively `nullable`,
`derivative`, `full-match`, `search`, `replace-first`, and `replace-all`. Each
action explicitly names its entry rewrite and uses the existing bounded
endomorphic normalization on `Computation`. Private continuation constructors
are declared and sorted through the same signature. The entry rule starts the
operation; normalization does not dispatch by guessing a constructor name.

Every listed `Done` constructor has codomain `Computation` and no outgoing
rewrite. Consequently each observation's declared result sort is
`Computation`, **not** the sort of the enclosed value. Applications extract the
enclosed result through a qualified structural FLT pattern. Deterministic
normalization claims require proof and runtime enforcement; finding the first
output does not establish determinism or completeness.

Text is the existing native String carrier; Scalar is a native String containing
exactly one valid Unicode scalar. Nat is the checked nonnegative subset of the
existing signed integer carrier. The carrier name alone does not enforce these
refinements. `BTrue` and `BFalse` are explicit constructors; native Boolean
intrinsic results require an explicit declared conversion, not tag coincidence.
Text and Scalar categories must explicitly admit the typed holes required by
the application. The present fixture's `admits_variables:false` must not be
bypassed by the adapter.

Host String fills use the existing native reflection codec, declared carrier,
and structural fill admission. A raw host string is not already a reflected
guest Text. Quoted text literals, when offered by the guest grammar, use the
existing literal decoder. They do not open an additional text parser.

## Search and replacement observations

Full match consumes the entire logical text. Search selects the least starting
scalar position admitting a match, then the longest match at that position.
Thus `a|aa` searching `aa` returns the two-character match even though the
shorter alternative appears first. No prefix ranking or top-k truncation may
change this semantic choice.

The public `MatchFound(start,end,text)` fields contain zero-based **UTF-8 byte
offsets**, an exclusive end, and the exact matched substring. `NoMatch` is a
complete negative result, not resource exhaustion. Internal reference positions
count Unicode scalars; the concrete rules advance byte cursors using existing
UTF-8 intrinsics. They must preserve this correspondence:

```math
\operatorname{byteSpan}(s,[i,j)) =
[\operatorname{scalarByteOffset}(s,i),
 \operatorname{scalarByteOffset}(s,j)).
```

Here $`s`$ is the scalar sequence and $`[i,j)`$ its half-open reference span.
There is no Unicode normalization, case folding, grapheme-cluster indexing, or
byte-wise splitting of a scalar. For `λ+` searching `éλλx`, the scalar span is
`[1,3)` and the public byte span is `[2,6)`, with substring `λλ`.

Replacement is structural: `ReplacementEmpty`, `ReplacementLiteral(Text)`,
`ReplacementWhole`, and `ReplacementAppend(left,right)`. Their guest spellings
are `empty`, `literal(t)`, `whole`, and `append(l,r)`. They are not interpolated
replacement strings. `whole` denotes only the entire matched substring; there
are no capture groups in this profile.

Replace-first replaces the selected search result once; a miss returns the
original text. Replace-all searches the remaining original input, never its
generated replacement. A nonempty match advances to its end. An empty match
emits its replacement and, if input remains, copies exactly one original scalar
before continuing. An empty match at the end emits once and terminates. This
also applies at the end following a nonempty match. Output and any internal
span trace remain private until the complete bounded computation succeeds.

## Direct FLT predicates in `where`

The required expression is an explicitly qualified `Computation` FLT whose
guest body is `fullMatch(a(b|c)+, ${text:Text})`, in the existing receive's
`where` position. The selector is the lexical installed handle `h`; the complete
FLT spelling is ``h:Computation`fullMatch(a(b|c)+, ${text:Text})` ``. A receive
binds `text`, and its guarded continuation uses that received value only after
the predicate succeeds. This is the target surface, not a claim that the
current lowering already accepts an installed selector in that position.

The host grammar already admits it. Its semantic meaning requires an explicit
binding, since an FLT's selector/category does not name an observation. Extend
the **existing observation declaration** with an optional checked predicate
role: input constructor, closed accepting result term, and closed rejecting
result term. Reuse the existing flat typed term representation. Do not add a
second action registry, pattern language, or regex method to the host.

For `FullMatch`, that role binds `CallFullMatch` to the observation's existing
action, accepting `DoneBool(BTrue)` and rejecting `DoneBool(BFalse)`. `Nullable`
may bind `CallNullable` in the same way. Derivative, search, and replacement
results are not implicitly truthy. No category name, alias, fingerprint, or
first-declared action grants a predicate role or execution authority.

Enrollment must check a unique binding per input constructor, its domain
against the action, both closed result terms against the observation result
sort, distinct accepting/rejecting terms under the actual structural comparison,
and an effect-free, reject-safe execution path. The role belongs to canonical
TheoryCore and its full-language commitment. Its versioned codec, module
composition, admission, and cache compatibility must be checked explicitly;
existing `language/2` and `language/3` artifacts must not silently change meaning.

| Complete checked observation | Predicate verdict |
|---|---|
| Nonempty roster, every term equals the accepting term | Proven true |
| Nonempty roster, every term equals the rejecting term | Proven false |
| Mixed, unclassified, empty, or incomplete roster | Undetermined |
| Exhaustion, cancellation, invalid result, missing authority, stale handle, or execution failure | Undetermined with a retained diagnostic; no successful commit |

This classification preserves duplicate results and never selects one candidate
from an unresolved family. `NoTransition` or a stuck state is **not** a checked
false result. The full-match rules themselves must prove that their terminal
Boolean is correct. A completed `DoneBool(BFalse)` is a successful observation
carrying false, distinct from a failed semantic-service call.

Reuse the existing [where-guard substrate](semantic-predicates/18-the-where-guard-substrate-wire.md),
its opaque-atom resolver, tri-state connectives, refusal ledger, and commit
policy. Negating Undetermined must remain Undetermined. Dispatch follows the
formula's defined evaluation order and shared budget, not an eager unbounded
pass over all embedded semantic operations. Keep capability-bearing atoms
residual during compile-time discharge: a closed literal does not remove its
live authority or funding obligations.

Guard lowering retains the structural template and an explicit lexical capture
map, not an ordinary construction/reply-channel trampoline. Resolve receive
binders by identity and de Bruijn level, including joins, shadowing and repeated
holes. Reuse declared hole admission and native reflection. Hiding bound
variables inside an opaque list envelope is insufficient: current substitution
deliberately does not descend into that envelope.

The actual COMM commit must atomically validate the retained authority,
snapshot/evidence, and host funding obligations before consuming any joined
message or running the continuation. Existing guarded reply publication does
not by itself guard an ordinary receive. Do not hold authority locks while
executing the semantic kernel or acquire them recursively. The existing
[guarded-receive architecture](semantic-predicates/08-runtime-comm-enforcement.md)
is the composition point, not an alternate application protocol.

## Ordinary application and resource boundary

The application installs its inline module, obtains the exported opaque handle,
and constructs scoped FLTs. Ordinary reduce/observe calls use the existing
six-field request `[1, handle, name, input, limits, reply]` as the system
process's single payload. The installed URNs are `rho:mettail:flt:reduce` and
`rho:mettail:flt:observe`. The complete
[wire contract](installed-flt-judgments.md#installed-semantic-system-processes)
defines statuses, term/receipt pairing, finite errors and cumulative usage.

The same declared operation is observed both through that interface and directly
in a guard; their checked semantic results must agree. Structural result
patterns extract `DoneBool`, `DoneMatch`, and `DoneText` results for deterministic
output. The guarded example also sends a later matching message after an
initial mismatch, demonstrating that rejection left the receive installed and
the first message available.

All parser, construction, semantic, proof, frontier, term, output and boundary
allowances are bounded by the applicable installed, host and request policies.
Meter primitive traversal and private construction before work/allocation;
abstract reference functions that calculate metrics after computing are not a
runtime preallocation strategy. Natural arithmetic is checked. Exhaustion
returns a distinguished refusal, never a partial replacement or a Boolean
fallback. Logical work, semantic resource grade, validator demand and actual
settlement remain distinct. A pure regex theory does not acquire a Cost(G)
profile or funding authority by declaring one. The existing host funding gate
and its checked projection must govern the actual public-node execution.

## Required observable cases

Spans below are public byte offsets. Pattern spelling follows the profile above;
the rows are semantic test vectors, not runnable host code fragments.

| Case | Operation and input | Expected result |
|---|---|---|
| M1 | Full match `a(b|c)+`, `abcb` | True |
| M2 | Full match `a(b|c)+`, `ax` | False |
| M3 | Full match `a(b|c)+`, `xab` | False, not substring search |
| M4 | Nullable `a?`; full match `.`, newline | True in each case |
| M5 | Full match `a{2,3}`, `a` / `aaa` / `aaaa` | False / true / false |
| M6 | `a{3,2}` | Denotes failure |
| D1 | Derivative `a`, `a+` | `DonePattern(a*)` |
| S1 | Search `a+`, `xaaab` | `MatchFound(1,4,"aaa")` |
| S2 | Search `a|aa`, `aa` | `MatchFound(0,2,"aa")` |
| S3 | Search `a+`, `bc` | `NoMatch` |
| U1 | Search `λ+`, `éλλx` | `MatchFound(2,6,"λλ")` |
| U2 | Literal U+00E9 against U+0065 U+0301 | False; no normalization |
| R1 | Replace-first `a+`, literal `x`, `baac` | `bxc` |
| R2 | Replace-all `a+`, literal `x`, `aaba` | `xbx` |
| R3 | Replace-first `a+`, append literal `[` / whole / literal `]`, `baac` | `b[aa]c` |
| R4 | Replace-first `a+`, literal `x`, `bc` | `bc` |
| R5 | Replace-all `()`, literal `x`, `ab` | `xaxbx` |
| R6 | Replace-all `()`, literal `x`, `λ` | `xλx`; advances one scalar |
| R7 | Replace-all `a*`, literal `x`, `a` | `xx`; final empty match once |

Public-node acceptance additionally requires these distinct cases:

1. Direct full-match FLT in `where`: M1 fires once; M2 consumes nothing and
   leaves the continuation installed. A later matching message can fire it.
2. Exhaustion/cancellation in the same guard and under `not`: no successful
   commit, a distinguishable refusal, no partial join consumption or output.
3. Wrong handle/category, forged reflected data, stale/revoked authority,
   missing observation/reduction rights, conflicting predicate bindings and
   malformed hole fills: reject before effects; no alias or URI authority.
4. Join-order, lexical shadowing, repeated-hole and nested-scope witnesses:
   exact received text reaches the intended declared slot without source
   interpolation, capture or message reordering.
5. Exact and one-less work/output allowances: completed results or explicit
   bounded refusal, including replacement that would otherwise emit a prefix.
6. Complete duplicate, mixed, empty and incomplete result families: the
   predicate classification above, including negation; no early candidate cut.
7. A changed declared regex rule changes the actual observed behavior and
   full-language commitment. No native regex handler supplies the answer.
8. Actual eval/gRPC parser provenance, funding/effect admission and deterministic
   outputs: no legacy frontend, hidden fallback, or library-only substitute.
9. Unsupported adjacent-postfix spellings `a*?`, `a++`, and `a?+`: syntax
   rejection rather than reinterpretation as nested operators; `()` has exactly
   the declared epsilon meaning and is not an arbitrary retained-reading choice.

## Proof and implementation correspondence

The six existing `RegexGslt` models provide the signature, derivatives, search,
replacement, rule interpretation and finite oracles. The existing
[SemanticIntrinsics](../../formal/rocq/runtime_grammar/theories/SemanticIntrinsics.v)
model supplies UTF-8 cursor laws. The additional
[application contract](../../formal/rocq/runtime_grammar/theories/RegexGsltApplication.v)
composes valid search spans and ordered replacement spans with those byte-offset
laws and checks concrete examples from the table. These are proofs of the
specified reference model, not the emitted DDL, Rust code, wire decoder or node.

Before each nontrivial implementation boundary, prove its precise refinement:
rule/continuation execution to the reference functions; native carriers to
scalars and byte cursors; predicate enrollment and complete-result
classification; capture substitution; and atomic authority/funding commit.
Then test the real source correspondence, including the negative cases above.
Rocq compilation and a separate silent kernel check are both required, under
explicit memory limits with artifacts in `target/`.

Implementation order is the application contract, admitted frontend contract,
nullable/derivative rules, full match, search, replacement, application source,
and the existing neutral frontend/provider/public-node gates. The provider
matcher owns the retained predicate/capture descriptor, semantic-atom resolver,
and actual COMM authorization/funding handoff. Each needs its proof and focused
tests before the public application gate; it cannot be deferred as an optional
regex optimization. Broader language parity and later automata optimization
retain their campaign owners without replacing any required behavior here.
