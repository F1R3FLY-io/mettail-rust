# Observation predicate roles

A predicate role gives an existing observation an explicit Boolean
interpretation. It names the input constructor and the two closed result terms
that mean acceptance and rejection. The role is immutable language data, not
authority, a new operation registry, or a host implementation of the guest
language.

## Canonical declaration

An observation in the `language/3` `oslf.observations` list can contain
`predicate_role`. For the Regex application, the observation record has this
shape; its action and constructors must also be declared by that language:

```rholang
{
  "name": "FullMatch",
  "action": "full-match",
  "result": "Computation",
  "predicate_role": {
    "input_constructor": "CallFullMatch",
    "accepting": ["DoneBool", ["BTrue"]],
    "rejecting": ["DoneBool", ["BFalse"]]
  }
}
```

This is the existing structural theory-term notation. Greg and Mike's DDL can
transport the record through `Data`; no additional DDL parser or source
reconstruction is introduced. Omitting `predicate_role` leaves an ordinary
observation with no implicit truthiness. The absence of a role does not select
another observation or guess from a category name.

The existing right-hand-side term compiler lowers each result with the declared
observation result sort. A fresh environment forbids external variable,
remainder, and binder-slot dependencies. Existing local comprehension bindings
remain available. A rule abstraction uses a binder slot; it is not silently
reinterpreted as a self-binding lambda constant. Unsupported or ill-typed forms
are rejected by the same compiler and validators used for ordinary theory
terms.

The canonical `ObservationPredicateRoleV1` stores `input_constructor`,
`accepting`, and `rejecting`. Each result is a `ClosedTheoryTermV1`: its existing
flat variable roster, term roster, and root index. The representation introduces
no new term operators and no fake rewrite rule.

## Validation and execution boundaries

Canonical validation requires a unique role per input constructor, an existing
unary action whose domain is that constructor's result sort, and result terms
of the observation/action result sort. The action must reference a checked
theory rule and declare a pure effect with no emitted effects. These checks
do not grant execution rights or waive resource charges.

Closed constants are constructed by the existing semantic image compiler and
native term-construction worker. Their exact ground keys must differ. Comparison
therefore preserves existing native collection canonicalization and is
independent of flat arena indices or directed-acyclic-graph (DAG) sharing. It does not introduce a new
alpha-equivalence or reduce constants by unrelated rewrite rules.

One shared native validator is used at three existing boundaries:

| Boundary | Reason |
|---|---|
| Fresh semantic-image compilation | Reject a newly compiled role whose constants cannot be constructed or are equal. |
| Public installation after cache resolution, before batch publication | Cached images bypass compilation; they require the same native check. |
| Installed semantic-service preparation | Defend against lower-level table installs and retain the exact authorized owner. |

Core image admission remains source- and fingerprint-exact; it does not call
upward into the native runtime. The service factory absorbs native validation
work through its existing accounted-stage interface, including failed attempts.
Each observation is charged before its optional role is inspected, including
omitted roles; cancellation or an exhausted visit retains the paid prefix.
The existing constructor lookup context is built only for the first actual role.
Role source nodes, references, variables, and literal payloads participate in
the existing aggregate image-admission bounds. Native work, output nodes, and
key bytes have explicit ceilings. Exhaustion or cancellation does not establish
inequality and cannot produce a successful predicate result.

On the semantic-service wire, a malformed role is `Error` in the service
diagnostic domain, code 7. Construction exhaustion and cancellation retain
their existing kernel `Undetermined` codes; neither becomes rejection or a
Boolean false result.

The installed execution path uses the existing kernel without an ambient guard
callback. Unavailable premises remain undetermined. Purity is not zero cost,
and this declaration does not authorize host effects or publication.

## Identity and compatibility

The role is serialized inside TheoryCore, so it affects both theory and full
language commitments, including modules. The grammar projection is unchanged:
a role change does not change the parser fingerprint.

The exact canonical application binary interface (ABI) formats are
LanguageCore ABI 5, TheoryCore ABI 4, and
`mettail-language-core-value/4`. Older exact-format versions are rejected rather
than silently reinterpreted. The existing `language/2` and `language/3`
presentations still accept omission of the optional role. Semantic images keep
their existing structural layout and are bound to the new full-language
commitment, preventing replay of an image committed before a role change.

## Verification scope

[`ObservationPredicateRole.v`](../../formal/rocq/runtime_grammar/theories/ObservationPredicateRole.v)
models unique source binding, failure to construct or distinguish constants,
effect-emission refusal, explicit version and unhashed role commitments, parser
projection isolation, and the unchanged borrowed worker interface. Its checked
proofs are not a proof of all Rust execution, hash injectivity, or a new native
equality algebra. Source tests separately exercise the concrete compiler,
canonical value/module transport, native comparison, and refusal paths.

The role boundary alone does not implement FLT capture in `where`, complete
observation-roster classification, or atomic communication (`COMM`) admission. Those consume this
declaration through the existing installed semantic service and guard substrate;
their required behavior is specified in the
[Regex application contract](regex-gslt-application-contract.md#direct-flt-predicates-in-where).
