# Structural admission of runtime syntax

## Purpose and boundary

An already parsed foreign-language term (FLT) can be reflected into Rholang's
`Par` representation and passed through a channel or used as a structural
template fill. Its reflected language tag alone does not establish that its
fields belong to the requested grammar category. `DynamicSyntaxAdmission`
checks that structural membership without parsing source or evaluating a term.

The implementation reuses the existing
[reflection format](../../rholang-codegen/src/dynamic_reflection.rs),
[native validators and admission worklist](../../rholang-codegen/src/dynamic_admission.rs),
and [token decoder/evaluator contracts](../../grammar-core/src/runtime.rs).
It does not create a new parser, evaluator, literal constructor, or capability.
The [installed semantic service](installed-flt-judgments.md) additionally needs
exact theory-sort conversion, operation authorization and result validation.
Those obligations are not discharged by structural admission.

## Constructor and literal alternatives

A category may contain constructor applications, native literal values, or
both. A token associated with a category can produce a native value without an
intermediate constructor. For example, a `Scalar` token whose decoder and `str`
carrier return text can produce the text atom for `a`; a `PLiteral` constructor
can then contain that atom as its `Scalar` field. Both must remain admissible.

Compilation preserves every existing constructor alternative and selects the
additional native branches according to the declared category carrier:

| Category carrier | Additional structural branches |
|---|---|
| Dynamic syntax | Successful output kinds of tokens whose category ID is exactly this category; unavailable contracts remain unknown |
| Builtin String, Integer, Boolean or Bytes | The declared native kind, even without a lexical token; incompatible token outputs cannot widen it |
| Other builtin, collection, external or opaque carrier | An unavailable-contract branch; existing constructor branches remain available |

The unavailable branch does not assert support for a missing carrier codec.
Existing constructor fields and collection syntax keep their structural checks.
Captured token fields use the token's actual output contract independently of
the enclosing category carrier. For example, the current `float` token
evaluation returns text; this permits that captured text field, but does not
justify treating the text atom as a native floating-point category member.

This is structural carrier membership, not lexical-image membership. Admitting
a text value does not prove that its bytes match a particular token regular
expression or that a host callback previously produced it. No lexer is replayed
and no callback is invoked to manufacture such provenance.

## Shared successful-output contracts

`runtime_token_output_contract` is defined beside the existing closed native
evaluator. It classifies a token decoder followed by its optional one-input
evaluation:

| Contract | Meaning |
|---|---|
| `Known(kind)` | Every successful output has this native kind |
| `NoSuccessfulOutput` | The declared one-input evaluation cannot succeed for this decoder's output kind |
| `UnavailableContract` | No supported static output-kind contract is available |

The first contract is conditional on success. For example, an integer conversion
may still fail on a particular text payload. The projection does not claim that
every possible value of its output kind can be produced.

Text, integer, Boolean, hexadecimal-byte and unit decoders have fixed output
kinds. An unrestricted capability decoder does not. Closed unary evaluations
can nevertheless constrain that decoder's successful output: `len` returns an
integer even if its input came from a callback. A handler without a declared
output contract remains unavailable. Binary operators cannot succeed when
supplied the single decoded token input.

The projection follows the current evaluator exactly: `int` produces integer,
`bool` produces Boolean, and `str`, `rat`, `fixed` and `float` produce text.
It does not reinterpret numeric text as a different native representation.

## Three-valued checking

The explicit result is `Admitted`, `Rejected`, or `Undetermined(reason)`.
The reasons currently distinguish work exhaustion from an unavailable contract.

- Constructor fields are conjoined: every field must be admitted; a rejected
  field refutes that constructor alternative.
- Category alternatives are disjoined: an admitted alternative establishes
  membership even if another alternative has an unavailable contract.
- When no alternative is admitted, an unresolved alternative prevents a
  definitive rejection.
- Work exhaustion stops the check with `Undetermined(WorkLimit)`. Unvisited
  alternatives are not silently replaced by an empty list.

Known native branches require the exact reflected fingerprint, nullary shape,
and canonical payload. Existing validators enforce UTF-8 text encoding,
canonical integer spelling, Boolean spelling and byte encoding. The
unavailable-contract branch first checks the existing structural envelope.
A malformed envelope remains rejected; a valid or unresolved envelope remains
unknown. An unrestricted callback can produce a nonnullary structure, so this
branch must not impose a native-leaf-only nullary restriction.

The Boolean methods `admits_category` and `admits_captures` remain fail-closed
compatibility interfaces: `false` means membership was not established, not
necessarily that non-membership was proved. Consumers requiring the explicit
judgment use `check_category_with_budget`.

## Worklist and accounting

The compiled automaton contains interned shape states and the category's
constructor/native alternatives. Checking uses an explicit task stack, result
stack and request-local memo table keyed by input-node identity and state.
Field traversal, alternative combination and unavailable-contract checks do
not recurse on the Rust call stack.

The following pseudocode explains the worklist; it is not a separate evaluator:

```text
allowance := minimum(caller remaining work, installed automaton limit)
push Eval(root, requested category state)
while a task remains:
    Eval(node, state):
        if allowance is exhausted, stop with Undetermined(WorkLimit)
        charge one evaluated state, including a memo hit
        reuse a memoized judgment or schedule this state's children/alternatives
    And(fields): combine all field judgments
    Or(alternatives): combine all alternative judgments
    Unavailable: preserve structural rejection; otherwise return unknown
    Store(node, state): memoize the resulting judgment
on either exhaustion or completion, subtract consumed allowance from caller remaining work
return the exhaustion judgment or the complete root judgment
```

The caller keeps any unused work, including work above the automaton's own
ceiling. Repeated calls sharing the same allowance cannot replenish it.
`admits_captures` checks its entire telescope under one allowance. This accounting
counts evaluated states, not bytes, allocations, or the work of a later hashing
or semantic-kernel operation. Those boundaries require their own accounting.

## Verification scope

[DynamicCategoryAdmission.v](../../formal/rocq/runtime_grammar/theories/DynamicCategoryAdmission.v)
proves successful token-output kind composition, preservation of constructor
alternatives, justified native acceptance, exact fingerprint and native-leaf
guards, unavailable-contract behavior, and three-valued branch combination.
Its composed driver starts from rejection and proves complete branch union
under sufficient fuel and unknown on exhaustion. It builds on the recognition
connection established by
[TokenCategoryNormalization.v](../../formal/rocq/runtime_grammar/theories/TokenCategoryNormalization.v).

The model takes an already category-selected token list and existing constructor
judgments. It does not assume those judgments are correct: the combination
theorems state precisely which positive evidence must be present. Selection by
category ID is checked separately in the implementation's two-category test.
The model's fuel counts an already-formed branch list, whereas Rust charges
evaluated structural states. The correspondence is logical union and judgment
refinement, not exact fuel-for-fuel equality.

The proof does not cover payload codecs, callback provenance, lexical-image
converses, whole-request allocation bounds, or arbitrary semantic-sort conversion.
Focused Rust tests compare the classifier with the actual closed evaluator,
exercise mixed categories, native carriers without tokens, captured numeric
text, unknown callbacks, foreign tags, malformed leaves, shared work limits and
20,000-level terms on a 256 KiB stack. The
[installed-language tests](../../rholang-runtime/src/language_install.rs) additionally
exercise actual inline Regex installation, parsing, reflection, and typed filling;
they do not substitute fabricated reflected values for that integration path.
