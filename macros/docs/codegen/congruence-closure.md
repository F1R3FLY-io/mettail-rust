# Dovetail Congruence Closure and Explicit Withholding

Primary implementation sources:

- [`dovetail_report.rs`](../../src/gen/runtime/dovetail_report.rs)
- [`withholding.rs`](../../src/gen/runtime/dovetail_report/withholding.rs)
- [`typed_lowering.rs`](../../src/gen/runtime/dovetail_report/typed_lowering.rs)
- [`reconstruct.rs`](../../src/gen/runtime/dovetail_report/reconstruct.rs)
- [`CongruenceWithholding.v`](../../../dovetail/formal/rocq/theories/Lowering/CongruenceWithholding.v)

## 1. Purpose

Dovetail evaluates a term language in an **e-graph**, a data structure whose
equivalence classes are called **e-classes** and whose operator applications
are called **e-nodes**. An e-node key contains its operator and the canonical
e-class identifiers of its child positions. That representation supplies
congruence closure intrinsically: once two child e-classes merge, parents that
differ only by those children acquire the same canonical key.

MeTTaIL exposes three authorial states for a rewrite context:

| declaration | meaning | Dovetail disposition |
|---|---|---|
| `| S ~> T |- C(... S ...) ~> C(... T ...)` | require propagation at the position occupied by `S` | delivered by e-graph congruence closure when that position is a child e-class; otherwise declined by name |
| no premise | infer the ordinary e-graph behavior | intrinsic congruence closure, with no explicit rule |
| `| S ~/> T |- C(... S ...) ~> C(... T ...)` | explicitly withhold propagation at the position occupied by `S` | sever the position, or decline the declaration by name when severance is not representable |

An **evaluation context** is a constructor position through which a child
rewrite propagates. **Severance** changes such a position from a child e-class
carrier into a payload-verbatim leaf. The payload remains reconstructable, but
the e-graph cannot inspect, match, or rewrite inside it.

The retired Ascent clause generator is not part of this pipeline. Its final
remaining module emitted only an uncalled freshness helper after the Dovetail
binder path moved to freshen-then-float; #95 retired that module and removes
stale `freshness.rs` artifacts during expansion.

## 2. Representation theorem

Let `$`f`$` be an operator and `$`c_0,\ldots,c_n`$` its child e-class
identifiers. The canonical e-node key is:

```math
K_f(c_0,\ldots,c_n)
=
\left(f,\operatorname{find}(c_0),\ldots,\operatorname{find}(c_n)\right).
```

Suppose `$`\operatorname{find}(a)=\operatorname{find}(b)`$`. Replacing `$`a`$`
with `$`b`$` at any child position leaves `$`K_f`$` unchanged. Hash-consing must
therefore place the two enclosing e-nodes in the same e-class. Congruence at a
child e-class position is a representation invariant, not a policy switch.

This yields **Theorem W1**:

> To withhold propagation at a position, the position must cease to store a
> child e-class identifier.

The typed lowering realizes W1 with a `FieldWithheld<Category>` carrier holding
the original category value. The carrier is a leaf from the e-graph's point of
view, while the generated inverse reconstructs the value losslessly. A lossy
`FieldOpaque(Debug)` carrier is not used for withholding because a term with no
redex could then fail reconstruction.

The Rocq development proves:

- `withholding_requires_severance`: merged child identifiers produce identical
  parent keys when the position uses `ChildClass`;
- `severed_payload_key_injective`: a `WithheldPayload` key remains injective in
  the original payload;
- `severance_removes_exactly_the_withheld_edges`: the severed edge relation
  retains exactly the ordinary propagation edges outside the derived withheld
  position set;
- preservation and rejection corollaries for unwithheld and withheld positions.

The proof uses no axioms, conjectures, parameters, admissions, or admitted
tactics. Its identifiers and payloads are natural numbers because the argument
requires only equality and child canonicalization.

## 3. Lowering architecture

```text
LanguageDef.rewrites
        |
        v
classify_withholdings
        |
        +-- accepted position --> typed field lowering --> FieldWithheld<Category>
        |                                                    |
        |                                                    v
        |                                           generated reconstruction
        |
        +-- unsupported position --> named refusal --> generated compile_error!

ordinary positive congruence --> child carrier reachable? -- yes --> closure disposition
                                                        |
                                                        no
                                                        v
                                                   named decline
```

`needs_typed_dovetail_path` routes every language containing a negative
congruence premise to the typed path. This routing includes declarations that
will be refused, ensuring the refusal is emitted on the same path that owns the
withholding semantics. The untyped `EGraph<String>` path never receives a
`WithholdingSet` and has no payload-bearing inverse carrier.

The same derived set is consumed by both sides of the typed isomorphism:

- `typed_lowering::field_child_expr_typed` emits a withheld carrier before any
  builtin, predicate, optional, collection, or ordinary-child branch;
- `reconstruct` recognizes the same severed positions and generates the inverse;
- `op_enum` derives the required `FieldWithheld<Category>` variants from the
  accepted positions.

No handwritten constructor-position table exists. The position is derived
from the declaring rewrite's left-hand side (LHS), then checked against the
constructor shape generated from the same `LanguageDef`.

## 4. Classification algorithms

**Algorithm 1 (Derive the withholding set).** For every negative premise, derive
one constructor-field coordinate or retain a named refusal. A declaration is
never silently dropped.

```pseudocode
procedure CLASSIFY_WITHHOLDINGS(language)
  positions <- empty sequence
  refusals <- empty sequence
  for each rewrite in language.rewrites do
    premise <- rewrite.withheld_congruence_premise()
    if premise is absent then
      continue
    end if
    result <- CLASSIFY_ONE(language, rewrite, premise.source)
    if result is a position then
      append result to positions
    else
      append the rule name and refusal reason to refusals
    end if
  end for
  return (positions, refusals)
end procedure
```

`CLASSIFY_ONE` refuses the following shapes explicitly:

- a rule carrying both positive and negative polarities;
- a left-hand side that is not a constructor application;
- zero or multiple direct occurrences of the source metavariable;
- a constructor whose generated shape is not `Regular`;
- an arity mismatch between the pattern and generated constructor;
- a builtin grammar slot, predicate, capture leaf, collection field, or
  optional field.

A native-backed language category such as `![i64] as Int` is deliberately not
a builtin grammar slot such as `Integer`. A field of category `Int` still holds
a child term/e-class and may be severed; an `Integer` field is already an opaque
leaf and has nothing to sever.

**Algorithm 2 (Lower one typed field).** Accepted severance is checked first so
the generated carrier and classifier cannot disagree about branch precedence.

```pseudocode
procedure LOWER_TYPED_FIELD(owner, index, field, value, withheld)
  if withheld.is_severed(owner, index) then
    emit payload-verbatim FieldWithheld leaf
  else if field is builtin, a predicate, or a capture leaf then
    emit the corresponding atomic leaf
  else if field is optional or a collection then
    emit its specialized carrier
  else
    enqueue a visit of the child category
  end if
end procedure
```

**Algorithm 3 (Record one rewrite disposition).** The report distinguishes a
delivered inference from an explicit suppression and from an unsupported
declaration.

```pseudocode
procedure LOWER_REWRITE(language, rewrite)
  if rewrite has an unsupported side condition then
    return Declined("has side conditions")
  else if rewrite has a negative congruence premise then
    return the classifier's Suppressed or Declined disposition
  else if rewrite has a positive congruence premise then
    if its carrier is unreachable by child e-class closure then
      return Declined(the carrier-specific reason)
    else
      return DeliveredElsewhere(EGraphCongruenceClosure)
    end if
  else
    continue with structural and native-rule lowering
  end if
end procedure
```

The parser stores the two polarities as distinct premise variants. It may parse
a rule containing both; Algorithm 1 refuses that contradiction by name before
lowering. Keeping parsing structural makes the semantic rejection observable
and testable.

## 5. Correctness and regression gates

The following layers guard the design:

| gate | obligation |
|---|---|
| withholding unit tests | empty baseline, scalar severance, nested refusal, contradictory-polarity refusal, builtin refusal, and native-category severance |
| [`congruence_declaration_witness.rs`](../../../languages/tests/congruence_declaration_witness.rs) | declared, undeclared, unreachable-carrier, and severed runtime behavior |
| [`congruence_withholding.rs`](../../../languages/tests/congruence_withholding.rs) | accepted withholding round-trip and reduction behavior |
| Rocq compilation | W1, payload injectivity, and edge-set theorems type-check |
| zero-admission scanner | the critical Rocq suites contain no unproved assumptions or admissions |
| reflected lowering dispositions | every declaration is delivered, suppressed, delivered elsewhere, or declined; silence is not a state |

The source of truth for the machine-checked model is
[`CongruenceWithholding.v`](../../../dovetail/formal/rocq/theories/Lowering/CongruenceWithholding.v).
The source of truth for runtime classification is
[`withholding.rs`](../../src/gen/runtime/dovetail_report/withholding.rs). Any
future carrier extension must update the classifier, typed lowering,
reconstruction, tests, and proof obligations together.
