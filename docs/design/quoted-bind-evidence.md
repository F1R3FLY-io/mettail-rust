# Quoted-bind evidence

The generated parser uses its existing evidence gate to select scalar quoted bind patterns.
For example, `for(@x <- c){Nil}` retains `InputBindQuoted`.
It does not also retain `InputBind(NQuoteShort(x), c)`.
The polyadic form `for(@x, @y <- c){Nil}` keeps its separate `InputBindPolyadic` rule.

## Repair

The merged binder classifier exposed two defects in the gate.
Binder repetition terminators, including `<-` and `<=`, entered the structural closing-delimiter table.
The scanner therefore stopped before it could recognize the bind trigger.
The new `LeadingCategory` routes also bypassed the gate that already guarded `CrossCatLhs` routes.

The repair supplies collection bracket pairs to the existing scanner.
A synthesized collection opener such as `Set (` contributes one opening parenthesis.
Binder repetition terminators do not change the bracket depth.
The first exposed bind trigger selects the quoted rule.
An earlier comma, row boundary, or enclosing closing bracket keeps the alternative route.
Nested rows cannot supply an outer bind trigger.

Both delegation paths now use the same evidence gate.
The string projection helper also uses that gate before it parses a leading cross-category operand.
The helper creates one lazy lexical lattice and reuses it across candidate assignments.
The gate checks the actual leading sigil, so ordinary unquoted binds keep their routes.

The generated trigger table uses the result category and source category together.
This distinction preserves cost signatures that contain quoted sends.
For example, `@channel!(1) :: ()` reaches `CostSigGround` through `Name`.
A send trigger from the `Name` source must not suppress the separate `CostSig` source.

The measured Rholang table has two entries:

| Result | Source | Bind triggers | Earlier alternative trigger |
|---|---|---|---|
| Proc | Name | `!`, `!!` | None |
| InputBind | Name | `<-`, `<=` | `,` |

All other source pairs have an inactive gate.
The change uses the existing grammar classifiers, scanner, dispatcher, and walker.
The owned engine already refuses the affected cross-category policy metadata at admission.
This repair does not add that unsupported policy to the owned engine.

## Verification

[AtQuotedBindGate.v](../../formal/rocq/prattail_wpda_runtime/theories/AtQuotedBindGate.v)
contains the existing model and the source-isolation extension.
All 57 theorem assumption checks are closed. The independent kernel check passes.
The model abstracts completed InputBind rule tails through `yields`.
The generated-parser tests check that abstraction against actual syntax and constructor families.
The model does not prove the complete parser or a linear bound for its full frontier.

| Model invariant or result | Implementation check |
|---|---|
| Bracket tables exclude binder terminators and count synthesized parentheses once | `bracket_alphabet_contains_only_collection_pairs` |
| Evidence agrees with the first exposed trigger and remains inactive without bind triggers | `bind_evidence_matches_first_exposed_trigger` |
| Nested rows do not suppress polyadic patterns | `balanced_nested_rows_cannot_supply_outer_bind_evidence` and the polyadic regression rows |
| Scalar selection is single-valued, retains the quoted interpretation, and removes only the modeled whole-name alternative | `generated_bind_gate_keeps_the_declared_pattern_family` and the scalar regression rows |
| The retained model interpretations need no further realization filtering | The same constructor-family property excludes the whole-name scalar variants |
| A missing source pair is inactive, and another source cannot supply its triggers | `send_triggers_do_not_suppress_cost_signature_sources` and the measured generated table |
| InputBind source isolation preserves the fixed gate | The constructor-family property covers scalar, persistent, query, and both polyadic forms |
| The projection helper cannot restore a rejected whole-name alternative | The constructor-family property compares the string facade, walker enumeration, and single-result parser |
| A non-sigil input keeps its ordinary source delegate | The same property covers ordinary scalar, persistent, and query binds |
| Other Proc readings remain available | `the_gated_proc_buckets_keep_their_readings`, compared with the before-run |

The three scanner and bracket properties each use 256 generated cases.
The two generated-parser properties each use 128 generated cases.
The model also retains counterexamples for the previous tables and incomplete repairs.
The recorded before-run reproduces five scalar failures and preserves both polyadic controls.
The generated-parser property also exposed a direct-query bypass through the projection helper.
Its minimized input is `@x0 <- channel!?(1)`. The regression seed remains in the test corpus.
Those counterexamples describe the old implementation, rather than required behavior of the corrected implementation.
The compile-time gate switch remains enabled. Its disabled branch is a model identity result, not a tested runtime configuration.

The final integration checks on 2026-10-22 pass all five quoted-bind tests and both `beat_5` REPL cases.
The complete Rholang suite passes all 353 tests, including exact bind counts at sizes 8, 16, and 24.
The debug and release stack checks pass at the unchanged 32768-byte frame limit.
The complete DDL suite also passes all 36 tests.
The separate semantic-predicate suite exposed an obsolete global-reservation expectation for the explicitly contextual `PPar` keyword.
That expectation belongs to the parser-expectation task and does not change the quoted-bind gate.

Run the focused checks:

```sh
cargo test --locked -p prattail --test quoted_bind_evidence
cargo test --locked -p languages --no-default-features \
  --features rholang,rho-codegen,dovetail-codegen,walker-trace \
  --test rholang_at_quoted_bind_gate --test rholang_cost_syntax \
  -- --test-threads=1
coqc -Q formal/rocq/prattail_wpda_runtime/theories PrattailWpdaRuntime \
  formal/rocq/prattail_wpda_runtime/theories/AtQuotedBindGate.v
coqchk -silent -Q formal/rocq/prattail_wpda_runtime/theories PrattailWpdaRuntime \
  PrattailWpdaRuntime.AtQuotedBindGate
```


## Prefix and continuation association

The gate table retains each result category, source category, prefix, and operator as one association.
A direct rule must contain a typed operand after its prefix.
The operand type must match the source wrapper's operand type.
A literal-only rule cannot provide this evidence.

The generator reuses the existing infix projection and atomic classifier.
It compares the complete continuation after the leading operand.
Parameter names are replaced by declaration indices for this comparison.
Operand types, literals, repetitions, separators, and parameter positions remain significant.
Unsupported projection entries cannot establish coverage.

Every whole-source rule for an operator must have a matching direct continuation for every applicable source wrapper.
An uncovered alternative makes that operator a stop.
The source wrapper's existing alias class supplies related constructor labels with the same prefix.
An unrelated source rule with that prefix prevents the gate from suppressing the source delegate.

For example, these rules do not permit a gate for `@` followed by `!`:

```text
Source ::= "@" Value
Result ::= Source "!" "(" Value ")"
Result ::= "#" Value "!" "(" Value ")"
Result ::= "@" "empty" "!" "(" ")"
```

The first direct alternative has a different prefix.
The second direct alternative has no general operand.
A direct alternative with braces also cannot cover the whole-source alternative with parentheses.

The existing realization filter consumes the same relation as the parse gate.
Its metadata identifies a whole-source rule and a source-atom rule together.
The filter suppresses a parent only when its first child has alternatives and every alternative has a qualified pair.
A child with an uncovered alternative keeps the parent.
The default engine relation is empty.

The table construction follows these steps:

```text
Group existing cross-category operators by result, source, and trigger.
Find declared prefix wrappers with the existing atomic classifier.
For each prefix, retain its source wrapper and alias labels.
For each trigger, compare every whole-source continuation with direct prefix continuations.
Add fully covered triggers to the bind set.
Add other triggers to the stop set.
Emit exact rule pairs for the fully covered families.
```

### Model and implementation checks

`AtQuotedBindGate.QualifiedGateRows` models qualified rows and complete alternative coverage.
It does not prove equivalence of arbitrary fold bodies or correctness of the complete parser.
The original constructor-family policy and bracket scanner remain in effect.
Generated-language tests check the retained policy against actual parser behavior.

| Model invariant | Implementation check |
|---|---|
| `key_eqb_spec` and `selected_row_has_exact_provenance` | `quoted_bind_rows_preserve_rule_associations` checks exact category, prefix, operator, and rule pairs |
| `unrelated_key_is_inert` | The same property checks unrelated prefixes and result categories; the realization property checks foreign source and result categories |
| `nullary_rule_cannot_cover` | The table property supplies a literal-only alternative |
| `foreign_operand_cannot_cover` | The table property supplies a different operand category |
| `different_tail_cannot_cover` | The table property changes the closing delimiter |
| `gate_covers_every_required_rule` and `uncovered_alternative_keeps_delegate` | The table property adds an uncovered rule with the same trigger; the realization property generates mixed child alternatives |
| `absent_family_keeps_delegate` | Both properties include empty families or empty child alternatives |
| `complete_family_selects_gate` | Both properties check fully covered families |
| `independent_unions_invent_a_pair` | The table property separates two prefixes and their operators |

The table property uses 64 cases.
The realization property uses 128 cases and calls the actual forest predicate.
`prefix_postfix_operand` also checks exact tree readback through the main parser and the facade.
Its recursive properties cover nested postfix operands and enclosing sends.
The existing Rholang bind, cost-syntax, and integration checks remain required before accepting this repair.
