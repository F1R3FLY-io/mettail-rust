# Rewrite-family proofs

These models describe explicit rewrite families and their translation into existing transition premises.
They cover the shared checker and the obligations of its source adapters.

| Model | Subject |
|---|---|
| `RewriteFamilyNormalization` | Typed lexical arguments, context plugging, and one-family transition equivalence. |
| `RewriteFamilyExtraction` | Paired contexts, occurrence rosters, and projection removal. |
| `RewriteFamilyPremises` | Declaration order and execution through existing premises. |
| `RewriteFamilyBoundary` | Ordinary-rule identity, idempotence, context preservation, and atomic publication. |
| `RewriteFamilyAuthored` | Equivalence between independent authored semantics and ordinary core rules. |
| `RewriteFamilyFocus` | Occurrence paths, typed child admission, separated holes, and parent type preservation. |
| `RewriteFamilyNames` | Complete name census, selective binder encoding, aliases, and compiler slots. |
| `RewriteFamilyAllocator` | Checked string allocation, freshness, distinct results, and exact exhaustion. |
| `RewriteFamilyAdapterRefinements` | Original parameter-list correspondence and ambiguity diagnostics that preserve existing outcomes. |
| `RewriteFamilyContext` | Exact context syntax admission, ordered domains, and ordinary payload preservation. |
| `RewriteContextSourceNames` | Context name observation, literal refusal, and existing canonical identifier validation. |
| `RewriteContextWireProjection` | Exact legacy selection, canonical child order, and type admission. |
| `RewriteContextTokenExtension` | Fresh custom-token preservation, priority ordering, reservation, and secondary dispatch. |
| `RewriteFamilyDescriptors` | Registered descriptors, ordered fields, unary binders, collection modes, and missing evidence. |
| `RootActivationProjection` | Exact root bindings, declaration order, local scope isolation, and projection refusal. |

The fifteen modules contain 206 theorem statements.
The adapter refinement imports the existing `TermParamReaderProjection` model.
The verification script checks every theorem's closed-assumption receipt and invokes the independent Rocq kernel checker.
The property extractor rejects theorem names without a behavior mapping.
[`property-behavior.tsv`](property-behavior.tsv) defines all 42 behavior groups.

## Run verification

Use Rocq 9.1.1 or a compatible version.
Put `coqc`, `coqchk`, and `rg` on `PATH`.
Alternatively, set `COQC` and `COQCHK` to their executable paths.

Run this command from the repository root:

```sh
bash formal/rocq/rewrite_family/verify.sh
```

The script copies the sources into `target/formal/rewrite-family`.
It writes compiled proofs, logs, source hashes, and the extracted property map there.
Supply an output directory as the first argument to select another location.

## Source correspondence

The [shared checker](../../../grammar-core/src/rewrite_family.rs) uses borrowed views of the original source trees.
Its [contract](../../../grammar-core/docs/rewrite-families.md) defines the adapter observations and edit numbering.
The proofs assume that these observations represent the actual source semantics.
Adapter tests must establish that correspondence for each frontend.

The context model separates an independent family-shape relation from a codomain scan.
Its unary and binary nodes represent recognized ordinary type constructors.
Unknown tags, invalid identifiers, and incorrect arities correspond to invalid syntax.
The scan preserves complete ordinary domains and results in their authored order.
Only rewrite contexts can admit the terminal `Rewrite` form.
Equation types, intrinsic output types, and ordinary term types retain their existing admission rules.

The context round-trip theorem covers family assembly and decoding.
It does not establish the complete wire codec.
Actual transport properties must compare the copied canonical payload with the original value.
Syntax admission does not imply executable support.
The existing executable context decoder rejects `multi`, even though the ordinary schema decoder accepts it.

The source-name model uses an independent relation for identifier and keyword tokens.
Its token classification premise corresponds to the existing lexer spelling table.
String literals remain separate, even when their payload resembles an identifier.
The final name check uses the existing canonical identifier rules.
The [transport properties](../../../mettail-elab/tests/rewrite_context.rs) exercise generated names, every current keyword, and literal refusal through the source parser.

The existing [WireAdmission model](../runtime_grammar/theories/WireAdmission.v) supplies the wire depth and resource admission laws.
Context types use the DDL structural depth limit.
Tag strings and envelope framing consume resources but do not increase type depth.
Source and wire properties exercise every recursive branch at depths 256 and 257.
Direct canonical context validation retains its independent admission behavior.

The allocator model abstracts names through an injective encoder and an exact equality test.
The implementation uses a fixed prefix and canonical decimal formatting.
Its checked counter has the model capacity `usize::MAX`.
Successful allocation requires a representable successor, so the final counter value cannot produce a result.

The typing proofs cover admitted, nonempty sorts.
They do not describe temporary untyped map binders.
The slot proofs preserve existing allocated prefixes and allow an injective mapping for later slots.
They do not assert whole-rule numeric slot identity for external guard evaluators.

The [test map](behavior-tests.tsv) connects every behavior group to exact implementation test functions.
Extraction rejects missing groups, unknown groups, duplicate groups, and missing test functions.
The generated status `mapped_to_tests` records this association only.
Successful test receipts remain separate evidence.
Passing shared-checker tests alone does not close adapter or runtime correspondence obligations.

The token extension imports the existing `LexForkKeywordReservation` model.
Its batch law assumes distinct new custom kinds, positive old priorities, and zero new priorities.
The concrete lexer must establish these premises and preserve the reserved-identifier shadow decision.

The batch fold receives new tokens in reverse concrete kind order.
Its output preserves the old alternatives as an exact prefix after reservation.
The generated consumer tests must also establish the secondary-dispatch premises.
These models do not establish whole-parser equivalence.

The descriptor model imports the existing Focus and SemanticTransitionKernel laws.
Exact lookup assumes unique registered names and exact string identity.
Existing validation owns registered references, Map product shape, and nonempty Product factors.
The adapter observes registered fields without introducing another type inference algorithm.

Root collections reuse the existing compiler selection helper.
That helper selects by the declared element before PathMap mode selection.
The adapter preserves zero-match and ambiguous-match refusal.
PathMap Set children use the key sort. Map children use the declared pair sort.

Temporary collection field evidence does not establish final payload admission.
Final validation still refuses payloads for PathMap Neutral and absent modes.
Actual compiler and runtime correspondence remain required for every mapped property.

The root projection model reuses the existing scoped variable and substitution definitions.
An independent chronological lookup specifies the latest exact binding.
Projection retains declared bindings from the rule activation, regardless of variable role.
Fresh comprehension activations keep their local keys outside the published domain.

Grounding still uses the complete substitution when a retained value depends on local terms.
Local-extension noninterference assumes unchanged grounding observations.
Unique output IDs require the unique declaration IDs checked during image restoration.
A grounding failure returns no projected vector.

The model abstracts grounding and does not prove allocation behavior or work counters.
[Projection properties](../../../dovetail-runtime/src/semantic_transition_kernel/tests/root_projection.rs) check the actual method, scope allocator, grounding, and refusal boundaries.
[Runtime correspondence](../../../dovetail-runtime/tests/rewrite_families.rs) checks complete abstraction reconstruction through the public compiler and matcher.
