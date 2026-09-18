# Regex GSLT rule-to-model correspondence

The [inline Regex declaration](../../rholang-runtime/tests/fixtures/regex_gslt.rho)
defines nullable, derivative, full-match, search, and replacement computations as
generalized structured language theory (GSLT) rewrites inside an ordinary
Rholang `Module` and `Theory`. This
document records how those declared rules correspond to existing Rocq models and
concrete runtime tests. The new application drivers require their focused runtime
checks; their presence does not establish a completed public-node application.
The required observable behavior remains the
[application contract](regex-gslt-application-contract.md).

The generated Rholang parser parses the inline declaration once. Elaboration
consumes that structure, the existing theory compiler builds its semantic image,
and `SemanticTransitionKernel` executes the declared transitions. None of the
models below is a second runtime evaluator, and no native regex engine implements
these operations.

## Representation and entry boundaries

`PFail`, `PEpsilon`, `PLiteral`, `PAny`, `PAlt`, `PConcat`, and `PStar` form the
seven-constructor core. `PGroup`, `PPlus`, `POptional`, and `PRepeat` extend the
surface syntax. Surface elaboration returns core patterns before nullable or
derivative evaluation begins. Continuations are declared data: `NFrames` for
nullable, `DFrames` for derivatives, and `EFrames` for surface elaboration.

`Bool` contains ordinary `BTrue` and `BFalse` constructors. `Flag` carries native
Boolean results of checked intrinsics. The declarations consume a native flag
through explicit true/false literal patterns; they do not confuse it with a
nullable result. `Nat` uses a checked nonnegative `i128` carrier:

```math
0 \leq n < 2^{127}.
```

`Nat` does not admit variable holes. An authorized whole-`Pattern` hole can still
carry a repetition term containing native integer bounds. Such structural inputs
must pass the declared bounds checks before evaluation can produce a Boolean.

## Named-rule correspondence

Every rule name below refers to the linked inline declaration. A suffix family
such as `SmartAlt*` denotes its explicitly enumerated constructor cases, not an
ordered wildcard rule in the implementation. The model may use a wildcard over
the finite core, but the DDL spells out disjoint constructor patterns.

| Declared rules or boundary | Existing model and exact correspondence |
| --- | --- |
| Pattern equations; `SmartAlt*`, `SmartConcat*`, `SmartStar*` | The reference `smart_alt`, `smart_concat`, and `smart_star` functions in [RegexGsltMatch](../../formal/rocq/runtime_grammar/theories/RegexGsltMatch.v) supply the oriented operations. [RegexGsltSmartMachine](../../formal/rocq/runtime_grammar/theories/RegexGsltSmartMachine.v) proves `smart_machine_step_preserves_meaning` and `declared_alt_computes_reference`, `declared_concat_computes_reference`, `declared_star_computes_reference`. Executable smart rewrites implement these operations; normalization does not saturate the declared equation set. |
| `SmartAltCompare`, `SmartAltSame`, `SmartAltDifferent` | `AltCheckEqual` and `AltDecideEqual` in the Smart model correspond to the existing `exact_term_eq` intrinsic followed by separate native-flag branches. Equal patterns return the original operand; distinct patterns construct `PAlt`. |
| `NullableFail/Epsilon/Literal/Any/Star/Alt/Concat/Return`; `NullableAltLeft/False/True`, `NullableConcatLeft/False/True` | [RegexGsltNullableMachine](../../formal/rocq/runtime_grammar/theories/RegexGsltNullableMachine.v): `nullable_machine_step`, `nullable_machine_step_preserves_meaning`, `nullable_step_decreases_exact_remaining_work`, and `declared_nullable_machine_computes_reference`. Ordered left/right continuation frames realize disjunction and conjunction without interchanging operands. |
| `DerivativeFail/Epsilon/Literal/Any/Alt/Concat/Star/Return`; derivative continuation returns, `DerivativeSmartStep/Done`, `DerivativeNullableStep/True/False` | [RegexGsltDerivativeMachine](../../formal/rocq/runtime_grammar/theories/RegexGsltDerivativeMachine.v): `derivative_machine_step`, `nullable_step_lifts_to_derivative`, `smart_step_lifts_to_derivative`, `derivative_core_completes`, and `completed_derivative_cannot_misreport`. Concatenation retains the original left operand for nullable and the original right operand for the product/right derivative. Star concatenates the derivative of its body with the smart star of the original body. |
| `DerivativeCompare`, `DerivativeSame`, `DerivativeDifferent` | The derivative model's `CompareLiteral` and `DecideLiteral` use scalar equality. The source realizes that comparison through `exact_term_eq` on admitted singleton text and branches on native `Flag`; equality yields `PEpsilon`, inequality yields `PFail`. |
| `ElaborateFail/Epsilon/Any/Group/Alt/Concat/Star/Plus/Optional/Repeat/Return` and corresponding frame returns; `ElaborateSmartStep/Done`, `ElaborateRepeatStep/Done` | [RegexGsltSurfaceMachine](../../formal/rocq/runtime_grammar/theories/RegexGsltSurfaceMachine.v): `surface_machine_step`, `surface_evaluation_returns_reference`, `declared_surface_computes_reference`, and `completed_surface_cannot_misreport`. Plus uses Star then Concat; Optional uses Alt with Epsilon; Repeat receives the already elaborated body. Grouping changes no pattern denotation. |
| `ElaborateLiteral`; `ElaborateScalarStart/Read/Admitted`; `DerivativeScalarStart/Read/Admitted` | [RegexGsltNativeAdmission](../../formal/rocq/runtime_grammar/theories/RegexGsltNativeAdmission.v): `scalar_admission_is_exact`, `scalar_administration_strictly_decreases`, and `scalar_read_decide_admits_exactly_singletons`. Source reads at byte offset zero, compares the entire original text with the returned singleton, and proceeds only on native true. Empty or multiple-scalar inputs cannot manufacture a negative nullable or derivative answer. |
| `RepeatCheckLower/ReachedLower/BelowLower`, `RepeatCheckRequiredUpper/ReversedBounds/AppendRequired/IncrementRequired`, `RepeatCheckOptionalUpper/ReachedUpper/BelowUpper/IncrementOptional`; `RepeatAppendStep`, `RepeatProductStep/Done`, `RepeatAlternativeStep`, `RepeatFinishStep/Done` | [RegexGsltRepeatMachine](../../formal/rocq/runtime_grammar/theories/RegexGsltRepeatMachine.v): `repeat_machine_step`, `declared_repeat_computes_reference`, `completed_repeat_cannot_misreport`, and `reachable_repeat_controls_are_valid`. Lower is checked before upper; reversed bounds return `PFail`. Required and optional accumulation retain the reference's ordered, right-nested construction. |
| `RepeatInitialize`, `RepeatAdmitBounds`, and the additional `RCheckUpper` stage | [RegexGsltRepeatAdmission](../../formal/rocq/runtime_grammar/theories/RegexGsltRepeatAdmission.v): `repeat_source_step_simulation`, `source_repeat_run_simulation`, `admitted_source_repeat_computes_reference`, and `completed_source_repeat_requires_admitted_bounds`. This accounts for the source administration around the core Repeat machine. Native admission proves `checked_add_zero_admits_exactly_native_naturals`, `checked_add_one_is_nat_successor`, `required_native_increment_fits`, and `optional_native_increment_fits`. |
| `StartNullable`, `NullableSurfaceStep/Done`, `NullableCoreStep/Done` | Source composition first runs surface elaboration, then nullable, then returns `DoneBool`. Each `Step` lifts one submachine transition; each `Done` passes its completed result to the next stage. The component completion theorems justify this inspected composition, not an automatic theorem about parsing/compiling the source file. |
| `StartDerivative`, `DerivativeSurfaceStep/Done`, `DerivativeCoreStep/Done` | Source composition first admits the scalar, then elaborates the surface pattern, runs the core derivative, and returns `DonePattern`. The same single-step lifting and completed-result handoff apply. |
| Declared `nullable`/`derivative` actions and `Nullable`/`Derivative` observations | Nullable's only action terminal is `DoneBool`; derivative's is `DonePattern`. `SDone`, `NDone`, `DDone`, `EDone`, and `RDone` are local submachine returns. The existing kernel's `normalization_terminal_state` enforces the declared root terminal. An observation selects its declared action, not another evaluator. |

## Concrete checks

### Application drivers

The [completed-frame model](../../formal/rocq/runtime_grammar/theories/RegexGsltApplicationMachine.v)
composes the existing nullable and derivative small-step machines. Its judgments
describe completed child frames, not a native operation replacing those
machines. The declaration's conditional `Step` rules lift one child rewrite;
its `Done` rules hand off the completed child in the same order. The model was
compiled and separately kernel-checked before these driver rules were added.
This is a refinement of their control structure, not extraction of Rust or DDL
from Rocq, and not proof that any chosen finite runtime budget suffices.

| Declared driver | Completed-frame correspondence |
| --- | --- |
| `FullSurface`, `FullScan`, `FullDerivative`, `FullNullable` | Surface elaboration is reused once. `FullScanNext` consumes one original scalar and the completed derivative; `FullScanEnd` uses the completed nullable result. `full_scan_exact` and `full_scan_exists` relate the scan to the existing `full_match`. |
| `PrefixScan`, `PrefixDerivative`, `PrefixUnwind`, `PrefixNullable` | `PrefixLonger` gives a successful later endpoint priority. Only a failed later prefix permits `PrefixFallback` to inspect current nullability. `prefix_scan_exact` and `prefix_scan_exists` establish the reference longest-prefix result without selecting the first alternative. |
| `SearchScan`, `SearchPrefix`, `SearchAtEnd`, `SearchDone` | `SearchHere` accepts that longest prefix; `SearchLater` advances one original scalar only after a complete miss. `search_scan_exact` and `search_scan_leftmost_longest` establish the two priorities. The source retains absolute byte cursors and the final byte length for slicing. The existing application and intrinsic cursor laws supply the separate scalar/byte correspondence. |
| `RenderEval`, `RenderLeft`, `RenderRight`, `RenderJoining` | `RenderAppend` completes the left template before the right, preserving ordered concatenation. `render_exact` and `render_exists` cover empty, literal, whole-match, and nested append templates. `JoinPieces` invokes the existing generic ordered-text-list intrinsic. |
| `ReplaceSurface`, `ReplaceSearch`, `ReplaceRender`, `ReplaceSplice` | `replace_first_exact` fixes unchanged prefix, rendered replacement and unchanged suffix. A miss returns the original text. Search receives only original input, never replacement output. |
| `ReplaceProgress`, `ReplaceEmptyEnd`, `ReplaceJoin`, `ReplaceJoinEmpty` | `replace_all_refines_reference` and `replace_all_reference_realized` relate all four branches to `ReplaceAllPlanSpec`. A nonempty match advances to its end; an empty match copies one original scalar, except at the end where it emits once and stops. `empty_replacement_frame_strictly_progresses` proves that distinction; `replace_all_frames_complete` establishes finite mathematical completion. |

The [standalone Rholang application](../../rholang-runtime/tests/fixtures/regex_gslt_application.rho)
embeds the same declaration, installs it through its URI capability, observes
qualified FLTs with structural `Text` holes, and matches qualified result FLTs.
It also uses the declared `FullMatch` predicate role directly in `where`.
The source-parsing test checks that its embedded module is byte-identical to
the service fixture. This mirror makes the application self-contained; it must
be updated together with the service fixture. Node execution, guard refusal and
funding/authority checks remain independent integration evidence.

The added focused tests are:

- `practical_regex_gslt_full_match_search_and_replacement_application_matrix`:
  13 whole-text matches, six searches and eight replacements, including UTF-8
  byte offsets, longest-alternative selection, whole-match rendering, empty
  Unicode progress and the final empty match after a nonempty one.
- `practical_regex_gslt_application_limits_refuse_without_partial_results`:
  measured exact, one-less and zero work allowances plus cancellation for match,
  search and empty-match replacement. A refusal has no successful result prefix.
- `practical_regex_gslt_full_match_result_is_controlled_by_the_declared_driver`:
  independently installs a changed terminal rule and checks that both the
  full-language commitment and observed full-match result change.
- `practical_regex_gslt_application_contains_the_checked_declaration_and_parses_once`:
  one generated host parse of the entire ordinary application, not separate
  parsing of its inline declaration.

These new tests specify concrete validation obligations; this documentation
does not assert their results before they have been run.

### Nullable and derivative foundations

The [installed-language tests](../../rholang-runtime/src/language_install/tests/regex_gslt.rs)
cross the generated Rholang parser, installation, FLT construction, and the
shared semantic kernel. Their distinct purposes are:

- `practical_regex_gslt_executes_declared_rules_through_the_generated_rholang_entrypoint`:
  26 nullable/derivative cases, including all eleven surface forms, Unicode,
  zero/equal/reversed repetition cases represented in the fixture matrix, and
  complete structural/semantic output equality. This is not a byte-for-byte
  protobuf assertion.
- `practical_regex_gslt_declared_rule_controls_observation`: change exactly the
  `NullableAny` right-hand side in a separate application input, install both
  specifications, and check opposite complete observations and distinct language
  owners. The modified theory deliberately has different semantics; it is not
  claimed to satisfy the reference regex specification. There is no rewriting or
  reparsing of an installed declaration.
- `practical_regex_gslt_structural_repeat_bounds_preserve_nat_hole_policy`:
  whole-Pattern fills with bounds `(0,2)` and `(2,2)` return the expected nullable
  result; `(-1,2)` and `(0,-1)` yield `StuckNonterminal`, not `DoneBool(false)`.
  Nat's prohibition on variable holes is retained.
- `practical_regex_gslt_scalar_holes_admit_singletons_and_refuse_other_text`:
  concrete one-, two-, three-, and four-byte UTF-8 singleton inputs, empty and
  multiple-scalar refusals, and zero-work refusal for both operations.

The two declaration/bounds tests compare complete output `Par` values using the
existing exact `Ord` comparison, including metadata. `Par`'s semantic `PartialEq`
alone does not establish metadata equality.

The [kernel tests](../../dovetail-runtime/src/semantic_transition_kernel.rs)
exercise `execute_intrinsic` directly. In
`closed_intrinsic_checked_nat_add_preserves_maximum_and_refuses_overflow`, the
eight operand pairs are `(0,0)`, `(MAX,0)`, `(MAX-1,1)`, `(MAX,1)`, `(1,MAX)`,
`(MAX,MAX)`, `(-1,0)`, and `(0,-1)`, where `MAX` means `i128::MAX`. Successful
cases check the exact integer and intrinsic receipt; overflow and negative
operands yield no relation result. The adjacent intrinsic tests retain Unicode,
boundary, cancellation, and resource-refusal checks. No enormous repetition is
executed merely to reach a machine-width boundary.

The [quantifier matrix](../../rholang-runtime/src/language_install/tests/regex_quantifiers.rs)
separately checks all sixteen forbidden adjacent quantifier pairs, all sixteen
grouped constructor trees with ordered bounds, binary precedence, and the public
parse-result boundary. [Postfix admission](runtime-lexical-lattice.md#nonassociative-postfix-declarations)
describes its generalized rule and scoped proof.

## What the evidence establishes

The existing Rocq models have been compiled and separately kernel-checked;
their unchanged sources and recorded evidence predate this validation-only
checkpoint. Source correspondence is
inspected and exercised by the named tests; Rust and DDL are not extracted from
these proofs. In particular:

- Core-machine composition applies to initialized reachable executions over
  elaborated patterns, not arbitrary forged internal `Computation` states,
  counter constants, or surface constructors injected into core frames.
- Scalar-sequence proofs do not certify Rust UTF-8 primitives or the reflected
  native codec. Concrete codec, intrinsic, and scalar-hole checks cover those
  implementation boundaries.
- Finite mathematical completion does not imply completion within an arbitrary
  configured kernel budget. Exhaustion remains a distinct refusal, not a Boolean.
- Administrative erasure proves semantic-control correspondence. It never erases
  work charges or receipts. Model transition measures are not parser weights,
  semantic resource grades, validator funding, or memory bounds.
- These checks do not prove global parser completeness, all generated-parser
  parity, full Rust correctness, or delivery through the public node.

Reproduction uses the named test filters in `rholang-runtime` (features
`rholang-runtime,bench-naive-baseline`, with default features disabled) and
`dovetail-runtime`. Run heavy checks serially with explicit memory and swap
limits; retain their command output under `target/verification/`. Both `coqc`
and a separate `coqchk` invocation are needed for fresh formal evidence; an
empty silent-check log alone is not evidence of a successful exit status.
