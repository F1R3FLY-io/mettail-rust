# Complete Module and Theory surface for MeTTaIL declarations

Status: design proposal for Greg and Mike's review. The syntax in this document is **not yet implemented**. The full-field spelling below is a mapping exercise, **not an accepted requirement to add every displayed builder**. The final surface must extend their existing `Module`/`Theory` declaration style only where the established builders cannot express the required interface; it does not define another host language or replace the canonical data representation.

The immediate motivation is the three `Data({...})` blocks in the [Regex GSLT application](../../../rholang-runtime/tests/fixtures/regex_gslt_application.rho). They currently carry (1) sorts, carriers, and literal tokens, (2) operator binding metadata, and (3) typed rewrites, rights, OSLF actions and observations, and limits. The readable `Terms`, `Equations`, and `Rewrites` around them already use Greg and Mike's style. The design obligation is a lossless route to **every admitted authoring field**, while retaining `Data` as the exact programmatic form; it does not imply one new syntax builder per field.

The authoritative sources have different jobs: `MeTTaIL/GSLT/src/main/bnfc/metta_venus.cf` is the **BNFC reference for a readable token-regex surface**; `f1r3node-rust-module-syntax/module-syntax/documentation/mettail-ddl-and-modules-2026-08-19.md` supplies **Greg and Mike's `Module`/`Theory`, `Types`, and judgment-form `Terms` structure**. Their document leaves retention of BNFC pragmas, including `token` and `position token`, open in §9.4. This proposal adopts a **BNFC-inspired**, not byte-for-byte BNFC-compatible, token declaration form inside the module structure. The established PraTTaIL regex compiler retains its semantics; similarity of spelling does not import BNFC's character classes or every BNFC operator. The [BNFC LBNF reference](https://github.com/BNFC/bnfc/blob/master/docs/lbnf.rst#lexer-definitions) documents the inspiration. Current implementation boundaries are the generated [Rholang specification](../../../languages/src/rholang.rs), [authoring schema](../../../mettail-elab/src/schema.rs), [canonical language core](../../../grammar-core/src/language_core.rs), and [runtime lexer-image compiler](../../../prattail/src/runtime_backend.rs).

## Terms and architecture

The *host* is the one Rholang language parsed by the generated frontend. A *theory* is an immutable language definition; it is not an installed parser or an authority. A *guest term* is parsed under an explicitly selected installed-language handle. `Data` denotes a structurally parsed Rholang value, not text passed to another DDL parser. A *carrier* specifies a native value representation; an ordinary theory constructor is still a distinct structural term. OSLF is the existing theory/action/observation layer. FLT means foreign-language term. The proposed `token Name Reg;` expressions specify **lexer tokens** using PraTTaIL regex semantics; they are not the Regex guest language being specified by the application.

![Proposed authored-to-installed-language flow](figures/module-ddl-full-surface-flow.svg)

The declaration path is one-way and structural: generated host AST, typed declaration AST, canonical value and `LanguageCore`, then the existing lexer/WPDA and semantic-image compilers. Exact-core `Data` enters at the canonical-value boundary. Neither route grants rights; installation intersects requested rights with an independent capability grant.

## Candidate full-field Regex spelling

This complete *section inventory* shows how the fields in the three current Regex `Data` blocks could be expressed without adding a builder for every canonical field. It is deliberately exhaustive, **not the minimum form required to declare a module or theory**. The existing `Exports` builder is extended with distinctly tagged `effect`, `operation`, and `observation` entries; its existing category-export and rename entries retain their meaning. Requested rights remain installation policy rather than a `Theory` attribute. `Options` owns optional lexer, parser, and semantic controls, including semantic limits. The two lexical declarations use a **BNFC-inspired `token Name Reg;` form**, retained inside the proposed `Terms` builder. They are not an invented `Literals { Category ::= Reg => carrier … }` language. `Types` carries the separate canonical carrier and variable-admission metadata. The short rewrite sample illustrates the rule grammar; the migration rule in [Typed rules](#typed-rules-and-native-values) applies to every remaining rewrite in the fixture. Each form shown is proposed syntax, not an assertion that the current parser accepts it.

```text
Module RegexGSLT {
  Theory Regex() {
    Types {
      data Pattern;
      data Computation;
      data NFrames;
      data DFrames;
      data EFrames;
      data MatchResult;
      data ReplacementTemplate;
      data PrefixResult;
      data Scalar = String;
      data Text = String;
      data Bool = bool;
      data Flag = bool;
      data Nat = BigInt;
      data Grade = BigInt;
    }

    Terms {
      token Scalar [A-Za-z0-9\u{80}-\u{10FFFF}];
      token Nat [0-9]+;

      PAlt . p:Pattern, q:Pattern
        |- p "|" q : Pattern left prefix(10);
      PConcat . p:Pattern, q:Pattern
        |- p q : Pattern left prefix(20);
      PStar . p:Pattern
        |- p "*" : Pattern nonassoc prefix(30);
      PPlus . p:Pattern
        |- p "+" : Pattern nonassoc prefix(30);
      POptional . p:Pattern
        |- p "?" : Pattern nonassoc prefix(30);
      PRepeat . p:Pattern, lo:Nat, hi:Nat
        |- p "{" lo "," hi "}" : Pattern nonassoc prefix(30);
    }

    Rewrites {
      FullReadEnd(p:Pattern, t:Text, i:Nat):
        if intrinsic utf8_at_end(t, i) => (b:Flag) then
          (FullScan p t i) ~> (FullAtEnd b p t i);

      FullAdvance(p:Pattern, t:Text, i:Nat):
        if intrinsic utf8_scalar_at(t, i) => (c:Scalar, j:Nat) then
          (FullAtEnd false p t i)
            ~> (FullDerivative (DEval c p (DNil)) t j);
    }

    Exports {
      effect Pure : pure requires {} emits {};

      operation "full-match" : (Computation) -> Computation
        via rewrite StartFullMatch
        effect Pure requires { Reduce } grade Grade
        normalize Computation until { DoneBool }
        branching deterministic;
      operation "search" : (Computation) -> Computation
        via rewrite StartSearch
        effect Pure requires { Reduce } grade Grade
        normalize Computation until { DoneMatch }
        branching deterministic;
      operation "replace-first" : (Computation) -> Computation
        via rewrite StartReplaceFirst
        effect Pure requires { Reduce } grade Grade
        normalize Computation until { DoneText }
        branching deterministic;
      operation "replace-all" : (Computation) -> Computation
        via rewrite StartReplaceAll
        effect Pure requires { Reduce } grade Grade
        normalize Computation until { DoneText }
        branching deterministic;
      operation "nullable" : (Computation) -> Computation
        via rewrite StartNullable
        effect Pure requires { Reduce } grade Grade
        normalize Computation until { DoneBool }
        branching deterministic;
      operation "derivative" : (Computation) -> Computation
        via rewrite StartDerivative
        effect Pure requires { Reduce } grade Grade
        normalize Computation until { DonePattern }
        branching deterministic;

      observation FullMatch : Computation via "full-match"
        predicate CallFullMatch
        accepts (DoneBool (BTrue))
        rejects (DoneBool (BFalse));
      observation Search : Computation via "search";
      observation ReplaceFirst : Computation via "replace-first";
      observation ReplaceAll : Computation via "replace-all";
      observation Nullable : Computation via "nullable";
      observation Derivative : Computation via "derivative";
    }

    Options {
      Semantics {
        Limits {
          max_term_nodes = 16384;
          max_proof_nodes = 16384;
          max_frontier = 256;
          max_steps = 10000000;
          max_grade_bits = 128;
        }
      }
    }
  }

  theory Regex()
}
```

### What the public interface and options mean

`Module` groups reusable declarations and their composition. `Terms`, `Equations`, and `Rewrites` specify the object language. `Exports` specifies what callers may name and how a named operation is executed and observed. `Options` groups operational controls rather than placing lexer, parser, or semantic settings beside the theory's defining rules. No additional block is mandatory for a syntax-only theory: its canonical action, observation, and effect lists remain empty, and its limits retain their bounded defaults.

| Surface clause | Canonical role | Why it appears in this example |
|---|---|---|
| `Rewrites` | Individual directed transitions, such as `StartFullMatch` and `FullAdvance`. | The theory defines reduction rules. A rule alone neither names a public operation nor grants permission to execute one. |
| `Exports { effect Pure ...; }` | A checked `EffectDeclV1`, not executable host code or a capability grant. | The predicate operation must name a declared pure effect with no emissions. The one declaration is shared by several operations. |
| `Exports { operation "full-match" ...; }` | A checked `SemanticActionV1` with a name, signature, entry rule, effect/right/grade contract, and execution policy. | The public operation starts at `StartFullMatch` and normalizes through applicable rewrites until `DoneBool`; it does not duplicate those rewrites. |
| `Exports { observation FullMatch ...; }` | A checked `ObservationDeclV1` naming an operation and interpreting its result. | The predicate entry states which completed guest terms accept or reject a `where` guard; no truthiness is inferred from names. Multiple observations may refer to one operation. |
| `Options { Semantics { Limits { ... } } }` | Checked `TheoryLimitsV1` bounds on rule work, proof/frontier size, grade size, and output. | The example preserves the existing fixture's stricter bounds; omission uses canonical defaults. Exhaustion does not fabricate a result or Boolean `false`. |

Within an exported `operation`, `via rewrite` selects its entry transition; `effect` and `requires` state checked effect and right requirements; `grade` names the resource-grade sort; and `normalize ... until` plus `branching` selects the existing normalization policy and its result multiplicity. These clauses describe how the named operation uses declared rules; they are not additional rewrite bodies. Distinct `effect`, `operation`, and `observation` entry prefixes preserve the existing unprefixed category-export and category-rename forms and make mixed `Exports` blocks structurally unambiguous.

Requested rights are a separate installation policy, outside `LanguageCoreV1` and its grammar/theory fingerprints. Omitting that request uses the current native-FLT default set (`Parse`, `Construct`, `Match`, `Observe`, `ReflectAst`, `Reduce`), equal to the fixture's explicit list. An explicit empty request instead requests no rights. Neither form grants authority: installation intersects the request with an independent host grant.

### Which fields need additional syntax?

Greg and Mike's existing `Terms`, `Equations`, and named `Rewrites` suffice to state constructors, equality, and the directed reduction relation. They do **not** uniquely determine an external operation contract: the same named rewrite could be a one-step operation or the entry to normalization, and normalization requires an explicit terminal set and branching policy. `Exports` currently exports and renames *categories only*; the proposed tagged `operation` entry extends that existing interface builder while preserving category-export behavior. It elaborates the existing canonical action record from a named rule and its checked sorts. No separate `Actions` builder is required.

Likewise, `Terms` can declare guest Boolean constructors and `Rewrites` can reduce to them, but their names alone do not authorize the host to treat arbitrary terms as true or false. The current `FullMatch` result uses a guest `Computation` term, so an explicit checked result interpretation appears as an `observation` entry in `Exports`, not as a standalone block. Non-pure effects cannot generally be inferred from rewrite syntax alone: such inference would require a checked effect signature for every intrinsic and a sound compositional effect analysis. The present core instead requires named effect metadata, especially a declared pure, no-emission effect for a predicate operation. A tagged `effect` entry in `Exports` carries that checked shared contract without adding a top-level `Effects` builder. Semantic limits already have canonical bounded defaults; any explicit override belongs under `Options.Semantics.Limits`, not at the Theory-builder level.

**Design direction:** preserve the existing Theory algebra and rule builders; extend `Exports` for checked public operations, effects, and observations; group all lexer, parser, and semantic controls under `Options`; and keep requested rights at the installation boundary. Before implementation, prove that structural elaboration reproduces the canonical action, observation, effect, limit, and requested-rights values without inferred grants, truthiness, or execution strategy. No new regex or rewrite semantics are authorized by this surface-design choice.

Thus a `fullMatch(...)` guest term is parsed under the installed grammar; the `FullMatch` observation invokes the `full-match` action, which starts and normalizes through `Rewrites`; the observation classifies completed terms. Requested rights, checked effects, and `Options.Semantics.Limits` constrain that path independently. `Equations` express equality; a normalizing action follows directed rewrites, not equations. The current schema can separately name an equation as the entry of a one-step action, but that is not how the Regex actions above are defined.

`token Scalar Reg;` and `token Nat Reg;` deliberately resemble BNFC token declarations, but `Reg` uses all existing PraTTaIL lexer-regex forms. For these two names, the typed `Types` declarations determine the existing native decoder deterministically: `String` maps to the checked `carrier str` representation and `BigInt` to `carrier int`. That inference is a proposed *elaboration rule*; it must be proved equal to the fixture's explicit `literals[].eval` values. A nondefault decoder remains an explicitly typed declaration, never an inference from the spelling of `Scalar` or `Nat`. Unlike BNFC's `["abc"]` enumeration, the unquoted `[A-Z]` character class uses PraTTaIL's existing range semantics. The two declarations lower to the fixture's unchanged runtime patterns `[A-Za-z0-9\u{80}-\u{10FFFF}]` and `[0-9]+` (the JSON source escapes each backslash), with no lexer-language or token-priority change.

### Why a BNFC-inspired token regex, not `regex("…")`

`Scalar ::= regex("[A-Za-z0-9\\u{80}-\\u{10FFFF}]")` is not the requested BNFC-style surface: it hides the pattern inside a string and blurs the distinction between a token declaration and a term rule. This proposal parses the BNFC-shaped `Reg` expression **as a structural part of the generated Rholang DDL AST**, then lowers supported expressions to the existing canonical `TokenPattern::Regex` string. For example:

```text
Terms {
  token Identifier [A-Za-z_][A-Za-z_0-9]*;
  position token MarkedIdentifier [A-Za-z_]+;
}
```

This is intentionally close to BNFC declaration syntax, not a claim of complete BNFC compatibility. `position token` is a proposed compatible-looking form but needs an explicit occurrence/position field in the canonical authoring schema, which does not currently have one; it must not be claimed as implemented by the present `TokenDecl`. Richer optional metadata—category/decoder override, priority, mode push/pop, and stream—belongs under `Options.Lexer.TokenOptions`, keyed by a previously declared token. It does not alter `token Name Reg;`. For example, `Options { Lexer { TokenOptions { Identifier : category Name, priority 10, stream Main; } } }` lowers to the existing token fields. `position token` requests source-location observation; it never turns a token's spelling into an authority.

The proposed `Reg` surface grammar exposes **every existing PraTTaIL lexer-regex form**, including classes, escapes, and bounded repetition. The following is a precedence sketch; `Escape` and `ClassBody` denote the existing PraTTaIL lexical forms, not new regex operations:

```text
Reg       := Reg1
Reg1      := Reg1 "|" Reg2 | Reg2
Reg2      := Reg2 Reg3 | Reg3
Reg3      := RegAtom Quantifier?
Quantifier := "*" | "+" | "?" | Bound
Bound     := "{" n "}" | "{" n "," "}" | "{" n "," m "}"
           | "{" "," m "}" | "{" "," "}"
RegAtom   := Literal | Escape | "." | "[" ClassBody "]" | "(" Reg ")"
```

The grammar above specifies **what the author writes**, not a second regex semantics. The generated Rholang parser must structurally recognize these forms with source occurrences; the adapter emits the same canonical `TokenPattern::Regex` pattern under the current character profile. The BNFC influence is the `token Name Reg;` declaration shape, not additional BNFC-only regex atoms or semantics. Full PraTTaIL lexer-regex coverage is the required surface contract:

| Existing lexer feature | Required authored form |
|---|---|
| Literal characters and escaped metacharacters | Bare literals and every escape currently accepted by PraTTaIL, including `\.`, `\\`, `\[`, `\{`, `\/`, and `\$`. |
| Control escapes and shorthand classes | `\n`, `\r`, `\t`, `\d`, `\w`, `\s`, `\D`, `\W`, and `\S`, under the same character profile as the existing lexer. |
| Unicode escapes and properties | `\u{03B1}`, `\u03B1`, `\U000003B1`, `\p{XID_Start}`, `\P{White_Space}`, and every property name the existing lexer accepts. |
| Character classes | `[abc]`, `[a-z]`, `[α-ω]`, `[\u0391-\u03C9]`, `[^abc]`, mixed ranges, and the existing valid class escapes, shorthands, and properties. |
| Wildcard, grouping, concatenation, and alternation | `.` with its existing newline exclusion, `(...)` as noncapturing grouping, adjacency, and alternation as in <code>a&#124;b</code>. |
| Repetition | `*`, `+`, `?`, `{n}`, `{n,}`, `{n,m}`, `{,n}`, and `{,}`, with PraTTaIL's existing bounds and nullable-token checks. |

The generated host parser must retain regex punctuation and escapes in a typed `Reg` AST; it may not hand an opaque DDL substring to another DDL parser. A top-level semicolon terminates `token Name Reg;`; a literal semicolon can be written `[;]` or `\u{3B}`. The full feature matrix needs source-to-canonical-pattern tests and installed-lexer differential tests, including class ranges, Unicode, negation, all bounded forms, invalid escapes, and declaration-delimiter cases. The existing lexer still rejects backreferences, lookaround, lazy quantifiers, named groups, and anchors; the new syntax must not pretend to support them. These are requirements to preserve the current supported surface, not to change its meaning.

BNFC general subtraction is outside this BNFC-inspired surface because it is not an existing PraTTaIL lexer-regex feature. That boundary is not an invitation to invent another regex evaluator or change the lexer. PraTTaIL's [existing regex compiler](../../../prattail/src/automata/regex.rs) handles target patterns with its stack-safe Thompson NFA, alphabet partitioning, subset construction, and DFA minimization. The [existing runtime compiler](../../../prattail/src/runtime_backend.rs) and [lexer-image verifier](../../../grammar-core/src/image.rs) continue to consume `TokenPattern::Regex` unchanged. No new canonical `Reg` arm, DFA-product operator, or alternative regex semantics is part of this proposal. The host grammar must distinguish regex punctuation from enclosing DDL syntax by its grammar state, not global character guessing.

Nullable and empty token languages remain rejected. Existing acceptance, priority, longest-match, mode, and alternative-token rules remain unchanged. Unicode scalar ranges use PraTTaIL's current Unicode path. Compilation and lowering have explicit size/work bounds and do not introduce recursive processing.

## Typed rules and native values

Existing simple Greg/Mike `Equations` and `Rewrites` remain valid. A named rule may add typed parameters before the colon. Those parameters become canonical `context` entries. Premises are ordered; each intrinsic output is introduced after its inputs, has a declared sort, and is available only to later premises and the conclusion. Supported premise forms are freshness (`x # y` and `x # ...rest`), a rewrite step, a named judgment/relation, bounded universal premise, a checked guard, and a closed intrinsic call. Intrinsics are drawn only from the installed closed ABI; for the Regex fixture that set is `exact_term_eq`, `utf8_at_end`, `utf8_scalar_at`, `utf8_slice`, `checked_nat_add`, and `utf8_concat_many`. A source string cannot register a new host function.

Native literals are distinct from constructors:

```text
Rewrites {
  RenderEmpty:
    (RenderEval (ReplacementEmpty) m) ~> (RenderDone "");
  RenderRightDone:
    (RenderRight l (RenderDone r))
      ~> (RenderJoining (JoinPieces { l, r }:Text));
  ReplaceAllPositive(p:Pattern, r:ReplacementTemplate, t:Text):
    (ReplaceProgress false p r t) ~> (ReplaceCompute p r t);
}
```

The last rule above is only a *syntax illustration*, not a replacement for the fixture's differently shaped `ReplaceAllPositive` rule. Bare `0`, `true`, and `""` map to canonical native `i128`, `bool`, and `str` literal nodes respectively; explicit `literal(i128, 0)`, `literal(bool, true)`, and `literal(str, "")` remain available when the carrier must be stated. `(BTrue)` and `(BFalse)` remain ordinary guest constructors, **not** native `true` and `false`. A typed collection such as `{ l, r }:Text` maps to the canonical typed-collection AST; its collection kind comes from the expected sort, not an inferred arbitrary host collection.

The complete rule-AST surface must cover variables, constructor applications, one/many binders, substitution, ordered and unordered collections with optional remainder, typed collections, collection map/zip, native literals, and the currently accepted legacy substitution form. Existing placement, scoping, and profile restrictions remain; presenting a legacy form does not make it executable in a profile that currently rejects it. Equations acquire optional names and typed contexts, while unnamed equations remain source-compatible. Equation premises retain their existing restrictions, including no illicit transition premise.

The authored `Terms` surface uses Greg and Mike's judgment arm `Label . bindings |- syntax : Category;`. A legacy BNFC arm `Label . Category ::= Items;`, if retained for import compatibility, is a distinct AST variant and must not be mistaken for the proposed **token-regex** syntax. Optional suffixes cover evaluation (`operator`, `carrier`, `handler`, or source requirement), `fold`/`step`, association, `prefix(n)`, sharing the preceding level, tier/bound/force, and documentation. Duplicated attributes are rejected. `prefix(n)` maps to the existing `prefix_bp` field even for a postfix rule; no new precedence convention is invented. Regex's explicit powers remain alternation 10, concatenation 20, postfix 30. Nonassociative postfix rejection and grouping behavior must remain unchanged.

## Remaining declaration families

The following table is the coverage contract for **all** top-level keys accepted by the [current schema](../../../mettail-elab/src/schema.rs), not merely fields used by Regex. The proposed surface does **not** assign a peer Theory builder to each schema key: public semantic records are tagged entries in `Exports`, and operational controls are nested in `Options`. Complex entries remain named and typed, not unvalidated free-form maps.

| Canonical field family | Proposed Theory syntax and exact obligation |
|---|---|
| `mettail`, `name` | Derived from the language profile and enclosing `Theory`; ordinary `Data` fragments still may not override them. |
| `types` | `Types` declares category name, optional native/collection/extern carrier, variable admission via `data`, collection delimiters, and refinement predicate. |
| `literals` | BNFC-inspired `token Category Reg;` inside `Terms` for a carrier-backed category; the `Types` carrier supplies the checked default decoder. An explicit typed decoder override covers the other native-evaluation variants. |
| `tokens` | The same `token Name Reg;` inside `Terms` for named tokens; `Options.Lexer.TokenOptions` attaches optional category/decoder, priority, push/pop, and stream without altering that declaration form. `position token` requires an additional canonical position field. |
| `modes` | `Modes` declares name, optional `raw`, and its ordered token declarations. |
| `sync` | `Sync` declares alignments and location tracking without changing stream membership implicitly. |
| `terms` | `Terms` preserves label, result sort, context, one of judgment syntax or BNFC items, evaluation, mode, association, `prefix_bp`, previous-level sharing, tier, and documentation. |
| `equations`, `rewrites` | `Equations`/`Rewrites` preserve names, contexts, ordered premises, and exact structural left/right ASTs. |
| `rights` | An explicit installation request, not a Theory builder. The installer grants no right without independent authority; omission uses the current native-FLT default request. |
| `oslf.effects` | Tagged `effect` entries in `Exports` preserve name, class, required effects/capabilities, and emitted effects. |
| `oslf.actions` | Tagged `operation` entries in `Exports` preserve ID, domain, codomain, entry transition, effect, effect class, required rights, grade, and execution plan. |
| `oslf.observations` | Tagged `observation` entries in `Exports` preserve name, action, result sort, and optional explicit predicate role. |
| `oslf.judgments` | `Judgments` preserves signature, exact/bounded decision mode, and ordered named rules/atoms. |
| `oslf.morphisms` | `Morphisms` preserves source/target and category, constructor, action, and grade mappings. |
| `oslf.interactive` | `Interactive` is a closed typed field block for cut, channel/datum/continuation sorts. |
| `oslf.continued` | `Continued` is a closed typed field block for continuation operators and checked witnesses. |
| `oslf.cost` | `Cost` is a closed typed field block for Cost(G) sorts, operations, laws, and witnesses. |
| `oslf.resource_projection` | `ResourceProjection` declares the checked semantic-grade-to-host-demand mapping; it grants no funding authority. |
| `oslf.checkers` | `Checkers` names a pre-installed ABI and limit profile; it cannot install code. |
| `oslf.limits` | `Options.Semantics.Limits` covers every accepted bound; omission retains the current default. |
| `guards` | `Guards` has typed predicate, connective, theory, channel, and join declarations with the current predicate subset and metadata. |
| `tree_invariants` | `TreeInvariants` declares named structural constraints and documentation. |
| `relations` | `Relations` preserves the legacy relation/rule schema only where its profile already permits it; it does not bypass `language/3` restrictions. |
| `options` | `Options` groups closed lexer, parser, generation, weighting, and semantic settings; parser recovery and semantic limits are nested closed blocks. The groupings lower to the existing canonical fields without changing their meaning. |
| `semantics`, `context`, `doc` | `Semantics`, `Context`, `Documentation` preserve these authored observations without making them executable code. |
| `extends`, `includes`, `mixins` | Separate builders preserve the resolver's different composition/projection/collision laws. |
| `exports`, `replacements` | Existing category-export/rename entries in `Exports` and existing `Replacements` retain their meaning. Tagged semantic entries in `Exports` use distinct syntax and checked cross-kind collision rules. |
| `core_schema`, `core` | Stay in closed exact-core `Data`; they are not presentation builders. |

Representative record spelling for the broader families is:

```text
Types {
  data Entries = Map(Key, Value)
    collection { open = "{"; close = "}"; sep = ","; key_val_sep = ":"; };
  data Positive = BigInt refine n:Nat where cmp(n, ">", 0);
}
Modes { Quoted raw { token CloseQuote ["]; } }
Options {
  Lexer { TokenOptions { Quoted.CloseQuote : pop; } }
  Parser { beam_width = auto; }
  Semantics { Limits { max_steps = 10000000; } }
}
Sync { align Main Auxiliary at {"\n"}; track Locations with Main; }
Judgments { J(A, B) decision exact { Rule: if K(x, y) then J(x, y); } }
Morphisms {
  M : "Source" -> "Target" {
    categories { A => B; }
    constructors { C => D; }
    actions { "a" => "b"; }
    grades { G => H; }
  }
}
Checkers { "checker-abi" limit_profile "profile"; }
```

The `Modes` example keeps the same `token Name Reg;` form inside a mode; `Options.Lexer.TokenOptions` supplies mode-stack behavior. The `Sync` example uses a BNFC-style sequence. Field blocks are closed and type-checked, not arbitrary host-code evaluation. The existing data-schema option keys are `beam_width`, `log_semiring_model_path`, `dispatch`, `emit_tests`, `emit_blockly`, `emit_simulator`, `parse_only`, `case_insensitive`, `unicode_normalization`, `reserved_keywords`, `contextual_keywords`, and `recovery`; the proposed nested grouping is surface organization, not a new interpretation of those keys. Recovery must include every current key: `skip_per_token`, `delete_cost`, `substitute_cost`, `insert_cost`, `swap_cost`, `max_skip_lookahead`, `deep_nesting_threshold`, `deep_nesting_skip_mult`, `shallow_depth_threshold`, `shallow_depth_skip_mult`, `low_bp_threshold`, `low_bp_skip_mult`, `collection_insert_mult`, `group_insert_mult`, `bracket_insert_mult`, `mixfix_substitute_mult`, `simulation_valid_mult`, `simulation_fail_penalty`, `beam_width`, `cascade_window`, `vpa_nesting_ceiling`, `adaptive_weight_threshold`, `deterministic_skip_discount`, `ambiguous_insert_discount`, and `max_recovery_depth`.

The complete guard/tree language needs dedicated structural productions for the existing predicate tags, not a string hidden in `guard(...)`: positive/negative calls, finite domains, bounded quantification, linear constraints, equality/inequality, comparisons, conjunction/disjunction/negation/implication, AC matching where admitted, and tree root/parent/child/subtree/category/label references. Each surface production lowers to exactly one admitted canonical tag; unsupported modal or profile-specific forms remain rejected.

## Boolean values and predicate evidence

The current Regex fixture declares `BTrue`/`BFalse` as constructors in the `Bool` sort. `Bool = bool` admits native Boolean carrier values but **does not equate** those constructors with Rholang `true`/`false`. The application currently matches `doneBool(yes)` and then explicitly sends `true`. Its `FullMatch` predicate role separately maps checked `DoneBool(BTrue)` and `DoneBool(BFalse)` to accept/refute evidence for a guard. An unexpected, conflicting, exhausted, or missing result is undetermined, not `false`.

### How `fullMatch` guards a receive

The [actual application](../../../rholang-runtime/tests/fixtures/regex_gslt_application.rho) uses the ordinary `where` clause, with an explicitly handle-qualified FLT:

```text
for(@text <- @"regex.guard.input"
    where language:Computation`fullMatch(a(b|c)+,${text:Text})`) {
  @"regex.guard"!(text)
}
```

`language` is an opaque installed handle in lexical scope. The qualified guest parser constructs `CallFullMatch(Pattern, Text)` in the declared `Computation` sort. The predicate role on observation `FullMatch` selects that input constructor, runs its checked `full-match` action through the shared semantic transition kernel, and compares **every** completed result against the declared closed `DoneBool(BTrue)` and `DoneBool(BFalse)` keys. It does not ask whether a term's name resembles `true`, nor does it coerce the guest `Bool` carrier to a Rholang Boolean. The classifications are:

| Checked result set | Guard evidence |
|---|---|
| Nonempty, uniformly `DoneBool(BTrue)` | `Sat` |
| Nonempty, uniformly `DoneBool(BFalse)` | `Unsat` |
| Empty, mixed, unexpected, exhausted, invalid, or unavailable | `DontKnow` or a typed refusal |

The RSpace communication commits only on `Sat` with a valid, still-live authority/commit receipt. `Unsat` does not match. `DontKnow` is fail-closed: it does not consume the datum or fire the continuation, but it is **not** a proof of `false`. The implementation boundaries are [predicate classification](../../../rholang-runtime/src/semantic_service/predicate.rs), [three-valued verdict algebra](../../../prattail/src/algebra_tower.rs), and [COMM-time guard policy](../../../rholang-runtime/src/guard_par_substrate.rs).

### What Boolean algebra is, and is not, present

`FullMatch` is *usable as a predicate* because its role gives a checked map from terminal guest terms into `Sat`, `Unsat`, or `DontKnow`. The verdicts use strong-Kleene conjunction, disjunction, and negation. For example, `Unsat and DontKnow` is `Unsat`, `Sat or DontKnow` is `Sat`, and `not DontKnow` remains `DontKnow`. This is **not** a two-valued Boolean algebra: excluded middle fails at `DontKnow` (`DontKnow or not DontKnow` remains `DontKnow`). The policy that blocks a receive on `DontKnow` is an operational admission decision, not a logical conversion from unknown to false. A safe collapse to native `bool` exists only for `Sat`/`Unsat`; `DontKnow` has no Boolean value.

The two guest constructors could represent the two elements of a Boolean algebra **only after** the theory declares Boolean operations and proves their total, closed, terminating/confluent truth tables on that constructor subset. The present Regex fixture declares no such general `and`/`or`/`not` algebra. For `FullMatch` specifically, a proof of total deterministic normalization into exactly one of the two declared terminal forms under adequate resources would make each successful observation two-valued; bounded exhaustion or invalid evidence still remains a third outcome. A first-class Rholang `bool` therefore needs the explicit projection below, not an inference from the `Bool` sort or from the guard policy.

![Checked FLT predicate and COMM-time admission](figures/module-ddl-predicate-flow.svg)

For first-class host values, add a separately versioned projection declaration and explicit observation operation:

```text
Projections {
  BooleanResult : Computation -> Rholang.Bool {
    (DoneBool (BTrue)) => true;
    (DoneBool (BFalse)) => false;
  }
}
Exports {
  observation FullMatch : Computation via "full-match"
    projects BooleanResult
    predicate CallFullMatch
    accepts (DoneBool (BTrue))
    rejects (DoneBool (BFalse));
  observation Nullable : Computation via "nullable" projects BooleanResult;
}
```

This is a **new canonical-schema and FLT-service feature**, not sugar over existing `predicate_role`. Existing `observe` still returns guest terms and receipts. An opt-in `observeValue` returns each checked guest result plus its projected host Boolean and receipt; it never elects a first result. Installation validates exact closed guest keys, unique rows, declared guest and host sorts, and authority to use the observation. Unmapped or inconclusive results fail explicitly. A later `Codecs` declaration may provide a proved, explicit bidirectional subset mapping for constructing `BTrue`/`BFalse` from Rholang Boolean inputs; it is not required for read-only observation and must not be inferred from the sort name. `ResourceProjection` remains exclusively about cost/funding and must not be overloaded for value conversion.

## Elaboration, identity, and authority laws

The generated Rholang grammar must emit typed `Ddl*` AST variants for each builder and BNFC `Reg` node. The existing structural DDL lowering then produces the canonical presentation value; the existing checked schema and composition machinery produce `LanguageCore`. There is no source substring extraction, host `Display` round-trip, or second DDL parser. The compiled lexer/WPDA and OSLF images remain derived and replaceable; the immutable language value remains authoritative.

The following laws are implementation requirements:

1. **Old-form preservation:** every previously admitted `Data` value decodes exactly as before. Closed exact-core `Data` still begins only at `Empty`, contains exactly `core_schema` and `core`, and cannot be mixed with presentation builders as an open fragment.
2. **Builder correspondence:** for each new declaration, structural elaboration equals its documented canonical fragment, including declaration order, optional-versus-present fields, native carrier spelling, names, and source occurrences.
3. **Core correspondence:** migrating a fixture yields the same admitted `LanguageCore`, including the same canonical regex-string patterns where applicable. No native `Reg` core arm or new regex semantics are introduced; if a surface form lacks an exact mapping, elaboration rejects it.
4. **No new authority:** syntax, `Data`, names, aliases, registry records, fingerprints, and reflected tags never act as handles or grants. Rights remain requested-versus-granted. Host handlers and checker ABIs are closed and separately authorized.
5. **No premature election:** token and parser ambiguity survives until admissible evidence resolves it; lexer priority and deterministic source order are explicit, not accidental effects of formatting.
6. **Bounds and stack safety:** parsing, AST lowering, regex algebra, core admission, image compilation, projection, and cleanup use the existing explicit-stack/resource-checked discipline. Exhaustion is a typed refusal, not a partial language or a Boolean negative.

One migration hazard is nonsemantic-looking identity change. Unnamed equations currently receive names derived from element identity, and each `Data` fragment consumes its own fragment identity. Splitting a fragment among builders can therefore change generated names and fingerprints. Add optional named equations and preserve old names where exact migration needs them; compare complete admitted cores and behavior before claiming parity. Operator power, intrinsic output order, predicate-role terms, and action terminal lists also must be compared exactly.

## Grammar and implementation plan

Braces delimit builders and semicolons terminate declarations. The generated host grammar distinguishes `token Name Reg;` from Greg and Mike's judgment-form term rules inside `Terms`, and both from ordinary Rholang process syntax. It also distinguishes regex alternation from Rholang process parallel composition. New keywords should be contextual where possible; making `char`, `digit`, or `token` globally reserved would be a Rholang regression. Action IDs may be quoted (`"full-match"`) because a hyphen must not be parsed as subtraction. Rule constructors stay parenthesized S-expressions. A native literal stays distinct from a constructor, and a typed collection's element annotation stays distinct from a result-sort annotation. Existing theory-algebra precedence, module imports, lexical scope, and full-expression extent remain unchanged.

Implementation should proceed as one reviewed contract, with these independently verifiable increments:

1. Freeze a schema-field/variant inventory and exact old/new fixture witnesses. Define the BNFC-inspired surface-to-PraTTaIL mapping and its rejection boundary before changing the parser.
2. Extend `languages/src/rholang.rs` with typed builders and the proposed BNFC-inspired `Reg` grammar; preserve generated AST occurrences and the existing parser hot path. Extend the structural DDL wire only where the authored declaration AST requires it.
3. Add categories, literal/token `Reg` surface forms, term metadata, and complete rule AST/premises. Lower accepted regex forms to existing canonical `TokenPattern::Regex` strings and reuse the existing PraTTaIL automata and semantic compiler without changing either one's semantics.
4. Extend the existing `Exports` builder with distinct checked effect, operation, and observation entries; place lexer, parser, and semantic controls under `Options`; keep requested rights at the installation boundary. Add the remaining genuinely declarative OSLF, guard, and composition forms without a redundant builder per canonical field. Preserve exact-core `Data` and current profile restrictions. Add the separately reviewed Boolean projection schema and opt-in service ABI.
5. Migrate the Regex fixture with no presentation `Data` blocks, retaining a canonical `Data` fixture as the oracle. Run property-based round trips, invalid-input tests, generated/static versus installed/runtime lexer/parser differential tests, full Regex semantic and FLT tests, and public-node entrypoint tests.

The proof model must cover builder-to-core correspondence; exact equivalence of each admitted surface regex to its emitted existing PraTTaIL pattern, including Unicode ranges and priority; explicit rejection of unmappable forms; declaration/handle capability separation; and projection/refusal laws. Tests must demonstrate that `a*?`, `a++`, and `a?+` remain rejected, grouping works, precedence is 10/20/30, `BTrue` differs from native `true`, and a failed or mixed observation never becomes a host `false`. Deep declarations and regexes must fail within admitted resource bounds, not overflow the process stack.

This proposal is intentionally a **surface and correspondence design**. It does not claim that the shown syntax or first-class Boolean projection currently exists or passes tests; it does not propose a BNFC difference backend or change PraTTaIL regex semantics.
