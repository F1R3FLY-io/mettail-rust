# PraTTaIL Data Flow

**Traces every data transformation from `LanguageSpec` input to `TokenStream` output.**

---

## Overview

The `generate_parser()` function in `lib.rs` delegates to `pipeline::run_pipeline()`,
which orchestrates a state-machine-driven pipeline. The pipeline extracts Send+Sync data
bundles from the `!Send` `LanguageSpec`, generates lexer and parser code as `String`
buffers, and performs a single `str::parse::<TokenStream>()` at the end to produce the
final output.

---

## Pipeline State Machine

The pipeline in `pipeline.rs` uses a `PipelineState` enum to track progress:

```
LanguageSpec
    │
    ▼
[Extract]  extract_from_spec()
    │       Separates LanguageSpec into Send+Sync bundles:
    │         LexerBundle  (grammar_rules, type_infos)
    │         ParserBundle (categories, bp_table, rule_infos, follow_inputs,
    │                       rd_rules, cross_rules, cast_rules)
    ▼
PipelineState::Ready { lexer_bundle, parser_bundle }
    │
    ▼
[Generate]  generate_lexer_code() + generate_parser_code()
    │         Produces complete lexer and parser as String buffers
    ▼
PipelineState::Generated { lexer_code: String, parser_code: String }
    │
    ▼
[Finalize]  concatenate + str::parse::<TokenStream>()
    │         Single parse of complete generated code string
    ▼
PipelineState::Complete(TokenStream)
```

### Why Send+Sync Bundles?

`LanguageSpec` is `!Send` because `RuleSpec.rust_code: Option<proc_macro2::TokenStream>`
wraps `Rc<()>` internally (in proc-macro context). The pipeline extracts all data that
code generation needs into `LexerBundle` and `ParserBundle`, which contain only owned
`String`, `Vec`, `BTreeMap`, and other Send+Sync types. This design enables future
parallelism even though the current implementation is sequential (rayon was tested and
rejected due to 81-197% regression under `taskset -c 0` — rayon's thread pool scheduling
overhead per `join` call (~30 μs) exceeded total codegen work for each phase, and under
single-core pinning the closures ran sequentially with added lock/queue overhead).

---

## Phase Diagram

```
LanguageSpec
    │
    │  Phase 1: Extraction and terminal analysis
    │  ============================================
    │
    ├───▶ extract_from_spec()
    │       │
    │       ├───▶ For each rule: collect terminals, detect infix/prefix/postfix/mixfix,
    │       │     build GrammarRuleInfo, InfixRuleInfo, RDRuleInfo, CrossCategoryRule, CastRule
    │       ├───▶ For each type: detect native types, build TypeInfo, CategoryInfo
    │       ├───▶ Build FollowSetInput projections (category + syntax only)
    │       ├───▶ analyze_binding_powers(infix_rules) → BindingPowerTable
    │       │
    │       ▼
    │     LexerBundle { grammar_rules: Vec<GrammarRuleInfo>, type_infos: Vec<TypeInfo> }
    │     ParserBundle { categories, bp_table, rule_infos, follow_inputs,
    │                    rd_rules, cross_rules, cast_rules }
    │
    │  Phase 2: Lexer code generation
    │  ================================
    │
    ├───▶ generate_lexer_code(lexer_bundle) → String
    │       │
    │       ├───▶ extract_terminals(grammar_rules, type_infos) → LexerInput
    │       │       { language_name, terminals: Vec<TerminalPattern>, needs: BuiltinNeeds }
    │       │
    │       ├───▶ build_nfa(terminals, needs) → Nfa
    │       │       │
    │       │       ├───▶ build_keyword_trie(nfa, fixed_terminals)
    │       │       │       Aho-Corasick prefix-sharing trie for all fixed terminals
    │       │       │       Single epsilon: global_start → trie_root
    │       │       │
    │       │       └───▶ build_ident_fragment / build_integer_fragment / etc.
    │       │               Builtin patterns connected via epsilon from global_start
    │       │
    │       ├───▶ compute_equivalence_classes(nfa) → AlphabetPartition
    │       │       256 byte values → ~15 equivalence classes
    │       │
    │       ├───▶ subset_construction(nfa, partition) → Dfa
    │       │       Powerset with HashMap state map
    │       │
    │       ├───▶ minimize_dfa(dfa) → Dfa
    │       │       True Hopcroft's with inverse transition map
    │       │
    │       └───▶ generate_lexer_string(dfa, partition, token_kinds) → String
    │               Token<'a> enum (zero-copy), Position, Range, ParseError,
    │               CHAR_CLASS table, lex<'a>() function, dfa_next/TRANSITIONS,
    │               accept_token<'a>(), is_whitespace()
    │
    │  Phase 3: Parser code generation
    │  =================================
    │
    ├───▶ generate_parser_code(parser_bundle) → String
    │       │
    │       ├───▶ compute_first_sets(rule_infos, categories) → FirstSets
    │       │       Fixed-point iteration, augmented with native literal tokens
    │       │
    │       ├───▶ compute_follow_sets_from_inputs(follow_inputs, ...) → FollowSets
    │       │       Fixed-point iteration over FollowSetInput records
    │       │
    │       ├───▶ build_dispatch_tables(rule_infos, categories, first_sets) → DispatchTables
    │       │
    │       ├───▶ analyze_cross_category_overlaps(categories, first_sets) → Overlaps
    │       │
    │       ├───▶ detect_grammar_warnings(rule_infos, categories, all_syntax)
    │       │       → Vec<GrammarWarning> (emitted at compile time)
    │       │
    │       ├───▶ detect NFA spillover categories
    │       │       categories_needing_nfa_spillover(dispatch_tables, rule_infos)
    │       │       → Vec<(category, token, Vec<(rule_label, f64)>)>
    │       │       Identifies dispatch tokens with 2+ rules after lookahead
    │       │       Orders alternatives by WFST TropicalWeight via nfa_alternative_order()
    │       │       Beam pruning: filter alternatives where weight > best + beam_width
    │       │       Sets TrampolineConfig.needs_nfa_spillover per category
    │       │
    │       ├───▶ write_parser_helpers(buf)
    │       │       expect_token, expect_ident, peek_token, peek_ahead
    │       │
    │       ├───▶ write_recovery_helpers(buf)
    │       │       sync_to, expect_token_rec, expect_ident_rec
    │       │
    │       ├───▶ For each RD rule: write_rd_handler(buf, rule) → PrefixHandler
    │       │
    │       ├───▶ For each category:
    │       │       write_pratt_parser(buf, config, bp_table, prefix_handlers)
    │       │         Pratt loop, prefix handler, infix_bp, make_infix,
    │       │         postfix_bp, make_postfix, mixfix_bp, handle_mixfix
    │       │
    │       ├───▶ For each category with cross/cast rules:
    │       │       write_category_dispatch(buf, category, cross_rules, ...)
    │       │
    │       ├───▶ For each category:
    │       │       generate_sync_predicate(buf, category, follow_set, grammar_terminals)
    │       │       write_pratt_parser_recovering(buf, config, bp_table)
    │       │       write_dispatch_recovering(buf, category)
    │       │
    │       └───▶ write_parse_entry_points(buf, categories)
    │               4 entry points per category:
    │                 Cat::parse(input) → Result<Cat, String>
    │                 Cat::parse_with_file_id(input, file_id)
    │                 Cat::parse_recovering(input) → (Option<Cat>, Vec<ParseError>)
    │                 Cat::parse_recovering_with_file_id(input, file_id)
    │
    │  Phase 4: Final assembly
    │  ========================
    │
    ├───▶ concatenate lexer_code + parser_code → complete String
    │
    ├───▶ complete.parse::<TokenStream>()  ── single parse of entire generated code
    │
    ▼
    TokenStream (complete lexer + parser for language)
```

---

## Path 1: LanguageSpec ──▶ Lexer Code

This path follows the automata pipeline.

### Step 1: Terminal Extraction

```
LanguageSpec.rules  ───▶  for each rule:
                            filter syntax items to SyntaxItemSpec::Terminal
                            collect terminal strings (recurses into Sep, Map, Zip, Optional body items)
                          ───▶  GrammarRuleInfo { label, category, terminals, is_infix }

LanguageSpec.types  ───▶  for each type:
                            check native_type (i32→integer, f64→float, bool→boolean, etc.)
                          ───▶  TypeInfo { name, language_name, native_type_name }

(GrammarRuleInfo[], TypeInfo[])
    │
    ▼
extract_terminals()
    │
    ├───▶ Scans rules for terminal strings, creates TerminalPattern { text, kind, is_keyword }
    ├───▶ Detects native types, sets BuiltinNeeds flags
    ├───▶ Injects "true"/"false" keywords for bool types
    ├───▶ Detects dollar-prefixed terminals
    ├───▶ Always includes structural delimiters: ( ) { } [ ] ,
    │
    ▼
LexerInput { language_name, terminals: Vec<TerminalPattern>, needs: BuiltinNeeds }
```

### Step 2: NFA Construction (Aho-Corasick Trie + Thompson's)

```
LexerInput.terminals  ───▶  Partition into fixed terminals and builtin patterns

Fixed terminals  ───▶  build_keyword_trie(nfa, fixed_terminals) → trie_root
                        Builds prefix-sharing trie directly in NFA:
                          "==" and "=" share the '=' prefix state
                          "true" and "false" share no prefix
                          trie_root reached via single epsilon from global_start
                        Priority via TokenKind::priority(): Fixed(10) > Ident(1)

LexerInput.needs  ───▶  if needs.ident:
                           build_ident_fragment(nfa)
                           [a-zA-Z_][a-zA-Z0-9_]* → accept(Ident)
                         if needs.integer:
                           build_integer_fragment(nfa)
                           [0-9]+ → accept(Integer)
                         if needs.float:
                           build_float_fragment(nfa)
                           [0-9]+.[0-9]+ → accept(Float)
                         if needs.string_lit:
                           build_string_lit_fragment(nfa)
                           "[^"]*" → accept(StringLit)

All fragments combined via epsilon from global start:
    global_start ──eps──▶ trie_root (single epsilon for ALL fixed terminals)
                 ──eps──▶ ident_fragment.start   (if needed)
                 ──eps──▶ integer_fragment.start  (if needed)
                 ──eps──▶ float_fragment.start    (if needed)
                 ──eps──▶ string_fragment.start   (if needed)

State savings: ~42% fewer NFA states for Calculator-class grammars (15 terminals)
vs the old per-terminal epsilon chain approach.
```

### Step 3: Alphabet Partitioning

```
Nfa  ───▶  compute_equivalence_classes()
             for each byte 0..255:
               compute signature (which states it transitions to from each NFA state)
             group bytes with identical signatures
           ───▶  AlphabetPartition { byte_to_class: [u8; 256], num_classes, class_representatives }

Typical results:
  '+' → class 5
  '*' → class 6
  'a'..'z' → class 2  (except special chars)
  '0'..'9' → class 3
  ...
  ~15 total classes (vs 256 raw bytes)
```

### Step 4: Subset Construction (NFA → DFA)

```
(Nfa, AlphabetPartition)  ───▶  subset_construction()
    start_set = epsilon_closure(nfa, [nfa.start])
    worklist iteration:
      for each DFA state (= set of NFA states):
        for each equivalence class:
          compute move + epsilon closure → target DFA state
          resolve accept: highest-priority token wins

  Key priority rule: Fixed("error") > Ident (keyword priority = 10 > 1)
  State set map: HashMap<Vec<StateId>, StateId> for O(1) lookup
  Result: Dfa with dense transition vectors using ClassId (not raw bytes)
```

### Step 5: DFA Minimization (Hopcroft's Algorithm)

```
Dfa  ───▶  minimize_dfa()
    Pre-build inverse transition map: inverse[target][class] = [predecessors]
    Initial partition by accept token kind (using &TokenKind references, no format!)
    Worklist of (partition_index, class_id) pairs:
      Only visit predecessors of splitter states via inverse map (true Hopcroft's)
      Split partitions, keep larger in place, create new for smaller
    O(1) state-to-partition lookup via partition_of: Vec<usize>
    Build new DFA from merged partitions
    Remap start state to 0

  Typical reduction: 10 states → 7 states for a simple grammar
```

### Step 6: Code Generation (String-Based)

```
(min_Dfa, AlphabetPartition, token_kinds)  ───▶  generate_lexer_string()
    │
    │   Builds entire lexer as a String buffer (no quote! / TokenStream intermediaries)
    │
    ├───▶ write_token_enum()     → enum Token<'a> { Eof, Ident(&'a str), Integer(i64), ... }
    ├───▶ write_position_and_range_defs()  → struct Position { line, column, byte_offset }
    │                                      → struct Range { start: Position, end: Position }
    ├───▶ write_parse_error_enum()         → enum ParseError { UnexpectedToken { ... }, ... }
    ├───▶ if states ≤ 30:
    │       write_direct_coded_lexer()
    │         static CHAR_CLASS: [u8; 256] = [...];
    │         fn dfa_next(state, class) -> u32 { match state { ... } }
    │         fn accept_token<'a>(state, text: &'a str) -> Option<Token<'a>> { ... }
    │         pub fn lex<'a>(input: &'a str) -> Result<Vec<(Token<'a>, Span)>, String>
    │
    └───▶ if states > 30:
            write_table_driven_lexer()
              static TRANSITIONS: [u32; states×classes] = [...];
              (same lex function, uses table lookup instead of match)
```

---

## Path 2: LanguageSpec ──▶ Binding Power Table

```
LanguageSpec.rules.filter(is_infix || is_postfix)
    │
    ▼
InfixRuleInfo[] { label, terminal, category, result_category, associativity,
                  is_cross_category, is_postfix, is_mixfix, mixfix_parts }
    │
    ▼
analyze_binding_powers()    ── two-pass algorithm
    │
    │  Pass 1: Non-postfix operators
    │    group by category, assign binding power pairs:
    │      precedence starts at 2
    │      for each operator in declaration order:
    │        Left-assoc:  (prec, prec+1), prec += 2
    │        Right-assoc: (prec+1, prec), prec += 2
    │        Mixfix:      assigned first (lowest precedence by default)
    │
    │  Pass 2: Postfix operators
    │    postfix_bp = max_non_postfix_bp + 4 (then +2 for additional postfix ops)
    │    Ensures: infix < prefix < postfix binding power hierarchy
    │
    ▼
BindingPowerTable { operators: Vec<InfixOperator> }
    │
    e.g., for Calculator with Add(+), Sub(-), Pow(^), Neg(-), Fact(!), Tern(? :):
      "?"  : category="Int", mixfix, left_bp=2, right_bp=3  (lowest)
      "+"  : category="Int", left_bp=4, right_bp=5  (left-assoc)
      "-"  : category="Int", left_bp=6, right_bp=7  (left-assoc)
      "^"  : category="Int", left_bp=9, right_bp=8  (right-assoc)
      "-"  : unary prefix, prefix_bp=12 (max_infix_bp + 2, NOT in bp_table)
      "!"  : category="Int", postfix, left_bp=14, right_bp=0
```

---

## Path 3: LanguageSpec ──▶ FIRST Sets ──▶ FOLLOW Sets ──▶ Dispatch Tables

```
LanguageSpec.rules → RuleInfo[]
    │
    ├───▶ first_items: for each rule, map syntax[0] to FirstItem
    │       Terminal(t) → terminal variant name
    │       NonTerminal(cat) → FIRST set of that category (transitive)
    │       IdentCapture / Binder / Collection → Ident
    │
    ▼
compute_first_sets()   ── fixed-point iteration until stable
    │                     augmented with native literal tokens (Integer for i32, Boolean for bool)
    │                     FirstSet.nullable flag set for empty-syntax rules
    ▼
BTreeMap<String, FirstSet>
    │
    ├───▶ compute_follow_sets_from_inputs(follow_inputs, ...)
    │       Fixed-point iteration: for each syntax item, what tokens can follow?
    │       Start: primary category FOLLOW set seeded with {Eof}
    │       Convergence: at most │categories│+1 iterations
    │       ───▶  BTreeMap<String, FirstSet>  (FOLLOW sets)
    │
    ├───▶ build_dispatch_tables()
    │       for each category:
    │         build token → rules mapping
    │         1 rule per token → DispatchAction::Direct
    │         multiple rules → DispatchAction::Lookahead
    │         var rule → DispatchAction::Variable (default)
    │       ───▶  BTreeMap<String, DispatchTable>
    │
    ├───▶ analyze_cross_category_overlaps()
    │       for each pair of categories:
    │         intersection of FIRST sets → ambiguous_tokens
    │         difference → unique_to_a, unique_to_b
    │       ───▶  BTreeMap<(String,String), CrossCategoryOverlap>
    │
    ├───▶ detect_grammar_warnings()
    │       AmbiguousPrefix: multiple non-variable rules share a leading token
    │       LeftRecursion: rule starts with non-terminal of same category
    │       UnusedCategory: category has rules but is never referenced by others
    │       ───▶  Vec<GrammarWarning>  (emitted as compile-time warnings)
    │
    └───▶ generate_sync_predicate() (per category)
            Sync tokens: FOLLOW set ∪ structural delimiters ∪ {Eof}
            Only includes structural delimiters (;  ,  )  }  ]) that exist in grammar
            ───▶  is_sync_<Cat>(token) → bool  (sync predicate function)
```

---

## Path 4: LanguageSpec ──▶ RD Handler Code

```
LanguageSpec.rules.filter(!is_infix && !is_var && !is_literal)
    │
    ▼
for each rule: RuleSpec → RDRuleInfo (extracted during Phase 1)
    │
    ▼
write_rd_handler(&mut buf, &rule) → PrefixHandler
    │
    ├───▶ write_parse_body(): walk items, emit parsing statements
    │       Terminal → expect_token(Token::Variant, "text")
    │       NonTerminal → let x = parse_<Cat>(tokens, pos, 0)?
    │       IdentCapture → let x = expect_ident(tokens, pos)?
    │       Binder → let x = expect_ident(tokens, pos)?
    │       Collection → loop { parse_elem, check separator }
    │       ZipMapSep → loop { parse body pattern, check separator }
    │       Optional → save pos, try inner, restore on failure
    │
    ├───▶ write_constructor(): build AST node from captures
    │       has_binder → Cat::Label(Scope::new(Binder(var), Box::new(body)))
    │       has_multi_binder → Cat::Label(Scope::new(binder_vec, Box::new(body)))
    │       no captures → Cat::Label (unit variant)
    │       with captures → Cat::Label(arg1, arg2, ...)
    │
    ├───▶ PrefixHandler { category, label, match_arm: String, ident_lookahead, parse_fn_name }
    └───▶ String appended to buf: fn parse_<label>() { ... }
```

### Specialized Handler Generators

In addition to the generic `write_rd_handler` path above, two specialized
handler generators produce their own `PrefixHandler` entries:

```
write_lambda_handlers(buf, categories, primary_category)
    │
    ├───▶ Generates parse_lambda(tokens, pos) → Result<Cat, ParseError>
    │       Three-step pipeline:
    │         1. Parse body as primary category
    │         2. Call body.infer_var_type(&binder_name) to determine domain
    │         3. Match on inferred type → select Lam{Domain} or MLam{Domain} variant
    │       Pre-builds match arm strings from all_categories:
    │         "Some(InferredType::Base(VarCategory::Name)) => Cat::LamName(scope),"
    │         ...one arm per category...
    │         "_ => Cat::LamCat(scope)"  (fallback to primary category default)
    │
    └───▶ PrefixHandler for Token::Caret (^) in primary category

write_dollar_handlers(buf, categories, primary_category)
    │
    ├───▶ For each domain category:
    │       Generates parse_dollar_{dom}(tokens, pos) → Result<Cat, ParseError>
    │         Parses: $dom(lambda_expr, arg)
    │         Constructs: Cat::Apply{Dom}(Box::new(f), Box::new(arg))
    │       Generates parse_ddollar_{dom}(tokens, pos) → Result<Cat, ParseError>
    │         Parses: $$dom(lambda_expr, arg1, arg2, ...)
    │         Constructs: Cat::MApply{Dom}(Box::new(f), args)
    │
    └───▶ PrefixHandler for Token::Dollar{Dom} ($dom) and Token::DDollar{Dom} ($$dom)
```

These are separate from the generic `write_rd_handler` path: lambda handlers
use inference-driven variant selection (not available in generic RD rules),
and dollar handlers parse a fixed `(lambda, arg)` structure with per-domain
application variants.

---

## FOLLOW Set Data Flow

```
LanguageSpec.rules  ───▶  FollowSetInput[] (lightweight projections)
                            { category: String, syntax: Vec<SyntaxItemSpec> }
                            (only the two fields compute_follow_sets reads)

FollowSetInput[] + FirstSets + categories + primary_category
    │
    ▼
compute_follow_sets_from_inputs()
    │
    Initialization:
      FOLLOW(primary) = { Eof }
      FOLLOW(other) = { }
    │
    Fixed-point iteration:
      for each input (rule):
        for each position i in syntax:
          if syntax[i] is NonTerminal(B):
            FOLLOW(B) += FIRST(rest_of_syntax)
            if rest_of_syntax is nullable:
              FOLLOW(B) += FOLLOW(input.category)
    │
    Convergence: at most │categories│ + 1 iterations
    │
    ▼
BTreeMap<String, FirstSet>   (FOLLOW sets)
    │
    ├───▶ Used by generate_sync_predicate() for error recovery
    └───▶ Used by write_pratt_parser_recovering() for sync-to targets
```

---

## WFST Prediction Data Flow (Always-On)

WFST-weighted prediction is always active in the pipeline. FIRST/FOLLOW sets
feed into prediction WFST construction, which produces weight-ordered dispatch
arms and static CSR arrays embedded in the generated parser.

```
FIRST sets + FOLLOW sets + DispatchTables + Overlaps
    │
    ▼
[build_prediction_wfsts()]
    │
    ├───▶ For each category:
    │       Build PredictionWfst from FIRST sets and dispatch actions
    │       Compute action weights via rule specificity analysis
    │       Sort dispatch arms by TropicalWeight (lowest = most likely)
    │
    ├───▶ [compute_composed_dispatch()]
    │       Compose lexer multi-accept DFA states with prediction WFSTs
    │       FIRST-set membership filter → rule specificity lookup → weight composition
    │       CountingWeight pass: emit codegen-time ambiguity warnings
    │       BooleanWeight pass: detect dead (unreachable) rules
    │
    ├───▶ [Tier 4: Semantic Liveness Resurrection]
    │       semantic_dependency_groups from macros crate
    │         (collected from equations/rewrites/logic via collect_constructor_labels())
    │       compute_semantic_live_labels(parsing_live, dependency_groups)
    │         Fixed-point closure: if any label in a dependency group is live,
    │         all labels in that group become live (transitive propagation)
    │       Resurrection: Tiers 1-3 flag as dead → Tier 4 checks dependency groups
    │         → unflag if semantically live (referenced by equations/rewrites/logic
    │           that also reference a parsing-live constructor)
    │
    ├───▶ [resolve_dispatch_winners()]
    │       For each (category, token) pair:
    │         Select tropical shortest-path winner → (winning_rule, weight)
    │       → BTreeMap<(String, String), (String, f64)>
    │
    ├───▶ [emit_prediction_wfst_static()]
    │       Serialize PredictionWfsts as static CSR-format arrays:
    │         PREDICTION_<CAT>_STATES, PREDICTION_<CAT>_ARCS, etc.
    │       Runtime access via LazyLock<PredictionWfst>
    │
    ├───▶ [write_category_dispatch_weighted()]
    │       Emit weight-ordered dispatch match arms in generated parser code
    │       Composed dispatch resolutions override arm ordering for ambiguous tokens
    │       Zero runtime cost — codegen-only arm reordering
    │
    ├───▶ [nfa_alternative_order()]
    │       For categories with NFA spillover (intra-category ambiguity):
    │         Query PredictionWfst for tropical weights of ambiguous rules
    │         Sort by weight (lowest = most likely = tried first)
    │         Default 0.5 for rules without explicit WFST weight
    │       Feeds into NFA merged prefix arm generation (Phase 3, step 5g)
    │
    └──▶  Static CSR arrays + weight-ordered dispatch arms + NFA alternative ordering
          (embedded in generated TokenStream)
```

> **Cross-reference:** See [benchmarks/wfst-pipeline-integration.md](../benchmarks/wfst-pipeline-integration.md)
> for detailed WFST pipeline benchmark results and performance analysis.

---

## Lint Layer Data Flow

After WFST construction, prediction, and dead-rule detection complete, the pipeline
runs a comprehensive lint pass before codegen. The lint layer borrows all pipeline
analysis data immutably — it never modifies state.

```
WFST construction + prediction outputs + dead-rule analysis
    │
    ▼
[run_lints(&LintContext)]
    │
    ├──▶ LintContext borrows all pipeline data immutably:
    │      categories, rules, rd_rules, first_sets, follow_sets,
    │      bp_table, prediction_wfsts, recovery_wfsts, cast_rules,
    │      cross_rules, all_syntax, follow_inputs,
    │      semantic_dependency_groups, nfa_spillover_categories,
    │      recovery_config, grammar_name, rule_locations
    │
    ├──▶ Lint diagnostics across 7 categories:
    │      G01-G10  Grammar structure (left-recursion, unused categories, etc.)
    │      W01-W16  WFST-specific (dead rules, ambiguous prefix, weight anomalies, WPDS)
    │      R01-R07  Recovery (empty sync set, sparse recovery, etc.)
    │      C01-C04  Cross-category (cast cycles, transitive redundancy, wide overlap)
    │      D01-D15  Decision tree + WPDS (trie ambiguity, complexity, witness traces)
    │      P02-P05  Performance (high NFA spillover, deep cast nesting, WPDS cost)
    │      COMP-08  WPDS refactoring suggestions
    │
    ├──▶ Emit to stderr in Rust-compiler-style format:
    │      warning[W01]: rule FloatToStr in category Str is unreachable (dead code)
    │        = hint: remove the rule or add a unique dispatch token
    │
    ▼
Vec<LintDiagnostic>  (informational only, does not block codegen)
```

---

## Error Recovery Data Flow

```
FollowSets + grammar_terminals
    │
    ▼
generate_sync_predicate(buf, category, follow_set, grammar_terminals)
    │
    Sync tokens = FOLLOW(category) ∪ (structural_delimiters ∩ grammar_terminals) ∪ {Eof}
    │
    ▼
fn is_sync_<Cat>(token: &Token) → bool { ... }
    │
    ├───▶ Used by parse_<Cat>_recovering() to find synchronization points
    └───▶ Used by sync_to() helper to advance past errors

Recovery helpers (generated once, shared by all categories):
  sync_to(tokens, pos, sync_predicate) → advances past errors
  expect_token_rec(tokens, pos, pred, expected, errors) → bool (insertion repair)
  expect_ident_rec(tokens, pos, errors) → String ("__error__" on failure)

Per-category recovering parsers:
  parse_<Cat>_recovering(tokens, pos, min_bp, errors) → Option<Cat>
    Wraps prefix and infix with catch-all error handling
    On error: push ParseError, sync_to(), try to continue
  parse_recovering(input) → (Option<Cat>, Vec<ParseError>)  (entry point)
```

---

## Grammar Warning Data Flow

```
RuleInfo[] + categories + all_syntax
    │
    ▼
detect_grammar_warnings()
    │
    ├───▶ Check AmbiguousPrefix:
    │       Build token_to_rules map per category
    │       Flag tokens mapping to multiple non-variable rules
    │
    ├───▶ Check LeftRecursion:
    │       For each rule, check if first syntax item is NonTerminal of same category
    │
    ├───▶ Check UnusedCategory:
    │       Track which categories appear as NonTerminal in any rule
    │       Flag categories that never appear
    │
    ▼
Vec<GrammarWarning>
    │
    ▼
    emitted as compile-time warnings (don't block compilation)
```

---

## Final Assembly

All generated code is assembled in `pipeline.rs`:

```
                     ┌────────────────────────────┐
                     │      Generated String      │
                     ├────────────────────────────┤
                     │                            │
Phase 2 output ────▶ │ // Lexer                   │
                     │ enum Token<'a> { ... }     │
                     │ struct Position { ... }    │
                     │ struct Range { ... }       │
                     │ enum ParseError { ... }    │
                     │ static CHAR_CLASS = [...]; │
                     │ fn lex<'a>(input) -> ...   │
                     │                            │
Phase 3 output ────▶ │ // Parser helpers          │
                     │ fn expect_token(...)       │
                     │ fn expect_ident(...)       │
                     │ fn peek_token(...)         │
                     │ fn peek_ahead(...)         │
                     │                            │
                     │ // Recovery helpers        │
                     │ fn sync_to(...)            │
                     │ fn expect_token_rec(...)   │
                     │ fn expect_ident_rec(...)   │
                     │                            │
                     │ // RD handlers             │
                     │ fn parse_pzero(...)        │
                     │ fn parse_pdrop(...)        │
                     │ ...                        │
                     │                            │
                     │ // Pratt parsers           │
                     │ fn infix_bp(token) -> ...  │
                     │ fn postfix_bp(t) -> ...    │
                     │ fn mixfix_bp(t) -> ...     │
                     │ fn make_infix(...)         │
                     │ fn make_postfix(...)       │
                     │ fn handle_mixfix(...)      │
                     │ fn parse_Proc(...)         │
                     │ fn parse_Proc_prefix(...)  │
                     │ ...                        │
                     │                            │
                     │ // Cross-category dispatch │
                     │ fn parse_Bool(...)         │
                     │   (wraps parse_Bool_own)   │
                     │                            │
                     │ // Sync predicates         │
                     │ fn is_sync_Proc(t) -> ...  │
                     │ fn is_sync_Int(t) -> ...   │
                     │                            │
                     │ // Recovering parsers      │
                     │ fn parse_Proc_recovering() │
                     │ fn parse_Int_recovering()  │
                     │ ...                        │
                     │                            │
                     │ // Entry points            │
                     │ impl Proc {                │
                     │   fn parse()               │
                     │   fn parse_with_file_id()  │
                     │   fn parse_recovering()    │
                     │   fn parse_recovering_     │
                     │     with_file_id()         │
                     │ }                          │
                     │ impl Int  { ... }          │
                     └─────────────┬──────────────┘
                                   │
                                   ▼
                      str::parse::<TokenStream>()
                                   │
                                   ▼
                       Final TokenStream output
```

---

## Complexity

| Phase                           | Time                                             | Space                   |
|---------------------------------|--------------------------------------------------|-------------------------|
| Extraction                      | O(R × T) where R = rules, T = terminals per rule | O(R + T_total)          |
| NFA construction (trie)         | O(T_total × L) where L = avg terminal length     | O(NFA states)           |
| Alphabet partitioning           | O(256 × NFA states)                              | O(256)                  |
| Subset construction             | O(2^N × C) worst case, O(D × C) typical          | O(D × C)                |
| DFA minimization                | O(D × C × log D)                                 | O(D)                    |
| Lexer codegen                   | O(D × C)                                         | O(D × C)                |
| Binding power analysis          | O(R_infix) two-pass                              | O(R_infix)              |
| FIRST set computation           | O(R × Categories) iterations                     | O(Categories × Tokens)  |
| FOLLOW set computation          | O(R × Categories) iterations                     | O(Categories × Tokens)  |
| Dispatch table building         | O(R × Tokens)                                    | O(Categories × Tokens)  |
| Grammar warnings                | O(R × Categories)                                | O(R)                    |
| RD handler generation           | O(R_structural × Items)                          | O(R_structural)         |
| Pratt parser generation         | O(Categories × R)                                | O(Categories)           |
| Recovery generation             | O(Categories × \|FOLLOW\|)                       | O(Categories)           |
| Cross-category dispatch         | O(Categories^2 × Tokens)                         | O(Categories^2)         |
| NFA spillover detection         | O(Categories × Tokens × R_per_token)             | O(Categories × R_ambig) |
| Final parse (str → TokenStream) | O(\|generated code\|)                            | O(\|generated code\|)   |

Where D = DFA states, C = equivalence classes, N = NFA states.

The generated parser itself runs in O(n) time and O(n) space on input length n
(both fail-fast and recovering paths).

