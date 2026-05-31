# Pass-2c Token-Soundness Fix (principled, evidence-based) — 2026-05-30

Replaces the premature-disambiguation weight heuristic with an evidence-based (token-soundness) fix.
Unblocks M4 → the cast family. Plan agent design; ledger: `drive-suite-green-ledger.md`.

## Principle (non-negotiable)
NEVER prematurely disambiguate. Drop an alternative ONLY when EVIDENCE rejects it. For a parser the
cardinal evidence is **token-soundness**: a derivation node for rule R must consume from the input every
terminal literal in R's syntax_pattern; a derivation's terminal yield must equal the input it spans.

## Bug (token-unsound construction)
`prefix.rs:1144-1194` **Pass 2c** emits trigger-bearing syntactic casts (`<Y>To<X> . a:Y |- "trig" "(" a ")" : X`,
e.g. `IntToFloat`/`FloatToBool`) as `slot=0` FREE wrap edges — identical shape to *transparent* Pass-2a
projections (`ProcInt . i:Int |- i : Proc`). `slot=0` + `CrossCatDelegate` schedules ONLY the operand
sub-parse; the cast's trigger terminals (`float(`,`)`) are NEVER matched against input. On the
`with_kind_return` pop the cast FireAction fires over just the operand → fabricates the cast node.
Result: `bool(0)` produces unsound `FloatToBool(IntToFloat(0))` (display `bool(float(0))`, yield ≠ input).
The 0.15 `BP_TIER_PASS2C_SYNTHESIZED` weight (`lex_weight.rs:271`) was added to make direct casts "always
win" over this — that is the FORBIDDEN premature-disambiguation heuristic masking the unsound construction.

## Fix
- **§3a (primary, codegen):** in `emit_unified_arm` `ImplicitCast` arms (`prefix.rs:1488-1521` singleton, `:1590-1619` Fork),
  DROP the `rule_at(X,rule_idx,slot=0).with_kind_return()` + cast-action wrap; emit instead a NON-fabricating
  **bootstrap delegation** = `Push category_entry(source_src_idx) → PrefixDispatch{cur_bp:0}` (model EXACTLY on
  the existing `CrossCatLhs` bootstrap arm `:1433-1453`). The Y-value is produced; the InfixLoop cross-cat
  machinery (`infix.rs is_cross_category`, independent of Pass-2c) forms the SOUND cross-cat term by consuming
  REAL operator tokens. The cast is then only reachable via its real keyword Fork (`:1239`, slot=1, trigger
  consumed via TriggerTerminal) — sound by construction. **Keep the bootstrap, drop the wrap** (R1).
- **§3b:** ensure `collect_first_set` (`prefix.rs:648-655`) recursion does NOT transitively reach trigger-bearing
  casts as free edges (it already recurses only through transparent `CrossCatProjection`; keep explicit +
  symmetric guard in the Pass-2c enumerator).
- **§5:** DELETE `BP_TIER_PASS2C_SYNTHESIZED` (`lex_weight.rs:271`) + its uses (gone with the removed arms).
  Keep `BP_TIER_CROSSCAT_PROJECTION`/`_LHS` (bias among SOUND coexisting branches, not soundness crutches).
- **Backstop (defense-in-depth, realize-time):** emit per-rule `expected_terminal_count[rule_idx]` =
  `syntax_pattern` literal count; in `realize_packing_call` (`wpda_walker.rs:4908`) reject a packing whose
  matched Terminal+TriggerTerminal child count < expected (return `Vec::new()`, like the existing arity/Trigger
  filters). Ship `debug_assert!`-gated first, then as a production filter. NOT a weight.
- **Soundness regression test:** assert `Bool::parse_via_wpda_all("bool(0)")` (+ a fabrication-prone corpus) has
  NO alt whose `format!("{}",t)` ≠ input.

## §4 — sound vs unsound (empirically classified; keeps the 16-regression set correct)
The 6 SOUND `int(false>b<N)`-style cases NEVER use the Pass-2c wrap (built by native first-input + InfixLoop);
the bootstrap-preserving §3a keeps them green. **3 inputs ONLY parsed via fabrication** (`int(false>a>z<"eoxyaib")`,
`int(true>=z<x<="a")`, `int(-220439700>...!=-0.5)` → `int(float(...))`) — they have NO token-sound parse, so per
the principle they MUST now error. The tests asserting `is_ok()` (`simulator_regression_bool_prefix_tokens` #2/#3,
`simulator_regression_cross_cat_dispatch_chaining` #4) were passing on UNSOUND parses → update them to expect the
structured ParseError (correctness improvement, flag to user).

## §6 — compose with M4
Land §3 FIRST, then re-land M4 (DispatchKey/PackedDispatchConfig rule/source discriminator, keep `EquivKey` narrow).
With Pass-2c non-fabricating, M4's un-conflation surfaces only SOUND distinct cast injections → M4 ships →
calc cast 0/12→8/12 + rhocalc casts parse → ~13/17 cast family closes. The 2 doubly-nested = separate Exp-15.
§3a (codegen prefix) and M4 (walker cohort keying) touch disjoint code → compose cleanly.

## Gates (in order)
soundness probe; `unit_calculator_bool_inttobool`; edge_case 229/229; op-suites (gen_calculator_op ≥1331/0,
gen_rhocalc_op 532/0); gauntlet 4220/0; `wpda_parity_*` + `-3!` ladder; sanctioned 3-test expectation updates;
(with M4) interleaved Welch chain panel + chain_1000/2000 RSS +5%.

## Risks
R1 bootstrap-vs-wrap separation (model on CrossCatLhs; verify each sound input individually). R2 the 3 unsound
inputs flip pass→fail (correct; sign-off). R3 bucket first-match shadowing (emit bootstrap into same bucket;
diff generated wpda.rs). R4 backstop terminal-count (count only Literal; debug_assert first). R5 M4 perf (separate
commit; Welch). R6 rhocalc analogous casts (grammar-agnostic; gen_rhocalc_op 532/0).
