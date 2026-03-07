# W01: dead-rule

**Severity:** Warning
**Category:** WFST-Specific

## Description

Detects rules that can never be reached during parsing. A dead rule wastes compile-time resources (WFST construction, codegen, minimization) and misleads grammar authors into believing a syntactic form is supported when it will never match any input. The lint employs a four-tier analysis, each tier catching progressively subtler unreachability patterns:

1. **LiteralNoNativeType** -- A rule that matches a native literal token (e.g., integer, string) lives in a category that declares no `native_type`. Since native literals are dispatched by `native_type`, the rule can never receive input.

2. **UnreachableCategory** -- The rule's entire category has no reachable prefix rules. A category without any prefix or cast path into it can never start a parse, so every rule in it is dead.

3. **WfstUnreachable** -- The prediction WFST for the rule's category shows no dispatch path from any FIRST-set token to this rule. The WFST encodes all token-to-rule mappings; if a rule has no entry, the generated parser will never invoke it.

4. **InterCategoryDeadPath** -- Forward-backward analysis with `BooleanWeight` over the inter-category dispatch graph reveals that the rule's category is isolated from the primary (root) category. Either the root cannot reach the category (forward), the category cannot reach back to the root (backward), or both.

> **Note:** W01 covers Tiers 1–4. For Tier 5 (WPDS stack-aware unreachability), see [W13](W13-wpds-unreachable.md). Tier 5 uses weighted pushdown system `poststar(BooleanWeight)` to detect rules that are unreachable when considering the full inter-category call stack. W13 warnings include D15 witness traces showing the shortest path evidence.

## Trigger Conditions

A W01 diagnostic fires when **any** of the following conditions holds for a rule:

- **Tier 1 (LiteralNoNativeType):** The rule is a literal rule (its syntax consists solely of a native token match) AND the category's `native_type` field is `None`.

- **Tier 2 (UnreachableCategory):** The rule's category has an empty FIRST set AND no cross-category or cast rule from a reachable category transitively introduces tokens into it (fixed-point reachability check).

- **Tier 3 (WfstUnreachable):** After prediction WFST construction, iterating over every token in `FIRST(category)` and querying `wfst.predict(token)` yields no `WeightedAction` whose `rule_label` matches this rule.

- **Tier 4 (InterCategoryDeadPath):** The inter-category dispatch graph is built with `BooleanWeight` edges. `forward_scores()` from the root and `backward_scores()` to the root are computed. If `forward[cat_idx].is_zero()` OR `backward[cat_idx].is_zero()`, all rules in that category are flagged. Rules already caught by Tiers 1--3 are deduplicated.

## Example

### Grammar

```
language! {
    name: ExampleLang;
    primary: Proc;

    category Int {
        native_type: Integer;

        IntLit     = <int>;              // OK: has native_type
        IntAdd     = Int "+" Int;
        IntNeg     = "-" Int;
    }

    category Bool {
        // Note: no native_type declared
        BoolLit    = <bool>;             // Tier 1: literal, no native_type
        BoolAnd    = Bool "&&" Bool;
        BoolNot    = "!" Bool;
    }

    category Float {
        native_type: Float;

        FloatLit   = <float>;
        FloatMul   = Float "*" Float;
    }

    // Isolated: no cast/cross-category path from Proc or Int
    category Phantom {
        native_type: String;

        PhantomLit = <string>;           // Tier 2 + Tier 4: entire category unreachable
        PhantomOp  = Phantom "~" Phantom;
    }

    category Str {
        native_type: String;

        StrLit     = <string>;
        FloatToStr = Float;              // Cast from Float
        IntToStr   = Int;                // Cast from Int

        // Tier 3: no FIRST-set token dispatches to this rule
        // because "render" is never a prefix token for any
        // other rule, and this rule shares its prefix with StrLit
        StrRender  = <string> "." "render" "(" ")";
    }

    category Proc {
        POutput = "stdout" "!" "(" Str ")";
        PEval   = "eval" "(" Int ")";

        // Cast from Int (provides reachability from Proc -> Int)
        CastInt = Int;
    }
}
```

### Output

```
warning[W01]: warning: literal rule BoolLit in category Bool is unreachable (dead code) — category has no native_type
  --> <macro>:12:9
  = in category `Bool`, rule `BoolLit`
  = hint: add a native_type to the category or remove the literal rule

warning[W01]: warning: rule PhantomLit in category Phantom is unreachable (dead code) — category Phantom has no reachable prefix rules
  --> <macro>:25:9
  = in category `Phantom`, rule `PhantomLit`
  = hint: add a prefix rule to make the category reachable

warning[W01]: warning: rule PhantomOp in category Phantom is unreachable (dead code) — category Phantom has no reachable prefix rules
  --> <macro>:26:9
  = in category `Phantom`, rule `PhantomOp`
  = hint: add a prefix rule to make the category reachable

warning[W01]: warning: rule StrRender in category Str is unreachable (dead code) — no token in FIRST(Str) dispatches to it via prediction WFST
  --> <macro>:36:9
  = in category `Str`, rule `StrRender`
  = hint: remove the rule or add a unique dispatch token

warning[W01]: warning: rule PhantomLit in category Phantom is on a dead inter-category path (forward+backward) — forward-backward analysis with BooleanWeight indicates no live path through this category
  = in category `Phantom`, rule `PhantomLit`
  = hint: check inter-category connections; this category may be isolated
```

Note: In practice, Tier 4 warnings are deduplicated against Tiers 1--3. The `PhantomLit` example above would only appear once (the Tier 2 version takes precedence). The Tier 4 message is shown separately here for illustration.

## Resolution

Each tier has a distinct resolution strategy:

1. **LiteralNoNativeType:** Add a `native_type` declaration to the category. For example, add `native_type: Boolean;` to the `Bool` category so the lexer knows how to dispatch `<bool>` tokens.

2. **UnreachableCategory:** Either add a cast rule from a reachable category (e.g., `CastPhantom = Phantom;` in `Proc`), or add cross-category prefix rules that can introduce the isolated category into the parse tree.

3. **WfstUnreachable:** The rule's prefix tokens are shadowed by another rule with an identical dispatch token. Either give the rule a unique leading terminal (e.g., change `StrRender` to `"render" "(" Str ")"` so it dispatches on `"render"` instead of `<string>`), or remove the rule if the syntactic form is redundant.

4. **InterCategoryDeadPath:** Examine the inter-category dispatch graph. If the direction is `"forward"`, the root category has no cast or cross-category path leading to this category -- add one. If `"backward"`, the category has no way to produce a term that the root can consume -- add a reverse cast. If `"forward+backward"`, the category is completely disconnected.

## Hint Explanation

The four hint messages correspond to the four tiers:

- **"add a native_type to the category or remove the literal rule"** -- Without a `native_type`, the lexer produces no typed literal tokens for the category, so literal match rules have nothing to match against.

- **"add a prefix rule to make the category reachable"** -- A category is parsed by first matching a prefix rule. If no prefix rule exists or is reachable (via FIRST-set tokens or cross-category dispatch), the category is a dead end.

- **"remove the rule or add a unique dispatch token"** -- The prediction WFST maps tokens to rules. If a rule has no mapping, it means every token that could plausibly start this rule is already claimed by another rule with higher (better) priority.

- **"check inter-category connections; this category may be isolated"** -- The `BooleanWeight` forward-backward analysis treats each inter-category edge as a boolean reachability marker. If the product of forward and backward scores is zero for a category, no live derivation path passes through it.

## Related Lints

- [G02](../grammar/G02-unused-category.md) -- Detects categories that are declared but never referenced in any rule; a structural precursor to W01 Tier 2
- [G05](../grammar/G05-empty-category.md) -- Detects categories with zero rules; a degenerate case where W01 would flag every (nonexistent) rule
- [G08](../grammar/G08-missing-cast-to-root.md) -- Detects categories with no **directed** cast/cross-cat path to the primary. G08 and A4 (W01 Tier 4) are **complementary**: G08 uses a directed cast-only graph, A4 uses a richer undirected graph including syntax-level references. G08 can fire on categories that A4 does NOT flag (syntax-connected but not cast-connected) and vice versa.
- [D03](../decision-tree/D03-trie-unreachable-rule.md) -- Complementary to Tier 3: Tier 3 + D03 trie confirmation = confirmed dead rule. Already properly composed in `collect_dead_rule_labels()`.
- [W13](W13-wpds-unreachable.md) -- Tier 5 dead-rule detection: WPDS stack-aware unreachability via `poststar(BooleanWeight)`. Catches rules that survive Tiers 1–4 but are unreachable when the full pushdown call structure is considered. Includes D15 witness traces.
