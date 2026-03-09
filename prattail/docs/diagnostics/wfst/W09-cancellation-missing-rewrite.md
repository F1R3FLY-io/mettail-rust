# W09: cancellation-pair-missing-rewrite

**Severity:** Warning
**Category:** WFST-Specific / Macro-Phase
**Feature Gate:** none (always active)

## Description

Detects cancellation pair equations that were **suppressed** from the Ascent
`eqrel` relation but have **no corresponding directional rewrite** to handle
the same pattern at runtime.  A cancellation pair has the form
`Outer(Inner(X)) = X`, which is semantically a no-op (the outer constructor
cancels the inner).  PraTTaIL suppresses these from `eqrel` to avoid
equivalence class explosion and instead handles them in `normalize()`.

The problem arises when the category has **congruence rewrites** that can
*introduce* the cancellation pattern at runtime during Ascent's fixpoint
iteration.  Without a corresponding rewrite `Outer(Inner(X)) ~> X`, the
cancellation can only be collapsed by explicit `normalize()` calls, not by
the fixpoint computation itself.

```
  Equation suppressed:  Send(Recv(X)) = X
  ┌──────────────────────────────────────────────────┐
  │  Congruence rewrite in Proc:                      │
  │    if a = b then Send(a) = Send(b)               │
  │                                                    │
  │  If a = Recv(X), congruence produces:             │
  │    Send(Recv(X))                                   │
  │                                                    │
  │  Without rewrite  Send(Recv(X)) ~> X:             │
  │    This term persists in the fixpoint,             │
  │    never reduced until normalize() is called.      │
  │                                                    │
  │  With rewrite  Send(Recv(X)) ~> X:                │
  │    Ascent's fixpoint reduces it immediately.       │
  └──────────────────────────────────────────────────┘
```

This lint is emitted by the **macros crate** during equation analysis (not by
the prattail lint pass), because it requires access to the full equation and
rewrite definitions.

## Trigger Conditions

All of the following must hold:

- A cancellation pair `Outer(Inner(X)) = X` was detected and suppressed
  (G25 was emitted).
- No rewrite rule in the grammar matches the pattern `Outer(Inner(X)) ~> X`
  (checking for matching outer/inner constructors and variable binding).
- The category of the outer constructor has at least one **congruence rewrite**
  (a rewrite generated from the category's equation congruence rules).

One diagnostic is emitted per cancellation pair missing its rewrite.

## Example

### Grammar

```rust
language! {
    name: ChannelLang,
    types { ![String] as Proc, ![String] as Name },
    terms {
        Send . x:Name, p:Proc |- x "!" "(" p ")" : Proc;
        Recv . x:Name         |- x "?" "("   ")" : Proc;
        Var  . |- <ident>     : Name;
    },
    equations {
        |- Send(X, Recv(X)) = Nil;  // cancellation pair
    },
    // Missing: |- Send(X, Recv(X)) ~> Nil;
}
```

### Output

```
warning[W09] (ChannelLang): cancellation pair `eq_send_recv` has no corresponding rewrite
  = hint: add `|- (Send (Recv X)) ~> X ;` to ensure runtime reduction; without this rewrite, Send(Recv(X)) can only be collapsed by normalize()
```

## Resolution

1. **Add the corresponding rewrite.**  The most direct fix is to add a
   directional rewrite that matches the cancellation pattern:
   ```
   |- Send(X, Recv(X)) ~> Nil;
   ```
   This allows Ascent's fixpoint to reduce the pattern immediately when
   congruence introduces it, without waiting for `normalize()`.

2. **Remove congruence rewrites.**  If the category does not need congruence
   propagation, disabling congruence rules for it eliminates the mechanism
   that introduces cancellation patterns at runtime.  W09 will not fire for
   categories without congruence rewrites.

3. **Accept the warning.**  If `normalize()` is called frequently enough
   that the un-reduced cancellation terms do not accumulate, the missing
   rewrite may be acceptable.  The fixpoint will still converge correctly;
   it may just take additional `normalize()` calls.

## Hint Explanation

The hint **"add `|- (Outer (Inner X)) ~> X ;` to ensure runtime reduction;
without this rewrite, Outer(Inner(X)) can only be collapsed by normalize()"**
explains the runtime behavior gap:

- The suppressed equation is handled by `normalize()`, which is called
  explicitly (not during fixpoint iteration).
- If congruence rules create new `Outer(Inner(X))` terms during fixpoint
  iteration, those terms persist until the next `normalize()` call.
- The rewrite closes this gap by enabling reduction during fixpoint iteration
  itself.

## Related Lints

- [G25](../grammar/G25-cancellation-pair-detected.md) -- The informational
  note that fires when a cancellation pair is detected and suppressed.  G25
  always precedes W09 for the same pair.
- [A01](../ascent/A01-fixpoint-non-convergence.md) -- Un-reduced cancellation
  terms contribute to term growth, compounding A01-style non-convergence
  risks.
- [A04](../ascent/A04-large-equivalence-class.md) -- Cancellation pair
  suppression is *designed* to prevent equivalence class explosion (A04);
  the missing rewrite means the suppression is incomplete.
