# SFT03: nondeterministic-sft

**Severity:** Note
**Module:** Symbolic Finite Transducers
**Feature gate:** `sft`

## What It Detects

An SFT is not single-valued (nondeterministic output). The functionality check
(`is_functional()`) returns false -- there exist inputs for which the SFT can
produce multiple different output sequences. This may be intentional (ambiguous
dispatch where the runtime selects nondeterministically) or accidental
(overlapping guards with different output functions on the same input class).

Detection uses the standard functionality test for symbolic transducers: the SFT
is composed with itself under input-equality constraints, and the resulting
product transducer is checked for whether any accepting run produces two
distinct output sequences. If such a run exists, the SFT is nondeterministic.

## Example

### Triggering Code

```
language! {
    name: Rewriter;
    primary: Proc;

    category Proc {
        Send  = Chan "!" "(" Expr ")";
        Recv  = "for" "(" Pattern "<-" Chan ")" "{" Proc "}";
        Par   = Proc "|" Proc;
        New   = "new" Name "in" "{" Proc "}";
        Zero  = "0";
    }

    category Expr {
        Num = /[0-9]+/;
        Var = /[a-z][a-zA-Z0-9_]*/;
        Add = Expr "+" Expr;
    }

    // Two overlapping input guards with different output functions:
    // for x in [1, 200], both clauses match inputs where x is in [50, 100].
    sft optimize_send {
        input:  Send where guard(x >= 1 /\ x <= 100);
        output: New "opt_ch" in { Send };

        input:  Send where guard(x >= 50 /\ x <= 200);
        output: Zero;
    }
}
```

The SFT `optimize_send` has two clauses with overlapping input domains: values
of `x` in the range `[50, 100]` satisfy both guards. For inputs in this overlap,
the SFT can produce either `New "opt_ch" in { Send }` or `Zero`, making it
nondeterministic.

### Diagnostic Output

```
note[SFT03] (Rewriter): SFT 'optimize_send' is nondeterministic (not single-valued)
  = hint: disambiguate overlapping input guards or confirm nondeterminism is intentional
```

### Fix

```
// Option 1: Make input guards disjoint to ensure single-valued output.
sft optimize_send {
    input:  Send where guard(x >= 1 /\ x < 50);
    output: New "opt_ch" in { Send };

    input:  Send where guard(x >= 50 /\ x <= 200);
    output: Zero;
}

// Option 2: If nondeterminism is intentional, suppress with an annotation.
#[allow(SFT03)]
sft optimize_send {
    input:  Send where guard(x >= 1 /\ x <= 100);
    output: New "opt_ch" in { Send };

    input:  Send where guard(x >= 50 /\ x <= 200);
    output: Zero;
}
```

## Rationale

- Nondeterminism complicates reasoning about transformations: the same input
  can yield different outputs depending on which transition the runtime selects.
  Unless the grammar author explicitly intends nondeterministic dispatch (as in
  concurrent process semantics), this is likely a specification error caused by
  overlapping guard predicates.
- Nondeterministic SFTs may indicate guard overlap bugs where two clauses
  accidentally cover the same input region with conflicting output functions.
  The overlap region can be extracted as a witness and presented to the user for
  inspection.
- Functional (single-valued) SFTs support efficient equivalence checking via
  the standard algorithm for deterministic transducers, while nondeterministic
  SFTs require the more expensive general inclusion check. Keeping SFTs
  functional enables the pipeline to use faster analysis paths.

## Related Lints

- [SFT01](SFT01.md) -- Empty SFT domain: the SFT never fires (no overlap problem because there is no input)
- [SFT02](SFT02.md) -- Constant SFT output: a trivially functional SFT (single-valued by construction)
- [SFT04](SFT04.md) -- Equivalent SFT pair: equivalence checking is only efficient for functional SFTs
- [SYM02](../symbolic/SYM02.md) -- Overlapping guards: the SFA-level analogue for guard overlap detection
