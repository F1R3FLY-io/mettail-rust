# SFT02: constant-sft-output

**Severity:** Note
**Module:** Symbolic Finite Transducers
**Feature gate:** `sft`

## What It Detects

An SFT always produces the same output regardless of input. All transitions use
`OutputFunction::Constant` with the same value, or all paths through the SFT
converge to identical output sequences. The SFT is simplifiable to a constant
function: it maps every accepted input to a single fixed output, making the full
transducer machinery unnecessary.

Detection enumerates all output functions on reachable transitions and checks
whether every path from an initial state to an accepting state produces the same
output sequence. If the output is invariant across all accepting runs, the SFT
is flagged as constant.

## Example

### Triggering Code

```
language! {
    name: Sanitizer;
    primary: Proc;

    category Proc {
        Send  = Chan "!" "(" Expr ")";
        Recv  = "for" "(" Pattern "<-" Chan ")" "{" Proc "}";
        Par   = Proc "|" Proc;
        Zero  = "0";
    }

    category Expr {
        Num = /[0-9]+/;
        Var = /[a-z][a-zA-Z0-9_]*/;
    }

    // This SFT replaces any Send expression with Zero, regardless of
    // what the Send contains. The output is always "0".
    sft discard_sends {
        input:  Send;
        output: Zero;
    }
}
```

The SFT `discard_sends` maps every `Send` term to `Zero`. No matter what
channel or expression appears in the input, the output is always the constant
term `0`. The transducer does not use any input-dependent output function.

### Diagnostic Output

```
note[SFT02] (Sanitizer): SFT 'discard_sends' always produces constant output 'Zero'
  = hint: consider replacing with a direct rewrite rule or verify this is intentional
```

### Fix

```
// Option 1: If the constant behavior is intentional, replace with a
// simpler rewrite rule that does not require SFT machinery.
rule discard_sends {
    Send => Zero;
}

// Option 2: If the output should depend on the input, add input-dependent
// output functions.
sft discard_sends {
    input:  Send where chan == "stderr";
    output: Zero;

    input:  Send;
    output: Send;  // pass through non-stderr sends
}
```

## Rationale

- A constant-output SFT is an optimization opportunity: the full transducer
  state machine, output function evaluation, and domain checking can be replaced
  by a simple pattern match and constant substitution, reducing both compilation
  cost and runtime overhead.
- Constant output may indicate an incomplete specification where the grammar
  author intended to add input-dependent transformations but has not yet done so.
  Flagging it as a note draws attention without blocking compilation.
- Constant SFTs do not need the full SFT machinery for equivalence checking,
  composition, or domain analysis. Recognizing them early allows the pipeline to
  use faster specialized paths for constant functions.

## Related Lints

- [SFT01](SFT01.md) -- Empty SFT domain: the SFT never fires at all (a stricter condition)
- [SFT03](SFT03.md) -- Nondeterministic SFT: the opposite problem where the SFT produces too many outputs
- [SFT04](SFT04.md) -- Equivalent SFT pair: two constant SFTs with the same output are trivially equivalent
