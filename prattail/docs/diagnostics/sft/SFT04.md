# SFT04: equivalent-sft-pair

**Severity:** Note
**Module:** Symbolic Finite Transducers
**Feature gate:** `sft`

## What It Detects

Two functional SFTs produce identical input-output behavior. Equivalence
checking (`is_equivalent_functional()`) determines that both transducers compute
the same function: for every input accepted by either SFT, both produce the same
output sequence. One of the two SFTs can be eliminated as redundant.

Detection requires both SFTs to be functional (single-valued). The algorithm
constructs the product of the two SFTs over shared input symbols and verifies
that every accepting run in the product produces identical output sequences from
both components. If no divergence is found, the SFTs are equivalent.

## Example

### Triggering Code

```
language! {
    name: Compiler;
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
    }

    // Two SFTs that both wrap sends in a new-channel scope.
    // They use different names but compute the same transformation.
    sft wrap_send_v1 {
        input:  Send;
        output: New "ch" in { Send };
    }

    sft wrap_send_v2 {
        input:  Send;
        output: New "ch" in { Send };
    }
}
```

The SFTs `wrap_send_v1` and `wrap_send_v2` have identical domains (all `Send`
terms) and identical output functions (wrapping in `New "ch" in { ... }`). The
equivalence check confirms they compute the same function, so one is redundant.

### Diagnostic Output

```
note[SFT04] (Compiler): SFTs 'wrap_send_v1' and 'wrap_send_v2' are equivalent (redundant pair)
  = hint: remove one SFT or unify them under a single name
```

### Fix

```
// Remove the duplicate and keep a single SFT.
sft wrap_send {
    input:  Send;
    output: New "ch" in { Send };
}
```

## Rationale

- Redundant SFTs waste analysis resources: the pipeline constructs, minimizes,
  and checks each SFT independently. Eliminating duplicates reduces compilation
  time, memory consumption, and the size of generated dispatch tables.
- Equivalent SFT pairs often indicate copy-paste grammar patterns where a
  transducer was duplicated during refactoring but never diverged. Flagging the
  redundancy encourages the grammar author to consolidate the definitions and
  reduce maintenance burden.
- Equivalence checking for functional SFTs runs in time polynomial in the
  product of the two automata's state counts (with a SAT query per transition
  pair). The check is tractable for typical grammar-derived SFTs and provides
  high-confidence deduplication without false positives.

## Related Lints

- [SFT01](SFT01.md) -- Empty SFT domain: both SFTs may be vacuously equivalent if their domains are empty
- [SFT02](SFT02.md) -- Constant SFT output: two constant SFTs with the same output are trivially equivalent
- [SFT03](SFT03.md) -- Nondeterministic SFT: equivalence checking requires functional SFTs; nondeterministic ones are not checked
- [G07](../grammar/G07-identical-rules.md) -- Identical rules: the parse-rule-level analogue for detecting duplicated grammar definitions
