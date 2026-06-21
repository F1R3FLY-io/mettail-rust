# LALRPOP Grammar Generation Design

## Overview

This document describes how MeTTaIL generates LALRPOP parsers from theory definitions.

---

## Architecture

### 1. Theory Definition → LALRPOP Grammar

```
theory! {
    terms {
        PZero . Proc ::= "0" ;
        PPar . Proc ::= Proc "|" Proc ;
    }
}
```

↓ **`lalrpop_gen::generate_lalrpop_grammar()`** ↓

```lalrpop
grammar;

pub Proc: Proc = {
    "0" => Proc::PZero,
    <l:Proc> "|" <r:Proc> => Proc::PPar(Box::new(l), Box::new(r)),
};
```

---

## Grammar Item Mapping

### Terminals
```
Input:  "0"
Output: "0" => Category::Constructor
```

### Non-Terminals
```
Input:  Proc
Output: <val:Proc> => ... Box::new(val) ...
```

### Variables
```
Input:  Var
Output: <v:Ident> => ... Var::Free(FreeVar::fresh_named(v)) ...
```

### Binders (Complex!)
```
Input:  "for" "(" Name <Name> ")" "{" Proc "}"
Output: "for" "(" <ch:Name> <x:Ident> ")" "{" <body:Proc> "}"
        => Proc::PInput(
            Box::new(ch),
            Scope::new(
                Binder(FreeVar::fresh_named(x)),
                Box::new(body)
            )
        )
```

---

## Challenges & Solutions

### Challenge 1: Precedence and Associativity

**Problem:** How to handle `P | Q | R`?

**Solution:** Use LALRPOP precedence tiers:
```lalrpop
pub Proc: Proc = {
    <Proc1>
};

Proc1: Proc = {  // Tier 1: Parallel composition (lowest precedence)
    <l:Proc1> "|" <r:Proc2> => Proc::PPar(Box::new(l), Box::new(r)),
    <Proc2>,
};

Proc2: Proc = {  // Tier 2: Atoms (highest precedence)
    "0" => Proc::PZero,
    "(" <Proc> ")",
};
```

### Challenge 2: Binder Scope Creation

**Problem:** How to create `Scope<Binder<String>, Box<Proc>>` during parsing?

**Solution:** Parse binder as identifier, create fresh variable, wrap body in Scope:
```rust
"for" "(" <ch> <x:Ident> ")" "{" <body> "}"
=> {
    let binder = Binder(FreeVar::fresh_named(x));
    let scope = Scope::new(binder, Box::new(body));
    Proc::PInput(Box::new(ch), scope)
}
```

**Limitation:** Variable names are parsed but immediately converted to fresh variables.
Need name hints for pretty-printing (Phase 2.5).

### Challenge 3: Left Recursion

**Problem:** `Proc ::= Proc "|" Proc` is left-recursive

**Solution:** LALRPOP handles left recursion naturally! Just write:
```lalrpop
<l:Proc> "|" <r:Term> => ...
```

### Challenge 4: Whitespace

**Problem:** How to handle whitespace between tokens?

**Solution:** LALRPOP handles it automatically! No explicit whitespace rules needed.

---

## Implementation Strategy

### Phase 1: Simple Terms (DONE)
- Terminals only
- Single non-terminal fields
- Unit constructors

### Phase 2: Compound Terms (CURRENT)
- Multiple fields
- Nested non-terminals
- Infix operators

### Phase 3: Binders (NEXT)
- Parse binder syntax
- Generate Scope creation code
- Handle multiple binders

### Phase 4: Precedence (FUTURE)
- Detect infix operators
- Infer precedence levels
- Generate tiered grammar

### Phase 5: Pretty-Printing (FUTURE)
- Generate Display impl
- Respect precedence (minimize parens)
- Handle name hints

---

## File Organization

```
macros/src/
├── lalrpop_gen.rs          # Grammar generation logic
└── parser_gen.rs           # (Old approach - to be replaced)

Generated during build:
target/generated/
└── theories/
    ├── rhocalc.lalrpop     # Generated grammar
    └── rhocalc_parser.rs   # LALRPOP output

runtime/src/
└── parsers/
    └── mod.rs              # Re-exports all generated parsers
```

---

## Testing Strategy

### Unit Tests (in lalrpop_gen.rs)
- Test grammar string generation
- Verify LALRPOP syntax is valid
- Check all rule types covered

### Integration Tests (in runtime/tests/)
- Parse simple expressions
- Parse complex nested terms
- Round-trip testing (parse → print → parse)
- Error message testing

### Theory Tests (in theories/*.rs)
- Rho Calculus parsing
- Lambda Calculus parsing
- Custom syntax testing

---

## Future Enhancements

### Custom Operators
Allow theories to specify precedence:
```rust
terms {
    @precedence(10, left)
    PPar . Proc ::= Proc "|" Proc ;

    @precedence(20, left)
    PSeq . Proc ::= Proc ";" Proc ;
}
```

### Error Recovery
Generate better error messages:
```rust
Expected: "}"
Found: "|"
Context: Inside binder body "for(x y) { *y |"
         Here ------------------^
```

### Incremental Parsing
Cache parse results for better IDE performance.

---

**Status:** Design complete, basic implementation done
**Next:** Test with real theories

