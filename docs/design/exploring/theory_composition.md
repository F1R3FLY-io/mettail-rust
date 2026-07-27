# Theory Parameterization & Composition Design

**Status:** Design Phase
**Priority:** Important but deferred to Phase 1.5/2
**Complexity:** High

---

## Overview

MeTTaIL theories are built by **composing** and **parameterizing** other theories. This is the core abstraction mechanism that enables:
- Code reuse (ParMonoid extends any CommutativeMonoid)
- Modularity (build complex theories from simple ones)
- Generic programming (theories as type parameters)

---

## Current MeTTaIL Syntax (Scala)

### Example: ParMonoid

```scala
Theory ParMonoid(cm: CommutativeMonoid) {
    cm                    // Extend base theory
      Exports {
        Elem => Proc;     // Rename category
      }
      Replacements {
        [] Zero.Proc => PZero.Proc ::= "0";           // Override rule
        [0, 1] Plus.Proc => PPar.Proc ::= "(" Proc "|" Proc ")";
      }
      Rewrites {
        RPar1 : let Src ~> Tgt in
                ( PPar Src Q ) ~> ( PPar Tgt Q ) ;
      }
}
```

**Key concepts:**
1. **Parameter:** `cm: CommutativeMonoid` - takes another theory as input
2. **Extension:** `cm` - inherits all of cm's exports, terms, equations
3. **Renaming:** `Elem => Proc` - renames exported categories
4. **Replacement:** Override specific rules from base theory
5. **Addition:** Add new terms, equations, rewrites

---

## Design Goals

### Must Support

1. **Theory Parameters**
   - Syntax: `params: (t1: TheoryType1, t2: TheoryType2)`
   - Type checking: ensure parameter constraints are met
   - Instantiation: concrete theories passed at use time

2. **Theory Extension**
   - Inherit exports from parameter theories
   - Inherit terms (grammar rules)
   - Inherit equations and rewrites
   - Allow overriding/replacing inherited rules

3. **Category Renaming**
   - Syntax: `Elem => Proc` in exports
   - Propagate renames through all inherited rules
   - Type-safe: ensure renamed categories used consistently

4. **Replacement Rules**
   - Syntax: `[indices] OldLabel.Cat => NewLabel.Cat ::= ...`
   - Override specific rules from base theory
   - Indices specify which occurrences to replace

5. **Theory Composition**
   - Conjunction (`/\`): merge two theories
   - Disjunction (`\/`): union of theories
   - Subtraction (`\`): remove elements from theory

---

## Rust Implementation Strategy

### Option A: Runtime Composition (Simpler)

**Approach:** Keep theory descriptors at runtime, compose dynamically

```rust
theory! {
    name: ParMonoid,
    params: (cm: CommutativeMonoid),

    // At macro expansion, we just record the structure
    extends: cm,

    exports {
        Elem => Proc;  // Rename instruction
    },

    replacements {
        Zero => PZero;  // Replacement instruction
    }
}

// At runtime/instantiation:
impl ParMonoid {
    pub fn new(cm_instance: Box<dyn Theory>) -> Self {
        let mut theory = ParMonoid::empty();

        // Inherit from cm
        theory.inherit_from(&cm_instance);

        // Apply renames
        theory.rename_category("Elem", "Proc");

        // Apply replacements
        theory.replace_rule("Zero", Rule { /* new def */ });

        theory
    }
}
```

**Pros:**
- Simpler to implement
- Flexible at runtime
- Can load theories from network

**Cons:**
- Less type-safe
- Runtime overhead
- No compile-time checking of parameter constraints

### Option B: Compile-Time Expansion (More Complex)

**Approach:** Fully expand theories at compile time

```rust
theory! {
    name: ParMonoid,
    params: (cm: CommutativeMonoid),

    extends: cm,

    exports {
        Elem => Proc;
    }
}

// Macro generates:
pub struct ParMonoid<CM: CommutativeMonoid> {
    _phantom: PhantomData<CM>,
}

// Fully expanded AST types (renames applied)
pub enum Proc {
    // Inherited from CM, but Elem renamed to Proc
    PZero,  // Was Zero in CM
    PPar(Box<Proc>, Box<Proc>),  // Was Plus in CM
    // ... new terms added
}
```

**Pros:**
- Fully type-safe
- Zero runtime overhead
- Compile-time checking of constraints

**Cons:**
- Very complex macro implementation
- Long compile times
- Hard to do dynamic loading

### Option C: Hybrid (Recommended)

**Approach:** Compile-time for known theories, runtime for dynamic

```rust
// Compile-time path: fully expand
theory! {
    name: ParMonoid,
    params: (cm: CommutativeMonoid),
    extends: cm,
    // ... generates generic Rust code
}

// Runtime path: compose dynamically
let composed = TheoryComposer::new()
    .with_base(monoid_instance)
    .rename("Elem", "Proc")
    .add_terms(new_terms)
    .build();
```

---

## Implementation Phases

### Phase 0: Design (Current)
- [x] Document requirements
- [x] Evaluate options
- [ ] Design AST representation
- [ ] Design type system for theory parameters

### Phase 1.5: Basic Parameterization (2-3 weeks)
- [ ] Extend AST to track theory parameters
- [ ] Parse `extends: base` syntax
- [ ] Implement inheritance of exports
- [ ] Implement inheritance of terms
- [ ] Basic validation

### Phase 2: Full Composition (3-4 weeks)
- [ ] Category renaming
- [ ] Replacement rules
- [ ] Theory conjunction/disjunction
- [ ] Complex validation
- [ ] Full Rholang example

---

## AST Design

### Current (Phase 1)

```rust
pub struct TheoryDef {
    pub name: Ident,
    pub params: Vec<TheoryParam>,  // ✓ Already have
    pub exports: Vec<Export>,
    pub terms: Vec<GrammarRule>,
    pub equations: Vec<Equation>,
}
```

### Proposed (Phase 1.5)

```rust
pub struct TheoryDef {
    pub name: Ident,
    pub params: Vec<TheoryParam>,
    pub base: Option<TheoryBase>,  // NEW: What we extend
    pub exports: Vec<Export>,       // May include renames
    pub terms: Vec<GrammarRule>,
    pub replacements: Vec<Replacement>,  // NEW: Override rules
    pub equations: Vec<Equation>,
    pub rewrites: Vec<Rewrite>,
}

pub enum TheoryBase {
    Param(Ident),              // extends: cm (parameter name)
    Ref(syn::Path),            // extends: path::to::Theory
    Composition(TheoryComposition),  // extends: A /\ B
}

pub struct TheoryComposition {
    pub op: CompositionOp,
    pub left: Box<TheoryBase>,
    pub right: Box<TheoryBase>,
}

pub enum CompositionOp {
    Conjunction,   // /\
    Disjunction,   // \/
    Subtraction,   // \
}

pub struct Export {
    pub from: Option<Ident>,  // Rename: from => to
    pub to: Ident,
}

pub struct Replacement {
    pub indices: Vec<usize>,     // Which occurrences
    pub old_label: Ident,
    pub new_rule: GrammarRule,
}
```

---

## Syntax Design

### Proposed Rust Syntax

```rust
theory! {
    name: ParMonoid,

    // Parameters (already supported)
    params: (cm: CommutativeMonoid),

    // Base theory to extend (NEW)
    extends: cm,

    // Exports with optional renames (ENHANCED)
    exports {
        Elem => Proc;    // Rename from base
        NewCat;          // Add new category
    },

    // Terms (current - no change)
    terms {
        PZero . Proc ::= "0" ;
    },

    // Replacements (NEW)
    replacements {
        // Replace rule at index 0 with new definition
        [0] Zero.Elem => PZero.Proc ::= "0" ;
        // Replace rules at indices 0 and 1
        [0, 1] Plus.Elem => PPar.Proc ::= "(" Proc "|" Proc ")" ;
    },

    // Equations (current - no change)
    equations {
        (LHS) == (RHS) ;
    }
}
```

### Alternative: Explicit Body Block

```rust
theory! {
    name: ParMonoid,
    params: (cm: CommutativeMonoid),

    body: cm {  // Explicit "extend cm and add..."
        exports {
            Elem => Proc;
        },

        replacements {
            Zero => PZero;
        }
    }
}
```

---

## Type System for Theory Parameters

### Theory Types

```rust
// In user code:
use mettail::prelude::*;

// Theory parameter constraints
theory! {
    name: ParMonoid,
    params: (cm: CommutativeMonoid),  // cm must satisfy CommutativeMonoid
    // ...
}

// What is CommutativeMonoid?
// Option 1: Trait
pub trait CommutativeMonoid: Theory {
    // Must have these exports
    type Elem;

    // Must have these operations
    fn zero() -> Self::Elem;
    fn plus(a: Self::Elem, b: Self::Elem) -> Self::Elem;
}

// Option 2: Structural (duck typing)
// Just check that theory has required exports/terms

// Option 3: Named theory references
theory! {
    name: CommutativeMonoid,
    // ... definition
}

theory! {
    name: ParMonoid,
    params: (cm: theory!(CommutativeMonoid)),  // Reference by name
    // ...
}
```

---

## Inheritance & Merging Rules

### Exports

```
Base theory cm:
  exports { Elem; }

Extending theory ParMonoid:
  exports { Elem => Proc; }

Result:
  exports { Proc; }  // Renamed
```

### Terms

```
Base theory cm:
  terms {
    Zero . Elem ::= "0" ;
    Plus . Elem ::= Elem "+" Elem ;
  }

Extending theory ParMonoid:
  replacements {
    [0] Zero.Elem => PZero.Proc ::= "0" ;
  }

Result:
  terms {
    PZero . Proc ::= "0" ;           // Replaced & renamed
    Plus . Proc ::= Proc "+" Proc ;  // Inherited & renamed
  }
```

### Equations

```
Base theory cm:
  equations {
    (Plus Zero X) == X ;
  }

Extending theory ParMonoid:
  equations {
    (New equation) ;
  }

Result:
  equations {
    (Plus Zero X) == X ;    // Inherited (with renames applied)
    (New equation) ;         // Added
  }
```

---

## Validation Rules

### Parameter Constraints

1. **Type Checking:** Parameter theories must satisfy constraints
   ```rust
   theory! {
       name: ParMonoid,
       params: (cm: CommutativeMonoid),
       // Must check: does cm actually implement CommutativeMonoid?
   }
   ```

2. **Export Requirements:** Base theory must export required categories
   ```rust
   extends: cm,
   exports { Elem => Proc; }
   // Must check: does cm export 'Elem'?
   ```

3. **Replacement Validity:** Replaced rules must exist
   ```rust
   replacements {
       [0] Zero.Elem => PZero.Proc ::= "0" ;
       // Must check: does base have a Zero.Elem rule?
   }
   ```

---

## Examples

### Example 1: Simple Extension

```rust
theory! {
    name: Monoid,
    exports { Elem; },
    terms {
        Zero . Elem ::= "0" ;
        Plus . Elem ::= Elem "+" Elem ;
    }
}

theory! {
    name: ParMonoid,
    params: (m: Monoid),
    extends: m,
    exports {
        Elem => Proc;  // Rename
    }
}
```

### Example 2: Multiple Parameters

```rust
theory! {
    name: Rholang,
    params: (nr: NewReplCalc, rc: Rholang),
    extends: nr \/ rc,  // Disjunction
}
```

### Example 3: Nested Composition

```rust
theory! {
    name: FreeRholang,
    body: {
        let m = Monoid();
        let cm = CommutativeMonoid(m);
        let pm = ParMonoid(cm);
        let qd = QuoteDropCalc(pm);
        pm
    }
}
```

---

## Open Questions

1. **Syntax for instantiation?**
   - How do we actually pass concrete theories to parameters?
   - Compile-time vs runtime instantiation?

2. **Recursive theories?**
   - Can a theory reference itself?
   - How to handle circular dependencies?

3. **Module system?**
   - How do theories import other theories?
   - Namespacing?

4. **Dynamic loading?**
   - If theory received from network, how to instantiate?
   - Type safety?

---

## Recommendation

**For Phase 1:** Skip theory parameterization entirely. Focus on:
1. Type-checking
2. Parser generation
3. Equation support
4. Basic examples

**For Phase 1.5:** Implement basic extension without composition:
- Single base theory (`extends: base`)
- Simple inheritance (no renames yet)
- No replacements yet

**For Phase 2:** Full composition system:
- Category renaming
- Replacement rules
- Theory composition operators
- Complex validation

This allows us to build a solid foundation before tackling the complex composition logic.

---

## Timeline

- **Phase 1 (Current):** 2-3 weeks - Foundation without parameterization
- **Phase 1.5:** 2-3 weeks - Basic extension
- **Phase 2:** 3-4 weeks - Full composition
- **Total:** 7-10 weeks for complete theory system

---

**Status:** Design complete, implementation deferred to Phase 1.5
**Next:** Continue Phase 1 foundation work (type-checker, parser gen)

