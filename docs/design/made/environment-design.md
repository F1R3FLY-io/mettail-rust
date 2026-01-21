# Environment Infrastructure Design

## Goal

Enable REPL-style interaction where users can:
1. Define named terms: `p = n!(0)` → adds `p` to environment
2. Use terms with substitution: `{ p | q }` → substitutes environment variables, yields `{ n!(0) | n?x.{*(x)} }`
3. Apply rewrites: `rewrites` → applies rewrite rules to get `*(@(0))`
4. Use lambdas with explicit substitution: `(subst dup my_name)` → applies substitution

The key semantic distinction:
- **Environment substitution**: Happens *before* rewriting, replaces all variables simultaneously
- **Rewrite rules**: Happen *after* substitution, apply term transformations

## Core Design Principles

### 1. Eager Bulk Substitution (Not Lazy Rewrites)

The environment substitutes ALL variables simultaneously before any rewriting. This is not done via Ascent rewrite rules because:

- **Atomicity**: All substitutions happen at once, not interleaved with rewrites
- **Performance**: O(n) substitution pass rather than O(n) Ascent iterations  
- **Predictability**: Users see substituted term before rewrites apply
- **Capture-avoiding**: Uses existing `multi_substitute` infrastructure

```
Input: { p | q } where env = {p -> n!(0), q -> n?x.{*(x)}}
                              ↓
Step 1 (Substitution):        { n!(0) | n?x.{*(x)} }
                              ↓
Step 2 (Rewrites):            *(@(0))
```

### 2. Per-Category Environments

Each exported category gets its own environment type and substitution method:

```rust
// For theory with exports { Proc; Name; }
pub struct ProcEnv(HashMap<String, Proc>);
pub struct NameEnv(HashMap<String, Name>);

// Combined environment for the theory
pub struct RhoCalcEnv {
    pub proc: ProcEnv,
    pub name: NameEnv,
}
```

This enables type-safe storage and cross-category substitution.

### 3. Lambda Abstraction Support

Lambdas (`^name.body`) define deferred substitution:
- `dup = ^n.{n?x.{{ *(x) | n!(*(x)) }}}`
- `(subst dup my_name)` → applies `my_name` for `n` in body

Lambdas use a special `Lambda<Binder, Body>` variant, and `subst` triggers substitution.

## Architecture

### Generated Components

For a theory with `exports { Proc; Name; }`:

```
┌─────────────────────────────────────────────────────────────┐
│                    Generated Code                            │
├─────────────────────────────────────────────────────────────┤
│ AST Types (existing)                                         │
│   enum Proc { PZero, PVar(OrdVar), ... }                    │
│   enum Name { NQuote(Box<Proc>), NVar(OrdVar), ... }        │
├─────────────────────────────────────────────────────────────┤
│ Environment Types (NEW)                                      │
│   struct ProcEnv(HashMap<String, Proc>)                     │
│   struct NameEnv(HashMap<String, Name>)                     │
│   struct RhoCalcEnv { proc: ProcEnv, name: NameEnv }        │
├─────────────────────────────────────────────────────────────┤
│ Substitution Methods (existing + NEW)                        │
│   impl Proc {                                                │
│     fn substitute(&self, var, replacement) -> Self          │ ← existing
│     fn multi_substitute(&self, vars, repls) -> Self         │ ← existing
│     fn substitute_env(&self, env: &RhoCalcEnv) -> Self      │ ← NEW
│   }                                                          │
├─────────────────────────────────────────────────────────────┤
│ Ascent Relations (optional, for advanced queries)            │
│   relation env_proc(String, Proc);                          │
│   relation env_name(String, Name);                          │
└─────────────────────────────────────────────────────────────┘
```

### Data Flow

```
User Input: "{ p | q }"
     │
     ▼
┌─────────────────┐
│  Parse Term     │  → Proc::PPar({Proc::PVar("p"), Proc::PVar("q")})
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  Substitute Env │  → term.substitute_env(&env)
│  (all at once)  │  → Proc::PPar({Proc::POutput(...), Proc::PInput(...)})
└────────┬────────┘
         │
         ▼
┌─────────────────┐
│  Run Ascent     │  → Apply rewrites to substituted term
│  (rewrites)     │  → Proc::PDrop(...)
└────────┬────────┘
         │
         ▼
Normal Forms
```

## Implementation Plan

### Phase 1: Environment Types

**File: `macros/src/codegen/env.rs` (new)**

Generate for each exported category:

```rust
/// Per-category environment
#[derive(Debug, Clone, Default)]
pub struct ProcEnv(pub std::collections::HashMap<String, Proc>);

impl ProcEnv {
    pub fn new() -> Self { Self(HashMap::new()) }
    pub fn get(&self, name: &str) -> Option<&Proc> { self.0.get(name) }
    pub fn set(&mut self, name: String, value: Proc) { self.0.insert(name, value); }
    pub fn remove(&mut self, name: &str) -> Option<Proc> { self.0.remove(name) }
    pub fn iter(&self) -> impl Iterator<Item = (&String, &Proc)> { self.0.iter() }
    pub fn is_empty(&self) -> bool { self.0.is_empty() }
}
```

And a combined environment:

```rust
/// Combined environment for all categories
#[derive(Debug, Clone, Default)]
pub struct RhoCalcEnv {
    pub proc: ProcEnv,
    pub name: NameEnv,
}

impl RhoCalcEnv {
    pub fn new() -> Self { Self::default() }
}
```

### Phase 2: Environment Substitution Methods

**File: `macros/src/codegen/subst.rs` (extend)**

Generate `substitute_env` method for each category:

```rust
impl Proc {
    /// Substitute all environment variables in this term
    ///
    /// Replaces all free variables that match keys in the environment
    /// with their corresponding values. Substitution is capture-avoiding.
    pub fn substitute_env(&self, env: &RhoCalcEnv) -> Self {
        // Collect all Proc variables from env
        let proc_vars: Vec<&FreeVar<String>> = ...;
        let proc_repls: Vec<Proc> = ...;
        
        // Apply multi-substitute (capture-avoiding, all at once)
        self.multi_substitute(&proc_vars, &proc_repls)
    }
}
```

Key insight: This leverages the existing `multi_substitute` which:
- Is capture-avoiding (respects binders)
- Handles nested terms correctly
- Substitutes all variables simultaneously

### Phase 3: Assignment Parsing

**File: `macros/src/codegen/parser/lalrpop.rs` (extend)**

Add assignment syntax to the parser:

```
// Assignment: name = term
Assignment: (String, Proc) = {
    <name:Ident> "=" <term:Proc> => (name, term),
};

// Or as part of REPL input (in repl crate)
ReplInput: ReplCommand = {
    <name:Ident> "=" <term:Proc> => ReplCommand::Assign(name, term),
    <term:Proc> => ReplCommand::Eval(term),
};
```

### Phase 4: REPL Integration

**File: `repl/src/state.rs` (extend)**

Add environment to REPL state:

```rust
pub struct ReplState {
    // ... existing fields ...
    
    /// Environment for variable bindings
    environment: Option<Box<dyn std::any::Any>>,  // Theory-specific env type
}

impl ReplState {
    /// Get the environment, typed for a specific theory
    pub fn env<T: 'static>(&self) -> Option<&T> {
        self.environment.as_ref()?.downcast_ref::<T>()
    }
    
    /// Get mutable environment
    pub fn env_mut<T: 'static>(&mut self) -> Option<&mut T> {
        self.environment.as_mut()?.downcast_mut::<T>()
    }
}
```

**File: `repl/src/repl.rs` (extend)**

Handle assignment commands:

```rust
fn handle_command(&mut self, line: &str) -> Result<()> {
    // Check for assignment: "name = term"
    if let Some((name, term_str)) = parse_assignment(line) {
        return self.cmd_assign(&name, term_str);
    }
    
    // Otherwise parse as term (with env substitution)
    self.cmd_eval(line)
}

fn cmd_assign(&mut self, name: &str, term_str: &str) -> Result<()> {
    let term = self.parse_term(term_str)?;
    
    // Get environment and add binding
    let env = self.get_or_create_env();
    env.proc.set(name.to_string(), term);
    
    println!("{} added to environment", name);
    Ok(())
}

fn cmd_eval(&mut self, term_str: &str) -> Result<()> {
    let term = self.parse_term(term_str)?;
    
    // Step 1: Substitute environment variables
    let env = self.get_env();
    let substituted = term.substitute_env(env);
    
    println!("Substituted: {}", substituted);
    
    // Step 2: Run Ascent rewrites
    let results = self.run_ascent(substituted)?;
    
    // ... display results ...
}
```

### Phase 5: Lambda/Subst Support (Optional Enhancement)

For explicit lambda abstraction and substitution:

```
// Syntax in theory definition:
Lambda . Name, ^[n].p:[Name -> Proc] |- "^" n "." "{" p "}" : LambdaProc ;

// Usage:
> dup = ^n.{n?x.{{ *(x) | n!(*(x)) }}}
> (subst dup my_name)
```

This uses existing `Scope` infrastructure with a new wrapper type.

## Design Decisions

### Why Not Ascent Relations for Environment?

We *could* use Ascent relations:
```
relation env_proc(String, Proc);
// Rule: if env_proc(x, v) then (PVar x) => v;
```

But this has drawbacks:
1. **Interleaving**: Substitution happens *during* rewriting, not before
2. **Non-determinism**: Order of substitution vs rewrite is undefined
3. **Performance**: Each substitution is an Ascent fixpoint iteration
4. **Semantics**: Doesn't match user mental model (define first, then rewrite)

The eager substitution approach is cleaner and matches user expectations.

### Why Per-Category Environments?

Rather than a single `Map<String, Term>`:
1. **Type safety**: Proc variables hold Proc values, Name variables hold Name values
2. **Clear semantics**: Cross-category substitution (Proc containing Name vars) is explicit
3. **Efficiency**: No runtime type checks

### Why Multi-Substitute?

Single substitution in a loop is wrong:
```rust
// WRONG: Sequential substitution can cause issues
for (var, val) in env {
    term = term.substitute(&var, &val);  // val might contain vars!
}
```

Multi-substitute is correct:
```rust
// CORRECT: All substitutions happen simultaneously
term = term.multi_substitute(&vars, &vals);
```

This prevents substituted values from being further substituted.

## Summary of Changes

| Component | File | Change |
|-----------|------|--------|
| Environment types | `codegen/env.rs` (new) | Generate `ProcEnv`, `NameEnv`, `TheoryEnv` |
| Substitution | `codegen/subst.rs` | Add `substitute_env` method generation |
| AST generation | `codegen/ast_gen.rs` | Call env generation |
| Codegen mod | `codegen/mod.rs` | Export env module |
| REPL state | `repl/src/state.rs` | Add environment field |
| REPL commands | `repl/src/repl.rs` | Add assignment handling, env substitution |
| Theory trait | `repl/src/theory.rs` | Add env-related methods |

## User Interaction Examples

```
rhocalc> p = n!(0)
[added p to environment]

rhocalc> q = n?x.{*(x)}
[added q to environment]

rhocalc> { p | q }
Substituted: { n!(0) | n?x.{*(x)} }
Running Ascent...
Normal forms:
  0) *(@(0))

rhocalc> env
  p = n!(0)
  q = n?x.{*(x)}

rhocalc> clear p
[removed p from environment]
```

## Future Extensions

1. **Persistent environments**: Save/load environment to file
2. **Environment scoping**: Push/pop environment frames
3. **Import from file**: `load definitions.rho`
4. **Type annotations**: `p : Proc = n!(0)`
