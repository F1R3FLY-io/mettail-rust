# Module 2: The Big Picture

**Goal**: Understand the *problem* MeTTaIL solves and how the pieces fit together.

---

## 2.1 What Is a Formal Language?

A formal language isn't a programming language you ship to production (at least not yet). It's a precise mathematical description of a system: what objects exist, how they're written, and how they compute.

MeTTaIL lets you define formal languages with four components:

### Types (Categories)

The kinds of things that exist in your language:

```
types {
    Proc        -- processes (things that compute)
    Name        -- names (channels/addresses)
    ![i32] as Int    -- native Rust i32, called "Int"
}
```

### Terms (Constructors)

How you build values of each type. Each term has a **name**, **fields**, **syntax**, and a **type**:

```
POutput . n:Name, q:Proc |- n "!" "(" q ")" : Proc ;
^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^  ^^^^
name and fields              surface syntax     result type
```

This says: `POutput` takes a `Name` and a `Proc`, is written as `n!(q)`, and produces a `Proc`.

### Equations

Structural identities - terms that are equal by definition:

```
equations {
    (NQuote (PDrop N)) = N ;
}
```

This says: quoting an unquote is the identity. If `N` is a name, then `@(*(N))` equals `N`. This is like saying `*(&x) == x` in C.

### Rewrites

Computation rules - directed reductions:

```
rewrites {
    (PPar {(PInput n ^x.p), (POutput n q), ...rest})
        ~> (PPar {(subst ^x.p (NQuote q)), ...rest});
}
```

This is the **COMM rule**: when a receiver and sender share a channel, the message is delivered. The receiver's body `p` gets the message substituted in, and the rest of the parallel composition continues.

---

## 2.2 What Is the Rho-Calculus?

The rho-calculus is the specific formal language that motivates MeTTaIL. It's a **process algebra** - a mathematical model of concurrent computation.

### Core Ideas

**Processes** are things that compute. They can:
- Do nothing: `{}` (the stopped process)
- Run in parallel: `{ P | Q }` (P and Q run simultaneously)
- Send a message: `n!(q)` (send process `q` on channel `n`)
- Receive a message: `n?x.{p}` (receive on channel `n`, bind it to `x`, then run `p`)
- Create a private channel: `new(x) in { p }` (fresh channel `x`, only visible inside `p`)

**Names** are channels. The key insight of rho-calculus: **names are quoted processes**. The name `@(P)` is the "address" of process `P`. And `*(n)` dereferences a name back to a process.

### A Concrete Example

```
{ @(0)!({}) | @(0)?x.{*(x)} }
```

Reading this:
- `@(0)` is the name obtained by quoting the null process `0`
- `@(0)!({})` sends the null process `{}` on channel `@(0)`
- `@(0)?x.{*(x)}` receives on channel `@(0)`, binds the message to `x`, then dereferences `x`
- `|` means these run in parallel

When the COMM rule fires:
1. Send and receive match on channel `@(0)`
2. The message `{}` is delivered
3. `x` gets bound to `@({})` (the quoted message)
4. `*(x)` becomes `*(@({}))` which equals `{}` by the equation `*(@ P) = P`
5. Result: `{}`

### Why Does This Matter?

The rho-calculus is the theoretical foundation of **Rholang** and the **f1r3fly** blockchain network. By implementing it precisely in MeTTaIL, you can:
- Verify that programs behave correctly
- Explore term rewriting step by step
- Prove properties about concurrent systems
- Eventually compile and deploy to the f1r3fly network

---

## 2.3 The `language!` Macro: One Definition Generates Everything

The central idea of MeTTaIL is that you write **one** definition and get **everything**:

```rust
// languages/src/calculator.rs (simplified)
language! {
    name: Calculator,

    types {
        ![i32] as Int
    },

    terms {
        AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
        SubInt . a:Int, b:Int |- a "-" b : Int ![a - b] fold;
        MulInt . a:Int, b:Int |- a "*" b : Int ![a * b] fold;
    },

    equations { },

    rewrites {
        AddIntCongL . | S ~> T |- (AddInt S R) ~> (AddInt T R);
        AddIntCongR . | S ~> T |- (AddInt L S) ~> (AddInt L T);
        // ...
    },
}
```

From this, the `language!` macro generates:

### 1. AST Enums

```rust
// Generated:
enum Int {
    NumLit(i32),       // Native literal
    IVar(OrdVar),      // Variable
    AddInt(Box<Int>, Box<Int>),
    SubInt(Box<Int>, Box<Int>),
    MulInt(Box<Int>, Box<Int>),
    // + auto-generated LamInt, ApplyInt for lambdas
}
```

### 2. Parser

A complete parser that turns strings into AST nodes:

```rust
// Generated (via PraTTaIL):
Int::parse("2 + 3 * 4")
// → Ok(AddInt(NumLit(2), MulInt(NumLit(3), NumLit(4))))
```

Handles operator precedence, parentheses, literals, variables - everything.

### 3. Display (Pretty-Printer)

The inverse of parsing - turns AST back into readable strings:

```rust
// Generated:
impl Display for Int { ... }

format!("{}", AddInt(NumLit(2), NumLit(3)))
// → "2 + 3"
```

### 4. Substitution

Capture-avoiding substitution for variable binding:

```rust
// Generated:
impl Int {
    pub fn substitute_int(&self, var: &Binder<String>, replacement: &Int) -> Int { ... }
}
```

### 5. Datalog Rewrite Engine

An Ascent program that computes all rewrites to fixpoint:

```rust
// Generated (in languages/src/generated/calculator-datalog.rs):
ascent! {
    struct CalculatorAscent;
    relation int_term(Int);
    relation rw_int(Int, Int);
    // ... hundreds of rules
}
```

### 6. Language Trait Implementation

Ties everything together:

```rust
// Generated:
pub struct CalculatorLanguage;
impl Language for CalculatorLanguage {
    fn name(&self) -> &'static str { "Calculator" }
    fn parse_term(&self, input: &str) -> Result<Box<dyn Term>, String> { ... }
    fn run_ascent(&self, term: &dyn Term) -> Result<AscentResults, String> { ... }
    // ...
}
```

---

## 2.4 The Five Generated Artifacts in Detail

Let's trace what happens when you type `exec 2 + 3 * 4` in the REPL with the Calculator language loaded:

### Step 1: Parsing

```
Input: "2 + 3 * 4"
                    ↓ PraTTaIL lexer + parser
AST: AddInt(NumLit(2), MulInt(NumLit(3), NumLit(4)))
```

The parser knows that `*` binds tighter than `+` because of how the grammar rules are structured (Pratt parsing with binding powers).

### Step 2: Normalization

For the Calculator, this includes **native evaluation** - the `![a + b]` blocks:

```
AddInt(NumLit(2), MulInt(NumLit(3), NumLit(4)))
                    ↓ evaluate MulInt: 3 * 4 = 12
AddInt(NumLit(2), NumLit(12))
                    ↓ evaluate AddInt: 2 + 12 = 14
NumLit(14)
```

### Step 3: Ascent Execution

The normalized term is fed into the generated Ascent program:

```
Seed: int_term(NumLit(14))
Rules fire → deconstruct, check rewrites, check equations
Fixpoint reached: NumLit(14) is already a normal form
```

### Step 4: Results Collection

```
AscentResults {
    all_terms: [TermInfo { display: "14", is_normal_form: true, ... }],
    rewrites: [],           // No rewrites from a literal
    equivalences: [],       // No equations apply
}
```

### Step 5: Display

```
Current term: 14
  - 1 term
  - 0 rewrites
  - 1 normal form
```

For RhoCalc, steps 2-4 are much more interesting because terms have real rewrites (COMM, Exec) and equations (QuoteDrop, Extrusion).

---

## 2.5 How the REPL Ties It All Together

The REPL (`repl/src/`) is the user-facing application. Here's the architecture:

```
User types command
        ↓
    Repl::handle_command()     [repl/src/repl.rs]
        ↓
    ┌───────────────────────────────────────┐
    │ "lang rhocalc"                        │
    │   → registry.get("rhocalc")           │
    │   → state.set_language(RhoCalcLang)   │
    │                                       │
    │ "exec { @(0)!({}) | @(0)?x.{*(x)} }" │
    │   → language.parse_term(input)        │  ← Generated parser
    │   → language.substitute_env(term)     │  ← Env vars replaced
    │   → language.run_ascent(term)         │  ← Datalog fixpoint
    │   → display results                   │
    │                                       │
    │ "rewrites"                            │
    │   → results.rewrites_from(current_id) │
    │   → display rewrite targets           │
    │                                       │
    │ "apply 0"                             │
    │   → follow rewrite edge               │
    │   → run_ascent on new term            │
    │   → display results                   │
    └───────────────────────────────────────┘
```

### The Language Registry

```rust
// repl/src/registry.rs
pub struct LanguageRegistry {
    languages: HashMap<String, Box<dyn Language>>,
}
```

When you type `lang rhocalc`, the REPL looks up `"rhocalc"` in the registry and gets back a `Box<dyn Language>` - a trait object that can parse, execute, and display terms for that language.

### The State Machine

```rust
// repl/src/state.rs
pub struct ReplState {
    language_name: Option<String>,
    current_term: Option<Box<dyn Term>>,
    ascent_results: Option<AscentResults>,
    history: Vec<HistoryEntry>,
    environment: Option<Box<dyn Any + Send + Sync>>,
}
```

The REPL maintains state between commands. `exec` sets the current term and results. `apply` follows a rewrite and updates the state. `env` manages variable bindings that get substituted into future `exec` calls.

---

## 2.6 The Crate Dependency Graph

Understanding which crate depends on which helps you know where to look:

```
                macros
               /      \
              /        \
         prattail   ascent_syntax_export
              \        /
               \      /
              languages  ←── runtime
                  |
                  ↓
                repl  ←── query
```

- `macros` depends on `prattail` (for parser generation) and `ascent_syntax_export` (for Datalog code generation)
- `languages` depends on `macros` (uses the `language!` macro) and `runtime` (uses `HashBag`, `Scope`, etc.)
- `repl` depends on `languages` (the concrete language implementations) and `query` (for custom Datalog queries)

When you change `runtime`, everything downstream recompiles. When you change `macros`, the languages recompile (and their generated code changes). When you change `repl`, only the binary recompiles.

---

## 2.7 Hands-On: Your First REPL Session

### Exercise 1: Calculator

```bash
cargo run
```

```
mettail> lang calculator
mettail> exec 2 + 3 * 4
mettail> exec 3! + 2 ^ 3
mettail> exec (1 + 2) * (3 + 4)
mettail> exec 10 > 5
mettail> exec "hello" ++ " world"
```

Try:
- What does `3!` evaluate to?
- What does `2 ^ 3 ^ 2` evaluate to? (Hint: `^` is right-associative)
- What does `10 ? 42 : 0` evaluate to?

### Exercise 2: RhoCalc

```
mettail> lang rhocalc
mettail> exec {}
mettail> exec { @(0)!({}) }
mettail> exec { @(0)!({}) | @(0)?x.{*(x)} }
mettail> rewrites
mettail> apply 0
mettail> rewrites
```

Try:
- What happens after each `apply`?
- When do you reach a normal form (no more rewrites)?
- Use `normal-forms` to see all normal forms at once

### Exercise 3: Environment

```
mettail> lang rhocalc
mettail> env
mettail> list-examples
mettail> exec { server!(request) | $proc($name($name(rep, location), server), id) }
mettail> rewrites
mettail> apply 0
mettail> apply 0
```

The `$name(...)` and `$proc(...)` syntax applies lambda expressions from the environment. The environment comes pre-loaded with useful combinators like `rep` (replication), `id` (identity), `fwd` (forwarding), etc.

### Exercise 4: Draw the Data Flow

On paper (or in your head), trace what happens when you type:

```
exec { @(0)!({}) | @(0)?x.{*(x)} }
```

1. Where does the string go first?
2. What function parses it?
3. What AST does it produce?
4. What does Ascent do with it?
5. What rewrites are available?
6. What does each rewrite produce?

If you can answer these, you understand the big picture.

---

## Checkpoint

Before moving on, make sure you can:

1. **Explain** in your own words what the four parts of a language definition are (types, terms, equations, rewrites)
2. **Describe** what the `language!` macro generates from a definition
3. **Use** the REPL to load a language, execute terms, and explore rewrites
4. **Trace** the data flow from user input to displayed results
5. **Name** the seven workspace crates and what each one does

---

**Next**: [Module 3: The Runtime Layer](03-runtime-layer.md) - The traits and types everything depends on
