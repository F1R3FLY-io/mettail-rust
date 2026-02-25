# Module 4: The Calculator Language

**Goal**: Understand a complete language definition with no variable binding.

The Calculator is the simplest language in MeTTaIL. It has no variables, no binding, no processes - just arithmetic, booleans, strings, and type casts. This makes it the perfect place to learn the `language!` macro syntax before tackling the complexity of rho-calculus.

---

## 4.1 The Full Definition

Open `languages/src/calculator.rs`. The entire language is defined in a single `language!` macro invocation. Let's break it down section by section.

### The Header

```rust
use mettail_macros::language;

language! {
    name: Calculator,
```

Every language definition starts with a `name`. This becomes:
- The `CalculatorLanguage` struct (implements `Language`)
- The prefix for generated Ascent structs
- The name used in the REPL (`lang calculator`)

### Types

```rust
    types {
        ![i32] as Int
        ![f64] as Float
        ![bool] as Bool
        ![str] as Str
    },
```

These define the **categories** (sorts) of the language. The `![rust_type] as Name` syntax means "wrap this Rust native type as a language category."

From this, the macro generates:
```rust
enum Int {
    NumLit(i32),    // Native literal: 42
    IVar(OrdVar),   // Variable: x (auto-generated)
    // ... term constructors added below
    LamInt(...)     // Auto-generated lambda
    ApplyInt(...)   // Auto-generated application
}
```

Each category always gets:
- A **literal variant** (e.g., `NumLit(i32)`) for native values
- A **variable variant** (e.g., `IVar(OrdVar)`) for symbolic variables
- **Lambda/Apply variants** for higher-order metaprogramming
- All term constructor variants defined in the `terms` section

---

## 4.2 Term Declarations: The Syntax

Terms are the heart of the language definition. Here's the general form:

```
ConstructorName . field1:Type1, field2:Type2 |- syntax_tokens : ResultType ![eval_expr] strategy;
```

Let's decode each piece using a real example:

```rust
AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
```

| Part | Meaning |
|------|---------|
| `AddInt` | Constructor name (becomes an enum variant) |
| `a:Int, b:Int` | Fields: `a` and `b`, both of type `Int` |
| `\|-` | Separator between fields and syntax |
| `a "+" b` | Surface syntax: field `a`, then literal `+`, then field `b` |
| `: Int` | Result type (this constructor produces an `Int`) |
| `![a + b]` | Native evaluation: when both operands are literals, compute `a + b` in Rust |
| `fold` | Evaluation strategy |

### Syntax Tokens

The part between `|-` and `:` defines how terms are parsed and displayed:

- **Field references**: `a`, `b` - placeholders for the subterms
- **String literals**: `"+"`, `"("`, `")"` - literal tokens in the syntax
- Mixed freely: `a "+" b` means "parse a, then +, then b"

More examples:
```rust
Neg . a:Int |- "-" a : Int                    // prefix: -a
Fact . a:Int |- a "!" : Int                   // postfix: a!
PowInt . a:Int, b:Int |- a "^" b : Int        // infix: a ^ b
SinFloat . a:Float |- "sin" "(" a ")" : Float // function call: sin(a)
Len . s:Str |- "|" s "|" : Int               // delimited: |s|
```

### Native Evaluation Blocks: `![...]`

The `![expr]` block tells the macro how to compute the result when all operands are known native values:

```rust
// Simple expression - directly evaluates
AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold;

// Method call
SinFloat . a:Float |- "sin" "(" a ")" : Float ![a.sin()] step;

// Block expression (for complex logic)
Fact . a:Int |- a "!" : Int ![{ (1..=a.max(0)).product::<i32>() }] step;

// Pattern matching (for type dispatch)
Tern . c:Int, t:Int, e:Int |- c "?" t ":" e : Int ![{ if c != 0 { t } else { e } }] step right;
```

Inside `![...]`, `a` and `b` refer to the *unwrapped* native values (e.g., `i32`, not `Int`). The macro handles the unwrapping.

### Evaluation Strategies: `fold` vs `step`

**`fold`** - Eagerly evaluate during normalization. When the term is constructed, if all operands are ground (no free variables), compute the result immediately. Used for basic arithmetic where you always want the answer:

```rust
AddInt . a:Int, b:Int |- a "+" b : Int ![a + b] fold;
// "2 + 3" is immediately normalized to "5" before Ascent even runs
```

**`step`** - Only evaluate during Ascent rewriting, one step at a time. Used for operations where you might want to see intermediate steps:

```rust
Fact . a:Int |- a "!" : Int ![{ (1..=a.max(0)).product::<i32>() }] step;
// "3!" stays as "3!" until Ascent rewrites it to "6"
```

### Associativity: `right`

```rust
PowInt . a:Int, b:Int |- a "^" b : Int ![a.pow(b as u32)] step right;
```

The `right` keyword makes the operator right-associative:
- `2 ^ 3 ^ 2` = `2 ^ (3 ^ 2)` = `2 ^ 9` = `512` (not `(2 ^ 3) ^ 2` = `64`)

Without `right`, operators are left-associative by default.

---

## 4.3 Operator Precedence

The order of term declarations determines precedence. Terms declared **earlier** have **lower** precedence (bind less tightly). In the Calculator:

```rust
// Lowest precedence (declared first):
Tern . c:Int, t:Int, e:Int |- c "?" t ":" e    // ternary
EqInt . a:Int, b:Int |- a "==" b                 // comparison
// ...
Not . a:Bool |- "not" a                          // unary not
And . a:Bool, b:Bool |- a "and" b                // boolean and
Or . a:Bool, b:Bool |- a "or" b                  // boolean or
// ...
AddInt . a:Int, b:Int |- a "+" b                 // addition
SubInt . a:Int, b:Int |- a "-" b                 // subtraction
MulInt . a:Int, b:Int |- a "*" b                 // multiplication
DivInt . a:Int, b:Int |- a "/" b                 // division
// Highest precedence (declared last):
PowInt . a:Int, b:Int |- a "^" b                 // exponentiation
Neg . a:Int |- "-" a                             // unary negation
Fact . a:Int |- a "!"                            // factorial
```

So `2 + 3 * 4` parses as `2 + (3 * 4)` because `Mul` is declared after `Add`.

---

## 4.4 Equations

The Calculator has no equations:

```rust
    equations {
    },
```

Equations define structural identities. The Calculator doesn't need them because all its types are native - there are no structural equivalences to declare.

(In contrast, RhoCalc has `@(*(n)) = n` - quoting an unquote is the identity.)

---

## 4.5 Rewrite Rules

### What Are Congruence Rules?

The Calculator's `rewrites` section is almost entirely **congruence rules**. These have the form:

```rust
AddIntCongL . | S ~> T |- (AddInt S R) ~> (AddInt T R);
AddIntCongR . | S ~> T |- (AddInt L S) ~> (AddInt L T);
```

Reading this:

```
AddIntCongL . | S ~> T |- (AddInt S R) ~> (AddInt T R);
^^^^^^^^^^^^   ^^^^^^^    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
rule name      premise         conclusion
```

- **Premise**: `S ~> T` means "if term S rewrites to term T"
- **Conclusion**: `(AddInt S R) ~> (AddInt T R)` means "then AddInt(S, R) rewrites to AddInt(T, R)"

In plain English: **if a subterm rewrites, the enclosing term rewrites too**. This is how computation propagates through expressions:

```
3! + 2 ^ 3
= 6 + 2 ^ 3        (Fact rewrites 3! to 6 — propagated by AddIntCongL)
= 6 + 8             (PowInt rewrites 2^3 to 8 — propagated by AddIntCongR)
= 14                (AddInt evaluates 6+8 to 14 — native eval)
```

### Why Two Rules Per Operator?

Binary operators need **two** congruence rules:
- `CongL` ("left congruence"): if the left operand rewrites, the whole expression rewrites
- `CongR` ("right congruence"): if the right operand rewrites, the whole expression rewrites

Unary operators need one:
- `NegCong . | S ~> T |- (Neg S) ~> (Neg T);`

### Why Are These Necessary?

Without congruence rules, Ascent would only apply native evaluation to the outermost term. Consider `(2 + 3) * 4`:

- Structure: `MulInt(AddInt(NumLit(2), NumLit(3)), NumLit(4))`
- Native eval can reduce `AddInt(2, 3)` to `5` (that's a rewrite)
- But without `MulIntCongL`, the outer `MulInt` doesn't know its left operand changed
- With `MulIntCongL`: since `AddInt(2,3) ~> 5`, we get `MulInt(AddInt(2,3), 4) ~> MulInt(5, 4)`
- Then native eval reduces `MulInt(5, 4)` to `20`

---

## 4.6 What Gets Generated

From the Calculator definition, the macro generates ~110KB of Rust code in `languages/src/generated/calculator-datalog.rs`. Here's a high-level map:

### AST Enums
```rust
enum Int {
    NumLit(i32),
    IVar(OrdVar),
    AddInt(Box<Int>, Box<Int>),
    SubInt(Box<Int>, Box<Int>),
    MulInt(Box<Int>, Box<Int>),
    DivInt(Box<Int>, Box<Int>),
    ModInt(Box<Int>, Box<Int>),
    PowInt(Box<Int>, Box<Int>),
    Neg(Box<Int>),
    Fact(Box<Int>),
    CustomOp(Box<Int>, Box<Int>),
    Tern(Box<Int>, Box<Int>, Box<Int>),
    // ... type casts, comparisons that return Int
    LamInt(Scope<Binder<String>, Int>),
    ApplyInt(Box<Int>, Box<Int>),
    // ...
}
// Similar for Float, Bool, Str
```

### Display
```rust
impl Display for Int {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Int::NumLit(n) => write!(f, "{}", n),
            Int::AddInt(a, b) => write!(f, "{} + {}", a, b),
            Int::Neg(a) => write!(f, "-{}", a),
            Int::Fact(a) => write!(f, "{}!", a),
            // ... etc
        }
    }
}
```

### Parser
Generated PraTTaIL Pratt parser with correct precedence and associativity.

### Ascent Program
```rust
ascent! {
    struct CalculatorAscent;

    // Relations
    relation int_term(Int);
    relation rw_int(Int, Int);
    // ...

    // Deconstruction: extract subterms
    int_term(a), int_term(b) <-- int_term(t), if let Int::AddInt(a,b) = t;

    // Rewrite: native eval (AddInt)
    rw_int(t, result) <-- int_term(t), if let Int::AddInt(a,b) = t,
                          if let Int::NumLit(av) = a, if let Int::NumLit(bv) = b,
                          let result = Int::NumLit(av + bv);

    // Congruence: AddIntCongL
    rw_int(Int::AddInt(s,r), Int::AddInt(t,r)) <--
        int_term(whole), if let Int::AddInt(s,r) = whole,
        rw_int(s.clone(), t);

    // ... hundreds more rules
}
```

---

## 4.7 Exercises

### Exercise 1: Inventory

Read `languages/src/calculator.rs` and answer:
1. How many types does Calculator define?
2. How many term constructors are there? (Count the lines between `terms {` and `}`)
3. How many rewrite rules? Are any of them *not* congruence rules?

### Exercise 2: REPL Exploration

```bash
cargo run -- calculator
```

Try these and predict the results before hitting enter:

```
exec 3! + 2 ^ 3
exec 2 ^ 3 ^ 2
exec 10 ? 42 : 0
exec 0 ? 42 : 99
exec |"hello"|
exec "hello" ++ " " ++ "world"
exec 3 + 4 == 7
exec int(3.14)
exec float(42)
exec str(true)
```

### Exercise 3: Add a New Operator

Add an absolute value operator to Calculator. Here's a step-by-step guide:

1. Open `languages/src/calculator.rs`

2. Add the term declaration (put it near `Neg`):
```rust
Abs . a:Int |- "abs" "(" a ")" : Int ![a.abs()] step;
```

3. Add a congruence rule in the `rewrites` section:
```rust
AbsCong . | S ~> T |- (Abs S) ~> (Abs T);
```

4. Test it:
```bash
cargo test -p mettail-languages
cargo run -- calculator
# Then in REPL:
exec abs(-5)
exec abs(3)
exec abs(-2 + -3)
```

### Exercise 4: Trace a Computation

For the expression `3! + 2 ^ 3`, trace the complete evaluation:

1. What AST does the parser produce?
2. Which native evals fire during normalization (fold)?
3. What terms does Ascent compute?
4. What's the rewrite chain from start to normal form?
5. How many total terms and rewrites does `exec` report?

Run it in the REPL and check your answers:
```
exec 3! + 2 ^ 3
rewrites
```

---

## Checkpoint

Before moving on, make sure you can:

1. **Read** a `language!` definition and identify types, terms, equations, and rewrites
2. **Explain** what each part of a term declaration means: `Name . fields |- syntax : Type ![eval] strategy`
3. **Explain** what congruence rules do and why they're needed
4. **Explain** the difference between `fold` and `step`
5. **Add** a simple operator to Calculator and verify it works

---

**Next**: [Module 5: The RhoCalc Language](05-rhocalc-language.md) - Variable binding, collections, and concurrent communication
