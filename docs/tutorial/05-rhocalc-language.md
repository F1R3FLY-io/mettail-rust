# Module 5: The RhoCalc Language

**Goal**: Understand variable binding, collections, equations, and the COMM rule.

RhoCalc is the flagship language of MeTTaIL - a full implementation of the rho-calculus with native arithmetic, strings, and booleans. If the Calculator was "Hello World", this is the real thing.

---

## 5.1 Types

```rust
types {
    Proc
    Name
    ![i64] as Int
    ![f64] as Float
    ![bool] as Bool
    ![str] as Str
}
```

Two **abstract** types (`Proc`, `Name`) and four **native** types. Unlike Calculator where everything is native, RhoCalc has types with no underlying Rust representation - they exist purely as symbolic AST structures.

- **Proc** (Process) - Things that compute: send, receive, parallel composition, etc.
- **Name** (Channel) - Addresses for communication. In rho-calculus, names are quoted processes.

---

## 5.2 Core Constructors

Let's go through each constructor in `rhocalc.rs`:

### PZero - The Null Process

```rust
PZero . |- "{}" : Proc;
```

No fields. Syntax is just `{}`. Represents a stopped process that does nothing.

### PDrop - Dereference (Unquote)

```rust
PDrop . n:Name |- "*" "(" n ")" : Proc ;
```

Takes a `Name`, produces a `Proc`. Syntax: `*(n)`. This "runs" a name - if `n = @(P)`, then `*(n)` reduces to `P`.

### PPar - Parallel Composition

```rust
PPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc;
```

This one introduces new syntax elements:

- **`ps:HashBag(Proc)`** - The field `ps` is a `HashBag` of processes (a multiset)
- **`ps.*sep("|")`** - Display/parse the elements separated by `|`
- Wrapped in `"{" ... "}"` delimiters

So `{ P | Q | R }` is `PPar(HashBag::from_iter([P, Q, R]))`.

Because `HashBag` is unordered, `{ P | Q }` and `{ Q | P }` are structurally identical - no equation needed.

### POutput - Send

```rust
POutput . n:Name, q:Proc |- n "!" "(" q ")" : Proc ;
```

Send process `q` on channel `n`. Syntax: `n!(q)`.

### PInputs - Receive (Multi-Input / Join)

```rust
PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc]
|- "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")" "." "{" p "}" : Proc ;
```

This is the most complex constructor. Let's unpack it:

**Fields**:
- `ns:Vec(Name)` - A vector of channel names to receive on
- `^[xs].p:[Name* -> Proc]` - A binding: `xs` is a vector of bound variable names, `p` is the body process

**The binding syntax**:
- `^` marks a binder
- `[xs]` means `xs` is a vector of binders (for multi-input)
- `.p` is the body (scope of the binding)
- `:[Name* -> Proc]` is the type: a multi-argument function from Names to Proc

**The syntax pattern**:
- `*zip(ns,xs)` - Zip the channel names with the bound variables
- `.*map(|n,x| n "?" x)` - For each pair, write `n?x`
- `.*sep(",")` - Separate pairs with commas
- Wrapped in `"(" ... ")" "." "{" p "}"`

**Single input** example: `@(0)?x.{*(x)}`
- One channel `@(0)`, one variable `x`, body `*(x)`

**Join (multi-input)** example: `(@(0)?x, @(1)?y).{*(x)}`
- Two channels `@(0)` and `@(1)`, two variables `x` and `y`, body `*(x)`

### NQuote - Quote (Name a Process)

```rust
NQuote . p:Proc |- "@" "(" p ")" : Name ;
```

Takes a `Proc`, produces a `Name`. Syntax: `@(P)`. This is the fundamental operation of rho-calculus: turning a process into an address.

### PNew - Name Restriction

```rust
PNew . ^[xs].p:[Name* -> Proc]
|- "new" "(" xs.*sep(",") ")" "in" "{" p "}" : Proc;
```

Create private channels. Syntax: `new(x,y) in { p }`. The variables `x` and `y` are fresh names visible only inside `p`.

Uses the same multi-binder syntax as PInputs, but here the bound variable names appear directly in the syntax (not zipped with channels).

### Err - Error Term

```rust
Err . |- "error" : Proc;
```

A sentinel value for failed operations (like dividing by zero in native ops).

### Native Type Casts and Operations

```rust
CastInt . k:Int |- k : Proc;      // Int as Proc
CastFloat . k:Float |- k : Proc;  // Float as Proc
CastBool . k:Bool |- k : Proc;    // Bool as Proc
CastStr . s:Str |- s : Proc;      // Str as Proc

Add . a:Proc, b:Proc |- a "+" b : Proc ![{ match (&a, &b) { ... } }] fold;
Sub . a:Proc, b:Proc |- a "-" b : Proc ![{ match (&a, &b) { ... } }] fold;
// ... Mul, Div, Eq, Ne, Gt, Lt, etc.
```

The native ops on RhoCalc work at the `Proc` level (not `Int` level like Calculator). The eval blocks must pattern-match to extract the native values:

```rust
Add . a:Proc, b:Proc |- a "+" b : Proc ![
    { match (&a, &b) {
        (Proc::CastInt(a), Proc::CastInt(b)) => Proc::CastInt(Box::new(*a.clone() + *b.clone())),
        (Proc::CastFloat(a), Proc::CastFloat(b)) => Proc::CastFloat(Box::new(*a.clone() + *b.clone())),
        _ => Proc::Err,
    }}
] fold;
```

---

## 5.3 Equations

### QuoteDrop: The Reflection Equation

```rust
QuoteDrop . |- (NQuote (PDrop N)) = N ;
```

This says: `@(*(N)) = N` for any name `N`. Quoting a dereference gives back the original name. It's like `&(*ptr) == ptr` in C.

**Named**: `QuoteDrop` (quote-drop)
**No premises**: the `|- ` before the equation means no conditions
**Bidirectional**: equations work both ways (unlike rewrites which are directed)

### Extrude: Scope Extrusion

```rust
Extrude . xs.*map(|x| x # ...rest)
    |- (PPar {(PNew ^[xs].p), ...rest}) = (PNew ^[xs].(PPar {p, ...rest})) ;
```

This is a structural law of rho-calculus: a private name can be "extruded" out of a parallel composition, as long as it doesn't clash with anything in `rest`.

Left side: `{ new(x) in { p } | rest }` - the `new` is inside one branch of a par
Right side: `new(x) in { { p | rest } }` - the `new` wraps the whole par

**The freshness condition**: `xs.*map(|x| x # ...rest)` means "each `x` in `xs` must be fresh (not free) in `rest`." The `#` symbol is the freshness annotation.

---

## 5.4 Rewrite Rules

### COMM: Communication

```rust
Comm . |- (PPar {(PInputs ns cont), *zip(ns,qs).*map(|n,q| (POutput n q)), ...rest})
    ~> (PPar {(eval cont qs.*map(|q| (NQuote q))), ...rest});
```

This is the heart of rho-calculus computation. Let's unpack it:

**Pattern (left side)**:
```
(PPar {
    (PInputs ns cont),                          -- a receiver: listening on channels ns
    *zip(ns,qs).*map(|n,q| (POutput n q)),      -- matching senders: one send per channel
    ...rest                                       -- everything else in the par
})
```

The receiver `(PInputs ns cont)` is listening on channels `ns`. For each channel, there must be a matching sender `(POutput n q)` in the parallel composition. `...rest` captures everything else.

**Result (right side)**:
```
(PPar {
    (eval cont qs.*map(|q| (NQuote q))),  -- apply the continuation to quoted messages
    ...rest                                 -- keep the rest
})
```

The continuation `cont` (a multi-binder `^[xs].p`) is applied to the quoted messages. Each message `q` is quoted to `@(q)` (because in rho-calculus, bound variables in receivers are Names, not Procs).

**Concrete example**:
```
{ @(0)!({}) | @(0)?x.{*(x)} }
```
- Receiver: `@(0)?x.{*(x)}` listens on `@(0)`, binds `x`, body is `*(x)`
- Sender: `@(0)!({})` sends `{}` on `@(0)`
- Channels match (`@(0)`)
- COMM fires: `x` gets bound to `@({})`, body becomes `*(@({}))`
- Result: `{ *(@({})) }` (which can further reduce by Exec)

### Exec: Dereference-Quote Reduction

```rust
Exec . |- (PDrop (NQuote P)) ~> P;
```

`*(@ P)` reduces to `P`. Dereferencing a quoted process gives back the process.

Combined with COMM: after `x` gets `@({})`, we have `*(@({}))` which reduces to `{}`.

### Structural Congruence Rules

```rust
ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest});
NewCong . | S ~> T |- (PNew ^[xs].S) ~> (PNew ^[xs].T);
```

Same concept as Calculator's congruence rules, but for process constructors:
- **ParCong**: If a process in a par rewrites, the whole par rewrites
- **NewCong**: If the body of a `new` rewrites, the `new` rewrites

Plus congruence rules for all the native operators (`AddCongL`, `AddCongR`, etc.).

---

## 5.5 The Logic Block: Custom Datalog Relations

```rust
logic {
    relation path(Proc, Proc);
    path(p0, p1) <-- rw_proc(p0, p1);
    path(p0, p2) <-- path(p0, p1), path(p1, p2);

    relation path_vec(Vec<Proc>);
    path_vec(xs) <--
        proc(x0), rw_proc(x0,x1),
        let xs = vec![x0.clone(), x1.clone()];
    path_vec(zs) <--
        path_vec(xs), path_vec(ys),
        if xs.last() == ys.first(),
        let zs = [xs.as_slice(), ys.as_slice()].concat();

    relation trans(Proc, Proc, Proc);
    trans(p,c,q) <--
        step_term(p), proc(c),
        if let Proc::LamProc(_) = c,
        let app = Proc::ApplyProc(Box::new(c.clone()), Box::new(p.clone())),
        let res = app.normalize(),
        path(res.clone(), q);
}
```

The `logic { ... }` block lets you add custom Datalog relations computed alongside the standard rewrites. These are written in raw Ascent syntax.

**`path(Proc, Proc)`** - Transitive closure of rewrites. If `P ~> Q` and `Q ~> R`, then `path(P, R)`.

**`path_vec(Vec<Proc>)`** - Stores the full rewrite path as a vector. You can see every step, not just the endpoints.

**`trans(Proc, Proc, Proc)`** - A labelled transition system. `trans(p, c, q)` means "process `p`, in context `c`, transitions to `q`." Used for exploring how processes behave under different environments.

You can query these relations in the REPL:
```
relations          -- list all custom relations
relation path      -- show contents of path relation
```

---

## 5.6 The Test Suite

**File**: `languages/tests/rhocalc_tests.rs`

The test file demonstrates how to write tests for a language:

### Test Helpers

```rust
fn parse(input: &str) -> Proc {
    Proc::parse(input).unwrap_or_else(|e| panic!("parse failed: {}", e))
}

fn fresh() {
    mettail_runtime::clear_var_cache();  // Critical!
}

fn run(input: &str) -> AscentResults {
    fresh();
    let lang = RhoCalcLanguage;
    let term = lang.parse_term(input).unwrap();
    lang.run_ascent(term.as_ref()).unwrap()
}
```

Note `fresh()` is called before every test to clear the variable cache.

### Common Assertions

```rust
// Assert a term reduces to a specific normal form
fn assert_reduces_to(input: &str, expected: &str) {
    let results = run(input);
    let nfs = normal_form_displays(&results);
    // ... check expected is among normal forms
}

// Assert at least N rewrites are available
fn assert_min_rewrites(input: &str, min: usize);

// Assert no rewrites (already normal form)
fn assert_no_rewrites(input: &str);
```

### Test Organization

Tests are organized by feature area:
- **comm** - Communication (single-input, multi-input, join patterns)
- **new_and_extrusion** - PNew and scope extrusion
- **congruence** - Rewrite propagation
- **native_ops** - Arithmetic, booleans, strings
- **parsing** - Basic parsing and round-trips
- **beta** - Lambda/dollar-syntax reduction

---

## 5.7 The Environment and Dollar Syntax

When you load RhoCalc in the REPL, the environment comes pre-loaded with combinators:

```
env
  dup = ^l.{l?x.{{l!(*(x)) | *(x)}}}
  rep = ^n.{^a.{^cont.{{n!(a?y.{{$name(cont, y) | $name(dup, n)}}) | $name(dup, n)}}}}
  id = ^z.{*(z)}
  fwd = ^src.{^dst.{src?x.{dst!(*(x))}}}
  const = ^val.{^n.{n?x.{*(val)}}}
  cell = ^loc.{^init.{loc!(init)}}
  read = ^loc.{^ret.{loc?x.{{ret!(*(x)) | loc!(*(x))}}}}
  write = ^loc.{^val.{loc?x.{loc!(val)}}}
```

These are **lambda expressions** (`^x.body`) that the `language!` macro auto-generates. The `$name(...)` and `$proc(...)` syntax applies these lambdas:

- `$name(fwd, x)` = apply the `fwd` combinator (which expects a Name) to `x`
- `$proc(f, p)` = apply `f` (which expects a Proc) to `p`

The REPL replaces dollar-syntax with applications and normalizes (beta-reduces) before execution.

---

## 5.8 Hands-On: Tracing COMM

Let's manually trace what happens with:

```
exec { @(0)!({}) | @(0)?x.{*(x)} }
```

**Step 1: Parse**
```
PPar(HashBag {
    POutput(NQuote(PZero), PZero),    -- @(0)!({})
    PInputs([NQuote(PZero)],          -- @(0)?x.{...}
            ^[x].PDrop(x))            --   body: *(x)
})
```

**Step 2: Ascent finds COMM**
- Receiver: `PInputs` on channel `@(0)`, binding `x`
- Sender: `POutput` on channel `@(0)`, sending `{}`
- Channels match!
- Result: substitute `x := @({})` into body `*(x)` → `*(@({}))`
- Wrap in par with rest (rest is empty): `{ *(@({})) }`

**Step 3: Ascent finds Exec**
- `PDrop(NQuote(PZero))` = `*(@({}))` matches `*(@ P) ~> P`
- Result: `PZero` = `{}`

**Step 4: Ascent finds QuoteDrop (equation)**
- Not directly applicable here, but would be if we had bare `@(*(n))`

**Result**:
```
Computed:
  - N terms
  - M rewrites
  - normal forms include: {}
```

---

## Exercises

### Exercise 1: Annotate Constructors

For each RhoCalc constructor, write:
1. What it represents in process algebra
2. An example term in surface syntax
3. What it looks like as an AST variant

### Exercise 2: Multi-Input Communication

In the REPL, try a join pattern:

```
exec { @(0)!(1) | @(1)!(2) | (@(0)?x, @(1)?y).{*(x) + *(y)} }
```

What should this reduce to? Run it and verify.

### Exercise 3: Scope Extrusion

Try:
```
exec { new(x) in { x!({}) } | @(0)?y.{*(y)} }
```

Does the Extrude equation fire? What's the result?

### Exercise 4: Environment Combinators

Load RhoCalc and try:
```
exec $proc(id, {})
exec { server!(request) | $proc($name(fwd, server), destination) }
```

What does `id` do? What does `fwd` do?

### Exercise 5: Read the Tests

Open `languages/tests/rhocalc_tests.rs` and find:
1. A test for basic COMM
2. A test for scope extrusion
3. A test for native arithmetic

How are the test helpers structured? Could you add a new test?

---

## Checkpoint

Before moving on, make sure you can:

1. **Name** all seven core constructors and what each represents
2. **Explain** the COMM rule in your own words
3. **Explain** what `^[xs].p` means (multi-binder)
4. **Read** the syntax combinators (`*zip`, `*map`, `*sep`) in term declarations
5. **Use** the REPL to execute rho-calculus terms and trace rewrites
6. **Explain** the difference between equations and rewrites

---

**Next**: [Module 6: Procedural Macros](06-procedural-macros.md) - How `language!` generates code
