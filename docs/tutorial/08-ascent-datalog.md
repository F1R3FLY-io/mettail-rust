# Module 8: The Ascent Datalog Engine

**Goal**: Understand how term rewriting is implemented as Datalog computation.

This module covers the most intellectually interesting part of MeTTaIL: how pattern-matching rewrite rules are compiled into Datalog programs that compute to a fixpoint.

---

## 8.1 Datalog 101

### What Is Datalog?

Datalog is a logic programming language. You declare **relations** (tables of facts) and **rules** (how to derive new facts from existing ones):

```
// Relations (tables):
parent("Alice", "Bob").
parent("Bob", "Charlie").

// Rule (derives new facts):
ancestor(X, Y) :- parent(X, Y).
ancestor(X, Z) :- parent(X, Y), ancestor(Y, Z).
```

A Datalog engine computes the **fixpoint** - it repeatedly applies rules until no new facts can be derived. This always terminates (unlike Prolog).

### Ascent: Datalog in Rust

[Ascent](https://github.com/s-arash/ascent) is a Rust crate that compiles Datalog rules into efficient Rust code via a proc macro:

```rust
ascent! {
    struct MyProgram;

    relation parent(String, String);
    relation ancestor(String, String);

    ancestor(x, y) <-- parent(x, y);
    ancestor(x, z) <-- parent(x, y), ancestor(y, z);
}
```

This generates a `MyProgram` struct with methods to add facts and run the computation. Relations are stored as hash-indexed tables for efficient joins.

### How MeTTaIL Uses Ascent

MeTTaIL compiles each language's term rewriting system into an Ascent program. Instead of `parent` and `ancestor`, the relations are:

- `proc(Proc)` - All known processes
- `name(Name)` - All known names
- `rw_proc(Proc, Proc)` - Rewrite relation on processes
- `eq_proc(Proc, Proc)` - Equality relation on processes
- `eq_name(Name, Name)` - Equality relation on names

The rules derive rewrites, equivalences, and explore the term space.

---

## 8.2 The Generated Relations

**File**: `macros/src/logic/relations.rs`

For each category in the language, the generator creates:

### Term Relations
```
proc(Proc)          -- all known processes
name(Name)          -- all known names
int_term(Int)       -- all known integers (for native types)
```

### Rewrite Relations
```
rw_proc(Proc, Proc)  -- P rewrites to Q
rw_name(Name, Name)  -- N rewrites to M
```

### Equality Relations (using `eqrel`)
```
eq_proc(Proc, Proc)  -- P is equivalent to Q (symmetric, transitive)
eq_name(Name, Name)  -- N is equivalent to M
```

The `eqrel` annotation tells Ascent to maintain these as proper equivalence relations (reflexive + symmetric + transitive closure is automatic).

### Projection Relations (for collections)
```
ppar_contains(Proc, Proc)  -- PPar bag contains element
```

### Step Term Relation
```
step_term(Proc)  -- the initial term to rewrite from
```

---

## 8.3 Category Rules: Exploring the Term Space

**File**: `macros/src/logic/categories.rs`

These rules ensure that all subterms and reachable terms are in the database.

### Exploration: Follow Rewrites
```datalog
proc(t1) <-- proc(t0), rw_proc(t0, t1);
```
If we know process `t0` and it rewrites to `t1`, then `t1` is also a known process.

### Deconstruction: Extract Subterms
```datalog
name(field) <-- proc(t), if let Proc::PDrop(field) = t;
name(n), proc(q) <-- proc(t), if let Proc::POutput(n, q) = t;
```
When we see a `PDrop(n)`, we extract `n` as a known name. When we see `POutput(n, q)`, both `n` and `q` become known.

### Collection Deconstruction
```datalog
proc(elem) <-- proc(t), if let Proc::PPar(bag) = t, for (elem, _) in bag.iter();
```
Every element of a parallel composition becomes a known process.

### Optimization: Lazy Deconstruction

Not all constructors need deconstruction. The generator only creates deconstruction rules for constructors that appear in rewrite or equation patterns. This was a 42x speedup:

Before: ~100 deconstruction rules
After: ~10 rules (only what's needed)

---

## 8.4 Equation Rules: Structural Equivalence

**File**: `macros/src/logic/equations.rs`

### Reflexivity
```datalog
eq_proc(t, t) <-- proc(t);
```
Every term is equivalent to itself. (With `eqrel`, symmetry and transitivity are automatic.)

### User-Defined Equations

For the RhoCalc equation `(NQuote (PDrop N)) = N`:

```datalog
eq_name(NQuote(PDrop(n)), n) <-- name(n);
```

If `n` is a known name, then `@(*(n))` is equivalent to `n`.

### Congruence for Equations

If two processes are equivalent, then wrapping them in the same constructor produces equivalent terms:

```datalog
eq_proc(Proc::PPar(bag1), Proc::PPar(bag2)) <--
    proc(Proc::PPar(bag1)),
    eq_proc(elem1, elem2),
    // ... complex bag replacement logic
```

---

## 8.5 Rewrite Rules: Pattern Matching

**File**: `macros/src/logic/rules.rs`, `macros/src/logic/rewrites/`

This is where the `rewrites { ... }` section becomes Datalog rules.

### Simple Rewrite: Exec

The rule `(PDrop (NQuote P)) ~> P` becomes:

```datalog
rw_proc(t, p) <--
    proc(t),
    if let Proc::PDrop(inner) = t,
    if let Name::NQuote(p) = inner.as_ref();
```

Read: "If `t` is a known process, and `t` matches `PDrop(NQuote(p))`, then `t` rewrites to `p`."

### Complex Rewrite: COMM

The COMM rule with shared variables and collection patterns is the most complex. It's compiled into multiple Datalog rules using **projection relations**:

```datalog
// Step 1: Project out the receiver
_comm_input_proj(parent, ns, cont, elem) <--
    proc(parent),
    if let Proc::PPar(bag) = parent,
    for (elem, _) in bag.iter(),
    if let Proc::PInputs(ns, cont) = elem;

// Step 2: Project out matching senders (joined on channel name)
_comm_output_proj(parent, n, q, elem) <--
    proc(parent),
    if let Proc::PPar(bag) = parent,
    for (elem, _) in bag.iter(),
    if let Proc::POutput(n, q) = elem;

// Step 3: Join projections on shared variable (channel name)
rw_proc(parent, result) <--
    _comm_input_proj(parent, ns, cont, input_elem),
    _comm_output_proj(parent, n, q, output_elem),
    eq_name(n_from_ns, n),  // channels match (via equality)
    // ... construct result by removing matched elements and applying continuation
```

This projection-join pattern is efficient because Ascent can index on the shared variable.

### Congruence Rules

For each explicit congruence rule like:
```
ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest});
```

The generator produces:
```datalog
rw_proc(PPar(bag), PPar(new_bag)) <--
    proc(PPar(bag)),
    for (s, _) in bag.iter(),
    rw_proc(s, t),
    let new_bag = bag.replace(s, t);
```

---

## 8.6 The Execution Flow

When you run `exec { @(0)!({}) | @(0)?x.{*(x)} }`:

### 1. Seed the Database
```
proc(PPar({POutput(@(0), PZero), PInputs([@(0)], ^x.PDrop(x))}))
step_term(PPar(...))
```

### 2. Deconstruct
```
proc(POutput(@(0), PZero))
proc(PInputs([@(0)], ^x.PDrop(x)))
name(@(0))
proc(PZero)
```

### 3. Apply Rules
```
// COMM fires:
rw_proc(PPar({POutput(@(0), PZero), PInputs([@(0)], ^x.PDrop(x))}),
        PPar({PDrop(@(PZero))}))

// New term enters database:
proc(PPar({PDrop(@(PZero))}))
proc(PDrop(@(PZero)))
name(@(PZero))

// Exec fires:
rw_proc(PDrop(@(PZero)), PZero)

// ParCong fires:
rw_proc(PPar({PDrop(@(PZero))}), PPar({PZero}))
```

### 4. Continue Until Fixpoint

The engine keeps applying rules until no new facts are derived. All reachable terms, rewrites, and equivalences are now in the database.

### 5. Extract Results

The generated code reads out the relations into `AscentResults`:
- `proc(t)` → `all_terms`
- `rw_proc(s, t)` → `rewrites`
- `eq_proc(s, t)` → `equivalences`
- Custom relations → `custom_relations`

---

## 8.7 Optimization Techniques

### Lazy Deconstruction
Only generate deconstruction rules for constructors referenced in rewrite/equation patterns. (42x speedup.)

### Projection-Based Matching
For patterns with shared variables across collection elements, generate projection relations and use indexed joins. This avoids O(n^2) nested iteration.

### SCC Splitting
For multi-category languages, the Ascent program can be split into strongly connected components. Each SCC runs to fixpoint independently, reducing the total work.

### Type-Aware Relations
Generate separate relations per category (`proc`, `name`, `int_term`) instead of a generic `term` relation. This reduces relation sizes and improves join efficiency.

---

## 8.8 Custom Logic

The `logic { ... }` block in a language definition inserts raw Ascent rules into the generated program. These can reference any generated relation:

```rust
logic {
    relation path(Proc, Proc);
    path(p0, p1) <-- rw_proc(p0, p1);
    path(p0, p2) <-- path(p0, p1), path(p1, p2);
}
```

This computes the transitive closure of rewrites. You can query it in the REPL:

```
relations              -- lists "path" among custom relations
relation path          -- shows all (from, to) pairs
```

---

## Exercises

### Exercise 1: Read Generated Datalog

Open `languages/src/generated/rhocalc-datalog.rs` (or the calculator equivalent). Find:
1. Relation declarations
2. A deconstruction rule
3. An equation rule
4. A rewrite rule (base, not congruence)
5. A congruence rule

### Exercise 2: REPL Exploration

```bash
cargo run -- rhocalc
```

```
exec { @(0)!({}) | @(0)?x.{*(x)} }
relations
relation path
relation path_vec
```

How many entries are in the `path` relation? What do they represent?

### Exercise 3: Custom Query

In the REPL, try a custom query:
```
query(x) <-- path(start, x)
```

(Note: the query system is still evolving - some queries may not work yet.)

### Exercise 4: Trace Fixpoint

For a simple term like `{ *(@ {}) }`:
1. What is the initial seed?
2. What deconstruction rules fire?
3. What rewrite rules fire?
4. How many iterations until fixpoint?

---

## Checkpoint

Before moving on, make sure you can:

1. **Explain** what Datalog is and how fixpoint computation works
2. **Name** the five types of generated relations
3. **Explain** what deconstruction, equation, rewrite, and congruence rules do
4. **Describe** how the COMM rule is compiled to Datalog
5. **Read** generated Datalog code and match it to the language definition

---

**Next**: [Module 9: The REPL](09-repl.md) - The interactive exploration tool
