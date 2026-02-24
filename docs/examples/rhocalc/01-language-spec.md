# The `language!` DSL — RhoCalc Definition

**Source file:** `languages/src/rhocalc.rs`

The `language!` macro is the single entry point for defining a MeTTaIL
language.  It declares types, concrete syntax, structural equations, directed
rewrite rules, native evaluation blocks, and custom Datalog logic — all in one
place.

## Anatomy of the Macro

```
language! {
    name: RhoCalc,          ← 1. Language name
    types { ... },          ← 2. Category declarations
    terms { ... },          ← 3. Term definitions (syntax + semantics)
    equations { ... },      ← 4. Structural equivalences
    rewrites { ... },       ← 5. Directed rewrite rules
    logic { ... },          ← 6. Custom Ascent Datalog rules
}
```

Each section is parsed by `macros/src/ast/language.rs` into a `LanguageDef` AST.

---

## 1. `name: RhoCalc`

The language name drives generated identifiers:

| Generated name        | Example                |
|-----------------------|------------------------|
| AST enums             | `Proc`, `Name`, `Int`  |
| Language struct       | `RhoCalcLanguage`      |
| Term wrapper          | `RhoCalcTerm`          |
| Ascent struct         | `RhoCalcAscent`        |
| REPL registration     | `"rhocalc"`            |

## 2. `types { ... }` — Category Declarations

```rust
types {
    Proc                    // Abstract process category (primary)
    Name                    // Channel name category
    ![i64] as Int           // Native integer (i64)
    ![f64] as Float         // Native float (f64)
    ![bool] as Bool         // Native boolean
    ![str] as Str           // Native string
}
```

**Ordering matters**: the first category (`Proc`) is the *primary* category —
it is the default for Ascent seeding, REPL display, and `step_term` iteration.

**Native types** (`![T] as Name`) generate:
- A `CastX` variant in the primary category (e.g., `Proc::CastInt(Box<Int>)`)
- Literal token recognition (e.g., `Token::Integer` → `Int::NumLit`)
- Cast rules that allow a value of type `Int` to appear where `Proc` is expected

Each `LangType` in the AST stores `name: Ident` and `native_type: Option<Type>`.

## 3. `terms { ... }` — Term Definitions

Each term uses *judgement notation*:

```
Label . params |- syntax : Category  [optional native eval]  [optional fold];
```

The `.` separates the constructor label from parameters.  The `|-` (turnstile)
separates parameters from concrete syntax.  The `:` gives the result category.

### 3.1 Nullary Terms

```rust
PZero .
|- "{}" : Proc;
```

No parameters.  The syntax is a single literal terminal `"{}"`.  This generates
`Proc::PZero` with no fields and a prefix parse handler matching `Token::Braces`
(or the comb-compressed equivalent).

### 3.2 Prefix Terms

```rust
PDrop . n:Name
|- "*" "(" n ")" : Proc ;
```

One parameter `n` of category `Name`.  Syntax: `*`, `(`, parse a `Name`, `)`.
Generates `Proc::PDrop(Box<Name>)`.  This is a *prefix* rule — it starts with
terminal tokens, not a nonterminal.

### 3.3 Collection Terms

```rust
PPar . ps:HashBag(Proc)
|- "{" ps.*sep("|") "}" : Proc;
```

The parameter `ps` has type `HashBag(Proc)` — a multiset of `Proc` values.
The syntax `ps.*sep("|")` means "parse zero or more `Proc` values separated by
`|`" and collect them into a `HashBag`.  Generates `Proc::PPar(HashBag<Proc>)`.

The `*sep(delim)` operator is a collection operation.  Available collection
types are `Vec(T)`, `HashBag(T)`, and `HashSet(T)`.

### 3.4 Binder Terms (Lambda / Multi-Lambda)

```rust
PInputs . ns:Vec(Name), ^[xs].p:[Name* -> Proc]
|- "(" *zip(ns,xs).*map(|n,x| n "?" x).*sep(",") ")" "." "{" p "}" : Proc ;
```

This is the most complex term in RhoCalc.  It demonstrates:

- **Multi-binder**: `^[xs].p` binds a *list* of names `xs` in the body `p`.
  The type `[Name* -> Proc]` means "a function from zero-or-more Names to Proc".
  The `^` is the binder annotation.

- **ZipMapSep**: `*zip(ns,xs).*map(|n,x| n "?" x).*sep(",")` is a chained
  pattern operation:
  1. `*zip(ns,xs)` — zip the `ns` (names) and `xs` (binder variables) pairwise
  2. `.*map(|n,x| n "?" x)` — for each pair, the concrete syntax is `n ? x`
  3. `.*sep(",")` — pairs are separated by commas

  This parses input like `(n0 ? x0, n1 ? x1)`.

Generates `Proc::PInputs(Vec<Name>, Scope<Vec<Name>, Proc>)` where the `Scope`
is from the `moniker` crate for hygienic alpha-equivalence.

```rust
PNew . ^x.p:[Name -> Proc]
|- "new" "(" x "," p ")" : Proc;
```

Single-binder: `^x.p` binds one name `x` in `p`.  Syntax: `new(x, body)`.

### 3.5 Infix Fold Terms (Native Evaluation)

```rust
Add . a:Proc, b:Proc |- a "+" b : Proc ![
    { match (&a, &b) {
        (Proc::CastInt(a), Proc::CastInt(b)) =>
            Proc::CastInt(Box::new(*a.clone() + *b.clone())),
        (Proc::CastFloat(a), Proc::CastFloat(b)) =>
            Proc::CastFloat(Box::new(*a.clone() + *b.clone())),
        _ => Proc::Err,
    }}
] fold;
```

This combines several features:

- **Infix**: `a "+" b` — left operand, terminal `"+"`, right operand.  Both
  operands and the result are `Proc`.  Classification detects this as
  `is_infix = true` and assigns binding powers for Pratt parsing.

- **Native eval block** (`![...]`): Rust code evaluated at Ascent fixpoint time.
  When both operands reduce to native integers, the result is computed directly.

- **`fold` annotation**: triggers big-step fold semantics.  The Ascent engine
  generates a `fold_proc` relation and special rules that try to reduce `Add`
  nodes to their native values during the fixpoint.

All arithmetic, comparison, logical, and conversion operators follow this
same pattern (Sub, Mul, Div, Eq, Ne, Gt, Lt, ...).

### 3.6 Unary Prefix with Fold

```rust
Not . a:Proc |- "not" a : Proc ![
    { match &a {
        Proc::CastBool(b) => match &**b {
            Bool::BoolLit(v) => Proc::CastBool(Box::new(Bool::BoolLit(!v))),
            _ => Proc::Err,
        },
        _ => Proc::Err,
    }}
] fold;
```

`Not` is classified as `is_unary_prefix = true` because the syntax is
`terminal nonterminal` (a terminal followed by exactly one same-category
nonterminal).  Unary prefix gets `prefix_bp = max_infix_bp + 2` so that
`not 3 + 4` parses as `(not 3) + 4` rather than `not (3 + 4)`.

### 3.7 Cast Rules

```rust
CastInt . k:Int |- k : Proc;
CastFloat . k:Float |- k : Proc;
CastBool . k:Bool |- k : Proc;
CastStr . s:Str |- s : Proc;
```

A cast rule has syntax that is exactly one nonterminal of a different category.
`CastInt` allows an `Int` to appear wherever a `Proc` is expected.  These are
classified with `is_cast = true, cast_source_category = Some("Int")`.

Cast rules are handled as *Pratt prefix handlers* (not dispatch wrappers) so
that the infix loop continues after parsing the cast.  This means
`3 + 4` is parsed as `CastInt(3) + CastInt(4)` = `Add(CastInt(3), CastInt(4))`.

### 3.8 Cross-Category Rules

```rust
NQuote . p:Proc
|- "@" "(" p ")" : Name ;
```

The parameter `p` is `Proc` but the result category is `Name`.  This is a
*cross-category* rule: it appears in the `Name` category's parser but parses a
`Proc` sub-expression.  Classification: `is_cross_category = true,
cross_source_category = Some("Proc")`.

## 4. `equations { ... }` — Structural Equivalences

```rust
equations {
    QuoteDrop . |- (NQuote (PDrop N)) = N ;
}
```

The equation `QuoteDrop` states that `@(*N) = N` — quoting a dereference
cancels out.  The `.` after the name separates it from optional contexts
(type context `|` propositional context `|-`).

Equations generate *bidirectional* Ascent rules:

```
eq_name(lhs, rhs) <-- name(lhs), if let Name::NQuote(p) = lhs,
                       if let Proc::PDrop(n) = &**p,
                       let rhs = (**n).clone();
eq_name(rhs, lhs) <-- /* symmetric */;
```

## 5. `rewrites { ... }` — Directed Rewrite Rules

### 5.1 The Communication Rule (Comm)

```rust
Comm . |- (PPar {(PInputs ns cont), *zip(ns,qs).*map(|n,q| (POutput n q)), ...rest})
    ~> (PPar {(eval cont qs.*map(|q| (NQuote q))), ...rest});
```

This is the core rho-calculus reduction.  It matches a parallel composition
containing a `PInputs` (receiver) and matching `POutput` (senders), then
substitutes the quoted messages into the receiver's body.

Pattern elements:
- `{...}` — collection pattern matching against `HashBag`
- `(PInputs ns cont)` — constructor pattern matching
- `*zip(ns,qs).*map(|n,q| (POutput n q))` — zip+map pattern: for each name in
  `ns`, there must be a matching `POutput` on that name
- `...rest` — rest pattern: remaining elements of the multiset
- `(eval cont qs.*map(|q| (NQuote q)))` — substitution: evaluate `cont`
  (the binder body) with the quoted messages as replacements

### 5.2 Exec (Dereference Reduction)

```rust
Exec . |- (PDrop (NQuote P)) ~> P;
```

Dereferencing a quoted process yields the process itself: `*(@(P)) ~> P`.

### 5.3 Congruence Rules

```rust
ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest});
AddCongL . | S ~> T |- (Add S X) ~> (Add T X);
AddCongR . | S ~> T |- (Add X S) ~> (Add X T);
```

Congruence rules propagate rewrites through constructors.  The premise
`S ~> T` in the propositional context (after `|`) means "if S rewrites to T".
These generate Ascent rules with an additional `rw_proc(s, t)` body literal.

## 6. `logic { ... }` — Custom Ascent Datalog

```rust
logic {
    proc(p) <-- if let Ok(p) = Proc::parse("^x.{{ x | serv!(req) }}");
    proc(p) <-- if let Ok(p) = Proc::parse("^x.{x}");

    proc(res) <--
        step_term(p), proc(c),
        if let Proc::LamProc(_) = c,
        let app = Proc::ApplyProc(Box::new(c.clone()), Box::new(p.clone())),
        let res = app.normalize();

    relation path(Proc, Proc);
    path(p0, p1) <-- rw_proc(p0, p1);
    path(p0, p2) <-- path(p0, p1), path(p1, p2);

    relation trans(Proc, Proc, Proc);
    trans(p,c,q) <--
        step_term(p), proc(c),
        if let Proc::LamProc(_) = c,
        let app = Proc::ApplyProc(Box::new(c.clone()), Box::new(p.clone())),
        let res = app.normalize(),
        path(res.clone(), q);
}
```

The `logic { ... }` block contains raw Ascent syntax that is injected verbatim
into the generated Ascent struct.  RhoCalc uses it to:

1. **Seed context processes** — lambda terms that model evaluation contexts
2. **Apply contexts** — apply `LamProc` contexts to the `step_term` and normalize
3. **Define `path`** — transitive closure of the rewrite relation
4. **Define `trans`** — transition relation: term × context × result

Custom `relation` declarations are extracted at parse time so the code generator
knows their types for extraction into `AscentResults::custom_relations`.

---

**Next:** [02-macro-expansion.md](02-macro-expansion.md) — how this DSL becomes
a `LanguageDef` and then a `LanguageSpec`.
