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
|- "Nil" : Proc;
```

No parameters.  The syntax is the keyword terminal `"Nil"` — the
[Rholang](https://rholang.io)-style spelling of the zero process.  This
generates `Proc::PZero` with no fields and a prefix parse handler matching
`Token::Nil`.  (Historically the rule was `"{}"`, but `{}` is now reserved for
the empty `Map` literal; see
[exploring/rhocalc-rholang-style-syntax.md](../../design/exploring/rhocalc-rholang-style-syntax.md).)

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
PParInfix . a:Proc, b:Proc |- a "|" b : Proc ![{
    crate::rhocalc::runtime::merge_pp_parallel(a.clone(), b.clone())
}] fold;

// Internal AST constructor — matched by equations / rewrites, never input by
// users. The `__ppar(…)` form is the round-trip surface for the AST.
PPar . ps:HashBag(Proc) |- "__ppar" "(" ps.*sep(",") ")" : Proc;
```

Parallel composition uses Rholang-style bare infix `a | b` (`PParInfix`),
which `fold`s to the multiset `Proc::PPar(HashBag<Proc>)` via
`merge_pp_parallel`. The `__ppar(…)` keyword rule keeps the `Proc::PPar`
variant available for equation/rewrite matching but is reserved for internal
use (never appears in user input). The earlier braced surface
`{ a | b | c }` was retired so that `{` `}` could be repurposed for the
Rholang-style empty `Map` literal — see
[exploring/rhocalc-rholang-style-syntax.md](../../design/exploring/rhocalc-rholang-style-syntax.md).

The `*sep(delim)` operator is a collection operation.  Available collection
types are `Vec(T)`, `HashBag(T)`, and `HashSet(T)`.

### 3.3.1 Map Literals and Method-Call Sugar

`Map` overrides the default `map(k:v)` delimiters to Rholang-style braces:

```rust
![HashMap<Proc, Proc>] as Map {
    open_parts: ["{"],
    close_parts: ["}"],
    sep: ",",
    key_val_sep: ":",
}
```

producing `{}`, `{k: v}`, `{k₁: v₁, k₂: v₂, …}`. An explicit `Map()` alias
is provided for chained method calls:

```rust
MapEmpty . |- "Map" "(" ")" : Proc ![{
    Proc::CastMap(Box::new(Map::MapLit(Default::default())))
}] fold;
```

### 3.3.2 Pathmap Literals (Rholang `{| … |}`)

`Pathmap` uses Rholang-style pathmap braces. Each element is one `Proc`; the
literal conflates path and stored value (`insert(e, e)`):

```rust
![mettail_runtime::PathMapLit<Proc, Proc>] as Pathmap {
    open_parts: ["{|"],
    close_parts: ["|}"],
    sep: ",",
}
```

producing `{||}`, `{| e |}`, `{| e₁, e₂, … |}` (lexer tokens `{|` / `|}`). List elements contribute **all**
segments to the trie key (e.g. `{| ["a","b","c"] |}`). Use `.set(k, v)` or
zipper `setLeaf` when the payload must differ from the path term. `Pathmap()`
is an alias for the empty literal.

Method-call surface (canonical AST; each method rule is its own constructor):

| Method form | AST node | Receiver |
|-------------|----------|----------|
| `m.get(k)` | `MGet(m, k)` | Map / Pathmap |
| `m.set(k, v)` | `MSet(m, k, v)` | Map / Pathmap |
| `m.contains(k)` | `MContains(m, k)` | Map / Set / Pathmap |
| `m.delete(k)` | `MDelete(m, k)` | Map / Set / List |
| `m.keys()` | `MKeys(m)` | Map |
| `m.values()` | `MValues(m)` | Map |
| `s.add(e)` | `SAdd(s, e)` | Set |
| `l.length()` | `LLength(l)` | List |
| `l.nth(i)` | `LNth(l, i)` | List |
| `l.concat(r)` | `LConcat(l, r)` | List / Str |
| `b.count(e)` | `BCount(b, e)` | Bag |
| `b.diff(c)` | `BDiff(b, c)` | Bag / Set |
| `b.remove(e)` | `BRemove(b, e)` | Bag |
| `m.restrict(b)` / `m.subtract(b)` / `m.meet(b)` | `PRestrict` / `PSubtract` / `PMeet` | Pathmap |
| `m.getSubtrie()` / `m.getSubtrieAt(p)` | `PGetSubtrie` / `PGetSubtrieAt` | Pathmap / ReadZipper |
| `m.readZipper()` / … | `PReadZipper` / `PReadZipperAt` / … | Pathmap |
| `z.getLeaf()` / … | `RZGetLeaf` / `RZDescendTo` / … | ReadZipper |
| `w.setLeaf(p,v)` / … | `WZSetLeaf` / `WZGraft` / … | WriteZipper |
| `x.size()` | `MSize(x)` | Map / Set / Bag |
| `x.union(y)` | `MUnion(x, y)` | Map / Set / Bag / Pathmap |

The unary forms (`m.size()`, `m.keys()`, `m.values()`, `l.length()`,
`b.size()`, Pathmap/Zipper zero-arg methods) use prattail's
zero-operand-after-trigger mixfix shape (1 NT with 3+ terminals), dispatched
inline without a frame push. Prefix functional forms such as `get(m, k)` are
not user-facing.

The shared-name methods `.union`, `.size`, `.contains`, `.delete`, and
`.diff` use a single grammar rule each (`MUnion`, `MSize`, `MContains`,
`MDelete`, `BDiff`) whose `fold` action inspects the (already-folded)
receiver and applies the appropriate semantics inline for `.union(n)`,
`.size()`, and related operations.

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

### 3.5.1 Collection equality (`==` / `!=`)

`Eq` and `Ne` fold collection casts injected into `Proc` to `CastBool` using
`compare_collection_equality` in `languages/src/rhocalc/runtime.rs`. List
comparison is ordered and duplicate-sensitive; bag comparison is multiset
(count-based) after `normalize_bag_elements`; map and set comparison are
order-independent on keys/members. Cross-type collection pairs (for example
`[1, 2] == Set(1, 2)`) fold to `false` / `true` for `!=`. Non-literal
collection operands yield `Proc::Err`, matching scalar `Eq` on non-literal
casts. `where` guards use the same helper via `eval_guard_bool` in
`languages/src/rhocalc/receive.rs`. Ascent `eq_list` / `eq_bag` / `eq_map` /
`eq_set` remain equational relations, separate from surface boolean
comparison. See
[rhocalc-collection-equality.md](../../design/made/rhocalc-collection-equality.md).

### 3.5.2 Collection wire (`toByteArray()`)

Collection casts support zero-argument `.toByteArray()`. It is a **pure
constructor** — it carries no `![{…}]` fold body — and lowers to Rholang's own
`EMethod("toByteArray")`, so the bytes are produced by the f1r3node reducer
(`reduce.rs:4137-4160`) and returned as a real `GByteArray`. Set/map members are
canonicalized by the machine's `SortedParHashSet`, and a bag rides its
`mettail.rhocalc.bag.v1` ABI tag.

Before 2026-07-25 it folded host-side to a hex `GString` through a forked copy of
f1r3node's `rhoapi` protobuf schema; that fork is retired. See
[rhocalc-collection-wire.md](../../design/made/rhocalc-collection-wire.md) §7 for
the three defects that made the fork unsalvageable.

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

#### `@Nil` shorthand

Rholang spells `Name::NQuote(Proc::PZero)` as `@Nil`. We add the same
shorthand by a Name-category fold rule that lowers to the canonical
`NQuote(PZero)` AST node:

```rust
NQuoteNil .
|- "@" "Nil" : Name ![{
    Name::NQuote(Box::new(Proc::PZero))
}] fold;
```

`Nil` is the surface keyword for `PZero` and is therefore not in `Name`'s
FIRST set; `NQuoteNil` instead enters via the shared `@` token, with prattail
disambiguating between `@(P)` (`NQuote`) and `@Nil` (`NQuoteNil`) by the
second-token NFA branch (`LParen` vs `KwNil`).

For send positions where `POutputQuoted`'s `@ <Name> ! ( q )` shape would
otherwise reject `Nil` (the inner Name parser does not accept the keyword), two
Proc-category sugars complete the surface:

```rust
POutputNil . q:Proc
|- "@" "Nil" "!" "(" q ")" : Proc ![{
    Proc::POutput(
        Box::new(Name::NQuote(Box::new(Proc::PZero))),
        Box::new(q.clone()),
    )
}] fold;

PPersistOutputNil . q:Proc
|- "@" "Nil" "!!" "(" q ")" : Proc ![{
    Proc::PPersistOutput(
        Box::new(Name::NQuote(Box::new(Proc::PZero))),
        Box::new(q.clone()),
    )
}] fold;
```

All three Proc rules dispatch from `Token::At`; prattail's
`write_nfa_merged_prefix_arm` NFA-tries each via its generated
`parse_<label>` standalone function, taking the first declaration-order
success.

#### Generalised `@P` shorthand for arbitrary `P:Proc`

Rholang lets `@` quote *any* process, not just `Nil` — `@1`, `@"k"`, `@*x`
are all valid Names. A single fold rule generalises both `NQuote` (`@(P)`)
and `NQuoteNil` (`@Nil`):

```rust
NQuoteShort . p:Proc
|- "@" p : Name ![{
    Name::NQuote(Box::new(p.clone()))
}] fold;
```

For send positions where neither `POutputQuoted` nor `POutputNil` matches
(e.g. the inner is a literal like `@1!(q)` or `@"k"!(q)`), we likewise
add generalised sugars:

```rust
POutputShort . p:Proc, q:Proc
|- "@" p "!" "(" q ")" : Proc ![{
    Proc::POutput(
        Box::new(Name::NQuote(Box::new(p.clone()))),
        Box::new(q.clone()),
    )
}] fold;

PPersistOutputShort . p:Proc, q:Proc
|- "@" p "!!" "(" q ")" : Proc ![{
    Proc::PPersistOutput(
        Box::new(Name::NQuote(Box::new(p.clone()))),
        Box::new(q.clone()),
    )
}] fold;
```

Five Proc-level rules now share the `@` opener; the NFA dispatcher above
tries each in declaration order (more specific rules — `POutputNil`,
`POutputQuoted` — declared first). For overlapping inputs the fold actions
collapse to the same canonical `POutput(NQuote(P), q)` AST, so the choice
is semantically transparent.

**Precedence:** All three short-form rules carry `prefix(220)`, a
cross-category prefix binding-power annotation. The framework now honours
`prefix(N)` for any prefix-shaped rule, threading the BP into the rule's
generated standalone parser without entering the same-category
unary-prefix dispatch. With `min_bp = 220` (well above all Proc-level
infix BPs), `@P` consumes only a high-precedence Proc subterm: `*@1 + 0`
parses as `(*@1) + 0`, and `@1+2!(0)` is a parse error rather than the
ambiguous `(@(1+2))!(0)`. Users wanting to quote a compound expression
still write `@(1+2)` explicitly.

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
