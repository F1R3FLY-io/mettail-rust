# Collection Types in MeTTaIL: Complete Design & Implementation Plan

## Status
**Ready for Implementation** - Design finalized, November 2025

## Table of Contents
1. [Motivation & Goals](#motivation--goals)
2. [User-Facing Syntax](#user-facing-syntax)
3. [Technical Foundation](#technical-foundation)
4. [Implementation Plan](#implementation-plan)
5. [Testing Strategy](#testing-strategy)
6. [Performance Targets](#performance-targets)
7. [Migration Path](#migration-path)

---

## Motivation & Goals

### The Problem

Currently, MeTTaIL uses **binary constructors** for associative-commutative (AC) operations:

```rust
PPar . Proc ::= Proc "|" Proc ;
// Generates: Proc::PPar(Box<Proc>, Box<Proc>)
```

This causes severe performance issues:

1. **Exponential Equality Checking**
   - `(a | b | c) == (c | a | b)` requires reasoning about AC axioms
   - Generates `O(n!)` equivalent representations
   - **Current performance**: 60-80 seconds for depth-6 terms

2. **Congruence Rule Explosion**
   - Auto-generated congruence creates thousands of equality facts
   - Ascent `eqrel` becomes saturated with redundant equivalences
   - Memory usage grows exponentially

3. **Rewrite Matching Overhead**
   - Must try all `O(n!)` permutations to find matching pattern
   - Deeply nested terms amplify the problem

### The Solution

Represent AC operations as **collections** (multisets/sets):

```rust
PPar . Proc ::= HashBag(Proc) sep "|" ;
// Generates: Proc::PPar(HashBag<Proc>)
```

**Benefits**:
- **O(n) equality**: Hash-based multiset comparison
- **No AC equations needed**: Structure encodes AC properties
- **Direct pattern matching**: Extract elements from bag
- **Expected speedup**: **100x+** (from 60s to < 1s)

### Design Goals

1. ✅ **Performance**: 100x speedup for AC operations
2. ✅ **Backward Compatible**: Existing theories continue working
3. ✅ **User-Friendly**: Intuitive syntax with flexible delimiters
4. ✅ **Type-Safe**: Collection types integrated into type system
5. ✅ **Complete**: Support in AST, parser, display, substitution, rewriting

---

## User-Facing Syntax

### Basic Collection Constructor

```rust
theory! {
    name: RhoCalc,
    exports { Proc, Name }

    terms {
        PZero . Proc ::= "0" ;

        // Collection-based parallel composition
        // Format: CollectionType(ElementType) sep "separator" delim "outer"
        PPar . Proc ::= HashBag(Proc) sep "|" ;

        // Other constructors unchanged
        PInput . Proc ::= "for" "(" Name <Name> ")" "{" Proc "}" ;
        POutput . Proc ::= Name "!" "(" Proc ")" ;
        PDrop . Proc ::= "*" Name ;
        NQuote . Name ::= "@" "(" Proc ")" ;
        NVar . Name ::= Var ;
    }
}
```

### Flexible Delimiters (Advanced)

Users can specify both **outer delimiters** and **inner separators**:

```rust
// Default: no outer delimiters, just separator
PPar . Proc ::= HashBag(Proc) sep "|" ;
// Parses: a | b | c

// With explicit delimiters
PList . Proc ::= Vec(Proc) sep "," delim "[" "]" ;
// Parses: [a, b, c]

// Set notation
PSet . Proc ::= HashSet(Proc) sep "," delim "{" "}" ;
// Parses: {a, b, c}

// Custom delimiters
PTuple . Term ::= Vec(Term) sep ";" delim "(" ")" ;
// Parses: (a; b; c)
```

**Grammar Syntax**:
```ebnf
CollectionSpec ::= CollectionType "(" ElementCategory ")" "sep" Separator ["delim" OpenDelim CloseDelim]

CollectionType ::= "HashBag" | "HashSet" | "Vec"
ElementCategory ::= Ident  // Must be a valid category in the theory
Separator ::= StringLiteral  // e.g., "|", ",", ";"
OpenDelim ::= StringLiteral  // e.g., "[", "{", "("
CloseDelim ::= StringLiteral  // e.g., "]", "}", ")"
```

### Collection Types

Three built-in collection types:

| Type | Duplicates? | Ordered? | Equality | Use Case |
|------|-------------|----------|----------|----------|
| `HashBag<T>` | ✅ Yes | ❌ No | Multiset (count-based) | AC operations (parallel composition) |
| `HashSet<T>` | ❌ No | ❌ No | Set equality | Unique elements only |
| `Vec<T>` | ✅ Yes | ✅ Yes | Ordered list | Sequences, tuples |

### Equation Simplifications

With collections, AC equations are **implicit**:

```rust
equations {
    // ❌ NOT NEEDED - implicit in HashBag:
    // (PPar P Q) == (PPar Q P)                      // Commutativity
    // (PPar P (PPar Q R)) == (PPar (PPar P Q) R)   // Associativity

    // ✅ STILL NEEDED - identity elements:
    // Empty bag normalizes to zero (auto-generated if PZero exists)

    // ✅ Other equations work as before:
    (PDrop (NQuote P)) == P ;  // Reflection
}
```

**Auto-Normalization**:
- `PPar([])` → `PZero` (if `PZero` constructor exists)
- `PPar([P])` → `P` (single-element bag unwraps)
- Generated automatically, no user specification needed

### Rewrite Pattern Matching (Future)

Pattern matching over collections (Phase 4):

```rust
rewrites {
    // Extract matching elements from bag
    if x # Q then
        (PPar [PInput chan x P, POutput chan Q, ...rest])
        => (PPar [subst P x (NQuote Q), ...rest])
}
```

**Pattern Syntax** (to be finalized in Phase 4):
- `[elem1, elem2, ...rest]` - match specific elements, bind remainder
- Order-independent matching
- Duplicate-aware matching for `HashBag`

---

## Technical Foundation

### AST Extensions

#### New AST Types (`macros/src/ast.rs`)

```rust
/// Collection type specifier in grammar
#[derive(Debug, Clone, PartialEq)]
pub enum CollectionType {
    HashBag,
    HashSet,
    Vec,
}

/// Extended grammar item to support collections
#[derive(Debug, Clone, PartialEq)]
pub enum GrammarItem {
    Terminal(String),
    NonTerminal(Ident),
    Binder { category: Ident },

    // NEW: Collection specification
    Collection {
        coll_type: CollectionType,
        element_type: Ident,         // Category of elements
        separator: String,            // Inner separator (e.g., "|")
        delimiters: Option<(String, String)>, // Optional (open, close)
    },
}
```

#### Parsing Collection Specs

Add parsing in `ast.rs`:

```rust
impl GrammarItem {
    fn parse_collection(input: ParseStream) -> SynResult<Self> {
        // Parse: HashBag(Proc) sep "|" [delim "[" "]"]
        let coll_type_ident = input.parse::<Ident>()?;
        let coll_type = match coll_type_ident.to_string().as_str() {
            "HashBag" => CollectionType::HashBag,
            "HashSet" => CollectionType::HashSet,
            "Vec" => CollectionType::Vec,
            _ => return Err(syn::Error::new(coll_type_ident.span(),
                "expected HashBag, HashSet, or Vec")),
        };

        // Parse (ElementType)
        let content;
        syn::parenthesized!(content in input);
        let element_type = content.parse::<Ident>()?;

        // Parse sep "separator"
        let sep_kw = input.parse::<Ident>()?;
        if sep_kw != "sep" {
            return Err(syn::Error::new(sep_kw.span(), "expected 'sep'"));
        }
        let separator: syn::LitStr = input.parse()?;

        // Optional: delim "open" "close"
        let delimiters = if input.peek(Ident) && input.peek2(syn::LitStr) {
            let delim_kw = input.parse::<Ident>()?;
            if delim_kw != "delim" {
                return Err(syn::Error::new(delim_kw.span(), "expected 'delim'"));
            }
            let open: syn::LitStr = input.parse()?;
            let close: syn::LitStr = input.parse()?;
            Some((open.value(), close.value()))
        } else {
            None
        };

        Ok(GrammarItem::Collection {
            coll_type,
            element_type,
            separator: separator.value(),
            delimiters,
        })
    }
}
```

### Runtime Types (`runtime/src/lib.rs`)

#### HashBag Implementation

```rust
use std::collections::HashMap;
use std::hash::{Hash, BuildHasherDefault};
use rustc_hash::FxHasher;

/// Multiset (bag) - unordered collection with duplicates
///
/// Uses HashMap to track element counts efficiently.
/// Equality is based on element counts (order-independent).
#[derive(Clone, Debug)]
pub struct HashBag<T: Clone + Hash + Eq> {
    counts: HashMap<T, usize, BuildHasherDefault<FxHasher>>,
    total_count: usize,
}

impl<T: Clone + Hash + Eq> HashBag<T> {
    pub fn new() -> Self {
        Self {
            counts: HashMap::default(),
            total_count: 0,
        }
    }

    pub fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut bag = Self::new();
        for item in iter {
            bag.insert(item);
        }
        bag
    }

    pub fn insert(&mut self, item: T) {
        *self.counts.entry(item).or_insert(0) += 1;
        self.total_count += 1;
    }

    pub fn remove(&mut self, item: &T) -> bool {
        if let Some(count) = self.counts.get_mut(item) {
            *count -= 1;
            self.total_count -= 1;
            if *count == 0 {
                self.counts.remove(item);
            }
            true
        } else {
            false
        }
    }

    pub fn contains(&self, item: &T) -> bool {
        self.counts.contains_key(item)
    }

    pub fn count(&self, item: &T) -> usize {
        self.counts.get(item).copied().unwrap_or(0)
    }

    pub fn len(&self) -> usize {
        self.total_count
    }

    pub fn is_empty(&self) -> bool {
        self.total_count == 0
    }

    /// Iterator over (element, count) pairs
    pub fn iter(&self) -> impl Iterator<Item = (&T, usize)> {
        self.counts.iter().map(|(k, &v)| (k, v))
    }

    /// Iterator that yields each element `count` times
    pub fn iter_elements(&self) -> impl Iterator<Item = &T> {
        self.counts.iter().flat_map(|(k, &count)| {
            std::iter::repeat(k).take(count)
        })
    }
}

// PartialEq: compare by element counts
impl<T: Clone + Hash + Eq> PartialEq for HashBag<T> {
    fn eq(&self, other: &Self) -> bool {
        self.total_count == other.total_count &&
        self.counts == other.counts
    }
}

impl<T: Clone + Hash + Eq> Eq for HashBag<T> {}

// Hash: hash all (element, count) pairs
impl<T: Clone + Hash + Eq> Hash for HashBag<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Hash count first
        self.total_count.hash(state);

        // Collect and sort entries for deterministic hashing
        let mut entries: Vec<_> = self.counts.iter().collect();
        entries.sort_by_key(|(k, _)| format!("{:?}", k));

        for (elem, &count) in entries {
            elem.hash(state);
            count.hash(state);
        }
    }
}

// Ord: lexicographic ordering by sorted elements
impl<T: Clone + Hash + Eq + Ord> PartialOrd for HashBag<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T: Clone + Hash + Eq + Ord> Ord for HashBag<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        // First compare by total count
        match self.total_count.cmp(&other.total_count) {
            Ordering::Equal => {
                // Then compare sorted elements lexicographically
                let mut v1: Vec<_> = self.iter_elements().collect();
                let mut v2: Vec<_> = other.iter_elements().collect();
                v1.sort();
                v2.sort();
                v1.cmp(&v2)
            }
            ord => ord,
        }
    }
}

// BoundTerm: needed for substitution with binders
impl<N, T> BoundTerm<N> for HashBag<T>
where
    N: Clone + PartialEq,
    T: Clone + Hash + Eq + BoundTerm<N>,
{
    fn term_eq(&self, other: &Self) -> bool {
        if self.total_count != other.total_count {
            return false;
        }
        // Check term equality for each element
        for (elem1, count1) in self.iter() {
            let count2 = other.iter()
                .filter(|(elem2, _)| elem1.term_eq(elem2))
                .map(|(_, c)| c)
                .sum::<usize>();
            if count1 != count2 {
                return false;
            }
        }
        true
    }

    fn close_term(&mut self, state: ScopeState, on_free: &impl OnFreeFn<N>) {
        // Close each unique element
        for (elem, _) in self.counts.iter_mut() {
            elem.close_term(state, on_free);
        }
    }

    fn open_term(&mut self, state: ScopeState, on_bound: &impl OnBoundFn<N>) {
        for (elem, _) in self.counts.iter_mut() {
            elem.open_term(state, on_bound);
        }
    }

    fn visit_vars(&self, on_var: &mut impl FnMut(&Var<N>)) {
        for (elem, _) in self.iter() {
            elem.visit_vars(on_var);
        }
    }

    fn visit_mut_vars(&mut self, on_var: &mut impl FnMut(&mut Var<N>)) {
        for (elem, _) in self.counts.iter_mut() {
            elem.visit_mut_vars(on_var);
        }
    }
}

impl<T: Clone + Hash + Eq> Default for HashBag<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone + Hash + Eq> FromIterator<T> for HashBag<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self::from_iter(iter)
    }
}
```

**Note**: Similar implementations needed for `HashSet<T>` (delegates to `std::collections::HashSet`) and wrappers for `Vec<T>` if needed for consistent trait implementations.

---

## Implementation Plan

### Overview

**Total Duration**: 10-12 days
**Phases**: 5 major milestones
**Approach**: Bottom-up (runtime → AST → codegen → parser → rewrites)

### Phase 1: Runtime Foundation (Days 1-2)

**Goal**: Implement collection types in `runtime`

#### Tasks

1. **HashBag Implementation** (Day 1)
   - [ ] Core `HashBag<T>` struct with `HashMap` backing
   - [ ] Methods: `new`, `insert`, `remove`, `contains`, `count`, `len`, `is_empty`
   - [ ] Iterators: `iter()` (element, count), `iter_elements()` (flattened)
   - [ ] Trait implementations: `Clone`, `Debug`, `Default`, `FromIterator`

2. **Trait Implementations** (Day 1-2)
   - [ ] `PartialEq` + `Eq` - multiset equality
   - [ ] `Hash` - deterministic hashing
   - [ ] `PartialOrd` + `Ord` - lexicographic ordering
   - [ ] `BoundTerm<N>` - integration with `moniker` for substitution

3. **HashSet & Vec Wrappers** (Day 2)
   - [ ] Newtype wrappers if needed for trait consistency
   - [ ] Same trait implementations as `HashBag`

4. **Testing** (Day 2)
   - [ ] Unit tests for all operations
   - [ ] Property tests (commutativity, associativity automatic)
   - [ ] Performance microbenchmarks
   - [ ] `BoundTerm` tests with substitution

**Deliverable**: `mettail_runtime::HashBag`, `HashSet`, `Vec` with full trait support

---

### Phase 2: AST & Grammar Extension (Days 3-4)

**Goal**: Extend AST to represent collection constructors

#### Tasks

1. **AST Types** (Day 3)
   - [ ] Add `CollectionType` enum to `ast.rs`
   - [ ] Extend `GrammarItem` with `Collection` variant
   - [ ] Update `GrammarRule` to handle collection items

2. **Parsing Collection Specs** (Day 3)
   - [ ] Parse `HashBag(Cat) sep "sep"` syntax
   - [ ] Parse optional `delim "open" "close"`
   - [ ] Validate element type exists in theory
   - [ ] Error messages for malformed specs

3. **Validation** (Day 4)
   - [ ] Check element category is valid
   - [ ] Check separator is not empty
   - [ ] Check delimiters are not empty if specified
   - [ ] Check collection constructor has exactly one item
   - [ ] Warn if collection used with binders (unsupported in Phase 1-3)

4. **Testing** (Day 4)
   - [ ] Parse various collection specs
   - [ ] Test error cases (invalid category, empty sep, etc.)
   - [ ] Verify AST structure

**Deliverable**: Extended AST that can represent collection constructors

---

### Phase 3: Code Generation (Days 5-7)

**Goal**: Generate Rust code for collection-based constructors

#### Tasks

1. **AST Generation** (`codegen.rs`) (Day 5)
   - [ ] Detect `GrammarItem::Collection` in rules
   - [ ] Generate enum variant with collection field
     ```rust
     // PPar . Proc ::= HashBag(Proc) sep "|"
     // Generates:
     Proc::PPar(mettail_runtime::HashBag<Proc>)
     ```
   - [ ] Handle `HashBag`, `HashSet`, `Vec` types
   - [ ] Ensure `#[derive(Clone, Debug, PartialEq, Eq, Hash, Ord)]` works

2. **Display Generation** (`display_gen.rs`) (Day 5-6)
   - [ ] Detect collection fields in enum variants
   - [ ] Generate display with separator
     ```rust
     write!(f, "{}", bag.iter_elements()
         .map(|e| e.to_string())
         .collect::<Vec<_>>()
         .join("|"))
     ```
   - [ ] Handle delimiters if specified
   - [ ] Handle empty collections (normalize to zero constructor if exists)

3. **Substitution Generation** (`subst_gen.rs`) (Day 6)
   - [ ] Detect collection fields
   - [ ] Generate recursive substitution
     ```rust
     Proc::PPar(bag) => {
         let new_bag = bag.iter()
             .map(|(elem, count)| {
                 (elem.substitute_X(var, replacement), count)
             })
             .collect();
         Proc::PPar(new_bag)
     }
     ```
   - [ ] Test substitution preserves multiset structure

4. **Auto-Normalization** (Day 7)
   - [ ] Detect zero constructor (e.g., `PZero`)
   - [ ] Generate normalization in constructors/destructors
     ```rust
     impl Proc {
         pub fn normalize(self) -> Self {
             match self {
                 Proc::PPar(bag) if bag.is_empty() => Proc::PZero,
                 Proc::PPar(bag) if bag.len() == 1 =>
                     bag.iter_elements().next().unwrap().clone(),
                 _ => self,
             }
         }
     }
     ```
   - [ ] Optionally auto-normalize in `substitute` and rewrites

5. **Testing** (Day 7)
   - [ ] Generate code for test theories
   - [ ] Verify enum variants correct
   - [ ] Verify Display roundtrip
   - [ ] Verify substitution works

**Deliverable**: Full code generation for collection constructors

---

### Phase 4: Parser Integration (Days 8-9)

**Goal**: Generate LALRPOP parsers that handle collections

#### Tasks

1. **LALRPOP Rule Generation** (`lalrpop_gen.rs`) (Day 8)
   - [ ] Detect `GrammarItem::Collection`
   - [ ] Generate separated list parsing
     ```lalrpop
     // For: HashBag(Proc) sep "|"
     <elems:(<Tier2> "|")*> <last:Tier2?> => {
         let mut bag = mettail_runtime::HashBag::new();
         for elem in elems { bag.insert(elem); }
         if let Some(elem) = last { bag.insert(elem); }
         Proc::PPar(bag)
     }
     ```
   - [ ] Handle delimiters if specified
   - [ ] Generate at appropriate precedence tier

2. **Precedence Handling** (Day 8)
   - [ ] Collection separator gets lowest precedence (per user request)
   - [ ] Place collection rules at `TierN` (lowest)
   - [ ] Other operators parse at higher tiers
   - [ ] Test: `a | b * c` parses as `bag[a, (b * c)]`

3. **Empty Collection Handling** (Day 9)
   - [ ] Parse empty delimited collections: `[]`, `{}`
   - [ ] Generate: `HashBag::new()` or normalize to zero
   - [ ] Test empty collection parsing

4. **Testing** (Day 9)
   - [ ] Parse `a | b | c` → `HashBag([a, b, c])`
   - [ ] Parse `[a, b, c]` if delimiters specified
   - [ ] Parse empty collections
   - [ ] Test precedence: `a | b * c`
   - [ ] Roundtrip: parse → display → parse
   - [ ] Test duplicates: `a | a | b` → `HashBag([(a,2), (b,1)])`

**Deliverable**: Working parsers for collection syntax

---

### Phase 5: Ascent Integration & Testing (Days 10-12)

**Goal**: Ensure collections work in Ascent relations and rewrite engine, including **rest pattern matching**

#### Rest Pattern Syntax

For rewrite rules to work with collections, we need to support **partial matching**:

```rust
// Extract one element:
({P, ...rest}) => P

// Extract specific elements:
({P, Q, ...rest}) => (P | Q)

// Match entire collection:
({P, Q}) => ...  // Only matches bags with exactly 2 elements
```

**Semantics**:
- `{P, ...rest}` matches a HashBag, binding `P` to one element and `rest` to a HashBag of the remaining elements
- Order doesn't matter (AC semantics)
- Rest can be empty: `{P}` is `{P, ...∅}`
- Multiple elements: `{P, Q, ...rest}` removes P and Q from the bag

**Implementation Strategy**:
1. **AST Extension**: Add `RestPattern` to `Expr`:
   ```rust
   Expr::CollectionPattern {
       elements: Vec<Expr>,  // Specific elements to match
       rest: Option<Ident>,  // Variable to bind remaining elements
   }
   ```

2. **Parser Extension**: Recognize `...rest` in equation/rewrite LHS
   - Parse `{P, Q, ...rest}` in `parse_expr`
   - Validate rest appears at most once per collection

3. **Ascent Generation**: Generate Ascent clauses for partial matching
   ```rust
   // For: ({P, ...rest}) => P
   rw_proc(s, t) <--
       proc(s),
       if let Proc::PPar(bag) = s,
       if bag.len() > 0,
       let p = bag.iter().next().unwrap().0.clone(),  // Take one
       let mut rest_bag = bag.clone(),
       rest_bag.remove(&p),  // Remove it
       let t = p;
   ```

4. **Congruence for Rest Patterns**:
   - Collections with rest patterns DON'T get automatic congruence
   - User must explicitly write structural rules
   - This prevents infinite rewrite chains

#### Tasks

1. **Ascent Relation Tests** (Day 10)
   - [ ] Verify `HashBag<Proc>` works in `proc/1` relation
   - [ ] Test equality in Ascent: `proc(PPar([a,b]))`, `proc(PPar([b,a]))` → same fact
   - [ ] Test `eqrel` with collections
   - [ ] Measure performance improvement

2. **Equation Generation** (`ascent_gen.rs`) (Day 10)
   - [ ] Detect collection constructors
   - [ ] Skip generating AC equations (they're implicit)
   - [ ] Generate identity equations if zero constructor exists
   - [ ] Test generated Ascent code compiles

3. **Rest Pattern Implementation** (Day 11) **← NEW**
   - [ ] Extend `Expr` AST with `CollectionPattern`
   - [ ] Extend parser to recognize `...rest` syntax
   - [ ] Validate rest patterns (at most one per collection)
   - [ ] Generate Ascent code for partial matching
   - [ ] Test: `({P, ...rest}) => P` extracts one element
   - [ ] Test: `({P, Q, ...rest}) => P` with multiple elements
   - [ ] Test: empty rest (`...rest` binds to empty HashBag)

4. **Rewrite Compatibility** (Day 11-12)
   - [ ] Test existing rewrites still work
   - [ ] Collections in rewrite patterns (basic support)
   - [ ] Rest patterns in rhocalc structural rules
   - [ ] Ensure freshness checks work
   - [ ] Ensure substitution in RHS works

5. **Benchmark Suite** (Day 12)
   - [ ] Create rhocalc with collection-based `PPar`
   - [ ] Benchmark: depth-3, depth-6, depth-9 terms
   - [ ] Compare: binary PPar vs. HashBag PPar
   - [ ] Measure: rewrites/second, memory usage
   - [ ] Target: 100x speedup

5. **Migration Example** (Day 12)
   - [ ] Convert `rhocalc.rs` to use collections
   - [ ] Document changes needed
   - [ ] Create migration guide
   - [ ] Verify all tests pass

6. **Documentation** (Day 12)
   - [ ] Update README with collection types
   - [ ] Write collection types tutorial
   - [ ] Document syntax and semantics
   - [ ] Update design documents

**Deliverable**: Collections fully integrated, benchmarked, documented

---

## Testing Strategy

### Unit Tests

#### Runtime Tests (`runtime/src/lib.rs`)
```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hashbag_insert_count() {
        let mut bag = HashBag::new();
        bag.insert("a");
        bag.insert("a");
        bag.insert("b");
        assert_eq!(bag.count(&"a"), 2);
        assert_eq!(bag.count(&"b"), 1);
        assert_eq!(bag.len(), 3);
    }

    #[test]
    fn hashbag_equality_order_independent() {
        let mut bag1 = HashBag::new();
        bag1.insert("a");
        bag1.insert("b");
        bag1.insert("c");

        let mut bag2 = HashBag::new();
        bag2.insert("c");
        bag2.insert("a");
        bag2.insert("b");

        assert_eq!(bag1, bag2);
    }

    #[test]
    fn hashbag_remove() {
        let mut bag = HashBag::new();
        bag.insert("a");
        bag.insert("a");
        bag.remove(&"a");
        assert_eq!(bag.count(&"a"), 1);
        bag.remove(&"a");
        assert_eq!(bag.count(&"a"), 0);
    }
}
```

### Integration Tests

#### Collection Parsing (`macros/tests/collection_tests.rs`)
```rust
#[test]
fn parse_hashbag_constructor() {
    let theory_code = quote! {
        theory! {
            name: TestBag,
            exports { Elem }
            terms {
                EBag . Elem ::= HashBag(Elem) sep "|" ;
                EZero . Elem ::= "0" ;
            }
        }
    };
    // Verify it compiles
}

#[test]
fn parse_with_delimiters() {
    let theory_code = quote! {
        theory! {
            name: TestList,
            exports { Elem }
            terms {
                EList . Elem ::= Vec(Elem) sep "," delim "[" "]" ;
            }
        }
    };
    // Verify it compiles
}
```

#### End-to-End Tests (`examples/rhocalc.rs`)
```rust
#[test]
fn rhocalc_with_collections() {
    let rdx_str = "a!(0) | b!(0) | c!(0)";
    mettail_runtime::clear_var_cache();
    let parser = rhocalc::ProcParser::new();
    let proc = parser.parse(rdx_str).unwrap();

    // Verify it's a PPar with HashBag
    if let Proc::PPar(bag) = proc {
        assert_eq!(bag.len(), 3);
    } else {
        panic!("Expected PPar");
    }

    // Verify display
    let displayed = format!("{}", proc);
    let reparsed = parser.parse(&displayed).unwrap();
    assert_eq!(proc, reparsed);
}
```

### Performance Tests

#### Benchmark Suite (`examples/benches/collection_bench.rs`)
```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn benchmark_binary_ppar(c: &mut Criterion) {
    c.bench_function("binary PPar depth 6", |b| {
        b.iter(|| {
            // Generate depth-6 term with binary PPar
            // Run rewrites
            // Measure time
        });
    });
}

fn benchmark_hashbag_ppar(c: &mut Criterion) {
    c.bench_function("HashBag PPar depth 6", |b| {
        b.iter(|| {
            // Generate depth-6 term with HashBag PPar
            // Run rewrites
            // Measure time
        });
    });
}

criterion_group!(benches, benchmark_binary_ppar, benchmark_hashbag_ppar);
criterion_main!(benches);
```

---

## Performance Targets

### Baseline (Binary PPar)
- Depth 3: ~1 second
- Depth 6: 60-80 seconds
- Depth 9: > 5 minutes (extrapolated)

### Target (HashBag PPar)
- Depth 3: < 0.1 seconds (**10x faster**)
- Depth 6: < 1 second (**60-80x faster**)
- Depth 9: < 10 seconds (**30x+ faster**)

### Success Criteria
✅ **100x speedup** for depth-6 terms
✅ **Linear scaling** with term size (not exponential)
✅ **Memory usage** < 100MB for large programs
✅ **Zero regressions** for non-collection theories

---

## Migration Path

### For Existing Theories

**Option 1: Keep Binary Constructors** (No changes needed)
```rust
// Existing code continues to work
PPar . Proc ::= Proc "|" Proc ;
```

**Option 2: Migrate to Collections** (Opt-in)
```rust
// Change one line
PPar . Proc ::= HashBag(Proc) sep "|" ;

// Remove AC equations (now implicit)
// equations {
//     (PPar P Q) == (PPar Q P) ;  // DELETE
//     ...
// }
```

### Migration Checklist

1. [ ] Change constructor definition to use `HashBag`
2. [ ] Remove AC equations (commutativity, associativity)
3. [ ] Keep identity equations (if desired)
4. [ ] Recompile theory
5. [ ] Test parsing and display
6. [ ] Benchmark performance improvement
7. [ ] Update rewrite patterns (Phase 4)

---

## Open Questions & Decisions

### ✅ Resolved

1. **Pattern Syntax** - Flexible delimiters: `sep "sep" [delim "o" "c"]`
2. **Display Ordering** - Arbitrary (fastest)
3. **Empty Collections** - Auto-normalize to zero
4. **Nested Collections** - Not supported initially
5. **Precedence** - Separator has lowest precedence
6. **Ascent Representation** - Collections are enum fields, not special relation handling

### ⏳ Deferred to Phase 4 (Rewrite Pattern Matching)

1. **Pattern matching over bags** - Extract elements, bind rest
2. **Multiple rewrites in one bag** - Apply all applicable rewrites
3. **Non-determinism** - Which rewrite to apply first?

---

## Related Work

### Academic
- **Maude** - AC matching modulo equations
- **K Framework** - Associative lists and sets
- **Stratego/XT** - AC rewriting with annotations

### Rust Ecosystem
- `multiset` crate - Similar to our `HashBag`
- `im` crate - Immutable data structures
- `hashbrown` - Fast hash maps (already in Ascent)

---

## Next Steps

1. ✅ **Review & refine design** (Complete)
2. → **Begin Phase 1: Runtime implementation** (Next)
3. → Weekly check-ins for progress tracking
4. → Adjust plan based on learnings
5. → Document discoveries and decisions

---

**Status**: Ready to begin implementation
**Start Date**: TBD
**Expected Completion**: 10-12 days from start
**Target Performance**: 100x speedup for complex terms
