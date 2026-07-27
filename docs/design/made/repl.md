# Term Explorer REPL - Design Document

**Status**: 🎯 Planned
**Timeline**: Q1 2026 (4 weeks)
**Priority**: HIGH (Developer Experience)

---

## Vision

An **interactive REPL** for exploring rewrite systems defined in MeTTaIL. Users can:
1. Load any theory dynamically
2. Input terms (parse, generate, or select)
3. Execute Ascent to compute rewrite closure
4. Query the rewrite graph interactively
5. Step through rewrites one at a time
6. Visualize rewrite paths and equivalence classes

**Goal**: Make MeTTaIL accessible to researchers, educators, and developers by providing an intuitive interface for exploring formal languages and their rewrite semantics.

---

## User Experience

### Startup

```bash
$ mettail repl rholang

╔════════════════════════════════════════════════════════════╗
║                   MeTTaIL Term Explorer                     ║
║                    Version 0.2.0                            ║
╚════════════════════════════════════════════════════════════╝

Loading theory: rholang
  ✓ 2 categories (Proc, Name)
  ✓ 8 constructors
  ✓ 3 equations
  ✓ 3 rewrite rules

Type 'help' for available commands.

rholang>
```

### Term Input

```
rholang> term: {a!(0), for(a->x0){*x0}}

Parsing... ✓
Running Ascent... ████████████████████ Done. (127ms)

Computed:
  - 45 terms
  - 62 rewrites
  - 11 normal forms

Current term: {a!(0), for(a->x0){*x0}}

rholang>
```

### Querying Rewrites

```
rholang> next

Available rewrites from {a!(0), for(a->x0){*x0}}:

  [1] {*@(0)}
      via: Communication (PInput/POutput)
      binds: chan=a, x=x0, P=*x0, Q=0

Select [1] or 'back' to return.

rholang> 1

Stepping to: {*@(0)}

Current term: {*@(0)}  [Normal form ✓]

rholang>
```

### Exploring the Graph

```
rholang> graph

Rewrite graph for initial term {a!(0), for(a->x0){*x0}}:

{a!(0), for(a->x0){*x0}}
  └─[comm]─> {*@(0)} ✓

Paths to normal forms: 1
Total reachable terms: 2

rholang>
```

### Generating Terms

```
rholang> generate random 5

Generated term at depth 5:
{for(a->x1){x1!(0)}, b!(for(a->x2){*x2}), for(@(0)->y0){*y0}}

Running Ascent... Done. (89ms)
  - 234 terms
  - 412 rewrites
  - 17 normal forms

rholang>
```

### Viewing Normal Forms

```
rholang> normals

Normal forms (11 found):

  [1] *@(0)
  [2] @(0)!(0)
  [3] @(*b)!(0)
  [4] {0, @(0)!(0), a!(*b)}
  [5] {0, @(*b)!(0), a!(0)}
  ... (6 more)

Select [1-11] to jump to that term, or 'all' to see full list.

rholang> 1

Jumping to: *@(0)

Current term: *@(0)  [Normal form ✓]

rholang>
```

### History and Navigation

```
rholang> history

Session history:

  [0] {a!(0), for(a->x0){*x0}}  (initial)
  [1] {*@(0)}  ← current

Type 'back' or 'goto <n>' to navigate.

rholang> back

Returning to: {a!(0), for(a->x0){*x0}}

Current term: {a!(0), for(a->x0){*x0}}

rholang>
```

### Equivalence Classes

```
rholang> equiv

Equivalence class of {a!(0), for(a->x0){*x0}}:

Terms in this class (modulo equations):
  - {a!(0), for(a->x0){*x0}}
  - {for(a->x0){*x0}, a!(0)}  (reordering)

All terms in this class can rewrite to the same normal forms.

rholang>
```

### Help System

```
rholang> help

Available commands:

Term Input:
  term: <expr>       Parse and load a term
  generate random <depth>  Generate random term at given depth
  generate all <depth>     Generate all terms up to depth
  example <n>        Load example term #n

Navigation:
  next               Show available rewrites from current term
  step <n>           Apply rewrite #n and move forward
  back               Go back to previous term
  goto <n>           Jump to term #n in history
  reset              Return to initial term

Queries:
  normals            Show all normal forms
  equiv              Show equivalence class
  graph              Visualize rewrite graph
  history            Show navigation history
  stats              Display statistics

Theory:
  load <theory>      Load a different theory
  info               Show theory information
  list-theories      List available theories

General:
  help               Show this help
  quit, exit         Exit REPL

rholang>
```

---

## Architecture

### Component Overview

```
┌─────────────────────────────────────────────────────────┐
│                     repl                        │
│                                                         │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐ │
│  │   CLI/TUI    │  │  Ascent      │  │   Theory     │ │
│  │   Interface  │◄─┤  Executor    │◄─┤   Loader     │ │
│  └──────────────┘  └──────────────┘  └──────────────┘ │
│         │                  │                 │          │
│         ▼                  ▼                 ▼          │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐ │
│  │  Navigation  │  │   Query      │  │   Parser     │ │
│  │   History    │  │   Engine     │  │   Dynamic    │ │
│  └──────────────┘  └──────────────┘  └──────────────┘ │
│         │                  │                 │          │
│         └──────────────────┴─────────────────┘          │
│                           │                             │
│                    ┌──────▼──────┐                      │
│                    │    State    │                      │
│                    │   Manager   │                      │
│                    └─────────────┘                      │
└─────────────────────────────────────────────────────────┘
                           │
                           ▼
               ┌───────────────────────┐
               │  mettail-examples     │
               │  (theory definitions) │
               └───────────────────────┘
```

### Key Components

#### 1. State Manager

Maintains the current session state:
- Loaded theory
- Current term
- Navigation history
- Computed Ascent results (relations)
- Normal forms cache

```rust
struct ReplState {
    theory_name: String,
    current_term: Box<dyn Category>,  // Trait object for any category
    history: Vec<HistoryEntry>,
    ascent_results: AscentResults,
    normal_forms: Vec<Box<dyn Category>>,
}

struct HistoryEntry {
    term: Box<dyn Category>,
    rewrite_applied: Option<RewriteInfo>,
}
```

#### 2. Theory Loader

Dynamically loads theory definitions:
- Scans `mettail-examples/` for theories
- Compiles theory to Rust code
- Links dynamically (or uses pre-compiled)
- Provides parser, AST types, and Ascent runner

**Challenge**: Rust doesn't have traditional dynamic loading. Solutions:
1. **Pre-compile all theories** - Include them at compile time
2. **Dynamic library loading** - Use `libloading` crate
3. **Proc-macro at runtime** - Requires nightly, complex

**Recommendation**: Start with **pre-compiled theories** using a registry:

```rust
trait Theory {
    fn name(&self) -> &str;
    fn parse(&self, input: &str) -> Result<Box<dyn Category>, ParseError>;
    fn run_ascent(&self, term: Box<dyn Category>) -> AscentResults;
    fn format_term(&self, term: &dyn Category) -> String;
}

// In mettail-examples/lib.rs:
pub fn get_theory(name: &str) -> Option<Box<dyn Theory>> {
    match name {
        "rholang" => Some(Box::new(RhoCalculusTheory)),
        "ambient" => Some(Box::new(AmbientCalculusTheory)),
        _ => None
    }
}
```

#### 3. Ascent Executor

Runs Ascent on the current term:
- Takes a term as input
- Executes the theory's Ascent program
- Returns relations: `proc(T)`, `eq_proc(T,U)`, `rw_proc(S,T)`
- Caches results for queries

```rust
struct AscentResults {
    all_terms: HashSet<Box<dyn Category>>,
    rewrites: Vec<Rewrite>,
    equations: HashMap<Box<dyn Category>, HashSet<Box<dyn Category>>>,
}

struct Rewrite {
    from: Box<dyn Category>,
    to: Box<dyn Category>,
    rule_name: String,
}
```

#### 4. Query Engine

Answers queries about the rewrite graph:
- **next**: Find all direct rewrites from current term
- **normals**: Find normal forms (no outgoing rewrites)
- **equiv**: Find all equivalent terms (via equations)
- **graph**: Build rewrite graph from initial term
- **stats**: Count terms, rewrites, normal forms

```rust
impl QueryEngine {
    fn next_rewrites(&self, term: &dyn Category) -> Vec<Rewrite>;
    fn normal_forms(&self) -> Vec<Box<dyn Category>>;
    fn equivalence_class(&self, term: &dyn Category) -> HashSet<Box<dyn Category>>;
    fn reachable_from(&self, term: &dyn Category) -> HashSet<Box<dyn Category>>;
}
```

#### 5. Navigation History

Stack-based navigation:
- Push new term when stepping forward
- Pop when going back
- Support arbitrary jumps via `goto`

```rust
struct NavigationHistory {
    stack: Vec<HistoryEntry>,
    current_idx: usize,
}

impl NavigationHistory {
    fn push(&mut self, entry: HistoryEntry);
    fn back(&mut self) -> Option<&HistoryEntry>;
    fn goto(&mut self, idx: usize) -> Option<&HistoryEntry>;
}
```

#### 6. CLI/TUI Interface

Two modes:
- **CLI mode**: Simple line-based REPL (like `irb`, `ghci`)
- **TUI mode**: Full terminal UI (like `htop`, `lazygit`)

Start with **CLI mode** for simplicity, add TUI later.

**CLI Libraries**:
- `rustyline` - Line editing, history, completion
- `colored` - Terminal colors
- `indicatif` - Progress bars

**TUI Libraries** (future):
- `ratatui` - Terminal UI framework
- `crossterm` - Terminal control

---

## Implementation Plan

### Phase 1: Foundation (Week 1)

**Goal**: Basic REPL with theory loading and term parsing

**Tasks**:
1. Create `repl` crate
2. Set up CLI with `rustyline`
3. Implement theory registry in `mettail-examples`
4. Add `Theory` trait with basic methods
5. Implement theory loading for Rholang
6. Parse terms and display them

**Deliverable**: Can load Rholang and parse terms

```bash
$ mettail repl rholang
rholang> term: a!(0)
Parsed: a!(0)
rholang>
```

### Phase 2: Ascent Integration (Week 1)

**Goal**: Execute Ascent and store results

**Tasks**:
1. Extend `Theory` trait with `run_ascent`
2. Implement Ascent execution for Rholang
3. Extract relations into `AscentResults`
4. Add `stats` command to display results

**Deliverable**: Can run Ascent and see statistics

```bash
rholang> term: {a!(0), for(a->x0){*x0}}
Running Ascent... Done.
  - 45 terms
  - 62 rewrites
  - 11 normal forms
rholang> stats
[displays detailed statistics]
```

### Phase 3: Query Engine (Week 2)

**Goal**: Implement all query commands

**Tasks**:
1. Implement `QueryEngine` struct
2. Add `next` command (find direct rewrites)
3. Add `normals` command (find normal forms)
4. Add `equiv` command (equivalence classes)
5. Add `graph` command (visualize reachable terms)

**Deliverable**: Can query the rewrite graph

```bash
rholang> next
Available rewrites:
  [1] {*@(0)} via Communication
rholang> normals
11 normal forms found
```

### Phase 4: Navigation (Week 2)

**Goal**: Step through rewrites interactively

**Tasks**:
1. Implement `NavigationHistory`
2. Add `step <n>` command
3. Add `back` command
4. Add `goto <n>` command
5. Add `history` command

**Deliverable**: Can explore rewrite graph interactively

```bash
rholang> next
[1] {*@(0)}
rholang> step 1
Stepping to: {*@(0)}
rholang> back
Returning to: {a!(0), for(a->x0){*x0}}
```

### Phase 5: Term Generation (Week 3)

**Goal**: Generate test terms

**Tasks**:
1. Extend `Theory` trait with generation methods
2. Implement `generate random <depth>`
3. Implement `generate all <depth>` (if feasible)
4. Add `example <n>` for pre-defined examples

**Deliverable**: Can generate and explore random terms

```bash
rholang> generate random 4
Generated: {a!(0), b!(0)}
Running Ascent... Done.
```

### Phase 6: Polish (Week 3-4)

**Goal**: Improve UX, add documentation

**Tasks**:
1. Add colors and formatting
2. Improve error messages
3. Add command completion (via `rustyline`)
4. Write user documentation
5. Add unit tests
6. Test with all example theories (Rholang, Ambient)

**Deliverable**: Production-ready REPL

---

## Technical Challenges

### Challenge 1: Dynamic Theory Loading

**Problem**: Rust doesn't have traditional runtime code loading.

**Solutions**:
1. **Pre-compile registry** (easiest)
   - Compile all theories into `mettail-examples`
   - Register them in a static map
   - Limitation: Can't add theories without recompiling

2. **Dynamic library loading** (harder)
   - Compile each theory to `.so`/`.dylib`/`.dll`
   - Use `libloading` to load at runtime
   - Requires stable ABI (hard in Rust)

3. **JIT compilation** (hardest)
   - Use `cranelift` or LLVM to JIT compile
   - Very complex, overkill for this use case

**Recommendation**: Start with #1 (pre-compile registry), move to #2 if needed.

### Challenge 2: Generic Term Type

**Problem**: Different theories have different term types (`Proc`, `Elem`, etc.)

**Solutions**:
1. **Trait objects** (`Box<dyn Category>`)
   - Requires `Category` trait with common operations
   - Downcast when needed for theory-specific ops

2. **Type erasure** (wrap terms)
   - Create `AnyTerm` enum with variants per theory
   - Match on theory to access concrete type

3. **Macro-generated dispatch**
   - Generate theory-specific REPL code
   - No runtime overhead, but code duplication

**Recommendation**: Use trait objects with careful design:

```rust
trait Category: Display + Debug + Clone + PartialEq + Eq + Hash {
    fn as_any(&self) -> &dyn Any;
    fn to_boxed(&self) -> Box<dyn Category>;
}
```

### Challenge 3: Ascent Results Extraction

**Problem**: Ascent results are in closure, need to extract.

**Solution**: Modify Ascent invocation to return relations:

```rust
let prog = ascent_run! {
    relation proc(Proc);
    relation rw_proc(Proc, Proc);
    // ... rules ...
};

// Access relations
let all_procs: Vec<Proc> = prog.proc.iter().cloned().collect();
let all_rewrites: Vec<(Proc, Proc)> = prog.rw_proc.iter().cloned().collect();
```

This works because `ascent_run!` returns a struct with relation fields!

### Challenge 4: Term Equality Across Rewrites

**Problem**: Need to match user-selected term with Ascent results.

**Solution**:
- Implement `Eq` and `Hash` for all term types (already done!)
- Use `HashMap` for fast lookups
- Handle α-equivalence by normalizing binders

---

## Future Enhancements

### TUI Mode

Full terminal UI with panels:
```
┌─────────────────────────────────────────────────────────┐
│ Theory: Rholang                              [Ctrl+Q]   │
├────────────────────────┬────────────────────────────────┤
│ Current Term:          │ Available Rewrites:            │
│                        │                                │
│ {a!(0),                │ [1] {*@(0)}                    │
│  for(a->x0){*x0}}      │     via Communication          │
│                        │                                │
│ History:               │ Normal Forms: 11               │
│ [0] Initial term       │ Equivalents:  2                │
│ [1] Current ◄          │                                │
│                        │                                │
├────────────────────────┴────────────────────────────────┤
│ > next                                                   │
└─────────────────────────────────────────────────────────┘
```

### Graph Visualization

ASCII art or export to GraphViz:
```
{a!(0), for(a->x0){*x0}}
  │
  └─[comm]─> {*@(0)} ✓
```

Or export DOT:
```bash
rholang> export graph.dot
Exported rewrite graph to graph.dot
$ dot -Tpng graph.dot -o graph.png
```

### Proof Explanation

Show why two terms are equivalent:
```bash
rholang> why-equal "{a!(0), b!(0)}" "{b!(0), a!(0)}"

Terms are equal via:
  1. Commutativity of PPar (equation)

Proof tree:
  {a!(0), b!(0)}
    ≡ {b!(0), a!(0)}  [PPar commutativity]
```

### Performance Profiling

Per-rule performance:
```bash
rholang> profile

Rule execution times:
  Communication: 23ms (45 applications)
  Congruence:    89ms (234 applications)
  Drop:          12ms (17 applications)

Total Ascent time: 127ms
```

---

## Success Metrics

### Usability
- ✅ Can load and explore any theory in < 5 commands
- ✅ Intuitive navigation (no manual needed for basics)
- ✅ Fast response times (< 200ms for queries)

### Completeness
- ✅ All example theories work (Rholang, Ambient)
- ✅ Can handle 1000+ term graphs
- ✅ Supports all query types (next, normals, equiv, graph)

### Quality
- ✅ Clear error messages
- ✅ Comprehensive help system
- ✅ Well-documented code
- ✅ Unit tests for core logic

---

## Conclusion

The Term Explorer REPL will make MeTTaIL **accessible and usable** by:
- Providing an intuitive interface for exploring rewrite systems
- Enabling interactive debugging of theories
- Demonstrating MeTTaIL's capabilities to new users
- Laying groundwork for educational applications

**Timeline**: 4 weeks (Jan-Feb 2026)
**Effort**: ~80-100 hours
**Priority**: HIGH - essential for developer experience

This is a **foundational tool** that will enable all future work on MeTTaIL by making it easy to understand, debug, and demonstrate the system.

