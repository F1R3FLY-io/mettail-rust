# REPL Implementation: Session Summary

**Date:** November 10, 2025
**Status:** Foundation Complete ✅

---

## 🎉 What We Built

### Core Achievement
Implemented a **fully functional Term Explorer REPL** for interactive rewrite system exploration. Users can now load theories, parse terms, and navigate rewrite graphs interactively.

---

## 📋 Implementation Details

### New Crate: `repl`

```
repl/
├── src/
│   ├── theory.rs         # Theory trait & results types
│   ├── registry.rs       # Dynamic theory loading
│   ├── state.rs          # Session state management
│   ├── repl.rs           # Main REPL loop & commands
│   ├── rhocalc_theory.rs # RhoCalc integration
│   ├── lib.rs            # Module exports
│   └── main.rs           # Binary entry point
├── build.rs              # LALRPOP compilation
└── Cargo.toml            # Dependencies
```

**Lines of Code:** ~800 LOC

---

### Key Components

#### 1. Theory Trait (`theory.rs`)
```rust
pub trait Theory {
    fn name(&self) -> &str;
    fn categories(&self) -> Vec<String>;
    fn constructor_count(&self) -> usize;
    fn equation_count(&self) -> usize;
    fn rewrite_count(&self) -> usize;
    fn parse_term(&self, input: &str) -> Result<Box<dyn Term>>;
    fn run_ascent(&self, term: Box<dyn Term>) -> Result<AscentResults>;
    fn format_term(&self, term: &dyn Term) -> String;
}
```

**Design Decision:** Dynamic dispatch via trait objects for flexible theory loading.

#### 2. Term Trait (`theory.rs`)
```rust
pub trait Term: Display + Debug {
    fn clone_box(&self) -> Box<dyn Term>;
    fn term_id(&self) -> u64;
    fn term_eq(&self, other: &dyn Term) -> bool;
    fn as_any(&self) -> &dyn std::any::Any;
}
```

**Purpose:** Generic interface for terms across different theories.

#### 3. AscentResults (`theory.rs`)
```rust
pub struct AscentResults {
    pub all_terms: Vec<TermInfo>,
    pub rewrites: Vec<Rewrite>,
    pub equivalences: Vec<EquivClass>,
}
```

**Key Insight:** Compute full rewrite graph **once**, then navigate without recomputation.

#### 4. ReplState (`state.rs`)
```rust
pub struct ReplState {
    theory_name: Option<String>,
    current_term: Option<Box<dyn Term>>,
    current_graph_id: Option<u64>,  // Critical for correct navigation!
    history: Vec<HistoryEntry>,
    history_idx: usize,
    ascent_results: Option<AscentResults>,
}
```

**Critical Bug Fix:** Tracked `current_graph_id` separately from `current_term.term_id()` because re-parsing terms from display strings generates different IDs.

#### 5. Commands (`repl.rs`)

**Theory Management:**
- `load <name>` - Load theory by name
- `list-theories` - Show available theories
- `info` - Display current theory metadata

**Term Exploration:**
- `term: <expr>` - Parse and execute term

**Navigation:**
- `rewrites` - List available rewrites
- `apply <N>` - Apply Nth rewrite
- `normal-forms` / `nf` - Show normal forms
- `goto <N>` - Jump to Nth normal form

**General:**
- `help` - Show command list
- `quit` / `exit` - Exit REPL

---

## 🐛 Bugs Fixed

### Critical: Rewrite Navigation Broken After First Apply

**Problem:**
After applying a rewrite, subsequent `rewrites` command showed no available rewrites, even when not at a normal form.

**Root Cause:**
When navigating to a target term:
1. We looked up the target by ID in the graph
2. Re-parsed the term from its display string
3. Used the newly parsed term's ID for filtering

But the newly parsed term got a **different hash ID** than the original term in the graph!

**Solution:**
Added `current_graph_id` to `ReplState`:
- Track the ID from the graph separately
- Use `set_term_with_id()` to explicitly set graph position
- Filter rewrites using `current_graph_id` instead of `term.term_id()`

**Code:**
```rust
pub struct ReplState {
    current_graph_id: Option<u64>,  // ← NEW
    // ...
}

pub fn set_term_with_id(&mut self, term: Box<dyn Term>,
                        results: AscentResults,
                        graph_id: u64) -> Result<()> {
    self.current_graph_id = Some(graph_id);  // ← Track separately
    // ...
}
```

**Impact:** Navigation now works correctly through entire rewrite graph.

---

## 🏗️ Design Decisions

### 1. Single Ascent Execution
**Decision:** Run Ascent once when term is loaded, reuse graph for navigation.

**Rationale:**
- Typical graphs compute in <1 second
- Full materialization enables fast navigation
- No incremental complexity needed yet

**Trade-off:** High memory for large graphs, but acceptable for current use cases.

### 2. Theory Macro Duplication
**Decision:** Each theory module duplicates the `theory!` invocation.

**Problem:** Generated `rhocalc_source!` macro is local to the invoking module.

**Solutions Considered:**
1. Export macro from examples library → **Doesn't work** (macro scope issues)
2. Use `include_source!` → **Doesn't work** (requires local macro)
3. Duplicate theory definition → **✅ Works!**

**Future:** Consider generating theory modules from shared definitions.

### 3. Dynamic Theory Loading
**Decision:** `TheoryRegistry` with `HashMap<String, Box<dyn Theory>>`.

**Rationale:**
- Flexible: Add theories at runtime
- Type-safe: `Theory` trait ensures interface compliance
- Extensible: Easy to add new theories

**Alternative Considered:** Static enum of theories → too rigid for long-term vision.

---

## 📊 Performance Characteristics

### RhoCalc Example (8 concurrent processes)
```
{
    a!(0), for(a->x0){ {x0!(0), for(b->y1){y1!(*a)}} },
    b!(0), for(b->x1){a!(*b)},
    c!(0), for(c->x2){x2!(0)},
    for(@(0)->y0){*y0}
}
```

**Results:**
- Computation: ~18 seconds
- Terms: 50
- Rewrites: 66
- Normal forms: 13

**Navigation:** Instant (<1ms per rewrite)

### Simple Example (2 processes)
```
{a!(0), for(a->x){*x}}
```

**Results:**
- Computation: <1 second
- Terms: 3
- Rewrites: 2
- Normal forms: 1

---

## 🎓 Lessons Learned

### 1. Hash-Based Identity is Tricky
**Problem:** Re-parsing terms breaks identity.

**Lesson:** When working with graphs, explicitly track node IDs separately from term identity.

**Application:** Added `current_graph_id` to separate logical position from term structure.

### 2. Generated Macros Have Scope
**Problem:** Can't export `rhocalc_source!` from library.

**Lesson:** Procedural macro outputs are scoped to the invocation site.

**Workaround:** Duplicate theory definitions where needed.

### 3. Dynamic Dispatch is Powerful
**Insight:** `Box<dyn Theory>` enables flexible theory loading without compile-time knowledge.

**Trade-off:** Small runtime cost, but worth it for extensibility.

---

## 📈 Impact

### User Experience
**Before:** Run examples manually, read terminal output
**After:** Interactive exploration, step through rewrites, inspect graph

### Development Workflow
**Before:** Add `println!` debugging to understand rewrite behavior
**After:** Load theory in REPL, navigate to problem, inspect state

### Future Potential
- Educational tool for teaching process calculi
- Debugging tool for complex rewrite systems
- Foundation for visual graph explorer
- Platform for comparing theories side-by-side

---

## 📝 Documentation Created

1. **[REPL-GUIDE.md](REPL-GUIDE.md)** - Comprehensive user guide
   - Quick start
   - Command reference
   - Example sessions
   - Architecture overview
   - Implementation notes

2. **[REPL-NEXT-STEPS.md](REPL-NEXT-STEPS.md)** - Development roadmap
   - Essential features checklist
   - Time estimates
   - Implementation details
   - Success criteria

3. **Updated [POLY-LINGUAL-ROADMAP.md](POLY-LINGUAL-ROADMAP.md)**
   - Marked REPL foundation complete
   - Updated Q1 2026 priorities

4. **Updated [README.md](../README.md)**
   - Added REPL quick start
   - Updated status line
   - Highlighted new feature

---

## 🎯 Next Steps

### Immediate (Week 2)
1. **History Navigation** - Wire up back/forward commands (2-3h)
2. **Current Term Display** - `show` command with context (1-2h)
3. **Equivalence Classes** - View related terms (2-3h)
4. **Path Visualization** - Show rewrite path (2-3h)
5. **Ambient Calculus** - Add second theory (2-4h)

### Near Term (Weeks 3-4)
- Statistics dashboard
- Better error messages
- Output formatting polish
- Command aliases

### Medium Term (Q1 2026)
- Graph visualization (DOT export)
- Term generation integration
- Multi-theory comparison
- Session save/load

---

## 🏆 Success Metrics

### Functionality ✅
- ✅ Load theories dynamically
- ✅ Parse terms correctly
- ✅ Compute rewrite graphs
- ✅ Navigate rewrites
- ✅ View normal forms
- ✅ Correct graph tracking

### Code Quality ✅
- ✅ Clean module structure
- ✅ Type-safe trait design
- ✅ Error handling with `anyhow`
- ✅ Documented public APIs

### User Experience ✅
- ✅ Colored output
- ✅ Clear command structure
- ✅ Helpful error messages
- ✅ Command history (via rustyline)

### Documentation ✅
- ✅ User guide
- ✅ Developer roadmap
- ✅ Architecture explanation
- ✅ README updates

---

## 🤝 Collaboration Notes

### Code Structure Decisions Made Together
1. Store theory name instead of theory object in state
2. Track graph ID separately from term ID
3. Reuse Ascent results for navigation
4. Duplicate theory definitions per module

### Debugging Together
1. Identified parse-based ID mismatch
2. Traced through rewrite filtering logic
3. Designed `set_term_with_id` solution
4. Tested with complex RhoCalc example

### Design Philosophy Established
- **Correctness first** - Get navigation right before optimizing
- **User experience matters** - Clean, colored, helpful output
- **Document as we go** - Capture decisions while fresh
- **Extensibility** - Design for multiple theories from day one

---

## 🎉 Conclusion

We built a **production-quality REPL foundation** in one session:
- ~800 LOC of clean, well-structured code
- Full navigation through rewrite graphs
- Extensible architecture for multiple theories
- Comprehensive documentation

The REPL is now **usable and useful** - a major milestone for MeTTaIL accessibility!

**Key Achievement:** Interactive exploration is no longer a future vision - it's working today.

---

**Next Session Goal:** Complete essential features (history, context, equivalence classes) to reach MVP status.

