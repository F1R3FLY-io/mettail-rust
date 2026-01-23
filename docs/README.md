# MeTTaIL Documentation

Organized documentation for the MeTTaIL project.

---

## Core Documents (Living)

These documents are actively maintained and should always reflect the current state:

- **`main_goals.md`** - Project vision, objectives, and roadmap
- **`getting_started.md`** - Quick start guide for new users
- **`architecture.md`** - System design and implementation overview
- **`contributing.md`** - How to contribute to the project

---

## Guides (Topical)

Focused guides on specific features:

- **`guides/theory_syntax.md`** - Complete `theory!` macro syntax reference
- **`guides/collections.md`** - Collection types and pattern matching
- **`guides/bindings.md`** - Variable binding and substitution
- **`guides/repl.md`** - Interactive REPL usage (→ `REPL-GUIDE.md`)

---

## Design Documents

Detailed technical designs:

### Made (Implemented)
- **`design/made/ascent_generation.md`** - How Datalog rules are generated
- **`design/made/data_structures.md`** - Collections and binding design
- **`design/made/repl.md`** - Term explorer REPL design

### Exploring (In Progress / Future)
- **`design/exploring/theory_composition.md`** - Module system design
- **`design/exploring/k_framework_comparison.md`** - Comparison with K Framework
- **`design/exploring/performance.md`** - Performance analysis and optimization

---

## Historical (Archive)

Development history organized by phase:

- **`archive/phase-1/`** - Initial implementation (parsing, binding, substitution)
- **`archive/phase-2/`** - Parser generation and rewrite engine
- **`archive/phase-3/`** - Collections and optimization
- **`archive/phase-6/`** - Equations and congruence rules

**Note**: Archive is for historical reference. Check core docs for current state.

---

## Internal (Meta)

Internal documentation about the documentation itself:

- **`meta/ide_linting.md`** - Handling IDE false positives
- **`meta/phase_naming.md`** - Development phase organization

---

## Reading Path for New Contributors

1. **Start**: `getting_started.md` - Learn basics
2. **Understand**: `architecture.md` - See how it works
3. **Explore**: `guides/` - Deep dive into specific features
4. **Design**: `design/made/` - Understand implementation decisions
5. **Contribute**: `contributing.md` - Make changes

---

## Reading Path for Researchers

1. **Vision**: `main_goals.md` - Understand objectives
2. **Theory**: `guides/theory_syntax.md` - See formal language
3. **Design**: `design/made/ascent_generation.md` - Execution model
4. **Performance**: `design/exploring/performance.md` - Optimization strategies
5. **Future**: `main_goals.md` → Theory Translation section

---

## Maintenance

### When to Update Core Docs
- ✅ Major feature completion
- ✅ API changes
- ✅ Architecture changes
- ✅ New milestones reached

### When to Create New Docs
- ✅ New major feature needs explanation
- ✅ Complex design needs documentation
- ✅ Common questions need answers
- ❌ Don't create for every minor change

### When to Archive
- ✅ Phase/milestone complete
- ✅ Design decisions finalized
- ✅ Information superseded by new approach
- ❌ Don't delete - move to `archive/`

---

## Documentation Style

- **Lowercase filenames**: `main_goals.md`, not `MAIN-GOALS.md`
- **Underscores for spaces**: `theory_syntax.md`, not `theory-syntax.md`
- **Clear structure**: Use headings, lists, code blocks
- **Examples**: Show, don't just tell
- **Concise**: Respect reader's time
- **Current**: Update "Last Updated" date

---

**Last Updated**: December 2025

