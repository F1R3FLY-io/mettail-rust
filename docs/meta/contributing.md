# Contributing to MeTTaIL

Thank you for your interest in contributing to MeTTaIL!

---

## Getting Started

1. **Read the docs**: Start with `getting_started.md` and `architecture.md`
2. **Build the project**: `cargo build --workspace`
3. **Run tests**: `cargo test --workspace`
4. **Try examples**: `cargo run --example rholang_demo`
5. **Explore**: `cargo run --bin repl`

---

## Ways to Contribute

### 1. Bug Reports
- Use GitHub Issues
- Include minimal reproduction
- Specify expected vs actual behavior
- Include theory definition if relevant

### 2. Feature Requests
- Open a Discussion first for large features
- Explain use case and motivation
- Propose API if applicable

### 3. Code Contributions
- Fork the repository
- Create feature branch
- Make changes with tests
- Open Pull Request

### 4. Documentation
- Fix typos and unclear explanations
- Add examples
- Improve comments
- Write tutorials

### 5. Example Theories
- Implement interesting calculi
- Add to `theories/` or `examples/`
- Include tests and documentation

---

## Development Guidelines

### Code Style

- **Follow Rust conventions**: `rustfmt` and `clippy`
- **Document public APIs**: Doc comments for all public items
- **Test your changes**: Add tests for new features
- **Keep it simple**: Prefer clarity over cleverness

### Testing

```bash
# Run all tests
cargo test --workspace

# Run specific test
cargo test test_name

# Run with output
cargo test -- --nocapture

# Check compilation only
cargo check --workspace
```

### Commit Messages

Use clear, descriptive commit messages:
```
Add collection pattern matching for nested terms

- Implement projection-based matching
- Handle shared variables via joins
- Add tests for nested patterns
```

### Pull Requests

- **Small PRs preferred**: Easier to review
- **Link to issue**: Reference issue number if applicable
- **Describe changes**: What and why
- **Update docs**: Keep documentation in sync
- **Pass CI**: Ensure tests pass

---

## Project Structure

```
macros/          # Procedural macro implementation
├── ast/         # Theory AST types and parsing
├── validation/  # Semantic checking
├── codegen/     # Rust code generation
└── ascent/      # Datalog rule generation

runtime/         # Runtime support library
├── collections/ # HashBag, HashSet
└── binding.rs   # Variable binding via moniker

theories/        # Example theories
├── rholang.rs   # Rho Calculus
└── ambient.rs   # Ambient Calculus

repl/            # Interactive explorer
examples/        # Demo programs
docs/            # Documentation
```

---

## Adding New Features

### Adding Grammar Items

If you want to support a new kind of grammar item (like `Collection`):

1. **Extend AST** in `macros/src/ast/types.rs`:
   ```rust
   pub enum GrammarItem {
       Terminal(String),
       NonTerminal(Ident),
       // Add your new variant
       MyNewItem { ... },
   }
   ```

2. **Update parser** in `macros/src/ast/parsing.rs`

3. **Update validation** in `macros/src/validation/validator.rs`

4. **Update code generation**:
   - `codegen/ast_gen.rs` - Rust enum generation
   - `codegen/parser/lalrpop.rs` - Parser grammar
   - `codegen/subst.rs` - Substitution
   - `codegen/display.rs` - Pretty-printing

5. **Update Ascent generation**:
   - `ascent/relations.rs` - If new relations needed
   - `ascent/categories.rs` - Deconstruction rules
   - `ascent/rewrites/patterns.rs` - Pattern matching
   - `ascent/rewrites/rhs.rs` - RHS construction

6. **Add tests**: Test round-trip parsing, execution, etc.

### Adding Rewrite Features

For new pattern syntax or rewrite capabilities:

1. **Extend `Expr`** in `macros/src/ast/types.rs`
2. **Update parser** for new syntax
3. **Generate pattern matching** in `ascent/rewrites/patterns.rs`
4. **Generate RHS** in `ascent/rewrites/rhs.rs`
5. **Add tests**

### Adding Validation Rules

To add new semantic checks:

1. **Add check** in `validation/validator.rs`
2. **Define error** in `validation/error.rs`
3. **Add test** showing error is caught

---

## Testing Guidelines

### Unit Tests

Test individual functions:
```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_my_feature() {
        // Arrange
        let input = ...;

        // Act
        let result = my_function(input);

        // Assert
        assert_eq!(result, expected);
    }
}
```

### Integration Tests

Test full theory compilation:
```rust
#[test]
fn test_simple_theory_compiles() {
    theory! {
        name: Simple,
        exports { T },
        terms { T ::= A | B(T) },
    }

    let term = T::B(Box::new(T::A));
    assert_eq!(format!("{}", term), "B(A)");
}
```

### Property-Based Tests (Future)

Generate random inputs and check invariants:
```rust
#[quickcheck]
fn parse_display_roundtrip(term: Proc) -> bool {
    let displayed = format!("{}", term);
    let parsed = Proc::parse(&displayed).unwrap();
    parsed == term
}
```

---

## Debugging

### Macro Expansion

```bash
# See generated code
cargo expand -p mettail-theories --lib

# Just one module
cargo expand -p mettail-theories rholang
```

### Ascent Output

Ascent code is printed during compilation:
```bash
cargo build -p mettail-theories 2>&1 | less
```

Look for:
```
========== FULL GENERATED ASCENT SOURCE ==========
ascent_source! {
    ...
}
```

### IDE Issues

If rust-analyzer shows false errors, see `design/ide_linting.md`.

---

## Documentation Standards

### Code Comments

```rust
/// Public API documentation (shows in docs)
///
/// # Examples
/// ```
/// let term = Proc::PZero;
/// ```
pub fn my_function() { }

// Private implementation comments
fn helper() {
    // Explain why, not what
}
```

### Doc Files

- Use lowercase with underscores: `my_feature.md`
- Keep focused on one topic
- Include examples
- Link to related docs
- Update "Last Updated" date

---

## Communication

### Questions
- Open a GitHub Discussion
- Be specific about what you're trying to do
- Include relevant code snippets

### Bug Reports
- GitHub Issues
- Include reproduction steps
- Specify versions
- Share relevant theory code

### Feature Discussion
- Start with Discussion, not PR
- Explain motivation and use case
- Consider alternatives
- Be open to feedback

---

## Code Review Process

### For Contributors
- Expect feedback and iteration
- Be responsive to comments
- Ask questions if unclear
- Be patient - reviews take time

### For Reviewers
- Be constructive and specific
- Explain reasoning
- Suggest improvements
- Appreciate the effort

---

## Getting Help

- **Documentation**: `docs/` directory
- **Examples**: `examples/` and `theories/`
- **Discussions**: GitHub Discussions
- **Issues**: For bugs and concrete problems

---

## License

MeTTaIL is open source. By contributing, you agree that your contributions will be licensed under the project license.

---

**Thank you for helping make MeTTaIL better!**

**Last Updated**: December 2025

