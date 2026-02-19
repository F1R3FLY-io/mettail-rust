# ascent_syntax_export integration plan (2026-02-16)

## Context

`ascent_syntax_export` was created in another workspace to expose Ascent’s internal parser types for runtime use. It was moved into this repo (at repo root as `ascent_syntax_export/`) and the sharing approach from `cursor_sharing_ascent_syntax_export_wit.md` was already applied there: optional `build.rs`, committed vendored source, `ascent_base` from crates.io.

This doc records what was done to **complete integration in mettail-rust** and how to use it.

---

## Plan (completed)

1. **Workspace integration**
   - Add `ascent_syntax_export` to root `Cargo.toml` `[workspace]` `members`.
   - Add `ascent_syntax_export = { path = "ascent_syntax_export" }` to `[workspace.dependencies]` so other crates can depend on it via `ascent_syntax_export = { workspace = true }`.

2. **No crate layout change**
   - Crate stays at repo root as `ascent_syntax_export/` (this repo has no `crates/` dir; members are top-level). `version.workspace = true` is satisfied by root `[workspace.package]` version.

3. **Demo**
   - Add `ascent_syntax_export/examples/parse_demo.rs`: parses a small Ascent program (transitive closure), then prints relations and rule heads via `parse_ascent_program_text`, `extract_relations`, `extract_rule_heads`.

4. **Verification**
   - `cargo check -p ascent_syntax_export` and `cargo run -p ascent_syntax_export --example parse_demo` both succeed.

---

## Usage

- **Run the demo**
  ```bash
  cargo run -p ascent_syntax_export --example parse_demo
  ```

- **Depend from another workspace crate** (e.g. `languages` or `repl` when you need to parse Ascent):
  ```toml
  [dependencies]
  ascent_syntax_export = { workspace = true }
  ```

- **Parse Ascent program text in code**
  ```rust
  use ascent_syntax_export::{parse_ascent_program_text, extract_relations, extract_rule_heads};

  let program = parse_ascent_program_text(r#" relation edge(i32,i32); path(x,y) <-- edge(x,y); "#)?;
  let relations = extract_relations(&program);
  let heads = extract_rule_heads(&program);
  ```

---

## Regenerating vendored parser (maintainers)

If you have a local Ascent clone and need to refresh `ascent_syntax_export/src/vendored/`:

- Put the ascent repo next to mettail-rust so the path from `ascent_syntax_export/` is `../../ascent/ascent_macro/src`, then build; or
- Set `ASCENT_MACRO_SRC` to the `ascent_macro/src` directory and build.

Then commit the updated `src/vendored/` files.
