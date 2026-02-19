# Sharing ascent_syntax_export without cloning
_Exported on 2/16/2026 at 16:03:53 PST from Cursor (2.4.23)_

---

**User**

@ascent is an embedding of datalog in rust via macros. I'm using it for a logic interface, and to expose some of its syntax internals I made @ascent/ascent_syntax_export. so far this has been working fine on my machine, but the whole directory is gitignored, so it couldn't be shared. hopefully there is a way to do this without requiring other users to clone ascent. determine the best approach, and summarize in the chat.

---

**Cursor**

Exploring the ascent_syntax_export setup and how it relates to ascent so we can recommend a shareable approach.


Checking workspace layout and how ascent_syntax_export is used:


Checking whether ascent is published on crates.io and how ascent_base is used:


Checking whether the vendored parser code references ascent_base:


Checking where the crate is referenced from and the exact path layout:


Here’s a concise summary and the approach that fits your setup.

---

## Situation

- **ascent_syntax_export** lives under **ascent/** (and the whole **ascent/** tree is gitignored).
- **build.rs** reads from `../ascent_macro/src`, patches three files, and writes to **src/vendored/**.
- **src/vendored/** is in `.gitignore`, so the patched code is never committed and the crate only works when ascent is cloned locally.
- **crates/db** and **crates/ui** depend on it (path deps are commented out). **ascent_base** is used by the vendored code (`ascent_base::util::update`); ascent and ascent_base are on crates.io.

---

## Recommended approach: vendor patched source and move crate into the repo

**1. Commit the vendored parser**

- Run the current build once (with ascent present) so **src/vendored/** is generated.
- Remove **src/vendored/** from `.gitignore` and **commit** those files (patched `ascent_syntax.rs`, `syn_utils.rs`, `utils.rs`, and the vendored `mod.rs`).
- The crate then builds from committed source; no clone of ascent is required for normal builds.

**2. Move the crate out of the ignored tree**

- Move **ascent_syntax_export** from **ascent/ascent_syntax_export** to something like **crates/ascent_syntax_export** so it’s inside the repo and not under **ascent/**.
- Add **crates/ascent_syntax_export** to the workspace and point **crates/db** and **crates/ui** at this path (and uncomment their dependency).

**3. Make build.rs optional**

- At the start of **build.rs**: if ascent_macro source is available (e.g. env `ASCENT_MACRO_SRC` or a known path such as `../../ascent/ascent_macro/src` when you have ascent beside the repo), run the existing patch and write to **src/vendored/**; otherwise **do nothing** (no copy, no write).
- So: “ascent present” → regenerate vendored files; “ascent not present” → use committed **src/vendored/** and don’t require ascent.

**4. Dependencies**

- In **ascent_syntax_export**’s **Cargo.toml**, depend on **ascent_base** from crates.io (e.g. `ascent_base = "0.8"`) instead of a workspace path, so the crate is self-contained and buildable without a local ascent tree.

**5. Document regeneration (optional)**

- In the crate (e.g. README or a comment in **build.rs**), note that **src/vendored/** was generated from **ascent_macro** and that maintainers can regenerate it by pointing at ascent (e.g. via `ASCENT_MACRO_SRC` or by cloning ascent and running from the repo root).

---

## Why not the other options

- **Git submodule for ascent** – Forces everyone to clone and manage ascent; you said you want to avoid requiring others to clone ascent.
- **Rely only on published ascent/ascent_macro** – The parser and types you need are internal (`pub(crate)`) in **ascent_macro** and not part of its public API, so you can’t get them from crates.io without either vendoring (what you’re doing) or a fork that exposes them.
- **Leaving the crate under ascent/ and only un-ignoring it** – It would still depend on sibling **ascent_macro** for build.rs; without committing vendored output, anyone without ascent would still have a broken build.

---

**TL;DR:** Commit the current **src/vendored/** output, move **ascent_syntax_export** to **crates/ascent_syntax_export**, make **build.rs** only run when ascent (or `ASCENT_MACRO_SRC`) is present, and depend on **ascent_base** from crates.io. Then the crate is shareable and buildable without cloning ascent; only maintainers who want to refresh the parser need access to ascent.

---

**User**

okay, I just moved @crates/ascent_syntax_export into my crates. please proceed 

---

**Cursor**


Checking the crate's state and applying the planned changes.



Vendored files are present. Checking the UI Cargo.toml location and .gitignore:



Implementing the plan: creating the todo list and applying changes.



Fixing the type: `env::var().map(Path::new)` yields a reference; unifying to `PathBuf`:



Checking how the UI crate is built (workspace membership):



Verifying the workspace builds:



Summary of what was done:

**1. build.rs is optional**
- Build script runs the vendoring/patch only when ascent_macro source is available:
  - Env: `ASCENT_MACRO_SRC` (path to `ascent_macro/src`), or
  - Default path: `../../ascent/ascent_macro/src` (ascent at repo root).
- If neither is present, it does nothing and the committed `src/vendored/` is used.

**2. Vendored code is tracked**
- `.gitignore` no longer ignores `src/vendored/`, so the existing vendored files are committed and the crate builds without a local ascent clone.

**3. ascent_base from crates.io**
- `ascent_syntax_export/Cargo.toml` now has `ascent_base = "0.8"` instead of `workspace = true`, so it works without ascent in the tree.

**4. Workspace and dependencies**
- Root `Cargo.toml`: added `crates/ascent_syntax_export` to `members` and `ascent_syntax_export = { path = "crates/ascent_syntax_export" }` to `[workspace.dependencies]`.
- `crates/db/Cargo.toml`: uncommented `ascent_syntax_export = { workspace = true }`.
- `crates/ui/Cargo.toml`: switched to `ascent_syntax_export = { workspace = true }` (replacing the old ascent path).

`cargo check -p ascent_syntax_export -p db` completes successfully. Anyone who clones the repo can build without ascent. To refresh the vendored parser from a local ascent clone, put it at `ascent/` next to the repo and build, or set `ASCENT_MACRO_SRC` to the `ascent_macro/src` directory.

