# Module 9: The REPL

**Goal**: Understand the interactive exploration tool and how to extend it.

The REPL (Read-Eval-Print Loop) is the user-facing application. It's where you interact with languages, execute terms, explore rewrites, and manage environments.

---

## 9.1 Entry Point

**File**: `repl/src/main.rs`

```rust
fn main() -> Result<()> {
    let args = Args::parse();           // CLI: optional language name
    let registry = build_registry()?;   // Register all languages
    let mut repl = Repl::new(registry)?; // Create REPL with rustyline editor

    if let Some(language_name) = args.language {
        repl.load_language(&language_name)?;  // Pre-load if specified
    }

    repl.run()?;  // Enter the command loop
    Ok(())
}
```

You can start with a language pre-loaded:
```bash
cargo run -- rhocalc    # Equivalent to starting then typing "lang rhocalc"
```

---

## 9.2 The Language Registry

**File**: `repl/src/registry.rs`

```rust
pub struct LanguageRegistry {
    languages: HashMap<String, Box<dyn Language>>,
}
```

The registry maps lowercase names to `Language` trait objects. `build_registry()` creates one with all built-in languages:

```rust
pub fn build_registry() -> Result<LanguageRegistry> {
    let mut registry = LanguageRegistry::new();
    registry.register("rhocalc", Box::new(RhoCalcLanguage));
    registry.register("calculator", Box::new(CalculatorLanguage));
    registry.register("ambient", Box::new(AmbientLanguage));
    registry.register("lambda", Box::new(LambdaLanguage));
    Ok(registry)
}
```

To add a new language to the REPL, you'd add it here.

---

## 9.3 The State Machine

**File**: `repl/src/state.rs`

```rust
pub struct ReplState {
    language_name: Option<String>,               // Currently loaded language
    current_term: Option<Box<dyn Term>>,         // Active term being explored
    current_graph_id: Option<u64>,               // Term's ID in the rewrite graph
    history: Vec<HistoryEntry>,                  // Navigation history
    history_idx: usize,                          // Current position
    ascent_results: Option<AscentResults>,       // Latest execution results
    environment: Option<Box<dyn Any + Send + Sync>>, // Variable bindings
}
```

The state tracks:
- **Which language** is loaded (determines parsing, execution, display)
- **Current term** being explored (set by `exec`, `apply`, `goto`)
- **History** of terms visited (for `goto` navigation)
- **Ascent results** from the last execution (for `rewrites`, `apply`, `normal-forms`)
- **Environment** for variable bindings (populated by `assign` and pre-loaded examples)

---

## 9.4 The Command Loop

**File**: `repl/src/repl.rs`

The main loop:

```rust
pub fn run(&mut self) -> Result<()> {
    self.print_banner();
    loop {
        let prompt = self.make_prompt();  // "mettail>" or "RhoCalc>"
        match self.editor.readline(&prompt) {
            Ok(line) => {
                self.editor.add_history_entry(&line)?;
                let line = line.trim();
                if line.is_empty() { continue; }
                if let Err(e) = self.handle_command(line) {
                    eprintln!("Error: {}", e);
                }
            }
            Err(ReadlineError::Interrupted) => continue,  // Ctrl+C
            Err(ReadlineError::Eof) => break,              // Ctrl+D
            Err(e) => return Err(e.into()),
        }
    }
    Ok(())
}
```

`handle_command()` dispatches on the first word:

```rust
fn handle_command(&mut self, line: &str) -> Result<()> {
    let parts: Vec<&str> = line.splitn(2, ' ').collect();
    let cmd = parts[0];
    let args: Vec<&str> = parts.get(1).map(|s| s.split_whitespace().collect()).unwrap_or_default();

    match cmd {
        "help" | "h"       => self.cmd_help(),
        "lang" | "l"       => self.cmd_lang(&args),
        "languages"        => self.cmd_languages(),
        "exec" | "e"       => self.cmd_exec(parts.get(1).unwrap_or(&"")),
        "step" | "s"       => self.cmd_step(parts.get(1).unwrap_or(&"")),
        "rewrites" | "rw"  => self.cmd_rewrites(false),
        "rewrites-all"     => self.cmd_rewrites(true),
        "apply" | "a"      => self.cmd_apply(&args),
        "goto" | "g"       => self.cmd_goto(&args),
        "env"              => self.cmd_env(),
        "assign"           => self.cmd_assign(parts.get(1).unwrap_or(&"")),
        "typeof" | "t"     => self.cmd_typeof(parts.get(1).unwrap_or(&"")),
        "types"            => self.cmd_types(),
        "normal-forms" | "nf" => self.cmd_normal_forms(),
        "equations" | "eq" => self.cmd_equations(),
        "relations"        => self.cmd_relations(),
        "relation"         => self.cmd_relation(&args),
        "query" | "q"      => self.cmd_query(parts.get(1).unwrap_or(&"")),
        "example"          => self.cmd_example(&args),
        "list-examples"    => self.cmd_list_examples(),
        // ... more commands
        _ => Err(anyhow::anyhow!("Unknown command: {}", cmd)),
    }
}
```

---

## 9.5 Key Commands in Detail

### `exec` - Full Execution

```rust
fn cmd_exec(&mut self, input: &str) -> Result<()> {
    let language = self.get_language()?;

    // 1. Pre-substitute environment variables in the input string
    let substituted = pre_substitute_env(input, language, env);

    // 2. Parse the substituted string
    let term = language.parse_term(&substituted)?;

    // 3. Substitute environment (at the AST level) and normalize
    let term = language.substitute_env(term.as_ref(), env)?;

    // 4. Try direct eval first (fast path for pure native terms)
    if let Some(result) = language.try_direct_eval(term.as_ref()) {
        // Display result and return early
    }

    // 5. Run Ascent (full Datalog fixpoint computation)
    let results = language.run_ascent(term.as_ref())?;

    // 6. Update state and display
    self.state.set_results(term, results);
    self.display_exec_results();
}
```

### `step` - Single Step

Like `exec` but uses `substitute_env_preserve_structure` (no constant folding) so you can see one rewrite at a time.

### `rewrites` - Show Available Rewrites

```rust
fn cmd_rewrites(&self, show_all: bool) -> Result<()> {
    let results = self.state.ascent_results()?;
    let current_id = self.state.current_graph_id()?;

    let rewrites = results.rewrites_from(current_id);
    for (i, rw) in rewrites.iter().enumerate() {
        let target = results.all_terms.iter().find(|t| t.term_id == rw.to_id);
        println!("  {}) → {}", i, target.display);
    }
}
```

### `apply N` - Follow a Rewrite

```rust
fn cmd_apply(&mut self, args: &[&str]) -> Result<()> {
    let index: usize = args[0].parse()?;
    let rewrites = results.rewrites_from(current_id);
    let rewrite = rewrites.get(index)?;

    // Find the target term
    let target_id = rewrite.to_id;
    let target_info = results.all_terms.iter().find(|t| t.term_id == target_id)?;

    // Re-parse the target term to get a proper AST
    let new_term = language.parse_term(&target_info.display)?;

    // Run Ascent on the new term
    let new_results = language.run_ascent(new_term.as_ref())?;

    // Update state
    self.state.set_results(new_term, new_results);
    self.state.add_history(target_id, target_info.display.clone());
}
```

### `env` and `assign` - Environment Management

```rust
fn cmd_assign(&mut self, input: &str) -> Result<()> {
    // Parse "name = expression"
    let (name, expr) = input.split_once('=')?.trim();

    let language = self.get_language()?;
    let term = language.parse_term_for_env(expr)?;

    let env = self.state.environment_mut()?;
    language.add_to_env(env, name, term.as_ref())?;
}
```

Environment bindings are substituted into future `exec` calls before parsing.

---

## 9.6 The Examples System

**File**: `repl/src/examples/`

Each language can provide pre-defined examples that are loaded when the language is activated:

```rust
// repl/src/examples/rhocalc.rs
pub fn rhocalc_examples() -> Vec<ExampleCategory> {
    vec![
        ExampleCategory {
            name: "combinators",
            description: "Common process combinators",
            examples: vec![
                Example {
                    name: "dup",
                    definition: "^l.{l?x.{{l!(*(x)) | *(x)}}}",
                    description: "Duplicator",
                },
                Example {
                    name: "id",
                    definition: "^z.{*(z)}",
                    description: "Identity",
                },
                // ...
            ],
        },
    ]
}
```

These are automatically loaded into the environment when you `lang rhocalc`.

---

## 9.7 Pretty Printing

**File**: `repl/src/pretty.rs`

The REPL uses the `colored` crate for terminal output:
- Keywords in **blue**
- Errors in **red**
- Rewrites with arrow indicators
- Term IDs for navigation

The `format_term_pretty()` function handles indentation and line-wrapping for large terms.

---

## 9.8 How to Extend the REPL

### Adding a New Command

1. Add a match arm in `handle_command()`:
```rust
"mycommand" => self.cmd_mycommand(&args),
```

2. Implement the method:
```rust
fn cmd_mycommand(&self, args: &[&str]) -> Result<()> {
    // Access state via self.state
    // Access language via self.get_language()?
    println!("My command output");
    Ok(())
}
```

3. Add to help text.

### Adding a New Example

1. Open `repl/src/examples/rhocalc.rs` (or the appropriate language)
2. Add an `Example` to the relevant category
3. The example will be auto-loaded into the environment

### Adding a New Language

1. Define the language in `languages/src/my_language.rs` using `language! { ... }`
2. Add the crate module in `languages/src/lib.rs`
3. Register it in `repl/src/registry.rs`:
```rust
registry.register("mylang", Box::new(MyLanguageLanguage));
```
4. Optionally add examples in `repl/src/examples/`

---

## Exercises

### Exercise 1: Explore All Commands

In the REPL, try every command listed in `help`. For each one, understand what it does:

```
help, lang, languages, exec, step, rewrites, rewrites-all, apply,
goto, env, assign, typeof, types, normal-forms, equations,
relations, relation, query, example, list-examples, clear, save, load-env
```

### Exercise 2: Add a Command

Add a `count` command that prints the number of terms, rewrites, and normal forms in the current results:

```
RhoCalc> count
Terms: 42, Rewrites: 15, Normal forms: 8
```

Hint: access `self.state.ascent_results()` and use the `AscentResults` methods.

### Exercise 3: Add an Example

Add a new RhoCalc example combinator to `repl/src/examples/rhocalc.rs`. Some ideas:
- A "tee" combinator that sends a message to two channels
- A "filter" combinator that only forwards messages matching a condition

### Exercise 4: Read the State Machine

Read `repl/src/state.rs` and trace what happens to the state through a session:
1. Start: state is empty
2. `lang rhocalc`: what changes?
3. `exec { @(0)!({}) | @(0)?x.{*(x)} }`: what changes?
4. `apply 0`: what changes?
5. `goto 0`: what changes?

---

## Checkpoint

Before moving on, make sure you can:

1. **Trace** the flow from user input to displayed output through the REPL code
2. **Explain** what `ReplState` tracks and how each command modifies it
3. **Describe** how environment substitution works (pre-substitute in string, then AST-level)
4. **Add** a simple command to the REPL
5. **Navigate** the REPL codebase (`main.rs`, `repl.rs`, `state.rs`, `registry.rs`, `examples/`)

---

**Next**: [Module 10: Contributing](10-contributing.md) - Making your first change
