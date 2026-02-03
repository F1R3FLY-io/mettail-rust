use crate::examples::{Example, ExampleCategory};
use crate::pretty::format_term_pretty;
use crate::registry::LanguageRegistry;
use crate::state::ReplState;
use anyhow::Result;
use colored::Colorize;
use mettail_runtime::{AscentResults, TermInfo};
use rustyline::error::ReadlineError;
use rustyline::{DefaultEditor, Result as RustyResult};
use std::time::Instant;

/// The main REPL
pub struct Repl {
    state: ReplState,
    registry: LanguageRegistry,
    editor: DefaultEditor,
}

impl Repl {
    /// Create a new REPL
    pub fn new(registry: LanguageRegistry) -> RustyResult<Self> {
        let editor = DefaultEditor::new()?;
        Ok(Self {
            state: ReplState::new(),
            registry,
            editor,
        })
    }

    pub fn name_str(&self) -> Option<&str> {
        self.state.language_name()
    }

    /// Load a language by name (for programmatic use)
    pub fn load_language(&mut self, name: &str) -> Result<()> {
        self.cmd_lang(&[name])
    }

    /// Run the REPL
    pub fn run(&mut self) -> Result<()> {
        self.print_banner();

        loop {
            let prompt = self.make_prompt();
            match self.editor.readline(&prompt) {
                Ok(line) => {
                    self.editor.add_history_entry(&line)?;

                    let line = line.trim();
                    if line.is_empty() {
                        continue;
                    }

                    if let Err(e) = self.handle_command(line) {
                        eprintln!("{} {}", "Error:".red().bold(), e);
                    }
                },
                Err(ReadlineError::Interrupted) => {
                    println!("^C");
                    continue;
                },
                Err(ReadlineError::Eof) => {
                    println!("exit");
                    break;
                },
                Err(err) => {
                    eprintln!("{} {:?}", "Error:".red().bold(), err);
                    break;
                },
            }
        }

        Ok(())
    }

    fn print_banner(&self) {
        println!("{}", "╔════════════════════════════════════════════════════════════╗".cyan());
        println!("{}", "║                   MeTTaIL Term Explorer                    ║".cyan());
        println!("{}", "║                      Version 0.1.0                         ║".cyan());
        println!("{}", "╚════════════════════════════════════════════════════════════╝".cyan());
        println!();
        println!("Type {} for available commands.", "'help'".green());
        println!();
    }

    fn make_prompt(&self) -> String {
        if let Some(language_name) = self.state.language_name() {
            format!("{}> ", language_name.green())
        } else {
            "mettail> ".to_string()
        }
    }

    fn handle_command(&mut self, line: &str) -> Result<()> {
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.is_empty() {
            return Ok(());
        }

        // Check for assignment syntax: name = term
        if let Some((name, term_str)) = Self::parse_assignment(line) {
            return self.cmd_assign(&name, &term_str);
        }

        match parts[0] {
            "help" => self.cmd_help(),
            "lang" => self.cmd_lang(&parts[1..]),
            "load-env" => self.cmd_load_env(&parts[1..]),
            "languages" => self.cmd_list_languages(),
            "info" => self.cmd_info(),
            "env" => self.cmd_env(),
            "save" => self.cmd_save(&parts[1..]),
            "clear" => self.cmd_clear(&parts[1..]),
            "clear-all" => self.cmd_clear_all(),
            "term" => self.cmd_term(),
            "type" => self.cmd_type(),
            "typeof" => self.cmd_typeof(&parts[1..]),
            "types" => self.cmd_types(),
            "rewrites" => self.cmd_rewrites(),
            "rewrites-all" => self.cmd_rewrites_all(),
            "equations" => self.cmd_equations(),
            "normal-forms" => self.cmd_normal_forms(),
            "apply" => self.cmd_apply(&parts[1..]),
            "goto" => self.cmd_goto(&parts[1..]),
            "example" => self.cmd_example(&parts[1..]),
            "list-examples" => self.cmd_list_examples(self.state.language_name().unwrap()),
            "quit" | "exit" => {
                println!("Goodbye!");
                std::process::exit(0);
            },
            "exec" => self.cmd_exec_term(line.strip_prefix("exec").unwrap()),
            "step" => self.cmd_step_term(line.strip_prefix("step").unwrap()),
            _ => {
                anyhow::bail!(
                    "Unknown command: '{}'. Type 'help' for available commands.",
                    parts[0]
                )
            },
        }
    }

    /// Parse assignment syntax: name = term
    /// Returns (name, term_string) if it's an assignment, None otherwise
    fn parse_assignment(line: &str) -> Option<(String, String)> {
        // Look for = that's not inside parentheses or brackets
        let mut paren_depth = 0;
        let mut bracket_depth = 0;

        for (i, ch) in line.char_indices() {
            match ch {
                '(' | '{' => paren_depth += 1,
                ')' | '}' => paren_depth -= 1,
                '[' => bracket_depth += 1,
                ']' => bracket_depth -= 1,
                '=' if paren_depth == 0 && bracket_depth == 0 => {
                    let name = line[..i].trim();
                    let term_str = line[i + 1..].trim();

                    // Validate name is a valid identifier (alphanumeric + underscore, starts with letter)
                    if !name.is_empty()
                        && name
                            .chars()
                            .next()
                            .map(|c| c.is_alphabetic())
                            .unwrap_or(false)
                        && name.chars().all(|c| c.is_alphanumeric() || c == '_')
                        && !term_str.is_empty()
                    {
                        return Some((name.to_string(), term_str.to_string()));
                    }
                },
                _ => {},
            }
        }
        None
    }

    fn cmd_help(&self) -> Result<()> {
        println!();
        println!("{}", "Available commands:".bold());
        println!();
        println!("{}", "  Language Management:".yellow());
        println!("    {}        Show available languages", "languages".green());
        println!("    {}  Open language", "lang <name>".green());
        println!("    {}              Show language information", "{lang_name}> info".green());
        println!();
        println!("{}", "  Term Input:".yellow());
        println!(
            "    {}    Execute a program (direct evaluation → result)",
            "exec <term>".green()
        );
        println!(
            "    {}    Step-by-step: show initial term, use {} to reduce",
            "step <term>".green(),
            "apply 0".cyan()
        );
        println!("    {}    Load example program", "example <name>".green());
        println!("    {}    List available examples", "list-examples".green());
        println!();
        println!("{}", "  Environment:".yellow());
        println!("    {} Define a named term", "<name> = <term>".green());
        println!("    {}      Save current term to environment", "save <name>".green());
        println!("    {}               Show all environment bindings", "env".green());
        println!("    {}    Remove a binding", "clear <name>".green());
        println!("    {}         Clear all bindings", "clear-all".green());
        println!("    {} Load declarations from file", "load-env <file>".green());
        println!();
        println!("{}", "  Type Inspection:".yellow());
        println!("    {}              Show type of current term", "type".green());
        println!("    {}             Show all variable types", "types".green());
        println!("    {}  Show type of specific variable", "typeof <var>".green());
        println!();
        println!("{}", "  Navigation:".yellow());
        println!("    {}           List rewrites from current term", "rewrites".green());
        println!("    {}         List all rewrites", "rewrites-all".green());
        println!("    {}        Show normal forms", "normal-forms".green());
        println!(
            "    {} Apply one rewrite from current term (use after {})",
            "apply <N>".green(),
            "step".cyan()
        );
        println!("    {}              Go to normal form N", "goto <N>".green());
        println!();
        println!("{}", "  General:".yellow());
        println!("    {}              Show this help", "help".green());
        println!("    {}        Exit REPL", "quit, exit".green());
        println!();
        Ok(())
    }

    fn cmd_lang(&mut self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: lang <language-name>");
        }

        let language_name = args[0];

        if !self.registry.contains(language_name) {
            anyhow::bail!(
                "Language '{}' not found. Use 'list-languages' to see available languages.",
                language_name
            );
        }

        println!("Loading language: {}", language_name.green());

        // Get the theory from the registry (for display info)
        let language = self.registry.get(language_name)?;

        // Print theory info
        // println!("  ✓ {} categories", theory.categories().len());
        // println!("  ✓ {} constructors", theory.constructor_count());
        // println!("  ✓ {} equations", theory.equation_count());
        // println!("  ✓ {} rewrite rules", theory.rewrite_count());

        // Store the theory name in state
        self.state.load_language(language.name());

        // Try to auto-load environment from repl/src/examples/{theory_name}.txt
        let env_file = format!("repl/src/examples/{}.txt", language_name);
        if std::path::Path::new(&env_file).exists() {
            match self.load_env_from_file(&env_file) {
                Ok(count) if count > 0 => {
                    println!("  [{} definitions from {}]", count, env_file);
                },
                Ok(_) => {}, // Empty file, no message
                Err(e) => {
                    println!("  {} Failed to load {}: {}", "⚠".yellow(), env_file, e);
                },
            }
        }
        println!();

        println!("{} Language loaded successfully!", "✓".green());
        println!("  {}  direct evaluation (result)", "'exec <term>'".cyan());
        println!(
            "  {}  step-by-step, then {} to reduce",
            "'step <term>'".cyan(),
            "apply 0".cyan()
        );
        println!();

        Ok(())
    }

    fn cmd_list_languages(&self) -> Result<()> {
        println!();
        println!("{}", "Available languages:".bold());
        println!();

        let languages = self.registry.list();
        if languages.is_empty() {
            println!("  {}", "No languages available.".yellow());
            println!("  {}", "Build mettail-examples first with: cargo build".dimmed());
        } else {
            for language in languages {
                println!("  - {}", language.green());
            }
        }

        println!();
        Ok(())
    }

    fn cmd_info(&self) -> Result<()> {
        if let Some(language_name) = self.state.language_name() {
            let language = self.registry.get(language_name)?;
            let meta = language.metadata();

            println!();
            println!("{}", "═".repeat(70).cyan());
            println!("{:^70}", format!("{} Language", meta.name()).bold());
            println!("{}", "═".repeat(70).cyan());

            // Types
            println!();
            println!("{}", "TYPES".yellow().bold());
            for ty in meta.types() {
                let primary = if ty.is_primary { " (primary)" } else { "" };
                let native = ty
                    .native_type
                    .map(|t| format!(" = {}", t))
                    .unwrap_or_default();
                println!("  {}{}{}", ty.name.cyan(), native.dimmed(), primary.dimmed());
            }

            // Terms grouped by type - format: [Label] syntax:Type -| context
            println!();
            println!("{} ({})", "TERMS".yellow().bold(), meta.terms().len());
            for ty in meta.types() {
                let terms: Vec<_> = meta
                    .terms()
                    .iter()
                    .filter(|t| t.type_name == ty.name)
                    .collect();
                if !terms.is_empty() {
                    println!("  {}:", ty.name);
                    for term in terms {
                        let label = format!("[{}]", term.name).cyan();

                        // Build type context from fields
                        let ctx: Vec<String> = term
                            .fields
                            .iter()
                            .map(|f| format!("{}:{}", f.name, f.ty))
                            .collect();

                        let judgement = if ctx.is_empty() {
                            format!("{}:{}", term.syntax, term.type_name)
                        } else {
                            format!(
                                "{}:{} {} {}",
                                term.syntax,
                                term.type_name,
                                "-|".dimmed(),
                                ctx.join(", ")
                            )
                        };

                        println!("    {} {}", label, judgement.green());
                    }
                }
            }

            // Equations - format: [conditions] lhs = rhs
            println!();
            println!("{} ({})", "EQUATIONS".yellow().bold(), meta.equations().len());
            for eq in meta.equations() {
                let cond_str = if eq.conditions.is_empty() {
                    String::new()
                } else {
                    format!("{} {} ", eq.conditions.join(", "), "|-".dimmed())
                };
                println!("  {}{} = {}", cond_str, eq.lhs.green(), eq.rhs.green());
            }

            // Rewrites - format: [premise] lhs ~> rhs
            println!();
            println!("{} ({})", "REWRITES".yellow().bold(), meta.rewrites().len());
            for rw in meta.rewrites() {
                let mut parts = Vec::new();

                // Add freshness conditions
                if !rw.conditions.is_empty() {
                    parts.push(rw.conditions.join(", "));
                }

                // Add premise (congruence rule)
                if let Some((s, t)) = rw.premise {
                    parts.push(format!("{} ~> {}", s, t));
                }

                let prefix = if parts.is_empty() {
                    String::new()
                } else {
                    format!("{} {} ", parts.join(", "), "|-".dimmed())
                };

                // Add optional name
                let name_str = rw
                    .name
                    .map(|n| format!("[{}] ", n).cyan().to_string())
                    .unwrap_or_default();

                println!("  {}{}{} ~> {}", name_str, prefix, rw.lhs.green(), rw.rhs.green());
            }

            println!();
            println!("{}", "═".repeat(70).cyan());
            println!();
        } else {
            println!("{} No language loaded. Use 'lang <name>' first.", "Info:".yellow());
        }
        Ok(())
    }

    // === Environment Commands ===

    fn cmd_assign(&mut self, name: &str, term_str: &str) -> Result<()> {
        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded. Use 'lang <language>' first."))?;

        let language = self.registry.get(language_name)?;

        // Parse the term WITHOUT clearing var cache
        // This allows shared variables across env definitions (e.g., same `n` in multiple terms)
        let term = language
            .parse_term_for_env(term_str)
            .map_err(|e| anyhow::anyhow!("{}", e))?;

        // Ensure environment exists
        let env = self.state.ensure_environment(|| language.create_env());

        // Add to environment
        language
            .add_to_env(env, name, term.as_ref())
            .map_err(|e| anyhow::anyhow!("{}", e))?;

        println!("{} {} added to environment", "✓".green(), name.cyan());
        Ok(())
    }

    fn cmd_env(&self) -> Result<()> {
        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded. Use 'lang <language>' first."))?;

        let language = self.registry.get(language_name)?;

        println!();
        println!("{}", "Environment:".bold());

        if let Some(env) = self.state.environment() {
            if language.is_env_empty(env) {
                println!("  {}", "(empty)".dimmed());
            } else {
                let bindings = language.list_env(env);
                let mut last_comment: Option<&str> = None;

                for (name, value, comment) in &bindings {
                    // Print section comment if it's different from the last one
                    if let Some(c) = comment {
                        if last_comment != Some(c.as_str()) {
                            println!();
                            println!("  {}", format!("// {}", c).dimmed());
                            last_comment = Some(c.as_str());
                        }
                    } else if last_comment.is_some() {
                        // No comment on this item, reset section tracking
                        last_comment = None;
                    }
                    println!("  {} = {}", name.cyan(), value.green());
                }
            }
        } else {
            println!("  {}", "(empty)".dimmed());
        }

        println!();
        Ok(())
    }

    fn cmd_clear(&mut self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: clear <name>");
        }

        let name = args[0];

        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded."))?;

        let language = self.registry.get(language_name)?;

        if let Some(env) = self.state.environment_mut() {
            if language
                .remove_from_env(env, name)
                .map_err(|e| anyhow::anyhow!("{}", e))?
            {
                println!("{} {} removed from environment", "✓".green(), name.cyan());
            } else {
                println!("{} {} not found in environment", "⚠".yellow(), name);
            }
        } else {
            println!("{} Environment is empty", "⚠".yellow());
        }

        Ok(())
    }

    fn cmd_clear_all(&mut self) -> Result<()> {
        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded."))?;

        let language = self.registry.get(language_name)?;

        if let Some(env) = self.state.environment_mut() {
            language.clear_env(env);
            println!("{} Environment cleared", "✓".green());
        } else {
            println!("{} Environment is already empty", "⚠".yellow());
        }

        Ok(())
    }

    /// Save the current term to the environment with a given name
    fn cmd_save(&mut self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: save <name>");
        }

        let name = args[0];

        // Validate name is a valid identifier
        if !name
            .chars()
            .next()
            .map(|c| c.is_alphabetic())
            .unwrap_or(false)
            || !name.chars().all(|c| c.is_alphanumeric() || c == '_')
        {
            anyhow::bail!("Invalid identifier: '{}'", name);
        }

        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded."))?;

        // Clone the current term to release the borrow on self.state
        let current_term = self
            .state
            .current_term()
            .ok_or_else(|| anyhow::anyhow!("No current term. Use 'term: <expr>' first."))?
            .clone_box();

        let language = self.registry.get(language_name)?;

        // Ensure environment exists
        self.state.ensure_environment(|| language.create_env());

        // Add the current term to the environment
        if let Some(env) = self.state.environment_mut() {
            language
                .add_to_env(env, name, current_term.as_ref())
                .map_err(|e| anyhow::anyhow!("{}", e))?;
            println!("{} {} added to environment", "✓".green(), name.cyan());
        }

        Ok(())
    }

    /// Load term declarations from a file
    fn cmd_load_env(&mut self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: load-env <file>");
        }

        let file_path = args[0];

        match self.load_env_from_file(file_path) {
            Ok(count) => {
                if count > 0 {
                    println!(
                        "{} Loaded {} declaration(s) from '{}'",
                        "✓".green(),
                        count,
                        file_path
                    );
                } else {
                    println!("{} No declarations found in '{}'", "ℹ".blue(), file_path);
                }
                Ok(())
            },
            Err(e) => Err(e),
        }
    }

    /// Helper to load environment from a file, returns count of loaded declarations
    fn load_env_from_file(&mut self, file_path: &str) -> Result<usize> {
        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded. Use 'lang <language>' first."))?;

        let language = self.registry.get(language_name)?;

        // Ensure environment exists
        self.state.ensure_environment(|| language.create_env());

        // Read the file
        let content = std::fs::read_to_string(file_path)
            .map_err(|e| anyhow::anyhow!("Failed to read file '{}': {}", file_path, e))?;

        let mut count = 0;
        let mut errors = Vec::new();
        // Track the most recent comment block to associate with the next definition
        let mut pending_comment: Option<String> = None;

        for (line_num, line) in content.lines().enumerate() {
            let line = line.trim();

            // Handle empty lines - they break comment association
            if line.is_empty() {
                continue;
            }

            // Handle comments - collect them for the next definition
            if line.starts_with("//") {
                let comment_text = line.trim_start_matches("//").trim();
                pending_comment = Some(comment_text.to_string());
                continue;
            }
            if line.starts_with('#') {
                let comment_text = line.trim_start_matches('#').trim();
                pending_comment = Some(comment_text.to_string());
                continue;
            }

            // Try to parse as assignment
            if let Some((name, term_str)) = Self::parse_assignment(line) {
                // Parse the term (using parse_term_for_env to share variable IDs)
                match language.parse_term_for_env(&term_str) {
                    Ok(term) => {
                        if let Some(env) = self.state.environment_mut() {
                            if let Err(e) = language.add_to_env(env, &name, term.as_ref()) {
                                errors.push(format!("Line {}: {}", line_num + 1, e));
                            } else {
                                // Store the comment if there was one
                                if let Some(comment) = pending_comment.take() {
                                    let _ = language.set_env_comment(env, &name, comment);
                                }
                                count += 1;
                            }
                        }
                    },
                    Err(e) => {
                        errors.push(format!(
                            "Line {}: Failed to parse '{}': {}",
                            line_num + 1,
                            name,
                            e
                        ));
                    },
                }
            } else {
                errors.push(format!("Line {}: Invalid assignment syntax", line_num + 1));
            }

            // Clear pending comment after processing a definition (whether successful or not)
            pending_comment = None;
        }

        // Report errors if any
        if !errors.is_empty() {
            println!();
            println!("{}", "Errors:".red());
            for error in errors {
                println!("  {}", error);
            }
        }

        Ok(count)
    }

    fn cmd_term(&mut self) -> Result<()> {
        println!("{}", "Current term:".bold());
        if let Some(term) = self.state.current_term() {
            let formatted = format_term_pretty(&format!("{}", term));
            println!("{}", formatted.cyan());
        } else {
            println!("{}", "(none)".dimmed());
        }
        println!();
        Ok(())
    }

    // === Type Inspection Commands ===

    fn cmd_type(&self) -> Result<()> {
        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded. Use 'lang <language>' first."))?;

        let language = self.registry.get(language_name)?;

        println!();
        println!("{}", "Term type:".bold());

        if let Some(term) = self.state.current_term() {
            let term_type = language.infer_term_type(term);
            println!("  {}", format!("{}", term_type).cyan());
        } else {
            println!("  {}", "(no term loaded)".dimmed());
        }

        println!();
        Ok(())
    }

    fn cmd_typeof(&self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: typeof <variable-name>");
        }

        let var_name = args[0];

        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded. Use 'lang <language>' first."))?;

        let language = self.registry.get(language_name)?;

        println!();

        if let Some(term) = self.state.current_term() {
            if let Some(var_type) = language.infer_var_type(term, var_name) {
                println!("{} : {}", var_name.cyan(), format!("{}", var_type).green());
            } else {
                println!(
                    "{}",
                    format!("Variable '{}' not found in current term", var_name).yellow()
                );
            }
        } else {
            println!("{}", "(no term loaded)".dimmed());
        }

        println!();
        Ok(())
    }

    fn cmd_types(&self) -> Result<()> {
        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded. Use 'lang <language>' first."))?;

        let language = self.registry.get(language_name)?;

        println!();

        if let Some(term) = self.state.current_term() {
            // Get term type
            let term_type = language.infer_term_type(term);

            // Get all variable types
            let var_types = language.infer_var_types(term);

            if var_types.is_empty() {
                println!("{}", "Free variables:".bold());
                println!("  {}", "(none - all variables are bound)".dimmed());
            } else {
                println!("{}", "Free variables:".bold());
                for var_info in &var_types {
                    println!("  {} : {}", var_info.name.cyan(), format!("{}", var_info.ty).green());
                }
            }

            println!();
            println!("{}", "Term type:".bold());
            println!("  {}", format!("{}", term_type).cyan());
        } else {
            println!("{}", "(no term loaded)".dimmed());
        }

        println!();
        Ok(())
    }

    fn cmd_exec_term(&mut self, term_str: &str) -> Result<()> {
        // Get the loaded theory name
        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded. Use 'lang <language>' first."))?;

        // Get the theory from the registry
        let language = self.registry.get(language_name)?;

        println!();
        print!("Parsing... ");

        // Parse the term using parse_term_for_env to share FreeVar IDs with environment
        // This ensures that variables like `a` in the input match `a` from substituted env terms
        let term = language
            .parse_term_for_env(term_str)
            .map_err(|e| anyhow::anyhow!("{}", e))?;
        println!("{}", "✓".green());

        // Apply environment substitution if environment exists and is not empty
        let term = if let Some(env) = self.state.environment() {
            if !language.is_env_empty(env) {
                print!("Substituting environment... ");
                let substituted = language
                    .substitute_env(term.as_ref(), env)
                    .map_err(|e| anyhow::anyhow!("{}", e))?;
                println!("{}", "✓".green());

                substituted
            } else {
                term
            }
        } else {
            term
        };

        // Direct eval path: if term is fully evaluable, bypass Ascent
        if let Some(result_term) = language.try_direct_eval(term.as_ref()) {
            let result_id = result_term.term_id();
            let results = AscentResults::from_single_term(result_term.as_ref());
            println!();
            println!("{}", "Current term (result):".bold());
            let formatted = format_term_pretty(&format!("{}", result_term));
            println!("{}", formatted.cyan());
            println!();
            self.state.set_term_with_id(result_term, results, result_id)?;
            return Ok(());
        }

        print!("Running Ascent... ");

        let start_time = Instant::now();
        // Run Ascent
        let results = language
            .run_ascent(term.as_ref())
            .map_err(|e| anyhow::anyhow!("{}", e))?;
        let end_time = Instant::now();
        let duration = end_time.duration_since(start_time);
        println!("Time taken: {:?}", duration);
        println!("{}", "Done!".green());

        println!();
        println!("Computed:");
        println!("  - {} terms", results.all_terms.len());
        println!("  - {} rewrites", results.rewrites.len());
        println!("  - {} normal forms", results.normal_forms().len());
        println!();

        // After exec, show the result: a normal form reachable from the initial term
        let initial_id = term.term_id();
        if let Some(nf) = results.normal_form_reachable_from(initial_id) {
            let result_term = language
                .parse_term(&nf.display)
                .map_err(|e| anyhow::anyhow!("{}", e))?;
            println!("{}", "Current term (result):".bold());
            let formatted = format_term_pretty(&nf.display);
            println!("{}", formatted.cyan());
            println!();
            self.state
                .set_term_with_id(result_term, results.clone(), nf.term_id)?;
            return Ok(());
        }

        // No reachable normal form (e.g. initial term not in graph): show initial term
        println!("{}", "Current term:".bold());
        let formatted = format_term_pretty(&format!("{}", term));
        println!("{}", formatted.cyan());
        println!();
        self.state.set_term(term, results)?;

        Ok(())
    }

    /// Step-by-step execution: run Ascent but leave current term at the initial term
    /// so the user can type `apply 0` to apply one rewrite at a time.
    fn cmd_step_term(&mut self, term_str: &str) -> Result<()> {
        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded. Use 'lang <language>' first."))?;

        let language = self.registry.get(language_name)?;

        println!();
        print!("Parsing... ");

        let term = language
            .parse_term_for_env(term_str)
            .map_err(|e| anyhow::anyhow!("{}", e))?;
        println!("{}", "✓".green());

        let term = if let Some(env) = self.state.environment() {
            if !language.is_env_empty(env) {
                print!("Substituting environment... ");
                let substituted = language
                    .substitute_env(term.as_ref(), env)
                    .map_err(|e| anyhow::anyhow!("{}", e))?;
                println!("{}", "✓".green());
                substituted
            } else {
                term
            }
        } else {
            term
        };

        print!("Running Ascent... ");
        let start_time = Instant::now();
        let results = language
            .run_ascent(term.as_ref())
            .map_err(|e| anyhow::anyhow!("{}", e))?;
        let end_time = Instant::now();
        println!("Time taken: {:?}", end_time.duration_since(start_time));
        println!("{}", "Done!".green());

        println!();
        println!("Computed:");
        println!("  - {} terms", results.all_terms.len());
        println!("  - {} rewrites", results.rewrites.len());
        println!("  - {} normal forms", results.normal_forms().len());
        println!();

        // Always show initial term so user can apply rewrites one by one
        let initial_id = term.term_id();
        let available = results.rewrites_from(initial_id).len();

        println!("{}", "Current term (initial):".bold());
        let formatted = format_term_pretty(&format!("{}", term));
        println!("{}", formatted.cyan());
        println!();
        self.state.set_term_with_id(term, results, initial_id)?;

        if available > 0 {
            println!("  Use {} to apply a rewrite ({} available).", "apply 0".cyan(), available);
        } else {
            println!("  No rewrites from this term (already a normal form).");
        }
        println!();

        Ok(())
    }

    fn get_results(&self) -> Result<&AscentResults> {
        self.state
            .ascent_results()
            .ok_or_else(|| anyhow::anyhow!("No term loaded. Use 'term: <expr>' first."))
    }

    fn cmd_equations(&self) -> Result<()> {
        let results = self.get_results()?;

        let equivalences = results.equivalences.clone();
        println!();
        println!("{}", "Equivalence Classes:".bold());
        for equ_class in equivalences {
            let terms = equ_class
                .term_ids
                .iter()
                .map(|id| {
                    results
                        .all_terms
                        .iter()
                        .find(|t| t.term_id == *id)
                        .unwrap()
                        .display
                        .as_str()
                })
                .collect::<Vec<_>>();
            println!("  {}", terms.join(" == "));
        }
        println!();
        Ok(())
    }

    fn cmd_rewrites_all(&self) -> Result<()> {
        let results = self.get_results()?;

        let rewrites = results.rewrites.clone();
        println!();
        println!("{}", "Rewrites:".bold());
        for rewrite in rewrites {
            let from_info = self.term_by_id(rewrite.from_id)?;
            let to_info = self.term_by_id(rewrite.to_id)?;
            println!("  {} → {}", from_info.display, to_info.display);
        }
        println!();
        Ok(())
    }

    fn cmd_rewrites(&self) -> Result<()> {
        let results = self.get_results()?;

        let current_id = self
            .state
            .current_graph_id()
            .ok_or_else(|| anyhow::anyhow!("No current term"))?;

        // Find rewrites from the current term
        let available_rewrites: Vec<_> = results
            .rewrites
            .iter()
            .filter(|r| r.from_id == current_id)
            .collect();

        println!();
        if available_rewrites.is_empty() {
            println!(
                "{} No rewrites available from current term (it's a normal form).",
                "✓".green()
            );
        } else {
            println!("{} available from current term:", "Rewrites".bold());
            println!();
            for (idx, rewrite) in available_rewrites.iter().enumerate() {
                // Find the target term display
                let target_info = self.term_by_id(rewrite.to_id)?;
                let target_display = target_info.display.as_str();

                // Pretty print the target
                let formatted = format_term_pretty(target_display);

                println!("  {}) {}", idx.to_string().cyan(), "→".yellow());
                // Indent each line of the formatted output
                for line in formatted.lines() {
                    println!("     {}", line.green());
                }
                println!();
            }
        }
        println!();
        Ok(())
    }

    fn term_by_id(&self, id: u64) -> Result<&TermInfo> {
        let results = self.get_results()?;
        results
            .all_terms
            .iter()
            .find(|t| t.term_id == id)
            .ok_or_else(|| anyhow::anyhow!("Term not found"))
    }

    fn cmd_normal_forms(&self) -> Result<()> {
        let results = self.get_results()?;

        let normal_forms = results.normal_forms();

        println!();
        if normal_forms.is_empty() {
            println!("{} No normal forms computed.", "Warning:".yellow());
        } else {
            println!("{} ({} total):", "Normal forms".bold(), normal_forms.len());
            println!();
            for (idx, nf) in normal_forms.iter().enumerate() {
                let formatted = format_term_pretty(&nf.display);
                println!("  {})", idx.to_string().cyan());
                for line in formatted.lines() {
                    println!("    {}", line.green());
                }
                println!();
            }
        }
        println!();
        Ok(())
    }

    fn cmd_apply(&mut self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: apply <rewrite-number>");
        }

        let idx: usize = args[0]
            .parse()
            .map_err(|_| anyhow::anyhow!("Invalid number: {}", args[0]))?;

        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded"))?;

        let language = self.registry.get(language_name)?;

        let results = self.get_results()?;

        let current_id = self
            .state
            .current_graph_id()
            .ok_or_else(|| anyhow::anyhow!("No current term"))?;

        // Find available rewrites
        let available_rewrites: Vec<_> = results
            .rewrites
            .iter()
            .filter(|r| r.from_id == current_id)
            .collect();

        if idx >= available_rewrites.len() {
            anyhow::bail!("Rewrite {} not found. Use 'rewrites' to see available rewrites.", idx);
        }

        let rewrite = available_rewrites[idx];

        // Find the target term
        let target_info = results
            .all_terms
            .iter()
            .find(|t| t.term_id == rewrite.to_id)
            .ok_or_else(|| anyhow::anyhow!("Target term not found"))?;

        // Parse the target term and update its ID to match what's in the graph
        let target_term = language
            .parse_term(&target_info.display)
            .map_err(|e| anyhow::anyhow!("{}", e))?;

        println!();
        println!("{}", "Applied rewrite →".yellow());
        let formatted = format_term_pretty(&target_info.display);
        for line in formatted.lines() {
            println!("  {}", line.green());
        }
        println!();

        // Update state - pass the target_id so we can track position in the graph
        self.state
            .set_term_with_id(target_term, results.clone(), rewrite.to_id)?;

        Ok(())
    }

    fn cmd_goto(&mut self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: goto <normal-form-number>");
        }

        let idx: usize = args[0]
            .parse()
            .map_err(|_| anyhow::anyhow!("Invalid number: {}", args[0]))?;

        let language_name = self
            .state
            .language_name()
            .ok_or_else(|| anyhow::anyhow!("No language loaded"))?;

        let language = self.registry.get(language_name)?;

        let results = self.get_results()?;

        let normal_forms = results.normal_forms();

        if idx >= normal_forms.len() {
            anyhow::bail!(
                "Normal form {} not found. Use 'normal-forms' to see available normal forms.",
                idx
            );
        }

        let target_info = &normal_forms[idx];

        // Parse the target term
        let target_term = language
            .parse_term(&target_info.display)
            .map_err(|e| anyhow::anyhow!("{}", e))?;

        println!();
        println!("{}", "Navigated to normal form:".bold());
        let formatted = format_term_pretty(&target_info.display);
        for line in formatted.lines() {
            println!("  {}", line.green());
        }
        println!();

        // Update state with the correct graph ID
        self.state
            .set_term_with_id(target_term, results.clone(), target_info.term_id)?;

        Ok(())
    }

    fn cmd_example(&mut self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: example <name>\nUse 'list-examples' to see available examples.");
        }

        let example_name = args[0];

        let example = Example::by_name(example_name).ok_or_else(|| {
            anyhow::anyhow!(
                "Example '{}' not found. Use 'list-examples' to see available examples.",
                example_name
            )
        })?;

        println!();
        println!("{} {}", "Example:".bold(), example.name.cyan());
        println!("{} {}", "Description:".bold(), example.description);
        println!();

        // Parse and load the example
        self.cmd_exec_term(example.source)?;

        Ok(())
    }

    fn cmd_list_examples(&self, language_name: &str) -> Result<()> {
        println!();
        println!("{}", "Available Examples:".bold());
        println!();

        // Group by category
        for &category in &[
            ExampleCategory::Simple,
            ExampleCategory::Branching,
            ExampleCategory::Complex,
            ExampleCategory::Parallel,
            ExampleCategory::Advanced,
            ExampleCategory::Performance,
            ExampleCategory::EdgeCase,
            ExampleCategory::MultiComm,
            ExampleCategory::Mobility,
            ExampleCategory::Security,
        ] {
            let examples = Example::by_language_name_and_category(language_name, category);
            if !examples.is_empty() {
                println!("{}", format!("  {:?}:", category).yellow());
                for ex in examples {
                    println!("    {} - {}", ex.name.cyan(), ex.description.dimmed());
                }
                println!();
            }
        }

        println!("Use {} to load an example.", "example <name>".green());
        println!();

        Ok(())
    }
}
