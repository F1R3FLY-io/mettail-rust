use crate::examples::{Example, ExampleCategory, TheoryName};
use crate::pretty::format_term_pretty;
use crate::registry::TheoryRegistry;
use crate::state::ReplState;
use crate::theory::{AscentResults, TermInfo};
use anyhow::Result;
use colored::Colorize;
use rustyline::error::ReadlineError;
use rustyline::{DefaultEditor, Result as RustyResult};
use std::time::Instant;

/// The main REPL
pub struct Repl {
    state: ReplState,
    registry: TheoryRegistry,
    editor: DefaultEditor,
}

impl Repl {
    /// Create a new REPL
    pub fn new(registry: TheoryRegistry) -> RustyResult<Self> {
        let editor = DefaultEditor::new()?;
        Ok(Self {
            state: ReplState::new(),
            registry,
            editor,
        })
    }

    pub fn name_str(&self) -> Option<&str> {
        self.state.theory_name().map(|name| name.as_str())
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
        if let Some(theory_name) = self.state.theory_name() {
            format!("{}> ", theory_name.as_str().green())
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
            "load" => self.cmd_load(&parts[1..]),
            "load-env" => self.cmd_load_env(&parts[1..]),
            "list" | "list-theories" => self.cmd_list_theories(),
            "info" => self.cmd_info(),
            "env" => self.cmd_env(),
            "save" => self.cmd_save(&parts[1..]),
            "clear" => self.cmd_clear(&parts[1..]),
            "clear-all" => self.cmd_clear_all(),
            "rewrites" => self.cmd_rewrites(),
            "rewrites-all" => self.cmd_rewrites_all(),
            "equations" => self.cmd_equations(),
            "normal-forms" | "nf" => self.cmd_normal_forms(),
            "apply" => self.cmd_apply(&parts[1..]),
            "goto" => self.cmd_goto(&parts[1..]),
            "example" => self.cmd_example(&parts[1..]),
            "list-examples" => self.cmd_list_examples(&self.state.theory_name().unwrap()),
            "quit" | "exit" => {
                println!("Goodbye!");
                std::process::exit(0);
            },
            "exec" => self.cmd_parse_term(line.strip_prefix("exec").unwrap()),
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
                        && name.chars().next().map(|c| c.is_alphabetic()).unwrap_or(false)
                        && name.chars().all(|c| c.is_alphanumeric() || c == '_')
                        && !term_str.is_empty()
                    {
                        return Some((name.to_string(), term_str.to_string()));
                    }
                }
                _ => {}
            }
        }
        None
    }

    fn cmd_help(&self) -> Result<()> {
        println!();
        println!("{}", "Available commands:".bold());
        println!();
        println!("{}", "  Theory Management:".yellow());
        println!("    {}  Load a theory", "load <name>".green());
        println!("    {}        Show available theories", "list-theories".green());
        println!("    {}              Show theory information", "info".green());
        println!();
        println!("{}", "  Term Input:".yellow());
        println!("    {}    Execute a program", "exec <term>".green());
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
        println!("{}", "  Navigation:".yellow());
        println!("    {}           List rewrites from current term", "rewrites".green());
        println!("    {}         List all rewrites", "rewrites-all".green());
        println!("    {}        Show normal forms", "normal-forms".green());
        println!("    {} Apply rewrite N", "apply <N>".green());
        println!("    {}              Go to normal form N", "goto <N>".green());
        println!();
        println!("{}", "  General:".yellow());
        println!("    {}              Show this help", "help".green());
        println!("    {}        Exit REPL", "quit, exit".green());
        println!();
        Ok(())
    }

    fn cmd_load(&mut self, args: &[&str]) -> Result<()> {
        if args.is_empty() {
            anyhow::bail!("Usage: load <theory-name>");
        }

        let theory_name = args[0];

        if !self.registry.contains(theory_name) {
            anyhow::bail!(
                "Theory '{}' not found. Use 'list-theories' to see available theories.",
                theory_name
            );
        }

        println!("Loading theory: {}", theory_name.green());

        // Get the theory from the registry (for display info)
        let theory = self.registry.get(theory_name)?;

        // Print theory info
        println!("  ✓ {} categories", theory.categories().len());
        println!("  ✓ {} constructors", theory.constructor_count());
        println!("  ✓ {} equations", theory.equation_count());
        println!("  ✓ {} rewrite rules", theory.rewrite_count());
        println!();

        // Store the theory name in state
        self.state.load_theory(theory.name());

        println!("{} Theory loaded successfully!", "✓".green());
        println!("Use {} to execute a program.", "'exec <term>'".cyan());
        println!();

        Ok(())
    }

    fn cmd_list_theories(&self) -> Result<()> {
        println!();
        println!("{}", "Available theories:".bold());
        println!();

        let theories = self.registry.list();
        if theories.is_empty() {
            println!("  {}", "No theories available.".yellow());
            println!("  {}", "Build mettail-examples first with: cargo build".dimmed());
        } else {
            for theory in theories {
                println!("  - {}", theory.green());
            }
        }

        println!();
        Ok(())
    }

    fn cmd_info(&self) -> Result<()> {
        if let Some(theory_name) = self.state.theory_name() {
            let theory = self.registry.get(theory_name.as_str())?;
            println!();
            println!("{} {}", "Theory:".bold(), theory.name().as_str().green());
            println!("  Categories: {}", theory.categories().len());
            println!("  Constructors: {}", theory.constructor_count());
            println!("  Equations: {}", theory.equation_count());
            println!("  Rewrites: {}", theory.rewrite_count());
            println!();
        } else {
            println!("{} No theory loaded. Use 'load <name>' first.", "Info:".yellow());
        }
        Ok(())
    }
    
    // === Environment Commands ===
    
    fn cmd_assign(&mut self, name: &str, term_str: &str) -> Result<()> {
        let theory_name = self
            .state
            .theory_name()
            .ok_or_else(|| anyhow::anyhow!("No theory loaded. Use 'load <theory>' first."))?;
        
        let theory = self.registry.get(theory_name.as_str())?;
        
        // Parse the term WITHOUT clearing var cache
        // This allows shared variables across env definitions (e.g., same `n` in multiple terms)
        let term = theory.parse_term_for_env(term_str)?;
        
        // Ensure environment exists
        let env = self.state.ensure_environment(|| theory.create_env());
        
        // Add to environment
        theory.add_to_env(env, name, term.as_ref())?;
        
        println!("{} {} added to environment", "✓".green(), name.cyan());
        Ok(())
    }
    
    fn cmd_env(&self) -> Result<()> {
        let theory_name = self
            .state
            .theory_name()
            .ok_or_else(|| anyhow::anyhow!("No theory loaded. Use 'load <theory>' first."))?;
        
        let theory = self.registry.get(theory_name.as_str())?;
        
        println!();
        println!("{}", "Environment:".bold());
        
        if let Some(env) = self.state.environment() {
            if theory.is_env_empty(env) {
                println!("  {}", "(empty)".dimmed());
            } else {
                let bindings = theory.list_env(env);
                for (name, value) in bindings {
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
        
        let theory_name = self
            .state
            .theory_name()
            .ok_or_else(|| anyhow::anyhow!("No theory loaded."))?;
        
        let theory = self.registry.get(theory_name.as_str())?;
        
        if let Some(env) = self.state.environment_mut() {
            if theory.remove_from_env(env, name)? {
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
        let theory_name = self
            .state
            .theory_name()
            .ok_or_else(|| anyhow::anyhow!("No theory loaded."))?;
        
        let theory = self.registry.get(theory_name.as_str())?;
        
        if let Some(env) = self.state.environment_mut() {
            theory.clear_env(env);
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
        if !name.chars().next().map(|c| c.is_alphabetic()).unwrap_or(false)
            || !name.chars().all(|c| c.is_alphanumeric() || c == '_')
        {
            anyhow::bail!("Invalid identifier: '{}'", name);
        }
        
        let theory_name = self
            .state
            .theory_name()
            .ok_or_else(|| anyhow::anyhow!("No theory loaded."))?;
        
        // Clone the current term to release the borrow on self.state
        let current_term = self
            .state
            .current_term()
            .ok_or_else(|| anyhow::anyhow!("No current term. Use 'term: <expr>' first."))?
            .clone_box();
        
        let theory = self.registry.get(theory_name.as_str())?;
        
        // Ensure environment exists
        self.state.ensure_environment(|| theory.create_env());
        
        // Add the current term to the environment
        if let Some(env) = self.state.environment_mut() {
            theory.add_to_env(env, name, current_term.as_ref())?;
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
        
        let theory_name = self
            .state
            .theory_name()
            .ok_or_else(|| anyhow::anyhow!("No theory loaded. Use 'load <theory>' first."))?;
        
        let theory = self.registry.get(theory_name.as_str())?;
        
        // Ensure environment exists
        self.state.ensure_environment(|| theory.create_env());
        
        // Read the file
        let content = std::fs::read_to_string(file_path)
            .map_err(|e| anyhow::anyhow!("Failed to read file '{}': {}", file_path, e))?;
        
        let mut count = 0;
        let mut errors = Vec::new();
        
        for (line_num, line) in content.lines().enumerate() {
            let line = line.trim();
            
            // Skip empty lines and comments
            if line.is_empty() || line.starts_with("//") || line.starts_with('#') {
                continue;
            }
            
            // Try to parse as assignment
            if let Some((name, term_str)) = Self::parse_assignment(line) {
                // Parse the term (using parse_term_for_env to share variable IDs)
                match theory.parse_term_for_env(&term_str) {
                    Ok(term) => {
                        if let Some(env) = self.state.environment_mut() {
                            if let Err(e) = theory.add_to_env(env, &name, term.as_ref()) {
                                errors.push(format!("Line {}: {}", line_num + 1, e));
                            } else {
                                count += 1;
                            }
                        }
                    }
                    Err(e) => {
                        errors.push(format!("Line {}: Failed to parse '{}': {}", line_num + 1, name, e));
                    }
                }
            } else {
                errors.push(format!("Line {}: Invalid assignment syntax", line_num + 1));
            }
        }
        
        // Report results
        if count > 0 {
            println!("{} Loaded {} declaration(s) from '{}'", "✓".green(), count, file_path);
        }
        
        if !errors.is_empty() {
            println!();
            println!("{}", "Errors:".red());
            for error in errors {
                println!("  {}", error);
            }
        }
        
        Ok(())
    }

    fn cmd_parse_term(&mut self, term_str: &str) -> Result<()> {
        // Get the loaded theory name
        let theory_name = self
            .state
            .theory_name()
            .ok_or_else(|| anyhow::anyhow!("No theory loaded. Use 'load <theory>' first."))?;

        // Get the theory from the registry
        let theory = self.registry.get(theory_name.as_str())?;

        println!();
        print!("Parsing... ");

        // Parse the term using parse_term_for_env to share FreeVar IDs with environment
        // This ensures that variables like `a` in the input match `a` from substituted env terms
        let term = theory.parse_term_for_env(term_str)?;
        println!("{}", "✓".green());
        
        println!("{}", "Current term:".bold());
        // Apply environment substitution if environment exists and is not empty
        let term = if let Some(env) = self.state.environment() {
            if !theory.is_env_empty(env) {
                print!("Substituting environment... ");
                let substituted = theory.substitute_env(term.as_ref(), env)?;
                println!("{}", "✓".green());
                
                // Show substituted term if different
                let orig_str = format!("{}", term);
                let subst_str = format!("{}", substituted);
                if orig_str != subst_str {
                    println!("{}", "Substituted:".bold());
                    let formatted = format_term_pretty(&subst_str);
                    println!("{}", formatted.cyan());
                    println!();
                }
                
                substituted
            } else {
                term
            }
        } else {
            term
        };

        print!("Running Ascent... ");

        let start_time = Instant::now();
        // Run Ascent
        let results = theory.run_ascent(term.clone_box())?;
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

        println!("{}", "Current term:".bold());
        let formatted = format_term_pretty(&format!("{}", term));
        println!("{}", formatted.cyan());
        println!();

        // Store in state
        self.state.set_term(term, results)?;

        Ok(())
    }

    fn get_results(&self) -> Result<&AscentResults> {
        self.state.ascent_results().ok_or_else(|| anyhow::anyhow!("No term loaded. Use 'term: <expr>' first."))
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
        results.all_terms
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

        let theory_name = self
            .state
            .theory_name()
            .ok_or_else(|| anyhow::anyhow!("No theory loaded"))?;

        let theory = self.registry.get(theory_name.as_str())?;

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
        let target_term = theory.parse_term(&target_info.display)?;

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

        let theory_name = self
            .state
            .theory_name()
            .ok_or_else(|| anyhow::anyhow!("No theory loaded"))?;

        let theory = self.registry.get(theory_name.as_str())?;

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
        let target_term = theory.parse_term(&target_info.display)?;

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
        self.cmd_parse_term(example.source)?;

        Ok(())
    }

    fn cmd_list_examples(&self, theory_name: &TheoryName) -> Result<()> {
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
            let examples = Example::by_theory_and_category(*theory_name, category);
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
