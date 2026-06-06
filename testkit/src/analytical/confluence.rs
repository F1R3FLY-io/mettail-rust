//! Confluence analysis integration for generated language tests.
//!
//! Wraps `mettail_prattail::confluence::check_confluence()` and provides
//! a higher-level interface that works with `LanguageMetadata` rather than
//! raw `RewriteRule` vectors.

use mettail_prattail::confluence::{self, ConfluenceAnalysis, RewriteRule, Term};
use mettail_runtime::LanguageMetadata;

/// Result of confluence checking on a language.
#[derive(Debug)]
pub struct ConfluenceResult {
    /// Whether the TRS is confluent (all critical pairs joinable).
    pub is_confluent: bool,
    /// Number of critical pairs found.
    pub critical_pair_count: usize,
    /// Number of non-joinable critical pairs.
    pub non_joinable_count: usize,
    /// Human-readable summary.
    pub summary: String,
}

/// Check confluence of a language's rewrite rules.
///
/// Converts the language's rewrite metadata into `RewriteRule` format
/// understood by the prattail confluence checker, then runs the analysis.
///
/// # Arguments
/// * `metadata` -- static language metadata providing rewrite rule definitions
///
/// # Returns
/// A `ConfluenceResult` summarizing whether the TRS is confluent.
pub fn check_language_confluence(metadata: &dyn LanguageMetadata) -> ConfluenceResult {
    let rewrites = metadata.rewrites();

    if rewrites.is_empty() {
        return ConfluenceResult {
            is_confluent: true,
            critical_pair_count: 0,
            non_joinable_count: 0,
            summary: format!("{}: no rewrite rules, trivially confluent", metadata.name()),
        };
    }

    // Convert metadata rewrites to prattail RewriteRule format.
    // The metadata stores LHS/RHS as user-syntax strings (e.g., "(Add X Y)").
    // We parse these into the prattail Term representation for analysis.
    let rules: Vec<RewriteRule> = rewrites
        .iter()
        .filter(|rw| rw.is_base()) // Skip congruence rules for critical pair analysis
        .filter_map(|rw| {
            let lhs = parse_pattern_to_term(rw.lhs)?;
            let rhs = parse_pattern_to_term(rw.rhs)?;
            if let Some(name) = rw.name {
                Some(RewriteRule::labeled(name, lhs, rhs))
            } else {
                Some(RewriteRule::new(lhs, rhs))
            }
        })
        .collect();

    if rules.is_empty() {
        return ConfluenceResult {
            is_confluent: true,
            critical_pair_count: 0,
            non_joinable_count: 0,
            summary: format!(
                "{}: no base rewrite rules (only congruence), trivially confluent",
                metadata.name()
            ),
        };
    }

    // Run the confluence analysis with a reasonable step limit
    let analysis: ConfluenceAnalysis = confluence::check_confluence(&rules, 100);

    ConfluenceResult {
        is_confluent: analysis.is_confluent,
        critical_pair_count: analysis.critical_pairs.len(),
        non_joinable_count: analysis.non_joinable_count,
        summary: format!(
            "{}: {} (critical pairs: {}, non-joinable: {})",
            metadata.name(),
            if analysis.is_confluent {
                "confluent"
            } else {
                "NOT confluent"
            },
            analysis.critical_pairs.len(),
            analysis.non_joinable_count,
        ),
    }
}

/// Parse a user-syntax pattern string into a prattail `Term`.
///
/// Handles simple pattern syntax like `(Add X Y)`, `(PPar {S, ...rest})`,
/// `X`, `42`, etc. Variables are single uppercase letters or capitalized names.
/// Function applications are `(Label args...)`.
///
/// Returns `None` if the pattern is too complex to parse (e.g., meta-operations
/// like `eval`, `*zip`, `*map`).
fn parse_pattern_to_term(pattern: &str) -> Option<Term> {
    let trimmed = pattern.trim();

    if trimmed.is_empty() {
        return None;
    }

    // Skip patterns with meta-operations that cannot be represented as TRS terms
    if trimmed.contains("eval ")
        || trimmed.contains("*zip")
        || trimmed.contains("*map")
        || trimmed.contains("...rest")
        || trimmed.contains("...")
    // collection rest patterns
    {
        return None;
    }

    // Simple variable: single uppercase letter or capitalized identifier
    if trimmed.len() <= 2
        && trimmed
            .chars()
            .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit())
    {
        return Some(Term::var(trimmed));
    }

    // Single ASCII letter (any case) is ALWAYS a metavariable, never a
    // nullary constructor. MeTTaIL's universal convention: bound rule
    // metavariables are single letters (`S`, `T`, `X`, `v`, `x`, `y`, `n`,
    // `p`, `q`, ...). No language uses a single lowercase letter as a
    // nullary constructor (those are multi-letter keywords like `new`,
    // `nil`, or quoted terminals like `cast_error_int`), and no single
    // lowercase letter is ever a function/App head in any rewrite pattern.
    //
    // This is the fix for the rhocalc/ledtest termination false-negative:
    // the auto-injected `NormCast<Src>To<Tgt>In<Cat>` rules render to user
    // syntax `v ~> v` (the cast wrappers are invisible transparent
    // projections). Pre-fix, the bare-identifier heuristic below classified
    // lowercase `v` as a nullary constant `App{v,[]}`, turning a reflexive
    // identity `Var(v) → Var(v)` into a self-looping defined-symbol DP
    // `⟨v#(), v#()⟩` with zero arity → flagged "no decreasing ordering" →
    // spurious PotentiallyNonTerminating. As a variable, `Var(v) → Var(v)`
    // yields NO dependency pairs (extract_dependency_pairs skips Var LHS),
    // which is the correct verdict: an identity rewrite is terminating.
    if trimmed.len() == 1 && trimmed.chars().all(|c| c.is_ascii_alphabetic()) {
        return Some(Term::var(trimmed));
    }

    // Parenthesized application: (Label arg1 arg2 ...)
    if trimmed.starts_with('(') && trimmed.ends_with(')') {
        let inner = &trimmed[1..trimmed.len() - 1].trim();
        let tokens = tokenize_pattern(inner);
        if tokens.is_empty() {
            return None;
        }

        let symbol = tokens[0].clone();
        let args: Vec<Term> = tokens[1..]
            .iter()
            .filter_map(|t| parse_pattern_to_term(t))
            .collect();

        // If we couldn't parse all args, bail out
        if args.len() != tokens.len() - 1 {
            return None;
        }

        return Some(Term::App { symbol, args });
    }

    // Bare identifier -- either a variable or a nullary constructor
    if trimmed.chars().all(|c| c.is_alphanumeric() || c == '_') {
        // Heuristic: all-uppercase or single letter = variable; otherwise = constant
        if trimmed.chars().all(|c| c.is_ascii_uppercase() || c == '_') {
            return Some(Term::var(trimmed));
        } else {
            return Some(Term::App {
                symbol: trimmed.to_string(),
                args: vec![],
            });
        }
    }

    // Numeric literal
    if trimmed.parse::<i64>().is_ok() || trimmed.parse::<f64>().is_ok() {
        return Some(Term::App {
            symbol: trimmed.to_string(),
            args: vec![],
        });
    }

    None
}

/// Public wrapper for `parse_pattern_to_term` for use by sibling modules.
pub(crate) fn parse_pattern_to_term_pub(pattern: &str) -> Option<Term> {
    parse_pattern_to_term(pattern)
}

/// Tokenize a pattern string into space-separated tokens, respecting parentheses.
fn tokenize_pattern(input: &str) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut current = String::new();
    let mut depth = 0;

    for ch in input.chars() {
        match ch {
            '(' => {
                depth += 1;
                current.push(ch);
            },
            ')' => {
                depth -= 1;
                current.push(ch);
            },
            ' ' | '\t' | '\n' if depth == 0 => {
                if !current.is_empty() {
                    tokens.push(current.clone());
                    current.clear();
                }
            },
            '{' | '}' | ',' if depth == 0 => {
                // Skip collection syntax at top level
                if !current.is_empty() {
                    tokens.push(current.clone());
                    current.clear();
                }
            },
            _ => {
                current.push(ch);
            },
        }
    }

    if !current.is_empty() {
        tokens.push(current);
    }

    tokens
}
