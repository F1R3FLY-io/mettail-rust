//! Pratt expression parser generation.
//!
//! Generates the core expression parsing loop for each category.
//! The Pratt parser handles precedence and associativity natively via
//! binding power pairs.
//!
//! Generated structure per category:
//! - `parse_<Category>(tokens, pos, min_bp)` — main Pratt loop
//! - `parse_<Category>_prefix(tokens, pos)` — nud (null denotation) handler
//! - `infix_bp_<Category>(token)` — binding power lookup
//! - `make_infix_<Category>(token, lhs, rhs)` — AST construction

use std::fmt::Write;

use crate::binding_power::BindingPowerTable;
use crate::dispatch::CastRule;
use crate::prediction::FirstSet;

/// Build a human-readable "expected" message from a FIRST set.
///
/// Converts internal token names to user-friendly representations:
/// - `"Integer"` → `"integer literal"`
/// - `"Boolean"` → `"boolean literal"`
/// - `"StringLit"` → `"string literal"`
/// - `"Ident"` → `"identifier"`
/// - Quoted tokens like `"+"`, `"lam"` → `"+", "lam"`
/// - Category names → kept as-is
///
/// Example output: `"Int expression (one of: integer literal, identifier, \"(\", \"-\")"`
fn build_expected_message(category: &str, first_set: &FirstSet) -> String {
    if first_set.tokens.is_empty() {
        return format!("{} expression", category);
    }

    let mut items: Vec<String> = Vec::with_capacity(first_set.tokens.len());
    let mut has_ident = false;
    let mut has_integer = false;
    let mut has_boolean = false;
    let mut has_string_lit = false;
    let mut has_float = false;

    for token in &first_set.tokens {
        match token.as_str() {
            "Ident" => has_ident = true,
            "Integer" => has_integer = true,
            "Boolean" => has_boolean = true,
            "StringLit" => has_string_lit = true,
            "Float" => has_float = true,
            t => items.push(format!("\"{}\"", t)),
        }
    }

    // Add friendly names for special tokens
    if has_integer {
        items.insert(0, "integer literal".to_string());
    }
    if has_float {
        items.insert(0, "float literal".to_string());
    }
    if has_boolean {
        items.insert(0, "boolean literal".to_string());
    }
    if has_string_lit {
        items.insert(0, "string literal".to_string());
    }
    if has_ident {
        items.insert(0, "identifier".to_string());
    }

    items.sort();

    if items.len() <= 3 {
        format!("{} expression (one of: {})", category, items.join(", "))
    } else {
        // For long lists, show first few and count
        format!(
            "{} expression (one of: {}, ... [{} options])",
            category,
            items[..3].join(", "),
            items.len()
        )
    }
}

/// Configuration for generating a category's Pratt parser.
pub struct PrattConfig {
    /// Category name (e.g., "Proc", "Int").
    pub category: String,
    /// Whether this is the primary (first-declared) category.
    pub is_primary: bool,
    /// Whether this category has infix operators.
    pub has_infix: bool,
    /// All category names in the language (for cross-references).
    pub all_categories: Vec<String>,
    /// Whether this category needs a cross-category dispatch wrapper.
    /// When true, the Pratt parser is emitted as `parse_Cat_own` instead of `parse_Cat`,
    /// and the dispatch module will generate the wrapping `parse_Cat`.
    pub needs_dispatch: bool,
    /// Whether this category has postfix operators.
    pub has_postfix: bool,
    /// Whether this category has mixfix operators (3+ operands, e.g., ternary).
    pub has_mixfix: bool,
    /// Native Rust type for this category, if any (e.g., "i32", "bool", "String").
    /// Used to generate literal token match arms in the prefix handler.
    pub native_type: Option<String>,
    /// Cast rules targeting this category (e.g., `Int → Proc`).
    /// These generate prefix match arms so the Pratt infix loop can continue.
    pub cast_rules: Vec<CastRule>,
    /// FIRST set for this category (for determining unique cast rule tokens).
    pub own_first_set: FirstSet,
    /// FIRST sets for all categories (for determining unique tokens per source).
    pub all_first_sets: std::collections::BTreeMap<String, FirstSet>,
    /// FOLLOW set for this category — tokens that can appear after a complete expression.
    /// Used for error messages ("expected one of: ...") and sync point selection.
    pub follow_set: FirstSet,
}

/// Write the complete Pratt parser for a single category to a string buffer.
///
/// Writes:
/// - `parse_<Category>()` function
/// - `parse_<Category>_prefix()` function
/// - Binding power lookup function (if infix operators exist)
/// - Infix AST construction function (if infix operators exist)
pub fn write_pratt_parser(
    buf: &mut String,
    config: &PrattConfig,
    bp_table: &BindingPowerTable,
    prefix_handlers: &[PrefixHandler],
) {
    let cat = &config.category;
    let parse_fn = if config.needs_dispatch {
        format!("parse_{}_own", cat)
    } else {
        format!("parse_{}", cat)
    };

    // Generate the main Pratt loop
    let has_led = config.has_infix || config.has_postfix || config.has_mixfix;

    if has_led {
        // Generate helper functions for each operator type
        if config.has_infix {
            write_bp_function(buf, config, bp_table);
            write_make_infix(buf, config, bp_table);
        }
        if config.has_postfix {
            write_postfix_bp_function(buf, config, bp_table);
            write_make_postfix(buf, config, bp_table);
        }
        if config.has_mixfix {
            write_mixfix_bp_function(buf, config, bp_table);
            write_handle_mixfix(buf, config, bp_table);
        }

        // Build the led handler chain
        write!(
            buf,
            "fn {parse_fn}<'a>(\
                tokens: &[(Token<'a>, Span)], \
                pos: &mut usize, \
                min_bp: u8, \
            ) -> Result<{cat}, ParseError> {{ \
                let mut lhs = parse_{cat}_prefix(tokens, pos)?; \
                loop {{ \
                    if *pos >= tokens.len() {{ break; }} \
                    let token = &tokens[*pos].0;",
        )
        .unwrap();
        write_led_chain(buf, config);
        buf.push_str("} Ok(lhs) }");
    } else {
        write!(
            buf,
            "fn {parse_fn}<'a>(\
                tokens: &[(Token<'a>, Span)], \
                pos: &mut usize, \
                _min_bp: u8, \
            ) -> Result<{cat}, ParseError> {{ \
                parse_{cat}_prefix(tokens, pos) \
            }}",
        )
        .unwrap();
    }

    // Generate the prefix handler
    write_prefix_handler(buf, config, prefix_handlers);
}

/// Write the led (left-denotation) handler chain for the Pratt loop.
///
/// Generates an if/else-if/else chain checking operator types in order:
/// postfix (binds tightest) → mixfix (n-ary) → infix (binary) → break.
fn write_led_chain(buf: &mut String, config: &PrattConfig) {
    let cat = &config.category;
    let parse_fn = if config.needs_dispatch {
        format!("parse_{}_own", cat)
    } else {
        format!("parse_{}", cat)
    };

    let mut wrote_first = false;

    if config.has_postfix {
        write!(
            buf,
            "if let Some(l_bp) = postfix_bp_{cat}(token) {{ \
                if l_bp < min_bp {{ break; }} \
                let op_token = token.clone(); \
                *pos += 1; \
                lhs = make_postfix_{cat}(&op_token, lhs); \
            }}",
        )
        .unwrap();
        wrote_first = true;
    }

    if config.has_mixfix {
        if wrote_first {
            buf.push_str(" else ");
        }
        write!(
            buf,
            "if let Some((l_bp, r_bp)) = mixfix_bp_{cat}(token) {{ \
                if l_bp < min_bp {{ break; }} \
                let op_token = token.clone(); \
                *pos += 1; \
                lhs = handle_mixfix_{cat}(&op_token, lhs, tokens, pos, r_bp)?; \
            }}",
        )
        .unwrap();
        wrote_first = true;
    }

    if config.has_infix {
        if wrote_first {
            buf.push_str(" else ");
        }
        write!(
            buf,
            "if let Some((l_bp, r_bp)) = infix_bp_{cat}(token) {{ \
                if l_bp < min_bp {{ break; }} \
                let op_token = token.clone(); \
                *pos += 1; \
                let rhs = {parse_fn}(tokens, pos, r_bp)?; \
                lhs = make_infix_{cat}(&op_token, lhs, rhs); \
            }}",
        )
        .unwrap();
        wrote_first = true;
    }

    if wrote_first {
        buf.push_str(" else { break; }");
    } else {
        buf.push_str("break;");
    }
}

/// Write the binding power lookup function.
fn write_bp_function(buf: &mut String, config: &PrattConfig, bp_table: &BindingPowerTable) {
    let cat = &config.category;
    write!(
        buf,
        "fn infix_bp_{cat}<'a>(token: &Token<'a>) -> Option<(u8, u8)> {{ match token {{"
    )
    .unwrap();

    for op in bp_table.operators_for_category(cat) {
        let variant = crate::automata::codegen::terminal_to_variant_name(&op.terminal);
        write!(buf, "Token::{} => Some(({}, {})),", variant, op.left_bp, op.right_bp).unwrap();
    }

    buf.push_str("_ => None } }");
}

/// Write the make_infix function.
fn write_make_infix(buf: &mut String, config: &PrattConfig, bp_table: &BindingPowerTable) {
    let cat = &config.category;
    write!(
        buf,
        "fn make_infix_{cat}<'a>(token: &Token<'a>, lhs: {cat}, rhs: {cat}) -> {cat} {{ match token {{",
    )
    .unwrap();

    for op in bp_table.operators_for_category(cat) {
        let variant = crate::automata::codegen::terminal_to_variant_name(&op.terminal);
        write!(
            buf,
            "Token::{} => {}::{}(Box::new(lhs), Box::new(rhs)),",
            variant, cat, op.label,
        )
        .unwrap();
    }

    buf.push_str("_ => unreachable!(\"make_infix called with non-infix token\") } }");
}

/// Write the postfix binding power lookup function.
fn write_postfix_bp_function(buf: &mut String, config: &PrattConfig, bp_table: &BindingPowerTable) {
    let cat = &config.category;
    write!(
        buf,
        "fn postfix_bp_{cat}<'a>(token: &Token<'a>) -> Option<u8> {{ match token {{"
    )
    .unwrap();

    for op in bp_table.postfix_operators_for_category(cat) {
        let variant = crate::automata::codegen::terminal_to_variant_name(&op.terminal);
        write!(buf, "Token::{} => Some({}),", variant, op.left_bp).unwrap();
    }

    buf.push_str("_ => None } }");
}

/// Write the make_postfix function.
fn write_make_postfix(buf: &mut String, config: &PrattConfig, bp_table: &BindingPowerTable) {
    let cat = &config.category;
    write!(
        buf,
        "fn make_postfix_{cat}<'a>(token: &Token<'a>, operand: {cat}) -> {cat} {{ match token {{",
    )
    .unwrap();

    for op in bp_table.postfix_operators_for_category(cat) {
        let variant = crate::automata::codegen::terminal_to_variant_name(&op.terminal);
        write!(buf, "Token::{} => {}::{}(Box::new(operand)),", variant, cat, op.label).unwrap();
    }

    buf.push_str("_ => unreachable!(\"make_postfix called with non-postfix token\") } }");
}

/// Write the mixfix binding power lookup function.
fn write_mixfix_bp_function(buf: &mut String, config: &PrattConfig, bp_table: &BindingPowerTable) {
    let cat = &config.category;
    write!(
        buf,
        "fn mixfix_bp_{cat}<'a>(token: &Token<'a>) -> Option<(u8, u8)> {{ match token {{",
    )
    .unwrap();

    for op in bp_table.mixfix_operators_for_category(cat) {
        let variant = crate::automata::codegen::terminal_to_variant_name(&op.terminal);
        write!(buf, "Token::{} => Some(({}, {})),", variant, op.left_bp, op.right_bp).unwrap();
    }

    buf.push_str("_ => None } }");
}

/// Write the handle_mixfix function.
///
/// For each mixfix operator, generates a match arm that parses
/// middle operands (with min_bp=0, like grouping) and the final
/// operand (with right_bp), then constructs the AST node.
fn write_handle_mixfix(buf: &mut String, config: &PrattConfig, bp_table: &BindingPowerTable) {
    let cat = &config.category;
    let parse_fn = if config.needs_dispatch {
        format!("parse_{}_own", cat)
    } else {
        format!("parse_{}", cat)
    };

    write!(
        buf,
        "fn handle_mixfix_{cat}<'a>(\
            trigger: &Token<'a>, \
            lhs: {cat}, \
            tokens: &[(Token<'a>, Span)], \
            pos: &mut usize, \
            r_bp: u8, \
        ) -> Result<{cat}, ParseError> {{ match trigger {{",
    )
    .unwrap();

    for op in bp_table.mixfix_operators_for_category(cat) {
        let variant = crate::automata::codegen::terminal_to_variant_name(&op.terminal);
        write!(buf, "Token::{} => {{", variant).unwrap();

        let mut param_names: Vec<String> = Vec::new();
        for (i, part) in op.mixfix_parts.iter().enumerate() {
            let param_ident = format!("param_{}", part.param_name);
            let is_last = i == op.mixfix_parts.len() - 1;

            let fn_name = if part.operand_category == *cat {
                parse_fn.clone()
            } else {
                format!("parse_{}", part.operand_category)
            };

            let bp = if is_last { "r_bp" } else { "0" };
            write!(buf, "let {} = {}(tokens, pos, {})?;", param_ident, fn_name, bp).unwrap();
            param_names.push(param_ident);

            // Expect the following separator terminal (if any)
            if let Some(ref terminal) = part.following_terminal {
                let sep_variant = crate::automata::codegen::terminal_to_variant_name(terminal);
                write!(
                    buf,
                    "expect_token(tokens, pos, |t| matches!(t, Token::{}), \"{}\")?;",
                    sep_variant, terminal,
                )
                .unwrap();
            }
        }

        // Construct the AST node: Cat::Label(Box::new(lhs), Box::new(p1), ...)
        write!(buf, "Ok({}::{}(Box::new(lhs)", cat, op.label).unwrap();
        for p in &param_names {
            write!(buf, ", Box::new({})", p).unwrap();
        }
        buf.push_str("))},");
    }

    buf.push_str("_ => unreachable!(\"handle_mixfix called with non-mixfix trigger\") } }");
}

/// Write a token match pattern string for a given token name.
fn write_token_pattern(buf: &mut String, token: &str) {
    match token {
        "Ident" => buf.push_str("Token::Ident(_)"),
        "Integer" => buf.push_str("Token::Integer(_)"),
        "Float" => buf.push_str("Token::Float(_)"),
        "Boolean" => buf.push_str("Token::Boolean(_)"),
        "StringLit" => buf.push_str("Token::StringLit(_)"),
        _ => write!(buf, "Token::{}", token).unwrap(),
    }
}

/// Write the prefix (nud) handler function.
fn write_prefix_handler(buf: &mut String, config: &PrattConfig, prefix_handlers: &[PrefixHandler]) {
    let cat = &config.category;
    let parse_fn = format!("parse_{}", cat);

    let mut match_arms: Vec<String> = Vec::new();

    // Collect handlers with ident_lookahead (nonterminal-first rules)
    let lookahead_handlers: Vec<&PrefixHandler> = prefix_handlers
        .iter()
        .filter(|h| h.category == *cat && h.ident_lookahead.is_some())
        .collect();

    // Generate match arms from terminal-first prefix handlers.
    // NFA disambiguation: group handlers by dispatch token. When multiple handlers
    // share the same token (e.g., FloatId and IntToFloat both dispatch on KwFloat),
    // emit a single merged arm that tries all alternatives NFA-style.
    {
        let mut handlers_by_token: std::collections::BTreeMap<String, Vec<&PrefixHandler>> =
            std::collections::BTreeMap::new();
        for handler in prefix_handlers {
            if handler.category != *cat {
                continue;
            }
            if handler.match_arm.is_empty() {
                continue;
            }
            // Extract the token pattern: everything before " => "
            if let Some(idx) = handler.match_arm.find(" => ") {
                let token_pattern = handler.match_arm[..idx].to_string();
                handlers_by_token
                    .entry(token_pattern)
                    .or_default()
                    .push(handler);
            } else {
                // Fallback: push as-is
                match_arms.push(handler.match_arm.clone());
            }
        }

        for (token_pattern, handlers) in &handlers_by_token {
            if handlers.len() == 1 {
                // Singleton: emit the original match arm
                match_arms.push(handlers[0].match_arm.clone());
            } else {
                // Multiple handlers share this token — NFA-style merged arm
                let mut arm = format!("{} => {{", token_pattern);
                arm.push_str("let nfa_saved = *pos;");
                write!(arm, "let mut nfa_results: Vec<{}> = Vec::new();", cat).unwrap();
                arm.push_str("let mut nfa_positions: Vec<usize> = Vec::new();");
                arm.push_str("let mut nfa_first_err: Option<ParseError> = None;");

                for handler in handlers {
                    arm.push_str("*pos = nfa_saved;");
                    write!(
                        arm,
                        "match {}(tokens, pos) {{ \
                            Ok(v) => {{ nfa_results.push(v); nfa_positions.push(*pos); }}, \
                            Err(e) => {{ if nfa_first_err.is_none() {{ nfa_first_err = Some(e); }} }}, \
                        }}",
                        handler.parse_fn_name,
                    )
                    .unwrap();
                }

                arm.push_str("match nfa_results.len() {");
                write!(
                    arm,
                    "0 => Err(nfa_first_err.unwrap_or_else(|| \
                        ParseError::UnexpectedToken {{ \
                            expected: \"{cat} expression\", \
                            found: format!(\"{{:?}}\", &tokens[nfa_saved].0), \
                            range: tokens[nfa_saved].1, \
                        }} \
                    )),",
                )
                .unwrap();
                arm.push_str("_ => { *pos = nfa_positions[0]; Ok(nfa_results.into_iter().next().expect(\"nfa_results non-empty\")) },");
                arm.push_str("}"); // close match
                arm.push_str("}"); // close arm body
                match_arms.push(arm);
            }
        }
    }

    // Add native literal match arms for this category's own native type
    if let Some(ref native_type) = config.native_type {
        match native_type.as_str() {
            "i32" => {
                match_arms.push(format!(
                    "Token::Integer(v) => {{ let val = *v as i32; *pos += 1; Ok({}::NumLit(val)) }}",
                    cat,
                ));
            },
            "i64" | "isize" => {
                match_arms.push(format!(
                    "Token::Integer(v) => {{ let val = *v; *pos += 1; Ok({}::NumLit(val)) }}",
                    cat,
                ));
            },
            "u32" => {
                match_arms.push(format!(
                    "Token::Integer(v) => {{ let val = *v as u32; *pos += 1; Ok({}::NumLit(val)) }}",
                    cat,
                ));
            },
            "u64" | "usize" => {
                match_arms.push(format!(
                    "Token::Integer(v) => {{ let val = *v as u64; *pos += 1; Ok({}::NumLit(val)) }}",
                    cat,
                ));
            },
            "f32" | "f64" => {
                match_arms.push(format!(
                    "Token::Float(v) => {{ let val = (*v).into(); *pos += 1; Ok({}::FloatLit(val)) }}",
                    cat,
                ));
            },
            "bool" => {
                match_arms.push(format!(
                    "Token::Boolean(v) => {{ let val = *v; *pos += 1; Ok({}::BoolLit(val)) }}",
                    cat,
                ));
            },
            "str" | "String" => {
                match_arms.push(format!(
                    "Token::StringLit(v) => {{ let val = (*v).to_string(); *pos += 1; Ok({}::StringLit(val)) }}",
                    cat,
                ));
            },
            _ => {}, // Unknown native type — no auto-literal
        }
    }

    // Add grouping: parenthesized expression
    match_arms.push(format!(
        "Token::LParen => {{ \
            *pos += 1; \
            let expr = {}(tokens, pos, 0)?; \
            expect_token(tokens, pos, |t| matches!(t, Token::RParen), \")\")?; \
            Ok(expr) \
        }}",
        parse_fn,
    ));

    // Add cast rule prefix arms
    for cast_rule in &config.cast_rules {
        if let Some(source_first) = config.all_first_sets.get(&cast_rule.source_category) {
            let unique_tokens = source_first.difference(&config.own_first_set);
            for token in &unique_tokens.tokens {
                let mut arm = String::new();
                write_token_pattern(&mut arm, token);
                write!(
                    arm,
                    " => {{ \
                        let val = parse_{}(tokens, pos, 0)?; \
                        Ok({}::{}(Box::new(val))) \
                    }}",
                    cast_rule.source_category, cat, cast_rule.label,
                )
                .unwrap();
                match_arms.push(arm);
            }
        }
    }

    // Generate the variable label
    let var_label = format!(
        "{}Var",
        cat.chars()
            .next()
            .unwrap_or('V')
            .to_uppercase()
            .collect::<String>()
    );

    // Add variable fallback (with optional lookahead for nonterminal-first rules)
    // With zero-copy Token<'a>, Ident(&'a str): `name` is `&&'a str` in match,
    // so we dereference with `*name` to get `&str` and `.to_string()` for ownership.
    if !lookahead_handlers.is_empty() {
        let mut arm = String::from("Token::Ident(name) => { match peek_ahead(tokens, *pos, 1) {");
        for handler in &lookahead_handlers {
            let terminal = handler.ident_lookahead.as_ref().expect("checked above");
            let variant = crate::automata::codegen::terminal_to_variant_name(terminal);
            write!(arm, "Some(Token::{}) => {}(tokens, pos),", variant, handler.parse_fn_name)
                .unwrap();
        }
        // Default: variable fallback
        write!(
            arm,
            "_ => {{ \
                let var_name = (*name).to_string(); \
                *pos += 1; \
                Ok({cat}::{var_label}(\
                    mettail_runtime::OrdVar(mettail_runtime::Var::Free(\
                        mettail_runtime::get_or_create_var(var_name)\
                    ))\
                )) \
            }}",
        )
        .unwrap();
        arm.push_str("} }");
        match_arms.push(arm);
    } else {
        // Simple variable fallback without lookahead
        match_arms.push(format!(
            "Token::Ident(name) => {{ \
                let var_name = (*name).to_string(); \
                *pos += 1; \
                Ok({cat}::{var_label}(\
                    mettail_runtime::OrdVar(mettail_runtime::Var::Free(\
                        mettail_runtime::get_or_create_var(var_name)\
                    ))\
                )) \
            }}",
        ));
    }

    // Build descriptive "expected" string from FIRST set
    let expected_msg = build_expected_message(cat, &config.own_first_set);
    // Escape the message for use in a string literal
    let expected_escaped = expected_msg.replace('\\', "\\\\").replace('"', "\\\"");

    // Error fallback arm
    match_arms.push(format!(
        "other => {{ \
            Err(ParseError::UnexpectedToken {{ \
                expected: \"{expected_escaped}\", \
                found: format!(\"{{:?}}\", other), \
                range: tokens[*pos].1, \
            }}) \
        }}",
    ));

    // Write the prefix function
    write!(
        buf,
        "fn parse_{cat}_prefix<'a>(\
            tokens: &[(Token<'a>, Span)], \
            pos: &mut usize, \
        ) -> Result<{cat}, ParseError> {{ \
            if *pos >= tokens.len() {{ \
                let eof_range = tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()); \
                return Err(ParseError::UnexpectedEof {{ \
                    expected: \"{expected_escaped}\", \
                    range: eof_range, \
                }}); \
            }} \
            match &tokens[*pos].0 {{ {arms} }} \
        }}",
        arms = match_arms.join(","),
    )
    .unwrap();
}

/// A prefix handler for a specific rule.
#[derive(Debug, Clone)]
pub struct PrefixHandler {
    /// Category this handler belongs to.
    pub category: String,
    /// Rule label.
    pub label: String,
    /// Generated match arm as a string fragment.
    pub match_arm: String,
    /// If the rule starts with a nonterminal (Ident-dispatched), this is the
    /// lookahead terminal to check after the Ident. `None` for terminal-first rules.
    pub ident_lookahead: Option<String>,
    /// The parse function name for direct call from lookahead dispatch.
    pub parse_fn_name: String,
}

/// Write helper functions used by all parsers.
///
/// All helper functions are generic over the token lifetime `'a` to support
/// zero-copy lexing (`Token<'a>` with `Ident(&'a str)`).
pub fn write_parser_helpers(buf: &mut String) {
    buf.push_str(
        "fn expect_token<'a>(\
            tokens: &[(Token<'a>, Span)], \
            pos: &mut usize, \
            predicate: impl Fn(&Token) -> bool, \
            expected: &'static str, \
        ) -> Result<(), ParseError> { \
            if *pos >= tokens.len() { \
                let eof_range = tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()); \
                return Err(ParseError::UnexpectedEof { expected, range: eof_range }); \
            } \
            if predicate(&tokens[*pos].0) { \
                *pos += 1; \
                Ok(()) \
            } else { \
                Err(ParseError::UnexpectedToken { \
                    expected, \
                    found: format!(\"{:?}\", tokens[*pos].0), \
                    range: tokens[*pos].1, \
                }) \
            } \
        }\n\
        fn expect_ident<'a>(tokens: &[(Token<'a>, Span)], pos: &mut usize) -> Result<String, ParseError> { \
            if *pos >= tokens.len() { \
                let eof_range = tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()); \
                return Err(ParseError::UnexpectedEof { expected: \"identifier\", range: eof_range }); \
            } \
            match &tokens[*pos].0 { \
                Token::Ident(name) => { \
                    let result = name.to_string(); \
                    *pos += 1; \
                    Ok(result) \
                } \
                other => { \
                    Err(ParseError::UnexpectedToken { \
                        expected: \"identifier\", \
                        found: format!(\"{:?}\", other), \
                        range: tokens[*pos].1, \
                    }) \
                } \
            } \
        }\n\
        fn peek_token<'a, 'b>(tokens: &'b [(Token<'a>, Span)], pos: usize) -> Option<&'b Token<'a>> { \
            tokens.get(pos).map(|(t, _)| t) \
        }\n\
        fn peek_ahead<'a, 'b>(tokens: &'b [(Token<'a>, Span)], pos: usize, offset: usize) -> Option<&'b Token<'a>> { \
            tokens.get(pos + offset).map(|(t, _)| t) \
        }",
    );
}

// ══════════════════════════════════════════════════════════════════════════════
// Error recovery code generation
// ══════════════════════════════════════════════════════════════════════════════

/// Write recovery helper functions used by `_recovering` parsers.
///
/// These are the recovery-mode counterparts of `expect_token` and `expect_ident`.
/// Instead of returning `Err`, they accumulate errors and use token insertion
/// repair (pretend the expected token was there without consuming the mismatched token).
pub fn write_recovery_helpers(buf: &mut String) {
    buf.push_str(
        // sync_to: advance position to the next sync token
        "fn sync_to<'a>(\
            tokens: &[(Token<'a>, Span)], \
            pos: &mut usize, \
            sync: &dyn Fn(&Token) -> bool, \
        ) { \
            while *pos < tokens.len() { \
                if sync(&tokens[*pos].0) { return; } \
                *pos += 1; \
            } \
        }\n\
        // expect_token_rec: token insertion repair. On mismatch, push error but
        // don't consume the mismatched token (pretend the expected token was there).
        fn expect_token_rec<'a>(\
            tokens: &[(Token<'a>, Span)], \
            pos: &mut usize, \
            predicate: impl Fn(&Token) -> bool, \
            expected: &'static str, \
            errors: &mut Vec<ParseError>, \
        ) -> bool { \
            if *pos >= tokens.len() { \
                let eof_range = tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()); \
                errors.push(ParseError::UnexpectedEof { expected, range: eof_range }); \
                return false; \
            } \
            if predicate(&tokens[*pos].0) { \
                *pos += 1; \
                true \
            } else { \
                errors.push(ParseError::UnexpectedToken { \
                    expected, \
                    found: format!(\"{:?}\", tokens[*pos].0), \
                    range: tokens[*pos].1, \
                }); \
                false \
            } \
        }\n\
        // expect_ident_rec: on mismatch, push error and return placeholder.
        fn expect_ident_rec<'a>(\
            tokens: &[(Token<'a>, Span)], \
            pos: &mut usize, \
            errors: &mut Vec<ParseError>, \
        ) -> String { \
            if *pos >= tokens.len() { \
                let eof_range = tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()); \
                errors.push(ParseError::UnexpectedEof { expected: \"identifier\", range: eof_range }); \
                return \"__error__\".to_string(); \
            } \
            match &tokens[*pos].0 { \
                Token::Ident(name) => { \
                    let result = name.to_string(); \
                    *pos += 1; \
                    result \
                } \
                other => { \
                    errors.push(ParseError::UnexpectedToken { \
                        expected: \"identifier\", \
                        found: format!(\"{:?}\", other), \
                        range: tokens[*pos].1, \
                    }); \
                    \"__error__\".to_string() \
                } \
            } \
        }",
    );
}

/// Write the recovering Pratt parser for a single category.
///
/// Generates `parse_<Category>_recovering(tokens, pos, min_bp, errors) -> Option<Cat>`.
/// The function structure mirrors the fail-fast parser but:
/// - Prefix errors are accumulated and return `None`
/// - Led loop errors are accumulated and break the loop (returning partial `Some(lhs)`)
/// - Sync points use the generated `is_sync_Cat` predicate
pub fn write_pratt_parser_recovering(
    buf: &mut String,
    config: &PrattConfig,
    bp_table: &BindingPowerTable,
) {
    let cat = &config.category;
    let parse_fn = if config.needs_dispatch {
        format!("parse_{}_own_recovering", cat)
    } else {
        format!("parse_{}_recovering", cat)
    };

    let has_led = config.has_infix || config.has_postfix || config.has_mixfix;

    write!(
        buf,
        "fn {parse_fn}<'a>(\
            tokens: &[(Token<'a>, Span)], \
            pos: &mut usize, \
            min_bp: u8, \
            errors: &mut Vec<ParseError>, \
        ) -> Option<{cat}> {{",
    )
    .unwrap();

    // Prefix: call fail-fast prefix, on Err push error + sync + return None
    write!(
        buf,
        "let mut lhs = match parse_{cat}_prefix(tokens, pos) {{ \
            Ok(v) => v, \
            Err(e) => {{ \
                errors.push(e); \
                sync_to(tokens, pos, &|t| is_sync_{cat}(t)); \
                return None; \
            }} \
        }};",
    )
    .unwrap();

    if has_led {
        // Led loop with recovery
        buf.push_str(
            "loop { \
            if *pos >= tokens.len() { break; } \
            let token = &tokens[*pos].0;",
        );

        write_led_chain_recovering(buf, config, bp_table);

        buf.push_str("} ");
    }

    buf.push_str("Some(lhs) }");
}

/// Write the recovering led (left-denotation) handler chain.
///
/// For postfix and mixfix: same as non-recovering (no sub-parse to fail for postfix;
/// mixfix wraps sub-parses with recovery).
/// For infix: wraps RHS parse in recovery — on error, push error + sync + break.
fn write_led_chain_recovering(
    buf: &mut String,
    config: &PrattConfig,
    _bp_table: &BindingPowerTable,
) {
    let cat = &config.category;
    let parse_fn = if config.needs_dispatch {
        format!("parse_{}_own", cat)
    } else {
        format!("parse_{}", cat)
    };

    let mut wrote_first = false;

    // Postfix: identical to non-recovering (no recursive parse)
    if config.has_postfix {
        write!(
            buf,
            "if let Some(l_bp) = postfix_bp_{cat}(token) {{ \
                if l_bp < min_bp {{ break; }} \
                let op_token = token.clone(); \
                *pos += 1; \
                lhs = make_postfix_{cat}(&op_token, lhs); \
            }}",
        )
        .unwrap();
        wrote_first = true;
    }

    // Mixfix: wrap sub-parses in recovery
    if config.has_mixfix {
        if wrote_first {
            buf.push_str(" else ");
        }
        write!(
            buf,
            "if let Some((l_bp, _r_bp)) = mixfix_bp_{cat}(token) {{ \
                if l_bp < min_bp {{ break; }} \
                let op_token = token.clone(); \
                *pos += 1; \
                match handle_mixfix_{cat}(&op_token, lhs.clone(), tokens, pos, _r_bp) {{ \
                    Ok(result) => {{ lhs = result; }} \
                    Err(e) => {{ \
                        errors.push(e); \
                        sync_to(tokens, pos, &|t| is_sync_{cat}(t)); \
                        break; \
                    }} \
                }} \
            }}",
        )
        .unwrap();
        wrote_first = true;
    }

    // Infix: wrap RHS parse in recovery
    if config.has_infix {
        if wrote_first {
            buf.push_str(" else ");
        }
        write!(
            buf,
            "if let Some((l_bp, r_bp)) = infix_bp_{cat}(token) {{ \
                if l_bp < min_bp {{ break; }} \
                let op_token = token.clone(); \
                *pos += 1; \
                match {parse_fn}(tokens, pos, r_bp) {{ \
                    Ok(rhs) => {{ lhs = make_infix_{cat}(&op_token, lhs, rhs); }} \
                    Err(e) => {{ \
                        errors.push(e); \
                        sync_to(tokens, pos, &|t| is_sync_{cat}(t)); \
                        break; \
                    }} \
                }} \
            }}",
        )
        .unwrap();
        wrote_first = true;
    }

    if wrote_first {
        buf.push_str(" else { break; }");
    } else {
        buf.push_str("break;");
    }
}

/// Write the recovering dispatch wrapper for cross-category categories.
///
/// Generates `parse_<Cat>_recovering(tokens, pos, min_bp, errors) -> Option<Cat>`.
/// Falls back to `parse_<Cat>_own_recovering` after cross-category dispatch.
pub fn write_dispatch_recovering(buf: &mut String, category: &str) {
    use std::fmt::Write;
    write!(
        buf,
        "fn parse_{cat}_recovering<'a>(\
            tokens: &[(Token<'a>, Span)], \
            pos: &mut usize, \
            min_bp: u8, \
            errors: &mut Vec<ParseError>, \
        ) -> Option<{cat}> {{ \
            parse_{cat}_own_recovering(tokens, pos, min_bp, errors) \
        }}",
        cat = category,
    )
    .unwrap();
}

// ══════════════════════════════════════════════════════════════════════════════
// Public accessors for trampoline module
// ══════════════════════════════════════════════════════════════════════════════

/// Public wrapper: write BP function (for trampoline codegen).
pub fn write_bp_function_pub(buf: &mut String, cat: &str, bp_table: &BindingPowerTable) {
    write!(
        buf,
        "fn infix_bp_{cat}<'a>(token: &Token<'a>) -> Option<(u8, u8)> {{ match token {{"
    )
    .unwrap();
    for op in bp_table.operators_for_category(cat) {
        let variant = crate::automata::codegen::terminal_to_variant_name(&op.terminal);
        write!(buf, "Token::{} => Some(({}, {})),", variant, op.left_bp, op.right_bp).unwrap();
    }
    buf.push_str("_ => None } }");
}

/// Public wrapper: write make_infix function (for trampoline codegen).
pub fn write_make_infix_pub(buf: &mut String, cat: &str, bp_table: &BindingPowerTable) {
    write!(
        buf,
        "fn make_infix_{cat}<'a>(token: &Token<'a>, lhs: {cat}, rhs: {cat}) -> {cat} {{ match token {{",
    ).unwrap();
    for op in bp_table.operators_for_category(cat) {
        let variant = crate::automata::codegen::terminal_to_variant_name(&op.terminal);
        write!(
            buf,
            "Token::{} => {}::{}(Box::new(lhs), Box::new(rhs)),",
            variant, cat, op.label
        )
        .unwrap();
    }
    buf.push_str("_ => unreachable!(\"make_infix called with non-infix token\") } }");
}

/// Public wrapper: write postfix BP function (for trampoline codegen).
pub fn write_postfix_bp_function_pub(buf: &mut String, cat: &str, bp_table: &BindingPowerTable) {
    write!(
        buf,
        "fn postfix_bp_{cat}<'a>(token: &Token<'a>) -> Option<u8> {{ match token {{"
    )
    .unwrap();
    for op in bp_table.postfix_operators_for_category(cat) {
        let variant = crate::automata::codegen::terminal_to_variant_name(&op.terminal);
        write!(buf, "Token::{} => Some({}),", variant, op.left_bp).unwrap();
    }
    buf.push_str("_ => None } }");
}

/// Public wrapper: write make_postfix function (for trampoline codegen).
pub fn write_make_postfix_pub(buf: &mut String, cat: &str, bp_table: &BindingPowerTable) {
    write!(
        buf,
        "fn make_postfix_{cat}<'a>(token: &Token<'a>, operand: {cat}) -> {cat} {{ match token {{",
    )
    .unwrap();
    for op in bp_table.postfix_operators_for_category(cat) {
        let variant = crate::automata::codegen::terminal_to_variant_name(&op.terminal);
        write!(buf, "Token::{} => {}::{}(Box::new(operand)),", variant, cat, op.label).unwrap();
    }
    buf.push_str("_ => unreachable!(\"make_postfix called with non-postfix token\") } }");
}

/// Public wrapper: write mixfix BP function (for trampoline codegen).
pub fn write_mixfix_bp_function_pub(buf: &mut String, cat: &str, bp_table: &BindingPowerTable) {
    write!(
        buf,
        "fn mixfix_bp_{cat}<'a>(token: &Token<'a>) -> Option<(u8, u8)> {{ match token {{",
    )
    .unwrap();
    for op in bp_table.mixfix_operators_for_category(cat) {
        let variant = crate::automata::codegen::terminal_to_variant_name(&op.terminal);
        write!(buf, "Token::{} => Some(({}, {})),", variant, op.left_bp, op.right_bp).unwrap();
    }
    buf.push_str("_ => None } }");
}

/// Public wrapper: build expected message from FIRST set (for trampoline codegen).
pub fn build_expected_message_pub(category: &str, first_set: &FirstSet) -> String {
    build_expected_message(category, first_set)
}

/// Public wrapper: write token match pattern (for trampoline codegen).
pub fn write_token_pattern_pub(buf: &mut String, token: &str) {
    write_token_pattern(buf, token);
}
