//! Recursive descent handler generation.
//!
//! Generates per-rule functions for structural constructs that don't fit the
//! Pratt infix/prefix pattern: binders, collections, pattern operations,
//! and complex multi-token syntax.

use std::fmt::Write;

use crate::automata::codegen::terminal_to_variant_name;
use crate::pratt::PrefixHandler;

/// Information about a grammar rule needed for recursive descent generation.
#[derive(Debug, Clone)]
pub struct RDRuleInfo {
    /// Constructor label (e.g., "PInputs", "PPar").
    pub label: String,
    /// Category this rule belongs to (e.g., "Proc").
    pub category: String,
    /// Syntax items describing the concrete syntax.
    pub items: Vec<RDSyntaxItem>,
    /// Whether this rule involves a single binder.
    pub has_binder: bool,
    /// Whether this rule involves multiple binders.
    pub has_multi_binder: bool,
    /// Whether this rule is a collection (PPar, etc.).
    pub is_collection: bool,
    /// Collection type if applicable.
    pub collection_type: Option<CollectionKind>,
    /// Separator for collection items.
    pub separator: Option<String>,
    /// Binding power for the recursive call in unary prefix rules.
    /// When set, NonTerminal calls use this bp instead of 0.
    pub prefix_bp: Option<u8>,
    /// Eval mode for HOL rules.
    pub eval_mode: Option<String>,
}

/// A syntax item in a rule's concrete syntax.
#[derive(Debug, Clone)]
pub enum RDSyntaxItem {
    /// A fixed terminal token to match (e.g., "(", "+", "error").
    Terminal(String),
    /// A nonterminal to parse (category name, parameter name).
    NonTerminal {
        category: String,
        param_name: String,
    },
    /// An identifier to capture (not a category — a raw identifier).
    IdentCapture {
        param_name: String,
    },
    /// A binder position.
    Binder {
        param_name: String,
        binder_category: String,
    },
    /// A collection with separator.
    Collection {
        param_name: String,
        element_category: String,
        separator: String,
        kind: CollectionKind,
    },
    /// A separated list using #sep pattern op.
    SepList {
        collection_name: String,
        element_category: String,
        separator: String,
        kind: CollectionKind,
    },
    /// A zip+map+sep pattern operation.
    ZipMapSep {
        left_name: String,
        right_name: String,
        left_category: String,
        right_category: String,
        body_items: Vec<RDSyntaxItem>,
        separator: String,
    },
    /// An optional group.
    Optional {
        inner: Vec<RDSyntaxItem>,
    },
}

/// Kind of collection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CollectionKind {
    HashBag,
    HashSet,
    Vec,
}

/// Generate a recursive descent handler for a single rule.
///
/// Writes the parse function to `buf`, returns a `PrefixHandler` with the
/// match arm string for the dispatch table.
pub fn write_rd_handler(buf: &mut String, rule: &RDRuleInfo) -> PrefixHandler {
    let cat = &rule.category;
    let parse_fn_name = format!("parse_{}", rule.label.to_lowercase());

    // Build the parse function body and capture info
    let mut body = String::new();
    let captures = write_parse_body(&mut body, rule);

    // Build the constructor call
    let mut constructor = String::new();
    write_constructor(&mut constructor, rule, &captures);

    // Write the complete parse function
    write!(
        buf,
        "fn {parse_fn_name}<'a>(\
            tokens: &[(Token<'a>, Span)], \
            pos: &mut usize, \
        ) -> Result<{cat}, ParseError> {{ \
            {body} \
            {constructor} \
        }}",
    )
    .unwrap();

    // Determine dispatch strategy based on what the rule starts with
    let starts_with_nonterminal = matches!(
        rule.items.first(),
        Some(RDSyntaxItem::NonTerminal { .. }) | Some(RDSyntaxItem::IdentCapture { .. })
    );

    // Find the first terminal in the items list
    let first_terminal = rule.items.iter().find_map(|item| {
        if let RDSyntaxItem::Terminal(t) = item {
            Some(t.clone())
        } else {
            None
        }
    });

    let (match_arm, ident_lookahead) = if starts_with_nonterminal {
        // Rule starts with a NonTerminal — needs Ident+lookahead dispatch.
        (String::new(), first_terminal.clone())
    } else if let Some(ref terminal) = first_terminal {
        // Rule starts with a terminal — direct dispatch
        let variant = terminal_to_variant_name(terminal);
        (
            format!("Token::{} => {{ {}(tokens, pos) }}", variant, parse_fn_name),
            None,
        )
    } else {
        // No terminals at all — cannot dispatch (handled by fallback)
        (String::new(), None)
    };

    PrefixHandler {
        category: rule.category.clone(),
        label: rule.label.clone(),
        match_arm,
        ident_lookahead,
        parse_fn_name,
    }
}

/// A captured value during parsing.
#[derive(Debug, Clone)]
struct Capture {
    name: String,
    kind: CaptureKind,
}

#[derive(Debug, Clone)]
enum CaptureKind {
    Simple,        // Regular parsed value
    // Reserved for future use: explicit Box::new() wrapping when generated
    // enum variants distinguish between boxed and unboxed nonterminal fields.
    // Currently all NonTerminal fields are boxed uniformly via write_constructor_arg().
    // Boxed,
    Collection,    // Vec/HashBag/HashSet
    Binder,        // Binder for scope
    Ident,         // Captured identifier string
}

fn collection_init_str(kind: &CollectionKind) -> &'static str {
    match kind {
        CollectionKind::HashBag => "mettail_runtime::HashBag::new()",
        CollectionKind::HashSet => "std::collections::HashSet::new()",
        CollectionKind::Vec => "Vec::new()",
    }
}

fn insert_method_str(kind: &CollectionKind) -> &'static str {
    match kind {
        CollectionKind::HashBag | CollectionKind::HashSet => "insert",
        CollectionKind::Vec => "push",
    }
}

/// Write the parsing body for a rule to `buf`, returning the list of captures.
fn write_parse_body(buf: &mut String, rule: &RDRuleInfo) -> Vec<Capture> {
    let mut captures: Vec<Capture> = Vec::new();
    write_parse_items(buf, &rule.items, rule.prefix_bp, &mut captures);
    captures
}

/// Write parsing code for a list of syntax items to `buf`, accumulating captures.
fn write_parse_items(
    buf: &mut String,
    items: &[RDSyntaxItem],
    prefix_bp: Option<u8>,
    captures: &mut Vec<Capture>,
) {
    for item in items {
        match item {
            RDSyntaxItem::Terminal(t) => {
                let variant = terminal_to_variant_name(t);
                write!(
                    buf,
                    "expect_token(tokens, pos, |t| matches!(t, Token::{}), \"{}\")?;",
                    variant, t,
                )
                .unwrap();
            }
            RDSyntaxItem::NonTerminal { category, param_name } => {
                let bp = prefix_bp.unwrap_or(0);
                write!(
                    buf,
                    "let {} = parse_{}(tokens, pos, {})?;",
                    param_name, category, bp,
                )
                .unwrap();
                captures.push(Capture {
                    name: param_name.clone(),
                    kind: CaptureKind::Simple,
                });
            }
            RDSyntaxItem::IdentCapture { param_name } => {
                write!(buf, "let {} = expect_ident(tokens, pos)?;", param_name).unwrap();
                captures.push(Capture {
                    name: param_name.clone(),
                    kind: CaptureKind::Ident,
                });
            }
            RDSyntaxItem::Binder { param_name, .. } => {
                write!(buf, "let {} = expect_ident(tokens, pos)?;", param_name).unwrap();
                captures.push(Capture {
                    name: param_name.clone(),
                    kind: CaptureKind::Binder,
                });
            }
            RDSyntaxItem::Collection {
                param_name,
                element_category,
                separator,
                kind,
            } => {
                let sep_variant = terminal_to_variant_name(separator);
                let init = collection_init_str(kind);
                let method = insert_method_str(kind);

                write!(
                    buf,
                    "let mut {param_name} = {init}; \
                    loop {{ \
                        match parse_{element_category}(tokens, pos, 0) {{ \
                            Ok(elem) => {{ \
                                {param_name}.{method}(elem); \
                                if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::{sep_variant})) {{ \
                                    *pos += 1; \
                                }} else {{ \
                                    break; \
                                }} \
                            }} \
                            Err(_) => break, \
                        }} \
                    }}",
                )
                .unwrap();

                captures.push(Capture {
                    name: param_name.clone(),
                    kind: CaptureKind::Collection,
                });
            }
            RDSyntaxItem::SepList {
                collection_name,
                element_category,
                separator,
                kind,
            } => {
                let sep_variant = terminal_to_variant_name(separator);
                let init = collection_init_str(kind);
                let method = insert_method_str(kind);

                write!(
                    buf,
                    "let mut {collection_name} = {init}; \
                    loop {{ \
                        match parse_{element_category}(tokens, pos, 0) {{ \
                            Ok(elem) => {{ \
                                {collection_name}.{method}(elem); \
                                if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::{sep_variant})) {{ \
                                    *pos += 1; \
                                }} else {{ \
                                    break; \
                                }} \
                            }} \
                            Err(_) => break, \
                        }} \
                    }}",
                )
                .unwrap();

                captures.push(Capture {
                    name: collection_name.clone(),
                    kind: CaptureKind::Collection,
                });
            }
            RDSyntaxItem::ZipMapSep {
                left_name,
                right_name,
                left_category: _,
                right_category: _,
                body_items,
                separator,
            } => {
                let sep_variant = terminal_to_variant_name(separator);

                // Determine which param (left or right) is a binder
                let right_is_binder = body_items.iter().any(|item| {
                    matches!(item, RDSyntaxItem::Binder { param_name, .. } if param_name == right_name)
                });
                let left_is_binder = body_items.iter().any(|item| {
                    matches!(item, RDSyntaxItem::Binder { param_name, .. } if param_name == left_name)
                });

                write!(
                    buf,
                    "let mut {left_name} = Vec::new(); \
                    let mut {right_name} = Vec::new(); \
                    loop {{ \
                        if *pos >= tokens.len() {{ break; }} \
                        if peek_token(tokens, *pos).map_or(false, |t| {{ \
                            matches!(t, Token::RParen | Token::RBrace | Token::RBracket | Token::Eof) \
                        }}) {{ break; }}",
                )
                .unwrap();

                // Write parsing for each body item
                for body_item in body_items {
                    match body_item {
                        RDSyntaxItem::Terminal(t) => {
                            let variant = terminal_to_variant_name(t);
                            write!(
                                buf,
                                "expect_token(tokens, pos, |t| matches!(t, Token::{}), \"{}\")?;",
                                variant, t,
                            )
                            .unwrap();
                        }
                        RDSyntaxItem::NonTerminal { category, param_name } => {
                            if param_name == left_name {
                                write!(
                                    buf,
                                    "let _zms_item = parse_{}(tokens, pos, 0)?; {}.push(_zms_item);",
                                    category, left_name,
                                )
                                .unwrap();
                            } else if param_name == right_name {
                                write!(
                                    buf,
                                    "let _zms_item = parse_{}(tokens, pos, 0)?; {}.push(_zms_item);",
                                    category, right_name,
                                )
                                .unwrap();
                            } else {
                                write!(
                                    buf,
                                    "let _ = parse_{}(tokens, pos, 0)?;",
                                    category,
                                )
                                .unwrap();
                            }
                        }
                        RDSyntaxItem::Binder { param_name, .. }
                        | RDSyntaxItem::IdentCapture { param_name } => {
                            if param_name == left_name {
                                write!(
                                    buf,
                                    "let _zms_item = expect_ident(tokens, pos)?; {}.push(_zms_item);",
                                    left_name,
                                )
                                .unwrap();
                            } else if param_name == right_name {
                                write!(
                                    buf,
                                    "let _zms_item = expect_ident(tokens, pos)?; {}.push(_zms_item);",
                                    right_name,
                                )
                                .unwrap();
                            } else {
                                buf.push_str("let _ = expect_ident(tokens, pos)?;");
                            }
                        }
                        _ => {}
                    }
                }

                write!(
                    buf,
                    "if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::{sep_variant})) {{ \
                        *pos += 1; \
                    }} else {{ \
                        break; \
                    }} }}",
                )
                .unwrap();

                captures.push(Capture {
                    name: left_name.clone(),
                    kind: if left_is_binder { CaptureKind::Binder } else { CaptureKind::Collection },
                });
                captures.push(Capture {
                    name: right_name.clone(),
                    kind: if right_is_binder { CaptureKind::Binder } else { CaptureKind::Collection },
                });
            }
            RDSyntaxItem::Optional { inner } => {
                write_optional_body(buf, inner, captures);
            }
        }
    }
}

/// Write a constructor argument string for a capture.
fn write_constructor_arg(buf: &mut String, c: &Capture) {
    match c.kind {
        CaptureKind::Simple => write!(buf, "Box::new({})", c.name).unwrap(),
        CaptureKind::Ident => write!(
            buf,
            "mettail_runtime::OrdVar(mettail_runtime::Var::Free(\
                mettail_runtime::get_or_create_var({})\
            ))",
            c.name,
        )
        .unwrap(),
        _ => buf.push_str(&c.name),
    }
}

/// Write the constructor call from captures.
fn write_constructor(buf: &mut String, rule: &RDRuleInfo, captures: &[Capture]) {
    let cat = &rule.category;
    let label = &rule.label;

    if rule.has_binder {
        // Single binder rule: construct with Scope.
        let binder_capture = captures
            .iter()
            .find(|c| matches!(c.kind, CaptureKind::Binder))
            .expect("binder rule should have a binder capture");
        let body_capture = captures
            .iter()
            .rev()
            .find(|c| matches!(c.kind, CaptureKind::Simple))
            .expect("binder rule should have a body capture");

        // Collect extra args: everything except the binder and body captures
        let extra_args: Vec<&Capture> = captures
            .iter()
            .filter(|c| c.name != binder_capture.name && c.name != body_capture.name)
            .collect();

        write!(buf, "Ok({cat}::{label}(").unwrap();
        for c in &extra_args {
            write_constructor_arg(buf, c);
            buf.push(',');
        }
        write!(
            buf,
            "mettail_runtime::Scope::new(\
                mettail_runtime::Binder(mettail_runtime::get_or_create_var({})), \
                Box::new({}), \
            )))",
            binder_capture.name, body_capture.name,
        )
        .unwrap();
    } else if rule.has_multi_binder {
        // Multi-binder rule: same pattern but with Vec of binders.
        let binder_capture = captures
            .iter()
            .find(|c| matches!(c.kind, CaptureKind::Binder))
            .expect("multi-binder rule should have a binder capture");
        let body_capture = captures
            .iter()
            .rev()
            .find(|c| matches!(c.kind, CaptureKind::Simple))
            .expect("multi-binder rule should have a body capture");

        let extra_args: Vec<&Capture> = captures
            .iter()
            .filter(|c| c.name != binder_capture.name && c.name != body_capture.name)
            .collect();

        write!(
            buf,
            "let binders: Vec<mettail_runtime::Binder<String>> = {}.into_iter() \
                .map(|s| mettail_runtime::Binder(mettail_runtime::get_or_create_var(s))) \
                .collect();",
            binder_capture.name,
        )
        .unwrap();

        write!(buf, "Ok({cat}::{label}(").unwrap();
        for c in &extra_args {
            write_constructor_arg(buf, c);
            buf.push(',');
        }
        write!(
            buf,
            "mettail_runtime::Scope::new(\
                binders, \
                Box::new({}), \
            )))",
            body_capture.name,
        )
        .unwrap();
    } else if captures.is_empty() {
        // Unit variant (no captures)
        write!(buf, "Ok({cat}::{label})").unwrap();
    } else {
        // Simple constructor with arguments
        write!(buf, "Ok({cat}::{label}(").unwrap();
        for (i, c) in captures.iter().enumerate() {
            if i > 0 {
                buf.push(',');
            }
            write_constructor_arg(buf, c);
        }
        buf.push_str("))");
    }
}

/// Write parsing code for an optional group.
fn write_optional_body(buf: &mut String, items: &[RDSyntaxItem], captures: &mut Vec<Capture>) {
    buf.push_str(
        "let saved_pos = *pos; \
        let opt_result = (|| -> Result<(), ParseError> {",
    );

    // Write the inner parsing code (captures are accumulated into the outer vec)
    write_parse_items(buf, items, None, captures);

    buf.push_str(
        "Ok(()) })(); \
        if opt_result.is_err() { *pos = saved_pos; }",
    );
}

/// Write dollar-syntax handlers for function application ($cat, $$cat( syntax).
///
/// For each domain category `dom`, generates two parse functions:
/// - `parse_dollar_{dom_lower}` — handles `$dom(f, x)` → `Primary::Apply{Dom}(f, x)`
/// - `parse_ddollar_{dom_lower}` — handles `$$dom(f, x1, x2, ...)` → `Primary::MApply{Dom}(f, args)`
///
/// These are always associated with the PRIMARY category (the function `f` and
/// the result are of the primary type).
pub fn write_dollar_handlers(
    buf: &mut String,
    primary_category: &str,
    all_categories: &[String],
) -> Vec<PrefixHandler> {
    let cat = primary_category;
    let mut handlers = Vec::with_capacity(all_categories.len() * 2);

    for dom in all_categories {
        let dom_lower = dom.to_lowercase();

        // Capitalize first letter for variant names: "proc" → "Proc"
        let dom_capitalized = {
            let mut s = String::with_capacity(dom.len());
            let mut chars = dom_lower.chars();
            if let Some(first) = chars.next() {
                s.extend(first.to_uppercase());
            }
            s.extend(chars);
            s
        };

        let dollar_variant = format!("Dollar{}", dom_capitalized);
        let ddollar_variant = format!("Ddollar{}Lp", dom_capitalized);
        let apply_variant = format!("Apply{}", dom);
        let mapply_variant = format!("MApply{}", dom);

        // ── A) Single-apply: $dom(f, x) ──

        let single_fn = format!("parse_dollar_{}", dom_lower);

        write!(
            buf,
            "fn {single_fn}<'a>(\
                tokens: &[(Token<'a>, Span)], \
                pos: &mut usize, \
            ) -> Result<{cat}, ParseError> {{ \
                expect_token(tokens, pos, |t| matches!(t, Token::{dollar_variant}), \"${dom_lower}\")?; \
                expect_token(tokens, pos, |t| matches!(t, Token::LParen), \"(\")?; \
                let f = parse_{cat}(tokens, pos, 0)?; \
                expect_token(tokens, pos, |t| matches!(t, Token::Comma), \",\")?; \
                let x = parse_{dom}(tokens, pos, 0)?; \
                expect_token(tokens, pos, |t| matches!(t, Token::RParen), \")\")?; \
                Ok({cat}::{apply_variant}(Box::new(f), Box::new(x))) \
            }}",
        )
        .unwrap();

        handlers.push(PrefixHandler {
            category: cat.to_string(),
            label: format!("Dollar{}", dom_capitalized),
            match_arm: format!(
                "Token::{} => {{ {}(tokens, pos) }}",
                dollar_variant, single_fn
            ),
            ident_lookahead: None,
            parse_fn_name: single_fn,
        });

        // ── B) Multi-apply: $$dom(f, x1, x2, ...) ──

        let multi_fn = format!("parse_ddollar_{}", dom_lower);

        write!(
            buf,
            "fn {multi_fn}<'a>(\
                tokens: &[(Token<'a>, Span)], \
                pos: &mut usize, \
            ) -> Result<{cat}, ParseError> {{ \
                expect_token(tokens, pos, |t| matches!(t, Token::{ddollar_variant}), \"$${dom_lower}(\")?; \
                let f = parse_{cat}(tokens, pos, 0)?; \
                expect_token(tokens, pos, |t| matches!(t, Token::Comma), \",\")?; \
                let mut args: Vec<{dom}> = Vec::new(); \
                loop {{ \
                    let arg = parse_{dom}(tokens, pos, 0)?; \
                    args.push(arg); \
                    if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::Comma)) {{ \
                        *pos += 1; \
                    }} else {{ \
                        break; \
                    }} \
                }} \
                expect_token(tokens, pos, |t| matches!(t, Token::RParen), \")\")?; \
                Ok({cat}::{mapply_variant}(Box::new(f), args)) \
            }}",
        )
        .unwrap();

        handlers.push(PrefixHandler {
            category: cat.to_string(),
            label: format!("Ddollar{}Lp", dom_capitalized),
            match_arm: format!(
                "Token::{} => {{ {}(tokens, pos) }}",
                ddollar_variant, multi_fn
            ),
            ident_lookahead: None,
            parse_fn_name: multi_fn,
        });
    }

    handlers
}

/// Write lambda parsing support (for the primary category).
pub fn write_lambda_handlers(
    buf: &mut String,
    primary_category: &str,
    _all_categories: &[String],
) -> Vec<PrefixHandler> {
    let cat = primary_category;
    let default_lam_variant = format!("Lam{}", cat);
    let default_mlam_variant = format!("MLam{}", cat);

    let handlers = vec![
        // Single lambda: ^x.{body}
        PrefixHandler {
            category: cat.to_string(),
            label: "Lambda".to_string(),
            match_arm: "Token::Caret => { parse_lambda(tokens, pos) }".to_string(),
            ident_lookahead: None,
            parse_fn_name: "parse_lambda".to_string(),
        },
    ];

    // Write the parse_lambda function
    write!(
        buf,
        "fn parse_lambda<'a>(\
            tokens: &[(Token<'a>, Span)], \
            pos: &mut usize, \
        ) -> Result<{cat}, ParseError> {{ \
            expect_token(tokens, pos, |t| matches!(t, Token::Caret), \"^\")?; \
            match peek_token(tokens, *pos) {{ \
                Some(Token::LBracket) => {{ \
                    *pos += 1; \
                    let mut binder_names = Vec::new(); \
                    loop {{ \
                        let name = expect_ident(tokens, pos)?; \
                        binder_names.push(name); \
                        if peek_token(tokens, *pos).map_or(false, |t| matches!(t, Token::Comma)) {{ \
                            *pos += 1; \
                        }} else {{ \
                            break; \
                        }} \
                    }} \
                    expect_token(tokens, pos, |t| matches!(t, Token::RBracket), \"]\")?; \
                    expect_token(tokens, pos, |t| matches!(t, Token::Dot), \".\")?; \
                    expect_token(tokens, pos, |t| matches!(t, Token::LBrace), \"{{\")?; \
                    let body = parse_{cat}(tokens, pos, 0)?; \
                    expect_token(tokens, pos, |t| matches!(t, Token::RBrace), \"}}\")?; \
                    let _inferred = if let Some(name) = binder_names.first() {{ \
                        body.infer_var_type(name) \
                    }} else {{ \
                        None \
                    }}; \
                    let binders: Vec<mettail_runtime::Binder<String>> = \
                        binder_names.into_iter() \
                            .map(|s| mettail_runtime::Binder(mettail_runtime::get_or_create_var(s))) \
                            .collect(); \
                    Ok({cat}::{default_mlam_variant}(mettail_runtime::Scope::new( \
                        binders, \
                        Box::new(body), \
                    ))) \
                }} \
                Some(Token::Ident(_)) => {{ \
                    let binder_name = expect_ident(tokens, pos)?; \
                    expect_token(tokens, pos, |t| matches!(t, Token::Dot), \".\")?; \
                    expect_token(tokens, pos, |t| matches!(t, Token::LBrace), \"{{\")?; \
                    let body = parse_{cat}(tokens, pos, 0)?; \
                    expect_token(tokens, pos, |t| matches!(t, Token::RBrace), \"}}\")?; \
                    let _inferred = body.infer_var_type(&binder_name); \
                    Ok({cat}::{default_lam_variant}(mettail_runtime::Scope::new( \
                        mettail_runtime::Binder(mettail_runtime::get_or_create_var(binder_name)), \
                        Box::new(body), \
                    ))) \
                }} \
                _ => {{ \
                    Err(ParseError::UnexpectedToken {{ \
                        expected: \"identifier or '['\", \
                        found: format!(\"{{:?}}\", tokens[*pos].0), \
                        range: tokens[*pos].1, \
                    }}) \
                }} \
            }} \
        }}",
    )
    .unwrap();

    handlers
}
