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

use std::collections::BTreeMap;
use std::fmt::Write;

use crate::automata::codegen::TokenVariantMap;
use crate::binding_power::BindingPowerTable;
use crate::dispatch::CastRule;
use crate::prediction::FirstSet;

/// BP03: Minimum number of operators in a category before the static array
/// lookup optimization is applied.  Below this threshold, the match-based
/// dispatch is typically faster because the compiler can emit a small jump
/// table directly.
pub const BP_TABLE_LOOKUP_THRESHOLD: usize = 8;

/// BP03: Configuration for static BP array lookup optimization.
///
/// When the optimization gate is enabled and a category has enough operators
/// (>= [`BP_TABLE_LOOKUP_THRESHOLD`]), the generated `infix_bp_*` / `postfix_bp_*` /
/// `mixfix_bp_*` functions use a `static` array indexed by `token_variant_id()`
/// instead of a `match` with per-operator arms.
///
/// The caller must ensure that `write_token_variant_id()` has been emitted
/// earlier in the generated code so the `token_variant_id()` function is in scope.
#[derive(Debug, Clone)]
pub struct BpTableConfig<'a> {
    /// The token variant map from lexer codegen — provides variant name → ordinal.
    pub variant_map: &'a TokenVariantMap,
    /// Whether the BP03 gate is enabled.
    pub enabled: bool,
}

/// BP05: Binding power range analysis result for a category.
///
/// When all infix (and optionally postfix/mixfix) operators have left binding
/// powers in a range [lo, hi] with `hi - lo <= 16`, the Pratt infix loop can
/// use a compact `u16` bitset for an early-exit guard: if no operator has
/// `left_bp >= cur_bp`, the loop breaks immediately without calling `infix_bp_*`.
///
/// The bitset has bit `i` set iff there exists an operator with `left_bp == lo + i`.
/// The guard check is: `ACTIVE_BP >> cur_bp.saturating_sub(lo) != 0`.
/// When this is zero, all active BPs are below `cur_bp`, and no operator can bind.
#[derive(Debug, Clone, Copy)]
pub struct BpRangeInfo {
    /// Minimum left_bp across all operators in this category.
    pub lo: u8,
    /// Maximum left_bp across all operators in this category.
    pub hi: u8,
    /// Bitset: bit `i` is set iff some operator has `left_bp == lo + i`.
    pub bitset: u16,
}

/// BP05: Analyze the binding power range for a category.
///
/// Collects all left_bp values from infix, postfix, and mixfix operators.
/// Returns `Some(BpRangeInfo)` if the range fits in 16 bits (hi - lo <= 16)
/// and there is at least one operator; `None` otherwise.
pub fn analyze_bp_range(cat: &str, bp_table: &BindingPowerTable) -> Option<BpRangeInfo> {
    let mut left_bps: Vec<u8> = Vec::new();

    // Collect left_bp from all operator types
    for op in bp_table.operators_for_category(cat) {
        left_bps.push(op.left_bp);
    }
    for op in bp_table.postfix_operators_for_category(cat) {
        left_bps.push(op.left_bp);
    }
    for op in bp_table.mixfix_operators_for_category(cat) {
        left_bps.push(op.left_bp);
    }

    if left_bps.is_empty() {
        return None;
    }

    let lo = *left_bps.iter().min().expect("non-empty left_bps");
    let hi = *left_bps.iter().max().expect("non-empty left_bps");

    // Range must fit in 16 bits
    if (hi as u16).saturating_sub(lo as u16) > 15 {
        return None;
    }

    // Build the bitset
    let mut bitset: u16 = 0;
    for &bp in &left_bps {
        bitset |= 1u16 << (bp - lo);
    }

    Some(BpRangeInfo { lo, hi, bitset })
}

/// BP05: Emit a static `ACTIVE_BP_{CAT}` constant and its `lo` value.
///
/// Generates:
/// ```rust,ignore
/// const ACTIVE_BP_CAT: u16 = 0b...;
/// const BP_LO_CAT: u8 = lo;
/// ```
///
/// The trampoline infix loop uses these for an early-exit guard:
/// `if (ACTIVE_BP_CAT >> cur_bp.saturating_sub(BP_LO_CAT)) == 0 { break; }`
pub fn write_bp_range_constants(buf: &mut String, cat: &str, info: &BpRangeInfo) {
    let cat_upper = cat.to_uppercase();
    write!(
        buf,
        "const ACTIVE_BP_{cat_upper}: u16 = 0b{bitset:016b}; \
         const BP_LO_{cat_upper}: u8 = {lo};",
        bitset = info.bitset,
        lo = info.lo,
    )
    .unwrap();
}

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

    if items.len() <= 6 {
        format!("{} expression (one of: {})", category, items.join(", "))
    } else if items.len() <= 10 {
        // Show all items for moderate-length lists
        format!("{} expression (one of: {})", category, items.join(", "))
    } else {
        // For very long lists, show first 6 and count
        format!(
            "{} expression (one of: {}, ... [{} options])",
            category,
            items[..6].join(", "),
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
    pub all_first_sets: std::collections::HashMap<String, FirstSet>,
    /// FOLLOW set for this category — tokens that can appear after a complete expression.
    /// Used for error messages ("expected one of: ...") and sync point selection.
    pub follow_set: FirstSet,
    /// LED delegation sources for sum-type categories.
    ///
    /// When non-empty, the LED chain falls back to delegating to constituent categories'
    /// operators when the sum type's own BP tables don't match the current token.
    pub led_delegation: Vec<LedDelegationSource>,
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
    let has_led = config.has_infix || config.has_postfix || config.has_mixfix
        || !config.led_delegation.is_empty();

    if has_led {
        // Generate helper functions for each operator type
        // Note: write_pratt_parser is the legacy (non-trampoline) path; BP03 array
        // lookup is not applied here (pass None). The trampoline path uses _pub
        // variants which receive the BpTableConfig.
        if config.has_infix {
            write_bp_function(buf, config, bp_table, None);
            write_make_infix(buf, config, bp_table);
        }
        if config.has_postfix {
            write_postfix_bp_function(buf, config, bp_table, None);
            write_make_postfix(buf, config, bp_table);
        }
        if config.has_mixfix {
            write_mixfix_bp_function(buf, config, bp_table, None);
            write_handle_mixfix(buf, config, bp_table);
        }

        // Build the led handler chain
        write!(
            buf,
            "fn {parse_fn}<'a>(\
                tokens: &[(Token<'a>, Range)], \
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
                tokens: &[(Token<'a>, Range)], \
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

    // LED delegation fallback
    let has_delegation = !config.led_delegation.is_empty();
    if has_delegation {
        if wrote_first {
            buf.push_str(" else ");
        }
        write!(
            buf,
            "{{ match led_delegate_{cat}(tokens, pos, &lhs) {{ \
                Some(new_lhs) => {{ lhs = new_lhs; }} \
                None => {{ break; }} \
            }} }}",
        )
        .unwrap();
    } else if wrote_first {
        buf.push_str(" else { break; }");
    } else {
        buf.push_str("break;");
    }
}

/// Write the binding power lookup function.
///
/// When `bp_cfg` is provided and enabled, and the category has enough operators
/// (>= `BP_TABLE_LOOKUP_THRESHOLD`), emits a static array indexed by
/// `token_variant_id()` instead of a match with per-operator arms.
fn write_bp_function(
    buf: &mut String,
    config: &PrattConfig,
    bp_table: &BindingPowerTable,
    bp_cfg: Option<&BpTableConfig>,
) {
    let cat = &config.category;
    let ops = bp_table.operators_for_category(cat);

    if let Some(cfg) = bp_cfg {
        if cfg.enabled && ops.len() >= BP_TABLE_LOOKUP_THRESHOLD {
            write_bp_function_array(buf, cat, &ops, cfg.variant_map);
            return;
        }
    }

    // Fallback: match-based dispatch
    write_bp_function_match(buf, cat, &ops);
}

/// Write a match-based `infix_bp_*` function (the original codegen path).
fn write_bp_function_match(
    buf: &mut String,
    cat: &str,
    ops: &[&crate::binding_power::InfixOperator],
) {
    write!(
        buf,
        "fn infix_bp_{cat}<'a>(token: &Token<'a>) -> Option<(u8, u8)> {{ match token {{"
    )
    .unwrap();

    // Group operators by (left_bp, right_bp) pair to emit compact match arms
    let mut bp_groups: BTreeMap<(u8, u8), Vec<String>> = BTreeMap::new();
    for op in ops {
        let variant = crate::automata::codegen::terminal_to_variant_name(&op.terminal);
        bp_groups
            .entry((op.left_bp, op.right_bp))
            .or_default()
            .push(format!("Token::{}", variant));
    }
    for ((left, right), tokens) in &bp_groups {
        let pattern = tokens.join(" | ");
        write!(buf, "{} => Some(({}, {})),", pattern, left, right).unwrap();
    }

    buf.push_str("_ => None } }");
}

/// BP03: Write a static-array-based `infix_bp_*` function.
///
/// Generates:
/// ```rust,ignore
/// static INFIX_BP_Cat: [(u8, u8); N] = [(0,0), ..., (left, right), ...];
/// fn infix_bp_Cat<'a>(token: &Token<'a>) -> Option<(u8, u8)> {
///     let bp = INFIX_BP_Cat[token_variant_id(token) as usize];
///     if bp != (0, 0) { Some(bp) } else { None }
/// }
/// ```
fn write_bp_function_array(
    buf: &mut String,
    cat: &str,
    ops: &[&crate::binding_power::InfixOperator],
    variant_map: &TokenVariantMap,
) {
    let array_len = variant_map.count as usize;
    let cat_upper = cat.to_uppercase();

    // Build the array initializer: (0,0) for all slots, then fill operator slots
    let mut entries = vec![(0u8, 0u8); array_len];
    for op in ops {
        let variant_name = crate::automata::codegen::terminal_to_variant_name(&op.terminal);
        if let Some(id) = variant_map.get_id(&variant_name) {
            entries[id as usize] = (op.left_bp, op.right_bp);
        }
    }

    // Emit the static array
    write!(buf, "static INFIX_BP_{}: [(u8, u8); {}] = [", cat_upper, array_len).unwrap();
    for (i, (l, r)) in entries.iter().enumerate() {
        if i > 0 {
            buf.push(',');
        }
        write!(buf, "({},{})", l, r).unwrap();
    }
    buf.push_str("];");

    // Emit the lookup function
    write!(
        buf,
        "#[inline] fn infix_bp_{cat}<'a>(token: &Token<'a>) -> Option<(u8, u8)> {{ \
            let bp = INFIX_BP_{cat_upper}[token_variant_id(token) as usize]; \
            if bp != (0, 0) {{ Some(bp) }} else {{ None }} \
        }}",
    )
    .unwrap();
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
///
/// When `bp_cfg` is provided and enabled, and the category has enough postfix
/// operators (>= `BP_TABLE_LOOKUP_THRESHOLD`), emits a static array indexed by
/// `token_variant_id()`.
fn write_postfix_bp_function(
    buf: &mut String,
    config: &PrattConfig,
    bp_table: &BindingPowerTable,
    bp_cfg: Option<&BpTableConfig>,
) {
    let cat = &config.category;
    let ops = bp_table.postfix_operators_for_category(cat);

    if let Some(cfg) = bp_cfg {
        if cfg.enabled && ops.len() >= BP_TABLE_LOOKUP_THRESHOLD {
            write_postfix_bp_function_array(buf, cat, &ops, cfg.variant_map);
            return;
        }
    }

    // Fallback: match-based dispatch
    write_postfix_bp_function_match(buf, cat, &ops);
}

/// Write a match-based `postfix_bp_*` function.
fn write_postfix_bp_function_match(
    buf: &mut String,
    cat: &str,
    ops: &[&crate::binding_power::InfixOperator],
) {
    write!(
        buf,
        "fn postfix_bp_{cat}<'a>(token: &Token<'a>) -> Option<u8> {{ match token {{"
    )
    .unwrap();

    // Group postfix operators by left_bp to emit compact match arms
    let mut bp_groups: BTreeMap<u8, Vec<String>> = BTreeMap::new();
    for op in ops {
        let variant = crate::automata::codegen::terminal_to_variant_name(&op.terminal);
        bp_groups
            .entry(op.left_bp)
            .or_default()
            .push(format!("Token::{}", variant));
    }
    for (left_bp, tokens) in &bp_groups {
        let pattern = tokens.join(" | ");
        write!(buf, "{} => Some({}),", pattern, left_bp).unwrap();
    }

    buf.push_str("_ => None } }");
}

/// BP03: Write a static-array-based `postfix_bp_*` function.
///
/// Sentinel value `0` means "not a postfix operator for this category".
/// This is safe because real postfix BPs are always > 0 (typically >= 4).
fn write_postfix_bp_function_array(
    buf: &mut String,
    cat: &str,
    ops: &[&crate::binding_power::InfixOperator],
    variant_map: &TokenVariantMap,
) {
    let array_len = variant_map.count as usize;
    let cat_upper = cat.to_uppercase();

    let mut entries = vec![0u8; array_len];
    for op in ops {
        let variant_name = crate::automata::codegen::terminal_to_variant_name(&op.terminal);
        if let Some(id) = variant_map.get_id(&variant_name) {
            entries[id as usize] = op.left_bp;
        }
    }

    // Emit the static array
    write!(buf, "static POSTFIX_BP_{}: [u8; {}] = [", cat_upper, array_len).unwrap();
    for (i, bp) in entries.iter().enumerate() {
        if i > 0 {
            buf.push(',');
        }
        write!(buf, "{}", bp).unwrap();
    }
    buf.push_str("];");

    // Emit the lookup function
    write!(
        buf,
        "#[inline] fn postfix_bp_{cat}<'a>(token: &Token<'a>) -> Option<u8> {{ \
            let bp = POSTFIX_BP_{cat_upper}[token_variant_id(token) as usize]; \
            if bp != 0 {{ Some(bp) }} else {{ None }} \
        }}",
    )
    .unwrap();
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
///
/// When `bp_cfg` is provided and enabled, and the category has enough mixfix
/// operators (>= `BP_TABLE_LOOKUP_THRESHOLD`), emits a static array indexed by
/// `token_variant_id()`.
fn write_mixfix_bp_function(
    buf: &mut String,
    config: &PrattConfig,
    bp_table: &BindingPowerTable,
    bp_cfg: Option<&BpTableConfig>,
) {
    let cat = &config.category;
    let ops = bp_table.mixfix_operators_for_category(cat);

    if let Some(cfg) = bp_cfg {
        if cfg.enabled && ops.len() >= BP_TABLE_LOOKUP_THRESHOLD {
            write_mixfix_bp_function_array(buf, cat, &ops, cfg.variant_map);
            return;
        }
    }

    // Fallback: match-based dispatch
    write_mixfix_bp_function_match(buf, cat, &ops);
}

/// Write a match-based `mixfix_bp_*` function.
fn write_mixfix_bp_function_match(
    buf: &mut String,
    cat: &str,
    ops: &[&crate::binding_power::InfixOperator],
) {
    write!(
        buf,
        "fn mixfix_bp_{cat}<'a>(token: &Token<'a>) -> Option<(u8, u8)> {{ match token {{",
    )
    .unwrap();

    // Group mixfix operators by (left_bp, right_bp) pair to emit compact match arms
    let mut bp_groups: BTreeMap<(u8, u8), Vec<String>> = BTreeMap::new();
    for op in ops {
        let variant = crate::automata::codegen::terminal_to_variant_name(&op.terminal);
        bp_groups
            .entry((op.left_bp, op.right_bp))
            .or_default()
            .push(format!("Token::{}", variant));
    }
    for ((left, right), tokens) in &bp_groups {
        let pattern = tokens.join(" | ");
        write!(buf, "{} => Some(({}, {})),", pattern, left, right).unwrap();
    }

    buf.push_str("_ => None } }");
}

/// BP03: Write a static-array-based `mixfix_bp_*` function.
///
/// Uses the same `(u8, u8)` pair layout as `write_bp_function_array` with
/// `(0, 0)` as sentinel.
fn write_mixfix_bp_function_array(
    buf: &mut String,
    cat: &str,
    ops: &[&crate::binding_power::InfixOperator],
    variant_map: &TokenVariantMap,
) {
    let array_len = variant_map.count as usize;
    let cat_upper = cat.to_uppercase();

    let mut entries = vec![(0u8, 0u8); array_len];
    for op in ops {
        let variant_name = crate::automata::codegen::terminal_to_variant_name(&op.terminal);
        if let Some(id) = variant_map.get_id(&variant_name) {
            entries[id as usize] = (op.left_bp, op.right_bp);
        }
    }

    // Emit the static array
    write!(buf, "static MIXFIX_BP_{}: [(u8, u8); {}] = [", cat_upper, array_len).unwrap();
    for (i, (l, r)) in entries.iter().enumerate() {
        if i > 0 {
            buf.push(',');
        }
        write!(buf, "({},{})", l, r).unwrap();
    }
    buf.push_str("];");

    // Emit the lookup function
    write!(
        buf,
        "#[inline] fn mixfix_bp_{cat}<'a>(token: &Token<'a>) -> Option<(u8, u8)> {{ \
            let bp = MIXFIX_BP_{cat_upper}[token_variant_id(token) as usize]; \
            if bp != (0, 0) {{ Some(bp) }} else {{ None }} \
        }}",
    )
    .unwrap();
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
            tokens: &[(Token<'a>, Range)], \
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
                            expected: Cow::Borrowed(\"{cat} expression\"), \
                            found: format_token_friendly(&tokens[nfa_saved].0), \
                            range: tokens[nfa_saved].1, \
                            hint: None, \
                        }} \
                    )),",
                )
                .unwrap();
                arm.push_str("_ => { *pos = nfa_positions[0]; Ok(nfa_results.into_iter().next().expect(\"nfa_results non-empty\")) },");
                arm.push('}'); // close match
                arm.push('}'); // close arm body
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

    // Add cast rule prefix arms (use source_first directly, not difference:
    // the target's own_first includes cast source tokens precisely because of the
    // cast rule, so difference would be empty and we'd miss the arm).
    //
    // Track tokens already emitted by earlier match_arms AND across cast sources
    // to prevent duplicate match arms (e.g., Ident in every source's FIRST set).
    {
        use std::collections::BTreeSet;
        let mut cast_handled: BTreeSet<String> = BTreeSet::new();

        // Collect tokens already in match_arms (from RD handlers, native literals, grouping)
        for arm in &match_arms {
            if let Some(idx) = arm.find(" => ") {
                let pattern = &arm[..idx];
                let variant = pattern
                    .strip_prefix("Token::")
                    .unwrap_or(pattern)
                    .trim_end_matches("(_)")
                    .trim_end_matches("(v)")
                    .to_string();
                cast_handled.insert(variant);
            }
        }

        for cast_rule in &config.cast_rules {
            if let Some(source_first) = config.all_first_sets.get(&cast_rule.source_category) {
                for token in &source_first.tokens {
                    // Skip Ident — the variable fallback handles identifiers at the
                    // target category level (prevents hijacking into a single constituent).
                    if token == "Ident" {
                        continue;
                    }
                    if cast_handled.contains(token) {
                        continue;
                    }
                    cast_handled.insert(token.clone());

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
                expected: Cow::Borrowed(\"{expected_escaped}\"), \
                found: format_token_friendly(other), \
                range: tokens[*pos].1, \
                hint: Some(Cow::Borrowed(\"this token cannot start a {cat} expression\")), \
            }}) \
        }}",
    ));

    // Write the prefix function
    write!(
        buf,
        "fn parse_{cat}_prefix<'a>(\
            tokens: &[(Token<'a>, Range)], \
            pos: &mut usize, \
        ) -> Result<{cat}, ParseError> {{ \
            if *pos >= tokens.len() {{ \
                let eof_range = tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()); \
                return Err(ParseError::UnexpectedEof {{ \
                    expected: Cow::Borrowed(\"{expected_escaped}\"), \
                    range: eof_range, \
                    hint: None, \
                }}); \
            }} \
            match &tokens[*pos].0 {{ {arms} }} \
        }}",
        arms = match_arms.join(","),
    )
    .unwrap();
}

/// LED delegation info for one constituent of a sum-type category.
///
/// When a sum-type category (e.g., `Proc` with cast rules from `Int`, `Float`, `Bool`, `Str`)
/// parses an expression and the Pratt LED chain encounters a token NOT in the sum type's own
/// BP tables, the parser delegates to the constituent's operators.
#[derive(Debug, Clone)]
pub struct LedDelegationSource {
    /// Cast label wrapping source INTO sum type (e.g., "CastInt").
    pub cast_label: String,
    /// Source category name (e.g., "Int").
    pub source_category: String,
    /// Whether source has same-category infix operators.
    pub has_infix: bool,
    /// Whether source has postfix operators.
    pub has_postfix: bool,
    /// Whether source has mixfix operators.
    pub has_mixfix: bool,
    /// Cross-category operators FROM this source.
    pub cross_cat_ops: Vec<CrossCatLedOp>,
    /// Label of the projection rule sum_type → source (e.g., "ProcToInt").
    /// None if no projection exists for this constituent. Used by Phase 2 auto-projection.
    pub projection_label: Option<String>,
}

/// A cross-category LED operator from a constituent.
///
/// Used by LED delegation to handle operators like `==`, `>`, `<` that operate on a
/// constituent type but produce a result in a different category. The result is re-wrapped
/// into the sum type via the `rewrap_label` cast.
#[derive(Debug, Clone)]
pub struct CrossCatLedOp {
    /// Terminal text (e.g., "==").
    pub terminal: String,
    /// Result category (e.g., "Bool").
    pub result_category: String,
    /// Constructor label (e.g., "EqInt").
    pub label: String,
    /// Cast label wrapping result category INTO sum type (e.g., "CastBool").
    pub rewrap_label: String,
    /// Left binding power.
    pub left_bp: u8,
    /// Right binding power.
    pub right_bp: u8,
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
            tokens: &[(Token<'a>, Range)], \
            pos: &mut usize, \
            predicate: impl Fn(&Token) -> bool, \
            expected: &'static str, \
        ) -> Result<(), ParseError> { \
            if *pos >= tokens.len() { \
                let eof_range = tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()); \
                return Err(ParseError::UnexpectedEof { expected: Cow::Borrowed(expected), range: eof_range, hint: None }); \
            } \
            if predicate(&tokens[*pos].0) { \
                *pos += 1; \
                Ok(()) \
            } else { \
                Err(ParseError::UnexpectedToken { \
                    expected: Cow::Borrowed(expected), \
                    found: format_token_friendly(&tokens[*pos].0), \
                    range: tokens[*pos].1, \
                    hint: None, \
                }) \
            } \
        }\n\
        fn expect_ident<'a>(tokens: &[(Token<'a>, Range)], pos: &mut usize) -> Result<String, ParseError> { \
            if *pos >= tokens.len() { \
                let eof_range = tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()); \
                return Err(ParseError::UnexpectedEof { expected: Cow::Borrowed(\"identifier\"), range: eof_range, hint: None }); \
            } \
            match &tokens[*pos].0 { \
                Token::Ident(name) => { \
                    let result = name.to_string(); \
                    *pos += 1; \
                    Ok(result) \
                } \
                other => { \
                    Err(ParseError::UnexpectedToken { \
                        expected: Cow::Borrowed(\"identifier\"), \
                        found: format_token_friendly(other), \
                        range: tokens[*pos].1, \
                        hint: Some(Cow::Borrowed(\"expected a variable name, not a keyword or operator\")), \
                    }) \
                } \
            } \
        }\n\
        fn peek_token<'a, 'b>(tokens: &'b [(Token<'a>, Range)], pos: usize) -> Option<&'b Token<'a>> { \
            tokens.get(pos).map(|(t, _)| t) \
        }\n\
        fn peek_ahead<'a, 'b>(tokens: &'b [(Token<'a>, Range)], pos: usize, offset: usize) -> Option<&'b Token<'a>> { \
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
            tokens: &[(Token<'a>, Range)], \
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
            tokens: &[(Token<'a>, Range)], \
            pos: &mut usize, \
            predicate: impl Fn(&Token) -> bool, \
            expected: &'static str, \
            errors: &mut Vec<ParseError>, \
        ) -> bool { \
            if *pos >= tokens.len() { \
                let eof_range = tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()); \
                errors.push(ParseError::UnexpectedEof { expected: Cow::Borrowed(expected), range: eof_range, hint: None }); \
                return false; \
            } \
            if predicate(&tokens[*pos].0) { \
                *pos += 1; \
                true \
            } else { \
                errors.push(ParseError::UnexpectedToken { \
                    expected: Cow::Borrowed(expected), \
                    found: format_token_friendly(&tokens[*pos].0), \
                    range: tokens[*pos].1, \
                    hint: None, \
                }); \
                false \
            } \
        }\n\
        // expect_ident_rec: on mismatch, push error and return placeholder.
        fn expect_ident_rec<'a>(\
            tokens: &[(Token<'a>, Range)], \
            pos: &mut usize, \
            errors: &mut Vec<ParseError>, \
        ) -> String { \
            if *pos >= tokens.len() { \
                let eof_range = tokens.last().map(|(_, r)| *r).unwrap_or(Range::zero()); \
                errors.push(ParseError::UnexpectedEof { expected: Cow::Borrowed(\"identifier\"), range: eof_range, hint: None }); \
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
                        expected: Cow::Borrowed(\"identifier\"), \
                        found: format_token_friendly(other), \
                        range: tokens[*pos].1, \
                        hint: Some(Cow::Borrowed(\"expected a variable name, not a keyword or operator\")), \
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

    let has_led = config.has_infix || config.has_postfix || config.has_mixfix
        || !config.led_delegation.is_empty();

    write!(
        buf,
        "fn {parse_fn}<'a>(\
            tokens: &[(Token<'a>, Range)], \
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

    // LED delegation fallback (recovering)
    let has_delegation = !config.led_delegation.is_empty();
    if has_delegation {
        if wrote_first {
            buf.push_str(" else ");
        }
        write!(
            buf,
            "{{ match led_delegate_{cat}(tokens, pos, &lhs) {{ \
                Some(new_lhs) => {{ lhs = new_lhs; }} \
                None => {{ break; }} \
            }} }}",
        )
        .unwrap();
    } else if wrote_first {
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
            tokens: &[(Token<'a>, Range)], \
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
///
/// When `bp_cfg` is `Some` and enabled with enough operators, emits a BP03
/// static array lookup; otherwise falls back to the match-based path.
pub fn write_bp_function_pub(
    buf: &mut String,
    cat: &str,
    bp_table: &BindingPowerTable,
    bp_cfg: Option<&BpTableConfig>,
) {
    let ops = bp_table.operators_for_category(cat);

    if let Some(cfg) = bp_cfg {
        if cfg.enabled && ops.len() >= BP_TABLE_LOOKUP_THRESHOLD {
            write_bp_function_array(buf, cat, &ops, cfg.variant_map);
            return;
        }
    }

    write_bp_function_match(buf, cat, &ops);
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
///
/// When `bp_cfg` is `Some` and enabled with enough operators, emits a BP03
/// static array lookup; otherwise falls back to the match-based path.
pub fn write_postfix_bp_function_pub(
    buf: &mut String,
    cat: &str,
    bp_table: &BindingPowerTable,
    bp_cfg: Option<&BpTableConfig>,
) {
    let ops = bp_table.postfix_operators_for_category(cat);

    if let Some(cfg) = bp_cfg {
        if cfg.enabled && ops.len() >= BP_TABLE_LOOKUP_THRESHOLD {
            write_postfix_bp_function_array(buf, cat, &ops, cfg.variant_map);
            return;
        }
    }

    write_postfix_bp_function_match(buf, cat, &ops);
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
///
/// When `bp_cfg` is `Some` and enabled with enough operators, emits a BP03
/// static array lookup; otherwise falls back to the match-based path.
pub fn write_mixfix_bp_function_pub(
    buf: &mut String,
    cat: &str,
    bp_table: &BindingPowerTable,
    bp_cfg: Option<&BpTableConfig>,
) {
    let ops = bp_table.mixfix_operators_for_category(cat);

    if let Some(cfg) = bp_cfg {
        if cfg.enabled && ops.len() >= BP_TABLE_LOOKUP_THRESHOLD {
            write_mixfix_bp_function_array(buf, cat, &ops, cfg.variant_map);
            return;
        }
    }

    write_mixfix_bp_function_match(buf, cat, &ops);
}

/// Public wrapper: write handle_mixfix function (for trampoline LED delegation codegen).
///
/// Generates a standalone `handle_mixfix_{cat}` function that can be called from
/// LED delegation code. This is needed because the trampoline normally handles mixfix
/// via frame variants, not standalone functions.
pub fn write_handle_mixfix_pub(buf: &mut String, cat: &str, bp_table: &BindingPowerTable) {
    let parse_fn = format!("parse_{}", cat);

    write!(
        buf,
        "fn handle_mixfix_{cat}<'a>(\
            trigger: &Token<'a>, \
            lhs: {cat}, \
            tokens: &[(Token<'a>, Range)], \
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

        write!(buf, "Ok({}::{}(Box::new(lhs)", cat, op.label).unwrap();
        for p in &param_names {
            write!(buf, ", Box::new({})", p).unwrap();
        }
        buf.push_str("))},");
    }

    buf.push_str("_ => unreachable!(\"handle_mixfix called with non-mixfix trigger\") } }");
}

/// Public wrapper: build expected message from FIRST set (for trampoline codegen).
pub fn build_expected_message_pub(category: &str, first_set: &FirstSet) -> String {
    build_expected_message(category, first_set)
}

/// Public wrapper: write token match pattern (for trampoline codegen).
pub fn write_token_pattern_pub(buf: &mut String, token: &str) {
    write_token_pattern(buf, token);
}

// ══════════════════════════════════════════════════════════════════════════════
// Tests
// ══════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use crate::automata::codegen::TokenVariantMap;
    use crate::binding_power::{
        analyze_binding_powers, Associativity, InfixRuleInfo,
    };

    /// Build a `TokenVariantMap` for a typical test grammar with many operators.
    fn test_variant_map() -> TokenVariantMap {
        let map = TokenVariantMap::from_token_kinds(&[
            crate::automata::TokenKind::Eof,
            crate::automata::TokenKind::Ident,
            crate::automata::TokenKind::Integer,
            crate::automata::TokenKind::Fixed("+".to_string()),
            crate::automata::TokenKind::Fixed("-".to_string()),
            crate::automata::TokenKind::Fixed("*".to_string()),
            crate::automata::TokenKind::Fixed("/".to_string()),
            crate::automata::TokenKind::Fixed("%".to_string()),
            crate::automata::TokenKind::Fixed("==".to_string()),
            crate::automata::TokenKind::Fixed("!=".to_string()),
            crate::automata::TokenKind::Fixed("<".to_string()),
            crate::automata::TokenKind::Fixed(">".to_string()),
            crate::automata::TokenKind::Fixed("<=".to_string()),
            crate::automata::TokenKind::Fixed(">=".to_string()),
            crate::automata::TokenKind::Fixed("&&".to_string()),
            crate::automata::TokenKind::Fixed("||".to_string()),
            crate::automata::TokenKind::Fixed("^".to_string()),
            crate::automata::TokenKind::Fixed("(".to_string()),
            crate::automata::TokenKind::Fixed(")".to_string()),
        ]);
        // Ensure deterministic IDs
        map
    }

    /// Create infix rules for an expression language with many operators.
    fn many_infix_rules() -> Vec<InfixRuleInfo> {
        let ops = vec![
            ("Add", "+", "Int"),
            ("Sub", "-", "Int"),
            ("Mul", "*", "Int"),
            ("Div", "/", "Int"),
            ("Mod", "%", "Int"),
            ("Eq", "==", "Int"),
            ("Ne", "!=", "Int"),
            ("Lt", "<", "Int"),
            ("Gt", ">", "Int"),
            ("Le", "<=", "Int"),
            ("Ge", ">=", "Int"),
            ("And", "&&", "Int"),
            ("Or", "||", "Int"),
            ("Xor", "^", "Int"),
        ];
        ops.into_iter()
            .map(|(label, terminal, cat)| InfixRuleInfo {
                label: label.to_string(),
                terminal: terminal.to_string(),
                category: cat.to_string(),
                result_category: cat.to_string(),
                associativity: Associativity::Left,
                is_cross_category: false,
                is_postfix: false,
                is_mixfix: false,
                mixfix_parts: Vec::new(),
            })
            .collect()
    }

    #[test]
    fn test_bp03_array_emitted_above_threshold() {
        // 14 operators > 8 threshold → should emit static array
        let rules = many_infix_rules();
        let bp_table = analyze_binding_powers(&rules);
        let variant_map = test_variant_map();

        let bp_cfg = BpTableConfig {
            variant_map: &variant_map,
            enabled: true,
        };

        let mut buf = String::new();
        let ops = bp_table.operators_for_category("Int");
        assert!(
            ops.len() >= BP_TABLE_LOOKUP_THRESHOLD,
            "test expects >= {} ops, got {}",
            BP_TABLE_LOOKUP_THRESHOLD,
            ops.len()
        );

        write_bp_function_pub(&mut buf, "Int", &bp_table, Some(&bp_cfg));

        // Should contain "static INFIX_BP_INT" (array) and "token_variant_id"
        assert!(
            buf.contains("static INFIX_BP_INT"),
            "expected static array, got:\n{}",
            buf
        );
        assert!(
            buf.contains("token_variant_id"),
            "expected token_variant_id call, got:\n{}",
            buf
        );
        // Should NOT contain "match token" (the fallback path)
        assert!(
            !buf.contains("match token"),
            "should not contain match when using array path, got:\n{}",
            buf
        );
    }

    #[test]
    fn test_bp03_match_emitted_below_threshold() {
        // 3 operators < 8 threshold → should emit match-based fallback
        let rules: Vec<InfixRuleInfo> = vec![
            InfixRuleInfo {
                label: "Add".to_string(),
                terminal: "+".to_string(),
                category: "Int".to_string(),
                result_category: "Int".to_string(),
                associativity: Associativity::Left,
                is_cross_category: false,
                is_postfix: false,
                is_mixfix: false,
                mixfix_parts: Vec::new(),
            },
            InfixRuleInfo {
                label: "Sub".to_string(),
                terminal: "-".to_string(),
                category: "Int".to_string(),
                result_category: "Int".to_string(),
                associativity: Associativity::Left,
                is_cross_category: false,
                is_postfix: false,
                is_mixfix: false,
                mixfix_parts: Vec::new(),
            },
            InfixRuleInfo {
                label: "Mul".to_string(),
                terminal: "*".to_string(),
                category: "Int".to_string(),
                result_category: "Int".to_string(),
                associativity: Associativity::Left,
                is_cross_category: false,
                is_postfix: false,
                is_mixfix: false,
                mixfix_parts: Vec::new(),
            },
        ];
        let bp_table = analyze_binding_powers(&rules);
        let variant_map = test_variant_map();

        let bp_cfg = BpTableConfig {
            variant_map: &variant_map,
            enabled: true,
        };

        let mut buf = String::new();
        let ops = bp_table.operators_for_category("Int");
        assert!(
            ops.len() < BP_TABLE_LOOKUP_THRESHOLD,
            "test expects < {} ops, got {}",
            BP_TABLE_LOOKUP_THRESHOLD,
            ops.len()
        );

        write_bp_function_pub(&mut buf, "Int", &bp_table, Some(&bp_cfg));

        // Should contain "match token" (fallback path)
        assert!(
            buf.contains("match token"),
            "expected match-based dispatch, got:\n{}",
            buf
        );
        // Should NOT contain "static INFIX_BP_INT"
        assert!(
            !buf.contains("static INFIX_BP_INT"),
            "should not contain static array below threshold, got:\n{}",
            buf
        );
    }

    #[test]
    fn test_bp03_disabled_gate_uses_match() {
        // Even with many operators, disabled gate → match
        let rules = many_infix_rules();
        let bp_table = analyze_binding_powers(&rules);
        let variant_map = test_variant_map();

        let bp_cfg = BpTableConfig {
            variant_map: &variant_map,
            enabled: false, // gate disabled
        };

        let mut buf = String::new();
        write_bp_function_pub(&mut buf, "Int", &bp_table, Some(&bp_cfg));

        assert!(
            buf.contains("match token"),
            "disabled gate should use match, got:\n{}",
            buf
        );
        assert!(
            !buf.contains("static INFIX_BP_INT"),
            "disabled gate should not emit static array, got:\n{}",
            buf
        );
    }

    #[test]
    fn test_bp03_none_config_uses_match() {
        // No BpTableConfig → match (backward compatibility)
        let rules = many_infix_rules();
        let bp_table = analyze_binding_powers(&rules);

        let mut buf = String::new();
        write_bp_function_pub(&mut buf, "Int", &bp_table, None);

        assert!(
            buf.contains("match token"),
            "None config should use match, got:\n{}",
            buf
        );
    }

    #[test]
    fn test_bp03_array_entries_correct() {
        // Verify array entries match operator binding powers
        let rules = many_infix_rules();
        let bp_table = analyze_binding_powers(&rules);
        let variant_map = test_variant_map();

        let bp_cfg = BpTableConfig {
            variant_map: &variant_map,
            enabled: true,
        };

        let mut buf = String::new();
        write_bp_function_pub(&mut buf, "Int", &bp_table, Some(&bp_cfg));

        // Verify that each operator's BP pair appears in the static array.
        // The "Add" operator (+) should have some (left, right) pair in the array.
        // Since we can't parse the generated code, just verify the array contains
        // non-zero entries at the correct positions.
        let _plus_id = variant_map.get_id("Plus").expect("Plus should be in variant map");
        let ops = bp_table.operators_for_category("Int");
        let plus_op = ops.iter().find(|op| op.terminal == "+").expect("should have + op");

        // The array string should contain the BP pair
        let bp_str = format!("({},{})", plus_op.left_bp, plus_op.right_bp);
        assert!(
            buf.contains(&bp_str),
            "array should contain BP pair {} for '+', got:\n{}",
            bp_str,
            buf
        );
    }

    #[test]
    fn test_bp03_postfix_array() {
        // Create 8+ postfix operators to trigger array path
        let rules: Vec<InfixRuleInfo> = (0..10)
            .map(|i| InfixRuleInfo {
                label: format!("Post{}", i),
                terminal: format!("op{}", i),
                category: "Expr".to_string(),
                result_category: "Expr".to_string(),
                associativity: Associativity::Left,
                is_cross_category: false,
                is_postfix: true,
                is_mixfix: false,
                mixfix_parts: Vec::new(),
            })
            .collect();
        let bp_table = analyze_binding_powers(&rules);

        // Build a variant map that includes these operator variants
        let mut name_to_id = std::collections::BTreeMap::new();
        let mut id_to_name = Vec::new();
        let mut insert = |name: String| {
            if !name_to_id.contains_key(&name) {
                let id = id_to_name.len() as u8;
                name_to_id.insert(name.clone(), id);
                id_to_name.push(name);
            }
        };
        insert("Eof".to_string());
        insert("Ident".to_string());
        for i in 0..10 {
            let variant = crate::automata::codegen::terminal_to_variant_name(&format!("op{}", i));
            insert(variant);
        }

        let variant_map = TokenVariantMap {
            count: id_to_name.len() as u8,
            name_to_id,
            id_to_name,
        };

        let bp_cfg = BpTableConfig {
            variant_map: &variant_map,
            enabled: true,
        };

        let mut buf = String::new();
        let ops = bp_table.postfix_operators_for_category("Expr");
        assert!(
            ops.len() >= BP_TABLE_LOOKUP_THRESHOLD,
            "test expects >= {} postfix ops, got {}",
            BP_TABLE_LOOKUP_THRESHOLD,
            ops.len()
        );

        write_postfix_bp_function_pub(&mut buf, "Expr", &bp_table, Some(&bp_cfg));

        assert!(
            buf.contains("static POSTFIX_BP_EXPR"),
            "expected static postfix array, got:\n{}",
            buf
        );
        assert!(
            buf.contains("token_variant_id"),
            "expected token_variant_id call, got:\n{}",
            buf
        );
    }

    // ═══════════════════════════════════════════════════════════════════
    // BP05: BP range analysis tests
    // ═══════════════════════════════════════════════════════════════════

    #[test]
    fn test_bp05_analyze_narrow_range() {
        // Two operators with left_bp 2 and 4 — range [2, 4], fits in 16 bits.
        let mut bp_table = BindingPowerTable::new();
        bp_table.operators.push(crate::binding_power::InfixOperator {
            terminal: "+".to_string(),
            category: "Int".to_string(),
            result_category: "Int".to_string(),
            left_bp: 2,
            right_bp: 3,
            label: "Add".to_string(),
            is_cross_category: false,
            is_postfix: false,
            is_mixfix: false,
            mixfix_parts: vec![],
        });
        bp_table.operators.push(crate::binding_power::InfixOperator {
            terminal: "*".to_string(),
            category: "Int".to_string(),
            result_category: "Int".to_string(),
            left_bp: 4,
            right_bp: 5,
            label: "Mul".to_string(),
            is_cross_category: false,
            is_postfix: false,
            is_mixfix: false,
            mixfix_parts: vec![],
        });

        let info = analyze_bp_range("Int", &bp_table);
        assert!(info.is_some(), "narrow range should produce BpRangeInfo");
        let info = info.expect("BpRangeInfo should be Some");
        assert_eq!(info.lo, 2);
        assert_eq!(info.hi, 4);
        // Bit 0 = left_bp 2, bit 2 = left_bp 4
        assert_eq!(info.bitset, 0b101);
    }

    #[test]
    fn test_bp05_analyze_empty_category() {
        let bp_table = BindingPowerTable::new();
        let info = analyze_bp_range("Int", &bp_table);
        assert!(info.is_none(), "no operators should return None");
    }

    #[test]
    fn test_bp05_bitset_constants_emitted() {
        let info = BpRangeInfo {
            lo: 2,
            hi: 6,
            bitset: 0b10101,
        };
        let mut buf = String::new();
        write_bp_range_constants(&mut buf, "Int", &info);
        assert!(buf.contains("ACTIVE_BP_INT"), "should contain ACTIVE_BP constant");
        assert!(buf.contains("BP_LO_INT"), "should contain BP_LO constant");
        assert!(buf.contains("0b0000000000010101"), "bitset should be 0b0000000000010101");
        assert!(buf.contains(": u8 = 2"), "lo should be 2");
    }
}
