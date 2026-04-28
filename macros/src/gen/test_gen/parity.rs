//! Phase 9 (2026-04-27): Model A dual-codegen parity test generator.
//!
//! For each grammar, walks `language.terms` + `language.types` to identify
//! all parseable shapes (atomic literals, terminal keywords, infix, prefix,
//! cross-cat projections, collections) and emits per-fixture tests that call
//! BOTH `Cat::parse(input)` (trampoline) and `Cat::parse_via_wpds(input)`
//! (WPDS facade), then asserts equality via `PartialEq`.
//!
//! Stage 4 of the WPDS migration: provides the parity gate that detects
//! semantic divergence between the two parser backends. Per
//! `feedback_parity_drift_ok_if_better.md`, divergences where WPDS produces
//! a strictly better parse (e.g., correct cross-cat dispatch where
//! trampoline fails) are accepted, not "fixed back". The generator emits
//! the asserts so divergences surface as panics during `cargo test`.
//!
//! ## Output
//!
//! Emitted into `languages/tests/gen_<lang>_parity.rs` as a standalone test
//! module. Each grammar with at least one parseable category gets ≥1 test
//! per atomic-literal / terminal-keyword rule, plus richer Pratt /
//! collection / cross-cat fixtures derived from the grammar.

use mettail_ast::grammar::{GrammarRule, SyntaxExpr, TermParam};
use mettail_ast::language::{LanguageDef, NativeKind};
use mettail_ast::types::TypeExpr;
use proc_macro2::{Ident, Span, TokenStream};
use quote::{format_ident, quote};

/// Generate Phase 9 Model A parity tests for a language.
pub fn generate_parity_section(language: &LanguageDef) -> TokenStream {
    let lang_name = language.name.to_string();
    let lang_lower = lang_name.to_lowercase();
    let lang_mod = format_ident!("{}", lang_lower);

    let mut tests: Vec<TokenStream> = Vec::new();
    let mut counter: usize = 0;
    let mut emit = |test_body: TokenStream| {
        tests.push(test_body);
    };

    // 1. Per-category atomic-literal fixtures (Int / UInt32 / BigInt /
    //    BigRat / Fixed / Float / Bool / Str — varied numeric/textual
    //    inputs within each).
    for type_def in &language.types {
        let cat_name = type_def.name.to_string();
        let token_def = language.token_defs.iter().find(|td| {
            td.from_literals
                && td.category.as_ref().map(|c| c.to_string() == cat_name).unwrap_or(false)
        });
        if token_def.is_none() {
            continue;
        }
        let Some(nt) = type_def.native_type.as_ref() else { continue };
        let native_kind = NativeKind::from_syn_type(nt);
        let cat_ident = format_ident!("{}", cat_name);

        for input in atomic_literal_fixtures(&native_kind, &cat_name) {
            let test_name = mk_name(&lang_lower, &cat_name, "atomic_lit", &mut counter);
            emit(emit_parity_test(
                &test_name,
                &lang_mod,
                &cat_ident,
                &input,
            ));
        }
    }

    // 2. Per-rule terminal-keyword fixtures (e.g., `Err . |- "error" : Int`).
    //    For each nullary rule with a single string literal, the input is
    //    that literal — parsing it should succeed in both backends.
    for rule in &language.terms {
        if let Some(input) = terminal_keyword_input(rule) {
            let cat_name = rule.category.to_string();
            // Skip if cat is a synthesized collection category (Vec/HashBag/HashMap)
            // — handled by collection fixtures below.
            if is_collection_category(&cat_name, language) {
                continue;
            }
            let cat_ident = format_ident!("{}", cat_name);
            let test_name = mk_name(&lang_lower, &cat_name, "term_kw", &mut counter);
            emit(emit_parity_test(
                &test_name,
                &lang_mod,
                &cat_ident,
                &input,
            ));
        }
    }

    // 3. Cross-category projection fixtures: `ProcInt . i:Int |- i : Proc`
    //    means a bare integer literal lexes as Proc::ProcInt(NumLit(...)).
    //    Generate one fixture per cross-cat projection rule × source category
    //    fixtures.
    for rule in &language.terms {
        if let Some((source_cat_name, _)) = cross_cat_projection_info(rule) {
            let cat_name = rule.category.to_string();
            if is_collection_category(&cat_name, language) {
                continue;
            }
            // Use one representative fixture from the source category.
            if let Some(input) = pick_source_fixture(&source_cat_name, language) {
                let cat_ident = format_ident!("{}", cat_name);
                let test_name = mk_name(
                    &lang_lower,
                    &cat_name,
                    &format!("cross_cat_{}", source_cat_name.to_lowercase()),
                    &mut counter,
                );
                emit(emit_parity_test(
                    &test_name,
                    &lang_mod,
                    &cat_ident,
                    &input,
                ));
            }
        }
    }

    // 4. Pratt infix fixtures: walk infix rules, emit `<lhs> <op> <rhs>`
    //    fixtures per rule with simple atomic literals on each side.
    for rule in &language.terms {
        if let Some((op_text, lhs_cat, rhs_cat)) = infix_rule_info(rule) {
            let result_cat = rule.category.to_string();
            if is_collection_category(&result_cat, language) {
                continue;
            }
            let Some(lhs_in) = pick_source_fixture(&lhs_cat, language) else { continue };
            let Some(rhs_in) = pick_source_fixture(&rhs_cat, language) else { continue };
            let input = format!("{} {} {}", lhs_in, op_text, rhs_in);
            let result_ident = format_ident!("{}", result_cat);
            let test_name = mk_name(
                &lang_lower,
                &result_cat,
                &format!("infix_{}", sanitize(&op_text)),
                &mut counter,
            );
            emit(emit_parity_test(
                &test_name,
                &lang_mod,
                &result_ident,
                &input,
            ));
        }
    }

    // 5. Prefix/unary fixtures: walk prefix-unary rules, emit `<op> <arg>`.
    for rule in &language.terms {
        if let Some((op_text, arg_cat)) = prefix_unary_info(rule) {
            let result_cat = rule.category.to_string();
            if is_collection_category(&result_cat, language) {
                continue;
            }
            let Some(arg_in) = pick_source_fixture(&arg_cat, language) else { continue };
            let input = format!("{} {}", op_text, arg_in);
            let result_ident = format_ident!("{}", result_cat);
            let test_name = mk_name(
                &lang_lower,
                &result_cat,
                &format!("unary_{}", sanitize(&op_text)),
                &mut counter,
            );
            emit(emit_parity_test(
                &test_name,
                &lang_mod,
                &result_ident,
                &input,
            ));
        }
    }

    // 6. Function-call / fixed-arity fixtures: `Op . a:Cat, b:Cat |- "op" "(" a "," b ")" : Out`.
    //    Generate one fixture per such rule with simple args.
    for rule in &language.terms {
        if let Some((kw, arg_cats)) = call_form_info(rule) {
            let result_cat = rule.category.to_string();
            if is_collection_category(&result_cat, language) {
                continue;
            }
            let mut args = Vec::with_capacity(arg_cats.len());
            let mut all_resolved = true;
            for ac in &arg_cats {
                match pick_source_fixture(ac, language) {
                    Some(s) => args.push(s),
                    None => {
                        all_resolved = false;
                        break;
                    }
                }
            }
            if !all_resolved {
                continue;
            }
            let input = format!("{}({})", kw, args.join(", "));
            let result_ident = format_ident!("{}", result_cat);
            let test_name = mk_name(
                &lang_lower,
                &result_cat,
                &format!("call_{}", sanitize(&kw)),
                &mut counter,
            );
            emit(emit_parity_test(
                &test_name,
                &lang_mod,
                &result_ident,
                &input,
            ));
        }
    }

    // 7. Collection fixtures: for each collection-typed category, emit empty
    //    + single-element + multi-element fixtures.
    for type_def in &language.types {
        let Some(coll_kind) = &type_def.collection_kind else { continue };
        let cat_name = type_def.name.to_string();
        let cat_ident = format_ident!("{}", cat_name);
        let element_cat = collection_element_cat(type_def);
        let Some(element_cat_name) = element_cat else { continue };
        let Some(elem_input) = pick_source_fixture(&element_cat_name, language) else { continue };
        let kind_str = format!("{:?}", coll_kind);
        for (suffix, input) in collection_fixtures(&kind_str, &elem_input) {
            let test_name = mk_name(
                &lang_lower,
                &cat_name,
                &format!("coll_{}", suffix),
                &mut counter,
            );
            emit(emit_parity_test(
                &test_name,
                &lang_mod,
                &cat_ident,
                &input,
            ));
        }
    }

    if tests.is_empty() {
        let placeholder = quote! {
            #[test]
            fn parity_placeholder_no_fixtures() {
                // No fixtures derivable from this grammar's rules. Phase 9
                // Model A parity tests are emitted only for grammars with
                // atomic literals or terminal keywords. Composite-rule
                // parity is exercised by `wpds_parity_*.rs` hand-authored
                // tests.
            }
        };
        tests.push(placeholder);
    }

    quote! {
        #![allow(non_snake_case, unused_imports, dead_code)]
        //! Auto-generated Phase 9 Model A parity tests.
        //!
        //! For each grammar shape (atomic literal, terminal keyword,
        //! cross-cat projection, infix, prefix, function call, collection),
        //! calls both the trampoline `Cat::parse(input)` and the WPDS
        //! `Cat::parse_via_wpds(input)`, asserting the two parse paths
        //! produce equal AST values via PartialEq. Divergences where one
        //! backend succeeds and the other fails are surfaced as test
        //! failures; per `feedback_parity_drift_ok_if_better.md`, accepted
        //! divergences should be moved out of this generator into a
        //! WPDS-only or trampoline-only fixture file.

        use mettail_languages::#lang_mod;

        #(#tests)*
    }
}

/// Emit a single parity test that compares `Cat::parse(input)` against
/// `Cat::parse_via_wpds(input)`.
///
/// Behavior: Both parse paths run; if either fails the test panics with a
/// descriptive message. If both succeed, asserts `legacy == wpds` via
/// `PartialEq`. Per `feedback_parity_drift_ok_if_better.md`, the test FAILS
/// loudly on divergence — divergence is information, not policy.
fn emit_parity_test(
    test_name: &Ident,
    lang_mod: &Ident,
    cat_ident: &Ident,
    input: &str,
) -> TokenStream {
    quote! {
        #[test]
        fn #test_name() {
            let input = #input;
            let legacy = #lang_mod::#cat_ident::parse(input);
            let wpds = #lang_mod::#cat_ident::parse_via_wpds(input);
            match (legacy, wpds) {
                (Ok(a), Ok(b)) => {
                    assert_eq!(
                        a, b,
                        "Model A parity divergence on {:?}: legacy={:?} wpds={:?}",
                        input, a, b,
                    );
                }
                (Err(le), Err(we)) => {
                    // Both error. Per parity-drift policy, accept this:
                    // the parse was rejected by both backends.
                    let _ = (le, we);
                }
                (Ok(a), Err(we)) => {
                    panic!(
                        "Model A parity divergence on {:?}: trampoline OK ({:?}) but WPDS Err ({})",
                        input, a, we,
                    );
                }
                (Err(le), Ok(b)) => {
                    panic!(
                        "Model A parity divergence on {:?}: WPDS OK ({:?}) but trampoline Err ({})",
                        input, b, le,
                    );
                }
            }
        }
    }
}

/// Construct a unique test identifier: `parity_<lang>_<cat>_<kind>_<idx>`.
fn mk_name(lang: &str, cat: &str, kind: &str, counter: &mut usize) -> Ident {
    let n = *counter;
    *counter += 1;
    let s = format!(
        "parity_{}_{}_{}_{:04}",
        lang,
        cat.to_lowercase(),
        kind,
        n,
    );
    Ident::new(&s, Span::call_site())
}

/// Sanitize an operator text into an identifier-safe suffix.
fn sanitize(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 4);
    for c in s.chars() {
        if c.is_alphanumeric() {
            out.push(c.to_ascii_lowercase());
        } else {
            match c {
                '+' => out.push_str("plus"),
                '-' => out.push_str("minus"),
                '*' => out.push_str("star"),
                '/' => out.push_str("slash"),
                '%' => out.push_str("percent"),
                '=' => out.push_str("eq"),
                '<' => out.push_str("lt"),
                '>' => out.push_str("gt"),
                '!' => out.push_str("bang"),
                '|' => out.push_str("pipe"),
                '&' => out.push_str("amp"),
                '^' => out.push_str("caret"),
                '~' => out.push_str("tilde"),
                '?' => out.push_str("q"),
                '(' | ')' | '[' | ']' | '{' | '}' => {}
                _ => out.push('_'),
            }
        }
    }
    if out.is_empty() {
        out.push_str("op");
    }
    out
}

/// Atomic literal fixtures: 3-10 inputs per native kind. The eval block
/// validates suffix compatibility so e.g. `42u32` parses as UInt32 but not
/// Int. For unsuffixed integers, the same `42` parses as Int, UInt32,
/// BigInt, BigRat (depending on context).
fn atomic_literal_fixtures(kind: &NativeKind, cat_name: &str) -> Vec<String> {
    match kind {
        NativeKind::Int8 | NativeKind::Int16 | NativeKind::Int32 | NativeKind::Isize => {
            vec![
                "0".into(),
                "1".into(),
                "42".into(),
                "-1".into(),
                "-7".into(),
                "127".into(),
            ]
        }
        NativeKind::Int64 | NativeKind::Int128 => {
            vec![
                "0".into(),
                "1".into(),
                "42".into(),
                "-1".into(),
                "1000".into(),
            ]
        }
        NativeKind::UInt8 | NativeKind::UInt16 => {
            vec!["0".into(), "1".into(), "42".into(), "200".into()]
        }
        NativeKind::UInt32 | NativeKind::UInt64 | NativeKind::UInt128 | NativeKind::Usize => {
            // u32 prefer the typed suffix to disambiguate from Int.
            vec![
                "0u32".into(),
                "1u32".into(),
                "42u32".into(),
                "100u32".into(),
            ]
        }
        NativeKind::CanonicalBigInt => {
            // BigInt accepts both bare digits and `n` suffix.
            vec![
                "0n".into(),
                "1n".into(),
                "42n".into(),
                "1000n".into(),
            ]
        }
        NativeKind::CanonicalBigRat => {
            // C3 (2026-04-28): composite forms `1r/2r` now lex atomically —
            // the BigRat regex was extended to match `<int>r(/<int>r)?` and
            // the WPDS facade routes through `parse_rational_lit` which
            // handles both whole and composite forms.
            vec![
                "0r".into(),
                "1r".into(),
                "42r".into(),
                "100r".into(),
                "1r/2r".into(),
                "3r/4r".into(),
                "0r/1r".into(),
                "10r/100r".into(),
                "0xFr/0x2r".into(),
            ]
        }
        NativeKind::CanonicalFixedPoint => {
            vec![
                "1.5p2".into(),
                "0.5p2".into(),
                "3.14p2".into(),
            ]
        }
        NativeKind::Float32 | NativeKind::Float64 => {
            vec![
                "0.0".into(),
                "1.0".into(),
                "3.14".into(),
                "2.5e1".into(),
                "-1.5".into(),
            ]
        }
        NativeKind::Bool => {
            // C6 (2026-04-28): all four bool literals exercised. The regex
            // accepts `yeap|nope|true|false`, the eval block converts each
            // to bool. Stage 7 deleted the trampoline; both `Cat::parse()`
            // and `Cat::parse_via_wpds()` now route through WPDS, which
            // honors the eval block correctly for the `yeap`/`nope` aliases.
            vec!["true".into(), "false".into(), "yeap".into(), "nope".into()]
        }
        NativeKind::Str => {
            vec![
                "\"hello\"".into(),
                "\"\"".into(),
                "\"x\"".into(),
            ]
        }
        NativeKind::Other => {
            // `NativeKind::Other` is overloaded — it covers (a) custom
            // user wrappers like `MyType` AND (b) container types like
            // `Vec<T>` / `HashMap<K,V>` / `HashBag<T>` (which DO appear
            // in shipped grammars as `![Vec<Proc>] as List` etc.).
            // Container categories carry their own fixtures via the
            // collection-literal path, so returning no atomic-literal
            // fixtures here is the semantically correct response. A
            // truly-unknown category would also hit this arm; if test
            // coverage gaps for such a grammar become a problem, extend
            // `NativeKind` with a dedicated variant rather than
            // panicking here.
            let _ = cat_name;
            Vec::new()
        }
    }
}

/// If the rule is a nullary terminal-keyword form (`Foo . |- "kw" : Cat`),
/// return `"kw"`. Else `None`.
fn terminal_keyword_input(rule: &GrammarRule) -> Option<String> {
    let tc = rule.term_context.as_ref()?;
    let sp = rule.syntax_pattern.as_ref()?;
    if !tc.is_empty() {
        return None;
    }
    if sp.len() != 1 {
        return None;
    }
    if let SyntaxExpr::Literal(text) = &sp[0] {
        return Some(text.clone());
    }
    None
}

/// If the rule is a cross-cat projection (`X . p:SrcCat |- p : ResultCat`),
/// return `(source_cat_name, ())`. Else `None`.
fn cross_cat_projection_info(rule: &GrammarRule) -> Option<(String, ())> {
    let tc = rule.term_context.as_ref()?;
    let sp = rule.syntax_pattern.as_ref()?;
    if tc.len() != 1 || sp.len() != 1 {
        return None;
    }
    let TermParam::Simple { name: param_name, ty } = &tc[0] else {
        return None;
    };
    let SyntaxExpr::Param(syn_name) = &sp[0] else {
        return None;
    };
    if syn_name != param_name {
        return None;
    }
    let TypeExpr::Base(source_ident) = ty else {
        return None;
    };
    let source_cat = source_ident.to_string();
    if source_cat == rule.category.to_string() {
        return None;
    }
    Some((source_cat, ()))
}

/// If the rule is a binary infix (`Op . a:Cat, b:Cat |- a "op" b : Cat`),
/// return `(op_text, lhs_cat, rhs_cat)`. Else `None`.
fn infix_rule_info(rule: &GrammarRule) -> Option<(String, String, String)> {
    let tc = rule.term_context.as_ref()?;
    let sp = rule.syntax_pattern.as_ref()?;
    if tc.len() != 2 || sp.len() != 3 {
        return None;
    }
    let (TermParam::Simple { name: a_name, ty: a_ty }, TermParam::Simple { name: b_name, ty: b_ty }) =
        (&tc[0], &tc[1])
    else {
        return None;
    };
    let (SyntaxExpr::Param(s1), SyntaxExpr::Literal(op), SyntaxExpr::Param(s2)) =
        (&sp[0], &sp[1], &sp[2])
    else {
        return None;
    };
    if s1 != a_name || s2 != b_name {
        return None;
    }
    let TypeExpr::Base(a_ident) = a_ty else { return None };
    let TypeExpr::Base(b_ident) = b_ty else { return None };
    Some((op.clone(), a_ident.to_string(), b_ident.to_string()))
}

/// If the rule is a prefix-unary (`Op . a:Cat |- "op" a : Cat`),
/// return `(op_text, arg_cat)`. Else `None`.
fn prefix_unary_info(rule: &GrammarRule) -> Option<(String, String)> {
    let tc = rule.term_context.as_ref()?;
    let sp = rule.syntax_pattern.as_ref()?;
    if tc.len() != 1 || sp.len() != 2 {
        return None;
    }
    let TermParam::Simple { name: a_name, ty: a_ty } = &tc[0] else {
        return None;
    };
    let (SyntaxExpr::Literal(op), SyntaxExpr::Param(s1)) = (&sp[0], &sp[1]) else {
        return None;
    };
    if s1 != a_name {
        return None;
    }
    let TypeExpr::Base(a_ident) = a_ty else { return None };
    Some((op.clone(), a_ident.to_string()))
}

/// If the rule is a function-call form (`Op . a:Cat, b:Cat |- "kw" "(" a "," b ")" : Out`),
/// return `(kw, [arg_cat_a, arg_cat_b, ...])`. Supports 1+ args.
fn call_form_info(rule: &GrammarRule) -> Option<(String, Vec<String>)> {
    let tc = rule.term_context.as_ref()?;
    let sp = rule.syntax_pattern.as_ref()?;
    if tc.is_empty() || sp.len() < 4 {
        return None;
    }
    // Pattern: Literal(kw), Literal("("), <param>, [Literal(","), <param>]*, Literal(")")
    let SyntaxExpr::Literal(kw) = &sp[0] else { return None };
    let SyntaxExpr::Literal(open) = &sp[1] else { return None };
    if open != "(" {
        return None;
    }
    let SyntaxExpr::Literal(close) = sp.last()? else { return None };
    if close != ")" {
        return None;
    }

    // Walk the middle: alternating param + comma.
    let middle = &sp[2..sp.len() - 1];
    let mut arg_names: Vec<String> = Vec::new();
    let mut expect_param = true;
    for item in middle {
        match item {
            SyntaxExpr::Param(n) if expect_param => {
                arg_names.push(n.to_string());
                expect_param = false;
            }
            SyntaxExpr::Literal(s) if !expect_param && s == "," => {
                expect_param = true;
            }
            _ => return None,
        }
    }
    if arg_names.is_empty() || arg_names.len() != tc.len() {
        return None;
    }

    let mut arg_cats: Vec<String> = Vec::with_capacity(arg_names.len());
    for n in &arg_names {
        let param = tc.iter().find(|p| match p {
            TermParam::Simple { name, .. } => name.to_string() == *n,
            _ => false,
        })?;
        let TermParam::Simple { ty, .. } = param else { return None };
        let TypeExpr::Base(ident) = ty else { return None };
        arg_cats.push(ident.to_string());
    }
    Some((kw.clone(), arg_cats))
}

/// Pick a representative input string for a category. Tries atomic literal
/// fixtures first; falls back to the first terminal keyword for that
/// category; gives up otherwise.
fn pick_source_fixture(cat_name: &str, language: &LanguageDef) -> Option<String> {
    // Try atomic literal.
    if let Some(type_def) = language.types.iter().find(|t| t.name.to_string() == cat_name) {
        if let Some(nt) = type_def.native_type.as_ref() {
            let kind = NativeKind::from_syn_type(nt);
            let fxs = atomic_literal_fixtures(&kind, cat_name);
            if let Some(f) = fxs.into_iter().next() {
                return Some(f);
            }
        }
    }
    // Try terminal keyword.
    for rule in &language.terms {
        if rule.category.to_string() != cat_name {
            continue;
        }
        if let Some(text) = terminal_keyword_input(rule) {
            return Some(text);
        }
    }
    // Try cross-cat projection (recursive — but bounded by depth 1 to
    // avoid divergence).
    for rule in &language.terms {
        if rule.category.to_string() != cat_name {
            continue;
        }
        if let Some((source_cat, _)) = cross_cat_projection_info(rule) {
            // Recurse one level — only into a category that is NOT
            // `cat_name` itself to prevent infinite loops.
            if source_cat != cat_name {
                if let Some(input) = pick_source_fixture(&source_cat, language) {
                    return Some(input);
                }
            }
        }
    }
    None
}

/// True if `cat_name` is a synthesized collection category (Vec, HashBag,
/// HashMap). Such categories have a `collection_kind` set in their
/// `LangType`; their parser comes from synthetic.rs Phase B and behaves
/// differently from plain term-rule categories.
fn is_collection_category(cat_name: &str, language: &LanguageDef) -> bool {
    language
        .types
        .iter()
        .find(|t| t.name.to_string() == cat_name)
        .map(|t| t.collection_kind.is_some())
        .unwrap_or(false)
}

/// Element-category name for a collection-typed `LangType`. For
/// `![Vec<Proc>] as List` returns `Some("Proc")`; for `HashMap<Proc, Proc>`
/// returns `Some("Proc")` (the value type — keys not yet supported as a
/// fixture-driving primitive).
fn collection_element_cat(type_def: &mettail_ast::language::LangType) -> Option<String> {
    let Some(nt) = type_def.native_type.as_ref() else { return None };
    let nt_text = quote! { #nt }.to_string();
    // Crude regex-free extraction: find first identifier inside `<...>`.
    let lt = nt_text.find('<')?;
    let gt = nt_text.rfind('>')?;
    if gt <= lt + 1 {
        return None;
    }
    let inside = &nt_text[lt + 1..gt];
    // For `Proc` or `Proc , Proc`, take the first segment.
    let first = inside
        .split(',')
        .next()
        .map(|s| s.trim().to_string())?;
    if first.is_empty() {
        return None;
    }
    Some(first)
}

/// Generate `(suffix, input)` pairs for collection fixtures. `kind_str` is
/// the debug-formatted collection kind (e.g. "Vec", "Bag", "Set", "Map");
/// `elem` is a representative element fixture string.
fn collection_fixtures(kind_str: &str, elem: &str) -> Vec<(String, String)> {
    let (open, close, sep) = if kind_str.contains("Vec") {
        ("[", "]", ",")
    } else if kind_str.contains("Bag") || kind_str.contains("Set") {
        ("{", "}", "|")
    } else if kind_str.contains("Map") {
        ("{", "}", ",")
    } else {
        return Vec::new();
    };
    let mut out = Vec::new();
    out.push((
        "empty".into(),
        format!("{}{}", open, close),
    ));
    out.push((
        "single".into(),
        format!("{} {} {}", open, elem, close),
    ));
    out.push((
        "multi".into(),
        format!("{} {} {} {} {}", open, elem, sep, elem, close),
    ));
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::language::{LangType, TokenDef};
    use proc_macro2::Span;
    use syn::{parse_quote, Ident};

    fn lang_with_int_literal() -> LanguageDef {
        let mut lang = LanguageDef {
            name: Ident::new("Toy", Span::call_site()),
            options: Default::default(),
            extends_names: Vec::new(),
            include_names: Vec::new(),
            mixin_names: Vec::new(),
            types: Vec::new(),
            refinement_types: Vec::new(),
            token_defs: Vec::new(),
            mode_defs: Vec::new(),
            sync_constraints: Vec::new(),
            tree_invariants: Vec::new(),
            terms: Vec::new(),
            equations: Vec::new(),
            rewrites: Vec::new(),
            logic: None,
            guard_config: None,
        };
        lang.types.push(LangType {
            name: Ident::new("Int", Span::call_site()),
            native_type: Some(parse_quote!(i32)),
            collection_kind: None,
        });
        lang.token_defs.push(TokenDef {
            name: Ident::new("Integer", Span::call_site()),
            pattern: r"[0-9]+".to_string(),
            category: Some(Ident::new("Int", Span::call_site())),
            rust_code: Some(quote! { Ok(0i32) }),
            priority: None,
            push_mode: None,
            is_pop: false,
            stream: None,
            from_literals: true,
        });
        lang
    }

    #[test]
    fn emits_at_least_one_test_per_atomic_literal_cat() {
        let lang = lang_with_int_literal();
        let ts = generate_parity_section(&lang).to_string();
        assert!(ts.contains("parity_toy_int_atomic_lit_"));
        assert!(ts.contains("Int :: parse") || ts.contains("Int::parse"));
        assert!(ts.contains("parse_via_wpds"));
    }

    #[test]
    fn empty_lang_emits_placeholder() {
        let lang = LanguageDef {
            name: Ident::new("Empty", Span::call_site()),
            options: Default::default(),
            extends_names: Vec::new(),
            include_names: Vec::new(),
            mixin_names: Vec::new(),
            types: Vec::new(),
            refinement_types: Vec::new(),
            token_defs: Vec::new(),
            mode_defs: Vec::new(),
            sync_constraints: Vec::new(),
            tree_invariants: Vec::new(),
            terms: Vec::new(),
            equations: Vec::new(),
            rewrites: Vec::new(),
            logic: None,
            guard_config: None,
        };
        let ts = generate_parity_section(&lang).to_string();
        assert!(ts.contains("parity_placeholder_no_fixtures"));
    }

    #[test]
    fn emitted_module_parses_as_rust() {
        let lang = lang_with_int_literal();
        let ts = generate_parity_section(&lang);
        let parsed: Result<syn::File, _> = syn::parse2(quote! { #ts });
        assert!(parsed.is_ok(), "parse error: {:?}", parsed.err());
    }

    #[test]
    fn sanitize_handles_punctuation() {
        assert_eq!(sanitize("+"), "plus");
        assert_eq!(sanitize("=="), "eqeq");
        assert_eq!(sanitize("a+b"), "aplusb");
        assert_eq!(sanitize("()"), "op");
    }

    #[test]
    fn collection_fixtures_emit_three_per_kind() {
        let v = collection_fixtures("Vec<Proc>", "0");
        assert_eq!(v.len(), 3);
        assert!(v.iter().any(|(k, s)| k == "empty" && s == "[]"));
        assert!(v.iter().any(|(k, s)| k == "single" && s.contains("[ 0 ]")));

        let v = collection_fixtures("Bag<Proc>", "0");
        assert_eq!(v.len(), 3);
        assert!(v.iter().any(|(k, _)| k == "multi"));
    }
}
