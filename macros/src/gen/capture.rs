//! **The ONE source of truth for a rule's variant field ORDER.**
//!
//! # Why this module exists
//!
//! A generated AST variant is written in two places that must agree
//! POSITIONALLY and that used to derive their order from two different lists:
//!
//! ```text
//!            ┌──────────────────────── the DEFINITION ─────────────────────────┐
//!            │  gen/types/enums.rs::generate_variant_from_term_context         │
//!            │      `Cat::Label(FieldTy₀, FieldTy₁, …)`                        │
//!            └─────────────────────────────────────────────────────────────────┘
//!            ┌──────────────────────── the CONSTRUCTION ───────────────────────┐
//!            │  gen/runtime/wpda_codegen/binder.rs::emit_binder_action_entry   │
//!            │      `Cat::Label(field_names…, scope?)`                          │
//!            └─────────────────────────────────────────────────────────────────┘
//! ```
//!
//! The constructor orders its arguments by **syntax-pattern encounter** (its
//! `field_names` are pushed while walking `action_args`, which
//! `classify_binder_in` builds by walking `syntax_pattern`). Before task #139
//! the definition ordered its fields by **term-context declaration**, and the
//! two coincided only by accident:
//!
//! * for a rule containing a `v@Tok` / `*flt(…)` capture the definition took
//!   the branch below and walked the SYNTAX PATTERN, agreeing by construction;
//! * for every other rule it walked `term_context`, agreeing only when the
//!   author happened to declare parameters in the order the surface mentions
//!   them.
//!
//! ★ The divergence is not merely a compile error in the generated crate. Two
//! same-typed parameters whose surface order differs from their declaration
//! order —
//!
//! ```text
//!   Sub . a:Proc, b:Proc |- "sub" "(" b "," a ")" : Proc ;
//! ```
//!
//! — make the constructor emit `Sub(Arc::new(b), Arc::new(a))` against a
//! definition `Sub(Arc<Proc>, Arc<Proc>)`. That **type-checks**, transposes the
//! operands, and produces no diagnostic anywhere. The same shape is what makes
//! a capture `String` and a `StringLiteral`-typed param field swappable in
//! silence: they are the SAME Rust type.
//!
//! The repair is not a special case for the shapes that were noticed. It is to
//! compute the order ONCE, here, and have the definition consume it — so the
//! definition FOLLOWS the constructor rather than agreeing with it by luck.
//!
//! # The order
//!
//! [`field_layout`] is TOTAL: it answers for every rule, capture-bearing or
//! not. It reproduces exactly what `binder.rs` constructs:
//!
//! 1. Walk `syntax_pattern` in order. A leading `sp[0]` capture is interned
//!    first by the prefix dispatch and is `sp[0]`, so an in-order walk is the
//!    right one. Each encountered element contributes at most one slot:
//!    a `v@Tok` capture → [`FieldSlotSource::TokenText`]; a `*flt(…)` guest
//!    body → [`FieldSlotSource::GuestBody`]; a `Param`, a `coll.*sep(…)` and
//!    the names accumulator of a `*zip(ns,xs).*map(…).*sep(…)` chain → the
//!    named term-context parameter ([`FieldSlotSource::Param`]); a `#opt(…)`
//!    group recurses. Literals and the multi-binder side of a chain contribute
//!    nothing.
//! 2. Append any declared parameter the walk did not reach, in declaration
//!    order. Measured EMPTY over the whole bundled corpus (51 languages, 561
//!    rules); it exists so that a pattern form this walk does not yet
//!    understand can never make a field silently DISAPPEAR, which would shift
//!    every later field left.
//! 3. Append the binder `Scope` LAST, exactly as `binder.rs` does
//!    (`binder.rs`'s two `#(#field_names,)* scope` sites). A multi-abstraction
//!    wins over a single one, mirroring `variant_kind_from_term_context`.
//!
//! # `capture_layout` is a PROJECTION of `field_layout`, not a second walk
//!
//! Four seams still ask the narrower question *"is this a capture rule?"* and
//! select a capture-specific path from the answer
//! (`gen/runtime/language.rs`, `gen/syntax/var_inference.rs` ×2,
//! `gen/syntax/display.rs`). [`capture_layout`] keeps serving them: it is
//! `field_layout` filtered by the capture predicate and re-expressed in the
//! [`CaptureLayout`] vocabulary. There is exactly one walk; `capture_layout`
//! is a view of it, never a parallel derivation.

use mettail_ast::grammar::{PatternOp, SyntaxExpr, TermParam};
use mettail_ast::types::TypeExpr;
use std::collections::HashSet;

use crate::gen::term_param_walk::{TermParamLeafKind, TermParamLeaves};

/// One non-scope variant field contributed by a capture-bearing rule, in
/// syntax-pattern encounter order.
#[derive(Clone)]
pub(crate) struct CaptureField<'a> {
    /// The name bound to this field: a capture's `bind` (or the synthesized
    /// `__tok_<Kind>` for an `@`-less capture), or a term-param's name. Used by
    /// the walkers (eval / display) to bind the field in the match pattern and
    /// reference it in user `![...]` code; ignored by the type/`FieldInfo`
    /// producers (which only need the kind).
    pub(crate) name: String,
    pub(crate) kind: CaptureFieldKind<'a>,
    /// True when this field lives inside a `#opt(...)` group → its runtime type
    /// is `Option<…>` and the pattern binding is `Option`-wrapped.
    pub(crate) optional: bool,
}

/// The nature of a non-scope capture-rule field.
#[derive(Clone)]
pub(crate) enum CaptureFieldKind<'a> {
    /// A `v@Tok` capture → a bare `std::string::String` leaf.
    TokenText,
    /// L9-4: a `*flt(bind, open, close)` guest-body capture → an
    /// `Arc<FltNode>` opaque leaf. Carries the opener/closer token KIND names
    /// so the WPDA codegen knows which delimiters bound the guest region.
    GuestBody {
        open: &'a syn::Ident,
        close: &'a syn::Ident,
    },
    /// A `Simple` term-param at this syntax position → its declared type.
    Term(&'a TypeExpr),
    /// A `?guard:Guard` predicate slot → a `BehavioralPred` leaf.
    Predicate,
}

/// The trailing binder `Scope` field of a capture rule that ALSO binds
/// (`^x.body` / `^[xs].body`). Appended after all non-scope fields.
pub(crate) struct CaptureScope<'a> {
    /// True for `^[xs].body` (multi-binder `Scope<Vec<Binder>, …>`).
    pub(crate) multi: bool,
    /// The abstraction's arrow type `[Domain -> Codomain]`.
    pub(crate) ty: &'a TypeExpr,
}

/// The full ordered field layout of a capture-bearing rule.
pub(crate) struct CaptureLayout<'a> {
    pub(crate) non_scope: Vec<CaptureField<'a>>,
    pub(crate) scope: Option<CaptureScope<'a>>,
}

/// Where one variant field's VALUE comes from — and therefore how its Rust type
/// is computed by `gen/types/enums.rs`.
pub(crate) enum FieldSlotSource<'a> {
    /// A `v@Tok` capture. Declared in the SYNTAX PATTERN, not the term context,
    /// so there is no [`TermParam`] to point at.
    TokenText,
    /// A `*flt(bind, open, close)` guest-body capture, likewise pattern-declared.
    /// Carries the opener/closer token KIND names for the WPDA codegen.
    GuestBody {
        open: &'a syn::Ident,
        close: &'a syn::Ident,
    },
    /// A term-context parameter, placed at its SYNTAX position. Never
    /// [`TermParam::Optional`] — an opt-group is flattened, one slot per inner
    /// parameter, exactly as `enums.rs` emits `Option<T>` fields separately
    /// rather than as one tuple.
    Param(&'a TermParam),
}

/// One ordered field slot of a rule's AST variant.
pub(crate) struct FieldSlot<'a> {
    /// The name bound to this field: a capture's `bind` (or the synthesized
    /// `__tok_<Kind>` for an `@`-less capture), or the parameter's name. Used by
    /// the walkers (eval / display) to bind the field in a match pattern and to
    /// reference it from user `![…]` code; the type producers need only `source`.
    pub(crate) name: String,
    pub(crate) source: FieldSlotSource<'a>,
    /// True when this field's runtime type is `Option<…>`.
    ///
    /// ⚠ The two slot families read this from DIFFERENT places, and that is
    /// deliberate. A `Param` slot takes it from the DECLARATION
    /// ([`TermParam::Optional`]), because that is what decides whether the
    /// generated field is `Option`-wrapped and what `enums.rs` has always used.
    /// A capture slot has no declaration, so it takes it from the PATTERN
    /// (`#opt(…)` nesting). For a rule that is both capture-bearing and
    /// parameterised the two coincide; no such rule exists in the bundled
    /// corpus, and [`field_layout`]'s unit cells pin both readings.
    pub(crate) optional: bool,
}

/// The full ordered field layout of ANY rule: non-scope slots in syntax-pattern
/// order, then the binder `Scope` last.
pub(crate) struct FieldLayout<'a> {
    pub(crate) slots: Vec<FieldSlot<'a>>,
}

/// ★ The ONE derivation of a rule's variant field order. See the module header.
///
/// `syntax_pattern` is `None` only for a rule written in the old BNFC item form,
/// which has no surface order to follow; declaration order is then the only
/// order there is, and it is returned unchanged.
pub(crate) fn field_layout<'a>(
    term_context: &'a [TermParam],
    syntax_pattern: Option<&'a [SyntaxExpr]>,
) -> FieldLayout<'a> {
    let Some(syntax_pattern) = syntax_pattern else {
        let mut slots = Vec::new();
        push_declaration_order(term_context, false, &mut slots);
        return FieldLayout { slots };
    };

    // Abstraction binder+body names are consumed by the trailing Scope, not
    // emitted as standalone fields, so the walk skips them wherever the pattern
    // mentions them — as a bare `Param`, or as the right-hand side of a
    // `*zip(ns,xs)` chain, or as the collection of a PNew-style `xs.*sep(…)`.
    let mut abstraction_names: HashSet<String> = HashSet::new();
    for p in term_context {
        if let TermParam::Abstraction { binder, body, .. }
        | TermParam::MultiAbstraction { binder, body, .. } = p
        {
            abstraction_names.insert(binder.to_string());
            abstraction_names.insert(body.to_string());
        }
    }

    let mut slots: Vec<FieldSlot<'a>> = Vec::new();
    walk_pattern(syntax_pattern, term_context, &abstraction_names, false, &mut slots);

    // Total-coverage clause. Every declared parameter that the walk did not
    // reach is appended in declaration order, BEFORE the Scope. Measured empty
    // over the bundled corpus; see the module header for why it is nonetheless
    // written down.
    let reached: HashSet<String> = slots.iter().map(|s| s.name.clone()).collect();
    let mut unreached: Vec<FieldSlot<'a>> = Vec::new();
    push_declaration_order(term_context, false, &mut unreached);
    for slot in unreached {
        let already = reached.contains(&slot.name)
            || matches!(
                slot.source,
                FieldSlotSource::Param(TermParam::Abstraction { .. })
                    | FieldSlotSource::Param(TermParam::MultiAbstraction { .. })
            );
        if !already {
            slots.push(slot);
        }
    }

    // The trailing Scope: a multi-abstraction wins over a single abstraction
    // (mirrors `variant_kind_from_term_context`'s precedence).
    let scope_param = term_context
        .iter()
        .find_map(|param| match param {
            TermParam::MultiAbstraction { body, .. } => Some((param, body)),
            _ => None,
        })
        .or_else(|| {
            term_context.iter().find_map(|param| match param {
                TermParam::Abstraction { body, .. } => Some((param, body)),
                _ => None,
            })
        });
    if let Some((param, body)) = scope_param {
        slots.push(FieldSlot {
            name: body.to_string(),
            source: FieldSlotSource::Param(param),
            optional: false,
        });
    }

    FieldLayout { slots }
}

/// Flatten `term_context` into slots in DECLARATION order, descending into
/// `#opt(…)` groups (whose inner parameters each become their own `Option<T>`
/// slot, never a tuple).
fn push_declaration_order<'a>(
    term_context: &'a [TermParam],
    optional: bool,
    out: &mut Vec<FieldSlot<'a>>,
) {
    for leaf in TermParamLeaves::new(term_context, optional) {
        let optional = leaf.is_optional;
        match leaf.kind {
            TermParamLeafKind::Simple { param, name, .. }
            | TermParamLeafKind::GuardBody { param, name } => out.push(FieldSlot {
                name: name.to_string(),
                source: FieldSlotSource::Param(param),
                optional,
            }),
            TermParamLeafKind::Abstraction { param, body, .. }
            | TermParamLeafKind::MultiAbstraction { param, body, .. } => {
                out.push(FieldSlot {
                    name: body.to_string(),
                    source: FieldSlotSource::Param(param),
                    optional,
                });
            },
        }
    }
}

/// Compute the capture field layout for a rule, or `None` if the syntax
/// pattern contains no `v@Tok` capture (in which case every seam keeps its
/// byte-identical capture-free path).
///
/// This is a PROJECTION of [`field_layout`] into the [`CaptureLayout`]
/// vocabulary, gated on the capture predicate; it is not a second walk. Four
/// seams still ask only *"is this a capture rule?"* and this is the question
/// they ask.
pub(crate) fn capture_layout<'a>(
    term_context: &'a [TermParam],
    syntax_pattern: &'a [SyntaxExpr],
) -> Option<CaptureLayout<'a>> {
    let has_capture = syntax_pattern
        .iter()
        .any(|e| matches!(e, SyntaxExpr::TokenKind { .. } | SyntaxExpr::GuestBody { .. }));
    if !has_capture {
        return None;
    }

    let layout = field_layout(term_context, Some(syntax_pattern));
    let mut non_scope: Vec<CaptureField<'a>> = Vec::new();
    let mut scope: Option<CaptureScope<'a>> = None;
    for slot in layout.slots {
        let kind = match slot.source {
            FieldSlotSource::TokenText => CaptureFieldKind::TokenText,
            FieldSlotSource::GuestBody { open, close } => {
                CaptureFieldKind::GuestBody { open, close }
            },
            FieldSlotSource::Param(TermParam::Simple { ty, .. }) => CaptureFieldKind::Term(ty),
            FieldSlotSource::Param(TermParam::GuardBody { .. }) => CaptureFieldKind::Predicate,
            FieldSlotSource::Param(TermParam::Abstraction { ty, .. }) => {
                scope = Some(CaptureScope { multi: false, ty });
                continue;
            },
            FieldSlotSource::Param(TermParam::MultiAbstraction { ty, .. }) => {
                scope = Some(CaptureScope { multi: true, ty });
                continue;
            },
            // `push_declaration_order` flattens opt-groups, so an `Optional`
            // never reaches a slot.
            FieldSlotSource::Param(TermParam::Optional { .. }) => continue,
        };
        non_scope.push(CaptureField {
            name: slot.name,
            kind,
            optional: slot.optional,
        });
    }

    Some(CaptureLayout { non_scope, scope })
}

/// Find a term param by name, descending into `Optional` groups without using
/// the machine stack.
/// Returns the parameter and whether it was declared INSIDE an `#opt(…)` group.
fn find_param<'a>(term_context: &'a [TermParam], name: &str) -> Option<(&'a TermParam, bool)> {
    for leaf in TermParamLeaves::new(term_context, false) {
        match leaf.kind {
            TermParamLeafKind::Simple { param, name: candidate, .. }
            | TermParamLeafKind::GuardBody { param, name: candidate }
                if candidate == name =>
            {
                return Some((param, leaf.is_optional));
            },
            _ => {},
        }
    }
    None
}

/// Push the slot for the term-context parameter named `n`, if there is one.
fn push_named_param<'a>(
    n: String,
    term_context: &'a [TermParam],
    abstraction_names: &HashSet<String>,
    out: &mut Vec<FieldSlot<'a>>,
) {
    if abstraction_names.contains(&n) {
        // Folds into the trailing Scope.
        return;
    }
    if let Some((param, declared_optional)) = find_param(term_context, &n) {
        out.push(FieldSlot {
            name: n,
            source: FieldSlotSource::Param(param),
            optional: declared_optional,
        });
    }
}

fn walk_pattern<'a>(
    exprs: &'a [SyntaxExpr],
    term_context: &'a [TermParam],
    abstraction_names: &HashSet<String>,
    optional: bool,
    out: &mut Vec<FieldSlot<'a>>,
) {
    let mut work: Vec<(&SyntaxExpr, bool)> =
        exprs.iter().rev().map(|expr| (expr, optional)).collect();
    while let Some((expr, optional)) = work.pop() {
        match expr {
            SyntaxExpr::Literal(_) => {},
            SyntaxExpr::TokenKind { name, bind } => {
                let field_name = bind
                    .as_ref()
                    .map(|b| b.to_string())
                    .unwrap_or_else(|| format!("__tok_{}", name));
                out.push(FieldSlot {
                    name: field_name,
                    source: FieldSlotSource::TokenText,
                    optional,
                });
            },
            SyntaxExpr::Param(id) => {
                push_named_param(id.to_string(), term_context, abstraction_names, out);
            },
            SyntaxExpr::GuestBody { open, close, bind } => {
                // L9-4: a `*flt(bind, open, close)` guest-body capture → an
                // `Arc<FltNode>` leaf named `bind`.
                out.push(FieldSlot {
                    name: bind.to_string(),
                    source: FieldSlotSource::GuestBody { open, close },
                    optional,
                });
            },
            SyntaxExpr::Op(PatternOp::Opt { inner }) => {
                work.extend(inner.iter().rev().map(|expr| (expr, true)));
            },
            // `coll.*sep("…")` — a Class-2 collection slot, or a PNew-style
            // binder list. `classify_binder_in` pushes a `CollectionDrain`
            // action arg for the former (⇒ a field) and a `BinderList` for the
            // latter (⇒ no field; it folds into the Scope), and
            // `push_named_param` makes the same distinction through
            // `abstraction_names`.
            SyntaxExpr::Op(PatternOp::Sep { collection, source: None, .. }) => {
                push_named_param(collection.to_string(), term_context, abstraction_names, out);
            },
            // `*zip(ns,xs).*map(|n,x| …).*sep("…")` — the Class-3 chain.
            // `classify_binder_in` emits TWO action args for it, in this order:
            // the synthesized names accumulator (`ns`, a declared collection
            // parameter ⇒ a field) then the multi-binder (`xs` ⇒ the Scope).
            SyntaxExpr::Op(PatternOp::Sep { source: Some(source), .. }) => {
                if let PatternOp::Map { source: zip, .. } = source.as_ref() {
                    if let PatternOp::Zip { left, .. } = zip.as_ref() {
                        push_named_param(left.to_string(), term_context, abstraction_names, out);
                    }
                }
            },
            // A bare `*zip`/`*map`/`*var` is not a complete surface form;
            // `classify_binder_in` refuses such a rule outright, so there is no
            // variant for it to contribute a field to.
            SyntaxExpr::Op(PatternOp::Zip { .. } | PatternOp::Map { .. } | PatternOp::Var(_)) => {},
        }
    }
}

/// ★ THE BUNDLED CORPUS, derived — the shared subject of every whole-corpus gate
/// in this crate.
///
/// # Why it lives here, and why it is derived rather than listed
///
/// Two gates range over "every rule in every bundled language": the field-order
/// gate (`gen/runtime/wpda_codegen/binder.rs`) and the reflection anti-vacuity
/// gate (`gen/runtime/metadata.rs`). A subject written out twice is a subject
/// that can be narrowed once, so it is written out here, once, and both read it.
///
/// It derives the subject from `mettail_ast::language_scan` — the SAME
/// manifest-declared walk the three inventory audits use — and reconstructs each
/// body with `mettail_ast::auto_inject::reconstruct_language_def_from_tokens`,
/// so it can neither omit a definition (there is no entry to keep in step) nor
/// be handed the wrong bytes (it parses the macro's OWN token stream, never a
/// slice of source text).
///
/// A test-only module inside `gen/capture.rs` rather than a file of its own:
/// `gen/mod.rs` declares the module list, and a `#[cfg(test)]` helper does not
/// belong in a production module list. `capture.rs` is its first consumer's
/// home.
#[cfg(test)]
pub(crate) mod bundled_corpus {
    use mettail_ast::auto_inject::reconstruct_language_def_from_tokens;
    use mettail_ast::language::LanguageDef;
    use mettail_ast::language_scan;
    use std::path::Path;
    use syn::Item;

    /// One bundled language: where it is declared, and the macro-time augmented
    /// definition the generator would see for it.
    pub(crate) struct BundledLanguage {
        /// Repository-relative and language-qualified: `languages/src/monoid.rs::Monoid`.
        pub(crate) tag: String,
        pub(crate) def: LanguageDef,
    }

    fn collect(items: &[Item], path: &str, out: &mut Vec<(String, proc_macro2::TokenStream)>) {
        for item in items {
            match item {
                Item::Macro(item_macro) => {
                    if item_macro.mac.path.is_ident("language") {
                        let tokens = item_macro.mac.tokens.clone();
                        // Parsed once here only to learn the declared NAME for the
                        // tag; the reconstruction below re-reads the same tokens.
                        if let Ok(def) = syn::parse2::<LanguageDef>(tokens.clone()) {
                            out.push((format!("{path}::{}", def.name), tokens));
                        }
                    }
                },
                // Inline `mod { … }` bodies count: `x2_lookahead_bracket_probe.rs`
                // declares three languages, one in each of three inline modules.
                Item::Mod(item_mod) => {
                    if let Some((_, nested)) = &item_mod.content {
                        collect(nested, path, out);
                    }
                },
                _ => {},
            }
        }
    }

    /// Every bundled language that can be reconstructed outside the macro.
    ///
    /// The three composed definitions in `languages/src/composition/` cannot be
    /// (their bases live in a runtime registry the macro populates), so they are
    /// absent here and covered instead by the build itself, which runs the same
    /// generator over them. Callers derive their expected work directly from the
    /// reconstructed definitions and assert exact visitation rather than retaining a
    /// grammar-size floor.
    pub(crate) fn bundled_languages() -> Vec<BundledLanguage> {
        let root =
            mettail_ast::manifest::find_workspace_root(Path::new(env!("CARGO_MANIFEST_DIR")))
                .expect("`macros` is a workspace member, so some ancestor declares [workspace]");
        let files = language_scan::language_files(&root).expect(
            "the subject IS this scan, so it must not continue with a guess: a narrowed \
             root list would make every gate over this corpus pass over nothing",
        );

        let mut bodies = Vec::new();
        for path in files {
            let source = std::fs::read_to_string(&path)
                .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
            // A declaration necessarily spells `language!` followed by a
            // delimiter, so this gate cannot hide one; it only spares `syn` the
            // generated hosts and simulator binaries the walk also reaches.
            if !language_scan::mentions_language_invocation(&source) {
                continue;
            }
            let file = syn::parse_file(&source)
                .unwrap_or_else(|e| panic!("parse {}: {e}", path.display()));
            collect(&file.items, &language_scan::repo_relative(&root, &path), &mut bodies);
        }

        let mut out = Vec::with_capacity(bodies.len());
        for (tag, tokens) in bodies {
            if let Ok(def) = reconstruct_language_def_from_tokens(tokens) {
                out.push(BundledLanguage { tag, def });
            }
        }
        out
    }

    /// The one bundled language whose declared name is `name`.
    pub(crate) fn bundled_language(name: &str) -> BundledLanguage {
        let mut matches: Vec<BundledLanguage> = bundled_languages()
            .into_iter()
            .filter(|l| l.def.name == name)
            .collect();
        assert_eq!(
            matches.len(),
            1,
            "expected exactly one bundled language named `{name}`; found {}. A cell that \
             names a shipped spec must resolve to that spec and not to a same-named twin.",
            matches.len(),
        );
        matches.remove(0)
    }
}

#[cfg(test)]
#[path = "../../tests/support/capture_recursive_oracle.rs"]
mod recursive_oracle;

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::grammar::SyntaxExpr;
    use mettail_ast::types::TypeExpr;
    use proc_macro2::Span;
    use std::ptr;
    use syn::Ident;

    fn id(s: &str) -> Ident {
        Ident::new(s, Span::call_site())
    }

    fn assert_same_slots(actual: &[FieldSlot<'_>], expected: &[FieldSlot<'_>]) {
        assert_eq!(actual.len(), expected.len());
        for (actual, expected) in actual.iter().zip(expected) {
            assert_eq!(actual.name, expected.name);
            assert_eq!(actual.optional, expected.optional);
            match (&actual.source, &expected.source) {
                (FieldSlotSource::TokenText, FieldSlotSource::TokenText) => {},
                (
                    FieldSlotSource::GuestBody { open: actual_open, close: actual_close },
                    FieldSlotSource::GuestBody {
                        open: expected_open,
                        close: expected_close,
                    },
                ) => {
                    assert_eq!(*actual_open, *expected_open);
                    assert_eq!(*actual_close, *expected_close);
                },
                (FieldSlotSource::Param(actual), FieldSlotSource::Param(expected)) => {
                    assert!(ptr::eq(*actual, *expected));
                },
                _ => panic!("field-slot source changed during iterative conversion"),
            }
        }
    }

    fn nested_term_context_fixture() -> Vec<TermParam> {
        vec![
            TermParam::Simple {
                name: id("head"),
                ty: TypeExpr::Base(id("Proc")),
            },
            TermParam::Optional {
                params: vec![
                    TermParam::GuardBody { name: id("guard") },
                    TermParam::Optional {
                        params: vec![TermParam::Simple {
                            name: id("nested"),
                            ty: TypeExpr::Base(id("Name")),
                        }],
                    },
                ],
            },
            TermParam::Abstraction {
                binder: id("x"),
                body: id("body"),
                ty: TypeExpr::Arrow {
                    domain: Box::new(TypeExpr::Base(id("Name"))),
                    codomain: Box::new(TypeExpr::Base(id("Proc"))),
                },
            },
        ]
    }

    #[test]
    fn iterative_capture_walkers_match_recursive_oracles() {
        let term_context = nested_term_context_fixture();

        let mut actual_declarations = Vec::new();
        push_declaration_order(&term_context, false, &mut actual_declarations);
        let mut expected_declarations = Vec::new();
        recursive_oracle::push_declaration_order(&term_context, false, &mut expected_declarations);
        assert_same_slots(&actual_declarations, &expected_declarations);

        for name in ["head", "guard", "nested", "missing"] {
            let actual = find_param(&term_context, name);
            let expected = recursive_oracle::find_param(&term_context, name);
            assert_eq!(
                actual.map(|(_, optional)| optional),
                expected.map(|(_, optional)| optional)
            );
            match (actual, expected) {
                (Some((actual, _)), Some((expected, _))) => assert!(ptr::eq(actual, expected)),
                (None, None) => {},
                _ => panic!("find_param result changed during iterative conversion"),
            }
        }

        let syntax_pattern = vec![
            SyntaxExpr::Literal("prefix".into()),
            SyntaxExpr::Param(id("head")),
            SyntaxExpr::Op(PatternOp::Opt {
                inner: vec![
                    SyntaxExpr::TokenKind { name: id("Word"), bind: Some(id("word")) },
                    SyntaxExpr::Param(id("nested")),
                    SyntaxExpr::GuestBody {
                        open: id("Open"),
                        close: id("Close"),
                        bind: id("guest"),
                    },
                ],
            }),
        ];
        let abstraction_names = HashSet::new();
        let mut actual_pattern = Vec::new();
        walk_pattern(
            &syntax_pattern,
            &term_context,
            &abstraction_names,
            false,
            &mut actual_pattern,
        );
        let mut expected_pattern = Vec::new();
        recursive_oracle::walk_pattern(
            &syntax_pattern,
            &term_context,
            &abstraction_names,
            false,
            &mut expected_pattern,
        );
        assert_same_slots(&actual_pattern, &expected_pattern);
    }

    #[test]
    fn capture_walkers_handle_20k_nesting_on_a_256k_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let mut nested_param = TermParam::Simple {
                    name: id("leaf"),
                    ty: TypeExpr::Base(id("Proc")),
                };
                for _ in 0..20_000 {
                    nested_param = TermParam::Optional { params: vec![nested_param] };
                }
                let term_context = vec![nested_param];

                let mut declarations = Vec::new();
                push_declaration_order(&term_context, false, &mut declarations);
                assert_eq!(declarations.len(), 1);
                assert!(declarations[0].optional);
                assert!(matches!(find_param(&term_context, "leaf"), Some((_, true))));

                let mut nested_pattern =
                    SyntaxExpr::TokenKind { name: id("Word"), bind: Some(id("leaf")) };
                for _ in 0..20_000 {
                    nested_pattern = SyntaxExpr::Op(PatternOp::Opt { inner: vec![nested_pattern] });
                }
                let syntax_pattern = [nested_pattern];
                let mut slots = Vec::new();
                walk_pattern(&syntax_pattern, &[], &HashSet::new(), false, &mut slots);
                assert_eq!(slots.len(), 1);
                assert!(slots[0].optional);
            })
            .expect("spawn low-stack capture-walker gate")
            .join()
            .expect("capture walkers must not consume nesting-proportional call stack");
    }

    #[test]
    fn no_capture_returns_none() {
        // A capture-free rule keeps every seam on its byte-identical path.
        let tc = vec![TermParam::Simple {
            name: id("a"),
            ty: TypeExpr::Base(id("Num")),
        }];
        let sp = vec![SyntaxExpr::Param(id("a"))];
        assert!(capture_layout(&tc, &sp).is_none());
    }

    #[test]
    fn captures_only_are_in_syntax_order() {
        // `"tag" w@Word` → one TokenText field named `w`.
        let sp = vec![
            SyntaxExpr::Literal("tag".into()),
            SyntaxExpr::TokenKind { name: id("Word"), bind: Some(id("w")) },
        ];
        let layout = capture_layout(&[], &sp).expect("has a capture");
        assert!(layout.scope.is_none());
        assert_eq!(layout.non_scope.len(), 1);
        assert_eq!(layout.non_scope[0].name, "w");
        assert!(matches!(layout.non_scope[0].kind, CaptureFieldKind::TokenText));
    }

    #[test]
    fn capture_adjacent_to_string_param_does_not_swap() {
        // F.1 no-swap: `w@Word s` where `s:StringLiteral` — BOTH fields lower to
        // `String`. The layout MUST bind strictly by syntax position: `w`
        // (capture, from the pattern) first, then `s` (param, from the context).
        let tc = vec![TermParam::Simple {
            name: id("s"),
            ty: TypeExpr::Base(id("StringLiteral")),
        }];
        let sp = vec![
            SyntaxExpr::TokenKind { name: id("Word"), bind: Some(id("w")) },
            SyntaxExpr::Param(id("s")),
        ];
        let layout = capture_layout(&tc, &sp).expect("has a capture");
        assert!(layout.scope.is_none());
        assert_eq!(layout.non_scope.len(), 2);
        // Position 0 is the capture `w`; position 1 is the param `s`. A swap
        // would reverse these (and be silent, since both are `String`).
        assert_eq!(layout.non_scope[0].name, "w");
        assert!(matches!(layout.non_scope[0].kind, CaptureFieldKind::TokenText));
        assert_eq!(layout.non_scope[1].name, "s");
        assert!(matches!(layout.non_scope[1].kind, CaptureFieldKind::Term(_)));
    }

    #[test]
    fn guest_body_is_an_opaque_capture_leaf() {
        // L9-4: `*flt(node, FltOpenBacktick, FltCloseBacktick)` → one GuestBody
        // field named `node`, carrying the opener/closer kinds.
        let sp = vec![SyntaxExpr::GuestBody {
            open: id("FltOpenBacktick"),
            close: id("FltCloseBacktick"),
            bind: id("node"),
        }];
        let layout = capture_layout(&[], &sp).expect("has a capture");
        assert!(layout.scope.is_none());
        assert_eq!(layout.non_scope.len(), 1);
        assert_eq!(layout.non_scope[0].name, "node");
        match &layout.non_scope[0].kind {
            CaptureFieldKind::GuestBody { open, close } => {
                assert_eq!(open.to_string(), "FltOpenBacktick");
                assert_eq!(close.to_string(), "FltCloseBacktick");
            },
            _ => panic!("expected GuestBody kind"),
        }
    }

    #[test]
    fn capture_with_abstraction_puts_scope_last() {
        // F.1 full-support: `"lam" w@Word x . body` with `^x.body:[Num -> Num]`
        // → non-scope [TokenText w], trailing Scope (binder x + body fold in).
        let tc = vec![TermParam::Abstraction {
            binder: id("x"),
            body: id("body"),
            ty: TypeExpr::Arrow {
                domain: Box::new(TypeExpr::Base(id("Num"))),
                codomain: Box::new(TypeExpr::Base(id("Num"))),
            },
        }];
        let sp = vec![
            SyntaxExpr::Literal("lam".into()),
            SyntaxExpr::TokenKind { name: id("Word"), bind: Some(id("w")) },
            SyntaxExpr::Param(id("x")),
            SyntaxExpr::Literal(".".into()),
            SyntaxExpr::Param(id("body")),
        ];
        let layout = capture_layout(&tc, &sp).expect("has a capture");
        assert_eq!(layout.non_scope.len(), 1, "only the capture is a non-scope field");
        assert_eq!(layout.non_scope[0].name, "w");
        let scope = layout.scope.expect("abstraction yields a trailing Scope");
        assert!(!scope.multi);
    }
}
