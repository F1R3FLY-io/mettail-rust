//! #131 — the `Ident`-capture ROUTING GATE.
//!
//! A rule that declares an `m:Ident` param promises the reader one thing: the
//! parser consumes ONE identifier token there and the AST field holds its text.
//! Two entirely separate machines can keep that promise, and which one claims a
//! rule is decided by the rule's SHAPE, not by anything the grammar author wrote:
//!
//! | rule shape | claimed by | capture carried as |
//! |---|---|---|
//! | LITERAL-leading (`Tagged . m:Ident \|- "tag" m`) | the binder machine, [`super::binder::classify_binder_in`] | [`super::binder::BinderPosition::IdentTextCapture`] |
//! | OPERAND-leading (`Call . recv:Num, m:Ident, … \|- recv "." m …`) | the Pratt machine, [`super::infix::classify_rule_public`] | [`mettail_prattail::binding_power::MixfixPart::capture_kind`] |
//!
//! # The defect this gate exists to make impossible
//!
//! Before #131 the Pratt machine had NO representation for a token consumption:
//! every `MixfixPart` was a category operand or a repetition of them. An
//! `m:Ident` in an operand-leading rule therefore produced a part whose
//! `operand_category` was the string `"Ident"` — which is not a declared
//! category. Nothing rejected it. `emit_mixfix_parts_fn` resolved it through
//! `position(..).unwrap_or(0)` to category 0, the FIRST declared category, and
//! the walker dutifully sub-parsed that category where an identifier stood.
//!
//! The rule then had NO realizable reading, at any arity, and the only diagnostic
//! the user ever saw was
//!
//! ```text
//! expected no accepting branch reached end of input
//! (canonical-GLL: no realizable readings), found end of input
//! ```
//!
//! which names neither `Ident`, nor the rule, nor the param. A grammar author
//! reading that message has no path to the cause. Worse, the LITERAL-leading
//! twin of the same declaration worked perfectly, so the feature appeared to
//! function and failed only on the shape that mattered — Rholang's collapsed
//! `EMethodCall`.
//!
//! # What the gate asserts
//!
//! For every rule `R` and every param `p : Ident` declared in `R`'s term
//! context, the emitted parser must contain exactly one consumer for `p`, and it
//! must be a TOKEN consumer — one of the two rows in the table above.
//!
//! Three distinct failures are therefore rejected, and each of them was a real,
//! measured state of this codebase rather than a hypothetical:
//!
//! 1. [`IdentRoutingFault::MixfixPartNotACapture`] — the Pratt machine claimed
//!    the rule but modelled the param as a category operand. THIS IS THE #131
//!    ROOT, and its red evidence is the pre-fix failure of
//!    `ident_param_beside_a_vec_collection_parses_at_every_arity`.
//! 2. [`IdentRoutingFault::PrattLeadingOperand`] — the param is the Pratt LHS.
//!    The LHS is a fully parsed sub-term of some category, and there is no
//!    `Ident` category for it to be a sub-term of, so no representation exists
//!    at all; the `unwrap_or(0)` sibling in the binding-power tables would
//!    silently make it category 0.
//! 3. [`IdentRoutingFault::Unclaimed`] — NEITHER machine claims the rule, so the
//!    position is never consumed by anything. This is the shape the campaign
//!    recorded as "a fork emitted into a dispatcher that is never called":
//!    every symbol involved exists and compiles, and the path is dead.
//!
//! # Why a gate rather than a comment
//!
//! Each of the three was found by a fixture, not by review, and each survived a
//! full build and a green type-check first. The gate converts all three from
//! "silently unparseable" into "the build stops and names the rule, the param
//! and the machine". It is checked at MACRO-EXPANSION time because that is the
//! only moment at which the rule, its classification and its emission are all in
//! scope simultaneously.
//!
//! # Inertness
//!
//! No shipped grammar declares an `Ident` param — the measurement that says so
//! is `cargo check -p languages --tests` completing across all 49 languages with
//! the gate active. So this gate can only reject a NEW grammar that reintroduces
//! one of the three faults, which is exactly its purpose.

use mettail_ast::grammar::{GrammarRule, SyntaxExpr, TermParam};
use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::quote_spanned;

use super::binder::{classify_binder_in, BinderPosition};

/// Why a declared `Ident` param has no token consumer in the emitted parser.
///
/// Carried separately from the message so the unit tests can assert WHICH fault
/// was detected rather than pattern-matching on prose.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum IdentRoutingFault {
    /// The Pratt machine claimed the rule and produced a `MixfixPart` for the
    /// param, but the part is a CATEGORY OPERAND (`capture_kind == None`)
    /// instead of a token capture. ★ The #131 root.
    MixfixPartNotACapture,
    /// The param is the Pratt machine's LEFT OPERAND. An LHS is a parsed
    /// sub-term of a declared category; `Ident` is a token class and has none.
    PrattLeadingOperand,
    /// Neither machine claimed the rule, so nothing consumes the param.
    Unclaimed,
}

impl IdentRoutingFault {
    /// The remedy sentence, kept next to the fault so the two cannot drift.
    fn remedy(&self) -> &'static str {
        match self {
            Self::MixfixPartNotACapture => {
                "the part must carry `capture_kind: Some(\"Ident\")` — see \
                 `capture_kind_of` in `infix.rs`, which is the single place a param \
                 type becomes a capture kind"
            },
            Self::PrattLeadingOperand => {
                "move the `Ident` param out of the leading position: an operand-leading \
                 rule's FIRST param is its left operand and must name a declared category"
            },
            Self::Unclaimed => {
                "give the rule a shape one of the two machines recognises — a \
                 LITERAL-leading rule reaches the binder machine, an OPERAND-leading \
                 rule reaches the Pratt machine"
            },
        }
    }
}

/// One rejected `(rule, param)` pair.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct IdentRoutingViolation {
    pub(crate) rule_label: String,
    pub(crate) param_name: String,
    pub(crate) fault: IdentRoutingFault,
}

impl IdentRoutingViolation {
    /// The build-stopping message. Names the rule, the param, the fault and the
    /// remedy — everything the pre-#131 diagnostic left out.
    pub(crate) fn message(&self) -> String {
        format!(
            "mettail: rule `{}` declares the `Ident` param `{}`, but the emitted parser \
             has no token consumer for it ({:?}): {}. Report this as a macro bug if you \
             believe this rule shape should be supported.",
            self.rule_label,
            self.param_name,
            self.fault,
            self.fault.remedy(),
        )
    }
}

/// The names of a rule's `Ident`-typed params, in declaration order.
///
/// Only top-level [`TermParam::Simple`] params are considered: an `Ident` inside
/// an `#opt(...)` group is routed by the opt-group machinery, which has its own
/// `IdentText` arm on both the dispatch and the extraction side, and is checked
/// by the binder path below through the group's inner positions.
fn ident_param_names(rule: &GrammarRule) -> Vec<String> {
    let Some(tc) = rule.term_context.as_ref() else {
        return Vec::new();
    };
    let mut names = Vec::with_capacity(tc.len());
    for p in tc {
        if let TermParam::Simple { name, ty } = p {
            if ty.is_ident_text() {
                names.push(name.to_string());
            }
        }
    }
    names
}

/// Does `positions` (or any `#opt(...)` group nested in it) consume `param` as an
/// identifier token?
fn binder_consumes(positions: &[BinderPosition], param: &str) -> bool {
    let mut work: Vec<&BinderPosition> = positions.iter().rev().collect();
    while let Some(position) = work.pop() {
        match position {
            BinderPosition::IdentTextCapture { param_name } if param_name == param => return true,
            BinderPosition::OptionalGroup { positions: inner_positions, .. } => {
                work.extend(inner_positions.iter().rev());
            },
            _ => {},
        }
    }
    false
}

/// Check one rule. Returns every violation it carries (a rule may declare more
/// than one `Ident` param, and reporting only the first would hide the rest).
pub(crate) fn check_rule(rule: &GrammarRule, language: &LanguageDef) -> Vec<IdentRoutingViolation> {
    let pratt = super::infix::classify_rule_public(rule);
    check_against(rule, pratt.as_ref(), Some(language))
}

/// The gate proper, evaluated against a CALLER-SUPPLIED Pratt classification.
///
/// [`check_rule`] derives that classification itself; this seam exists so a test
/// can hand in a MUTATED one and prove the gate rejects it. Without the seam the
/// only way to exercise the `MixfixPartNotACapture` arm would be to revert
/// `capture_kind_of` in the source — which is precisely the kind of "mutation
/// that may or may not have applied" this campaign has been burned by.
///
/// `language` is optional because `classify_binder_in` needs it and a Pratt-only
/// check does not; `None` means "the binder machine is not available", which is
/// strictly conservative (it can only produce MORE violations, never fewer).
pub(crate) fn check_against(
    rule: &GrammarRule,
    pratt: Option<&mettail_prattail::binding_power::InfixRuleInfo>,
    language: Option<&LanguageDef>,
) -> Vec<IdentRoutingViolation> {
    let idents = ident_param_names(rule);
    if idents.is_empty() {
        return Vec::new();
    }
    let binder = language.and_then(|l| classify_binder_in(rule, l));
    // The Pratt machine's LEFT operand is `syntax_pattern[0]` when that is a
    // Param. It is not represented in `mixfix_parts` (which covers only the
    // parts AFTER the trigger), so it has to be read off the pattern directly.
    let pratt_lhs_param: Option<String> = match (&pratt, rule.syntax_pattern.as_ref()) {
        (Some(_), Some(sp)) => match sp.first() {
            Some(SyntaxExpr::Param(p)) => Some(p.to_string()),
            _ => None,
        },
        _ => None,
    };
    let mut violations = Vec::with_capacity(idents.len());
    for name in idents {
        // Route 1 — the Pratt machine, via a capture `MixfixPart`.
        if let Some(info) = &pratt {
            if let Some(part) = info.mixfix_parts.iter().find(|p| p.param_name == name) {
                match part.capture_kind.is_some() {
                    true => continue,
                    false => {
                        violations.push(IdentRoutingViolation {
                            rule_label: rule.label.to_string(),
                            param_name: name,
                            fault: IdentRoutingFault::MixfixPartNotACapture,
                        });
                        continue;
                    },
                }
            }
            if pratt_lhs_param.as_deref() == Some(name.as_str()) {
                violations.push(IdentRoutingViolation {
                    rule_label: rule.label.to_string(),
                    param_name: name,
                    fault: IdentRoutingFault::PrattLeadingOperand,
                });
                continue;
            }
        }
        // Route 2 — the binder machine, via an `IdentTextCapture` position.
        if let Some(shape) = &binder {
            if binder_consumes(&shape.positions, &name) {
                continue;
            }
        }
        violations.push(IdentRoutingViolation {
            rule_label: rule.label.to_string(),
            param_name: name,
            fault: IdentRoutingFault::Unclaimed,
        });
    }
    violations
}

/// Run the gate over a whole language. Returns `Some(compile_error!(..))` tokens
/// — one per violation, in rule order — when any rule carries an unrouted `Ident`
/// param, and `None` when the language is clean.
///
/// # ⚠ WHY `compile_error!` AND NOT `panic!`, MEASURED
///
/// The first version of this gate panicked, on the reasoning that a codegen
/// INVARIANT is not a user-facing diagnostic tier and that the sibling hardenings
/// in `emit_mixfix_parts_fn` and `semantic_actions.rs` panic too.
///
/// That reasoning was WRONG, and the measurement that refutes it is recorded
/// here so it is not re-derived: `[profile.dev]` builds this proc-macro crate
/// under the **cranelift** backend, and a panic raised inside a
/// cranelift-compiled proc macro does not unwind back across the `proc_macro`
/// bridge. `rustc` aborts instead:
///
/// ```text
/// fatal runtime error: Rust cannot catch foreign exceptions, aborting
/// error: could not compile `languages` (test "ident_param_capture")
///   process didn't exit successfully: `rustc …` (signal: 6, SIGABRT)
/// ```
///
/// The panic's payload — the rule, the param, the fault, the remedy — is NEVER
/// PRINTED. A gate that stops the build while saying nothing is strictly worse
/// than the defect it replaces: the pre-#131 diagnostic at least named a
/// position in the input. This was observed directly, by mutating
/// `capture_kind_of` back to its pre-#131 behaviour and building the fixture.
///
/// `compile_error!` is immune: it is a TOKEN the gate emits, rendered by `rustc`
/// at the macro call site, and it needs no unwinding at all.
///
/// ⚠ The sibling `panic!`s noted above are subject to the same swallowing. They
/// are proven INERT (no shipped grammar reaches them), so they are backstops
/// rather than diagnostics, and this gate is what stands in front of them: it
/// rejects the malformed grammar BEFORE codegen can reach a mute abort.
///
/// ★ #141-R2: this gate is invoked from `macros/src/lib.rs`, at the macro
/// boundary, where its `return` discards the WHOLE expansion. It used to be
/// called from inside `generate_wpda_engine_module`, the eleventh of twelve
/// generators, where returning tokens only replaced that one module's
/// contribution — `language!` carried on and still spilled five `include!` files
/// for a grammar it had already rejected.
pub(crate) fn enforce(language: &LanguageDef) -> Option<TokenStream> {
    let violations = enforce_violations(language);
    if violations.is_empty() {
        return None;
    }
    let mut out = TokenStream::new();
    for (label, message) in violations {
        // ★ #141 change 6 — SPANNED AT THE OFFENDING RULE. This was
        // `quote! { compile_error!(#m); }`, whose tokens carry `Span::call_site()`,
        // so `rustc` drew its caret under the `language!` invocation — the whole
        // grammar — while `check_rule` had `rule.label` in hand the entire time.
        // For Rholang that is a 400-line macro call and a caret on all of it.
        out.extend(quote_spanned!(label.span() => compile_error!(#message);));
    }
    Some(out)
}

/// Every violation in `language`, each paired with the IDENT of the rule that
/// carries it.
///
/// Split out of [`enforce`] so the span's PROVENANCE is assertable. In a unit
/// test `proc_macro2::Span` is a fallback span with no file, line or equality —
/// there is nothing to compare — so a cell that called [`enforce`] and read the
/// rendered tokens could not tell a rule-spanned refusal from a call-site-spanned
/// one; the token text is byte-identical. Returning the `Ident` moves the claim
/// to something a test CAN pin: that the label handed to `quote_spanned!` is the
/// offending rule's own. The remaining step, `label.span()`, is one line above
/// and in view.
///
/// (The rendered caret is observable only out of process. It was measured
/// there — see this campaign's `red0` fixture — but that measurement cannot be a
/// committed unit test.)
pub(crate) fn enforce_violations(language: &LanguageDef) -> Vec<(&syn::Ident, String)> {
    let mut violations: Vec<(&syn::Ident, String)> = Vec::new();
    for rule in &language.terms {
        for violation in check_rule(rule, language) {
            violations.push((&rule.label, violation.message()));
        }
    }
    violations
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::grammar::{rule_fixture, PatternOp};
    use mettail_ast::types::{CollectionType, TypeExpr};
    use proc_macro2::Span;
    use syn::Ident;

    fn id(s: &str) -> Ident {
        Ident::new(s, Span::call_site())
    }

    fn simple(name: &str, ty: &str) -> TermParam {
        TermParam::Simple {
            name: id(name),
            ty: TypeExpr::Base(id(ty)),
        }
    }

    fn vec_param(name: &str, elem: &str) -> TermParam {
        TermParam::Simple {
            name: id(name),
            ty: TypeExpr::Collection {
                coll_type: CollectionType::Vec,
                element: Box::new(TypeExpr::Base(id(elem))),
            },
        }
    }

    fn param(name: &str) -> SyntaxExpr {
        SyntaxExpr::Param(id(name))
    }

    fn lit(s: &str) -> SyntaxExpr {
        SyntaxExpr::Literal(s.to_string())
    }

    fn sep(collection: &str, separator: &str) -> SyntaxExpr {
        SyntaxExpr::Op(PatternOp::Sep {
            collection: id(collection),
            separator: separator.to_string(),
            source: None,
        })
    }

    fn rule(label: &str, cat: &str, tc: Vec<TermParam>, sp: Vec<SyntaxExpr>) -> GrammarRule {
        GrammarRule {
            term_context: Some(tc),
            syntax_pattern: Some(sp),
            ..rule_fixture(id(label), id(cat))
        }
    }

    fn language_with(rules: Vec<GrammarRule>) -> LanguageDef {
        LanguageDef {
            terms: rules,
            ..crate::gen::empty_language_for_tests()
        }
    }

    /// `Call`'s exact shape: operand-leading, `m:Ident` between the trigger and a
    /// `*sep` collection. This is Rholang's collapsed `EMethodCall`.
    fn call_rule() -> GrammarRule {
        rule(
            "Call",
            "Num",
            vec![simple("recv", "Num"), simple("m", "Ident"), vec_param("args", "Num")],
            vec![param("recv"), lit("."), param("m"), lit("("), sep("args", ","), lit(")")],
        )
    }

    /// `Tagged`'s exact shape: literal-leading, routed by the binder machine.
    fn tagged_rule() -> GrammarRule {
        rule("Tagged", "Num", vec![simple("m", "Ident")], vec![lit("tag"), param("m")])
    }

    /// ★ THE CONTROL, asserted alongside every rejection below so a gate that
    /// rejected everything would fail here rather than look strict.
    ///
    /// `Call` must PASS, and for the RIGHT reason — the classifier gave its `m`
    /// part a `capture_kind`. That is asserted separately rather than inferred
    /// from the gate's silence.
    #[test]
    fn the_call_shape_is_routed_and_its_part_is_really_a_capture() {
        let r = call_rule();
        let lang = language_with(vec![r.clone()]);
        assert_eq!(
            check_rule(&r, &lang),
            Vec::new(),
            "`Call` is the shape `capture_kind` was added for; rejecting it would reject \
             the very grammar #131 exists to support",
        );
        let info = super::super::infix::classify_rule_public(&r)
            .expect("`Call` is claimed by the Pratt machine");
        let part = info
            .mixfix_parts
            .iter()
            .find(|p| p.param_name == "m")
            .expect("`m` is a mixfix part of `Call`");
        assert_eq!(
            part.capture_kind.as_deref(),
            Some("Ident"),
            "the gate must pass because the part IS a capture, not because the gate is \
             blind to this shape",
        );
    }

    /// ★ THE RED, AS A UNIT. Mutation: strip the part's `capture_kind` — EXACTLY
    /// the pre-#131 classifier output, when `capture_kind_of` did not exist and
    /// every part was a category operand. The gate must reject it, and must name
    /// the root fault rather than the generic one.
    ///
    /// ⚠ THE MUTATION IS ASSERTED TO HAVE APPLIED. A patch that silently failed
    /// to apply would otherwise report green while proving nothing — a failure
    /// mode this campaign has recorded.
    #[test]
    fn a_mixfix_ident_part_that_is_not_a_capture_is_rejected() {
        let r = call_rule();
        let lang = language_with(vec![r.clone()]);
        // Control passes BEFORE the mutation.
        assert_eq!(check_rule(&r, &lang), Vec::new(), "control must pass pre-mutation");

        let mut info = super::super::infix::classify_rule_public(&r)
            .expect("`Call` is claimed by the Pratt machine");
        let part = info
            .mixfix_parts
            .iter_mut()
            .find(|p| p.param_name == "m")
            .expect("`m` is a mixfix part of `Call`");
        // THE MUTATION APPLIED — if it were already `None`, everything below
        // would be asserting nothing.
        assert_eq!(
            part.capture_kind.take().as_deref(),
            Some("Ident"),
            "the mutation only means something if the un-mutated part IS a capture",
        );
        assert!(part.capture_kind.is_none(), "the mutation must have taken effect");

        let violations = check_against(&r, Some(&info), Some(&lang));
        assert_eq!(
            violations
                .iter()
                .map(|v| v.fault.clone())
                .collect::<Vec<_>>(),
            vec![IdentRoutingFault::MixfixPartNotACapture],
            "the gate must reject the pre-#131 shape, and name the ROOT fault",
        );
        let msg = violations[0].message();
        assert!(msg.contains("Call"), "the message must name the rule: {msg}");
        assert!(msg.contains('`'), "the message must quote the param: {msg}");
        assert!(msg.contains("capture_kind"), "the message must name the remedy: {msg}");
    }

    /// Control + red for the LEADING-OPERAND fault: an `Ident` as the Pratt LHS
    /// has no representation at all (an LHS is a parsed sub-term of a declared
    /// category, and `Ident` is a token class).
    #[test]
    fn an_ident_as_the_pratt_left_operand_is_rejected() {
        let control = call_rule();
        let control_lang = language_with(vec![control.clone()]);
        assert_eq!(
            check_rule(&control, &control_lang),
            Vec::new(),
            "control must pass both before and after the mutated case is evaluated",
        );

        // MUTATION: swap `Call`'s LHS from `recv:Num` to `m:Ident`.
        let mutated = rule(
            "LhsIdent",
            "Num",
            vec![simple("m", "Ident"), simple("x", "Num")],
            vec![param("m"), lit("+"), param("x")],
        );
        let lang = language_with(vec![mutated.clone()]);
        // The mutation applied: the leading syntax item really is the `Ident` param.
        assert!(
            matches!(mutated.syntax_pattern.as_ref().expect("pattern").first(), Some(SyntaxExpr::Param(p)) if p == "m"),
            "the mutation must have put the `Ident` param in the leading position",
        );
        assert_eq!(
            check_rule(&mutated, &lang)
                .iter()
                .map(|v| v.fault.clone())
                .collect::<Vec<_>>(),
            vec![IdentRoutingFault::PrattLeadingOperand],
        );

        // Control still passes AFTER.
        assert_eq!(check_rule(&control, &control_lang), Vec::new(), "control must still pass");
    }

    /// The literal-leading twin routes through the binder machine and must PASS.
    /// Without this the gate could be "satisfied" by rejecting every `Ident` that
    /// is not a mixfix capture — which would break `Tagged`, green throughout.
    #[test]
    fn the_literal_leading_shape_is_routed_by_the_binder_machine() {
        let r = tagged_rule();
        let lang = language_with(vec![r.clone()]);
        assert_eq!(
            check_rule(&r, &lang),
            Vec::new(),
            "`Tagged` is routed by `classify_binder_in` → `IdentTextCapture`; the gate \
             must not disturb the path that has worked throughout",
        );
        let shape = classify_binder_in(&r, &lang).expect("`Tagged` is binder-classified");
        assert!(
            binder_consumes(&shape.positions, "m"),
            "and it must pass because the binder machine really consumes `m`",
        );
    }

    /// A rule with no `Ident` param is not the gate's business.
    #[test]
    fn rules_without_an_ident_param_are_untouched() {
        let r = rule("Lit", "Num", vec![], vec![lit("#")]);
        let lang = language_with(vec![r.clone()]);
        assert_eq!(check_rule(&r, &lang), Vec::new());
        assert!(ident_param_names(&r).is_empty(), "and it has no `Ident` param to route");
    }

    /// ★ `enforce` must emit a `compile_error!` CARRYING THE MESSAGE — the gate is
    /// only worth having if the grammar author can read why the build stopped.
    ///
    /// ⚠ This asserts the RENDERED TOKENS, not merely that something was
    /// returned. The first version of this gate panicked instead, and the panic's
    /// payload was swallowed whole by the cranelift proc-macro abort (see
    /// [`enforce`]) — a gate that stopped the build while saying nothing. The only
    /// way to keep that from recurring silently is to assert the text.
    #[test]
    fn enforce_emits_a_readable_compile_error() {
        let lang = language_with(vec![rule(
            "LhsIdent",
            "Num",
            vec![simple("m", "Ident"), simple("x", "Num")],
            vec![param("m"), lit("+"), param("x")],
        )]);
        let tokens = enforce(&lang).expect("the gate must reject this language");
        let rendered = tokens.to_string();
        assert!(
            rendered.contains("compile_error"),
            "the diagnostic must be a `compile_error!`, which renders without \
             unwinding: {rendered}",
        );
        for needle in ["LhsIdent", "has no token consumer", "leading position"] {
            assert!(
                rendered.contains(needle),
                "the diagnostic must contain {needle:?}: {rendered}",
            );
        }
    }

    /// And `enforce` must return `None` for the two shapes that are correctly
    /// routed — the control for the test above.
    #[test]
    fn enforce_admits_both_routed_shapes() {
        assert!(
            enforce(&language_with(vec![call_rule(), tagged_rule()])).is_none(),
            "both routed shapes must pass; a gate that rejected them would be \
             rejecting the grammars #131 exists to support",
        );
    }

    /// One `compile_error!` PER VIOLATION: a language with two unrouted params
    /// must report both, or fixing the first would only reveal the second.
    #[test]
    fn every_violation_is_reported_not_just_the_first() {
        let lang = language_with(vec![
            rule(
                "LhsIdentA",
                "Num",
                vec![simple("m", "Ident"), simple("x", "Num")],
                vec![param("m"), lit("+"), param("x")],
            ),
            rule(
                "LhsIdentB",
                "Num",
                vec![simple("n", "Ident"), simple("y", "Num")],
                vec![param("n"), lit("-"), param("y")],
            ),
        ]);
        let rendered = enforce(&lang).expect("both rules are rejected").to_string();
        assert_eq!(
            rendered.matches("compile_error").count(),
            2,
            "one diagnostic per violation: {rendered}",
        );
        assert!(rendered.contains("LhsIdentA") && rendered.contains("LhsIdentB"));
    }

    /// ★ #141 change 6 — the refusal is spanned at THE OFFENDING RULE, and the
    /// span source is asserted rather than assumed.
    ///
    /// MUTATION: a two-rule language in which only the SECOND rule offends. The
    /// diagnostic that `enforce` renders is identical whichever span it carries,
    /// so the only assertable claim is the one this cell makes — that the ident
    /// `enforce` hands to `quote_spanned!` is `LhsIdentB`'s own label, not
    /// `Clean`'s, and not a call-site span synthesised from nothing.
    ///
    /// CONTROL that must NOT discriminate: the clean rule contributes no
    /// violation at all, so a gate keyed on rule ORDER rather than on the
    /// offending rule would be caught here as a wrong label rather than passing
    /// on a lucky index.
    #[test]
    fn each_refusal_carries_the_offending_rules_own_label() {
        let clean = rule("Clean", "Num", vec![simple("x", "Num")], vec![param("x")]);
        let offending = rule(
            "LhsIdentB",
            "Num",
            vec![simple("n", "Ident"), simple("y", "Num")],
            vec![param("n"), lit("-"), param("y")],
        );
        let lang = language_with(vec![clean, offending]);

        let violations = enforce_violations(&lang);
        assert_eq!(violations.len(), 1, "exactly the second rule offends");
        let (label, message) = &violations[0];
        assert_eq!(
            label.to_string(),
            "LhsIdentB",
            "★ the span must come from the offending rule's label — before this \
             change the tokens carried `Span::call_site()` and `rustc` drew its \
             caret under the whole `language!` invocation",
        );
        assert!(
            message.contains("LhsIdentB") && message.contains('n'),
            "the message names the rule and the param independently of the span: {message}",
        );
    }
}
