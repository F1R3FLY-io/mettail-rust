//! ★ THE SURFACE-SYNONYMY GATE — *one denotation, one surface*, asserted per language from a
//! table the language itself generates.
//!
//! # What a surface synonym is, and why it is a defect rather than a convenience
//!
//! A grammar may spell one term more than one way. Rholang spells a quoted name three ways:
//!
//! ```text
//!   NQuote      . p:Proc |- "@" "(" p ")" : Name ;
//!   NQuoteShort . p:Proc |- "@" p         : Name ![{ Name::NQuote(…p…) }] fold prefix(220) canonical;
//!   NQuoteNil   .        |- "@" "Nil"     : Name ![{ Name::NQuote(…PZero…) }] fold;
//! ```
//!
//! Each is a distinct AST constructor, and before 2026-07-26 each rendered ITS OWN surface. That
//! makes `Display` a function of the CONSTRUCTOR rather than of the TERM, and composing it with
//! `Parse` — which elects a constructor from a surface, **context-dependently** — is then not a
//! fixpoint. One surface is shed per nesting layer:
//!
//! ```text
//!   (@(error)) <- @Nil ─▶ @(error) <- @Nil ─▶ @error <- @Nil ─▶ @error <- @Nil
//!                          ↑ layer 1          ↑ layer 2          ↑ fixpoint at layer 3
//! ```
//!
//! `gen_rholang_prop::inputbind_display_parse_roundtrip` asserts a fixpoint after ONE re-parse,
//! so it failed on every term whose synonym sat two layers deep — for months, as a single opaque
//! string mismatch that named neither the class nor the layer.
//!
//! # What this file asserts
//!
//! The `language!` macro derives the synonymy classes from the grammar's own fold bodies
//! (`macros/src/gen/syntax/synonymy.rs`) and emits three tables plus one entry point into every
//! language module:
//!
//! | item | content |
//! |---|---|
//! | `__SURFACE_SYNONYMY_CLASSES` | `(category, members, canonical)` — the derived classes |
//! | `__SURFACE_SYNONYMY_SAMPLES` | one parseable SAMPLE SURFACE per member, built from that member's own syntax pattern with each parameter filled by its category's simplest nullary surface |
//! | `__SURFACE_INERT_GROUPINGS` | the bracket-pair rules whose body is the identity |
//! | `__surface_synonymy_normalise(cat, surface, structured)` | `surface ──parse──▶ term ──Display──▶ surface`, on either string seam |
//!
//! and this file is the shared harness over them. Three properties, in increasing strength:
//!
//! 1. **STABILITY** — `D(P(s)) == D(P(D(P(s))))` for every sample. The surface a class emits must
//!    be a fixpoint of `Display∘Parse`. This is the property the roundtrip proptest needs, and it
//!    covers the inert groupings too (whose brackets are NOT collapsed — see below).
//! 2. **SINGLETON AFTER NORMALISATION** — all samples of one alias class normalise to the SAME
//!    string. This is the property that makes the NEXT synonym impossible instead of discovered:
//!    a newly added member shows up in the table and breaks this line by name.
//! 3. **BOTH SEAMS AGREE** — 1 and 2 hold identically through `Cat::parse` and
//!    `Cat::parse_via_wpda`. A one-seam gate cannot see a seam-dependent election, and a
//!    seam-dependent election was one of the two hypotheses the 2026-07-26 investigation had to
//!    refute by measurement.
//!
//! # ⚠ An INERT GROUPING is deliberately NOT collapsed
//!
//! `NParen . n:Name |- "(" n ")" : Name ![{ n.clone() }] fold;` is the identity, so `NParen(x)`
//! and `x` are one term with two surfaces — the same shape as an alias class. Collapsing it was
//! IMPLEMENTED and REFUTED by measurement on 2026-07-26: the brackets are the ONLY observable
//! separating the kept-grouping reading from its transparent twin, so deleting them from the
//! surface collapses `|R|_distinct` and disambiguates at the display layer.
//!
//! ```text
//!   rd_a1_budget::genuinely_ambiguous_witness_strict_boundary
//!       `@((a)!(0))!()` has TWO readings differing only by the kept `NParen`; under
//!       transparency both displayed `@(a!(0))!()` and the budget boundary moved.
//!   rholang_tests::realize_mode_contract_pins
//!       ::prefix_bounded_alternatives_enumerate_display_distinct_family   (USER-APPROVED)
//!       requires `@Nil!(@(@Nil)!())` and `@Nil!(@@Nil!())` to stay a display-DISTINCT family.
//! ```
//!
//! So an inert grouping is held to property 1 only — which measurement shows it already
//! satisfies, because the parser re-elects the grouping from its own brackets.

#![allow(clippy::items_after_test_module)]

/// One language's generated synonymy tables, addressed uniformly.
struct LanguageGate {
    name: &'static str,
    classes: &'static [(&'static str, &'static [&'static str], &'static str)],
    samples: &'static [(&'static str, &'static [(&'static str, &'static str)])],
    inert_groupings: &'static [&'static str],
    normalise: fn(&str, &str, bool) -> Result<String, String>,
}

/// Every bundled language that generates the tables. A language is listed here once and inherits
/// all three properties; nothing per-language is asserted by hand.
fn gates() -> Vec<LanguageGate> {
    let mut out: Vec<LanguageGate> = Vec::new();
    #[cfg(feature = "rholang")]
    out.push(LanguageGate {
        name: "Rholang",
        classes: mettail_languages::rholang::__SURFACE_SYNONYMY_CLASSES,
        samples: mettail_languages::rholang::__SURFACE_SYNONYMY_SAMPLES,
        inert_groupings: mettail_languages::rholang::__SURFACE_INERT_GROUPINGS,
        normalise: mettail_languages::rholang::__surface_synonymy_normalise,
    });
    #[cfg(feature = "calculator")]
    out.push(LanguageGate {
        name: "Calculator",
        classes: mettail_languages::calculator::__SURFACE_SYNONYMY_CLASSES,
        samples: mettail_languages::calculator::__SURFACE_SYNONYMY_SAMPLES,
        inert_groupings: mettail_languages::calculator::__SURFACE_INERT_GROUPINGS,
        normalise: mettail_languages::calculator::__surface_synonymy_normalise,
    });
    #[cfg(feature = "lambda")]
    out.push(LanguageGate {
        name: "Lambda",
        classes: mettail_languages::lambda::__SURFACE_SYNONYMY_CLASSES,
        samples: mettail_languages::lambda::__SURFACE_SYNONYMY_SAMPLES,
        inert_groupings: mettail_languages::lambda::__SURFACE_INERT_GROUPINGS,
        normalise: mettail_languages::lambda::__surface_synonymy_normalise,
    });
    #[cfg(feature = "ambient")]
    out.push(LanguageGate {
        name: "Ambient",
        classes: mettail_languages::ambient::__SURFACE_SYNONYMY_CLASSES,
        samples: mettail_languages::ambient::__SURFACE_SYNONYMY_SAMPLES,
        inert_groupings: mettail_languages::ambient::__SURFACE_INERT_GROUPINGS,
        normalise: mettail_languages::ambient::__surface_synonymy_normalise,
    });
    out
}

/// The two string seams, named for the failure message.
const SEAMS: [(&str, bool); 2] = [("parse_via_wpda", false), ("parse", true)];

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  0 — THE TEETH TEST. A gate over an empty table asserts nothing.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// The derivation must actually FIND the classes it is supposed to find. Rholang's `Name` class
/// `{ NQuote, NQuoteNil, NQuoteShort }` is the one this whole mechanism was built for, and its
/// canonical member is declared in `languages/src/rholang.rs`; if the derivation silently stopped
/// producing it, every assertion below would pass vacuously.
#[cfg(feature = "rholang")]
#[test]
fn the_derivation_finds_the_class_it_was_built_for() {
    let classes = mettail_languages::rholang::__SURFACE_SYNONYMY_CLASSES;
    let name_class = classes
        .iter()
        .find(|(cat, members, _)| *cat == "Name" && members.contains(&"NQuote"))
        .expect(
            "Rholang's `Name` alias class {NQuote, NQuoteNil, NQuoteShort} is no longer derived — \
             `classify_fold_alias_shape` or the class construction has stopped seeing the fold \
             bodies that declare it",
        );
    let mut members = name_class.1.to_vec();
    members.sort_unstable();
    assert_eq!(
        members,
        vec!["NQuote", "NQuoteNil", "NQuoteShort"],
        "the `Name` class membership moved — re-derive it from the fold bodies in rholang.rs"
    );
    assert_eq!(
        name_class.2, "NQuoteShort",
        "the declared canonical member moved. It is fixed by a SIBLING rule's surface: \
         `InputBindQuoted . pat:Proc, n:Name |- \"@\" pat \"<-\" n` spells its quoted pattern with \
         the SHORTHAND, so choosing `NQuote` would leave a surface that still sheds a layer on \
         re-parse."
    );
    assert!(
        mettail_languages::rholang::__SURFACE_INERT_GROUPINGS.contains(&"NParen"),
        "`NParen` is no longer classified as an inert grouping — the identity-body classifier \
         stopped matching it"
    );
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  1 — STABILITY. Every sample surface is a fixpoint of `Display ∘ Parse`, on both seams.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// `D(P(s)) == D(P(D(P(s))))` for every generated sample of every class of every language.
///
/// This is the property `inputbind_display_parse_roundtrip` needs and the one whose absence made
/// that test fail as an opaque string mismatch. Here the failure names the language, the class,
/// the member and the seam.
#[test]
fn every_class_members_surface_is_a_display_parse_fixpoint() {
    let mut failures: Vec<String> = Vec::new();
    for gate in gates() {
        for (category, samples) in gate.samples {
            for (member, surface) in *samples {
                for (seam_name, structured) in SEAMS {
                    let once = match (gate.normalise)(category, surface, structured) {
                        Ok(s) => s,
                        Err(e) => {
                            failures.push(format!(
                                "  [{}/{category}/{member}/{seam_name}] the generated sample \
                                 surface {surface:?} does not parse: {e}",
                                gate.name
                            ));
                            continue;
                        },
                    };
                    let twice = match (gate.normalise)(category, &once, structured) {
                        Ok(s) => s,
                        Err(e) => {
                            failures.push(format!(
                                "  [{}/{category}/{member}/{seam_name}] the DISPLAYED form \
                                 {once:?} does not re-parse: {e}",
                                gate.name
                            ));
                            continue;
                        },
                    };
                    if once != twice {
                        failures.push(format!(
                            "  [{}/{category}/{member}/{seam_name}] not a fixpoint:\n        \
                             sample   {surface:?}\n        D(P(s))  {once:?}\n        \
                             D(P(D(P(s)))) {twice:?}",
                            gate.name
                        ));
                    }
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "★ {} surface(s) are not a fixpoint of `Display ∘ Parse`. A synonym whose surface is not \
         stable sheds one surface per nesting layer, so a term two layers deep fails the \
         display/parse roundtrip:\n{}",
        failures.len(),
        failures.join("\n"),
    );
}

/// The same stability, for the INERT GROUPINGS — which are deliberately NOT collapsed (see the
/// module header), so their brackets must be re-elected by the parser from the surface `Display`
/// emits. Measured for Rholang's `NParen`: `(@Nil)` ⇒ `(@Nil)`.
#[cfg(feature = "rholang")]
#[test]
fn an_inert_groupings_brackets_are_re_elected_from_its_own_surface() {
    use mettail_languages::rholang::Name;
    // `parse` and `parse_via_wpda` carry different error types, so each seam renders its own.
    fn show(name: &str, surface: &str, structured: bool) -> String {
        let r = if structured {
            Name::parse(surface)
                .map(|t| format!("{t}"))
                .map_err(|e| format!("{e:?}"))
        } else {
            Name::parse_via_wpda(surface)
                .map(|t| format!("{t}"))
                .map_err(|e| format!("{e:?}"))
        };
        r.unwrap_or_else(|e| panic!("`{surface}` must parse on the {name} seam: {e}"))
    }
    for surface in ["(@Nil)", "((@Nil))", "(x)"] {
        for (seam_name, structured) in SEAMS {
            let once = show(seam_name, surface, structured);
            let twice = show(seam_name, &once, structured);
            assert_eq!(
                once, twice,
                "★ the inert grouping's surface is not a fixpoint on the {seam_name} seam \
                 ({surface:?}). Its brackets are NOT collapsed by design — they are the only \
                 observable separating the kept-grouping reading from its transparent twin — so \
                 they must survive a re-parse."
            );
        }
    }
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  2 — SINGLETON AFTER NORMALISATION. ★ THE LOUD LINE.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// Every member of an alias class normalises to the SAME surface.
///
/// The samples of one class are, by construction, the SAME denotation written each member's own
/// way (each member's syntax pattern filled with the same nullary child), so any difference in
/// their normalised surface is a surface synonym that `Display` has not collapsed.
///
/// ★ This is the line a newly added synonym breaks. It names the class, the two members and the
/// two surfaces, so the fix — annotate the intended member `canonical` — is stated by the failure
/// itself rather than discovered.
#[test]
fn every_alias_class_is_a_singleton_after_normalisation() {
    let mut failures: Vec<String> = Vec::new();
    let mut checked = 0usize;
    for gate in gates() {
        for (category, samples) in gate.samples {
            if samples.len() < 2 {
                continue;
            }
            for (seam_name, structured) in SEAMS {
                let mut normalised: Vec<(&str, String)> = Vec::with_capacity(samples.len());
                for (member, surface) in *samples {
                    match (gate.normalise)(category, surface, structured) {
                        Ok(s) => normalised.push((member, s)),
                        Err(e) => failures.push(format!(
                            "  [{}/{category}/{member}/{seam_name}] sample {surface:?} does not \
                             parse: {e}",
                            gate.name
                        )),
                    }
                }
                checked += 1;
                let Some((first_member, first)) = normalised.first() else {
                    continue;
                };
                for (member, other) in normalised.iter().skip(1) {
                    if other != first {
                        failures.push(format!(
                            "  [{}/{category}/{seam_name}] the class is NOT a singleton after \
                             normalisation:\n        {first_member} ⇒ {first:?}\n        \
                             {member} ⇒ {other:?}\n      Annotate the intended member with the \
                             `canonical` keyword in the grammar (after the eval mode, alongside \
                             `right` / `prefix(N)`), so `Display` renders the whole class through \
                             it.",
                            gate.name
                        ));
                    }
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "★ {} surface synonym(s) survive normalisation. One denotation must have ONE surface, or \
         `Display ∘ Parse` is not a fixpoint and a term sheds one surface per nesting \
         layer:\n{}",
        failures.len(),
        failures.join("\n"),
    );
    assert!(
        checked > 0,
        "no multi-member class was checked — the generated sample table is empty, so this gate is \
         vacuous. Either the derivation stopped finding classes or no member could be given a \
         filler surface."
    );
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  3 — COVERAGE. A class the gate cannot exercise must be VISIBLE, not silently skipped.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// A member with a `.*sep` list, a capture, or an optional group has no single filler surface, so
/// it contributes no sample. That is a deliberate conservatism — a guessed surface would be a
/// worse gate than none — but it must be reported rather than hidden, so this test prints the
/// coverage table and fails only if a class that DECLARES a canonical member has no samples at
/// all (which would mean the declaration is unverified).
#[test]
fn every_class_with_a_declared_canonical_member_is_exercised() {
    let mut unexercised: Vec<String> = Vec::new();
    for gate in gates() {
        for (category, members, canonical) in gate.classes {
            let samples = gate
                .samples
                .iter()
                .find(|(c, _)| c == category)
                .map(|(_, s)| *s)
                .unwrap_or(&[]);
            println!(
                "  {:<10} {category:<12} members={members:?} canonical={canonical:?} \
                 samples={}/{}",
                gate.name,
                samples.len(),
                members.len()
            );
            if !canonical.is_empty() && samples.len() < 2 {
                unexercised.push(format!(
                    "  [{}/{category}] declares `{canonical}` canonical but only {} of {} members \
                     could be given a sample surface, so the declaration is unverified",
                    gate.name,
                    samples.len(),
                    members.len()
                ));
            }
        }
    }
    assert!(
        unexercised.is_empty(),
        "★ a declared canonical member is not exercised by the gate:\n{}",
        unexercised.join("\n"),
    );
}
