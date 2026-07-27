//! ★ THE SIGIL-OPERAND WRAP GATE — *a `Display` arm may not emit a surface its own grammar
//! cannot parse back.*
//!
//! # The invariant, and the two ways of getting it wrong
//!
//! A cross-category sigil prefix (`NQuoteShort . p:Proc |- "@" p : Name`, `prefix(220)`) parses
//! its operand under a very high binding-power cap, so the operand parser accepts only a
//! self-delimiting primary. `Display` therefore has to decide, per operand, whether to keep a
//! `( … )` around it — `__at_sigil_operand_needs_wrap`. **Both directions of getting that decision
//! wrong are silent**, and this repository reached both within one afternoon:
//!
//! | direction | what happens | witness |
//! |---|---|---|
//! | too EAGER | the bracket is kept where it is not needed. Two constructors that render the SAME surface then disagree about it, so `Display ∘ Parse` sheds one surface per nesting layer. | `POutput2Plus(NQuoteShort(PZero), a, [])` and `POutputNil2Plus(a, [])` both render `@Nil!(Nil,)`; the first was wrapped and the second was not, and `gen_rhocalc_prop::inputbind_display_parse_roundtrip` failed at depth 2. |
//! | too LAX | the bracket is dropped where the re-parse needs it, and `Display` emits a surface the grammar REJECTS. | `Display(NQuoteShort(Mul(send, Nil)))` emitted `@@a!(a,) * Nil`, which does not parse: `@` takes `@@a!(a,)` and `* Nil` is stranded. |
//!
//! Each was found by a single proptest draw. **A draw is a poor detector**: it finds an instance
//! only when the generator happens to build one, it reports two opaque strings, and the same
//! predicate can be wrong for a constructor no draw ever reaches. This file asks the question of
//! EVERY RULE of every category that can stand after a sigil prefix, from a sample surface the
//! macro builds out of that rule's own syntax pattern — so a newly declared constructor is
//! covered the moment it exists.
//!
//! It is the CONSTRUCTOR-surface counterpart of `literal_domain_agreement.rs`, which asserts the
//! same *Display ⊆ acceptor* discipline for LITERAL categories in both directions.
//!
//! # What is asserted
//!
//! For every `(operand_category, sigil_result_category, sigil, rule_label, sample_surface)` the
//! macro emits:
//!
//! 1. **The sample parses** at its operand category — otherwise the gate is measuring nothing.
//! 2. **The composed spelling parses.** `__sigil_operand_wrap_surface` renders the operand exactly
//!    as `Display` would after the sigil (with the bracket iff the predicate says so); prefixing
//!    the sigil must yield a surface the grammar accepts at the sigil's result category. This is
//!    the TOO-LAX direction.
//! 3. **The composed spelling is a `Display` fixpoint.** Re-parsing and re-rendering must return
//!    the same string. This is the TOO-EAGER direction: a bracket kept where a synonym would not
//!    keep it shows up here as a moving surface.
//!
//! ⚠ A rule whose pattern has no single filler surface — a `.*sep` list, a capture, an optional
//! group, or a parameter whose category has no nullary constructor — contributes no sample rather
//! than a guessed one, and the coverage test prints what was skipped instead of hiding it.

#![allow(clippy::items_after_test_module)]

/// One language's generated wrap-gate table, addressed uniformly.
struct LanguageGate {
    name: &'static str,
    samples: &'static [(
        &'static str,
        &'static str,
        &'static str,
        &'static str,
        &'static str,
        &'static str,
        &'static str,
    )],
    /// `(operand_category, sample_surface) -> the operand as Display renders it after the sigil`.
    wrap: fn(&str, &str) -> Result<String, String>,
    /// `(frame_result_category, surface) -> Display(parse(surface))`.
    normalise: fn(&str, &str) -> Result<String, String>,
}

fn gates() -> Vec<LanguageGate> {
    let mut out: Vec<LanguageGate> = Vec::new();
    #[cfg(feature = "rhocalc")]
    out.push(LanguageGate {
        name: "RhoCalc",
        samples: mettail_languages::rhocalc::__SIGIL_OPERAND_WRAP_SAMPLES,
        wrap: mettail_languages::rhocalc::__sigil_operand_wrap_surface,
        normalise: mettail_languages::rhocalc::__sigil_frame_normalise,
    });
    out
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  0 — TEETH. A gate over an empty table asserts nothing.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// The table must contain the shapes the two known defects lived on: an operand-leading SEND
/// (whose wrap was too eager) and a binary INFIX (whose wrap is load-bearing). If the derivation
/// stops producing them, every assertion below passes vacuously.
#[cfg(feature = "rhocalc")]
#[test]
fn the_table_contains_the_shapes_the_defects_lived_on() {
    let samples = mettail_languages::rhocalc::__SIGIL_OPERAND_WRAP_SAMPLES;
    assert!(!samples.is_empty(), "no sigil-operand samples were derived at all");
    for label in ["POutput", "Mul"] {
        assert!(
            samples.iter().any(|(_, _, _, _, _, l, _)| *l == label),
            "`{label}` is missing from the wrap-gate table — the sample derivation stopped \
             covering the shape class it belongs to, and the gate is that much weaker.\n  \
             have: {:?}",
            samples
                .iter()
                .map(|(_, _, _, _, _, l, _)| *l)
                .collect::<Vec<_>>()
        );
    }
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  1 — TOO LAX: every surface `Display` emits after the sigil must PARSE.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// ★ THE DIRECTION THAT EMITS AN UNPARSEABLE SURFACE.
#[test]
fn every_sigil_operand_surface_display_emits_parses_back() {
    let mut failures: Vec<String> = Vec::new();
    let mut checked = 0usize;
    for gate in gates() {
        for (opcat, result_cat, frame, prefix, suffix, label, sample) in gate.samples {
            let rendered = match (gate.wrap)(opcat, sample) {
                Ok(r) => r,
                Err(e) => {
                    failures.push(format!(
                        "  [{}/{frame}/{label}] the generated sample {sample:?} does not parse at \
                         its own category: {e}",
                        gate.name
                    ));
                    continue;
                },
            };
            // ⚠ SPACE-JOINED, and that was a measured correction. Concatenating the three
            // pieces directly produced `@Nil<- @ Nil`, whose missing separator made 194 rows
            // "fail" for the GATE's reason rather than the predicate's. The frame's pieces are
            // rendered from its own pattern items, which are space-joined, so the composition
            // must be too; the parser is whitespace-tolerant, so this is the frame's real
            // surface up to formatting.
            let composed = [*prefix, rendered.as_str(), *suffix]
                .iter()
                .filter(|p| !p.is_empty())
                .copied()
                .collect::<Vec<_>>()
                .join(" ");
            checked += 1;
            if let Err(e) = (gate.normalise)(result_cat, &composed) {
                failures.push(format!(
                    "  [{}/{frame}/{label}] `Display` emits `{composed}` in the `{frame}` frame, \
                     and the grammar REJECTS it: {e}\n        operand sample: \
                     {sample:?}\n        rendered as   : {rendered:?}",
                    gate.name
                ));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "★ {} sigil-operand surface(s) that `Display` emits do not parse back. \
         `__at_sigil_operand_needs_wrap` dropped a bracket the re-parse needs — the TOO-LAX \
         direction:\n{}",
        failures.len(),
        failures.join("\n"),
    );
    assert!(checked > 0, "no sample was composed — the gate is vacuous");
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  2 — TOO EAGER: the composed surface must be a `Display` fixpoint.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// ★ THE DIRECTION THAT SHEDS A SURFACE PER LAYER. A bracket kept where a synonym of the same
/// denotation would not keep it makes the composed surface move on re-parse, which is exactly
/// what `inputbind_display_parse_roundtrip` measured at depth 2 — here it names the rule.
#[test]
fn every_composed_sigil_surface_is_a_display_fixpoint() {
    let mut failures: Vec<String> = Vec::new();
    for gate in gates() {
        for (opcat, result_cat, frame, prefix, suffix, label, sample) in gate.samples {
            let Ok(rendered) = (gate.wrap)(opcat, sample) else {
                continue;
            };
            // ⚠ SPACE-JOINED, and that was a measured correction. Concatenating the three
            // pieces directly produced `@Nil<- @ Nil`, whose missing separator made 194 rows
            // "fail" for the GATE's reason rather than the predicate's. The frame's pieces are
            // rendered from its own pattern items, which are space-joined, so the composition
            // must be too; the parser is whitespace-tolerant, so this is the frame's real
            // surface up to formatting.
            let composed = [*prefix, rendered.as_str(), *suffix]
                .iter()
                .filter(|p| !p.is_empty())
                .copied()
                .collect::<Vec<_>>()
                .join(" ");
            let Ok(once) = (gate.normalise)(result_cat, &composed) else {
                continue;
            };
            match (gate.normalise)(result_cat, &once) {
                Ok(twice) if twice == once => {},
                Ok(twice) => failures.push(format!(
                    "  [{}/{frame}/{label}] the composed surface is not a fixpoint:\n        \
                     composed  {composed:?}\n        D(P(s))   {once:?}\n        D(P(D(P(s)))) \
                     {twice:?}",
                    gate.name
                )),
                Err(e) => failures.push(format!(
                    "  [{}/{frame}/{label}] `{once}` does not re-parse: {e}",
                    gate.name
                )),
            }
        }
    }
    assert!(
        failures.is_empty(),
        "★ {} composed sigil-operand surface(s) move under re-parse. Two constructors that render \
         the same surface disagree about the bracket — the TOO-EAGER direction, which sheds one \
         surface per nesting layer:\n{}",
        failures.len(),
        failures.join("\n"),
    );
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  3 — COVERAGE. What the gate could not exercise must be VISIBLE.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// Prints the per-category sample census. A rule with a `.*sep` list, a capture or an optional
/// group has no single filler surface and contributes nothing; that is deliberate conservatism —
/// a guessed surface would be a worse gate than none — but it is reported rather than hidden.
#[test]
fn the_wrap_gate_coverage_is_reported() {
    for gate in gates() {
        let mut per_cat: std::collections::BTreeMap<&str, usize> =
            std::collections::BTreeMap::new();
        for (opcat, _, _, _, _, _, _) in gate.samples {
            *per_cat.entry(opcat).or_default() += 1;
        }
        println!("  {} sigil-operand wrap samples:", gate.name);
        for (cat, n) in &per_cat {
            println!("      {cat:<14} {n} rule sample(s)");
        }
        assert!(
            !per_cat.is_empty(),
            "{}: no sigil-operand category produced a sample",
            gate.name
        );
    }
}
