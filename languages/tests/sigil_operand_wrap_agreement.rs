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
//! | too EAGER | the bracket is kept where it is not needed. Two constructors that render the SAME surface then disagree about it, so `Display ∘ Parse` sheds one surface per nesting layer. | `POutput2Plus(NQuoteShort(PZero), a, [])` and `POutputNil2Plus(a, [])` both render `@Nil!(Nil,)`; the first was wrapped and the second was not, and `gen_rholang_prop::inputbind_display_parse_roundtrip` failed at depth 2. |
//! | too LAX | the bracket is dropped where the re-parse needs it, and `Display` emits a surface the grammar REJECTS. | `Display(NQuoteShort(Mul(send, Nil)))` emitted `@@a!(a,) * Nil`, which does not parse: `@` takes `@@a!(a,)` and `* Nil` is stranded. |
//!
//! Each was found by a single proptest draw. **A draw is a poor detector**: it finds an instance
//! only when the generator happens to build one, it reports two opaque strings, and the same
//! predicate can be wrong for a constructor no draw ever reaches.
//!
//! # ★ A SURFACE-FIRST GATE CANNOT REJECT THIS CLASS (2026-07-28)
//!
//! The first version of this file asked the question of every rule from a SAMPLE SURFACE the macro
//! composed out of that rule's syntax pattern — and then recovered the term by PARSING that
//! surface. It stayed green while `Display(NQuote(MGet(NegProc(a), PZero)))` emitted the
//! unparseable `@-a.get(Nil)`, and a controlled A/B (the fix reverted, the defect re-armed)
//! confirmed it could not go red. Two reasons, both measured:
//!
//! 1. **Direction.** A row recovered by parsing can only ever test a term the parser ELECTS. The
//!    defect class is exactly *"terms whose `Display` surface the parser does not elect back"*, so
//!    those terms are unreachable from a composed string by construction.
//! 2. **Depth, and folding.** Sample parameters were nullary FILLERS: ground, and self-delimiting.
//!    A ground argument is what a `fold` rule consumes, so `- Nil . get ( Nil )` did not even
//!    denote `MGet(NegProc(…), …)` — it denoted `MGet(error, Nil)`. And the composition is
//!    space-joined, which moves the election on its own:
//!
//!    ```text
//!      Proc::parse("- a . get ( a )")  ─▶  NegProc(MGet(a, a))
//!      Proc::parse("-a.get(a)")        ─▶  MGet(NegProc(a), a)     ← the shape at issue
//!    ```
//!
//! So this file now carries a **TERM-FIRST** leg: the macro CONSTRUCTS the term out of the
//! language's own constructors — leaves are single identifiers, which have one reading — asks
//! `Display` for its surface, and holds that surface to the two directions. With the fix reverted
//! it reports **45** rejected surfaces where the surface-first legs report none.
//!
//! It is the CONSTRUCTOR-surface counterpart of `literal_domain_agreement.rs`, which asserts the
//! same *Display ⊆ acceptor* discipline for LITERAL categories in both directions.
//!
//! # What is asserted
//!
//! *Surface-first* (`__SIGIL_OPERAND_WRAP_SAMPLES`, one row per sigil FRAME x operand rule x
//! filler regime — ground and variable):
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
//! *Term-first* (`__SIGIL_OPERAND_WRAP_TERM_ROWS`, one row per operand rule and per (operand rule
//! with a wrap RECURSION x rule of its leading operand's category)):
//!
//! 4. **`Display` of the constructed frame parses**, and
//! 5. **is a fixpoint** — the same two directions, asked of a term rather than of a string.
//!
//! ⚠ A rule with no single filler surface, or with a `.*sep` list, a capture, a binder, an optional
//! group, or a parameter whose category has no leaf — contributes no row rather than a guessed
//! one, and the coverage tests print what was skipped instead of hiding it.

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
    /// The TERM-FIRST leg. `(operand_category, frame_result_category, frame_label, frame_prefix,
    /// operand_rule_label, leading_operand_rule_label)`; an empty leading label names the operand
    /// rule's own depth-1 term.
    term_rows: &'static [(
        &'static str,
        &'static str,
        &'static str,
        &'static str,
        &'static str,
        &'static str,
    )],
    /// `(operand_category, operand_rule_label, leading_operand_rule_label) -> Display` of the
    /// sigil frame built around that CONSTRUCTED term. `None` when the pair names no
    /// constructible term.
    term_surface: fn(&str, &str, &str) -> Option<String>,
    /// `(operand_category, sample_surface) -> the operand as Display renders it after the sigil`.
    wrap: fn(&str, &str) -> Result<String, String>,
    /// `(frame_result_category, surface) -> Display(parse(surface))`.
    normalise: fn(&str, &str) -> Result<String, String>,
}

/// The frame surface a row composes: `prefix + <operand as Display renders it> + suffix`.
///
/// ⚠ SPACE-JOINED, and that was a measured correction. Concatenating the three pieces directly
/// produced `@Nil<- @ Nil`, whose missing separator made 194 rows "fail" for the GATE's reason
/// rather than the predicate's. The frame's pieces are rendered from its own pattern items, which
/// are space-joined, so the composition must be too; the parser is whitespace-tolerant, so this is
/// the frame's real surface up to formatting.
fn compose(prefix: &str, rendered: &str, suffix: &str) -> String {
    [prefix, rendered, suffix]
        .iter()
        .filter(|p| !p.is_empty())
        .copied()
        .collect::<Vec<_>>()
        .join(" ")
}

fn gates() -> Vec<LanguageGate> {
    let mut out: Vec<LanguageGate> = Vec::new();
    #[cfg(feature = "rholang")]
    out.push(LanguageGate {
        name: "Rholang",
        samples: mettail_languages::rholang::__SIGIL_OPERAND_WRAP_SAMPLES,
        term_rows: mettail_languages::rholang::__SIGIL_OPERAND_WRAP_TERM_ROWS,
        term_surface: mettail_languages::rholang::__sigil_term_frame_surface,
        wrap: mettail_languages::rholang::__sigil_operand_wrap_surface,
        normalise: mettail_languages::rholang::__sigil_frame_normalise,
    });
    out
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  0 — TEETH. A gate over an empty table asserts nothing.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// The table must contain the shapes the two known defects lived on: an operand-leading SEND
/// (whose wrap was too eager) and a binary INFIX (whose wrap is load-bearing). If the derivation
/// stops producing them, every assertion below passes vacuously.
#[cfg(feature = "rholang")]
#[test]
fn the_table_contains_the_shapes_the_defects_lived_on() {
    let samples = mettail_languages::rholang::__SIGIL_OPERAND_WRAP_SAMPLES;
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

/// ★ THE TERM-FIRST TEETH, and the two reasons this leg exists.
///
/// **1 — depth.** The table above fills every parameter with a NULLARY filler, and a nullary
/// constructor is self-delimiting by construction, so for an operand-leading rule it can only ever
/// place a self-delimiting term in the slot `__at_sigil_operand_needs_wrap` RECURSES into. The
/// shapes that make the recursion answer differently — a prefix application, an infix, a send —
/// are outside its sample space however many rows it has.
///
/// **2 — direction.** Every row above is a STRING the macro composes, and the term it is about is
/// recovered by PARSING that string. A row like that can only test a term the parser ELECTS — and
/// the defect class is exactly *"terms whose `Display` surface the parser does not elect back"*.
/// Measured, and it is not subtle: the composed sample is space-joined, and
///
/// ```text
///   Proc::parse("- a . get ( a )")  ─▶  NegProc(MGet(a, a))    ← what a surface-first row measures
///   Proc::parse("-a.get(a)")        ─▶  MGet(NegProc(a), a)    ← the shape at issue
/// ```
///
/// A controlled A/B settled it: with the `classify_unary_prefix_shape` guard in
/// `self_delimiting_sigil_arms_for` disabled — the defect re-armed — every surface-first row stayed
/// GREEN, at depth 1 and at depth 2, under both filler regimes, while these term-first rows go RED.
///
/// This asserts the term table reaches the exact pair the defect lived on and that BOTH branches
/// of the wrap recursion are reachable from it. Without the second check the leg could be a
/// depth-1 re-run wearing a longer table.
#[cfg(feature = "rholang")]
#[test]
fn the_term_first_table_reaches_a_prefix_application_in_the_leading_slot() {
    let rows = mettail_languages::rholang::__SIGIL_OPERAND_WRAP_TERM_ROWS;
    assert!(!rows.is_empty(), "no term-first sigil-operand rows were derived at all");
    assert!(
        rows.iter()
            .any(|(_, _, _, _, op, ld)| *op == "MGet" && *ld == "NegProc"),
        "the term table no longer carries `MGet` with `NegProc` in its leading slot — the exact \
         pair `gen_rholang_prop::name_display_parse_roundtrip` failed on (2026-07-28).\n  \
         MGet rows present: {:?}",
        rows.iter()
            .filter(|(_, _, _, _, op, _)| *op == "MGet")
            .map(|(_, _, _, _, _, ld)| *ld)
            .collect::<Vec<_>>()
    );
    // The operand is WRAPPED iff the frame's own prefix is followed by the bracket, which the row
    // carries so this test needs no knowledge of the language's sigil.
    let (mut bare, mut wrapped, mut uncovered) = (0usize, 0usize, 0usize);
    for (opcat, _, _, prefix, op, lead) in rows {
        match (mettail_languages::rholang::__sigil_term_frame_surface)(opcat, op, lead) {
            None => uncovered += 1,
            Some(surface) => match surface.strip_prefix(*prefix) {
                Some(rest) if rest.trim_start().starts_with('(') => wrapped += 1,
                _ => bare += 1,
            },
        }
    }
    assert!(
        bare > 0 && wrapped > 0,
        "the term rows exercise only ONE branch of the wrap recursion (bare {bare}, wrapped \
         {wrapped}) — the leg is as blind as the table it repairs"
    );
    println!(
        "  term-first rows: {} (bare {bare}, wrapped {wrapped}, uncovered {uncovered})",
        rows.len()
    );
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
            let composed = compose(prefix, &rendered, suffix);
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
            let composed = compose(prefix, &rendered, suffix);
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
//  3 — TERM-FIRST: build the term, ask `Display`, and hold the answer to the same two directions.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// Walk the term-first table, applying `check` to each constructed frame surface.
///
/// Returns `(checked, uncovered, failures)`. `uncovered` counts pairs that name no constructible
/// term — a rule with a `.*sep` list, a capture, a binder or an optional group has no single child
/// to build, and a guessed one would be a worse gate than none. The count is REPORTED by
/// `the_term_first_coverage_is_reported` rather than absorbed.
fn run_term_first<F>(mut check: F) -> (usize, usize, Vec<String>)
where
    F: FnMut(&LanguageGate, &str, &str) -> Option<String>,
{
    let mut failures: Vec<String> = Vec::new();
    let (mut checked, mut uncovered) = (0usize, 0usize);
    for gate in gates() {
        for (opcat, result_cat, frame, _prefix, op_label, lead_label) in gate.term_rows {
            let Some(surface) = (gate.term_surface)(opcat, op_label, lead_label) else {
                uncovered += 1;
                continue;
            };
            checked += 1;
            if let Some(why) = check(&gate, result_cat, &surface) {
                let shown = if lead_label.is_empty() {
                    (*op_label).to_string()
                } else {
                    format!("{op_label}<{lead_label}")
                };
                failures.push(format!("  [{}/{frame}/{shown}] {why}", gate.name));
            }
        }
    }
    (checked, uncovered, failures)
}

/// ★ THE DIRECTION THAT EMITS AN UNPARSEABLE SURFACE — asked of a CONSTRUCTED term, which is the
/// only way to ask it about a term the parser would not have elected.
#[test]
fn every_term_first_sigil_frame_surface_parses_back() {
    let (checked, uncovered, failures) = run_term_first(|gate, result_cat, surface| {
        (gate.normalise)(result_cat, surface)
            .err()
            .map(|e| format!("`Display` emits {surface:?}, and the grammar REJECTS it: {e}"))
    });
    assert!(
        failures.is_empty(),
        "★ {} constructed term(s) whose `Display` surface does not parse back. \
         `__at_sigil_operand_needs_wrap` dropped a bracket the re-parse needs — the TOO-LAX \
         direction:\n{}",
        failures.len(),
        failures.join("\n"),
    );
    assert!(
        checked > 0,
        "no term was constructed — the leg is vacuous (uncovered {uncovered})"
    );
}

/// ★ AND THE DUAL: the surface a constructed term renders must be a `Display` fixpoint, or it
/// sheds one spelling per nesting layer — the failure mode
/// `gen_rholang_prop::name_display_parse_roundtrip` reports as "converged in N extra layer(s)".
#[test]
fn every_term_first_sigil_frame_surface_is_a_display_fixpoint() {
    let (_checked, _uncovered, failures) = run_term_first(|gate, result_cat, surface| {
        let once = (gate.normalise)(result_cat, surface).ok()?;
        match (gate.normalise)(result_cat, &once) {
            Ok(twice) if twice == once => None,
            Ok(twice) => Some(format!(
                "the surface is not a fixpoint:\n        Display(t) {surface:?}\n        D(P(s))    \
                 {once:?}\n        D(P(D(P(s)))) {twice:?}"
            )),
            Err(e) => Some(format!("`{once}` does not re-parse: {e}")),
        }
    });
    assert!(
        failures.is_empty(),
        "★ {} constructed term(s) whose surface moves under re-parse — the TOO-EAGER \
         direction:\n{}",
        failures.len(),
        failures.join("\n"),
    );
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  4 — THE NAMED WITNESS. A sigil-led PREFIX APPLICATION is not a self-delimiting primary.
// ══════════════════════════════════════════════════════════════════════════════════════════════

/// ★ THE TERM THE DEPTH-1 GATE COULD NOT BUILD (2026-07-27, `gen_rholang_prop`).
///
/// `__at_sigil_operand_needs_wrap` drops the bracket for an operand-leading rule whose LEADING
/// OPERAND renders sigil-led. The recursion's premise is that a sigil opener keeps the whole
/// surface reachable at the sigil's binding-power cap. That premise holds for a sigil-led
/// PRIMARY (`@Nil!(…)`, `*a`, `{…}`) and FAILS for a sigil-led **same-category prefix
/// application**: `NegProc . a:Proc |- "-" a : Proc` puts its operand in its own category's
/// precedence ladder, so under the cap the `-` closes at its own prefix binding power and the
/// frame's tail is stranded.
///
/// ```text
///   term       NQuote(MGet(NegProc(PVar a), PZero))
///   before     @-a.get(Nil)     1:13 no accepting branch reached end of input   ✗
///   after      @(-a.get(Nil))   parses, canonical `@-(a.get(Nil))`, fixpoint    ✓
/// ```
///
/// Every sample the gate's table carries fills the leading-operand slot with the operand
/// category's NULLARY filler, and a nullary constructor is self-delimiting by construction — so
/// the class this pins is outside the depth-1 sample space. The generic repair is the depth-2
/// leg of the table (`__SIGIL_OPERAND_WRAP_LEAD_SAMPLES`); this is its named witness.
#[cfg(feature = "rholang")]
#[test]
fn a_sigil_led_prefix_application_does_not_delimit_the_frame_it_leads() {
    use mettail_languages::rholang::{Name, Proc};
    // Built by parsing, so the pin cannot drift from the surface it is about: this is exactly
    // the shrunk counterexample `MGet(NegProc(PVar a), PZero)`.
    let inner = Proc::parse("-a.get(Nil)").expect("`-a.get(Nil)` parses at Proc");
    assert_eq!(
        format!("{inner}"),
        "-a.get(Nil)",
        "the Proc-level rendering is the fixpoint this test builds on"
    );
    let quoted = Name::NQuote(std::sync::Arc::new(inner));
    let displayed = format!("{quoted}");
    let parsed = Name::parse(&displayed).unwrap_or_else(|e| {
        panic!(
            "★ `Display` emitted a surface the grammar REJECTS: {displayed:?}: {e}\n   \
             the `@`-operand kept no bracket around a frame whose LEADING OPERAND is a \
             sigil-led PREFIX APPLICATION (`-a`), which is not a self-delimiting primary at \
             the sigil's binding-power cap"
        )
    });
    let canonical = format!("{parsed}");
    let recanonical = format!(
        "{}",
        Name::parse(&canonical)
            .unwrap_or_else(|e| panic!("canonical {canonical:?} must parse: {e}"))
    );
    assert_eq!(canonical, recanonical, "the canonical surface must be a `Display` fixpoint");
}

/// ★ THE CONTRAST, so the repair stays MINIMAL. A sigil-led prefix whose operand is in a
/// DIFFERENT category (`PDrop . n:Name |- "*" n : Proc`) does not join `Proc`'s precedence
/// ladder: `@*a.get(Nil)` parses, and re-introducing a bracket there would be the too-eager
/// direction the file's second test guards. Measured 2026-07-27 over the whole sigil-led
/// cohort: of the sixteen `Proc` rules whose sample renders sigil-led, fifteen keep a postfix
/// tail after `@` and only `NegProc` — the sole SAME-category unary prefix among them — does
/// not.
#[cfg(feature = "rholang")]
#[test]
fn a_cross_category_sigil_prefix_still_delimits_the_frame_it_leads() {
    use mettail_languages::rholang::{Name, Proc};
    let inner = Proc::parse("*a.get(Nil)").expect("`*a.get(Nil)` parses at Proc");
    let quoted = Name::NQuote(std::sync::Arc::new(inner));
    assert_eq!(
        format!("{quoted}"),
        "@*a.get(Nil)",
        "a cross-category sigil prefix keeps the BARE spelling — the bracket would be the \
         too-eager direction"
    );
    assert!(Name::parse("@*a.get(Nil)").is_ok(), "and that bare spelling parses");
}

// ══════════════════════════════════════════════════════════════════════════════════════════════
//  5 — COVERAGE. What the gate could not exercise must be VISIBLE.
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

/// Prints the TERM-FIRST census: rows per (operand category, operand rule), and how many name no
/// constructible term. An uncovered pair is not a pass — it is a pair this gate says nothing
/// about — so the number is printed next to the number built rather than absorbed silently.
#[test]
fn the_term_first_coverage_is_reported() {
    for gate in gates() {
        let mut per_op: std::collections::BTreeMap<(&str, &str), usize> =
            std::collections::BTreeMap::new();
        let mut uncovered_labels: std::collections::BTreeSet<&str> =
            std::collections::BTreeSet::new();
        let (mut built, mut uncovered) = (0usize, 0usize);
        for (opcat, _, _, _, op_label, lead_label) in gate.term_rows {
            *per_op.entry((opcat, op_label)).or_default() += 1;
            match (gate.term_surface)(opcat, op_label, lead_label) {
                Some(_) => built += 1,
                None => {
                    uncovered += 1;
                    // Attribute the gap to the rule that actually caused it: when the OPERAND
                    // rule alone is already not constructible, naming the leading-operand rule
                    // would blame a rule that builds perfectly well on its own.
                    let operand_alone_builds = (gate.term_surface)(opcat, op_label, "").is_some();
                    uncovered_labels.insert(if operand_alone_builds && !lead_label.is_empty() {
                        lead_label
                    } else {
                        op_label
                    });
                },
            }
        }
        println!(
            "  {} term-first rows: {} total over {} (category, rule) pair(s); {built} built, \
             {uncovered} uncovered",
            gate.name,
            gate.term_rows.len(),
            per_op.len(),
        );
        if !uncovered_labels.is_empty() {
            println!("      not constructible: {:?}", uncovered_labels);
        }
        assert!(
            !per_op.is_empty(),
            "{}: the term-first leg produced no rows — the recursion is unguarded again",
            gate.name
        );
    }
}
