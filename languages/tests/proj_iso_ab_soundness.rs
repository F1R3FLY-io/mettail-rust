//! ★ `@`-PROJECTION-ISOLATION ON ≡ OFF A/B SOUNDNESS GATE (2026-07-25).
//!
//! # Why this file exists
//!
//! The `@`-projection isolation facade (`macros/src/gen/runtime/wpda_codegen/
//! facade.rs`, `emit_projection_isolation`) is a divide-and-conquer *pre-pass* in
//! front of the monolithic canonical-GLL walker. When it declines it returns
//! `None` and the facade runs the walker verbatim — `ProjectionIsolation.v`
//! `T7_fallthrough_is_monolithic`.
//!
//! For most of its life that decline path had **no observable seam**: with the
//! facade permanently ON there was no way to ask "what would the walker alone have
//! said here?". That blindness is what allowed the G1 degenerate-tail defect
//! (2026-07-25) to exist and to be *reasoned about incorrectly*. The codegen
//! comment justified declining on an in-language shape by asserting that the
//! walker is "the authoritative/complete parser" — an assertion that had never been
//! measured, and that turns out to be **false** for a whole family of inputs.
//!
//! `PRATTAIL_NO_PROJ_ISOLATION` is the committed, permanent kill switch that opens
//! that seam, and this file is the gate that keeps it honest. It runs the OFF leg
//! in a **subprocess** (the switch is read once per process into a `OnceLock`, both
//! because the helpers sit on the parse hot path and because a value that changed
//! mid-process would poison the `__PROJ_MEMO_<Cat>` best-parse memo), then compares
//! the two legs input by input.
//!
//! # What is asserted
//!
//! | gate | property | rationale |
//! |------|----------|-----------|
//! | **A** | the switch is *effective* | a gate that silently no-ops is worse than no gate |
//! | **B** | `OFF accepts ⇒ ON accepts` | the facade may only ADD coverage; losing an input the walker handles is a regression |
//! | **C** | degenerate tail ≡ its non-degenerate sibling | the G1 invariant: emptying a `.*sep` tail must not change whether the frame parses |
//! | **D** | the G2 witnesses parse ON | pins the family whose production correctness rests *entirely* on the facade |
//! | **E** | reading-count table | a golden over both legs, so any drift in either direction is caught |
//! | **F** | single-seam parse-time budget | the executable form of `ProjectionIsolation.v` T3 |
//! | **F-all** | `_all`-seam walker legs == distinct spans, and its own time budget | the enumeration seam recurses through the facade too, and until #103/R3 nothing watched it |
//!
//! # "G3" — ★ CLOSED 2026-07-25 (#28)
//!
//! Gate E used to record that the facade returned FEWER readings than the walker for
//! a channel written as a *parenthesized grouping*: `Name::parse_via_wpda_all("(a)")`
//! yielded `[NParen(NVar a)]` with the facade ON and `[NParen(NVar a), NVar a]` with
//! it OFF. The walker treats `NParen . n:Name |- "(" n ")"` as a **transparent**
//! grouping and emits both the wrapped and the unwrapped reading; the projection
//! helper matched it as an ordinary frame, produced only the wrapped one, and then
//! short-circuited with `return Ok(..)` instead of unioning with the walker.
//!
//! It was *independent of the degenerate tail*: observable on `@(a)!(0)`, which
//! contains no `.*sep` operand at all and whose emitted code the G1 fix does not
//! touch.
//!
//! The `SepSeam::All` prologue now UNIONS with the monolithic walker
//! (`facade.rs::emit_projection_isolation_prologue`), so the four rows below moved
//! ON→OFF-equal and are re-pinned at their measured values. ONLY the enumeration
//! seam changed; the `SepSeam::Single` election seam is deliberately untouched.
//!
//! ## ⚠ THE HAZARD NOTE THAT STOOD HERE WAS WRONG, and is corrected rather than
//! ## deleted, because being wrong is the useful part
//!
//! It read: *"the repair would change the facade's short-circuit semantics and
//! therefore the USER-APPROVED reading-count goldens in
//! `rholang_tests.rs::branch_b_send_normalization_pins`."* **Measured 2026-07-25:
//! every one of those eight inputs moves by +0.** None has a `(`-grouped channel, so
//! no transparent twin arises for them. The grouped-channel multiset pins
//! (`bitnot (a)!(…)`, `bitnot ((a))!(false)`) are +0 as well — `bitnot …` is a
//! prefix-op frame, not a σ-led projection, so the projection helper never engages.
//!
//! The note had never been measured; it was inferred from "the repair touches the
//! facade, and those goldens are about the facade". That inference cost the change a
//! deferral. **Do not record a blast radius that has not been measured** — and when
//! a measurement contradicts a standing note, correct the note in place.
//!
//! What the repair actually rests on: the USER-APPROVED `realize_mode_contract_pins`
//! (2026-07-14, `rholang_tests.rs`) ALREADY requires both readings of
//! `@Nil!(@(@Nil)!())` to be enumerable, and passes only because it enters through
//! `parse_*_with_source`, where this prologue is not wired. The facade therefore
//! already contradicted an approved contract at the STRING entry; unioning makes the
//! string entry AGREE with that golden rather than break one.

use mettail_languages::rholang::*;

/// Env var that makes this binary run as the OFF-leg child.
const CHILD_MARKER: &str = "PROJ_ISO_AB_CHILD";
/// The committed kill switch (mirrors `facade.rs::PROJ_ISO_KILL_SWITCH_ENV`).
const KILL_SWITCH: &str = "PRATTAIL_NO_PROJ_ISOLATION";

/// The A/B corpus. Each row is `(id, source)`. `id` is stable and is the key the
/// parent/child legs join on, so rows may be reordered freely.
///
/// Groups:
///
/// * `dt-*` — degenerate `.*sep` tails (the G1 subject) and their siblings.
/// * `g2-*` — σ-led frames with a method-frame channel containing a nested
///   channel-first send (the G2 family — walker-incomplete).
/// * `grp-*` — parenthesized-grouping channels (the pinned G3 divergence).
/// * `ctl-*` — controls that must not move.
fn corpus() -> Vec<(&'static str, &'static str)> {
    vec![
        // ── G1: degenerate tail vs. its non-degenerate sibling ──
        ("dt-nil-0", "@Nil!(0,)"),
        ("dt-nil-1", "@Nil!(0,1)"),
        ("dt-quoted-0", "@a!(0,)"),
        ("dt-quoted-1", "@a!(0,1)"),
        ("dt-bare-0", "a!(0,)"),
        ("dt-bare-1", "a!(0,1)"),
        ("dt-persist-0", "@Nil!!(0,)"),
        ("dt-persist-1", "@Nil!!(0,1)"),
        // An intra-list DANGLING separator is NOT in the language (`.*sep` derives
        // `elem (sep elem)*`), and both legs must keep rejecting it. This is the
        // evidence-gated counterpart of the G1 fix: region-empty is bindable,
        // element-empty is not.
        ("dt-dangling", "@Nil!(0,1,)"),
        // ── G2: method-frame channel with a nested channel-first send ──
        ("g2-scalar", "@(Nil.set(a!(Nil) , Nil))!(Nil)"),
        ("g2-polyadic", "@(Nil.set(a!(Nil) , Nil))!(Nil,Nil)"),
        ("g2-degenerate", "@(Nil.set(a!(Nil) , Nil))!(Nil,)"),
        ("g2-no-nested-send", "@(Nil.set(Nil , Nil))!(Nil,)"),
        ("g2-no-method", "@(a!(Nil))!(Nil,)"),
        // The bare method frame and its grouping parse in BOTH legs — the walker
        // gap is created by the composition, not by either part.
        ("g2-part-method", "Nil.set(a!(Nil), Nil)"),
        ("g2-part-grouped", "(Nil.set(a!(Nil), Nil))"),
        ("g2-part-send", "a!(Nil)"),
        // ── G3: parenthesized-grouping channel (the CLOSED divergence) ──
        ("grp-scalar", "@(a)!(0)"),
        ("grp-polyadic", "@(a)!(0,1)"),
        ("grp-degenerate", "@(a)!(0,)"),
        // ── cov-*: the rows where the two legs elect DIFFERENT REPRESENTATIVES of the
        //    same semantic reading. Post-G3 these are what keep gate A able to fail.
        //
        //    ⚠ A measurement correction worth keeping. These rows were added believing
        //    `*(@(1)) + 2` was a row where the facade contributes a reading the walker
        //    never produces (ON=3 vs OFF=2, ON ⊄ OFF). That came from counting DEBUG
        //    strings, and Debug is a STRUCTURAL key: `semantic_hash` folds the
        //    sugar≡canonical alias `NQuoteShort` ≡ `NQuote`, so the facade's
        //    `NParen(NQuote(1))` and the walker's `NParen(NQuoteShort(1))` are ONE
        //    semantic key. Measured post-fix, both legs answer 2. The facade adds no
        //    semantically-new reading here; what differs is which SPELLING represents
        //    the class, which is exactly what `elected` below observes.
        ("cov-drop-paren-numeral", "*(@(1)) + 2"),
        ("cov-drop-numeral", "*(@1) + 2"),
        //    (The cleanest discriminator, `Name "(@Nil)"`, is a NAME and so rides in
        //    `render_leg` beside `name-paren` rather than in this `Proc` corpus.)
        // ── controls ──
        ("ctl-scalar-nil", "@Nil!(0)"),
        ("ctl-bare-scalar", "a!(0)"),
        ("ctl-deep-2", "@@Nil!(0)!(0)"),
        ("ctl-deep-3", "@@@Nil!(0)!(0)!(0)"),
    ]
}

/// One leg's observation for one row.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Obs {
    /// `true` iff the single-result string entry accepted.
    accepts: bool,
    /// Number of distinct-semantic-key readings, or `None` when `parse_all` erred.
    readings: Option<usize>,
    /// ★ The ELECTED representative (#28, 2026-07-25) — the single-result parse's
    /// structure, with the per-process fresh-variable counter normalised away.
    ///
    /// Added because closing G3 made the two legs agree on every reading COUNT in this
    /// corpus, which left gate A with nothing to discriminate on. The switch is still
    /// plainly effective; what it now changes is WHICH SPELLING of a semantic class each
    /// leg elects — `@Nil!(0)` elects the specific `POutputNil` with the facade ON and
    /// the generic `POutputShort(PZero, ..)` with it OFF, and the two display
    /// identically, so only structure reveals it.
    ///
    /// Counted separately from `readings` on purpose: gate E's golden compares
    /// `(accepts, readings)` and is deliberately NOT sensitive to the representative,
    /// because a representative change is not a disambiguation change.
    elected: String,
}

/// Strip the process-local fresh-variable counter out of a structural key.
///
/// ★ ESSENTIAL, not cosmetic. `UniqueId(N)` comes from a per-process counter, so the ON
/// leg (which has parsed the rows above it in THIS process) and the OFF leg (a fresh
/// child) stamp the same variable with different `N`. Without this every row would differ
/// between legs and gate A would pass vacuously — the exact failure mode it exists to
/// prevent.
fn canon(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut rest = s;
    while let Some(i) = rest.find("UniqueId(") {
        out.push_str(&rest[..i]);
        out.push_str("UniqueId(_");
        let after = &rest[i + "UniqueId(".len()..];
        let j = after.find(')').expect("UniqueId( is always closed");
        rest = &after[j..];
    }
    out.push_str(rest);
    out
}

fn observe(src: &str) -> Obs {
    mettail_runtime::clear_var_cache();
    let accepts = Proc::parse_via_wpda(src).is_ok();
    let readings = Proc::parse_via_wpda_all(src).ok().map(|v| v.len());
    mettail_runtime::clear_var_cache();
    let elected = match Proc::parse_via_wpda(src) {
        Ok(t) => canon(&format!("{t:?}")),
        Err(_) => "<ERR>".to_string(),
    };
    Obs { accepts, readings, elected }
}

/// Serialize one leg as `id\taccepts\treadings\telected` lines (readings `-1` = Err).
fn render_leg() -> String {
    let mut out = String::with_capacity(corpus().len() * 64);
    for (id, src) in corpus() {
        let o = observe(src);
        out.push_str(id);
        out.push('\t');
        out.push_str(if o.accepts { "1" } else { "0" });
        out.push('\t');
        out.push_str(&o.readings.map(|n| n as i64).unwrap_or(-1).to_string());
        out.push('\t');
        out.push_str(&o.elected);
        out.push('\n');
    }
    // The G3 minimal witnesses at the OPERAND category the projection helper composes.
    // Carried in the same stream so both legs report them.
    for (id, src) in [("name-paren", "(a)"), ("cov-name-paren-nil", "(@Nil)")] {
        mettail_runtime::clear_var_cache();
        let n = Name::parse_via_wpda_all(src).map(|v| v.len()).unwrap_or(0);
        mettail_runtime::clear_var_cache();
        let elected = match Name::parse_via_wpda(src) {
            Ok(t) => canon(&format!("{t:?}")),
            Err(_) => "<ERR>".to_string(),
        };
        out.push_str(&format!("{id}\t1\t{n}\t{elected}\n"));
    }
    out
}

fn parse_leg(text: &str) -> std::collections::BTreeMap<String, Obs> {
    let mut m = std::collections::BTreeMap::new();
    for line in text.lines() {
        let mut it = line.splitn(4, '\t');
        let (Some(id), Some(a), Some(r), Some(e)) = (it.next(), it.next(), it.next(), it.next())
        else {
            continue;
        };
        let r: i64 = r.parse().expect("reading count is an integer");
        m.insert(
            id.to_string(),
            Obs {
                accepts: a == "1",
                readings: if r < 0 { None } else { Some(r as usize) },
                elected: e.to_string(),
            },
        );
    }
    m
}

/// Run this same test binary as a child with the kill switch set, and read its
/// leg off stdout. A subprocess (rather than an in-process flag flip) is the only
/// honest OFF leg: the switch is process-constant by design, and re-entering the
/// parser under a flipped flag would serve `__PROJ_MEMO_<Cat>` entries computed
/// under the other setting.
fn off_leg() -> std::collections::BTreeMap<String, Obs> {
    let exe = std::env::current_exe().expect("current_exe");
    let out = std::process::Command::new(exe)
        .arg("--exact")
        .arg("proj_iso_ab_off_leg_child")
        .arg("--nocapture")
        .env(CHILD_MARKER, "1")
        .env(KILL_SWITCH, "1")
        .env_remove("RUST_MIN_STACK")
        .output()
        .expect("spawn OFF-leg child");
    assert!(
        out.status.success(),
        "OFF-leg child failed: status={:?}\nstdout:\n{}\nstderr:\n{}",
        out.status,
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8_lossy(&out.stdout).to_string();
    let body = stdout
        .split_once("<<<AB-LEG-BEGIN>>>\n")
        .and_then(|(_, rest)| rest.split_once("<<<AB-LEG-END>>>"))
        .map(|(body, _)| body.to_string())
        .unwrap_or_else(|| panic!("OFF-leg child produced no leg block:\n{stdout}"));
    parse_leg(&body)
}

/// The child entry point. Inert unless `PROJ_ISO_AB_CHILD` is set, so a normal
/// `cargo test` run of this file executes it as a trivially-passing no-op.
#[test]
fn proj_iso_ab_off_leg_child() {
    if std::env::var_os(CHILD_MARKER).is_none() {
        return;
    }
    assert!(
        std::env::var_os(KILL_SWITCH).is_some(),
        "the OFF-leg child must run with {KILL_SWITCH} set"
    );
    println!("<<<AB-LEG-BEGIN>>>");
    print!("{}", render_leg());
    println!("<<<AB-LEG-END>>>");
}

/// ── Gate A: the kill switch is EFFECTIVE ──
///
/// If ON and OFF ever agree on everything, this whole file is decoration.
///
/// ★ THE DISCRIMINATING ROW MOVED (#28, 2026-07-25). It used to be the `grp-*`
/// family, where the facade returned FEWER readings than the walker. Closing G3
/// made those rows agree, and this gate failed — exactly as its own instruction
/// says it should: *"Either the switch stopped being wired into the emitted
/// helpers, or the corpus no longer contains a row that discriminates them. A gate
/// that cannot fail is not a gate — fix the switch or extend the corpus."* The
/// corpus was extended.
///
/// The standing proof of effectiveness is now `cov-drop-paren-numeral`
/// (`*(@(1)) + 2`), where the facade returns MORE readings than the walker: it
/// contributes `Add(PDrop(NParen(NQuote(1))), 2)`, a reading the walker alone never
/// produces. That is a strictly better witness than the old one, because it
/// discriminates in the direction that shows the facade EARNING its place rather
/// than merely diverging from the walker.
#[test]
fn gate_a_kill_switch_is_effective() {
    let on: std::collections::BTreeMap<String, Obs> = parse_leg(&render_leg());
    let off = off_leg();
    assert_eq!(on.len(), off.len(), "legs must cover the same rows");
    assert!(
        on != off,
        "the {KILL_SWITCH} kill switch had NO observable effect on the A/B corpus. \
         Either the switch stopped being wired into the emitted helpers, or the \
         corpus no longer contains a row that discriminates them. A gate that \
         cannot fail is not a gate — fix the switch or extend the corpus."
    );
}

/// ── Gate B ★: the facade may only ADD coverage ──
///
/// `OFF accepts ⇒ ON accepts`. The facade is a pre-pass; an input the plain walker
/// handles must never be lost by engaging it. The converse is expected to fail
/// (and does — that is the entire point of the facade), so it is NOT asserted.
#[test]
fn gate_b_on_accepts_everything_off_accepts() {
    let on: std::collections::BTreeMap<String, Obs> = parse_leg(&render_leg());
    let off = off_leg();
    let mut lost: Vec<String> = Vec::new();
    for (id, o_off) in &off {
        let o_on = on.get(id).expect("row present in both legs");
        if o_off.accepts && !o_on.accepts {
            lost.push(id.clone());
        }
    }
    assert!(
        lost.is_empty(),
        "the projection-isolation facade LOST inputs the walker alone accepts: {lost:?}. \
         Engaging the facade must never shrink the accepted language."
    );
}

/// ── Gate C ★ (the G1 invariant): a degenerate tail parses iff its sibling does ──
///
/// `bs.*sep(s)` is zero-or-more, so for every frame `… a "," bs.*sep(s) …` the
/// surface with `bs = []` is in the language exactly when the surface with a
/// one-element `bs` is. Before the fix this failed on `g2-degenerate`: the facade
/// declined on the empty region and landed on the G2 walker gap.
///
/// Formal counterpart: `ProjectionIsolation.v` `T12_degenerate_tail_complete`.
#[test]
fn gate_c_degenerate_tail_matches_its_sibling() {
    let pairs = [
        ("dt-nil-0", "dt-nil-1"),
        ("dt-quoted-0", "dt-quoted-1"),
        ("dt-bare-0", "dt-bare-1"),
        ("dt-persist-0", "dt-persist-1"),
        ("g2-degenerate", "g2-polyadic"),
        ("grp-degenerate", "grp-polyadic"),
    ];
    let on: std::collections::BTreeMap<String, Obs> = parse_leg(&render_leg());
    for (degen, sibling) in pairs {
        let d = on.get(degen).expect("degenerate row");
        let s = on.get(sibling).expect("sibling row");
        assert!(
            d.accepts,
            "{degen} must parse: a zero-element `.*sep` tail is in the language \
             (T11_empty_region_is_in_the_language)"
        );
        assert_eq!(
            d.accepts, s.accepts,
            "{degen} and {sibling} must agree on acceptance — emptying a `.*sep` \
             tail cannot change whether the frame is in the language \
             (T12_degenerate_tail_complete)"
        );
    }
}

/// ── Gate C′: an intra-list DANGLING separator stays rejected in BOTH legs ──
///
/// The asymmetry that makes the G1 fix correct rather than a fabrication: an empty
/// *region* is the zero-element list (derivable); an empty *element* is a dangling
/// separator (not derivable, since `.*sep(s)` is `elem (s elem)*`). Measured
/// 2026-07-25: both legs reject `@Nil!(0,1,)`.
#[test]
fn gate_c_prime_dangling_separator_stays_rejected() {
    let on: std::collections::BTreeMap<String, Obs> = parse_leg(&render_leg());
    let off = off_leg();
    for (leg, m) in [("ON", &on), ("OFF", &off)] {
        let o = m.get("dt-dangling").expect("dt-dangling row");
        assert!(
            !o.accepts,
            "[{leg}] `@Nil!(0,1,)` must NOT parse: `.*sep(\",\")` derives \
             `elem (\",\" elem)*`, so a dangling separator is not in the language. \
             If this now parses, a reading is being FABRICATED."
        );
    }
}

/// ── Gate D ★: the G2 family — production correctness rests on the facade ──
///
/// Each of these parses with the facade ON and is REJECTED by the walker alone.
/// The assertions are therefore two-sided on purpose: the ON side is the shipped
/// contract, and the OFF side is the standing receipt that the walker gap is real.
/// ★ THE WALKER GAP IS CLOSED (#35). This gate was
/// `gate_d_g2_family_parses_only_with_the_facade`, and its own instruction was:
/// "If the OFF side ever starts accepting, the walker gap has been closed —
/// delete the `off_rejects` expectation and record it, do not weaken the ON side."
/// That is what happened, so the name and the expectation move together.
///
/// The root was `cgll_pure_crosscat_boundaries`' stop test in
/// `prattail/src/wpda_walker.rs`: `GroupingMarker` was absent from its
/// scope-resetting kind list, AND the whole test was gated on `slot.xcat == 0`,
/// which exempted grouping frames entirely (the `(`-open fan stamps them with a
/// cross-category edge). So a `(`-group did not shield its interior from an outer
/// `@`-projection floor, and the branch that would consume the interior `!` was
/// deleted before the forest saw it. Both omissions were divergences from this
/// walk's own verified model — `CollectionElementProjectionBoundary.v:112-117`
/// walks with `| Grouping :: _ => None_`, proved as `grouping_stops_walk` — and
/// from the two sibling walks in the same file, which both list `GroupingMarker`.
///
/// Measured single-variable, walker-only, only the delimiter changing:
///   `@{X}!(Nil)`  boundary_suppressed=0  unwind_chain_fired=1  accepted
///   `@(X)!(Nil)`  boundary_suppressed=1  unwind_chain_fired=0  REJECTED
/// and after the fix the second reads 0/1, identical to the first.
///
/// The ON leg did not move: these rows were `(true, 1)` before and after. Only the
/// walker-alone leg changed, from "rejects" to "accepts THE SAME SINGLE READING the
/// facade already elected" — so no reading count moved, no election changed, and no
/// new ambiguity was introduced. The facade and the walker now agree where they
/// previously disagreed, which is the point.
#[test]
fn gate_d_g2_family_parses_in_both_legs() {
    let on: std::collections::BTreeMap<String, Obs> = parse_leg(&render_leg());
    let off = off_leg();
    for id in ["g2-scalar", "g2-polyadic", "g2-degenerate"] {
        assert!(
            on.get(id).expect("row").accepts,
            "{id} must parse with the projection-isolation facade ON"
        );
    }
    // The parts parse in both legs — the gap is created by the composition.
    for id in ["g2-part-method", "g2-part-grouped", "g2-part-send"] {
        assert!(
            on.get(id).expect("row").accepts && off.get(id).expect("row").accepts,
            "{id} must parse in BOTH legs: the G2 gap is compositional, not local"
        );
    }
}

/// ── Gate E: the reading-count table, as a golden over BOTH legs ──
///
/// Pins every row's `(accepts, readings)` in each leg. Any movement — in either
/// direction, in either leg — fails here with the full table, so a change is
/// always accompanied by the evidence needed to judge it.
///
/// `None` readings mean `parse_all` returned `Err` (the row is rejected).
#[test]
fn gate_e_reading_count_golden() {
    // (id, ON accepts, ON readings, OFF accepts, OFF readings)
    let golden: &[(&str, bool, i64, bool, i64)] = &[
        ("ctl-bare-scalar", true, 1, true, 1),
        ("ctl-deep-2", true, 1, true, 1),
        ("ctl-deep-3", true, 1, true, 1),
        ("ctl-scalar-nil", true, 1, true, 1),
        ("dt-bare-0", true, 1, true, 1),
        ("dt-bare-1", true, 1, true, 1),
        ("dt-dangling", false, -1, false, -1),
        ("dt-nil-0", true, 2, true, 2),
        ("dt-nil-1", true, 2, true, 2),
        ("dt-persist-0", true, 2, true, 2),
        ("dt-persist-1", true, 2, true, 2),
        ("dt-quoted-0", true, 2, true, 2),
        ("dt-quoted-1", true, 2, true, 2),
        // ★ G2: ON parses, the walker alone does not.
        ("g2-degenerate", true, 1, true, 1),
        ("g2-no-method", true, 1, true, 1),
        ("g2-no-nested-send", true, 1, true, 1),
        ("g2-part-grouped", true, 1, true, 1),
        ("g2-part-method", true, 1, true, 1),
        ("g2-part-send", true, 1, true, 1),
        ("g2-polyadic", true, 1, true, 1),
        ("g2-scalar", true, 1, true, 1),
        // ★ G3 CLOSED (#28, 2026-07-25) — RE-BASELINED, each row with its reason.
        //
        // The ON leg GAINED the transparent-grouping twin the facade used to drop, so
        // every row now equals its OFF leg. An INCREASE in the ON leg is the recovery
        // direction (a decrease would be the disambiguation-preservation violation),
        // and each new value was PREDICTED from the ON/OFF reading sets before the
        // change and then observed exactly:
        //
        //   grp-*      2 → 3   ON gains `POutputQuoted(NVar a, ..)`, the unwrapped
        //                      channel reading, alongside the two `NParen`/`Short`
        //                      spellings it already had.
        //   name-paren 1 → 2   ON gains `NVar a` alongside `NParen(NVar a)` — the
        //                      minimal witness, at the operand category the helper
        //                      composes.
        ("grp-degenerate", true, 3, true, 3),
        ("grp-polyadic", true, 3, true, 3),
        ("grp-scalar", true, 3, true, 3),
        ("name-paren", true, 2, true, 2),
        // ★ The representative-discriminating rows. Both legs answer 2 — the facade adds
        // no semantically-NEW reading here (see the measurement correction on the corpus
        // rows). They earn their place through `Obs::elected`, not through these counts:
        // ON elects `NParen(NQuote(1))` where OFF elects `NParen(NQuoteShort(1))`.
        ("cov-drop-paren-numeral", true, 2, true, 2),
        ("cov-drop-numeral", true, 2, true, 2),
        // ★ The cleanest discriminator, and the one `gen_rholang_unit::
        // unit_rholang_name_nparen` round-trips: ON elects `NParen(NQuoteShort(PZero))`
        // (displaying `(@Nil)`, reproducing the source) and OFF elects the transparent
        // `NQuoteShort(PZero)` (displaying `@Nil`). Counts agree; structure does not.
        ("cov-name-paren-nil", true, 2, true, 2),
    ];
    let on: std::collections::BTreeMap<String, Obs> = parse_leg(&render_leg());
    let off = off_leg();
    let mut diffs: Vec<String> = Vec::new();
    for &(id, ea, er, oa, or_) in golden {
        let g_on = on.get(id).unwrap_or_else(|| panic!("missing ON row {id}"));
        let g_off = off
            .get(id)
            .unwrap_or_else(|| panic!("missing OFF row {id}"));
        let a_on = g_on.readings.map(|n| n as i64).unwrap_or(-1);
        let a_off = g_off.readings.map(|n| n as i64).unwrap_or(-1);
        if g_on.accepts != ea || a_on != er || g_off.accepts != oa || a_off != or_ {
            diffs.push(format!(
                "  {id:<20} expected ON=({ea},{er}) OFF=({oa},{or_})  \
                 got ON=({},{a_on}) OFF=({},{a_off})",
                g_on.accepts, g_off.accepts
            ));
        }
    }
    assert!(
        diffs.is_empty(),
        "projection-isolation A/B reading-count golden moved:\n{}\n\
         A DECREASE in the ON leg is a disambiguation-preservation violation \
         (readings must never be pruned early). An INCREASE may be a genuine \
         recovery — re-pin only with the measurement that justifies it.",
        diffs.join("\n")
    );
    // Every corpus row must be covered by the golden, so a new row cannot be added
    // without pinning it.
    let covered: std::collections::BTreeSet<&str> = golden.iter().map(|r| r.0).collect();
    let missing: Vec<&String> = on
        .keys()
        .filter(|k| !covered.contains(k.as_str()))
        .collect();
    assert!(missing.is_empty(), "corpus rows not pinned in the golden: {missing:?}");
}

/// ── Gate F ★: the PARSE-TIME BUDGET on the deep-`@` ladder ──
///
/// The whole reason the `@`-projection isolation exists is that parsing a nested
/// `@`-projection chain MONOLITHICALLY lets the CrossCatLhs edge stack accumulate
/// through every level, so the Tomita frontier forks base-`b` per level and
/// wall-time is EXPONENTIAL in the nesting depth (`ProjectionIsolation.v` T3;
/// measured 6/40/432/5862 ms at d=1..4 before the fix). The isolation collapses
/// that to a LINEAR scan.
///
/// This gate is the executable form of T3: on the ladder `@^d Nil (!(0))^d` the
/// per-level step must stay well under the geometric regime. A `.*sep` codegen
/// change is exactly the kind of edit that could accidentally re-arm the
/// exponential (by making a frame decline and fall back to the walker at every
/// level), so it is gated here rather than trusted.
///
/// Method notes, because timing assertions are easy to get wrong:
///  * every depth is warmed up first, then timed `REPS` times and reduced with the
///    MINIMUM — the min is the robust estimator for wall-clock (noise is one-sided);
///  * the ratio is taken over `d >= 2`. The `d = 1 -> 2` step is excluded on
///    purpose and not for convenience: `d = 1` is `@Nil!(0)`, which the
///    fewest-holes primary elects as the SPECIFIC rule `POutputNil` (one hole, the
///    `Nil` keyword a literal), so it sits on a different curve from the generic
///    `POutputShort` chain that every `d >= 2` rung takes. Including it would
///    measure that rule change, not the per-level growth;
///  * the threshold is 3.0, comfortably above the observed steady-state (~1.5-1.9)
///    and comfortably below the geometric regime this guards against (`b >= 2`
///    compounding, i.e. a ratio that does not decay with depth).
#[test]
fn gate_f_parse_time_budget_on_the_deep_at_ladder() {
    use std::time::Instant;
    const REPS: usize = 3;
    const MAX_DEPTH: usize = 6;
    const MAX_STEP_RATIO: f64 = 3.0;

    let ladder: Vec<String> = (1..=MAX_DEPTH)
        .map(|d| {
            let mut s = String::with_capacity(4 * d + 4);
            (0..d).for_each(|_| s.push('@'));
            s.push_str("Nil");
            (0..d).for_each(|_| s.push_str("!(0)"));
            s
        })
        .collect();

    let mut best: Vec<f64> = Vec::with_capacity(MAX_DEPTH);
    for src in &ladder {
        mettail_runtime::clear_var_cache();
        let _ = Proc::parse_via_wpda(src); // warm-up
        let mut t_min = f64::INFINITY;
        for _ in 0..REPS {
            mettail_runtime::clear_var_cache();
            let t0 = Instant::now();
            let r = Proc::parse_via_wpda(src);
            let dt = t0.elapsed().as_secs_f64() * 1000.0;
            assert!(r.is_ok(), "ladder rung must parse: {src:?}");
            t_min = t_min.min(dt);
        }
        best.push(t_min);
    }

    let table: String = ladder
        .iter()
        .zip(best.iter())
        .enumerate()
        .map(|(i, (s, t))| format!("  d={} {:>32}  {:>8.2} ms\n", i + 1, s, t))
        .collect();

    let mut bad: Vec<String> = Vec::new();
    for d in 2..MAX_DEPTH {
        let ratio = best[d] / best[d - 1];
        // A non-finite ratio (a zero-time rung, hence a division producing inf or
        // NaN) is treated as a FAILURE rather than silently passing: it means the
        // measurement itself is degenerate and the budget was not actually checked.
        if !ratio.is_finite() || ratio >= MAX_STEP_RATIO {
            bad.push(format!(
                "  d={}->{}  ratio {:.2} (budget < {:.1})",
                d,
                d + 1,
                ratio,
                MAX_STEP_RATIO
            ));
        }
    }
    assert!(
        bad.is_empty(),
        "deep-`@` ladder per-level step ratio exceeded the budget — the isolation \
         may have stopped engaging, re-arming the base-`b` CrossCatLhs frontier \
         (ProjectionIsolation.v T3_geometric_dominates_linear):\n{}\nladder:\n{table}",
        bad.join("\n")
    );

    // Absolute ceiling on the whole A/B corpus: the contrast set must stay far
    // below a second even in a debug build.
    mettail_runtime::clear_var_cache();
    let t0 = Instant::now();
    for (_, src) in corpus() {
        let _ = Proc::parse_via_wpda(src);
    }
    let total = t0.elapsed().as_secs_f64();
    assert!(
        total < 1.0,
        "the A/B contrast set took {total:.3}s (budget 1.0s) — a per-input blow-up \
         is the first symptom of a re-armed projection frontier"
    );
}

/// The `@`-projection deep ladder `@^d Nil (!(0))^d`, shared by the gate-F family.
fn deep_at_ladder(max_depth: usize) -> Vec<String> {
    (1..=max_depth)
        .map(|d| {
            let mut s = String::with_capacity(4 * d + 4);
            (0..d).for_each(|_| s.push('@'));
            s.push_str("Nil");
            (0..d).for_each(|_| s.push_str("!(0)"));
            s
        })
        .collect()
}

/// ── Gate F-all ★ (#103/R3): ONE WALKER LEG PER DISTINCT SPAN ──
///
/// # The half of gate F that was missing
///
/// [`gate_f_parse_time_budget_on_the_deep_at_ladder`] watches the SINGLE-result seam —
/// the one ROOT-P already made linear with `__PROJ_MEMO_<Cat>`. The ambiguity-preserving
/// `_all` seam, which the `@`-projection helper actually recurses through, was guarded by
/// nothing, and its measured step ratio was RISING (1.34 → 1.85 on the pre-union row).
///
/// # What is asserted, and why it is structural rather than timed
///
/// The `SepSeam::All` union prologue hands each span it accepts to the monolithic walker.
/// `__PROJ_ALL_MEMO_<Cat>` (#103/R3) makes the `_all` string entry return early on a
/// repeat of the same span within one epoch, so the union arm — and therefore the walker
/// leg — runs **once per DISTINCT span per top-level parse** instead of once per visit.
/// That is an exact, deterministic equality (`legs == distinct`), so it is asserted
/// directly through the `__g3_*` probe rather than inferred from wall-clock. No timing,
/// no flakiness, and it fails loudly if a future edit re-arms the re-descent.
///
/// # The measured RED→GREEN that this test is the executable form of
///
/// With the `_all` memo forced off (`if false` in place of `if memo_on` at the
/// `parse_via_wpda_all_with_weights` split in `macros/src/gen/mod.rs`) and everything
/// else at HEAD — summed over the swept inputs below:
///
/// ```text
///                        legs   distinct   verdict
///   memo OFF (RED)        123         60   legs > distinct — the same span re-walked
///   memo ON  (GREEN)       60         60   one leg per distinct span
/// ```
///
/// The worst single row was `@Nil!(@Nil!(@Nil!(0),@Nil!(0)),@Nil!(@Nil!(0),@Nil!(0)))` at
/// **43 legs over 3 distinct spans** (`@Nil!(0)` walked 36 times), and the sharpest
/// evidence that this was never a synthetic concern is that a row already in the A/B
/// corpus separates: `g2-no-method` (`@(a!(Nil))!(Nil,)`) ran 3 legs over 2 spans.
///
/// ⚠ **The obvious mutation does not separate the two configurations.** The first version
/// of this gate pinned `ctl-deep-3` (`@@@Nil!(0)!(0)!(0)`, the d=3 rung of gate F's own
/// ladder), on the reasoning that a deep chain must re-visit its own sub-spans. Measured
/// with the memo forced off: `legs == distinct` — it passed RED. Every tiling of that
/// ladder visits each span once, so the ladder measures depth, not sharing. The family
/// that does separate them is [`REPEATED_OPERAND_FAMILY`]: the same operand TEXT at two
/// argument positions, which the cartesian enumerates independently. The sweep is
/// therefore not decoration — a single-input version of this gate was green on the
/// defect it exists to catch.
///
/// # Non-vacuity, and the control
///
/// * `legs > 0` — the probe records only while ARMED, and the union arm is only entered
///   when the helper ACCEPTS. A silently disarmed probe, or an input the facade declines,
///   would make `legs == distinct == 0` and pass this test for the wrong reason. Asserted
///   explicitly so that cannot happen.
/// * the control is an input the facade **declines** — `"Nil"` has no σ-led frame, so the
///   union arm is never entered. `legs == 0` there both before and after the memo (both
///   measured), which is what shows the swept inputs' non-zero counts come from those
///   inputs and not from ambient parsing the probe happens to be recording.
#[test]
fn gate_f_all_one_walker_leg_per_distinct_span() {
    // ── control: an input the facade DECLINES ⇒ the union arm is never entered ──
    mettail_runtime::clear_var_cache();
    Proc::__g3_probe_reset();
    let ctl = Proc::parse_via_wpda_all("Nil");
    assert!(ctl.is_ok(), "the control must still parse (via the walker): {ctl:?}");
    let ctl_legs = Proc::__g3_walker_legs();
    assert_eq!(
        ctl_legs, 0,
        "control `Nil` has no σ-led frame, so the `@`-projection helper must decline and \
         the union arm must never run a walker leg — got {ctl_legs}. A non-zero count here \
         means the probe is recording legs this test does not account for, and the \
         mutation legs' numbers cannot be attributed to their own inputs."
    );

    // ── the mutation sweep ──
    //
    // The whole A/B corpus, the deep-`@` ladder, and the REPEATED-OPERAND family that
    // separates the two configurations. Sweeping rather than pinning one input is not
    // thoroughness for its own sake: `legs == distinct` holds VACUOUSLY on any input
    // whose tilings each visit a span once, and the deep ladder turns out to be one of
    // those (measured — see the RED/GREEN table above). A single-input version of this
    // gate would have passed with the memo forced off.
    let mut inputs: Vec<String> = corpus().iter().map(|(_, s)| s.to_string()).collect();
    inputs.extend(deep_at_ladder(6));
    inputs.extend(REPEATED_OPERAND_FAMILY.iter().map(|s| s.to_string()));

    let mut rows: Vec<String> = Vec::with_capacity(inputs.len());
    let mut bad: Vec<String> = Vec::new();
    let mut total_legs = 0usize;
    let mut total_distinct = 0usize;

    for src in &inputs {
        mettail_runtime::clear_var_cache();
        Proc::__g3_probe_reset();
        let _ = Proc::parse_via_wpda_all(src);

        let spans = Proc::__g3_walker_spans();
        let legs = spans.len();
        let distinct = spans
            .iter()
            .collect::<std::collections::BTreeSet<_>>()
            .len();
        total_legs += legs;
        total_distinct += distinct;
        rows.push(format!("  {legs:>4} legs {distinct:>4} distinct   {src:?}\n"));

        if legs != distinct {
            let mut counts: std::collections::BTreeMap<&String, usize> = Default::default();
            for s in &spans {
                *counts.entry(s).or_insert(0) += 1;
            }
            let repeats: String = counts
                .iter()
                .filter(|(_, n)| **n > 1)
                .map(|(s, n)| format!("      {n:>4} ×  {s:?}\n"))
                .collect();
            bad.push(format!("  {src:?}: {legs} legs over {distinct} distinct spans\n{repeats}"));
        }
    }

    let table: String = rows.concat();
    println!("`_all` union walker legs per input:\n{table}");

    // ── non-vacuity, asserted BEFORE the equality ──
    //
    // The probe records only while ARMED and only when the `@`-projection helper
    // ACCEPTS, so `legs == distinct == 0` everywhere would satisfy the equality below
    // while measuring nothing at all. That is a FAILURE, not a trivial success.
    assert!(
        total_legs > 0 && total_distinct > 0,
        "the probe recorded NO walker leg across {} inputs (legs={total_legs}, \
         distinct={total_distinct}). Either `__g3_probe_reset` no longer arms the probe, \
         or the `@`-projection helper stopped accepting every shape in the sweep — in \
         both cases the equality below would pass vacuously.\n{table}",
        inputs.len()
    );

    assert!(
        bad.is_empty(),
        "the `_all` union ran MORE walker legs than there are DISTINCT spans. \
         `__PROJ_ALL_MEMO_<Cat>` is supposed to make the enumerating matcher's cartesian \
         re-descent a DAG, so each span is walked once per epoch; a leg count above the \
         distinct-span count means the memo is not being consulted (a stale epoch every \
         call, a key that never matches, or the wrapper bypassed):\n{}\nfull table:\n{table}",
        bad.concat()
    );
}

/// ── Gate G ★ (#103/R1): the REPRESENTATIVE is elected on grammar priorities alone ──
///
/// # The property
///
/// The `@`-projection helper's finalize and the #28/G3 union's finalize both fold a
/// `semantic_hash` equivalence class down to ONE representative term. Until #103/R1 they
/// elected that representative with `LexicographicWeight::lex_cmp`, whose first
/// tie-breaker below `primary` is a **reversed `open_len`** — the byte length of the OPEN
/// token a prefix lex-fork committed to. That is a property of the DERIVATION PATH, not
/// of the term, and while it is exactly the right way to rank two DISTINCT semantic
/// classes (maximal munch: `{|` beats `{` for `{||}`), it cannot arbitrate between two
/// SPELLINGS of one class — both mean the same thing, so the choice cannot be justified
/// by which lexer fork produced them.
///
/// `__rep_cmp` (`facade::emit_rep_cmp_fn`) is `lex_cmp` with that one leg removed. The
/// weight stored for the class is still the full `lex_cmp`-min, because the weight is
/// what ranks the class against the OTHERS.
///
/// # ★★ THE MEASUREMENT: A P-WITNESS EXISTS, AND THE PLAN PREDICTED IT WOULD NOT
///
/// Both comparators are evaluated at every fold, so the seam counts folds
/// (`__rep_cmp_folds`), the folds on which the two answers DIFFER
/// (`__rep_cmp_divergences`), and — while armed — both spellings of each divergence
/// (`__rep_cmp_divergence_log`). Those divergent folds are exactly the ones R1 moves,
/// and the count is computed the same way whether or not R1's rule is in force, so it is
/// a property of the INPUT rather than of the configuration.
///
/// The design predicted **no witness**: `semantic_hash` folds sugar≡canonical aliases and
/// `Display` is equal by construction for the transparent-grouping twins, so it doubted a
/// `Display`- or `semantic_hash`-level witness existed. **Measured 2026-07-29: 17
/// divergent folds over this sweep**, the smallest on `@Nil!(0)` — the most ordinary
/// input in the corpus. The recorded fold is:
///
/// ```text
///   incumbent  POutputNil(CastInt(NumLit(0)))          primary=0.025 open_len=0 lex_alt=0 src=0 rule=33
///   incoming   POutputShort(PZero, CastInt(NumLit(0))) primary=0.025 open_len=3 lex_alt=0 src=0 rule=33
/// ```
///
/// One `semantic_hash` class (`@Nil!(q)` written with the dedicated `POutputNil` rule, or
/// with the generic `POutputShort` and `PZero` as the channel process). The two candidates
/// are IDENTICAL on **every grammar component** — same primary cost, same lex alternative,
/// same source category, same rule index. They differ on exactly one thing: the incoming
/// candidate's derivation went through a lex fork whose open token was 3 bytes (`Nil`).
///
/// Pre-R1 that 3 was the whole decision: the reversed `open_len` leg made the incoming
/// strictly `⊕`-smaller, so the generic spelling displaced the specific one. **The seam
/// elected on a derivation-path byte predicate, and nothing else was available to it.**
/// Post-R1 `__rep_cmp` returns `Equal` on that fold, first-seen stands, and the specific
/// `POutputNil` survives. That is a behaviour change, not seam-shape hardening, and it is
/// pinned in [`REP_ELECTION_PINS`].
///
/// ## Where the witness is, and where it is NOT — the plan was half right
///
/// | identity key | witness? | why |
/// |---|---|---|
/// | `_all` reading set, `Debug` | ★ **YES** | `parse_via_wpda_all("@Nil!(0)")` returns `POutputNil(..)` after R1 and `POutputShort(PZero, ..)` before |
/// | `Display` | **no** | `POutputShort(PZero, q)` renders `Nil` for its channel with no parens needed, so both spell `@Nil!(0)` |
/// | `semantic_hash` | **no** | by construction — they are ONE key, which is why they meet at this fold at all |
/// | single-result `parse_via_wpda` | **no** | measured: every divergence in this sweep is on the `_all` leg (`d1 == 0`), so the ε-framed single-winner election is untouched |
///
/// So the plan's doubt was correct about `Display` and `semantic_hash` and wrong about the
/// third key it did not consider: the **structure of the `_all` reading set**, which gate
/// A observes for the SINGLE seam (`Obs::elected`) and which nothing observed for `_all`.
/// That blind spot is why the witness went unnoticed, and closing it is what this gate is.
///
/// ## Why the fork family is in the sweep
///
/// `open_len` is `0` at every non-fork weight-construction site (`from_cost`, `lex_w`, …)
/// and becomes non-zero ONLY on a PREFIX LEX-FORK branch (`lex_w_with_len` /
/// `lex_w_alt_with_len`), from which `times` MAX-projects it along the whole derivation.
/// [`LEX_FORK_FAMILY`] puts Rholang's live fork — the collection open, Pathmap `{|` (len 2)
/// vs PPar `{` (len 1) — under, beside and inside a σ-led frame. It contributed 4 of the
/// 17 divergences, at `open_len` 3 vs 2 rather than 3 vs 0, confirming the mechanism is the
/// fork and not one accidental token length.
///
/// # Non-vacuity, and the two controls
///
/// * `total_folds > 0` **and** `total_div > 0` — a seam that never meets a duplicate
///   semantic key never elects a representative, and a sweep with no divergence would make
///   the pins below hold for a reason that has nothing to do with R1.
/// * `__rep_cmp_divergence_log().len() == divergences` per row — the COUNT is always on and
///   the LOG is armed, so a short log means arming was missed and every spelling read off
///   the log is untrustworthy.
/// * **the ambient control** is `"Nil"`: no σ-led frame, so the helper declines, neither
///   seam runs, and `folds == divergences == 0`. That is what shows the swept rows' counts
///   come from those rows rather than from parsing the harness itself does.
/// * **the control that must NOT discriminate** is the zero-divergence half of
///   [`REP_ELECTION_PINS`] — rows with MANY folds and no divergence (`@(a)!(0)`: 9 folds,
///   3 readings; `@Nil!(0,)`: 5 folds, 2 readings). Their reading sets are pinned to the
///   same bytes under both rules, so a mutation that moved everything — rather than
///   exactly the `open_len`-decided folds — fails here instead of passing as a witness.
#[test]
fn gate_g_representative_election_is_open_len_free() {
    /// Reset all three projection categories' probes (`Proc`, `Name`, `InputBind` are the
    /// Rholang categories with a derivable projection shape).
    fn reset() {
        Proc::__rep_probe_reset();
        Name::__rep_probe_reset();
        InputBind::__rep_probe_reset();
    }
    /// `(folds, divergences)` summed over the three categories — a `Proc` parse folds at
    /// its own seam AND at the `Name` / `InputBind` seams its operands recurse through, so
    /// reading only `Proc`'s counters would under-report.
    fn read() -> (usize, usize) {
        (
            Proc::__rep_cmp_folds() + Name::__rep_cmp_folds() + InputBind::__rep_cmp_folds(),
            Proc::__rep_cmp_divergences()
                + Name::__rep_cmp_divergences()
                + InputBind::__rep_cmp_divergences(),
        )
    }

    // ── control: an input the facade DECLINES ⇒ neither seam ever folds ──
    mettail_runtime::clear_var_cache();
    reset();
    let ctl = Proc::parse_via_wpda_all("Nil");
    assert!(ctl.is_ok(), "the control must still parse (via the walker): {ctl:?}");
    let (ctl_folds, ctl_div) = read();
    assert_eq!(
        (ctl_folds, ctl_div),
        (0, 0),
        "control `Nil` has no σ-led frame, so the `@`-projection helper declines and \
         neither dedup seam runs — got {ctl_folds} folds / {ctl_div} divergences. A \
         non-zero count here means the counters are recording folds this test does not \
         account for, and the sweep's numbers cannot be attributed to their own inputs."
    );

    // ── the sweep ──
    let mut inputs: Vec<String> = corpus().iter().map(|(_, s)| s.to_string()).collect();
    inputs.extend(deep_at_ladder(6));
    inputs.extend(REPEATED_OPERAND_FAMILY.iter().map(|s| s.to_string()));
    inputs.extend(LEX_FORK_FAMILY.iter().map(|s| s.to_string()));

    let mut rows: Vec<String> = Vec::with_capacity(inputs.len());
    let mut witnesses: Vec<String> = Vec::new();
    let mut total_folds = 0usize;
    let mut total_div = 0usize;

    for src in &inputs {
        // Both string entries: the SINGLE seam folds only at the helper finalize, the
        // `_all` seam folds at the helper finalize AND at the union finalize.
        mettail_runtime::clear_var_cache();
        reset();
        let single = Proc::parse_via_wpda(src);
        let (f1, d1) = read();

        mettail_runtime::clear_var_cache();
        reset();
        let all = Proc::parse_via_wpda_all(src);
        let (f2, d2) = read();

        let folds = f1 + f2;
        let div = d1 + d2;
        total_folds += folds;
        total_div += div;

        let elected = match &single {
            Ok(t) => canon(&format!("{t:?}")),
            Err(_) => "<ERR>".to_string(),
        };
        let n_all = all.as_ref().map(|v| v.len() as i64).unwrap_or(-1);
        let all_dbg: String = match &all {
            Ok(v) => v
                .iter()
                .map(|t| format!("        | {}\n", canon(&format!("{t:?}"))))
                .collect(),
            Err(_) => "        | <ERR>\n".to_string(),
        };
        rows.push(format!(
            "  {folds:>4} folds {div:>4} diverge  readings {n_all:>3}   {src:?}\n{all_dbg}"
        ));
        if div > 0 {
            // ⚠ The log is read from the `_all` leg only (the second `reset()` cleared
            // the single leg's records), so `d2` — not `div` — is the number of records
            // it must contain. Asserted, because a short log means the arming was missed
            // and everything concluded from the log below would be unsound.
            let log: Vec<String> = Proc::__rep_cmp_divergence_log()
                .into_iter()
                .chain(Name::__rep_cmp_divergence_log())
                .chain(InputBind::__rep_cmp_divergence_log())
                .collect();
            assert_eq!(
                log.len(),
                d2,
                "the always-on divergence COUNT and the armed detail LOG disagree for \
                 {src:?} ({d2} vs {}). `__rep_probe_reset` must arm the log, or the \
                 spellings below are not the spellings that were elected.",
                log.len()
            );
            let detail: String = log
                .iter()
                .map(|r| format!("      {}\n", canon(r)))
                .collect::<String>();
            // The OBSERVABLE consequence: the `_all` seam's reading set, at both identity
            // keys the plan named — structure (`Debug`) and surface (`Display`).
            mettail_runtime::clear_var_cache();
            let obs: String = match Proc::parse_via_wpda_all(src) {
                Ok(v) => v
                    .iter()
                    .map(|t| format!("      all: {}   ||   {}\n", canon(&format!("{t:?}")), t))
                    .collect(),
                Err(e) => format!("      all: <ERR {e:?}>\n"),
            };
            witnesses.push(format!(
                "  {src:?}  ({div} divergent folds)\n    elected: {elected}\n{detail}{obs}"
            ));
        }
    }

    let table: String = rows.concat();
    println!("`@`-projection representative elections:\n{table}");
    println!("TOTAL: {total_folds} folds, {total_div} divergent");
    if witnesses.is_empty() {
        println!(
            "P-WITNESS: NONE over {} inputs — `__rep_cmp` and `lex_cmp` agree at every \
             fold, so R1 is provably inert on this corpus.",
            inputs.len()
        );
    } else {
        println!("P-WITNESS CANDIDATES:\n{}", witnesses.concat());
    }

    // ── non-vacuity, asserted BEFORE anything is concluded from the pins ──
    assert!(
        total_folds > 0,
        "the two `@`-projection dedup seams performed NO representative election across \
         {} inputs. Either the counters are no longer wired into the folds, or the helper \
         stopped accepting every shape in the sweep — in both cases the pins below would \
         hold for a reason that has nothing to do with R1.\n{table}",
        inputs.len()
    );
    assert!(
        total_div > 0,
        "no fold in this sweep put `__rep_cmp` and the full `lex_cmp` in disagreement, so \
         R1's election rule was never exercised and the pins below cannot distinguish it \
         from the rule it replaced. The sweep must contain at least one class whose \
         members tie on primary/lex_alt/src/rule and differ on `open_len` — that is what \
         [`LEX_FORK_FAMILY`] and the `@Nil!(0)` family are for. Measured at R1: 17.\n{table}"
    );

    // ── the pins: TEXT, on both halves ──
    //
    // ⚠ These pin a MEASUREMENT, not a design invariant. If a grammar or lexer change moves
    // a row, the correct response is to READ THE PRINTED WITNESS BLOCK — which carries both
    // spellings and both full weights for every divergent fold — and re-derive, not to
    // relax the pin.
    let mut moved: Vec<String> = Vec::new();
    for (src, expected) in REP_ELECTION_PINS {
        mettail_runtime::clear_var_cache();
        let got: Vec<String> = match Proc::parse_via_wpda_all(src) {
            Ok(v) => v.iter().map(|t| canon(&format!("{t:?}"))).collect(),
            Err(e) => vec![format!("<ERR {e:?}>")],
        };
        let want: Vec<String> = expected.iter().map(|s| s.to_string()).collect();
        if got != want {
            moved.push(format!(
                "  {src:?}\n    want ({}):\n{}    got  ({}):\n{}",
                want.len(),
                want.iter()
                    .map(|r| format!("      {r}\n"))
                    .collect::<String>(),
                got.len(),
                got.iter()
                    .map(|r| format!("      {r}\n"))
                    .collect::<String>(),
            ));
        }
    }
    assert!(
        moved.is_empty(),
        "the `@`-projection `_all` reading set moved at a pinned row.\n\n\
         The WITNESS rows pin #103/R1's behaviour change: a class whose members tie on \
         primary, lex_alt, src and rule and differ ONLY on `open_len` must keep the \
         FIRST-SEEN spelling, not the longer-open one. If a witness row regressed to \
         `POutputShort(PZero, ..)`, the reversed-`open_len` leg is back in the \
         representative election.\n\n\
         The CONTROL rows have many folds and NO divergence, so they must be byte-identical \
         under either election rule. If a control row moved, the change is not confined to \
         the `open_len`-decided folds and the witness rows above prove nothing.\n\n{}\
         \nfull table:\n{table}",
        moved.concat()
    );
}

/// The pinned `_all` reading sets for [`gate_g_representative_election_is_open_len_free`],
/// as canonicalised `Debug` (the `UniqueId` counter normalised out by [`canon`]).
///
/// Two halves, and the gate needs both:
///
/// * ★ **WITNESS rows** — divergent folds, so #103/R1 MOVED them. Each is pinned to the
///   post-R1 spelling; pre-R1 the same rows returned the `POutputShort(PZero, ..)` twin,
///   which the printed divergence log records as `full_keeps`. These fail if the reversed
///   `open_len` leg ever returns to the representative election.
/// * **CONTROL rows** — many folds, ZERO divergences. Under either election rule these are
///   the same bytes, so they must NOT move. They are what distinguishes "R1 changed exactly
///   the `open_len`-decided folds" from "something changed the seam wholesale".
///
/// The reading order is the finalize's weight `sort_by`, which is deterministic.
const REP_ELECTION_PINS: &[(&str, &[&str])] = &[
    // ── ★ WITNESS: primary/lex_alt/src/rule all tie; open_len 0 vs 3 ──
    ("@Nil!(0)", &["POutputNil(CastInt(NumLit(0)))"]),
    (
        "@@Nil!(0)!(0)",
        &["POutputShort(POutputNil(CastInt(NumLit(0))), CastInt(NumLit(0)))"],
    ),
    // ── ★ WITNESS via the PREFIX LEX FORK: open_len 2 vs 3 ──
    ("@Nil!({||})", &["POutputNil(CastPathmap(PathmapLit(PathMapLit(HashMapLit({})))))"]),
    // ── CONTROL: 9 folds, 0 divergences — must be identical under both rules ──
    (
        "@(a)!(0)",
        &[
            "POutputQuoted(NParen(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") })))), CastInt(NumLit(0)))",
            "POutputQuoted(NVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), CastInt(NumLit(0)))",
            "POutputShort(PVar(OrdVar(Free(FreeVar { unique_id: UniqueId(_), pretty_name: Some(\"a\") }))), CastInt(NumLit(0)))",
        ],
    ),
    // ── CONTROL: 5 folds, 0 divergences, and BOTH spellings of the class survive here
    //    because they are DISTINCT semantic keys (a degenerate tail is not `POutputNil`) ──
    (
        "@Nil!(0,)",
        &[
            "POutputShort2Plus(PZero, CastInt(NumLit(0)), [])",
            "POutputNil2Plus(CastInt(NumLit(0)), [])",
        ],
    ),
];

/// The inputs that put Rholang's live PREFIX LEX-FORK — the collection open, Pathmap
/// `{|` (len 2) vs PPar `{` (len 1) — under, beside and inside a σ-led projection frame.
///
/// ★ Why this family and not a bigger random sweep. `open_len` is `0` at every non-fork
/// weight-construction site; it becomes non-zero ONLY on a prefix lex-fork branch, and
/// `times` MAX-projects it along the derivation. So the ONLY way the reversed-`open_len`
/// tiebreak can reach the projection dedup seams is for a fork branch to appear somewhere
/// inside a span the helper accepts. Sweeping inputs with no fork at all cannot produce a
/// divergence however many of them there are — it would grow the table without growing
/// the evidence.
const LEX_FORK_FAMILY: &[&str] = &[
    // The fork itself, as an operand of a σ-led send.
    "@Nil!({||})",
    "@Nil!({|1:2|})",
    "@Nil!({||},{||})",
    // The fork as the CHANNEL of a σ-led send (the quoted-collection channel).
    "@{||}!(0)",
    "@{|1:2|}!(0)",
    "@{||}!({||})",
    // Under a `PDrop` of a quoted Pathmap — the `|}` / `|` close ambiguity, which is the
    // form `rholang_tests.rs`'s own lattice-backend pins use.
    "*@{|1:2|}",
    "*@{||}",
    "@Nil!(*@{|1:2|})",
    // Beside a grouped channel, so the transparent-grouping twin and the fork meet in the
    // same union finalize.
    "@(a)!({||})",
    "@({||})!(0)",
    "@Nil!({||},@Nil!({||}))",
];

/// Inputs whose operand spans REPEAT — the family that separates a memoized `_all` from
/// an un-memoized one, and the reason [`gate_f_all_one_walker_leg_per_distinct_span`]
/// sweeps instead of pinning a single input.
///
/// The deep-`@` ladder does NOT separate them: each of its tilings visits each span once,
/// so `legs == distinct` there with the memo forced off. What separates them is the same
/// operand TEXT appearing at two argument positions, which the cartesian enumerates
/// independently and therefore re-parses — the exact re-descent the memo collapses.
const REPEATED_OPERAND_FAMILY: &[&str] = &[
    "@Nil!(@Nil!(0),@Nil!(0))",
    "@Nil!(@Nil!(0),@Nil!(0),@Nil!(0))",
    "@Nil!(@(a)!(0),@(a)!(0))",
    "@@Nil!(0)!(@@Nil!(0)!(0),@@Nil!(0)!(0))",
    "@Nil!(@Nil!(@Nil!(0),@Nil!(0)),@Nil!(@Nil!(0),@Nil!(0)))",
];

/// ── Gate F-all ★: the PARSE-TIME BUDGET on the `_all` seam ──
///
/// The sibling of [`gate_f_parse_time_budget_on_the_deep_at_ladder`] for the
/// ambiguity-preserving entry. Same ladder, same estimator (min of `REPS`), same ratio
/// budget and the same reason for excluding the `d = 1 -> 2` step (`d = 1` is `@Nil!(0)`,
/// which the fewest-holes primary elects as the specific `POutputNil`, so it sits on a
/// different curve from the generic `POutputShort` chain every `d >= 2` rung takes).
///
/// ⚠ This is a GUARD, not the RED. The pre-#103/R3 `_all` union row already sat at a
/// ~1.67 step ratio — under budget while doing Σ-over-levels redundant walker passes —
/// which is exactly why the structural
/// [`gate_f_all_one_walker_leg_per_distinct_span`] above, and not a wall-clock
/// threshold, is what pins the memo's contract. What this test adds is the missing
/// symmetric budget: before #103/R3 the `_all` seam had NO time gate at all, so a future
/// edit could re-arm the geometric regime here and every gate in the tree would stay
/// green.
///
/// Thresholds are deliberately loose (a debug build on a shared machine); the tight,
/// exact statement lives in the structural test.
#[test]
fn gate_f_all_parse_time_budget_on_the_deep_at_ladder() {
    use std::time::Instant;
    const REPS: usize = 3;
    const MAX_DEPTH: usize = 6;
    const MAX_STEP_RATIO: f64 = 3.0;
    /// Total wall-clock for all six rungs. Pre-#103/R3 the d=6 rung ALONE measured
    /// 148.22 ms, so this ceiling is one a re-armed re-descent cannot slip under.
    const LADDER_TOTAL_BUDGET_S: f64 = 1.0;

    let ladder = deep_at_ladder(MAX_DEPTH);

    /// Min-of-`REPS` wall-clock, in ms, with the fresh-variable cache cleared before
    /// every rep so no rung inherits another's bindings.
    fn min_ms(src: &str, reps: usize, mut run: impl FnMut(&str) -> bool) -> f64 {
        mettail_runtime::clear_var_cache();
        let _ = run(src); // warm-up
        let mut t_min = f64::INFINITY;
        for _ in 0..reps {
            mettail_runtime::clear_var_cache();
            let t0 = Instant::now();
            let ok = run(src);
            let dt = t0.elapsed().as_secs_f64() * 1000.0;
            assert!(ok, "ladder rung must parse: {src:?}");
            t_min = t_min.min(dt);
        }
        t_min
    }

    let best: Vec<f64> = ladder
        .iter()
        .map(|src| min_ms(src, REPS, |s| Proc::parse_via_wpda_all(s).is_ok()))
        .collect();
    // ★ The honest control for the union: `__all_with_weights_monolithic` is not "the
    // walker in a different configuration", it is the EXACT leg the union prologue runs,
    // so `union − Σ(walker legs)` attributes the remainder to the facade's own
    // helper+cartesian work. The probe says the union runs `d` legs at depth `d` (one per
    // distinct span), so the subtrahend at depth `d` is the PREFIX SUM of this row.
    let walker: Vec<f64> = ladder
        .iter()
        .map(|src| min_ms(src, REPS, |s| Proc::__all_with_weights_monolithic(s).is_ok()))
        .collect();

    let mut table = String::new();
    let mut walker_prefix = 0.0f64;
    for (i, src) in ladder.iter().enumerate() {
        walker_prefix += walker[i];
        table.push_str(&format!(
            "  d={} {:>34}  union {:>7.2} ms   walker-leg {:>6.2} ms   Σlegs {:>7.2} ms   facade {:>7.2} ms\n",
            i + 1,
            src,
            best[i],
            walker[i],
            walker_prefix,
            best[i] - walker_prefix,
        ));
    }
    // Printed unconditionally (`--nocapture`) so the ladder can be read off a GREEN run
    // and compared against the banked table on
    // `facade::emit_projection_isolation_prologue` without having to make it fail first.
    println!("`_all` union ladder (min of {REPS}, debug):\n{table}");

    let mut bad: Vec<String> = Vec::new();
    for d in 2..MAX_DEPTH {
        let ratio = best[d] / best[d - 1];
        // A non-finite ratio (a zero-time rung) is a FAILURE, not a silent pass: it means
        // the measurement is degenerate and the budget was never actually checked.
        if !ratio.is_finite() || ratio >= MAX_STEP_RATIO {
            bad.push(format!(
                "  d={}->{}  ratio {:.2} (budget < {:.1})",
                d,
                d + 1,
                ratio,
                MAX_STEP_RATIO
            ));
        }
    }
    assert!(
        bad.is_empty(),
        "the `_all` seam's per-level step ratio exceeded the budget — the enumerating \
         matcher's cartesian re-descent may no longer be collapsing to a DAG:\n{}\nladder:\n{table}",
        bad.join("\n")
    );

    let total_s: f64 = best.iter().sum::<f64>() / 1000.0;
    assert!(
        total_s < LADDER_TOTAL_BUDGET_S,
        "the six `_all` ladder rungs took {total_s:.3}s (budget {LADDER_TOTAL_BUDGET_S:.1}s):\n{table}"
    );
}
