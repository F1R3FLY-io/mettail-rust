//! ★ **THE REFUSAL VOCABULARY** — *"the guard is false"* vs *"the guard could not be decided"*.
//!
//! [`Sat3::DontKnow`] has one symbol for every way a guard decider can fail to reach a verdict,
//! and [`dont_know_policy`] then spells that symbol `false`. That is correct as a COMM verdict
//! and wrong as an *observation*: it makes a guard that was evaluated and REFUTED
//! indistinguishable from a guard that was never decided at all. This module holds the types
//! that make those two different objects.
//!
//! # ★ Why these types live in `prattail` rather than in a lane
//!
//! There are **two** run-time guard legs over the one substrate, and they are — in
//! `guard_par_substrate`'s own words — *"the same shape as well as the same decider"*:
//!
//! | lane | crate | input | encoder |
//! |---|---|---|---|
//! | the surface leg | `mettail_languages::rholang::guard_substrate` | a substituted `Proc` | `encode_guard` |
//! | the lowered leg | `mettail_rholang_runtime::guard_par_substrate` | a substituted `rhoapi::Par` | `encode_par_guard` |
//!
//! Both encode into [`GuardFormula`] and both decide with [`ground_verdict_with`]. A refusal
//! vocabulary that lived in either lane could only be reached by that lane, and the crate graph
//! settles which: `rholang-runtime` **depends on** `languages`, so `languages` cannot depend
//! back. `prattail` is the common ancestor both already depend on — it is where the rest of the
//! shared guard vocabulary (`Sat3`, [`GuardFormula`], [`dont_know_policy`],
//! [`UndecidedCause`]) already lives, so the refusal vocabulary joins it rather than being
//! duplicated into a second, drifting enum.
//!
//! ⚠ **Nothing `Par`-shaped or `Proc`-shaped may enter this module.** Every field below is a
//! `String` or an enum, exactly so that neither AST can reach `prattail` — the same rule that
//! keeps [`GuardAtom`]'s payload in the caller's side table. The rendering of a guard term into
//! the [`GuardRefusal::guard`] string is each lane's own business.
//!
//! [`Sat3::DontKnow`]: crate::algebra_tower::Sat3::DontKnow
//! [`dont_know_policy`]: crate::guard_formula::dont_know_policy
//! [`GuardFormula`]: crate::guard_formula::GuardFormula
//! [`ground_verdict_with`]: crate::guard_formula::ground_verdict_with
//! [`UndecidedCause`]: crate::guard_formula::UndecidedCause
//! [`GuardAtom`]: crate::guard_formula::GuardAtom

/// **Where the obstruction came from** — the fact that decides whether a compile-time gate
/// could ever have caught it.
///
/// A lane can answer this when it holds *both* terms: the guard **as written**, and its image
/// under the arrived payload. Comparing the two separates an obstruction the author typed from
/// one a *datum* carried in.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum RefusalProvenance {
    /// The obstruction is present in the guard term itself, before any payload arrives. A
    /// compile-time gate sees it, and it obstructs **every** datum.
    Term,
    /// The guard term is clean; the obstruction was spliced in by *this* payload. No static
    /// gate can see it — this is the position `rho_pure_eval::decidable`'s module docs name as
    /// "the one position a static walk cannot see".
    Datum,
}

/// ★ **The two-class split, adopted verbatim from the machine lane (`6ab1c78b`).**
///
/// | class | meaning | remedy |
/// |---|---|---|
/// | [`DeciderGap`](Self::DeciderGap) | the answer **does not exist on this node** — no datum would produce one | refuse **loudly** |
/// | [`DataDependent`](Self::DataDependent) | the answer exists; *this* datum broke it (`x / y` is fine until `y` is 0) | recorded and `ERROR`-logged, **not** refused |
///
/// The partition is exactly the machine lane's criterion — *"decidable from the guard term
/// alone"* — and here it is **computed** rather than tabulated: a cause is a decider gap iff its
/// [`RefusalProvenance`] is [`Term`](RefusalProvenance::Term). Tabulating it is what lets a
/// gate drift, and drift is the mechanism by which this defect class recurred three times.
///
/// ⚠ **Neither class fires a COMM.** `dont_know_policy` still selects
/// `DontKnowPolicy::FailClosedBlock` for both; the class decides how *loud* the non-firing is,
/// never *whether* it fires. Failing closed was never the defect — being silent was.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum GuardRefusalClass {
    /// The decider has no procedure for this guard, for any payload.
    DeciderGap,
    /// The decider has a procedure; this payload took it outside its domain.
    DataDependent,
}

impl GuardRefusalClass {
    /// The class implied by a provenance. One rule, applied to every cause.
    pub const fn of(provenance: RefusalProvenance) -> Self {
        match provenance {
            RefusalProvenance::Term => GuardRefusalClass::DeciderGap,
            RefusalProvenance::Datum => GuardRefusalClass::DataDependent,
        }
    }
}

/// ★ **THE COMPLETE ENUMERATION of what stops a substrate lane deciding a `where` guard.**
///
/// Each variant is one of the three refusals both lanes' deciders apply, split by *what*
/// stopped it rather than by *which line* returned. There is no catch-all: a new stop must add
/// a variant here, and each lane's exhaustive matches will not compile until it is classified.
///
/// | # | cause | raised by | provenance | class |
/// |---|---|---|---|---|
/// | 1 | [`ResidualBinder`](Self::ResidualBinder) | step 1 — `encoding.vars` is non-empty | always `Term` | gap |
/// | 2 | [`Unsupported`](Self::Unsupported) | step 2 — the fragment carries a construct the delegated decider has no arm for | computed | either |
/// | 3 | [`NotABoolean`](Self::NotABoolean) | step 2 — the fragment evaluated cleanly to something that is not a verdict | computed | either |
/// | 4 | [`Malformed`](Self::Malformed) | step 2 — an expression node with no instance | computed | either |
/// | 5 | [`UnresolvedReference`](Self::UnresolvedReference) | step 2 — a variable reference survived substitution | always `Term` | gap |
/// | 6 | [`EvaluationFailed`](Self::EvaluationFailed) | step 2 — the fragment's evaluation ran and failed | always `Datum` | data-dependent |
/// | 7 | [`FormulaUndecided`](Self::FormulaUndecided) | step 3 — the substrate's own ground procedures gave up | always `Term` | gap |
///
/// ★ Rows 1 and 5 are **the same fact** — a slot no payload can supply — reached by two routes:
/// an encoder interns a binder as a substrate *variable* (row 1) but turns an unreadable
/// reference into an opaque *atom* (row 5), where the delegated evaluator then reports it.
/// Filing one fact in two classes because two code paths found it is exactly the arm-specific
/// drift that let this defect survive two fixes, so both are decider gaps.
///
/// ⚠ **Not every lane can reach every variant**, and that is a property of the lane's delegated
/// decider rather than of this enum. Rows 4–6 are read off an evaluator's *error channel*; a
/// lane whose delegated deciders answer `Option<bool>` has no such channel and therefore cannot
/// produce them. Each lane documents its own reachable subset at its decider.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GuardRefusalCause {
    /// A binder the substitution could not reach: a de Bruijn slot past the arrived bindings,
    /// or a match-frame slot the delegated evaluator rejects outright.
    ///
    /// Always [`RefusalProvenance::Term`]: substitution has *already* applied every binding the
    /// receive will ever get, so a surviving reference is one no payload can supply.
    ResidualBinder {
        /// The substrate names of the unreachable slots, in interning order.
        slots: Vec<String>,
    },
    /// The fragment carries a construct the delegated decider has no arm for. This is
    /// **precisely** the machine lane's undecidable class, and the names come from that lane's
    /// own derivation from the evaluator's arms so the two cannot drift.
    Unsupported {
        /// The construct names, in the order the evaluator would have reached them.
        nodes: Vec<String>,
    },
    /// The fragment evaluated cleanly, and the value is not a verdict — no predicate was ever
    /// tested. `where x + 1` is `Term`; `where x` under a non-boolean payload is `Datum`.
    NotABoolean,
    /// An expression node carrying no instance — a malformed term, not an undecidable one.
    Malformed,
    /// A variable reference survived substitution *inside an opaque fragment*, where the encoder
    /// interned no substrate variable for it. Row 1's fact, other route.
    UnresolvedReference {
        /// What could not be read: a de Bruijn slot, a wildcard — which binds anything and is
        /// therefore never a *readable* value — or a variable carrying no instance at all.
        slot: String,
    },
    /// The fragment's evaluation ran and failed on *this* payload: an operator type mismatch,
    /// a division by zero, an arithmetic overflow, or a non-single value where one was needed.
    EvaluationFailed {
        /// The evaluator's own rendering of the failure.
        error: String,
    },
    /// [`ground_verdict_with`] left the ground formula undecided after every binder was
    /// substituted and every opaque fragment resolved.
    ///
    /// [`ground_verdict_with`]: crate::guard_formula::ground_verdict_with
    FormulaUndecided,
}

impl GuardRefusalCause {
    /// The plain-English phrase a diagnostic quotes back to the author.
    fn describe(&self) -> String {
        match self {
            GuardRefusalCause::ResidualBinder { slots } => {
                format!("a binder the payload does not supply ({})", slots.join(", "))
            },
            GuardRefusalCause::Unsupported { nodes } => {
                format!("a construct the guard decider has no arm for ({})", nodes.join(", "))
            },
            GuardRefusalCause::NotABoolean => {
                "a value that is not a verdict — the guard is not a predicate".to_string()
            },
            GuardRefusalCause::Malformed => "a malformed expression node".to_string(),
            GuardRefusalCause::UnresolvedReference { slot } => {
                format!("an unreadable variable reference (`{slot}`)")
            },
            GuardRefusalCause::EvaluationFailed { error } => {
                format!("an evaluation failure on this payload ({error})")
            },
            GuardRefusalCause::FormulaUndecided => {
                "a formula the substrate's own procedures could not settle".to_string()
            },
        }
    }
}

/// One `where` guard a substrate lane produced **no verdict** for, recorded at the instant it
/// was refused.
///
/// ★ This is the whole point of the fix: a `GuardRefusal` exists exactly when the guard was
/// *not* decided, and it never exists when the guard was decided — so "the guard is false" and
/// "the guard could not be decided" are two different objects rather than one boolean.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GuardRefusal {
    /// What stopped the decider.
    pub cause: GuardRefusalCause,
    /// Whether the obstruction is in the guard term or arrived with the payload.
    pub provenance: RefusalProvenance,
    /// The remedy class implied by the provenance.
    pub class: GuardRefusalClass,
    /// What the refusal is *about*, rendered by the lane that raised it — required to be total,
    /// deterministic and bounded, so a refusal message never depends on a derive or on the
    /// build.
    ///
    /// For a [`RefusalProvenance::Term`] refusal this is **the guard as written**, and is
    /// therefore the same string under every payload. For a
    /// [`RefusalProvenance::Datum`] refusal whose obstruction is a *value* — a division by zero,
    /// a type mismatch — it is the offending **fragment** instead, because naming the whole
    /// guard would not say which datum broke it.
    ///
    /// ⚠ A lane whose terms are not ground values renders them in a stable opaque form (the
    /// lowered lane's is `⟨opaque Par, n bytes, blake2b256:…⟩`). That is a correlation handle,
    /// not the actionable part: the actionable part is [`cause`](Self::cause), which names what
    /// stopped the decider in the author's own vocabulary. A prettier rendering would mean a
    /// recursive printer with no stability contract, on a path that reaches published data.
    pub guard: String,
}

impl GuardRefusal {
    /// A refusal, with its [`GuardRefusalClass`] derived from `provenance` by the one rule.
    ///
    /// `guard` is the lane's own rendering of the term the refusal is about; see
    /// [`GuardRefusal::guard`] for the determinism contract it must meet.
    pub fn new(cause: GuardRefusalCause, provenance: RefusalProvenance, guard: String) -> Self {
        GuardRefusal {
            cause,
            provenance,
            class: GuardRefusalClass::of(provenance),
            guard,
        }
    }
}

impl std::fmt::Display for GuardRefusal {
    /// A **noun phrase**, not a sentence: it is written into the `obstructions` slot of
    /// `InterpreterError::UndecidableGuard`, whose own `Display` supplies the frame *"`where`
    /// guard cannot be decided: it contains …"*. Emitting a second full sentence here produced a
    /// doubled message, which is how this shape was arrived at.
    ///
    /// It names what stopped the decider, the guard it stopped on, and — because the remedies
    /// differ — whether the guard term or the payload carried the obstruction.
    ///
    /// A pure function of the recorded fields: [`GuardRefusal::guard`] is required to be
    /// deterministic and bounded, `GuardRefusalCause::describe` is a fixed per-variant phrase,
    /// and the foreign strings it can embed are hand-written `Display`s rather than derives. So
    /// two nodes deciding the same guard render the same bytes — which matters, because on the
    /// speculation lane this text reaches a published `^spec-failure` datum.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let provenance = match self.provenance {
            RefusalProvenance::Term => {
                "present in the guard term, so no payload can make this guard decidable"
            },
            RefusalProvenance::Datum => {
                "carried in by this payload; the guard term itself is decidable"
            },
        };
        write!(f, "{} in `{}` [{}]", self.cause.describe(), self.guard, provenance)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The class is DERIVED from the provenance, for every provenance. Tabulating it per cause
    /// is what let the machine lane's gate drift.
    #[test]
    fn the_class_is_a_function_of_the_provenance_alone() {
        assert_eq!(GuardRefusalClass::of(RefusalProvenance::Term), GuardRefusalClass::DeciderGap);
        assert_eq!(
            GuardRefusalClass::of(RefusalProvenance::Datum),
            GuardRefusalClass::DataDependent
        );
        for cause in [
            GuardRefusalCause::ResidualBinder { slots: vec!["y$0".to_string()] },
            GuardRefusalCause::Unsupported { nodes: vec!["matches".to_string()] },
            GuardRefusalCause::NotABoolean,
            GuardRefusalCause::Malformed,
            GuardRefusalCause::UnresolvedReference { slot: "_".to_string() },
            GuardRefusalCause::EvaluationFailed { error: "division by zero".to_string() },
            GuardRefusalCause::FormulaUndecided,
        ] {
            let term = GuardRefusal::new(cause.clone(), RefusalProvenance::Term, "g".to_string());
            let datum = GuardRefusal::new(cause, RefusalProvenance::Datum, "g".to_string());
            assert_eq!(term.class, GuardRefusalClass::DeciderGap);
            assert_eq!(datum.class, GuardRefusalClass::DataDependent);
        }
    }

    /// Every cause renders a distinct noun phrase, and the rendering names the guard and the
    /// provenance. A refusal whose `Display` did not distinguish two causes would put the two
    /// lanes' diagnostics back into one bucket at the last step.
    #[test]
    fn every_cause_renders_a_distinct_phrase_naming_guard_and_provenance() {
        let causes = [
            GuardRefusalCause::ResidualBinder { slots: vec!["y$0".to_string()] },
            GuardRefusalCause::Unsupported { nodes: vec!["matches".to_string()] },
            GuardRefusalCause::NotABoolean,
            GuardRefusalCause::Malformed,
            GuardRefusalCause::UnresolvedReference { slot: "_".to_string() },
            GuardRefusalCause::EvaluationFailed { error: "division by zero".to_string() },
            GuardRefusalCause::FormulaUndecided,
        ];
        let mut rendered: Vec<String> = Vec::with_capacity(causes.len());
        for cause in causes {
            let refusal =
                GuardRefusal::new(cause, RefusalProvenance::Term, "the guard".to_string());
            let text = refusal.to_string();
            assert!(text.contains("the guard"), "the rendering must name the guard: {text}");
            assert!(
                text.contains("no payload can make this guard decidable"),
                "the rendering must name the provenance: {text}"
            );
            rendered.push(text);
        }
        let mut deduped = rendered.clone();
        deduped.sort();
        deduped.dedup();
        assert_eq!(deduped.len(), rendered.len(), "two causes rendered the same phrase");
    }
}
