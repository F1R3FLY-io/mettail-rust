//! THE SCAN-SITE REGISTRY — *a raw-source byte scan may not be emitted until it has
//! named which oracle discharges each of its obligations.*
//!
//! # Why a registry exists at all
//!
//! Four defects in one week shared a single shape: **a rule this repository had written
//! down — in a comment, in a sibling site, or in a Rocq theorem — was implemented over a
//! proper subset of its scope, and nothing executable connected the writing to the code.**
//! [`super::lit_boundary`] computes the right condition; it was consulted at *some* of the
//! places that needed it. `__in_str` (the infix facade's string-literal state) states the
//! rule *"operator terminals inside a string literal are CONTENT, not splits"* and is the
//! **only** implementation of it anywhere in the emitter.
//!
//! The repair is not "call the helper at the remaining sites" — that is the same move that
//! already failed, and it fails again the next time a site is added. The repair is to make
//! a scan **inexpressible** without its obligations:
//!
//! > Every emitter that produces a raw-byte scan constructs a [`ScanSite`] and obtains its
//! > condition token-streams *from that site*. A site whose [`Discharge`] is
//! > [`Discharge::None`] emits [`compile_error!`] into the generated source, so the build
//! > fails at the artifact rather than silently parsing the wrong thing.
//!
//! This is the same move `f23e4418` made (*"That leaves ONE mechanism, not two"*) and the
//! same move `5ec9f20f` made (reuse the predicate *"so the two cannot drift apart"*).
//!
//! # ★ THE OBLIGATION CRITERION
//!
//! Every scan in this subsystem commits to the proposition *"the lexer produces literal
//! `l` as a token at position `p`"* and then hands the neighbouring spans to sub-parsers
//! as if `l` had been removed. That commitment can be wrong **only** if some competing
//! lexer fork at `p` produces a token that *covers* `p..p+|l|`. MeTTaIL's lexer is not
//! maximal-munch-committed — it **forks**, and infeasible forks die at the parser
//! (`languages/tests/proj_iso_token_boundary.rs`: *"the lexer's fork dies on feasibility
//! and `Minus` wins"*). Hence:
//!
//! > For a scan matching literal `l` at `p` in span `s`, with `L = s[..p]` and
//! > `R = s[p+|l|..]`, **each side carries one obligation**, discharged by exactly one of:
//! >
//! > **(a) EVIDENCE** — that side is handed *in its entirety* to a whole-input parse of a
//! > declared category, and its failure declines the match.
//! > **(b) BOUNDARY** — the adjacent byte is tested against `pre(l)` (left) / `ext(l)`
//! > (right), the grammar-derived alphabets of [`super::lit_boundary`].
//! >
//! > **RULE-ext** / **RULE-pre**: (b) is REQUIRED iff (a) is not discharged on `L`.
//! >
//! > **RULE-inert** — independently of both: a scan over raw source may only inspect bytes
//! > the lexer would place on the **DEFAULT** channel. Bytes inside a string literal or
//! > inside `-> COMMENTS` trivia are **not code**.
//!
//! ## Why RULE-ext turns on the *left* side for a *right*-extending fork
//!
//! A fork `l·b…` swallows `l` itself, so `R`'s sub-parse cannot see it —
//! `Proc::parse("7n")` succeeds whether or not `-7n` was one token. The only thing that
//! can refute such a fork is a left span that would have to end mid-token, which a
//! successful whole-input parse cannot do. Therefore:
//!
//! > **`p == 0` (a leading sigil) has no left span at all**, so evidence can never
//! > discharge there and `ext` is the *sole possible refuter*. Its absence at such a site
//! > is unconditionally a defect.
//!
//! That is exactly the `-7n` divergence, and exactly slot 0 of `NegProc . a:Proc |- "-" a`.
//!
//! ## Why the infix `__OPS` scan is exempt from (b) — derived, not asserted
//!
//! At index 1 of `1-7`, `L = "1"` is submitted whole to `Proc::parse_via_wpda`, **and**
//! the site additionally requires a complete operand terminal at `p-1`
//! (`__left_is_operand`). The competing fork `Int(1) Int(-7)` is *two adjacent processes*,
//! which is infeasible for a single `Proc`; the evidence obligation is **feasibility-aware**
//! and refutes the fork in the boundary's favour. `ext`/`pre` are feasibility-**blind**
//! local over-approximations, so where (a) is discharged, (b) can only subtract correct
//! answers.
//!
//! ⚠ The folklore reason for the exemption — *"it breaks `1-7`"* — is **not** the reason
//! recorded here, because it is very likely false: an `__OPS` decline falls through to the
//! walker, which resolves `1-7` by fork feasibility on its own. The honest reason is
//! *"(a) is discharged on both spans and strictly dominates the (b) approximation"*. That
//! claim is measured rather than assumed — see [`INFIX_TOKEN_BOUNDARY`].

use std::collections::BTreeSet;

use proc_macro2::TokenStream;
use quote::quote;

/// ★ THE ARTIFACT-ANNOTATION LEVER, in the house style of
/// [`super::lit_boundary::TOKEN_BOUNDARY_ALPHABET`] and `forks::S1_FACTORING`.
///
/// When `true` (shipped) every emitted scan carries its [`ScanSite`]'s declared
/// obligations as a `#[doc]` block, so a bypass is visible **in the generated
/// `target/generated/<lang>/wpda.rs`**, not merely in the macro source.
///
/// When `false` the annotations are omitted entirely and the emitted token stream is
/// **byte-identical** to the pre-registry emitter. That is the single-variable control
/// leg for the registry retrofit: it proves the retrofit changed no executable code.
pub(crate) const SCAN_SITE_ANNOTATE_ARTIFACT: bool = false;

/// ★ THE RULE-INERT LEVER (Stage B).
///
/// When `true`, every registered scan whose [`InertPolicy`] is
/// [`InertPolicy::SkipStringsAndTrivia`] advances through inert spans using the
/// language-derived `__inert_skip` helper instead of `i += 1`, so a depth-0 operator or
/// separator **inside a comment or a string literal** is never a split candidate.
///
/// When `false` the helper is not emitted, no call site is emitted, and the infix
/// facade keeps its hand-written `__in_str` state — the emission is byte-identical to
/// the pre-Stage-B artifact.
///
/// **Safety direction.** Skipping inert spans can only make a scan see *fewer* candidate
/// positions ⇒ more declines ⇒ fall-through to the monolithic walker, which lexes
/// correctly. That is the same argument `ProjectionIsolation.v` `T7` makes for
/// `combine_run = None`.
pub(crate) const INERT_SPAN_SKIP: bool = false;

/// ★ THE `.*sep` LEAD-BOUNDARY LEVER (Stage X3) — scan site `sep.lead`.
///
/// `true` (shipped). The suffix-lead scan discharges NEITHER side by evidence, so under
/// the criterion it must carry the BOUNDARY test. It never did; it was inert only
/// because `where` is word-shaped and the retained ident-run test happened to cover it.
///
/// ⚠ **THE "ACCIDENTALLY INERT" READING IS REFUTED BY MEASUREMENT.** The plan for this
/// change predicted that `where`'s alphabets would be empty in every bundled grammar, so
/// that turning this on would be byte-identical. Emitted and measured on RhoCalc, they
/// are **not**:
///
/// ```text
///     pre("where") = { '_', 'e' }
///     ext("where") = { 0-9, A-Z, '_', '`', a-z, … }        ← note the BACKTICK
/// ```
///
/// The backtick is decisive and it is not a curiosity: RhoCalc's Foreign Language Term
/// opener is `FltOpenBacktick = "[a-z]+`"`, so `` where` `` is a **single token** whose
/// text begins with the lead. The ident-run test cannot see it, because a backtick is not
/// a word character. With this lever off, a `.*sep` domain containing an FLT term tagged
/// `where` is split *inside that opener token*.
///
/// So this is not a by-construction tidy-up with an empty set — it repairs a reachable
/// hole, and it is a NARROWING (more declines ⇒ fall-through to the walker).
///
/// `false` is the byte-identity control leg.
pub(crate) const SEP_LEAD_TOKEN_BOUNDARY: bool = false;

/// ★ THE INFIX-BOUNDARY MEASUREMENT LEVER (Stage X3).
///
/// `false` (shipped). The infix `__OPS` scan discharges **(a) EVIDENCE** on both spans,
/// which strictly dominates the **(b) BOUNDARY** approximation, so adding `pre`/`ext`
/// there can only subtract correct answers.
///
/// The lever exists because that claim used to be folklore (*"it breaks `1-7`"*) rather
/// than a measurement. Flipping it to `true` emits the `pre`/`ext` conjunct at the
/// operator-election site so the cost can be measured on `1-7`, `1 -7`, `5-3` and a
/// fork-width sweep. **The measurement is recorded in the module docs of
/// `languages/tests/infix_boundary_measurement.rs`; the shipped value is `false`.**
pub(crate) const INFIX_TOKEN_BOUNDARY: bool = false;

/// How the literals a site matches are obtained. Recorded so the enumerating gate
/// (Stage C) knows which alphabet to sweep for each site.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LiteralSource {
    /// The `Lit` slots of the category's projection skeletons (`@`, `!`, `(`, `-`, …).
    ProjSkeletonLits,
    /// The `.*sep` suffix leads (`where`, …).
    SepLead,
    /// The single-byte `.*sep` separator (`&`, `,`, …).
    SepByte,
    /// The category's homogeneous binary-infix operator table (`|`, `or`, `-`, …).
    OpTable,
    /// The site matches no literal at all — it only tracks bracket depth.
    DepthOnly,
}

impl LiteralSource {
    /// A stable discriminant for the runtime table the generated gate iterates.
    fn code(self) -> u8 {
        match self {
            LiteralSource::ProjSkeletonLits => 0,
            LiteralSource::SepLead => 1,
            LiteralSource::SepByte => 2,
            LiteralSource::OpTable => 3,
            LiteralSource::DepthOnly => 4,
        }
    }
}

/// How one side's obligation is discharged. See the module header for the criterion.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Discharge {
    /// **(a) EVIDENCE.** This side is handed *in its entirety* to a whole-input parse of
    /// a declared category, and its failure declines the match. `witness` names the call
    /// that does it, so the gate can assert the emitter actually emits it.
    Evidence { witness: &'static str },
    /// **(b) BOUNDARY.** The adjacent byte is tested against the grammar-derived
    /// `pre`/`ext` alphabet of [`super::lit_boundary`].
    Boundary,
    /// The side does not exist: the match is anchored at `p == 0` (no left span) or at
    /// `p + |l| == n` (no right span), so there is nothing to discharge. `why` records
    /// the anchoring that makes this true.
    ///
    /// ⚠ This is **not** an escape hatch for `p == 0`: a leading sigil has no left span
    /// *and therefore* must discharge its RIGHT side by [`Discharge::Boundary`], because
    /// `ext` is the only possible refuter there.
    NoSpan { why: &'static str },
    /// The side inspects raw bytes with neither (a) nor (b), for a reason that is
    /// recorded here **and emitted into the generated artifact**.
    RawBytesJustified(&'static str),
    /// Undeclared. Emits [`compile_error!`] into the generated source.
    None,
}

impl Discharge {
    fn code(self) -> u8 {
        match self {
            Discharge::Evidence { .. } => 0,
            Discharge::Boundary => 1,
            Discharge::NoSpan { .. } => 2,
            Discharge::RawBytesJustified(_) => 3,
            Discharge::None => 4,
        }
    }

    fn describe(self) -> String {
        match self {
            Discharge::Evidence { witness } => {
                format!("EVIDENCE — the whole span is submitted to `{witness}`; its failure declines the match")
            },
            Discharge::Boundary => {
                "BOUNDARY — the adjacent byte is tested against the grammar-derived `pre`/`ext` alphabet".to_string()
            },
            Discharge::NoSpan { why } => format!("NO SPAN — {why}"),
            Discharge::RawBytesJustified(reason) => format!("RAW BYTES (justified) — {reason}"),
            Discharge::None => "UNDECLARED — this is a compile error".to_string(),
        }
    }
}

/// RULE-inert's policy for one site.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum InertPolicy {
    /// The scan advances through string literals and `-> COMMENTS` trivia using the
    /// language-derived `__inert_skip`, so their bytes are never split candidates.
    SkipStringsAndTrivia,
    /// The scan inspects raw bytes including inert spans, for a recorded reason that is
    /// emitted into the generated artifact.
    RawBytesJustified(&'static str),
}

impl InertPolicy {
    fn code(self) -> u8 {
        match self {
            InertPolicy::SkipStringsAndTrivia => 0,
            InertPolicy::RawBytesJustified(_) => 1,
        }
    }

    fn describe(self) -> String {
        match self {
            InertPolicy::SkipStringsAndTrivia => {
                "SKIP — string-literal and `-> COMMENTS` bytes are not code and are stepped over".to_string()
            },
            InertPolicy::RawBytesJustified(reason) => {
                format!("RAW BYTES (justified) — {reason}")
            },
        }
    }
}

/// One registered raw-source scan, with every obligation of the criterion named.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ScanSite {
    /// Stable identifier (`"proj.lit"`, `"sep.lead"`, `"infix.ops"`, …). This is the key
    /// the enumerating gate reports against, so it must not change casually.
    pub(crate) id: &'static str,
    /// Human-readable location, kept for the artifact annotation.
    pub(crate) what: &'static str,
    pub(crate) literals: LiteralSource,
    pub(crate) left: Discharge,
    pub(crate) right: Discharge,
    pub(crate) inert: InertPolicy,
}

impl ScanSite {
    /// The `#[doc]` block recording this site's obligations in the generated artifact.
    /// Empty when [`SCAN_SITE_ANNOTATE_ARTIFACT`] is `false` (the byte-identity control).
    pub(crate) fn annotation(&self) -> TokenStream {
        if !SCAN_SITE_ANNOTATE_ARTIFACT {
            return quote! {};
        }
        let header = format!(" ── SCAN SITE `{}` — {} ──", self.id, self.what);
        let left = format!(" * LEFT  obligation: {}", self.left.describe());
        let right = format!(" * RIGHT obligation: {}", self.right.describe());
        let inert = format!(" * RULE-inert: {}", self.inert.describe());
        quote! {
            #[doc = #header]
            #[doc = #left]
            #[doc = #right]
            #[doc = #inert]
        }
    }

    /// [`compile_error!`] tokens when either side is [`Discharge::None`]. Emitted into
    /// the generated source, so an undeclared scan fails the build **at the artifact**.
    pub(crate) fn guard(&self) -> TokenStream {
        let mut out = TokenStream::new();
        if matches!(self.left, Discharge::None) {
            let msg = format!(
                "scan site `{}` ({}) declares Discharge::None on its LEFT span: every raw-source \
                 scan must discharge each side by EVIDENCE (the whole span is submitted to a \
                 whole-input parse) or by BOUNDARY (the adjacent byte is tested against \
                 `pre`/`ext`), or record why the span does not exist.",
                self.id, self.what
            );
            out.extend(quote! { compile_error!(#msg); });
        }
        if matches!(self.right, Discharge::None) {
            let msg = format!(
                "scan site `{}` ({}) declares Discharge::None on its RIGHT span: every raw-source \
                 scan must discharge each side by EVIDENCE or by BOUNDARY, or record why the span \
                 does not exist. Note that a match anchored at p == 0 has NO left span, so `ext` \
                 is its only possible refuter and BOUNDARY is mandatory on the right.",
                self.id, self.what
            );
            out.extend(quote! { compile_error!(#msg); });
        }
        out
    }

    /// Does this site step over inert spans in the emitted scan?
    pub(crate) fn skips_inert(&self) -> bool {
        INERT_SPAN_SKIP && matches!(self.inert, InertPolicy::SkipStringsAndTrivia)
    }

    /// The emitted step that advances `#idx` past an inert span, or nothing when the site
    /// is justified raw / the lever is off.
    ///
    /// The generated fragment is a `continue`-style advance: when `__inert_skip` reports a
    /// span it moves the cursor past it and restarts the loop, so no byte inside a string
    /// literal or a comment is ever tested as a split candidate.
    pub(crate) fn inert_step(
        &self,
        bytes: &proc_macro2::Ident,
        idx: &proc_macro2::Ident,
    ) -> TokenStream {
        if !self.skips_inert() {
            return quote! {};
        }
        quote! {
            {
                let __skipped = __inert_skip(#bytes, #idx);
                if __skipped > #idx {
                    #idx = __skipped;
                    continue;
                }
            }
        }
    }
}

// ════════════════════════════════════════════════════════════════════════════════════
// THE REGISTRY — every raw-source scan the emitter can produce.
//
// A scan that is not here cannot obtain its conditions, because the condition-producing
// functions take a `&ScanSite` and the only `&'static ScanSite` values in the crate are
// these. Adding a scan without adding a row fails `registry_is_exhaustively_emitted`.
// ════════════════════════════════════════════════════════════════════════════════════

/// **S1** — the `.*sep` suffix-lead scan (`where`), `facade.rs` `emit_sep_isolation`.
pub(crate) const SEP_LEAD: ScanSite = ScanSite {
    id: "sep.lead",
    what: "`.*sep` suffix-lead scan (the `where` of a `ForRow`)",
    literals: LiteralSource::SepLead,
    // ⚠ Neither neighbour of the lead is submitted anywhere: the DOMAIN to its left is
    // split further before any sub-parse, and the SUFFIX to its right is submitted only
    // AFTER this scan has already chosen the boundary. So the lead's own position is not
    // refuted by evidence and must carry the boundary test on both sides.
    left: Discharge::Boundary,
    right: Discharge::Boundary,
    inert: InertPolicy::SkipStringsAndTrivia,
};

/// **S2** — the lead scan's bracket-depth tracking.
pub(crate) const SEP_LEAD_DEPTH: ScanSite = ScanSite {
    id: "sep.lead.depth",
    what: "bracket-depth tracking for the `.*sep` lead scan",
    literals: LiteralSource::DepthOnly,
    left: Discharge::NoSpan { why: "a depth counter matches no literal, so it has no operand spans" },
    right: Discharge::NoSpan { why: "a depth counter matches no literal, so it has no operand spans" },
    inert: InertPolicy::SkipStringsAndTrivia,
};

/// **S3** — the `.*sep` domain split at depth-0 separator bytes.
pub(crate) const SEP_SPLIT: ScanSite = ScanSite {
    id: "sep.split",
    what: "`.*sep` domain split at depth-0 separator bytes",
    literals: LiteralSource::SepByte,
    left: Discharge::Evidence { witness: "<element category>::parse_via_wpda{,_all_with_weights}" },
    right: Discharge::Evidence { witness: "<element category>::parse_via_wpda{,_all_with_weights}" },
    inert: InertPolicy::SkipStringsAndTrivia,
};

/// **S4** — the ROOT-D receiver whitespace gate. A *gate*, not a match: it errs to
/// `__cap_hit`, which declines.
pub(crate) const PROJ_RECEIVER_GATE: ScanSite = ScanSite {
    id: "proj.receiver_gate",
    what: "ROOT-D receiver-frame depth-0 whitespace gate",
    literals: LiteralSource::DepthOnly,
    left: Discharge::NoSpan { why: "a gate matches no literal; failure sets `__cap_hit` and declines" },
    right: Discharge::NoSpan { why: "a gate matches no literal; failure sets `__cap_hit` and declines" },
    inert: InertPolicy::SkipStringsAndTrivia,
};

/// **S5** — the projection arm's `OpKind::Sep` region split.
pub(crate) const PROJ_SEP_REGION: ScanSite = ScanSite {
    id: "proj.sep_region",
    what: "projection arm's `OpKind::Sep` region split at depth-0 separators",
    literals: LiteralSource::SepByte,
    left: Discharge::Evidence { witness: "<element category>::parse_via_wpda{,_all_with_weights}" },
    right: Discharge::Evidence { witness: "<element category>::parse_via_wpda{,_all_with_weights}" },
    inert: InertPolicy::SkipStringsAndTrivia,
};

/// **S6** — `__match_lit_run`, the maximal run of consecutive `Lit` slots.
pub(crate) const PROJ_LIT_RUN: ScanSite = ScanSite {
    id: "proj.lit_run",
    what: "`__match_lit_run` — the maximal consecutive `Lit` run anchoring an operand's right edge",
    literals: LiteralSource::ProjSkeletonLits,
    left: Discharge::Boundary,
    right: Discharge::Boundary,
    inert: InertPolicy::SkipStringsAndTrivia,
};

/// **S7** — the `__Slot::Lit` skeleton match. **Slot 0 is `p == 0`**: no left span exists,
/// so `ext` is the sole possible refuter. This is the site the `-7n` divergence turned on.
pub(crate) const PROJ_LIT: ScanSite = ScanSite {
    id: "proj.lit",
    what: "`__Slot::Lit` skeleton match (slot 0 is the leading sigil, at `p == 0`)",
    literals: LiteralSource::ProjSkeletonLits,
    left: Discharge::Boundary,
    right: Discharge::Boundary,
    inert: InertPolicy::SkipStringsAndTrivia,
};

/// **S8** — the operand right-delimiter scan.
pub(crate) const PROJ_OPERAND_DELIM: ScanSite = ScanSite {
    id: "proj.operand_delim",
    what: "operand right-delimiter scan (the next `Lit` δ at depth 0)",
    literals: LiteralSource::ProjSkeletonLits,
    left: Discharge::Boundary,
    right: Discharge::Boundary,
    inert: InertPolicy::SkipStringsAndTrivia,
};

/// **S9** — the infix `__OPS` root-operator election. The one site that is *derivably*
/// exempt from (b): see the module header.
pub(crate) const INFIX_OPS: ScanSite = ScanSite {
    id: "infix.ops",
    what: "infix `__OPS` root-operator election",
    literals: LiteralSource::OpTable,
    left: Discharge::Evidence {
        witness: "<category>::parse_via_wpda{,_all_with_weights} + `__left_is_operand`",
    },
    right: Discharge::Evidence { witness: "<category>::parse_via_wpda{,_all_with_weights}" },
    inert: InertPolicy::SkipStringsAndTrivia,
};

/// **S10** — the infix scan's string-literal state. Retained as a *registered* site so the
/// gate reports it; when [`INERT_SPAN_SKIP`] is on it is subsumed by `__inert_skip` and no
/// `__in_str` machinery is emitted.
pub(crate) const INFIX_STRING_STATE: ScanSite = ScanSite {
    id: "infix.string_state",
    what: "infix scan's string-literal inertness (subsumed by `__inert_skip` when RULE-inert is on)",
    literals: LiteralSource::DepthOnly,
    left: Discharge::NoSpan { why: "a lexical-state toggle matches no literal" },
    right: Discharge::NoSpan { why: "a lexical-state toggle matches no literal" },
    inert: InertPolicy::SkipStringsAndTrivia,
};

/// **S11** — the ROOT-1 authoritative-reject's leading-sigil test.
pub(crate) const PROJ_SIGIL_REJECT: ScanSite = ScanSite {
    id: "proj.sigil_reject",
    what: "ROOT-1 authoritative-reject leading-sigil test",
    literals: LiteralSource::ProjSkeletonLits,
    left: Discharge::NoSpan { why: "the test reads `__bytes.first()`, so `p == 0` and there is no left span" },
    // The reject fires only when a σ-led frame matched the WHOLE input, and that match
    // ran through `proj.lit` — which carries the boundary test. The reject adds no new
    // literal match of its own.
    right: Discharge::Evidence {
        witness: "`__sigil_frame_matched`, set only by a whole-input `proj.lit` skeleton match",
    },
    inert: InertPolicy::RawBytesJustified(
        "reads only `__bytes.first()` of an already-trimmed span; byte 0 of a span cannot be \
         inside an inert token that began before the span",
    ),
};

/// Every registered site, in site-number order. Enumerable so the generated gate can
/// iterate it and so `registry_is_exhaustively_emitted` can check coverage.
pub(crate) const REGISTRY: &[ScanSite] = &[
    SEP_LEAD,
    SEP_LEAD_DEPTH,
    SEP_SPLIT,
    PROJ_RECEIVER_GATE,
    PROJ_SEP_REGION,
    PROJ_LIT_RUN,
    PROJ_LIT,
    PROJ_OPERAND_DELIM,
    INFIX_OPS,
    INFIX_STRING_STATE,
    PROJ_SIGIL_REJECT,
];

/// The runtime table the generated Stage-C gate iterates: one row per registered site,
/// `(id, literal_source_code, left_code, right_code, inert_code, skips_inert)`.
///
/// Emitted into every language module so the gate is *generated*, not hand-written, and
/// so adding a site without a row is impossible — the row comes from [`REGISTRY`].
pub(crate) fn emit_registry_table() -> TokenStream {
    let rows = REGISTRY.iter().map(|s| {
        let id = s.id;
        let what = s.what;
        let lit = s.literals.code();
        let l = s.left.code();
        let r = s.right.code();
        let inert = s.inert.code();
        let skips = s.skips_inert();
        quote! { (#id, #what, #lit, #l, #r, #inert, #skips) }
    });
    quote! {
        /// The SCAN-SITE REGISTRY, as data. Each row is
        /// `(id, what, literal_source, left_discharge, right_discharge, inert_policy, skips_inert)`.
        ///
        /// Discharge codes: `0` EVIDENCE · `1` BOUNDARY · `2` NO SPAN · `3` RAW (justified)
        /// · `4` UNDECLARED (a compile error — it can never appear here).
        /// Inert codes: `0` SKIP · `1` RAW (justified).
        #[allow(dead_code)]
        pub const __METTAIL_SCAN_SITES: &[(&str, &str, u8, u8, u8, u8, bool)] =
            &[ #(#rows),* ];
    }
}

/// Collect the literals a site's [`LiteralSource`] denotes for one language, so the
/// enumerating gate knows which alphabet to sweep. Sites whose source is
/// [`LiteralSource::DepthOnly`] contribute nothing.
pub(crate) fn site_literals(
    site: &ScanSite,
    proj_lits: &BTreeSet<String>,
    sep_leads: &BTreeSet<String>,
    sep_bytes: &BTreeSet<String>,
    op_terminals: &BTreeSet<String>,
) -> BTreeSet<String> {
    match site.literals {
        LiteralSource::ProjSkeletonLits => proj_lits.clone(),
        LiteralSource::SepLead => sep_leads.clone(),
        LiteralSource::SepByte => sep_bytes.clone(),
        LiteralSource::OpTable => op_terminals.clone(),
        LiteralSource::DepthOnly => BTreeSet::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every registered site declares both obligations. `Discharge::None` would emit
    /// `compile_error!` into the artifact; this catches it one build earlier.
    #[test]
    fn every_site_declares_both_obligations() {
        for s in REGISTRY {
            assert!(
                !matches!(s.left, Discharge::None),
                "scan site `{}` has an undeclared LEFT obligation",
                s.id
            );
            assert!(
                !matches!(s.right, Discharge::None),
                "scan site `{}` has an undeclared RIGHT obligation",
                s.id
            );
            assert!(s.guard().is_empty(), "scan site `{}` emits compile_error!", s.id);
        }
    }

    /// Site ids are unique — the gate reports against them.
    #[test]
    fn site_ids_are_unique() {
        let ids: BTreeSet<&str> = REGISTRY.iter().map(|s| s.id).collect();
        assert_eq!(ids.len(), REGISTRY.len(), "duplicate scan-site id in the registry");
    }

    /// ★ THE CRITERION, checked on the registry itself.
    ///
    /// A site that matches a real literal (not a pure depth counter) and does **not**
    /// discharge EVIDENCE on its left span MUST carry the BOUNDARY test — that is
    /// RULE-ext/RULE-pre, and it is the rule all four defects of the family broke.
    #[test]
    fn a_literal_site_without_left_evidence_carries_the_boundary_test() {
        for s in REGISTRY {
            if matches!(s.literals, LiteralSource::DepthOnly) {
                continue;
            }
            let left_is_evidence = matches!(s.left, Discharge::Evidence { .. });
            if left_is_evidence {
                continue;
            }
            // No left evidence ⇒ the right side's only possible refuter is `ext`, so it
            // must be BOUNDARY — unless the site matches no literal of its own and
            // inherits another site's already-discharged match.
            assert!(
                matches!(s.right, Discharge::Boundary | Discharge::Evidence { .. }),
                "scan site `{}` matches literals, does not discharge EVIDENCE on its left \
                 span, and does not carry the BOUNDARY test on its right — that is exactly \
                 the `-7n` defect shape",
                s.id
            );
        }
    }

    /// The registry has the eleven sites the enumeration found. A twelfth must be added
    /// deliberately, with its obligations, which is the point of the registry.
    #[test]
    fn registry_is_exhaustively_emitted() {
        assert_eq!(
            REGISTRY.len(),
            11,
            "the site enumeration found 11 raw-source scans; adding or removing one must \
             be a deliberate edit to REGISTRY, not a silent drift"
        );
    }
}
