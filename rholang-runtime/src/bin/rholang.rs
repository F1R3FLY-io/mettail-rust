//! `rholang` — a Rholang (Rholang 1.4) interpreter over the f1r3node reducer.
//!
//! It takes a Rholang source-file PATH, parses it with the GENERATED Rholang parser
//! (`Proc::parse`), lowers it to a normalized `rhoapi::Par` (`lower_rholang_proc_with_resolver`),
//! and EVALUATES it on the real f1r3node Rholang reducer — no host/Dovetail simulation.
//!
//! ## Evaluation: a term reduces to its normal form; a process runs to rest
//! The interpreter dispatches on the lowered program's shape, the usual expression-vs-statement
//! dichotomy:
//!  * A bare **term** (no top-level send/receive/new) EVALUATES TO ITS NORMAL FORM. The reduction
//!    runs entirely on the reducer, driven by the registered guest language's own reduction engine
//!    (its in-Rho quiescence driver, seeded with `rho_net_drive_call_par`); the resulting normal
//!    form is read from `@"OUT"` along with the `^fired` rewrite ledger. This is the mechanism the
//!    `flt_from_source` Beat-4 subject-drive test pins.
//!  * A **process** (sends/receives/news) RUNS TO REST via
//!    `run_normalized_par_for_oracle_and_read_runtime_values`, and its `@"OUT"` observations are
//!    reported.
//!
//! ## Foreign Language Terms are a grammar feature, not a special case
//! The Rholang grammar supports Foreign Language Terms (FLT): the opener `tag`…`` embeds a term of
//! a guest language written in the guest's own concrete syntax. The interpreter is NOT
//! FLT-specific — it just interprets Rholang — but it supplies an [`FltResolve`] registry of the
//! guest languages it bundles (`calculator`, the production `CalculatorLanguage`; `lambda`, the
//! untyped λ-calculus `LambdaLanguage`) so that programs USING the FLT feature lower, and so a bare guest term can be reduced to normal form by
//! that guest's reduction engine. A program with no FLT never touches the registry; a program
//! whose FLT opener is unregistered fails closed with a clear `unknown guest language ⌜tag⌝`.
//!
//! ## Comments are LEXED and RETAINED on the `COMMENTS` channel (task #18)
//! Comments are no longer removed before parsing. `//` line comments and `/* … */` block comments
//! are declared as ordinary tokens in the Rholang grammar's `tokens {}` block, routed to the
//! alternative channel `COMMENTS` (`languages/src/rholang.rs`). A `-> CHANNEL` token is TRIVIA: the
//! lexer resolves it by the same maximal-munch rule as every other token, and when it wins the span
//! is consumed but never delivered to the parse stream — exactly how inter-token whitespace is
//! already consumed. So the parser sees precisely the token sequence it saw under the old
//! pre-parse strip, while the comment TEXT and its source `Range` survive in
//! `LexResult.streams["COMMENTS"]`.
//!
//! The interpreter reads them back with [`comments_on_channel`] (`rholang::lex_with_streams` →
//! [`mettail_prattail::LexResult::tokens_on_channel`]) and reports the count, which is the proof
//! that retention is live end-to-end. `--emit-comments` dumps them with their positions.
//!
//! **The channel boundary is hard**: `COMMENTS` is compile-time / tooling-facing apparatus. Only
//! `DEFAULT` feeds the parser AND the running program. There is no `@"COMMENTS"` rho channel, no
//! injected send, and no way for a running Rholang program to observe a comment.
//!
//! ## Exit codes (sysexits-style)
//!   0  success · 64 usage · 66 cannot read input · 65 parse/lower error · 70 reduce/driver/stuck.

use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::Arc;

use mettail_languages::calculator::CalculatorLanguage;
use mettail_languages::lambda::LambdaLanguage;
use mettail_languages::rholang::Proc;
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reconstruct_language_def, rho_net_drive_call_par,
    suggest_rejected_rule_dispositions, FltReflect, FltRegistry, FltResolve, RhoCoverageEvidence,
    RhoDefaultBackendRequirements, RhoFoldDataflowDisposition, RhoGuardCoverageEvidence,
    RhoScalarType, BOUND_VAR_REFLECT_LABEL, LAMBDA_REFLECT_LABEL, PEANO_SUCC_REFLECT_LABEL,
};
use mettail_rholang_runtime::lookahead::{
    SPEC_DELIVERY_CHANNEL, SPEC_ERR_CHANNEL, SPEC_FAILURE_CHANNEL, SPEC_REQUEST_CHANNELS,
    SPEC_SUCCESS_CHANNEL, SPEC_TRUNCATED_CHANNEL,
};
use mettail_rholang_runtime::speculation::search::ErrorCode;
use mettail_rholang_runtime::speculation::server::{LookaheadEngine, SpeculationGuest};
use mettail_rholang_runtime::{
    lower_rholang_proc_with_resolver, par_as_runtime_observation_value,
    render_observation_text_with, run_normalized_par_with_lookahead_engine,
    DriveObservationChannels, ObservationTermNotation, PlannedRhoBackend, RholangAstLowerError,
};
use mettail_runtime::{clear_var_cache, Language, RuntimeObservationValue};
use models::rhoapi::Par;

const USAGE: &str = "\
rholang — Rholang (Rholang 1.4) interpreter over the f1r3node reducer

USAGE:
    rholang [--emit-comments] <SOURCE.rho>
    rholang --help

OPTIONS:
    --emit-comments   dump every comment retained on the COMMENTS channel with its source position.
                      Comments are LEXED (not stripped) and routed off the parser's DEFAULT stream;
                      this is a backend diagnostic, never data a running program can observe.

It parses the Rholang source with the generated parser, lowers it to a normalized Rholang term,
and evaluates it on the f1r3node reducer:
  * a bare term evaluates to its NORMAL FORM (reduced on the reducer by the registered guest's
    reduction engine), printed with the ^fired rewrite ledger;
  * a process (sends/receives) runs to rest and its @\"OUT\" observations are reported.

The Rholang grammar supports Foreign Language Terms (`tag`…``). An opener IS the lower-cased name
of the guest grammar, so the tag is never a nickname to memorize. The interpreter bundles two:
  * `calculator` — the production Calculator grammar (arithmetic, comparison, boolean, string). A
                   bare `calculator`…`` term EVALUATES to a value through the E3 fold-dataflow:
                   every operator becomes a real metered Rholang expression on the reducer.
  * `lambda`     — the untyped λ-calculus, reduced to normal form by its in-Rho quiescence driver.";

/// THE opener a guest is registered under: the lower-cased form of the grammar's OWN name, read off
/// the guest itself ([`mettail_runtime::Language::name`], which the `language!` macro emits from the
/// `LanguageDef`'s `name:` field). `CalculatorLanguage` ⟶ `calculator`; `LambdaLanguage` ⟶ `lambda`.
///
/// Derived rather than passed, because every hand-typed opener this interpreter has carried was an
/// arbitrary abbreviation that had to be corrected afterwards (`lam`, then `calc`). A registration
/// site that cannot name its own tag cannot invent a third one: adding a guest now yields exactly
/// one legal opener, and it is the one a reader would guess from the grammar's name.
fn derived_opener(guest: &dyn FltReflect) -> String {
    guest.name().to_lowercase()
}

/// The guest registry the interpreter installs so Rholang's Foreign Language Term feature can
/// lower and reduce. Each guest is registered under [`derived_opener`].
fn guest_resolver() -> Arc<dyn FltResolve> {
    let guests: Vec<Box<dyn FltReflect>> =
        vec![Box::new(CalculatorLanguage), Box::new(LambdaLanguage)];
    let registry = guests
        .into_iter()
        .fold(FltRegistry::new(), |registry, guest| {
            registry.with_guest(derived_opener(guest.as_ref()), guest)
        });
    Arc::new(registry)
}

/// The openers the registry accepts, in registration order — one derivation, so the `--help` text
/// and the unknown-guest diagnostic can never drift from what is actually registered.
fn registered_openers() -> Vec<String> {
    let guests: Vec<Box<dyn FltReflect>> =
        vec![Box::new(CalculatorLanguage), Box::new(LambdaLanguage)];
    guests
        .iter()
        .map(|guest| derived_opener(guest.as_ref()))
        .collect()
}

/// The registered `lambda` guest's Rho-default reduction backend + its definition fingerprint
/// (identical derivation to `flt_from_source::lambda_backend`, so the installed reducer program and
/// the reflected term share one fingerprint). This is the engine that reduces a bare guest term to
/// its normal form on the reducer.
fn lambda_backend() -> (PlannedRhoBackend, String) {
    let source = LambdaLanguage
        .metadata()
        .definition_source()
        .expect("generated LambdaLanguage must expose its definition_source");
    let def = reconstruct_language_def(source)
        .expect("LambdaLanguage definition_source must reconstruct as a LanguageDef");
    let lowering = lower_language_def(&def);
    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(suggest_rejected_rule_dispositions(
            &def, &lowering,
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan = plan_rho_default_backend(&def, requirements)
        .expect("production Lambda must plan its Rho-default backend");
    let fingerprint = plan.definition_fingerprint().to_string();
    (PlannedRhoBackend::from_plan(plan), fingerprint)
}

/// The registered `calculator` guest's Rho-default backend: the installed program carries one Rholang
/// CONTRACT per lowerable Calculator scalar operator (`AddInt`, `MulInt`, `GtInt`, …), each body a
/// real metered arithmetic/relational expression on the reducer. The E3 fold dataflow wires an
/// expression TREE through those contracts, one call per node, so `2 + 3 * 4` executes as two
/// communications and observes `14`.
///
/// Derived exactly as [`lambda_backend`] — from the generated language's own `definition_source`,
/// so the contracts the reducer runs are the production Calculator's own rules, not a fragment.
fn calculator_backend() -> Result<PlannedRhoBackend, String> {
    let source = CalculatorLanguage
        .metadata()
        .definition_source()
        .ok_or("generated CalculatorLanguage must expose its definition_source")?;
    let def = reconstruct_language_def(source)
        .map_err(|err| format!("CalculatorLanguage definition_source must reconstruct: {err}"))?;
    let lowering = lower_language_def(&def);
    let requirements = RhoDefaultBackendRequirements {
        coverage: RhoCoverageEvidence::CoveredRejectedRules(suggest_rejected_rule_dispositions(
            &def, &lowering,
        )),
        guard_coverage: RhoGuardCoverageEvidence::NoGuardObligations,
    };
    let plan = plan_rho_default_backend(&def, requirements)
        .map_err(|err| format!("Calculator could not plan its Rho-default backend: {err:?}"))?;
    Ok(PlannedRhoBackend::from_plan(plan))
}

// ── error surface — one actionable message + a distinct exit code per failure class ─────────────

enum InterpError {
    Usage,
    Io { path: PathBuf, source: std::io::Error },
    Parse(String),
    Lower(RholangAstLowerError),
    Reduce(String),
    DriverError(String),
    Stuck(String),
}

impl InterpError {
    /// Print a clear, actionable message to STDERR and return the process exit code.
    fn report(&self) -> ExitCode {
        match self {
            InterpError::Usage => {
                eprintln!("{USAGE}");
                ExitCode::from(64) // EX_USAGE
            },
            InterpError::Io { path, source } => {
                eprintln!("error: cannot read source file `{}`: {source}", path.display());
                ExitCode::from(66) // EX_NOINPUT
            },
            InterpError::Parse(message) => {
                eprintln!("error: parse error (Rholang / Rholang 1.4)");
                eprintln!("  {message}");
                ExitCode::from(65) // EX_DATAERR
            },
            InterpError::Lower(err) => report_lower(err),
            InterpError::Reduce(message) => {
                eprintln!("error: reduction failed on the f1r3node reducer");
                eprintln!("  {message}");
                ExitCode::from(70) // EX_SOFTWARE
            },
            InterpError::DriverError(rendered) => {
                eprintln!("error: the in-Rho reduction driver reported an unrecognized head / typed error");
                eprintln!("  offending datum(a): {rendered}");
                ExitCode::from(70)
            },
            InterpError::Stuck(rendered) => {
                eprintln!("error: the term did not reach a normal form — reduction fuel exhausted");
                eprintln!("  the term is non-terminating or exceeds the per-path reduction budget");
                eprintln!("  stuck redex(es): {rendered}");
                ExitCode::from(70)
            },
        }
    }
}

/// Map each `RholangAstLowerError` variant to a specific, actionable message. The FLT-resolver miss
/// (`UnresolvedFltTag`) gets the `unknown guest language ⌜tag⌝` message.
fn report_lower(err: &RholangAstLowerError) -> ExitCode {
    match err {
        RholangAstLowerError::UnresolvedFltTag(tag) => {
            eprintln!("error: unknown guest language ⌜{tag}⌝");
            eprintln!("  the Rholang program embeds a Foreign Language Term with opener `{tag}`,");
            eprintln!("  but no guest is registered for it. an opener is the LOWER-CASED name of");
            eprintln!("  the guest grammar; registered: {}", registered_openers().join(", "));
            ExitCode::from(65)
        },
        RholangAstLowerError::FltGuestHasNoFingerprint(tag) => {
            eprintln!("error: FLT guest ⌜{tag}⌝ exposes no definition fingerprint");
            eprintln!("  its reflected tags cannot be minted — the guest has no lowered identity.");
            ExitCode::from(70)
        },
        RholangAstLowerError::FltReflect(message) => {
            eprintln!("error: the FLT guest could not reflect the embedded term");
            eprintln!(
                "  (a category mismatch, a malformed hole envelope, or an unfilled construction hole)"
            );
            eprintln!("  {message}");
            ExitCode::from(65)
        },
        other => {
            eprintln!("error: could not lower the Rholang program to the Rho machine");
            eprintln!("  {other:?}");
            ExitCode::from(65)
        },
    }
}

// ── comments: LEXED to the retained `COMMENTS` channel (task #18) ───────────────────────────────

/// Every comment the lexer retained on the `COMMENTS` channel, as
/// `(text, line, column)` with 1-based line/column, in source order.
///
/// This is the BACKEND view of the channel: `lex_with_streams()` runs the same DFA tables and the
/// same maximal-munch rule the parse path runs, so the comments reported here are exactly the spans
/// the parse path consumed as trivia. Reading them is what makes the round trip observable —
/// `Proc::parse` cannot re-emit a comment, because a comment is off-`DEFAULT` and therefore has no
/// AST node to `Display`.
///
/// Failing to lex is NOT an error here: the caller's `Proc::parse` reports parse failures with a
/// far better message, so an unlexable source simply yields no comments.
fn comments_on_channel(source: &str) -> Vec<(&str, usize, usize)> {
    let Ok(lexed) = mettail_languages::rholang::lex_with_streams(source) else {
        return Vec::new();
    };
    lexed
        .tokens_on_channel(COMMENTS_CHANNEL)
        .iter()
        .map(|(_token, range)| {
            // The retained `Range` indexes the ORIGINAL source, so the verbatim comment text is a
            // borrow of it — the precise thing the pre-parse strip destroyed.
            (
                &source[range.start.byte_offset..range.end.byte_offset],
                range.start.line + 1,
                range.start.column + 1,
            )
        })
        .collect()
}

/// The conventional channel name Rholang's `tokens {}` block routes its comment tokens to. It
/// carries no engine-level privilege — it is an ordinary channel name, treated exactly as
/// `PRAGMAS` or `DOCTESTS` would be.
const COMMENTS_CHANNEL: &str = "COMMENTS";

// ─────────────────────────────────────────────────────────────────────────────────────────────────
// RETIRED (task #18, 2026-07-25) — `fn strip_comments(source: &str) -> String`
//
// This was a PRE-PARSE STRING PREPROCESSOR: a 3-state (`Code`/`Str`/`Guest`) scanner that deleted
// comment bytes from the source before `Proc::parse` ever saw it, replacing them with nothing (and
// their newlines with newlines, so line numbers still tracked). It was lossy and unprincipled —
// column positions shifted, comments could never round-trip, and no downstream consumer could ever
// observe them.
//
// WHAT REPLACED IT: the comment tokens now declared in the Rholang grammar's `tokens {}` block,
// routed to the retained `COMMENTS` channel —
//     LineComment  = "//[^\n]*"                  -> COMMENTS ;
//     BlockComment = "/\*([^*]|\*+[^*/])*\*+/"   -> COMMENTS ;
// (`languages/src/rholang.rs`). The lexer resolves them by maximal munch like every other token and
// treats a channel-routed win as TRIVIA (consumed, never handed to the parser — `expand_lex_node_impl`
// and the `*_core_modal` scanners in `prattail/src/runtime_types.rs`), while `lex_with_streams()`
// retains them with their source `Range` for the backend (`comments_on_channel` above).
//
// Each hand-rolled state maps to a mechanism the lexer already had, which is why none of it is
// needed any more:
//   * `State::Str`   ⟶  `StringLit` is a single maximal-munch span, so a `//` inside `"…"` is
//                       string bytes and never sits at a token-start position.
//   * `State::Guest` ⟶  the FLT guest modes are RAW and declare their own tokens; the comment
//                       tokens exist only in the DEFAULT mode, so a marker inside a guest body is
//                       verbatim guest text.
//   * `//` vs `/`    ⟶  maximal munch, the same rule that already separates every other token pair.
//
// ONE DELIBERATE BEHAVIOUR CHANGE: an unterminated `/*` used to be swallowed silently to EOF. It is
// now a hard lex error (no accept ⇒ the modal core's unterminated-region surface), reported through
// the existing exit code 65. That is strictly better and is pinned by a test.
//
// Retained here (commented, not deleted) as the record of what the channel mechanism subsumed.
//
// fn strip_comments(source: &str) -> String {
//     enum State {
//         Code,
//         Str,
//         Guest,
//     }
//     let mut out = String::with_capacity(source.len());
//     let mut chars = source.chars().peekable();
//     let mut state = State::Code;
//     while let Some(c) = chars.next() {
//         match state {
//             State::Code => match c {
//                 '"' => {
//                     out.push('"');
//                     state = State::Str;
//                 }
//                 '`' => {
//                     out.push('`');
//                     state = State::Guest;
//                 }
//                 '/' if chars.peek() == Some(&'/') => {
//                     chars.next(); // consume the second '/'
//                     for next in chars.by_ref() {
//                         if next == '\n' {
//                             out.push('\n');
//                             break;
//                         }
//                     }
//                 }
//                 '/' if chars.peek() == Some(&'*') => {
//                     chars.next(); // consume the '*'
//                     let mut prev = '\0';
//                     for next in chars.by_ref() {
//                         if prev == '*' && next == '/' {
//                             break;
//                         }
//                         if next == '\n' {
//                             out.push('\n');
//                         }
//                         prev = next;
//                     }
//                 }
//                 _ => out.push(c),
//             },
//             State::Str => {
//                 out.push(c);
//                 if c == '"' {
//                     state = State::Code;
//                 }
//             }
//             State::Guest => {
//                 out.push(c);
//                 if c == '`' {
//                     state = State::Code;
//                 }
//             }
//         }
//     }
//     out
// }
// ─────────────────────────────────────────────────────────────────────────────────────────────────

// ── legible rendering of decoded observations (λ-calculus aware) ────────────────────────────────

/// The de-Bruijn index carried by a reflected `^peano` numeral (`Z ⟼ 0`, `S(n) ⟼ n + 1`).
fn peano_index(value: &RuntimeObservationValue) -> usize {
    match value {
        RuntimeObservationValue::Term { constructor, children }
            if constructor == PEANO_SUCC_REFLECT_LABEL =>
        {
            children.first().map(peano_index).unwrap_or(0) + 1
        },
        _ => 0,
    }
}

/// The body of a `^lambda` node, or `None` for anything else.
fn lambda_body(value: &RuntimeObservationValue) -> Option<&RuntimeObservationValue> {
    match value {
        RuntimeObservationValue::Term { constructor, children }
            if constructor == LAMBDA_REFLECT_LABEL =>
        {
            match children.as_slice() {
                [body] => Some(body),
                _ => None,
            }
        },
        _ => None,
    }
}

/// The de-Bruijn index of a `^bound` leaf, or `None` for anything else.
fn bound_index(value: &RuntimeObservationValue) -> Option<usize> {
    match value {
        RuntimeObservationValue::Term { constructor, children }
            if constructor == BOUND_VAR_REFLECT_LABEL =>
        {
            match children.as_slice() {
                [index] => Some(peano_index(index)),
                _ => None,
            }
        },
        _ => None,
    }
}

/// The two halves of an `App` node, or `None` for anything else.
fn app_parts(
    value: &RuntimeObservationValue,
) -> Option<(&RuntimeObservationValue, &RuntimeObservationValue)> {
    match value {
        RuntimeObservationValue::Term { constructor, children } if constructor == "App" => {
            match children.as_slice() {
                [fun, arg] => Some((fun, arg)),
                _ => None,
            }
        },
        _ => None,
    }
}

/// The CHURCH READING of a normal form, when it has one — a NAME for a shape the reducer produced,
/// never a computation. `λf.λx. f(f(…(f x)))` with `n` applications of the outer binder is the
/// Church numeral `n`; the two zero-application shapes are the Church booleans.
///
/// This exists because a Church numeral is *real* on screen but hard to read at a glance: the
/// audience should not have to count `1`s to see that the machine computed `6`. The reading is
/// derived STRUCTURALLY from the decoded observation, so it cannot report a number the reducer did
/// not produce — an unrecognized shape simply gets no annotation.
fn church_reading(value: &RuntimeObservationValue) -> Option<String> {
    // Two binders: the numeral's `f` (de Bruijn 1 in the body) and `x` (de Bruijn 0).
    let body = lambda_body(lambda_body(value)?)?;
    // Peel `App(1, …)` spines, counting the applications of `f`.
    let mut applications = 0usize;
    let mut cursor = body;
    while let Some((fun, arg)) = app_parts(cursor) {
        if bound_index(fun) != Some(1) {
            return None;
        }
        applications += 1;
        cursor = arg;
    }
    match (bound_index(cursor)?, applications) {
        (0, n) if n > 0 => Some(format!("Church numeral {n}")),
        // DELIBERATELY unannotated: the zero-application shapes `λf.λx.x` and `λt.λf.t` are the
        // Church booleans as much as they are the numeral zero, so a single name would be a
        // guess. They are also the very combinators the `flt-assay-desk` demo publishes, whose
        // transcripts are pinned byte-for-byte — an annotation there would be noise AND churn.
        _ => None,
    }
}

/// Render a decoded observation to compact surface syntax, adding the λ-calculus guest's own
/// surface for its `App` constructor so a normal form reads as `(f a)` rather than `App(f, a)`.
///
/// ★ Everything delegates to [`render_observation_text_with`], whose explicit work stack applies
/// the layout at every nesting level. The hook receives no child values, so it cannot reintroduce
/// native recursion.
///
/// The split is not "λ-specific vs structural" — it is **guest constructor vs reserved ABI
/// label**. `^lambda`, `^bound`, `^Z`/`^S` are reserved reflected-ABI tags shared by every
/// MeTTaIL language (`is_reserved_reflect_label(l) = l.starts_with('^')`, complete by
/// construction), so their sugar belongs in the library and is now rendered there. `App` is a
/// user constructor of `languages/src/lambda.rs`, so its surface is this binary's business.
///
/// This also closes a real defect. The old fallback arm was `other => format!("{other:?}")`,
/// which is why a `^spec-failure` datum — a `List([Bytes(…), List([Int(…), Text(…)])])` — used
/// to print as a Rust `Debug` dump with the message re-quoted inside it. `Display` renders the
/// same values as `0x…` hex and plain text, and is bounded and deterministic.
fn render_obs(value: &RuntimeObservationValue) -> String {
    render_observation_text_with(value, &|constructor, arity| {
        (constructor == "App" && arity == 2).then_some(ObservationTermNotation {
            open: "(",
            separator: " ",
            close: ")",
        })
    })
}

/// Render a slice of raw ledger `Par`s (decoding each) for the `^drive-err`/`^drive-fuel` reports.
fn render_pars(pars: &[Par]) -> String {
    if pars.is_empty() {
        return "(none)".to_string();
    }
    pars.iter()
        .map(|par| match par_as_runtime_observation_value(par) {
            Some(value) => format!("⟦{}⟧", render_obs(&value)),
            None => "⟨undecodable reflected Par⟩".to_string(),
        })
        .collect::<Vec<_>>()
        .join(", ")
}

/// Render one `^spec-failure` datum on a single line.
///
/// The FIPS failure entry is `[trace…, [code, message]]` — *"an extra two-element list
/// containing an error code for the failure and a message … concatenated to the end of the
/// trace"*. Two writers produce that shape with different trace representations (the request
/// server keys a guest-evaluator failure by a single `trace_digest`, the service emits the
/// step list), so this destructures what it can and falls back to [`render_pars`] for anything
/// else rather than refusing to print a datum it does not recognise.
///
/// ★ The trace digest is abbreviated to 8 hex characters **for presentation only**. Saying so
/// here because an abbreviated digest in a pinned demo transcript is exactly the thing that
/// later gets mistaken for the wire format.
fn render_spec_failure(datum: &Par) -> String {
    let fallback = || render_pars(std::slice::from_ref(datum));
    let Some(RuntimeObservationValue::List(entry)) = par_as_runtime_observation_value(datum) else {
        return fallback();
    };
    // The leaf is the last element; everything before it is the trace.
    let Some((leaf, trace)) = entry.split_last() else {
        return fallback();
    };
    let RuntimeObservationValue::List(leaf) = leaf else {
        return fallback();
    };
    let [RuntimeObservationValue::Int(code), RuntimeObservationValue::Text(message)] =
        leaf.as_slice()
    else {
        return fallback();
    };
    let named = match ErrorCode::from_i64(*code) {
        Some(known) => format!("code {code} ({})", known.label()),
        // Append-only discriminants: a newer writer's code is reported verbatim, never guessed.
        None => format!("code {code} (unrecognized)"),
    };
    let trace = match trace {
        [] => "trace (none)".to_string(),
        [RuntimeObservationValue::Bytes(handle)] => {
            let hex: String = handle
                .iter()
                .take(4)
                .map(|byte| format!("{byte:02x}"))
                .collect();
            format!("trace 0x{hex}…")
        },
        steps => format!("trace ({} step(s))", steps.len()),
    };
    format!("{trace}  {named}  {message}")
}

// ── the evaluation modes ────────────────────────────────────────────────────────────────────────

/// Evaluate a bare `calculator`…`` TERM to a VALUE on the reducer, through the E3 fold dataflow.
///
/// The guest body is parsed by the production `CalculatorLanguage`'s own parser, its expression
/// tree is lowered to a Rholang DATAFLOW (one contract call per operator node, wired through
/// intermediate channels in post-order), and that dataflow runs on the f1r3node reducer against the
/// installed Calculator contract program. Every `+`, `*`, `<`, `++` is therefore a real metered
/// Rholang expression evaluated by the machine — the host computes nothing.
///
/// Three dispositions, all reported rather than papered over: `Run` executes; `Defer` means the term
/// has no dataflow image (a collection, a big-numeric carrier, a fold with no Rho contract);
/// `BlockedBySemanticPredicate` means the term IS lowerable but a semantic predicate declined it
/// (`5 / 0` — the guard that stops an unguarded `EDiv` hard-erroring inside the reducer).
async fn evaluate_calculator_term(body: &str) -> Result<(), InterpError> {
    println!(
        "mode: term → evaluating on the f1r3node reducer (guest `calculator`, E3 fold dataflow)"
    );
    let parsed = CalculatorLanguage
        .parse_term_for_env(body)
        .map_err(|err| InterpError::Parse(format!("guest `calculator` body ⌜{body}⌝: {err}")))?;
    let disposition = CalculatorLanguage::rho_fold_dataflow_invocation_to(parsed.as_ref(), "OUT")
        .map_err(InterpError::Reduce)?;
    let invocation = match disposition {
        RhoFoldDataflowDisposition::Run(invocation) => invocation,
        RhoFoldDataflowDisposition::Defer => {
            return Err(InterpError::Reduce(format!(
                "the `calculator` term ⌜{body}⌝ has no Rholang dataflow image (its operators lower to \
                 native folds, not to Rho contracts) — it cannot be evaluated on the reducer"
            )))
        },
        RhoFoldDataflowDisposition::BlockedBySemanticPredicate(block) => {
            return Err(InterpError::Reduce(format!(
                "the `calculator` term ⌜{body}⌝ is blocked by a semantic predicate ({block:?}) — the \
                 machine declines it rather than emitting an operation that would hard-error"
            )))
        },
    };
    let backend = calculator_backend().map_err(InterpError::Reduce)?;
    let call = invocation.call;
    let rendered = match invocation.result_type {
        RhoScalarType::Int => backend
            .run_with_call_and_observe_ints(&call, "OUT")
            .await
            .map(|report| report.values.iter().map(i64::to_string).collect::<Vec<_>>()),
        RhoScalarType::Bool => backend
            .run_with_call_and_observe_bools(&call, "OUT")
            .await
            .map(|report| {
                report
                    .values
                    .iter()
                    .map(bool::to_string)
                    .collect::<Vec<_>>()
            }),
        RhoScalarType::Str => backend
            .run_with_call_and_observe_strings(&call, "OUT")
            .await
            .map(|report| {
                report
                    .values
                    .iter()
                    .map(|value| format!("{value:?}"))
                    .collect::<Vec<_>>()
            }),
    }
    .map_err(InterpError::Reduce)?;
    if rendered.is_empty() {
        println!("  value on @\"OUT\": (none observed)");
    } else {
        println!("  value on @\"OUT\" ({}):", rendered.len());
        for (index, value) in rendered.iter().enumerate() {
            println!("    [{index}] {value}");
        }
    }
    Ok(())
}

/// Evaluate a bare guest TERM to its normal form: seed it into the registered guest's in-Rho
/// reduction driver and reduce fully on the reducer. Fail-closed on driver errors and fuel
/// exhaustion.
async fn evaluate_term_to_normal_form(term: Par) -> Result<(), InterpError> {
    println!("mode: term → reducing to normal form on the f1r3node reducer");
    let (backend, fingerprint) = lambda_backend();
    let seed = rho_net_drive_call_par(&fingerprint, term, "OUT");
    let channels = DriveObservationChannels::for_fingerprint(&fingerprint, "OUT");
    let set = backend
        .run_rho_net_with_call_and_read_observation_set(&seed, &channels)
        .await
        .map_err(InterpError::Reduce)?;

    // Fail-closed edge cases BEFORE reporting a normal form.
    if !set.err_data.is_empty() {
        return Err(InterpError::DriverError(render_pars(&set.err_data)));
    }
    if !set.fuel_data.is_empty() {
        return Err(InterpError::Stuck(render_pars(&set.fuel_data)));
    }

    let fired = set.fired_labels().map_err(InterpError::Reduce)?;
    if set.out_values.is_empty() {
        println!("  normal form on @\"OUT\": (none observed)");
    } else {
        println!("  normal form on @\"OUT\" ({}):", set.out_values.len());
        for (index, value) in set.out_values.iter().enumerate() {
            println!("    [{index}] ⟦{}⟧", render_obs(value));
            if let Some(reading) = church_reading(value) {
                println!("        = {reading}");
            }
        }
    }
    println!("  ^fired ledger: {fired:?}   ({} in-Rho rewrite firing(s))", fired.len());
    println!(
        "  ^drive-err: {} datum(a) · ^drive-fuel: {} datum(a)   (both empty ⟹ terminated by quiescence)",
        set.err_data.len(),
        set.fuel_data.len()
    );
    Ok(())
}

/// The `[*]` / `[n]` request server this interpreter installs, carrying the `lambda` guest.
///
/// A speculation over a Foreign Language Term needs the guest's **installed program** and a
/// **seed** that hands the reflected term to it — see `speculation::server`'s `prelude`
/// section. Registering the guest here, next to the FLT resolver that lowers its terms, is
/// what makes `lambda`…`` speculable; a subject of any other language is refused typed on
/// `^spec-err` rather than explored inert.
fn lookahead_engine() -> LookaheadEngine {
    let (backend, fingerprint) = lambda_backend();
    match backend.plan().installed_rho_net_program_par() {
        Ok(prelude) => {
            LookaheadEngine::new().with_guest(SpeculationGuest::driven(fingerprint, prelude))
        },
        // Fail-closed rather than fail-quiet: an engine with no guest still SERVES requests,
        // and refuses every foreign subject loudly on `^spec-err`. Silently installing no
        // engine at all would leave the request resting, which reads as "the feature is not
        // wired" rather than "this language's program would not lower".
        Err(_) => LookaheadEngine::new(),
    }
}

/// Run a PROCESS to rest on the reducer and report the `@"OUT"` observations, with the
/// `[*]` / `[n]` request server installed.
///
/// Fail-closed, in the same shape `evaluate_term_to_normal_form` uses for the drive's typed
/// channels: an unserved request or a request-level refusal is reported BEFORE any
/// observation, because a `[*]` that nothing served publishes nothing and is otherwise
/// indistinguishable from a program that legitimately observed nothing.
async fn run_process_to_rest(program: &Par) -> Result<(), InterpError> {
    println!("mode: process → running to rest on the f1r3node reducer (observing @\"OUT\")");
    let engine = lookahead_engine();

    let mut channels: Vec<&str> = Vec::with_capacity(SPEC_REQUEST_CHANNELS.len() + 6);
    channels.push("OUT");
    channels.push(SPEC_SUCCESS_CHANNEL);
    channels.push(SPEC_FAILURE_CHANNEL);
    channels.push(SPEC_TRUNCATED_CHANNEL);
    channels.push(SPEC_ERR_CHANNEL);
    channels.push(SPEC_DELIVERY_CHANNEL);
    channels.extend_from_slice(SPEC_REQUEST_CHANNELS);

    let rest = run_normalized_par_with_lookahead_engine(program, &engine, &channels)
        .await
        .map_err(InterpError::Reduce)?;
    let on = |channel: &str| rest.get(channel).map(Vec::as_slice).unwrap_or_default();

    // ★ FAIL-CLOSED: a request nobody served, or one the engine refused.
    let mut unserved: Vec<(&'static str, Vec<Par>)> =
        Vec::with_capacity(SPEC_REQUEST_CHANNELS.len());
    for channel in SPEC_REQUEST_CHANNELS {
        unserved.push((channel, on(channel).to_vec()));
    }
    let unserved = mettail_rholang_runtime::lookahead::unserved_requests(&unserved);
    if !unserved.is_empty() {
        // Name the channel and the rendered request per line. `UnservedRequest::rendered` is
        // now `render_par_text` (bounded, deterministic) rather than a prost `Debug` dump, so
        // this reads as a diagnostic instead of as ~15 KB of struct noise per request.
        let detail = unserved
            .iter()
            .map(|request| format!("{} ← {}", request.channel, request.rendered))
            .collect::<Vec<_>>()
            .join("; ");
        return Err(InterpError::DriverError(format!(
            "{} lookahead request(s) rested unserved: {detail}",
            unserved.len(),
        )));
    }
    if !on(SPEC_ERR_CHANNEL).is_empty() {
        return Err(InterpError::DriverError(render_pars(on(SPEC_ERR_CHANNEL))));
    }

    let out_values: Vec<RuntimeObservationValue> = on("OUT")
        .iter()
        .filter_map(par_as_runtime_observation_value)
        .collect();
    if out_values.is_empty() {
        println!("  @\"OUT\": (the program rested without publishing any observation)");
    } else {
        println!("  @\"OUT\" observations ({}):", out_values.len());
        for (index, value) in out_values.iter().enumerate() {
            println!("    [{index}] ⟦{}⟧", render_obs(value));
            if let Some(reading) = church_reading(value) {
                println!("        = {reading}");
            }
        }
    }

    // The speculation transcript, reported only when a `[*]` / `[n]` actually ran.
    let speculated = on(SPEC_DELIVERY_CHANNEL).len();
    if speculated > 0 {
        println!(
            "  lookahead: {speculated} request(s) served · ^spec-success: {} · ^spec-failure: {} \
             · ^spec-truncated: {}",
            on(SPEC_SUCCESS_CHANNEL).len(),
            on(SPEC_FAILURE_CHANNEL).len(),
            on(SPEC_TRUNCATED_CHANNEL).len(),
        );
        for (index, datum) in on(SPEC_FAILURE_CHANNEL).iter().enumerate() {
            println!("    ^spec-failure[{index}] {}", render_spec_failure(datum));
        }
    }
    Ok(())
}

// ── driver ──────────────────────────────────────────────────────────────────────────────────────

/// Parse, lower, and evaluate the Rholang source at `path`.
///
/// `emit_comments` dumps the retained `COMMENTS` channel (an out-of-band diagnostic artifact of the
/// BACKEND — never data on any program-observable channel).
async fn interpret(path: &Path, emit_comments: bool) -> Result<(), InterpError> {
    let source = std::fs::read_to_string(path)
        .map_err(|source| InterpError::Io { path: path.to_path_buf(), source })?;

    println!("rholang — Rholang (Rholang 1.4) interpreter");
    println!("source: {}", path.display());

    // Task #18: comments are LEXED, not stripped. They are routed to the `COMMENTS` channel, kept
    // off `DEFAULT` (so the parse below is byte-for-byte the parse of the comment-free program),
    // and RETAINED with their source positions for the backend. `interpret` reads them purely as a
    // diagnostic; nothing downstream — least of all the running program — can observe them.
    let comments = comments_on_channel(&source);
    if !comments.is_empty() {
        println!("comments: {} retained on the COMMENTS channel", comments.len());
    }
    if emit_comments {
        for (text, line, column) in &comments {
            println!("  {line}:{column}: {text}");
        }
    }

    // Fresh binder interning before the parse (mirrors every from-source beat).
    clear_var_cache();
    // ★ `parse_via_wpda`, NOT `Proc::parse` — the PRODUCTION parse entry.
    //
    // `Proc::parse` is `parse_structured`, which starts from `parse_via_wpda(input)` (the correct
    // term) and then, whenever `display(parsed) != input`, REPLACES the returned representative
    // with the reparse of its own DISPLAY, accepting it as soon as the display is a fixpoint
    // (`redisplay == display`). Display stability is not term preservation, and Rholang's display
    // is not term-preserving for a projection operand of an arithmetic/relational/boolean
    // operator: a scalar literal there is rendered through a PROJECTION SURFACE — the first
    // delimited single-param `Proc` rule reachable from the literal's category, which is
    // `POutputNil . q:Proc |- "@" "Nil" "!" "(" q ")"` (`macros/src/gen/syntax/display.rs`,
    // `find_projection_surface_wrapper`). So
    //
    //     parse_via_wpda("1 + 2")  =  Add(CastInt 1, CastInt 2)          ← correct
    //     display(that)            =  "@Nil!(1) + @Nil!(2)"              ← NOT term-preserving
    //     Proc::parse("1 + 2")     =  Add(POutputNil 1, POutputNil 2)    ← a pair of SENDS
    //
    // and every downstream symptom follows mechanically: the operand of `+`/`<`/`==`/`and`/`not`
    // is a PROCESS, not an expression, so arithmetic and comparison raise "parallel or non
    // expression found where expression expected", boolean connectives raise "Multiple
    // expressions given", and — silently — `where x == 42` becomes `EEq(BoundVar 0, Send)`, which
    // the STRUCTURAL `EEq` decides `false` while `x != 43` decides `true`. Guards over bound data
    // then never fire, and `match.rs::guard_passes` deliberately collapses "false" / "not a
    // boolean" / "eval failed" into one verdict, so the lowering artifact is invisible.
    //
    // Every other production caller of the Rholang parser already uses `parse_via_wpda` (it is
    // "the disambiguated best-parse entry the production AST-first lowering path uses" —
    // `rho_rholang_conformance.rs`); this binary was the sole outlier. The display defect itself
    // is upstream in the display codegen and is reported separately; using the production entry
    // removes it from this path entirely rather than compensating for it downstream.
    let proc = Proc::parse_via_wpda(&source).map_err(|err| InterpError::Parse(err.to_string()))?;

    // A WHOLE-PROGRAM bare FLT (the file is one `tag`…`` and nothing else) is evaluated by THAT
    // GUEST'S OWN engine, so the tag is read off the AST before lowering reflects it away. Each
    // registered guest brings its own reduction mechanism, and both run on the reducer:
    //   `calculator` → the E3 fold dataflow (metered Rholang arithmetic contracts);
    //   `lambda`     → the in-Rho quiescence driver (β as committed communications).
    let bare_guest = match &proc {
        Proc::PFlt(node) | Proc::PFltFence(node) | Proc::PFltBrace(node) => {
            Some((node.selector_name.clone(), node.body_src.clone()))
        },
        _ => None,
    };
    if let Some((tag, body)) = &bare_guest {
        if tag == &derived_opener(&CalculatorLanguage) {
            return evaluate_calculator_term(body).await;
        }
    }

    let program =
        lower_rholang_proc_with_resolver(&proc, guest_resolver()).map_err(InterpError::Lower)?;

    // Dispatch on the lowered program's shape: a bare term (no send/receive/new) evaluates to its
    // normal form; anything with process structure runs to rest.
    if program.sends.is_empty() && program.receives.is_empty() && program.news.is_empty() {
        evaluate_term_to_normal_form(program).await
    } else {
        run_process_to_rest(&program).await
    }
}

#[tokio::main]
async fn main() -> ExitCode {
    // Exactly one positional argument (the source path), plus the optional `--emit-comments` flag
    // in either order.
    let mut path: Option<PathBuf> = None;
    let mut emit_comments = false;
    for argument in std::env::args_os().skip(1) {
        match argument.to_str() {
            Some("-h") | Some("--help") => {
                println!("{USAGE}");
                return ExitCode::SUCCESS;
            },
            Some("--emit-comments") => emit_comments = true,
            _ if path.is_none() => path = Some(PathBuf::from(argument)),
            _ => return InterpError::Usage.report(),
        }
    }
    let Some(path) = path else {
        return InterpError::Usage.report();
    };
    match interpret(&path, emit_comments).await {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => err.report(),
    }
}
