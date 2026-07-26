//! `rhocalc` — a RhoCalc (Rholang 1.4) interpreter over the f1r3node reducer.
//!
//! It takes a RhoCalc source-file PATH, parses it with the GENERATED RhoCalc parser
//! (`Proc::parse`), lowers it to a normalized `rhoapi::Par` (`lower_rhocalc_proc_with_resolver`),
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
//! The RhoCalc grammar supports Foreign Language Terms (FLT): the opener `tag`…`` embeds a term of
//! a guest language written in the guest's own concrete syntax. The interpreter is NOT
//! FLT-specific — it just interprets RhoCalc — but it supplies an [`FltResolve`] registry of the
//! guest languages it bundles (currently `lam`, the untyped λ-calculus `LambdaLanguage`) so that
//! programs USING the FLT feature lower, and so a bare guest term can be reduced to normal form by
//! that guest's reduction engine. A program with no FLT never touches the registry; a program
//! whose FLT opener is unregistered fails closed with a clear `unknown guest language ⌜tag⌝`.
//!
//! ## Comments are LEXED and RETAINED on the `COMMENTS` channel (task #18)
//! Comments are no longer removed before parsing. `//` line comments and `/* … */` block comments
//! are declared as ordinary tokens in the RhoCalc grammar's `tokens {}` block, routed to the
//! alternative channel `COMMENTS` (`languages/src/rhocalc.rs`). A `-> CHANNEL` token is TRIVIA: the
//! lexer resolves it by the same maximal-munch rule as every other token, and when it wins the span
//! is consumed but never delivered to the parse stream — exactly how inter-token whitespace is
//! already consumed. So the parser sees precisely the token sequence it saw under the old
//! pre-parse strip, while the comment TEXT and its source `Range` survive in
//! `LexResult.streams["COMMENTS"]`.
//!
//! The interpreter reads them back with [`comments_on_channel`] (`rhocalc::lex_with_streams` →
//! [`mettail_prattail::LexResult::tokens_on_channel`]) and reports the count, which is the proof
//! that retention is live end-to-end. `--emit-comments` dumps them with their positions.
//!
//! **The channel boundary is hard**: `COMMENTS` is compile-time / tooling-facing apparatus. Only
//! `DEFAULT` feeds the parser AND the running program. There is no `@"COMMENTS"` rho channel, no
//! injected send, and no way for a running RhoCalc program to observe a comment.
//!
//! ## Exit codes (sysexits-style)
//!   0  success · 64 usage · 66 cannot read input · 65 parse/lower error · 70 reduce/driver/stuck.

use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::Arc;

use mettail_languages::lambda::LambdaLanguage;
use mettail_languages::rhocalc::Proc;
use mettail_rholang_codegen::{
    lower_language_def, plan_rho_default_backend, reconstruct_language_def, rho_net_drive_call_par,
    suggest_rejected_rule_dispositions, FltRegistry, FltResolve, RhoCoverageEvidence,
    RhoDefaultBackendRequirements, RhoGuardCoverageEvidence, BOUND_VAR_REFLECT_LABEL,
    LAMBDA_REFLECT_LABEL, PEANO_SUCC_REFLECT_LABEL,
};
use mettail_rholang_runtime::{
    lower_rhocalc_proc_with_resolver, par_as_runtime_observation_value,
    run_normalized_par_for_oracle_and_read_runtime_values, DriveObservationChannels,
    PlannedRhoBackend, RhocalcAstLowerError,
};
use mettail_runtime::{clear_var_cache, Language, RuntimeObservationValue};
use models::rhoapi::Par;

const USAGE: &str = "\
rhocalc — RhoCalc (Rholang 1.4) interpreter over the f1r3node reducer

USAGE:
    rhocalc [--emit-comments] <SOURCE.rho>
    rhocalc --help

OPTIONS:
    --emit-comments   dump every comment retained on the COMMENTS channel with its source position.
                      Comments are LEXED (not stripped) and routed off the parser's DEFAULT stream;
                      this is a backend diagnostic, never data a running program can observe.

It parses the RhoCalc source with the generated parser, lowers it to a normalized Rholang term,
and evaluates it on the f1r3node reducer:
  * a bare term evaluates to its NORMAL FORM (reduced on the reducer by the registered guest's
    reduction engine), printed with the ^fired rewrite ledger;
  * a process (sends/receives) runs to rest and its @\"OUT\" observations are reported.

The RhoCalc grammar supports Foreign Language Terms (`tag`…``); the interpreter bundles the `lam`
guest (the untyped λ-calculus) so programs that embed λ-terms lower, run, and reduce.";

/// The guest registry the interpreter installs so RhoCalc's Foreign Language Term feature can
/// lower and reduce: the `lam` opener resolves to the production `LambdaLanguage`.
fn guest_resolver() -> Arc<dyn FltResolve> {
    Arc::new(FltRegistry::new().with_guest("lam", Box::new(LambdaLanguage)))
}

/// The registered `lam` guest's Rho-default reduction backend + its definition fingerprint
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

// ── error surface — one actionable message + a distinct exit code per failure class ─────────────

enum InterpError {
    Usage,
    Io { path: PathBuf, source: std::io::Error },
    Parse(String),
    Lower(RhocalcAstLowerError),
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
            }
            InterpError::Io { path, source } => {
                eprintln!("error: cannot read source file `{}`: {source}", path.display());
                ExitCode::from(66) // EX_NOINPUT
            }
            InterpError::Parse(message) => {
                eprintln!("error: parse error (RhoCalc / Rholang 1.4)");
                eprintln!("  {message}");
                ExitCode::from(65) // EX_DATAERR
            }
            InterpError::Lower(err) => report_lower(err),
            InterpError::Reduce(message) => {
                eprintln!("error: reduction failed on the f1r3node reducer");
                eprintln!("  {message}");
                ExitCode::from(70) // EX_SOFTWARE
            }
            InterpError::DriverError(rendered) => {
                eprintln!("error: the in-Rho reduction driver reported an unrecognized head / typed error");
                eprintln!("  offending datum(a): {rendered}");
                ExitCode::from(70)
            }
            InterpError::Stuck(rendered) => {
                eprintln!("error: the term did not reach a normal form — reduction fuel exhausted");
                eprintln!("  the term is non-terminating or exceeds the per-path reduction budget");
                eprintln!("  stuck redex(es): {rendered}");
                ExitCode::from(70)
            }
        }
    }
}

/// Map each `RhocalcAstLowerError` variant to a specific, actionable message. The FLT-resolver miss
/// (`UnresolvedFltTag`) gets the `unknown guest language ⌜tag⌝` message.
fn report_lower(err: &RhocalcAstLowerError) -> ExitCode {
    match err {
        RhocalcAstLowerError::UnresolvedFltTag(tag) => {
            eprintln!("error: unknown guest language ⌜{tag}⌝");
            eprintln!("  the RhoCalc program embeds a Foreign Language Term with opener `{tag}`,");
            eprintln!("  but no guest is registered for it. registered guests: lam (LambdaLanguage)");
            ExitCode::from(65)
        }
        RhocalcAstLowerError::FltGuestHasNoFingerprint(tag) => {
            eprintln!("error: FLT guest ⌜{tag}⌝ exposes no definition fingerprint");
            eprintln!("  its reflected tags cannot be minted — the guest has no lowered identity.");
            ExitCode::from(70)
        }
        RhocalcAstLowerError::FltReflect(message) => {
            eprintln!("error: the FLT guest could not reflect the embedded term");
            eprintln!(
                "  (a category mismatch, a malformed hole envelope, or an unfilled construction hole)"
            );
            eprintln!("  {message}");
            ExitCode::from(65)
        }
        other => {
            eprintln!("error: could not lower the RhoCalc program to the Rho machine");
            eprintln!("  {other:?}");
            ExitCode::from(65)
        }
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
    let Ok(lexed) = mettail_languages::rhocalc::lex_with_streams(source) else {
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

/// The conventional channel name RhoCalc's `tokens {}` block routes its comment tokens to. It
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
// WHAT REPLACED IT: the comment tokens now declared in the RhoCalc grammar's `tokens {}` block,
// routed to the retained `COMMENTS` channel —
//     LineComment  = "//[^\n]*"                  -> COMMENTS ;
//     BlockComment = "/\*([^*]|\*+[^*/])*\*+/"   -> COMMENTS ;
// (`languages/src/rhocalc.rs`). The lexer resolves them by maximal munch like every other token and
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
        }
        _ => 0,
    }
}

/// Render a decoded observation to compact surface syntax, special-casing the λ-calculus guest
/// (`λ.<body>` for lambdas, the de-Bruijn index for bound vars, `(<f> <a>)` for applications) so a
/// normal form such as the identity `I` reads legibly as `λ.0`.
fn render_obs(value: &RuntimeObservationValue) -> String {
    match value {
        RuntimeObservationValue::Term { constructor, children } => {
            let label = constructor.as_str();
            if label == LAMBDA_REFLECT_LABEL {
                if let [body] = children.as_slice() {
                    return format!("λ.{}", render_obs(body));
                }
            } else if label == BOUND_VAR_REFLECT_LABEL {
                if let [index] = children.as_slice() {
                    return peano_index(index).to_string();
                }
            } else if label == "App" {
                if let [fun, arg] = children.as_slice() {
                    return format!("({} {})", render_obs(fun), render_obs(arg));
                }
            }
            if children.is_empty() {
                constructor.clone()
            } else {
                let inner = children.iter().map(render_obs).collect::<Vec<_>>().join(", ");
                format!("{constructor}({inner})")
            }
        }
        other => format!("{other:?}"),
    }
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

// ── the two evaluation modes ────────────────────────────────────────────────────────────────────

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

/// Run a PROCESS to rest on the reducer and report the `@"OUT"` observations. This is the exact
/// helper the from-source beats use (`out_values_from_source`).
async fn run_process_to_rest(program: &Par) -> Result<(), InterpError> {
    println!("mode: process → running to rest on the f1r3node reducer (observing @\"OUT\")");
    let out_values = run_normalized_par_for_oracle_and_read_runtime_values(program, "OUT")
        .await
        .map_err(InterpError::Reduce)?;
    if out_values.is_empty() {
        println!("  @\"OUT\": (the program rested without publishing any observation)");
    } else {
        println!("  @\"OUT\" observations ({}):", out_values.len());
        for (index, value) in out_values.iter().enumerate() {
            println!("    [{index}] ⟦{}⟧", render_obs(value));
        }
    }
    Ok(())
}

// ── driver ──────────────────────────────────────────────────────────────────────────────────────

/// Parse, lower, and evaluate the RhoCalc source at `path`.
///
/// `emit_comments` dumps the retained `COMMENTS` channel (an out-of-band diagnostic artifact of the
/// BACKEND — never data on any program-observable channel).
async fn interpret(path: &Path, emit_comments: bool) -> Result<(), InterpError> {
    let source = std::fs::read_to_string(path)
        .map_err(|source| InterpError::Io { path: path.to_path_buf(), source })?;

    println!("rhocalc — RhoCalc (Rholang 1.4) interpreter");
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
    // (`redisplay == display`). Display stability is not term preservation, and RhoCalc's display
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
    // Every other production caller of the RhoCalc parser already uses `parse_via_wpda` (it is
    // "the disambiguated best-parse entry the production AST-first lowering path uses" —
    // `rho_rhocalc_conformance.rs`); this binary was the sole outlier. The display defect itself
    // is upstream in the display codegen and is reported separately; using the production entry
    // removes it from this path entirely rather than compensating for it downstream.
    let proc = Proc::parse_via_wpda(&source)
        .map_err(|err| InterpError::Parse(err.to_string()))?;
    let program =
        lower_rhocalc_proc_with_resolver(&proc, guest_resolver()).map_err(InterpError::Lower)?;

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
            }
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
