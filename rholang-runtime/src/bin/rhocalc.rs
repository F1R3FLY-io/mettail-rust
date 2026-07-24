//! `rhocalc` — a RhoCalc (Rholang 1.4) interpreter over the f1r3node reducer.
//!
//! It takes a RhoCalc source-file PATH, parses it with the GENERATED RhoCalc parser
//! (`Proc::parse`), lowers it to a normalized `rhoapi::Par` (`lower_rhocalc_proc_with_resolver`),
//! and EVALUATES it on the real f1r3node Rholang reducer
//! (`run_normalized_par_for_oracle_and_read_runtime_values`) — no host/Dovetail simulation. The
//! observations that come to rest on `@"OUT"` are decoded and printed to stdout.
//!
//! ## Foreign Language Terms are a grammar feature, not a special case
//! The RhoCalc grammar supports Foreign Language Terms (FLT): the opener `tag`…`` embeds a term of
//! a guest language written in the guest's own concrete syntax. The interpreter is NOT
//! FLT-specific — it just interprets RhoCalc — but to lower a program that USES the FLT feature it
//! supplies an [`FltResolve`] registry of the guest languages it bundles (currently `lam`, the
//! untyped λ-calculus `LambdaLanguage`). A program with no FLT never touches it; a program whose
//! FLT opener is not registered fails closed with a clear `unknown guest language ⌜tag⌝` message.
//!
//! ## Comments
//! The interpreter strips `//` line comments and `/* … */` block comments (outside `"`-strings and
//! `` ` ``-delimited guest bodies) before handing the source to the generated parser. This is an
//! interim measure: the RhoCalc grammar exposes a per-token output-`stream` annotation, but that
//! channel routing is only wired into the opt-in `lex_with_streams` entry, not the default
//! `Proc::parse` path — so comments cannot yet be routed off the parser's token stream at the
//! grammar level. Stripping keeps them out of the parse without affecting interpretation.
//!
//! ## Exit codes (sysexits-style)
//!   0  success · 64 usage · 66 cannot read input · 65 parse/lower error · 70 reduce error.

use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::Arc;

use mettail_languages::lambda::LambdaLanguage;
use mettail_languages::rhocalc::Proc;
use mettail_rholang_codegen::{
    FltRegistry, FltResolve, BOUND_VAR_REFLECT_LABEL, LAMBDA_REFLECT_LABEL,
    PEANO_SUCC_REFLECT_LABEL,
};
use mettail_rholang_runtime::{
    lower_rhocalc_proc_with_resolver, run_normalized_par_for_oracle_and_read_runtime_values,
    RhocalcAstLowerError,
};
use mettail_runtime::{clear_var_cache, RuntimeObservationValue};

const USAGE: &str = "\
rhocalc — RhoCalc (Rholang 1.4) interpreter over the f1r3node reducer

USAGE:
    rhocalc <SOURCE.rho>
    rhocalc --help

It parses the RhoCalc source with the generated parser, lowers it to a normalized Rholang term,
and evaluates it on the f1r3node reducer, printing the observations that rest on @\"OUT\".

The RhoCalc grammar supports Foreign Language Terms (`tag`…``); the interpreter bundles the `lam`
guest (the untyped λ-calculus) so programs that embed λ-terms lower and run.";

/// The guest registry the interpreter installs so RhoCalc's Foreign Language Term feature can
/// lower: the `lam` opener resolves to the production `LambdaLanguage`.
fn guest_resolver() -> Arc<dyn FltResolve> {
    Arc::new(FltRegistry::new().with_guest("lam", Box::new(LambdaLanguage)))
}

// ── error surface — one actionable message + a distinct exit code per failure class ─────────────

enum InterpError {
    Usage,
    Io { path: PathBuf, source: std::io::Error },
    Parse(String),
    Lower(RhocalcAstLowerError),
    Reduce(String),
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

// ── comment stripping (UTF-8-safe; preserves string + guest-body literals) ──────────────────────

/// Strip `//` line comments and `/* … */` block comments, preserving text inside `"`-delimited
/// strings and `` ` ``-delimited FLT guest bodies (a `//` or `/*` there is never a comment).
/// Newlines are preserved so the parser's reported line numbers still track the source.
fn strip_comments(source: &str) -> String {
    enum State {
        Code,
        Str,
        Guest,
    }
    let mut out = String::with_capacity(source.len());
    let mut chars = source.chars().peekable();
    let mut state = State::Code;
    while let Some(c) = chars.next() {
        match state {
            State::Code => match c {
                '"' => {
                    out.push('"');
                    state = State::Str;
                }
                '`' => {
                    out.push('`');
                    state = State::Guest;
                }
                '/' if chars.peek() == Some(&'/') => {
                    chars.next(); // consume the second '/'
                    for next in chars.by_ref() {
                        if next == '\n' {
                            out.push('\n');
                            break;
                        }
                    }
                }
                '/' if chars.peek() == Some(&'*') => {
                    chars.next(); // consume the '*'
                    let mut prev = '\0';
                    for next in chars.by_ref() {
                        if prev == '*' && next == '/' {
                            break;
                        }
                        if next == '\n' {
                            out.push('\n');
                        }
                        prev = next;
                    }
                }
                _ => out.push(c),
            },
            State::Str => {
                out.push(c);
                if c == '"' {
                    state = State::Code;
                }
            }
            State::Guest => {
                out.push(c);
                if c == '`' {
                    state = State::Code;
                }
            }
        }
    }
    out
}

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
/// term such as `App(I, K)` reads legibly as `(λ.0 λ.λ.1)`.
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

// ── driver ──────────────────────────────────────────────────────────────────────────────────────

/// Parse, lower, and evaluate the RhoCalc source at `path`, reporting the `@"OUT"` observations.
async fn interpret(path: &Path) -> Result<(), InterpError> {
    let source = std::fs::read_to_string(path)
        .map_err(|source| InterpError::Io { path: path.to_path_buf(), source })?;

    println!("rhocalc — RhoCalc (Rholang 1.4) interpreter");
    println!("source: {}", path.display());

    // Fresh binder interning before the parse (mirrors every from-source beat).
    clear_var_cache();
    let program_source = strip_comments(&source);
    let proc = Proc::parse(&program_source).map_err(InterpError::Parse)?;
    let program =
        lower_rhocalc_proc_with_resolver(&proc, guest_resolver()).map_err(InterpError::Lower)?;

    println!("running on the f1r3node reducer (observing @\"OUT\") …");
    let out_values = run_normalized_par_for_oracle_and_read_runtime_values(&program, "OUT")
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

#[tokio::main]
async fn main() -> ExitCode {
    let mut args = std::env::args_os().skip(1);
    let first = match args.next() {
        Some(first) => first,
        None => return InterpError::Usage.report(),
    };
    if matches!(first.to_str(), Some("-h") | Some("--help")) {
        println!("{USAGE}");
        return ExitCode::SUCCESS;
    }
    if args.next().is_some() {
        // Exactly one positional argument (the source path) is accepted.
        return InterpError::Usage.report();
    }
    let path = PathBuf::from(first);
    match interpret(&path).await {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => err.report(),
    }
}
