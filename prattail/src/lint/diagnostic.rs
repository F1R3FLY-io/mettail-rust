use super::*;

// ══════════════════════════════════════════════════════════════════════════════
// Core types
// ══════════════════════════════════════════════════════════════════════════════

/// Lint severity level.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LintSeverity {
    /// Infrastructure informational — pipeline progress messages.
    Info,
    /// Informational note — no action required.
    Note,
    /// Compile-time warning — possible issue.
    Warning,
    /// Compile-time error — correctness bug.
    Error,
}

impl fmt::Display for LintSeverity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LintSeverity::Info => write!(f, "info"),
            LintSeverity::Note => write!(f, "note"),
            LintSeverity::Warning => write!(f, "warning"),
            LintSeverity::Error => write!(f, "error"),
        }
    }
}

/// Generate the `DiagnosticId` enum, `as_str()`, and `Display` from a single table.
macro_rules! define_diagnostic_ids {
    ( $( $variant:ident => $str:literal ),* $(,)? ) => {
        /// Strongly-typed diagnostic identifier.
        ///
        /// Each variant corresponds to a unique lint/diagnostic code.
        /// Use [`DiagnosticId::as_str()`] or `Display` for the string form.
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub enum DiagnosticId {
            $( $variant, )*
        }

        impl DiagnosticId {
            /// Return the canonical string form (e.g., `"W01"`, `"C-AP03"`).
            pub const fn as_str(&self) -> &'static str {
                match self {
                    $( DiagnosticId::$variant => $str, )*
                }
            }
        }

        impl fmt::Display for DiagnosticId {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(self.as_str())
            }
        }
    };
}

define_diagnostic_ids! {
    // ── Annotation (A) ──
    A01 => "A01", A02 => "A02", A03 => "A03", A04 => "A04", A05 => "A05",
    A06 => "A06", A07 => "A07", A08 => "A08", A09 => "A09", A10 => "A10",

    // ── Cross-category (C) ──
    C01 => "C01", C02 => "C02", C04 => "C04",
    CAP00 => "C-AP00", CAP01 => "C-AP01", CAP02 => "C-AP02",
    CAP03 => "C-AP03", CAP04 => "C-AP04", CAP05 => "C-AP05",

    // ── CEK machine ──
    CEK01 => "CEK01", CEK03 => "CEK03",

    // ── Composition (COMP / X) ──
    COMP08 => "COMP-08",
    X01 => "X01", X02 => "X02", X03 => "X03", X04 => "X04",
    X05 => "X05", X06 => "X06", X07 => "X07",

    // ── Decision tree (D) ──
    D01 => "D01", D02 => "D02", D03 => "D03", D04 => "D04", D05 => "D05",
    D06 => "D06", D07 => "D07", D08 => "D08", D09 => "D09", D10 => "D10",
    D11 => "D11", D12 => "D12", D13 => "D13", D14 => "D14",

    // ── Disambiguation (DIS) ──
    DIS01 => "DIS01", DIS02 => "DIS02", DIS03 => "DIS03", DIS04 => "DIS04", DIS05 => "DIS05",

    // ── Error (E) ──
    E01 => "E01", E02 => "E02",

    // ── E-graph (EG) ──
    EG01 => "EG01", EG02 => "EG02", EG03 => "EG03", EG04 => "EG04",

    // ── Grammar (G) ──
    G01 => "G01", G02 => "G02", G03 => "G03", G04 => "G04", G05 => "G05",
    G06 => "G06", G07 => "G07", G08 => "G08", G09 => "G09", G10 => "G10",
    G24 => "G24", G25 => "G25", G26 => "G26", G27 => "G27",
    G28 => "G28", G29 => "G29", G30 => "G30", G31 => "G31",
    G32 => "G32", G34 => "G34", G35 => "G35",
    G36 => "G36", G37 => "G37", G38 => "G38",
    G39 => "G39", G40 => "G40", G41 => "G41", G42 => "G42",

    // ── Infrastructure (I) ──
    I01 => "I01", I02 => "I02", I03 => "I03", I04 => "I04",
    I05 => "I05", I06 => "I06", I07 => "I07", I08 => "I08", I09 => "I09",
    I10 => "I10", I11 => "I11", I12 => "I12", I13 => "I13", I14 => "I14", I15 => "I15",
    I16 => "I16", I17 => "I17", I18 => "I18", I19 => "I19",
    I20 => "I20", I21 => "I21",

    // ── Keyword (K) ──
    K01 => "K01", K02 => "K02",

    // ── Lexer (L / LEX) ──
    L01 => "L01", L02 => "L02",
    LEX01 => "LEX01", LEX02 => "LEX02", LEX03 => "LEX03", LEX04 => "LEX04", LEX05 => "LEX05",

    // ── Literal (LT) ──
    LT01 => "LT01",

    // ── Morphism (M) ──
    M01 => "M01", M02 => "M02",

    // ── Missing (MS) ──
    MS01 => "MS01", MS02 => "MS02",

    // ── MSO ──
    MSO01 => "MSO01", MSO02 => "MSO02", MSO03 => "MSO03",

    // ── Multitrack (MT) ──
    MT01 => "MT01", MT02 => "MT02",

    // ── Naming (N) ──
    N01 => "N01", N02 => "N02", N03 => "N03", N04 => "N04",
    N05 => "N05", N06 => "N06", N07 => "N07",

    // ── Optimization (O) ──
    O01 => "O01", O02 => "O02",

    // ── Parsing (P) ──
    P03 => "P03", P04 => "P04", P05 => "P05", P06 => "P06",

    // ── Parallel (PAR) ──
    PAR01 => "PAR01", PAR02 => "PAR02", PAR03 => "PAR03",
    PAR04 => "PAR04",
    // Stage 10.8 (2026-05-05): PAR05 (trampoline-frame-variant-count) DELETED —
    // Frame_Cat enum gone with trampoline.rs (Stage 10.6).

    // ── Parser bridge (PB) ──
    PB01 => "PB01", PB02 => "PB02", PB03 => "PB03",

    // ── Prediction (PD) ──
    PD01 => "PD01", PD02 => "PD02", PD03 => "PD03", PD04 => "PD04",

    // ── Prefix (PR) ──
    PR01 => "PR01", PR02 => "PR02", PR03 => "PR03", PR04 => "PR04",

    // ── Pattern (PT) ──
    PT01 => "PT01", PT02 => "PT02", PT03 => "PT03",

    // ── Recovery (R) ──
    R01 => "R01", R02 => "R02", R05 => "R05", R06 => "R06", R07 => "R07",

    // ── Runtime analysis (RA) ──
    RA01 => "RA01", RA02 => "RA02", RA03 => "RA03",

    // ── Runtime (RT) ──
    RT01 => "RT01", RT02 => "RT02", RT03 => "RT03",
    RT04 => "RT04", RT05 => "RT05", RT06 => "RT06",
    // RT07: OSLF Phase-4 `.1` transducer dead-cast (empty pre-image). Emitted
    // only when `oslf-transducer` is on; the variant is always defined so the
    // ID table stays total.
    RT07 => "RT07",

    // ── Syntax (S) ──
    S01 => "S01", S02 => "S02", S03 => "S03", S04 => "S04", S05 => "S05", S06 => "S06",

    // ── SFT ──
    SFT01 => "SFT01", SFT02 => "SFT02", SFT03 => "SFT03", SFT04 => "SFT04",

    // ── Slash (SL) ──
    SL01 => "SL01", SL02 => "SL02",

    // ── Stratification (STRAT) — predicated types Phase 3F ──
    STRAT01 => "STRAT01",

    // ── DNF normalization (DNF) — predicated types Phase 1B ──
    DNF01 => "DNF01",

    // ── Tier override (TIER) — predicated types Phase 11 ──
    TIER01 => "TIER01",

    // ── Tokenization (TOK) — predicated types Phase 1A ──
    TOK01 => "TOK01",

    // ── Symbol (SYM) ──
    SYM01 => "SYM01", SYM02 => "SYM02", SYM03 => "SYM03", SYM04 => "SYM04",

    // ── Type (T) ──
    T01 => "T01", T02 => "T02", T03 => "T03", T04 => "T04",

    // ── Type witness (TW) ──
    TW01 => "TW01", TW02 => "TW02", TW03 => "TW03",

    // ── Unification (UN) ──
    UN01 => "UN01", UN02 => "UN02", UN03 => "UN03",

    // ── Validation (V) ──
    V01 => "V01", V02 => "V02", V03 => "V03", V04 => "V04", V05 => "V05", V06 => "V06",

    // ── WFST (W) ──
    W01 => "W01", W02 => "W02", W03 => "W03", W04 => "W04",
    W05 => "W05", W06 => "W06", W07 => "W07",
    W09 => "W09", W12 => "W12", W13 => "W13", W14 => "W14", W16 => "W16",

    // ── Zone (Z) ──
    Z01 => "Z01",
}

/// A structured lint diagnostic.
#[derive(Debug, Clone)]
pub struct LintDiagnostic {
    /// Lint ID (e.g., `DiagnosticId::G01`, `DiagnosticId::W01`).
    pub id: DiagnosticId,
    /// Human-readable lint name (e.g., "left-recursion", "dead-rule").
    pub name: &'static str,
    /// Severity level.
    pub severity: LintSeverity,
    /// Category name (for category-specific lints).
    pub category: Option<String>,
    /// Rule label (for rule-specific lints).
    pub rule: Option<String>,
    /// Diagnostic message.
    pub message: String,
    /// Optional fix suggestion.
    pub hint: Option<String>,
    /// Grammar name for multi-grammar context.
    pub grammar_name: Option<String>,
    /// Source location of the relevant rule in the `language!` macro.
    pub source_location: Option<SourceLocation>,
}

impl fmt::Display for LintDiagnostic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}[{}]: {}", self.severity, self.id, self.message)?;
        // Source location line (rustc-style `-->` pointer)
        if let Some(ref loc) = self.source_location {
            if loc.line > 0 {
                write!(f, "\n  --> <macro>:{}", loc)?;
            }
        }
        // Category/rule context line
        match (&self.category, &self.rule) {
            (Some(cat), Some(rule)) => {
                write!(f, "\n  = in category `{}`, rule `{}`", cat, rule)?;
            },
            (Some(cat), None) => {
                write!(f, "\n  = in category `{}`", cat)?;
            },
            _ => {},
        }
        if let Some(ref hint) = self.hint {
            write!(f, "\n  = hint: {}", hint)?;
        }
        Ok(())
    }
}

/// Emit all lint diagnostics to stderr (plain text).
pub fn emit_diagnostics(diagnostics: &[LintDiagnostic]) {
    for diag in diagnostics {
        eprintln!("{}", diag);
    }
}

/// Emit a single diagnostic to stderr with ANSI-colorized output.
///
/// Diagnostics whose severity is below the threshold set by `PRATTAIL_LINT_LEVEL`
/// are silently dropped. See [`lint_level()`] for the env-var semantics.
pub fn emit_diagnostic(diag: &LintDiagnostic) {
    if diag.severity < lint_level() {
        return;
    }
    eprintln!("{}", format_diagnostic_colored(diag));
}

/// Minimum severity level for diagnostic output.
///
/// Controlled by `PRATTAIL_LINT_LEVEL` env var:
/// - `"error"`: only errors
/// - `"warning"` (default): warnings and errors
/// - `"note"`: notes, warnings, errors
/// - `"info"` or `"all"`: everything
pub(crate) fn lint_level() -> LintSeverity {
    use std::cell::Cell;
    thread_local! {
        static CACHED: Cell<Option<LintSeverity>> = const { Cell::new(None) };
    }
    CACHED.with(|c| {
        if let Some(level) = c.get() {
            return level;
        }
        let level = match std::env::var("PRATTAIL_LINT_LEVEL").as_deref() {
            Ok("error") => LintSeverity::Error,
            Ok("note") => LintSeverity::Note,
            Ok("info") | Ok("all") => LintSeverity::Info,
            _ => LintSeverity::Warning, // default
        };
        c.set(Some(level));
        level
    })
}

/// Format a single lint diagnostic with ANSI colors.
///
/// Color scheme:
/// - Error: bold red label + ID
/// - Warning: bold yellow label + ID
/// - Note / Info: bold cyan label + ID
/// - Grammar name: dim parentheses after `[ID]` when present
/// - Source location (`-->`): bold blue
/// - Category/rule context (`= in`): dim
/// - Hint (`= hint:`): green
/// - Backtick-quoted identifiers: bold
pub fn format_diagnostic_colored(diag: &LintDiagnostic) -> String {
    use std::fmt::Write;
    let mut out = String::with_capacity(256);

    // Severity label + lint ID
    let (label_color, id_color) = match diag.severity {
        LintSeverity::Error => (ansi::BOLD_RED, ansi::BOLD_RED),
        LintSeverity::Warning => (ansi::BOLD_YELLOW, ansi::BOLD_YELLOW),
        LintSeverity::Note | LintSeverity::Info => (ansi::BOLD_CYAN, ansi::BOLD_CYAN),
    };

    // Colorize backtick-quoted identifiers in the message
    let message = colorize_backtick_spans(&diag.message, ansi::BOLD, ansi::RESET);

    write!(
        out,
        "{}{}{}[{}{}{}]",
        label_color,
        diag.severity,
        ansi::RESET,
        id_color,
        diag.id,
        ansi::RESET,
    )
    .expect("write to String");

    // Grammar name in dim parentheses after [ID]
    if let Some(ref grammar) = diag.grammar_name {
        write!(out, " {}({}){}", ansi::DIM, grammar, ansi::RESET).expect("write to String");
    }

    write!(out, ": {}", message).expect("write to String");

    // Source location (rustc-style `-->` pointer)
    if let Some(ref loc) = diag.source_location {
        if loc.line > 0 {
            write!(out, "\n  {}{}{} <macro>:{}", ansi::BOLD_BLUE, "-->", ansi::RESET, loc,)
                .expect("write to String");
        }
    }

    // Category/rule context
    match (&diag.category, &diag.rule) {
        (Some(cat), Some(rule)) => {
            write!(
                out,
                "\n  {}= in category `{}`, rule `{}`{}",
                ansi::DIM, cat, rule, ansi::RESET,
            ).expect("write to String");
        },
        (Some(cat), None) => {
            write!(out, "\n  {}= in category `{}`{}", ansi::DIM, cat, ansi::RESET,)
                .expect("write to String");
        },
        _ => {},
    }

    // Hint
    if let Some(ref hint) = diag.hint {
        let hint_colored = colorize_backtick_spans(hint, ansi::BOLD, ansi::GREEN);
        write!(out, "\n  {}= hint: {}{}", ansi::GREEN, hint_colored, ansi::RESET,)
            .expect("write to String");
    }

    out
}

/// Replace backtick-quoted spans `` `foo` `` with bold formatting.
///
/// Scans for matching pairs of backticks and wraps the enclosed text
/// (including backticks) with the given ANSI start/end codes.
pub fn colorize_backtick_spans(text: &str, start: &str, end: &str) -> String {
    let mut result = String::with_capacity(text.len() + 64);
    let mut chars = text.char_indices().peekable();

    while let Some((i, ch)) = chars.next() {
        if ch == '`' {
            // Find closing backtick
            if let Some(close_pos) = text[i + 1..].find('`') {
                let close = i + 1 + close_pos;
                result.push_str(start);
                result.push_str(&text[i..=close]);
                result.push_str(end);
                // Advance past the closing backtick
                while chars.peek().is_some_and(|&(j, _)| j <= close) {
                    chars.next();
                }
            } else {
                result.push(ch);
            }
        } else {
            result.push(ch);
        }
    }
    result
}
