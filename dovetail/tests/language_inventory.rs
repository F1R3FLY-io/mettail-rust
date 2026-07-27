use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Requirement {
    Equation,
    DirectionalRewrite,
    CongruencePremise,
    FoldNativeHandler,
    FreshnessPremise,
    EnvRelationPremise,
    BehavioralGuard,
    SyntheticInjectionGuard,
    CollectionPattern,
    MapPattern,
    ZipPattern,
    BinderPattern,
    SubstitutionPattern,
    RhoCommHandlerContract,
    RhoResourceGuardContract,
}

#[derive(Debug)]
struct DiscoveredLanguage {
    rocq_name: String,
    source_path: PathBuf,
    requirements: BTreeSet<Requirement>,
    /// `options { parse_only: true }` — a syntax/lex-only fixture excluded from
    /// the production LanguageDefInventory (see `declared_parse_only`).
    parse_only: bool,
    /// Whether the source declares any reduction semantics — the anti-loophole
    /// guard: a `parse_only` language must have none (see `has_reduction_semantics`).
    has_reduction: bool,
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("dovetail crate has workspace parent")
        .to_path_buf()
}

fn read_repo_file(relative: &str) -> String {
    let path = repo_root().join(relative);
    fs::read_to_string(&path).unwrap_or_else(|err| panic!("failed to read {path:?}: {err}"))
}

fn repo_relative(path: &Path) -> String {
    path.strip_prefix(repo_root())
        .unwrap_or(path)
        .to_string_lossy()
        .replace('\\', "/")
}

// ══════════════════════════════════════════════════════════════════════════════
// Quotation vs. declaration
// ══════════════════════════════════════════════════════════════════════════════

/// `source` with every comment and string literal blanked out — the DECLARATIONS
/// only, with line and column structure preserved.
///
/// # Why this file cannot scan raw source
///
/// Every scanner below looks for a short needle. A needle is evidence of a
/// declaration only where a declaration can occur, and three places in a Rust file
/// look exactly like the DSL without being it:
///
/// | quotation | needle it hit | requirement wrongly reported |
/// |---|---|---|
/// | `//! # Clause-by-clause containment` (a markdown heading) | `"# "` | `ReqFreshnessPremise` |
/// | `//! \| omnibus clause \| our clause \|` (a markdown table row) | `"\| "` | `ReqCongruencePremise` |
/// | ``//! `rhocalc.rs` `POutput` idiom`` (prose quoting another language) | `"POutput"` | `ReqRhoCommHandlerContract` |
///
/// Those are not hypotheticals: they were measured on `json`, `monoid`, and `turing`,
/// which were each told they declare a freshness premise they do not have. The
/// direction is harmless for the coverage theorems — over-approximating the
/// requirement set cannot cause a requirement to be MISSED — but it is wrong as
/// documentation, and a reader has no way to tell a reported requirement from a
/// quoted one.
///
/// # What is removed
///
/// Line comments (`//`, `///`, `//!`) to end of line; block comments (`/* … */`,
/// nested as Rust allows); string literals including raw (`r"…"`, `r#"…"#`) and byte
/// (`b"…"`, `br#"…"#`) forms; and character literals. A `'` that does not open a
/// well-formed character literal is left alone, so lifetimes (`&'static str`) survive
/// intact rather than swallowing the rest of the file.
///
/// Removed text becomes spaces, and newlines are kept, so line-oriented scans see the
/// same line numbering as the file on disk.
fn declarations_only(source: &str) -> String {
    let chars: Vec<char> = source.chars().collect();
    let mut out = String::with_capacity(source.len());
    let mut index = 0usize;

    /// Blank one character, keeping newlines so line structure survives.
    fn blank(out: &mut String, ch: char) {
        out.push(if ch == '\n' { '\n' } else { ' ' });
    }

    /// The raw/byte string prefix at `start` (`r`, `b`, `br`) with its hash count,
    /// or `None` when this is an ordinary identifier rather than a literal prefix.
    fn raw_prefix(chars: &[char], start: usize) -> Option<(usize, usize)> {
        let mut at = start;
        let mut saw_raw = false;
        if chars.get(at) == Some(&'b') {
            at += 1;
        }
        if chars.get(at) == Some(&'r') {
            at += 1;
            saw_raw = true;
        }
        if !saw_raw {
            return None;
        }
        let hashes = chars[at..].iter().take_while(|ch| **ch == '#').count();
        (chars.get(at + hashes) == Some(&'"')).then_some((at + hashes + 1 - start, hashes))
    }

    while index < chars.len() {
        let ch = chars[index];
        let previous = index.checked_sub(1).map(|at| chars[at]);
        let continues_identifier = previous.is_some_and(|ch| ch.is_alphanumeric() || ch == '_');

        match ch {
            // ── line comment ──
            '/' if chars.get(index + 1) == Some(&'/') => {
                while index < chars.len() && chars[index] != '\n' {
                    blank(&mut out, chars[index]);
                    index += 1;
                }
            },
            // ── block comment (nested, as Rust allows) ──
            '/' if chars.get(index + 1) == Some(&'*') => {
                let mut depth = 1usize;
                out.push_str("  ");
                index += 2;
                while index < chars.len() && depth > 0 {
                    if chars[index] == '/' && chars.get(index + 1) == Some(&'*') {
                        depth += 1;
                        out.push_str("  ");
                        index += 2;
                    } else if chars[index] == '*' && chars.get(index + 1) == Some(&'/') {
                        depth -= 1;
                        out.push_str("  ");
                        index += 2;
                    } else {
                        blank(&mut out, chars[index]);
                        index += 1;
                    }
                }
            },
            // ── raw / byte string literal ──
            'r' | 'b' if !continues_identifier && raw_prefix(&chars, index).is_some() => {
                let (opener, hashes) = raw_prefix(&chars, index).expect("checked by the guard");
                for _ in 0..opener {
                    out.push(' ');
                }
                index += opener;
                loop {
                    let closes = chars.get(index) == Some(&'"')
                        && chars[index + 1..]
                            .iter()
                            .take(hashes)
                            .filter(|ch| **ch == '#')
                            .count()
                            == hashes;
                    if index >= chars.len() || closes {
                        break;
                    }
                    blank(&mut out, chars[index]);
                    index += 1;
                }
                for _ in 0..(hashes + 1).min(chars.len().saturating_sub(index)) {
                    out.push(' ');
                    index += 1;
                }
            },
            // ── ordinary (or byte) string literal ──
            'b' if !continues_identifier && chars.get(index + 1) == Some(&'"') => {
                out.push_str("  ");
                index += 2;
                index = blank_string_body(&mut out, &chars, index);
            },
            '"' => {
                out.push(' ');
                index += 1;
                index = blank_string_body(&mut out, &chars, index);
            },
            // ── character literal, but NOT a lifetime ──
            '\'' => match character_literal_len(&chars, index) {
                Some(len) => {
                    for _ in 0..len {
                        out.push(' ');
                    }
                    index += len;
                },
                None => {
                    out.push(ch);
                    index += 1;
                },
            },
            _ => {
                out.push(ch);
                index += 1;
            },
        }
    }

    out
}

/// Blank a string literal body starting at `index`, returning the index past its
/// closing quote. `\`-escapes are consumed as a unit so `"\""` does not end early.
fn blank_string_body(out: &mut String, chars: &[char], mut index: usize) -> usize {
    while index < chars.len() {
        match chars[index] {
            '\\' => {
                out.push_str("  ");
                index += 2;
            },
            '"' => {
                out.push(' ');
                index += 1;
                return index;
            },
            ch => {
                out.push(if ch == '\n' { '\n' } else { ' ' });
                index += 1;
            },
        }
    }
    index
}

/// The length of the character literal opening at `index`, or `None` when the quote
/// opens a lifetime (`'static`, `'a`) instead.
fn character_literal_len(chars: &[char], index: usize) -> Option<usize> {
    match chars.get(index + 1)? {
        '\\' => {
            // `'\n'`, `'\''`, `'\u{1F600}'` — scan to the closing quote.
            let close = chars[index + 2..]
                .iter()
                .take(12)
                .position(|ch| *ch == '\'')?;
            Some(index + 2 + close + 1 - index)
        },
        _ if chars.get(index + 2) == Some(&'\'') => Some(3),
        _ => None,
    }
}

fn is_language_macro_source(source: &str) -> bool {
    source
        .lines()
        .any(|line| line.trim_start().starts_with("language!"))
}

fn declared_language_names(source: &str) -> Vec<String> {
    let mut waiting_for_name = false;
    let mut names = Vec::new();
    for line in source.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("language!") {
            waiting_for_name = true;
            continue;
        }
        if !waiting_for_name {
            continue;
        }
        let Some(rest) = trimmed.strip_prefix("name:") else {
            continue;
        };
        if let Some(name) = rest
            .trim()
            .trim_end_matches(',')
            .split(|ch: char| ch.is_whitespace() || ch == ',')
            .next()
            .filter(|name| !name.is_empty())
        {
            names.push(name.to_owned());
            waiting_for_name = false;
        }
    }
    names
}

/// Whether the `language!` source declares `options { parse_only: true }`.
fn declared_parse_only(source: &str) -> bool {
    source.lines().any(|line| {
        line.trim()
            .strip_prefix("parse_only:")
            .map(|rest| rest.trim().trim_end_matches(',').trim() == "true")
            .unwrap_or(false)
    })
}

/// Textual detection of reduction semantics — the dovetail-side mirror of the AST
/// test's structural guard. A `parse_only` language must have NONE: no non-empty
/// `equations`/`rewrites`/`logic`/`guards` block. Empty `equations {}`/`rewrites {}`
/// (which some thin smoke languages carry) do NOT count, matching the AST side's
/// `!def.equations.is_empty()`.
fn has_reduction_semantics(source: &str) -> bool {
    nonempty_block(source, "equations")
        || nonempty_block(source, "rewrites")
        || nonempty_block(source, "logic")
        || nonempty_block(source, "guards")
}

/// Whether `source` contains a `<name> { … }` block with any non-blank,
/// non-comment content between its braces (whitespace-tolerant).
fn nonempty_block(source: &str, name: &str) -> bool {
    let inline_open = format!("{name} {{");
    let inline_open_tight = format!("{name}{{");
    let mut lines = source.lines();
    while let Some(line) = lines.next() {
        let trimmed = line.trim();
        let is_open = trimmed == name
            || trimmed.starts_with(&inline_open)
            || trimmed.starts_with(&inline_open_tight);
        if !is_open {
            continue;
        }
        // Inline form: `equations { <maybe content> }` on one line (possibly with
        // a trailing comma). Content is strictly between the braces.
        if let Some(open_idx) = trimmed.find('{') {
            let after = &trimmed[open_idx + 1..];
            if let Some(close_idx) = after.find('}') {
                if after[..close_idx].trim().is_empty() {
                    continue; // inline empty block `{}`
                }
                return true; // inline non-empty block
            }
        }
        // Multi-line: the first meaningful line is not the closing brace.
        for next in lines.by_ref() {
            let nt = next.trim();
            if nt.is_empty() || nt.starts_with("//") {
                continue;
            }
            return !nt.starts_with('}');
        }
    }
    false
}

fn rocq_inventory_names(source: &str) -> BTreeSet<String> {
    let marker = "inventory_name := \"";
    source
        .lines()
        .filter_map(|line| {
            let start = line.find(marker)? + marker.len();
            let rest = &line[start..];
            let end = rest.find('"')?;
            Some(rest[..end].to_owned())
        })
        .collect()
}

fn rocq_current_requirement_names(source: &str) -> BTreeSet<String> {
    let marker = "Definition current_mettail_rewrite_requirements";
    let start = source
        .find(marker)
        .unwrap_or_else(|| panic!("Rocq coverage file missing `{marker}`"));
    let list_source = &source[start..];
    let open = list_source
        .find('[')
        .unwrap_or_else(|| panic!("Rocq current requirement list has no opening `[`"));
    let close = list_source[open..]
        .find(']')
        .unwrap_or_else(|| panic!("Rocq current requirement list has no closing `]`"));

    list_source[open + 1..open + close]
        .split(|ch: char| ch == ';' || ch.is_whitespace())
        .filter(|token| token.starts_with("Req"))
        .map(ToOwned::to_owned)
        .collect()
}

fn discover_rust_files(root: &Path) -> Vec<PathBuf> {
    let mut pending = vec![root.to_path_buf()];
    let mut files = Vec::new();
    while let Some(path) = pending.pop() {
        let metadata =
            fs::metadata(&path).unwrap_or_else(|err| panic!("failed to stat {path:?}: {err}"));
        if metadata.is_dir() {
            let name = path
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or("");
            if matches!(name, "bin" | "generated") {
                continue;
            }
            for entry in fs::read_dir(&path)
                .unwrap_or_else(|err| panic!("failed to read directory {path:?}: {err}"))
            {
                pending.push(entry.expect("source directory entry").path());
            }
        } else if path.extension().and_then(|ext| ext.to_str()) == Some("rs") {
            files.push(path);
        }
    }
    files.sort();
    files
}

/// Every directory that may hold a `language!` definition.
///
/// Task #11 split language definitions by role: `languages/src/` holds PRODUCTION
/// languages (they are library modules), and `languages/tests/definitions/` holds
/// TEST definitions (declared `options { hosted_in: … }`, reachable only by the test
/// binaries that `#[path]`-include them).
///
/// BOTH are scanned, and that is load-bearing. This inventory's whole purpose is that
/// every `language!` in the repo carries a formal requirements entry — the `parse_only`
/// anti-loophole guard below says so outright: "a real reduction language cannot hide
/// behind the flag to escape the formal rewrite inventory". If relocation dropped a
/// definition from discovery, MOVING A FILE would become exactly that escape hatch, and
/// a language's reduction semantics could leave formal inventory without any test
/// failing. Scanning both directories keeps the guard total: where a definition lives is
/// a packaging decision, never a formal-coverage decision.
fn language_definition_roots() -> Vec<std::path::PathBuf> {
    vec![
        repo_root().join("languages/src"),
        repo_root().join("languages/tests/definitions"),
    ]
}

fn discover_language_sources() -> Vec<DiscoveredLanguage> {
    language_definition_roots()
        .iter()
        .filter(|root| root.exists())
        .flat_map(|root| discover_rust_files(root))
        .collect::<Vec<_>>()
        .into_iter()
        .flat_map(|path| {
            let raw = fs::read_to_string(&path)
                .unwrap_or_else(|err| panic!("failed to read {path:?}: {err}"));
            // Every scan below reads DECLARATIONS, never quotations: a `language!`
            // named in prose is not a definition, a `parse_only: true` inside a
            // comment must not exclude a language from the inventory, and a needle
            // in a markdown table is not a premise.
            let source = declarations_only(&raw);
            if !is_language_macro_source(&source) {
                return Vec::new();
            }
            let display_names = declared_language_names(&source);
            assert!(
                !display_names.is_empty(),
                "{} contains a language! macro without a `name:` declaration",
                repo_relative(&path)
            );
            let requirements = classify_source(&source);
            let parse_only = declared_parse_only(&source);
            let has_reduction = has_reduction_semantics(&source);
            display_names
                .into_iter()
                .map(|display_name| DiscoveredLanguage {
                    rocq_name: display_name.to_ascii_lowercase(),
                    source_path: path.clone(),
                    requirements: requirements.clone(),
                    parse_only,
                    has_reduction,
                })
                .collect::<Vec<_>>()
        })
        .collect()
}

/// Whether some rule declares a REWRITE PREMISE — `Label . | S ~> T |- …`.
///
/// The DSL puts a rule's premises between the label's `.` and the turnstile `|-`, so
/// a congruence premise is a `~>` on the premise side of a statement. The previous
/// test — "the file contains `| ` somewhere AND `~>` somewhere" — is satisfied by any
/// rewriting language that also contains a pipe for any reason, and two such reasons
/// occur in this corpus: a markdown table row in a doc comment, and a Rust closure
/// (`map_err(|_| ())`) inside a native action. Turing has both, no congruence rule,
/// and was reported with one.
///
/// Statements are `;`-separated. Splitting there cannot manufacture a premise: it can
/// only cut a statement into smaller pieces, and a piece claims a congruence premise
/// only if a `~>` and a following `|-` survive together inside it.
fn declares_congruence_premise(code: &str) -> bool {
    code.split(';').any(|statement| match statement.find("|-") {
        Some(turnstile) => statement[..turnstile].contains("~>"),
        None => false,
    })
}

/// Whether some rule declares a GUARD SLOT — `?<name>:Guard` in a term context.
///
/// The previous test also accepted the bare word `where` surrounded by spaces, which
/// matches English prose: five demo languages were reported with a behavioral guard
/// because their header comments contain the phrase "where the installed …". Worse,
/// it did not match the guard that `GuardOptSmoke` actually declares — `?g:Guard`,
/// whose slot name is not the literal `guard` — so that language's only route to its
/// REAL requirement was a doc comment. Matching the slot shape covers every spelling
/// of the name and reads no prose.
fn declares_guard_slot(code: &str) -> bool {
    code.match_indices('?').any(|(at, _)| {
        let rest = &code[at + 1..];
        let name = rest
            .find(|ch: char| !(ch.is_ascii_alphanumeric() || ch == '_'))
            .unwrap_or(rest.len());
        if name == 0 {
            return false;
        }
        rest[name..]
            .trim_start()
            .strip_prefix(':')
            .is_some_and(|typed| typed.trim_start().starts_with("Guard"))
    })
}

/// Classify a `language!` source by the Dovetail rewrite requirements it declares.
///
/// `source` must already have been through [`declarations_only`]: every needle here
/// is evidence of a declaration, and none of them can tell prose from code by itself.
fn classify_source(source: &str) -> BTreeSet<Requirement> {
    let mut reqs = BTreeSet::new();
    if source
        .lines()
        .any(|line| line.contains("|-") && line.contains(" = "))
    {
        reqs.insert(Requirement::Equation);
    }
    if source.contains("~>") || source.contains("extends: [BaseMath]") {
        reqs.insert(Requirement::DirectionalRewrite);
    }
    if declares_congruence_premise(source) || source.contains("extends: [BaseMath]") {
        reqs.insert(Requirement::CongruencePremise);
    }
    if source.contains("] fold")
        || source.contains("] step")
        || source.contains("extends: [BaseMath]")
    {
        reqs.insert(Requirement::FoldNativeHandler);
    }
    if source.contains("# ") {
        reqs.insert(Requirement::FreshnessPremise);
    }
    if source.contains("logic {") || source.contains("relation ") || source.contains(" = { x:") {
        reqs.insert(Requirement::EnvRelationPremise);
    }
    if declares_guard_slot(source) || source.contains("guards {") {
        reqs.insert(Requirement::BehavioralGuard);
        reqs.insert(Requirement::SyntheticInjectionGuard);
    }
    if source.contains("HashBag(")
        || source.contains("Vec(")
        || source.contains("Vec<")
        || source.contains("...rest")
        || source.contains("*opt(")
        || source.contains(".*sep")
    {
        reqs.insert(Requirement::CollectionPattern);
    }
    if source.contains("HashMap<") || source.contains("HashMap(") || source.contains(":Map") {
        reqs.insert(Requirement::MapPattern);
    }
    if source.contains("*zip(") {
        reqs.insert(Requirement::ZipPattern);
    }
    if source.contains('^') && source.contains("->") {
        reqs.insert(Requirement::BinderPattern);
    }
    if source.contains("eval ") || source.contains("eval(") {
        reqs.insert(Requirement::SubstitutionPattern);
    }
    if source.contains("PInputs") || source.contains("POutput") || source.contains("PGuardedInput")
    {
        reqs.insert(Requirement::RhoCommHandlerContract);
    }
    if source.contains("guards {") {
        reqs.insert(Requirement::RhoResourceGuardContract);
    }
    reqs
}

// ══════════════════════════════════════════════════════════════════════════════
// Guards for the quotation/declaration boundary
// ══════════════════════════════════════════════════════════════════════════════

/// The classification pipeline as `discover_language_sources` runs it.
fn classify(raw: &str) -> BTreeSet<Requirement> {
    classify_source(&declarations_only(raw))
}

/// Every requirement of the taxonomy, DECLARED — so the scan cannot pass by seeing
/// nothing.
///
/// This is the half that matters most. Removing quotations narrows the classifier,
/// and a classifier that narrows too far drops formal coverage SILENTLY: the
/// inventory test only asserts that each production language classifies something and
/// that the aggregate is a subset of the Rocq requirement list, both of which a
/// too-small set satisfies. So every needle is exercised in the position the DSL
/// actually puts it.
const DECLARES_EVERY_REQUIREMENT: &str = r##"
language! {
    name: EveryRequirement,

    types {
        Proc
        Name
        ![Vec<Proc>] as List
        ![HashMap<Proc, Proc>] as Map
    },

    terms {
        PZero . |- "Nil" : Proc ;
        POutput . n:Name, p:Proc |- n "!" "(" p ")" : Proc ;
        PFor . n:Name, ^x.p:[Name -> Proc] |- "for" "(" x "<-" n ")" p : Proc ;
        PPar . ps:HashBag(Proc) |- ps.*sep("|") : Proc ;
        PZip . ns:Vec(Name), xs:Vec(Proc) |- *zip(ns,xs) : Proc ;
        PMap . m:Map |- "{" m "}" : Proc ;
        PCheck . k:Proc, ?g:Guard |- "check" "(" k g ")" : Proc ;
        AddNum . a:Proc, b:Proc |- a "+" b : Proc ![a + b] fold ;
    },

    equations {
        ParUnit . |- (PPar {P, PZero}) = P ;
        ScopeExt . | x # ...rest |- (PNew ^x.P) = (PNew ^x.P) ;
    },

    rewrites {
        Comm . |- (PPar {(PFor N cont), (POutput N Q), ...rest})
             ~> (PPar {(eval cont Q), ...rest}) ;
        ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest}) ;
    },

    logic {
        relation ok(Proc);
    },

    guards {
        channels { PCheck(ch: Name) }
    },
}
"##;

/// The same needles, QUOTED — and nothing is reported.
///
/// Each line below is a real shape from this repository's language sources: markdown
/// headings and tables in module documentation, prose naming another language's rule
/// labels, a commented-out rewrite, and DSL terminals that happen to be pipes.
const QUOTES_EVERY_REQUIREMENT: &str = r##"
//! # Clause-by-clause containment
//!
//! | omnibus clause | our clause | delta |
//! | --- | --- | --- |
//! | `Mul . x:M, y:M \|- x "*" y : M ;` | identical | — |
//!
//! Follows the `rhocalc.rs` `POutput` / `PInputs` / `PGuardedInput` idiom, where the
//! carrier is a `Vec(T)` slot. The paper writes `x # ...rest` for freshness and
//! `S ~> T` for a step; substitution is spelled `eval`, e.g. `(eval cont Q)`, and a
//! `?g:Guard` slot would sit in the term context. See `logic { relation ok(Proc); }`
//! and `guards { channels }`, plus `*zip(ns,xs)`, `HashBag(Proc)`, `:Map`, `] fold`,
//! `^x.p:[Name -> Proc]`, and an equation `|- (Mul X Y) = (Mul Y X)`.
/*
    ParCong . | S ~> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest}) ;
    logic { relation ok(Proc); }
*/
language! {
    name: QuotesOnly,
    types { Sym Tape },
    terms {
        // A tape whose delimiters are pipes: terminals, not premise bars.
        Tp . h:Sym |- "<" "|" h "|" ">" : Tape ;
    },
}
"##;

/// Quoted needles are not declarations.
#[test]
fn quotation_declares_nothing() {
    let quoted = classify(QUOTES_EVERY_REQUIREMENT);
    assert!(
        quoted.is_empty(),
        "a file that only TALKS about these constructs declares none of them, got {:?}",
        quoted
            .iter()
            .map(|req| rocq_requirement_name(*req))
            .collect::<Vec<_>>()
    );

    // And the scan is not passing by reading an empty string: the same text with its
    // quoting removed is exactly what the declaring fixture reports.
    assert!(
        !classify(DECLARES_EVERY_REQUIREMENT).is_empty(),
        "the declaring fixture must be non-empty or this test proves nothing"
    );
}

/// Declared needles are reported — every one of them.
#[test]
fn declaration_reports_every_requirement() {
    let declared = classify(DECLARES_EVERY_REQUIREMENT);
    let missing = [
        Requirement::Equation,
        Requirement::DirectionalRewrite,
        Requirement::CongruencePremise,
        Requirement::FoldNativeHandler,
        Requirement::FreshnessPremise,
        Requirement::EnvRelationPremise,
        Requirement::BehavioralGuard,
        Requirement::SyntheticInjectionGuard,
        Requirement::CollectionPattern,
        Requirement::MapPattern,
        Requirement::ZipPattern,
        Requirement::BinderPattern,
        Requirement::SubstitutionPattern,
        Requirement::RhoCommHandlerContract,
        Requirement::RhoResourceGuardContract,
    ]
    .into_iter()
    .filter(|req| !declared.contains(req))
    .map(rocq_requirement_name)
    .collect::<Vec<_>>();

    assert!(
        missing.is_empty(),
        "the classifier stopped seeing declarations it must see: {missing:?}"
    );
}

/// The guard slot is matched by SHAPE, so every spelling of its name is seen.
#[test]
fn guard_slot_is_matched_by_shape_not_by_name() {
    assert!(
        declares_guard_slot("PCheck . k:Int, *opt(?g:Guard)"),
        "the corpus spells it `?g`"
    );
    assert!(declares_guard_slot("PGuardedInput . n:Name, ?guard:Guard, ^x.p:[Name -> Proc]"));
    assert!(declares_guard_slot("Wrapped . ?the_guard : Guard"), "whitespace-tolerant");
    // Prose, and a `?` that opens no slot.
    assert!(!declares_guard_slot("where the installed receiver binds it"));
    assert!(!declares_guard_slot("is it a guard? Guard is the type."));
    assert!(!declares_guard_slot("k:Int, ?g:Int"));
}

/// A congruence premise is a rewrite ON THE PREMISE SIDE of a rule.
#[test]
fn congruence_premise_is_matched_on_the_premise_side() {
    assert!(declares_congruence_premise("ParCong . | S ~> T |- (PPar {S}) ~> (PPar {T}) ;"));
    assert!(
        declares_congruence_premise("WrapCong . | S ~> T\n    |- (Wrap S) ~> (Wrap T) ;"),
        "the premise may sit on its own line"
    );
    // A rewrite with no premise: the `~>` is on the conclusion side only.
    assert!(!declares_congruence_premise("D_q0_0 . |- (Cf Q0 (Tp L Zero R)) ~> (Cf Q1 R) ;"));
    // A Rust closure inside a native action, next to an unrelated rewrite rule.
    assert!(!declares_congruence_premise(
        "eval: ![ { parse_int_lit(text).map_err(|_| ()) } ] ;\n D . |- (A) ~> (B) ;"
    ));
}

/// The stripper keeps declarations and drops quotations, with line structure intact.
#[test]
fn declarations_only_removes_exactly_the_quotations() {
    let stripped = declarations_only(
        "//! # heading\n\
         let s = \"# in a string\";\n\
         /* # in a block /* nested */ comment */\n\
         ScopeExt . | x # ...rest |- (PNew ^x.P) = (PNew ^x.P) ;\n\
         let c = '#';\n\
         fn f<'a>(x: &'a str) -> &'a str { x }\n",
    );

    assert_eq!(
        stripped.lines().count(),
        6,
        "line structure must survive so line-oriented scans keep their numbering"
    );
    assert!(stripped.contains("ScopeExt . | x # ...rest |-"), "the declaration survives");
    assert!(!stripped.contains("heading"), "doc comment removed");
    assert!(!stripped.contains("in a string"), "string literal removed");
    assert!(!stripped.contains("nested"), "nested block comment removed");
    assert_eq!(stripped.matches("# ").count(), 1, "one freshness premise, in code");
    assert!(
        stripped.contains("fn f<'a>(x: &'a str) -> &'a str"),
        "a lifetime is not a character literal and must not swallow the file"
    );

    // Raw and byte strings, which the corpus uses for token patterns.
    let raw = declarations_only("pattern: r\"(0b[01]|0o[0-7])\"; keep_me: 1");
    assert!(!raw.contains("0b[01]"), "raw string removed");
    assert!(raw.contains("keep_me: 1"), "code after a raw string survives");
    let hashed = declarations_only("p: r#\"a \"quoted\" b\"#; keep_me: 2");
    assert!(!hashed.contains("quoted"), "hashed raw string removed");
    assert!(hashed.contains("keep_me: 2"), "code after a hashed raw string survives");
    let bytes = declarations_only("b: b\"# bytes\"; keep_me: 3");
    assert!(!bytes.contains("bytes"), "byte string removed");
    assert!(bytes.contains("keep_me: 3"));
}

/// The measured false positives, pinned on the real corpus — with the true positives
/// they sat next to.
///
/// `json`, `monoid`, and `turing` were each reported with a freshness premise because
/// their headers open with markdown `#` headings; `turing` with a congruence premise
/// because its header renders a markdown table; `json` with a Rho COMM handler
/// contract because its header quotes another language's `POutput` idiom. `pi` was
/// reported with a freshness premise TOO — and that one is real (`| x # ...rest` in
/// its `ScopeExt` equation), which is why the fix cannot be "stop looking for `#`".
#[test]
fn requirements_are_not_inherited_from_prose() {
    let discovered = discover_language_sources();
    let requirements = |name: &str| {
        discovered
            .iter()
            .find(|language| language.rocq_name == name)
            .unwrap_or_else(|| panic!("`{name}` must be discovered by the inventory scan"))
            .requirements
            .clone()
    };

    for (name, absent) in [
        ("json", Requirement::FreshnessPremise),
        ("json", Requirement::RhoCommHandlerContract),
        ("json", Requirement::SubstitutionPattern),
        ("monoid", Requirement::FreshnessPremise),
        ("turing", Requirement::FreshnessPremise),
        ("turing", Requirement::CongruencePremise),
    ] {
        assert!(
            !requirements(name).contains(&absent),
            "`{name}` does not declare {} — it only mentions it in prose",
            rocq_requirement_name(absent)
        );
    }

    for (name, present) in [
        ("pi", Requirement::FreshnessPremise),
        ("pi", Requirement::CongruencePremise),
        ("turing", Requirement::DirectionalRewrite),
        ("turing", Requirement::FoldNativeHandler),
        ("json", Requirement::CollectionPattern),
        ("monoid", Requirement::Equation),
        ("guardoptsmoke", Requirement::BehavioralGuard),
    ] {
        assert!(
            requirements(name).contains(&present),
            "`{name}` DOES declare {} and must keep it",
            rocq_requirement_name(present)
        );
    }
}

fn relation_head(line: &str) -> Option<&str> {
    let line = line.trim();
    if !line.contains("<--") {
        return None;
    }
    let open = line.find('(')?;
    let head = line[..open].trim();
    (!head.is_empty()
        && head
            .chars()
            .all(|ch| ch.is_ascii_alphanumeric() || ch == '_'))
    .then_some(head)
}

fn declared_relation_head(line: &str) -> Option<&str> {
    let line = line.trim();
    let marker = "relation ";
    let marker_start = line.find(marker)?;
    let after_marker = &line[marker_start + marker.len()..];
    let open = after_marker.find('(')?;
    let head = after_marker[..open].trim();
    (!head.is_empty()
        && head
            .chars()
            .all(|ch| ch.is_ascii_alphanumeric() || ch == '_'))
    .then_some(head)
}

#[derive(Debug)]
struct RelationDecl {
    head: String,
    params: Vec<String>,
}

fn declared_relation(line: &str) -> Option<RelationDecl> {
    let line = line.trim();
    let marker = "relation ";
    let marker_start = line.find(marker)?;
    let after_marker = &line[marker_start + marker.len()..];
    let open = after_marker.find('(')?;
    let close = after_marker[open + 1..].find(')')? + open + 1;
    let head = after_marker[..open].trim();
    if head.is_empty()
        || !head
            .chars()
            .all(|ch| ch.is_ascii_alphanumeric() || ch == '_')
    {
        return None;
    }

    let params = split_relation_params(&after_marker[open + 1..close]);
    Some(RelationDecl { head: head.to_owned(), params })
}

fn split_relation_params(params: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut start = 0usize;
    let mut angle_depth = 0usize;

    for (idx, ch) in params.char_indices() {
        match ch {
            '<' => angle_depth += 1,
            '>' => angle_depth = angle_depth.saturating_sub(1),
            ',' if angle_depth == 0 => {
                let param = params[start..idx].trim();
                if !param.is_empty() {
                    out.push(param.to_owned());
                }
                start = idx + ch.len_utf8();
            },
            _ => {},
        }
    }

    let param = params[start..].trim();
    if !param.is_empty() {
        out.push(param.to_owned());
    }
    out
}

fn is_generated_category_relation(decl: &RelationDecl) -> bool {
    let [payload_type] = decl.params.as_slice() else {
        return false;
    };
    decl.head == payload_type.to_ascii_lowercase()
}

fn category_relation_heads_from_datalog(source: &str) -> BTreeSet<String> {
    let relation_prelude = source.split("// Category rules").next().unwrap_or(source);
    relation_prelude
        .lines()
        .filter_map(declared_relation)
        .filter(is_generated_category_relation)
        .map(|decl| decl.head)
        .collect()
}

fn generated_category_heads(source: &str) -> BTreeSet<String> {
    let mut in_category_info = false;
    let mut brace_depth = 0usize;
    let mut heads = BTreeSet::new();

    for line in source.lines() {
        if !in_category_info {
            if line.contains("export const categoryInfo = {") {
                in_category_info = true;
                brace_depth = 1;
            }
            continue;
        }

        let trimmed = line.trim();
        if brace_depth == 1 && trimmed.ends_with('{') {
            if let Some((head, _)) = trimmed.split_once(':') {
                let head = head.trim().trim_matches('"').trim_matches('\'');
                if !head.is_empty() {
                    heads.insert(head.to_ascii_lowercase());
                }
            }
        }

        for ch in line.chars() {
            match ch {
                '{' => brace_depth += 1,
                '}' => brace_depth = brace_depth.saturating_sub(1),
                _ => {},
            }
        }
        if brace_depth == 0 {
            break;
        }
    }

    heads
}

fn classify_datalog_head(head: &str) -> Option<Requirement> {
    if head.starts_with("rw_") {
        Some(Requirement::DirectionalRewrite)
    } else if head.starts_with("fold_") {
        Some(Requirement::FoldNativeHandler)
    } else if head.starts_with("eq_") {
        Some(Requirement::Equation)
    } else if head.ends_with("_contains") || head.ends_with("_vec") {
        Some(Requirement::CollectionPattern)
    } else {
        None
    }
}

#[test]
fn generated_category_heads_are_derived_from_relation_signatures() {
    let source = r#"
        ascent_source! {
            sample_source:

            // Relations
            relation proc(Proc);
            #[ds(crate::eqrel)] relation eq_proc(Proc, Proc);
            #[ds(crate::dual_indexed)] relation rw_proc(Proc, Proc);
            relation name(Name);
            relation step_term(Proc);
            #[ds(crate::dual_indexed)] relation ppar_contains(Proc, Proc);

            // Category rules
            proc(t) <-- proc(t);
        }
    "#;

    assert_eq!(
        category_relation_heads_from_datalog(source),
        BTreeSet::from(["name".to_owned(), "proc".to_owned()])
    );
}

fn rocq_requirement_name(requirement: Requirement) -> &'static str {
    match requirement {
        Requirement::Equation => "ReqEquation",
        Requirement::DirectionalRewrite => "ReqDirectionalRewrite",
        Requirement::CongruencePremise => "ReqCongruencePremise",
        Requirement::FoldNativeHandler => "ReqFoldNativeHandler",
        Requirement::FreshnessPremise => "ReqFreshnessPremise",
        Requirement::EnvRelationPremise => "ReqEnvRelationPremise",
        Requirement::BehavioralGuard => "ReqBehavioralGuard",
        Requirement::SyntheticInjectionGuard => "ReqSyntheticInjectionGuard",
        Requirement::CollectionPattern => "ReqCollectionPattern",
        Requirement::MapPattern => "ReqMapPattern",
        Requirement::ZipPattern => "ReqZipPattern",
        Requirement::BinderPattern => "ReqBinderPattern",
        Requirement::SubstitutionPattern => "ReqSubstitutionPattern",
        Requirement::RhoCommHandlerContract => "ReqRhoCommHandlerContract",
        Requirement::RhoResourceGuardContract => "ReqRhoResourceGuardContract",
    }
}

#[test]
fn source_language_inventory_matches_rocq_inventory_and_taxonomy() {
    let rocq_inventory =
        read_repo_file("dovetail/formal/rocq/theories/Requirements/LanguageDefInventory.v");
    let rocq_names = rocq_inventory_names(&rocq_inventory);
    let discovered_languages = discover_language_sources();
    assert!(
        !discovered_languages.is_empty(),
        "no in-repo language! macro sources discovered"
    );

    // Anti-loophole guard: a parse_only language must declare NO reduction
    // semantics, else fail loudly — a real reduction language cannot hide behind
    // the flag to escape the formal rewrite inventory.
    for language in &discovered_languages {
        if language.parse_only {
            assert!(
                !language.has_reduction,
                "{} is marked `parse_only: true` but declares reduction semantics \
                 (equations/rewrites/logic/guards); parse_only is for syntax-only fixtures",
                repo_relative(&language.source_path)
            );
        }
    }

    // Parse-only fixtures (syntax/lex demonstrations that declare
    // `options { parse_only: true }`, e.g. the keyword-reservation FortranModel/
    // ReservedModel) are excluded from the production LanguageDefInventory.
    // Fail-closed: a language is inventoried unless it explicitly opts out.
    let production = discovered_languages
        .iter()
        .filter(|language| !language.parse_only)
        .collect::<Vec<_>>();

    let discovered_names = production
        .iter()
        .map(|language| language.rocq_name.clone())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        discovered_names, rocq_names,
        "Rocq LanguageDefInventory must exactly match discovered production language! sources"
    );

    let mut aggregate = BTreeSet::new();

    for language in &production {
        assert!(
            !language.requirements.is_empty(),
            "{} did not classify any Dovetail rewrite requirement",
            repo_relative(&language.source_path)
        );
        assert!(
            rocq_inventory.contains(&format!("inventory_name := \"{}\"", language.rocq_name)),
            "Rocq LanguageDefInventory is missing {}",
            language.rocq_name
        );
        aggregate.extend(language.requirements.iter().copied());
    }

    let formal_coverage =
        read_repo_file("dovetail/formal/rocq/theories/Requirements/MeTTaILRewriteCoverage.v");
    let formal_requirements = rocq_current_requirement_names(&formal_coverage);
    let aggregate_requirements = aggregate
        .iter()
        .map(|requirement| rocq_requirement_name(*requirement).to_owned())
        .collect::<BTreeSet<_>>();
    assert!(
        aggregate_requirements.is_subset(&formal_requirements),
        "source-classified LanguageDef requirements are not covered by Rocq current_mettail_rewrite_requirements: source={aggregate_requirements:?}, formal={formal_requirements:?}"
    );
}

#[test]
fn generated_datalog_relation_heads_are_requirement_classified() {
    let generated_dir = repo_root().join("languages/src/generated");
    let mut datalog_files = fs::read_dir(&generated_dir)
        .unwrap_or_else(|err| panic!("failed to read {generated_dir:?}: {err}"))
        .map(|entry| entry.expect("generated dir entry").path())
        .filter(|path| {
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.ends_with("-datalog.rs"))
        })
        .collect::<Vec<_>>();
    datalog_files.sort();
    assert!(!datalog_files.is_empty(), "no generated Datalog files found");

    let mut classified = BTreeSet::new();
    let mut unknown_heads = Vec::new();
    let mut category_metadata_pairs = 0usize;
    for path in datalog_files {
        let source = fs::read_to_string(&path)
            .unwrap_or_else(|err| panic!("failed to read {path:?}: {err}"));
        let declared_heads = source
            .lines()
            .filter_map(declared_relation_head)
            .collect::<BTreeSet<_>>();
        assert!(
            !declared_heads.is_empty(),
            "{} has no generated relation declarations to audit",
            path.display()
        );

        for head in &declared_heads {
            if let Some(req) = classify_datalog_head(head) {
                classified.insert(req);
            }
        }

        for head in source.lines().filter_map(relation_head) {
            if let Some(req) = classify_datalog_head(head) {
                classified.insert(req);
            } else if !declared_heads.contains(head) {
                unknown_heads.push(format!("{}:{head}", path.display()));
            }
        }

        let category_path = path.with_file_name(
            path.file_name()
                .and_then(|name| name.to_str())
                .expect("generated Datalog file name")
                .replace("-datalog.rs", "-categories.ts"),
        );
        if category_path.exists() {
            category_metadata_pairs += 1;
            let category_source = fs::read_to_string(&category_path)
                .unwrap_or_else(|err| panic!("failed to read {category_path:?}: {err}"));
            let category_heads = generated_category_heads(&category_source);
            assert!(
                !category_heads.is_empty(),
                "{} has no generated category metadata heads to audit",
                category_path.display()
            );
            let relation_category_heads = category_relation_heads_from_datalog(&source);
            assert_eq!(
                category_heads, relation_category_heads,
                "{} generated category metadata must exactly match generated Datalog category relations",
                path.display(),
            );
        }
    }

    assert!(
        category_metadata_pairs > 0,
        "no generated Datalog/category metadata pairs found"
    );
    assert!(
        unknown_heads.is_empty(),
        "unclassified generated Datalog relation heads: {unknown_heads:#?}"
    );
    assert!(
        !classified.is_empty(),
        "generated Datalog did not expose any classified relation families"
    );
    let formal_coverage =
        read_repo_file("dovetail/formal/rocq/theories/Requirements/MeTTaILRewriteCoverage.v");
    let formal_requirements = rocq_current_requirement_names(&formal_coverage);
    let classified_requirements = classified
        .iter()
        .map(|requirement| rocq_requirement_name(*requirement).to_owned())
        .collect::<BTreeSet<_>>();
    assert!(
        classified_requirements.is_subset(&formal_requirements),
        "generated Datalog relation families are not covered by Rocq current_mettail_rewrite_requirements: generated={classified_requirements:?}, formal={formal_requirements:?}"
    );
}
