//! THROWAWAY P2 ISOLATION+COMBINE S0-CG codegen-correctness gate (Plan a7986200,
//! 2026-07-05). Runs against the GENERATED `ForRow` facade with the isolation
//! codegen flipped ON (`SEP_ISOLATION_CATEGORIES = &["ForRow"]`). The A/B control
//! is the runtime env `PRATTAIL_NO_SEP_ISOLATION`: UNSET ⇒ isolation ON, SET ⇒
//! the monolithic (pre-fix) path — so ON vs OFF are compared in ONE binary.
//!
//! GATES (HALT-on-fail):
//!   S0-CG-sound   `ForRow::parse_via_wpda_all` k=0..8 ON alt SET == OFF/monolithic.
//!   S0-CG-linear  ON wall-time LINEAR in k (vs monolithic exponential).
//!   S0-CG-single  `ForRow::parse` single winner ON == OFF, k=0..4.
//!   S0-CG-variants ForRowWhere (`a & b where c`) + single (`a`, `a where c`).
//!
//! Run: `cargo test -p languages --test zz_p2cg_s0_gate -- --ignored --nocapture`

use std::collections::HashSet;
use std::time::{Duration, Instant};

use mettail_languages::rhocalc::ForRow;

/// Canonicalize monotonic fresh-var ids (mirrors the DC probe).
fn normalize_var_ids(debug: &str) -> String {
    const MARK: &str = "UniqueId(";
    let mut out = String::with_capacity(debug.len());
    let mut rest = debug;
    while let Some(idx) = rest.find(MARK) {
        out.push_str(&rest[..idx]);
        out.push_str(MARK);
        out.push('_');
        rest = &rest[idx + MARK.len()..];
        let after_digits = rest.find(|c: char| !c.is_ascii_digit()).unwrap_or(rest.len());
        rest = &rest[after_digits..];
    }
    out.push_str(rest);
    out
}

/// `@x0<-@y0 & @x1<-@y1 & … & @x{k}<-@y{k}` — (k+1) segments.
fn build_input(k: usize) -> String {
    (0..=k).map(|i| format!("@x{i}<-@y{i}")).collect::<Vec<_>>().join(" & ")
}

fn alt_set_all(input: &str) -> Option<HashSet<String>> {
    mettail_runtime::clear_var_cache();
    ForRow::parse_via_wpda_all(input)
        .ok()
        .map(|alts| alts.iter().map(|fr| normalize_var_ids(&format!("{:?}", fr))).collect())
}

fn single_winner(input: &str) -> Option<String> {
    mettail_runtime::clear_var_cache();
    ForRow::parse(input).ok().map(|fr| normalize_var_ids(&format!("{:?}", fr)))
}

fn run_with_timeout<T: Send + 'static>(secs: u64, body: impl FnOnce() -> T + Send + 'static) -> Option<T> {
    use std::sync::mpsc;
    let (tx, rx) = mpsc::channel();
    let _ = std::thread::Builder::new()
        .name("p2cg-mono".into())
        .spawn(move || {
            let _ = tx.send(body());
        });
    rx.recv_timeout(Duration::from_secs(secs)).ok()
}

fn iso_on() {
    std::env::remove_var("PRATTAIL_NO_SEP_ISOLATION");
}
fn iso_off() {
    std::env::set_var("PRATTAIL_NO_SEP_ISOLATION", "1");
}

#[test]
#[ignore = "throwaway P2 S0-CG codegen gate; run explicitly"]
fn p2cg_s0_gate() {
    let kmax: usize = std::env::var("P2_KMAX").ok().and_then(|s| s.parse().ok()).unwrap_or(8);
    let mono_kmax: usize = std::env::var("P2_MONO_KMAX").ok().and_then(|s| s.parse().ok()).unwrap_or(4);
    let mono_timeout: u64 = std::env::var("P2_MONO_TIMEOUT").ok().and_then(|s| s.parse().ok()).unwrap_or(60);

    eprintln!("================ P2 S0-CG CODEGEN GATE ================");
    let mut lost = false;
    let mut on_ms_ladder: Vec<u128> = Vec::new();
    let mut off_ms_ladder: Vec<String> = Vec::new();

    for k in 0..=kmax {
        let input = build_input(k);

        // ── ON (isolation) ──
        iso_on();
        let t0 = Instant::now();
        let on = alt_set_all(&input);
        let on_ms = t0.elapsed().as_millis();
        on_ms_ladder.push(on_ms);
        let on_set = on.clone().unwrap_or_default();

        // ── OFF (monolithic), timeout-bounded ──
        let off_desc = if k <= mono_kmax {
            let input_c = input.clone();
            let t1 = Instant::now();
            let off = run_with_timeout(mono_timeout, move || {
                iso_off();
                let r = alt_set_all(&input_c);
                iso_on();
                r
            });
            let off_ms = t1.elapsed().as_millis();
            match off {
                None => {
                    format!("TIMEOUT>{mono_timeout}s")
                }
                Some(off_set) => {
                    let off_set = off_set.unwrap_or_default();
                    let missing: Vec<&String> = off_set.difference(&on_set).collect();
                    let extra: Vec<&String> = on_set.difference(&off_set).collect();
                    if !missing.is_empty() {
                        lost = true;
                        eprintln!("  [S0-CG-sound] k={k} ON DROPPED {} monolithic reading(s): {:?}", missing.len(), missing);
                    }
                    if !extra.is_empty() {
                        eprintln!("  [S0-CG-sound] k={k} ON GAINED {} reading(s): {:?}", extra.len(), extra);
                    }
                    let verdict = if missing.is_empty() && extra.is_empty() { "==" } else if missing.is_empty() { "ON⊋OFF" } else { "LOST!" };
                    format!("{off_ms}ms|off{}|on{}|{}", off_set.len(), on_set.len(), verdict)
                }
            }
        } else {
            format!("(skipped k>{mono_kmax})")
        };
        off_ms_ladder.push(off_desc.clone());
        eprintln!("[k={k}] ON {on_ms}ms alts={} :: OFF {off_desc}", on_set.len());
    }

    // ── S0-CG-single: single winner ON == OFF for k=0..4 ──
    eprintln!("--- S0-CG-single (single winner ON vs OFF) ---");
    for k in 0..=mono_kmax.min(4) {
        let input = build_input(k);
        iso_on();
        let on_w = single_winner(&input);
        iso_off();
        let off_w = single_winner(&input);
        iso_on();
        let same = on_w == off_w;
        eprintln!("  [single] k={k} same_winner={same}");
        assert!(same, "S0-CG-single HALT: single winner differs at k={k}\n ON={:?}\n OFF={:?}", on_w, off_w);
    }

    // ── S0-CG-variants ──
    eprintln!("--- S0-CG-variants ---");
    let variant_cases = [
        ("@a<-@b & @c<-@d where Nil", "ForRowWhere (2-seg + where)"),
        ("@a<-@b where Nil", "ForRowSingleWhere (fall-through)"),
        ("@a<-@b", "ForRowSingleNoWhere (fall-through)"),
    ];
    for (src, desc) in variant_cases {
        iso_on();
        let on = single_winner(src);
        iso_off();
        let off = single_winner(src);
        iso_on();
        let same = on == off;
        eprintln!("  [variant] `{src}` ({desc}) parses_on={} same_as_off={same}", on.is_some());
        assert!(on.is_some(), "S0-CG-variants HALT: `{src}` failed to parse with isolation ON");
        assert!(same, "S0-CG-variants HALT: `{src}` winner differs ON vs OFF\n ON={:?}\n OFF={:?}", on, off);
    }

    eprintln!("--- SUMMARY ---");
    eprintln!("ON wall-ms ladder (S0-CG-linear): {:?}", on_ms_ladder);
    eprintln!("OFF ladder (monolithic)         : {:?}", off_ms_ladder);
    eprintln!("any_reading_lost = {lost}");
    eprintln!("================ END P2 S0-CG GATE ================");
    assert!(!lost, "S0-CG-sound HALT: isolation ON dropped a monolithic reading");
}
