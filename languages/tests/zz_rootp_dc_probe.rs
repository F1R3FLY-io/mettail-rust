//! THROWAWAY Stage-0 probe for the DIVIDE-AND-CONQUER `.*sep` reconvergence fix
//! (ROOT-P `<-` linearization, Plan ad4b660e, 2026-07-05). MEASURE-ONLY — creates
//! no behavioral change; the peak is read from the measure-only `dc_shadow` sink
//! (byte-identical unless `PRATTAIL_DC_SHADOW=1`).
//!
//! Unlike the 8 refuted priors (M0 watermark, BCC seal, DW `(edge_target,EdgeKind)`
//! projection …), which all FOLDED a merge-key projection of the *monolithic*
//! frontier, this probe measures a GENUINELY NEW quantity: the cost of parsing each
//! `&`-separated segment in a TRULY ISOLATED sub-parse (its own walker via the public
//! `InputBind::parse_via_wpda_all` facade → `new_for_category`, edge-stack from ROOT,
//! NO cross-segment accumulation). That is the ground truth the DW shadow could not
//! simulate.
//!
//! GATES (HALT-on-fail):
//!   S0-A  per-segment isolated peak CONSTANT across position k (each ≈ the k=0
//!         whole-ForRow peak; DOESN'T grow with k).
//!   S0-B  ★DECISIVE composite Σ isolated peaks LINEAR in k (≈ (k+1)·base, NOT the
//!         monolithic ~9×/seg exponential).
//!   S0-snd  isolated per-segment reading SET ⊇ each monolithic position's reading
//!           SET (NO reading lost); report equality / superset.
//!   S0-bnd  depth-0 `&` split is bracket-depth determinate (never splits an inner
//!           `for(…&…){…}`).
//!
//! Run: `cargo test -p languages --features walker-stats --test zz_rootp_dc_probe -- --nocapture --ignored`
//! with `PRATTAIL_DC_SHADOW=1` (and, for full k, a generous timeout).

use std::collections::HashSet;
use std::time::{Duration, Instant};

use mettail_languages::rhocalc::{ForRow, InputBind};

// ── measure-only peak sink accessors (cfg-gated so the probe still compiles
//    without the walker-stats feature; peaks are simply absent then) ──────────
fn clear_peaks() {
    #[cfg(feature = "walker-stats")]
    mettail_prattail::walker_stats::dc_shadow::clear_peaks();
}
fn drain_last_peak() -> Option<u64> {
    #[cfg(feature = "walker-stats")]
    {
        return mettail_prattail::walker_stats::dc_shadow::drain_peaks()
            .into_iter()
            .last();
    }
    #[allow(unreachable_code)]
    None
}

/// Canonicalize monotonic fresh-var ids so two SEPARATE parses of the same reading
/// compare equal (mirrors `rhocalc_tests::normalize_var_ids`). Var NAMES are kept
/// (distinct per segment: `x0/y0`, `x1/y1`, …), only the `UniqueId(<n>)` counter is
/// erased — isolating GENUINE structural differences.
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

/// Bracket-depth-aware split at depth-0 `&` (S0-boundary). Tracks `()[]{}` nesting
/// (the multi-char collection delimiters `#{ }# {| |}` are handled implicitly by
/// their `{`/`}` component). Splits ONLY when depth == 0, so an inner
/// `for(u<-v & s<-t){…}` `&` never fragments an enclosing segment.
fn split_amp_depth0(input: &str) -> Vec<String> {
    let mut segs = Vec::new();
    let mut depth: i32 = 0;
    let mut cur = String::new();
    let mut chars = input.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '(' | '[' | '{' => {
                depth += 1;
                cur.push(c);
            }
            ')' | ']' | '}' => {
                depth -= 1;
                cur.push(c);
            }
            '&' if depth == 0 => {
                segs.push(cur.trim().to_string());
                cur.clear();
            }
            _ => cur.push(c),
        }
    }
    let last = cur.trim().to_string();
    if !last.is_empty() {
        segs.push(last);
    }
    segs
}

/// `@x0<-@y0 & @x1<-@y1 & … & @x{k}<-@y{k}` — (k+1) segments, distinct names so no
/// two binds dedup. `@`-quoted-LHS `<-` is the ROOT-P adversarial carrier.
fn build_input(k: usize) -> String {
    (0..=k)
        .map(|i| format!("@x{i}<-@y{i}"))
        .collect::<Vec<_>>()
        .join(" & ")
}

/// Decompose a no-where ForRow reading into its per-position InputBind readings
/// (canonicalized Debug). `None` for any OTHER variant (where/persistent/lam/…),
/// tallied separately so an unexpected variant is visible, not silently dropped.
fn forrow_positions(fr: &ForRow) -> Option<Vec<String>> {
    match fr {
        ForRow::ForRowNoWhere(b, bs) => {
            let mut v = Vec::with_capacity(bs.len() + 1);
            v.push(normalize_var_ids(&format!("{:?}", b)));
            for ib in bs {
                v.push(normalize_var_ids(&format!("{:?}", ib)));
            }
            Some(v)
        }
        ForRow::ForRowSingleNoWhere(b) => {
            Some(vec![normalize_var_ids(&format!("{:?}", b))])
        }
        _ => None,
    }
}

/// Run `body` on a worker thread, `None` on timeout (worker detached — process exit
/// reaps it; callers break the monolithic ladder on the first timeout so at most one
/// detached exponential parse ever runs).
fn run_with_timeout<T: Send + 'static>(secs: u64, body: impl FnOnce() -> T + Send + 'static) -> Option<T> {
    use std::sync::mpsc;
    let (tx, rx) = mpsc::channel();
    let _ = std::thread::Builder::new()
        .name("dc-probe-mono".into())
        .spawn(move || {
            let _ = tx.send(body());
        });
    rx.recv_timeout(Duration::from_secs(secs)).ok()
}

#[test]
#[ignore = "throwaway ROOT-P D&C Stage-0 measurement; run explicitly with PRATTAIL_DC_SHADOW=1"]
fn dc_stage0_measure() {
    let kmax: usize = std::env::var("DC_KMAX").ok().and_then(|s| s.parse().ok()).unwrap_or(6);
    let mono_kmax: usize = std::env::var("DC_MONO_KMAX").ok().and_then(|s| s.parse().ok()).unwrap_or(4);
    let mono_timeout: u64 = std::env::var("DC_MONO_TIMEOUT").ok().and_then(|s| s.parse().ok()).unwrap_or(120);

    eprintln!("=================== DC STAGE-0 PROBE ===================");
    eprintln!("shadow_active={} kmax={kmax} mono_kmax={mono_kmax} mono_timeout={mono_timeout}s",
        cfg!(feature = "walker-stats"));

    // ── S0-boundary: bracket-depth-aware split determinism ──────────────────
    {
        let flat = build_input(3);
        let segs = split_amp_depth0(&flat);
        eprintln!("[S0-bnd] flat k=3 split -> {} segs {:?}", segs.len(), segs);
        assert_eq!(segs.len(), 4, "flat depth-0 split must yield k+1 segments");
        // nested inner `&` inside `@( … for(u<-v & s<-t){Nil} … )` must NOT split
        let nested = "@a<-@(for(u<-v & s<-t){Nil}) & @c<-@d";
        let nsegs = split_amp_depth0(nested);
        eprintln!("[S0-bnd] nested split -> {} segs {:?}", nsegs.len(), nsegs);
        assert_eq!(nsegs.len(), 2, "nested inner `&` must NOT be split (bracket depth)");
    }

    // ── ISOLATED per-segment measurements (fast; S0-A / S0-B) ────────────────
    // Stored so the monolithic phase can reuse the reading sets for soundness.
    let mut iso_sum_by_k: Vec<u64> = Vec::new();
    let mut iso_peaks_by_k: Vec<Vec<Option<u64>>> = Vec::new();
    let mut iso_sets_by_k: Vec<Vec<HashSet<String>>> = Vec::new();

    for k in 0..=kmax {
        let input = build_input(k);
        let segs = split_amp_depth0(&input);
        assert_eq!(segs.len(), k + 1);

        let mut peaks: Vec<Option<u64>> = Vec::with_capacity(k + 1);
        let mut sets: Vec<HashSet<String>> = Vec::with_capacity(k + 1);
        let start = Instant::now();
        for seg in &segs {
            mettail_runtime::clear_var_cache();
            clear_peaks();
            let alts = InputBind::parse_via_wpda_all(seg).unwrap_or_default();
            let peak = drain_last_peak();
            peaks.push(peak);
            let set: HashSet<String> = alts
                .iter()
                .map(|ib| normalize_var_ids(&format!("{:?}", ib)))
                .collect();
            sets.push(set);
        }
        let iso_sum: u64 = peaks.iter().flatten().sum();
        let elapsed = start.elapsed();
        let alt_counts: Vec<usize> = sets.iter().map(|s| s.len()).collect();
        let product: usize = alt_counts.iter().product();
        eprintln!(
            "[ISO] k={k} peaks={:?} SUM={iso_sum} alt_counts={:?} product={product} ({} ms)",
            peaks, alt_counts, elapsed.as_millis()
        );
        iso_sum_by_k.push(iso_sum);
        iso_peaks_by_k.push(peaks);
        iso_sets_by_k.push(sets);
    }

    // ── MONOLITHIC measurements (exponential; re-baseline + soundness) ───────
    let mut mono_peaks: Vec<Option<u64>> = Vec::new();
    for k in 0..=mono_kmax.min(kmax) {
        let input = build_input(k);
        clear_peaks();
        let start = Instant::now();
        let input_clone = input.clone();
        let result: Option<(Vec<Vec<String>>, usize, usize)> = run_with_timeout(mono_timeout, move || {
            mettail_runtime::clear_var_cache();
            let alts = ForRow::parse_via_wpda_all(&input_clone).unwrap_or_default();
            let total = alts.len();
            let mut readings = Vec::new();
            let mut other = 0usize;
            for fr in &alts {
                match forrow_positions(fr) {
                    Some(p) => readings.push(p),
                    None => other += 1,
                }
            }
            (readings, other, total)
        });
        let mono_peak = drain_last_peak();
        mono_peaks.push(mono_peak);
        let elapsed = start.elapsed();

        match result {
            None => {
                eprintln!("[MONO] k={k} TIMEOUT >{mono_timeout}s (exponential) — breaking monolithic ladder");
                break;
            }
            Some((readings, other, total)) => {
                // aggregate per-position reading sets across all monolithic readings
                let mut pos_sets: Vec<HashSet<String>> = vec![HashSet::new(); k + 1];
                let mut shape_mismatch = 0usize;
                for r in &readings {
                    if r.len() == k + 1 {
                        for (i, p) in r.iter().enumerate() {
                            pos_sets[i].insert(p.clone());
                        }
                    } else {
                        shape_mismatch += 1;
                    }
                }
                // S0-snd: for each position, is the isolated set a SUPERSET of the
                // monolithic position set? (i.e. no monolithic reading is lost)
                let iso_sets = &iso_sets_by_k[k];
                let mut lost_total = 0usize;
                let mut rel = Vec::new();
                for i in 0..=k {
                    let lost: Vec<&String> = pos_sets[i].difference(&iso_sets[i]).collect();
                    lost_total += lost.len();
                    let relation = if pos_sets[i] == iso_sets[i] {
                        "=="
                    } else if pos_sets[i].is_subset(&iso_sets[i]) {
                        "iso⊋mono"
                    } else {
                        "LOST!"
                    };
                    rel.push(format!("p{i}:mono{}|iso{}|{}", pos_sets[i].len(), iso_sets[i].len(), relation));
                    if !lost.is_empty() {
                        eprintln!("  [S0-snd] k={k} pos={i} LOST {} reading(s): {:?}", lost.len(), lost);
                    }
                }
                eprintln!(
                    "[MONO] k={k} peak={:?} total_alts={total} nowhere_readings={} other_variants={other} shape_mismatch={shape_mismatch} ({} ms)",
                    mono_peak, readings.len(), elapsed.as_millis()
                );
                eprintln!("  [S0-snd] {} lost_total={lost_total}", rel.join("  "));
            }
        }
    }

    // ── VERDICT SUMMARY ─────────────────────────────────────────────────────
    eprintln!("--------------------- SUMMARY ---------------------");
    eprintln!("iso_sum ladder (S0-B): {:?}", iso_sum_by_k);
    // per-segment peak table (S0-A): each segment across k
    eprintln!("mono_peak ladder     : {:?}", mono_peaks);
    // S0-B linearity ratios
    let mut ratios = Vec::new();
    for w in iso_sum_by_k.windows(2) {
        if w[0] > 0 {
            ratios.push(format!("{:.2}", w[1] as f64 / w[0] as f64));
        } else {
            ratios.push("-".into());
        }
    }
    eprintln!("iso_sum step-ratios  : {:?} (LINEAR ⇒ →1.0, EXP ⇒ ≫1)", ratios);
    let mut mono_ratios = Vec::new();
    for w in mono_peaks.windows(2) {
        match (w[0], w[1]) {
            (Some(a), Some(b)) if a > 0 => mono_ratios.push(format!("{:.2}", b as f64 / a as f64)),
            _ => mono_ratios.push("-".into()),
        }
    }
    eprintln!("mono_peak step-ratios: {:?} (the exponential baseline)", mono_ratios);
    eprintln!("=================== END DC STAGE-0 ===================");
}

/// Full cartesian product of per-position reading sets → set of position tuples.
fn cartesian(per_pos: &[Vec<String>]) -> HashSet<Vec<String>> {
    let mut acc: HashSet<Vec<String>> = HashSet::new();
    acc.insert(Vec::new());
    for s in per_pos {
        let mut next = HashSet::with_capacity(acc.len() * s.len().max(1));
        for prefix in &acc {
            for item in s {
                let mut t = prefix.clone();
                t.push(item.clone());
                next.insert(t);
            }
        }
        acc = next;
    }
    acc
}

/// S0-soundness STRESS: on HETEROGENEOUS and potentially d>1 segment lists, verify
/// the isolated-then-COMBINED alt SET (cartesian product of per-segment InputBind
/// readings) EXACTLY equals the monolithic ForRow alt SET (decomposed to position
/// tuples). This is the make-or-break the design mandates: `mono ⊆ cartesian` (NO
/// reading lost — HALT if violated) and `cartesian ⊆ mono` (no spurious gain — a
/// never-disambiguate-early note if violated).
#[test]
#[ignore = "throwaway ROOT-P D&C Stage-0 soundness stress; run explicitly"]
fn dc_stage0_soundness_shapes() {
    // Each case: a Vec of segment source strings (the `&`-joined ForRow).
    let cases: Vec<Vec<&str>> = vec![
        vec!["@a<-@b"],
        vec!["x<-c"],
        vec!["@a<-@b", "x<-c"],
        vec!["x<-c", "y<-d"],
        vec!["@a<-@b", "@c<-@d", "x<-e"],
        vec!["@a<=@b"],
        vec!["@a<=@b", "@c<=@d"],
        vec!["a,b<-c"],
        vec!["@a<-@b", "a,b<-c"],
        vec!["@(Map()<@Nil!())<=a"],
        vec!["@(Map()<@Nil!())<=a", "@b<-@c"],
    ];

    eprintln!("============== DC STAGE-0 SOUNDNESS SHAPES ==============");
    let mut any_lost = false;
    for segs in &cases {
        let whole = segs.join(" & ");
        // isolated per-segment reading sets
        let mut per_pos: Vec<Vec<String>> = Vec::new();
        let mut iso_counts: Vec<usize> = Vec::new();
        let mut iso_ok = true;
        for seg in segs {
            mettail_runtime::clear_var_cache();
            match InputBind::parse_via_wpda_all(seg) {
                Ok(alts) if !alts.is_empty() => {
                    let mut set: Vec<String> = alts
                        .iter()
                        .map(|ib| normalize_var_ids(&format!("{:?}", ib)))
                        .collect::<HashSet<_>>()
                        .into_iter()
                        .collect();
                    set.sort();
                    iso_counts.push(set.len());
                    per_pos.push(set);
                }
                other => {
                    iso_ok = false;
                    eprintln!("[SND] `{seg}` isolated parse did NOT yield InputBind alts: {:?}", other.map(|v| v.len()));
                    break;
                }
            }
        }
        if !iso_ok {
            eprintln!("[SND] SKIP `{whole}` (a segment is not a bare InputBind)\n");
            continue;
        }
        let combine = cartesian(&per_pos);

        // monolithic ForRow reading set → position tuples
        mettail_runtime::clear_var_cache();
        let mono = ForRow::parse_via_wpda_all(&whole);
        let (mono_tuples, mono_total, mono_other): (HashSet<Vec<String>>, usize, usize) = match &mono {
            Ok(alts) => {
                let mut set = HashSet::new();
                let mut other = 0usize;
                for fr in alts {
                    match forrow_positions(fr) {
                        Some(p) if p.len() == segs.len() => {
                            set.insert(p);
                        }
                        _ => other += 1,
                    }
                }
                (set, alts.len(), other)
            }
            Err(e) => {
                eprintln!("[SND] `{whole}` monolithic ForRow::parse_via_wpda_all ERR: {e}\n");
                continue;
            }
        };

        let lost: Vec<&Vec<String>> = mono_tuples.difference(&combine).collect();
        let gained: Vec<&Vec<String>> = combine.difference(&mono_tuples).collect();
        if !lost.is_empty() {
            any_lost = true;
        }
        let verdict = if mono_tuples == combine {
            "SOUND+COMPLETE (==)"
        } else if lost.is_empty() {
            "SOUND, iso⊋mono (never-disambiguate-early GAIN)"
        } else {
            "★LOST — HALT"
        };
        eprintln!(
            "[SND] `{whole}` iso_counts={:?} cartesian={} mono_tuples={} mono_total={mono_total} mono_other={mono_other} :: {verdict}",
            iso_counts, combine.len(), mono_tuples.len()
        );
        if !lost.is_empty() {
            eprintln!("      LOST {}: {:?}", lost.len(), lost);
        }
        if !gained.is_empty() {
            eprintln!("      GAINED {}: {:?}", gained.len(), gained);
        }
    }
    eprintln!("any_reading_lost={any_lost}");
    eprintln!("============== END SOUNDNESS SHAPES ==============");
    assert!(!any_lost, "S0-soundness HALT: the isolated-combine LOST a monolithic reading");
}
