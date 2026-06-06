//! T4 SIGUSR1 hang-dump facility (designed 2026-05-02, implemented 2026-05-05).
//!
//! Lets a user send `SIGUSR1` to a running parser process and capture a
//! snapshot of walker state — useful for debugging hangs that the trace
//! facility wasn't pre-armed for. Also supports automatic watchdog mode:
//! `PRATTAIL_HANG_WATCHDOG=N` (seconds) auto-dumps if the walker's
//! `step_counter` is unchanged for N polls.
//!
//! ## Architecture (per Plan agent design 2026-05-02)
//!
//! - **Async-signal-safe handler**: `signal-hook` flips an `AtomicBool` only.
//! - **Daemon thread**: polls every 50ms; performs all I/O outside signal context.
//! - **Walker publishes**: `wpda_walker::run_to_saturation` writes a
//!   [`HangSnapshot`] into [`SNAPSHOT_SLOT`] at the top of every iteration.
//! - **Watcher reads**: non-blocking `try_lock` on the slot. Snapshots are
//!   `Arc`-shared so the watcher can dump without holding the lock.
//!
//! ## Activation
//!
//! - **Build-time**: requires the `hang-dump` Cargo feature.
//! - **Run-time**: requires `PRATTAIL_HANG_DUMP=1`. Zero-cost when not set.
//!
//! ## Watchdog mode
//!
//! `PRATTAIL_HANG_WATCHDOG=N` (e.g., `5` for 5-second timeout). The watcher
//! polls `step_counter`; if unchanged across `N * 1000 / 50` poll intervals,
//! auto-dump. The dump re-arms — does NOT kill the process.
//!
//! ## Output
//!
//! - **stderr banner**: always when active.
//! - **JSON file**: `PRATTAIL_HANG_DUMP_PATH=/tmp/x.json` (hand-formatted; per
//!   `feedback_postcard_over_serde_json`, we don't depend on `serde_json`).

#[cfg(feature = "hang-dump")]
mod imp {
    use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
    use std::sync::{Arc, LazyLock, Once};
    use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

    /// Trigger that produced a hang-dump.
    #[derive(Debug, Clone, Copy)]
    pub enum HangTrigger {
        /// User sent `SIGUSR1`.
        Sigusr1,
        /// Watchdog detected `step_counter` unchanged for `idle_secs`.
        Watchdog { idle_secs: u64 },
    }

    /// Type-erased per-cursor row in the dump.
    #[derive(Debug, Clone)]
    pub struct CursorRow {
        pub idx: usize,
        pub pos: usize,
        pub state_dbg: String,
        pub weight_dbg: String,
        pub source_priority: u32,
        pub pending_ops_len: usize,
        pub collection_depth: usize,
    }

    /// Snapshot captured at signal time. Type-erased so a single static can
    /// hold any walker's state regardless of `W: Semiring`.
    #[derive(Debug, Clone)]
    pub struct HangSnapshot {
        pub timestamp_unix_secs: u64,
        pub pid: u32,
        pub trigger: HangTrigger,
        pub walker_state_dbg: String,
        pub walker_pos: usize,
        pub cursor_count: usize,
        pub gss_node_count: usize,
        pub step_index: u64,
        pub cursors: Vec<CursorRow>,
    }

    impl HangSnapshot {
        /// Build a banner suitable for stderr.
        pub fn to_banner(&self) -> String {
            let mut s = String::with_capacity(512);
            s.push_str("════════════════ PRATTAIL HANG DUMP ════════════════\n");
            s.push_str(&format!(
                "  trigger={:?}  pid={}  ts={}\n",
                self.trigger, self.pid, self.timestamp_unix_secs
            ));
            s.push_str(&format!(
                "  step_index={}  walker_pos={}  state={}\n",
                self.step_index, self.walker_pos, self.walker_state_dbg
            ));
            s.push_str(&format!(
                "  cursor_count={}  gss_node_count={}\n",
                self.cursor_count, self.gss_node_count
            ));
            for row in self.cursors.iter().take(8) {
                s.push_str(&format!(
                    "  cursor[{}] pos={} state={} weight={} src_pri={} pending={} coll_depth={}\n",
                    row.idx,
                    row.pos,
                    row.state_dbg,
                    row.weight_dbg,
                    row.source_priority,
                    row.pending_ops_len,
                    row.collection_depth,
                ));
            }
            if self.cursors.len() > 8 {
                s.push_str(&format!("  ... ({} more cursors omitted)\n", self.cursors.len() - 8));
            }
            s.push_str("═════════════════════════════════════════════════════\n");
            s
        }

        /// Render as JSON. Hand-formatted (per feedback memory: no
        /// `serde_json` dep). Schema is flat enough that manual escaping
        /// is cheap and obvious.
        pub fn to_json(&self) -> String {
            let mut s = String::with_capacity(512 + self.cursors.len() * 128);
            s.push('{');
            push_json_field(
                &mut s,
                "timestamp_unix_secs",
                &self.timestamp_unix_secs.to_string(),
                false,
            );
            s.push(',');
            push_json_field(&mut s, "pid", &self.pid.to_string(), false);
            s.push(',');
            push_json_field(&mut s, "trigger", &format!("{:?}", self.trigger), true);
            s.push(',');
            push_json_field(&mut s, "walker_state", &self.walker_state_dbg, true);
            s.push(',');
            push_json_field(&mut s, "walker_pos", &self.walker_pos.to_string(), false);
            s.push(',');
            push_json_field(&mut s, "cursor_count", &self.cursor_count.to_string(), false);
            s.push(',');
            push_json_field(&mut s, "gss_node_count", &self.gss_node_count.to_string(), false);
            s.push(',');
            push_json_field(&mut s, "step_index", &self.step_index.to_string(), false);
            s.push(',');
            s.push_str("\"cursors\":[");
            for (i, c) in self.cursors.iter().enumerate() {
                if i > 0 {
                    s.push(',');
                }
                s.push('{');
                push_json_field(&mut s, "idx", &c.idx.to_string(), false);
                s.push(',');
                push_json_field(&mut s, "pos", &c.pos.to_string(), false);
                s.push(',');
                push_json_field(&mut s, "state", &c.state_dbg, true);
                s.push(',');
                push_json_field(&mut s, "weight", &c.weight_dbg, true);
                s.push(',');
                push_json_field(&mut s, "source_priority", &c.source_priority.to_string(), false);
                s.push(',');
                push_json_field(&mut s, "pending_ops_len", &c.pending_ops_len.to_string(), false);
                s.push(',');
                push_json_field(&mut s, "collection_depth", &c.collection_depth.to_string(), false);
                s.push('}');
            }
            s.push(']');
            s.push('}');
            s
        }
    }

    /// Append `"key": value` to the JSON buffer. When `quote_value` is true,
    /// the value is JSON-string-escaped (`"`, `\`, control chars). Otherwise
    /// it's emitted verbatim (numeric / boolean).
    fn push_json_field(buf: &mut String, key: &str, value: &str, quote_value: bool) {
        buf.push('"');
        buf.push_str(key);
        buf.push_str("\":");
        if quote_value {
            buf.push('"');
            for ch in value.chars() {
                match ch {
                    '"' => buf.push_str("\\\""),
                    '\\' => buf.push_str("\\\\"),
                    '\n' => buf.push_str("\\n"),
                    '\r' => buf.push_str("\\r"),
                    '\t' => buf.push_str("\\t"),
                    c if (c as u32) < 0x20 => {
                        buf.push_str(&format!("\\u{:04x}", c as u32));
                    },
                    c => buf.push(c),
                }
            }
            buf.push('"');
        } else {
            buf.push_str(value);
        }
    }

    /// Async-signal-safe flag flipped by the SIGUSR1 handler. The watcher
    /// daemon polls this and clears it after each dump. Held as `Arc` so it
    /// can be shared with `signal_hook::flag::register` (which takes
    /// `Arc<AtomicBool>`).
    static SIGUSR1_FIRED: LazyLock<Arc<AtomicBool>> =
        LazyLock::new(|| Arc::new(AtomicBool::new(false)));

    /// The walker writes a fresh `HangSnapshot` into this slot at safe points.
    /// The watcher does `try_lock` (non-blocking); the walker holds the lock
    /// only for the duration of the swap.
    static SNAPSHOT_SLOT: parking_lot::Mutex<Option<Arc<HangSnapshot>>> =
        parking_lot::Mutex::new(None);

    /// Step-counter mirror updated by `publish_snapshot`. The watchdog
    /// inspects this to detect "no progress" without taking the slot lock.
    static LAST_STEP_INDEX: AtomicU64 = AtomicU64::new(0);

    /// Ensures `install_hang_dump_handler` runs at most once per process.
    static INSTALL_ONCE: Once = Once::new();

    /// Install the SIGUSR1 handler + spawn the watcher daemon thread.
    ///
    /// No-op when `PRATTAIL_HANG_DUMP` env var is not set. Safe to call
    /// multiple times — the `Once` guard ensures only one install.
    pub fn install_hang_dump_handler() {
        if std::env::var("PRATTAIL_HANG_DUMP").is_err() {
            return;
        }
        INSTALL_ONCE.call_once(|| {
            // Register SIGUSR1 → flip flag (async-signal-safe).
            if let Err(e) =
                signal_hook::flag::register(signal_hook::consts::SIGUSR1, SIGUSR1_FIRED.clone())
            {
                eprintln!("prattail-hang-dump: failed to register SIGUSR1: {e}");
                return;
            }

            // Watchdog interval (env-driven).
            let watchdog_secs: Option<u64> = std::env::var("PRATTAIL_HANG_WATCHDOG")
                .ok()
                .and_then(|s| s.parse().ok());

            // Spawn watcher daemon.
            std::thread::Builder::new()
                .name("prattail-hang-watcher".into())
                .spawn(move || watcher_loop(watchdog_secs))
                .ok();
        });
    }

    /// The walker calls this every step (top of `run_to_saturation`'s loop)
    /// to publish its current snapshot. Cheap on the happy path: an
    /// AtomicU64 store and a non-blocking lock. Skipped when the
    /// `PRATTAIL_HANG_DUMP` env isn't set (the install guard means
    /// SIGUSR1_FIRED can't be flipped).
    pub fn publish_snapshot(snapshot: HangSnapshot) {
        LAST_STEP_INDEX.store(snapshot.step_index, Ordering::Relaxed);
        if let Some(mut guard) = SNAPSHOT_SLOT.try_lock() {
            *guard = Some(Arc::new(snapshot));
        }
        // If lock contended (the watcher is reading), we skip — the next
        // publish will catch up.
    }

    /// Daemon thread loop. Polls SIGUSR1_FIRED + watchdog idleness.
    fn watcher_loop(watchdog_secs: Option<u64>) {
        let poll_interval = Duration::from_millis(50);
        let polls_per_sec = 1000 / 50; // = 20
        let watchdog_polls: Option<u64> = watchdog_secs.map(|s| s * polls_per_sec);

        let mut last_seen_step: u64 = 0;
        let mut idle_polls: u64 = 0;
        let watcher_started = Instant::now();

        loop {
            std::thread::sleep(poll_interval);

            // Manual SIGUSR1 trigger
            if SIGUSR1_FIRED.swap(false, Ordering::AcqRel) {
                if let Some(snap) = take_snapshot(HangTrigger::Sigusr1) {
                    dump_snapshot(&snap);
                }
                idle_polls = 0;
                last_seen_step = LAST_STEP_INDEX.load(Ordering::Relaxed);
                continue;
            }

            // Watchdog mode
            if let Some(threshold) = watchdog_polls {
                let cur_step = LAST_STEP_INDEX.load(Ordering::Relaxed);
                if cur_step == last_seen_step {
                    idle_polls += 1;
                    if idle_polls >= threshold && watcher_started.elapsed().as_secs() > 1 {
                        let trigger =
                            HangTrigger::Watchdog { idle_secs: idle_polls / polls_per_sec };
                        if let Some(snap) = take_snapshot(trigger) {
                            dump_snapshot(&snap);
                        }
                        idle_polls = 0;
                    }
                } else {
                    last_seen_step = cur_step;
                    idle_polls = 0;
                }
            }
        }
    }

    /// Snapshot the current slot, overriding the trigger field.
    fn take_snapshot(trigger: HangTrigger) -> Option<Arc<HangSnapshot>> {
        let guard = SNAPSHOT_SLOT.try_lock()?;
        let snap = guard.clone()?;
        // Construct a new Arc with the trigger overridden — preserves
        // immutability of any concurrently-held Arc clones.
        let mut overridden = (*snap).clone();
        overridden.trigger = trigger;
        Some(Arc::new(overridden))
    }

    /// Emit the snapshot to stderr + optional JSON file.
    fn dump_snapshot(snap: &HangSnapshot) {
        eprintln!("{}", snap.to_banner());
        if let Ok(path) = std::env::var("PRATTAIL_HANG_DUMP_PATH") {
            let json = snap.to_json();
            if let Err(e) = std::fs::write(&path, &json) {
                eprintln!("prattail-hang-dump: failed to write {path}: {e}");
            }
        }
    }

    /// Read the current Unix timestamp (seconds since epoch).
    pub fn now_unix_secs() -> u64 {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0)
    }

    /// Process ID. Wrapping `std::process::id()` for testability.
    pub fn current_pid() -> u32 {
        std::process::id()
    }

    // ─── Test-only helpers ───────────────────────────────────────────────────
    //
    // These let the test harness exercise the publish → take_snapshot
    // pipeline without sending real signals. Cfg-gated so they don't
    // leak into production builds.

    /// T4 hang-dump test helper: force a snapshot into the slot
    /// (bypassing the walker). Mirrors the production `publish_snapshot`
    /// path so tests verify the same Mutex semantics.
    #[cfg(test)]
    pub(crate) fn test_force_snapshot(snapshot: HangSnapshot) {
        publish_snapshot(snapshot);
    }

    /// T4 hang-dump test helper: take the currently-published snapshot
    /// with the given trigger override (mirrors what the watcher does on
    /// SIGUSR1 or watchdog firing).
    #[cfg(test)]
    pub(crate) fn test_take_snapshot(trigger: HangTrigger) -> Option<Arc<HangSnapshot>> {
        take_snapshot(trigger)
    }

    /// T4 hang-dump test helper: clear the global slot + LAST_STEP_INDEX
    /// so each test starts from a clean state. Required because the
    /// snapshot slot is process-global; without explicit reset, test
    /// ordering would leak state across test fns.
    #[cfg(test)]
    pub(crate) fn test_clear_slot() {
        *SNAPSHOT_SLOT.lock() = None;
        LAST_STEP_INDEX.store(0, Ordering::Relaxed);
    }
}

#[cfg(feature = "hang-dump")]
pub use imp::*;

// Feature-disabled fallback emitted when the `hang-dump` feature is off. The
// walker always calls `publish_snapshot`; in this configuration it becomes a
// no-op and the compiler inlines it away.
#[cfg(not(feature = "hang-dump"))]
mod disabled {
    /// `publish_snapshot` argument type for feature-disabled builds.
    #[derive(Debug, Clone)]
    pub struct HangSnapshot;

    /// No-op when the feature is off.
    #[inline(always)]
    pub fn publish_snapshot(_: HangSnapshot) {}

    /// No-op installer when the feature is off.
    #[inline(always)]
    pub fn install_hang_dump_handler() {}
}

#[cfg(not(feature = "hang-dump"))]
pub use disabled::*;
