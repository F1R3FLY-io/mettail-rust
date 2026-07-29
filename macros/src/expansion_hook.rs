//! ★ THE EXPANSION PANIC HOOK — the one thing that can name the *language*.
//!
//! # What this is for, stated against what the default handler already does
//!
//! It is tempting to describe this hook as "the thing that makes mute panics
//! speak". ⚠ **That description is false, and it was measured false** (2026-07-29,
//! `red0`/`scope-panic-nohook`): with **no** hook installed at all, the standard
//! library's default handler already prints
//!
//! ```text
//! thread '<unnamed>' panicked at prattail/src/confluence.rs:812:9:
//! <the payload>
//! ```
//!
//! for a panic raised in a spawned analysis thread inside the proc macro. The
//! payload and the source position are **not** lost. What *is* lost is everything
//! the default handler cannot possibly know:
//!
//! | fact | default handler | this hook |
//! |---|---|---|
//! | payload | ✓ | — (chains to it) |
//! | file:line of the `panic!` | ✓ | — (chains to it) |
//! | **which `language!` was being expanded** | ✗ | ✓ |
//!
//! One `rustc` process expands every `language!` in a crate — 54 of them in
//! `mettail_languages`. A `panicked at factoring.rs:2416` with no language name
//! names a *generator site* and leaves the reader to bisect 54 grammars to find
//! the *input* that reached it. That attribution is this hook's entire product,
//! and it is why the hook is not made redundant by returning `compile_error!`
//! tokens everywhere: a `compile_error!` is only available where the refusal was
//! *anticipated*. The hook covers the sites nobody enumerated.
//!
//! # Why a hook can speak where a `catch_unwind` cannot
//!
//! This workspace compiles `[profile.dev]` with the **cranelift** backend, which
//! emits no catch pads: an unwind sails straight through any `catch_unwind`
//! monomorphised in a cranelift-compiled crate, and `rustc` dies with
//! `fatal runtime error: Rust cannot catch foreign exceptions` (proc macro) or
//! `failed to initiate panic, error 5` (spawned thread). Both are `SIGABRT`.
//!
//! `std::panic::set_hook` is immune to that, because the hook is **not a landing
//! pad**. `std::panicking::rust_panic_with_hook` calls it on the panicking
//! thread, on the ordinary call path, *before* any unwinding is initiated — and
//! that code lives in the precompiled LLVM `std`. Whether the unwind that follows
//! succeeds, aborts, or sails through a catch pad that was never emitted is
//! irrelevant to whether the hook ran.
//!
//! # Installation discipline
//!
//! * Installed **once per process** via [`std::sync::Once`], from the
//!   `#[proc_macro]` entry point only — never from [`crate::expand_language`],
//!   which the unit tests call. A test binary has libtest's own hook and its own
//!   capture machinery; replacing it from a test would change what every other
//!   test in the binary reports.
//! * It **chains**: the previous hook is captured by [`std::panic::take_hook`]
//!   and invoked after ours, so the payload and location still print exactly as
//!   they did before. This hook only ever *adds* a line.

use std::sync::{Mutex, Once};

/// Guards the one-time [`std::panic::set_hook`] call.
static HOOK_INSTALLED: Once = Once::new();

/// The name of the most recent `language!` this process began expanding.
///
/// A `Mutex` rather than a `thread_local!` **because the attribution has to
/// survive a thread boundary**: `prattail::pipeline::analysis` spawns 33 theory
/// analyses inside `std::thread::scope`, and a panic in one of them runs the hook
/// on a thread that never saw the macro entry. A thread-local would print
/// `<none>` for exactly the 114 sites that most need naming.
///
/// It is never cleared on the way out. That is deliberate and the message says
/// so: the useful attribution for a panic during expansion is "the last grammar
/// this process picked up", and clearing it would require threading a guard
/// through every early return in [`crate::expand_language`] — nine of which are
/// refusals that are *supposed* to leave without ceremony.
static EXPANDING: Mutex<Option<String>> = Mutex::new(None);

/// Install the hook, at most once per process.
pub(crate) fn install() {
    HOOK_INSTALLED.call_once(|| {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            eprintln!(
                "[mettail] PANIC during macro expansion — most recently entered \
                 `language!`: {}. The line below names the generator site; this line \
                 names the grammar that reached it.",
                expanding()
            );
            previous(info);
        }));
    });
}

/// Record the grammar `language!` has just started expanding.
pub(crate) fn entering(language_name: &str) {
    let mut slot = EXPANDING
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    match slot.as_mut() {
        Some(existing) => {
            existing.clear();
            existing.push_str(language_name);
        },
        None => *slot = Some(language_name.to_string()),
    }
}

/// The recorded grammar name, rendered for the diagnostic.
fn expanding() -> String {
    let slot = EXPANDING
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    match slot.as_deref() {
        Some(name) => format!("`{name}`"),
        // Reachable only for a panic raised before the first `language!` body
        // parses — e.g. inside `syn`'s own parser.
        None => "<none entered yet>".to_string(),
    }
}

// ⚠ `raised_by_proc_macro_error` — the `AbortNow` FILTER — was DELETED here
// together with the `proc-macro-error` dependency itself (#141 change 3b). It read:
//
//     fn raised_by_proc_macro_error(info: &std::panic::PanicHookInfo<'_>) -> bool {
//         info.location()
//             .is_some_and(|location| location.file().contains("proc-macro-error"))
//     }
//
// and it guarded the `eprintln!` above.
//
// # Why it existed, and why it no longer can
//
// MEASURED, 2026-07-29 (`red0`/`case-hook-abort`): `proc_macro_error::abort!` is
// implemented as `panic!(AbortNow)`, raised at
// `proc-macro-error-1.0.4/src/lib.rs:472`, and it therefore RAN THIS HOOK. Every
// deliberate, fully-rendered `abort!` diagnostic would otherwise have grown a
// spurious `[mettail] PANIC during macro expansion` line underneath it, with a
// `<non-string payload>` body — a clean diagnostic made to read like a crash.
// The discrimination was on the panic's LOCATION rather than its payload,
// because `AbortNow` is a private unit struct that cannot be downcast from here,
// while a payload-shape test ("not a `&str` and not a `String`") would have
// swallowed every legitimate structured panic — the opposite of this hook's
// purpose. That filter was correct, and it was necessary for exactly as long as
// this crate depended on `proc-macro-error`.
//
// It is deleted rather than retained as a guard against re-introduction: with
// the dependency gone from `macros/Cargo.toml`, no `AbortNow` can be raised in
// this process, so the predicate is a branch that can never be taken —
// dead code justified only by a comment, which is the shape #141 exists to
// remove. If `proc-macro-error` ever returns, this block is the record of what
// has to come back with it.
