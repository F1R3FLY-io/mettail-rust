//! ★★ THE REPORTED DISPOSITION — why a partial operation refused, carried as a value.
//!
//! # The root this module closes
//!
//! [`crate::SafeArith`] never panics, which is correct and load-bearing: a panic raised inside a
//! Dovetail fold body runs with the e-graph mid-saturation, and under this workspace's
//! `[profile.dev] codegen-backend = "cranelift"` it is not containable — `catch_unwind`
//! monomorphised in a cg_clif crate emits no catch pad, so the unwind either sails through or
//! aborts with `fatal runtime error: failed to initiate panic, error 5`
//! (`dovetail/tests/panic_expectation_gate.rs`).
//!
//! But the repair that removed those panics rewrote them to an **absence** — `Option::None` —
//! when the correct rewrite is to a **reported disposition**. The proof is in the tree: three
//! Calculator fold bodies were written `.expect("ElemList: invalid index")`,
//! `.expect("DeleteList: invalid index")`, `.expect("get: key not found")` — three deliberate,
//! message-carrying failures — and the `safeify` pass rewrote all three into an unlabelled `?`,
//! discarding the messages (`macros/src/gen/native/rust_code_rewrite.rs`). The authors' intent was
//! to *err*; the machinery silently converted it to *defer*.
//!
//! # The partition rule
//!
//! > **Err where a reason exists that the deployer must act on and that no further reduction can
//! > supply. Defer where the reason is "not yet" — where a different, already-declared rule could
//! > still fire on this redex.**
//!
//! | case | example | disposition | variant |
//! |---|---|---|---|
//! | an operand is still a redex | `*@1 + 2` | **defer** | [`Partiality::NotReduced`] |
//! | **(a)** undefined at this input | `1/0`, `at([1,2],5)`, `get({},k)` | **err**, naming the operation and the carrier | [`Partiality::Undefined`] |
//! | **(b)** not representable in this carrier | `i64::MAX + 1` | **err**, naming the carrier that did not fit | [`Partiality::NotRepresentable`] |
//! | the author declared the failure | `.expect("get: key not found")` | **err**, carrying the author's own words | [`Partiality::Declared`] |
//! | a fallible step declined and said nothing | `.unwrap()`, a `try_*` helper's `None` | **err**, and the silence is itself the report | [`Partiality::Unreported`] |
//!
//! ⚠ **Only [`Partiality::NotReduced`] is structural.** Everything else is a *semantic decline*:
//! the shape was reducible and the operation refused the input. That is exactly the partition
//! `mettail_rholang_codegen::RhoFoldDataflowDisposition::{Run, Defer, BlockedBySemanticPredicate}`
//! already draws on the Rho lane; this module carries it on the Dovetail lane, which until now
//! erased it by returning `Option<EClassId>`.
//!
//! # What this module does NOT change
//!
//! Nothing here alters a computed value or a post-state hash. A declining fold still leaves its
//! redex **unreduced**, which is the disposition the consensus lane needs: a stuck
//! `Proc::Div(a, b)` lowers to `EDivBody` and f1r3node's metered reducer decides it, whereas
//! `Proc::Err` has no Rho image at all (`rholang-runtime/src/rholang_ast.rs`'s `lower_arm_err`
//! returns `UnsupportedProc("error process")`). The decline is *recorded alongside* the deferral,
//! never *instead of* it.

use core::cell::RefCell;
use core::fmt;

// ═══════════════════════════════════════════════════════════════════════════════════════════════
// The reason vocabulary
// ═══════════════════════════════════════════════════════════════════════════════════════════════

/// Why an operation has **no value at all** at this input — case (a) of the partition rule.
///
/// Distinct from [`Partiality::NotRepresentable`], where a value exists and the carrier is too
/// small for it. `1 / 0` has no quotient in any carrier; `i64::MAX + 1` has one in `i128`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UndefinedReason {
    /// A divisor of zero. No carrier supplies a quotient.
    DivisionByZero,
    /// A modulus of zero. No carrier supplies a remainder.
    RemainderByZero,
    /// The IEEE result is `NaN` — the indeterminate form (`0.0 / 0.0`, `Inf - Inf`, `Inf / Inf`).
    ///
    /// Rejected rather than propagated because `NaN != NaN` poisons every hash key and every
    /// e-graph congruence it reaches. `±Inf` is NOT rejected: it is a legitimate element of the
    /// extended reals used by log-domain / tropical semirings.
    NotANumber,
    /// An integer raised to a negative power. The value exists in the rationals
    /// (`2^-1 = 1/2`), never in an integer carrier, and no wider integer carrier helps —
    /// so this is (a), not (b).
    NegativeExponent,
    /// The operation is not defined on this carrier at all — `bool - bool`, `String / String`.
    /// A carrier-level type error the grammar allowed to be spelled.
    NotDefinedForCarrier,
}

impl UndefinedReason {
    /// The stable discriminant token. Assertions pin THIS, never the prose of
    /// [`fmt::Display`], so rewording a message cannot silently retarget a test.
    #[inline]
    pub const fn token(self) -> &'static str {
        match self {
            Self::DivisionByZero => "DivisionByZero",
            Self::RemainderByZero => "RemainderByZero",
            Self::NotANumber => "NotANumber",
            Self::NegativeExponent => "NegativeExponent",
            Self::NotDefinedForCarrier => "NotDefinedForCarrier",
        }
    }
}

impl fmt::Display for UndefinedReason {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let prose = match self {
            Self::DivisionByZero => "division by zero",
            Self::RemainderByZero => "remainder by zero",
            Self::NotANumber => "the result is NaN",
            Self::NegativeExponent => "a negative exponent on an integer carrier",
            Self::NotDefinedForCarrier => "the operation is not defined on this carrier",
        };
        f.write_str(prose)
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════════════
// The disposition itself
// ═══════════════════════════════════════════════════════════════════════════════════════════════

/// Why a partial operation produced no value — the failure channel of [`crate::SafeArith`] and of
/// every `safeify`-rewritten `![…]` fold body.
///
/// `Copy` and 40 bytes wide: every field is a `&'static str` or a C-like discriminant, so the
/// error slot of `Result<T, Partiality>` costs no allocation and no `Drop` glue on the hot
/// saturation path. The `Declared` message is a `&'static str` because
/// `macros/src/gen/native/rust_code_rewrite.rs` bakes the author's `.expect(…)` **string
/// literal** into the generated code; a non-literal argument is refused at macro-expansion time
/// rather than silently dropped (which is the very defect this type exists to close).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Partiality {
    /// **(a)** The operation has no value at this input, in this carrier or any other.
    Undefined {
        /// The operation's short name — `"add"`, `"div"`, `"pow"`, …
        operation: &'static str,
        /// The carrier the operation ran in — `"i64"`, `"CanonicalFloat64"`, …
        carrier: &'static str,
        /// Which flavour of undefined.
        reason: UndefinedReason,
    },
    /// **(b)** The value exists; this carrier cannot hold it. `i64::MAX + 1`, `u32::MAX + 1u32`,
    /// `i64::MIN / -1`, `-i64::MIN`.
    ///
    /// ⚠ A lossless-promotion reading may still succeed on the same term — the auto-injected
    /// coercion chain (`ast/src/auto_inject.rs`) gives `UInt32 ▸ BigInt ▸ BigRat` readings that
    /// compute the value in a wider carrier. This disposition is what makes the *declining*
    /// reading visible instead of having it silently vanish from the lattice.
    NotRepresentable {
        /// The operation's short name — `"add"`, `"sub"`, `"neg"`, …
        operation: &'static str,
        /// The carrier that was too narrow — `"i64"`, `"u32"`, …
        carrier: &'static str,
    },
    /// The grammar author declared this failure and gave it words: `.expect(msg)` in a `![…]`
    /// body. The message is the author's, verbatim.
    Declared {
        /// The author's own message, e.g. `"ElemList: invalid index"`.
        message: &'static str,
    },
    /// **STRUCTURAL, never a decline.** An operand is still a redex — a `Var`-bearing or
    /// not-yet-folded child — so a *different, already-declared* rule may still fire here. The
    /// answer is "not yet", which is precisely what a deferral means.
    NotReduced,
    /// A fallible step declined without stating a reason: a bare `.unwrap()`, or a body whose
    /// tail expression is an `Option` that came back `None`.
    ///
    /// Recorded as a decline rather than swallowed, because the silence is the finding: every
    /// `Unreported` in a run names a site whose vocabulary is still missing.
    Unreported,
}

impl Partiality {
    /// The stable discriminant token — the finest one available. Assertions pin THIS.
    ///
    /// `Undefined` reports its inner [`UndefinedReason`] (`"DivisionByZero"`), so (a) and (b)
    /// can never collide on one token.
    #[inline]
    pub const fn reason_token(&self) -> &'static str {
        match self {
            Self::Undefined { reason, .. } => reason.token(),
            Self::NotRepresentable { .. } => "NotRepresentable",
            Self::Declared { .. } => "Declared",
            Self::NotReduced => "NotReduced",
            Self::Unreported => "Unreported",
        }
    }

    /// The carrier the operation ran in, when one is known.
    #[inline]
    pub const fn carrier(&self) -> Option<&'static str> {
        match self {
            Self::Undefined { carrier, .. } | Self::NotRepresentable { carrier, .. } => {
                Some(carrier)
            },
            Self::Declared { .. } | Self::NotReduced | Self::Unreported => None,
        }
    }

    /// The operation's short name, when one is known.
    #[inline]
    pub const fn operation(&self) -> Option<&'static str> {
        match self {
            Self::Undefined { operation, .. } | Self::NotRepresentable { operation, .. } => {
                Some(operation)
            },
            Self::Declared { .. } | Self::NotReduced | Self::Unreported => None,
        }
    }

    /// The author's declared message, when there is one.
    #[inline]
    pub const fn message(&self) -> Option<&'static str> {
        match self {
            Self::Declared { message } => Some(message),
            _ => None,
        }
    }

    /// ★ THE PARTITION. `true` for a **semantic decline** — the shape was reducible and the
    /// operation refused this input, so the deployer has something to act on. `false` for the one
    /// **structural** case, where the answer is "not yet" and a later reduction may supply it.
    #[inline]
    pub const fn is_decline(&self) -> bool {
        !matches!(self, Self::NotReduced)
    }
}

impl fmt::Display for Partiality {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Undefined {
                operation,
                carrier,
                reason,
            } => write!(f, "`{operation}` on `{carrier}` is undefined here: {reason}"),
            Self::NotRepresentable { operation, carrier } => write!(
                f,
                "the result of `{operation}` is not representable in `{carrier}`",
            ),
            Self::Declared { message } => write!(f, "{message}"),
            Self::NotReduced => f.write_str("an operand is still a redex"),
            Self::Unreported => f.write_str("declined without stating a reason"),
        }
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════════════
// The three-valued fold disposition
// ═══════════════════════════════════════════════════════════════════════════════════════════════

/// ★★ The THREE-VALUED outcome of running ONE declared `![…]` fold body on ONE redex.
///
/// Until this type existed the generated dispatcher answered `Option<EClassId>`, and `None` meant
/// **both** "no rule applies here" and "the operation declined this input". Those are different
/// findings and a report that conflates them can only say "already a normal form".
///
/// The shape is copied deliberately from
/// `mettail_rholang_codegen::RhoFoldDataflowDisposition::{Run, Defer, BlockedBySemanticPredicate}`,
/// which answers this exact question one lane away: *"`Defer` means the shape is not fully
/// Rho-lowerable … `BlockedBySemanticPredicate` means the shape is Rho-lowerable, but a semantic
/// predicate such as safe arithmetic declined it."*
///
/// ⚠ `Declined` and `Defer` both contribute **nothing** to the e-graph — they differ only in what
/// gets recorded. That is what keeps this change additive: no computed value moves.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FoldDisposition<T> {
    /// The body computed a value; the fold fires.
    Ran(T),
    /// STRUCTURAL: nothing to run yet. The redex is left in place for a later iteration.
    Defer,
    /// SEMANTIC: the operation refused this input and named the reason. The redex is left in
    /// place — but the reason is recorded.
    Declined(Partiality),
}

/// Classify a fold body's `Result` into the three-valued disposition.
///
/// This is the ONE place the (a)/(b)/declared/unreported ⟶ *decline* and not-reduced ⟶ *defer*
/// partition is applied, so it cannot drift between the emission sites.
#[inline]
pub fn classify<T>(outcome: Result<T, Partiality>) -> FoldDisposition<T> {
    match outcome {
        Ok(value) => FoldDisposition::Ran(value),
        Err(partiality) if partiality.is_decline() => FoldDisposition::Declined(partiality),
        Err(_) => FoldDisposition::Defer,
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════════════
// The record and its sink
// ═══════════════════════════════════════════════════════════════════════════════════════════════

/// One aggregated finding: a declared fold body DECLINED, and why.
///
/// ⚠ **Aggregated, exactly like `RuntimeDovetailRuleFiring`.** Equality saturation re-dispatches a
/// surviving redex on every iteration, so `6 / 0` declines once per iteration. One record per
/// distinct `(label, partiality)` carrying a `count` is therefore the only shape in which "how
/// many distinct declines did this run produce" is a stable question.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeclinedFold {
    /// The fold rule's published label — `"Calculator::fold::Int_DivInt"`. The same string the
    /// rule's firing would carry, so a decline and a firing are comparable by name.
    pub label: String,
    /// Why the body declined.
    pub partiality: Partiality,
    /// How many times this exact `(label, partiality)` pair declined during the run.
    pub count: usize,
}

impl DeclinedFold {
    /// The stable discriminant token — see [`Partiality::reason_token`].
    #[inline]
    pub const fn reason_token(&self) -> &'static str {
        self.partiality.reason_token()
    }

    /// The carrier the operation ran in, when one is known.
    #[inline]
    pub const fn carrier(&self) -> Option<&'static str> {
        self.partiality.carrier()
    }

    /// The operation's short name, when one is known.
    #[inline]
    pub const fn operation(&self) -> Option<&'static str> {
        self.partiality.operation()
    }

    /// The author's declared message, when there is one.
    #[inline]
    pub const fn message(&self) -> Option<&'static str> {
        self.partiality.message()
    }
}

impl fmt::Display for DeclinedFold {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} declined: {}", self.label, self.partiality)?;
        if self.count > 1 {
            write!(f, " (×{})", self.count)?;
        }
        Ok(())
    }
}

/// The collector the generated dispatcher writes declines into.
///
/// # Why `RefCell` and not an atomic
///
/// `dovetail::rules::NativeDispatch` is a `dyn Fn` — not `FnMut` — because the engine hands it
/// `&mut EGraph` and cannot also hand out a unique borrow of the dispatcher. Saturation is
/// single-threaded **by construction** (`saturate_compiled_with_native(&mut self, …)` holds the
/// only `&mut` to the graph for the whole run), so the cheapest correct interior mutability is a
/// `RefCell`. Every borrow here is a straight-line push with no reentrancy: `record` neither calls
/// back into the dispatcher nor holds the borrow across a call.
#[derive(Debug, Default)]
pub struct DeclineSink {
    records: RefCell<Vec<DeclinedFold>>,
}

impl DeclineSink {
    /// An empty sink.
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    /// Record one decline, aggregating into the existing `(label, partiality)` record when one is
    /// already present.
    ///
    /// ⚠ A [`Partiality::NotReduced`] is **structural** and is dropped here rather than recorded:
    /// a term that does not fold because an operand is still a redex has declined nothing. That
    /// refusal is the load-bearing control of the whole change — without it, every non-firing
    /// rule would look like a decline.
    pub fn record(&self, label: &str, partiality: Partiality) {
        if !partiality.is_decline() {
            return;
        }
        let mut records = self.records.borrow_mut();
        if let Some(existing) = records
            .iter_mut()
            .find(|r| r.partiality == partiality && r.label == label)
        {
            existing.count += 1;
            return;
        }
        records.push(DeclinedFold {
            label: label.to_string(),
            partiality,
            count: 1,
        });
    }

    /// Drain the collected records in first-encounter order.
    pub fn take(&self) -> Vec<DeclinedFold> {
        core::mem::take(&mut *self.records.borrow_mut())
    }

    /// How many distinct `(label, partiality)` records have been collected.
    pub fn len(&self) -> usize {
        self.records.borrow().len()
    }

    /// Whether nothing has declined.
    pub fn is_empty(&self) -> bool {
        self.records.borrow().is_empty()
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════════════
// The rewrite-pass helpers — what `safeify` emits
// ═══════════════════════════════════════════════════════════════════════════════════════════════

/// A value a `![…]` body may `.expect(msg)` / `.unwrap()`: `Option<T>` or `Result<T, E>`.
///
/// `safeify` rewrites both to a `Partiality`-carrying `Result` so the author's declared failure
/// survives into the run report instead of becoming an unlabelled `?`.
pub trait Declarable {
    /// The value the author expected to be there.
    type Value;

    /// The author wrote `.expect(message)`. Carry the message.
    fn declared(self, message: &'static str) -> Result<Self::Value, Partiality>;

    /// The author wrote `.unwrap()`. There is no message to carry, and that silence is the
    /// report — see [`Partiality::Unreported`].
    fn unwrapped(self) -> Result<Self::Value, Partiality>;
}

impl<T> Declarable for Option<T> {
    type Value = T;

    #[inline]
    fn declared(self, message: &'static str) -> Result<T, Partiality> {
        self.ok_or(Partiality::Declared { message })
    }

    #[inline]
    fn unwrapped(self) -> Result<T, Partiality> {
        self.ok_or(Partiality::Unreported)
    }
}

impl<T, E> Declarable for Result<T, E> {
    type Value = T;

    #[inline]
    fn declared(self, message: &'static str) -> Result<T, Partiality> {
        self.map_err(|_| Partiality::Declared { message })
    }

    #[inline]
    fn unwrapped(self) -> Result<T, Partiality> {
        self.map_err(|_| Partiality::Unreported)
    }
}

/// A child term that has not reduced yet — the STRUCTURAL case. Emitted by `safeify` for
/// `x.eval()` ⟶ `not_reduced(x.try_eval())?`.
#[inline]
pub fn not_reduced<T>(value: Option<T>) -> Result<T, Partiality> {
    value.ok_or(Partiality::NotReduced)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// ★ (a) and (b) must never collide on one token — the whole point of the split.
    #[test]
    fn undefined_and_not_representable_have_disjoint_tokens() {
        let undefined = Partiality::Undefined {
            operation: "div",
            carrier: "i64",
            reason: UndefinedReason::DivisionByZero,
        };
        let overflow = Partiality::NotRepresentable {
            operation: "add",
            carrier: "i64",
        };
        assert_eq!(undefined.reason_token(), "DivisionByZero");
        assert_eq!(overflow.reason_token(), "NotRepresentable");
        assert_ne!(undefined.reason_token(), overflow.reason_token());
        assert_eq!(undefined.carrier(), Some("i64"));
        assert_eq!(overflow.carrier(), Some("i64"));
    }

    /// ★ THE PARTITION: exactly one variant is structural.
    #[test]
    fn only_not_reduced_is_structural() {
        assert!(!Partiality::NotReduced.is_decline());
        assert!(Partiality::Unreported.is_decline());
        assert!(Partiality::Declared { message: "m" }.is_decline());
        assert!(Partiality::NotRepresentable {
            operation: "add",
            carrier: "i64"
        }
        .is_decline());
        assert!(Partiality::Undefined {
            operation: "div",
            carrier: "i64",
            reason: UndefinedReason::DivisionByZero,
        }
        .is_decline());
    }

    /// ★ THE CONTROL that the whole change rests on: a structural deferral records NOTHING.
    #[test]
    fn a_structural_deferral_is_not_recorded() {
        let sink = DeclineSink::new();
        sink.record("L::fold::X", Partiality::NotReduced);
        assert!(sink.is_empty(), "a not-yet operand is not a decline");
        sink.record("L::fold::X", Partiality::Unreported);
        assert_eq!(sink.len(), 1, "a reasonless decline IS a decline");
    }

    /// Repeated declines of the same `(label, partiality)` aggregate into one record, because
    /// saturation re-dispatches a surviving redex once per iteration.
    #[test]
    fn repeated_declines_aggregate_into_one_counted_record() {
        let sink = DeclineSink::new();
        let partiality = Partiality::Undefined {
            operation: "div",
            carrier: "i64",
            reason: UndefinedReason::DivisionByZero,
        };
        for _ in 0..7 {
            sink.record("Calculator::fold::Int_DivInt", partiality);
        }
        let records = sink.take();
        assert_eq!(records.len(), 1, "{records:?}");
        assert_eq!(records[0].count, 7);
        assert_eq!(records[0].label, "Calculator::fold::Int_DivInt");
        assert_eq!(records[0].reason_token(), "DivisionByZero");
        assert!(sink.is_empty(), "`take` drains");
    }

    /// Two DIFFERENT reasons under one label stay two records — aggregation is by pair, not by
    /// label, or a carrier overflow would hide behind a division by zero.
    #[test]
    fn distinct_reasons_under_one_label_stay_distinct() {
        let sink = DeclineSink::new();
        sink.record(
            "L::fold::X",
            Partiality::Undefined {
                operation: "div",
                carrier: "i64",
                reason: UndefinedReason::DivisionByZero,
            },
        );
        sink.record(
            "L::fold::X",
            Partiality::NotRepresentable {
                operation: "div",
                carrier: "i64",
            },
        );
        assert_eq!(sink.len(), 2);
    }

    /// `classify` is the ONE place the partition is applied.
    #[test]
    fn classify_routes_structural_to_defer_and_semantic_to_declined() {
        assert_eq!(classify::<i64>(Ok(3)), FoldDisposition::Ran(3));
        assert_eq!(
            classify::<i64>(Err(Partiality::NotReduced)),
            FoldDisposition::Defer,
        );
        assert_eq!(
            classify::<i64>(Err(Partiality::Declared { message: "boom" })),
            FoldDisposition::Declined(Partiality::Declared { message: "boom" }),
        );
    }

    /// ★ The author's message survives — both from an `Option` and from a `Result`.
    #[test]
    fn a_declared_message_survives_from_both_carriers() {
        let from_option: Result<i32, Partiality> =
            Declarable::declared(None::<i32>, "get: key not found");
        assert_eq!(
            from_option.unwrap_err().message(),
            Some("get: key not found"),
        );
        let from_result: Result<i32, Partiality> =
            Declarable::declared(Err::<i32, &str>("inner"), "ElemList: invalid index");
        assert_eq!(
            from_result.unwrap_err().message(),
            Some("ElemList: invalid index"),
        );
    }

    /// `.unwrap()` has no message, and `Unreported` says exactly that.
    #[test]
    fn unwrap_declines_without_a_message() {
        let declined: Result<i32, Partiality> = Declarable::unwrapped(None::<i32>);
        assert_eq!(declined.unwrap_err(), Partiality::Unreported);
        assert_eq!(declined.unwrap_err().message(), None);
    }

    /// `not_reduced` is the STRUCTURAL constructor — it must not produce a decline.
    #[test]
    fn not_reduced_is_structural() {
        let deferred: Result<i32, Partiality> = not_reduced(None);
        assert_eq!(deferred.unwrap_err(), Partiality::NotReduced);
        assert!(!deferred.unwrap_err().is_decline());
        assert_eq!(not_reduced(Some(9)), Ok(9));
    }

    /// The error slot stays small and allocation-free on the hot path.
    #[test]
    fn the_error_slot_is_copy_and_narrow() {
        // `&'static str` × 2 + a byte discriminant + the outer tag, rounded to alignment.
        assert!(
            core::mem::size_of::<Partiality>() <= 40,
            "Partiality grew to {} bytes — it sits in the error slot of every `safe_*` call",
            core::mem::size_of::<Partiality>(),
        );
        // A compile-time witness that it is `Copy` (a moved-from value stays usable).
        let p = Partiality::NotReduced;
        let _first = p;
        let _second = p;
    }
}
