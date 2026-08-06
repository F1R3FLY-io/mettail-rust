//! Guard decidability analysis for generated language tests.
//!
//! Wraps `mettail_prattail::symbolic::{classify_decidability,
//! classify_decidability_sorted}` to classify a language's guards by
//! decidability tier (T1..T4).
//!
//! ## Structural vs. behavioral guards (OSLF substrate Phase 1 `.1`)
//!
//! Guards in MeTTaIL control dispatch — which rewrite rule or parsing path to
//! take based on a runtime condition. They split into two kinds with **very
//! different** decidability foundations, and this module routes each kind to its
//! true tier instead of flattening everything into an opaque `Atom` (the prior
//! behavior, which collapsed every guard to T1):
//!
//! - **Structural guards** are *data-sort type assertions*: a term constructor
//!   field `f : T` (over a data sort `T` such as `Int`, `Float`, `Str`,
//!   `BigRat`, …) implicitly guards that the value in that position inhabits the
//!   sort `T`. These are decided by the **EBA-backed sorted classifier**
//!   ([`classify_decidability_sorted`]): when `T` resolves to a registry-resident
//!   scalar [`Sort`], the deciding effective Boolean algebra has a *terminating*
//!   SAT/witness procedure, so the guard is **compile-time decidable (T1)**. A
//!   field whose category has no scalar native type (a process category, a
//!   collection container, a user ADT) carries a non-scalar sentinel sort that is
//!   absent from the scalar registry; the classifier then falls back to the
//!   untyped structural classifier on the predicate skeleton — and because the
//!   structural guard's predicate is `AnyPred::True` (a pure, ground-decidable
//!   type assertion), that fallback is **also T1**. Either way, a structural
//!   guard is T1, which is *sound* precisely because it is backed by the EBA's
//!   decidable core (see `formal/rocq/symbolic_algebra/theories/
//!   GuardTierClassificationSound.v`).
//!
//! - **Behavioral guards** are *side conditions on the rewrite relation*, not on
//!   any data sort. There are three: **freshness** conditions (`x # P` — "`x` is
//!   fresh for `P`"); **congruence premises** (`S ~> T` — "if `S` rewrites to
//!   `T`"); and **binder freshness** (a binder field `^x. body` carries an
//!   implicit freshness obligation on `x`). None of these is decided by a scalar
//!   algebra: each references the rewrite / reduction relation (or
//!   α-equivalence), so it is modeled as a relational behavioral predicate
//!   [`BehavioralFormula::Relation`] and classified by the `algebra_tower`-backed
//!   [`BehavioralFormula::decidability_tier`], landing at **runtime-decidable
//!   (T2)** — decidable once the relation is populated, but not at compile time.
//!
//! (OSLF Phase 3 wired this: behavioral guards now route through the
//! `algebra_tower`-backed [`BehavioralFormula::decidability_tier`], which lands
//! relational guards at T2 — every current behavioral guard, as here — and
//! modal/temporal guards (once Phase 5's surface syntax lands them) at
//! semi-decidable T3, never below. The routing soundness — anything classified
//! `≤ T2` is non-modal, hence handled completely by the relational runtime
//! evaluator — is proven in
//! `formal/rocq/symbolic_algebra/theories/BehavioralTierClassificationSound.v`.)
//!
//! The final summary folds both kinds into one `T1/T2/T3/T4` tally (the
//! `worst_tier` is the weakest tier present — `tier_max` in the certificate
//! lattice). A language with no freshness/premise/binder guards (e.g. a
//! pure-arithmetic grammar) is therefore **all-T1**; a language with binders or
//! congruence rules surfaces those obligations at **T2**.

use mettail_prattail::any_algebra::{AnyPred, Sort, SortRegistry, SortedGuard};
use mettail_prattail::behavioral_algebra::{Arg, BehavioralFormula};
use mettail_prattail::symbolic::{classify_decidability_sorted, DecidabilityTier};
use mettail_runtime::LanguageMetadata;

/// Result of guard decidability analysis on a language.
#[derive(Debug)]
pub struct GuardResult {
    /// Total number of guards analyzed.
    pub total_guards: usize,
    /// Number of guards that are compile-time decidable (T1).
    pub compile_time_decidable: usize,
    /// Number of guards that are runtime decidable (T2).
    pub runtime_decidable: usize,
    /// Number of guards that are semi-decidable (T3).
    pub semi_decidable: usize,
    /// Number of guards that are undecidable (T4).
    pub undecidable: usize,
    /// The highest (worst) decidability tier found among all guards.
    pub worst_tier: String,
    /// Human-readable summary.
    pub summary: String,
}

/// Conservative bounds for the scalar [`SortRegistry`].
///
/// `IntervalAlgebra::new` requires `min < max`; these bounds satisfy that and
/// are otherwise immaterial — a *structural* guard's predicate is `AnyPred::True`
/// (a type assertion), so its tier depends only on whether the field's sort is
/// registry-resident, never on the interval extent. We use a wide-but-finite
/// window so the registry is well-formed.
const REGISTRY_INT_LO: i64 = i64::MIN / 2;
const REGISTRY_INT_HI: i64 = i64::MAX / 2;

/// Map a scalar **native-type string** (the `TypeDef::native_type` the macro
/// emits, e.g. `"i32"`, `"f64"`, `"bool"`, `"mettail_runtime :: CanonicalBigRat"`)
/// to the carrier [`Sort`] that decides it, or `None` for a non-scalar / unknown
/// native type.
///
/// This is a **local mirror** of [`mettail_prattail::any_algebra::sort_of_native`]
/// composed with [`mettail_ast::language::NativeKind::from_syn_type`] — the
/// *source of truth* for native-type → sort classification. We re-implement the
/// last-segment match here (rather than depend on it) because testkit must NOT
/// pull in `mettail-ast`, and the `any_algebra` mirror is gated behind the
/// `any-algebra-carrier` feature. The match keys off the **last `::`/whitespace
/// segment** exactly as `NativeKind::from_syn_type` keys off the last `syn` path
/// segment (`metadata.rs` renders the type via `quote!`, which spaces `::` as
/// `" :: "`, so the last segment is the bare ident regardless of the leading
/// path). Any change to `NativeKind::from_syn_type` MUST be reflected here.
fn sort_of_native_type_str(native: &str) -> Option<Sort> {
    // Last path/whitespace segment, mirroring `Type::Path::segments.last()`.
    // `quote!` renders `mettail_runtime::CanonicalBigRat` as
    // `"mettail_runtime :: CanonicalBigRat"`, so splitting on whitespace and `:`
    // and taking the final non-empty token yields the bare ident.
    let seg = native
        .split(|c: char| c.is_whitespace() || c == ':')
        .rfind(|s| !s.is_empty())?;

    match seg {
        // Bounded-integer widths all collapse to the `Sort::Int` universe.
        "i8" | "i16" | "i32" | "i64" | "i128" | "isize" | "u8" | "u16" | "u32" | "u64" | "u128"
        | "usize" => Some(Sort::Int),
        "f32" | "f64" => Some(Sort::Float),
        "bool" => Some(Sort::Bool),
        "str" | "String" => Some(Sort::Str),
        "CanonicalBigRat" => Some(Sort::BigRat),
        "CanonicalFixedPoint" => Some(Sort::Fixed),
        // `NativeKind::from_syn_type`: any wrapper whose last segment ends with
        // `"BigInt"` is the arbitrary-precision integer category.
        other if other.ends_with("BigInt") => Some(Sort::BigInt),
        // Custom wrappers, collection containers (`Vec`, `HashBag`, `HashMap`),
        // user ADTs (process categories) — no scalar sort.
        _ => None,
    }
}

/// Resolve a constructor field's declared category name (`FieldDef::ty`, e.g.
/// `"Int"`, `"Vec(Proc)"`, `"Option<Int>"`) to its scalar [`Sort`] via the
/// language's `name → native_type` table, or `None` when it has no scalar sort.
///
/// `FieldDef::ty` is a **category name**, not a native Rust type; the scalar
/// native type is one indirection away through `metadata.types()`
/// (`TypeDef { name, native_type }`). A leading `Option<…>` wrapper (emitted for
/// opt-group fields) is stripped first so the inner category drives the sort.
fn field_category_sort(
    field_ty: &str,
    native_by_category: &[(&str, Option<&str>)],
) -> Option<Sort> {
    // Strip a single leading `Option<…>` wrapper to reach the inner category.
    let inner = field_ty
        .strip_prefix("Option<")
        .and_then(|rest| rest.strip_suffix('>'))
        .unwrap_or(field_ty);

    let native = native_by_category
        .iter()
        .find(|(name, _)| *name == inner)
        .and_then(|(_, nt)| *nt)?;
    sort_of_native_type_str(native)
}

/// Check guard decidability for a language.
///
/// Classifies each of the language's guards **by source** into a single
/// `T1/T2/T3/T4` tally:
///
/// - **Structural (c)** — every non-binder, non-`Guard` constructor field is a
///   data-sort type assertion. Its sort is resolved through the
///   `category → native_type` table; a scalar sort yields
///   `SortedGuard { sort, pred: AnyPred::True }` tiered by the EBA-backed
///   [`classify_decidability_sorted`] (registry-resident scalar ⇒ T1), and a
///   non-scalar category yields the same `True` predicate over a sentinel sort
///   that the scalar registry never holds, so the classifier's fallback fires
///   and likewise returns T1.
/// - **Behavioral (a, b, d)** — rewrite freshness conditions, congruence
///   premises, and binder freshness become relational behavioral predicates
///   [`BehavioralFormula::Relation`] tiered by the `algebra_tower`-backed
///   [`BehavioralFormula::decidability_tier`] (⇒ T2).
///
/// # Arguments
/// * `metadata` -- static language metadata providing rewrite and term definitions
///
/// # Returns
/// A `GuardResult` summarizing the decidability classification.
pub fn check_guard_decidability(metadata: &dyn LanguageMetadata) -> GuardResult {
    let rewrites = metadata.rewrites();
    let terms = metadata.terms();
    let types = metadata.types();

    // The scalar EBA registry the structural classifier consults: a
    // registry-resident sort is decided by a terminating SAT/witness procedure.
    let registry = SortRegistry::scalars(REGISTRY_INT_LO, REGISTRY_INT_HI, Vec::new());

    // `category name → native_type` table (e.g. `"Int" → Some("i32")`,
    // `"Proc" → None`). Built once; structural-field sort resolution looks up
    // `FieldDef::ty` here.
    let native_by_category: Vec<(&str, Option<&str>)> =
        types.iter().map(|t| (t.name, t.native_type)).collect();

    // One shared tally across both guard kinds.
    let mut compile_time = 0usize;
    let mut runtime = 0usize;
    let mut semi = 0usize;
    let mut undecidable = 0usize;
    let mut total = 0usize;
    let mut worst = DecidabilityTier::CompileTimeDecidable;

    let mut tally = |tier: DecidabilityTier| {
        total += 1;
        match tier {
            DecidabilityTier::CompileTimeDecidable => compile_time += 1,
            DecidabilityTier::RuntimeDecidable => runtime += 1,
            DecidabilityTier::SemiDecidable => semi += 1,
            DecidabilityTier::Undecidable => undecidable += 1,
        }
        if tier > worst {
            worst = tier;
        }
    };

    // ── Behavioral (a): rewrite freshness conditions ────────────────────────
    // Each condition `x # P` is a freshness side-condition on the reduction
    // relation → a relational atom, runtime-decidable (T2).
    for rw in rewrites {
        for &condition in rw.conditions {
            let formula = BehavioralFormula::Relation {
                name: "fresh".to_string(),
                args: vec![Arg::Var(condition.to_string())],
            };
            tally(formula.decidability_tier());
        }

        // ── Behavioral (b): congruence premise `(S, T)` = "if S ~> T" ────────
        if let Some((premise_lhs, premise_rhs)) = rw.premise {
            let formula = BehavioralFormula::Relation {
                name: "rewrites".to_string(),
                args: vec![Arg::Var(premise_lhs.to_string()), Arg::Var(premise_rhs.to_string())],
            };
            tally(formula.decidability_tier());
        }
    }

    // ── Structural (c) + Behavioral (d) over term-constructor fields ────────
    for term_def in terms {
        for field in term_def.fields {
            if field.is_binder {
                // Behavioral (d): a binder field carries an implicit freshness
                // obligation on the bound variable → relational atom, T2.
                let formula = BehavioralFormula::Relation {
                    name: "fresh_binder".to_string(),
                    args: vec![Arg::Var(field.name.to_string())],
                };
                tally(formula.decidability_tier());
                continue;
            }

            // A `?guard:Guard` slot is the guard body itself, not a data-sort
            // type assertion — it is the *carrier* of behavioral predicates, not
            // a structural guard, so it is not tallied as a structural field.
            if field.ty == "Guard" || field.ty == "Option<Guard>" {
                continue;
            }

            // Structural (c): a data-sort type assertion. Resolve the field's
            // scalar sort (None ⇒ non-scalar sentinel so the registry-fallback
            // fires) and tier it via the EBA-backed sorted classifier.
            let sort = field_category_sort(field.ty, &native_by_category).unwrap_or(
                // Non-scalar sentinel: the scalar registry never holds
                // `Sort::Tree`, so `classify_decidability_sorted` falls back to
                // the structural classifier on the `True` skeleton (⇒ T1).
                Sort::Tree,
            );
            let sg = SortedGuard { sort, pred: AnyPred::True };
            tally(classify_decidability_sorted(&sg, &registry));
        }
    }

    if total == 0 {
        return GuardResult {
            total_guards: 0,
            compile_time_decidable: 0,
            runtime_decidable: 0,
            semi_decidable: 0,
            undecidable: 0,
            worst_tier: "N/A".to_string(),
            summary: format!(
                "{}: no guards found, decidability analysis trivially empty",
                metadata.name()
            ),
        };
    }

    let worst_str = format!("{}", worst);

    GuardResult {
        total_guards: total,
        compile_time_decidable: compile_time,
        runtime_decidable: runtime,
        semi_decidable: semi,
        undecidable,
        worst_tier: worst_str.clone(),
        summary: format!(
            "{}: guard decidability (total: {}, T1: {}, T2: {}, T3: {}, T4: {}, worst: {})",
            metadata.name(),
            total,
            compile_time,
            runtime,
            semi,
            undecidable,
            worst_str,
        ),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_prattail::any_algebra::Sort;
    use mettail_runtime::{EquationDef, FieldDef, RewriteDef, TermDef, TypeDef};

    // ── Local native-type matcher mirrors NativeKind::from_syn_type ──────────

    #[test]
    fn native_matcher_mirrors_nativekind_scalars() {
        // Bounded-integer widths all collapse to Int.
        for s in [
            "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128", "usize",
        ] {
            assert_eq!(sort_of_native_type_str(s), Some(Sort::Int), "{s}");
        }
        assert_eq!(sort_of_native_type_str("f32"), Some(Sort::Float));
        assert_eq!(sort_of_native_type_str("f64"), Some(Sort::Float));
        assert_eq!(sort_of_native_type_str("bool"), Some(Sort::Bool));
        assert_eq!(sort_of_native_type_str("str"), Some(Sort::Str));
        assert_eq!(sort_of_native_type_str("String"), Some(Sort::Str));
        assert_eq!(sort_of_native_type_str("CanonicalBigRat"), Some(Sort::BigRat));
        assert_eq!(sort_of_native_type_str("CanonicalFixedPoint"), Some(Sort::Fixed));
        // `…BigInt` suffix rule.
        assert_eq!(sort_of_native_type_str("CanonicalBigInt"), Some(Sort::BigInt));
    }

    #[test]
    fn native_matcher_keys_off_last_path_segment() {
        // `quote!` renders `mettail_runtime::CanonicalBigRat` with spaced `::`.
        assert_eq!(
            sort_of_native_type_str("mettail_runtime :: CanonicalBigRat"),
            Some(Sort::BigRat)
        );
        assert_eq!(
            sort_of_native_type_str("mettail_runtime :: CanonicalBigInt"),
            Some(Sort::BigInt)
        );
        assert_eq!(
            sort_of_native_type_str("mettail_runtime :: CanonicalFixedPoint"),
            Some(Sort::Fixed)
        );
        // Non-scalar containers / user ADTs → None.
        assert_eq!(sort_of_native_type_str("Vec < Proc >"), None);
        assert_eq!(sort_of_native_type_str("mettail_runtime :: HashBag < Proc >"), None);
        assert_eq!(sort_of_native_type_str("HashMap < Proc , Proc >"), None);
        assert_eq!(sort_of_native_type_str("MyCustomWrapper"), None);
    }

    #[test]
    fn field_category_sort_strips_option_wrapper_and_resolves_via_table() {
        let table: Vec<(&str, Option<&str>)> = vec![
            ("Int", Some("i32")),
            ("BigRat", Some("mettail_runtime :: CanonicalBigRat")),
            ("Proc", None),
            ("List", Some("Vec < Proc >")),
        ];
        assert_eq!(field_category_sort("Int", &table), Some(Sort::Int));
        assert_eq!(field_category_sort("Option<Int>", &table), Some(Sort::Int));
        assert_eq!(field_category_sort("BigRat", &table), Some(Sort::BigRat));
        // Non-scalar native type → None.
        assert_eq!(field_category_sort("List", &table), None);
        // Category with no native type → None.
        assert_eq!(field_category_sort("Proc", &table), None);
        // Unknown category → None.
        assert_eq!(field_category_sort("Nonexistent", &table), None);
    }

    // ── Hand-written metadata to drive `check_guard_decidability` ────────────

    /// A minimal, fully hand-authored `LanguageMetadata`. The fields are chosen
    /// to exercise every routing branch: scalar structural (Int), non-scalar
    /// structural (Proc), a binder field, a `Guard` slot (excluded), a freshness
    /// rewrite condition, and a congruence premise.
    struct ProbeMeta {
        terms: &'static [TermDef],
        rewrites: &'static [RewriteDef],
    }

    static PROBE_TYPES: &[TypeDef] = &[
        TypeDef {
            name: "Proc",
            native_type: None,
            is_primary: true,
        },
        TypeDef {
            name: "Name",
            native_type: None,
            is_primary: false,
        },
        TypeDef {
            name: "Int",
            native_type: Some("i32"),
            is_primary: false,
        },
    ];

    impl LanguageMetadata for ProbeMeta {
        fn name(&self) -> &'static str {
            "Probe"
        }
        fn types(&self) -> &'static [TypeDef] {
            PROBE_TYPES
        }
        fn terms(&self) -> &'static [TermDef] {
            self.terms
        }
        fn equations(&self) -> &'static [EquationDef] {
            &[]
        }
        fn rewrites(&self) -> &'static [RewriteDef] {
            self.rewrites
        }
    }

    fn fld(name: &'static str, ty: &'static str, is_binder: bool) -> FieldDef {
        FieldDef { name, ty, is_binder }
    }

    #[test]
    fn empty_language_is_trivially_empty() {
        let m = ProbeMeta { terms: &[], rewrites: &[] };
        let r = check_guard_decidability(&m);
        assert_eq!(r.total_guards, 0);
        assert_eq!(r.worst_tier, "N/A");
    }

    #[test]
    fn scalar_structural_field_is_t1() {
        // One Int field ⇒ one structural T1 guard, nothing else.
        static TERMS: &[TermDef] = &[TermDef {
            name: "CastInt",
            type_name: "Proc",
            syntax: "k",
            description: None,
            fields: &[FieldDef { name: "k", ty: "Int", is_binder: false }],
        }];
        let m = ProbeMeta { terms: TERMS, rewrites: &[] };
        let r = check_guard_decidability(&m);
        assert_eq!((r.total_guards, r.compile_time_decidable, r.runtime_decidable), (1, 1, 0));
        assert_eq!(r.worst_tier, "T1 (compile-time decidable)");
    }

    #[test]
    fn nonscalar_structural_field_is_t1_via_fallback() {
        // A `Proc` field has no scalar native type → sentinel sort → registry
        // fallback on the `True` skeleton → still T1.
        static TERMS: &[TermDef] = &[TermDef {
            name: "PWrap",
            type_name: "Proc",
            syntax: "p",
            description: None,
            fields: &[FieldDef { name: "p", ty: "Proc", is_binder: false }],
        }];
        let m = ProbeMeta { terms: TERMS, rewrites: &[] };
        let r = check_guard_decidability(&m);
        assert_eq!((r.total_guards, r.compile_time_decidable, r.runtime_decidable), (1, 1, 0));
        assert_eq!(r.worst_tier, "T1 (compile-time decidable)");
    }

    #[test]
    fn binder_field_is_t2_and_never_structural() {
        // R1 containment: a binder field is behavioral (T2), never structural.
        static TERMS: &[TermDef] = &[TermDef {
            name: "Lam",
            type_name: "Proc",
            syntax: "^x.body",
            description: None,
            fields: &[
                FieldDef {
                    name: "^x.body",
                    ty: "[Proc -> Proc]",
                    is_binder: true,
                },
                FieldDef { name: "k", ty: "Int", is_binder: false },
            ],
        }];
        let m = ProbeMeta { terms: TERMS, rewrites: &[] };
        let r = check_guard_decidability(&m);
        // 1 binder (T2) + 1 Int structural (T1).
        assert_eq!((r.total_guards, r.compile_time_decidable, r.runtime_decidable), (2, 1, 1));
        assert_eq!(r.worst_tier, "T2 (runtime decidable)");
    }

    #[test]
    fn guard_slot_field_is_excluded_from_structural_tally() {
        // A `?guard:Guard` slot is the guard-body carrier, not a data-sort
        // assertion, so it contributes NOTHING to the structural tally.
        static TERMS: &[TermDef] = &[TermDef {
            name: "PGuardedInput",
            type_name: "Proc",
            syntax: "?guard",
            description: None,
            fields: &[
                FieldDef {
                    name: "?guard",
                    ty: "Guard",
                    is_binder: false,
                },
                FieldDef {
                    name: "?opt",
                    ty: "Option<Guard>",
                    is_binder: false,
                },
                FieldDef { name: "n", ty: "Name", is_binder: false },
            ],
        }];
        let m = ProbeMeta { terms: TERMS, rewrites: &[] };
        let r = check_guard_decidability(&m);
        // Only `n:Name` is structural; both Guard slots excluded; no behavioral.
        assert_eq!((r.total_guards, r.compile_time_decidable, r.runtime_decidable), (1, 1, 0));
    }

    #[test]
    fn freshness_condition_and_congruence_premise_are_t2() {
        // A congruence rewrite with a freshness condition: the condition string
        // and the congruence premise are both behavioral (T2).
        static REWRITES: &[RewriteDef] = &[RewriteDef {
            name: Some("ParCong"),
            conditions: &["x # rest"],
            premise: Some(("S", "T")),
            lhs: "(PPar {S, ...rest})",
            rhs: "(PPar {T, ...rest})",
            is_guarded: false,
        }];
        let m = ProbeMeta { terms: &[], rewrites: REWRITES };
        let r = check_guard_decidability(&m);
        // 1 freshness condition + 1 congruence premise ⇒ 2 × T2.
        assert_eq!((r.total_guards, r.compile_time_decidable, r.runtime_decidable), (2, 0, 2));
        assert_eq!(r.worst_tier, "T2 (runtime decidable)");
    }

    #[test]
    fn mixed_language_folds_structural_and_behavioral_into_one_tally() {
        // The integration shape: structural (T1) + behavioral (T2) share one
        // tally; worst = T2.
        static TERMS: &[TermDef] = &[
            TermDef {
                name: "CastInt",
                type_name: "Proc",
                syntax: "k",
                description: None,
                fields: &[FieldDef { name: "k", ty: "Int", is_binder: false }],
            },
            TermDef {
                name: "PNew",
                type_name: "Proc",
                syntax: "^x.p",
                description: None,
                fields: &[FieldDef {
                    name: "^x.p",
                    ty: "[Name -> Proc]",
                    is_binder: true,
                }],
            },
        ];
        static REWRITES: &[RewriteDef] = &[RewriteDef {
            name: Some("NewCong"),
            conditions: &[],
            premise: Some(("S", "T")),
            lhs: "(PNew ^x.S)",
            rhs: "(PNew ^x.T)",
            is_guarded: false,
        }];
        let m = ProbeMeta { terms: TERMS, rewrites: REWRITES };
        let r = check_guard_decidability(&m);
        // T1: 1 Int field. T2: 1 binder + 1 congruence premise = 2.
        assert_eq!(
            (
                r.total_guards,
                r.compile_time_decidable,
                r.runtime_decidable,
                r.semi_decidable,
                r.undecidable
            ),
            (3, 1, 2, 0, 0)
        );
        assert_eq!(r.worst_tier, "T2 (runtime decidable)");

        // The use of `fld` keeps the helper exercised even as the static TERMS
        // above use struct-literal syntax for `'static` placement.
        let _ = fld("z", "Int", false);
    }
}
