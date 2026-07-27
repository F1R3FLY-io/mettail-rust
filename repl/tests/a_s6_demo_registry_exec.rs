// ─────────────────────────────────────────────────────────────────────────────
// Task #11 (extended 2026-07-26) — TURNED OFF IN FULL, not deleted.
//
// Every test in this file resolves its language through the REPL REGISTRY (or through a
// `*_backed()` wrapper, which is the registry's constructor). Per the USER decision "I
// don't want REPL integration for the non-production grammars!", SwapDemo and the eleven
// rho_net DEMONSTRATION grammars are no longer registered and their wrappers no longer
// exist, so the SUBJECT of every assertion below is gone. The subject was the
// REGISTRATION, not the language: none of these is relocatable into a language-scoped
// test, because what each one asserts is "the REPL registry exposes this demo and execs
// it on the machine".
//
// The BEHAVIOUR they covered is unaffected and stays covered directly, one file per
// family, in `rholang-runtime/tests/`: rho_net_equivalence (SwapDemo), rho_net_ac_firing
// (AcDemo), rho_net_ac_bag_firing (AcBagDemo), rho_net_nl_ac_firing (NlAcDemo),
// rho_net_ambient_firing (AmbDemo + AmbNewDemo), rho_net_inout_firing (InOutDemo),
// rho_net_comm_firing (CommDemo), rho_net_contextual_firing (CtxDemo),
// rho_net_bicong_firing (BiCongDemo), rho_net_beta_firing (LambdaDemo),
// rho_net_native_firing (NativeDemo) — each driving the same in-Rho path this file
// reached through the registry.
//
// Commented out rather than dropped silently so the A-S6 coverage matrix stays readable
// and so restoring it is a one-step edit if the REPL ever regains a demo profile.
// ─────────────────────────────────────────────────────────────────────────────

// //! A-S6 (the DEMO FLIP) — end-to-end registry exec pins for the flipped demo languages.
// //!
// //! USER decision (2026-07-20): the runtime mandate — "Dovetail handles only semantic
// //! predicates at runtime" — is UNIVERSAL. Every rho_net demo registers in the production
// //! `build_registry` on the two-stage LAZY wrapper whose default exec path is the generated
// //! report-free `rho_net_match_invocation_to` (the in-Rho locate-all set-automaton match;
// //! demos are NOT drive-opted — `DRIVE_OPT_IN` stays exactly {Lambda, Ambient}).
// //!
// //! One pin per rewrite-family class, exercised THROUGH THE REGISTRY (`build_registry` →
// //! `get` → `run_backend_report(RhoMachine, …)`), asserting the machine backend and the
// //! structurally exact probed result (`scratchpad/as6_probe2.log`, 2026-07-20):
// //!
// //! | class | demo | subject → machine result |
// //! |---|---|---|
// //! | AC (flat, linear) | AcDemo | `#{A \| B \| C}#` → one `Wrap(x)` per located pick |
// //! | AC (bag-valued RHS + equation) | AcBagDemo | `#{A \| B \| C}#` → flat `{mark(x), rest…}` |
// //! | AC (non-linear `{x, x, …rest}`) | NlAcDemo | `#{A \| A \| B}#` → `Wrap(A)` (unique pick) |
// //! | structural AC (OpenRule) | AmbDemo | open fires → flat `{PA, PB}` |
// //! | structural AC + binder ctor | AmbNewDemo | redex under `new(x, …)` fires too |
// //! | nested structural AC (In/Out) | InOutDemo | C-G In/Out contracta (nested bags) |
// //! | COMM (deferral, by design) | CommDemo | match DEFERS (PFor pre-scope field) → lazy D-stage + σ-replay fires the Comm |
// //! | contextual (1-ary) | CtxDemo | `Flip` fires under `wrap(…)` |
// //! | contextual (2-ary) | BiCongDemo | both holes' `Flip`s fire |
// //! | binder β subst | LambdaDemo | β through the TRS seed → `F(A)` |
// //! | native system process | NativeDemo | `2 ^ 3` → handler-computed `NumLit(8)` |
// //! | native scalar fold (multi-site) | NativeFoldDemo | `1 + 2 + 3` → both sites fire |
// //! | normal form (no located redex) | AcDemo | `wrap(A)` → empty OUT (no firing) |
// #![cfg(feature = "rho-languages")]
//
// use mettail_repl::build_registry;
// use mettail_rholang_runtime::dstage_instrumentation::dovetail_report_invocations;
// use mettail_runtime::{RuntimeBackend, RuntimeObservationValue};
//
// fn term_obs(constructor: &str, children: Vec<RuntimeObservationValue>) -> RuntimeObservationValue {
//     RuntimeObservationValue::Term { constructor: constructor.to_string(), children }
// }
//
// fn nullary(constructor: &str) -> RuntimeObservationValue {
//     term_obs(constructor, Vec::new())
// }
//
// /// Exec `subject` on `name`'s REGISTERED production wrapper; assert the machine backend
// /// and return `(OUT values, D-stage delta)`. `channel` is "OUT" for single-shot match
// /// execs and the per-firing replay channel ("OUT0", …) for deferral execs.
// fn registry_exec(name: &str, subject: &str, channel: &str) -> (Vec<RuntimeObservationValue>, usize) {
//     let registry = build_registry().expect("build_registry installs every production wrapper");
//     let language = registry.get(name).expect("the flipped demo is registered");
//     assert_eq!(
//         language.selected_default_runtime_backend(),
//         Some(RuntimeBackend::RhoMachine),
//         "{name} must default to the Rho machine (A-S6)"
//     );
//     let term = language
//         .parse_term(subject)
//         .unwrap_or_else(|err| panic!("{name} must parse {subject:?}: {err}"));
//     let before = dovetail_report_invocations();
//     let report = language
//         .run_backend_report(RuntimeBackend::RhoMachine, term.as_ref())
//         .unwrap_or_else(|err| panic!("{name} exec of {subject:?} must run on the machine: {err}"));
//     let delta = dovetail_report_invocations() - before;
//     assert_eq!(report.backend(), RuntimeBackend::RhoMachine, "{name} ran on the Rho machine");
//     let out = report
//         .observations_for_channel(channel)
//         .unwrap_or_else(|| panic!("{name} exec observes channel {channel}"))
//         .values
//         .clone();
//     (out, delta)
// }
//
// /// The flat-bag observation entries, order-insensitively.
// fn bag_entries(value: &RuntimeObservationValue) -> Vec<(RuntimeObservationValue, usize)> {
//     let RuntimeObservationValue::Bag(entries) = value else {
//         panic!("expected a bag observation, got {value:?}");
//     };
//     entries.clone()
// }
//
// /// AC (flat, linear): `AcStep . {x, ...rest} ~> wrap(x)` — the automaton locates the bag
// /// redex from the SUBJECT SPREAD and fires; each located pick lands one `Wrap(x)`.
// #[test]
// fn a_s6_acdemo_ac_redex_fires_in_rho_via_the_registry() {
//     let (out, delta) = registry_exec("AcDemo", "#{A | B | C}#", "OUT");
//     assert_eq!(delta, 0, "an ADMITTED AcDemo exec builds ZERO Dovetail reports");
//     assert_eq!(out.len(), 1, "one located AC firing observed: {out:?}");
//     let RuntimeObservationValue::Term { constructor, children } = &out[0] else {
//         panic!("the AC contractum is a constructor term: {out:?}");
//     };
//     assert_eq!(constructor, "Wrap", "AcStep fires {{x, ...rest}} ~> wrap(x)");
//     assert_eq!(children.len(), 1);
//     assert!(
//         ["A", "B", "C"]
//             .iter()
//             .any(|element| children[0] == nullary(element)),
//         "the wrapped element is one of the bag's members: {out:?}"
//     );
// }
//
// /// Normal form: a subject with NO located redex rests with an EMPTY observation — the
// /// machine ran, nothing fired, nothing was host-computed.
// #[test]
// fn a_s6_acdemo_normal_form_execs_to_an_empty_observation() {
//     let (out, delta) = registry_exec("AcDemo", "wrap(A)", "OUT");
//     assert_eq!(delta, 0, "a normal-form exec still builds ZERO Dovetail reports");
//     assert!(out.is_empty(), "no located redex ⇒ no firing observation: {out:?}");
// }
//
// /// AC with a bag-valued RHS (+ the `MarkIdem` equation, probed NOT to gate the match
// /// path): `AcBagStep . {x, ...rest} ~> {mark(x), ...rest}` — the whole contractum bag
// /// re-sources from the subject spread and rests FLAT.
// #[test]
// fn a_s6_acbagdemo_bag_valued_rhs_fires_flat_in_rho() {
//     let (out, delta) = registry_exec("AcBagDemo", "#{A | B | C}#", "OUT");
//     assert_eq!(delta, 0, "an ADMITTED AcBagDemo exec builds ZERO Dovetail reports");
//     assert_eq!(out.len(), 1, "one located AC firing observed: {out:?}");
//     let entries = bag_entries(&out[0]);
//     let element_count: usize = entries.iter().map(|(_, count)| count).sum();
//     assert_eq!(element_count, 3, "the contractum bag is FLAT with 3 elements: {entries:?}");
//     let marked: Vec<_> = entries
//         .iter()
//         .filter(|(element, _)| {
//             matches!(element, RuntimeObservationValue::Term { constructor, .. } if constructor == "Mark")
//         })
//         .collect();
//     assert_eq!(marked.len(), 1, "exactly one element is marked: {entries:?}");
// }
//
// /// Non-linear AC (`{x, x, ...rest}`): the subject `{A | A | B}` has the UNIQUE
// /// non-linear match `x = A` (the sole multiplicity-≥2 element), enforced by the
// /// reducer's consistency guard over the subject spread.
// #[test]
// fn a_s6_nlacdemo_nonlinear_pick_fires_in_rho() {
//     let (out, delta) = registry_exec("NlAcDemo", "#{A | A | B}#", "OUT");
//     assert_eq!(delta, 0, "an ADMITTED NlAcDemo exec builds ZERO Dovetail reports");
//     assert_eq!(
//         out,
//         vec![term_obs("Wrap", vec![nullary("A")])],
//         "the unique non-linear pick is x = A ⇒ wrap(A)"
//     );
// }
//
// /// Structural AC (the Ambient-calculus OpenRule): `{open(na, A) | na[B]}` fires to the
// /// FLAT bag `{A, B}` (demo constructors `PA`/`PB`).
// #[test]
// fn a_s6_ambdemo_open_fires_in_rho() {
//     let (out, delta) = registry_exec("AmbDemo", "{ open(na, A) | na[B] }", "OUT");
//     assert_eq!(delta, 0, "an ADMITTED AmbDemo exec builds ZERO Dovetail reports");
//     assert_eq!(out.len(), 1);
//     let entries = bag_entries(&out[0]);
//     assert_eq!(entries.len(), 2, "open fired: flat {{PA, PB}}: {entries:?}");
//     for expected in ["PA", "PB"] {
//         assert!(
//             entries.iter().any(|(element, count)| element == &nullary(expected) && *count == 1),
//             "the resting bag contains {expected}: {entries:?}"
//         );
//     }
// }
//
// /// Structural AC under a binder CONSTRUCTOR: AmbNewDemo's OpenRule redex under
// /// `new(x, …)` still locates and fires in Rho (probed 2026-07-20).
// #[test]
// fn a_s6_ambnewdemo_open_under_new_fires_in_rho() {
//     let (out, delta) = registry_exec("AmbNewDemo", "new(x, { open(na, A) | na[B] })", "OUT");
//     assert_eq!(delta, 0, "an ADMITTED AmbNewDemo exec builds ZERO Dovetail reports");
//     assert_eq!(out.len(), 1);
//     let entries = bag_entries(&out[0]);
//     assert_eq!(entries.len(), 2, "open fired under new(x, …): flat {{PA, PB}}: {entries:?}");
// }
//
// /// Nested structural AC (depth-2, C-G Red In): `{na[{in(nb, A)}] | nb[B]}` — the `na`
// /// ambient moves INSIDE `nb`: `{nb[{na[{A}], B}]}`.
// #[test]
// fn a_s6_inoutdemo_in_fires_in_rho() {
//     let (out, delta) = registry_exec("InOutDemo", "{ na[{ in(nb, A) }] | nb[B] }", "OUT");
//     assert_eq!(delta, 0, "an ADMITTED InOutDemo exec builds ZERO Dovetail reports");
//     assert_eq!(out.len(), 1);
//     let entries = bag_entries(&out[0]);
//     assert_eq!(entries.len(), 1, "one root ambient rests: {entries:?}");
//     let RuntimeObservationValue::Term { constructor, children } = &entries[0].0 else {
//         panic!("the resting root is an ambient: {entries:?}");
//     };
//     assert_eq!(constructor, "PAmb");
//     assert_eq!(children[0], nullary("Nb"), "the root ambient is nb (In moved na inside)");
//     let inner = bag_entries(&children[1]);
//     assert_eq!(inner.len(), 2, "nb's body is {{na[{{A}}], B}}: {inner:?}");
// }
//
// /// Nested structural AC (depth-2, C-G Red Out): `nb[{na[{out(nb, A)}] | B}]` — the `na`
// /// ambient exits `nb`: `{na[{A}], nb[{B}]}` (the residual stays inside the parent).
// #[test]
// fn a_s6_inoutdemo_out_fires_in_rho() {
//     let (out, delta) = registry_exec("InOutDemo", "nb[{ na[{ out(nb, A) }] | B }]", "OUT");
//     assert_eq!(delta, 0, "an ADMITTED InOutDemo exec builds ZERO Dovetail reports");
//     assert_eq!(out.len(), 1);
//     let entries = bag_entries(&out[0]);
//     assert_eq!(entries.len(), 2, "out fired: {{na[{{A}}], nb[B]}}: {entries:?}");
//     for (element, _) in &entries {
//         let RuntimeObservationValue::Term { constructor, .. } = element else {
//             panic!("each resting element is an ambient: {entries:?}");
//         };
//         assert_eq!(constructor, "PAmb");
//     }
// }
//
// /// COMM — the BY-DESIGN deferral pin (probed 2026-07-20): CommDemo's `PFor` is a binder
// /// node with a PRE-SCOPE Name field, which the match-path reflection does not support,
// /// so the report-free match DEFERS (`GateReject`); the wrapper LAZILY builds the checked
// /// Dovetail report (D-stage delta ≥ 1), the report-driven match rejects for the same
// /// reason, and the σ-replay driver fires the Comm through its comm arm — the contractum
// /// `{nb!(nc)}` (= `cont[Q/y]`) rests on the per-firing replay channel `OUT0`.
// #[test]
// fn a_s6_commdemo_comm_defers_to_the_lazy_sigma_replay() {
//     let (out, delta) = registry_exec("CommDemo", "{ for(y <- na){ y!(nc) } | na!(nb) }", "OUT0");
//     assert!(
//         delta >= 1,
//         "the CommDemo deferral must LAZILY build the Dovetail report (delta {delta} < 1)"
//     );
//     assert_eq!(out.len(), 1);
//     let entries = bag_entries(&out[0]);
//     assert_eq!(
//         entries,
//         vec![(term_obs("POutput", vec![nullary("Nb"), nullary("Nc")]), 1)],
//         "the Comm fired: cont[Q/y] = nb!(nc)"
//     );
// }
//
// /// Contextual (1-ary congruence): CtxDemo's `Flip` fires INSIDE the `wrap(…)` context —
// /// the congruence-only `WrapCong` is statically exempt (A-S5.1) and the hole's reduct
// /// routes through the contextual join.
// #[test]
// fn a_s6_ctxdemo_contextual_flip_fires_in_rho() {
//     let (out, delta) = registry_exec("CtxDemo", "wrap(swap(A, B))", "OUT");
//     assert_eq!(delta, 0, "an ADMITTED CtxDemo exec builds ZERO Dovetail reports");
//     assert_eq!(
//         out,
//         vec![term_obs("Pair", vec![nullary("B"), nullary("A")])],
//         "Flip fired in the wrap(…) hole: swap(A, B) ~> pair(B, A)"
//     );
// }
//
// /// Contextual (2-ary congruence): BiCongDemo's `Flip` fires in BOTH `node(…)` holes.
// #[test]
// fn a_s6_bicongdemo_both_holes_fire_in_rho() {
//     let (out, delta) = registry_exec("BiCongDemo", "node(swap(A, B), swap(C, D))", "OUT");
//     assert_eq!(delta, 0, "an ADMITTED BiCongDemo exec builds ZERO Dovetail reports");
//     let pair_b_a = term_obs("Pair", vec![nullary("B"), nullary("A")]);
//     let pair_d_c = term_obs("Pair", vec![nullary("D"), nullary("C")]);
//     assert_eq!(out.len(), 2, "both holes fired: {out:?}");
//     assert!(
//         out.contains(&pair_b_a) && out.contains(&pair_d_c),
//         "each hole's Flip reduct observed: {out:?}"
//     );
// }
//
// /// Binder β substitution: LambdaDemo's `Beta` fires in-Rho through the TRS seed —
// /// `(lam x. f(x), A)` β-reduces to `f(A)` with zero Dovetail work.
// #[test]
// fn a_s6_lambdademo_beta_fires_in_rho() {
//     let (out, delta) = registry_exec("LambdaDemo", "(lam x. f(x), A)", "OUT");
//     assert_eq!(delta, 0, "an ADMITTED LambdaDemo exec builds ZERO Dovetail reports");
//     assert_eq!(
//         out,
//         vec![term_obs("F", vec![nullary("A")])],
//         "β fired through the σ ABI + subst TRS: (λx. f x) A → f(A)"
//     );
// }
//
// /// Native system process: NativeDemo's `PowInt` value is computed by the REGISTERED
// /// machine-side handler at COMM time (A-S3) — `2 ^ 3` rests `NumLit(8)`.
// #[test]
// fn a_s6_nativedemo_powint_computes_on_the_machine() {
//     let (out, delta) = registry_exec("NativeDemo", "2 ^ 3", "OUT");
//     assert_eq!(delta, 0, "an ADMITTED NativeDemo exec builds ZERO Dovetail reports");
//     assert_eq!(out, vec![nullary("NumLit(8)")], "the handler computed 2^3 = 8 at COMM time");
// }
//
// // Task #11 (extended 2026-07-26) — TURNED OFF, not deleted. `registry_exec("NativeFoldDemo", …)`
// // resolves the language through the REPL REGISTRY, and per the USER decision "I don't want REPL
// // integration for the non-production grammars!" NativeFoldDemo is no longer registered. The
// // multi-site native-scalar-fold behavior itself is unaffected and stays covered by
// // `rholang-runtime/tests/rho_net_native_fold_firing.rs`.
// // /// Native scalar fold, MULTI-SITE: NativeFoldDemo's `1 + 2 + 3` locates BOTH AddInt
// // /// sites — each drives its own machine-side handler invocation (A-S3 lifts the
// // /// single-native-firing restriction on the admitted path).
// // #[test]
// // fn a_s6_nativefolddemo_multi_site_folds_compute_on_the_machine() {
// //     let (out, delta) = registry_exec("NativeFoldDemo", "1 + 2 + 3", "OUT");
// //     assert_eq!(delta, 0, "an ADMITTED NativeFoldDemo exec builds ZERO Dovetail reports");
// //     assert_eq!(out.len(), 2, "both located AddInt sites fired: {out:?}");
// //     assert!(
// //         out.contains(&nullary("NumLit(3)")) && out.contains(&nullary("NumLit(6)")),
// //         "the nested site computes 1 + 2 = 3 and the root site computes (1 + 2) + 3 = 6 \
// //          (recursive ground evaluation of the captured subtree): {out:?}"
// //     );
// // }
//
