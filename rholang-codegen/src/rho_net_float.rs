//! The generated in-Rho `^float` receiver family (A-S5.8, design
//! `scratchpad/a_s5_design/a_s5_8_float_design_v1.md` + delta amendments F8-AM-1..5) —
//! the PER-ITERATION binder-float canonicalizer that constructively discharges the
//! boundary-float premise: for a FLOAT-BEARING language every `^drive` subject (the S2
//! seed and every fired contractum, decision Q-AB = A) is float-canonicalized ON the live
//! f1r3node reducer, so a contractum-introduced `ν` (the F8-AM-1a witness's `Seal`
//! contractum) can no longer hide a redex from the driver's Match arms.
//!
//! # Theory (USER MANDATE: Ambient = the Ambient Calculus)
//!
//! The float implements exactly the Cardelli–Gordon subset ≡ steps the match-completeness
//! theorem needs — (Struct Res Par) at the bag seam (`ScopeExtrusion` → the merge
//! satellite), (Struct Res Amb) + the three documented capability extensions at the
//! prefix seams (`AmbNew`/`InNew`/`OutNew`/`OpenNew` → the hoist satellites) — over the
//! NAMELESS reflected ABI, where α-freshening is UNNECESSARY: moving material under one
//! extruded binder is `^shift(Z, ·)` arithmetic, and the extruded binder's index `0` is
//! NEVER in the shift image, so the floated binder is never referenced by shifted
//! material — the side condition `x ∉ fn(P)` holds BY THE SHIFT-IMAGE ARGUMENT (FV:
//! `InRhoFloatCanonicalization.v`, `hoist_side_condition_by_shift_image`). NewComm
//! ((Struct Res Res)) is DELIBERATELY not reordered in-Rho (user decision Q-NC): the
//! host's canonical run order is the α-canonical (FIX-A) semantic-KEY minimization
//! (`FramedSemanticKeyHasher`, `binder_congruence.rs`) — a function of the α-quotient the
//! erased ABI retains, but with NO Match-expressible total order/hash over reflected
//! `Par`s — and redex exposure is NewComm-invariant
//! (`redex_invariant_under_run_permutation`), so the float NF is unique UP TO the NewComm
//! run permutation and display canonicality stays host-side.
//!
//! # The family (Ambient: 8 receivers; installed 7 → 15)
//!
//! ```text
//! for(@t, @ret <= ⌜^float⌝) {                                -- THE DISPATCHER
//!   match t {
//!     [⌜^lambda⌝, b]   => float b, rewrap                     -- (1) a binder over a float-canonical
//!                                                             --     body is float-canonical
//!     [⌜C⌝, c₀, …]     => float children, join,               -- (2) C has a recognized float-across
//!                         ⌜^float-hoist:C⌝!(s…, ret)          --     equation (PIn/POut/POpen/PAmb)
//!     [⌜D⌝, c₀, …]     => float children, join, rewrap        -- (3) other ≥1-ary ctor (Lambda-App
//!                                                             --     analogue; no hoist)
//!     [⌜E⌝]            => ret!([⌜E⌝])                         -- (4) nullary leaf
//!     {@"ac:op"!(e)|r} => float e + r concurrently, join,     -- (5) soup peel, one arm per
//!                         ⌜^float-merge:op⌝!(ve, vr, ret)     --     merge-equipped bag op
//!     Nil              => ret!(Nil)                           -- (6) the empty bag (AM-3)
//!     [⌜^free⌝, x]     => passthrough                         -- (7) name leaves are inert
//!     [⌜^bound⌝, n]    => passthrough
//!     _                => @"^drive-err:{fp}"!(t)              -- (8) fail-closed (the EXISTING
//!   }                                                         --     channel — no new surface)
//! }
//!
//! for(@a₀, …, @a_{m-1}, @ret <= ⌜^float-hoist:C⌝) {          -- ONE PER PREFIX EQUATION'S C
//!   match a_i {                                               -- i = the equation's float position
//!     [⌜^lambda⌝, B] => ∏_{j≠i} ⌜^shift⌝!(Z, a_j, s_j)        -- shift every OTHER field by 1 at
//!                     | join { ⌜^float-hoist:C⌝!(…, B, …, rh) -- cutoff 0, recurse on the body,
//!                            | for(@h <- rh){ ret!([⌜^lambda⌝, h]) } }   -- rewrap ONE binder
//!     _              => ret!([⌜C⌝, a₀, …])                    -- no binder: rebuild
//!   }
//! }
//!
//! for(@u, @v, @ret <= ⌜^float-merge:op⌝) {                   -- ONE PER COLLECTION EQUATION'S op
//!   match u {                                                 -- u-FIRST deterministic order:
//!     [⌜^lambda⌝, P] => ⌜^shift⌝!(Z, v, sv)                   -- strip u's run first (u's binders
//!                     | for(@vs <- sv){ merge!(P, vs, rm)     -- end OUTERMOST), shifting the
//!                     | for(@m <- rm){ ret!([⌜^lambda⌝, m]) } } -- stayed-outside side by 1 per
//!     _ => match v {                                          -- stripped binder;
//!       [⌜^lambda⌝, Q] => (symmetric: shift u, recurse, rewrap)
//!       _ => three-case-dispatch u → w; ret!({w | v})         -- BASE: the AM-2/AM-3 splice
//!     }                                                       -- INSIDE the float
//!   }
//! }
//! ```
//!
//! plus the SHARED `^shift`/`^cmp` satellites
//! ([`crate::rho_net_subst_trs::shift_receiver_par`] — WITH the A-S5.8 soup/Nil arms,
//! F8-AM-5e/5f — and [`crate::rho_net_subst_trs::cmp_receiver_par`]), installed by the
//! float family exactly when the language carries no subst TRS (Ambient: first-time
//! install; the closed dependency set is `^shift` + `^cmp` — the `^bound` arm's Peano
//! comparison — and nothing else).
//!
//! # Derivation (never hardcoded to Ambient)
//!
//! The satellite set is READ OFF the landed float-equation recognizer classification
//! ([`crate::rho_net_lower::float_satellite_table`] — the SAME per-equation walk
//! `equations_boundary_canonicalizable` admits with): one `^float-hoist:{C}` per
//! recognized PREFIX float-across-constructor equation, one `^float-merge:{op}` per
//! recognized COLLECTION float equation, nothing for the binder-commutation family
//! (Q-NC). A bag op with NO collection float equation gets NO peel arm — its soups fall
//! to the fail-closed wildcard (loud `^drive-err`, never a silent wrong float).
//!
//! # Fixpoint, fuel, termination, confluence (design §3)
//!
//! Single bottom-up structural pass; local recursions to quiescence; the fixpoint
//! property is FV (`float_identity_on_canonical` — a second pass is the identity up to
//! bag multiset order). Float steps consume NO drive fuel (`≡`, not `→` — cost-free iso
//! in KT terms) and the family carries NO fuel of its own: every dispatcher arm recurses
//! on STRICT SUBTERMS (children / peeled element / remainder — the peel strictly shrinks
//! the soup), the hoist/merge recursions strictly decrease the leading-`^lambda` run
//! length of one argument, and no arm constructs an unconsumed `^lambda` — the global
//! potential is the binder depth-sum (the host float's own termination measure). Real
//! machine cost ≈ 2 COMMs/node/pass + O(|shifted|) per hoisted binder, labeled
//! `[τ float]` by the step classifier, never in the firing ledger. CONFLUENCE: the only
//! schedule choice is the peel order — every order reaches the same canonical core with
//! the TOP BINDER RUN PERMUTED (unique up to NewComm; FV
//! `float_functional_up_to_NewComm`), and with no reorder arm there is no ping-pong.
//!
//! # Gate
//!
//! Generated + installed ([`crate::rho_net_lower::RhoNetLowered::float`]) iff
//! [`language_is_float_bearing`] ([`crate::rho_net_lower::language_has_float_handler`] ∧
//! [`crate::rho_net_lower::equations_boundary_canonicalizable`]) ∧ the drive admission is
//! `Admitted` — the bundled corpus is EXACTLY the production Ambient (pinned by the
//! macros-side corpus test). Every other language's lowering artifact and installed
//! program are BYTE-IDENTICAL to pre-A-S5.8.
//!
//! FV: `formal/rocq/rho_bridge/theories/InRhoFloatCanonicalization.v` (the de Bruijn
//! fragment + shift + float in the run-length Config representation: `float_step_sound`,
//! `float_functional_up_to_NewComm` + `float_identity_on_canonical`,
//! `float_preserves_bag_flatness`, `float_exposes_redexes`,
//! `redex_invariant_under_run_permutation`) and `InRhoDriveWithFloat.v` (the driver float
//! phase: `float_phase_conservative`, the premise discharge
//! `drive_with_float_on_raw_eq_drive_on_canonical`).

use mettail_ast::language::LanguageDef;
use models::rhoapi::Par;

use crate::rho_net_drive::{
    bag_fragment_dispatch, drive_err_channel, hashbag_collection_ops, soup_peel_pattern,
};
use crate::rho_net_lower::{
    equations_boundary_canonicalizable, float_satellite_table, language_has_float_handler,
    FloatSatelliteTable, BOUND_VAR_REFLECT_LABEL, FLOAT_HOIST_RESERVED_LABEL,
    FLOAT_MERGE_RESERVED_LABEL, FLOAT_RESERVED_LABEL, FREE_VAR_REFLECT_LABEL,
    LAMBDA_REFLECT_LABEL, PEANO_ZERO_REFLECT_LABEL, SHIFT_RESERVED_LABEL,
};
use crate::rho_net_subst_trs::{
    cmp_receiver_par, for1, ground, join, match_, new_scope, nullary_term,
    object_congruence_constructors, par2, pat_free, pat_tagged, pat_wildcard,
    persistent_contract, send, shift_receiver_par, tag_par, tagged, Case, Env, Node,
};

use models::rust::utils::new_gstring_par;

/// A-S5.8: whether `def` is FLOAT-BEARING — the macros side generates the host binder
/// float for it AND its whole equational theory is float-discharged. Conjoined with
/// `DriveAdmission::Admitted` this is the family's install gate (the bundled corpus is
/// exactly the production Ambient); alone it decides the firing-emission routing
/// (`rho_net_drive::redex_cases` — the emissions and the family install under the SAME
/// predicate, so a float-routed drive always has its `^float` receivers).
pub fn language_is_float_bearing(def: &LanguageDef) -> bool {
    language_has_float_handler(def) && equations_boundary_canonicalizable(def)
}

/// The reserved per-constructor hoist satellite tag label `"^float-hoist:{C}"`.
pub(crate) fn float_hoist_label(constructor: &str) -> String {
    format!("{FLOAT_HOIST_RESERVED_LABEL}:{constructor}")
}

/// The reserved per-op merge satellite tag label `"^float-merge:{op}"`.
pub(crate) fn float_merge_label(op: &str) -> String {
    format!("{FLOAT_MERGE_RESERVED_LABEL}:{op}")
}

/// The whole installable `^float` receiver family for one float-bearing language (module
/// docs): the dispatcher, the equation-derived hoist/merge satellites (deterministic
/// order: hoists in equation-declaration order, then merges), and — when
/// `include_shift_cmp` (the language installs no subst TRS, so these are first-time) —
/// the shared `^shift`/`^cmp` satellites.
pub(crate) fn float_program_par(
    def: &LanguageDef,
    fingerprint: &str,
    include_shift_cmp: bool,
) -> Par {
    let table = float_satellite_table(def);
    let mut program = float_dispatcher_par(def, fingerprint, &table);
    for (constructor, float_index, arity) in &table.hoist {
        program = program.append(float_hoist_receiver_par(
            fingerprint,
            constructor,
            *float_index,
            *arity,
        ));
    }
    for op in &table.merge_ops {
        program = program.append(float_merge_receiver_par(fingerprint, op));
    }
    if include_shift_cmp {
        program = program
            .append(shift_receiver_par(def, fingerprint))
            .append(cmp_receiver_par(fingerprint));
    }
    program
}

/// The `^float(t, ret)` DISPATCHER (module docs — the arm table; head universe = the
/// `^drive` receiver's minus the redex arms, patterns pairwise disjoint).
fn float_dispatcher_par(def: &LanguageDef, fp: &str, table: &FloatSatelliteTable) -> Par {
    let env = Env::root(&["t", "ret"]);
    let mut cases: Vec<Case> = Vec::new();

    // (1) The binder arm: float the body, rewrap — a `^lambda` over a float-canonical
    //     body is float-canonical (the run assembles from the inside out).
    cases.push(Case {
        pattern: pat_tagged(fp, LAMBDA_REFLECT_LABEL, vec![pat_free(0)]),
        free_count: 1,
        body: {
            let env = env.push(&["b"]);
            new_scope(1, {
                let env = env.push(&["r"]);
                let recur = send(
                    ground(tag_par(fp, FLOAT_RESERVED_LABEL)),
                    vec![env.var("b"), env.var("r")],
                );
                let rewrap = for1(env.var("r"), {
                    let env = env.push(&["fb"]);
                    send(
                        env.var("ret"),
                        vec![tagged(fp, LAMBDA_REFLECT_LABEL, vec![env.var("fb")])],
                    )
                });
                par2(recur, rewrap)
            })
        },
    });

    // (2)/(3)/(4) One arm per object constructor (declaration order): a HOIST ctor (a
    //     recognized prefix float equation) floats its children then dispatches to its
    //     satellite; any other ≥1-ary ctor floats its children and rewraps (the
    //     Lambda-App analogue — no hoist); a nullary ctor is its own float NF.
    for (label, arity) in object_congruence_constructors(def) {
        let hoist = table
            .hoist
            .iter()
            .find(|(constructor, _, _)| *constructor == label);
        if let Some((_, _, hoist_arity)) = hoist {
            debug_assert_eq!(
                *hoist_arity, arity,
                "the float-equation classification and the C2 enumeration agree on {label}'s arity"
            );
        }
        let child_pats: Vec<Par> = (0..arity).map(pat_free).collect();
        let body = {
            let child_names: Vec<String> = (0..arity).map(|i| format!("c{i}")).collect();
            let child_refs: Vec<&str> = child_names.iter().map(String::as_str).collect();
            let env = env.push(&child_refs);
            if arity == 0 {
                send(env.var("ret"), vec![tagged(fp, &label, Vec::new())])
            } else {
                new_scope(arity, {
                    let ret_names: Vec<String> = (0..arity).map(|i| format!("r{i}")).collect();
                    let ret_refs: Vec<&str> = ret_names.iter().map(String::as_str).collect();
                    let env = env.push(&ret_refs);
                    // Concurrent child floats.
                    let mut composed: Option<Node> = None;
                    for i in 0..arity {
                        let call = send(
                            ground(tag_par(fp, FLOAT_RESERVED_LABEL)),
                            vec![env.var(&child_names[i]), env.var(&ret_names[i])],
                        );
                        composed = Some(match composed {
                            None => call,
                            Some(acc) => par2(acc, call),
                        });
                    }
                    // The atomic join, then hoist-dispatch or rewrap.
                    let join_sources: Vec<Node> = ret_names.iter().map(|r| env.var(r)).collect();
                    let is_hoist = hoist.is_some();
                    let label = label.clone();
                    let join_node = join(join_sources, {
                        let s_names: Vec<String> = (0..arity).map(|i| format!("s{i}")).collect();
                        let s_refs: Vec<&str> = s_names.iter().map(String::as_str).collect();
                        let env = env.push(&s_refs);
                        if is_hoist {
                            let mut data: Vec<Node> = Vec::with_capacity(arity + 1);
                            for s in &s_names {
                                data.push(env.var(s));
                            }
                            data.push(env.var("ret"));
                            send(ground(tag_par(fp, &float_hoist_label(&label))), data)
                        } else {
                            let assembled: Vec<Node> =
                                s_names.iter().map(|s| env.var(s)).collect();
                            send(env.var("ret"), vec![tagged(fp, &label, assembled)])
                        }
                    });
                    par2(composed.expect("arity ≥ 1"), join_node)
                })
            }
        };
        cases.push(Case {
            pattern: pat_tagged(fp, &label, child_pats),
            free_count: arity,
            body,
        });
    }

    // (5) One soup-peel arm per MERGE-equipped bag op (equation-derived): float the
    //     peeled element and the remainder concurrently, join, and hand both to the
    //     merge satellite (which extrudes their binder runs and splices). A bag op
    //     WITHOUT a collection float equation gets no arm — its soups fall to (8).
    for op in &table.merge_ops {
        let body = {
            let env = env.push(&["e", "rem"]);
            new_scope(2, {
                let env = env.push(&["re", "rr"]);
                let float_element = send(
                    ground(tag_par(fp, FLOAT_RESERVED_LABEL)),
                    vec![env.var("e"), env.var("re")],
                );
                let float_remainder = send(
                    ground(tag_par(fp, FLOAT_RESERVED_LABEL)),
                    vec![env.var("rem"), env.var("rr")],
                );
                let join_node = join(vec![env.var("re"), env.var("rr")], {
                    let env = env.push(&["ve", "vr"]);
                    send(
                        ground(tag_par(fp, &float_merge_label(op))),
                        vec![env.var("ve"), env.var("vr"), env.var("ret")],
                    )
                });
                par2(par2(float_element, float_remainder), join_node)
            })
        };
        cases.push(Case { pattern: soup_peel_pattern(fp, op), free_count: 2, body });
    }

    // (6) The Nil (empty-bag) leaf — its own float NF (AM-3; also the peel recursion's
    //     base case). Emitted exactly when the language has bag constructors at all
    //     (the drive's Nil-leaf gating).
    if !hashbag_collection_ops(def).is_empty() {
        cases.push(Case {
            pattern: Par::default(),
            free_count: 0,
            body: send(env.var("ret"), vec![ground(Par::default())]),
        });
    }

    // (7) Reserved passthroughs: name leaves are inert under the float.
    cases.push(Case {
        pattern: pat_tagged(fp, FREE_VAR_REFLECT_LABEL, vec![pat_free(0)]),
        free_count: 1,
        body: {
            let env = env.push(&["x"]);
            send(
                env.var("ret"),
                vec![tagged(fp, FREE_VAR_REFLECT_LABEL, vec![env.var("x")])],
            )
        },
    });
    cases.push(Case {
        pattern: pat_tagged(fp, BOUND_VAR_REFLECT_LABEL, vec![pat_free(0)]),
        free_count: 1,
        body: {
            let env = env.push(&["n"]);
            send(
                env.var("ret"),
                vec![tagged(fp, BOUND_VAR_REFLECT_LABEL, vec![env.var("n")])],
            )
        },
    });

    // (8) The typed fail-close wildcard — the EXISTING `^drive-err:{fp}` GString (no new
    //     observation surface): an unrecognized head is never silently float-canonical.
    cases.push(Case {
        pattern: pat_wildcard(),
        free_count: 0,
        body: send(
            ground(new_gstring_par(drive_err_channel(fp), Vec::new(), false)),
            vec![env.var("t")],
        ),
    });

    let body = match_(env.var("t"), cases);
    persistent_contract(tag_par(fp, FLOAT_RESERVED_LABEL), 2, body).par
}

/// One `^float-hoist:{C}(a₀, …, a_{m-1}, ret)` satellite (module docs): extrude the
/// leading `^lambda` run of the float-position argument `a_i` across `C` — one binder per
/// recursion step, shifting every OTHER (already-floated) field by 1 at cutoff 0 per
/// stripped binder (the C-G (Struct Res Amb) / capability-extension step; the side
/// condition holds by the shift-image argument), rewrapping the binder outside. The
/// wildcard rebuilds `C` unchanged (no binder to hoist).
fn float_hoist_receiver_par(fp: &str, constructor: &str, float_index: usize, arity: usize) -> Par {
    let formal_names: Vec<String> = (0..arity).map(|i| format!("a{i}")).collect();
    let mut root_formals: Vec<&str> = formal_names.iter().map(String::as_str).collect();
    root_formals.push("ret");
    let env = Env::root(&root_formals);
    let others: Vec<usize> = (0..arity).filter(|j| *j != float_index).collect();

    let binder_case_body = {
        let env = env.push(&["__B"]);
        if others.is_empty() {
            // A unary hoist ctor: nothing crosses the binder — recurse and rewrap.
            new_scope(1, {
                let env = env.push(&["__rh"]);
                let recur = send(
                    ground(tag_par(fp, &float_hoist_label(constructor))),
                    vec![env.var("__B"), env.var("__rh")],
                );
                let rewrap = for1(env.var("__rh"), {
                    let env = env.push(&["__h"]);
                    send(
                        env.var("ret"),
                        vec![tagged(fp, LAMBDA_REFLECT_LABEL, vec![env.var("__h")])],
                    )
                });
                par2(recur, rewrap)
            })
        } else {
            let k = others.len();
            new_scope(k, {
                let shift_ret_names: Vec<String> = (0..k).map(|i| format!("__s{i}")).collect();
                let shift_ret_refs: Vec<&str> =
                    shift_ret_names.iter().map(String::as_str).collect();
                let env = env.push(&shift_ret_refs);
                // Shift every other field by 1 at cutoff 0, concurrently — it now sits
                // under ONE more binder.
                let mut composed: Option<Node> = None;
                for (i, j) in others.iter().enumerate() {
                    let call = send(
                        ground(tag_par(fp, SHIFT_RESERVED_LABEL)),
                        vec![
                            ground(nullary_term(fp, PEANO_ZERO_REFLECT_LABEL)),
                            env.var(&formal_names[*j]),
                            env.var(&shift_ret_names[i]),
                        ],
                    );
                    composed = Some(match composed {
                        None => call,
                        Some(acc) => par2(acc, call),
                    });
                }
                // Join the shifted fields, recurse on the scope body, rewrap ONE binder.
                let join_sources: Vec<Node> =
                    shift_ret_names.iter().map(|s| env.var(s)).collect();
                let others_for_join = others.clone();
                let join_node = join(join_sources, {
                    let shifted_names: Vec<String> =
                        (0..k).map(|i| format!("__t{i}")).collect();
                    let shifted_refs: Vec<&str> =
                        shifted_names.iter().map(String::as_str).collect();
                    let env = env.push(&shifted_refs);
                    new_scope(1, {
                        let env = env.push(&["__rh"]);
                        let mut data: Vec<Node> = Vec::with_capacity(arity + 1);
                        for j in 0..arity {
                            if j == float_index {
                                data.push(env.var("__B"));
                            } else {
                                let position = others_for_join
                                    .iter()
                                    .position(|other| *other == j)
                                    .expect("j is an other-field index");
                                data.push(env.var(&shifted_names[position]));
                            }
                        }
                        data.push(env.var("__rh"));
                        let recur =
                            send(ground(tag_par(fp, &float_hoist_label(constructor))), data);
                        let rewrap = for1(env.var("__rh"), {
                            let env = env.push(&["__h"]);
                            send(
                                env.var("ret"),
                                vec![tagged(fp, LAMBDA_REFLECT_LABEL, vec![env.var("__h")])],
                            )
                        });
                        par2(recur, rewrap)
                    })
                });
                par2(composed.expect("k ≥ 1"), join_node)
            })
        }
    };

    let rebuild_body = {
        let assembled: Vec<Node> = formal_names.iter().map(|a| env.var(a)).collect();
        send(env.var("ret"), vec![tagged(fp, constructor, assembled)])
    };

    let body = match_(
        env.var(&formal_names[float_index]),
        vec![
            Case {
                pattern: pat_tagged(fp, LAMBDA_REFLECT_LABEL, vec![pat_free(0)]),
                free_count: 1,
                body: binder_case_body,
            },
            Case { pattern: pat_wildcard(), free_count: 0, body: rebuild_body },
        ],
    );
    persistent_contract(tag_par(fp, &float_hoist_label(constructor)), arity + 1, body).par
}

/// One `^float-merge:{op}(u, v, ret)` satellite (module docs — the ScopeExtrusion
/// clauses): merge two already-floated values into one float-canonical bag member set —
/// strip `u`'s leading `^lambda` run FIRST (u-first deterministic order; u's binders end
/// outermost), then `v`'s, shifting the OTHER side by 1 at cutoff 0 per stripped binder
/// (the C-G (Struct Res Par) step; side condition by the shift-image argument); the BASE
/// case (neither side binder-headed) is the three-case [`bag_fragment_dispatch`] on `u`
/// (Nil ⇒ nothing / same-op soup ⇒ splice / else ⇒ wrap — the AM-2/AM-3 splice INSIDE
/// the float) composed with `v` (a soup/Nil by the float invariant). The F8-AM-5f
/// load-bearing case: a `v`-side strip shifts a Nil `u` — the A-S5.8 `^shift` Nil arm.
fn float_merge_receiver_par(fp: &str, op: &str) -> Par {
    let env = Env::root(&["u", "v", "ret"]);

    // Strip one binder from `side` (its scope body bound as `__P`), shifting the OTHER
    // side by 1 at cutoff 0, recursing with the two sides in their original positions,
    // and rewrapping the binder outside.
    let strip_case = |stripped_is_u: bool| -> Node {
        let env = env.push(&["__P"]);
        new_scope(1, {
            let env = env.push(&["__sv"]);
            let other = if stripped_is_u { "v" } else { "u" };
            let shift_other = send(
                ground(tag_par(fp, SHIFT_RESERVED_LABEL)),
                vec![
                    ground(nullary_term(fp, PEANO_ZERO_REFLECT_LABEL)),
                    env.var(other),
                    env.var("__sv"),
                ],
            );
            let observe = for1(env.var("__sv"), {
                let env = env.push(&["__vs"]);
                new_scope(1, {
                    let env = env.push(&["__rm"]);
                    let (first, second) = if stripped_is_u {
                        ("__P", "__vs")
                    } else {
                        ("__vs", "__P")
                    };
                    let recur = send(
                        ground(tag_par(fp, &float_merge_label(op))),
                        vec![env.var(first), env.var(second), env.var("__rm")],
                    );
                    let rewrap = for1(env.var("__rm"), {
                        let env = env.push(&["__m"]);
                        send(
                            env.var("ret"),
                            vec![tagged(fp, LAMBDA_REFLECT_LABEL, vec![env.var("__m")])],
                        )
                    });
                    par2(recur, rewrap)
                })
            });
            par2(shift_other, observe)
        })
    };

    // BASE: neither side is binder-headed — dispatch `u`'s fragment and compose with `v`.
    let base_case = new_scope(1, {
        let env = env.push(&["__f"]);
        let dispatch = bag_fragment_dispatch(fp, op, env.var("u"), env.var("__f"));
        let observe = for1(env.var("__f"), {
            let env = env.push(&["__w"]);
            send(env.var("ret"), vec![par2(env.var("__w"), env.var("v"))])
        });
        par2(dispatch, observe)
    });

    let body = match_(
        env.var("u"),
        vec![
            Case {
                pattern: pat_tagged(fp, LAMBDA_REFLECT_LABEL, vec![pat_free(0)]),
                free_count: 1,
                body: strip_case(true),
            },
            Case {
                pattern: pat_wildcard(),
                free_count: 0,
                body: match_(
                    env.var("v"),
                    vec![
                        Case {
                            pattern: pat_tagged(fp, LAMBDA_REFLECT_LABEL, vec![pat_free(0)]),
                            free_count: 1,
                            body: strip_case(false),
                        },
                        Case { pattern: pat_wildcard(), free_count: 0, body: base_case },
                    ],
                ),
            },
        ],
    );
    persistent_contract(tag_par(fp, &float_merge_label(op)), 3, body).par
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lower::lower_language_def;
    use crate::rho_net::RhoNetProgram;
    use mettail_ast::language::LanguageDef;

    /// The REAL production Ambient definition (the a_s5c reconstruction path).
    fn production_ambient_def() -> LanguageDef {
        let source = include_str!("../../languages/src/ambient.rs");
        let start = source.find("language! {").expect("language! block") + "language! {".len();
        let end = source.rfind('}').expect("closing brace");
        crate::reconstruct_language_def(&source[start..end])
            .expect("the production Ambient body must reconstruct")
    }

    /// The REAL production Lambda definition.
    fn production_lambda_def() -> LanguageDef {
        let source = include_str!("../../languages/src/lambda.rs");
        let start = source.find("language! {").expect("language! block") + "language! {".len();
        let end = source.rfind('}').expect("closing brace");
        crate::reconstruct_language_def(&source[start..end])
            .expect("the production Lambda body must reconstruct")
    }

    fn lowered_for(def: &LanguageDef) -> crate::rho_net_lower::RhoNetLowered {
        let lowering = lower_language_def(def);
        RhoNetProgram::from_language_def(def, &lowering).lower_to_par(def, &lowering)
    }

    /// ★ The A-S5.8 satellite DERIVATION table for the production Ambient: the four
    /// prefix equations (`InNew`/`OutNew`/`OpenNew`/`AmbNew` — declaration order) derive
    /// the four hoist satellites, each with the float position at the single plain
    /// primary-category field (index 1 of 2); `ScopeExtrusion` derives the one `PPar`
    /// merge; `NewComm` (binder commutation) deliberately derives NOTHING (Q-NC).
    #[test]
    fn ambient_satellite_table_is_derived_from_the_equation_classification() {
        let def = production_ambient_def();
        let table = float_satellite_table(&def);
        assert_eq!(
            table.hoist,
            vec![
                ("PIn".to_string(), 1, 2),
                ("POut".to_string(), 1, 2),
                ("POpen".to_string(), 1, 2),
                ("PAmb".to_string(), 1, 2),
            ],
            "the hoist satellites are read off the prefix float equations, in declaration \
             order"
        );
        assert_eq!(
            table.merge_ops,
            vec!["PPar".to_string()],
            "the merge satellite is read off the ScopeExtrusion collection equation"
        );
    }

    /// ★ Gating: production Ambient is float-bearing and its lowering carries the
    /// 8-receiver family (dispatcher + merge + 4 hoists + first-time `^shift`/`^cmp`);
    /// production Lambda is NOT float-bearing and carries none (its artifact is
    /// byte-identical to pre-A-S5.8 — the a_s5_6 byte pins are the executable form).
    #[test]
    fn ambient_emits_the_eight_receiver_family_and_lambda_none() {
        let ambient = production_ambient_def();
        assert!(language_is_float_bearing(&ambient), "Ambient is float-bearing");
        let lowered = lowered_for(&ambient);
        let float = lowered.float().expect("Ambient carries the ^float family");
        assert_eq!(
            float.receives.len(),
            8,
            "^float + ^float-merge:PPar + 4 ^float-hoist + ^shift + ^cmp"
        );
        assert!(
            float.receives.iter().all(|receive| receive.persistent),
            "every family receiver is persistent"
        );
        let fp = lowered.language_fingerprint.as_str();
        let mut sources: Vec<Par> = float
            .receives
            .iter()
            .map(|receive| {
                receive.binds[0]
                    .source
                    .clone()
                    .expect("every family receiver has a ground source")
            })
            .collect();
        let mut expected = vec![
            tag_par(fp, FLOAT_RESERVED_LABEL),
            tag_par(fp, &float_hoist_label("PIn")),
            tag_par(fp, &float_hoist_label("POut")),
            tag_par(fp, &float_hoist_label("POpen")),
            tag_par(fp, &float_hoist_label("PAmb")),
            tag_par(fp, &float_merge_label("PPar")),
            tag_par(fp, crate::rho_net_lower::SHIFT_RESERVED_LABEL),
            tag_par(fp, crate::rho_net_lower::CMP_RESERVED_LABEL),
        ];
        sources.sort_by_key(|par| format!("{par:?}"));
        expected.sort_by_key(|par| format!("{par:?}"));
        assert_eq!(sources, expected, "the family rests on exactly the reserved roots");

        let lambda = production_lambda_def();
        assert!(!language_is_float_bearing(&lambda), "Lambda is not float-bearing");
        let lowered = lowered_for(&lambda);
        assert!(lowered.float().is_none(), "Lambda carries no ^float family");
    }

    /// ★ The `^shift` soup-arm GATE (F8-AM-5e): a bag-carrying language's `^shift` gains
    /// exactly one soup-peel arm per HashBag op plus the Nil leaf; a bag-free language's
    /// `^shift` is BYTE-IDENTICAL to pre-A-S5.8 (Lambda: 3 fixed arms + 2 object arms).
    #[test]
    fn shift_soup_arms_are_gated_on_hashbag_ops() {
        let ambient = production_ambient_def();
        let shift = shift_receiver_par(&ambient, "fp-gate");
        let body = shift.receives[0].body.as_ref().expect("shift body");
        // E-2-D ground guard + ^bound + ^lambda + ^free + 5 object arms (PZero/PIn/POut/POpen/PAmb;
        // PNew is the binder, PPar the collection — both excluded from C2) + 1 soup peel (PPar)
        // + 1 Nil = 11.
        assert_eq!(
            body.matches[0].cases.len(),
            11,
            "Ambient ^shift = E-2-D guard + 3 fixed + 5 object + soup + Nil arms"
        );

        let lambda = production_lambda_def();
        let shift = shift_receiver_par(&lambda, "fp-gate");
        let body = shift.receives[0].body.as_ref().expect("shift body");
        // E-2-D ground guard + ^bound + ^lambda + ^free + 1 object arm (App; Lam is the binder)
        // = 5 — NO soup or Nil arm (bag-op gate; byte-identity with pre-A-S5.8 modulo the guard).
        assert_eq!(
            body.matches[0].cases.len(),
            5,
            "Lambda ^shift = E-2-D guard + 3 fixed + 1 object arm (no soup/Nil, bag-op gate)"
        );
    }

    /// ★ The dispatcher's arm table for the production Ambient (module docs): binder,
    /// 4 hoist-dispatch ctors + 1 nullary, the PPar soup peel, Nil, the two passthroughs,
    /// and the fail-closed wildcard — 11 cases, patterns pairwise disjoint.
    #[test]
    fn ambient_dispatcher_arm_table() {
        let def = production_ambient_def();
        let table = float_satellite_table(&def);
        let dispatcher = float_dispatcher_par(&def, "fp-arms", &table);
        assert_eq!(dispatcher.receives.len(), 1, "the dispatcher is one receiver");
        let receive = &dispatcher.receives[0];
        assert!(receive.persistent);
        assert_eq!(receive.binds[0].patterns.len(), 2, "the frame is (t, ret)");
        let body = receive.body.as_ref().expect("dispatcher body");
        // 1 (^lambda) + 5 (PZero nullary + PIn/POut/POpen/PAmb hoist) + 1 (PPar peel)
        // + 1 (Nil) + 2 (passthroughs) + 1 (wildcard) = 11.
        assert_eq!(body.matches[0].cases.len(), 11, "the Ambient dispatcher arm table");
    }

    /// A float-bearing def whose bag op has NO collection float equation (a NewComm +
    /// prefix-float-only theory): the dispatcher emits NO soup-peel arm for it — a soup
    /// subject falls to the fail-closed wildcard, never a silent wrong float.
    #[test]
    fn bag_op_without_a_collection_equation_gets_no_peel_arm() {
        let fragment = r#"
            name: HoistOnly,
            types { Proc Name },
            terms {
                PZero . Proc ::= "0" ;
                PAmb . Proc ::= Name "[" Proc "]" ;
                PNew . ^x.p:[Name -> Proc] |- "new" "(" x "," p ")" : Proc;
                PPar . Proc ::= HashBag(Proc) sep "|" delim "{" "}" ;
            },
            equations {
                AmbNew . | x # N |- (PAmb N (PNew ^x.P)) = (PNew ^x.(PAmb N P));
            },
            rewrites {},
        "#;
        let def = syn::parse_str::<LanguageDef>(fragment).expect("the hoist-only def parses");
        let table = float_satellite_table(&def);
        assert_eq!(table.hoist.len(), 1, "one hoist satellite (PAmb)");
        assert!(table.merge_ops.is_empty(), "no collection equation ⟹ no merge satellite");
        let dispatcher = float_dispatcher_par(&def, "fp-hoistonly", &table);
        let body = dispatcher.receives[0].body.as_ref().expect("dispatcher body");
        // 1 (^lambda) + 2 (PZero, PAmb) + 0 peel + 1 (Nil — the def declares a bag op)
        // + 2 (passthroughs) + 1 (wildcard) = 7.
        assert_eq!(
            body.matches[0].cases.len(),
            7,
            "no peel arm without a collection float equation (soups fall to the wildcard)"
        );
    }
}
