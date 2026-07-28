//! The RECURSIVE lowering, retained verbatim as a differential ORACLE (M-2).
//!
//! # Why a twin exists at all
//!
//! [`super::lower_proc`] was converted from 87 mutually recursive functions into one
//! explicit-stack driver (`super::drive`). A conversion of that size cannot be reviewed
//! into confidence: "the author believes the two agree" is not a claim a reader can
//! check. What a reader *can* check is that the two implementations were run against the
//! same inputs and produced **byte-identical** `Par`s, error cases included.
//!
//! So the superseded implementation is kept here, verbatim — not paraphrased, not
//! simplified, not re-indented. Every function below is the exact text that stood in
//! `rholang_ast.rs` at commit `1b334d62`, moved by
//! `scratch/extract.py` (an item-span extractor that edits nothing inside a span).
//! Its call sites into the NON-recursive helpers (`binary_expr_par`, `send_par`,
//! `new_elist_par`, the 21 leaf `lower_arm_*` functions, …) resolve through
//! `use super::*` to the very same code the driver calls, so the differential compares
//! *traversal strategy* and nothing else.
//!
//! # What "verbatim" costs, and why it is worth it
//!
//! It costs ~1,700 lines that are compiled only under `cfg(test)`. It buys a test that
//! fails on the first term where the driver's child ORDER, ENVIRONMENT threading, or
//! ERROR precedence diverges — the three things a hand conversion gets wrong, and the
//! three things no type checker can catch.
//!
//! # ⚠ This module is not a fallback
//!
//! Nothing outside `cfg(test)` may call it. A second production lowering path would be
//! exactly the dual-runtime shape this tree forbids: two answers to "what does this term
//! lower to", with no mechanism deciding which is authoritative.

#![allow(clippy::all)]

use super::*;

pub fn lower_proc_in_env(proc: &Proc, env: &BoundEnv) -> Result<Par, RholangAstLowerError> {
    lower_proc(proc, env)
}

fn lower_proc(proc: &Proc, env: &BoundEnv) -> Result<Par, RholangAstLowerError> {
    // A-S4: exec submits the RAW parse tree (no pre-normalization), so the send-sugar nodes
    // (`x!()`, `c!(a,b)`, `@Nil!(q)`, `@n!(…)`, …) arrive unfolded. Desugar the HEAD node to its
    // canonical channel-first form first — a pure structural rearrangement (the same constructor
    // rewrite the rule's `fold` body performs, no value computation) — then lower that.
    if let Some(desugared) = desugar_surface_sugar_node(proc) {
        return lower_proc(&desugared, env);
    }
    match proc {
        Proc::PZero => lower_arm_p_zero(),
        Proc::PDrop(name) => lower_arm_p_drop(name, env),
        // L9-6b CONSTRUCTION arm: a `PFlt*` in VALUE position (a send payload, a
        // re-quote) elaborates to the reflected foreign term via the guest
        // reflector selected by its `tag`. The three delimiter forms are identical
        // at this level — same `Arc<FltNode>` payload.
        Proc::PFlt(node) | Proc::PFltFence(node) | Proc::PFltBrace(node) => {
            lower_arm_p_flt(node, env)
        },
        Proc::PPar(parts) => lower_arm_p_par(parts, env),
        // Bare infix parallel `a | b` (no outer braces). The WPDA parser emits the raw `PParInfix`
        // node; its `fold` to `PPar({a, b})` (`merge_pp_parallel`) runs only at eval time. Parallel
        // composition lowers to `Par::append` (associative/commutative over sends/receives/etc.),
        // which is exactly what lowering the folded `PPar` bag would produce. A free-process member
        // (e.g. `q` in `c!(p) | q`) lowers via its own `PVar` arm, so it rides this path too.
        Proc::PParInfix(left, right) => lower_arm_p_par_infix(left, right, env),
        Proc::POutput(channel, payload) => lower_arm_p_output(channel, payload, env),
        // ★ THE LOOKAHEAD ARMS — `x!(P)[*]` and `x!(P)[n]`.
        //
        // These do NOT lower to a send. `x!(P)[*]` is not "send P on x, and also explore": it is
        // an EXPLORATION whose results are delivered on `x`. So the lowering emits a speculation
        // REQUEST and no send at all; the data that eventually rest on `x` are the terminal terms
        // the engine computed.
        Proc::PLookaheadAll(subject) => lower_arm_p_lookahead_all(subject, env),
        Proc::PLookahead(subject, bound) => lower_arm_p_lookahead(subject, bound, env),
        // `for(...)` receive. Each `;`-separated row nests as the continuation of the previous one;
        // each row may be a single bind, a `&`-join, persistent (`<=`), empty (`<- n`), and may
        // carry a `where` guard. See [`lower_pfor_user`].
        Proc::PForUser(rows, body) => lower_arm_p_for_user(rows, body, env),
        Proc::PPersistOutput(channel, payload) => lower_arm_p_persist_output(channel, payload, env),
        // Rholang-style short sends `@P!(q)` / `@P!!(q)`. The WPDA parser emits the raw `*Short`
        // nodes (the `fold` to `POutput(NQuote(P), q)` / `PPersistOutput(NQuote(P), q)` runs only at
        // eval time), so lower them here with the SAME semantics: the channel is the quote of `P`,
        // i.e. `lower_name(NQuote(P)) == lower_proc(P)`. This is the canonical rho send idiom and the
        // body of most COMM examples (`@("c")!(@("OUT")!("p"))` nests two of these).
        Proc::POutputShort(channel_proc, payload) => {
            lower_arm_p_output_short(channel_proc, payload, env)
        },
        Proc::PPersistOutputShort(channel_proc, payload) => {
            lower_arm_p_persist_output_short(channel_proc, payload, env)
        },
        Proc::PNew(scope) => lower_arm_p_new(scope, env),
        // ── A-S4 cast purity: casts lower STRUCTURALLY ─────────────────────────────────────
        // A literal leaf is DATA (embedding `GInt(5)` is translation, not evaluation); a
        // structural node lowers to the machine's own metered `Expr` (`-a` → `ENeg`); anything
        // with no machine algebra (the macro-injected cross-type conversion constructors, an
        // unsubstituted category variable, a lambda) fails closed, typed and named. The former
        // `.try_eval()` arms computed those values host-side at lowering time.
        Proc::CastInt(value) => lower_arm_cast_int(value, env),
        Proc::CastBool(value) => lower_arm_cast_bool(value),
        Proc::CastStr(value) => lower_arm_cast_str(value),
        Proc::PVar(var) => lower_arm_p_var(var, env),
        Proc::Err => lower_arm_err(),
        Proc::CastBigRat(value) => lower_arm_cast_big_rat(value),
        Proc::CastFixed(value) => lower_arm_cast_fixed(value),
        Proc::CastFloat(value) => lower_arm_cast_float(value),
        Proc::CastBigInt(value) => lower_arm_cast_big_int(value),
        Proc::CastUInt32(value) => lower_arm_cast_u_int32(value),
        Proc::CastList(value) => lower_arm_cast_list(value, env),
        Proc::CastBag(value) => lower_arm_cast_bag(value, env),
        Proc::CastMap(value) => lower_arm_cast_map(value, env),
        Proc::CastSet(value) => lower_arm_cast_set(value, env),
        Proc::CastPathmap(value) => lower_arm_cast_pathmap(value, env),
        Proc::CastBytes(value) => lower_arm_cast_bytes(value),
        // ── A-S4 fold purity: EVERY width/precision fold trampolines on the machine ─────────
        // Fold nodes are lifted into fold-contract trampolines by [`lower_body_lifting_folds`]
        // BEFORE `lower_proc` descends (ground operands included — the former Tier-1 in-place
        // `try_eval_fold_proc` host fold is deleted). A fold reaching THIS arm sits in a position
        // the lift traversal cannot reach (inside a hashed-collection literal, a receive
        // pattern, or a fold with a non-ground width) — fail closed, typed and named.
        Proc::IntBinProc(..) => lower_arm_int_bin_proc(),
        Proc::UIntBinProc(..) => lower_arm_u_int_bin_proc(),
        Proc::FloatBinProc(..) => lower_arm_float_bin_proc(),
        Proc::FixedBinProc(..) => lower_arm_fixed_bin_proc(),
        Proc::BigintCastProc(..) => lower_arm_bigint_cast_proc(),
        Proc::BigratCastProc(..) => lower_arm_bigrat_cast_proc(),
        // ── A-S4 metered machine arithmetic (the Rholang face of the E3 pattern) ────────────
        // Operands lower STRUCTURALLY; the machine's reducer evaluates the expression with its
        // size-dependent primitive costs (f1r3node `reduce.rs`: `EPlus`/`EMinus`/`EMult`/`EDiv`/
        // `EMod`/`ENeg` over GInt/GDouble/GBigInt/GBigRat/GFixedPoint). String `+` is Rholang
        // `++` (`EPlusPlus`): when BOTH operands lower to ground string leaves the concat parity
        // arm is chosen; `EPlus` has no GString algebra.
        Proc::Add(a, b) => lower_arm_add(a, b, env),
        Proc::Sub(a, b) => lower_arm_sub(a, b, env),
        Proc::Mul(a, b) => lower_arm_mul(a, b, env),
        Proc::Div(a, b) => lower_arm_div(a, b, env),
        Proc::Mod(a, b) => lower_arm_mod(a, b, env),
        Proc::NegProc(a) => lower_arm_neg_proc(a, env),
        // Boolean/comparison guard operators (used by `where`-conditions and boolean payloads):
        // lower both operands and wrap in the matching Rholang comparison/logical `Expr`.
        Proc::Eq(a, b) => lower_arm_eq(a, b, env),
        Proc::Ne(a, b) => lower_arm_ne(a, b, env),
        Proc::Lt(a, b) => lower_arm_lt(a, b, env),
        Proc::Gt(a, b) => lower_arm_gt(a, b, env),
        Proc::LtEq(a, b) => lower_arm_lt_eq(a, b, env),
        Proc::GtEq(a, b) => lower_arm_gt_eq(a, b, env),
        Proc::And(a, b) => lower_arm_and(a, b, env),
        Proc::Or(a, b) => lower_arm_or(a, b, env),
        // M-0 — material implication. Rholang's expression algebra has no `EImplies`, and it
        // needs none: `a implies b ≡ (not a) or b`, and BOTH halves of that identity are
        // already emitted on this very path (`ENotBody` two arms below, `EOrBody` one arm
        // above) and both are already decided by `rho-pure-eval`
        // (`eval.rs::ENotBody`/`EOrBody` → `bool_binop("||", …)`). So `implies` costs the
        // machine exactly zero new surface: no new `ExprInstance`, no new evaluator arm, no
        // consensus-visible wire change.
        //
        // Built from the two shared assemblers rather than `lower_binary_expr` because the
        // negation must wrap ONLY the antecedent: `unary_expr_par` propagates the
        // antecedent's `locally_free`/`connective_used` onto the `ENot`, and
        // `binary_expr_par` then unions that with the consequent's — so the resulting `Par`
        // carries exactly the free-variable footprint of `a` ∪ `b`, as `Or` would.
        Proc::Implies(a, b) => lower_arm_implies(a, b, env),
        Proc::Not(a) => lower_arm_not(a, env),
        // M-1b — the SPATIAL satisfaction operator `t matches φ`.
        //
        // The TARGET is an ordinary term, lowered by `lower_proc`; the FORMULA is
        // compiled to a Rholang PATTERN by `rholang_formula::lower_formula_in_env`
        // (§18.1). The two are packed into ONE
        // `EMatchesBody(EMatches{target, pattern})`, which `rho-pure-eval` decides
        // through the caller-injected `SpatialMatch` oracle (M-1a, f1r3node
        // `99b7b1c4`) using the reducer's OWN spatial matcher. MeTTaIL never
        // matches anything itself on this path.
        //
        // ★ §18.1's static-`false` fold. When the formula is unsatisfiable by
        // construction, `t matches φ` is `false` for EVERY `t`, so the whole guard
        // collapses to `GBool(false)` and the matcher is never invoked. The
        // judgement (`formula::is_statically_false`) is syntactic and conservative
        // — it answers `true` only where the formula's own shape forces it — so
        // the fold can only ever be a missed optimization, never a wrong verdict.
        // The TARGET is still lowered, and its typed lowering error still
        // propagates: folding must not turn an ill-formed program into a
        // well-formed `false`.
        Proc::Matches(target, formula) => lower_arm_matches(target, formula, env),
        // M-1b — `PPar(φ, ψ)` is a PATTERN former, not a term former. It denotes
        // the separating conjunction, which is meaningful only as the right operand
        // of `matches` (where `rholang_formula` compiles it to a par-pattern). In
        // TERM position it has no denotation at all, so it fails CLOSED with a
        // typed error rather than being silently lowered as an ordinary parallel
        // composition — which would look like it worked while meaning something
        // different (`a | b` builds a process; `PPar(a,b)` asserts a split).
        // A program that wants parallel composition writes `{ a | b }` or `a | b`.
        Proc::SpatialPPar(..) => lower_arm_spatial_p_par(),
        // ── Methods routed to the reducer's OWN method table (option C, C1/C2) ───────────────
        //
        // Every name below is a key of `reduce.rs::method_table` (8197-8256). Dispatch is on the
        // EVALUATED receiver, so one arm covers every receiver type Rholang supports — `size` on
        // a Map and on a Set, `length` on a List and on a String, `nth` on an `EList`, an
        // `ETuple` AND a `GByteArray` (`reduce.rs:4106-4118`) — and a COMM-bound receiver works
        // exactly like a literal one. See [`lower_method`].
        //
        // `.toByteArray()` (C2) replaces the retired `rhoapi` schema fork
        // (`languages/proto/rholang_wire.proto` + `languages/src/rholang/wire.rs`), which encoded
        // a hex `GString` in protobuf BYTE order and could not encode any collection the Rholang
        // grammar actually produces.
        Proc::MToByteArray(m) => lower_arm_m_to_byte_array(m, env),
        //
        // ── C1 — the collection method surface (landed 2026-07-26) ──────────────────────────
        //
        // Each arm names a key of `reduce.rs::method_table` (`method_table` is at
        // `rholang/src/rust/interpreter/reduce.rs:8464` in the pinned `../f1r3node-rust-mettail`
        // worktree; the stale citation "8197-8256" that stood here predated several edits). The
        // reducer dispatches on the EVALUATED receiver, so a COMM-bound receiver works exactly
        // like a literal one.
        //
        // ★ SOUNDNESS RESTS ON A MEASURED CARRIER MAP, NOT ON THE METHOD NAME.
        //
        // Rholang has two carriers with no Rholang analog, and both survive lowering only as an
        // ENCODING: a `Bag` becomes `EList[GPrivate(RHOLANG_BAG_ABI_TAG), EList[pairs]]` (always
        // exactly 2 elements — see [`lower_bag`]), and a `Pathmap` becomes a plain `EMap`,
        // discarding the trie (divergence G — see [`lower_pathmap`]). Routing a method whose
        // interpreter implementation ACCEPTS that encoding would compute over the encoding and
        // answer something plausible and wrong. So every arm below was checked against the
        // accepted-carrier set of the interpreter method it targets, read from the method bodies
        // themselves (line numbers are the pinned worktree's):
        //
        //   method    interpreter accepts            reduce.rs   encoding reachable?
        //   ────────  ─────────────────────────────  ─────────   ───────────────────────────────
        //   get       EMap                                7593   Pathmap→EMap: KEY-FAITHFUL, ok
        //   set       EMap                                7707   Pathmap→EMap: key-faithful, ok
        //   contains  EMap, ESet, GBool                   7528   Pathmap→EMap: key-faithful, ok
        //   delete    EMap, ESet                          7444   Pathmap→EMap: key-faithful, ok
        //   keys      EMap, ESet                          7770   Pathmap→EMap: key-faithful, ok
        //   size      EMap, ESet                          7829   Bag→EList REJECTED ⇒ closed
        //   union     EMap, ESet, EPathmap                4336   Bag→EList REJECTED ⇒ closed
        //   diff      EMap, ESet, EPathmap                4463   Bag→EList REJECTED ⇒ closed
        //   add       ESet                                7378   —
        //   length    EList, GString, GByteArray          7893   ⚠ Bag→EList ACCEPTED ⇒ GATED
        //   nth       EList, ETuple, GByteArray           4078   ⚠ Bag→EList ACCEPTED ⇒ GATED
        //
        // The note that stood here asserted that routing would make `#{1|2|2}#.size()` answer the
        // tagged list's pair count. That is FALSE and was the reason C1 was held: `size_method`
        // (reduce.rs:7829) accepts only `EMapBody`/`ESetBody`, so a lowered `Bag` fails closed
        // with `MethodNotDefined { method: "size", other_type: "List" }`. The hazard is real but
        // lives on `length` and `nth` — the two routed methods that DO accept `EListBody` — and
        // those two are gated by [`lower_length`] / [`lower_nth`]. Measured, not hypothesized:
        // `rho_rholang_conformance.rs::c1_bag_encoding_is_rejected_by_every_routed_method`.
        Proc::MGet(m, k) => lower_arm_m_get(m, k, env),
        Proc::MSet(m, k, v) => lower_arm_m_set(m, k, v, env),
        Proc::MContains(m, k) => lower_arm_m_contains(m, k, env),
        Proc::MDelete(m, k) => lower_arm_m_delete(m, k, env),
        Proc::MUnion(a, b) => lower_arm_m_union(a, b, env),
        Proc::MSize(m) => lower_arm_m_size(m, env),
        Proc::MKeys(m) => lower_arm_m_keys(m, env),
        Proc::BDiff(a, b) => lower_arm_b_diff(a, b, env),
        Proc::SAdd(s, e) => lower_arm_s_add(s, e, env),
        Proc::LLength(l) => lower_arm_l_length(l, env),
        Proc::LNth(l, i) => lower_arm_l_nth(l, i, env),
        // `concat` is the one C1 method with NO `method_table` key: Rholang spells list/string
        // concatenation as the `++` OPERATOR (`EPlusPlus`), not as a method. Routing to `++`
        // still hands the operation to the reducer's own evaluator — the single-evaluator
        // property C1 exists for — so this is a name change, not a second implementation.
        //
        // ⚠ `combine_plus_plus` accepts `EList`, `EMap`, `ESet`, `GByteArray` and `GString`, so it
        // is a THIRD `EList`-accepting operation and takes the same bag gate as `length`/`nth`.
        // Ungated, `#{1|2}#.concat(#{3}#)` would concatenate the two ENCODINGS into a 4-element
        // list carrying two ABI tags — where the fold body, which accepts only (List, List) and
        // (Str, Str), answers `error`. See [`lower_concat`].
        Proc::LConcat(l, r) => lower_arm_l_concat(l, r, env),
        //
        // ── C1b — the Pathmap/Zipper family: routed, but UNREACHABLE until C4 ───────────────
        //
        // These are routed for the same reason as the rest — the reducer owns the semantics — but
        // every one of them requires an `EPathmapBody` or `EZipperBody` receiver, and Rholang's
        // `Pathmap` still lowers to `EMap` (divergence G). So on the machine they all fail closed
        // at REDUCE time with `MethodNotDefined { other_type: "map" }` rather than at LOWER time.
        // That is strictly more informative (it names the carrier that is actually wrong, which
        // is the thing C4 fixes) and it is still fail-closed — measured by
        // `c1b_pathmap_zipper_family_is_c4_blocked_at_the_carrier`.
        //
        // ★★ CORRECTION (C4 investigation, 2026-07-26 — MEASURED). The sentence that stood here,
        // "when C4 gives `Pathmap` its native carrier these arms start working with no further
        // change here", is FALSE, and the reason is worth more than the sentence.
        //
        // C4 is not a plumbing change, because **Rholang's `Pathmap` and Rholang's `EPathMap` are
        // different types**:
        //
        //   Rholang   `PathMapLit<Proc, Proc>`  a KEY→VALUE map. `{| 1 : 10 |}` is well formed and
        //                                       `pathmap_get` reads a value out at a key.
        //   Rholang   `EPathMap { ps }`         a SET OF PATHS. An element is its own key AND its
        //                                       own value.
        //
        // The second is measured three independent ways, not read off a comment:
        //
        //   1. the reducer answers `getPath() == getLeaf()` ▸ `true` at every leaf, and `atPath(k)`
        //      returns `k` itself
        //      (`rho_rholang_conformance.rs::c4_the_native_carrier_has_no_value_slot`);
        //   2. `models/.../pathmap_crate_type_mapper.rs::rholang_pathmap_to_e_pathmap` keeps only
        //      the trie's VALUES and discards its keys, so a key that is not its own value cannot
        //      survive one round trip through the mapper; and
        //   3. decisively, the GROUND WIRE. Since f1r3node `f34c2d7e` a ground `EPathMap`
        //      serialises as `bytes serialized_paths = 8` — the uncompressed trie-ordered KEY
        //      STREAM — and `merge_field` rebuilds `ps` by `decode_trie_path` of each key. Proto
        //      fields 6 and 7, RESERVED by that same commit, were "a retired value_form/
        //      value_entries experiment". A value distinct from its key is not merely unrepresented
        //      in the carrier: it is unrepresentable on the consensus wire, and that wire is the
        //      hash preimage.
        //
        // Two further measured consequences, both of which a naive flip would hit immediately:
        //
        //   * the native carrier REFUSES the Map surface — `get`/`set`/`contains`/`delete`/`keys`/
        //     `size`/`length` all answer `MethodNotDefined { other_type: "pathmap" }` on an
        //     `EPathmapBody` receiver. Five of them work on a `Pathmap` receiver TODAY only because
        //     this file emits an `EMap` (`c1_pathmap_methods_answer_through_the_emap_encoding`), so
        //     the flip trades twenty-two dead methods for seven newly dead ones unless each is
        //     re-expressed. Measured by `c4_the_native_carrier_refuses_the_map_method_surface`.
        //   * ✅ RETIRED 2026-07-27 — a SECOND blocker used to be recorded here and it no longer
        //     exists. A Rholang pathmap key is BARE by default (`{| 1 : 10 |}` has key `1`), and
        //     that element shape used to read back as `Nil` while `toNextLeaf` sat on a FIXED
        //     POINT, so a walk-until-`Nil` over `{| 1, 2, 3 |}` did not terminate; pointing
        //     `lower_pathmap` at `EPathmapBody` would have made the very enumeration surface C4
        //     exists to unlock HANG rather than work. f1r3node closed it in three commits —
        //     `5aacebc3` (the walk primitive `next_value_key` is total for a `from_key` that does
        //     not exist, which is where the fixed point actually lived: an upstream pathmap-0.2.2
        //     iteration rewind, NOT key termination), `0a6d2ce0` (`entry_key_at`: a reader holding
        //     the whole path `Par` asks the codec), and `7dcff96f` (`EZipper.cursor_kind`: the
        //     cursor carries its own Split/Bare/Prefix arm). No canonical key moved and no
        //     activation height was needed. Now measured SOUND by
        //     `rho_rholang_conformance.rs::c4_a_bare_element_reads_back_as_itself` and
        //     `::c4_a_bare_element_walk_visits_every_element_in_order`, and the bare row is back in
        //     `::c1_zipper_walk_exhaustion_terminates_within_leaf_count` where it was written.
        //     ⚠ So the VALUE SLOT below is the whole of what holds C4 — do not cite the walk.
        //
        // So C4 requires DECIDING what Rholang's value slot becomes — drop it, fuse it into the key
        // path (which changes what `getPath`/`getLeaf` mean), or add a value arm to the consensus
        // wire — and every answer costs something that is not a lowering's to spend. The decision
        // is presented, not taken here; `lower_pathmap` keeps emitting `EMap` until it is made.
        //
        // ★ `toNextLeaf` carries a DELIBERATE CROSS-ENDPOINT CONVENTION MISMATCH, and
        // mistranslating it does not error — it LOOPS FOREVER. The reducer reports an exhausted
        // walk as `Nil` (`Ok(Par::default())`); Rholang's fold body reports it as `Err(())`, the
        // house "failed navigation stays STUCK" form. See
        // `languages/src/rholang/zipper.rs::zipper_to_next_leaf` and its f1r3node twin
        // `rholang/tests/zipper_enumeration_spec.rs::to_next_leaf_returns_nil_when_exhausted`,
        // which name each other.
        //
        // What C1 owes the contract is that the `Nil` NEVER becomes a usable zipper on this side.
        // It cannot, and the reason is structural rather than defensive, so there is no predicate
        // here to call: `Nil` is not an `EZipperBody`, so the reducer's own zipper methods reject
        // it (`MethodNotDefined`), a walk cannot continue on it, and mettail has no decoder that
        // could lift it back — `RuntimeObservationValue` (`runtime/src/language.rs:108`) has no
        // zipper variant and `Proc::CastReadZipper` is deliberately NOT lowered (see
        // [`unsupported_construct_name`]). The property is proved end-to-end, against the real
        // reducer and BOUNDED so a violation fails instead of hanging, by
        // `rho_rholang_conformance.rs::c1_zipper_walk_exhaustion_terminates_within_leaf_count`.
        Proc::PGetSubtrie(m) => lower_arm_p_get_subtrie(m, env),
        Proc::PReadZipper(m) => lower_arm_p_read_zipper(m, env),
        Proc::PReadZipperAt(m, p) => lower_arm_p_read_zipper_at(m, p, env),
        Proc::PWriteZipper(m) => lower_arm_p_write_zipper(m, env),
        Proc::PWriteZipperAt(m, p) => lower_arm_p_write_zipper_at(m, p, env),
        Proc::RZGetLeaf(z) => lower_arm_r_z_get_leaf(z, env),
        Proc::RZDescendTo(z, rel) => lower_arm_r_z_descend_to(z, rel, env),
        Proc::RZChildCount(z) => lower_arm_r_z_child_count(z, env),
        Proc::RZDescendFirst(z) => lower_arm_r_z_descend_first(z, env),
        Proc::RZToNextSibling(z) => lower_arm_r_z_to_next_sibling(z, env),
        Proc::RZToPrevSibling(z) => lower_arm_r_z_to_prev_sibling(z, env),
        Proc::RZDescendIndexedBranch(z, i) => lower_arm_r_z_descend_indexed_branch(z, i, env),
        Proc::RZAscendOne(z) => lower_arm_r_z_ascend_one(z, env),
        Proc::RZAscend(z, n) => lower_arm_r_z_ascend(z, n, env),
        Proc::RZGetPath(z) => lower_arm_r_z_get_path(z, env),
        Proc::RZToNextLeaf(z) => lower_arm_r_z_to_next_leaf(z, env),
        Proc::RZLeafCount(z) => lower_arm_r_z_leaf_count(z, env),
        // ⚠ `setLeaf` is NOT routed, and it is the reason this file checks ARITY and SEMANTICS
        // rather than trusting a shared name. The two `setLeaf`s are different operations:
        //
        //   Rholang  `w.setLeaf(full, v)`  writes at the ABSOLUTE path given as an argument —
        //                                  `write_zipper_set_leaf` is
        //                                  `pm.set_val_at(encode_proc_path_entry(full), v)`
        //                                  (`languages/src/rholang/zipper.rs:529`). The zipper's
        //                                  focus is not consulted at all.
        //   Rholang  `z.setLeaf(v)`        APPENDS `v` to the map as a new element, at the path `v`
        //                                  derives for ITSELF. One argument. The zipper's focus is
        //                                  not consulted either — see the correction below.
        //
        // Emitting `EMethod("setLeaf")` with Rholang's two arguments would raise
        // `MethodArgumentNumberMismatch` — fail-closed, but for the WRONG reason, and it would
        // leave a mapping that becomes silently incorrect the moment anyone "fixes" the arity by
        // dropping `full`.
        //
        // ★★ CORRECTION (C4 investigation, 2026-07-26 — MEASURED). This note used to say Rholang's
        // `setLeaf` "writes at the zipper's CURRENT FOCUS", and to name `writeZipperAt(full)
        // .setLeaf(v)` as the rewrite that would express Rholang's meaning on the machine. **Both
        // halves were wrong, and the second was a trap.**
        //
        // `reduce.rs::set_leaf_method` does `pathmap.ps_make_mut().push(value)` on BOTH of its arms
        // and never reads `zipper.current_path`. Its doc comment still reads "set value at current
        // position" — a leftover from the retired value-arm experiment (proto fields 6/7, RESERVED
        // by `f34c2d7e`) — and that stale comment is what the old note was written from. Measured
        // by `rho_rholang_conformance.rs::c4_set_leaf_appends_an_element_and_ignores_the_focus`:
        // the map GROWS by one, the focused entry SURVIVES, the new element lands at its own path,
        // and `writeZipperAt("b").setLeaf(v)`, `writeZipperAt("c").setLeaf(v)` and
        // `writeZipper().setLeaf(v)` all produce the SAME map. `writeZipperAt(p)` is inert in front
        // of `setLeaf`.
        //
        // So the proposed rewrite would have written at the wrong place while looking correct in
        // review — the same "fix the arity by dropping the path" failure this note exists to
        // prevent, wearing a different hat.
        //
        // The REAL reason `setLeaf` cannot be routed is the C4 carrier fact above: a path-addressed
        // write needs a value slot, and `EPathMap` has none. `setLeaf(v)` is the only write the
        // carrier can express — *insert the element `v`*, whose key is derived from `v` — and
        // Rholang's `setLeaf(full, v)` is simply not that operation. It stays fail-closed and
        // named, and it will still be fail-closed after a naive carrier flip, because the obstacle
        // is the missing value slot rather than the argument count.
        //
        // The arity of every other routed zipper method was checked against the interpreter's own
        // `expected:` counts, and `setLeaf` is the only mismatch.
        Proc::WZSetSubtrie(w, rel) => lower_arm_w_z_set_subtrie(w, rel, env),
        Proc::WZRemoveLeaf(w) => lower_arm_w_z_remove_leaf(w, env),
        Proc::WZRemoveBranches(w) => lower_arm_w_z_remove_branches(w, env),
        Proc::WZGraft(w, rz) => lower_arm_w_z_graft(w, rz, env),
        Proc::WZJoinInto(w, rz) => lower_arm_w_z_join_into(w, rz, env),
        //
        // A-S4 fail-closed: every remaining construct has no machine algebra (bitwise ops,
        // cross-type conversions, the MeTTaIL-only collection residue, lambda forms, internal
        // gates). The typed error NAMES the construct; nothing silently host-evaluates.
        other => lower_arm_unsupported(other),
    }
}

#[inline(never)]
fn lower_arm_p_drop(
    name: &std::sync::Arc<Name>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_drop(name.as_ref(), env)
}

#[inline(never)]
fn lower_arm_p_par(
    parts: &mettail_runtime::HashBag<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    parts
        .iter_elements()
        .try_fold(Par::default(), |acc, part| Ok(acc.append(lower_proc(part, env)?)))
}

#[inline(never)]
fn lower_arm_p_par_infix(
    left: &std::sync::Arc<Proc>,
    right: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    Ok(lower_proc(left.as_ref(), env)?.append(lower_proc(right.as_ref(), env)?))
}

#[inline(never)]
fn lower_arm_p_output(
    channel: &std::sync::Arc<Name>,
    payload: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    let channel = lower_name(channel.as_ref(), env)?;
    let payload = lower_proc(payload.as_ref(), env)?;
    Ok(send_par(channel, vec![payload]))
}

#[inline(never)]
fn lower_arm_p_lookahead_all(
    subject: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    let (channel, payload) = lower_lookahead_operand(subject.as_ref(), env)?;
    Ok(crate::lookahead::spec_all_request(payload, channel))
}

#[inline(never)]
fn lower_arm_p_lookahead(
    subject: &std::sync::Arc<Proc>,
    bound: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    let (channel, payload) = lower_lookahead_operand(subject.as_ref(), env)?;
    let bound = lookahead_bound(bound.as_ref())?;
    Ok(crate::lookahead::spec_n_request(payload, bound, channel))
}

#[inline(never)]
fn lower_arm_p_for_user(
    rows: &Vec<ForRow>,
    body: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_pfor_user(rows, body.as_ref(), env)
}

#[inline(never)]
fn lower_arm_p_persist_output(
    channel: &std::sync::Arc<Name>,
    payload: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    let channel = lower_name(channel.as_ref(), env)?;
    let payload = lower_proc(payload.as_ref(), env)?;
    Ok(send_par_persistent(channel, vec![payload]))
}

#[inline(never)]
fn lower_arm_p_output_short(
    channel_proc: &std::sync::Arc<Proc>,
    payload: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    let channel = lower_proc(channel_proc.as_ref(), env)?;
    let payload = lower_proc(payload.as_ref(), env)?;
    Ok(send_par(channel, vec![payload]))
}

#[inline(never)]
fn lower_arm_p_persist_output_short(
    channel_proc: &std::sync::Arc<Proc>,
    payload: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    let channel = lower_proc(channel_proc.as_ref(), env)?;
    let payload = lower_proc(payload.as_ref(), env)?;
    Ok(send_par_persistent(channel, vec![payload]))
}

#[inline(never)]
fn lower_arm_p_new(
    scope: &mettail_runtime::Scope<Vec<mettail_runtime::Binder<String>>, std::sync::Arc<Proc>>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    let (binders, body) = scope.clone().unbind::<String>();
    let extended_env = extend_env(env, &binders);
    // A-S4: the `new` body is a fold-lift scope — a width/precision fold inside it
    // trampolines here (mirrors receive bodies and the top level).
    let body = lower_body_lifting_folds(body.as_ref(), &extended_env)?;
    let locally_free = filter_and_adjust_bitset(&body.locally_free, binders.len());

    let connective_used = body.connective_used;
    Ok(new_new_par(
        binders.len() as i32,
        body,
        Vec::new(),
        BTreeMap::new(),
        locally_free.clone(),
        locally_free,
        connective_used,
    ))
}

#[inline(never)]
fn lower_arm_cast_list(
    value: &std::sync::Arc<List>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_list(value.as_ref(), env)
}

#[inline(never)]
fn lower_arm_cast_bag(
    value: &std::sync::Arc<Bag>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_bag(value.as_ref(), env)
}

#[inline(never)]
fn lower_arm_cast_map(
    value: &std::sync::Arc<Map>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_map(value.as_ref(), env)
}

#[inline(never)]
fn lower_arm_cast_set(
    value: &std::sync::Arc<Set>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_set(value.as_ref(), env)
}

#[inline(never)]
fn lower_arm_cast_pathmap(
    value: &std::sync::Arc<Pathmap>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_pathmap(value.as_ref(), env)
}

#[inline(never)]
fn lower_arm_add(
    a: &std::sync::Arc<Proc>,
    b: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    let lhs = lower_proc(a.as_ref(), env)?;
    let rhs = lower_proc(b.as_ref(), env)?;
    if is_single_gstring_value(&lhs) && is_single_gstring_value(&rhs) {
        Ok(binary_expr_par(lhs, rhs, |p1, p2| {
            ExprInstance::EPlusPlusBody(EPlusPlus { p1, p2 })
        }))
    } else {
        Ok(binary_expr_par(lhs, rhs, |p1, p2| ExprInstance::EPlusBody(EPlus { p1, p2 })))
    }
}

#[inline(never)]
fn lower_arm_sub(
    a: &std::sync::Arc<Proc>,
    b: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_binary_expr(a.as_ref(), b.as_ref(), env, |p1, p2| {
        ExprInstance::EMinusBody(EMinus { p1, p2 })
    })
}

#[inline(never)]
fn lower_arm_mul(
    a: &std::sync::Arc<Proc>,
    b: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_binary_expr(a.as_ref(), b.as_ref(), env, |p1, p2| {
        ExprInstance::EMultBody(EMult { p1, p2 })
    })
}

#[inline(never)]
fn lower_arm_div(
    a: &std::sync::Arc<Proc>,
    b: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_binary_expr(a.as_ref(), b.as_ref(), env, |p1, p2| ExprInstance::EDivBody(EDiv { p1, p2 }))
}

#[inline(never)]
fn lower_arm_mod(
    a: &std::sync::Arc<Proc>,
    b: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_binary_expr(a.as_ref(), b.as_ref(), env, |p1, p2| ExprInstance::EModBody(EMod { p1, p2 }))
}

#[inline(never)]
fn lower_arm_neg_proc(
    a: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    let operand = lower_proc(a.as_ref(), env)?;
    Ok(unary_expr_par(operand, |p| ExprInstance::ENegBody(ENeg { p })))
}

#[inline(never)]
fn lower_arm_eq(
    a: &std::sync::Arc<Proc>,
    b: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_binary_expr(a.as_ref(), b.as_ref(), env, |p1, p2| ExprInstance::EEqBody(EEq { p1, p2 }))
}

#[inline(never)]
fn lower_arm_ne(
    a: &std::sync::Arc<Proc>,
    b: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_binary_expr(a.as_ref(), b.as_ref(), env, |p1, p2| ExprInstance::ENeqBody(ENeq { p1, p2 }))
}

#[inline(never)]
fn lower_arm_lt(
    a: &std::sync::Arc<Proc>,
    b: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_binary_expr(a.as_ref(), b.as_ref(), env, |p1, p2| ExprInstance::ELtBody(ELt { p1, p2 }))
}

#[inline(never)]
fn lower_arm_gt(
    a: &std::sync::Arc<Proc>,
    b: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_binary_expr(a.as_ref(), b.as_ref(), env, |p1, p2| ExprInstance::EGtBody(EGt { p1, p2 }))
}

#[inline(never)]
fn lower_arm_lt_eq(
    a: &std::sync::Arc<Proc>,
    b: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_binary_expr(a.as_ref(), b.as_ref(), env, |p1, p2| ExprInstance::ELteBody(ELte { p1, p2 }))
}

#[inline(never)]
fn lower_arm_gt_eq(
    a: &std::sync::Arc<Proc>,
    b: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_binary_expr(a.as_ref(), b.as_ref(), env, |p1, p2| ExprInstance::EGteBody(EGte { p1, p2 }))
}

#[inline(never)]
fn lower_arm_and(
    a: &std::sync::Arc<Proc>,
    b: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_binary_expr(a.as_ref(), b.as_ref(), env, |p1, p2| ExprInstance::EAndBody(EAnd { p1, p2 }))
}

#[inline(never)]
fn lower_arm_or(
    a: &std::sync::Arc<Proc>,
    b: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_binary_expr(a.as_ref(), b.as_ref(), env, |p1, p2| ExprInstance::EOrBody(EOr { p1, p2 }))
}

#[inline(never)]
fn lower_arm_implies(
    a: &std::sync::Arc<Proc>,
    b: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    let antecedent = lower_proc(a.as_ref(), env)?;
    let consequent = lower_proc(b.as_ref(), env)?;
    let negated = unary_expr_par(antecedent, |p| ExprInstance::ENotBody(ENot { p }));
    Ok(binary_expr_par(negated, consequent, |p1, p2| {
        ExprInstance::EOrBody(EOr { p1, p2 })
    }))
}

#[inline(never)]
fn lower_arm_not(a: &std::sync::Arc<Proc>, env: &BoundEnv) -> Result<Par, RholangAstLowerError> {
    let operand = lower_proc(a.as_ref(), env)?;
    Ok(unary_expr_par(operand, |p| ExprInstance::ENotBody(ENot { p })))
}

#[inline(never)]
fn lower_arm_matches(
    target: &std::sync::Arc<Proc>,
    formula: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    let target = lower_proc(target.as_ref(), env)?;
    if mettail_languages::rholang::formula::is_statically_false(formula.as_ref()) {
        let mut folded = new_gbool_par(false, Vec::new(), false);
        folded.locally_free = target.locally_free;
        return Ok(folded);
    }
    let pattern = crate::rholang_formula::lower_formula_in_env(formula.as_ref(), env)?;
    // `connective_used` is NOT propagated from the pattern. The result of
    // `matches` is a BOOLEAN expression, not a pattern: it is the one place
    // in the lowering where a connective legitimately appears inside a Par
    // that is itself not a pattern. This mirrors f1r3node's own
    // `normalize_p_matches`, which builds the `EMatches` from a target
    // normalized in the OUTER scope and a pattern normalized in a PUSHED
    // scope with a fresh free map, and returns the LEFT operand's free map.
    let locally_free = union(target.locally_free.clone(), pattern.locally_free.clone());
    let mut par = Par::default().with_exprs(vec![Expr {
        expr_instance: Some(ExprInstance::EMatchesBody(EMatches {
            target: Some(target),
            pattern: Some(pattern),
        })),
    }]);
    par.locally_free = locally_free;
    par.connective_used = false;
    Ok(par)
}

#[inline(never)]
fn lower_arm_m_to_byte_array(
    m: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("toByteArray", m.as_ref(), &[], env)
}

#[inline(never)]
fn lower_arm_m_get(
    m: &std::sync::Arc<Proc>,
    k: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("get", m.as_ref(), &[k.as_ref()], env)
}

#[inline(never)]
fn lower_arm_m_set(
    m: &std::sync::Arc<Proc>,
    k: &std::sync::Arc<Proc>,
    v: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("set", m.as_ref(), &[k.as_ref(), v.as_ref()], env)
}

#[inline(never)]
fn lower_arm_m_contains(
    m: &std::sync::Arc<Proc>,
    k: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("contains", m.as_ref(), &[k.as_ref()], env)
}

#[inline(never)]
fn lower_arm_m_delete(
    m: &std::sync::Arc<Proc>,
    k: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("delete", m.as_ref(), &[k.as_ref()], env)
}

#[inline(never)]
fn lower_arm_m_union(
    a: &std::sync::Arc<Proc>,
    b: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("union", a.as_ref(), &[b.as_ref()], env)
}

#[inline(never)]
fn lower_arm_m_size(m: &std::sync::Arc<Proc>, env: &BoundEnv) -> Result<Par, RholangAstLowerError> {
    lower_method("size", m.as_ref(), &[], env)
}

#[inline(never)]
fn lower_arm_m_keys(m: &std::sync::Arc<Proc>, env: &BoundEnv) -> Result<Par, RholangAstLowerError> {
    lower_method("keys", m.as_ref(), &[], env)
}

#[inline(never)]
fn lower_arm_b_diff(
    a: &std::sync::Arc<Proc>,
    b: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("diff", a.as_ref(), &[b.as_ref()], env)
}

#[inline(never)]
fn lower_arm_s_add(
    s: &std::sync::Arc<Proc>,
    e: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("add", s.as_ref(), &[e.as_ref()], env)
}

#[inline(never)]
fn lower_arm_l_length(
    l: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_length(l.as_ref(), env)
}

#[inline(never)]
fn lower_arm_l_nth(
    l: &std::sync::Arc<Proc>,
    i: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_nth(l.as_ref(), i.as_ref(), env)
}

#[inline(never)]
fn lower_arm_l_concat(
    l: &std::sync::Arc<Proc>,
    r: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_concat(l.as_ref(), r.as_ref(), env)
}

#[inline(never)]
fn lower_arm_p_get_subtrie(
    m: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("getSubtrie", m.as_ref(), &[], env)
}

#[inline(never)]
fn lower_arm_p_read_zipper(
    m: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("readZipper", m.as_ref(), &[], env)
}

#[inline(never)]
fn lower_arm_p_read_zipper_at(
    m: &std::sync::Arc<Proc>,
    p: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("readZipperAt", m.as_ref(), &[p.as_ref()], env)
}

#[inline(never)]
fn lower_arm_p_write_zipper(
    m: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("writeZipper", m.as_ref(), &[], env)
}

#[inline(never)]
fn lower_arm_p_write_zipper_at(
    m: &std::sync::Arc<Proc>,
    p: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("writeZipperAt", m.as_ref(), &[p.as_ref()], env)
}

#[inline(never)]
fn lower_arm_r_z_get_leaf(
    z: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("getLeaf", z.as_ref(), &[], env)
}

#[inline(never)]
fn lower_arm_r_z_descend_to(
    z: &std::sync::Arc<Proc>,
    rel: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("descendTo", z.as_ref(), &[rel.as_ref()], env)
}

#[inline(never)]
fn lower_arm_r_z_child_count(
    z: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("childCount", z.as_ref(), &[], env)
}

#[inline(never)]
fn lower_arm_r_z_descend_first(
    z: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("descendFirst", z.as_ref(), &[], env)
}

#[inline(never)]
fn lower_arm_r_z_to_next_sibling(
    z: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("toNextSibling", z.as_ref(), &[], env)
}

#[inline(never)]
fn lower_arm_r_z_to_prev_sibling(
    z: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("toPrevSibling", z.as_ref(), &[], env)
}

#[inline(never)]
fn lower_arm_r_z_descend_indexed_branch(
    z: &std::sync::Arc<Proc>,
    i: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("descendIndexedBranch", z.as_ref(), &[i.as_ref()], env)
}

#[inline(never)]
fn lower_arm_r_z_ascend_one(
    z: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("ascendOne", z.as_ref(), &[], env)
}

#[inline(never)]
fn lower_arm_r_z_ascend(
    z: &std::sync::Arc<Proc>,
    n: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("ascend", z.as_ref(), &[n.as_ref()], env)
}

#[inline(never)]
fn lower_arm_r_z_get_path(
    z: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("getPath", z.as_ref(), &[], env)
}

#[inline(never)]
fn lower_arm_r_z_to_next_leaf(
    z: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("toNextLeaf", z.as_ref(), &[], env)
}

#[inline(never)]
fn lower_arm_r_z_leaf_count(
    z: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("leafCount", z.as_ref(), &[], env)
}

#[inline(never)]
fn lower_arm_w_z_set_subtrie(
    w: &std::sync::Arc<Proc>,
    rel: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("setSubtrie", w.as_ref(), &[rel.as_ref()], env)
}

#[inline(never)]
fn lower_arm_w_z_remove_leaf(
    w: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("removeLeaf", w.as_ref(), &[], env)
}

#[inline(never)]
fn lower_arm_w_z_remove_branches(
    w: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("removeBranches", w.as_ref(), &[], env)
}

#[inline(never)]
fn lower_arm_w_z_graft(
    w: &std::sync::Arc<Proc>,
    rz: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("graft", w.as_ref(), &[rz.as_ref()], env)
}

#[inline(never)]
fn lower_arm_w_z_join_into(
    w: &std::sync::Arc<Proc>,
    rz: &std::sync::Arc<Proc>,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    lower_method("joinInto", w.as_ref(), &[rz.as_ref()], env)
}

fn lower_binary_expr(
    a: &Proc,
    b: &Proc,
    env: &BoundEnv,
    build: impl FnOnce(Option<Par>, Option<Par>) -> ExprInstance,
) -> Result<Par, RholangAstLowerError> {
    let lhs = lower_proc(a, env)?;
    let rhs = lower_proc(b, env)?;
    Ok(binary_expr_par(lhs, rhs, build))
}

fn lower_method(
    method_name: &str,
    target: &Proc,
    arguments: &[&Proc],
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    let target_par = lower_proc(target, env)?;
    let mut argument_pars = Vec::with_capacity(arguments.len());
    for argument in arguments {
        argument_pars.push(lower_proc(argument, env)?);
    }

    let mut locally_free = target_par.locally_free.clone();
    let mut connective_used = target_par.connective_used;
    for argument in &argument_pars {
        locally_free = union(locally_free, argument.locally_free.clone());
        connective_used = connective_used || argument.connective_used;
    }

    let mut par = Par::default().with_exprs(vec![Expr {
        expr_instance: Some(ExprInstance::EMethodBody(EMethod {
            method_name: method_name.to_string(),
            target: Some(target_par),
            arguments: argument_pars,
            locally_free: locally_free.clone(),
            connective_used,
        })),
    }]);
    par.locally_free = locally_free;
    par.connective_used = connective_used;
    Ok(par)
}

fn lower_length(target: &Proc, env: &BoundEnv) -> Result<Par, RholangAstLowerError> {
    match receiver_is_literal_bag(target) {
        true => Err(RholangAstLowerError::UnsupportedProc(
            "#{…}#.length() bag cardinality (no Rholang analog — the machine would measure the \
             2-element bag ABI encoding, not the multiset; C3 residue)",
        )),
        false => lower_method("length", target, &[], env),
    }
}

fn lower_nth(target: &Proc, index: &Proc, env: &BoundEnv) -> Result<Par, RholangAstLowerError> {
    match receiver_is_literal_bag(target) {
        true => Err(RholangAstLowerError::UnsupportedProc(
            "#{…}#.nth(i) bag indexing (no Rholang analog — the machine would index the 2-element \
             bag ABI encoding, not the multiset; C3 residue)",
        )),
        false => lower_method("nth", target, &[index], env),
    }
}

fn lower_concat(left: &Proc, right: &Proc, env: &BoundEnv) -> Result<Par, RholangAstLowerError> {
    match receiver_is_literal_bag(left) || receiver_is_literal_bag(right) {
        true => Err(RholangAstLowerError::UnsupportedProc(
            "#{…}#.concat(…) bag concatenation (no Rholang analog — `++` would concatenate the \
             2-element bag ABI encodings, tags and all; C3 residue)",
        )),
        false => Ok(binary_expr_par(lower_proc(left, env)?, lower_proc(right, env)?, |p1, p2| {
            ExprInstance::EPlusPlusBody(EPlusPlus { p1, p2 })
        })),
    }
}

fn lower_body_lifting_folds(body: &Proc, env: &BoundEnv) -> Result<Par, RholangAstLowerError> {
    let Some((operand, kind, width)) = find_fold(body) else {
        return lower_proc(body, env);
    };
    let site_index = HELD_FOLD_SITES.with(|sites| sites.borrow().len()) as u8;
    // ★ #36 S5: the site is scoped to the language it belongs to. `site_index` alone made two
    // co-installed fold-bearing languages collide on `[0xF0, 0]` / `0xF000`.
    let fingerprint = held_fold_language_fingerprint();
    HELD_FOLD_SITES.with(|sites| {
        sites.borrow_mut().push(FoldSpec {
            kind,
            width,
            site_index,
            fingerprint: fingerprint.clone(),
        })
    });
    let channel = fold_channel(site_index, &fingerprint);

    // Fresh result binders: `new ret` (innermost) and the `for`-bound `r`.
    let ret_var = mettail_runtime::get_or_create_var(format!("__mtl_ret_{site_index}"));
    let r_var = mettail_runtime::get_or_create_var(format!("__mtl_r_{site_index}"));
    let r_drop = Proc::PDrop(Arc::new(Name::NVar(OrdVar(Var::Free(r_var.clone())))));

    let mut replaced = false;
    let transformed = replace_fold(body, &r_drop, &mut replaced);

    // `new ret` shifts `env` by 1; the `for` then binds `r` (index 0), `ret` (index 1).
    let env_new = extend_env(env, &[Binder(ret_var)]);
    let env_for = extend_env(&env_new, &[Binder(r_var)]);

    // Send `@channel!(operand, ret)` at the `new` level (ret = boundvar 0). A statically ground
    // operand EXPRESSION (`5 + 3`) lowers to its metered `Expr`; the machine evaluates it at
    // send time, so the contract always receives a ground value leaf.
    let operand_par = lower_proc(&operand, &env_new)?;
    let ret_channel = new_boundvar_par(0, Vec::new(), false);
    let send = send_par(channel, vec![operand_par, ret_channel.clone()]);

    // `for(@r <- ret){ <recursively-lifted transformed body> }`.
    let for_body = lower_body_lifting_folds(&transformed, &env_for)?;
    let bind = ReceiveBind {
        patterns: vec![new_freevar_par(0, Vec::new())],
        source: Some(ret_channel),
        remainder: None,
        free_count: 1,
    };
    let recv_locally_free = receive_locally_free(&[bind.clone()], &for_body, 1);
    let recv = new_receive_par(
        vec![bind],
        for_body,
        false,
        false,
        1,
        recv_locally_free.clone(),
        false,
        recv_locally_free,
        false,
    );

    // `new ret { send | recv }`.
    let inner = send.append(recv);
    let new_locally_free = filter_and_adjust_bitset(&inner.locally_free, 1);
    Ok(new_new_par(
        1,
        inner,
        Vec::new(),
        BTreeMap::new(),
        new_locally_free.clone(),
        new_locally_free,
        false,
    ))
}

fn lower_bag(bag: &Bag, env: &BoundEnv) -> Result<Par, RholangAstLowerError> {
    match bag {
        Bag::BagLit(entries) => {
            let mut entries = entries.iter().collect::<Vec<_>>();
            entries.sort_by_key(|(item, _)| *item);

            let mut pairs = Vec::with_capacity(entries.len());
            for (item, count) in entries {
                let count = i64::try_from(count).map_err(|_| {
                    RholangAstLowerError::UnsupportedProc("bag multiplicity exceeds i64")
                })?;
                let item = lower_proc(item, env)?;
                let count = new_gint_par(count, Vec::new(), false);
                let pair_locally_free =
                    union(item.locally_free.clone(), count.locally_free.clone());
                let pair_connective = item.connective_used || count.connective_used;
                pairs.push(new_elist_par(
                    vec![item, count],
                    pair_locally_free.clone(),
                    pair_connective,
                    None,
                    pair_locally_free,
                    pair_connective,
                ));
            }

            let pairs_locally_free = locally_free_union(&pairs);
            let pairs_connective = any_connective_used(&pairs);
            let pairs = new_elist_par(
                pairs,
                pairs_locally_free.clone(),
                pairs_connective,
                None,
                pairs_locally_free,
                pairs_connective,
            );
            let tag = GPrivateBuilder::new_par_from_string(crate::RHOLANG_BAG_ABI_TAG.to_string());
            let locally_free = union(tag.locally_free.clone(), pairs.locally_free.clone());

            let connective_used = tag.connective_used || pairs.connective_used;
            Ok(new_elist_par(
                vec![tag, pairs],
                locally_free.clone(),
                connective_used,
                None,
                locally_free,
                connective_used,
            ))
        },
        _ => Err(RholangAstLowerError::UnsupportedProc("computed bag process")),
    }
}

fn lower_list(list: &List, env: &BoundEnv) -> Result<Par, RholangAstLowerError> {
    match list {
        List::ListLit(items) => {
            let items = items
                .iter()
                .map(|item| lower_proc(item, env))
                .collect::<Result<Vec<_>, _>>()?;
            let locally_free = locally_free_union(&items);
            let connective_used = any_connective_used(&items);
            Ok(new_elist_par(
                items,
                locally_free.clone(),
                connective_used,
                None,
                locally_free,
                connective_used,
            ))
        },
        _ => Err(RholangAstLowerError::UnsupportedProc("computed list process")),
    }
}

fn lower_map(map: &Map, env: &BoundEnv) -> Result<Par, RholangAstLowerError> {
    match map {
        Map::MapLit(entries) => {
            let mut pairs = Vec::with_capacity(entries.len());
            let mut locally_free = Vec::new();

            let mut connective_used = false;

            for (key, value) in entries.iter() {
                let key = lower_proc(key, env)?;
                let value = lower_proc(value, env)?;
                locally_free = union(
                    locally_free,
                    union(key.locally_free.clone(), value.locally_free.clone()),
                );
                connective_used |= key.connective_used || value.connective_used;
                pairs.push(new_key_value_pair(key, value));
            }

            Ok(new_emap_par(
                pairs,
                locally_free.clone(),
                connective_used,
                None,
                locally_free,
                connective_used,
            ))
        },
        _ => Err(RholangAstLowerError::UnsupportedProc("computed map process")),
    }
}

fn lower_set(set: &Set, env: &BoundEnv) -> Result<Par, RholangAstLowerError> {
    match set {
        Set::SetLit(items) => {
            // `HashSetLit` iterates in hash order; sort by `Proc` `Ord` for a deterministic `ESet`
            // (mirrors how `lower_bag` sorts its entries).
            let mut items: Vec<&Proc> = items.iter().collect();
            items.sort();
            let elements = items
                .into_iter()
                .map(|item| lower_proc(item, env))
                .collect::<Result<Vec<_>, _>>()?;
            let locally_free = locally_free_union(&elements);
            let connective_used = any_connective_used(&elements);
            Ok(new_eset_par(
                elements,
                locally_free.clone(),
                connective_used,
                None,
                locally_free,
                connective_used,
            ))
        },
        _ => Err(RholangAstLowerError::UnsupportedProc("computed set process")),
    }
}

fn lower_pathmap(pathmap: &Pathmap, env: &BoundEnv) -> Result<Par, RholangAstLowerError> {
    match pathmap {
        Pathmap::PathmapLit(entries) => {
            // A pathmap is key/value like a map; lower to a Rholang `EMap` (mirrors `lower_map`).
            // `PathMapLit` (insertion-order) is sorted by key for a deterministic encoding.
            let mut entries: Vec<(&Proc, &Proc)> = entries.iter().collect();
            entries.sort_by(|(key_a, _), (key_b, _)| key_a.cmp(key_b));

            let mut pairs = Vec::with_capacity(entries.len());
            let mut locally_free = Vec::new();
            let mut connective_used = false;
            for (key, value) in entries {
                let key = lower_proc(key, env)?;
                let value = lower_proc(value, env)?;
                locally_free = union(
                    locally_free,
                    union(key.locally_free.clone(), value.locally_free.clone()),
                );
                connective_used |= key.connective_used || value.connective_used;
                pairs.push(new_key_value_pair(key, value));
            }

            Ok(new_emap_par(
                pairs,
                locally_free.clone(),
                connective_used,
                None,
                locally_free,
                connective_used,
            ))
        },
        _ => Err(RholangAstLowerError::UnsupportedProc("computed pathmap process")),
    }
}

fn lower_pfor_user(
    rows: &[ForRow],
    body: &Proc,
    env: &BoundEnv,
) -> Result<Par, RholangAstLowerError> {
    if rows.is_empty() {
        // No rows left: the body is the whole process.
        return lower_body_lifting_folds(body, env);
    }
    let row = &rows[0];

    // Continuation = the remaining rows (nested `PForUser`) or the body when this is the last row.
    let continuation = if rows.len() > 1 {
        Proc::PForUser(rows[1..].to_vec(), Arc::new(body.clone()))
    } else {
        body.clone()
    };

    let (binds, persistent, cond) = decompose_for_row(row)?;
    if binds.is_empty() {
        return Err(RholangAstLowerError::EmptyInputJoin);
    }

    // Lower each bind: source channel (OUTER env) + pattern `Par`(s) + the bind's local binders.
    // #14: binders accumulate as `ReceiveSlot`s IN BIND ORDER — a moniker `PVar` binder or a
    // name-keyed FLT hole — so an FLT hole and a moniker binder that co-occur in a `&`-join share
    // one coherent de-Bruijn numbering (a hole's global level then follows from its slot position,
    // not the FLT bind's local `FreeVar` numbering).
    let mut binds_rho: Vec<ReceiveBind> = Vec::with_capacity(binds.len());
    let mut slots: Vec<ReceiveSlot> = Vec::new();
    for bind in &binds {
        let channel = bind_channel_name(bind)
            .ok_or(RholangAstLowerError::UnsupportedProc("for-row channel"))?;
        let source = lower_name(channel, env)?;

        if let Some(node) = bind_flt_node(bind) {
            let (pattern, free_count, hole_names) = lower_flt_pattern(node.as_ref(), env)?;
            // The FLT bind contributes one hole slot per `FreeVar`, in `FreeVar` order.
            for name in hole_names {
                slots.push(ReceiveSlot::Hole(name));
            }
            binds_rho.push(ReceiveBind {
                patterns: vec![pattern],
                source: Some(source),
                remainder: None,
                free_count,
            });
            continue;
        }

        let (patterns, bind_binders) = if is_empty_bind(bind) {
            // `for(_ <- c)` — match (and discard) any single message; no bound variables.
            (vec![new_wildcard_par(Vec::new(), false)], Vec::new())
        } else {
            let pat_proc = bind_pattern_proc(bind)
                .ok_or(RholangAstLowerError::UnsupportedProc("for-row pattern"))?;
            let mut counter = 0i32;
            let mut bind_binders = Vec::new();
            let pat_par = lower_pattern_proc(&pat_proc, &mut counter, &mut bind_binders)?;
            (vec![pat_par], bind_binders)
        };

        let free_count = bind_binders.len() as i32;
        for binder in bind_binders {
            slots.push(ReceiveSlot::Moniker(binder));
        }
        binds_rho.push(ReceiveBind {
            patterns,
            source: Some(source),
            remainder: None,
            free_count,
        });
    }

    // #14: ONE unified continuation scope over the receive's binder slots (moniker + FLT holes
    // interleaved in bind order). `receive_binder_count` is the receive's total bound-var width
    // used by the `locally_free` accounting below. For a moniker-only receive this is byte-identical
    // to the former `extend_env(env, &all_binders)` (same slot order, same `width - 1 - i` levels).
    let receive_binder_count = slots.len();
    let extended_env = env.extend_slots(&slots);

    // The continuation is lowered under the extended env: a nested row recurses; otherwise this is
    // the innermost user body, where held folds are lifted into Dovetail trampolines.
    let lowered_body = match &continuation {
        // The nesting shortcut goes straight to `lower_pfor_user`, bypassing `lower_proc` and
        // with it the surface-sugar expansion, so it is valid only when the inner `for` IS
        // already a receive. A `!?` query bind denotes a `new`-scoped `send | receive`; it
        // takes the ordinary body route and is expanded at `lower_proc`'s head. This mirrors
        // the driver's guard in `schedule_for_body` — the two must agree here or the
        // differential is comparing two different languages.
        Proc::PForUser(rest_rows, rest_body) if !pfor_user_still_has_query_rows(rest_rows) => {
            lower_pfor_user(rest_rows, rest_body.as_ref(), &extended_env)?
        },
        other => lower_body_lifting_folds(other, &extended_env)?,
    };

    // `where`-guard (if any) is an ordinary boolean `Proc`, lowered in the extended env.
    let condition = match &cond {
        Some(guard) => Some(lower_proc(guard, &extended_env)?),
        None => None,
    };

    // ════════════════════════════════════════════════════════════════════════════════════════
    // S-D0 — COMPILE-TIME GUARD DISCHARGE (the decision site)
    // ════════════════════════════════════════════════════════════════════════════════════════
    //
    // ★ POSITION IS LOAD-BEARING. The discharge happens HERE — after the guard is lowered, and
    // BEFORE the `locally_free` union below. Discharging *after* the union would leave the
    // receive carrying bits contributed by a condition that is no longer in the emitted `Par`:
    // a bitset inconsistent with its own term, i.e. a latent scoping bug in every downstream
    // consumer of `locally_free` (substitution, `connective_used` derivation, sorting).
    //
    // The decision is recorded by simply NOT populating `Receive.condition` — f1r3node's
    // `check_commit` short-circuits `None` to `true`, which is exactly what the guard would
    // have answered. `None`, never `Some(Par::default())`: the empty-`Par` form is a *different*
    // artifact that `reduce.rs` happens to collapse, and an artifact difference is a consensus
    // difference. See `crate::guard_discharge` for the soundness argument and the fence.
    let condition = match (&cond, condition) {
        (Some(guard), Some(cond_par)) if env.options.guard_discharge => {
            // The routing is CONSULTED, not derived (the ROUTE-SITE INVARIANT): a populated
            // `Receive.condition` is by construction what the Rho machine's `check_commit`
            // reads, so this guard is `MachineEvaluated` as a structural fact about the
            // artifact being emitted. When the wiring plan's `GuardPlan` lands, the plan's
            // recorded route is passed here instead — `classify` still decides no routing.
            let host_verdict = eval_guard_bool(guard);
            let outcome = guard_discharge::classify(
                host_verdict,
                &cond_par,
                guard_discharge::GuardRouting::MachineEvaluated,
            );
            record_guard_outcome(outcome, guard);
            match outcome.omits_condition() {
                true => None,
                // Residual AND Refuted both emit the condition verbatim: a `for` that can never
                // fire is a RESTING, OBSERVABLE continuation (it is in the normal form, the
                // state hash and storage), so folding it away would be unsound. Refutation is
                // diagnostic only — the artifact is byte-identical.
                false => Some(cond_par),
            }
        },
        (_, condition) => condition,
    };

    let bind_count = receive_binder_count as i32;
    let mut locally_free = receive_locally_free(&binds_rho, &lowered_body, receive_binder_count);
    if let Some(cond_par) = &condition {
        // The guard is lowered in the same extended env as the body, so adjust its `locally_free`
        // the same way (drop this receive's own bound vars, shift outer references down).
        locally_free = union(
            locally_free,
            filter_and_adjust_bitset(&cond_par.locally_free, receive_binder_count),
        );
    }

    // M-1b: `connective_used` is DERIVED, not asserted. For a receive it is the
    // connective-ness of the SOURCES (the channels being listened on) and of the
    // BODY — never of the bind PATTERNS, whose free variables are the receive's own
    // binders and therefore make it no less concrete
    // (`HasLocallyFree<ReceiveBind>::connective_used(rb) = connective_used(rb.source)`).
    // Every term-position receive lowers concrete sources and a concrete body, so
    // this is `false` there and the emitted `Par` is byte-identical; it becomes
    // load-bearing only for a receive appearing inside a `matches` formula.
    let connective_used = binds_rho.iter().any(|bind| {
        bind.source
            .as_ref()
            .is_some_and(|source| source.connective_used)
    }) || lowered_body.connective_used;
    let mut receive_par = new_receive_par(
        binds_rho,
        lowered_body,
        persistent,
        false,
        bind_count,
        locally_free.clone(),
        connective_used,
        locally_free,
        connective_used,
    );

    if let Some(cond_par) = condition {
        // `new_receive_par` hardcodes `condition: None`; attach the `where`-guard post-construction
        // (the matcher coordinator evaluates it against the combined bindings of all binds).
        if let Some(receive) = receive_par.receives.get_mut(0) {
            receive.condition = Some(cond_par);
        }
    }

    Ok(receive_par)
}

fn lower_pattern_proc(
    pat: &Proc,
    counter: &mut i32,
    binders: &mut Vec<Binder<String>>,
) -> Result<Par, RholangAstLowerError> {
    match pat {
        Proc::PVar(ordvar) => match &ordvar.0 {
            Var::Free(free_var) => {
                let index = *counter;
                *counter += 1;
                binders.push(Binder(free_var.clone()));
                Ok(new_freevar_par(index, Vec::new()))
            },
            Var::Bound(_) => {
                Err(RholangAstLowerError::UnsupportedProc("bound var in receive pattern"))
            },
        },
        Proc::CastList(list) => match list.as_ref() {
            List::ListLit(items) => {
                let mut item_pars = Vec::with_capacity(items.len());
                for item in items {
                    item_pars.push(lower_pattern_proc(item, counter, binders)?);
                }
                let locally_free = locally_free_union(&item_pars);
                // A list pattern is "connective-using" iff it contains free variables; derive that
                // from the lowered children (a free-variable `Par` carries `connective_used = true`).
                let connective_used = item_pars.iter().any(|item| item.connective_used);
                Ok(new_elist_par(
                    item_pars,
                    locally_free.clone(),
                    connective_used,
                    None,
                    locally_free,
                    connective_used,
                ))
            },
            _ => Err(RholangAstLowerError::UnsupportedProc("computed list receive pattern")),
        },
        // Map pattern `@{k: v, ...}` — keys/values may contain pattern variables (e.g. `{1: x}`
        // binds `x` to the value at key `1`). Recurse so embedded `PVar`s become free variables;
        // ground keys/values stay exact-match. Mirrors `lower_map` but threads the freevar counter.
        Proc::CastMap(map) => match map.as_ref() {
            Map::MapLit(entries) => {
                let mut pairs = Vec::with_capacity(entries.len());
                let mut locally_free = Vec::new();
                let mut connective_used = false;
                for (key, value) in entries.iter() {
                    let key = lower_pattern_proc(key, counter, binders)?;
                    let value = lower_pattern_proc(value, counter, binders)?;
                    connective_used =
                        connective_used || key.connective_used || value.connective_used;
                    locally_free = union(
                        locally_free,
                        union(key.locally_free.clone(), value.locally_free.clone()),
                    );
                    pairs.push(new_key_value_pair(key, value));
                }
                Ok(new_emap_par(
                    pairs,
                    locally_free.clone(),
                    connective_used,
                    None,
                    locally_free,
                    connective_used,
                ))
            },
            _ => Err(RholangAstLowerError::UnsupportedProc("computed map receive pattern")),
        },
        // Set pattern `@Set(e, ...)` — elements may contain pattern variables. Recurse; ground
        // elements stay exact-match. (Sorted for a deterministic `ESet`, as `lower_set` does.)
        Proc::CastSet(set) => match set.as_ref() {
            Set::SetLit(items) => {
                let mut items: Vec<&Proc> = items.iter().collect();
                items.sort();
                let mut elements = Vec::with_capacity(items.len());
                for item in items {
                    elements.push(lower_pattern_proc(item, counter, binders)?);
                }
                let locally_free = locally_free_union(&elements);
                let connective_used = elements.iter().any(|e| e.connective_used);
                Ok(new_eset_par(
                    elements,
                    locally_free.clone(),
                    connective_used,
                    None,
                    locally_free,
                    connective_used,
                ))
            },
            _ => Err(RholangAstLowerError::UnsupportedProc("computed set receive pattern")),
        },
        // A ground sub-pattern (literal/constructor with no pattern variables): exact-match value.
        // This covers ground Bag/Pathmap/Drop/Nil/numeric/string patterns, whose `lower_proc`
        // encoding is itself the exact structure to match.
        other => lower_proc(other, &BoundEnv::new()),
    }
}

fn lower_lookahead_operand(
    operand: &Proc,
    env: &BoundEnv,
) -> Result<(Par, Par), RholangAstLowerError> {
    // A receive is diagnosed BEFORE expansion — see the driver's `lookahead_operand`, whose
    // error precedence this twin exists to check.
    if matches!(operand, Proc::PForUser(..)) {
        return Err(RholangAstLowerError::LookaheadOperandNotASend("a receive"));
    }
    if let Some(desugared) = desugar_surface_sugar_node(operand) {
        return lower_lookahead_operand(&desugared, env);
    }
    match operand {
        Proc::POutput(channel, payload) => {
            Ok((lower_name(channel.as_ref(), env)?, lower_proc(payload.as_ref(), env)?))
        },
        // `@P!(q)` — the channel is the quote of `P`, i.e. `lower_proc(P)`.
        Proc::POutputShort(channel_proc, payload) => {
            Ok((lower_proc(channel_proc.as_ref(), env)?, lower_proc(payload.as_ref(), env)?))
        },
        Proc::PPersistOutput(..) | Proc::PPersistOutputShort(..) => {
            Err(RholangAstLowerError::LookaheadOperandNotASend("a persistent send (`!!`)"))
        },
        Proc::PZero => Err(RholangAstLowerError::LookaheadOperandNotASend("Nil")),
        Proc::PForUser(..) => Err(RholangAstLowerError::LookaheadOperandNotASend("a receive")),
        Proc::PPar(..) | Proc::PParInfix(..) => {
            Err(RholangAstLowerError::LookaheadOperandNotASend("a parallel composition"))
        },
        Proc::CastList(..) => Err(RholangAstLowerError::LookaheadOperandNotASend("a list literal")),
        _ => Err(RholangAstLowerError::LookaheadOperandNotASend("a non-send process")),
    }
}

fn lower_drop(name: &Name, env: &BoundEnv) -> Result<Par, RholangAstLowerError> {
    match name {
        // `*@(P)` drops to `P`.
        Name::NQuote(proc) => lower_proc(proc.as_ref(), env),
        // `*@P` short-quote: the WPDA parser keeps the raw `NQuoteShort` node (its `fold` to
        // `NQuote(P)` runs only at eval time), and dropping `@P` yields `P`.
        Name::NQuoteShort(proc) => lower_proc(proc.as_ref(), env),
        // `*@Nil` drops the quote of `Nil` back to `Nil` (the empty process).
        Name::NQuoteNil => Ok(Par::default()),
        // Parenthesized name grouping `*(N)`: the WPDA parser keeps the raw `NParen` wrapper (its
        // `fold` to `N` runs only at eval time), so `*(N)` is just `*N`. This is the canonical
        // `*(x)` / `*(@(0))` rho drop idiom and the body of most COMM examples.
        Name::NParen(inner) => lower_drop(inner.as_ref(), env),
        Name::NVar(var) => lower_name_var(var, env),
        _ => Err(RholangAstLowerError::UnsupportedName("computed rholang name")),
    }
}

fn lower_name(name: &Name, env: &BoundEnv) -> Result<Par, RholangAstLowerError> {
    match name {
        // `@(P)` quotes `P`; its channel `Par` is just `P`'s lowering.
        Name::NQuote(proc) => lower_proc(proc.as_ref(), env),
        // `@P` short-quote (raw `NQuoteShort`; folds to `NQuote(P)` at eval time) — same channel.
        Name::NQuoteShort(proc) => lower_proc(proc.as_ref(), env),
        // `@Nil` quotes `Nil`; its channel is the empty process.
        Name::NQuoteNil => Ok(Par::default()),
        // Parenthesized name grouping `(N)` is transparent for channels (raw `NParen`; folds to `N`).
        Name::NParen(inner) => lower_name(inner.as_ref(), env),
        Name::NVar(var) => lower_name_var(var, env),
        _ => Err(RholangAstLowerError::UnsupportedName("computed rholang name")),
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// The 87th SCC member — `rholang_formula::lower_formula_in_env`, verbatim.
//
// It lives in a different translation unit (`rholang-runtime/src/rholang_formula.rs`) but the
// same strongly-connected component: its `FormulaShape::Term` arm re-enters `lower_proc_in_env`,
// and `Proc::Matches`' arm calls it. A twin that stopped at the module boundary would leave the
// formula half of `t matches φ` uncompared.
// ═══════════════════════════════════════════════════════════════════════════════════════════

/// Compile a spatial formula to a Rholang PATTERN, in `env` (recursive twin).
fn lower_formula_in_env(formula: &Proc, env: &BoundEnv) -> Result<Par, RholangAstLowerError> {
    use crate::rholang_formula::{connective_par, falsum_pattern, negated, verum_pattern};
    use mettail_languages::rholang::formula::{classify, FormulaShape};
    use models::rust::utils::{new_conn_and_body_par, new_conn_or_body_par};

    match classify(formula) {
        FormulaShape::Verum => Ok(verum_pattern()),
        FormulaShape::Falsum => Ok(falsum_pattern()),
        FormulaShape::Conjunction(left, right) => {
            let operands = [lower_formula_in_env(left, env)?, lower_formula_in_env(right, env)?];
            Ok(connective_par(
                new_conn_and_body_par(operands.to_vec(), Vec::new(), true),
                &operands,
            ))
        },
        FormulaShape::Disjunction(left, right) => {
            let operands = [lower_formula_in_env(left, env)?, lower_formula_in_env(right, env)?];
            Ok(connective_par(
                new_conn_or_body_par(operands.to_vec(), Vec::new(), true),
                &operands,
            ))
        },
        FormulaShape::Negation(inner) => Ok(negated(lower_formula_in_env(inner, env)?)),
        FormulaShape::Implication(antecedent, consequent) => {
            let operands = [
                negated(lower_formula_in_env(antecedent, env)?),
                lower_formula_in_env(consequent, env)?,
            ];
            Ok(connective_par(
                new_conn_or_body_par(operands.to_vec(), Vec::new(), true),
                &operands,
            ))
        },
        FormulaShape::Separation(parts) => parts
            .into_iter()
            .try_fold(Par::default(), |acc, part| Ok(acc.append(lower_formula_in_env(part, env)?))),
        FormulaShape::Term => lower_proc_in_env(formula, &env.in_pattern_position()),
    }
}

// ═══════════════════════════════════════════════════════════════════════════════════════════
// THE DIFFERENTIAL
//
// Obligation 1 of the M-2 acceptance criteria: the driver and this twin must agree on
// BYTE-IDENTICAL `Par` output, on the error cases, and on the SIDE REGISTERS the lowering
// writes (the held-fold site list and the guard-discharge report), over a corpus that covers
// every arm family.
//
// ★ ANTI-VACUITY. A differential over a corpus that misses an arm proves nothing about that
// arm, and a corpus is exactly the sort of thing that silently stops covering what its comment
// says it covers. Three mechanisms, all asserted rather than asserted-about:
//
//   1. `every_corpus_entry_lowers_or_fails_for_its_declared_reason` — each entry declares
//      whether it is expected to lower or to fail, and the test asserts the declaration. A
//      typo'd source that stops parsing, or an arm that starts failing closed, is caught as a
//      DECLARATION mismatch rather than passing as "both sides agree it errors".
//   2. `the_corpus_reaches_every_kont` — the driver counts the continuations it pushes, and the
//      test asserts that every variant of `Kont` was exercised at least once. A `Kont` nobody
//      reaches is a `Kont` the differential says nothing about, and the assertion NAMES it.
//   3. `the_corpus_reaches_a_nesting_depth_worth_measuring` — the deep entries are asserted to
//      carry the depth they claim, by counting the structure rather than by trusting the source
//      string's brackets.
// ═══════════════════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod differential {
    use super::*;
    use prost::Message;

    /// What a corpus entry is expected to do.
    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    enum Expect {
        /// Both implementations must produce a `Par`.
        Lowers,
        /// Both implementations must produce the SAME typed error. Fail-closed arms are as much
        /// a part of the contract as the ones that succeed — an arm that starts silently
        /// succeeding is a soundness regression, not an improvement.
        Fails,
    }

    /// `(source, arm family, expectation)`.
    ///
    /// Sources are Rholang SURFACE, parsed by the same WPDA parser production uses, so the
    /// corpus exercises the raw parse-tree shapes (`POutputShort`, `POutput2Plus`,
    /// `PParInternal`, …) that `desugar_surface_sugar_node` rewrites — the arms a hand-built `Proc`
    /// corpus would never reach.
    const CORPUS: &[(&str, &str, Expect)] = &[
        // ── leaves ──────────────────────────────────────────────────────────────────────────
        ("Nil", "PZero", Expect::Lowers),
        ("42", "CastInt", Expect::Lowers),
        ("-7", "CastInt / NegInt", Expect::Lowers),
        (
            "- - - - 5",
            "CastInt / nested NegInt (the lower_int_value axis)",
            Expect::Lowers,
        ),
        ("true", "CastBool", Expect::Lowers),
        ("\"hello\"", "CastStr", Expect::Lowers),
        ("1.5", "CastFloat", Expect::Lowers),
        ("x", "PVar (free)", Expect::Lowers),
        // ── sends, in every surface spelling the parser emits ───────────────────────────────
        ("@\"OUT\"!(1)", "POutput", Expect::Lowers),
        ("@\"OUT\"!!(1)", "PPersistOutput", Expect::Lowers),
        ("@\"OUT\"!()", "POutputEmpty ▸ desugar ▸ empty list", Expect::Lowers),
        ("@\"OUT\"!(1, 2, 3)", "POutput2Plus ▸ desugar ▸ list1", Expect::Lowers),
        ("@\"OUT\"!!(1, 2)", "PPersistOutput2Plus ▸ desugar", Expect::Lowers),
        ("@Nil!(1)", "POutputNil ▸ desugar ▸ quote_nil", Expect::Lowers),
        ("@Nil!()", "POutputNilEmpty ▸ desugar", Expect::Lowers),
        ("@Nil!(1, 2)", "POutputNil2Plus ▸ desugar", Expect::Lowers),
        ("@(\"c\")!(1)", "POutputShort", Expect::Lowers),
        ("@(\"c\")!!(1)", "PPersistOutputShort", Expect::Lowers),
        ("@\"OUT\"!(@\"IN\"!(\"p\"))", "nested sends", Expect::Lowers),
        // ── parallel composition ────────────────────────────────────────────────────────────
        ("{ Nil | Nil }", "PPar (bag)", Expect::Lowers),
        ("@\"a\"!(1) | @\"b\"!(2)", "PParInfix", Expect::Lowers),
        ("{ @\"a\"!(1) | @\"b\"!(2) | @\"c\"!(3) }", "PPar, width 3", Expect::Lowers),
        // ── collections ─────────────────────────────────────────────────────────────────────
        ("@\"OUT\"!([1, 2, 3])", "CastList", Expect::Lowers),
        ("@\"OUT\"!([])", "CastList, empty", Expect::Lowers),
        (
            "@\"OUT\"!([[[[1]]]])",
            "CastList, nested (the reproducer's shape)",
            Expect::Lowers,
        ),
        ("@\"OUT\"!({1 : 2, 3 : 4})", "CastMap", Expect::Lowers),
        ("@\"OUT\"!(Set(1, 2, 3))", "CastSet", Expect::Lowers),
        ("@\"OUT\"!(#{1 | 2 | 2}#)", "CastBag (the tagged ABI encoding)", Expect::Lowers),
        ("@\"OUT\"!({| 1 : 10, 2 : 20 |})", "CastPathmap", Expect::Lowers),
        // ── arithmetic and comparison ───────────────────────────────────────────────────────
        ("@\"OUT\"!(1 + 2)", "Add (numeric parity)", Expect::Lowers),
        ("@\"OUT\"!(\"a\" + \"b\")", "Add (string parity ▸ EPlusPlus)", Expect::Lowers),
        ("@\"OUT\"!(5 - 3)", "Sub", Expect::Lowers),
        ("@\"OUT\"!(5 * 3)", "Mul", Expect::Lowers),
        ("@\"OUT\"!(6 / 3)", "Div", Expect::Lowers),
        ("@\"OUT\"!(7 % 3)", "Mod", Expect::Lowers),
        ("@\"OUT\"!(1 == 2)", "Eq", Expect::Lowers),
        ("@\"OUT\"!(1 != 2)", "Ne", Expect::Lowers),
        ("@\"OUT\"!(1 < 2)", "Lt", Expect::Lowers),
        ("@\"OUT\"!(1 > 2)", "Gt", Expect::Lowers),
        ("@\"OUT\"!(1 <= 2)", "LtEq", Expect::Lowers),
        ("@\"OUT\"!(1 >= 2)", "GtEq", Expect::Lowers),
        ("@\"OUT\"!(true and false)", "And", Expect::Lowers),
        ("@\"OUT\"!(true or false)", "Or", Expect::Lowers),
        ("@\"OUT\"!(true implies false)", "Implies", Expect::Lowers),
        ("@\"OUT\"!(not true)", "Not", Expect::Lowers),
        (
            "@\"OUT\"!(((1 + 2) + 3) + 4)",
            "Add chain (the lower_add gate subject)",
            Expect::Lowers,
        ),
        // ── methods ─────────────────────────────────────────────────────────────────────────
        ("@\"OUT\"!({1 : 2}.get(1))", "MGet", Expect::Lowers),
        ("@\"OUT\"!({1 : 2}.set(3, 4))", "MSet", Expect::Lowers),
        ("@\"OUT\"!({1 : 2}.contains(1))", "MContains", Expect::Lowers),
        ("@\"OUT\"!({1 : 2}.delete(1))", "MDelete", Expect::Lowers),
        ("@\"OUT\"!({1 : 2}.size())", "MSize", Expect::Lowers),
        ("@\"OUT\"!({1 : 2}.keys())", "MKeys", Expect::Lowers),
        ("@\"OUT\"!({1 : 2}.union({3 : 4}))", "MUnion", Expect::Lowers),
        ("@\"OUT\"!(Set(1).diff(Set(2)))", "BDiff", Expect::Lowers),
        ("@\"OUT\"!(Set(1).add(2))", "SAdd", Expect::Lowers),
        ("@\"OUT\"!([1, 2].length())", "LLength", Expect::Lowers),
        ("@\"OUT\"!([1, 2].nth(0))", "LNth", Expect::Lowers),
        ("@\"OUT\"!([1].concat([2]))", "LConcat", Expect::Lowers),
        ("@\"OUT\"!(1.toByteArray())", "MToByteArray", Expect::Lowers),
        // ── the C3 bag gates: three routed operations that must FAIL on a bag receiver ──────
        ("@\"OUT\"!(#{1 | 2}#.length())", "LLength bag gate", Expect::Fails),
        ("@\"OUT\"!(#{1 | 2}#.nth(0))", "LNth bag gate", Expect::Fails),
        ("@\"OUT\"!(#{1}#.concat(#{2}#))", "LConcat bag gate", Expect::Fails),
        // ── binders ─────────────────────────────────────────────────────────────────────────
        ("new c in { @\"OUT\"!(1) }", "PNew", Expect::Lowers),
        ("new c in { c!(1) }", "PNew, binder referenced", Expect::Lowers),
        ("new a, b in { a!(1) | b!(2) }", "PNew, 2 binders", Expect::Lowers),
        ("new a in { new b in { a!(1) | b!(2) } }", "PNew, nested", Expect::Lowers),
        // ── receives ────────────────────────────────────────────────────────────────────────
        ("for(x <- @\"c\") { @\"OUT\"!(*x) }", "PForUser, single bind", Expect::Lowers),
        ("for(x <= @\"c\") { @\"OUT\"!(*x) }", "PForUser, persistent", Expect::Lowers),
        ("for(<- @\"c\") { @\"OUT\"!(1) }", "PForUser, empty bind", Expect::Lowers),
        (
            "for(x <- @\"a\" & y <- @\"b\") { @\"OUT\"!(*x) }",
            "PForUser, `&`-join",
            Expect::Lowers,
        ),
        (
            "for(x <- @\"a\"; y <- @\"b\") { @\"OUT\"!(*x) }",
            "PForUser, two rows (the continuation nest)",
            Expect::Lowers,
        ),
        (
            "for(x <- @\"c\") { for(y <- @\"d\") { @\"OUT\"!(*x) } }",
            "PForUser, body is itself a receive",
            Expect::Lowers,
        ),
        // `!?` QUERY BINDS — expanded by `desugar_surface_sugar_node` into
        // `new r in { svc!(*r, args…) | for(pat <- r){body} }`. The driver and this oracle
        // expand at DIFFERENT places (the driver's `enter_proc` head loop; the oracle's
        // `lower_proc` head), and both must additionally decline the nested-body shortcut for a
        // query-carrying inner `for` — three chances to disagree, which is what these rows
        // check. All three surfaces appear, in both the row-head and `&`-join-tail positions.
        (
            "for(x <- @\"c\"!?(1)) { @\"OUT\"!(*x) }",
            "InputBindQuery ▸ query-bind expansion",
            Expect::Lowers,
        ),
        (
            "for(@x <- @\"c\"!?(1)) { @\"OUT\"!(x) }",
            "InputBindQuotedQuery ▸ query-bind expansion",
            Expect::Lowers,
        ),
        (
            "for(<- @\"c\"!?(1)) { @\"OUT\"!(1) }",
            "InputBindEmptyQuery ▸ query-bind expansion",
            Expect::Lowers,
        ),
        (
            "for(x <- @\"c\"!?()) { @\"OUT\"!(*x) }",
            "InputBindQuery ▸ zero-argument (MONADIC request arity)",
            Expect::Lowers,
        ),
        (
            "for(x <- @\"c\"!?(1, 2, 3)) { @\"OUT\"!(*x) }",
            "InputBindQuery ▸ multi-argument request",
            Expect::Lowers,
        ),
        (
            "for(x <- @\"a\" & y <- @\"b\"!?(1)) { @\"OUT\"!(*x) }",
            "query bind in the `&`-join TAIL (an ordinary head must not mask it)",
            Expect::Lowers,
        ),
        (
            "for(x <- @\"a\"!?(1) & y <- @\"b\"!?(2)) { @\"OUT\"!(*x) }",
            "two query binds in one row ▸ two private return channels under one `new`",
            Expect::Lowers,
        ),
        (
            "for(x <- @\"a\"!?(1); y <- @\"b\") { @\"OUT\"!(*x) }",
            "query bind in the first of two rows (the continuation nest)",
            Expect::Lowers,
        ),
        (
            "for(x <- @\"c\") { for(y <- @\"d\"!?(1)) { @\"OUT\"!(*y) } }",
            "query bind in a receive BODY ▸ the nested-`for` shortcut must decline it",
            Expect::Lowers,
        ),
        (
            "new k in { for(x <- @\"c\"!?(1)) { k!(*x) } }",
            "query bind under an outer `new` (binder-level threading)",
            Expect::Lowers,
        ),
        (
            "for(x <- @\"c\"!?(1) where 1 < 2) { @\"OUT\"!(*x) }",
            "query bind with a `where` guard",
            Expect::Lowers,
        ),
        (
            "for(@[a, b] <- @\"c\") { @\"OUT\"!(a) }",
            "lower_pattern_proc, list pattern",
            Expect::Lowers,
        ),
        (
            "for(@{1 : v} <- @\"c\") { @\"OUT\"!(v) }",
            "lower_pattern_proc, map pattern",
            Expect::Lowers,
        ),
        (
            "for(@Set(a) <- @\"c\") { @\"OUT\"!(a) }",
            "lower_pattern_proc, set pattern",
            Expect::Lowers,
        ),
        (
            "for(@[[a]] <- @\"c\") { @\"OUT\"!(a) }",
            "lower_pattern_proc, NESTED list pattern",
            Expect::Lowers,
        ),
        (
            "for(@5 <- @\"c\") { @\"OUT\"!(1) }",
            "lower_pattern_proc, ground fallthrough to lower_proc",
            Expect::Lowers,
        ),
        (
            "for(x, y <- @\"c\") { @\"OUT\"!(*x) }",
            "InputBindPolyadic ▸ mk_proc_list pattern",
            Expect::Lowers,
        ),
        (
            "for(x <- @\"c\" where 1 < 2) { @\"OUT\"!(*x) }",
            "PForUser with a `where` guard",
            Expect::Lowers,
        ),
        // ── folds (the held-fold trampoline, and the site register) ─────────────────────────
        ("new c in { @\"OUT\"!(int(5, 8)) }", "IntBinProc ▸ held fold", Expect::Lowers),
        (
            "new c in { @\"OUT\"!(bigint(5)) }",
            "BigintCastProc ▸ held fold",
            Expect::Lowers,
        ),
        (
            "new c in { @\"OUT\"!(int(5, 8)) | @\"OUT\"!(int(6, 8)) }",
            "TWO fold sites ▸ site-index order",
            Expect::Lowers,
        ),
        // ── `matches`, and therefore the formula compiler ───────────────────────────────────
        ("@\"OUT\"!(1 matches 1)", "Matches ▸ FormulaShape::Term", Expect::Lowers),
        ("@\"OUT\"!(1 matches true)", "Matches ▸ Verum", Expect::Lowers),
        ("@\"OUT\"!(1 matches false)", "Matches ▸ statically-false fold", Expect::Lowers),
        ("@\"OUT\"!(1 matches (1 and 1))", "Matches ▸ Conjunction", Expect::Lowers),
        ("@\"OUT\"!(1 matches (1 or 2))", "Matches ▸ Disjunction", Expect::Lowers),
        ("@\"OUT\"!(1 matches (not 2))", "Matches ▸ Negation", Expect::Lowers),
        ("@\"OUT\"!(1 matches (1 implies 2))", "Matches ▸ Implication", Expect::Lowers),
        (
            "@\"OUT\"!(@\"a\"!(1) matches { @\"a\"!(1) | @\"b\"!(2) })",
            "Matches ▸ Separation",
            Expect::Lowers,
        ),
        (
            "@\"OUT\"!(1 matches (1 and (2 and (3 and 4))))",
            "Matches ▸ NESTED connectives (the formula depth axis)",
            Expect::Lowers,
        ),
        // ── lookahead ───────────────────────────────────────────────────────────────────────
        ("@\"OUT\"!(1)[*]", "PLookaheadAll", Expect::Lowers),
        ("@\"OUT\"!(1)[3]", "PLookahead, bounded", Expect::Lowers),
        ("Nil[*]", "PLookaheadAll ▸ operand is not a send", Expect::Fails),
        ("@\"OUT\"!!(1)[*]", "PLookaheadAll ▸ persistent operand", Expect::Fails),
        // ── fail-closed arms ────────────────────────────────────────────────────────────────
        ("@\"OUT\"!(int(5, 8))", "IntBinProc outside a liftable position", Expect::Fails),
        ("@\"OUT\"!(bool(1))", "ToBool — no machine algebra", Expect::Fails),
    ];

    /// Terms deep enough that a per-level constant would show, driven through BOTH
    /// implementations. The oracle recurses, so these run on a large explicit thread stack —
    /// which is itself the point being made: the driver needs no such accommodation.
    const DEEP_DEPTH: usize = 400;

    fn parse(source: &str) -> Option<Proc> {
        Proc::parse_via_wpda(source).ok()
    }

    /// The readings of a parsed source.
    ///
    /// `parse_via_wpda` already resolves the WPDA's alternatives to one `Proc`, so this is a
    /// one-element list today. It is a list rather than a scalar so that a corpus driven from
    /// `RholangTerm` (which does carry `Ambiguous`) can be dropped in without restructuring the
    /// comparison, and so the failure messages already name a reading index.
    fn readings(term: &Proc) -> Vec<&Proc> {
        vec![term]
    }

    /// Run one implementation with the side registers cleared, and return everything it
    /// produced: the `Par` (as encoded BYTES), the typed error, and both registers.
    fn run<F>(lower: F, proc: &Proc) -> (Result<Vec<u8>, String>, String, String)
    where
        F: FnOnce(&Proc, &BoundEnv) -> Result<Par, RholangAstLowerError>,
    {
        clear_held_fold_sites();
        clear_guard_discharge_report();
        let outcome = match lower(proc, &BoundEnv::new()) {
            Ok(par) => Ok(par.encode_to_vec()),
            Err(error) => Err(format!("{error:?}")),
        };
        let sites = format!("{:?}", take_held_fold_sites());
        let report = format!("{:?}", take_guard_discharge_report());
        (outcome, sites, report)
    }

    /// ★ The obligation: byte-identical `Par`, identical typed errors, identical side
    /// registers, over every reading of every corpus entry.
    #[test]
    fn driver_matches_the_recursive_oracle() {
        let mut compared = 0usize;
        for (source, family, _) in CORPUS {
            let Some(term) = parse(source) else {
                panic!("differential corpus: `{source}` ({family}) no longer parses");
            };
            for (index, proc) in readings(&term).into_iter().enumerate() {
                let driven = run(super::super::lower_proc_in_env, proc);
                let recursed = run(lower_proc_in_env, proc);
                assert_eq!(
                    driven.0, recursed.0,
                    "M-2 DIFFERENTIAL FAILED on `{source}` ({family}), reading {index}: the \
                     explicit-stack driver and the recursive oracle disagree on the emitted \
                     `Par` (or on the typed error).\n  driver: {:?}\n  oracle: {:?}",
                    driven.0, recursed.0
                );
                assert_eq!(
                    driven.1, recursed.1,
                    "M-2 DIFFERENTIAL FAILED on `{source}` ({family}), reading {index}: the two \
                     wrote DIFFERENT held-fold site registers. Site order and site index are \
                     part of the emitted artifact — the contract channel is keyed by them."
                );
                assert_eq!(
                    driven.2, recursed.2,
                    "M-2 DIFFERENTIAL FAILED on `{source}` ({family}), reading {index}: the two \
                     wrote DIFFERENT guard-discharge reports."
                );
                compared += 1;
            }
        }
        assert!(
            compared >= CORPUS.len(),
            "differential: compared {compared} readings for {} corpus entries — an entry that \
             yields no reading compares nothing",
            CORPUS.len()
        );
        println!("  M-2 differential: {compared} readings over {} entries", CORPUS.len());
    }

    /// ★ The formula half, compared SEPARATELY — and the reason it has to be.
    ///
    /// `lower_arm_matches` (above, verbatim) calls `crate::rholang_formula::lower_formula_in_env`
    /// by ABSOLUTE PATH, and that function now delegates to the driver. So on a `matches` corpus
    /// entry the oracle's TERM half is genuinely recursive while its FORMULA half is already the
    /// driver — `driver_matches_the_recursive_oracle` compares the driver against itself there,
    /// and would pass no matter what the formula conversion did.
    ///
    /// That is a vacuity hole, not a theoretical one: it is the exact shape of "a test that
    /// cannot fail". It is closed here by comparing the two formula implementations head to
    /// head, rather than by editing the verbatim twin to reach around it.
    #[test]
    fn the_formula_compiler_matches_its_recursive_oracle() {
        const FORMULAS: &[(&str, &str)] = &[
            ("true", "Verum"),
            ("false", "Falsum"),
            ("1", "Term"),
            ("x", "Term with a free variable ▸ Wildcard in pattern position"),
            ("1 and 2", "Conjunction"),
            ("1 or 2", "Disjunction"),
            ("not 1", "Negation"),
            ("1 implies 2", "Implication"),
            ("@\"a\"!(1) | @\"b\"!(2)", "Separation"),
            ("1 and (2 and (3 and (4 and 5)))", "Conjunction, nested"),
            ("not (not (not 1))", "Negation, nested"),
            ("(1 and 2) or (not 3)", "mixed connectives"),
            ("[1, [2, [3]]]", "Term ▸ a nested collection read as a pattern"),
        ];
        for (source, shape) in FORMULAS {
            let formula = parse(source)
                .unwrap_or_else(|| panic!("formula corpus: `{source}` ({shape}) does not parse"));
            let env = BoundEnv::new();
            let driven = crate::rholang_formula::lower_formula_in_env(&formula, &env)
                .map(|par| par.encode_to_vec())
                .map_err(|error| format!("{error:?}"));
            let recursed = lower_formula_in_env(&formula, &env)
                .map(|par| par.encode_to_vec())
                .map_err(|error| format!("{error:?}"));
            assert_eq!(
                driven, recursed,
                "M-2 FORMULA DIFFERENTIAL FAILED on `{source}` ({shape}): the driver's \
                 `Job::Formula`/`Kont::Formula*` path and the recursive formula compiler \
                 disagree"
            );
        }
        println!("  M-2 differential: {} formula shapes", FORMULAS.len());
    }

    /// ★ ANTI-VACUITY 1. Each entry declares whether it lowers or fails; assert the
    /// declaration. Without this, an entry that quietly stopped exercising its arm — because
    /// the surface changed, or because the arm started failing closed — would still "pass"
    /// (both implementations agreeing on an error is agreement about nothing).
    #[test]
    fn every_corpus_entry_lowers_or_fails_for_its_declared_reason() {
        for (source, family, expect) in CORPUS {
            let term = parse(source).unwrap_or_else(|| {
                panic!("differential corpus: `{source}` ({family}) does not parse")
            });
            let proc = readings(&term)[0];
            clear_held_fold_sites();
            let outcome = super::super::lower_proc_in_env(proc, &BoundEnv::new());
            match expect {
                Expect::Lowers => assert!(
                    outcome.is_ok(),
                    "corpus entry `{source}` ({family}) is declared to LOWER but failed: {:?}",
                    outcome.err()
                ),
                Expect::Fails => assert!(
                    outcome.is_err(),
                    "corpus entry `{source}` ({family}) is declared to FAIL CLOSED but lowered. \
                     A fail-closed arm that starts succeeding is a soundness regression."
                ),
            }
        }
    }

    /// ★ ANTI-VACUITY 2. The corpus must reach every continuation the machine can push.
    ///
    /// `Kont` variants are counted by NAME through the driver's own instrumentation hook, so
    /// this cannot drift from the enum: a new variant nobody's corpus reaches fails here, and
    /// the failure NAMES it.
    #[test]
    fn the_corpus_reaches_every_kont() {
        let mut seen = std::collections::BTreeSet::new();
        for (source, family, _) in CORPUS {
            let Some(term) = parse(source) else {
                panic!("differential corpus: `{source}` ({family}) no longer parses");
            };
            for proc in readings(&term) {
                clear_held_fold_sites();
                super::super::kont_trace(proc, &BoundEnv::new(), &mut seen);
            }
        }
        let missing: Vec<&&str> = super::super::KONT_NAMES
            .iter()
            .filter(|name| !seen.contains(**name))
            .collect();
        assert!(
            missing.is_empty(),
            "ANTI-VACUITY: the differential corpus never reaches these continuations, so the \
             differential says NOTHING about them: {missing:?}.\nAdd a corpus entry per name, \
             or delete the continuation."
        );
        println!(
            "  M-2 differential: {} of {} continuations reached",
            seen.len(),
            super::super::KONT_NAMES.len()
        );
    }

    /// ★ ANTI-VACUITY 3. The deep entries must carry the depth they claim.
    ///
    /// Measured by walking the built term, not by trusting the source string. Both
    /// implementations then lower it — the oracle on an explicitly large stack, because it is
    /// the thing being retired.
    #[test]
    fn the_driver_and_the_oracle_agree_on_a_deep_term() {
        let mut proc = Proc::CastInt(Arc::new(Int::NumLit(1)));
        for _ in 0..DEEP_DEPTH {
            proc = Proc::CastList(Arc::new(List::ListLit(vec![proc])));
        }

        // The subject carries the depth it claims — counted, not assumed.
        let mut measured = 0usize;
        let mut cursor = &proc;
        while let Proc::CastList(list) = cursor {
            let List::ListLit(items) = list.as_ref() else {
                break;
            };
            let Some(item) = items.first() else { break };
            measured += 1;
            cursor = item;
        }
        assert_eq!(
            measured, DEEP_DEPTH,
            "ANTI-VACUITY: the deep subject was built at nesting depth {measured}, not \
             {DEEP_DEPTH} — a differential over a shallow term proves nothing about depth"
        );

        let driven = super::super::lower_proc_in_env(&proc, &BoundEnv::new())
            .expect("driver: the deep term lowers")
            .encode_to_vec();

        // The ORACLE recurses, so it needs a stack sized for `DEEP_DEPTH` levels of 87-member
        // frames. Giving it one here is not a workaround — it is the measurement this whole
        // conversion exists to make unnecessary.
        let recursed = std::thread::Builder::new()
            .stack_size(512 * 1024 * 1024)
            .spawn(move || {
                lower_proc_in_env(&proc, &BoundEnv::new())
                    .expect("oracle: the deep term lowers")
                    .encode_to_vec()
            })
            .expect("differential: failed to spawn the oracle thread")
            .join()
            .expect("differential: the recursive oracle overflowed its stack");

        assert_eq!(
            driven, recursed,
            "M-2 DIFFERENTIAL FAILED at nesting depth {DEEP_DEPTH}: the driver and the oracle \
             disagree on a deep term, which is exactly the regime the conversion is for"
        );
    }
}
