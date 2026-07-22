//! E-6a (pgmcp experiment 145) — PathMap-backed SUBJECT INDEXING for in-Rho
//! matching: BENCHMARK-ONLY support, quarantined behind `bench-naive-baseline`
//! exactly like [`crate::bench_support`]. NO production surface: nothing here
//! is reachable from a default build, and no production emitter is touched.
//!
//! # What this module is
//!
//! The TREATMENT arm of experiment E-6a. The CONTROL arm is the current
//! spread+drive path (`spread_term_par` + per-site
//! `multi_pattern_receiver_network_par` networks over `loc:`/`col:`/`cap:`
//! channels, sites located by the HOST-side `collect_redex_sites` walk). The
//! treatment replaces BOTH the per-node spread and the host site walk:
//!
//! 1. [`pathmap_spread_term_par`] publishes ONE persistent [`EPathMap`] VALUE
//!    — the subject index — on [`e6a_index_channel`]. Entries mirror
//!    `spread_child_location`'s site derivation, with each site's `/`-joined
//!    location SEGMENTED into its components (`["site0", "Pair.0", "Swap.1"]`)
//!    so the trie shares prefixes the way the paths-subspaces reading
//!    prescribes. Two families per subject node at location ℓ with head
//!    constructor `f` and subtree `t`:
//!
//!    * «s» (site/tag): `[tag(f), c₀, …, c_d]` — op-FIRST, so ONE
//!      `readZipperAt([tag(op)]).getSubtrie()` query selects every candidate
//!      site of a rule-root op;
//!    * «v» (value): `["v", c₀, …, c_d, @val, (⟦t⟧,)]` — the σ carrier: the
//!      reflected subtree [`reflect_ground_term_par`], wrapped in a 1-TUPLE,
//!      rides as the last list element after the [`VALUE_LEAF_SENTINEL`]
//!      (`@val`) segment, recovered in-process by
//!      `readZipperAt(["v", c₀…c_d, @val]).descendFirst().getLeaf()` (the
//!      stored trie VALUE is the ORIGINAL entry `Par`, lossless). The `@val`
//!      sentinel guarantees that below the `["v", c₀…c_d, @val]` prefix there
//!      is EXACTLY the value tuple — even when the σ position binds a NON-LEAF
//!      subtree whose DEEPER «v» entries would otherwise share the `["v",
//!      c₀…c_d]` prefix (they carry a `{op}.{i}` descent component at the
//!      sentinel's position, never `@val`). See [`VALUE_LEAF_SENTINEL`] for the
//!      full root cause (the `lambda_chain` binder-body σ fire-0).
//!
//! 2. [`discovery_call_par`] installs, per rule-root op, the MACHINE-side
//!    site enumeration (`getSubtrie` on the op prefix, result published on
//!    [`e6a_sites_channel`]). `collect_redex_sites` is NEVER called on the
//!    treatment path.
//!
//! 3. The harness reads each op's subtrie back ([`decode_sites_par`]),
//!    verifies pairwise NON-ANCESTRY ([`sites_non_ancestral`], fail-closed),
//!    and instantiates one [`entry_query_match_par`] per (entry, candidate
//!    site): guards re-verify the head tag at the site and every nested
//!    descent position (`pathExists`), σ binds from the «v» family
//!    (`descendFirst().getLeaf()` + an `EList`/`ETuple` match), and the
//!    accept fires in the exact `build_accept_send` ABI (σ slots in
//!    pattern-DFS first-occurrence order, then `@out`). This is the
//!    pre-registered REDUCED form: discovery and matching are machine-side;
//!    what honestly remains host-side is the readback + per-site `Par`
//!    codegen + the second injection.
//!
//! # Why this dissolves `NestedEntryMultiSite`
//!
//! The control gate fails closed on nested-entry multi-site subjects because
//! co-installed networks would RACE for the one linear `loc:` head-tag send at
//! a descent position. The treatment has NO linear tags: every guard and σ
//! read is a NON-DESTRUCTIVE query method against the persistent index value,
//! so co-installed per-site query processes cannot contend, at any nesting
//! depth.
//!
//! # Machine caps (discovered in Phase 0/1, enforced host-side)
//!
//! The reducer's trie-key encoder (`models/src/rust/path_map_encoder.rs`)
//! PANICS outside its envelope, and `e_pathmap_to_rholang_pathmap` re-encodes
//! EVERY entry on EVERY query-method call, so an index containing even one
//! over-cap entry would abort the injection. The caps:
//!
//! * S-expression SYMBOL length 1..=63 bytes (`encode_into`, panic) — and
//!   `Tag::Symbol(63)` encodes as byte `0xC0 + 63 = 0xFF`, COLLIDING with the
//!   0xFF segment separator the reducer splits child segments on, so the SAFE
//!   symbol budget is 1..=62 bytes;
//! * list ARITY ≤ 63 (`encode_into`, panic) — this caps the entry's segment
//!   count (site depth) and the σ tuple's token count.
//!
//! [`pathmap_spread_term_par`] therefore validates every «s» entry against the
//! caps (an over-cap «s» entry fails the whole cell closed — recorded as a
//! DNF-by-machine-cap) and OMITS any «v» entry that does not fit (recording
//! the omitted locations; a query needing σ at an omitted location fails
//! closed at harness build time via [`e6a_omitted_value_locations`]). The
//! E-6a corpus σ positions all bind leaf/small subtrees, which fit; what the
//! caps genuinely exclude is recorded honestly by the driver.
//!
//! # Determinism
//!
//! The zipper navigation methods sort+dedup child segments
//! byte-lexicographically (`reduce.rs` `descendFirst`/`descendIndexedBranch`/
//! `childCount`), `getSubtrie` collects in the PathMap trie's canonical DFS
//! byte order, and the injection seeds are FIXED byte strings — the spike
//! asserts bit-identical readback and counter snapshots across repeated runs.

use std::collections::{BTreeMap, BTreeSet};
use std::time::{Duration, Instant};

use crypto::rust::hash::blake2b512_random::Blake2b512Random;
use models::create_bit_vector;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::{EAnd, EList, EMethod, EPathMap, ETuple, Expr, MatchCase, Par, ReceiveBind};
use models::rust::canonical_path::encode_trie_path;
use models::rust::par_to_sexpr::ParToSExpr;
use models::rust::utils::{
    new_boundvar_par, new_elist_par, new_freevar_par, new_gbool_par, new_gstring_par,
    new_match_par, new_receive_par, new_send_par, new_wildcard_par,
};

use dovetail::set_automaton::{AutomatonNode, SetAutomatonView, StateId};
use mettail_rholang_codegen::{
    reflect_ground_term_par, spread_child_location, GroundTerm, InRhoMatchingRuleset,
};
use prost::Message;
use rho_pure_eval::Env;
use rholang::rust::interpreter::accounting::costs::Cost;
use rholang::rust::interpreter::accounting::has_cost::HasCost;
use rholang::rust::interpreter::rho_runtime::RhoRuntime;

use crate::bench_support::{
    bench_runtime_with_counters, count_receive_nodes, BenchRunResult, BenchWorkloadParams,
};

/// The «v» (σ-carrier) family discriminant — the first path segment of every
/// value entry. Distinct from every tag segment (tags start `t.`).
const VALUE_FAMILY: &str = "v";

/// The «v» value-leaf SENTINEL segment, interposed between a value entry's
/// LOCATION components and its σ-value tuple: `["v", c₀…c_d, @val, (⟦t⟧,)]`.
///
/// # Why (root cause of the `lambda_chain` fire-0)
///
/// σ-retrieval is `readZipperAt(["v", c₀…c_d, @val]).descendFirst().getLeaf()`.
/// Without the sentinel the query prefix was `["v", c₀…c_d]`, and the design
/// (see the retired module-rustdoc claim) ASSUMED exactly one entry sits below
/// it. That holds only when the σ position binds a LEAF subterm. When it binds
/// a NON-LEAF (e.g. `lambda_chain`'s β rule `App(Lam(fun), arg) ~> eval fun
/// arg` binds `fun` = the lambda BODY `^bound(Z)`, and `arg` = the chain tail),
/// the subject node has CHILDREN, so DEEPER «v» entries share the `["v",
/// c₀…c_d]` prefix (`["v", c₀…c_d, {op}.{i}, …]`). Their next segment is a
/// descent-component `GString` (canonical-codec tag `0x04`), which sorts BEFORE
/// the value tuple's `ETuple` segment (tag `0x0C`), so `descendFirst`
/// (byte-lex-smallest child) selected a DEEPER descent branch and `getLeaf`
/// returned Nil — the σ match then never fired. (Under the reducer's former
/// S-expression trie codec a list/arity tag byte sorted BEFORE a symbol tag
/// byte, so the tuple WAS picked first and the bug was latent; the f1r3node
/// "Job-A" canonical-path re-key flipped that ordering. The bug is INDEPENDENT
/// of the E-2-D `^gnd`/`^nog` marker — the marker enlarges the tuple's CONTENT
/// but never changes the descent CHOICE, since the tuple's leading `0x0C` and
/// the descent `GString`'s leading `0x04` are both marker-invariant.)
///
/// The sentinel makes each location's σ value uniquely addressable: below
/// `["v", c₀…c_d, @val]` there is EXACTLY the value tuple (a deeper «v» entry
/// carries a `{op}.{i}` component at that position, never `@val`), so
/// `descendFirst` unambiguously descends the tuple regardless of σ arity. It is
/// collision-free with every location component (`root_site` = `site0`; every
/// descent component is `{op}.{index}`, which always contains a `.` — `@val`
/// contains none) and with the family discriminant (`v`).
const VALUE_LEAF_SENTINEL: &str = "@val";

/// The SAFE S-expression symbol budget: the encoder panics outside 1..=63 and
/// `Symbol(63)`'s tag byte is `0xFF` (the segment separator), so 62 is the
/// largest collision-free symbol length.
const MAX_SYMBOL_BYTES: usize = 62;

/// The encoder's list-arity cap (inclusive; `encode_into` panics above it).
const MAX_LIST_ARITY: usize = 63;

/// How many leading fingerprint characters the E-6a tag strings carry. The tag
/// is an E-6a-LOCAL trie key (both the index build and every query derive it
/// through [`e6a_tag_string`]) — it deliberately does NOT reuse the full
/// `mettail.term.{fp}.{ctor}` reflect-tag string, whose unbounded fingerprint
/// could blow the symbol cap. One language per counting runtime (the bench
/// discipline), so the 8-char prefix cannot collide across languages.
const TAG_FINGERPRINT_PREFIX: usize = 8;

/// The deterministic E-6a tag STRING of a constructor: `t.{fp≤8}.{ctor}`.
pub fn e6a_tag_string(language_fingerprint: &str, constructor: &str) -> String {
    let prefix_len = language_fingerprint.len().min(TAG_FINGERPRINT_PREFIX);
    format!("t.{}.{constructor}", &language_fingerprint[..prefix_len])
}

/// The persistent index channel of the subject spread at root site `root_site`.
pub fn e6a_index_channel(root_site: &str) -> String {
    format!("e6a:idx:{root_site}")
}

/// The machine-side site-enumeration RESULT channel for rule-root op `op`.
pub fn e6a_sites_channel(root_site: &str, op: &str) -> String {
    format!("e6a:sites:{root_site}/{op}")
}

fn quoted(name: &str) -> Par {
    new_gstring_par(name.to_string(), Vec::new(), false)
}

/// A ground `EList` of the given elements (no free vars, no remainder).
fn ground_list(elements: Vec<Par>) -> Par {
    new_elist_par(elements, Vec::new(), false, None, Vec::new(), false)
}

/// A ground 1-`ETuple` wrapping `inner` — the σ-carrier wrapper: the tuple's
/// S-expression `(tuple …)` is `(`-headed, so the reducer's `parse_sexpr`
/// parses it as a LIST of small symbols instead of one giant symbol, keeping
/// every symbol under the 62-byte cap for any subtree whose token shape fits
/// the arity cap (validated host-side by [`entry_fits_machine_caps`]).
fn ground_tuple(inner: Par) -> Par {
    Par {
        exprs: vec![Expr {
            expr_instance: Some(ExprInstance::ETupleBody(ETuple {
                ps: vec![inner],
                locally_free: Vec::new(),
                connective_used: false,
            })),
        }],
        ..Par::default()
    }
}

/// A `Par` carrying one method call `target.method_name(args…)`, free in the
/// De Bruijn indices `free`.
fn method_par(target: Par, method_name: &str, arguments: Vec<Par>, free: &[usize]) -> Par {
    let bits = create_bit_vector(&free.to_vec());
    Par {
        exprs: vec![Expr {
            expr_instance: Some(ExprInstance::EMethodBody(EMethod {
                method_name: method_name.to_string(),
                target: Some(target),
                arguments,
                locally_free: bits.clone(),
                connective_used: false,
            })),
        }],
        locally_free: bits,
        connective_used: false,
        ..Par::default()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Host-side mirror of the reducer's trie-key caps
// ─────────────────────────────────────────────────────────────────────────────

/// Split an S-expression body on depth-0 spaces — the exact tokenization of
/// the reducer's `split_sexpr` (parens and double-quotes drive depth/string
/// state; brackets are ordinary symbol characters).
fn split_sexpr_tokens(s: &str) -> Vec<String> {
    let mut parts = Vec::new();
    let mut current = String::new();
    let mut depth = 0i32;
    let mut in_string = false;
    let mut escape = false;
    for ch in s.chars() {
        if escape {
            current.push(ch);
            escape = false;
            continue;
        }
        match ch {
            '\\' if in_string => escape = true,
            '"' => {
                in_string = !in_string;
                current.push(ch);
            },
            '(' if !in_string => {
                depth += 1;
                current.push(ch);
            },
            ')' if !in_string => {
                depth -= 1;
                current.push(ch);
            },
            ' ' | '\t' | '\n' if !in_string && depth == 0 => {
                if !current.is_empty() {
                    parts.push(std::mem::take(&mut current));
                }
            },
            _ => current.push(ch),
        }
    }
    if !current.is_empty() {
        parts.push(current);
    }
    parts
}

/// NOTE: the reducer's `split_sexpr` does NOT push the quote characters into
/// the token (`'"' => in_string = !in_string` without a push), so a quoted
/// symbol loses its quotes during tokenization inside lists — but a TOP-LEVEL
/// quoted string (`parse_sexpr` on `"…"`) keeps them (it never tokenizes).
/// [`split_sexpr_tokens`] above deliberately KEEPS quotes so the host-side
/// length check is CONSERVATIVE (an over-estimate can only fail closed).
///
/// Whether one S-expression STRING fits the reducer's encode caps: parsed the
/// way `parse_sexpr` parses it, every symbol must be 1..=[`MAX_SYMBOL_BYTES`]
/// bytes and every list arity ≤ [`MAX_LIST_ARITY`].
fn sexpr_string_fits(s: &str) -> bool {
    let s = s.trim();
    if !s.starts_with('(') {
        let len = s.len();
        return (1..=MAX_SYMBOL_BYTES).contains(&len);
    }
    if s.starts_with('(') && s.ends_with(')') {
        let inner = &s[1..s.len() - 1];
        let tokens = split_sexpr_tokens(inner);
        if tokens.len() > MAX_LIST_ARITY {
            return false;
        }
        return tokens.iter().all(|token| sexpr_string_fits(token));
    }
    (1..=MAX_SYMBOL_BYTES).contains(&s.len())
}

/// Whether one INDEX ENTRY (an `EList` of elements) fits the machine caps:
/// element count ≤ [`MAX_LIST_ARITY`] (the entry's segment count) and every
/// element's S-expression fits ([`sexpr_string_fits`]).
fn entry_fits_machine_caps(elements: &[Par]) -> bool {
    if elements.len() > MAX_LIST_ARITY {
        return false;
    }
    elements
        .iter()
        .all(|element| sexpr_string_fits(&ParToSExpr::par_to_sexpr(element)))
}

// ─────────────────────────────────────────────────────────────────────────────
// The index value + the ONE persistent publish (the treatment "spread")
// ─────────────────────────────────────────────────────────────────────────────

/// A built subject index: the [`EPathMap`] VALUE plus the build metadata the
/// harness needs for honest accounting and fail-closed σ checks.
#[derive(Debug, Clone)]
pub struct PathmapIndex {
    /// The index EPathMap VALUE (publish with [`pathmap_spread_term_par`]).
    pub index: Par,
    /// «s» entries (one per subject node).
    pub site_entries: usize,
    /// «v» entries actually included (≤ node count).
    pub value_entries: usize,
    /// Locations whose «v» entry was OMITTED because its encoding would blow
    /// the machine caps. A query needing σ at one of these fails closed at
    /// harness build time.
    pub omitted_value_locations: BTreeSet<String>,
}

fn push_index_entries(
    term: &GroundTerm,
    language_fingerprint: &str,
    components: &mut Vec<String>,
    entries: &mut Vec<Par>,
    value_entries: &mut usize,
    omitted: &mut BTreeSet<String>,
) -> Result<(), String> {
    // «s»: [ tag(f), c₀, …, c_d ] — MUST fit (else the cell fails closed).
    let mut s_elements: Vec<Par> =
        Vec::with_capacity(1 + components.len());
    s_elements.push(quoted(&e6a_tag_string(language_fingerprint, &term.constructor)));
    for component in components.iter() {
        s_elements.push(quoted(component));
    }
    if !entry_fits_machine_caps(&s_elements) {
        return Err(format!(
            "E-6a index «s» entry exceeds the machine trie-key caps at location `{}` \
             (site depth {} — symbol ≤ {MAX_SYMBOL_BYTES} bytes, arity ≤ {MAX_LIST_ARITY}): \
             the cell fails closed (DNF-by-machine-cap)",
            components.join("/"),
            components.len(),
        ));
    }
    entries.push(ground_list(s_elements));

    // «v»: [ "v", c₀, …, c_d, @val, (⟦t⟧,) ] — OMITTED (recorded) when over-cap.
    // The `@val` sentinel isolates the σ value below `["v", c₀…c_d, @val]` so it
    // stays uniquely addressable when the σ position binds a NON-LEAF (deeper
    // «v» entries share `["v", c₀…c_d]`); see [`VALUE_LEAF_SENTINEL`].
    let mut v_elements: Vec<Par> = Vec::with_capacity(3 + components.len());
    v_elements.push(quoted(VALUE_FAMILY));
    for component in components.iter() {
        v_elements.push(quoted(component));
    }
    v_elements.push(quoted(VALUE_LEAF_SENTINEL));
    v_elements.push(ground_tuple(reflect_ground_term_par(term, language_fingerprint)));
    if entry_fits_machine_caps(&v_elements) {
        entries.push(ground_list(v_elements));
        *value_entries += 1;
    } else {
        omitted.insert(components.join("/"));
    }

    for (index, child) in term.children.iter().enumerate() {
        components.push(child_component(&term.constructor, index));
        push_index_entries(
            child,
            language_fingerprint,
            components,
            entries,
            value_entries,
            omitted,
        )?;
        components.pop();
    }
    Ok(())
}

/// The `{op}.{index}` component of one descent step — the SAME derivation as
/// [`spread_child_location`] (`{parent}/{op}.{index}`), exposed per component
/// so paths segment at the slashes.
fn child_component(op: &str, index: usize) -> String {
    // spread_child_location("", op, index) would yield "/op.index"; strip the
    // joiner by deriving from an empty parent and dropping the leading slash —
    // asserting the two derivations can never drift.
    let derived = spread_child_location("", op, index);
    derived
        .strip_prefix('/')
        .expect("spread_child_location joins with a slash")
        .to_string()
}

/// Build the subject index for `subject` at root site `root_site` — two entry
/// families per node (see the module rustdoc). Fails closed when any «s»
/// entry exceeds the machine caps.
pub fn build_pathmap_index(
    subject: &GroundTerm,
    language_fingerprint: &str,
    root_site: &str,
) -> Result<PathmapIndex, String> {
    let node_count = e6a_node_count(subject);
    let mut entries: Vec<Par> = Vec::with_capacity(2 * node_count);
    let mut components: Vec<String> = vec![root_site.to_string()];
    let mut value_entries = 0usize;
    let mut omitted: BTreeSet<String> = BTreeSet::new();
    push_index_entries(
        subject,
        language_fingerprint,
        &mut components,
        &mut entries,
        &mut value_entries,
        &mut omitted,
    )?;
    // E-2-D (reflected-ABI v2): the reducer NORMALIZES an `EPathMap` to its TRIE-CANONICAL entry
    // order (`canonical_path`: "trie order = canonical order", a lexicographic walk over each
    // entry's `encode_trie_path` bytes) on reduction. Emit the entries in that canonical order
    // HOST-side too, so the whole-value bind+forward round-trip stays byte-identical: the
    // hereditary-ground marker enlarged each «v» value, which reordered the trie walk relative to
    // the DFS traversal order these were pushed in (they coincided pre-marker). Sorting by the
    // f1r3node-exposed `encode_trie_path` reproduces the reducer's order exactly (no f1r3node edit).
    entries.sort_by_cached_key(encode_trie_path);
    let index = Par::default().with_exprs(vec![Expr {
        // EPathMap fix P3 (f1r3node-rust-mettail, PM-2): `EPathMap` is now the
        // hand-maintained extern_path wrapper with a private shadow cell —
        // struct literals are impossible out of crate; construct via
        // `EPathMap::new` (same four proto fields, cell starts empty).
        expr_instance: Some(ExprInstance::EPathmapBody(EPathMap::new(
            entries,
            Vec::new(),
            false,
            None,
        ))),
    }]);
    Ok(PathmapIndex {
        index,
        site_entries: node_count,
        value_entries,
        omitted_value_locations: omitted,
    })
}

/// Node count of a subject (up to 2 index entries are built per node).
pub fn e6a_node_count(term: &GroundTerm) -> usize {
    1 + term.children.iter().map(e6a_node_count).sum::<usize>()
}

/// THE treatment "spread": ONE PERSISTENT produce of the subject index on
/// [`e6a_index_channel`] — the E-6a replacement for the per-node
/// [`spread_term_par`](mettail_rholang_codegen::spread_term_par) sends. Every
/// discovery process and per-site query process reads the SAME one datum
/// (persistent produce ⇒ non-destructive reads), so the treatment's
/// spread-send count is exactly 1. Returns the publish `Par` plus the build
/// metadata.
pub fn pathmap_spread_term_par(
    subject: &GroundTerm,
    language_fingerprint: &str,
    root_site: &str,
) -> Result<(Par, PathmapIndex), String> {
    let built = build_pathmap_index(subject, language_fingerprint, root_site)?;
    let publish = new_send_par(
        quoted(&e6a_index_channel(root_site)),
        vec![built.index.clone()],
        true, // PERSISTENT: one produce serves every query COMM.
        Vec::new(),
        false,
        Vec::new(),
        false,
    );
    Ok((publish, built))
}

/// The locations whose «v» entry the cap validator would omit for `subject` —
/// the harness-side fail-closed check for σ positions (deterministic mirror of
/// the build walk; exposed separately so query building needs no index value).
pub fn e6a_omitted_value_locations(
    subject: &GroundTerm,
    language_fingerprint: &str,
    root_site: &str,
) -> Result<BTreeSet<String>, String> {
    Ok(build_pathmap_index(subject, language_fingerprint, root_site)?.omitted_value_locations)
}

// ─────────────────────────────────────────────────────────────────────────────
// Machine-side site enumeration (discovery)
// ─────────────────────────────────────────────────────────────────────────────

/// The rule-root ops of every compiled entry (read off the compiled RULESET's
/// automaton view — the host never walks the SUBJECT for this).
pub fn e6a_entry_root_ops(ruleset: &InRhoMatchingRuleset) -> Vec<String> {
    let view = ruleset.automaton.view();
    let mut ops: Vec<String> = (0..view.entry_count())
        .filter_map(|entry| match view.node(view.entry_root_state(entry)) {
            AutomatonNode::App { op, .. } => Some(op.to_string()),
            AutomatonNode::Var(_) => None,
        })
        .collect();
    ops.sort();
    ops.dedup();
    ops
}

/// The MACHINE-side site-enumeration call: per rule-root op, ONE process
///
/// ```text
/// for(@idx <- e6a:idx:ρ){ e6a:sites:ρ/op!( idx.readZipperAt([tag(op)]).getSubtrie() ) }
/// ```
///
/// The op-first «s» family makes the subtrie EXACTLY the candidate-site set of
/// `op`, computed by the reducer from the published index. One query COMM (the
/// idx bind against the persistent produce) + one result produce per op.
pub fn discovery_call_par(
    ruleset: &InRhoMatchingRuleset,
    language_fingerprint: &str,
    root_site: &str,
) -> Par {
    let mut call = Par::default();
    for op in e6a_entry_root_ops(ruleset) {
        let tag = e6a_tag_string(language_fingerprint, &op);
        let zipper = method_par(
            new_boundvar_par(0, create_bit_vector(&[0]), false),
            "readZipperAt",
            vec![ground_list(vec![quoted(&tag)])],
            &[0],
        );
        let subtrie = method_par(zipper, "getSubtrie", Vec::new(), &[0]);
        let publish = new_send_par(
            quoted(&e6a_sites_channel(root_site, &op)),
            vec![subtrie],
            false,
            create_bit_vector(&[0]),
            false,
            create_bit_vector(&[0]),
            false,
        );
        let receive = new_receive_par(
            vec![ReceiveBind {
                patterns: vec![new_freevar_par(0, Vec::new())],
                source: Some(quoted(&e6a_index_channel(root_site))),
                remainder: None,
                free_count: 1,
            }],
            publish,
            false,
            false,
            1,
            Vec::new(),
            false,
            Vec::new(),
            false,
        );
        call = call.append(receive);
    }
    call
}

/// Decode a machine-enumerated per-op subtrie value (read back from
/// [`e6a_sites_channel`]) into its candidate SITE strings: each entry is the
/// «s» list `[GString(tag), GString(c₀), …, GString(c_d)]`; the site string is
/// the `/`-join of the components. Fails loudly on anything else;
/// `expected_tag` pins that the subtrie really is the queried op's family.
pub fn decode_sites_par(sites_value: &Par, expected_tag: &str) -> Result<Vec<String>, String> {
    let [expr] = sites_value.exprs.as_slice() else {
        return Err(format!("sites value is not a single expr: {sites_value:?}"));
    };
    let Some(ExprInstance::EPathmapBody(pathmap)) = &expr.expr_instance else {
        return Err(format!("sites value is not an EPathMap: {expr:?}"));
    };
    let mut sites: Vec<String> = Vec::with_capacity(pathmap.ps.len());
    for entry in &pathmap.ps {
        let [entry_expr] = entry.exprs.as_slice() else {
            return Err(format!("subtrie entry is not a single expr: {entry:?}"));
        };
        let Some(ExprInstance::EListBody(list)) = &entry_expr.expr_instance else {
            return Err(format!("subtrie entry is not an EList: {entry_expr:?}"));
        };
        if list.ps.len() < 2 {
            return Err(format!("subtrie entry has no site components: {list:?}"));
        }
        let tag = single_gstring(&list.ps[0])
            .ok_or_else(|| format!("subtrie entry tag is not a GString: {:?}", list.ps[0]))?;
        if tag != expected_tag {
            return Err(format!("subtrie entry tag `{tag}` != expected `{expected_tag}`"));
        }
        let mut components: Vec<&str> = Vec::with_capacity(list.ps.len() - 1);
        for component_par in &list.ps[1..] {
            components.push(single_gstring(component_par).ok_or_else(|| {
                format!("subtrie entry component is not a GString: {component_par:?}")
            })?);
        }
        sites.push(components.join("/"));
    }
    Ok(sites)
}

fn single_gstring(par: &Par) -> Option<&str> {
    match par.exprs.as_slice() {
        [expr] => match &expr.expr_instance {
            Some(ExprInstance::GString(s)) => Some(s.as_str()),
            _ => None,
        },
        _ => None,
    }
}

/// Pairwise NON-ANCESTRY of machine-enumerated candidate sites — the same
/// prefix-comparability check the `multi_rule_shared` sa drive pins
/// structurally (in the paths-subspaces reading: no site lies in another's
/// SUBSPACE). Ancestral candidate sets fail closed — the treatment keeps the
/// conservative refusal honestly for them.
pub fn sites_non_ancestral(sites: &[String]) -> bool {
    for (i, a) in sites.iter().enumerate() {
        for b in sites.iter().skip(i + 1) {
            if a == b || a.starts_with(&format!("{b}/")) || b.starts_with(&format!("{a}/")) {
                return false;
            }
        }
    }
    true
}

// ─────────────────────────────────────────────────────────────────────────────
// Per-(entry, site) QUERY-MATCH process (matching driven from the index)
// ─────────────────────────────────────────────────────────────────────────────

/// The compiled shape of ONE automaton entry, read off the automaton view by
/// the SAME pattern-DFS as the network emitter's `collect_nested_schedule`:
/// guard positions (site-relative components + op, pre-order — the root plus
/// every nested App descent) and σ positions (Var-leaf site-relative
/// components, DFS first-occurrence order — exactly `build_accept_send`'s
/// slot order). LINEAR entries only (a repeated var fails closed, mirroring
/// `AutomatonUnsupported::NonLinearVariable`; the E-6a corpus is linear).
#[derive(Debug, Clone)]
pub struct EntryQueryShape {
    /// `(site-relative components, op)` for the root (empty components) and
    /// every nested App position.
    pub guards: Vec<(Vec<String>, String)>,
    /// Var-leaf site-relative components in pattern-DFS order (the σ slots).
    pub sigma_positions: Vec<Vec<String>>,
}

fn collect_query_shape(
    view: &SetAutomatonView<'_, String>,
    state: StateId,
    relative: &mut Vec<String>,
    guards: &mut Vec<(Vec<String>, String)>,
    sigma_positions: &mut Vec<Vec<String>>,
    names: &mut Vec<String>,
) -> Result<(), String> {
    match view.node(state) {
        AutomatonNode::Var(name) => {
            if names.iter().any(|seen| seen == name) {
                return Err(format!(
                    "E-6a query codegen is LINEAR-only (repeated var `{name}`) — fail closed"
                ));
            }
            names.push(name.to_string());
            sigma_positions.push(relative.clone());
            Ok(())
        },
        AutomatonNode::App { op, args } => {
            let op = op.to_string();
            let args = args.to_vec();
            guards.push((relative.clone(), op.clone()));
            for (index, arg) in args.into_iter().enumerate() {
                relative.push(child_component(&op, index));
                collect_query_shape(view, arg, relative, guards, sigma_positions, names)?;
                relative.pop();
            }
            Ok(())
        },
    }
}

/// Read one compiled entry's [`EntryQueryShape`] off the automaton view.
pub fn entry_query_shape(
    view: &SetAutomatonView<'_, String>,
    entry: usize,
) -> Result<EntryQueryShape, String> {
    let mut guards: Vec<(Vec<String>, String)> = Vec::new();
    let mut sigma_positions: Vec<Vec<String>> = Vec::new();
    let mut names: Vec<String> = Vec::new();
    let mut relative: Vec<String> = Vec::new();
    collect_query_shape(
        view,
        view.entry_root_state(entry),
        &mut relative,
        &mut guards,
        &mut sigma_positions,
        &mut names,
    )?;
    Ok(EntryQueryShape { guards, sigma_positions })
}

/// The absolute component path of a site-relative position at `site`.
fn absolute_components(site: &str, relative: &[String]) -> Vec<String> {
    let mut components: Vec<String> = site.split('/').map(str::to_string).collect();
    components.extend(relative.iter().cloned());
    components
}

/// The query path-list `Par` `[first, c₀, …, c_d]`.
fn query_path_list(first: &str, components: &[String]) -> Par {
    let mut elements: Vec<Par> = Vec::with_capacity(1 + components.len());
    elements.push(quoted(first));
    for component in components {
        elements.push(quoted(component));
    }
    ground_list(elements)
}

/// The «v» value-leaf query PREFIX `Par` `["v", c₀, …, c_d, @val]` — the
/// sentinel-terminated prefix below which sits EXACTLY the σ-value tuple (see
/// [`VALUE_LEAF_SENTINEL`]). Both the σ-existence guard and the σ chain address
/// the value through THIS prefix so `descendFirst` cannot mis-descend into a
/// deeper «v» entry when the σ position binds a non-leaf subtree.
fn value_query_path(components: &[String]) -> Par {
    let mut elements: Vec<Par> = Vec::with_capacity(2 + components.len());
    elements.push(quoted(VALUE_FAMILY));
    for component in components {
        elements.push(quoted(component));
    }
    elements.push(quoted(VALUE_LEAF_SENTINEL));
    ground_list(elements)
}

/// `idx.readZipperAt([tag(op), c₀…c_d]).pathExists()` — TRUE iff the subject
/// node at the location exists with head constructor `op`.
fn tag_guard_expr(tag: &str, components: &[String]) -> Par {
    let zipper = method_par(
        new_boundvar_par(0, create_bit_vector(&[0]), false),
        "readZipperAt",
        vec![query_path_list(tag, components)],
        &[0],
    );
    method_par(zipper, "pathExists", Vec::new(), &[0])
}

/// `idx.readZipperAt(["v", c₀…c_d, @val]).pathExists()` — the σ-position
/// existence guard (defensive totality: keeps `getLeaf` unreachable on any
/// malformed or cap-omitted index entry rather than aborting the injection).
fn value_exists_guard_expr(components: &[String]) -> Par {
    let zipper = method_par(
        new_boundvar_par(0, create_bit_vector(&[0]), false),
        "readZipperAt",
        vec![value_query_path(components)],
        &[0],
    );
    method_par(zipper, "pathExists", Vec::new(), &[0])
}

/// `idx.readZipperAt(["v", c₀…c_d, @val]).descendFirst().getLeaf()` — navigate
/// to the σ value below the sentinel-terminated prefix and return the ORIGINAL
/// entry `Par` `["v", c₀, …, c_d, @val, (⟦t⟧,)]`. The `@val` sentinel makes the
/// value tuple the SOLE child below the prefix even when the σ position binds a
/// non-leaf subtree (see [`VALUE_LEAF_SENTINEL`]).
fn sigma_chain_expr(components: &[String]) -> Par {
    let zipper = method_par(
        new_boundvar_par(0, create_bit_vector(&[0]), false),
        "readZipperAt",
        vec![value_query_path(components)],
        &[0],
    );
    let descended = method_par(zipper, "descendFirst", Vec::new(), &[0]);
    method_par(descended, "getLeaf", Vec::new(), &[0])
}

/// Conjoin ≥ 1 guard exprs with `EAnd` (left fold).
fn and_all(mut conjuncts: Vec<Par>) -> Par {
    let mut guard = conjuncts.remove(0);
    for conjunct in conjuncts {
        guard = Par {
            exprs: vec![Expr {
                expr_instance: Some(ExprInstance::EAndBody(EAnd {
                    p1: Some(guard),
                    p2: Some(conjunct),
                })),
            }],
            locally_free: create_bit_vector(&[0]),
            connective_used: false,
            ..Par::default()
        };
    }
    guard
}

/// Build the PER-(entry, site) QUERY-MATCH process — the treatment analogue of
/// one per-site receiver network, with matching driven from the INDEX instead
/// of spread channels:
///
/// ```text
/// for(@idx <- e6a:idx:ρ){
///   match (tag-guards ∧ σ-existence-guards) {
///     true => match [σ-chain₀, …, σ-chainₖ₋₁] {
///       [[…, (s₀,)], …, […, (sₖ₋₁,)]] => accept!(s₀, …, sₖ₋₁, @out)
///     }
///     _ => Nil
///   }
/// }
/// ```
///
/// * ONE query COMM (the idx bind against the persistent index produce);
/// * guards + σ chains are COMM-free method evaluations;
/// * the accept send is byte-shaped like `build_accept_send` (σ slots in
///   pattern-DFS first-occurrence order, then `@out`), so the SAME
///   σ-receivers/σ-echoes consume it;
/// * a guard-failing site fires NOTHING (`_ => Nil`) — the discovery
///   pre-filter is re-VERIFIED on the machine, so a stale site can never
///   fire a wrong match.
///
/// Fails closed (Err) when a σ position's «v» entry was cap-omitted
/// (`omitted_value_locations`).
pub fn entry_query_match_par(
    shape: &EntryQueryShape,
    language_fingerprint: &str,
    root_site: &str,
    site: &str,
    accept_channel: &str,
    out_channel: &str,
    omitted_value_locations: &BTreeSet<String>,
) -> Result<Par, String> {
    // ── σ positions must have «v» entries (cap-omission fails closed) ───────
    let sigma_components: Vec<Vec<String>> = shape
        .sigma_positions
        .iter()
        .map(|relative| absolute_components(site, relative))
        .collect();
    for components in &sigma_components {
        let location = components.join("/");
        if omitted_value_locations.contains(&location) {
            return Err(format!(
                "E-6a query at site `{site}` needs σ at `{location}`, whose «v» entry was \
                 omitted by the machine-cap validator — fail closed"
            ));
        }
    }

    // ── the guard conjunction (evaluated under idx = BoundVar(0)) ────────────
    let mut conjuncts: Vec<Par> =
        Vec::with_capacity(shape.guards.len() + sigma_components.len());
    for (relative, op) in &shape.guards {
        conjuncts.push(tag_guard_expr(
            &e6a_tag_string(language_fingerprint, op),
            &absolute_components(site, relative),
        ));
    }
    for components in &sigma_components {
        conjuncts.push(value_exists_guard_expr(components));
    }
    let guard = and_all(conjuncts);

    // ── the σ-extraction match (inside the true case) ────────────────────────
    let k = sigma_components.len();
    let sigma_target = Par {
        exprs: vec![Expr {
            expr_instance: Some(ExprInstance::EListBody(EList {
                ps: sigma_components
                    .iter()
                    .map(|components| sigma_chain_expr(components))
                    .collect(),
                locally_free: create_bit_vector(&[0]),
                connective_used: false,
                remainder: None,
            })),
        }],
        locally_free: create_bit_vector(&[0]),
        connective_used: false,
        ..Par::default()
    };
    // Pattern: per slot, the «v» entry list ["v", c₀, …, c_d, @val, (⟦t⟧,)]
    // matched as [_ × (d+3), (s,)] — wildcards for the family+components+@val
    // sentinel, a 1-tuple pattern binding the σ slot.
    let sigma_pattern = Par {
        exprs: vec![Expr {
            expr_instance: Some(ExprInstance::EListBody(EList {
                ps: sigma_components
                    .iter()
                    .enumerate()
                    .map(|(slot, components)| {
                        let arity = components.len() + 3; // "v" + components + @val + tuple
                        let mut elements: Vec<Par> = Vec::with_capacity(arity);
                        for _ in 0..arity - 1 {
                            elements.push(new_wildcard_par(Vec::new(), true));
                        }
                        elements.push(Par {
                            exprs: vec![Expr {
                                expr_instance: Some(ExprInstance::ETupleBody(ETuple {
                                    ps: vec![new_freevar_par(slot as i32, Vec::new())],
                                    locally_free: Vec::new(),
                                    connective_used: true,
                                })),
                            }],
                            locally_free: Vec::new(),
                            connective_used: true,
                            ..Par::default()
                        });
                        Par {
                            exprs: vec![Expr {
                                expr_instance: Some(ExprInstance::EListBody(EList {
                                    ps: elements,
                                    locally_free: Vec::new(),
                                    connective_used: true,
                                    remainder: None,
                                })),
                            }],
                            locally_free: Vec::new(),
                            connective_used: true,
                            ..Par::default()
                        }
                    })
                    .collect(),
                locally_free: Vec::new(),
                connective_used: true,
                remainder: None,
            })),
        }],
        locally_free: Vec::new(),
        connective_used: true,
        ..Par::default()
    };
    // Body: accept!(s₀, …, sₖ₋₁, @out) — FreeVar(slot) is BoundVar(k−1−slot)
    // in the case body (the `build_accept_send` frame: DFS-first slot highest).
    let mut accept_data: Vec<Par> = Vec::with_capacity(k + 1);
    for slot in 0..k {
        let idx = k - 1 - slot;
        accept_data.push(new_boundvar_par(idx as i32, create_bit_vector(&[idx]), false));
    }
    accept_data.push(quoted(out_channel));
    let accept_free: Vec<usize> = (0..k).collect();
    let accept_bits = create_bit_vector(&accept_free);
    let accept_send = new_send_par(
        quoted(accept_channel),
        accept_data,
        false,
        accept_bits.clone(),
        false,
        accept_bits,
        false,
    );
    let sigma_case = MatchCase {
        pattern: Some(sigma_pattern),
        source: Some(accept_send),
        free_count: k as i32,
        guard: None,
    };
    let sigma_match = new_match_par(
        sigma_target,
        vec![sigma_case],
        create_bit_vector(&[0]),
        false,
        create_bit_vector(&[0]),
        false,
    );

    // ── the guard match: true ⇒ σ match, anything else ⇒ Nil ────────────────
    let guard_cases = vec![
        MatchCase {
            pattern: Some(new_gbool_par(true, Vec::new(), false)),
            source: Some(sigma_match),
            free_count: 0,
            guard: None,
        },
        MatchCase {
            pattern: Some(new_wildcard_par(Vec::new(), true)),
            source: Some(Par::default()),
            free_count: 0,
            guard: None,
        },
    ];
    let guard_match = new_match_par(
        guard,
        guard_cases,
        create_bit_vector(&[0]),
        false,
        create_bit_vector(&[0]),
        false,
    );

    // ── the idx bind (ONE query COMM against the persistent index) ──────────
    Ok(new_receive_par(
        vec![ReceiveBind {
            patterns: vec![new_freevar_par(0, Vec::new())],
            source: Some(quoted(&e6a_index_channel(root_site))),
            remainder: None,
            free_count: 1,
        }],
        guard_match,
        false,
        false,
        1,
        Vec::new(),
        false,
        Vec::new(),
        false,
    ))
}

// ─────────────────────────────────────────────────────────────────────────────
// The TWO-PHASE treatment drive (the pre-registered REDUCED form)
// ─────────────────────────────────────────────────────────────────────────────

/// Injection-1 seed (index publish + discovery). Distinct from the phase-2
/// seed so the two injections' per-term randomness never aliases (both fixed,
/// so a rep reproduces bit-identically).
const E6A_PHASE1_SEED: &[u8] =
    b"mettail E-6a PathMap-index treatment :: phase-1 (publish+discovery) seed v1";

/// Injection-2 seed (per-site query-match processes).
const E6A_PHASE2_SEED: &[u8] =
    b"mettail E-6a PathMap-index treatment :: phase-2 (per-site queries) seed v1";

/// One treatment rep's outcome.
#[derive(Debug)]
pub struct E6aDriveOutcome {
    /// The instrumented record: counters are CUMULATIVE over the ONE fresh
    /// runtime (both injections), `build`/`inj`/`readback` are the summed
    /// phase timers, `program_encoded_len`/`program_receiver_count` sum both
    /// injected programs, `observed` is the OUT readback after injection 2.
    pub result: BenchRunResult,
    /// The MACHINE-enumerated candidate sites per rule-root op (decoded from
    /// the per-op subtrie readback), in readback order.
    pub machine_sites: BTreeMap<String, Vec<String>>,
    /// The treatment's static spread-send count: the ONE persistent index
    /// publish + the per-op discovery-result sends (`1 + #ops`).
    pub treatment_spread_sends: usize,
    /// «v» entries the machine-cap validator omitted (empty for every admitted
    /// corpus cell; recorded for honesty).
    pub omitted_value_locations: BTreeSet<String>,
    /// Host-side emission span (index build + discovery + query codegen).
    pub emission: Duration,
    /// Counting-runtime construction span.
    pub bringup: Duration,
}

/// A typed treatment-drive failure (the driver records it as a DNF line).
#[derive(Debug)]
pub struct E6aDriveFailure {
    pub reason: String,
}

impl E6aDriveFailure {
    fn new(reason: impl Into<String>) -> E6aDriveFailure {
        E6aDriveFailure { reason: reason.into() }
    }
}

/// One phase's injection on the shared counting runtime: soft checkpoint +
/// budget reset + FIXED seed + `inj` (the `bench_inj_and_read` discipline with
/// a caller-supplied seed and no readback).
async fn e6a_inj_phase<R: RhoRuntime>(
    runtime: &mut R,
    program: &Par,
    seed: &[u8],
) -> Result<(Duration, Duration), E6aDriveFailure> {
    let build_started = Instant::now();
    let checkpoint = runtime.create_soft_checkpoint().await;
    runtime.cost().set(Cost::unsafe_max());
    let rand = Blake2b512Random::create_from_bytes(seed);
    let build = build_started.elapsed();

    let inj_started = Instant::now();
    if let Err(err) = runtime.inj(program.clone(), Env::new(), rand).await {
        runtime.revert_to_soft_checkpoint(checkpoint).await;
        return Err(E6aDriveFailure::new(format!("e6a inj: {err:?}")));
    }
    Ok((build, inj_started.elapsed()))
}

/// Drive ONE E-6a treatment rep for `subject` against `ruleset` on a FRESH
/// counting runtime — the pre-registered REDUCED form, two-phase:
///
/// 1. **Injection 1** (seed [`E6A_PHASE1_SEED`]): the installed σ-receiver
///    program (when the workload has one) + the direct-construction σ-echoes
///    + [`pathmap_spread_term_par`] (ONE persistent index produce) +
///    [`discovery_call_par`] (machine-side per-op site enumeration).
/// 2. **Readback**: the per-op subtrie values are read off
///    [`e6a_sites_channel`] and decoded ([`decode_sites_par`]); the union of
///    candidate sites must be pairwise NON-ANCESTRAL
///    ([`sites_non_ancestral`], fail-closed).
/// 3. **Injection 2** (seed [`E6A_PHASE2_SEED`]): one
///    [`entry_query_match_par`] per (entry, machine-enumerated candidate site
///    of the entry's root op) — matching + σ-binding run ON the machine
///    against the persistent index; accepts fire the SAME σ-receivers.
/// 4. **OUT readback** into the returned [`BenchRunResult`].
///
/// What honestly remains host-side: the readback + decode, the per-site query
/// `Par` CODEGEN, and the second injection. What the machine does: candidate
/// discovery, head/descent verification, σ-binding, and firing.
///
/// `site_filter`: when `Some`, only machine-enumerated sites IN the filter get
/// a query process — the β-STRATEGY selector (e.g. the λ-chain per-step drive
/// restricts to the root site, mirroring the control column's root-restricted
/// per-step discipline; the machine still enumerates ALL candidate sites, and
/// a filter site absent from the enumeration simply installs nothing). The
/// non-ancestry check applies to the INSTALLED set.
#[allow(clippy::too_many_arguments)]
pub async fn drive_e6a_treatment(
    ruleset: &InRhoMatchingRuleset,
    installed_program: Option<&Par>,
    echo_channels: &[String],
    subject: &GroundTerm,
    root_site: &str,
    out_channel: &str,
    params: BenchWorkloadParams,
    echo_receiver: impl Fn(&str) -> Par,
    site_filter: Option<&BTreeSet<String>>,
) -> Result<E6aDriveOutcome, E6aDriveFailure> {
    let language_fingerprint = &ruleset.language_fingerprint;

    // ── bringup ─────────────────────────────────────────────────────────────
    let bringup_started = Instant::now();
    let (mut runtime, comm_counters, match_counters) =
        bench_runtime_with_counters(Vec::new(), out_channel)
            .await
            .map_err(|e| E6aDriveFailure::new(format!("counting runtime bring-up: {e}")))?;
    let bringup = bringup_started.elapsed();

    // ── emission, phase 1 ───────────────────────────────────────────────────
    let emission_started = Instant::now();
    let (publish, built) = pathmap_spread_term_par(subject, language_fingerprint, root_site)
        .map_err(E6aDriveFailure::new)?;
    let discovery = discovery_call_par(ruleset, language_fingerprint, root_site);
    let treatment_spread_sends = count_send_nodes(&publish) + count_send_nodes(&discovery);

    let mut phase1 = match installed_program {
        Some(installed) => installed.clone(),
        None => Par::default(),
    };
    for channel in echo_channels {
        phase1 = phase1.append(echo_receiver(channel));
    }
    phase1 = phase1.append(publish).append(discovery);
    let mut emission = emission_started.elapsed();

    // ── injection 1: publish + discovery ────────────────────────────────────
    let (build1, inj1) = e6a_inj_phase(&mut runtime, &phase1, E6A_PHASE1_SEED).await?;

    // ── machine-enumeration readback ────────────────────────────────────────
    let readback_started = Instant::now();
    let ops = e6a_entry_root_ops(ruleset);
    let mut machine_sites: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut all_sites: Vec<String> = Vec::new();
    for op in &ops {
        let channel = quoted(&e6a_sites_channel(root_site, op));
        let data = runtime.get_data(&channel).await;
        let [datum] = data.as_slice() else {
            return Err(E6aDriveFailure::new(format!(
                "expected exactly one discovery result on {}, got {}",
                e6a_sites_channel(root_site, op),
                data.len(),
            )));
        };
        let [value] = datum.a.pars.as_slice() else {
            return Err(E6aDriveFailure::new(format!(
                "discovery result on {} is not a single value",
                e6a_sites_channel(root_site, op),
            )));
        };
        let sites = decode_sites_par(value, &e6a_tag_string(language_fingerprint, op))
            .map_err(E6aDriveFailure::new)?;
        all_sites.extend(
            sites
                .iter()
                .filter(|site| site_filter.map_or(true, |filter| filter.contains(*site)))
                .cloned(),
        );
        machine_sites.insert(op.clone(), sites);
    }
    if !sites_non_ancestral(&all_sites) {
        return Err(E6aDriveFailure::new(format!(
            "machine-enumerated candidate sites (post-filter) are not pairwise non-ancestral — \
             fail closed (sites: {all_sites:?})"
        )));
    }
    let mut readback = readback_started.elapsed();

    // ── emission, phase 2: per-(entry, site) query-match codegen ────────────
    let emission2_started = Instant::now();
    let view = ruleset.automaton.view();
    let mut phase2 = Par::default();
    for entry in 0..view.entry_count() {
        let AutomatonNode::App { op, .. } = view.node(view.entry_root_state(entry)) else {
            return Err(E6aDriveFailure::new("variable-root entry — fail closed"));
        };
        let op = op.to_string();
        let pid = view.entry_id(entry);
        let accept_channel = ruleset
            .accept_channels
            .iter()
            .find(|(entry_pid, _)| *entry_pid == pid)
            .map(|(_, channel)| channel.clone())
            .ok_or_else(|| E6aDriveFailure::new("entry without an accept channel"))?;
        let shape = entry_query_shape(&view, entry).map_err(E6aDriveFailure::new)?;
        let sites = machine_sites
            .get(&op)
            .expect("every entry root op has a discovery readback entry");
        for site in sites
            .iter()
            .filter(|site| site_filter.map_or(true, |filter| filter.contains(*site)))
        {
            phase2 = phase2.append(
                entry_query_match_par(
                    &shape,
                    language_fingerprint,
                    root_site,
                    site,
                    &accept_channel,
                    out_channel,
                    &built.omitted_value_locations,
                )
                .map_err(E6aDriveFailure::new)?,
            );
        }
    }
    emission += emission2_started.elapsed();

    // ── injection 2: per-site query-match ───────────────────────────────────
    let (build2, inj2) = e6a_inj_phase(&mut runtime, &phase2, E6A_PHASE2_SEED).await?;

    // ── OUT readback ────────────────────────────────────────────────────────
    let consumed_cost_units = runtime.cost().total_cost().value;
    let out_read_started = Instant::now();
    let out_data = runtime.get_data(&quoted(out_channel)).await;
    let mut observed: Vec<Par> =
        Vec::with_capacity(out_data.iter().map(|datum| datum.a.pars.len()).sum());
    for datum in out_data {
        // EPathMap fix P4.1 coupling: Datum.a is Arc-shared — materialize
        // the readback (cold path, once per run).
        for par in std::sync::Arc::unwrap_or_clone(datum.a).pars {
            observed.push(par);
        }
    }
    readback += out_read_started.elapsed();

    let result = BenchRunResult {
        workload: params,
        build: build1 + build2,
        inj: inj1 + inj2,
        readback,
        program_encoded_len: phase1.encoded_len() + phase2.encoded_len(),
        program_receiver_count: count_receive_nodes(&phase1) + count_receive_nodes(&phase2),
        observed,
        consumed_cost_units,
        comm: comm_counters.snapshot(),
        matches: match_counters.snapshot(),
    };
    Ok(E6aDriveOutcome {
        result,
        machine_sites,
        treatment_spread_sends,
        omitted_value_locations: built.omitted_value_locations,
        emission,
        bringup,
    })
}

/// Count the `Send` nodes of a `Par`, recursively over every `Par`-carrying
/// position — the STATIC "spread sends" component of the E-6a primary metric
/// (control: sends of the per-node spread; treatment: the one index publish +
/// the per-op discovery-result sends).
pub fn count_send_nodes(par: &Par) -> usize {
    fn visit_opt(par: &Option<Par>, count: &mut usize) {
        if let Some(par) = par {
            visit(par, count);
        }
    }
    fn visit(par: &Par, count: &mut usize) {
        for send in &par.sends {
            *count += 1;
            visit_opt(&send.chan, count);
            for datum in &send.data {
                visit(datum, count);
            }
        }
        for receive in &par.receives {
            for bind in &receive.binds {
                for pattern in &bind.patterns {
                    visit(pattern, count);
                }
                visit_opt(&bind.source, count);
            }
            visit_opt(&receive.body, count);
            visit_opt(&receive.condition, count);
        }
        for new in &par.news {
            visit_opt(&new.p, count);
        }
        for match_node in &par.matches {
            visit_opt(&match_node.target, count);
            for case in &match_node.cases {
                visit_opt(&case.pattern, count);
                visit_opt(&case.source, count);
                visit_opt(&case.guard, count);
            }
        }
        for bundle in &par.bundles {
            visit_opt(&bundle.body, count);
        }
    }
    let mut count = 0usize;
    visit(par, &mut count);
    count
}
