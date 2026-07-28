//! Decoding a resting `Par` into a [`RuntimeObservationValue`], and **rendering** one
//! into the short, stable text a diagnostic carries.
//!
//! # Why this module is not feature-gated
//!
//! The decoder below used to live in [`crate::run`] behind `#[cfg(feature = "runtime-report")]`,
//! and the renderer did not exist at all — so every datum-producing path that needed to name a
//! `Par` reached for `format!("{par:?}")`, prost's derived `Debug`.
//!
//! That is a defect, not a cosmetic one, because some of those strings become **data on the
//! live tuplespace**. [`crate::speculation::server`]'s publisher calls `produce` into the
//! running deploy's RSpace, so a `[*]` branch failure's message is part of the post-deploy
//! state and therefore of the checkpoint root. Two properties follow, and they are the whole
//! reason this module exists:
//!
//! 1. **The rendering may not depend on the build.** A `#[cfg]` on the renderer — or on the
//!    decoder it needs — would give a `--no-default-features` build a different image for the
//!    same `Par`, i.e. two nodes disagreeing on a block's post-state because of a Cargo flag.
//!    So the decoder is unconditional here, and `runtime-report` keeps gating only what its
//!    name says: the conversion into `mettail_runtime::RuntimeBackendReport` and the installer
//!    wrappers.
//! 2. **The rendering may not depend on a derive.** prost's `Debug` is generated code; a prost
//!    bump that re-spells it silently changes those bytes, so a node built against the new
//!    derive cannot replay a block produced by the old one. That is exactly the hazard
//!    [`crate::speculation::search::ErrorCode`] writes its discriminants out longhand to
//!    prevent, and the `message` beside the code got no such protection.
//!
//! [`render_par_text`] is the answer: **total** (every `Par` has an image), **deterministic**
//! (the image is a function of the `Par`'s protobuf bytes and of this file, and of nothing
//! else), and **bounded** (by [`RENDER_BUDGET_CHARS`] plus a fixed marker).
//!
//! # Two notations, deliberately
//!
//! [`render_observation_text`] renders the **machine's neutral notation**: reserved
//! reflected-ABI labels (`^lambda`, `^bound`, the Peano index) get their standard sugar
//! because they are ABI, shared by every MeTTaIL language; a *user* constructor renders as
//! `Label(child, …)`. Guest surface syntax — λ's `(f a)` for its own `App` constructor — is
//! the business of whatever is presenting, and [`render_observation_text_with`] is the seam
//! it hooks into.
//!
//! ★ That seam is barred from any datum-producing path. A caller-supplied closure deciding
//! consensus-visible bytes would make them depend on *which binary rendered them* — the same
//! defect as (1) above, arrived at from the other direction. The server calls the
//! closure-free entry point.

use mettail_rholang_codegen::{
    BOUND_VAR_REFLECT_LABEL, FREE_VAR_REFLECT_LABEL, LAMBDA_REFLECT_LABEL, PEANO_SUCC_REFLECT_LABEL,
};
use mettail_runtime::RuntimeObservationValue;
use models::rhoapi::expr::ExprInstance;
use models::rhoapi::g_unforgeable::UnfInstance;
use models::rhoapi::Par;
use models::rust::rholang::implicits::GPrivateBuilder;
use prost::Message;
use rspace_plus_plus::rspace::hashing::blake2b256_hash::Blake2b256Hash;

// ══════════════════════════════════════════════════════════════════════════
// Decoding: `Par` → `RuntimeObservationValue`
// ══════════════════════════════════════════════════════════════════════════

fn par_has_only_ground_value_fields(par: &Par) -> bool {
    par.sends.is_empty()
        && par.receives.is_empty()
        && par.news.is_empty()
        && par.matches.is_empty()
        && par.bundles.is_empty()
        && par.connectives.is_empty()
        && par.conditionals.is_empty()
        && par.locally_free.is_empty()
        && !par.connective_used
}

fn single_expr_instance(par: &Par) -> Option<&ExprInstance> {
    if !par_has_only_ground_value_fields(par) || !par.unforgeables.is_empty() {
        return None;
    }

    let [expr] = par.exprs.as_slice() else {
        return None;
    };
    expr.expr_instance.as_ref()
}

fn par_as_unforgeable_observation(par: &Par) -> Option<RuntimeObservationValue> {
    if !par_has_only_ground_value_fields(par) || !par.exprs.is_empty() {
        return None;
    }

    let [unforgeable] = par.unforgeables.as_slice() else {
        return None;
    };

    match unforgeable.unf_instance.as_ref()? {
        UnfInstance::GPrivateBody(value) => {
            Some(RuntimeObservationValue::PrivateName(value.id.clone()))
        },
        UnfInstance::GDeployIdBody(value) => {
            Some(RuntimeObservationValue::DeployId(value.sig.clone()))
        },
        UnfInstance::GDeployerIdBody(value) => {
            Some(RuntimeObservationValue::DeployerId(value.public_key.clone()))
        },
        UnfInstance::GSysAuthTokenBody(_) => Some(RuntimeObservationValue::SysAuthToken),
    }
}

fn decode_runtime_values(pars: &[Par]) -> Option<Vec<RuntimeObservationValue>> {
    pars.iter().map(par_as_runtime_observation_value).collect()
}

fn decode_runtime_map(
    pairs: &[models::rhoapi::KeyValuePair],
) -> Option<Vec<(RuntimeObservationValue, RuntimeObservationValue)>> {
    let mut out = Vec::with_capacity(pairs.len());
    for pair in pairs {
        let key = par_as_runtime_observation_value(pair.key.as_ref()?)?;
        let value = par_as_runtime_observation_value(pair.value.as_ref()?)?;
        out.push((key, value));
    }
    out.sort();
    Some(out)
}

fn list_body(par: &Par) -> Option<&models::rhoapi::EList> {
    match single_expr_instance(par)? {
        ExprInstance::EListBody(list) if list.remainder.is_none() && !list.connective_used => {
            Some(list)
        },
        _ => None,
    }
}

fn decode_rholang_bag(
    list: &models::rhoapi::EList,
) -> Option<Vec<(RuntimeObservationValue, usize)>> {
    let [tag, entries] = list.ps.as_slice() else {
        return None;
    };
    let expected_tag = GPrivateBuilder::new_par_from_string(crate::RHOLANG_BAG_ABI_TAG.to_string());
    if tag != &expected_tag {
        return None;
    }

    let entries = list_body(entries)?;
    let mut counts = std::collections::BTreeMap::<RuntimeObservationValue, usize>::new();
    for entry in &entries.ps {
        let entry = list_body(entry)?;
        let [value, count] = entry.ps.as_slice() else {
            return None;
        };
        let value = par_as_runtime_observation_value(value)?;
        let count = match par_as_runtime_observation_value(count)? {
            RuntimeObservationValue::Int(count) if count >= 0 => usize::try_from(count).ok()?,
            _ => return None,
        };
        let slot = counts.entry(value).or_insert(0);
        *slot = slot.checked_add(count)?;
    }
    Some(counts.into_iter().collect())
}

/// Whether `par` is a NON-empty sends-only parallel composition — the AC bag-carrier soup shape
/// (Stage AC2b): at least one `Send` and every other `Par` field empty/closed. Mirrors the exact
/// field set of [`par_has_only_ground_value_fields`], inverted for `sends`.
fn par_is_only_sends(par: &Par) -> bool {
    !par.sends.is_empty()
        && par.exprs.is_empty()
        && par.receives.is_empty()
        && par.news.is_empty()
        && par.matches.is_empty()
        && par.bundles.is_empty()
        && par.connectives.is_empty()
        && par.conditionals.is_empty()
        && par.unforgeables.is_empty()
        && par.locally_free.is_empty()
        && !par.connective_used
}

/// Whether a `Par` is the fully-empty Nil process — the A-S5.5 (AM-3) reflection of an
/// EMPTY AC bag (`op{}` reflects as `Par::default()`), decoded by
/// [`par_as_runtime_observation_value`] as the empty multiset `Bag`.
fn par_is_empty_nil(par: &Par) -> bool {
    par.sends.is_empty()
        && par.exprs.is_empty()
        && par.receives.is_empty()
        && par.news.is_empty()
        && par.matches.is_empty()
        && par.bundles.is_empty()
        && par.connectives.is_empty()
        && par.conditionals.is_empty()
        && par.unforgeables.is_empty()
        && par.locally_free.is_empty()
        && !par.connective_used
}

/// The CARRIER IDENTITY a soup send's channel `@"ac:…"` denotes — everything after the
/// reserved `"ac:"` prefix — when the channel is a quoted, non-empty `GString`.
///
/// Deliberately NOT parsed down to the bare operator label, because the `ac:` family has two
/// shapes and only one of them ends in the operator: the bare soup carrier
/// [`ac_soup_channel`](mettail_rholang_codegen::ac_soup_channel) is
/// `ac:{fingerprint}/{op}`, while the site-keyed
/// [`ac_carrier_channel`](mettail_rholang_codegen::ac_carrier_channel) is
/// `ac:loc:{fingerprint}/{site path}/{op}`. Splitting either one to recover `op` alone would
/// need to know which shape it is holding, and the sole caller does not care: it uses this
/// value ONLY to check that every send in a candidate soup rides the SAME carrier, and
/// carrier equality is the stronger, correct test.
///
/// ★ INV-S6 makes this test strictly sharper than it was. Before the carriers carried a
/// fingerprint, two co-installed languages' same-`op` soups shared one channel name and this
/// decoder MERGED them into a single bag without any way to notice. They now differ in their
/// scope segment, so the `Some(_) => return None` mixed-carrier arm rejects the mixture and
/// fails closed.
fn ac_soup_carrier_identity(chan: &Par) -> Option<&str> {
    match single_expr_instance(chan)? {
        ExprInstance::GString(name) => name
            .strip_prefix("ac:")
            .filter(|carrier| !carrier.is_empty()),
        _ => None,
    }
}

/// Decode the AC bag-carrier process soup — a bag-VALUED AC RHS's OUT value (Stage AC2b) — into a
/// multiset of decoded elements.
///
/// The carrier is a sends-only parallel `Par` in which every send is `@"ac:{op}"!(⟦e⟧)`, the exact
/// shape the codegen `reflect_ac_bag_par` (subject side) and `reflect_hashbag_soup_par` (the AC
/// receiver's bag-RHS body) emit for a `HashBag`: all sends on the SAME `"ac:{op}"` channel, each
/// with exactly one datum, non-persistent, with nothing else present. Each datum decodes through
/// the same [`par_as_runtime_observation_value`], so a bag whose elements are themselves reflected
/// terms (e.g. `Wrap(A)`) decodes recursively. Returns `None` for any `Par` that is not exactly
/// such a soup — a tagged-`EList` term, a scalar, an unforgeable, a `for`-carrying process, or a
/// mixed-operator soup — so this never mis-claims another observation shape (the `"ac:"` channel
/// prefix + sends-only shape are disjoint from every other decoder's head).
fn decode_ac_bag_soup(par: &Par) -> Option<Vec<(RuntimeObservationValue, usize)>> {
    if !par_is_only_sends(par) {
        return None;
    }
    let mut carrier: Option<&str> = None;
    let mut counts = std::collections::BTreeMap::<RuntimeObservationValue, usize>::new();
    for send in &par.sends {
        if send.persistent {
            return None;
        }
        let send_carrier = ac_soup_carrier_identity(send.chan.as_ref()?)?;
        match carrier {
            None => carrier = Some(send_carrier),
            Some(existing) if existing == send_carrier => {},
            // A mixed carrier is not a single AC bag — two operators, two sites, or (since
            // INV-S6) two LANGUAGES. Fail closed rather than merge two bags.
            Some(_) => return None,
        }
        let [datum] = send.data.as_slice() else {
            return None;
        };
        let value = par_as_runtime_observation_value(datum)?;
        let slot = counts.entry(value).or_insert(0);
        *slot = slot.checked_add(1)?;
    }
    Some(counts.into_iter().collect())
}

/// Recover the UTF-8 tag string carried by a private-name `Par`, when that name
/// was built by `GPrivateBuilder::new_par_from_string(s)`.
///
/// That builder sets the unforgeable's `id` to `s.encode_to_vec()`, i.e.
/// `<String as prost::Message>` — protobuf field 1, length-delimited. `String::
/// decode` is that builder's exact inverse, so this needs no direct knowledge of
/// the wire layout. Returns `None` for any `Par` that is not exactly one
/// `GPrivate` unforgeable, or whose `id` is not a valid encoded string (e.g. a
/// `GPrivate` created by `new_par` from a random UUID still decodes, but its tag
/// simply will not carry the reflected-term prefix).
fn private_name_tag(par: &Par) -> Option<String> {
    if !par_has_only_ground_value_fields(par) || !par.exprs.is_empty() {
        return None;
    }
    let [unforgeable] = par.unforgeables.as_slice() else {
        return None;
    };
    match unforgeable.unf_instance.as_ref()? {
        UnfInstance::GPrivateBody(value) => String::decode(value.id.as_slice()).ok(),
        _ => None,
    }
}

/// Decode a reflected constructor term list into a structural
/// [`RuntimeObservationValue::Term`], mirroring [`decode_rholang_bag`].
///
/// The reflected-term ABI (codegen `reflect_ground_term_par` / the RHS reflector)
/// is `EList[GPrivate("mettail.term.{fingerprint}.{label}"), children…]`. This
/// returns `None` unless the list's head is a private name whose tag carries the
/// shared [`crate::REFLECTED_TERM_ABI_PREFIX`]. Each child is decoded through the
/// same [`par_as_runtime_observation_value`] entry point, so a nested reflected
/// term (a σ argument that is itself a constructor) decodes recursively.
///
/// ★ CORRECTED (S1). This doc previously asserted that "a constructor label is a
/// dot-free identifier, so the FINAL `.` of the remainder separates fingerprint
/// from label", and the code split accordingly with `rsplit_once`. Both were
/// wrong, and they contradicted `native_contract::par_to_ground_term`, which
/// documented the opposite invariant and split at the FIRST `.`. Labels are NOT
/// dot-free: synthesized literal leaves bake the value into the label, so
/// `FloatLit(8.5)` is producible. Under `rsplit_once` that yielded
/// `fingerprint = "…:XXXX.FloatLit(8"`, `label = "5)"` — and because the
/// corrupted fingerprint then failed `is_ground_marker_par`, the marker was not
/// skipped and leaked into the decoded term as a phantom child. Silent, not an
/// error. The split now goes through the single shared inverse
/// [`mettail_rholang_codegen::parse_reflected_tag`], whose correctness rests on
/// the one invariant the writer asserts: the fingerprint is dot-free.
fn decode_reflected_term(list: &models::rhoapi::EList) -> Option<RuntimeObservationValue> {
    let (head, children) = list.ps.split_first()?;
    let tag = private_name_tag(head)?;
    let (fingerprint, label) = mettail_rholang_codegen::parse_reflected_tag(&tag)?;
    // E-2-D (reflected-ABI v2): a marked-object node carries the `^gnd`/`^nog` hereditary-ground
    // marker at index 1 — skip it so the DECODED term is byte-identical to the pre-D observation
    // (the marker is codegen metadata, never an observable child). A bare marker GPrivate never
    // occurs as a genuine child, so this claims only the marker.
    let children = match children.first() {
        Some(first) if mettail_rholang_codegen::is_ground_marker_par(first, fingerprint) => {
            &children[1..]
        },
        _ => children,
    };
    let children = children
        .iter()
        .map(par_as_runtime_observation_value)
        .collect::<Option<Vec<_>>>()?;
    Some(RuntimeObservationValue::Term { constructor: label.to_string(), children })
}

/// Pull one closed Rho ground value out of a `Par`.
///
/// This deliberately rejects arbitrary process bodies. Runtime observations are
/// public resting data values: scalars, unforgeable names, closed collection
/// bodies, and rholang's tagged bag ABI.
pub fn par_as_runtime_observation_value(par: &Par) -> Option<RuntimeObservationValue> {
    if let Some(value) = par_as_unforgeable_observation(par) {
        return Some(value);
    }

    // Stage AC2b: a bag-VALUED AC RHS lands on OUT as the bare process-soup carrier
    // (`@"ac:{op}"!(⟦e⟧) | …`) — the SAME shape a `HashBag` reflects to — not an `EList`. Decode
    // it to a multiset `Bag`. The `"ac:"` channel + sends-only shape are disjoint from every
    // `single_expr_instance` head below, so this claims only the AC carrier.
    if let Some(entries) = decode_ac_bag_soup(par) {
        return Some(RuntimeObservationValue::Bag(entries));
    }

    // A-S5.5 (AM-3): the EMPTY bag reflects as `Par::default()` (Nil) — the zero-send
    // degenerate of the process-soup carrier above (`decode_ac_bag_soup` requires ≥ 1
    // send, so Nil falls through to here). It decodes as the empty multiset `Bag`, which
    // is how a driven `op{}` — e.g. the redeclared Ambient `OutRule`'s singleton firing
    // `m[{n[{out(m,p)}]}] ⇒ {n[{p}], m[{}]}` — observes: `m[{}]`'s second child is Nil.
    // No other reflected value is the empty `Par`, so the claim is unambiguous.
    if par_is_empty_nil(par) {
        return Some(RuntimeObservationValue::Bag(Vec::new()));
    }

    match single_expr_instance(par)? {
        ExprInstance::GBool(value) => Some(RuntimeObservationValue::Bool(*value)),
        ExprInstance::GInt(value) => Some(RuntimeObservationValue::Int(*value)),
        ExprInstance::GString(value) => Some(RuntimeObservationValue::Text(value.clone())),
        ExprInstance::GUri(value) => Some(RuntimeObservationValue::Uri(value.clone())),
        ExprInstance::GByteArray(value) => Some(RuntimeObservationValue::Bytes(value.clone())),
        ExprInstance::GDouble(value) => Some(RuntimeObservationValue::DoubleBits(*value)),
        ExprInstance::GBigInt(value) => Some(RuntimeObservationValue::BigIntBytes(value.clone())),
        ExprInstance::GBigRat(value) => Some(RuntimeObservationValue::BigRationalBytes {
            numerator: value.numerator.clone(),
            denominator: value.denominator.clone(),
        }),
        ExprInstance::GFixedPoint(value) => Some(RuntimeObservationValue::FixedPointBytes {
            unscaled: value.unscaled.clone(),
            scale: value.scale,
        }),
        ExprInstance::EListBody(list) if list.remainder.is_none() && !list.connective_used => {
            // Try the reflected-term ABI first (head = a `mettail.term.` private
            // name), then the rholang bag ABI (head = the bag tag), else a plain
            // list. The three head shapes are disjoint, so ordering only decides
            // which decoder claims a match, never correctness.
            if let Some(term) = decode_reflected_term(list) {
                Some(term)
            } else if let Some(entries) = decode_rholang_bag(list) {
                Some(RuntimeObservationValue::Bag(entries))
            } else {
                Some(RuntimeObservationValue::List(decode_runtime_values(&list.ps)?))
            }
        },
        ExprInstance::ETupleBody(tuple) if !tuple.connective_used => {
            Some(RuntimeObservationValue::Tuple(decode_runtime_values(&tuple.ps)?))
        },
        ExprInstance::ESetBody(set) if set.remainder.is_none() && !set.connective_used => {
            let mut values = decode_runtime_values(&set.ps)?;
            values.sort();
            Some(RuntimeObservationValue::Set(values))
        },
        ExprInstance::EMapBody(map) if map.remainder.is_none() && !map.connective_used => {
            Some(RuntimeObservationValue::Map(decode_runtime_map(&map.kvs)?))
        },
        _ => None,
    }
}

// ══════════════════════════════════════════════════════════════════════════
// Rendering: `Par` → the short, stable text a diagnostic carries
// ══════════════════════════════════════════════════════════════════════════

/// The maximum rendered length, **in characters**, of a `Par` embedded in a diagnostic.
///
/// Chosen with headroom rather than tightness: Ω's reflected redex renders in 30 characters
/// and the largest normal form any pinned demo publishes (Church 6's body) in about 40, so 512
/// is an order of magnitude of slack while keeping a whole `failure` entry inside a kilobyte.
/// It is a named constant with its reasoning attached precisely so that widening it is a
/// deliberate edit by someone who has read this paragraph, not a silent drift.
pub const RENDER_BUDGET_CHARS: usize = 512;

/// Hex, lowercase, no separators — the spelling [`crate::speculation`]'s digests already use.
fn hex(bytes: &[u8]) -> String {
    let mut rendered = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        rendered.push_str(&format!("{byte:02x}"));
    }
    rendered
}

/// The de-Bruijn index a reflected Peano numeral carries (`^Z ⟼ 0`, `^S(n) ⟼ n + 1`).
fn peano_index(value: &RuntimeObservationValue) -> usize {
    match value {
        RuntimeObservationValue::Term { constructor, children }
            if constructor == PEANO_SUCC_REFLECT_LABEL =>
        {
            children.first().map(peano_index).unwrap_or(0) + 1
        },
        _ => 0,
    }
}

/// Render a decoded observation in the **machine's neutral notation**.
///
/// This is the entry point every datum-producing path uses. See the module header for why it
/// takes no presentation hook.
pub fn render_observation_text(value: &RuntimeObservationValue) -> String {
    render_observation_text_with(value, &render_observation_text)
}

/// [`render_observation_text`], with children routed through `child` so a **presentation**
/// layer can add guest-surface sugar and still inherit the reserved-label rendering below.
///
/// ★ Never call this from a path that produces a datum. See the module header.
pub fn render_observation_text_with(
    value: &RuntimeObservationValue,
    child: &dyn Fn(&RuntimeObservationValue) -> String,
) -> String {
    let RuntimeObservationValue::Term { constructor, children } = value else {
        // Every non-`Term` arm already has a deterministic, bounded `Display`.
        return value.to_string();
    };
    // The sugar below is confined to RESERVED reflected-ABI labels — `^`-prefixed, hence
    // unforgeable against any user constructor (which is a Rust `Ident`) — and to the exact
    // child arities the ABI emits. A reserved label with an unexpected arity, and every
    // reserved label without sugar (`^multilambda` among them, whose runtime child shape this
    // renderer does not claim to know), falls to the default arm: `Label(c₁, …, cₙ)`, which is
    // a complete and honest rendering, just an unsweetened one.
    match (constructor.as_str(), children.as_slice()) {
        (LAMBDA_REFLECT_LABEL, [body]) => format!("λ.{}", child(body)),
        (BOUND_VAR_REFLECT_LABEL, [index]) => peano_index(index).to_string(),
        (FREE_VAR_REFLECT_LABEL, [name]) => child(name),
        _ if children.is_empty() => constructor.clone(),
        _ => {
            let inner = children.iter().map(child).collect::<Vec<_>>().join(", ");
            format!("{constructor}({inner})")
        },
    }
}

/// Render an arbitrary resting `Par` as the short, stable text a diagnostic carries.
///
/// **Total, deterministic, bounded** — the three properties the module header argues for, one
/// arm each:
///
/// | input | image |
/// |---|---|
/// | decodes, and renders inside the budget | `⟦…⟧` |
/// | decodes, but renders over the budget | `⟦…⟧ (elided, N chars, blake2b256:…)` |
/// | does not decode | `⟨opaque Par, N bytes, blake2b256:…⟩` |
///
/// The third arm is a **digest**, not a fixed literal, deliberately. A literal would map every
/// undecodable `Par` to one string, so a consumer trying to tell two failed branches apart
/// could not — the same silence
/// [`ErrorCode::GuestEvaluatorRefused`](crate::speculation::search::ErrorCode::GuestEvaluatorRefused)
/// exists to prevent, reintroduced on exactly the inputs where a diagnostic matters most. It is
/// also not a *structural sketch*: of the three candidates, a sketch is the only one that can
/// be **wrong** — it can look like a term it is not. A digest and a byte count cannot.
pub fn render_par_text(par: &Par) -> String {
    let bytes = par.encode_to_vec();
    let Some(value) = par_as_runtime_observation_value(par) else {
        return format!(
            "⟨opaque Par, {} bytes, blake2b256:{}⟩",
            bytes.len(),
            hex(Blake2b256Hash::new(&bytes).bytes().as_slice()),
        );
    };
    let rendered = render_observation_text(&value);
    let count = rendered.chars().count();
    if count <= RENDER_BUDGET_CHARS {
        return format!("⟦{rendered}⟧");
    }
    // ★ Truncate on a CHARACTER boundary. These images contain `λ`, `⟦` and `…`, so a byte
    // index would split a code point and panic.
    let head: String = rendered.chars().take(RENDER_BUDGET_CHARS).collect();
    format!(
        "⟦{head}⟧ (elided, {count} chars, blake2b256:{})",
        hex(Blake2b256Hash::new(&bytes).bytes().as_slice()),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use models::rust::utils::{new_elist_par, new_gint_par, new_gstring_par, new_send_par};

    /// A reflected constructor node `EList[GPrivate("mettail.term.{fp}.{label}"), children…]`.
    fn reflected(label: &str, children: Vec<Par>) -> Par {
        let mut elements = Vec::with_capacity(children.len() + 1);
        elements.push(GPrivateBuilder::new_par_from_string(
            mettail_rholang_codegen::reflected_tag_string("test-fp", label),
        ));
        elements.extend(children);
        new_elist_par(elements, Vec::new(), false, None, Vec::new(), false)
    }

    /// The reflected de-Bruijn index `n` — `^bound(^S^n(^Z))`.
    fn bound(n: usize) -> Par {
        let mut peano = reflected(mettail_rholang_codegen::PEANO_ZERO_REFLECT_LABEL, Vec::new());
        for _ in 0..n {
            peano = reflected(PEANO_SUCC_REFLECT_LABEL, vec![peano]);
        }
        reflected(BOUND_VAR_REFLECT_LABEL, vec![peano])
    }

    /// Ω = `App(λ.App(0, 0), λ.App(0, 0))` — the divergent term the `[*]` demo drives.
    fn omega() -> Par {
        let self_app = reflected("App", vec![bound(0), bound(0)]);
        let lam = reflected(LAMBDA_REFLECT_LABEL, vec![self_app]);
        reflected("App", vec![lam.clone(), lam])
    }

    // ── totality ────────────────────────────────────────────────────────────────────────

    /// ★ Every `Par` has an image, including the ones the decoder refuses. A renderer with a
    /// precondition is a renderer that eventually gets a `{:?}` fallback bolted onto it.
    #[test]
    fn every_par_renders() {
        let opaque = new_send_par(
            new_gstring_par("c".to_string(), Vec::new(), false),
            vec![new_gint_par(1, Vec::new(), false)],
            false,
            Vec::new(),
            false,
            Vec::new(),
            false,
        );
        for (label, par) in [
            ("nil", Par::default()),
            ("scalar", new_gint_par(7, Vec::new(), false)),
            ("text", new_gstring_par("hi".to_string(), Vec::new(), false)),
            ("reflected", omega()),
            ("opaque process", opaque),
            (
                "nested list",
                new_elist_par(
                    vec![new_elist_par(
                        vec![new_elist_par(
                            vec![new_gint_par(1, Vec::new(), false)],
                            Vec::new(),
                            false,
                            None,
                            Vec::new(),
                            false,
                        )],
                        Vec::new(),
                        false,
                        None,
                        Vec::new(),
                        false,
                    )],
                    Vec::new(),
                    false,
                    None,
                    Vec::new(),
                    false,
                ),
            ),
        ] {
            let rendered = render_par_text(&par);
            assert!(!rendered.is_empty(), "{label} must render to something");
        }
    }

    // ── the reserved-label sugar ────────────────────────────────────────────────────────

    /// The neutral notation of Ω — reserved ABI labels sugared, the user constructor `App`
    /// rendered structurally. This exact string is what a `^spec-failure` message carries.
    #[test]
    fn omega_renders_in_the_neutral_notation() {
        assert_eq!(render_par_text(&omega()), "⟦App(λ.App(0, 0), λ.App(0, 0))⟧");
    }

    /// A reserved label the renderer does not sugar still renders — as itself, with its
    /// children — rather than falling through to a dump.
    #[test]
    fn an_unsugared_reserved_label_renders_structurally() {
        let node = reflected(
            mettail_rholang_codegen::MULTILAMBDA_REFLECT_LABEL,
            vec![bound(0), bound(1), reflected("App", vec![bound(0), bound(1)])],
        );
        assert_eq!(render_par_text(&node), "⟦^multilambda(0, 1, App(0, 1))⟧");
    }

    // ── boundedness ─────────────────────────────────────────────────────────────────────

    /// ★ THE CLASS ASSERTION. A `Par` whose rendering exceeds the budget is elided, so no
    /// input — however large, however adversarial — can put an unbounded string into a datum.
    #[test]
    fn an_oversized_rendering_is_elided_within_the_budget() {
        // A left-nested application spine, deep enough that its rendering exceeds the budget.
        let mut deep = bound(0);
        for _ in 0..RENDER_BUDGET_CHARS {
            deep = reflected("App", vec![deep, bound(0)]);
        }
        let rendered = render_par_text(&deep);
        assert!(
            rendered.contains("(elided,"),
            "an over-budget rendering must say so: {rendered}"
        );
        assert!(
            rendered.chars().count() <= RENDER_BUDGET_CHARS + 128,
            "the elided image must stay within the budget plus its marker, got {} chars",
            rendered.chars().count()
        );
    }

    /// Truncation lands on a CHARACTER boundary — a byte index would panic here, because the
    /// budget'th character of this rendering is the multi-byte `λ`.
    #[test]
    fn truncation_respects_character_boundaries() {
        let mut deep = bound(0);
        for _ in 0..RENDER_BUDGET_CHARS {
            deep = reflected(LAMBDA_REFLECT_LABEL, vec![deep]);
        }
        let rendered = render_par_text(&deep);
        assert!(rendered.contains('λ'), "the head must survive intact: {rendered}");
        assert!(rendered.contains("(elided,"));
    }

    // ── determinism ─────────────────────────────────────────────────────────────────────

    /// The image is a function of the `Par` alone: same input, same bytes, every time.
    #[test]
    fn the_rendering_is_stable_across_calls() {
        let par = omega();
        let first = render_par_text(&par);
        for _ in 0..100 {
            assert_eq!(render_par_text(&par), first);
        }
    }

    /// Two `Par`s that differ only in the INSERTION ORDER of a set render identically — the
    /// decoder sorts, so no host-side iteration order reaches the rendered bytes.
    #[test]
    fn set_insertion_order_does_not_reach_the_rendering() {
        let elements = |a: i64, b: i64| {
            models::rust::utils::new_eset_par(
                vec![new_gint_par(a, Vec::new(), false), new_gint_par(b, Vec::new(), false)],
                Vec::new(),
                false,
                None,
                Vec::new(),
                false,
            )
        };
        assert_eq!(render_par_text(&elements(1, 2)), render_par_text(&elements(2, 1)));
    }

    // ── the opaque arm ──────────────────────────────────────────────────────────────────

    /// The undecodable arm carries the digest of the `Par`'s own protobuf bytes, so two
    /// different opaque processes stay distinguishable.
    #[test]
    fn the_opaque_arm_is_the_digest_of_the_encoded_par() {
        let opaque = |datum: i64| {
            new_send_par(
                new_gstring_par("c".to_string(), Vec::new(), false),
                vec![new_gint_par(datum, Vec::new(), false)],
                false,
                Vec::new(),
                false,
                Vec::new(),
                false,
            )
        };
        let par = opaque(1);
        let bytes = par.encode_to_vec();
        assert_eq!(
            render_par_text(&par),
            format!(
                "⟨opaque Par, {} bytes, blake2b256:{}⟩",
                bytes.len(),
                hex(Blake2b256Hash::new(&bytes).bytes().as_slice()),
            )
        );
        assert_ne!(
            render_par_text(&opaque(1)),
            render_par_text(&opaque(2)),
            "★ two different opaque Pars must not collapse to one string"
        );
    }

    // ── anti-regression ─────────────────────────────────────────────────────────────────

    /// ★ THE CELL THAT WOULD HAVE CAUGHT THE ORIGINAL DEFECT. No rendering, of any input,
    /// may contain a prost field name — that is the signature of a derived `Debug` dump.
    #[test]
    fn no_rendering_leaks_a_prost_debug_dump() {
        let opaque = new_send_par(
            new_gstring_par("c".to_string(), Vec::new(), false),
            vec![new_gint_par(1, Vec::new(), false)],
            false,
            Vec::new(),
            false,
            Vec::new(),
            false,
        );
        for par in [Par::default(), omega(), opaque] {
            let rendered = render_par_text(&par);
            for marker in
                ["expr_instance", "EListBody", "unforgeables", "connective_used", "locally_free"]
            {
                assert!(
                    !rendered.contains(marker),
                    "★ {marker:?} in a rendering means a prost Debug dump got in: {rendered}"
                );
            }
        }
    }
}
