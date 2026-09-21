//! Shared binder rule descriptors used by WPDA classification and generation.
//!
//! Nested position and action forests retain their explicit-worklist lifecycle
//! operations. Moving the descriptors does not change their ordering, payloads,
//! or stack-safe clone, formatting, and destruction implementations.

use mettail_ast::types::CollectionType;

/// Classification of a multi-step rule.
#[derive(Debug, Clone)]
pub struct BinderShape {
    /// Constructor label (e.g., `"Lam"`, `"Fraction"`, `"PNew"`).
    pub label: String,
    /// Result category name (e.g., `"Term"`, `"BigRat"`, `"Proc"`).
    pub result_cat: String,
    /// Category parsed by a leading nonterminal parameter, when the syntax
    /// begins with `Param` rather than a consumed terminal trigger. The prefix
    /// dispatcher descends into this category without consuming input, then
    /// resumes this rule at position 1.
    pub leading_category: Option<String>,
    /// A leading inert `name@Ident` capture. Prefix dispatch consumes it
    /// through the token-family capture path without opening binder scope.
    pub leading_ident_capture: Option<String>,
    /// Per-position dispatch entries (excluding position 0 which is the
    /// trigger consumed at PrefixDispatch open arm).
    pub positions: Vec<BinderPosition>,
    /// Whether the rule uses a multi-binder list (^[xs]).
    pub is_multi: bool,
    /// Whether the rule has any binder slot at all (for action body shape).
    pub has_binder: bool,
    /// Action arity (number of args the action consumes).
    pub action_arity: u8,
    /// Action body: per-arg, what kind of arg it is (Ident binder name,
    /// Term sub-parse, Predicate, BinderListNames). Used to construct the
    /// Cat::Label(...) expression.
    pub action_args: Vec<ActionArgKind>,
    /// Body category (for single-binder rules — None for non-binder).
    pub body_cat: Option<String>,
    /// Param categories in declaration order (for non-binder Simple params).
    // dead_code: populated by production codegen but only read by the `#[cfg(test)]` shape assertions.
    #[cfg_attr(not(test), allow(dead_code))]
    pub param_cats: Vec<String>,
}

/// A single position in a multi-step rule's syntax pattern.
pub enum BinderPosition {
    /// `Literal("text")` — consume + advance position.
    Literal(String),
    /// L9-3: `w@Word` — consume ONE token of the custom KIND `kind_name`
    /// (a single-branch Fork carrying `GuardedConsumeTokenKindAndReplace`,
    /// structural clone of the `Literal` position), binding its text as the
    /// `param_name` action arg (`ActionArgKind::TokenText`). No binder scope.
    TokenKindCapture { kind_name: String, param_name: String },
    /// An `m:Ident` param — consume ONE builtin `Token::Ident` and bind its TEXT as the
    /// `param_name` action arg ([`ActionArgKind::IdentText`]). No binder scope, no new
    /// token kind, no lexical co-accept.
    ///
    /// Emits the EXISTING walker op `ForkActionKind::ConsumeIdentAndReplace {
    /// start_scope: false }` (`prattail/src/wpda_walker.rs:2612`), which interns the token
    /// as an `ActionArg::Ident`; the action body reads it back through the existing
    /// `ActionArg::as_ident()` (`prattail/src/wpda_runtime.rs:2821`). Because both halves
    /// already existed, giving `Ident` a mid-rule surface required ZERO prattail change.
    ///
    /// Structural twin of [`Self::TokenKindCapture`], and deliberately NOT
    /// [`Self::BinderIdent`]: a binder ident opens a scope, which is precisely the
    /// semantics an inert identifier field must not have.
    IdentTextCapture { param_name: String },
    /// L9-4: `*flt(node, open, close)` — consume a whole guest region (opener →
    /// GuestChunk/Hole run → closer) in one action (`ConsumeGuestBodyAndReplace`
    /// mid-rule / `ConsumeGuestBodyAndPush` leading), binding the assembled
    /// `Arc<FltNode>` as the `param_name` action arg (`ActionArgKind::GuestBody`).
    GuestBodyCapture {
        open_kind: String,
        nested_open_kinds: Vec<String>,
        close_kind: String,
        param_name: String,
    },
    /// `Param(binder_name)` — capture single Ident, start_binder_scope,
    /// advance position.
    BinderIdent,
    /// `Op(Sep { collection: xs, separator })` — for ^[xs] multi-binder
    /// list. Engine enters BinderListLoop sub-state, captures Idents
    /// separated by `separator`, until close delim of position N+1 (the
    /// next Literal in the syntax pattern).
    ///
    /// B8 / Class 3 ZIP-MAP-SEP (2026-05-08): extended fields support the
    /// chained `Sep{source: Some(Map{source: Zip})}` pattern (e.g.
    /// rholang PInputs `*zip(ns,xs).*map(|n,x| n "?" x).*sep(",")`).
    /// `inner_positions` is the per-iteration inner walk; for PNew-style
    /// rules it's `[BinderIdent]`.
    /// `collection_param_cat` is `Some(elem_cat)` for Class 3 (the
    /// synthesized Names accumulator's element category) and None for
    /// PNew-style rules (no synthesized accumulator).
    BinderListLoop {
        separator: String,
        close: String,
        /// Per-iteration inner walk. PNew → `[BinderIdent]`. Class 3 →
        /// the body of the Map closure (e.g. `[ParamParse{Name,
        /// collection:Some(...)}, Literal("?"), BinderIdent]`).
        inner_positions: Vec<BinderPosition>,
        /// For Class 3 rules: the element category of the synthesized
        /// names accumulator. None for PNew-style rules.
        collection_param_cat: Option<String>,
        /// Phase 3 Redesign B (2026-05-11): whether empty-binder-list is
        /// permitted at parse time. `true` for multi-binder PNew-style
        /// rules (`^[xs].body` — zero or more idents are valid) and
        /// Class 3 (the collection itself may be empty). `false` for
        /// single-binder collapsed shapes (`^x.body` — exactly one
        /// ident required).
        ///
        /// Default for existing construction sites: `true` (preserves
        /// pre-Phase-3 behavior). Single-binder collapse (sub-commit
        /// 3.B.3) will construct with `false`.
        allow_empty: bool,
        /// Phase 3 Redesign B (2026-05-11): whether more-than-one ident
        /// is permitted. `true` for multi-binder and Class 3. `false`
        /// for single-binder collapsed shapes (exactly one ident).
        ///
        /// Default: `true`. Single-binder collapse will construct with
        /// `false`.
        allow_multi: bool,
        /// Phase 4 #2 (2026-05-12): rule-global collection-slot index
        /// for the synthesized names accumulator (Class-3 ZIP-MAP-SEP
        /// only — `collection_param_cat: Some(_)`). Encoded at the
        /// CollectionMarker symbol's `bp` field at push time so the
        /// walker's per-(src, rule, slot_idx) lookup
        /// `is_class3_collection_per_slot` correctly distinguishes the
        /// Class-3 slot from sibling Class-2 slots in the same rule
        /// (e.g. PInputsTagged: ns:Vec(Name) — slot 0 (Class-3) +
        /// tags:Vec(Proc) — slot 1 (Class-2)).
        ///
        /// For non-Class-3 BinderListLoop variants (PNew-style and
        /// single-binder collapse): `slot_idx == 0` and the field is
        /// informational only — no names accumulator is allocated, no
        /// CollectionMarker carries this slot_idx.
        slot_idx: u8,
    },
    /// `Param(name)` — sub-parse the param's category. After the parse
    /// returns, the marker advances to the next position. When the marker
    /// reaches `positions.len() + 1`, the rule's RuleAt symbol pops in
    /// Unwinding and the action fires (no separate `is_final` flag needed
    /// — it's encoded by position arithmetic).
    ///
    /// B9 / Class 2 (2026-05-08): when the param is `Sep`-driven over a
    /// SimpleCollection (e.g. `Vec(Proc).*sep("|") ")"`), `collection`
    /// is `Some(...)`. The dispatch arm pushes a CollectionMarker onto
    /// the GSS, transitioning to PrefixDispatch where the existing
    /// CollectionLoop apparatus parses elements separated by `separator`
    /// until `close`. On close, the marker pops — but the FireAction is
    /// suppressed (binder-internal collection); the binder rule's
    /// terminal action drains the CollectionId via `CollectionDrain`.
    ParamParse {
        cat: String,
        collection: Option<CollectionSepInfo>,
    },
    /// `Param(guard)` for `?guard:Guard` — parse predicate inline via
    /// `parse_predicate_from_tokens`. Advance position.
    GuardSlot,
    /// Opt-Group (2026-04-29): `Op(Opt { inner })` — recursive
    /// optional-group lowering. The engine transitions into
    /// `WpdaState::OptionalGroup { sub_pos: 0 }`; on entry it peeks
    /// the FIRST-set of `inner_positions[0]` to decide whether to take
    /// the group (push inner args + advance into group) or skip (push
    /// `ActionArg::Optional(None)` + advance past group). The
    /// `first_token_set` is a list of literal-text predicates that
    /// trigger entry into the group (computed at codegen from the
    /// inner positions' types).
    OptionalGroup {
        positions: Vec<BinderPosition>,
        /// Dense preorder identity of this group in the rule's recursive
        /// position forest. It remains unique across nested groups.
        group_idx: u32,
        /// Tokens that, when peeked at group entry, indicate the group
        /// should be taken. Strings are the literal text from the first
        /// inner Literal; if the first inner is a ParamParse the
        /// FIRST-set is computed from the param's category.
        first_token_set: Vec<String>,
    },
}

/// B9 / Class 2 (2026-05-08): separator + close + container-kind info
/// for a `ParamParse` slot whose source is a `Sep`-driven collection.
/// Mirrors `CollectionShape` (collection.rs) but lives on the binder
/// position because the slot is INSIDE a multi-position binder rule
/// rather than the rule itself BEING a collection rule.
#[derive(Debug, Clone)]
pub struct CollectionSepInfo {
    pub separator: String,
    pub close: String,
    pub elem_cat: String,
    /// Phase 4 #5b (2026-05-12): inter-pair separator for HashMap
    /// collections (e.g., `":"` for `k: v`). `None` for Vec/HashBag/
    /// HashSet. The walker's `CollectionLoop` uses this to dispatch
    /// key/value parsing phases while preserving the drained
    /// `[k0, v0, k1, v1, ...]` invariant.
    pub key_val_separator: Option<String>,
    /// Phase 4 #1 (2026-05-11): rule-global slot index. 0-based dense
    /// index over collection slots in `shape.positions` order. Encoded
    /// at the `CollectionMarker` symbol's `bp` field at push time so
    /// the walker's per-CollectionMarker close/sep/element-src
    /// lookups can disambiguate sibling slots within the same rule.
    /// `accumulator_id` (runtime stack-relative slot id) is recovered
    /// from `cursor.collection_stack.len() - 1` at push time. For
    /// single-slot rules, `slot_idx == 0` and behavior is unchanged
    /// (the slot_idx vs accumulator_id coincide).
    pub slot_idx: u8,
}

/// What kind of arg the action body extracts at each position (in push order).
pub enum ActionArgKind {
    /// `ActionArg::Ident { name }` — single binder name.
    BinderName,
    /// L9-3: `ActionArg::Token { text, .. }` — a captured custom-kind token's
    /// text, extracted via `as_token_text()` (the proven native-literal path)
    /// and bound as a `String` action arg / AST field.
    TokenText { param_name: String },
    /// `ActionArg::Ident { name }` — the TEXT of one consumed builtin `Token::Ident`,
    /// extracted via `as_ident()` and bound as a `String` action arg / AST field.
    ///
    /// The builtin-kind twin of [`Self::TokenText`]: same `String` destination, different
    /// source token class. `TokenText` reads a DECLARED `tokens { }` kind
    /// (`ActionArg::Token`, pushed by `GuardedConsumeTokenKindAndReplace`); this reads the
    /// generic `Ident` (`ActionArg::Ident`, pushed by `ConsumeIdentAndReplace`). Keeping
    /// them distinct is what lets an `Ident`-typed param avoid declaring a new token kind
    /// — measured to move Rholang's multi-accept DFA states 0.8 % → 79.8 % and parse time
    /// geomean ×2.49 — while still landing an inert `String` in the AST.
    IdentText { param_name: String },
    /// L9-4: `ActionArg::GuestBody(GuestBodyData)` — an assembled FLT guest
    /// body, extracted via `as_guest_body()` and lowered to an
    /// `Arc<mettail_runtime::FltNode>` action arg / AST field.
    GuestBody {
        param_name: String,
        kind: mettail_ast::grammar::DelimitedRegionKind,
    },
    /// `ActionArg::Term { value, .. }` of a specific category.
    Term(String),
    /// `ActionArg::Predicate` — parsed predicate.
    Predicate,
    /// Multi-binder list: a `BinderHandle` pushed by the binder-list-loop
    /// finalize step. Action body wraps as `Scope<Vec<Binder>, ...>`.
    BinderList,
    /// Opt-Group: a captured optional group's inner action args.
    /// `inner` mirrors the inner positions' action_args layout. At
    /// runtime the action body extracts `ActionArg::Optional(Option<
    /// Vec<ActionArg>>)` and produces `Some(...)` / `None` for each
    /// `Option<T>` field of the AST variant in inner-args order.
    Optional(Vec<ActionArgKind>),
    /// B9 / Class 2 (2026-05-08): a CollectionId arg pushed by the
    /// CollectionMarker push helper. The action body calls
    /// `b.drain_collection(id)` to materialize the elements into the
    /// container type per `coll_kind`. Mirrors the body of
    /// `emit_collection_action_entry::action_fn` but for a SLOT inside
    /// a multi-position binder rule.
    CollectionDrain {
        elem_cat: String,
        coll_kind: CollectionType,
    },
}

mod model_lifecycle;

pub mod optional;
pub mod term_param;

/// Parameter roles observed by the binder classifier in declaration order.
pub enum ParamKind {
    Simple {
        cat: String,
    },
    Binder,
    BinderList,
    Body {
        cat: String,
    },
    Guard,
    /// A `Simple` parameter whose value is collected by a `Sep` syntax
    /// operator inside a larger binder rule.
    SimpleCollection {
        elem_cat: String,
        coll_kind: CollectionType,
    },
}
