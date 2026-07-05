//! Binding power analysis and table generation.
//!
//! Analyzes grammar rules to identify infix operators and assigns binding power
//! pairs for Pratt parsing. Binding power pairs `(left_bp, right_bp)` control
//! precedence and associativity:
//! - Left-associative: `left_bp < right_bp` (e.g., `(2, 3)` for `+`)
//! - Right-associative: `left_bp > right_bp` (e.g., `(7, 6)` for `^`)

use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use crate::automata::codegen::terminal_to_variant_name;

/// Associativity of an infix operator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Associativity {
    Left,
    Right,
}

/// H3 chain-absorption descriptor for ONE canonical iterative-eligible
/// operator. Emitted as a `const` literal by `iter_eligible_<cat>` (codegen,
/// `infix.rs`) and consumed by the walker's `IterativeChainAbsorb` arm +
/// the InfixLoop pre-fork trigger (`engine_impl.rs`). Carries everything the
/// direct SPPF synthesizer needs so it can build the absorbed chain's forest
/// without a grammar lookup at parse time. See
/// `prattail/docs/design/plans/c1-right-assoc-ternary-h3-absorption.md` (§3.5).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IterAbsorbSpec {
    /// Operator left binding power.
    pub left_bp: u8,
    /// Operator right binding power.
    pub right_bp: u8,
    /// `left_bp > right_bp` — right-associative binary. Always `false` for
    /// mixfix (mixfix associativity is structural, see `is_mixfix`).
    pub assoc_right: bool,
    /// This operator is a (ternary-shaped, right-recursive) mixfix.
    pub is_mixfix: bool,
    /// Result-category source index of the operator (the packing's category;
    /// the global packing rule id is `(op_cat_src_idx << 16) | op_rule_idx`).
    pub op_cat_src_idx: u16,
    /// Local rule index of the operator within its result category.
    pub op_rule_idx: u16,
    /// Operand (atom) category source index (== `op_cat_src_idx` for the
    /// same-category chains C1 targets).
    pub atom_cat_src_idx: u16,
    /// Local rule index of the operand category's literal-injection rule
    /// (`NumLit` = `per_cat[atom_cat][0]`), used to synthesize each atom leaf.
    pub atom_lit_rule_idx: u16,
    /// Mixfix trigger terminal (`"?"`); `""` for binary operators. Stored as
    /// the terminal STRING (not a precomputed tag) because `token_kind_to_tag`
    /// is a runtime FxHash over the exact `TokenKind` the lexer emits — the
    /// peek compares against the live token at parse time instead.
    pub trigger: &'static str,
    /// Mixfix inner separator (`":"`); `""` for binary operators.
    pub sep: &'static str,
}

/// An infix operator with its binding power.
#[derive(Debug, Clone)]
pub struct InfixOperator {
    /// The terminal text of the operator (e.g., "+", "*", "==").
    /// For mixfix operators, this is the trigger terminal (e.g., "?" for ternary).
    pub terminal: String,
    /// The category this operator applies to (e.g., "Proc", "Int").
    pub category: String,
    /// The result category (usually same as `category` for same-type infix,
    /// but different for cross-category like `Int == Int -> Bool`).
    pub result_category: String,
    /// Left binding power.
    pub left_bp: u8,
    /// Right binding power.
    pub right_bp: u8,
    /// The constructor label for this operator (e.g., "Add", "PPar").
    pub label: String,
    /// Whether this is a cross-category operator (operands from one category,
    /// result in another).
    pub is_cross_category: bool,
    /// Whether this is a postfix operator (e.g., a!, a?, a++).
    /// Postfix operators have left_bp but no right recursive call.
    pub is_postfix: bool,
    /// Whether this is a mixfix operator (e.g., a ? b : c, with 3+ operands).
    /// Mixfix operators parse middle operands at min_bp=0 (reset like grouping)
    /// and the final operand at right_bp.
    pub is_mixfix: bool,
    /// Parts of a mixfix operator: the operand-separator pairs after the trigger.
    /// Empty for regular infix/postfix.
    pub mixfix_parts: Vec<MixfixPart>,
    /// GEN-1 B-1 (Stage S2): for a 0-operand ("nullary") mixfix rule — one
    /// whose only Simple param is the LHS and whose pattern is
    /// `LHS trigger lit lit …` with NO inner operand (e.g. POutputEmpty
    /// `n "!" "(" ")"`, or a zero-arg method `.size()`) — this carries the
    /// literal sequence consumed AFTER the trigger (`["(", ")"]`). `mixfix_parts`
    /// is empty for such a rule; the walker consumes `nullary_literals` then
    /// pops the marker and fires the LHS-only (arity-1) action. Empty for all
    /// other operators.
    pub nullary_literals: Vec<String>,
}

/// A part of a mixfix operator after the trigger terminal.
///
/// Each part describes an operand to parse, with literal sequences that
/// must be consumed before and after the operand sub-parse.
///
/// L12 follow-up B6 (2026-05-07): widened from
/// `following_terminal: Option<String>` to vectors so postfix-mixfix
/// rules with consecutive literals between operands (e.g. POutput's
/// `n "!" "(" q ")"`) can be expressed without classifier dead zones.
/// The previous `Option<String>` is the degenerate `Vec` of length 0
/// or 1 — existing classic mixfix rules (Tern's `a "?" b ":" c`)
/// produce single-element preceding/following vectors.
///
/// Example: `a "?" b ":" c` has parts:
/// - MixfixPart {
///     operand_category: "Int", param_name: "b",
///     preceding_terminals: vec![],  following_terminals: vec![":"]
///   }
/// - MixfixPart {
///     operand_category: "Int", param_name: "c",
///     preceding_terminals: vec![],  following_terminals: vec![]
///   }
///
/// Example: POutput `n "!" "(" q ")"` (Class 1 MIXFIX-LHS-PARAM) has parts:
/// - MixfixPart {
///     operand_category: "Proc", param_name: "q",
///     preceding_terminals: vec!["("], following_terminals: vec![")"]
///   }
#[derive(Debug, Clone)]
pub struct MixfixPart {
    /// Category of the operand to parse.
    pub operand_category: String,
    /// Parameter name (for AST construction).
    pub param_name: String,
    /// Literals that MUST be consumed BEFORE the operand sub-parse
    /// begins. Empty for traditional mixfix where the trigger absorbs
    /// the first literal; non-empty for postfix-mixfix shapes like
    /// POutput where the trigger `!` is followed by `(` BEFORE the
    /// operand.
    pub preceding_terminals: Vec<String>,
    /// Literals that MUST be consumed AFTER the operand sub-parse
    /// returns. For traditional mixfix the per-part separator (e.g.
    /// `:` between `b` and `c`) appears here as a single-element
    /// vector; for trailing closers like `)` the last part carries
    /// multi-element vectors.
    pub following_terminals: Vec<String>,
    /// GEN-1 B-3 (Stage S2/S3): when `Some`, this part is a REPETITION
    /// operand `xs.*sep(s)` — a zero-or-more list of `operand_category`
    /// elements separated by `repetition.separator`, terminated by
    /// `repetition.close`. The walker drives it through the existing
    /// `CollectionLoop` machinery (S3); the drained `Vec<elem>` is
    /// delivered to the rule action as an `ActionArg::CollectionId`.
    /// `None` for ordinary single-operand parts.
    pub repetition: Option<MixfixRep>,
}

/// GEN-1 B-3 (Stage S2/S3): the descriptor for a mixfix repetition operand
/// produced by `xs.*sep(s)` in a Param-prefixed (infix/mixfix-classified)
/// rule, e.g. POutput2Plus `n "!" "(" a "," bs.*sep(",") ")"`.
///
/// The repetition accumulates zero-or-more elements of the enclosing
/// `MixfixPart.operand_category` separated by `separator`. The repetition is
/// terminated by `close` — the literal(s) that follow the `*sep` in the
/// grammar pattern (e.g. `")"` for POutput2Plus, `"<-"` for the polyadic
/// bind, `"where"` for the where-guarded for-row, or `[]` for the open-ended
/// `&`-join `ForRowNoWhere` where the loop stops when the next token is not
/// the separator). The CLOSE belongs to the repetition (the loop owns it),
/// NOT to `following_terminals`, so the per-element loop can decide when to
/// finalize without colliding with the surrounding mixfix literal run.
#[derive(Debug, Clone)]
pub struct MixfixRep {
    /// Element separator (e.g. `","` for sends, `"&"` for joins).
    pub separator: String,
    /// Minimum element count. Always `0` for `*sep` (Kleene star); the
    /// required leading operand (e.g. POutput2Plus's `a`) is a SEPARATE
    /// normal `MixfixPart` that precedes this repetition part.
    pub min: u8,
    /// Literal(s) that terminate (and are consumed by) the repetition. Empty
    /// for open-ended repetitions whose terminator is "next token is not the
    /// separator" (e.g. `ForRowNoWhere`). At most one token in every shipped
    /// rule; modeled as a `Vec` for generality.
    pub close: Vec<String>,
}

impl InfixOperator {
    /// Returns the associativity of this operator.
    pub fn associativity(&self) -> Associativity {
        if self.left_bp < self.right_bp {
            Associativity::Left
        } else {
            Associativity::Right
        }
    }

    /// True iff this mixfix operator right-recurses through its LAST operand
    /// (the `else` slot of a `c "?" t ":" e`-shaped ternary): its final
    /// `MixfixPart.operand_category` equals its `result_category`, and the
    /// operator's own `category` equals `result_category`.
    ///
    /// Needed because mixfix associativity is hard-coded `Left` at
    /// classification (the `step right` annotation does NOT reach
    /// `associativity()` for the mixfix path), so right-recursion must be
    /// detected structurally rather than via binding powers. See the C1 plan
    /// (V5).
    pub fn right_recursive_tail(&self) -> bool {
        self.is_mixfix
            && self.category == self.result_category
            && self
                .mixfix_parts
                .last()
                .map_or(false, |p| p.operand_category == self.result_category)
    }

    /// Phase F.13 chain_10000 Exp 6 (Plan A first substage, 2026-05-26):
    /// `true` iff this operator can be parsed by a single per-chain
    /// `WpdaState::InfixChainIterative` GSS RuleAt push followed by
    /// repeated RHS sub-parses at `right_bp`, instead of one Return
    /// RuleAt push per `+` (today's `ConsumeAndPush` per token).
    ///
    /// Conservative gate (all must hold):
    ///   1. `!self.is_cross_category` — same-category result. Cross-
    ///      cat dispatch has separate semantics that the iterative
    ///      shape doesn't preserve.
    ///   2. `!self.is_postfix` — postfix has no RHS chain.
    ///   3. `!self.is_mixfix` — mixfix has inner-operand state the
    ///      iterative shape doesn't model.
    ///   4. `self.left_bp < self.right_bp` — left-associative. The
    ///      Plan A first substage scope. Right-assoc analog is
    ///      symmetric but deferred to a later substage.
    ///
    /// Category/rule uniqueness at the `(terminal, l_bp >= outer_bp)`
    /// pair (Plan A invariant I1, singleton InfixLoop dispatch) is
    /// NOT checked here — it requires a `BindingPowerTable` scan and
    /// belongs in the codegen emit site (`emit_iter_eligible_fn` in
    /// `macros/src/gen/runtime/wpda_codegen/infix.rs`, Substage 6b).
    ///
    /// This predicate is the STRUCTURAL filter only — it admits any binary
    /// directional infix op (left- or right-assoc) and any same-category
    /// right-recursive ternary-shaped mixfix. It does NOT decide which op
    /// actually absorbs; two cross-cutting filters guard correctness:
    ///
    /// - **D1 (cross-category fanout) → canonical-op-per-terminal** is
    ///   enforced at the codegen emit site (`BindingPowerTable::
    ///   is_canonical_iter_op` in `emit_iter_eligible_fn`,
    ///   `macros/.../wpda_codegen/infix.rs`). Numeric terminals like `+`
    ///   are shared across categories (Int `AddInt`, BigInt `AddBigInt`,
    ///   …); a bare literal is ambiguous across them. H3 absorption jumps
    ///   the cursor to `chain_end`+Unwinding, BYPASSING the Tomita merge
    ///   that reconciles category ambiguity, so if MORE than one category
    ///   absorbed the same chain the divergent cursors would never
    ///   converge ("no accepting branch reached end of input"). The
    ///   canonical filter admits exactly ONE category per terminal (lowest
    ///   `category_src_idx`); the rest stay on the convergent normal
    ///   walker — exactly why the original AddInt-only pilot was safe.
    ///   (WALK-S1.5 confirmed this on a clean build + tracing; it is NOT
    ///   an incremental-build artifact.)
    /// - **D2 (right-assoc / mixfix never iterate to the singleton)** is
    ///   handled by a NEW pre-fork absorption trigger in `engine_impl.rs`
    ///   (right-assoc `^` recurses via the RHS sub-parse and ternary `?`
    ///   enters the mixfix tier; neither reaches the left-assoc InfixLoop
    ///   singleton). Left-assoc `AddInt` keeps the existing singleton path.
    ///
    /// See `prattail/docs/design/plans/c1-right-assoc-ternary-h3-absorption.md`.
    pub fn is_iterative_candidate(&self) -> bool {
        // Binary infix, left- OR right-associative (distinct binding powers
        // = a genuinely directional operator; `==` would be ambiguous and is
        // excluded).
        let binary = !self.is_mixfix && self.left_bp != self.right_bp;
        // OR a same-category right-recursive ternary-shaped mixfix: exactly
        // two parts (three operands incl. the LHS), no preceding terminals,
        // exactly one separator per inner part, an empty trailing terminal
        // set, and right-recursion through the last operand. This admits
        // `Tern` (c "?" t ":" e) while excluding postfix-mixfix shapes
        // (POutput's `n "!" "(" q ")"`, non-empty preceding/following).
        let ternary_mixfix = self.is_mixfix
            && self.mixfix_parts.len() == 2
            && self
                .mixfix_parts
                .iter()
                .all(|p| p.preceding_terminals.is_empty())
            && self
                .mixfix_parts
                .last()
                .map_or(false, |p| p.following_terminals.is_empty())
            && self
                .mixfix_parts
                .iter()
                .rev()
                .skip(1)
                .all(|p| p.following_terminals.len() == 1)
            && self.right_recursive_tail();
        !self.is_cross_category && !self.is_postfix && (binary || ternary_mixfix)
    }
}

/// A binding power table for a language.
#[derive(Debug, Clone)]
pub struct BindingPowerTable {
    /// All infix operators, grouped by result category.
    pub operators: Vec<InfixOperator>,
}

impl BindingPowerTable {
    /// Create a new empty binding power table.
    pub fn new() -> Self {
        BindingPowerTable { operators: Vec::new() }
    }

    /// D1 (canonical-op-per-terminal): among every iterative-candidate
    /// operator sharing `op`'s terminal, is `op` THE canonical one — i.e. the
    /// one whose result category is the runtime lex-min WINNER for a chain
    /// over that terminal? The winner minimizes, smallest-first:
    ///   1. `value_home_rank(cat)`: 0 if `cat` parses this terminal's operand
    ///      token via a tier-0.0 polymorphic literal home prefix arm (today:
    ///      integer-home categories — `NativeType::is_integer()`, incl.
    ///      `CanonicalBigInt`), else 1. Mirrors `LexicographicWeight`'s
    ///      primary key: a literal-home cursor parses the operand at tier 0.0,
    ///      a cross-cat-projected cursor at >= BP_TIER_CROSSCAT_PROJECTION
    ///      (0.025). This is why bare-integer chains converge on Int even when
    ///      a non-integer-home category (e.g. BigRat, which reaches a bare
    ///      integer only via a cross-cat projection) has a lower
    ///      `category_src_idx`.
    ///   2. `cat_src_idx(cat)`: the category source index — the lex-min
    ///      tiebreak after primary/lex_alt, among equal-rank cursors.
    ///   3. the operator's label: a deterministic total order; cannot tie
    ///      across distinct categories sharing one terminal.
    ///
    /// Selecting the lex-min winner guarantees exactly ONE category absorbs a
    /// given terminal's chains AND that it is the SAME category the convergent
    /// normal walker selects at EOI — so the absorbed parse equals the
    /// pre-broadening parse (modulo absorption). For a terminal owned by a
    /// single category the sole candidate is trivially canonical, independent
    /// of `value_home_rank`. This generalizes the AddInt-only pilot and
    /// prevents the WALK-S1.5 cross-category fanout. `cat_src_idx` resolves a
    /// category NAME to its source index; `value_home_rank` to its 0/1 rank.
    pub fn is_canonical_iter_op(
        &self,
        op: &InfixOperator,
        cat_src_idx: &dyn Fn(&str) -> Option<u16>,
        value_home_rank: &dyn Fn(&str) -> u8,
    ) -> bool {
        if !op.is_iterative_candidate() {
            return false;
        }
        let Some(op_s) = cat_src_idx(&op.result_category) else {
            return false;
        };
        let op_key = (value_home_rank(&op.result_category), op_s, op.label.as_str());
        for other in &self.operators {
            if !other.is_iterative_candidate() || other.terminal != op.terminal {
                continue;
            }
            let Some(o_s) = cat_src_idx(&other.result_category) else {
                continue;
            };
            let other_key = (value_home_rank(&other.result_category), o_s, other.label.as_str());
            // A strictly-lower (value_home_rank, src_idx, label) candidate
            // exists for this terminal ⇒ `op` is not canonical. Strict `<`
            // makes the self-comparison a no-op without an identity check.
            if other_key < op_key {
                return false;
            }
        }
        true
    }

    /// Get all regular infix operators for a given category (excludes postfix, mixfix, cross-category).
    pub fn operators_for_category(&self, category: &str) -> Vec<&InfixOperator> {
        self.operators
            .iter()
            .filter(|op| {
                op.category == category && !op.is_cross_category && !op.is_postfix && !op.is_mixfix
            })
            .collect()
    }

    /// Get all postfix operators for a given category.
    pub fn postfix_operators_for_category(&self, category: &str) -> Vec<&InfixOperator> {
        self.operators
            .iter()
            .filter(|op| op.category == category && op.is_postfix)
            .collect()
    }

    /// Get all mixfix operators for a given category.
    pub fn mixfix_operators_for_category(&self, category: &str) -> Vec<&InfixOperator> {
        self.operators
            .iter()
            .filter(|op| op.category == category && op.is_mixfix)
            .collect()
    }

    /// Get all cross-category operators that produce results in the given category.
    pub fn cross_category_operators(&self, result_category: &str) -> Vec<&InfixOperator> {
        self.operators
            .iter()
            .filter(|op| op.result_category == result_category && op.is_cross_category)
            .collect()
    }

    /// Generate the `infix_bp` function for a specific category.
    ///
    /// Groups operators that share the same (left_bp, right_bp) pair into
    /// a single match arm with `|`-separated patterns for compact codegen.
    pub fn generate_bp_function(&self, category: &str) -> TokenStream {
        // Group operators by (left_bp, right_bp) pair
        let mut bp_groups: std::collections::BTreeMap<(u8, u8), Vec<proc_macro2::Ident>> =
            std::collections::BTreeMap::new();
        for op in self.operators_for_category(category) {
            let variant = format_ident!("{}", terminal_to_variant_name(&op.terminal));
            bp_groups
                .entry((op.left_bp, op.right_bp))
                .or_default()
                .push(variant);
        }

        let mut arms: Vec<TokenStream> = Vec::with_capacity(bp_groups.len() + 1);
        for ((left_bp, right_bp), variants) in &bp_groups {
            let left_bp = *left_bp;
            let right_bp = *right_bp;
            arms.push(quote! {
                #(Token::#variants)|* => Some((#left_bp, #right_bp))
            });
        }

        arms.push(quote! { _ => None });

        quote! {
            /// Get the binding power pair for an infix operator in this category.
            fn infix_bp(token: &Token) -> Option<(u8, u8)> {
                match token {
                    #(#arms),*
                }
            }
        }
    }

    /// BP03: Generate the `infix_bp` function using a static array lookup.
    ///
    /// When the category has >= `threshold` operators and `variant_map` is provided,
    /// emits a `static` array indexed by `token_variant_id()` instead of a match.
    /// Falls back to `generate_bp_function()` when the threshold is not met.
    ///
    /// Requires that `token_variant_id()` is emitted elsewhere (e.g., by
    /// `write_token_variant_id()` in `codegen.rs`).
    pub fn generate_bp_function_array(
        &self,
        category: &str,
        variant_map: &crate::automata::codegen::TokenVariantMap,
        threshold: usize,
    ) -> TokenStream {
        let ops = self.operators_for_category(category);
        if ops.len() < threshold {
            return self.generate_bp_function(category);
        }

        let array_len = variant_map.count as usize;
        let cat_upper = format_ident!("INFIX_BP_{}", category.to_uppercase());

        // Build array entries
        let mut entries = vec![(0u8, 0u8); array_len];
        for op in &ops {
            let variant_name = terminal_to_variant_name(&op.terminal);
            if let Some(id) = variant_map.get_id(&variant_name) {
                entries[id as usize] = (op.left_bp, op.right_bp);
            }
        }

        let entry_tokens: Vec<TokenStream> =
            entries.iter().map(|(l, r)| quote! { (#l, #r) }).collect();
        let len_lit = array_len;

        quote! {
            static #cat_upper: [(u8, u8); #len_lit] = [#(#entry_tokens),*];

            /// Get the binding power pair for an infix operator in this category.
            #[inline]
            fn infix_bp(token: &Token) -> Option<(u8, u8)> {
                let bp = #cat_upper[token_variant_id(token) as usize];
                if bp != (0, 0) { Some(bp) } else { None }
            }
        }
    }

    /// Generate the `make_infix` function for a specific category.
    pub fn generate_make_infix(&self, category: &str) -> TokenStream {
        let cat_ident = format_ident!("{}", category);
        let mut arms: Vec<TokenStream> = Vec::new();

        for op in self.operators_for_category(category) {
            let variant = format_ident!("{}", terminal_to_variant_name(&op.terminal));
            let label = format_ident!("{}", op.label);
            arms.push(quote! {
                Token::#variant => #cat_ident::#label(Box::new(lhs), Box::new(rhs))
            });
        }

        arms.push(quote! {
            _ => unreachable!("make_infix called with non-infix token")
        });

        quote! {
            /// Construct an infix AST node from an operator token and operands.
            fn make_infix(token: &Token, lhs: #cat_ident, rhs: #cat_ident) -> #cat_ident {
                match token {
                    #(#arms),*
                }
            }
        }
    }
}

impl Default for BindingPowerTable {
    fn default() -> Self {
        Self::new()
    }
}

/// Standardized offset for unary-prefix binding power above the maximum
/// non-postfix infix binding power in a category.
///
/// **Stage 3.27d-pre standardization (user-approved 2026-04-30):** the
/// unary-prefix binding power is `max_infix_bp + PREFIX_BP_OFFSET = max_infix_bp + 2`.
/// This places prefix in the upper half of the 2-slot gap that
/// `analyze_binding_powers` reserves between max-infix and first-postfix
/// (postfix starts at `max_infix_bp + 4`).
///
/// **Why +2 (not +1):** matches the existing Display behavior at
/// `macros/src/gen/syntax/display.rs:174` and the legacy recursive-descent
/// path at `prattail/src/pipeline.rs:1259` — both already use `+2`.
/// Standardizing to `+2` is zero-regression. Margin above max-infix also
/// provides defense-in-depth against off-by-one bugs in BP comparisons.
///
/// **Consumers:**
/// - `prattail/src/pipeline.rs::generate_parser` — RDRuleInfo emission
/// - `macros/src/gen/syntax/display.rs::build_bp_lookup` — Display paren elision
/// - `macros/src/gen/runtime/wpda_codegen/binder.rs:708,1004` — WPDS ParamParse arms
///   (Stage 3.27d G-PREFIX-BP installs `cur_bp = compute_prefix_bp(...)` here)
pub const PREFIX_BP_OFFSET: u8 = 2;

/// Compute the binding power for a unary-prefix rule's operand sub-parse.
///
/// **Algorithm:**
/// - If `explicit_prefix_precedence` is `Some(bp)`, return that (user-supplied).
/// - Otherwise compute `max_infix_bp(category) + PREFIX_BP_OFFSET`, where
///   `max_infix_bp(category)` is the maximum of `(left_bp, right_bp)` across
///   all non-postfix operators with `op.category == rule_category`.
/// - Returns 0 + PREFIX_BP_OFFSET = 2 when the category has no infix operators
///   (cleanly handles empty-infix categories without a special case).
///
/// **Filtering rationale:** the operand-category filter (`op.category ==
/// rule_category`) is the right scope because the operand sub-parse is at
/// `cur_bp = prefix_bp`; only operators producing in the operand category
/// (i.e., that could fire on the operand) need to be dominated. Cross-cat
/// operators with `result_category != category` are correctly EXCLUDED.
///
/// **Use in WPDS, Display, and pipeline:** all three paths must call this
/// function rather than duplicating the formula. See module-level docs.
pub fn compute_prefix_bp(
    rule_category: &str,
    explicit_prefix_precedence: Option<u8>,
    bp_table: &BindingPowerTable,
) -> u8 {
    if let Some(explicit) = explicit_prefix_precedence {
        return explicit;
    }
    let cat_max: u8 = bp_table
        .operators
        .iter()
        .filter(|op| op.category == rule_category && !op.is_postfix)
        .map(|op| op.left_bp.max(op.right_bp))
        .max()
        .unwrap_or(0);
    cat_max.saturating_add(PREFIX_BP_OFFSET)
}

/// Analyze grammar rules to build the binding power table.
///
/// Rules are classified as infix if:
/// - Old syntax: ≥3 items, first and last are NonTerminal matching the category,
///   with at least one Terminal in between
/// - New syntax: syntax_pattern is [Param, Literal, Param] with both params
///   having the same type as the result category
///
/// Precedence is assigned by declaration order: first-declared infix operator
/// gets the lowest precedence. Operators within the same precedence group
/// are left-associative by default.
///
/// Postfix operators are assigned binding powers above all non-postfix operators
/// in a second pass, ensuring they always bind tighter than infix operators
/// regardless of declaration order. This follows the standard convention that
/// postfix binds tighter than infix (e.g., `3 + 5!` = `3 + (5!)`), and unary
/// prefix binds between infix and postfix (e.g., `-5!` = `-(5!)`).
pub fn analyze_binding_powers(rules: &[InfixRuleInfo]) -> BindingPowerTable {
    let mut table = BindingPowerTable::new();

    // Group infix rules by category
    let mut by_category: std::collections::BTreeMap<String, Vec<&InfixRuleInfo>> =
        std::collections::BTreeMap::new();
    for rule in rules {
        by_category
            .entry(rule.category.clone())
            .or_default()
            .push(rule);
    }

    // Assign binding powers per category using two passes:
    // 1. Non-postfix (infix) operators in declaration order
    // 2. Postfix operators above the non-postfix range, leaving a gap for
    //    unary prefix (which gets max_non_postfix_bp + 2 in lib.rs)
    for cat_rules in by_category.values() {
        let mut precedence: u8 = 2; // Start at 2 to leave room for 0 (entry) and 1

        // First pass: non-postfix operators (regular infix + mixfix)
        for rule in cat_rules.iter().filter(|r| !r.is_postfix) {
            let (left_bp, right_bp) = match rule.associativity {
                Associativity::Left => {
                    let bp = (precedence, precedence + 1);
                    precedence += 2;
                    bp
                },
                Associativity::Right => {
                    let bp = (precedence + 1, precedence);
                    precedence += 2;
                    bp
                },
            };

            table.operators.push(InfixOperator {
                terminal: rule.terminal.clone(),
                category: rule.category.clone(),
                result_category: rule.result_category.clone(),
                left_bp,
                right_bp,
                label: rule.label.clone(),
                is_cross_category: rule.is_cross_category,
                is_postfix: false,
                is_mixfix: rule.is_mixfix,
                mixfix_parts: rule.mixfix_parts.clone(),
                nullary_literals: rule.nullary_literals.clone(),
            });
        }

        // Second pass: postfix operators start above non-postfix + prefix gap.
        // Layout (Stage 3.27d-pre standardized 2026-04-30, PREFIX_BP_OFFSET=2):
        //   [infix at 2..max_infix_bp] [prefix at max_infix_bp+2] [postfix at max_infix_bp+4..]
        // where `precedence` after the infix loop = max_infix_bp + 1.
        // Prefix BP is computed by `compute_prefix_bp()` and installed at codegen
        // time in WPDS binder.rs:708,1004 ParamParse arms (Stage 3.27d work).
        let mut postfix_prec = precedence + 2;
        for rule in cat_rules.iter().filter(|r| r.is_postfix) {
            table.operators.push(InfixOperator {
                terminal: rule.terminal.clone(),
                category: rule.category.clone(),
                result_category: rule.result_category.clone(),
                left_bp: postfix_prec + 1,
                right_bp: 0, // unused for postfix (no right recursive call)
                label: rule.label.clone(),
                is_cross_category: rule.is_cross_category,
                is_postfix: true,
                is_mixfix: false,
                mixfix_parts: Vec::new(),
                nullary_literals: Vec::new(),
            });
            postfix_prec += 2;
        }
    }

    table
}

/// Simplified infix rule info for binding power analysis.
#[derive(Debug, Clone)]
pub struct InfixRuleInfo {
    /// Constructor label (e.g., "Add", "Mul").
    pub label: String,
    /// Terminal operator text (e.g., "+", "*").
    /// For mixfix operators, this is the trigger terminal (e.g., "?" for ternary).
    pub terminal: String,
    /// Operand category (e.g., "Int").
    pub category: String,
    /// Result category (e.g., "Int" for same-category, "Bool" for cross-category).
    pub result_category: String,
    /// Associativity (default: Left).
    pub associativity: Associativity,
    /// Whether this is a cross-category operator.
    pub is_cross_category: bool,
    /// Whether this is a postfix operator.
    pub is_postfix: bool,
    /// Whether this is a mixfix operator (3+ operands, 2+ terminals).
    pub is_mixfix: bool,
    /// Mixfix parts (operand-separator pairs after the trigger). Empty for non-mixfix.
    pub mixfix_parts: Vec<MixfixPart>,
    /// GEN-1 B-1 (Stage S2): post-trigger literal sequence for a 0-operand
    /// (nullary) mixfix rule (e.g. POutputEmpty `n "!" "(" ")"` ⇒
    /// `["(", ")"]`). Empty for every operand-bearing rule. See
    /// [`InfixOperator::nullary_literals`].
    pub nullary_literals: Vec<String>,
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper to create an InfixRuleInfo with default flags (non-cross, non-postfix, non-mixfix).
    fn make_rule(
        label: &str,
        terminal: &str,
        category: &str,
        assoc: Associativity,
    ) -> InfixRuleInfo {
        InfixRuleInfo {
            label: label.to_string(),
            terminal: terminal.to_string(),
            category: category.to_string(),
            result_category: category.to_string(),
            associativity: assoc,
            is_cross_category: false,
            is_postfix: false,
            is_mixfix: false,
            mixfix_parts: Vec::new(),
            nullary_literals: Vec::new(),
        }
    }

    /// Helper to create an InfixOperator directly (for filter tests that bypass analyze).
    fn make_op(
        label: &str,
        terminal: &str,
        category: &str,
        result_category: &str,
        left_bp: u8,
        right_bp: u8,
        is_cross_category: bool,
        is_postfix: bool,
        is_mixfix: bool,
    ) -> InfixOperator {
        InfixOperator {
            terminal: terminal.to_string(),
            category: category.to_string(),
            result_category: result_category.to_string(),
            left_bp,
            right_bp,
            label: label.to_string(),
            is_cross_category,
            is_postfix,
            is_mixfix,
            mixfix_parts: Vec::new(),
            nullary_literals: Vec::new(),
        }
    }

    #[test]
    fn test_bp_table_new_empty() {
        let table = BindingPowerTable::new();
        assert!(table.operators.is_empty(), "new table should have zero operators");
    }

    // ── C1 D1: canonical-op-per-terminal winner selection ───────────────
    // These pin the value-home-rank rule so a future `terms {}` reorder (the
    // original WALK-S1.5 failure mode: BigRat's `error` rule pushed BigRat to
    // a lower src_idx than Int) cannot silently re-break the canonical winner.

    #[test]
    fn test_canonical_iter_op_value_home_beats_lower_src_idx() {
        // `+` shared across BigRat(src 1, NOT integer-home), Int(2, home),
        // UInt32(3, home), BigInt(6, home) — the calculator's actual order
        // (Proc=0, BigRat=1, Int=2, UInt32=3, ..., BigInt=6). The walker's
        // lex-min winner for a bare-integer chain is Int, NOT the
        // lower-src_idx BigRat (a bare integer reaches BigRat only via a
        // cross-cat projection at a worse tier). The value-home key selects
        // Int; the OLD lowest-src_idx-only rule wrongly selected AddBigRat.
        let mut table = BindingPowerTable::new();
        table.operators.push(make_op(
            "AddBigRat",
            "+",
            "BigRat",
            "BigRat",
            2,
            3,
            false,
            false,
            false,
        ));
        table
            .operators
            .push(make_op("AddInt", "+", "Int", "Int", 2, 3, false, false, false));
        table.operators.push(make_op(
            "AddUInt32",
            "+",
            "UInt32",
            "UInt32",
            2,
            3,
            false,
            false,
            false,
        ));
        table.operators.push(make_op(
            "AddBigInt",
            "+",
            "BigInt",
            "BigInt",
            2,
            3,
            false,
            false,
            false,
        ));
        let src = |n: &str| -> Option<u16> {
            match n {
                "BigRat" => Some(1),
                "Int" => Some(2),
                "UInt32" => Some(3),
                "BigInt" => Some(6),
                _ => None,
            }
        };
        // 0 = integer-home (tier-0.0 polymorphic home arm); BigRat is
        // rational-home (rank 1, reachable only via cross-cat for integers).
        let home = |n: &str| -> u8 {
            match n {
                "Int" | "UInt32" | "BigInt" => 0,
                _ => 1,
            }
        };
        let by_label = |lbl: &str| table.operators.iter().find(|o| o.label == lbl).unwrap();
        assert!(
            table.is_canonical_iter_op(by_label("AddInt"), &src, &home),
            "AddInt (integer-home, lex-min winner) must be canonical for `+`"
        );
        assert!(
            !table.is_canonical_iter_op(by_label("AddBigRat"), &src, &home),
            "AddBigRat (lower src_idx but NOT integer-home) must NOT be canonical"
        );
        assert!(
            !table.is_canonical_iter_op(by_label("AddUInt32"), &src, &home),
            "AddUInt32 (integer-home but higher src than Int) must NOT be canonical"
        );
        assert!(
            !table.is_canonical_iter_op(by_label("AddBigInt"), &src, &home),
            "AddBigInt (integer-home but higher src than Int) must NOT be canonical"
        );
    }

    #[test]
    fn test_canonical_iter_op_right_assoc_pow() {
        // `^` shared across Int(src 2, integer-home) and Float(5, not). Right-
        // assoc (left_bp > right_bp). Int is the winner (only integer-home).
        let mut table = BindingPowerTable::new();
        table
            .operators
            .push(make_op("PowInt", "^", "Int", "Int", 27, 26, false, false, false));
        table
            .operators
            .push(make_op("PowFloat", "^", "Float", "Float", 27, 26, false, false, false));
        let src = |n: &str| -> Option<u16> {
            match n {
                "Int" => Some(2),
                "Float" => Some(5),
                _ => None,
            }
        };
        let home = |n: &str| -> u8 {
            if n == "Int" {
                0
            } else {
                1
            }
        };
        let by_label = |lbl: &str| table.operators.iter().find(|o| o.label == lbl).unwrap();
        assert!(
            table.is_canonical_iter_op(by_label("PowInt"), &src, &home),
            "PowInt (integer-home) must be canonical for `^`"
        );
        assert!(
            !table.is_canonical_iter_op(by_label("PowFloat"), &src, &home),
            "PowFloat (not integer-home) must NOT be canonical"
        );
    }

    #[test]
    fn test_canonical_iter_op_unique_terminal() {
        // A terminal owned by a single (non-integer-home) category is
        // trivially canonical despite the rank-1 penalty — uniqueness wins.
        let mut table = BindingPowerTable::new();
        table
            .operators
            .push(make_op("EPar", "|", "Expr", "Expr", 2, 3, false, false, false));
        let src = |n: &str| -> Option<u16> {
            if n == "Expr" {
                Some(4)
            } else {
                None
            }
        };
        let home = |_: &str| -> u8 { 1 };
        let by_label = |lbl: &str| table.operators.iter().find(|o| o.label == lbl).unwrap();
        assert!(
            table.is_canonical_iter_op(by_label("EPar"), &src, &home),
            "the sole candidate for a unique terminal must be canonical"
        );
    }

    #[test]
    fn test_operators_for_category_filter() {
        let mut table = BindingPowerTable::new();
        // Two Int operators, one Bool operator
        table
            .operators
            .push(make_op("Add", "+", "Int", "Int", 2, 3, false, false, false));
        table
            .operators
            .push(make_op("Mul", "*", "Int", "Int", 4, 5, false, false, false));
        table
            .operators
            .push(make_op("And", "&&", "Bool", "Bool", 2, 3, false, false, false));

        let int_ops = table.operators_for_category("Int");
        assert_eq!(int_ops.len(), 2, "should return only Int operators");
        assert_eq!(int_ops[0].label, "Add");
        assert_eq!(int_ops[1].label, "Mul");

        let bool_ops = table.operators_for_category("Bool");
        assert_eq!(bool_ops.len(), 1);
        assert_eq!(bool_ops[0].label, "And");

        let empty = table.operators_for_category("String");
        assert!(empty.is_empty(), "non-existent category should return empty");
    }

    #[test]
    fn test_postfix_operators_for_category() {
        let mut table = BindingPowerTable::new();
        table
            .operators
            .push(make_op("Add", "+", "Int", "Int", 2, 3, false, false, false));
        table
            .operators
            .push(make_op("Fact", "!", "Int", "Int", 10, 0, false, true, false));
        table
            .operators
            .push(make_op("Incr", "++", "Int", "Int", 12, 0, false, true, false));

        let postfix = table.postfix_operators_for_category("Int");
        assert_eq!(postfix.len(), 2, "should return only postfix operators");
        assert_eq!(postfix[0].label, "Fact");
        assert_eq!(postfix[1].label, "Incr");
    }

    #[test]
    fn test_mixfix_operators_for_category() {
        let mut table = BindingPowerTable::new();
        table
            .operators
            .push(make_op("Add", "+", "Int", "Int", 2, 3, false, false, false));
        let mut ternary = make_op("Ternary", "?", "Int", "Int", 2, 3, false, false, true);
        ternary.mixfix_parts = vec![
            MixfixPart {
                operand_category: "Int".to_string(),
                param_name: "b".to_string(),
                preceding_terminals: vec![],
                following_terminals: vec![":".to_string()],
                repetition: None,
            },
            MixfixPart {
                operand_category: "Int".to_string(),
                param_name: "c".to_string(),
                preceding_terminals: vec![],
                following_terminals: vec![],
                repetition: None,
            },
        ];
        table.operators.push(ternary);

        let mixfix = table.mixfix_operators_for_category("Int");
        assert_eq!(mixfix.len(), 1, "should return only mixfix operators");
        assert_eq!(mixfix[0].label, "Ternary");
        assert_eq!(mixfix[0].mixfix_parts.len(), 2);
    }

    #[test]
    fn test_cross_category_operators() {
        let mut table = BindingPowerTable::new();
        // Regular same-category op
        table
            .operators
            .push(make_op("Add", "+", "Int", "Int", 2, 3, false, false, false));
        // Cross-category: Int == Int -> Bool
        table
            .operators
            .push(make_op("Eq", "==", "Int", "Bool", 2, 3, true, false, false));
        // Cross-category: Int < Int -> Bool
        table
            .operators
            .push(make_op("Lt", "<", "Int", "Bool", 2, 3, true, false, false));

        let cross = table.cross_category_operators("Bool");
        assert_eq!(cross.len(), 2, "should return cross-cat ops producing Bool");
        assert_eq!(cross[0].label, "Eq");
        assert_eq!(cross[1].label, "Lt");

        let cross_int = table.cross_category_operators("Int");
        assert!(cross_int.is_empty(), "no cross-cat ops produce Int");
    }

    #[test]
    fn test_analyze_bp_left_assoc() {
        let rules = vec![
            make_rule("Add", "+", "Int", Associativity::Left),
            make_rule("Sub", "-", "Int", Associativity::Left),
        ];
        let table = analyze_binding_powers(&rules);
        assert_eq!(table.operators.len(), 2);

        for op in &table.operators {
            assert!(
                op.left_bp < op.right_bp,
                "left-assoc operator {} should have left_bp({}) < right_bp({})",
                op.label,
                op.left_bp,
                op.right_bp
            );
        }
    }

    #[test]
    fn test_analyze_bp_right_assoc() {
        let rules = vec![
            make_rule("Pow", "^", "Int", Associativity::Right),
            make_rule("Assign", "=", "Int", Associativity::Right),
        ];
        let table = analyze_binding_powers(&rules);
        assert_eq!(table.operators.len(), 2);

        for op in &table.operators {
            assert!(
                op.left_bp > op.right_bp,
                "right-assoc operator {} should have left_bp({}) > right_bp({})",
                op.label,
                op.left_bp,
                op.right_bp
            );
        }
    }

    #[test]
    fn test_analyze_bp_precedence_ordering() {
        // Add declared first (lower precedence), Mul declared second (higher precedence)
        let rules = vec![
            make_rule("Add", "+", "Int", Associativity::Left),
            make_rule("Mul", "*", "Int", Associativity::Left),
        ];
        let table = analyze_binding_powers(&rules);

        let add = table
            .operators
            .iter()
            .find(|op| op.label == "Add")
            .expect("Add not found");
        let mul = table
            .operators
            .iter()
            .find(|op| op.label == "Mul")
            .expect("Mul not found");

        // Mul should have strictly higher binding powers than Add
        assert!(
            mul.left_bp > add.left_bp,
            "Mul.left_bp({}) should be > Add.left_bp({})",
            mul.left_bp,
            add.left_bp
        );
        assert!(
            mul.right_bp > add.right_bp,
            "Mul.right_bp({}) should be > Add.right_bp({})",
            mul.right_bp,
            add.right_bp
        );
    }

    #[test]
    fn test_postfix_above_infix() {
        let rules = vec![
            make_rule("Add", "+", "Int", Associativity::Left),
            make_rule("Mul", "*", "Int", Associativity::Left),
            {
                let mut r = make_rule("Fact", "!", "Int", Associativity::Left);
                r.is_postfix = true;
                r
            },
        ];
        let table = analyze_binding_powers(&rules);

        let max_infix_bp = table
            .operators
            .iter()
            .filter(|op| !op.is_postfix)
            .map(|op| op.left_bp.max(op.right_bp))
            .max()
            .expect("should have infix operators");

        let fact = table
            .operators
            .iter()
            .find(|op| op.label == "Fact")
            .expect("Fact not found");
        assert!(fact.is_postfix, "Fact should be postfix");
        assert!(
            fact.left_bp > max_infix_bp,
            "postfix left_bp({}) should be > max infix bp({})",
            fact.left_bp,
            max_infix_bp
        );
    }

    #[test]
    fn test_associativity_method() {
        let left_op = InfixOperator {
            terminal: "+".to_string(),
            category: "Int".to_string(),
            result_category: "Int".to_string(),
            left_bp: 2,
            right_bp: 3,
            label: "Add".to_string(),
            is_cross_category: false,
            is_postfix: false,
            is_mixfix: false,
            mixfix_parts: Vec::new(),
            nullary_literals: Vec::new(),
        };
        assert_eq!(left_op.associativity(), Associativity::Left);

        let right_op = InfixOperator {
            terminal: "^".to_string(),
            category: "Int".to_string(),
            result_category: "Int".to_string(),
            left_bp: 3,
            right_bp: 2,
            label: "Pow".to_string(),
            is_cross_category: false,
            is_postfix: false,
            is_mixfix: false,
            mixfix_parts: Vec::new(),
            nullary_literals: Vec::new(),
        };
        assert_eq!(right_op.associativity(), Associativity::Right);

        // Equal BP should return Right (left_bp < right_bp is false)
        let equal_op = InfixOperator {
            terminal: "=".to_string(),
            category: "Int".to_string(),
            result_category: "Int".to_string(),
            left_bp: 5,
            right_bp: 5,
            label: "Eq".to_string(),
            is_cross_category: false,
            is_postfix: false,
            is_mixfix: false,
            mixfix_parts: Vec::new(),
            nullary_literals: Vec::new(),
        };
        assert_eq!(equal_op.associativity(), Associativity::Right);
    }

    // ─────────────────────────────────────────────────────────────────
    // Stage 3.27d-pre (2026-04-30): compute_prefix_bp tests
    // ─────────────────────────────────────────────────────────────────

    #[test]
    fn test_compute_prefix_bp_default_is_max_infix_bp_plus_offset() {
        // Three left-assoc infix operators in Int: +, *, ^.
        // analyze_binding_powers assigns precedences 2-3, 4-5, 6-7.
        // max_infix_bp = 7, so prefix_bp = 7 + PREFIX_BP_OFFSET = 9.
        let rules = vec![
            make_rule("Add", "+", "Int", Associativity::Left),
            make_rule("Mul", "*", "Int", Associativity::Left),
            make_rule("Pow", "^", "Int", Associativity::Left),
        ];
        let table = analyze_binding_powers(&rules);
        let bp = compute_prefix_bp("Int", None, &table);
        assert_eq!(
            bp,
            7 + PREFIX_BP_OFFSET,
            "default prefix_bp should be max_infix_bp ({}) + PREFIX_BP_OFFSET ({}) = {}",
            7,
            PREFIX_BP_OFFSET,
            7 + PREFIX_BP_OFFSET,
        );
    }

    #[test]
    fn test_compute_prefix_bp_explicit_overrides_auto() {
        // Even with infix operators present, explicit takes precedence.
        let rules = vec![make_rule("Add", "+", "Int", Associativity::Left)];
        let table = analyze_binding_powers(&rules);
        assert_eq!(
            compute_prefix_bp("Int", Some(42), &table),
            42,
            "explicit prefix_precedence should override auto-computed",
        );
    }

    #[test]
    fn test_compute_prefix_bp_empty_infix_returns_offset() {
        // Category with no infix operators: max defaults to 0, so prefix_bp = 0 + offset.
        let table = BindingPowerTable::new();
        assert_eq!(
            compute_prefix_bp("Int", None, &table),
            PREFIX_BP_OFFSET,
            "empty-infix category should yield prefix_bp = PREFIX_BP_OFFSET",
        );
    }

    #[test]
    fn test_compute_prefix_bp_below_min_postfix_bp() {
        // Layout invariant: postfix should bind tighter than prefix.
        // With infix at 2-3 and postfix injected at max+4 (analyze_binding_powers
        // pattern), the lowest postfix_l_bp must exceed compute_prefix_bp's output.
        let rules = vec![
            make_rule("Add", "+", "Int", Associativity::Left),
            InfixRuleInfo {
                label: "Fact".to_string(),
                terminal: "!".to_string(),
                category: "Int".to_string(),
                result_category: "Int".to_string(),
                associativity: Associativity::Left,
                is_cross_category: false,
                is_postfix: true,
                is_mixfix: false,
                mixfix_parts: Vec::new(),
                nullary_literals: Vec::new(),
            },
        ];
        let table = analyze_binding_powers(&rules);
        let prefix = compute_prefix_bp("Int", None, &table);
        let postfix_min = table
            .postfix_operators_for_category("Int")
            .iter()
            .map(|op| op.left_bp)
            .min()
            .expect("at least one postfix op");
        assert!(
            postfix_min > prefix,
            "postfix l_bp {} must exceed prefix_bp {} so `-x!` parses as `-(x!)`",
            postfix_min,
            prefix,
        );
    }

    #[test]
    fn test_compute_prefix_bp_filters_by_operand_category() {
        // Cross-cat operator with operand=Int, result=Bool should NOT contribute
        // to Bool's prefix_bp computation (it's filtered by operand category).
        let mut table = BindingPowerTable::new();
        table
            .operators
            .push(make_op("Lt", "<", "Int", "Bool", 4, 5, true, false, false));
        table
            .operators
            .push(make_op("And", "&&", "Bool", "Bool", 2, 3, false, false, false));

        // For Bool's prefix_bp: only `&&` (operand=Bool) contributes; `<` (operand=Int) is filtered.
        // max from Bool ops = 3, so prefix_bp = 3 + 2 = 5.
        let bool_prefix = compute_prefix_bp("Bool", None, &table);
        assert_eq!(
            bool_prefix,
            3 + PREFIX_BP_OFFSET,
            "Bool's prefix_bp should derive from Bool-operand operators only",
        );

        // For Int's prefix_bp: only `<` (operand=Int) contributes.
        let int_prefix = compute_prefix_bp("Int", None, &table);
        assert_eq!(
            int_prefix,
            5 + PREFIX_BP_OFFSET,
            "Int's prefix_bp should derive from Int-operand operators only",
        );
    }
}
