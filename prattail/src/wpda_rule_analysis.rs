//! Shared rule observations and original WPDA derivation implementations.
//!
//! This is a relocation of the macro-era classifier, not a second rule
//! analyzer. It produces the existing binding-power descriptions, not a new
//! parser instruction set. Callers preserve authored parameter order and keep
//! unsupported entries as markers; they must not reconstruct declaration
//! order from concrete syntax. BNF normalization remains the caller's existing
//! operation.
//!
//! The classifiers observe authored grammar through their existing descriptors
//! or shallow readers. These are not a replacement language schema.
//! Nested unsupported data is neither traversed nor copied. The projection
//! boundary is modeled in `InfixClassifierProjection.v`; exact source
//! correspondence and before/after tests bind it to this relocated code.

use crate::binding_power::{Associativity, InfixRuleInfo, MixfixPart, MixfixRep};

pub mod atomic;
pub mod authored;
pub mod binder;
pub mod census;
pub mod collection;
pub mod factoring;
pub mod fork_emission;
pub mod grouping;
pub mod mixfix;
pub mod parikh;
pub mod prefix;
pub mod synthetic;

/// Ordered rule observations, with absent lists distinguished from empty ones.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InfixRuleShape {
    /// Constructor name, unchanged.
    pub label: String,
    /// Result category, unchanged.
    pub category: String,
    /// Declared right associativity.
    pub is_right_assoc: bool,
    /// Declared sharing of the previous precedence level.
    pub shares_level_with_previous: bool,
    /// Parameters in declaration order, including unsupported markers.
    pub term_context: Option<Vec<InfixParamShape>>,
    /// Syntax in source order, including unsupported markers.
    pub syntax_pattern: Option<Vec<InfixSyntaxShape>>,
}

/// The classifier observes only simple parameters; other positions still count.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InfixParamShape {
    /// A named parameter with its shallow type observations.
    Simple { name: String, ty: InfixTypeShape },
    /// A binder, guard, optional group, or other non-simple parameter.
    Other,
}

/// The type observations used by the original classifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InfixTypeShape {
    /// Exact base-type name, including the distinguished `Ident` capture.
    Base(String),
    /// Only an immediate base element is an operand; nested types remain None.
    Collection { element_base: Option<String> },
    /// Any type the original classifier does not inspect.
    Other,
}

impl InfixTypeShape {
    /// Preserve the AST's exact builtin identifier-text predicate.
    fn is_ident_text(&self) -> bool {
        matches!(self, Self::Base(name) if name == IDENT_CAPTURE_KIND_NAME)
    }
}

/// Top-level syntax observations; unsupported entries are never filtered out.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InfixSyntaxShape {
    /// Literal text, unchanged.
    Literal(String),
    /// Exact parameter name.
    Param(String),
    /// The original Sep branch observes only collection name and separator.
    Sep { collection: String, separator: String },
    /// Unsupported syntax retains its original position and rejection behavior.
    Other,
}

/// Classify a projected rule using the original branch and fallthrough order.
pub fn classify_rule(rule: &InfixRuleShape) -> Option<InfixRuleInfo> {
    if let (Some(tc), Some(sp)) = (&rule.term_context, &rule.syntax_pattern) {
        return classify_judgement(rule, tc, sp);
    }
    None
}

fn classify_judgement(
    rule: &InfixRuleShape,
    term_context: &[InfixParamShape],
    syntax_pattern: &[InfixSyntaxShape],
) -> Option<InfixRuleInfo> {
    // Filter to Simple params only — binder / guard / multi-abstraction
    // rules are Phase A.5 / A.6 / A.8.
    let simples: Vec<(&String, &InfixTypeShape)> = term_context
        .iter()
        .filter_map(|p| match p {
            InfixParamShape::Simple { name, ty } => Some((name, ty)),
            _ => None,
        })
        .collect();
    if simples.len() != term_context.len() {
        return None;
    }

    let result_cat = rule.category.to_string();

    // Binary infix: 2 Simple params, pattern = [Param, Literal, Param].
    if simples.len() == 2 && syntax_pattern.len() == 3 {
        if let (
            InfixSyntaxShape::Param(p1),
            InfixSyntaxShape::Literal(op),
            InfixSyntaxShape::Param(p2),
        ) = (&syntax_pattern[0], &syntax_pattern[1], &syntax_pattern[2])
        {
            let (n1, t1) = simples[0];
            let (n2, t2) = simples[1];
            if n1 == p1 && n2 == p2 {
                let t1_str = base_type_name(t1)?;
                let t2_str = base_type_name(t2)?;
                // GEN-1 GAP-1 (2026-06-28): only the HOMOGENEOUS-operand binary
                // (t1 == t2) is a plain binary infix. For HETEROGENEOUS operands
                // (t1 ≠ t2) we MUST NOT `return None` from the whole classifier —
                // that silently dropped `A op B → C` (A ≠ B), losing its table
                // entry, its lex-alt arm, AND its `cat_can_reach` edge (the
                // goal-gate then becomes non-conservative). Instead we fall
                // through to `classify_postfix_mixfix` below (reached at
                // `simples.len() >= 1 && syntax_pattern.len() >= 3`), which treats
                // `[Param, Literal, Param]` as an LHS (cross-cat source = t1) plus
                // ONE goal-bounded inner operand (t2) — emitted as a mixfix with
                // `category = t1`, `result_category = C`. This restores the
                // `t1 → C` LHS edge for heterogeneous casts (`e:Expr "as" t:Type
                // |- :R`, `x satisfies T`, `x is T`). Audit §GAP-1.
                if t1_str == t2_str {
                    let is_cross_category = t1_str != result_cat;
                    return Some(InfixRuleInfo {
                        label: rule.label.to_string(),
                        terminal: op.clone(),
                        category: t1_str,
                        result_category: result_cat,
                        associativity: if rule.is_right_assoc {
                            Associativity::Right
                        } else {
                            Associativity::Left
                        },
                        shares_level_with_previous: rule.shares_level_with_previous,
                        is_cross_category,
                        is_postfix: false,
                        is_mixfix: false,
                        mixfix_parts: Vec::new(),
                        nullary_literals: Vec::new(),
                    });
                }
                // t1 ≠ t2: fall through to classify_postfix_mixfix (no return).
            }
        }
    }

    // Unary postfix: 1 Simple param, pattern = [Param, Literal].
    if simples.len() == 1 && syntax_pattern.len() == 2 {
        if let (InfixSyntaxShape::Param(p1), InfixSyntaxShape::Literal(op)) =
            (&syntax_pattern[0], &syntax_pattern[1])
        {
            let (n1, t1) = simples[0];
            if n1 == p1 {
                let t1_str = base_type_name(t1)?;
                let is_cross_category = t1_str != result_cat;
                return Some(InfixRuleInfo {
                    label: rule.label.to_string(),
                    terminal: op.clone(),
                    category: t1_str,
                    result_category: result_cat,
                    // A postfix operator has no right operand, so it has no
                    // associativity to declare; `analyze_binding_powers` lays every
                    // postfix operator out in a separate pass ABOVE the whole infix
                    // range, where neither this field nor `shares_level_with_previous`
                    // is read.
                    associativity: Associativity::Left,
                    shares_level_with_previous: false,
                    is_cross_category,
                    is_postfix: true,
                    is_mixfix: false,
                    mixfix_parts: Vec::new(),
                    nullary_literals: Vec::new(),
                });
            }
        }
    }

    // Mixfix: 3+ Simple params with alternating [Param, Lit, Param, ...].
    if simples.len() >= 3 {
        if let Some(info) = classify_mixfix(rule, &simples, syntax_pattern) {
            return Some(info);
        }
    }

    // L12 follow-up B6 step 3 (2026-05-07) — Class 1 MIXFIX-LHS-PARAM:
    // classify_postfix_mixfix is now ACTIVE in the dispatch chain. The
    // walker-side `WpdaState::MixfixLiteralRun` (added in this same
    // commit) walks the postfix-mixfix per-part literal sequences via
    // per-iteration ConsumeAndReplace.
    //
    // GEN-1 B-1 (Stage S2): gate relaxed `simples >= 2` → `simples >= 1` so a
    // 0-operand ("nullary") Param-prefixed rule — only LHS, then literals
    // (POutputEmpty `n "!" "(" ")"`, zero-arg methods `.size()`) — reaches
    // the classifier and is emitted as a nullary mixfix (arity-1 LHS-only).
    if simples.len() >= 1 && syntax_pattern.len() >= 3 {
        if let Some(info) = classify_postfix_mixfix(rule, &simples, syntax_pattern) {
            return Some(info);
        }
    }

    None
}

/// L12 follow-up B6 step 2 (2026-05-07) — Class 1 classifier.
///
/// Recognizes Param-prefixed multi-element rules with possibly-consecutive
/// literals between operands. The first Param is the LHS (cross-cat-source);
/// the first Literal is the trigger; subsequent Literals are absorbed into
/// preceding_terminals (before the next operand) or following_terminals
/// (after the most-recent operand).
///
/// Returns InfixRuleInfo with `is_mixfix: true` so downstream dispatch
/// (mixfix_bp_<cat> table, Unwinding-MixfixMarker arm, MixfixContinuation
/// state) handles the rule via the existing mixfix machinery — the widened
/// MixfixPart::preceding_terminals/following_terminals (B6 step 1) carry
/// the multi-literal sequences.
fn classify_postfix_mixfix(
    rule: &InfixRuleShape,
    simples: &[(&String, &InfixTypeShape)],
    syntax_pattern: &[InfixSyntaxShape],
) -> Option<InfixRuleInfo> {
    // GEN-1 B-1 (Stage S2): gate relaxed `< 2` → `< 1`. A 1-Simple rule whose
    // only param is the LHS, followed by trigger + literals with NO inner
    // operand, is a NULLARY mixfix (POutputEmpty `n "!" "(" ")"`, zero-arg
    // methods `.size()`); it is emitted with empty `mixfix_parts` and the
    // post-trigger literals in `nullary_literals`.
    if simples.len() < 1 || syntax_pattern.len() < 3 {
        return None;
    }
    // Position 0 must be the LHS Param.
    let InfixSyntaxShape::Param(lhs_name) = &syntax_pattern[0] else {
        return None;
    };
    let (lhs_simple_name, lhs_ty) = simples[0];
    if lhs_simple_name != lhs_name {
        return None;
    }
    let lhs_cat = base_type_name(lhs_ty)?;
    let result_cat = rule.category.to_string();
    let is_cross_category = lhs_cat != result_cat;

    // Trigger: must be a Literal immediately after LHS.
    let trigger = match syntax_pattern.get(1) {
        Some(InfixSyntaxShape::Literal(t)) => t.clone(),
        _ => return None,
    };

    // Walk the remaining pattern, accumulating preceding_terminals before
    // each new operand and following_terminals after the most-recent one.
    let mut preceding_buffer: Vec<String> = Vec::new();
    let mut parts: Vec<MixfixPart> = Vec::new();
    let mut simple_idx: usize = 1; // simples[0] is the LHS already consumed.
    let mut idx: usize = 2;
    while idx < syntax_pattern.len() {
        match &syntax_pattern[idx] {
            InfixSyntaxShape::Literal(t) => {
                match parts.last_mut() {
                    // GEN-1 B-3 (Stage S2/S3): a literal AFTER a `*sep`
                    // repetition part belongs to that repetition's CLOSE (the
                    // per-element loop owns the terminator), NOT to
                    // following_terminals — see `MixfixRep::close`.
                    Some(last) if last.repetition.is_some() => {
                        last.repetition
                            .as_mut()
                            .expect("repetition is_some in this arm")
                            .close
                            .push(t.clone());
                    },
                    // After the most-recent (non-rep) operand — append to its
                    // following_terminals.
                    Some(last) => last.following_terminals.push(t.clone()),
                    // Before any inner operand — accumulate as preceding for
                    // the next operand (or, if no operand ever appears, as the
                    // nullary literal run).
                    None => preceding_buffer.push(t.clone()),
                }
                idx += 1;
            },
            InfixSyntaxShape::Param(p) => {
                let (sname, sty) = simples.get(simple_idx)?;
                if sname != &p {
                    return None;
                }
                let scat = base_type_name(sty)?;
                parts.push(MixfixPart {
                    operand_category: scat,
                    param_name: p.to_string(),
                    preceding_terminals: std::mem::take(&mut preceding_buffer),
                    following_terminals: Vec::new(),
                    repetition: None,
                    // #131: an `m:Ident` param in an OPERAND-LEADING rule is a TOKEN
                    // CAPTURE, not a category operand. Rholang's collapsed method
                    // surface — `recv "." m "(" args.*sep(",") ")"` — is exactly this
                    // shape, and it is the whole reason the field exists.
                    //
                    // Before this, `base_type_name` yielded `"Ident"`, which is not a
                    // declared category, and the walker sub-parsed a category that does
                    // not exist: the rule had NO realizable reading and `# . f ( )`
                    // failed at every arity with a diagnostic that never mentioned
                    // `Ident`. See `MixfixPart::capture_kind` for why this is a field
                    // and not a variant, and why the kind is carried by name.
                    capture_kind: capture_kind_of(sty),
                });
                simple_idx += 1;
                idx += 1;
            },
            // GEN-1 B-3 C3 (Stage S2): `xs.*sep(s)` — a repetition operand.
            // The `*sep` consumes exactly one Simple param (`xs:Vec(elem)`);
            // push a repetition MixfixPart carrying the element category and
            // the separator. The CLOSE is filled by subsequent literals (see
            // the Literal arm above). Until the S3 walker handling lands, the
            // rep part is INERT: `mixfix_part(..)` returns None for it
            // (`emit_mixfix_parts_fn` skips rep parts) while
            // `mixfix_parts_len` still counts it, so a parse that reaches the
            // rep slot cleanly Errors (the fork dies, NO mis-parse).
            InfixSyntaxShape::Sep { collection, separator } => {
                // GEN-1 B-3 stage gate (Stage S3): classify the repetition operand
                // into a `MixfixRep` part UNLESS the rule's RESULT category is
                // excluded (the ForRow `&`-join — the root-caused S2 regression).
                // Returning `None` here leaves the whole rule unclassified, exactly
                // as at baseline. See [`gen1_rep_classify_enabled`].
                if !gen1_rep_classify_enabled(&result_cat) {
                    return None;
                }
                let (sname, sty) = simples.get(simple_idx)?;
                // The `*sep` collection name must be the next Simple param.
                if sname != &collection {
                    return None;
                }
                // Element category = the inner type of the `Vec(elem)` /
                // `HashBag(elem)` / … collection param.
                let elem_cat = match sty {
                    InfixTypeShape::Collection { element_base } => element_base.clone()?,
                    _ => return None,
                };
                parts.push(MixfixPart {
                    operand_category: elem_cat,
                    param_name: collection.to_string(),
                    preceding_terminals: std::mem::take(&mut preceding_buffer),
                    following_terminals: Vec::new(),
                    repetition: Some(MixfixRep {
                        separator: separator.clone(),
                        min: 0,
                        close: Vec::new(),
                    }),
                    // #131: a repetition accumulates CATEGORY operands, so it is never
                    // also a token capture. The two modes are orthogonal and both
                    // appear in `Call` — on DIFFERENT parts.
                    capture_kind: None,
                });
                simple_idx += 1;
                idx += 1;
            },
            _ => return None,
        }
    }
    // All simples must be consumed.
    if simple_idx != simples.len() {
        return None;
    }

    // GEN-1 B-1 (Stage S2): NULLARY path. No inner operand was parsed but the
    // pattern had post-trigger literals (now in `preceding_buffer`). Emit a
    // 0-operand mixfix: empty `mixfix_parts`, literals in `nullary_literals`.
    // The walker's `(2, None) if parts_len == 0` arm consumes them and fires
    // the arity-1 (LHS-only) action.
    if parts.is_empty() {
        if preceding_buffer.is_empty() {
            // Degenerate: LHS + trigger only (a plain postfix `a op`), which is
            // the 2-token postfix path's job (syntax_pattern.len() == 2 there);
            // here syntax_pattern.len() >= 3 with no operand and no literals is
            // impossible, but reject defensively.
            return None;
        }
        return Some(InfixRuleInfo {
            label: rule.label.to_string(),
            terminal: trigger,
            category: lhs_cat,
            result_category: result_cat,
            // A NULLARY mixfix (`n "!" "(" ")"`) has no operand after the trigger, so it
            // has no right edge for a chain to nest into and associativity is not
            // observable in its surface. See `classify_mixfix` for the shape where it is.
            associativity: Associativity::Left,
            shares_level_with_previous: rule.shares_level_with_previous,
            is_cross_category,
            is_postfix: false,
            is_mixfix: true,
            mixfix_parts: Vec::new(),
            nullary_literals: preceding_buffer,
        });
    }

    // preceding_buffer should be empty at end (literals after the last operand
    // were routed into its following_terminals or — for a rep — its close).
    if !preceding_buffer.is_empty() {
        return None;
    }

    Some(InfixRuleInfo {
        label: rule.label.to_string(),
        terminal: trigger,
        category: lhs_cat,
        result_category: result_cat,
        // A postfix-mixfix (`n "!" "(" q ")"`) closes with a literal, so its final
        // operand is delimited and the rule has no open right edge — associativity is
        // not observable. `classify_mixfix` handles the shape where it is.
        associativity: Associativity::Left,
        shares_level_with_previous: rule.shares_level_with_previous,
        is_cross_category,
        is_postfix: false,
        // Treated as mixfix for downstream dispatch — the widened
        // MixfixPart vectors carry the postfix-mixfix-specific terminal
        // sequences.
        is_mixfix: true,
        mixfix_parts: parts,
        nullary_literals: Vec::new(),
    })
}

fn classify_mixfix(
    rule: &InfixRuleShape,
    simples: &[(&String, &InfixTypeShape)],
    syntax_pattern: &[InfixSyntaxShape],
) -> Option<InfixRuleInfo> {
    if syntax_pattern.len() != 2 * simples.len() - 1 {
        return None;
    }
    let mut parts = Vec::new();
    let mut trigger: Option<String> = None;
    for (i, expr) in syntax_pattern.iter().enumerate() {
        if i % 2 == 0 {
            match expr {
                InfixSyntaxShape::Param(p) => {
                    let param_idx = i / 2;
                    let (pname, pty) = simples.get(param_idx)?;
                    if *pname != p {
                        return None;
                    }
                    if param_idx > 0 {
                        // #131: an `Ident` param here is a TOKEN CAPTURE, carried by
                        // `MixfixPart::capture_kind` and consumed one token at a time by
                        // the walker's mixfix part driver.
                        //
                        // ⚠ THE GUARD THAT USED TO STAND HERE IS GONE ON PURPOSE. It
                        // panicked at macro-expansion time because `MixfixPart` had no
                        // representation for a token consumption, so `base_type_name`
                        // yielded the non-category `"Ident"` and the walker sub-parsed a
                        // category that does not exist — the rule had no realizable
                        // reading at all. Making that LOUD was right while the shape was
                        // unsupported; keeping it once the shape IS supported would
                        // reject exactly the grammars the field was added to serve
                        // (Rholang's collapsed `EMethodCall`). `capture_kind_of` replaces
                        // the rejection with the representation.
                        let cat = base_type_name(pty)?;
                        // L12 follow-up B6 (2026-05-07): widened from
                        // `following_terminal: Option<String>` to vectors.
                        // For traditional mixfix the per-part separator
                        // appears as a single-element following_terminals
                        // vec; preceding_terminals stays empty (the trigger
                        // OR the previous part's following_terminals
                        // already consumed the literals before this operand).
                        let following = if i + 1 < syntax_pattern.len() {
                            if let InfixSyntaxShape::Literal(t) = &syntax_pattern[i + 1] {
                                vec![t.clone()]
                            } else {
                                return None;
                            }
                        } else {
                            Vec::new()
                        };
                        parts.push(MixfixPart {
                            operand_category: cat,
                            param_name: p.to_string(),
                            preceding_terminals: Vec::new(),
                            following_terminals: following,
                            repetition: None,
                            // #131: the classic-mixfix twin of the postfix-mixfix site.
                            // Both classifiers reach `capture_kind_of` so a rule's
                            // reading does not depend on WHICH classifier claimed it —
                            // the very asymmetry that made `Tagged` (literal-leading,
                            // binder path) green while `Call` (operand-leading, Pratt
                            // path) had no realizable reading at all.
                            capture_kind: capture_kind_of(pty),
                        });
                    }
                },
                // GEN-1 B-3 (Stage S2): a `*sep` repetition operand at an even
                // (operand) position makes this rule defer to
                // `classify_postfix_mixfix`, which owns the repetition-part
                // construction (single canonical path). Returning None here lets
                // the caller fall through to that classifier.
                _ => return None,
            }
        } else {
            match expr {
                InfixSyntaxShape::Literal(t) => {
                    if i == 1 {
                        trigger = Some(t.clone());
                    }
                },
                _ => return None,
            }
        }
    }
    let trigger = trigger?;
    let (_, lhs_ty) = simples[0];
    let lhs_cat = base_type_name(lhs_ty)?;
    let result_cat = rule.category.to_string();
    let is_cross_category = lhs_cat != result_cat;

    // ★ MIXFIX ASSOCIATIVITY (2026-07-28) — this used to be a hard-coded
    // `Associativity::Left`, which silently DROPPED a declared `right` on every mixfix
    // rule. `Tern` (`c "?" t ":" e … step right` in Calculator) is exactly such a rule,
    // and `macros/src/gen/syntax/display.rs` honours the declaration, so the printer and
    // this table disagreed about what the same grammar meant.
    //
    // Associativity is a property of the rule's RIGHT EDGE — it decides how a chain of
    // the operator nests, which is only observable when the FINAL operand is open on the
    // right. It is derived here rather than assumed: a mixfix whose last part is followed
    // by a literal (`n "!" "(" q ")"`) is self-delimiting, and `right` on such a rule has
    // no chain to re-nest. The ternary's last part (`e`) has no following terminal, so it
    // does, and `1 ? 2 : 0 ? 3 : 4` reads `1 ? 2 : (0 ? 3 : 4)`.
    let has_open_right_edge = parts
        .last()
        .is_some_and(|part| part.following_terminals.is_empty());

    Some(InfixRuleInfo {
        label: rule.label.to_string(),
        terminal: trigger,
        category: lhs_cat,
        result_category: result_cat,
        associativity: if rule.is_right_assoc && has_open_right_edge {
            Associativity::Right
        } else {
            Associativity::Left
        },
        shares_level_with_previous: rule.shares_level_with_previous,
        is_cross_category,
        is_postfix: false,
        is_mixfix: true,
        mixfix_parts: parts,
        nullary_literals: Vec::new(),
    })
}

fn base_type_name(ty: &InfixTypeShape) -> Option<String> {
    match ty {
        InfixTypeShape::Base(ident) => Some(ident.to_string()),
        _ => None,
    }
}

/// #131: the TOKEN KIND a mixfix part must consume, or `None` if the part is an
/// ordinary category operand.
///
/// This is the SINGLE decision point that turns a declared param type into
/// [`MixfixPart::capture_kind`]. It answers exactly one question — "does this
/// param consume a token instead of naming a category?" — and it answers it from
/// [`InfixTypeShape::is_ident_text`], equivalent to the AST predicate that the
/// binder path uses to route `m:Ident` to `BinderPosition::IdentTextCapture`.
/// Both paths therefore agree on
/// what an identifier param IS, which is what lets the LITERAL-leading rule
/// (`Tagged . m:Ident |- "tag" m`) and the OPERAND-leading rule
/// (`Call . recv:Num, m:Ident, … |- recv "." m …`) deliver the same `String` field
/// through two different machines.
///
/// The returned name is resolved at parse time by the walker's `capture_kind`,
/// which maps `"Ident"` to the builtin `TokenKind::Ident` the lexer actually
/// emits (commit `ac46362b`) — NOT to `TokenKind::Custom("Ident")`, which no lexer
/// ever produces and which would leave the gate permanently dead.
fn capture_kind_of(ty: &InfixTypeShape) -> Option<String> {
    match ty.is_ident_text() {
        true => Some(IDENT_CAPTURE_KIND_NAME.to_string()),
        false => None,
    }
}

/// The token-kind name a builtin-`Ident` mixfix capture demands. See
/// [`capture_kind_of`] for why it is spelled exactly once.
pub const IDENT_CAPTURE_KIND_NAME: &str = "Ident";

/// GEN-1 B-3 repetition-classification stage gate (Stage S3, 2026-06-28).
///
/// Per-RESULT-category compile-time gate (consistent with the `GEN1_MAX_SLICE`
/// kill-switch pattern: a `const` resolved at macro expansion, NOT a runtime env
/// var) selecting which `xs.*sep(s)` repetition operands — in Param-prefixed
/// rules routed through [`classify_postfix_mixfix`] — are classified into a
/// [`MixfixRep`] part and driven by the B-3 walker. A rule whose RESULT category
/// appears here keeps the pre-S3 behavior: its `*sep` operand is NOT classified
/// (the `Op(Sep)` arm returns `None`), so the rule stays unclassified EXACTLY as
/// at baseline — regression-free.
///
/// EXCLUDED — `ForRow`. The InputBind→ForRow cross-cat `&`-join repetition rules
/// (`ForRowWhere` / `ForRowNoWhere` / `ForRowPersistentWhere` /
/// `ForRowPersistentNoWhere` — all `… "&" bs.*sep("&") …`, result category
/// `ForRow`, LHS category InputBind or Name) REGRESS 6 pattern-COMM / quoted-bind
/// tests when classified — EVEN with the repetition INERT. The breakage is
/// PRESENCE-based: registering them as `&`- (or `<=`-) triggered mixfix operators
/// on the InputBind / Name tiers removes the valid derivation of
/// quoted-collection pattern binds `for(@[..]/@#{..}# <- c){…}` (cursors reach the
/// body but no branch accepts at EOF). Root-caused by the S2 bisect: enabling rep
/// classification GLOBALLY gave 6 regressions — `comm::pattern_comm_{bag,list}_`
/// `literal_pattern_{matches,blocks_mismatch}`,
/// `comm::join_pattern_mismatch_is_noop_for_receive_group`,
/// `parsing::quoted_plain_bind_parses` — while gating `ForRow` OUT removes all 6
/// AND classifies the safe set cleanly (POutput2Plus / PPersistOutput2Plus →
/// `Proc`; InputBind query / polyadic binds → `InputBind`). See
/// `scratchpad/s1-s3-gate.log`.
///
/// This is a STAGE BOUNDARY, not a permanent exclusion: a separate ForRow fix
/// (co-designing the `&`-join classification + dispatch so it does not disturb the
/// InputBind→ForRow projection) lands the join, at which point `ForRow` is removed
/// from this list. Full B-3 revert = add every rep-bearing result category
/// (`"Proc"`, `"InputBind"`, `"ForRow"`) here, or restore the pre-S3 snapshot.
///
/// F1 (2026-06-28): `ForRow` REMOVED — the `&`-join rules (`ForRowWhere` /
/// `ForRowNoWhere` / `ForRowPersistentWhere` / `ForRowPersistentNoWhere`) now
/// classify. The 6 pattern-COMM / quoted-bind regressions that this caused at S2
/// are now prevented by the F0 cross-cat-LHS PUSH-gate (forks.rs +
/// `prefix_crosscat_lhs_trigger_ahead_scoped` + `crosscat_lhs_has_projection_fallback`,
/// kind_dispatch.rs): a triggerless quoted-collection bind (`for(@[..]<-c){…}`)
/// has the `InputBind→ForRow` projection fallback (`ForRowSingleNoWhere`), so its
/// EXTENSION delegate is suppressed and it parses projection-only — exactly the
/// pre-S2 derivation. The classified `&`-rep itself stays INERT until the §4.5
/// no-close repetition walker (F2) lands; until then an `&`-join parses its first
/// bind, forks on `&`, and cleanly Errors at the rep slot (no mis-parse).
const GEN1_REP_CLASSIFY_EXCLUDED_CATEGORIES: &[&str] = &[];

/// Compile-time per-result-category gate for GEN-1 B-3 repetition classification
/// (see [`GEN1_REP_CLASSIFY_EXCLUDED_CATEGORIES`]). Returns `true` when a `*sep`
/// repetition operand in a rule producing `result_category` may be classified
/// into a [`MixfixRep`] part.
fn gen1_rep_classify_enabled(result_category: &str) -> bool {
    !GEN1_REP_CLASSIFY_EXCLUDED_CATEGORIES.contains(&result_category)
}
