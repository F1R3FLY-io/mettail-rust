//! ★★★ (#195) **Withheld congruence propagation** — the derivation of the SEVERED
//! POSITION SET from the declarations, and the typed refusal of every declaration the
//! e-graph lane cannot honour.
//!
//! # 1. The problem this module exists to solve
//!
//! A *congruence* is the inference rule that closes a rewrite relation under a context:
//! `| S ~> T |- (Add S X) ~> (Add T X)` says "if `S` steps to `T` then `Add S X` steps to
//! `Add T X`". A position at which the relation is closed is an **evaluation context**.
//!
//! Before #195, congruence propagation on the Dovetail e-graph lane had **two** states —
//! *declared* and *undeclared* — and they were **indistinguishable in behaviour**.
//! `languages/tests/congruence_declaration_witness.rs` measured it, in both directions:
//!
//! | probe | congruence declared | source | dovetail-normal | reduced? |
//! |---|---|---|---|---|
//! | ZERO | n/a (kernel) | `*@(1)` | `1` | YES |
//! | SUBJECT | **YES** `AddCong` | `*@(1) + 2` | `3` | YES |
//! | CONTROL | **NO** `POutput` | `@(0)!(*@(1))` | `@0!(1)` | **YES** |
//! | SEVERED | **NO** `CastList` | `[*@(1), 2]` | `[*@1, 2]` | **NO** |
//!
//! *Different declaredness, identical behaviour* (SUBJECT/CONTROL); *identical
//! declaredness, different behaviour* (CONTROL/SEVERED). Together those force one
//! conclusion: **the reach of the e-graph lane was decided by what a field lowers to — its
//! carrier — and never by the declaration.** An author who wanted to say "propagation
//! stops here" had no way to say it: withholding read exactly like having no opinion.
//!
//! # 2. Why the fix is a THIRD STATE and not "honour the declarations"
//!
//! Making only-declared positions propagate would break the thing that must keep working:
//! **inference**. `ast/src/auto_inject.rs` synthesizes `<Source>To<Target>Cong` rules so a
//! chain of numeric casts propagates with no declaration at all, and the intrinsic e-graph
//! closure is what makes an undeclared position behave sensibly. So the default stays
//! *inferred closure*, and the new state is the **declared refusal**:
//!
//! | author's intent | spelling | outcome |
//! |---|---|---|
//! | propagate here | `\| S ~> T \|-` | honoured, or **refused by name** if unreachable |
//! | infer it; no opinion | declare nothing | the intrinsic closure — the sensible default |
//! | **withhold propagation** | `\| S ~/> T \|-` | the position is **severed** |
//!
//! # 3. ★ Theorem W1 — withholding REQUIRES severance (there is no other realization)
//!
//! An e-graph's e-node identity is the pair `(operator, canonical child e-class ids)`, and
//! its hashcons maps that pair to an e-class. Suppose position `i` of operator `f` holds a
//! child e-class id, and suppose `a` and `b` are merged (`find(a) = find(b)`). Then the
//! canonical child vectors of `f(…a…)` and `f(…b…)` are *equal*, so the two e-nodes are
//! **the same key**, so they inhabit **the same e-class**. Propagation through position `i`
//! is therefore not a policy the engine applies — it is an identity the data structure
//! *is*. Hence:
//!
//! > **For an e-graph to withhold propagation at a position, that position must not hold a
//! > child e-class id.**
//!
//! The machine-checked statement and proof are in
//! `dovetail/formal/rocq/theories/Lowering/CongruenceWithholding.v`
//! (`withholding_requires_severance`, `severance_removes_exactly_the_withheld_edges`),
//! which also records **why the property
//! the defect report first proposed is FALSE**: "the e-graph's equivalence equals the
//! declared-plus-inferred closure minus the withheld edges" cannot hold for *any* e-graph,
//! because the right-hand side is not a congruence and an e-graph's quotient always is.
//!
//! Severing a position means lowering the field to a **payload-verbatim leaf**: the value
//! travels whole, inside one nullary e-node, so it is not an e-class, no rule can match
//! inside it, and 1-best extraction cannot substitute a rewritten member for it. That is
//! exactly the carrier the SEVERED probe already measured — `dovetail_report`'s
//! `CollectionCarrier::OrderedSeq`/`Opaque` leaves — reused deliberately rather than
//! reinvented.
//!
//! # 4. What this module computes
//!
//! [`classify_withholdings`] walks `language.rewrites` once and returns
//! [`WithholdingSet`], which answers exactly two questions:
//!
//!  * [`WithholdingSet::is_severed`] — "is `(constructor, field_index)` severed?", read by
//!    `typed_lowering::field_child_expr_typed` and by `super::field_child_expr`;
//!  * [`WithholdingSet::refusals`] — every declaration the lane cannot honour, each
//!    carrying the reason, emitted as a `compile_error!` so an unhonourable declaration
//!    **cannot ship silently**.
//!
//! ⚠ The position is **DERIVED from the declaring rule's own LHS pattern**, never
//! transcribed. `| S ~/> T |- (POutput N S) ~> (POutput N T)` names `POutput` field 1
//! because `S` occupies `args[1]`. There is no list of positions to keep in sync with the
//! grammar, which is the failure mode "*complete the list* is not a repair" names.

use mettail_ast::language::{LanguageDef, RewriteRule};
use mettail_ast::pattern::{Pattern as AstPattern, PatternTerm};
use syn::Ident;

use crate::gen::runtime::disposition::LoweringDisposition;
use crate::gen::term_ops::subst::FieldInfo;
use mettail_runtime::{LoweredConstructKind, LoweredConstructOrigin};

/// ★ One position the author declared **not** to be an evaluation context.
///
/// Identified by `(constructor, field_index)` — the coordinates the e-graph lowering keys
/// its field emission on — plus the declaring rule's name, so every diagnostic can point
/// at the declaration that caused the severance rather than at the position in isolation.
#[derive(Debug, Clone)]
pub(crate) struct WithheldPosition {
    /// The name of the `| S ~/> T |-` rule that declared this withholding.
    pub(crate) rule: String,
    /// The constructor whose field is severed (the grammar rule label, e.g. `POutput`).
    pub(crate) constructor: String,
    /// The field's positional index within that constructor.
    pub(crate) field_index: usize,
    /// The field's declared category (`Proc`, `Name`, …). The severed leaf's op-enum
    /// variant is per-category, so this is what earns a `FieldWithheld<Cat>` variant.
    pub(crate) category: Ident,
}

/// ★ A declaration the e-graph lane **cannot honour**, with the reason.
///
/// Emitted as a `compile_error!`, never dropped. A withholding the lane silently ignored
/// would be the exact defect #195 fixes, reintroduced one level up: a declaration that
/// reads as load-bearing and is not.
#[derive(Debug, Clone)]
pub(crate) struct WithholdingRefusal {
    /// The declaring rule's name.
    pub(crate) rule: String,
    /// Why the lane cannot honour it — a full sentence, naming the shape.
    pub(crate) reason: String,
}

/// The derived answer to "which positions are severed, and which declarations were
/// refused?" for one language.
#[derive(Debug, Clone, Default)]
pub(crate) struct WithholdingSet {
    positions: Vec<WithheldPosition>,
    refusals: Vec<WithholdingRefusal>,
}

impl WithholdingSet {
    /// Whether `(constructor, field_index)` is a severed position.
    ///
    /// ⚠ Read by BOTH e-graph lowerings (typed and `EGraph<String>`) so the two cannot
    /// disagree about which fields are severed.
    pub(crate) fn is_severed(&self, constructor: &Ident, field_index: usize) -> bool {
        let label = constructor.to_string();
        self.positions
            .iter()
            .any(|p| p.constructor == label && p.field_index == field_index)
    }

    /// The severed position matching `(constructor, field_index)`, if any.
    pub(crate) fn position(
        &self,
        constructor: &Ident,
        field_index: usize,
    ) -> Option<&WithheldPosition> {
        let label = constructor.to_string();
        self.positions
            .iter()
            .find(|p| p.constructor == label && p.field_index == field_index)
    }

    /// Every severed position, in declaration order.
    pub(crate) fn positions(&self) -> &[WithheldPosition] {
        &self.positions
    }

    /// Every refused declaration, in declaration order.
    pub(crate) fn refusals(&self) -> &[WithholdingRefusal] {
        &self.refusals
    }

    /// Whether this language declares any withholding at all — severed or refused.
    ///
    /// ★ Includes REFUSALS deliberately: `super::needs_typed_dovetail_path` consults this
    /// to route a withholding language to the typed path (where the invertible carrier
    /// lives), and a language whose only withholding was refused must still take that
    /// route so its `compile_error!` is emitted on the path that produced it.
    pub(crate) fn is_empty(&self) -> bool {
        self.positions.is_empty() && self.refusals.is_empty()
    }

    /// Every category that earns a `FieldWithheld<Cat>` op-enum variant, deduplicated, in
    /// first-declaration order.
    ///
    /// ★ THE single predicate deciding which `FieldWithheld*` variants exist — read by the
    /// enum emitter (`op_enum::collect_op_variants`), the lowering
    /// (`typed_lowering::field_child_expr_typed`) and the inverse
    /// (`reconstruct::withheld_reconstruct`), exactly as
    /// `op_enum::ordered_seq_element_categories` is for `FieldSeq*`. Three readers, one
    /// derivation, so a leaf can never name a variant the enum does not have.
    pub(crate) fn earned_categories(&self) -> Vec<Ident> {
        let mut out: Vec<Ident> = Vec::with_capacity(self.positions.len());
        for position in &self.positions {
            if !out.iter().any(|seen| *seen == position.category) {
                out.push(position.category.clone());
            }
        }
        out
    }

    /// `compile_error!` tokens for every refusal, in declaration order.
    pub(crate) fn refusal_errors(&self) -> Vec<proc_macro2::TokenStream> {
        self.refusals
            .iter()
            .map(|refusal| {
                let message = format!(
                    "#195: rewrite `{}` declares a WITHHELD congruence (`| S ~/> T |-`) the \
                     Dovetail e-graph lane cannot honour: {}\n\nA withholding is honoured by \
                     SEVERING the named position — lowering that field to a payload-verbatim \
                     leaf so it is not an e-class (see `macros/docs/codegen/\
                     congruence-closure.md`, Theorem W1). Severance is defined for a plain \
                     scalar category field of a `Regular` constructor. Rather than accept the \
                     declaration and quietly not honour it — which is exactly the defect #195 \
                     repairs — the generator refuses it here.",
                    refusal.rule, refusal.reason
                );
                quote::quote! { compile_error!(#message); }
            })
            .collect()
    }

    /// One [`LoweringDisposition`] per severed position and per refusal, so the reflected
    /// metadata records what the lane did with every withholding declaration.
    pub(crate) fn dispositions(&self) -> Vec<LoweringDisposition> {
        let mut out = Vec::with_capacity(self.positions.len() + self.refusals.len());
        for position in &self.positions {
            out.push(LoweringDisposition::suppressed(
                LoweredConstructKind::Rewrite,
                position.rule.clone(),
                LoweredConstructOrigin::Declared,
                format!(
                    "withheld congruence honoured by SEVERANCE: `{}` field {} ({}) lowers to a \
                     payload-verbatim `FieldWithheld{}` leaf, so it is not an e-class and \
                     propagation cannot reach it; no rewrite rule is emitted because the \
                     declaration denies an inference rather than adding one",
                    position.constructor,
                    position.field_index,
                    position.category,
                    position.category,
                ),
            ));
        }
        for refusal in &self.refusals {
            out.push(LoweringDisposition::declined(
                LoweredConstructKind::Rewrite,
                refusal.rule.clone(),
                LoweredConstructOrigin::Declared,
                format!("withheld congruence cannot be honoured: {}", refusal.reason),
                true,
            ));
        }
        out
    }
}

/// ★★ Walk `language.rewrites` and classify every `| S ~/> T |-` declaration.
///
/// # Literate description of the classifier
///
/// The declaration names its position *structurally*: the source metavariable `S` occupies
/// one argument slot of the LHS constructor application. The classifier therefore reads the
/// pattern rather than any auxiliary list.
///
/// ```pseudocode
/// procedure CLASSIFY-WITHHOLDINGS(language)
///   positions ← ⟨⟩ ; refusals ← ⟨⟩
///   for each rewrite rw in language.rewrites do
///     (S, T) ← WITHHELD-CONGRUENCE-PREMISE(rw)          ▷ absent ⇒ not a withholding
///     if absent then continue
///     if rw also carries `S ~> T` then                   ▷ assert and deny at once
///       REFUSE(rw, "carries both polarities")            ▷ (rejected at parse time too)
///     (ctor, args) ← APPLY-HEAD(rw.left)                 ▷ else REFUSE: LHS not an application
///     i ← the unique j with args[j] = Var(S)             ▷ else REFUSE: 0 or ≥2 occurrences
///     kind ← VARIANT-KIND(language, ctor)                ▷ the AST shape the codegen built
///     require kind = Regular{label = ctor, fields}       ▷ else REFUSE, naming the shape
///     require |args| = |fields|                          ▷ else REFUSE: arity disagreement
///     f ← fields[i]
///     require SEVERABLE(f)                               ▷ else REFUSE, naming the reason
///     positions ← positions ⌢ ⟨(rw.name, ctor, i, f.category)⟩
///   return (positions, refusals)
/// ```
///
/// `SEVERABLE(f)` holds exactly when the field is a plain category child — the positions
/// whose lowering is `__mettail_dovetail_add_<cat>(eg, …)`, i.e. precisely the positions
/// that hold a child e-class id and therefore the only ones Theorem W1 says severance
/// applies to.
///
/// ★ EVERY refusal path is a *named* refusal. There is deliberately no arm that returns
/// "not a withholding" for a rule that carries the premise: a declaration is either
/// honoured or refused out loud.
pub(crate) fn classify_withholdings(language: &LanguageDef) -> WithholdingSet {
    let mut set = WithholdingSet::default();
    for rewrite in &language.rewrites {
        let Some((source, _target)) = rewrite.withheld_congruence_premise() else {
            continue;
        };
        let rule = rewrite.name.to_string();
        match classify_one(language, rewrite, source) {
            Ok(mut position) => {
                position.rule = rule;
                set.positions.push(position);
            },
            Err(reason) => set.refusals.push(WithholdingRefusal { rule, reason }),
        }
    }
    set
}

/// Classify ONE withholding declaration: either the severable position it names, or the
/// reason the lane cannot honour it.
fn classify_one(
    language: &LanguageDef,
    rewrite: &RewriteRule,
    source: &Ident,
) -> Result<WithheldPosition, String> {
    if rewrite.is_congruence_rule() {
        return Err(format!(
            "it carries BOTH polarities for this position — a `{source} ~> {source}'` premise \
             asserting the inference and a `{source} ~/> …` premise denying it. Keep exactly one."
        ));
    }

    let AstPattern::Term(PatternTerm::Apply { constructor, args }) = &rewrite.left else {
        return Err(
            "its left-hand side is not a constructor application `(C … S …)`, so there is no \
             `(constructor, field)` position to sever. Spell the withholding as the inference it \
             denies, e.g. `| S ~/> T |- (POutput N S) ~> (POutput N T)`"
                .to_string(),
        );
    };

    let occurrences: Vec<usize> = args
        .iter()
        .enumerate()
        .filter(|(_, arg)| is_exactly_var(arg, source))
        .map(|(index, _)| index)
        .collect();
    let field_index = match occurrences.as_slice() {
        [only] => *only,
        [] => {
            return Err(format!(
                "the withheld metavariable `{source}` is not a DIRECT argument of `{constructor}`. \
                 Severance applies to one field of one constructor; a metavariable nested inside a \
                 collection, a binder, or an inner application names no single scalar position"
            ));
        },
        many => {
            return Err(format!(
                "the withheld metavariable `{source}` occupies {} argument positions of \
                 `{constructor}` ({:?}). A withholding must name exactly one position, so write \
                 one declaration per position",
                many.len(),
                many
            ));
        },
    };

    // ★ SHARED with `congruence_position_unreachable`, deliberately: the two polarities
    // must analyse a position the SAME way, or a position could be "not severable" for a
    // withholding while being "reachable" for a congruence — a contradiction the compiler
    // would not catch if each polarity had its own lookup.
    let Some(fields) = super::regular_constructor_fields(language, constructor) else {
        return Err(format!(
            "`{constructor}` is not a `Regular` constructor of any declared category, so it has \
             no positional field list to sever. Severance is defined for a plain scalar category \
             field; a collection constructor's elements share ONE carrier leaf and a binder's \
             body lives inside a `Scope`, so neither has an independent per-field carrier"
        ));
    };

    if args.len() != fields.len() {
        return Err(format!(
            "`{constructor}` was declared with {} argument(s) in this rule but its AST shape has \
             {} field(s), so argument position {field_index} cannot be aligned with a field. Fix \
             the rule's arity",
            args.len(),
            fields.len()
        ));
    }

    let field = &fields[field_index];
    severable(field).map_err(|why| {
        format!("`{constructor}` field {field_index} is not a severable position: {why}")
    })?;

    Ok(WithheldPosition {
        // Overwritten by the caller, which owns the rule name.
        rule: String::new(),
        constructor: constructor.to_string(),
        field_index,
        category: field.category.clone(),
    })
}

/// Whether `pattern` is EXACTLY the metavariable `name` — not a pattern containing it.
///
/// ⚠ The distinction is the whole classifier: `(POutput N S)` severs field 1, while
/// `(POutput N (PPar {S, ...rest}))` names no scalar position and is refused.
fn is_exactly_var(pattern: &AstPattern, name: &Ident) -> bool {
    matches!(pattern, AstPattern::Term(PatternTerm::Var(var)) if var == name)
}

/// Whether a field holds a child e-class id — the only kind of position Theorem W1's
/// severance applies to — or the reason it does not.
///
/// ★ MIRRORS `typed_lowering::field_child_expr_typed`'s branch order exactly, and must:
/// severance replaces the `__mettail_dovetail_add_<cat>(eg, …)` fall-through, so a field
/// that never reaches that fall-through has no child e-class id to sever, and refusing it
/// is the honest answer rather than emitting a leaf nothing reads.
fn severable(field: &FieldInfo) -> Result<(), String> {
    use mettail_ast::grammar::NonTerminalKind;
    if NonTerminalKind::classify(&field.category.to_string()).is_builtin() {
        return Err(format!(
            "it is a BUILTIN (`{}`), which already lowers to a `FieldOpaque` leaf. It holds no \
             child e-class, so propagation never reached it and there is nothing to withhold",
            field.category
        ));
    }
    if field.is_predicate {
        return Err(
            "it is a semantic-predicate slot (`?g:Guard`), which lowers to a `FieldOpaque` leaf. \
             It holds no child e-class, so there is nothing to withhold"
                .to_string(),
        );
    }
    if field.is_opaque_leaf() {
        return Err(
            "it is a capture leaf (a `v@Tok` token text or a `*flt` guest body), which lowers to \
             a `FieldTokenText`/`FieldOpaque` leaf. It holds no child e-class, so there is \
             nothing to withhold"
                .to_string(),
        );
    }
    if field.is_collection {
        return Err(
            "it is a COLLECTION field. Its container already lowers to ONE carrier — an AC bag \
             node or a `FieldSeq`/`FieldOpaque` leaf — so its elements are governed as a group, \
             not per position. Withholding one element is not expressible; withhold the whole \
             field by declaring its container `HashSet`/`HashMap`, or withhold the enclosing \
             scalar position instead"
                .to_string(),
        );
    }
    if field.is_optional {
        return Err(
            "it is an OPTIONAL field (`#opt(…)`). Its present arm holds a child e-class and its \
             absent arm is a `FieldNone` sentinel, so severance would need a two-arm carrier and \
             a two-arm inverse. Not implemented — and refused rather than silently half-honoured"
                .to_string(),
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use mettail_ast::language::LanguageDef;

    fn parse(src: &str) -> LanguageDef {
        syn::parse_str::<LanguageDef>(src).expect("language must parse")
    }

    /// The BASELINE: a language with no withholding derives an EMPTY set, so every
    /// pre-#195 language's lowering is byte-identical. Without this row a bug that
    /// severed everything would still look like a pass on the rows below.
    #[test]
    fn no_withholding_declares_no_severed_position() {
        let language = parse(
            r#"
                name: NoWithholding,
                types { Proc }
                terms {
                    PZero . |- "0" : Proc ;
                    PPair . a:Proc, b:Proc |- "<" a "," b ">" : Proc ;
                }
                equations {}
                rewrites {
                    Kill . |- (PPair PZero PZero) ~> PZero ;
                    PairCongL . | S ~> T |- (PPair S X) ~> (PPair T X) ;
                }
            "#,
        );
        let set = classify_withholdings(&language);
        assert!(set.is_empty(), "no `~/>` declared ⇒ nothing severed, nothing refused");
        assert!(set.earned_categories().is_empty());
    }

    /// The SUBJECT: a withholding on a plain scalar field derives exactly that position.
    #[test]
    fn a_scalar_field_withholding_derives_its_position() {
        let language = parse(
            r#"
                name: ScalarWithholding,
                types { Proc }
                terms {
                    PZero . |- "0" : Proc ;
                    PPair . a:Proc, b:Proc |- "<" a "," b ">" : Proc ;
                }
                equations {}
                rewrites {
                    Kill . |- (PPair PZero PZero) ~> PZero ;
                    PairRightWithheld . | S ~/> T |- (PPair X S) ~> (PPair X T) ;
                }
            "#,
        );
        let set = classify_withholdings(&language);
        assert!(set.refusals().is_empty(), "refusals: {:#?}", set.refusals());
        assert_eq!(set.positions().len(), 1);
        let position = &set.positions()[0];
        assert_eq!(position.rule, "PairRightWithheld");
        assert_eq!(position.constructor, "PPair");
        assert_eq!(position.field_index, 1, "`S` occupies args[1]");
        assert_eq!(position.category.to_string(), "Proc");
        assert!(set.is_severed(&position_ident("PPair"), 1));
        assert!(
            !set.is_severed(&position_ident("PPair"), 0),
            "★ the SIBLING position must stay unsevered — severance is per position, and a \
             withholding that severed the whole constructor would make this test's own \
             three-state claim vacuous"
        );
    }

    fn position_ident(name: &str) -> Ident {
        Ident::new(name, proc_macro2::Span::call_site())
    }

    /// A withholding whose metavariable is nested inside a collection names no scalar
    /// position, and is REFUSED BY NAME rather than ignored.
    #[test]
    fn a_nested_withholding_is_refused_by_name() {
        let language = parse(
            r#"
                name: NestedWithholding,
                types { Proc }
                terms {
                    PZero . |- "0" : Proc ;
                    PPar . ps:HashBag(Proc) |- "{" ps "}" : Proc ;
                }
                equations {}
                rewrites {
                    ParWithheld . | S ~/> T |- (PPar {S, ...rest}) ~> (PPar {T, ...rest}) ;
                }
            "#,
        );
        let set = classify_withholdings(&language);
        assert!(set.positions().is_empty(), "nothing severable here");
        assert_eq!(set.refusals().len(), 1);
        assert_eq!(set.refusals()[0].rule, "ParWithheld");
        assert!(
            set.refusals()[0].reason.contains("not a DIRECT argument")
                || set.refusals()[0]
                    .reason
                    .contains("no positional field list"),
            "the refusal must NAME the shape: {}",
            set.refusals()[0].reason
        );
        assert!(!set.is_empty(), "a refused withholding still routes the language typed");
        assert_eq!(set.refusal_errors().len(), 1, "and emits one `compile_error!`");
    }

    /// A rule carrying BOTH polarities asserts and denies the same inference; refused.
    #[test]
    fn both_polarities_at_once_is_refused() {
        let language = parse(
            r#"
                name: BothPolarities,
                types { Proc }
                terms {
                    PZero . |- "0" : Proc ;
                    PPair . a:Proc, b:Proc |- "<" a "," b ">" : Proc ;
                }
                equations {}
                rewrites {
                    Confused . | S ~> T, S ~/> T |- (PPair S X) ~> (PPair T X) ;
                }
            "#,
        );
        let set = classify_withholdings(&language);
        assert!(set.positions().is_empty());
        assert_eq!(set.refusals().len(), 1);
        assert!(
            set.refusals()[0].reason.contains("BOTH polarities"),
            "reason: {}",
            set.refusals()[0].reason
        );
    }

    /// A withholding on a builtin-typed field has no child e-class to sever; refused with
    /// the reason, so the author learns propagation never reached it in the first place.
    #[test]
    fn a_builtin_field_withholding_is_refused_because_it_was_never_a_child() {
        let language = parse(
            r#"
                name: BuiltinWithholding,
                types { Proc, ![i64] as Int }
                terms {
                    PZero . |- "0" : Proc ;
                    PLit . n:Int, p:Proc |- "lit" n p : Proc ;
                }
                equations {}
                rewrites {
                    LitWithheld . | S ~/> T |- (PLit S P) ~> (PLit T P) ;
                }
            "#,
        );
        let set = classify_withholdings(&language);
        assert!(set.positions().is_empty());
        assert_eq!(set.refusals().len(), 1);
        assert!(
            set.refusals()[0].reason.contains("BUILTIN")
                || set.refusals()[0].reason.contains("nothing to withhold"),
            "reason: {}",
            set.refusals()[0].reason
        );
    }
}
