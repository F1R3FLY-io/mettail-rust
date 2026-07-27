//! ★ SURFACE SYNONYMY — one denotation, one surface.
//!
//! # The defect this module exists to make impossible
//!
//! A grammar may spell the SAME term more than one way. Rholang spells a quoted name three:
//!
//! ```text
//!   NQuote      . p:Proc |- "@" "(" p ")" : Name ;
//!   NQuoteShort . p:Proc |- "@" p         : Name ![{ Name::NQuote(Arc::new(p.clone())) }] fold prefix(220) canonical;
//!   NQuoteNil   .        |- "@" "Nil"     : Name ![{ Name::NQuote(Arc::new(Proc::PZero)) }] fold;
//! ```
//!
//! All three are the same `Name`; the last two say so in their own fold bodies. Each is a
//! DISTINCT surface constructor in the AST, and before this module each rendered ITS OWN
//! surface. That makes `Display` a function of the constructor rather than of the term, and
//! composing it with `Parse` — which elects a constructor from a surface — is then not a
//! fixpoint:
//!
//! ```text
//!   (@(error)) <- @Nil  ──parse──▶  InputBind(NQuote(Err), NQuoteShort(PZero))
//!                       ──display─▶ @(error) <- @Nil
//!                       ──parse──▶  InputBindQuoted(Err, NQuoteShort(PZero))
//!                       ──display─▶ @error <- @Nil          ← a THIRD surface
//!                       ──parse──▶  InputBindQuoted(Err, NQuoteShort(PZero))
//!                       ──display─▶ @error <- @Nil          ← fixpoint, one layer too late
//! ```
//!
//! One surface is shed per nesting layer, so `gen_rholang_prop::inputbind_display_parse_roundtrip`
//! (which asserts `D(P(D(P(D(t))))) == D(P(D(t)))`, i.e. a fixpoint after ONE re-parse) fails on
//! every term whose synonym sits two layers deep.
//!
//! # ★ Why the canonical member is DECLARED and not inferred
//!
//! The obvious repair — *"render the member the parser itself would elect"* — was REFUTED by
//! measurement (2026-07-26). Two candidate mechanisms, both killed:
//!
//! | hypothesis | measurement | verdict |
//! |---|---|---|
//! | `parse_structured` falls back to a different member than `parse_via_wpda` | the two agree EXACTLY on every probe input | refuted |
//! | the election prefers the inert grouping (`NParen`) | at `Name` level it DOES prefer `NParen`; inside `InputBind` the SAME substring elects `NQuoteShort` | refuted |
//!
//! The surviving mechanism is that **the election is CONTEXT-DEPENDENT**: the same substring
//! elects `NParen(NQuote(…))` standing alone and `NQuoteShort(…)` inside an `InputBind`, and
//! `Display` faithfully renders whichever it got. So "the parser's own election order" is *not a
//! function of the synonymy class* and cannot name a canonical member — no amount of inference
//! from the parser can produce a context-free answer to a context-free question.
//!
//! The grammar can. `canonical` is a rule annotation (`GrammarRule::is_canonical_synonym`), and
//! `Display` renders every member of the class through it. `D(P(D(t))) = D(t)` then holds
//! INDEPENDENTLY of parse context, which is exactly what a context-dependent election cannot give.
//!
//! # The two shapes, and why they are different in kind
//!
//! ```text
//!   ┌──────────────────── ALIAS CLASS ────────────────────┐   ┌──── INERT GROUPING ────┐
//!   │                                                     │   │                        │
//!   │   NQuoteShort ──fold──▶ NQuote ◀──fold── NQuoteNil   │   │  NParen(n)  ≡  n       │
//!   │       (renaming: NQuote(p)  ⇒ inverse [0])           │   │  ("(" n ")", body n)   │
//!   │       (partial : NQuote(PZero) ⇒ no inverse)         │   │                        │
//!   │                                                     │   │  canonical member = the│
//!   │   canonical member = a DECLARED rule of the class    │   │  WRAPPED TERM — there  │
//!   │                                                     │   │  is no second rule to  │
//!   │                                                     │   │  nominate, so `Display`│
//!   │                                                     │   │  is transparent.       │
//!   └─────────────────────────────────────────────────────┘   └────────────────────────┘
//! ```
//!
//! An **alias class** is a connected component of `alias ──▶ fold target`
//! ([`FoldAliasShape::target_label`]). A member can be RE-ROUTED through the canonical member
//! only when both are RENAMINGS of the target — every constructor argument a bare parameter wrap,
//! the parameters a permutation ([`FoldAliasShape::renaming_inverse`]). A merely PARTIAL alias
//! (`POutputShort`'s channel is `NQuote(p)`, `NQuoteNil`'s is the literal `PZero`) names only a
//! SUBSET of its target's terms, so "render an arbitrary target through it" is undefined, not
//! merely awkward; such a member keeps its own arm and the generated per-language gate
//! (`languages/tests/surface_synonymy_gate.rs`) proves its surface already agrees.
//!
//! An **inert grouping** ([`classify_inert_grouping_shape`]) is a bracket pair whose body is the
//! identity. Its class is `{ Grouping(x), x }` for every `x`, so the canonical member is the
//! wrapped term by construction. `Display` forwards the child at the INHERITED binding-power
//! threshold, and the fence / precedence machinery re-inserts brackets wherever the surface needs
//! them — which is why dropping them cannot make a term unparseable.
//!
//! # The loud gate
//!
//! [`compile_errors`] emits `compile_error!` into the generated source for any alias class that
//! has a re-routable member and does not declare exactly one canonical member. A newly added
//! surface synonym therefore fails the BUILD, naming the class and its members, until the grammar
//! says which member is canonical.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use mettail_ast::grammar::{GrammarRule, SyntaxExpr, TermParam};
use mettail_ast::grammar_shapes::{classify_fold_alias_shape, classify_inert_grouping_shape};
use mettail_ast::language::LanguageDef;
use proc_macro2::TokenStream;
use quote::quote;

/// The FILLER SURFACE of each category: the first rule of that category whose syntax pattern is
/// entirely literals (a nullary constructor), rendered space-separated. Rholang's `Proc` filler is
/// `PZero`'s `Nil`; its `Name` filler is `NQuoteNil`'s `@ Nil`.
///
/// Shared by the surface-synonymy gate table and by the sigil-operand wrap gate
/// (`display::generate_sigil_operand_wrap_gate`), so both exercise the SAME sample surfaces.
pub(crate) fn nullary_filler_surfaces(language: &LanguageDef) -> BTreeMap<String, String> {
    let mut filler: BTreeMap<String, String> = BTreeMap::new();
    for rule in &language.terms {
        let Some(sp) = &rule.syntax_pattern else {
            continue;
        };
        if sp.is_empty() || !sp.iter().all(|e| matches!(e, SyntaxExpr::Literal(_))) {
            continue;
        }
        let text = sp
            .iter()
            .filter_map(|e| match e {
                SyntaxExpr::Literal(l) => Some(l.clone()),
                _ => None,
            })
            .collect::<Vec<_>>()
            .join(" ");
        filler.entry(rule.category.to_string()).or_insert(text);
    }
    filler
}

/// One PARSEABLE SAMPLE SURFACE for `rule`: its own syntax pattern with every parameter replaced
/// by its category's [`nullary_filler_surfaces`] entry.
///
/// `None` when any pattern element has no single filler surface — a `.*sep` list, a capture, an
/// optional group, or a parameter whose category has no nullary constructor. A member that
/// contributes no sample is REPORTED as uncovered by the gates rather than given a guessed one.
pub(crate) fn sample_surface_for(
    rule: &GrammarRule,
    filler: &BTreeMap<String, String>,
) -> Option<String> {
    let sp = rule.syntax_pattern.as_ref()?;
    let tc = rule.term_context.as_ref()?;
    let mut parts: Vec<String> = Vec::with_capacity(sp.len());
    for e in sp {
        match e {
            SyntaxExpr::Literal(l) => parts.push(l.clone()),
            SyntaxExpr::Param(p) => {
                let pname = p.to_string();
                let pcat = tc.iter().find_map(|tp| match tp {
                    TermParam::Simple {
                        name,
                        ty: mettail_ast::types::TypeExpr::Base(cat),
                    } if name.to_string() == pname => Some(cat.to_string()),
                    _ => None,
                })?;
                parts.push(filler.get(&pcat)?.clone());
            },
            _ => return None,
        }
    }
    Some(parts.join(" "))
}

/// One surface-synonymy ALIAS class: the rules of a single category that denote the same term.
#[derive(Debug, Clone)]
pub(crate) struct AliasClass {
    /// The category all members produce.
    pub category: String,
    /// The class ROOT — the fold target every alias re-wraps into. It is a member.
    pub target: String,
    /// Every member label, sorted, including [`AliasClass::target`].
    pub members: Vec<String>,
    /// The DECLARED canonical member (`canonical` keyword), if any.
    pub canonical: Option<String>,
    /// Members that are total RENAMINGS of the target: `label ↦ inverse`, where `inverse[i]` is
    /// the member-parameter index supplying the target's `i`-th field. The target itself is
    /// present with the identity.
    pub renamings: BTreeMap<String, Vec<usize>>,
}

/// How `Display` renders one member: through the canonical member's syntax pattern, with the
/// member's own fields permuted into the canonical's parameter order.
#[derive(Debug, Clone)]
pub(crate) struct Reroute {
    /// The canonical member whose rule supplies the surface.
    pub canonical: String,
    /// `tc_perm[j]` = the index into the CANONICAL rule's `term_context` of the parameter that
    /// this member's field `j` supplies. Used to permute the canonical rule's term context so the
    /// emitted match arm binds the member's fields in the member's own order while the canonical's
    /// syntax pattern refers to them by the canonical's own names.
    pub tc_perm: Vec<usize>,
}

/// The derived surface-synonymy model of a language.
#[derive(Debug, Clone, Default)]
pub(crate) struct SynonymyModel {
    /// Every derived alias class with ≥2 members, ordered by (category, target).
    pub classes: Vec<AliasClass>,
    /// `member label ↦ how to render it`. Contains only members that are NOT the canonical
    /// member of their class and that are re-routable.
    pub reroutes: HashMap<String, Reroute>,
    /// Labels of inert-grouping rules — rendered TRANSPARENTLY (the child at the inherited
    /// binding-power threshold, no brackets of their own).
    pub inert_groupings: BTreeSet<String>,
}

/// The number of constructor fields a rule's term context declares (all `Simple` params; a rule
/// with any other param kind is never a renaming alias, so the count is only ever consulted for
/// rules that are).
fn field_arity(rule: &GrammarRule) -> usize {
    rule.term_context.as_ref().map(|tc| tc.len()).unwrap_or(0)
}

/// Derive the surface-synonymy model from the grammar alone.
///
/// The alias graph is `alias ──▶ target_label` restricted to one category; its connected
/// components are the classes. Because every edge points from a `fold` rule to a DIFFERENT
/// constructor of the same category (`classify_fold_alias_shape` rejects self-folds), the graph is
/// a forest of stars in every grammar seen so far, but the union–find below does not assume that.
pub(crate) fn derive(language: &LanguageDef) -> SynonymyModel {
    let mut model = SynonymyModel::default();

    // ── Inert groupings ──
    for rule in &language.terms {
        if classify_inert_grouping_shape(rule).is_some() {
            model.inert_groupings.insert(rule.label.to_string());
        }
    }

    // ── Alias edges, per category ──
    // `edges[category][alias] = (target, renaming_inverse)`
    let mut edges: BTreeMap<String, BTreeMap<String, (String, Option<Vec<usize>>)>> =
        BTreeMap::new();
    for rule in &language.terms {
        let Some(shape) = classify_fold_alias_shape(rule) else {
            continue;
        };
        edges
            .entry(rule.category.to_string())
            .or_default()
            .insert(rule.label.to_string(), (shape.target_label, shape.renaming_inverse));
    }

    let by_label: HashMap<String, &GrammarRule> = language
        .terms
        .iter()
        .map(|r| (r.label.to_string(), r))
        .collect();

    for (category, cat_edges) in &edges {
        // Group aliases by the target they re-wrap into. A chain `A ⇒ B ⇒ C` would need
        // path-compression; none exists in any bundled grammar (an alias's target is always a
        // plain constructor, never itself an alias), and the loop below follows the chain to its
        // root so a future chain is handled rather than silently mis-grouped.
        let mut root_of: BTreeMap<String, String> = BTreeMap::new();
        for alias in cat_edges.keys() {
            let mut cur = alias.clone();
            let mut hops = 0usize;
            while let Some((next, _)) = cat_edges.get(&cur) {
                cur = next.clone();
                hops += 1;
                // A cycle is impossible (`variant_seg != rule_label` forbids self-folds and the
                // fold semantics forbid mutual re-wraps), but bound the walk anyway rather than
                // hang the compiler on a malformed grammar.
                if hops > cat_edges.len() + 1 {
                    break;
                }
            }
            root_of.insert(alias.clone(), cur);
        }

        let mut by_root: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for (alias, root) in &root_of {
            by_root.entry(root.clone()).or_default().push(alias.clone());
        }

        for (target, aliases) in by_root {
            // The target must itself be a declared rule of this category; if the fold body names
            // a constructor with no surface rule (a synthesised variant), there is no surface to
            // be canonical about and the class is not a SURFACE synonymy class.
            let Some(target_rule) = by_label.get(&target) else {
                continue;
            };
            if target_rule.category.to_string() != *category {
                continue;
            }

            let mut members: Vec<String> = aliases.clone();
            members.push(target.clone());
            members.sort();
            members.dedup();
            if members.len() < 2 {
                continue;
            }

            // Renamings: the target is the identity; an alias contributes its own inverse when it
            // has one AND its arity matches the target's (a renaming is a bijection, so the
            // arities must agree — the arity check is redundant with the permutation check but
            // states the invariant where a reader looks for it).
            let target_arity = field_arity(target_rule);
            let mut renamings: BTreeMap<String, Vec<usize>> = BTreeMap::new();
            renamings.insert(target.clone(), (0..target_arity).collect());
            for alias in &aliases {
                let Some((_, Some(inverse))) = cat_edges.get(alias) else {
                    continue;
                };
                let Some(alias_rule) = by_label.get(alias) else {
                    continue;
                };
                if inverse.len() == target_arity && field_arity(alias_rule) == target_arity {
                    renamings.insert(alias.clone(), inverse.clone());
                }
            }

            let declared: Vec<String> = members
                .iter()
                .filter(|m| by_label.get(*m).is_some_and(|r| r.is_canonical_synonym))
                .cloned()
                .collect();
            let canonical = match declared.len() {
                1 => Some(declared[0].clone()),
                _ => None,
            };

            model.classes.push(AliasClass {
                category: category.clone(),
                target: target.clone(),
                members,
                canonical,
                renamings,
            });
        }
    }

    // ── Re-route plans ──
    for class in &model.classes {
        let Some(canonical) = class.canonical.as_ref() else {
            continue;
        };
        let Some(canonical_inverse) = class.renamings.get(canonical) else {
            continue;
        };
        for member in &class.members {
            if member == canonical {
                continue;
            }
            let Some(member_inverse) = class.renamings.get(member) else {
                continue;
            };
            // target field `i` is supplied by member parameter `member_inverse[i]` and by
            // canonical parameter `canonical_inverse[i]`, so the member's field
            // `member_inverse[i]` and the canonical's parameter `canonical_inverse[i]` are THE
            // SAME child. Invert that into the member's own field order.
            let mut tc_perm = vec![usize::MAX; member_inverse.len()];
            for (i, &member_field) in member_inverse.iter().enumerate() {
                tc_perm[member_field] = canonical_inverse[i];
            }
            if tc_perm.iter().any(|&x| x == usize::MAX) {
                continue;
            }
            model
                .reroutes
                .insert(member.clone(), Reroute { canonical: canonical.clone(), tc_perm });
        }
    }

    model
}

/// The canonical rule with its `term_context` permuted into the MEMBER's field order, so the
/// emitted arm binds `Member(f₀ … fₙ)` while the canonical's syntax pattern refers to those same
/// children by the canonical's own parameter names.
///
/// The syntax pattern is untouched: it names parameters, and the parameters keep their names —
/// only their POSITIONS move, and positions are exactly what the match arm binds by.
pub(crate) fn rerouted_rule(canonical_rule: &GrammarRule, plan: &Reroute) -> GrammarRule {
    let mut synthetic = canonical_rule.clone();
    if let Some(tc) = &canonical_rule.term_context {
        let permuted: Vec<TermParam> = plan.tc_perm.iter().map(|&i| tc[i].clone()).collect();
        synthetic.term_context = Some(permuted);
    }
    synthetic
}

/// ★ THE PER-LANGUAGE GATE TABLE — the generated half of the loud gate.
///
/// Emits three module-scope constants into the language module:
///
/// ```text
///   __SURFACE_SYNONYMY_CLASSES : &[(category, members, canonical_or_empty)]
///   __SURFACE_SYNONYMY_SAMPLES : &[(category, &[(member_label, sample_surface)])]
///   __SURFACE_INERT_GROUPINGS  : &[label]
/// ```
///
/// `__SURFACE_SYNONYMY_SAMPLES` is what makes the gate EXECUTABLE rather than descriptive. For
/// each class member with a syntax pattern, the sample is that pattern rendered with every
/// parameter replaced by a FILLER SURFACE — the surface of the simplest nullary rule of the
/// parameter's category (a rule whose syntax pattern is literals only, e.g. Rholang's
/// `PZero |- "Nil"`). So Rholang's `Name` class yields
///
/// ```text
///   NQuote      ⇒ "@ ( Nil )"
///   NQuoteShort ⇒ "@ Nil"
///   NQuoteNil   ⇒ "@ Nil"
/// ```
///
/// three SURFACES of the same denotation. The shared harness
/// (`languages/tests/surface_synonymy_gate.rs`) parses each and asserts the displays are
/// IDENTICAL — *the class is a singleton after normalisation*. A member whose parameters have no
/// nullary filler contributes no sample rather than a guessed one; it is reported by the harness
/// as uncovered instead of silently passing.
pub(crate) fn gate_table(language: &LanguageDef, model: &SynonymyModel) -> TokenStream {
    let by_label: HashMap<String, &GrammarRule> = language
        .terms
        .iter()
        .map(|r| (r.label.to_string(), r))
        .collect();

    let filler = nullary_filler_surfaces(language);

    let class_rows: Vec<TokenStream> = model
        .classes
        .iter()
        .map(|c| {
            let category = &c.category;
            let members = c.members.iter().map(|m| quote! { #m });
            let canonical = c.canonical.clone().unwrap_or_default();
            quote! { (#category, &[#(#members),*], #canonical) }
        })
        .collect();

    let sample_rows: Vec<TokenStream> = model
        .classes
        .iter()
        .map(|c| {
            let category = &c.category;
            let samples: Vec<TokenStream> = c
                .members
                .iter()
                .filter_map(|m| {
                    let rule = by_label.get(m)?;
                    let surface = sample_surface_for(rule, &filler)?;
                    Some(quote! { (#m, #surface) })
                })
                .collect();
            quote! { (#category, &[#(#samples),*]) }
        })
        .collect();

    let groupings = model.inert_groupings.iter().map(|g| quote! { #g });

    // The per-category normalise arms: `surface ──parse──▶ term ──Display──▶ surface`, on BOTH
    // string seams. Emitted only for categories that actually carry a class, so the gate cannot
    // reference a category with no string entry.
    let mut gate_categories: BTreeSet<String> =
        model.classes.iter().map(|c| c.category.clone()).collect();
    for rule in &language.terms {
        if model.inert_groupings.contains(&rule.label.to_string()) {
            gate_categories.insert(rule.category.to_string());
        }
    }
    let normalise_arms: Vec<TokenStream> = gate_categories
        .iter()
        .map(|c| {
            let cat_ident = quote::format_ident!("{}", c);
            quote! {
                #c => {
                    // `parse` and `parse_via_wpda` carry DIFFERENT error types (a `String`
                    // and a `ParseError`), so each branch is stringified where it is produced
                    // rather than after the join.
                    if structured {
                        #cat_ident::parse(surface)
                            .map(|__t| format!("{}", __t))
                            .map_err(|__e| format!("{__e:?}"))
                    } else {
                        #cat_ident::parse_via_wpda(surface)
                            .map(|__t| format!("{}", __t))
                            .map_err(|__e| format!("{__e:?}"))
                    }
                },
            }
        })
        .collect();

    quote! {
        /// ★ SURFACE SYNONYMY — the gate's parse-and-render entry, per category and per STRING
        /// SEAM. `structured = true` is `Cat::parse`, `false` is `Cat::parse_via_wpda`; both are
        /// exercised, because the refuted `parse_structured`-fallback hypothesis is exactly the
        /// kind of seam difference a one-seam gate cannot see.
        #[allow(dead_code, non_snake_case)]
        pub fn __surface_synonymy_normalise(
            category: &str,
            surface: &str,
            structured: bool,
        ) -> Result<String, String> {
            // A language with no synonymy class emits no arms; the parameters are then unread.
            let _ = (surface, structured);
            match category {
                #(#normalise_arms)*
                other => Err(format!("no string entry generated for category `{other}`")),
            }
        }
        /// ★ SURFACE SYNONYMY — the derived alias classes of this language.
        /// `(category, members, canonical)`; the canonical is `""` when the class needs none
        /// (no two members are total renamings of the target, so no two surfaces are
        /// interchangeable). See `macros/src/gen/syntax/synonymy.rs`.
        #[allow(dead_code)]
        pub const __SURFACE_SYNONYMY_CLASSES: &[(&str, &[&str], &str)] = &[
            #(#class_rows),*
        ];
        /// ★ SURFACE SYNONYMY — one parseable SAMPLE SURFACE per class member, built from that
        /// member's own syntax pattern with each parameter filled by its category's simplest
        /// nullary surface. All samples of one class denote the same term, so their displays
        /// must be identical: that is *singleton-after-normalisation*, executable.
        #[allow(dead_code)]
        pub const __SURFACE_SYNONYMY_SAMPLES: &[(&str, &[(&str, &str)])] = &[
            #(#sample_rows),*
        ];
        /// ★ SURFACE SYNONYMY — the inert-grouping rules, rendered transparently by `Display`.
        #[allow(dead_code)]
        pub const __SURFACE_INERT_GROUPINGS: &[&str] = &[#(#groupings),*];
    }
}

/// `compile_error!` tokens for every alias class that must declare a canonical member and does
/// not, or that declares more than one.
///
/// ★ THE LOUD GATE. This is what makes the NEXT surface synonym impossible rather than
/// discovered: a class becomes eligible the moment two of its members are total renamings of the
/// same target, which is precisely the moment their surfaces become interchangeable, and the build
/// then stops until the grammar says which surface is the canonical one.
pub(crate) fn compile_errors(language: &LanguageDef, model: &SynonymyModel) -> TokenStream {
    let by_label: HashMap<String, &GrammarRule> = language
        .terms
        .iter()
        .map(|r| (r.label.to_string(), r))
        .collect();
    let mut out = TokenStream::new();
    for class in &model.classes {
        // Eligibility: ≥2 members are total renamings of the target, so `Display` genuinely has a
        // choice to make. A class whose only renaming is the target itself (every alias merely
        // partial, e.g. `POutput` + `POutputNil`) has no interchangeable pair — each member's
        // surface is reachable only from its own terms — so no declaration is required and the
        // generated runtime gate checks the residue.
        if class.renamings.len() < 2 {
            continue;
        }
        let declared: Vec<&String> = class
            .members
            .iter()
            .filter(|m| by_label.get(*m).is_some_and(|r| r.is_canonical_synonym))
            .collect();
        if declared.len() == 1 {
            continue;
        }
        let category = &class.category;
        let target = &class.target;
        let members = class.members.join(", ");
        let renamings: Vec<&String> = class.renamings.keys().collect();
        let renamings = renamings
            .iter()
            .map(|s| s.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        let message = if declared.is_empty() {
            format!(
                "SURFACE SYNONYMY: the `{category}` rules {{{members}}} all denote the same term \
                 (they fold to `{target}`), and {{{renamings}}} are total RENAMINGS of it, so \
                 their surfaces are interchangeable and `Display` must choose ONE. Annotate \
                 exactly one of them with the `canonical` keyword (after the eval mode, alongside \
                 `right` / `prefix(N)`). Without it `Display(Parse(Display(t)))` is not a fixpoint: \
                 the parser's election is context-dependent, so the same denotation sheds one \
                 surface per nesting layer."
            )
        } else {
            let declared = declared
                .iter()
                .map(|s| s.as_str())
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "SURFACE SYNONYMY: the `{category}` synonymy class {{{members}}} declares MORE \
                 THAN ONE canonical member ({declared}). A class has exactly one canonical \
                 surface; remove the `canonical` keyword from all but one."
            )
        };
        out.extend(quote! { compile_error!(#message); });
    }
    out
}
