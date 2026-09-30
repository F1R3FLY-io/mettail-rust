//! Finite depth-zero constructor adapter around the existing tree automaton.
//!
//! `FiniteConstructorWitnessAdapter.v` specifies ordered fixed/required slots,
//! typed witness insertion, occurrence traversal, and unchanged direct bases.
//! This module does not implement productivity analysis or positive-depth tape
//! execution. The existing automaton is the only finite-witness search.

use super::{classify_direct_variants, collect_spec_only_variants, constructor_expression};
use crate::gen::capture::{field_layout, FieldSlotSource};
use crate::gen::term_gen::{ident_samples, CaptureSamplingContext};
use crate::gen::term_ops::subst::{
    field_info_for_token_capture, field_infos_from_term_param, rule_to_variant_kind, FieldInfo,
    OpaqueLeafKind, VariantKind,
};
use crate::gen::test_gen::unit_tests::construct_leaf_value;
use mettail_ast::grammar::{GrammarRule, TermParam};
use mettail_ast::language::LanguageDef;
use mettail_prattail::sym_tree::{SymTerm, SymbolicTreeAutomaton, TreeTrans};
use mettail_prattail::symbolic::CharClassAlgebra;
use std::cell::{OnceCell, RefCell};
use std::collections::{HashMap, HashSet};
use std::fmt::Write;

pub(super) struct FiniteWitnessContext<'a> {
    language: &'a LanguageDef,
    compiled: OnceCell<Result<CompiledRecipes, String>>,
    bases: RefCell<HashMap<String, Result<Option<String>, String>>>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use quote::format_ident;

    fn language(source: &str) -> LanguageDef {
        syn::parse_str(source).expect("finite witness fixture must parse")
    }

    fn base(context: &FiniteWitnessContext<'_>, category: &str) -> String {
        let source = context
            .base_for(&format_ident!("{category}"))
            .expect("finite witness must not refuse")
            .expect("finite witness must exist");
        syn::parse_str::<syn::Expr>(&source)
            .expect("flat witness source must be a Rust expression");
        source
    }

    #[test]
    fn mixed_captures_and_repeated_children_keep_exact_argument_order() {
        let language = language(
            r#"
            name: FiniteMixed,
            types { data Leaf data Pair }
            tokens { Word = "<[a-z]+>"; }
            terms {
                Atom . |- word@Word : Leaf;
                PairNode . left:Leaf, right:Leaf
                    |- tag@Ident left raw@StringLiteral right : Pair;
            }
        "#,
        );
        let context = FiniteWitnessContext::new(&language);
        let source = base(&context, "Pair");
        assert_eq!(source.matches("Leaf::Atom(\"<a>\".to_string())").count(), 2);
        let sample = CaptureSamplingContext::new(&language);
        let tag = sample.sample("Ident").expect("identifier sample");
        let raw = sample
            .sample("StringLiteral")
            .expect("raw quoted-string sample");
        assert!(source.contains(&format!(
            "Pair::PairNode({tag:?}.to_string(), std::sync::Arc::new(__mettail_finite_0), {raw:?}.to_string(), std::sync::Arc::new(__mettail_finite_1))"
        )), "{source}");
        assert!(source.contains("AnyTerm::WrapPair(__mettail_finite_2)"));
        assert!(!source.contains("build_leaf_from_tape"));
        assert_eq!(base(&context, "Pair"), source);
        assert_eq!(context.bases.borrow().len(), 1);
    }

    #[test]
    fn declaration_permutation_uses_canonical_layout_not_variant_field_positions() {
        let language = language(
            r#"
            name: FiniteOrder,
            types { data Left data Right data Root }
            terms {
                L . |- "left" : Left;
                R . |- "right" : Right;
                Swap . first:Left, second:Right |- "swap" second first : Root;
            }
        "#,
        );
        let source = base(&FiniteWitnessContext::new(&language), "Root");
        assert!(source.contains("let __mettail_finite_0: Right ="), "{source}");
        assert!(source.contains("let __mettail_finite_1: Left ="), "{source}");
        assert!(source.contains("Root::Swap(std::sync::Arc::new(__mettail_finite_0), std::sync::Arc::new(__mettail_finite_1))"));
    }

    #[test]
    fn ddl_like_empty_containers_and_required_cross_category_head_are_real_terms() {
        let language = language(
            r#"
            name: FiniteDdl,
            types { data DdlPath data DdlImport data DdlImports data DdlTerm }
            terms {
                Path . |- name@Ident : DdlPath;
                Import . |- "import" raw@StringLiteral "as" alias@Ident : DdlImport;
                Imports . head:DdlImport, tail:Vec(DdlImport) |- head tail.*sep("") : DdlImports;
                Term . bindings:Vec(DdlPath), syntax:Vec(DdlPath)
                    |- label@Ident "." bindings.*sep(",") "|-" syntax.*sep("") ":" result@Ident ";" : DdlTerm;
            }
        "#,
        );
        let context = FiniteWitnessContext::new(&language);
        let imports = base(&context, "DdlImports");
        assert!(imports.contains("DdlImport::Import("));
        assert!(imports
            .contains("DdlImports::Imports(std::sync::Arc::new(__mettail_finite_0), vec![])"));
        let term = base(&context, "DdlTerm");
        assert!(term.contains(".to_string(), vec![], vec![], "), "{term}");
        assert!(!term.contains("DdlPath::Path"));
    }

    #[test]
    fn productive_cycle_uses_existing_exit_and_unproductive_cycle_returns_none() {
        let productive = language(
            r#"
            name: FiniteExit,
            types { data A data B }
            terms {
                Around . child:B |- "a" child : A;
                Back . child:A |- "b" child : B;
                Exit . |- "exit" : B;
            }
        "#,
        );
        let source = base(&FiniteWitnessContext::new(&productive), "A");
        assert!(source.contains("B::Exit"));
        assert!(source.contains("A::Around("));
        assert!(!source.contains("B::Back("));
        let unproductive = language(
            r#"
            name: FiniteCycle,
            types { data A data B }
            terms {
                Around . child:B |- "a" child : A;
                Back . child:A |- "b" child : B;
            }
        "#,
        );
        assert_eq!(
            FiniteWitnessContext::new(&unproductive).base_for(&format_ident!("A")),
            Ok(None)
        );
    }

    #[test]
    fn malformed_or_unknown_capture_never_becomes_a_productive_empty_leaf() {
        for source in [
            r#"name: FiniteUnknown, types { data Term } terms { Captured . |- x@Missing : Term; }"#,
            r#"name: FiniteBroken, types { data Term } tokens { Broken = "["; } terms { Captured . |- x@Broken : Term; }"#,
        ] {
            let language = language(source);
            let error = FiniteWitnessContext::new(&language)
                .base_for(&format_ident!("Term"))
                .expect_err("invalid token must refuse rather than form a leaf");
            assert!(error.contains("Term::Captured"), "{error}");
        }
    }

    #[test]
    fn original_direct_base_expression_is_reused_without_rewriting() {
        let language = language(
            r#"
            name: FiniteDirect,
            types { ![i32] as Num data Root }
            terms {
                Zero . |- "zero" : Num;
                RootNode . value:Num |- "root" value : Root;
            }
        "#,
        );
        let before = classify_direct_variants(&format_ident!("Num"), &language).leaves;
        assert!(before.len() >= 2);
        let source = base(&FiniteWitnessContext::new(&language), "Root");
        assert!(source.contains(&format!("({}).unwrap_num()", before[0].1)), "{source}");
        assert_eq!(classify_direct_variants(&format_ident!("Num"), &language).leaves, before);
    }

    #[test]
    fn malformed_collection_metadata_refuses_before_existing_fallback() {
        let language = language(
            "name: FiniteBadField, types { data Root } terms { End . |- \"end\" : Root; }",
        );
        let compiled = CompiledRecipes::from_language(&language).expect("valid original base");
        let sampling = CaptureSamplingContext::new(&language);
        let field = FieldInfo {
            category: format_ident!("Root"),
            is_collection: true,
            coll_type: None,
            is_predicate: false,
            is_optional: true,
            opaque_leaf: None,
        };
        let error = match compiled.field_slot(&field, None, &language, &sampling) {
            Err(error) => error,
            Ok(_) => panic!("missing collection metadata must not enter the existing vec fallback"),
        };
        assert!(error.contains("coll_type"));
    }

    #[test]
    fn unsupported_scope_and_native_fields_do_not_poison_an_independent_base() {
        let language = language(
            r#"
            name: FiniteUnsupported,
            types { Proc data Bound ![OpaqueCarrier] as Opaque data NativeHolder data Good }
            terms {
                Bind . ^x.body:[Proc -> Proc] |- "bind" x "." body : Bound;
                WrapNative . value:Opaque |- "native" value : NativeHolder;
                End . |- "end" : Good;
            }
        "#,
        );
        let context = FiniteWitnessContext::new(&language);
        assert!(base(&context, "Good").contains("Good::End"));
        let scope = context
            .base_for(&format_ident!("Bound"))
            .expect_err("scope unsupported");
        assert!(scope.contains("scope"), "{scope}");
        let native = context
            .base_for(&format_ident!("NativeHolder"))
            .expect_err("native unsupported");
        assert!(native.contains("runtime-only"), "{native}");
    }

    #[test]
    fn witness_assembly_rejects_wrong_category_and_surplus_children() {
        let mut compiled =
            CompiledRecipes::new(vec!["A".to_owned(), "B".to_owned()]).expect("categories");
        compiled.add_recipe(Recipe {
            category: 0,
            construction: Construction::Direct("AnyTerm::WrapA(A::A0)".to_owned()),
        });
        compiled.add_recipe(Recipe {
            category: 1,
            construction: Construction::Ordinary {
                label: "NeedsB".to_owned(),
                slots: vec![Slot::Required(1)],
            },
        });
        let wrong = SymTerm::node("finite_recipe_1", vec![SymTerm::constant("finite_recipe_0")]);
        assert!(compiled
            .emit(&wrong, 1)
            .expect_err("wrong child category")
            .contains("category mismatch"));
        let surplus = SymTerm::node("finite_recipe_0", vec![SymTerm::constant("finite_recipe_0")]);
        assert!(compiled
            .emit(&surplus, 0)
            .expect_err("extra child")
            .contains("surplus"));
    }

    #[test]
    fn long_finite_witness_emits_flat_source_on_a_small_stack() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                const DEPTH: usize = 4_096;
                let mut compiled =
                    CompiledRecipes::new((0..DEPTH).map(|i| format!("C{i}")).collect())
                        .expect("unique chain categories");
                compiled.add_recipe(Recipe {
                    category: 0,
                    construction: Construction::Direct("AnyTerm::WrapC0(C0::End)".to_owned()),
                });
                for category in 1..DEPTH {
                    compiled.add_recipe(Recipe {
                        category,
                        construction: Construction::Ordinary {
                            label: "Next".to_owned(),
                            slots: vec![Slot::Required(category - 1)],
                        },
                    });
                }
                let source = compiled
                    .base_for(&format!("C{}", DEPTH - 1))
                    .expect("chain witness")
                    .expect("productive chain");
                assert_eq!(source.matches("let __mettail_finite_").count(), DEPTH);
                assert!(source.contains("Arc::new(__mettail_finite_4094)"));
                assert!(!source.contains("build_c"));
            })
            .expect("spawn small-stack witness test")
            .join()
            .expect("finite adapter is stack safe");
    }
}

impl<'a> FiniteWitnessContext<'a> {
    pub(super) fn new(language: &'a LanguageDef) -> Self {
        Self {
            language,
            compiled: OnceCell::new(),
            bases: RefCell::new(HashMap::new()),
        }
    }

    /// An AnyTerm-wrapped expression, an absent finite witness, or a diagnostic.
    /// The caller retains its existing nonempty direct-base list.
    pub(super) fn base_for(&self, category: &syn::Ident) -> Result<Option<String>, String> {
        let category = category.to_string();
        if let Some(result) = self.bases.borrow().get(&category) {
            return result.clone();
        }
        let result = self
            .compiled
            .get_or_init(|| CompiledRecipes::from_language(self.language))
            .as_ref()
            .map_err(Clone::clone)
            .and_then(|compiled| compiled.base_for(&category));
        self.bases.borrow_mut().insert(category, result.clone());
        result
    }
}

enum Slot {
    Fixed(String),
    Required(usize),
}

enum Construction {
    /// The existing expression already returns AnyTerm and may consume tape.
    Direct(String),
    Ordinary {
        label: String,
        slots: Vec<Slot>,
    },
}

struct Recipe {
    category: usize,
    construction: Construction,
}

struct CompiledRecipes {
    categories: Vec<String>,
    states: HashMap<String, usize>,
    recipes: Vec<Recipe>,
    symbols: HashMap<String, usize>,
    automaton: RefCell<SymbolicTreeAutomaton<CharClassAlgebra>>,
    unsupported: HashMap<usize, Vec<String>>,
}

impl CompiledRecipes {
    fn new(categories: Vec<String>) -> Result<Self, String> {
        let mut states = HashMap::with_capacity(categories.len());
        let mut automaton = SymbolicTreeAutomaton::new(CharClassAlgebra::new());
        for category in &categories {
            let state = automaton.add_state();
            if states.insert(category.clone(), state).is_some() {
                return Err(format!("mettail: duplicate finite-witness category `{category}`"));
            }
        }
        Ok(Self {
            categories,
            states,
            recipes: Vec::new(),
            symbols: HashMap::new(),
            automaton: RefCell::new(automaton),
            unsupported: HashMap::new(),
        })
    }

    fn from_language(language: &LanguageDef) -> Result<Self, String> {
        let mut compiled = Self::new(
            language
                .types
                .iter()
                .map(|ty| ty.name.to_string())
                .collect(),
        )?;
        let sampling = CaptureSamplingContext::new(language);
        for (category, ty) in language.types.iter().enumerate() {
            let direct = classify_direct_variants(&ty.name, language);
            let variants = collect_spec_only_variants(&ty.name, language);
            let mut direct_labels = HashSet::new();
            for (label, expression) in direct.leaves {
                let variant = variants
                    .iter()
                    .find(|variant| variant.label().to_string() == label);
                match variant {
                    Some(VariantKind::Refused { message, .. }) => {
                        // A compiler diagnostic is not a productive transition.
                        return Err(message.clone());
                    },
                    Some(VariantKind::Regular { .. }) => {
                        // Existing regular direct leaves are Ident-only. Their
                        // emitter embeds compile_error on failure; recheck the
                        // same Result before admitting its source as a leaf.
                        ident_samples(language)?;
                    },
                    Some(_) => {},
                    None => {
                        return Err(format!(
                            "mettail: direct base `{}::{label}` has no spec variant",
                            ty.name,
                        ))
                    },
                }
                direct_labels.insert(label);
                compiled.add_recipe(Recipe {
                    category,
                    construction: Construction::Direct(expression),
                });
            }
            for rule in language
                .terms
                .iter()
                .filter(|rule| rule.category == ty.name)
            {
                if direct_labels.contains(&rule.label.to_string())
                    || crate::gen::generatability::tape_rule_gap(rule).is_some()
                {
                    continue;
                }
                match compiled.ordinary_recipe(rule, language, &sampling)? {
                    Ok(construction) => compiled.add_recipe(Recipe { category, construction }),
                    Err(reason) => compiled
                        .unsupported
                        .entry(category)
                        .or_default()
                        .push(reason),
                }
            }
        }
        Ok(compiled)
    }

    fn add_recipe(&mut self, recipe: Recipe) {
        let symbol = format!("finite_recipe_{}", self.recipes.len());
        let children = match &recipe.construction {
            Construction::Direct(_) => Vec::new(),
            Construction::Ordinary { slots, .. } => slots
                .iter()
                .filter_map(|slot| match slot {
                    Slot::Fixed(_) => None,
                    Slot::Required(category) => Some(*category),
                })
                .collect(),
        };
        let automaton = self.automaton.get_mut();
        automaton.register(symbol.clone(), children.len());
        automaton.add_transition(TreeTrans {
            constructor: symbol.clone(),
            payload_guard: None,
            child_states: children,
            target: recipe.category,
        });
        self.symbols.insert(symbol, self.recipes.len());
        self.recipes.push(recipe);
    }

    /// Inner Err records unsupported construction. Outer Err is malformed
    /// metadata or failed checked sampling, and remains a diagnostic.
    fn ordinary_recipe(
        &self,
        rule: &GrammarRule,
        language: &LanguageDef,
        sampling: &CaptureSamplingContext<'_>,
    ) -> Result<Result<Construction, String>, String> {
        let location = format!("{}::{}", rule.category, rule.label);
        match rule_to_variant_kind(rule, language) {
            VariantKind::Refused { message, .. } => return Err(message),
            VariantKind::Binder { .. } | VariantKind::MultiBinder { .. } => {
                return Ok(Err(format!("{location}: finite scope construction is unsupported")));
            },
            VariantKind::Regular { .. } => {},
            _ => {
                return Ok(Err(format!(
                    "{location}: non-regular constructor requires its existing specialized emitter",
                )));
            },
        }
        if rule.term_context.is_none() && rule.syntax_pattern.is_none() {
            return Ok(Err(format!("{location}: no canonical term-context field layout")));
        }
        let layout = field_layout(
            rule.term_context.as_deref().unwrap_or(&[]),
            rule.syntax_pattern.as_deref(),
        );
        let mut slots = Vec::with_capacity(layout.slots.len());
        for slot in layout.slots {
            let context = format!("{location} field `{}`", slot.name);
            let (field, capture) = match slot.source {
                FieldSlotSource::TokenText { kind } => {
                    let mut field = field_info_for_token_capture();
                    field.is_optional = slot.optional;
                    (field, Some(kind.to_string()))
                },
                FieldSlotSource::GuestBody { .. } => {
                    return Ok(Err(format!(
                        "{context}: finite guest-body construction is unsupported",
                    )))
                },
                FieldSlotSource::Param(param) => {
                    if matches!(
                        param,
                        TermParam::Abstraction { .. } | TermParam::MultiAbstraction { .. }
                    ) {
                        return Ok(Err(format!(
                            "{context}: finite scope construction is unsupported"
                        )));
                    }
                    let mut fields = field_infos_from_term_param(param, slot.optional);
                    if fields.len() != 1 {
                        return Err(format!(
                            "mettail: {context}: canonical slot has {} field descriptors",
                            fields.len()
                        ));
                    }
                    let field = fields
                        .pop()
                        .expect("checked one canonical field descriptor");
                    let capture = (field.opaque_leaf == Some(OpaqueLeafKind::TokenText))
                        .then(|| "Ident".to_owned());
                    (field, capture)
                },
            };
            if field.opaque_leaf.is_none() && !field.is_predicate {
                if crate::gen::category_is_runtime_only_native(&field.category, language) {
                    return Ok(Err(format!(
                        "{context}: runtime-only native category `{}` has no surface construction",
                        field.category,
                    )));
                }
                if !self.states.contains_key(&field.category.to_string()) {
                    return Ok(Err(format!(
                        "{context}: required category `{}` is not declared",
                        field.category,
                    )));
                }
            }
            slots.push(
                self.field_slot(&field, capture.as_deref(), language, sampling)
                    .map_err(|reason| format!("mettail: {context}: {reason}"))?,
            );
        }
        Ok(Ok(Construction::Ordinary { label: rule.label.to_string(), slots }))
    }

    fn field_slot(
        &self,
        field: &FieldInfo,
        capture: Option<&str>,
        language: &LanguageDef,
        sampling: &CaptureSamplingContext<'_>,
    ) -> Result<Slot, String> {
        if field.opaque_leaf == Some(OpaqueLeafKind::GuestBody) {
            return Err("guest-body fields require their existing explicit construction contract"
                .to_owned());
        }
        if field.is_collection && field.coll_type.is_none() {
            return Err("collection field is missing coll_type metadata".to_owned());
        }
        if field.is_optional || field.is_predicate || field.is_collection {
            // Only these existing helper branches are admitted: never its
            // shallow category search or missing-coll_type fallback.
            return construct_leaf_value(field, language)
                .map(Slot::Fixed)
                .ok_or_else(|| "existing fixed-field constructor is unavailable".to_owned());
        }
        if let Some(kind) = capture {
            return sampling
                .sample(kind)
                .map(|sample| Slot::Fixed(format!("{sample:?}.to_string()")));
        }
        if field.opaque_leaf.is_some() {
            return Err("opaque field has no checked token provenance".to_owned());
        }
        self.states
            .get(&field.category.to_string())
            .copied()
            .map(Slot::Required)
            .ok_or_else(|| format!("required category `{}` is not declared", field.category))
    }

    fn base_for(&self, category: &str) -> Result<Option<String>, String> {
        let state = *self.states.get(category).ok_or_else(|| {
            format!("mettail: finite-witness category `{category}` is not declared")
        })?;
        let witness = {
            let mut automaton = self.automaton.borrow_mut();
            automaton.accepting.clear();
            automaton.set_accepting(state);
            automaton.witness()
        };
        match witness {
            Some(witness) => self.emit(&witness, state).map(Some),
            None => match self.unsupported.get(&state) {
                Some(reasons) => Err(format!(
                    "mettail: category `{category}` has no supported finite constructor witness: {}",
                    reasons.join("; "),
                )),
                None => Ok(None),
            },
        }
    }

    fn emit(&self, witness: &SymTerm<char>, expected: usize) -> Result<String, String> {
        enum Task<'a> {
            Visit(&'a SymTerm<char>),
            Build(&'a SymTerm<char>, usize),
        }
        struct Value {
            category: usize,
            name: String,
        }
        let mut tasks = vec![Task::Visit(witness)];
        let mut values: Vec<Value> = Vec::new();
        let mut out = String::from("{\n");
        let mut next_value = 0usize;
        while let Some(task) = tasks.pop() {
            match task {
                Task::Visit(node) => {
                    let index =
                        *self.symbols.get(&node.constructor).ok_or_else(|| {
                            format!(
                                "mettail: witness references unknown recipe `{}`",
                                node.constructor,
                            )
                        })?;
                    if node.payload.is_some() {
                        return Err("mettail: finite constructor witness unexpectedly has payload"
                            .to_owned());
                    }
                    tasks.push(Task::Build(node, index));
                    for child in node.children.iter().rev() {
                        tasks.push(Task::Visit(child));
                    }
                },
                Task::Build(node, index) => {
                    let recipe = &self.recipes[index];
                    let category = &self.categories[recipe.category];
                    let start = values
                        .len()
                        .checked_sub(node.children.len())
                        .ok_or_else(|| {
                            "mettail: finite witness assembly lost child results".to_owned()
                        })?;
                    let mut children = values.split_off(start).into_iter();
                    let expression = match &recipe.construction {
                        Construction::Direct(expression) => {
                            format!("({expression}).unwrap_{}()", category.to_lowercase(),)
                        },
                        Construction::Ordinary { label, slots } => {
                            let mut arguments = Vec::with_capacity(slots.len());
                            for slot in slots {
                                arguments.push(match slot {
                                    Slot::Fixed(expression) => expression.clone(),
                                    Slot::Required(expected) => {
                                        let child = children.next().ok_or_else(||
                                            "mettail: finite witness has too few required children".to_owned())?;
                                        if child.category != *expected {
                                            return Err("mettail: finite witness child category mismatch".to_owned());
                                        }
                                        format!("std::sync::Arc::new({})", child.name)
                                    },
                                });
                            }
                            constructor_expression(category, label, &arguments)
                        },
                    };
                    if children.next().is_some() {
                        return Err("mettail: finite witness has surplus child results".to_owned());
                    }
                    let name = format!("__mettail_finite_{next_value}");
                    next_value = next_value
                        .checked_add(1)
                        .ok_or_else(|| "mettail: finite witness value index overflow".to_owned())?;
                    writeln!(out, "    let {name}: {category} = {expression};")
                        .expect("writing constructor source to String");
                    values.push(Value { category: recipe.category, name });
                },
            }
        }
        if values.len() != 1 || values[0].category != expected {
            return Err("mettail: finite witness root category mismatch".to_owned());
        }
        writeln!(out, "    AnyTerm::Wrap{}({})\n}}", self.categories[expected], values[0].name)
            .expect("writing finite witness root to String");
        Ok(out)
    }
}
