//! Generation of the per-language numeric-cast **adapter** trait impls.
//!
//! Emits, for each language that declares numeric casts, the
//! `mettail_runtime::{CastWidth, ProcToNumericInput, CastResult}` impls that let the
//! language-agnostic reductions in `mettail_runtime::numeric_cast_adapter` (the `numeric_*`
//! and `proc_*` fns) drive that language's concrete `Proc` AST. This replaces the
//! hand-written, per-language `calc_*`/`rho_*` glue in `languages/numeric_dispatch.rs`
//! (deleted in Phase 3): a new language now writes NO numeric glue — the macro derives the
//! adapter from its `Cast*` wrapper rules and numeric-cast `fold` rules.
//!
//! Recognition is **purely structural** (`recognize_cast_fold`) — no keyword, constructor
//! label, or body fn-name is ever read. A numeric cast is a `fold` rule whose first param is the
//! primary/object category, whose optional second param is an integer width, and whose OUTPUT
//! category is either a numeric native type (native-output) or the object category itself
//! (object-output, keyed on the binary width-bearing shape). Flavor and arity both come from the
//! output category: a native-output cast (Calculator `int(a,m) : Int`) returns `Option<scalar>`,
//! defers on `None`, and reads its arity from the output kind; an object-output cast (RhoCalc
//! `int(a,m) : Proc`) returns the result `Proc` (`Err` on a bad cast), needs `CastResult`, and
//! carries no arity (parse-committed by the WPDA, never needed at reduction).
//!
//! Gating (zero dead-code): a language with a native-output numeric cast has its adapter
//! consumed by the always-emitted `eval.rs` native path, so its impls are UNGATED; a
//! language whose numeric casts are all object-output is consumed only by the
//! `#[cfg(feature = "dovetail-codegen")]` typed dispatcher, so its impls carry that gate.
//!
//! See `docs/design/made/native-types/numeric-cast-adapter-generation.md`.

use mettail_ast::grammar::{GrammarRule, TermParam};
use mettail_ast::language::{LanguageDef, NativeKind};
use mettail_ast::types::{EvalMode, TypeExpr};
use proc_macro2::TokenStream;
use quote::quote;
use syn::Ident;

use crate::gen::generate_literal_label;

/// The numeric family a cast narrows to. For native-output casts this is read structurally from
/// the OUTPUT category's native kind (`arity_of_kind`); object-output casts carry no arity (it is
/// parse-committed and unneeded — see `CastFold::arity`).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Arity {
    Int,
    UInt,
    Float,
    Fixed,
    BigInt,
    BigRat,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Flavor {
    Native,
    Object,
}

struct CastFold<'a> {
    /// the redex constructor label (`IntBin` native / `IntBinProc` object)
    label: &'a Ident,
    /// the rule's output category (`Int` native / `Proc` object)
    output_cat: &'a Ident,
    /// the cast arity. `Some` for native-output casts — derived **structurally from the OUTPUT
    /// category's native kind**, never from the keyword/label/body fn-name. `None` for
    /// object-output casts: the object arity is PARSE-COMMITTED (the WPDA commits the constructor
    /// from the keyword evidence) and is never needed at reduction — a nested object cast reduces
    /// child-first via saturation (`try_fold_to_self`) into a value WRAPPER, reaching the
    /// literal-wrapper arm, so the macro derives no object nested arm and needs no object arity.
    arity: Option<Arity>,
    flavor: Flavor,
    /// binary cast (carries a width param, `int(a, m)`) vs unary (`bigint(a)`) — from the param
    /// count (shape), independent of arity.
    is_binary: bool,
}

struct Wrapper<'a> {
    /// the `Proc`-producing wrapper constructor (`ProcInt` / `CastInt`)
    proc_variant: &'a Ident,
    /// the inner numeric category (`Int`)
    inner_cat: &'a Ident,
    /// the inner literal variant (`NumLit`/`RatLit`/`FixedLit`/`FloatLit`/`BoolLit`/`StringLit`)
    literal: Ident,
    kind: NativeKind,
}

/// The cast **arity** for a numeric native `kind` — the structural target of a native-output
/// cast, read from its OUTPUT category (never from the keyword, label, or body fn-name). `None`
/// for kinds that are not numeric-cast outputs (`Bool`/`Str`/`Other`/wide uints).
fn arity_of_kind(kind: NativeKind) -> Option<Arity> {
    Some(match kind {
        NativeKind::Int8
        | NativeKind::Int16
        | NativeKind::Int32
        | NativeKind::Int64
        | NativeKind::Int128
        | NativeKind::Isize => Arity::Int,
        NativeKind::UInt8 | NativeKind::UInt16 | NativeKind::UInt32 => Arity::UInt,
        NativeKind::Float32 | NativeKind::Float64 => Arity::Float,
        NativeKind::CanonicalFixedPoint => Arity::Fixed,
        NativeKind::CanonicalBigInt => Arity::BigInt,
        NativeKind::CanonicalBigRat => Arity::BigRat,
        _ => return None,
    })
}

/// Recognize a numeric-cast `fold` rule **purely by its shape** (the OSLF cast-rule shape), with
/// NO coupling to the keyword, constructor label, or body fn-name — the parser already committed
/// the constructor from the keyword evidence; the macro only mirrors the structure. A cast fold:
///
///   * is a `fold` rule whose **first param is the primary/object category** `proc_cat` (a cast
///     reinterprets a primary-category value);
///   * has **1 or 2 value params** — binary casts carry an **integer width** as the 2nd param
///     (`int(a, m)`), unary casts have none (`bigint(a)`); and
///   * **outputs** either a **numeric native** category (native-output cast — `Flavor::Native`,
///     arity from the output kind) or the **object category** `proc_cat` itself (object-output
///     cast — `Flavor::Object`).
///
/// Object-output casts are keyed on the **binary** (width-bearing) shape only: a unary
/// `proc_cat → proc_cat` fold is shape-indistinguishable from an ordinary unary operation
/// (`bitnot a`, `not a`, `len(p)`), and the macro needs nothing from object-unary casts — their
/// result is built by the `CastResult` impl already emitted for the binary object casts, and their
/// nesting reduces child-first via saturation. Native-output casts have a distinct numeric output
/// category, so unary native casts (`bigint(a) : BigInt`) are unambiguous and recognized too.
fn recognize_cast_fold<'a>(
    language: &LanguageDef,
    rule: &'a GrammarRule,
    proc_cat: &Ident,
) -> Option<CastFold<'a>> {
    if rule.eval_mode != Some(EvalMode::Fold) {
        return None;
    }
    let ps = rule.term_context.as_ref()?;
    if ps.is_empty() || ps.len() > 2 {
        return None;
    }
    // param 0 must be the primary/object category (the cast's input value).
    if simple_param_cat(&ps[0])? != proc_cat {
        return None;
    }
    let is_binary = ps.len() == 2;
    if is_binary {
        // binary cast ⇒ the 2nd param is an integer width.
        let w = simple_param_cat(&ps[1])?;
        if !kind_of(language, w)?.is_integer() {
            return None;
        }
    }
    // Flavor + arity from the OUTPUT category (structural, never the name):
    //   * numeric-native output  ⇒ native cast, arity = output kind;
    //   * object-category output ⇒ object cast (binary only — see above), arity unneeded.
    let (flavor, arity) = match kind_of(language, &rule.category) {
        Some(k) => (Flavor::Native, Some(arity_of_kind(k)?)),
        None if &rule.category == proc_cat && is_binary => (Flavor::Object, None),
        _ => return None,
    };
    Some(CastFold {
        label: &rule.label,
        output_cat: &rule.category,
        arity,
        flavor,
        is_binary,
    })
}

/// The base category of a `Simple` typed param (`a:Proc` → `Proc`).
fn simple_param_cat(p: &TermParam) -> Option<&Ident> {
    match p {
        TermParam::Simple {
            ty: TypeExpr::Base(c),
            ..
        } => Some(c),
        _ => None,
    }
}

/// The `Simple` value params of a rule, in order (None ⇒ not a judgement-style rule).
fn simple_params(rule: &GrammarRule) -> Option<Vec<&Ident>> {
    rule.term_context
        .as_ref()
        .map(|ps| ps.iter().filter_map(simple_param_cat).collect())
}

/// The `NumericInput` constructor expression for a literal of the given native kind, binding
/// the matched literal payload as `__v`. `Str` is handled by `as_numeric_str`, not here.
fn numeric_input_arm(kind: NativeKind, v: &Ident) -> TokenStream {
    match kind {
        NativeKind::Int32 => quote!(::mettail_runtime::NumericInput::I32(*#v)),
        NativeKind::Int8 | NativeKind::Int16 => {
            quote!(::mettail_runtime::NumericInput::I32(*#v as i32))
        },
        NativeKind::Int64 => quote!(::mettail_runtime::NumericInput::I64(*#v)),
        NativeKind::Int128 | NativeKind::Isize => {
            quote!(::mettail_runtime::NumericInput::I64(*#v as i64))
        },
        NativeKind::UInt32 => quote!(::mettail_runtime::NumericInput::U32(*#v)),
        NativeKind::UInt8 | NativeKind::UInt16 => {
            quote!(::mettail_runtime::NumericInput::U32(*#v as u32))
        },
        NativeKind::CanonicalBigInt => quote!(::mettail_runtime::NumericInput::BigInt(#v.get())),
        NativeKind::CanonicalBigRat => quote!(::mettail_runtime::NumericInput::BigRat(#v.get())),
        NativeKind::CanonicalFixedPoint => quote!(::mettail_runtime::NumericInput::Fixed(#v)),
        NativeKind::Float64 => quote!(::mettail_runtime::NumericInput::F64(#v.get())),
        NativeKind::Float32 => quote!(::mettail_runtime::NumericInput::F64(#v.get() as f64)),
        NativeKind::Bool => quote!(::mettail_runtime::NumericInput::I32(if *#v { 1 } else { 0 })),
        // Not a numeric carrier (Str / Other / wider uints) — caller filters these out.
        _ => quote!(return None),
    }
}

/// The runtime native reduction fn ident for `arity`, choosing the int width from `int_kind`.
fn numeric_fn_for(arity: Arity, int_kind: NativeKind) -> Ident {
    let name = match arity {
        Arity::Int => {
            if matches!(int_kind, NativeKind::Int64 | NativeKind::Int128 | NativeKind::Isize) {
                "numeric_int_bin_i64"
            } else {
                "numeric_int_bin_i32"
            }
        },
        Arity::UInt => "numeric_uint_bin_u32",
        Arity::Float => "numeric_float_bin",
        Arity::Fixed => "numeric_fixed_bin",
        Arity::BigInt => "numeric_bigint_unary",
        Arity::BigRat => "numeric_bigrat_unary",
    };
    Ident::new(name, proc_macro2::Span::call_site())
}

/// `NumericInput`-carrier wrapper for a reduced value of `arity` (used by `to_numeric_input`
/// nested arms): `int → I32/I64(n)`, `uint → U32(n)`, `float → F64(cf.get())`.
fn numeric_input_for_reduced(arity: Arity, int_kind: NativeKind, val: &Ident) -> TokenStream {
    match arity {
        Arity::Int => {
            if matches!(int_kind, NativeKind::Int64 | NativeKind::Int128 | NativeKind::Isize) {
                quote!(::mettail_runtime::NumericInput::I64(#val))
            } else {
                quote!(::mettail_runtime::NumericInput::I32(#val))
            }
        },
        Arity::UInt => quote!(::mettail_runtime::NumericInput::U32(#val)),
        Arity::Float => quote!(::mettail_runtime::NumericInput::F64(#val.get())),
        // Fixed/BigInt/BigRat reduced values are not re-fed as scalar NumericInputs here.
        _ => quote!(return None),
    }
}

/// Whether a native kind is a numeric category the adapter can carry.
fn is_numeric_kind(kind: NativeKind) -> bool {
    matches!(
        kind,
        NativeKind::Int8
            | NativeKind::Int16
            | NativeKind::Int32
            | NativeKind::Int64
            | NativeKind::Int128
            | NativeKind::Isize
            | NativeKind::UInt8
            | NativeKind::UInt16
            | NativeKind::UInt32
            | NativeKind::Float32
            | NativeKind::Float64
            | NativeKind::Bool
            | NativeKind::Str
            | NativeKind::CanonicalBigInt
            | NativeKind::CanonicalBigRat
            | NativeKind::CanonicalFixedPoint
    )
}

fn kind_of(language: &LanguageDef, cat: &Ident) -> Option<NativeKind> {
    let t = language.get_type(cat)?;
    let native = t.native_type.as_ref()?;
    Some(NativeKind::from_syn_type(native))
}

pub(crate) fn generate_numeric_cast_adapter(language: &LanguageDef) -> TokenStream {
    // 1. Cast-wrapper rules: a single numeric-typed field, Proc-producing, no body. Group by
    //    output category; the object/primary category `ProcCat` is the one carrying them. Computed
    //    FIRST — the cast-fold recognizer below keys on `ProcCat` to identify a cast's input value.
    struct WrapCand<'a> {
        proc_cat: &'a Ident,
        proc_variant: &'a Ident,
        inner_cat: &'a Ident,
        kind: NativeKind,
    }
    let wrap_cands: Vec<WrapCand<'_>> = language
        .terms
        .iter()
        .filter_map(|rule| {
            if rule.rust_code.is_some() {
                return None;
            }
            let ps = rule.term_context.as_ref()?;
            if ps.len() != 1 {
                return None;
            }
            let inner_cat = simple_param_cat(&ps[0])?;
            let kind = kind_of(language, inner_cat)?;
            if !is_numeric_kind(kind) {
                return None;
            }
            Some(WrapCand {
                proc_cat: &rule.category,
                proc_variant: &rule.label,
                inner_cat,
                kind,
            })
        })
        .collect();
    if wrap_cands.is_empty() {
        return quote!();
    }
    // ProcCat = the category with the most wrapper candidates (the object/primary category).
    let proc_cat: &Ident = {
        use std::collections::HashMap;
        let mut counts: HashMap<String, (&Ident, usize)> = HashMap::new();
        for c in &wrap_cands {
            let e = counts.entry(c.proc_cat.to_string()).or_insert((c.proc_cat, 0));
            e.1 += 1;
        }
        counts.values().max_by_key(|(_, n)| *n).map(|(id, _)| *id).expect("non-empty")
    };
    let wrappers: Vec<Wrapper<'_>> = wrap_cands
        .iter()
        .filter(|c| c.proc_cat == proc_cat)
        .filter_map(|c| {
            let native = language.get_type(c.inner_cat)?.native_type.as_ref()?;
            Some(Wrapper {
                proc_variant: c.proc_variant,
                inner_cat: c.inner_cat,
                literal: generate_literal_label(native),
                kind: c.kind,
            })
        })
        .collect();

    let wrapper_for_inner = |inner: &Ident| -> Option<&Wrapper<'_>> {
        wrappers.iter().find(|w| w.inner_cat == inner)
    };

    // 2. Numeric-cast fold rules (the redex constructors), recognized PURELY BY SHAPE — no keyword,
    //    label, or body fn-name is ever read (see `recognize_cast_fold`). Native casts carry an
    //    arity (from their output category); object casts do not (parse-committed, unneeded).
    let folds: Vec<CastFold<'_>> = language
        .terms
        .iter()
        .filter_map(|rule| recognize_cast_fold(language, rule, proc_cat))
        .collect();
    if folds.is_empty() {
        return quote!();
    }

    // Gating (computed up-front, applied per-impl — a single `#[cfg]` before a multi-item
    // block would gate only the first item, the op-enum bug fixed in 4645b0ab):
    //   * a language with a native-output cast has its `CastWidth`/`ProcToNumericInput`
    //     consumed by the always-emitted `eval.rs` path ⇒ ungated;
    //   * an object-only language's adapter is consumed only by the `dovetail-codegen`
    //     typed dispatcher ⇒ gated;
    //   * `CastResult` is ALWAYS `dovetail-codegen`-gated (it is consumed only on the
    //     object-output typed path, even when a mixed language's other impls are ungated).
    let has_native = folds.iter().any(|f| f.flavor == Flavor::Native);
    let gate: TokenStream = if has_native {
        quote!()
    } else {
        quote!(#[cfg(feature = "dovetail-codegen")])
    };
    let result_gate: TokenStream = quote!(#[cfg(feature = "dovetail-codegen")]);

    // 3. Width category `IntCat` = the 2nd param category of any binary cast fold (shape-derived —
    //    every binary cast, native or object, carries its integer width there).
    let int_cat: Option<&Ident> = folds.iter().filter(|f| f.is_binary).find_map(|f| {
        let rule = language
            .terms
            .iter()
            .find(|r| &r.label == f.label && &r.category == f.output_cat)?;
        simple_params(rule)?.get(1).copied()
    });
    let int_kind = int_cat.and_then(|c| kind_of(language, c)).unwrap_or(NativeKind::Int64);

    // ── CastWidth impls (only if a binary cast exists, i.e. there is a width category) ──
    let cast_width_impls = match int_cat {
        Some(ic) => {
            let lit = match language.get_type(ic).and_then(|t| t.native_type.as_ref()) {
                Some(nt) => generate_literal_label(nt),
                None => return quote!(compile_error!(
                    "numeric-cast width category has no native literal type"
                );),
            };
            quote! {
                #gate
                impl ::mettail_runtime::CastWidth for #ic {
                    fn into_width_i64(self) -> ::core::option::Option<i64> {
                        match self { #ic::#lit(b) => ::core::option::Option::Some(b as i64), _ => ::core::option::Option::None }
                    }
                }
                #gate
                impl ::mettail_runtime::CastWidth for &#ic {
                    fn into_width_i64(self) -> ::core::option::Option<i64> {
                        match self { #ic::#lit(b) => ::core::option::Option::Some(*b as i64), _ => ::core::option::Option::None }
                    }
                }
            }
        },
        None => quote!(),
    };

    // ── to_numeric_input ──
    let v = Ident::new("__v", proc_macro2::Span::call_site());
    // (a) wrapper arms (Str excluded — handled by as_numeric_str), with native nested sub-arms.
    let wrapper_arms: Vec<TokenStream> = wrappers
        .iter()
        .filter(|w| w.kind != NativeKind::Str)
        .map(|w| {
            let pv = w.proc_variant;
            let ic = w.inner_cat;
            let lit = &w.literal;
            let lit_arm = numeric_input_arm(w.kind, &v);
            // native, binary folds whose redex lives in THIS inner category get a nested sub-arm.
            let nested: Vec<TokenStream> = folds
                .iter()
                .filter(|f| f.flavor == Flavor::Native && f.is_binary && f.output_cat == ic)
                .filter_map(|f| {
                    let arity = f.arity?;
                    let fl = f.label;
                    let nfn = numeric_fn_for(arity, int_kind);
                    let n = Ident::new("__n", proc_macro2::Span::call_site());
                    let wrapped = numeric_input_for_reduced(arity, int_kind, &n);
                    Some(quote! {
                        #ic::#fl(inner_a, inner_w) => {
                            let #n = ::mettail_runtime::#nfn(inner_a.as_ref(), inner_w.as_ref())?;
                            #wrapped
                        },
                    })
                })
                .collect();
            quote! {
                #proc_cat::#pv(x) => match x.as_ref() {
                    #ic::#lit(#v) => #lit_arm,
                    #(#nested)*
                    _ => return ::core::option::Option::None,
                },
            }
        })
        .collect();
    // (b) object-output casts get NO top-level redex arm here. By the time a cast body runs, its
    //     argument was already reduced child-first (`try_fold_to_self`), so a nested object cast is
    //     a value WRAPPER (matched by (a)), never an un-reduced redex — object nesting reduces via
    //     saturation, not a `to_numeric_input` self-arm (the `nested_int_cast_folds_via_saturation`
    //     regression confirms this). It is also why object casts need no macro-derived arity: their
    //     only obligation is building the result, discharged by the `CastResult` impl below.
    let to_numeric_input = quote! {
        fn to_numeric_input(&self) -> ::core::option::Option<::mettail_runtime::NumericInput<'_>> {
            ::core::option::Option::Some(match self {
                #(#wrapper_arms)*
                _ => return ::core::option::Option::None,
            })
        }
    };

    // ── peel_numeric_elem: emit iff an indexed-collection cast rule exists (param0 = collection,
    //    param1 = integer index). Reproduces calc_peel_list_elem (OOB-safe, never panics). ──
    let peel_method: TokenStream = {
        let elem = language.terms.iter().find_map(|rule| {
            if &rule.category != proc_cat {
                return None;
            }
            let ps = rule.term_context.as_ref()?;
            if ps.len() != 2 {
                return None;
            }
            let c0 = simple_param_cat(&ps[0])?;
            let c1 = simple_param_cat(&ps[1])?;
            let coll = language.get_type(c0)?;
            coll.collection_kind.as_ref()?;
            let k1 = kind_of(language, c1)?;
            if !k1.is_integer() {
                return None;
            }
            let list_native = coll.native_type.as_ref()?;
            let list_lit = generate_literal_label(list_native);
            let idx_lit = generate_literal_label(language.get_type(c1)?.native_type.as_ref()?);
            Some((&rule.label, c0, list_lit, c1, idx_lit))
        });
        match elem {
            Some((label, list_cat, list_lit, idx_cat, idx_lit)) => quote! {
                fn peel_numeric_elem(&self) -> &Self {
                    match self {
                        #proc_cat::#label(list, index) => {
                            let #idx_cat::#idx_lit(n) = index.as_ref() else { return self; };
                            let idx = *n as usize;
                            match list.as_ref() {
                                #list_cat::#list_lit(v) => v.get(idx).unwrap_or(self),
                                _ => self,
                            }
                        },
                        _ => self,
                    }
                }
            },
            None => quote!(),
        }
    };

    // ── as_numeric_str: iff a Str wrapper exists ──
    let as_numeric_str: TokenStream = match wrappers.iter().find(|w| w.kind == NativeKind::Str) {
        Some(w) => {
            let pv = w.proc_variant;
            let ic = w.inner_cat;
            let lit = &w.literal;
            quote! {
                fn as_numeric_str(&self) -> ::core::option::Option<&str> {
                    match self {
                        #proc_cat::#pv(s) => match s.as_ref() {
                            #ic::#lit(st) => ::core::option::Option::Some(st),
                            _ => ::core::option::Option::None,
                        },
                        _ => ::core::option::Option::None,
                    }
                }
            }
        },
        None => quote!(),
    };

    // ── as_evaluable_bigrat: iff a BigRat wrapper exists (try_eval on its inner) ──
    let as_evaluable_bigrat: TokenStream =
        match wrappers.iter().find(|w| w.kind == NativeKind::CanonicalBigRat) {
            Some(w) => {
                let pv = w.proc_variant;
                quote! {
                    fn as_evaluable_bigrat(&self) -> ::core::option::Option<::mettail_runtime::CanonicalBigRat> {
                        match self {
                            #proc_cat::#pv(r) => r.as_ref().try_eval(),
                            _ => ::core::option::Option::None,
                        }
                    }
                }
            },
            None => quote!(),
        };

    // ── as_int_bin / as_float_bin / as_fixed_bin: the nested same-op fast-path consulted by the
    //    NATIVE reductions. Emitted only for native binary casts of the given arity — the redex
    //    lives in the inner numeric category, wrapped by its Proc wrapper (`ProcInt(Int::IntBin)`).
    //    Object casts have no entry here: their nesting reduces child-first via saturation (see the
    //    `to_numeric_input` (b) note). ──
    let nested_hook = |arity: Arity, method: &str| -> TokenStream {
        let arms: Vec<TokenStream> = folds
            .iter()
            .filter(|f| f.flavor == Flavor::Native && f.is_binary && f.arity == Some(arity))
            .filter_map(|f| {
                let fl = f.label;
                // redex lives in the inner category, wrapped by its Proc wrapper.
                let w = wrapper_for_inner(f.output_cat)?;
                let pv = w.proc_variant;
                let ic = w.inner_cat;
                Some(quote! {
                    #proc_cat::#pv(x) => match x.as_ref() {
                        #ic::#fl(a, w) =>
                            ::mettail_runtime::CastWidth::into_width_i64(w.as_ref())
                                .map(|wi| (a.as_ref(), wi)),
                        _ => ::core::option::Option::None,
                    },
                })
            })
            .collect();
        if arms.is_empty() {
            return quote!();
        }
        let m = Ident::new(method, proc_macro2::Span::call_site());
        quote! {
            fn #m(&self) -> ::core::option::Option<(&Self, i64)> {
                match self {
                    #(#arms)*
                    _ => ::core::option::Option::None,
                }
            }
        }
    };
    let as_int_bin = nested_hook(Arity::Int, "as_int_bin");
    let as_float_bin = nested_hook(Arity::Float, "as_float_bin");
    let as_fixed_bin = nested_hook(Arity::Fixed, "as_fixed_bin");

    let proc_to_numeric_input = quote! {
        #gate
        impl ::mettail_runtime::ProcToNumericInput for #proc_cat {
            #to_numeric_input
            #peel_method
            #as_numeric_str
            #as_evaluable_bigrat
            #as_int_bin
            #as_float_bin
            #as_fixed_bin
        }
    };

    // ── CastResult: only for object-output languages ──
    let has_object = folds.iter().any(|f| f.flavor == Flavor::Object);
    let cast_result: TokenStream = if has_object {
        // builder for an arity → the wrapper constructor + inner literal.
        let builder = |arity: Arity, kind_filter: &dyn Fn(NativeKind) -> bool, val: &Ident| -> TokenStream {
            match wrappers.iter().find(|w| kind_filter(w.kind)) {
                Some(w) => {
                    let pv = w.proc_variant;
                    let ic = w.inner_cat;
                    let lit = &w.literal;
                    quote!(#proc_cat::#pv(::std::sync::Arc::new(#ic::#lit(#val))))
                },
                None => {
                    let _ = arity;
                    quote!(compile_error!("object-output language missing a numeric cast wrapper"))
                },
            }
        };
        // Err constructor: a nullary Proc rule labelled `Err`.
        let err_ctor = language.terms.iter().find(|r| {
            &r.category == proc_cat
                && r.label == "Err"
                && r.term_context.as_ref().map_or(true, |ps| {
                    ps.iter().all(|p| !matches!(p, TermParam::Simple { .. }))
                })
        });
        let err_expr = match err_ctor {
            Some(r) => {
                let l = &r.label;
                quote!(#proc_cat::#l)
            },
            None => quote!(compile_error!(
                "object-output numeric casts require a nullary `Err` constructor on the object category"
            )),
        };
        let n = Ident::new("n", proc_macro2::Span::call_site());
        let f = Ident::new("f", proc_macro2::Span::call_site());
        let from_int = builder(Arity::Int, &|k| matches!(k, NativeKind::Int32 | NativeKind::Int64 | NativeKind::Int8 | NativeKind::Int16 | NativeKind::Int128 | NativeKind::Isize), &n);
        let from_uint = builder(Arity::UInt, &|k| matches!(k, NativeKind::UInt32 | NativeKind::UInt8 | NativeKind::UInt16), &n);
        let from_float = builder(Arity::Float, &|k| matches!(k, NativeKind::Float64 | NativeKind::Float32), &f);
        let from_fixed = builder(Arity::Fixed, &|k| matches!(k, NativeKind::CanonicalFixedPoint), &f);
        let from_bigint = builder(Arity::BigInt, &|k| matches!(k, NativeKind::CanonicalBigInt), &n);
        let from_bigrat = builder(Arity::BigRat, &|k| matches!(k, NativeKind::CanonicalBigRat), &n);
        quote! {
            #result_gate
            impl ::mettail_runtime::CastResult for #proc_cat {
                fn err() -> Self { #err_expr }
                fn from_int(n: i64) -> Self { #from_int }
                fn from_uint(n: u32) -> Self { #from_uint }
                fn from_float(f: ::mettail_runtime::CanonicalFloat64) -> Self { #from_float }
                fn from_fixed(f: ::mettail_runtime::CanonicalFixedPoint) -> Self { #from_fixed }
                fn from_bigint(n: ::mettail_runtime::CanonicalBigInt) -> Self { #from_bigint }
                fn from_bigrat(n: ::mettail_runtime::CanonicalBigRat) -> Self { #from_bigrat }
            }
        }
    } else {
        quote!()
    };

    // Each impl already carries its own gate (`#gate` / `#result_gate`) per the per-item
    // gating rule above, so this is a flat concatenation.
    quote! {
        #cast_width_impls
        #proc_to_numeric_input
        #cast_result
    }
}
