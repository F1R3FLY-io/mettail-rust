//! Original ordered WPDA category census and rule-coordinate indexing.
//!
//! The five census passes are relocated intact from the macro frontend.
//! Borrowed source readers replace only field observations; they run at the
//! original sites, including unseen-category gates and token short-circuiting.
//! No category classifier, normalized grammar reconstruction, or new ordering
//! policy is introduced. Rule/type/token payloads need not implement Clone.
//!
//! `CategoryCensusProjection.v` proves finite source/accessor correspondence,
//! output order, observation order, duplicate handling and index behavior.
//! This helper preserves the original narrowing casts and category indexing;
//! admission of untrusted inputs remains the caller's separate obligation.

/// Direct observations of original borrowed grammar occurrences.
///
/// Implementations must preserve the source's name spelling and field values.
/// Calls are lazy: an already-seen type suppresses eligibility reads, and a
/// nonliteral token suppresses its category read. No normalization is permitted
/// in these methods.
pub trait CategoryCensusReader {
    type Rule;
    type Type;
    type Token;

    fn rule_category(&mut self, rule: &Self::Rule) -> String;
    fn type_name(&mut self, category: &Self::Type) -> String;
    fn has_collection(&mut self, category: &Self::Type) -> bool;
    fn has_native(&mut self, category: &Self::Type) -> bool;
    fn from_literals(&mut self, token: &Self::Token) -> bool;
    fn token_category(&mut self, token: &Self::Token) -> Option<String>;
}

/// Collect categories in the original rule/literal/collection/native/remainder
/// pass order, retaining the first appearance within each pass.
pub fn collect_category_names_with_literals<A: CategoryCensusReader>(
    rules: &[A::Rule],
    types: &[A::Type],
    tokens: &[A::Token],
    reader: &mut A,
) -> Vec<String> {
    let mut seen = std::collections::BTreeSet::new();
    let mut categories = Vec::new();
    // Pass 1: categories that appear as rule LHS.
    for rule in rules {
        let cat = reader.rule_category(rule);
        if seen.insert(cat.clone()) {
            categories.push(cat);
        }
    }
    // Pass 2: categories with `from_literals` TokenDefs that weren't already
    // added. Iterate `language.types` for stable declaration order.
    for type_def in types {
        let cat = reader.type_name(type_def);
        if seen.contains(&cat) {
            continue;
        }
        let has_literal_block = tokens.iter().any(|td| {
            reader.from_literals(td) && reader.token_category(td).map(|c| c == cat).unwrap_or(false)
        });
        if has_literal_block {
            seen.insert(cat.clone());
            categories.push(cat);
        }
    }
    // Stage 1.3 (Pass 3): collection-typed categories (`![Vec<T>] as List`,
    // `![HashBag<T>] as Bag`, `![HashMap<K,V>] as Map`). These have
    // `collection_kind = Some(...)` but no user-written rules; the WPDS
    // codegen synthesizes `ListLit`/`BagLit`/`MapLit` rules in
    // `synthetic.rs` and they need their categories present here so the
    // synthesis loop can find their per-cat slot.
    for type_def in types {
        let cat = reader.type_name(type_def);
        if seen.contains(&cat) {
            continue;
        }
        if reader.has_collection(type_def) {
            seen.insert(cat.clone());
            categories.push(cat);
        }
    }
    // Stage 4 fix (Pass 4): native-type-only categories (e.g. Rholang's
    // `![bool] as Bool` and `![str] as Str` declared at type-level but
    // with no rules and no `literals { ... }` block). Cross-cat projection
    // rules in OTHER categories may reference these as source categories
    // (e.g., `CastBool . k:Bool |- k : Proc;`). Without the categories
    // present in `WPDA_CATEGORIES`, the emitted CrossCatDelegate falls
    // back to `source_src_idx: 0u16` (Proc) and the engine recurses into
    // Proc's PrefixDispatch on the same token. The synthetic atomic-literal
    // rule emitted in `synthetic.rs` for these native-type categories
    // gives them a self-contained sub-parser.
    for type_def in types {
        let cat = reader.type_name(type_def);
        if seen.contains(&cat) {
            continue;
        }
        if reader.has_native(type_def) {
            seen.insert(cat.clone());
            categories.push(cat);
        }
    }
    // Pass 5: any remaining user-declared `LangType` not covered above.
    // Examples: Ambient's `Name` (declared but with no LHS rules, no
    // literals block, no collection_kind, no native_type). These are
    // typically reference-only categories — their tokens are bound by
    // other rules' production bodies. `synthetic.rs` Phase 5a fabricates
    // a Var rule for any such category, giving them an identifier-shaped
    // parser. Without this pass the synthetic Var rule never gets emitted
    // (it's gated on the category being in `cat_idx` built from the
    // categories list returned here), and any rule body referencing the
    // category becomes unparseable.
    for type_def in types {
        let cat = reader.type_name(type_def);
        if seen.insert(cat.clone()) {
            categories.push(cat);
        }
    }
    categories
}

/// Index labels by their bucket owner, preserving original last-key overwrite
/// behavior and u16 casts. Every bucket indexes its category before visiting
/// rules, including empty buckets; this is not a bounds-checking admission API.
pub fn build_label_index_with<R>(
    categories: &[String],
    per_cat: &[Vec<R>],
    mut label: impl FnMut(&R) -> String,
) -> std::collections::HashMap<(String, String), (u16, u16)> {
    let mut idx = std::collections::HashMap::new();
    for (cat_i, rules) in per_cat.iter().enumerate() {
        let cat_name = &categories[cat_i];
        for (rule_i, rule) in rules.iter().enumerate() {
            idx.insert((cat_name.clone(), label(rule)), (cat_i as u16, rule_i as u16));
        }
    }
    idx
}
