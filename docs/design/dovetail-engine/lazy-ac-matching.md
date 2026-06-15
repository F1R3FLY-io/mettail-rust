# In-Engine Lazy AC (Associative-Commutative) Rewrite Matching

Status: Step 1 + Step 2 implementation (branch `feature/wfst-architecture`).

## Problem

The Ambient calculus parallel composition `PPar` is an associative-commutative
(AC) operator: `{P, Q, R}` is a multiset (`HashBag<Proc>`), so any reordering or
re-association denotes the same process. Its reduction rules match a *sub-multiset*
of the bag and leave the remainder (`...rest`) as an AC complement:

```
OpenRule . |- (PPar {(POpen N P), (PAmb N Q), ...rest}) ~> (PPar {P, Q, ...rest});
```

The shared name `N` is a non-linear constraint: the `open(N,·)` and the ambient
`N[·]` must agree on `N`. Every distinct way of choosing the `(POpen, PAmb)` pair
out of the bag (that satisfies the shared-`N` constraint) is a *distinct*
reduction — these must all survive as separate alternatives.

Before this work, `PPar` lowered to an OPAQUE LEAF in the Dovetail report
compiler (`opaque_leaf_expr`), so the bag's structure was invisible to the
e-graph and AC rules could not fire at all.

## Three governing mandates (hard constraints)

1. **Ambiguity preserved end-to-end.** Every valid AC sub-multiset matching is a
   DISTINCT alternative. Weight ORDERS, never PRUNES; all equal-weight pairings
   survive extraction. (Mirrors `NBestExtraction.v` `equal_weight_both_survive`.)
2. **Laziness.** AC sub-multiset selection is materialized ON DEMAND via a lazy
   `Iterator`, never an eager `Vec` of all selections (AC selection is
   exponential). Mirrors the single-index-advance shape of `enum_vectors`.
3. **Exact keys, no lossy hash.** AC canonicalization is a sorted EXACT
   `ContentKey`, never a 64-bit hash. AC stays OUT of `ENode`/hashcons identity
   (which is order-sensitive by design); the n-ary bag node's children are merely
   stored in canonical (sorted) order as a *hint*.

## Step 1 — Canonical n-ary PPar lowering + canonicalization proof

### Engine (`dovetail/src/egraph.rs`)

Two new public helpers (require `L: SemanticHash`):

- `canonical_class_key(&self, class) -> ContentKey`: the exact content key of a
  class's canonical representative. The representative is chosen
  deterministically: the e-node in `nodes(find(class))` whose own
  `content_key()` is minimal (a total order over the class's exact node keys).
  Ties are impossible because `rebuild_exact_indices` deduplicates exact nodes,
  so distinct nodes have distinct keys. For a class with no live nodes the key
  is the framed class id (defensive; never reached for live classes).
- `ENode::ac_content_key(&self, &eg) -> ContentKey`: `op` content bytes, then the
  SORTED vector of `canonical_class_key(child)` for each child, each
  `write_framed`. Sorting makes the key invariant under child permutation — the
  AC/commutative identity at the key level.

These give a *commutative* key WITHOUT changing `ENode::content_key` (which stays
order-sensitive and is the hashcons identity). They are used by the lowering to
choose a canonical stored order, and by the Step-2 matcher to recompute the
multiset identity FRESH from current UF-reps.

### Macro (`macros/src/gen/runtime/dovetail_report.rs`)

`VariantKind::Collection` and the optional-collection branch of `field_child_expr`
now lower a `HashBag<ElemCat>` to an n-ary `ENode`:

- Iterate `bag.iter_elements()` (each element with multiplicity), lower each
  element through the element category's `__mettail_dovetail_add_<cat>` fn to an
  `EClassId`.
- Collect the child `EClassId`s, SORT them by `eg.canonical_class_key(child)`
  (deterministic canonical bag order), then
  `eg.add(ENode::new("<lang>::<cat>::<label>", sorted_children))`.

The label keeps the same `<lang>::<Category>::<Label>` scheme as scalar
constructors so the same op-string identifies the bag operator across the
e-graph and the AC rule's `op`.

`premise_supported` is made EXHAUSTIVE over every `Premise` variant (no
`_ => false` catch-all): `Congruence => true`; `Freshness`, `RelationQuery`,
`ForAll`, `BehavioralGuard`, `SyntheticInjGuard => false`.

### R1 mitigation (rebuild / hashcons-vs-AC-order subtlety)

`rebuild` re-canonicalizes every child to its UF representative and may reorder
or merge nodes. If the AC match relied on the *stored* child order being the
canonical sorted order, a post-merge re-canonicalization could change the order
and lose a match. **Mitigation:** the stored sorted order is only a HINT. The
Step-2 matcher computes the canonical multiset of the bag node FRESH at match
time from `eg.find(child)` for each current child, and binds `...rest` by
building a fresh canonical n-ary node via `try_add_with_budget` (which itself
canonicalizes). So correctness never depends on the stored order surviving
`rebuild`. The sorted store merely makes two equal bags hashcons together more
often (a dedup win), and is proven order-invariant at the key level by
`canon_iff_permutation`.

### Proof (`dovetail/formal/rocq/theories/Lowering/CollectionAcLowering.v`)

Model a bag's children as `list nat` (an injective `ContentKey` standin, exactly
as `NBestExtraction.v`/`EnumerationCompleteness.v` model keys as `nat`).
`canon := sort` via Stdlib `Mergesort` (`NatSort`).

**`canon_iff_permutation : forall b b', Permutation b b' <-> canon b = canon b'`.**

- Forward (`Permutation b b' -> canon b = canon b'`): `sort` of two permutations
  are both `Sorted` and both permutations of each other (`Permuted_sort` +
  `Permutation` transitivity/symmetry), so by `Sorted`-permutation uniqueness
  (`Sort_unique` / `StronglySorted` antisymmetry of `Nat.leb`) they are equal.
- Backward (`canon b = canon b' -> Permutation b b'`): `b ~ sort b = sort b' ~ b'`
  by `Permuted_sort` on both sides + transitivity.

This is the **no-collision / no-alias guarantee**: two bags get the same canonical
key IFF they are the same multiset (a permutation). No distinct multiset aliases
onto another (soundness of the dedup), and no equal multiset is split into two
keys (completeness of the dedup).

## Step 2 — `OpenRule` AC redex end-to-end

### Engine (`dovetail/src/rules.rs`)

New pattern variant:

```rust
Pattern::AcApp { op: L, fixed: Vec<Pattern<L>>, rest: Option<String> }
```

with a `Pattern::ac(op, fixed, rest)` builder.

`collect_matches` arm for `AcApp`:

1. Find a bag `ENode` in `class` with `enode.op == op` and
   `enode.children.len() >= fixed.len()`.
2. Canonicalize the children to current UF-reps (`eg.find`), forming the working
   multiset `bag`.
3. Enumerate sub-multiset selections of size `|fixed|` LAZILY via
   `lazy_ac_select(bag, k)` — combinations of indices advanced one position at a
   time (mirrors `enum_vectors`'s single-coordinate increment). Each selection
   yields `(selected: Vec<EClassId>, complement: Vec<EClassId>)`.
4. For each selection, enumerate PERMUTATIONS pairing `fixed[i]` to the selected
   children (a position assignment), and recurse `collect_matches(fixed[i],
   selected[π(i)], …)`. The existing non-linear `Var` re-bind check
   (`collect_matches`/`Var` arm) prunes pairings whose shared `N` disagrees — BY
   EVIDENCE, never speculatively.
5. Bind `rest` (if `Some`) to the complement as a FRESH canonical n-ary `ENode`
   via `try_add_with_budget` (budget-gated, honest `NodeLimit`). The `rest`
   binding inserts the complement class id into the substitution under the
   `rest` name.
6. Each surviving `(root, subst)` is pushed as a DISTINCT alternative.

`instantiate` handles `AcApp` on the RHS: instantiate each `fixed[i]` and, if
`rest` is `Some`, the bound complement class, then build the result bag with
`try_add_with_budget`. (For `OpenRule` the RHS is the *positional* `PPar {P, Q,
...rest}`, so the RHS uses `AcApp` with `fixed = [P, Q]`, `rest = Some("rest")`.)

Laziness: `lazy_ac_select` returns an `Iterator` (`LazyAcSelect`) holding only the
current `k`-combination of indices and advancing ONE index per `next()`
(lexicographic next-combination, O(k); never a `Vec` of all selections —
`lazy_ac_select_is_lazy_partial_consumption` pulls 3 of C(40,5)≈658k without
materializing the rest). Permutation enumeration over `|fixed|` positions is
bounded by `|fixed|!` which is tiny (2 for OpenRule). Budget gating on the fresh
complement node keeps growth honest (`NodeLimit` reported, never silent).

`search` takes `&mut self` because AC matching materializes a fresh canonical
n-ary `op` node per `rest` complement (`add_canonical_bag`, budget-gated) — an
honest, bounded e-graph growth; positional matching adds nothing. The complement
node is only created when a pairing survives (`paired.is_empty()` ⇒ skip). The
node-iterating arms snapshot the class's nodes (clone children) before the
`&mut self` recursion to avoid a borrow conflict.

### Macro (`macros/src/gen/runtime/dovetail_report.rs`)

New submodule `dovetail_report/ac.rs` (`pub(crate) mod ac;`) with
`lower_ac_collection(language, op_label, coll_pattern) -> Result<TokenStream,
String>` emitting a `Pattern::ac(op, fixed, rest)` from an
`AstPattern::Collection`:

- `op` = the enclosing constructor's resolved Dovetail label (passed in by the
  caller, which knows the constructor; the collection pattern itself carries no
  constructor — see the `Pattern::Collection` doc).
- `fixed` = each element lowered via `super::pattern_to_dovetail`.
- `rest` = `coll.rest.map(|id| id.to_string())`.
- Only `HashBag` (or the inferred `None`) is accepted; an explicit non-`HashBag`
  type returns `Err` (fail closed — matches the engine's HashBag-only AC support).

Dispatch is in `pattern_term_to_dovetail`'s `Apply` arm: a constructor whose SOLE
argument is a `Collection` (`[AstPattern::Collection { .. }]`) emits the `AcApp`
with `op = constructor label` via `ac::lower_ac_collection`, rather than wrapping
a positional `App`. `pattern_to_dovetail`'s bare-`Collection` arm stays an `Err`
(a collection with no enclosing constructor has no operator and the grammar does
not produce one). `Map` / `Zip` STAY `Err`.

**Generalization beyond OpenRule (the principled solution).** Because the dispatch
fires for ANY constructor-with-a-collection-argument, ALL Ambient `PPar`
collections lower to `AcApp` uniformly — including the NESTED `PPar`s of `InRule`
/ `OutRule` (e.g. `PAmb N (PPar { ... })` lowers to a `PAmb` app whose second
child is itself an `AcApp`). The engine's recursive matcher handles nested
`AcApp` (the `collect_matches` AcApp arm recurses through `pair_fixed`), so the
lowering need not special-case OpenRule. The Step-2 TEST scope is OpenRule, but
the lowering + engine are general. `ScopeExtrusion` (an equation with a freshness
premise) is still rejected by `premise_supported`; the congruence rules
(`ParCong`/`NewCong`/`AmbCong`) are still supplied by e-graph congruence closure.

### Proof additions (`CollectionAcLowering.v`)

Mirror `enum_vectors_complete`/`sound` for sub-multiset selection. A selection is
modeled the way the position-based lazy iterator actually produces it: `bag` is an
INTERLEAVING (a *split*) of a chosen sub-sequence `sel` and the complementary
sub-sequence `comp` — at each position the iterator either TAKEs the element into
`sel` or SKIPs it into `comp`. `is_split bag sel comp` is that take/skip merge
(an inductive relation). This is the faithful positional semantics; it then
connects to the multiset reading via `Permutation` (`split_permutation`,
`ac_select_partitions_bag`).

- `ac_select (bag : list nat) (k : nat) : list (list nat * list nat)` —
  `select_lists`, enumerating every size-`k` split `(sel, comp)` by a single
  take-or-skip decision per position (mirrors `enum_vectors`'s single-coordinate
  advance).
- **`ac_select_complete`**: `is_split bag sel comp -> length sel = k -> In (sel,
  comp) (ac_select bag k)` (NO-MISS: every size-`k` split is enumerated).
- **`ac_select_sound`**: `In (sel, comp) (ac_select bag k) -> is_split bag sel
  comp /\ length sel = k` (NO-FABRICATION).
- **`ac_select_iff`**: the bidirectional contract.
- **`ac_select_partitions_bag`**: `In (sel, comp) (ac_select bag k) ->
  Permutation bag (sel ++ comp) /\ length sel = k` — the multiset reading
  (`sel`, `comp` partition the bag; no element lost or fabricated).
- Corollary `ac_lowering_requirements_covered`: one-line
  `apply every_requirement_constructor_is_covered` (reusing `ReqCollectionPattern`
  → `CapPatternLowering`; NO new requirement constructor).

Why a split rather than a `bag_minus`-fixed remainder: distinct OCCURRENCES of an
equal value selected from a bag denote the SAME multiset, but a `remove_first`-keyed
remainder would force a single canonical remainder per value and could not be made
to agree with a faithful occurrence-based iterator (a duplicate value chosen from a
later position leaves a list-distinct-but-multiset-equal remainder). The `is_split`
model captures the genuine positional truth and `split_permutation` recovers the
multiset complement exactly; the AC ambiguity that must survive (distinct VALUES,
e.g. `n[B]` vs `n[C]`) is preserved because those are distinct positions with
distinct `comp` lists AND distinct canonical keys downstream.

### `GeneratedReportCompiler.v` additions

- New `GeneratedPatternClass` constructor `GPatAcStructuralApply`.
- `pattern_supported GPatAcStructuralApply => true` (keep `GPatCollectionMeta =>
  false` — the *unlowered* meta-collection class still rejects; the new class is
  the *lowered* AC apply).
- `pattern_requirements GPatAcStructuralApply => [ReqExactContentKey]` (so
  `supported_patterns_have_only_exact_key_requirement` extends by one `destruct`
  case; the AC node's identity is still an exact content key).
- Each partition theorem's `destruct p`/`destruct (classify_rule …)` gains the
  new case (same tactic shape).
- The rejection theorems (`collection_lhs_is_rejected`, `binder_lhs_is_rejected`,
  `substitution_lhs_is_rejected`) MUST stay `reflexivity` — `GPatCollectionMeta`
  still rejects.
- New `ac_structural_lhs_is_lowered` proving an `AcApp`-LHS rule with supported
  RHS + congruence/empty premises classifies as `LoweredAsDovetailRule`.

## Tests

- `dovetail/tests/ac_ambiguity.rs`: seed `open(n,A) | n[B] | n[C]` as a bag
  `PPar{POpen n A, PAmb n B, PAmb n C}`. Wait — `OpenRule` matches `(POpen N P),
  (PAmb N Q)`: with `POpen n A` and TWO ambients `n[B]`, `n[C]` sharing `N = n`,
  there are TWO valid pairings: `(POpen n A, PAmb n B)` leaving `{n[C]}` as rest
  → result `{A, B, n[C]}`; and `(POpen n A, PAmb n C)` leaving `{n[B]}` → result
  `{A, C, n[B]}`. Assert BOTH results survive as distinct equal-weight roots
  (distinct `ContentKey`) and `completeness == Complete`. Mirrors
  `extract.rs::tests::t2_ambiguous_hand_built_no_miss`.
- `dovetail/tests/ac_lowering_shape.rs`: assert the lowered `AcApp` shape (op,
  fixed arity, rest) and that a bag node's children are stored sorted by
  `canonical_class_key`.

## Verification gates

- `cargo build -p dovetail -p mettail-languages --features ambient`.
- `cargo test -p dovetail` (incl. new tests) green.
- `theories/Lowering/CollectionAcLowering.vo` compiles; `rocq-dovetail` +
  `rocq-critical-zero-admission` green (the authoritative no-admit gate).
- Existing Ambient tests still pass (`gen_ambient_rewrite`, `ambient_tests`).
</content>
</invoke>
