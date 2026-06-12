# Dovetail Increment 6 — Newton-SCC cyclic inside-weight closure

> Plan-agent design (2026-06-09). Make the **inside weight** exact on cyclic
> e-graphs via `rigail::solve_scc_weights_newton`, so the 1-best + the A*/KA*
> heuristic are exact on cycles. **Honest scope (a):** enumeration (k≥2) stays
> acyclic-with-cycle-cut (`had_cycle_cut()` surfaces the boundary); full cyclic
> k-best enumeration (Eppstein-style) is a later increment. Nothing
> reachable-and-finite is dropped from the 1-best; the only residual
> incompleteness (infinite cycle-unrolled k-best) is FLAGGED, never silent.

## Weight bound
`W: StarSemiring` on the new path ONLY (`inside_weights_closed`, `with_heuristic`);
`Extractor`/`kth`/`derivations` keep `W: BestOrder`. Both `TropicalWeight`
(`rigail/src/lib.rs:759`) and `LexicographicWeight` (`lex_weight.rs:563`) impl
`StarSemiring` ⟹ `StarSemiringRef` by blanket ⟹ Newton-callable. `max_iters = 64`
(matches prattail; idempotent semirings converge in O(scc_size)).

## scc.rs (NEW, crate-private) — deterministic iterative Tarjan
Class-dependency graph: `q → c` iff some e-node of `q` has a child with
`find(child)==c`. Port prattail's proven iterative Tarjan (`sppf.rs:1142-1208`),
e-graph-typed. **Sort class ids before indexing** (HashMap order is
nondeterministic; the crate's `t7_determinism` invariant requires reproducible
SCCs). `has_self_loop(eg,q)` = some node of q has a child `find()`-ing to q.
SCCs returned in reverse-topological order (leaf SCCs first) — children solved
before parents read them as out-of-SCC constants.

## wta.rs — `inside_weights_closed` (where W: StarSemiring) + `solve_scc`
Driver:
1. `let mut inside = self.inside_weights();` (acyclic seed; partial on cycles)
2. `for scc in tarjan_sccs(eg)`: skip trivial (`len==1 && !has_self_loop`);
   else `let solved = solve_scc(scc, &inside); for (i,q) in scc { inside.insert(q, solved[i]); }`
3. return inside.

**★ LOAD-BEARING (no double-star):** dovetail WRITES Newton's result directly
(it is the COMPLETE closed inside weight). Do NOT post-multiply by `star_ref()`
the way prattail's `wpda_walker.rs:5146` does — prattail's memo holds
acyclic-unrolled contributions and uses the aggregate as a correction multiplier;
dovetail's fixpoint is from-scratch and Newton replaces it. Double-star = bug
(caught by Test A's 2-node SCC).

`solve_scc(scc, inside) -> Vec<W>` (e-graph port of `sppf.rs::factor_scc_packing`
+ `wpda_walker.rs::solve_scc_aggregate`):
- `idx: HashMap<EClassId,usize>` = SCC-local indices.
- For each in-SCC class `scc[i]`, each `node ∈ nodes(scc[i])`: build a
  `PackingFactored<W>`:
  - `target_i = i`
  - `outside_product = weigh(node) ⊗ Π_{child, find(child)∉SCC} inside[find(child)]`
    (default `W::one_ref()` if a child class absent)
  - `in_scc_children = [ idx[find(child)] for child in node.children if find(child)∈SCC ]`
    (SOURCE ORDER — matters for the Leibniz differential)
- `rigail::solve_scc_weights_newton(scc.len(), &packings, 64)` → `Vec<W>`.
- Self-loop singleton (`x = a | f(x)`): the `f(x)` node → `in_scc_children=[0]`,
  the `a` node → exit packing (`in_scc_children=[]`, feeds `b`); hits Newton's
  linear fast-path (exact in one Lehmann step).

## extract.rs — heuristic routed through closed inside; honest docs
`with_heuristic` tightened to `where W: StarSemiring`, computes the CLOSED inside
(reuse `wta::inside_weights_closed(egraph, &weigh)` — a free fn taking `&F` so it
shares with `EGraphDfta`). The admissible reachability skip is now exact on
cycles (still admissible: never over-estimates "best"). Enumeration core
UNCHANGED (the `on_stack` cut + `had_cycle_cut` stay). Update module `## Cycles`
doc: "inside weights / 1-best are EXACT on cycles (Newton-closed); exhaustive
k-best ENUMERATION across back-edges remains cut and is reported by
`had_cycle_cut`; full cyclic k-best is a later increment."

## Tests
- **A (wta):** `x = a|f(x)` tropical (a↦5,f↦1) ⟹ `inside_closed(P)=5` (cycle only
  worsens); `y=b|f(y)` (b↦3)⟹3; a 2-node SCC (u=f(v)|c1, v=g(u)|c2) hand-solved
  (exercises non-singleton + catches double-star); acyclic re-run == fixpoint.
- **B (extract):** extractor 1-best on the cycle == `inside_closed[P]`.
- **C (extract):** `derivations(P)` terminates, yields the acyclic `a`,
  `had_cycle_cut()==true`.
- **D (extract):** heuristic invariance on a cyclic graph (plain vs `with_heuristic`
  identical stream).
- **E (scc):** Tarjan SCC partition reproducible across two builds (determinism).

## FV obligation (implemented; zero-admission)
Record in a `wta.rs` doc block: the SCC→`PackingFactored` lowering is a syntactic
re-indexing of the e-graph inside-weight recurrence (in-SCC unknowns named by
SCC-local index; out-of-SCC terms pre-evaluated constants); given that equality,
the Esparza–Kiefer–Luttenberger correctness of `solve_scc_weights_newton` (Newton
computes the least fixpoint of `Y=f(Y)` on an ω-continuous semiring) yields the
exact `⊕`-aggregate. The lowering-equivalence lemma is the one dovetail-specific
obligation and is proven in
`dovetail/formal/rocq/theories/InsideWeights/InsideWeightSccClosure.v`.

## Files
Implemented in `dovetail/src/scc.rs`, `dovetail/src/wta.rs`, and
`dovetail/src/extract.rs`. No rigail/Cargo change was required.
