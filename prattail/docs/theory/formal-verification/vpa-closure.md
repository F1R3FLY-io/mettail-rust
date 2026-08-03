# Rocq verification of VPA closure and exact decisions

## Artifact set

PraTTaIL splits its VPA argument across four assumption-free Rocq files:

| Artifact | Mechanized concern |
|---|---|
| `VpaClosureProperties.v` | final-state acceptance, deterministic complement, synchronized product intersection, equivalence reduction |
| `VpaDelimiterSoundness.v` | typed delimiter pairing, mismatch preservation, unbounded-depth counterexample |
| `VpaReachability.v` | balanced-summary leastness and sound/complete exact emptiness abstraction |
| `VpaDeterminization.v` | $`(S,R)`$ transition equations and same-stack-symbol return correlation |

All reside in
`formal/rocq/mathematical_analyses/theories/` and are registered in that
suite's `_CoqProject`.

## Operational semantics

A configuration contains a control state and the frames above the permanent
bottom marker. The proof represents the permanent marker by the empty list:

- an internal edge preserves the list;
- a call conses one frame;
- an above-bottom return removes the head frame;
- a bottom return uses a separate edge relation and preserves the empty list.

Acceptance requires a final state but permits any residual list. This matches
`WeightedVpa::weighted_run`; it deliberately does not impose empty-stack
acceptance.

## Closure proof

`VpaClosureProperties.v` first proves that deterministic complementation
flips final-state acceptance for every word:

```coq
Theorem complement_correctness : forall w,
  complement_accepts w = true <-> accepts w = false.
```

Because acceptance does not require an empty residual stack, the theorem has no
spurious well-matchedness side condition. The involution theorem then shows
that flipping twice restores the original acceptance predicate.

For intersection, both automata use the same visible symbol class at each
input position. Product states and product stack symbols therefore advance in
lockstep. Projection lemmas prove that the product run's two components equal
the corresponding source runs; intersection correctness follows:

```coq
Theorem intersection_correctness : forall w,
  prod_accepts w = true <-> accepts w = true /\ accepts2 w = true.
```

The equivalence theorem reduces equality to emptiness of both Boolean
differences. The Rust implementation supplies the concrete exact emptiness
procedure described below.

## Balanced-summary emptiness proof

The least relation `balanced_summary p q` has four constructors:

1. identity;
2. an internal edge;
3. composition of two summaries;
4. a call and return that share one pushed frame around a nested summary.

`balanced_summary_run_sound` proves by induction that every summary denotes a
concrete word which leaves any surrounding stack unchanged.
`balanced_summary_is_least` proves that every relation closed under the four
rules contains this inductively generated relation.

Ground reachability begins in an initial state and closes under balanced
summaries and bottom returns. Prefix reachability additionally closes under
calls whose frames may remain unmatched at the accepting state. The theorems
`ground_reachable_run_sound` and `prefix_reachable_run_sound` construct
concrete runs. For the converse, `normalized_reachable` represents every
concrete configuration as ground reachability followed by zero or more
unmatched frames whose current segments are balanced summaries.
`steps_preserve_normalized` proves that every operational transition
preserves this form, and `normalized_implies_prefix` projects it back to the
finite prefix relation. Therefore
`summary_operational_nonempty_iff` proves exact equivalence between summary
nonemptiness and operational final-state nonemptiness.

Executable property tests additionally compare the Rust matrix/work-queue
saturation with independent graph and bounded-word oracles.

## Determinization invariant

A deterministic state is:

```coq
Record det_state : Type := DetState {
  summary : State -> State -> Prop;
  reachable : State -> Prop
}.
```

The matched-return bridge quantifies one frame `pushed` and uses that same
witness in the opening call and closing return. Consequently:

- `matched_return_reachable_iff` unfolds the exact successor equation;
- `matched_return_uses_one_stack_witness` exposes the correlation witness;
- `cross_gamma_cannot_create_bridge` excludes a successor assembled from
  incompatible call branches;
- `bottom_return_is_stack_neutral_relation` records bottom-return behavior;
- the update-totality theorems show every input pair has one mathematical
  successor, including the empty/dead pair.

## Rust correspondence

| Rocq definition | Rust counterpart |
|---|---|
| `transition_bottom_return` | return using `initial_stack_symbol` without `pop()` |
| `balanced_summary` | summary matrix and work queue in `decision::is_language_empty` |
| `ground_reachable` | first finite reachability phase |
| `prefix_reachable` | above-bottom phase with unmatched calls |
| `normalized_reachable` | completeness invariant for concrete configurations |
| `det_state` | private `DetState { summary, reachable }` |
| `return_bridge` | `matched_return_successor` |
| `relation_compose` | caller-summary composition |
| `bottom_return_update` | `bottom_return_successor` |

## Property-test counterparts

`prattail/tests/vpa_decision_soundness.rs` exercises proof invariants as
executable properties:

- repeated bottom returns preserve the bottom marker;
- accepting states may retain unmatched call frames;
- a 20-state language whose shortest witness reaches depth 91 defeats the old
  $`4|Q|+2`$ cutoff but is found by summaries;
- cross-gamma nondeterministic branches cannot create an accepting run;
- complement is total over missing transitions;
- false Boolean edges do not create support reachability;
- product stack-symbol encoding is injective;
- random internal-only emptiness matches an independent graph oracle;
- source and determinized membership agree for every generated short word.

## Running the proof

From the repository root:

```sh
make -C formal check-capped FORMAL_CAPPED_TARGET=rocq-mathematical-analyses
```

The capped runner limits memory, disables swap, uses one build job, and invokes
the suite's zero-admission checks. A direct source scan must also find no
`Axiom`, `Conjecture`, `Parameter`, `Admitted`, or `admit` command.

## References

- Rajeev Alur and P. Madhusudan, “Visibly Pushdown Languages,” STOC 2004.
  [DOI: 10.1145/1007352.1007390](https://doi.org/10.1145/1007352.1007390).
- Rajeev Alur and P. Madhusudan, “Adding Nesting Structure to Words,”
  *Journal of the ACM* 56(3), 2009.
  [DOI: 10.1145/1516512.1516518](https://doi.org/10.1145/1516512.1516518).
