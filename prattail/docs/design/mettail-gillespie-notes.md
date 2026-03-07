# MeTTaIL-Gillespie Integration Notes

Architectural notes for the future integration of PraTTaIL's semiring and
lattice infrastructure with the MeTTaIL-Gillespie stochastic/quantum simulation
prototype (`/home/dylon/Workspace/f1r3fly.io/MeTTaIL/MeTTaIL-Gillespie/`, ~4000 LOC).

## 1. Critical Bug: Decoupled Weight Systems

The prototype fuzzer production weights (`Production::weight`) and the
simulator propensities (`RateMap`) are completely independent — changing one
does not affect the other. This means the fuzzer generates terms at frequencies
unrelated to the simulator's actual transition rates. Fix requires a shared
`LogWeight`-based training infrastructure where both systems derive weights
from the same source.

## 2. Reusable PraTTaIL Infrastructure

The following PraTTaIL components are directly applicable to MeTTaIL-Gillespie:

| Component | Location | Gillespie Use |
|-----------|----------|---------------|
| `Semiring` trait | `semiring.rs` | Weight algebra unification |
| `LogWeight` | `semiring.rs` | Numerically stable propensity computation |
| `AmplitudeWeight` | `semiring.rs` | Quantum CTMC amplitude propagation |
| `TokenLattice<T, S, W>` | `lattice.rs` | `ReactionLattice` for BFS state-space exploration |
| `forward_scores` / `backward_scores` / `total_weight` | `lattice.rs` | Trajectory analysis |
| `RuleWeights` / `TrainedModel` / `SpilloverTrainer` | `training.rs` | Fuzzer-simulator weight unification |
| `log_push_weights` | `log_push.rs` | Propensity normalization |
| `ProductWeight<S1, S2>` | `semiring.rs` | Multi-criteria (amplitude × classical priority) |

## 3. Key Types to Migrate

From `MeTTaIL-Gillespie/src/`:

- **`RateValue`** (real/complex dual) — replace with `LogWeight` for classical
  rates and `AmplitudeWeight` for quantum amplitudes; bridge via
  `AmplitudeWeight::from_log_weight()`.
- **`SpatialBehavior`** enum (`Null`, `Local`, `Interaction`, ...) — spatial
  annotation on reactions; independent of semiring, migrate as-is.
- **`RateMap`** — internally `Vec<(SpatialBehavior, LogWeight)>` after migration.
- **`AugmentedRewriteRule<W: Semiring>`** — generic over weight type for
  classical (`LogWeight`) vs. quantum (`AmplitudeWeight`) simulation.
- **`ClassicalGillespie`** — SSA with `LogWeight` propensity.
- **`QuantumGillespie`** — CTMC with `AmplitudeWeight`.
- **`Fuzzer`** — weighted term generation with `LogWeight`.

## 4. Spec Extensions Planned

- `where { T1 => 0.5, T2 => 0.3 }` — rate annotations on rewrite rules
- `producing { local(n) => 0.5 }` — output rate annotations
- `properties { ... }` block with 6 property classes + proptest codegen
- Weighted bisimilarity (Dubut & Wissmann 2023)

## 5. Weight Derivation Hierarchy

When no user annotations are provided, weights are derived in increasing
priority order:

| Level | Source | Description |
|-------|--------|-------------|
| 0 | Uniform | Maximum entropy (all transitions equally likely) |
| 1 | Structure-derived | From WFST compile-time weights |
| 2 | Observation-refined | Via `SpilloverTrainer` from observed traces |
| 3 | User-supplied | Explicit `where`/`producing` clause annotations |

Higher levels override lower levels. Level 0 is the default when no other
information is available. Level 1 provides structure-aware defaults from the
grammar topology. Levels 2–3 incorporate runtime/user knowledge.
