# Stochastic Petri Nets

## What Is It?

A stochastic Petri net (SPN) extends the classical Petri net with **exponentially distributed firing delays** on each transition. This transforms the discrete event system into a continuous-time Markov chain (CTMC), enabling probabilistic analysis of concurrent systems. The simulation is driven by Gillespie's Stochastic Simulation Algorithm (SSA), which produces exact (not approximate) sample trajectories.

Located in `simulation/src/stochastic_petri.rs`.

## What Does It Do?

The stochastic Petri net module provides:

1. **StochasticPetriNet**: a Petri net where each transition has an associated rate parameter λ > 0.
2. **Gillespie SSA**: an exact simulation algorithm that produces a time-ordered sequence of firing events.
3. **Steady-state analysis**: multiple replica simulations with statistical aggregation.

## Why Was It Chosen?

### The Chemical Master Equation Analogy

Gillespie (1977) developed the SSA for simulating chemical reaction networks. The analogy to concurrent processes is direct:

| Chemistry                           | Process Algebra                    |
|-------------------------------------|------------------------------------|
| Molecules in a well-stirred reactor | Processes in parallel composition  |
| Chemical species                    | Channel names                      |
| Reactions                           | Communication rules (send/receive) |
| Reaction rates                      | Transition rates                   |
| Molecular counts                    | Token counts (Petri net marking)   |

The MeTTaIL language system defines process algebras (like Rholang) where parallel processes communicate via channels. A stochastic Petri net model of such a system enables:

- **Performance analysis**: mean time to reach a specific state
- **Throughput estimation**: average rate of communication events
- **Deadlock probability**: fraction of runs that deadlock
- **Bottleneck identification**: which transitions fire least frequently

### Exactness of Gillespie's SSA

Unlike approximate methods (tau-leaping, Euler-Maruyama), Gillespie's SSA produces **exact** samples from the underlying CTMC. Each sample trajectory is a valid realization of the stochastic process, with correct timing and transition selection probabilities. This is essential for simulation-based verification where statistical guarantees matter.

## Gillespie's SSA (Direct Method)

### The Algorithm

```
PROCEDURE gillespie_ssa(net, max_time, max_events, rng) → SimulationTrace:
    marking ← net.initial_marking
    time ← 0.0
    events ← []

    FOR _ in 0..max_events:
        // Step 1: Compute propensities
        props ← net.propensities(marking)
        a₀ ← Σ props                    // total propensity

        IF a₀ ≤ 0 THEN
            deadlocked ← true
            BREAK

        // Step 2: Sample time to next event
        //         τ ~ Exp(a₀), i.e., P(τ > t) = exp(-a₀ · t)
        u₁ ← rng.uniform(0, 1)
        τ ← -ln(u₁) / a₀
        time ← time + τ

        IF time > max_time THEN BREAK

        // Step 3: Select which transition fires
        //         P(transition j) = aⱼ / a₀
        u₂ ← rng.uniform(0, a₀)
        cumulative ← 0
        selected ← 0
        FOR j in 0..|transitions|:
            cumulative ← cumulative + props[j]
            IF cumulative ≥ u₂ THEN
                selected ← j
                BREAK

        // Step 4: Fire the selected transition
        marking ← fire(selected, marking)
        events.push(SimulationEvent { time, transition: selected, marking })

    RETURN SimulationTrace { events, final_time: time, final_marking: marking,
                              num_events: |events|, deadlocked }
```

### Propensity Computation

The propensity `aⱼ` of transition j at marking m is:

```
aⱼ = λⱼ × hⱼ(m)
```

where λⱼ is the base rate and hⱼ(m) is the **combinatorial function** counting the number of distinct enabled token combinations. In the implementation, hⱼ(m) is the minimum token multiplicity across input places:

```
PROCEDURE propensities(marking) → [f64]:
    FOR (i, transition) in transitions:
        IF is_enabled(i, marking) THEN
            min_mult ← min over (p, w) in transition.inputs:
                IF w == 0 THEN ∞ ELSE marking[p] / w
            props[i] ← transition.rate × min_mult
        ELSE
            props[i] ← 0.0
```

**Intuition:** If a transition requires 1 token from place P and P has 5 tokens, there are 5 distinct ways to fire the transition, so the propensity is 5 × λ. This is the mass-action kinetics assumption from chemistry.

### Exponential Firing Rates

Each transition fires after an exponentially distributed delay:

```
firing_time ~ Exp(aⱼ)

P(firing_time > t) = exp(-aⱼ · t)
E[firing_time] = 1/aⱼ
```

The memoryless property of the exponential distribution ensures that the next event depends only on the current marking, not on the history. This is what makes the process a Markov chain.

### The Race Condition

When multiple transitions are enabled simultaneously, they "race": each has its own exponential clock, and the one with the shortest firing time wins. The probability that transition j fires next is:

```
P(j fires next) = aⱼ / a₀ = aⱼ / Σᵢ aᵢ
```

and the time to the next event (regardless of which transition fires) is:

```
τ ~ Exp(a₀)
```

Gillespie's SSA exploits this by sampling τ and the transition index independently, avoiding the need to sample individual clocks for each transition.

## Data Structures

### StochasticTransition

```rust
pub struct StochasticTransition {
    pub transition: PetriTransition,  // base Petri net transition
    pub rate: f64,                    // firing rate λ > 0
}
```

### StochasticPetriNet

```rust
pub struct StochasticPetriNet {
    pub places: Vec<Place>,
    pub transitions: Vec<StochasticTransition>,
    pub initial_marking: Marking,
}
```

### SimulationEvent

```rust
pub struct SimulationEvent {
    pub time: f64,            // simulation time
    pub transition: usize,    // index of the transition that fired
    pub marking: Marking,     // marking after firing
}
```

### SimulationTrace

```rust
pub struct SimulationTrace {
    pub events: Vec<SimulationEvent>,
    pub final_time: f64,
    pub final_marking: Marking,
    pub num_events: usize,
    pub deadlocked: bool,
}
```

## Construction

### From Scratch

```rust
let mut net = StochasticPetriNet::new();
let buffer = net.add_place("buffer");
let produce = net.add_transition("produce", 1.0);  // rate = 1.0
let consume = net.add_transition("consume", 2.0);  // rate = 2.0
net.add_output(produce, buffer, 1);   // produce puts 1 token in buffer
net.add_input(consume, buffer, 1);    // consume takes 1 token from buffer
net.set_initial_tokens(buffer, 3);    // start with 3 tokens
```

### From a Base PetriNet

```rust
let snet = StochasticPetriNet::from_petri_net(&base_net, &[1.0, 2.0, 0.5]);
```

## Steady-State Analysis

The `steady_state_analysis()` function runs multiple replicas and computes statistics:

```
PROCEDURE steady_state_analysis(net, max_time, max_events, num_runs, rng):
    FOR _ in 0..num_runs:
        trace ← gillespie_ssa(net, max_time, max_events, rng)
        accumulate token counts, event counts, deadlock status

    RETURN SteadyStateStats {
        mean_tokens: [mean final tokens per place],
        stddev_tokens: [stddev of final tokens per place],
        mean_events: mean events per run,
        deadlock_fraction: fraction of runs that deadlocked,
        num_runs
    }
```

This provides confidence intervals for steady-state behavior, enabling questions like: "With 95% confidence, the average buffer occupancy is between 2.1 and 2.9 tokens."

## Deadlock Detection

A marking is **deadlocked** when no transition is enabled (total propensity = 0). The SSA detects this naturally: if all propensities are zero, the simulation terminates with `deadlocked = true`.

In the steady-state analysis, the `deadlock_fraction` field reports the proportion of runs that deadlocked. A non-zero deadlock fraction indicates a design flaw in the concurrent system.

## References

- Gillespie, D.T. (1977). "Exact Stochastic Simulation of Coupled Chemical Reactions." Journal of Physical Chemistry, 81(25), pp. 2340-2361.
- Molloy, M.K. (1982). "Performance Analysis Using Stochastic Petri Nets." IEEE Transactions on Computers, C-31(9), pp. 913-917.
- Murata, T. (1989). "Petri Nets: Properties, Analysis and Applications." Proceedings of the IEEE, 77(4), pp. 541-580.
