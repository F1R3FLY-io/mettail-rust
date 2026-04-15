# Markov Decision Processes

## What Is It?

A Markov Decision Process (MDP) is a mathematical framework for sequential decision-making under uncertainty. An MDP extends a Markov chain with **actions**: at each state, an agent chooses an action, which determines the probability distribution over next states and the immediate reward. The goal is to find a **policy** (a mapping from states to actions) that maximizes the expected cumulative reward.

Located in `simulation/src/mdp.rs`.

## What Does It Do?

The MDP module provides:

1. **MDP data structure**: states, actions, probabilistic transitions, rewards, and a discount factor.
2. **Value iteration** (Bellman (1957)): computes the optimal value function V*(s) and extracts the optimal policy.
3. **Q-value computation**: evaluates Q(s, a) for all state-action pairs.
4. **Policy simulation**: executes a policy on the MDP with stochastic transitions.

## Why Was It Chosen?

### Optimal Scheduling of Rewrites

In a MeTTaIL language, multiple rewrite rules may be applicable at any given state. The choice of which rule to apply first affects:

- **Termination time**: some orderings reach normal form faster
- **Resource consumption**: some orderings produce smaller intermediate terms
- **Coverage**: some orderings exercise more rules

An MDP model of the rewrite system treats:
- States = terms (or term equivalence classes)
- Actions = applicable rewrite rules
- Transitions = probabilistic outcomes of applying a rule (nondeterministic choice modeled as probability)
- Rewards = negative step cost, or positive reward for reaching normal form

Value iteration then finds the optimal rewrite strategy: which rule to apply at each state to minimize expected cost.

### Adversarial Testing

MDPs also model **adversarial** environments. By treating the environment (nondeterministic choices in the language semantics) as an adversary that tries to maximize cost (or find bugs), the MDP framework generates worst-case test scenarios.

Combined with proptest, this enables adversarial property-based testing:

1. Build an MDP from the language's rewrite system.
2. Compute the adversarial policy (maximize probability of invariant violation).
3. Use the policy to guide term generation toward likely failure states.

### Theoretical Foundation

Bellman (1957) established the principle of optimality:

**Bellman's Principle:** An optimal policy has the property that whatever the initial state and initial decision are, the remaining decisions must constitute an optimal policy with regard to the state resulting from the first decision.

This leads to the Bellman optimality equation:

```
V*(s) = max_a Σ_{s'} P(s'|s,a) [R(s,a,s') + γ · V*(s')]
```

Value iteration converges to V* for any initial value function, provided γ < 1 and rewards are bounded (Puterman (1994)).

## Formal Definition

An MDP is a tuple M = (S, A, P, R, γ) where:

- **S**: finite set of states
- **A**: finite set of actions (may vary per state)
- **P(s'|s,a)**: transition probability function; P(s'|s,a) ∈ [0,1], Σ_{s'} P(s'|s,a) = 1
- **R(s,a,s')**: immediate reward function
- **γ ∈ [0, 1)**: discount factor

A **policy** π: S → A maps each state to an action. The **value** of a state under policy π is:

```
V^π(s) = E_π[ Σ_{t=0}^∞ γ^t · R(sₜ, π(sₜ), sₜ₊₁) | s₀ = s ]
```

The **optimal value function** V*(s) = max_π V^π(s) satisfies the Bellman equation.

## Data Structures

### States and Actions

```rust
pub struct StateDesc {
    pub id: StateId,            // usize
    pub name: String,
    pub actions: Vec<ActionDesc>,
    pub terminal: bool,         // terminal states have no actions
}

pub struct ActionDesc {
    pub id: ActionId,           // usize (local to state)
    pub name: String,
    pub outcomes: Vec<Outcome>,
}

pub struct Outcome {
    pub probability: f64,       // P(s'|s,a)
    pub next_state: StateId,
    pub reward: f64,            // R(s,a,s')
}
```

### MDP

```rust
pub struct MDP {
    pub states: Vec<StateDesc>,
    pub discount: f64,          // γ ∈ [0, 1)
}
```

### Validation

The `validate()` method checks:
- All transition probabilities sum to 1.0 (within tolerance 10⁻⁶)
- All referenced states exist
- No negative probabilities

## Value Iteration

### The Algorithm

```
PROCEDURE value_iteration(mdp, ε, max_iterations) → ValueIterationResult:
    V ← [0.0; |S|]            // initial value function
    π ← [None; |S|]           // initial policy

    FOR iter in 0..max_iterations:
        V_new ← [0.0; |S|]
        max_δ ← 0.0

        FOR s in S:
            IF s is terminal or has no actions THEN
                V_new[s] ← 0.0
                CONTINUE

            best_value ← -∞
            best_action ← None

            FOR a in s.actions:
                // Compute Q(s, a) = Σ_{s'} P(s'|s,a) [R(s,a,s') + γ V(s')]
                Q ← Σ over outcomes o of action a:
                    o.probability × (o.reward + γ × V[o.next_state])

                IF Q > best_value THEN
                    best_value ← Q
                    best_action ← Some(a.id)

            V_new[s] ← best_value
            π[s] ← best_action
            max_δ ← max(max_δ, |V_new[s] - V[s]|)

        V ← V_new

        IF max_δ < ε THEN BREAK    // converged

    RETURN ValueIterationResult {
        values: V,
        policy: π,
        iterations: iter,
        residual: max_δ
    }
```

### Convergence Guarantee

**Theorem (Puterman (1994)).** For any MDP with γ < 1 and bounded rewards, value iteration converges: for any ε > 0, there exists K such that ||V_K - V*||∞ < ε.

The convergence rate is geometric: ||V_{k+1} - V*||∞ ≤ γ · ||V_k - V*||∞. For γ = 0.9, this means each iteration reduces the error by a factor of 10.

### Computational Complexity

Each iteration requires O(|S| · |A| · max_outcomes) time. With |S| states, |A| actions per state, and at most T outcomes per action, each iteration is O(|S| · |A| · T). The number of iterations to reach residual ε is O(log(1/ε) / log(1/γ)).

## Q-Values

The Q-value function Q(s, a) gives the expected return of taking action a in state s and then following the optimal policy:

```
Q(s, a) = Σ_{s'} P(s'|s,a) [R(s,a,s') + γ · V*(s')]
```

The `q_values()` function computes Q for all state-action pairs:

```rust
pub fn q_values(mdp: &MDP, values: &[f64]) -> HashMap<(StateId, ActionId), f64>
```

Q-values are useful for ranking actions: at any state, the actions can be ordered by their Q-values, revealing which are near-optimal and which are suboptimal.

## Policy Simulation

The `simulate_policy()` function executes a policy on the MDP:

```
PROCEDURE simulate_policy(mdp, policy, initial_state, max_steps, rng):
    state ← initial_state
    trajectory ← []
    total_return ← 0.0
    discount ← 1.0

    FOR _ in 0..max_steps:
        IF state is terminal THEN BREAK
        action ← policy[state]
        IF action is None THEN BREAK

        // Sample outcome according to transition probabilities
        u ← rng.uniform(0, 1)
        outcome ← sample from action.outcomes by cumulative probability

        trajectory.push((state, action, outcome.reward))
        total_return ← total_return + discount × outcome.reward
        discount ← discount × γ
        state ← outcome.next_state

    RETURN (trajectory, total_return)
```

This enables Monte Carlo evaluation of policies and comparison between the optimal policy and alternatives.

## proptest-Driven Adversarial Testing

The MDP framework integrates with proptest for adversarial testing:

1. **Build the MDP**: construct states from term equivalence classes, actions from applicable rewrite rules, and transitions from nondeterministic rewrite outcomes.

2. **Compute the adversarial policy**: instead of maximizing reward, minimize it (or maximize the probability of reaching a "bad" state like an invariant violation).

3. **Generate test sequences**: the adversarial policy guides proptest's term generation toward states where the optimal adversary predicts the highest failure probability.

4. **Shrink**: when a failure is found, proptest shrinks the generated sequence to the minimal reproducing case.

## Example: Simple Grid MDP

```rust
let mut mdp = MDP::new(0.9);  // discount factor γ = 0.9

let start  = mdp.add_state("start");
let middle = mdp.add_state("middle");
let goal   = mdp.add_terminal_state("goal");

mdp.add_action(start, "right", vec![
    Outcome::new(0.8, middle, -1.0),  // 80%: move to middle, cost 1
    Outcome::new(0.2, start,  -1.0),  // 20%: slip, stay in start
]);

mdp.add_action(middle, "right", vec![
    Outcome::new(0.9, goal,   10.0),  // 90%: reach goal, reward 10
    Outcome::new(0.1, middle, -1.0),  // 10%: slip, stay in middle
]);
mdp.add_action(middle, "left", vec![
    Outcome::new(0.9, start,  -1.0),  // 90%: go back to start
    Outcome::new(0.1, middle, -1.0),  // 10%: slip, stay in middle
]);

let result = value_iteration(&mdp, 1e-6, 1000);
// result.policy[start] = Some(0)   → "right"
// result.policy[middle] = Some(0)  → "right"
```

## References

- Bellman, R. (1957). Dynamic Programming. Princeton University Press.
- Puterman, M.L. (1994). Markov Decision Processes: Discrete Stochastic Dynamic Programming. Wiley.
- Howard, R.A. (1960). Dynamic Programming and Markov Processes. MIT Press.
