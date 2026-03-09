# VPA -- Visibly Pushdown Automata

| Property | Value |
|----------|-------|
| **Feature gate** | `vpa` |
| **Source file** | `prattail/src/vpa.rs` (~2062 lines) |
| **Pipeline phase** | Grammar structure verification |
| **Lint codes** | V01 (`vpa-unreachable`), V02 (`vpa-nondeterministic`), V03 (`wta-unrecognized-term`), V04 (`wta-hot-path`) |

## 1. Rationale

PraTTaIL grammars contain matched delimiters (parentheses, braces, brackets) that
impose a nested structure on the token stream. Verifying that grammar transformations
and error recovery preserve this nesting requires a formalism more powerful than
regular languages but still decidable for equivalence and inclusion. Visibly
Pushdown Automata (VPA) are precisely this formalism: the stack discipline is
determined by the input alphabet partition, yielding closure under Boolean
operations and decidable equivalence.

## 2. Theoretical Foundations

### 2.1. Visibly Pushdown Languages

**Definition (VPA).** A Visibly Pushdown Automaton over a partitioned alphabet
`Sigma = Sigma_c cup Sigma_r cup Sigma_int` is a tuple
`M = (Q, Sigma, Gamma, delta, Q_0, Z_0, F)` where:

- `Q` is a finite set of states
- `Sigma_c` (call symbols) push onto the stack
- `Sigma_r` (return symbols) pop from the stack
- `Sigma_int` (internal symbols) leave the stack unchanged
- `Gamma` is the stack alphabet
- `delta = (delta_c, delta_r, delta_int)` is the transition function:
  - `delta_c: Q x Sigma_c -> P(Q x Gamma)` (call: push)
  - `delta_r: Q x Sigma_r x Gamma -> P(Q)` (return: pop)
  - `delta_int: Q x Sigma_int -> P(Q)` (internal: stack-neutral)
- `Q_0 subseteq Q` are initial states
- `Z_0 in Gamma` is the initial stack symbol
- `F subseteq Q` are accepting states

**Theorem (Closure Properties; Alur & Madhusudan 2004).** The class of Visibly
Pushdown Languages (VPL) is closed under:
- Union (product construction with accepting = either accepts)
- Intersection (product construction with accepting = both accept)
- Complement (determinize then swap accepting/non-accepting)
- Concatenation and Kleene star

**Theorem (Decidability).** For VPAs M1 and M2:
- Equivalence: `L(M1) = L(M2)` is decidable in polynomial time
- Inclusion: `L(M1) subseteq L(M2)` is decidable in polynomial time
- Emptiness: `L(M) = emptyset` is decidable in O(|Q|^2 * |Sigma|)

### 2.2. Determinization

**Theorem (Determinizability; Alur & Madhusudan 2004).** Every nondeterministic
VPA can be determinized. The construction uses a **subset construction** adapted
for the visibly pushdown setting:

- **Internal transitions**: standard powerset construction.
- **Call transitions**: the current macro-state ID is pushed onto a virtual stack.
- **Return transitions**: the virtual stack is popped to recover the caller
  macro-state, and the transition is resolved against the matching call.

The determinized VPA has at most `2^|Q|` states (exponential worst case), but
in practice the reachable subset is much smaller.

### 2.3. Myhill-Nerode Theorem for VPLs

**Theorem (Alur, Kumar, Madhusudan & Viswanathan 2005).** There exists a
Myhill-Nerode characterization for visibly pushdown languages, enabling
canonical minimization of deterministic VPAs.

## 3. Algorithm Pseudocode

### 3.1. Determinization (Subset Construction for VPAs)

```
function determinize(nfa: Vpa) -> Vpa:
    macro_state_map := {}   // BTreeSet<usize> -> macro_state_id
    worklist := Queue

    // Initial macro-state = set of NFA initial states
    initial_set := nfa.initial_states
    dfa := Vpa::new(nfa.alphabet)
    initial_id := dfa.add_state("M" + initial_set)
    dfa.initial_states.insert(initial_id)
    macro_state_map[initial_set] := initial_id
    if initial_set intersect nfa.accepting_states != emptyset:
        dfa.accepting_states.insert(initial_id)
    worklist.push((initial_set, initial_id))

    while (current_set, current_id) := worklist.pop():
        // Internal transitions
        for symbol in nfa.alphabet.internal_symbols:
            successor_set := {}
            for q in current_set:
                successor_set := successor_set union
                    nfa.internal_transitions[(q, symbol)]
            if successor_set not in macro_state_map:
                new_id := dfa.add_state(...)
                macro_state_map[successor_set] := new_id
                worklist.push((successor_set, new_id))
            dfa.add_internal_transition(current_id, symbol,
                macro_state_map[successor_set])

        // Call transitions
        for symbol in nfa.alphabet.call_symbols:
            successor_set := {}
            for q in current_set:
                for (target, push_sym) in nfa.call_transitions[(q, symbol)]:
                    successor_set.insert(target)
            push_symbol := "M" + current_id  // encode caller state
            if successor_set not in macro_state_map:
                new_id := dfa.add_state(...)
                macro_state_map[successor_set] := new_id
                worklist.push((successor_set, new_id))
            dfa.add_call_transition(current_id, symbol,
                macro_state_map[successor_set], push_symbol)

        // Return transitions
        for symbol in nfa.alphabet.return_symbols:
            for each caller_set, caller_id in macro_state_map:
                successor_set := {}
                for q in current_set:
                    for q_caller in caller_set:
                        // Find push symbols from caller call transitions
                        for (_, push_sym) in nfa.call_transitions[(q_caller, *)]:
                            for target in nfa.return_transitions[(q, symbol, push_sym)]:
                                successor_set.insert(target)
                if successor_set not empty:
                    stack_sym := "M" + caller_id
                    if successor_set not in macro_state_map:
                        new_id := dfa.add_state(...)
                        macro_state_map[successor_set] := new_id
                        worklist.push((successor_set, new_id))
                    dfa.add_return_transition(current_id, symbol, stack_sym,
                        macro_state_map[successor_set])

    return dfa
```

### 3.2. Reachability Analysis

```
function reachable_state_ids(vpa: Vpa) -> Set<usize>:
    visited := {}
    queue := Queue
    for q0 in vpa.initial_states:
        visited.insert(q0)
        queue.push(q0)
    while state := queue.pop():
        for each transition from state (internal, call, return):
            for target in transition.targets:
                if target not in visited:
                    visited.insert(target)
                    queue.push(target)
    return visited
```

### 3.3. Trim (Unreachable State Removal)

```
function trim(vpa: Vpa) -> Vpa:
    reachable := reachable_state_ids(vpa)
    old_to_new := compact_mapping(reachable)
    trimmed := new Vpa with remapped states and transitions
    return trimmed
```

## 4. Complexity Analysis

| Operation | Time | Space |
|-----------|------|-------|
| `construct_vpa` | O(c + i) | O(c + i) |
| `determinize` | O(2^n * |Sigma| * n) | O(2^n) |
| `reachable_state_ids` | O(n + m) | O(n) |
| `trim` | O(n + m) | O(n + m) |
| `is_deterministic` | O(m) | O(1) |
| Equivalence check | O(n1 * n2 * |Sigma|) | O(n1 * n2) |
| Inclusion check | O(n1 * n2 * |Sigma|) | O(n1 * n2) |

Where: n = number of states, m = number of transitions,
c = |call_return_pairs|, i = |internal_symbols|.

## 5. Unicode Diagrams

### 5.1. VPA Structure

```
    ┌─────────────────────────────────────────────┐
    │           VPA Alphabet Partition             │
    ├─────────────┬───────────────┬───────────────┤
    │  Sigma_c    │   Sigma_r     │  Sigma_int    │
    │  (call)     │   (return)    │  (internal)   │
    │             │               │               │
    │  (  {  [    │   )  }  ]     │  + - * id     │
    │             │               │  if else      │
    │  PUSH       │   POP         │  NOP          │
    └─────────────┴───────────────┴───────────────┘
```

### 5.2. VPA Execution on Nested Input

```
  Input:  (  a  (  b  )  c  )
  Stack:  Z0              (bottom of stack)
          ├── push "(" ──> Z0 . gamma_1
          │   internal "a" (stack unchanged)
          │   ├── push "(" ──> Z0 . gamma_1 . gamma_2
          │   │   internal "b" (stack unchanged)
          │   │   pop ")" ──> Z0 . gamma_1
          │   internal "c" (stack unchanged)
          │   pop ")" ──> Z0

  State trace:
    q0 ─(─> q1 ─a─> q1 ─(─> q2 ─b─> q2 ─)─> q1 ─c─> q1 ─)─> q3
    ^                                                          ^
    initial                                                accepting
```

### 5.3. Determinization Macro-State Expansion

```
    NFA states: {q0, q1, q2, q3}

    ┌───────────────┐     a      ┌───────────────┐
    │  {q0}         │ ─────────> │  {q1, q2}     │
    │  (initial)    │            │               │
    └───────────────┘            └──────┬────────┘
                                        │ b
                                        v
                                 ┌───────────────┐
                                 │  {q2, q3}     │
                                 │  (accepting)  │
                                 └───────────────┘
```

## 6. PraTTaIL Integration

### 6.1. Pipeline Bridge Functions

- `construct_vpa(call_return_pairs, internal_symbols)` -- Builds a VPA from
  grammar delimiter pairs.
- `Vpa::determinize()` -- Subset construction for determinization.
- `Vpa::trim()` -- Removes unreachable states.
- `Vpa::reachable_states()` / `reachable_state_ids()` -- BFS reachability.
- `Vpa::is_deterministic()` -- Checks the 4 determinism conditions.

### 6.2. Lint Emission

- **V01** (`vpa-unreachable`): States not reachable from initial. Severity: Warning.
- **V02** (`vpa-nondeterministic`): VPA fails determinism check. Severity: Note.
- **V03** (`wta-unrecognized-term`): Cross-referenced with tree automata. Severity: Warning.
- **V04** (`wta-hot-path`): Hot transitions in the VPA/WTA. Severity: Note.

### 6.3. Repair Integration

Trimming automatically removes unreachable states. For nondeterminism, the
`determinize()` method provides the repair. No explicit `RepairSuggestion`
objects are generated; the VPA module produces a transformed automaton directly.

## 7. Rust Implementation Notes

| Type | Role |
|------|------|
| `VpaAlphabet` | Partitioned alphabet: call, return, internal symbol sets |
| `SymbolKind` | Enum: Call, Return, Internal |
| `VpaState` | State with id and optional label |
| `Vpa` | Full VPA: states, alphabet, 3 transition maps, initial/accepting |

The transition maps use `HashMap` keyed by `(state_id, symbol)` for internal
and call transitions, and `(state_id, symbol, stack_top)` for return transitions.
Target lists allow nondeterminism (multiple targets per key).

## 8. Worked Example

**Grammar delimiters:** `(` / `)`, `{` / `}`.
**Internal symbols:** `+`, `id`.

Build a VPA recognizing well-nested expressions like `(id + {id})`:

```
Alphabet: Sigma_c = {"(", "{"}, Sigma_r = {")", "}"}, Sigma_int = {"+", "id"}

States: q0 (initial, accepting), q1 (inside parens)

Transitions:
  delta_c(q0, "(") = (q1, gamma_paren)
  delta_c(q0, "{") = (q1, gamma_brace)
  delta_int(q1, "id") = q1
  delta_int(q1, "+") = q1
  delta_c(q1, "(") = (q1, gamma_paren)
  delta_c(q1, "{") = (q1, gamma_brace)
  delta_r(q1, ")", gamma_paren) = q0
  delta_r(q1, "}", gamma_brace) = q0
  delta_r(q1, ")", gamma_paren) = q1  // nested
  delta_r(q1, "}", gamma_brace) = q1  // nested
```

Accepting trace for `(id + {id})`:
```
q0 ─(─> q1 [push gamma_paren]
q1 ─id─> q1
q1 ─+─> q1
q1 ─{─> q1 [push gamma_brace]
q1 ─id─> q1
q1 ─}─> q1 [pop gamma_brace]
q1 ─)─> q0 [pop gamma_paren]  -> accepting
```

## 9. References

1. Alur, R. & Madhusudan, P. (2004).
   "Visibly Pushdown Languages."
   *Proc. 36th ACM Symposium on Theory of Computing (STOC)*, pp. 202--211.

2. Alur, R. & Madhusudan, P. (2009).
   "Adding Nesting Structure to Words."
   *Journal of the ACM*, 56(3), Article 16.

3. Alur, R., Kumar, V., Madhusudan, P. & Viswanathan, M. (2005).
   "Congruences for Visibly Pushdown Languages."
   *Proc. 32nd International Colloquium on Automata, Languages, and
   Programming (ICALP)*, LNCS 3580, Springer, pp. 1102--1114.

4. Alur, R., Madhusudan, P. (2006).
   "Visibly Pushdown Languages."
   *Proc. 33rd ACM SIGPLAN-SIGACT Symposium on Principles of Programming
   Languages (POPL)* (extended abstract).

5. La Torre, S., Madhusudan, P. & Parlato, G. (2007).
   "A Robust Class of Context-Sensitive Languages."
   *Proc. 22nd Annual IEEE Symposium on Logic in Computer Science (LICS)*,
   pp. 161--170.
