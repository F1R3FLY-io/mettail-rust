# WPDS Forward Simulation

## Theorem (CEK.2)

For every concrete CEK transition `s → s'`, there exists a WPDS transition sequence such that `α(s) →*_WPDS α(s')`.

## Abstraction Function

```
α(phase, pos, bp, lhs, [F₁, …, Fₙ]) = ⟨p, γ₁ γ₂ … γₙ⟩
```

where `p` is the single WPDS control location and `γᵢ = bijection.frame_to_symbol(Fᵢ)`.

## Proof Sketch

Case analysis on the 10 transition rules:

### DRIVE

The DRIVE rule does not change the stack → α(s) = α(s'). The WPDS has a self-loop Replace rule for the current category entry.

### PREFIX-TERMINAL (with NT)

Pushes frame `F`: stack goes from K to `F :: K`.

```
α(s)  = ⟨p, γ(K)⟩
α(s') = ⟨p, γ(F) · γ(K)⟩
```

The WPDS has a Push rule from the category entry to the frame's symbol + continuation.

### PREFIX-TERMINAL (leaf)

No stack change → α(s) = α(s'). The WPDS has a Replace rule.

### PREFIX-TAIL (BP02)

No stack change (tail_wrap is a local variable) → α(s) = α(s'). The WPDS treats this as a Replace rule at the category entry.

### INFIX

Pushes `InfixRHS` frame → same as PREFIX-TERMINAL (with NT).

### POSTFIX

No stack change → Replace rule.

### UNWIND-INFIX

Pops `InfixRHS` frame → Pop rule in the WPDS.

### UNWIND-PREFIX

Pops `UnaryPrefix_L` frame → Pop rule.

### UNWIND-RD

Two sub-cases:
- If next segment has NT: Pop current frame, Push new frame → Pop + Push in WPDS
- If final segment: Pop frame → Pop rule

### UNWIND-EMPTY

Stack is empty → α(s') = ⟨p, ε⟩ (empty stack). Acceptance in WPDS.

## Corollary (CEK.3: Dead Rule Soundness)

If a WPDS stack symbol `γ` has zero weight in the poststar P-automaton, the corresponding frame variant is never pushed during any parse.

*Proof.* By contraposition: if the frame were ever pushed, the Forward Simulation theorem guarantees a WPDS transition giving `γ` non-zero weight. ∎

## Formal Proof

Machine-checked in `formal/rocq/trampoline/theories/WpdsSimulation.v`.
