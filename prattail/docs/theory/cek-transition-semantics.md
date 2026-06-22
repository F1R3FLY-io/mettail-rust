# CEK Transition Semantics

## State Space

### Definition 1 (Token Stream)

A **token stream** is a finite sequence `T = [t₁, t₂, …, tₙ]` where each `tᵢ ∈ Σ` is a terminal token. Access is by position: `T[pos]` returns the token at position `pos`, or `Eof` if `pos ≥ n`.

### Definition 2 (Binding Power)

A **binding power** is a natural number `bp ∈ ℕ`. Each infix operator has a pair `(l_bp, r_bp)` where `l_bp` is the left binding power and `r_bp = l_bp + 1` (left-associative) or `r_bp = l_bp` (right-associative).

### Definition 3 (Frame)

A **frame** is a tagged record from the set:

```
Frame = InfixRHS(lhs: Cat, op_pos: ℕ, saved_bp: ℕ)
      | GroupClose(saved_bp: ℕ)
      | UnaryPrefix_L(saved_bp: ℕ)              for each label L
      | RD_L_i(saved_bp: ℕ, captures: Map)      for each label L, segment i
      | CollectionElem_L(elems: [Cat], bp: ℕ)    for each label L
      | Mixfix_L_i(lhs: Cat, bp: ℕ, caps: Map)  for each label L, step i
```

### Definition 4 (Configuration)

A **configuration** is a tuple `(phase, pos, bp, lhs, stack)` where:

- `phase ∈ Phase` (see below)
- `pos ∈ ℕ` — current position in the token stream
- `bp ∈ ℕ` — current binding power
- `lhs ∈ Cat ∪ {⊥}` — current left-hand side value (⊥ if no value yet)
- `stack ∈ Frame*` — continuation stack (may be empty)

### Definition 5 (Phase)

```
Phase = Drive           — entering prefix dispatch
      | PrefixDone      — prefix value produced, entering infix loop
      | InfixCheck      — checking for infix/postfix operators
      | Unwind          — popping and applying continuation
      | Accept          — parse complete
      | Error(msg)      — parse failed
```

## Transition Rules

### Rule 1: DRIVE

```
(Drive, pos, bp, ⊥, K) ─────→ dispatch on T[pos]
```

Token dispatch selects exactly one of rules 2–4.

### Rule 2: PREFIX-TERMINAL (with nonterminal)

```
(Drive, pos, bp, ⊥, K)
───────────────────────────────── T[pos] matches rule R with same-cat NT at segment i
(Drive, pos', bp', ⊥, RD_R_i{bp, captures} :: K)
```

where `pos'` is the position after consuming inline items, `bp'` is the NT's binding power, and `captures` are the accumulated values from segments 0..i.

### Rule 3: PREFIX-TERMINAL (leaf)

```
(Drive, pos, bp, ⊥, K)
──────────────────────── T[pos] matches rule R with no same-cat NT
(PrefixDone, pos', bp, v, K)
```

where `v = construct(R, captures)` is the fully-constructed AST node.

### Rule 4: PREFIX-TAIL (BP02)

```
(Drive, pos, bp, ⊥, K)
──────────────────────── T[pos] matches tail-call-eligible rule R
(Drive, pos', R.bp, ⊥, K)     with tail_wrap = (R.tag, bp)
```

No frame is pushed. The `tail_wrap` records the constructor to apply later.

### Rule 5: INFIX

```
(PrefixDone, pos, bp, lhs, K)
──────────────────────────────── T[pos] is infix op with l_bp ≥ bp
(Drive, pos+1, r_bp, ⊥, InfixRHS{lhs, pos, bp} :: K)
```

### Rule 6: POSTFIX

```
(PrefixDone, pos, bp, lhs, K)
──────────────────────────────── T[pos] is postfix op with l_bp ≥ bp
(PrefixDone, pos+1, bp, f(lhs), K)
```

where `f` is the postfix constructor.

### Rule 7: UNWIND-INFIX

```
(Unwind, pos, _, rhs, InfixRHS{lhs, op_pos, saved_bp} :: K)
──────────────────────────────────────────────────────────────
(PrefixDone, pos, saved_bp, make_infix(T[op_pos], lhs, rhs), K)
```

### Rule 8: UNWIND-PREFIX

```
(Unwind, pos, _, v, UnaryPrefix_L{saved_bp} :: K)
──────────────────────────────────────────────────
(PrefixDone, pos, saved_bp, Cat::L(Box::new(v)), K)
```

### Rule 9: UNWIND-RD

```
(Unwind, pos, _, nt_val, RD_L_i{saved_bp, caps} :: K)
──────────────────────────────────────────────────────
```

Two sub-cases:
- If segment i+1 has a nonterminal: `(Drive, pos', bp', ⊥, RD_L_{i+1}{saved_bp, caps'} :: K)`
- If segment i+1 is final: `(PrefixDone, pos', saved_bp, construct(L, caps'), K)`

### Rule 10: UNWIND-EMPTY

```
(Unwind, pos, _, v, [])
───────────────────────
(Accept, pos, _, v, [])
```

## Properties

### Theorem (Determinism)

For any non-terminal configuration, at most one transition rule applies.

### Theorem (Termination)

The transition system terminates for all finite token streams. Measure: `2 × |T| − 2 × pos + |K|`.

### Theorem (Soundness)

If `(Accept, pos, _, v, [])` is reachable from `(Drive, 0, min_bp, ⊥, [])`, then `v` is a valid parse tree for `T[0..pos]` in the grammar.
