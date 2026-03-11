# Variety Classification — Eilenberg's Theorem and Module Dispatch

## Motivation

**Core question**: Given a predicate formula φ, which automaton variety V best
captures φ's computational requirements?

Eilenberg's variety theorem (1976) establishes a bijection between pseudovarieties
of finite monoids and varieties of recognizable languages. This deep algebraic
result provides the theoretical foundation for PraTTaIL's dispatch mechanism:
each advanced automata module M_i corresponds to a specific pseudovariety, and
feature extraction determines which pseudovarieties are relevant to a given
predicate.

The Chomsky hierarchy classifies languages by generative power (regular, CF, CS,
RE). Eilenberg's theorem refines the regular level into algebraically natural
subclasses — and each subclass has an efficient specialized module in PraTTaIL.

## Definitions

**Definition 1.1** (Finite Monoid). A **finite monoid** (M, ·, 1) is a finite set
M equipped with an associative binary operation · : M × M → M and an identity
element 1 ∈ M such that 1 · m = m · 1 = m for all m ∈ M.

*Intuition*: Monoids abstract "sequential composition." Concatenating strings,
composing automata transitions, and chaining state updates are all monoid
operations. The identity element represents "do nothing."

**Definition 1.2** (Syntactic Monoid). For a regular language L ⊆ Σ*, the
**syntactic monoid** M(L) is the quotient Σ*/≡_L where the syntactic congruence
≡_L is defined by:

  u ≡_L v  ⟺  ∀x,y ∈ Σ* : xuy ∈ L ⟺ xvy ∈ L

*Intuition*: Two strings are syntactically equivalent if no context can distinguish
them with respect to membership in L. The syntactic monoid is the coarsest
(smallest) monoid that recognizes L — it captures exactly the algebraic structure
needed to decide membership.

*Example*: For L = {w ∈ {a,b}* : |w|_a is even}, the syntactic monoid is
M(L) ≅ ℤ/2ℤ = ({0, 1}, +, 0). Two elements: even-a-count (accepting) and
odd-a-count (rejecting). The monoid has exactly 2 elements because only the
parity of the a-count matters.

**Definition 1.3** (Division). A monoid N **divides** M (written N ≺ M) if N is
a quotient of a submonoid of M. That is, there exists a submonoid S ⊆ M and a
surjective morphism h : S → N.

*Intuition*: Division is the algebraic analogue of "can be simulated by." If
N ≺ M, then any language recognized by N can also be recognized by M.

**Definition 1.4** (Pseudovariety of Monoids). A **pseudovariety** 𝐕 is a class
of finite monoids closed under:
1. Division: if M ∈ 𝐕 and N ≺ M, then N ∈ 𝐕
2. Finite direct products: if M₁, M₂ ∈ 𝐕, then M₁ × M₂ ∈ 𝐕

*Intuition*: A pseudovariety is a "natural algebraic class" — closed under the
operations that preserve computational character.

**Definition 1.5** (Variety of Languages). A **variety of languages** 𝒱 assigns
to each finite alphabet Σ a set 𝒱(Σ*) ⊆ Reg(Σ*) of regular languages, closed
under:
1. Boolean operations: union, intersection, complement
2. Inverse morphisms: for any morphism h : Σ* → Γ* and L ∈ 𝒱(Γ*),
   h⁻¹(L) ∈ 𝒱(Σ*)
3. Left and right quotients: u⁻¹L = {w : uw ∈ L} and Lu⁻¹ = {w : wu ∈ L}

*Intuition*: A variety is a "natural class" of regular languages that is
algebraically well-behaved under all natural operations on languages.

## Eilenberg's Variety Theorem

**Theorem 1.1** (Eilenberg, 1976). There is a bijection between pseudovarieties
of finite monoids and varieties of recognizable languages:

  𝐕 ↦ 𝒱_𝐕   where   𝒱_𝐕(Σ*) = { L ⊆ Σ* : M(L) ∈ 𝐕 }
  𝒱 ↦ 𝐕_𝒱   where   𝐕_𝒱 = { M(L) : L ∈ 𝒱(Σ*) for some Σ }

*Proof sketch*: The forward direction (𝐕 ↦ 𝒱_𝐕 is a variety) follows from the
minimality of syntactic monoids: M(L) divides any monoid recognizing L, so the
class 𝒱_𝐕 is closed under inverse morphisms. Boolean closure follows from
the closure of pseudovarieties under direct products and division. The backward
direction (𝒱 ↦ 𝐕_𝒱 is a pseudovariety) uses the fact that quotients and
submonoids of syntactic monoids correspond to quotient and sub-languages of
the original variety.

*Reference*: Eilenberg, S. (1976). *Automata, Languages, and Machines*, Vol. B.
Academic Press. Chapter V, Theorems 3.4 and 3.6.

## Variety–Module Correspondence

The key insight: each PraTTaIL module M_i corresponds to a pseudovariety 𝐕_i.
The dispatch automaton determines which 𝐕_i's contain the syntactic monoid of
the predicate's language.

```
┌────────────────────┬──────────────────┬───────────────────────────────────────┐
│  Pseudovariety 𝐕   │  Module          │  Characterization                     │
├────────────────────┼──────────────────┼───────────────────────────────────────┤
│  𝐀 (aperiodic)     │  M1 Symbolic     │  Star-free = FO[<] definable          │
│  𝐆 (groups)        │  M2 Büchi        │  ω-regular, group languages           │
│  𝐉₁ (J-trivial)    │  M3 AWA          │  Piecewise testable                   │
│  𝐃𝐀 (DA-monoids)   │  M4 VPA          │  Unambiguous languages (VPL)          │
│  𝐁𝐕 (block groups) │  M5 Parity Tree  │  Tree-recognizable (μ-calculus)       │
│  — (non-regular)    │  M6 Register     │  Data languages (orbit-finite)        │
│  — (probabilistic)  │  M7 Probabilistic│  Stochastic recognizable              │
│  𝐀×𝐀 (products)    │  M8 Multi-Tape   │  k-tape regular relations             │
│  𝐂𝐨𝐦 (commutative) │  M9 Multiset     │  Commutative languages                │
│  𝐁𝐚𝐥𝐥 (all monoids)│  M10 Weighted MSO│  Full MSO definable                   │
│  𝐋𝐃𝐀 (local DA)    │  M11 Two-Way     │  2-way = MSO-definable transductions  │
└────────────────────┴──────────────────┴───────────────────────────────────────┘
```

**M1 / 𝐀 (Aperiodic)**. The Schützenberger–McNaughton–Papert theorem establishes
that a language is star-free iff its syntactic monoid is aperiodic (group-free)
iff it is first-order definable with order. M1's symbolic automata operate over
Boolean algebras, which naturally express star-free properties. Reference:
Schützenberger (1965), McNaughton & Papert (1971).

**M2 / 𝐆 (Groups)**. Büchi's theorem (1960) characterizes ω-regular languages as
exactly the MSO-definable sets of infinite words. The group component captures
the liveness properties (infinitely-often conditions). M2 implements Büchi
acceptance for stream-based predicates.

**M3 / 𝐉₁ (J-trivial)**. Simon's theorem (1975) characterizes piecewise testable
languages as those with J-trivial syntactic monoids. M3's alternating automata
handle universal branching — the "for all paths" quantifier that characterizes
the piecewise testable fragment.

**M4 / 𝐃𝐀**. The DA pseudovariety characterizes unambiguous languages (Schützenberger,
1976). Visibly pushdown languages form a Boolean algebra closed under complement
and intersection, generalizing DA to nested word structures.

**M5 / 𝐁𝐕 (Block groups)**. Tree automata with parity acceptance recognize
exactly the μ-calculus definable properties of infinite trees. The algebraic
counterpart is the pseudovariety of block groups. Reference: Walukiewicz (2002).

**M6 / Data languages**. Register automata extend beyond regular languages to
handle data values with equality tests. The algebraic framework uses orbit-finite
nominal sets (Bojańczyk et al., 2014) rather than classical monoids.

**M7 / Probabilistic**. Stochastic automata assign probabilities to transitions.
No classical monoid pseudovariety applies; the algebraic structure is a
probabilistic semiring. Reference: Rabin (1963), Paz (1971).

**M8 / 𝐀×𝐀 (Products)**. Multi-tape automata recognize regular relations over
k-tuples of words. The algebraic structure is a direct product of monoids, one
per tape. Reference: Elgot & Mezei (1965).

**M9 / 𝐂𝐨𝐦 (Commutative)**. Commutative languages are recognized by monoids
where xy = yx for all elements. Multiset automata naturally operate in this
variety. Reference: Eilenberg (1976), Vol. B, Chapter VII.

**M10 / 𝐁𝐚𝐥𝐥 (All finite monoids)**. By Büchi's and Elgot's theorems, MSO
captures exactly the regular languages — the variety of all finite monoids.
M10 provides the full MSO specification language.

**M11 / 𝐋𝐃𝐀 (Local DA)**. Engelfriet & Hoogeboom (2001) proved that two-way
transducers define exactly the MSO-definable string transductions. The algebraic
characterization involves local DA monoids. Reference: Filiot & Reynier (2016).

## Practical Classification

Computing syntactic monoids at runtime is infeasible (exponential in the worst
case for general regular languages). Instead, PraTTaIL uses **morphological
feature extraction**: syntactic features of the formula AST correlate with
variety membership.

This is a conservative approximation — feature extraction may activate extra
modules but never misses a needed one:

**Lemma 1.1** (Soundness of Feature Extraction). For any predicate formula φ
and channel context Γ:

  { M_i : M(⟦φ⟧) ∈ 𝐕_i }  ⊆  { M_i : bit i set in extract_features(φ, Γ).signature }

That is, the signature computed by feature extraction is a superset of the
modules whose pseudovarieties contain the syntactic monoid of φ's denotation.

*Proof*: By structural induction on the AST. Each match arm in `extract_features()`
conservatively sets bits for every variety that *could* be relevant to the
syntactic construct. For instance, `ForallInfinite` sets both M2 (ω-regular)
and M3 (alternating) because universal quantification over infinite domains
requires both Büchi acceptance and alternation. No match arm *clears* bits, so
the signature can only grow — ensuring the superset property. See
`morphological-decomposition.md` for the full inductive proof.

## References

- Eilenberg, S. (1976). *Automata, Languages, and Machines*, Vol. B. Academic Press.
- Pin, J.-É. (1986). *Varieties of Formal Languages*. Plenum.
- Straubing, H. (1994). *Finite Automata, Formal Logic, and Circuit Complexity*. Birkhäuser.
- D'Antoni, L. & Veanes, M. (2017). The power of symbolic automata and transducers. *CAV 2017*.
- Droste, M. & Gastin, P. (2007). Weighted automata and weighted logics. *TCS* 380(1–2).
- Schützenberger, M. P. (1965). On finite monoids having only trivial subgroups. *Information and Control* 8(2).
- McNaughton, R. & Papert, S. (1971). *Counter-Free Automata*. MIT Press.
- Simon, I. (1975). Piecewise testable events. *ICALP 1975*, LNCS 33.
- Bojańczyk, M., Klin, B. & Lasota, S. (2014). Automata theory in nominal sets. *LMCS* 10(3).
- Walukiewicz, I. (2002). Monadic second-order logic on tree-like structures. *TCS* 275(1–2).
- Engelfriet, J. & Hoogeboom, H. J. (2001). MSO definable string transductions and two-way finite-state transducers. *ACM TOCL* 2(2).
- Filiot, E. & Reynier, P.-A. (2016). Transducers, logic and algebra for functions of finite words. *SIGLOG News* 3(3).
