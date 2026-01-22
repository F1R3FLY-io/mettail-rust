# Papers

## Already written

- Native Types

- Hypercube paper

## Yet to write

1. GSLTs for operational semantics.  Hennessey–Milner Thm.

  - structure-preserving functors between them ("syntactic category of GSLTs")

  - strong-bisimulation-preserving maps between them ("semantic cat of GSLTs").  "Map" here is a map of LTSs between the LTSs generated from the GSLTs where labels come from reduction contexts.

    - Main theorem: processes are bisimilar iff they satisfy the same formulae

    - What are the relevant formulae to make that true?

      - Topos: T, F, and, or, not, modal operators from hypercube

  - MeTTaIL's role
  
2. Weaken strong bisimilarity & address issues that arise

  - Pi to RHO

  - A thm: if two programs are strongly bisimilar in a theory with a natural number type then they're weakly bisimilar in theory without the natural number type using the Church encoding.

  - General thm: if the set of equations in a theory can be reduced to a set of rewrite rules by Knuth–Bendix, then given any two strongly bisimilar programs in the theory, they're weakly bisimilar in the theory without the equations using the KB rewrites

  - Reflective construction

    Assume Turing complete interactive (with binary op ⊙) GSLT Th whose equations can be replaced by rewrites using Knuth–Bendix.

    1. For each unary or above term constructor, create a nullary tag.  We also have finite limit and exponential constructors.

    2. For each tag, add rewrite rule tag ⊙ args ~> tag(...args)

    3. Replace equations by Knuth–Bendix-generated rewrites.

    4. Destructuring resource (maybe linear, maybe not) such that tag(...args) ⊙ destruct ~> (tag, ...args)

3. Compare Hypercube (with structural stuff but may have weaker logic) to paper 1 above (without structural stuff but with topos).

4. Stochastic stuff

  - define finite presentations of weighted GSLTs
  - thm: any finitely presentable theory using Warrell's approach can be presented using our approach

5. HDC

  - Write down shredding idea for substitution, analyze performance
  - hypothesis: running all the parsing, lookup, regenerating the table, reencoding etc. as vector ops on the GPU is faster than doing the same without vectors on the CPU.
