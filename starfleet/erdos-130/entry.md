---
id: F-017
title: Erdős Problem 130 has an infinite-chromatic general-position example
tier: lean
polarity: positive
depends_on: [F-016]
supersedes: []
verifier: export PATH="$HOME/.elan/bin:$PATH"; cd verified_math/F-017_erdos130-infinite-chromatic-solution && lake build && ! rg -n '\b(sorry|admit)\b|^\s*axiom\s' Research.lean Research
date: 2026-07-10
---

## Statement

There exists an infinite set `A ⊆ ℝ²` containing no three collinear points and
no four concyclic points such that, for every natural number `k`, the graph on
`A` joining exactly pairs at positive integer distance has no proper coloring
by `Fin k`.

The exact pinned formal statement is:

```lean
theorem Erdos130.erdos130_infinite_chromatic :
    ∃ A : Set Point,
      A.Infinite ∧ GeneralPosition A ∧ ∀ k : ℕ, ¬ HasKColoring A k
```

`Research/Basic.lean` proves this by invoking
`InfiniteAssembly.erdos130_infinite_chromatic_solution`.  This is the exact
statement audited in `check_answer/README.md`, with no weakened quantifier or
extra hypothesis.

## Proof / verification

F-016 supplies, for each `k`, a finite rational point block in strong determinant
general position whose positive-integer-distance graph has no `Fin k` coloring.
The only remaining issue is putting countably many such blocks in one plane
without introducing mixed incidence degeneracies.

`Research/InfiniteAssembly.lean` translates each new block by `(t,t³)`.  It
represents every mixed center collision, triple orientation, and quadruple
cyclic determinant as an explicit univariate real polynomial.  The crucial
nonidentity cases are proved exactly:

- one or two moving points in a triple expose a nonzero displacement component;
- one or three moving points in a quadruple have degree-six coefficient equal,
  up to sign, to the orientation of the fixed/moving triple;
- for two moving and two fixed points, the degree-six and degree-four
  coefficients are the two components of the complex product of their two
  nonzero displacement vectors, so they cannot both vanish.

A finite product of these nonzero polynomials is nonzero, hence has a rational
parameter at which every mixed condition is avoided.  A recursive `PrefixState`
chooses such a parameter for each block and stores a Lean proof of strong general
position for every finite prefix.  Compatibility of the prefix parameters is
proved, and every finite tuple from the countable union is embedded into a later
verified prefix.  Therefore the final indexed family is injective and has
nonzero orientation on every distinct triple and nonzero cyclic determinant on
every distinct quadruple.

Translation preserves all within-block squared distances.  Thus a hypothetical
`Fin k` coloring of the final range restricts to the `k`th block and contradicts
its finite witness property.  The index sigma type is infinite (it has one
nonempty block over every natural number), and injectivity makes the point range
infinite.  Finally the indexed determinant conditions imply the verifier's
`GeneralPosition` predicate, and the coloring contradiction is transported to
the subtype coloring used by `HasKColoring`.

The complete project rebuilds successfully.  `#print axioms` for both the pinned
theorem and the assembly theorem reports only `propext`, `Classical.choice`, and
`Quot.sound`.

Artifacts: `Research/Defs.lean`, `Research/Circles.lean`,
`Research/TangencyBooster.lean`, `Research/GenericBooster.lean`,
`Research/QuadGeneric.lean`, `Research/RationalInversion.lean`,
`Research/FiniteWitness.lean`, `Research/InfiniteAssembly.lean`,
`Research/Basic.lean`, `Research.lean`, and pinned Lean/Mathlib project files.
