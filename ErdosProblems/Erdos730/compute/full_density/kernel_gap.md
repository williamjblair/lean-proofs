# Erdős #730 full-density proof: kernel gap closed

Audit date: 2026-07-13
Toolchain: Lean `v4.29.1`, Mathlib `v4.29.1`

## Result

The former analytic kernel gap is closed.  The repository proves the exact
positive-density claim for the explicit quadratic family and the upstream
Erdős #730 infinitude statement:

```text
Erdos730.FullDensityTheorem.candidatePositiveDensity :
  Erdos730.FullDensityReduction.CandidatePositiveDensityClaim

Erdos730.FullDensityTheorem.pairSet_infinite :
  Erdos730.FullDensityCore.PairSet.Infinite
```

`Erdos730FullDensityTheoremAudit.lean` reports only
`[propext, Classical.choice, Quot.sound]` for both declarations.

## Kummer input

Pinned Mathlib supplies the Kummer results used by the transition criterion:

- `Nat.Prime.multiplicity_choose` in
  `Mathlib/Data/Nat/Multiplicity.lean`;
- `padicValNat_choose` and
  `sub_one_mul_padicValNat_choose_eq_sub_sum_digits` in
  `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean`.

The local Kummer and consecutive-transition modules use these theorem
surfaces without adding axioms.

## Reciprocal-prime Mertens closure

`Erdos730Mertens.lean` proves the required reciprocal-prime estimate inside
the repository.  The proof builds a bounded first Mertens error from the
factorial/von-Mangoldt identity, bounds proper prime powers, and applies Abel
summation.  Its terminal surface is

```text
Erdos730.FullDensity.mertensReciprocalPrimeInput :
  Erdos730.FullDensity.MertensReciprocalPrimeInput
```

The coefficient in the formal bound is explicit and positive.  The density
argument requires its decay rate, so it does not depend on the paper's
particular coefficient `4`.

## Fixed-modulus PNT-AP closure

`Erdos730PNTAP.lean` imports
`PrimeNumberTheoremAnd.Consequences.chebyshev_asymptotic_pnt` and derives the
unweighted prime-counting limit by partial summation.  It proves

```text
Erdos730.FullDensity.requiredFixedModulusPNTAPInput :
  Erdos730.FullDensity.RequiredFixedModulusPNTAPInput
```

for the fixed moduli `1`, `222138`, and `148092`.  The package revision is
`d7f9e2bfdcc7e34dfb9328b7494a6d424ff50c96`.

The external package contains admitted declarations in an unrelated
Wiener/Fourier-decay experiment, named `prelim_decay_2` and
`prelim_decay_3`.  The proof imports no declaration from that experiment.
`Erdos730PNTAPAudit.lean` checks `chebyshev_asymptotic_pnt`, `WeakPNT_AP`,
and `requiredFixedModulusPNTAPInput`; each dependency cone contains no
`sorryAx` and uses at most `[propext, Classical.choice, Quot.sound]`.

## Closed event-count chain

The kernel proof covers each range used by the paper:

- higher prime powers tend to zero by complete/padded blocks and dominated
  convergence;
- first powers up to `sqrt X` satisfy the fixed-depth Fourier bounds and the
  uniform moving-depth tail estimate;
- the transition range tends to zero;
- divisor switching bounds the top-prime range by `(2/3) log 2`.

The exact rational budget then gives lower density greater than `107/2500`,
and strict increase of the family maps those parameters to distinct
consecutive pairs.

## Gate

The verification command

```text
bash scripts/check_axioms.sh
```

completed with

```text
PASS: 1260 headline theorem(s) clean, axioms subset of
      [propext, Classical.choice, Quot.sound]
```

The terminal cone contains no `sorry`, `admit`, `sorryAx`, new axiom, or
`native_decide` proof.
