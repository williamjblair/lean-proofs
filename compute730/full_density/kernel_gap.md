# Erdős #730 full-density proof: pinned-library kernel gap

Audit date: 2026-07-13
Toolchain: Lean `v4.29.1`, Mathlib `v4.29.1`

## Result

The pinned dependency graph contains the Kummer input needed by the proof,
but it does not contain either of the two analytic asymptotics used to sum the
prime bands.  Consequently the paper proof cannot currently be registered as
an unconditional kernel theorem without adding a substantial analytic
formalization.

This is a library-availability statement, not a mathematical objection to the
paper proof.  The exact missing surfaces are defined, without adding axioms,
in `ErdosProblems/Erdos730AnalyticInputs.lean`.

## Available Kummer input

Pinned Mathlib exposes Kummer in two useful forms:

- `Nat.Prime.multiplicity_choose` in `Mathlib/Data/Nat/Multiplicity.lean`;
- `padicValNat_choose` and
  `sub_one_mul_padicValNat_choose_eq_sub_sum_digits` in
  `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean`.

It also exposes `Nat.factorization_choose` in
`Mathlib/Data/Nat/Choose/Factorization.lean`.  The local #730 Kummer module
uses only theorem surfaces already in the pinned dependency.

## Missing reciprocal-prime Mertens asymptotic

`Mathlib/NumberTheory/SumPrimeReciprocals.lean` proves divergence of the sum
of reciprocal primes (`Nat.Primes.not_summable_one_div`) and convergence of
higher real powers.  It does not state the asymptotic

```text
sum_{p<=N} 1/p - log(log N) -> M.
```

The exact integer specialization of the paper's explicit bound is
`Erdos730.FullDensity.MertensReciprocalPrimeInput`.

## Missing fixed-modulus PNT in arithmetic progressions

`Mathlib/NumberTheory/LSeries/PrimesInAP.lean` proves Dirichlet infinitude,
not asymptotic equidistribution.  Its terminal public results include
`Nat.infinite_setOf_prime_and_eq_mod` and
`Nat.forall_exists_prime_gt_and_modEq`; there is no theorem asserting

```text
pi(N; A,a) / (N/log N) -> 1/phi(A).
```

The precise qualitative surfaces used here are
`Erdos730.FullDensity.PNTAPInputAtModulus` at the fixed moduli `1`, `222138`,
and `148092`, bundled by `RequiredFixedModulusPNTAPInput`.  The development
does not assume modulus-uniform PNT-AP.

## External dependency check

The public `AlexKontorovich/PrimeNumberTheoremAnd` project was also inspected
as a possible source compatible with this toolchain.  Its PNT-AP development
still reaches unfinished Wiener/PNT nodes through declarations containing
`sorry`; it therefore cannot pass this repository's kernel gate and was not
added as a dependency.

## Exact remaining Lean statement

All downstream set-theoretic work is closed by
`Erdos730.FullDensityReduction.pairSet_infinite_of_candidatePositiveDensity`.
The kernel-banked chain also includes the complete consecutive-transition
criterion, pointwise bad-event coverage, the summable higher-power majorant,
generic dominated convergence, and the sublinear terminal prime-power count.
The one remaining quantified lemma is

```text
Erdos730.FullDensityReduction.CandidatePositiveDensityClaim
```

whose expansion is the strict `107/2500` lower-density estimate for the
explicit family.  This proposition is stronger than the upstream infinitude
target and is exactly the theorem proved on paper; it is not introduced as an
axiom or listed in `proofs.yaml`.
