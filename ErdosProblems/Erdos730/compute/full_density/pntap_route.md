# Erdős 730 fixed-modulus PNT-AP closure audit

## Hostile verdict

`RequiredFixedModulusPNTAPInput` is now proved, not assumed.  The checked
route is

```text
PrimeNumberTheoremAnd.chebyshev_asymptotic_pnt
  -> AP Abel-summation identity
  -> AP integral bounded by the ordinary Chebyshev integral
  -> PNTAPInputAtModulus A for every A > 0
  -> RequiredFixedModulusPNTAPInput
```

The exact required conjunction at moduli `1`, `222138`, and `148092`
kernel-checks with only

```text
[propext, Classical.choice, Quot.sound]
```

There is no remaining PNT-AP lemma in the Erdős 730 dependency surface.

## Pinned primary source and compatibility

The repository pins Alex Kontorovich's
[`PrimeNumberTheoremAnd`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd)
at commit `d7f9e2bfdcc7e34dfb9328b7494a6d424ff50c96` (tag `v4.29.0`).
Its source was compiled unchanged against this repository's Lean and Mathlib
`v4.29.1`.  In particular, these declarations all printed only the standard
three axioms:

- `WeakPNT_AP_prelim`;
- `WienerIkeharaTheorem''` and `WienerIkeharaTheorem'`;
- `limiting_cor_W21` and `decay_bounds_key`;
- `WeakPNT_AP`;
- `chebyshev_asymptotic_pnt`.

The upstream theorem used locally is in
[`Consequences.lean`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/v4.29.0/PrimeNumberTheoremAnd/Consequences.lean):

```lean
theorem chebyshev_asymptotic_pnt
    {q : ℕ} {a : ℕ} (hq : q ≥ 1) (ha : a.Coprime q) (ha' : a < q) :
    (fun x ↦ ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊),
      if p % q = a then Real.log p else 0) ~[atTop]
      (fun x ↦ x / q.totient)
```

This is the weighted prime number theorem in a fixed reduced residue class.
No quantitative error term and no uniformity in a varying modulus are used.

## Exact local bridge

The bridge is in `ErdosProblems/Erdos730PNTAP.lean`.  For

```text
thetaAP(A,a,x) = sum_{p <= x, p prime, p = a (mod A)} log p,
piAP(A,a,x)    = #{p <= x : p prime, p = a (mod A)},
```

it proves the residue-class Abel-summation identity

```text
piAP(A,a,x)
  = thetaAP(A,a,x) / log x
    + integral_[2,x] thetaAP(A,a,t) / (t log(t)^2) dt.
```

The proof is a direct specialization of Mathlib's
`Chebyshev.primeCounting_eq_theta_div_log_add_integral`, with the sequence
replaced by the indicator of `Prime p ∧ p % A = a`.

Pointwise,

```text
0 <= thetaAP(A,a,t) <= Chebyshev.theta(t).
```

Consequently the AP integral is dominated by Mathlib's already proved
ordinary integral, and therefore

```lean
(fun x => ∫ t in 2..x, thetaAP A a t / (t * Real.log t ^ 2))
  =o[atTop] (fun x => x / Real.log x).
```

Dividing the Abel identity by `x / log x` leaves
`thetaAP(A,a,x) / x + o(1)`.  The upstream weighted PNT makes the first term
tend to `1 / phi(A)`.  Restricting from real `x` to natural `N` and proving
the exact `Icc`/`range (N+1)` identity yields

```lean
theorem pntAPInputAtModulus (A : ℕ) (hA : 0 < A) :
    PNTAPInputAtModulus A
```

and hence

```lean
theorem requiredFixedModulusPNTAPInput :
    RequiredFixedModulusPNTAPInput
```

## Axiom and dead-code audit

Run:

```sh
lake build ErdosProblems.Erdos730PNTAP ErdosProblems.Erdos730PNTAPAudit
```

The audit prints only `[propext, Classical.choice, Quot.sound]` for the
upstream weighted PNT, `WeakPNT_AP`, the local Abel identity, the generic
fixed-modulus theorem, and the exact required conjunction.

The upstream [`Wiener.lean`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/v4.29.0/PrimeNumberTheoremAnd/Wiener.lean)
does contain two admitted experimental declarations:

- `prelim_decay_2` at line 322;
- `prelim_decay_3` at line 341, and the derived unused `decay_alt`.

Repository-wide reference search in the pinned package finds no downstream
use of these declarations.  More decisively, `#print axioms` shows that
neither `WeakPNT_AP` nor any local target depends on `sorryAx`.  The active
route instead passes through the kernel-clean `W21` decay branch:

```text
WeakPNT_AP
  -> WienerIkeharaTheorem''
  -> WienerIkeharaTheorem'
  -> WienerIkeharaInterval_discrete'
  -> WienerIkeharaInterval
  -> wiener_ikehara_smooth_real
  -> wiener_ikehara_smooth
  -> limiting_cor_schwartz
  -> limiting_cor_W21
  -> decay_bounds_key.
```

Thus the kernel gate is clean.  A policy that additionally forbids admitted
declarations anywhere in a third-party package, even outside the dependency
cone, would require a trivial pinned fork deleting those three unused
declarations.  That is packaging hygiene, not a missing mathematical lemma.

## Why Brun-Titchmarsh is not the preferred route

The pinned upstream
[`BrunTitchmarsh.lean`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/v4.29.0/PrimeNumberTheoremAnd/BrunTitchmarsh.lean)
is kernel-clean, but its terminal theorem

```lean
BrunTitchmarsh.primesBetween_le
```

bounds all primes in an interval.  It is not a Brun-Titchmarsh theorem for a
residue class.  Applying it here would require a new Selberg-sieve
specialization to `A*m+a`, including the local factors at primes dividing
`A`.  That route is strictly longer than the now checked PNT-AP route.

## Audit of the alternate integer-identity family

For odd `n`, even `D`, `gcd(n,3D)=1`, put

```text
A = nD - 1,  B = nD + 1,  T = 3AB,
P = 6nTx + p,  Q = 12DTx + q,
R = 4nTx + r,  S = 12DTx + s,
```

where

```text
2p - 3r = n,  s - q = D,  nq = 3Dr + 1.
```

Then exact expansion gives

```text
2PQ - 1 = 3RS,
2DP - nQ = A,       3DR - nS = -B,
2DP - nS = -1,      nQ - 3DR = 1,
2P - 3R = n,        S - Q = D.
```

The four obstruction maps are

```text
Phi_P = (2D p^a c^2 - Ac) / n,
Phi_Q = (n p^a c^2 + Ac) / (2D),
Phi_R = (9D p^a c^2 + 3Bc - n) / (2n),
Phi_S = (n p^a c^2 - Bc - D) / (2D).
```

Clearing both `Q` and `S` at the top digit requires every unit `c mod 2D`
to have the least residue of `n*c^2 mod 2D` strictly greater than `D`.
Moreover the surviving fractions for `P` and `R` are equal.  Therefore a
factor-two Brun-Titchmarsh estimate could fit the existing one-third budget
only if the `P` fraction were at most `1/6`.

### The proposed `(n,D)=(35,12)` case is dead

Here `A=419`, `B=421`, `T=529197`, and one valid choice gives

```text
P=210Tx+541, Q=144Tx+359, R=140Tx+349, S=144Tx+371.
```

Although the `P` and `R` fractions are each `1/6`, every unit `c mod 24`
has `c^2=1 mod 24`, so the leading residue in both `Phi_Q` and `Phi_S` is
`35 mod 24 = 11 < 12`.  Both supposedly cleared branches are therefore top
obstructions.  Exact witnesses are:

- at `x=3`, `Q=228613463=13*17585651`; `Phi_Q=4334130463` has base-`17585651`
  digits `[8060317,246]`, both at most `(17585651-1)/2`;
- at `x=5`, `S=381022211` is prime; `Phi_S=555657373` has base-`381022211`
  digits `[174635162,1]`, both at most `(381022211-1)/2`.

### Quantified bounded search

Exact unit-square-coset enumeration for every even `D <= 10000` found
`Q/S`-clear moduli only for

```text
D = 2, 4, 6, 10, 12, 20, 28, 42, 60.
```

For every odd `n <= 100000` in the corresponding allowed cosets, with
`gcd(n,6D)=1` and both `nD-1` and `nD+1` prime, there were 2530 candidates.
None had combined `P+R` fraction at most `1/3`.  The unique best value was
the original `(n,D)=(7,6)`, with combined fraction `2/3`.

Reproduction hashes:

```text
da21cd67451c342e79bd7b18f102e9130c7f5ea1e3d61ea0586dbf7238642e8c  enumerate_qclear.py
56528bf563ba30baecdd54cf01c6864b0d028d435aad9c6983ae14d9654c7b25  search_twin_top.py
acc39dcffa3ef454219656478360e87d860f6e6c57b3928548489debb1a667de  enumerate_qclear.out
d6116550e90a3ded8b9365e0942be2166cac44a672fec9a93e6bb2c84cfaba25  search_twin_top.out
```

This is a bounded impossibility statement, not an unbounded classification.
It is sufficient to reject the proposed family as a practical replacement
for PNT-AP; it is not used by the completed kernel proof.
