# Hostile audit: reflected harmonic obstruction

## Verdict

PASS for the exact uniform denominator theorem and its coefficient bridge;
not a closure of the whole two-large-prime Pell branch.  Lean proves that for
odd `k>=5` and
`1<=i<(k+1)/2`,

```text
4*(k+1-2*i) * sum_{s=i}^{k-i} 1/s
```

is not an integer.  The theorem uses no bounded scan over `k` (the length-two
base branch has one finite interval check) and has axiom footprint exactly
`[propext, Classical.choice, Quot.sound]`.

## Dependency tree

1. Sylvester--Schur supplies a prime larger than the interval length for a
   consecutive block beginning beyond that length.  The complete upstream
   Lean proof at commit `482dacc4d9335240f26218cdc62032da3100392b`
   is vendored in `Erdos686SylvesterSchur.lean`; its upstream SHA-256 is
   `ab0987fe6012fb421138af86ea6509979fcf885aa54744f06b2215fbb7f7e7b4`.
2. When the interval begins no later than its even length, Bertrand supplies
   a prime in the upper half of the combined endpoint range.  It lies in the
   interval, divides exactly one denominator, and does not divide four times
   the interval length.
3. A unique prime-divisible denominator gives a unique negative `p`-adic
   valuation among the reciprocal summands.  The ultrametric equality keeps
   that valuation after summation; multiplication by the prime-free factor
   does not change it.  An integer cannot have negative valuation.
4. The length-two branch is handled exactly.  The false boundary
   `(k,i)=(3,1)` has value `12`; `k>=5` forces its live length-two start to be
   at least two and the value is nonintegral.

## Bridge closure

`Erdos686ReflectedHarmonicBridge.lean` formalizes the missing generic
coefficient algebra.  It rewrites each local second linear coefficient as its
constant coefficient times an exact owner slope, proves that slope strictly
decreases and changes sign under reflection, and shows that simultaneous zero
obstructions force reflected owners and the forbidden integer harmonic value.
Consequently `second_obstruction_pair_not_both_zero` proves that at least one
fixed second obstruction is nonzero for all distinct owners in every odd row
`k>=5`.

## Mechanical checks

- direct compile of the vendored Sylvester--Schur source: PASS;
- direct compile of `Erdos686ReflectedHarmonic.lean`: PASS;
- direct compile of `Erdos686ReflectedHarmonicBridge.lean`: PASS;
- direct compile of the equation-facing Pell composition theorem: PASS;
- source scan: no `sorry`, `admit`, `native_decide`, declared `axiom`, or
  `opaque` declaration;
- all headline gates in the wrapper, bridge, and Pell composition print only
  `[propext, Classical.choice, Quot.sound]`.
- vendored source SHA-256 after import/provenance adaptation:
  `9c16d59ea2a1e4e41b1ba0329f6f43749973e14ef064bd2f003cf95ef2c71243`;
- reflected wrapper SHA-256:
  `c5a40ae98ea30623456d1fbe257ea701dd9c1734b879ee537d449ddc4936141e`;
- coefficient bridge SHA-256:
  `dbc8424086fdb4d91a78c7a976a7b39199cad952bcf54ef4307f2c75da948fae`;
- Pell source with the equation-facing composition theorem SHA-256:
  `bd2a26c2a5282b7be69e0eeabcab32d0b4a1862af8f5a71842175d7872129c8b`.
