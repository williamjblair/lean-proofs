# Hostile audit: uniform large-odd two-prime Pell package

## Exact target of this lane

The lane proves a proper restriction, not Erdős #686 itself:

Every exact solution in an odd row `k>=17` whose whole gap is the product of
two distinct prime powers with bases at least `k` admits the explicit
distinct-owner Pell and second-lift certificate recorded in `findings.md`.

No lower bound on `d`, smoothness premise, or unproved nonvanishing statement
is inserted.

## Dependency tree and verdicts

1. **Large-row ratio ceiling.**
   `18(n+1)<13kd`.
   - Source: `Erdos686LargePrimeGapComponent`.
   - Verdict: existing exact theorem.
2. **Integral base bound.**
   `n+1<kd`.
   - Verdict: follows from node 1 and `13kd<18kd`; no rounding.
3. **Coefficient choice.**
   `C=k`, `A=3k+2`, and `A<k^2`.
   - Verdict: exact polynomial inequality valid from `k=4`; the live odd
     threshold is `k=17` only because node 1 starts at `k>=16`.
4. **Distinct-owner bounded Pell package.**
   - Source: existing `two_large_prime_support_bounded_pell`, instantiated
     with nodes 2-3.
   - Verdict: returns all residual, ratio, coefficient, Pell, and center data;
     no private lemma is assumed.
5. **Lower-factor divisibility.**
   - Verdict: each residual square and the gap component divide
     `3(n+i)`; because `p,q>=17`, the factor 3 cancels exactly.
6. **Second-order local lifts.**
   - Source: existing `second_order_local_lift`, applied independently to
     `P` and `Q`.
   - Verdict: equation-facing and integral; no natural subtraction is hidden.
7. **Fixed second obstructions.**
   - Source: existing `second_obstruction_divisibilities` plus the exact Pell
     subtraction.
   - Verdict: yields the two displayed divisibilities with `ab<A^2`.
8. **Certificate assembly.**
   - Verdict: the new structure retains every premise and conclusion needed
     downstream, including the center bound `d<A^5`.

## Boundary audit

- `k=17`: included with `r=8`, `A=53`, `ab<2809`, and center bound
  `d<418195493`.
- `k=15`: not claimed by this wrapper because the imported large-row ratio
  theorem starts at 16.  Its fixed-row theorem already exists.
- exponent one: `e=f=1` is included.
- `p=k` and `q=k`: allowed whenever those values are prime; the hypotheses
  are non-strict.
- equal primes: excluded because the whole-gap decomposition requires two
  distinct primary components and the localization proof uses coprimality.
- same owner: already excluded inside the reused bounded-Pell theorem; the
  wrapper does not silently assume distinctness.
- center owner: retained and accompanied by the cubic divisor and explicit
  `A^5` bound.
- coefficient endpoint: `ab=A^2` is excluded by a strict inequality; the
  finite coefficient range is exactly `1<=ab<=A^2-1`.
- no target-size premise: the theorem applies at every positive whole gap of
  the stated form.

## Simultaneous-zero audit

The natural claim that one second obstruction is always nonzero is not used.
The determinant vanishes at reflected owner pairs.  A full-component
simultaneous zero would require the rational number

`4(k+1-2i) * sum_{s=i}^{k-i} 1/s`

to be integral.  Exact scanning finds no integral value through odd `k=1001`,
but this is not promoted to a theorem.  The package therefore returns both
divisibilities and stops; it does not claim a finite obstruction closure.

This boundary is materially different from a pure congruence route.  The
package already uses the exact equation, archimedean window, full local square
lifts, bounded Pell coefficients, and second-order Taylor identities.

## Falsification-record audit

- MalekZ local solutions are not contradicted: no modulus-only obstruction is
  asserted.
- The fixed-prefix witness `(984,3177026,4480)` is not an equation witness and
  no row-prefix implication appears.
- The `n=48502` census cluster is irrelevant unless it satisfies the full
  equation and the exact two-large-prime whole-gap premises.
- Odd-row `d=1` telescopes have no two-positive-prime whole-gap support and lie
  outside `d>=k`.
- No irrationality measure, Baker bound, smoothness-only claim, or Siegel
  finiteness theorem is used.

## Mechanical status

- exact verifier: pass;
- focused pytest: `6 passed`;
- ratio-boundary cases: 3,720;
- determinant pairs: 1,362,884;
- reflected denominator cases: 125,249;
- source scan: no `native_decide`, `sorry`, `admit`, or declared axiom;
- trailing-whitespace scan: clean;
- Lean direct-check: success;
- both `#print axioms` gates: exactly
  `[propext, Classical.choice, Quot.sound]`;
- shared imports, manifests, attestations, and existing theorem files:
  untouched.
