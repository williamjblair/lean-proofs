# Erdős 686 campaign intake audit

This audit follows the dependency-tree discipline in `compute730/audit.md`.
It is updated as candidates enter or leave the proof path.

## Baseline

- Focused terminal module compiles.
- `proofs.yaml` and the manifest-tracked `Audit.lean` section agree on 396
  theorem names.
- The axiom audit checks 807 printed theorem surfaces and permits only
  `[propext, Classical.choice, Quot.sound]`.
- `attestations.json` contains 396 non-null clean attestations, including
  370 for problem 686, 10 for problem 23, and 12 for problem 730.

## Dependency tree: odd-tail prime-power restriction

1. Exact block equation. **Banked premise.**
2. `d | 3*B_k(n)`. **Lean banked.**
3. Unique localization of `p^e` for prime `p>=k`, including `p=k`;
   for `p<k`, concentration of all but `v_p((k-1)!)` units of block
   valuation in one factor. **Lean banked.**
4. Local square/cubic Taylor lift. **Lean banked; exact coefficient tests
   pass.**
5. Explicit ratio-window constants `C_k`. **Lean banked.**
6. `p^(2e)<A_k*d`, center `p^(3e)<A_k*d`, with
   `A_k=14,17,23,26,29,35`. **Lean banked.**
7. Dominant component `(p^e)^2>=A_k*d` is impossible for `p>=k`.
   For a whole small-base prime-power gap, the raw local coefficient and
   concentration give
   `d < 14! * 35 * 13^30 < 10^120`. **Lean banked.**
8. Therefore every whole prime-power gap `d=p^e>=10^120` is impossible
   in all six odd rows, uniformly over `p`, including `p=2,3` and the
   boundary `p=k`. **Lean banked and independently hostile-audited.**

Verdict: genuinely new proper restriction.  It is not equivalent to
`OddThueTailHypothesis`: it removes the complete one-prime-support regime,
but gaps with at least two distinct prime divisors remain unrestricted by
this closure.

## Dependency tree: two-prime-support restriction

1. Per-prime concentration divisor with loss at most `4096`, with no loss
   for bases at least `k`. **Lean banked.**
2. Raw square and center-cubic bounds for concentrated divisors.
   **Lean banked.**
3. If both components use one factor, then
   `d < 4096^4 * 14! * 35 < 10^120`. **Lean banked.**
4. If one of two distinct concentration factors is the center, then the
   exact sixth-power combination is a 99-digit bound below `10^120`.
   **Lean banked.**
5. Hence every target-size two-prime gap has two distinct noncentral
   concentration indices, including when a base is `2` or `3`.
   **Lean banked and independently hostile-audited.**
6. In the clean `p,q>=k` slice, exact positive residual coefficients obey
   `ab<A_k^2` and
   `a*p^(2e)-b*q^(2f)=3(i-j)`. **Lean banked.**

Verdict: proper finite-coefficient reduction plus complete same-index and
center closures.  The remaining generalized Pell/prime-power families are
not asserted empty and are not equivalent to the full odd tail when small
prime support or three or more prime divisors are allowed.

## Dependency tree: primitive scale and discriminant routes

1. Reduced scale polynomial in `z=g^2`. **Exact identity reproduced.**
2. Constant and next-coefficient `z`-adic filters. **Necessary, exact.**
3. Infinite `k=5` family satisfying both filters, coprimality, parity,
   sign, and the real ratio window, but with `Q(z)>0`. **Exact counterfamily
   and positivity certificate banked.**
4. Genuine surviving floor pin
   `z=floor(5*A_3/A_5)`. **Exact proof and 341-row reproduction banked.**
5. Discriminant square cover. **Exact genus-6 reconstruction; not a
   reduction.**  The square condition recovers the original plane quintic;
   the quotient is genus 2 and the complementary Prym has no rational
   elliptic factor in the recorded exact good-reduction audit.

Verdict: the first two scale congruences are decisively refuted as an
unbounded closure mechanism.  The floor pin and divisor descent are proper
restrictions, but primitive `g=1` candidates and the infinite CF tail remain.

## Dependency tree: reflection compression

1. Reflection congruence `S | reflectionCoeff(k)*B_k(n)`. **Banked.**
2. Per-factor `gcd(S,n+i) | d+k+1-2i`. **Banked.**
3. Finite-product gcd compression. **Lean banked.**
4. `S | reflectionCoeff(k)*reflectionProduct(k,d)`. **Lean banked.**

Verdict: genuinely new but insufficient.  Exact smooth row-prefix points and
two stronger synthetic counterexamples satisfy the reflection conditions and
still fail row divisibility or the equation.

## Dependency tree: greatest-prime-factor wedge

1. `d+k-1<n` and lower-block smoothness. **Banked.**
2. `n>9d` for `k>=16`. **Lean banked from the exact ratio window.**
3. Every lower term is composite. **Lean banked from smoothness and size.**
4. Nair-Shorey `P(product)>221k/50`. **Published theorem, externally verified; not formalized.**
5. Contradiction for `k>=16` and `50(d+k-1)<=221k`. **Lean banked downstream of the explicit external-theorem interface.**

Verdict: rigorous paper-level unbounded wedge, but not accepted by the local
kernel gate until dependency 4 is formalized.

## Mandatory falsification verdicts

- `k=9,15`, `d=1` telescopes: preserved by every new odd-tail lemma.
- `(984,3177026,4480)`: exact window and rows 1..16 reproduced; row 17 fails;
  not an equation solution.
- `(244,48502,277)`: exact window and rows 1..15 reproduced; row 16 fails;
  not an equation solution.
- Fixed-prefix claims: remain refuted.
- Congruence-only route: not used.
- Gross log-mass counting: not used.

## Current exact gaps

The terminal proof still requires both original quantified hypotheses:

```lean
OddThueTailHypothesis
LargeKSmoothHypothesis
```

The results above have not been substituted for either target.  No theorem
equivalent to a target is being counted as progress.
