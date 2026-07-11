# Erdős 686 campaign intake audit

This audit follows the dependency-tree discipline in `compute730/audit.md`.
It is updated as candidates enter or leave the proof path.

## Baseline

- Focused terminal module compiles.
- `proofs.yaml` and the manifest-tracked `Audit.lean` section agree on 471
  theorem names.
- The combined full axiom audit reports 897 theorem surfaces, all within the
  allowlist `[propext, Classical.choice, Quot.sound]`.
- `attestations.json` was regenerated successfully for all 471 entries.

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

## Dependency tree: global residual square lift

1. Put `X_i=3(n+i)-d`; multiplying the block equation by `3^k` gives
   `prod(X_i+4d)=4 prod(X_i+d)`. **Exact identity and Lean banked.**
2. For an arbitrary integer polynomial `P`, the constant terms in
   `P(4d)-4P(d)+3P(0)` cancel, the linear term vanishes, and every higher
   coefficient contains `(4^r-4)d^r`, divisible by `3d^2`.
   **Lean banked monomialwise.**
3. Cancelling the nonzero factor three gives
   `d^2 | prod_i X_i`. **Lean banked in signed and positive-natural forms;
   independently hostile-audited.**
4. Exact scans reproduce every small equation solution, including all
   `d=1` telescopes through length fifteen, and the theorem correctly does
   not apply to the two named large-k prefix fixtures. **Exact checked.**

Verdict: a genuinely stronger global input with no localization or
small-prime exception.  It does not alone bound a mixed-prime gap; the active
next node is valuation concentration inside the residual progression.

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
7. The second local Taylor congruences make each prime-power component
   divide one of two explicit fixed obstruction integers. **Lean banked.**
8. For each of the six target rows, exhaustive kernel-reduced certificates
   show that the obstruction pair never vanishes simultaneously and that
   both absolute values are below `10^20`. **Lean banked, exact-reproduced,
   and independently hostile-audited.**
9. The Pell ratio bounds then give
   `d < 35 * 10^40 < 10^120`. **Lean banked.**
10. Global residual cleaning removes the base-size hypothesis with loss at
    most `64` for each base other than three and `59049` at three.  Same-owner
    clean components multiply as coprime squares; distinct owners enter the
    second/third obstruction split. **Lean banked, exact-reproduced, and
    independently hostile-audited.**
11. Hence every exact gap `d=p^e q^f` with distinct primes and positive
    exponents is below `10^120`, including bases `2` and `3`. **Lean banked.**

Verdict: the complete two-distinct-prime-support slice is closed, not merely
reduced to Pell families.  The remaining odd-tail gap has at least three
distinct prime divisors.

## Dependency tree: three cleaned residual buckets

1. Three pairwise-coprime cleaned buckets at distinct owners give two exact
   step-three square-difference equations. **Explicit hypotheses.**
2. Multiplying one second local lift by the two opposite coefficients
   eliminates both opposite squares and gives `P|O_i`. **Lean banked.**
3. The third local lift composes to
   `P^2|-3O_i+180E_i g^2(i-j)(i-l)d`. **Lean banked.**
4. All 1,035 unordered target triples have three pairwise-distinct exact zero
   slopes. **Exact-reproduced; not claimed kernel-enumerated.**
5. A 121-digit CRT pseudo-witness satisfies the square, second, third, global
   square, and both global moment congruences, while its block equation and
   `X_i<14d` window both fail. **Independent exact hostile reproduction.**

Verdict: proper local restriction and decisive falsification of a
congruence-only resultant route.  The single remaining exactly-three-bucket
node is the quantified short-CRT/window lemma; it is not proved here and does
not cover four-or-more buckets.

## Dependency tree: global cubic moment lifts

1. For a polynomial `P`, the identity `P(2d)=4P(d)` and `2^2=4` cancel
   every term through degree two after explicit constant and linear
   corrections. **Lean banked monomialwise.**
2. Hence `d^3` divides the corrected low-moment combination. **Lean banked.**
3. Applying the same calculation to the two residual progressions gives
   lower and reflected upper companion divisibilities for every exact gap.
   **Lean banked and independently hostile-audited.**
4. The exact solution `(k,n,d)=(1,0,3)` has raw residual products `-2` and
   `6`, neither divisible by `27`; only the corrected combinations vanish.
   **Exact counterexample reproduced.**

Verdict: a proper cubic global restriction intended for the
three-or-more-bucket regime.  No raw-product cube divisibility is claimed.

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

## Dependency tree: maximum-valuation matching compression

1. Consecutive-block concentration outside a maximum owner costs at most
   `v_p((k-1)!)`. **Lean banked.**
2. The exact equation makes the lower block divide the upper block, so the
   lower valuation chunk after that one allowance divides both a lower and an
   upper owner. **Lean banked.**
3. Their positive difference is one of
   `d-k+1,...,d+k-1`; coprime chunks for different primes multiply into the
   single lcm. **Lean banked.**
4. Hence `B(k,n) | (k-1)! C(k,d)`.  Concentrating a surviving row instead of
   using the upper equation owner gives the row-only two-factorial fallback.
   **Lean banked and independently hostile-audited.**
5. Exact Bernoulli/rational-window arithmetic gives `kd<5n` for `k>=16`,
   hence `(kd)^k < 5^k (k-1)! C(k,d)`. **Lean banked.**
6. The paper-only absorption `r! lcm(x,...,x+2r) | product(x,...,x+2r)` is
   exact-tested but not used as a Lean premise or counted as a manifest
   surface.  It still leaves degree `2k-1` host mass. **Proper but
   insufficient.**

Verdict: a genuine equation-level compression that survives both deep
fixtures and the `d=1` telescopes.  It does not prove `LargeKSmoothHypothesis`;
arithmetic correlations among the owner landings remain necessary.

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
