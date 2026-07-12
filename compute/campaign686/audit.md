# Erdős 686 campaign intake audit

This audit follows the dependency-tree discipline in `compute730/audit.md`.
It is updated as candidates enter or leave the proof path.

## Baseline

- Focused terminal module compiles.
- `proofs.yaml` and the manifest-tracked `Audit.lean` section must agree
  exactly; the live count is reported by `scripts/check_manifest.sh`.
- The combined full axiom audit must stay within the allowlist
  `[propext, Classical.choice, Quot.sound]`.
- `attestations.json` must be regenerated after the final full build; its live
  count is checked against `proofs.yaml` rather than frozen in this document.

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

## Dependency tree: complete aggregate two-owner branch

1. Multiply all per-prime cleaning losses in a target row.  Exact Legendre
   arithmetic gives
   `G_k=108,1620,136080,1224720,242494560,18914575680`.
   **Lean table banked and independently reproduced.**
2. Supply a decomposition `d=gPQ`, with `P,Q` coprime cleaned square
   components at at most two residual owners and `g<=G_k`.
   **Explicit `HasAtMostTwoGlobalResidualOwners` hypothesis.**
3. Coincident owners multiply as coprime squares and force
   `d<A_k g^2`. **Lean banked.**
4. Distinct owners satisfy a cleaned Pell identity.  A nonzero second
   obstruction gives `d<A_k*(10^16)^2*g^6`. **Lean banked and exact-audited.**
5. If both second obstructions vanish, the third lifts and
   `gcd(P,b),gcd(Q,a) | 3|i-j|` cancel the opposite coefficients, yielding
   a cubic bound below `10^120`. **Lean banked and exact-audited.**
6. Therefore an exact target-row solution equipped with
   `HasAtMostTwoGlobalResidualOwners` has `d<10^120`. **Lean banked and
   independently hostile-audited.**
7. Global concentration chooses one certified owner for every prime divisor.
   If its nonzero cleaned owner range is covered by two indices, exact finite
   factorization reconstructs `d=gPQ`, proves the two buckets coprime, proves
   their factor and square divisibilities, and packs the complementary loss
   below `G_k`. **Lean banked, exact-reproduced, and independently
   hostile-audited.**
8. Hence every target-size solution has one certified assignment with no
   two-index cover. **Lean banked.**

Verdict: the former finite grouping gap is closed.  The remaining odd-tail
branch is a certified assignment with more than two distinct owner values
among its nonzero cleaned components.  The theorem is scoped to the one
assignment selected by concentration; it does not quantify over all possible
assignments.

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

### Quarantined zero-obstruction LCM follow-up

A generic Lean theorem proves that a vanished composed obstruction packs all
three pairwise-coprime components into one coefficient multiple and yields
`d|L*g^4`; independent exact arithmetic checks all 1,427 positive-zero
occurrences and puts their bounds below `10^120`.  Hostile audit did not admit
this candidate to the manifest because no exported Lean wrapper discharges
the six row-specific coefficient hypotheses.  It also rejected the claimed
novelty of the associated `abc` thresholds: the banked `2d<n` inequality
already implies `abc>125*g^2*d`, stronger by at least `2.7*10^84` at the
target cutoff.  The generic node and falsification record are retained, but
the short-CRT/window core is unchanged.

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
5. Lower and upper maximum-valuation owners carry the reflection-center
   residual power after the parity coefficient and one factorial loss.
   **Lean banked and independently hostile-audited.**
6. Subtracting the reflected and centered owner differences puts that power
   into `|i+j-(k+1)|`; a non-reflected pair lands in
   `lcm(1,...,k-1)`. **Lean banked.**
7. The lower landing also aggregates to
   `S | reflectionCoeff(k)*(k-1)!*reflectionDiffLcm(k,d)`.
   **Lean banked.**

Verdict: genuinely new but insufficient.  Exact smooth row-prefix points and
two stronger synthetic counterexamples satisfy the reflection conditions and
still fail row divisibility or the equation.  The exact surviving owner
alternative is `j=k+1-i`; the factorial-lcm and product right sides are not
uniformly ordered.

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

## Dependency tree: joint all-owner resultant audit

1. Reconstruct all 60 target-row coefficient triples and every full-grid
   second/third obstruction. **Exact reproduced against the Lean tables.**
2. Enumerate all 42,274 owner subsets and all 2,576 four-owner circuits.
   Every primitive circuit is sign-mixed; four zero-coordinate circuits in
   row seven remain mixed. **Exact reproduced.**
3. The annihilator of the columns `X_i*i^r`, `0<=r<=s-2`, has dimension one,
   and its common-term moment is exactly
   `(-3)^(s-1)/product_i X_i != 0`. **Exact rational linear algebra.**
4. On the full grid the determinant identities are
   `L(D)=3V e_(k-2)` and `L(E)=9V e_(k-3)`. **Exact reproduced in all six
   target rows.**
5. Substitution into the exact block equation leaves a remainder beginning
   at `d^4=(gM)^4`; the induced `M^4` divisibility is automatic term by term.
   **Exact structural obstruction.**

Verdict: PASS as a negative route audit; FAIL as a Target 1 closure.  No new
Lean surface is attested because no stronger equation-facing theorem results.

## Dependency tree: greatest-prime-factor wedge

1. `d+k-1<n` and lower-block smoothness. **Banked.**
2. `n>9d` for `k>=16`. **Lean banked from the exact ratio window.**
3. Every lower term is composite. **Lean banked from smoothness and size.**
4. Nair-Shorey `P(product)>221k/50`. **Published theorem, externally verified; not formalized.**
5. Contradiction for `k>=16` and `50(d+k-1)<=221k`. **Lean banked downstream of the explicit external-theorem interface.**

Verdict: rigorous paper-level unbounded wedge, but not accepted by the local
kernel gate until dependency 4 is formalized.

## Dependency tree: `10^1000` odd-tail band

1. Exact rational root brackets and primitive-scale denominator lower bounds
   for all six rows. **Lean banked.**
2. Farey-neighbor certificates covering every admissible denominator below
   `10^1000`. **Generated by exact arithmetic and checked by ordinary kernel
   reduction.**
3. Reverse Newton/gcd bounds and exact centered-equation refutation at every
   leaf. **Lean banked and independently reproduced.**
4. Composition with the former cutoff at `10^120`. **Lean banked.**

Verdict: PASS for `10^120 <= d < 10^1000`; the infinite tails beginning at
`10^1000` remain open.

## Dependency tree: universal even tails and closed rows

1. For `S_r(W)=product_j(W^2-(2j-1)^2)`, a descending rational recurrence
   constructs the monic polynomial part `Q_r` of its square root. **Lean
   banked for every `r>=2`.**
2. Positive denominator clearing constructs integral `T,D,C`; the simple
   root of `S_r` at one proves `D!=0`. **Lean banked.**
3. Exact coefficient norms produce the explicit threshold
   `max(2r,2A+1,7F+1,10E+1)`. **Lean banked, no asymptotic phrase.**
4. The integral Runge trap excludes every solution above that threshold.
   **Lean banked.**
5. Separate finite square-root traps and prime-field covers close all gaps in
   rows `k=16,18,20,24,28,32`. The k=18, k=28, and k=32 covers are balanced
   across ordinary-`decide` shards. **Exact reproduced and kernel-sharded;
   no `native_decide`.**

Verdict: PASS as an unconditional restricted-but-unbounded Target 2 result
and six complete Target 2 rows. It does not control the finite strip below
the row-dependent threshold for arbitrary even `k`.

## Dependency tree: lower prime-power terms

1. A lower prime-power owner contributes its exponent plus the exact split
   baseline `v_p((i-1)!(k-i)!)`. **Lean banked.**
2. Upper concentration loses at most `v_p((k-1)!)`; multiplication by four
   contributes exactly `v_p(4)`. **Lean banked.**
3. The displayed factorial-loss inequality excludes that position; it is
   automatic at both endpoints for all primes and at every position for
   `p>k`. **Lean banked.**
4. A single large-base rough owner `a*p^A` transfers to one upper owner, so
   `p^A<=d+k-1`; the exact size premise `a(d+k-1)<n+i` closes it. The
   sharp centered `1218443kd<1853952n` window supplies this for
   `3707904a<=1218443k`. **Lean banked.**
5. Exact interior fixtures at `p=2` and `p=3` violate the unrestricted
   factorial inequality. **Reproduced; universal interior claim rejected.**

Verdict: PASS as proper unbounded restrictions, not a proof that arbitrary
smooth lower terms contain such a prime-power owner.

## Dependency tree: large gap components and grouped owners

1. The exact power bracket gives `18(n+1)<13kd` for every large-row
   equation. **Lean banked.**
2. A clean local square lift `p^(2e)|3(n+i)-d`, together with positivity,
   gives `6p^(2e)<(13k-6)d+18(k-1)`. **Lean banked for every prime
   `p>=k`, positive `e`, and `p^e|d`.**
3. The same inequality holds for every square divisor of a positive local
   residual.  Composing with the existing full cleaned owner aggregation
   gives the bound for every bucket in one assignment constructed from the
   equation. **Lean banked.**
4. Whole gaps `d=p^e`, `e>=2`, satisfy the opposite weak inequality and are
   impossible.  If `d=p^e q^f` with distinct `p,q>=k`, the full components
   therefore have distinct owners. **Lean banked, all parity.**
5. For odd `k>=17`, the surviving distinct-owner branch constructs the
   uniform `A=3k+2` Pell certificate and both second-lift divisibilities.
   **Lean banked.**
6. Simultaneous vanishing forces a reflected harmonic-denominator value.
   The complete Sylvester--Schur theorem is now vendored, and a p-adic
   interval wrapper proves uniformly that this value is not an integer for
   every odd `k>=5`.  The generic coefficient identities, strict monotonicity
   of the owner slope, reflection step, and final bridge from two zero
   obstructions to that value are also formalized. **Lean banked.**
7. Independently, Lucas arithmetic at `k=p^a-1`, `p>=5`, excludes `p^a`
   from both endpoint parameters. **Lean banked; a proper restriction, not
   a congruence-only closure.**

Verdict: PASS as genuine infinite subclasses and a uniform Pell reduction.
The surviving nonzero-obstruction Pell branch and arbitrary mixed support
remain open.

## Dependency tree: consecutive small-part mass

1. Define the part of each integer supported on primes at most `k`.
   **Lean banked.**
2. `k!` divides every stripped length-`k` block product, and an exact equation
   gives stripped upper product equal to four times the lower. **Lean banked.**
3. Erdős--Lacampagne--Selfridge Theorems 1 and 4 classify bounded parts.
   **Theorem 1 proof reproduced paper-level; Theorem 4 remains an explicit
   external dependency and is not represented as a Lean axiom.**
4. In the both-bounded branch, exact owner accounting gives at least `k+1`
   edges, then `k+2` beyond `(2(k+1))^k`; at a larger displayed threshold
   every component is spanning or an even half-size component. **Exact
   paper derivation and computational audit.**
5. A reflection-compatible k=19 four-cycle fixture satisfies ordering,
   owner rows, `n>9d`, and aggregate reflection but fails the lower ratio
   window. **Exact counterfixture reproduced.**

Verdict: PASS for the kernel arithmetic and stated paper-level restrictions;
FAIL as a cycle closure. No extra alternating determinant exists.

## Mandatory falsification verdicts

- `k=9,15`, `d=1` telescopes: preserved by every new odd-tail lemma.
- `(984,3177026,4480)`: exact window and rows 1..16 reproduced; row 17 fails;
  not an equation solution.
- `(244,48502,277)`: exact window and rows 1..15 reproduced; row 16 fails;
  not an equation solution.
- Fixed-prefix claims: remain refuted.
- Congruence-only route: not used.
- Gross log-mass counting: not used.

## Current exact gap

The terminal proof is now composed through the single quantified statement
`FinalResidual686Hypothesis` in
`ErdosProblems/Erdos686FinalResidual.lean`. Its odd arm starts at `10^1000`
and carries `AllOwnerAssemblyThirdNonzeroCertificate`. Its large-row arm
removes `k=16,18,20,24,28,32`, every universal even tail, the exact
split-factorial prime-power families, and the large-base owner families with
`3707904a<=1218443k`.  It also records the component and complete grouped-
owner square ceilings and the prime-power boundary-row restriction.
For odd whole gaps supported on two distinct primes at least `k`, it also
records the uniform `A=3k+2` Pell certificate and the exact second-lift
divisibilities, without claiming that this restriction closes the family.

Lean proves

```text
FinalResidual686Hypothesis
  -> OddThueTail1000Hypothesis
  -> OddThueTailHypothesis,

FinalResidual686Hypothesis
  -> LargeKSmoothHypothesis,

FinalResidual686Hypothesis
  -> not (universal Erdos 686 statement).

OddThueTail1000Hypothesis and LargeKSmoothHypothesis
  -> FinalResidual686Hypothesis.
```

The exact named first-arm theorems are
`oddThueTail1000Hypothesis_of_finalResidual` and
`oddThueTailHypothesis_of_tail1000`. The residual hypothesis itself remains
open.  The theorem `finalResidual_iff_tail1000_and_smooth` proves that the
single interface is equivalent to the conjunction of the updated two
targets.  Its explicit premises are an auditable ledger of genuine new
unconditional results, but naming this target-equivalent residual is not
itself progress.
