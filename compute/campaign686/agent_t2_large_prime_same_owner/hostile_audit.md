# Hostile audit: large-prime same-owner dominance

## Exact theorem surfaces

The strongest new no-solution surface is:

For distinct primes `p,q`, positive `e,f`, `k>=16`, `k<=d`, `p,q>=k`,
components `p^e,q^f` dividing both `d` and one common lower factor `n+i`, the
quotient-four equation is impossible whenever

`(13k-6)d+18(k-1) <= 6(p^e q^f)^2`.

The whole-gap corollary does not assume a combined lift.  Starting only from
`d=p^e q^f` and an exact equation, it invokes the two separate public local
square lifts, derives the product-square divisor by coprimality, and proves
that their unique owners are distinct.

## Dependency tree and verdicts

1. `eighteen_mul_n_add_one_lt_thirteen_mul_k_mul_gap_of_four_solution`.
   - Source: `Erdos686LargePrimeGapComponent`.
   - Verdict: existing exact `18/13` ratio ceiling.
2. Positive residual `X_i=3(n+i)-d`.
   - Source: existing `9d<n` large-row bound.
   - Verdict: explicit; no positivity premise is hidden.
3. Pairwise-coprime same-owner aggregation.
   - Source: existing public theorem
     `globalResidualGroupedLeft_square_dvd_residual`.
   - Verdict: already stronger than the initially requested raw theorem, so
     no duplicate finite-product result was added.
4. Generic square-divisor ceiling.
   - New statement: `h^2|X_i` implies
     `6h^2<(13k-6)d+18(k-1)` under an exact solution.
   - Verdict: four displayed integer inequalities; every constant is exact.
5. Grouped-owner dominance.
   - New statement: the opposite non-strict inequality for the existing owner
     product rules out the equation.
   - Verdict: a direct strict/non-strict contradiction, not a new hypothesis
     about all solutions.
6. Two-component mixed gap.
   - Source: two instances of
     `primePower_sq_dvd_three_factor_sub_gap` plus prime-power coprimality.
   - Verdict: the combined product-square lift is derived, not assumed.
7. Whole-gap arithmetic.
   - New statement: `d=p^e q^f`, `p,q>=k>=16`, `e,f>0` implies the dominance
     inequality with `h=d`.
   - Verdict: exact chain through `d>=k^2` and
     `13k+12<=6k^2`; no asymptotic phrase remains.
8. Owner separation.
   - Source: the existing unique localization theorem for each component.
   - Verdict: equality of the two owners invokes node 6 and contradicts the
     equation.  The distinct-owner branch remains explicitly open.

## Subsumption audit

- `Erdos686TwoOwnerGrouping` already aggregates arbitrarily many cleaned
  components at one owner and proves their product square divides the same
  residual.
- For `p>=k>=16`, this aggregation retains the full prime-power exponent;
  the factorial cleaning loss is zero.
- `Erdos686TwoPrimeGap.two_large_prime_support_bounded_pell` already proves a
  stronger Pell package and distinct owners for odd rows under its own
  `A<k^2` hypotheses.
- The new work is nonduplicative because it contributes the missing exact
  large-row dominance threshold, permits additional gap factors in the mixed
  theorem, and supplies an all-parity `k>=16` whole-gap wrapper.

## Boundary and falsification audit

- `k=16`: included.  For `p=17,q=19,e=f=1`, the exact margin is 560,458.
- exponent one: included for both components; no square exponent assumption
  on the gap factors is made.
- `p=k` or `q=k`: allowed when that base is prime; the public local lift
  explicitly allows its boundary `p=k`.
- `p=q`: excluded.  Product-square aggregation uses coprimality and must not
  be claimed for two copies of the same primary component.
- primes below `k`: excluded from the direct mixed theorem.  Their full
  powers need not localize without factorial loss.
- extra factors of `d`: allowed in the mixed dominance theorem.  They can
  make the displayed inequality fail, in which case the theorem is silent.
- whole-gap case: dominance is automatic, but only same-owner localization
  is eliminated.  Distinct owners are not converted into a no-solution claim.
- equality at the dominance boundary: excluded correctly because a solution
  gives a strict `<`, while the obstruction uses `<=` in the opposite
  direction.
- grouped assignment premise: it is a finite local certificate already
  constructed from an equation by existing concentration.  The new theorem
  does not assume that every solution has a dominant bucket.
- MalekZ congruence families: irrelevant.  This is not a pure congruence
  obstruction; it combines the exact equation, a positive archimedean bound,
  localization, and a size-dominant owner bucket.
- fixed-prefix witness `(984,3177026,4480)`: no prefix implication appears.
  The theorem only applies after its exact same-owner and dominance premises
  are checked.
- smooth-block census fixtures: no smoothness-only implication is used.

## Mechanical status

- exact verifier: pass;
- focused pytest: `5 passed`;
- exact sweep: 41,625 cases;
- source scan: no `native_decide`, `sorry`, `admit`, or declared axiom;
- trailing-whitespace scan: clean;
- Lean direct-check: success;
- all six `#print axioms` gates: exactly
  `[propext, Classical.choice, Quot.sound]`;
- shared imports, manifests, attestations, and existing theorem modules:
  untouched.
