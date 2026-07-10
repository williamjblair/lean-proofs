# Erdős 686 approach registry

Campaign branch: `codex/erdos686-full-solve`

Exact targets:

```lean
def OddThueTailHypothesis : Prop :=
  ∀ k, k ∈ ({5, 7, 9, 11, 13, 15} : Finset ℕ) →
    NoLargeGapSolutionFour k (10 ^ 120)

def LargeKSmoothHypothesis : Prop :=
  ∀ k n d : ℕ, 16 ≤ k → k ≤ d →
    blockProduct k (n + d) = 4 * blockProduct k n →
    (∀ i, i ∈ Finset.Icc 1 k → ∀ q, q.Prime → q ∣ n + i → q < d + k) →
    False
```

The first declaration is in `ErdosProblems/Erdos686FinalReduction.lean`;
the second is in `ErdosProblems/Erdos686PrimeObstruction.lean`.

Verdicts are one of `active`, `proved`, `refuted`, or `blocked`. A `proved`
entry requires a complete dependency tree and exact reproduction; a `blocked`
entry must name one quantified missing lemma.

## Mandatory falsification fixtures

| Fixture | Scope | Required check |
|---|---|---|
| `k = 9`, `P_9(8) = 4 P_9(7)` | Target 1 structure | Any polynomial identity must explain why `d = 1` survives and use `d >= k` where needed. |
| `k = 15`, banked `d = 1` telescope | Target 1 structure | Same boundary check as `k = 9`. |
| `(k,n,d) = (984,3177026,4480)` | Target 2 row structure | Passes rows 1 through 16 and fails row 17; refutes every fixed row-prefix cap at 16. |
| `n = 48502` survivor cluster | Target 2 row structure | Passes through row 15 and fails at row 16 in the recorded range. |
| MalekZ all-moduli family for `(N,k) = (4,5)` | Congruence routes | A pure finite-congruence obstruction cannot be universal. |

## Target 1 routes

| ID | Family | Exact proposed leverage | Verdict | Evidence or gap |
|---|---|---|---|---|
| T1-CF | CF remainder identity | Substitute each exact quasi-convergent class into `P_k(X)-4P_k(Y)` and retain the signed integral remainder, not just `|alpha-X/Y|`. | active | Parallel analysis in progress. |
| T1-VAL | p-adic valuation | A prime power `p^e | d`, `p >= k`, localizes to one lower factor and forces a square lift, cubic at the center. | proved on paper; Lean in progress | Exact consequence: `p^(2e) < A_k*d`, with `A_k = 14,17,23,26,29,35`; center gives `p^(3e) < A_k*d`. This excludes a dominant primary component but is vacuous for gaps supported below `k`. |
| T1-PUI | Puiseux denominator | Expand the algebraic branch solving `P_k(X)=4P_k(Y)` beyond the leading root and prove an explicit denominator/integrality trap. | blocked | After `L` terms the cleared algebraic norm grows like `Y^(2L(k-1)-2)`; ordinary norm-smallness cannot force zero without new denominator cancellation. |
| T1-UNIT | Unit equation | Use conjugate information in `Q(4^(1/k))` to bound the structured norm identity. | active | Generic Baker-Feldman bounds are disallowed unless below `10^120`. |
| T1-SCALE | Primitive CF scale | For `X=gu`, `Y=gv`, exact coefficient reduction gives `g^2 | (r!)^2(u-4v)`. | proved exact; insufficient | The primitive branch `g=1` survives automatically; most recorded convergent scales survive as well. |

## Target 2 routes

| ID | Family | Exact proposed leverage | Verdict | Evidence or gap |
|---|---|---|---|---|
| T2-MATCH | Prime-power matching | Build the full row-by-prime-power incidence graph and seek a Hall deficit forced by all `k` rows. | active | Must pass both deep survivor fixtures. |
| T2-VAL | Sliding-window valuations | Compare the unique landing rows of every prime power `p^e > k` with the exponent budget from the exact equation. | active | Gross log-mass counting alone is known insufficient. |
| T2-TRANS | Row-transition rigidity | Use changes between consecutive row windows to force an unsupported prime power at an unbounded row. | active | Fixed-prefix variants are refuted. |
| T2-XFER | Transfer to centered equation | Combine double smoothness with the centered `P_k` identity to obtain structure absent from arbitrary smooth blocks. | active | Smoothness by itself is not a universal obstruction. |
| T2-REFL | Reflection gcd compression | With `S=2n+d+k+1`, compress the banked reflection congruence to `S | reflectionCoeff(k)*reflectionProduct(k,d)`. | proved on paper; Lean in progress | Exact smooth row-prefix counterexamples satisfy this too, so full row constraints remain essential. |
| T2-442 | Greatest-prime-factor wedge | Apply the published Nair-Shorey `P(x...(x+k-1)) > 4.42k` theorem after proving every lower term composite. | paper-rigorous; outside kernel gate | Would close the unbounded range `k >= 25`, `k <= d`, `50*(d+k-1) <= 221*k`; the Nair-Shorey theorem itself is not formalized here. |

## Stronger banked Target 2 facts

- `difference_block_below_n_of_four_solution`: `d+k-1 < n`.
- `smooth_blocks_of_four_gap_solution`: both length-`k` blocks are smooth up
  to `d+k-1`.
- `smooth_blocks_and_reflection_of_four_gap_solution`: the two blocks and
  `2*n+d+k+1` are all smooth up to `d+k-1`.
- `LargePrimeMatch`: every odd prime above `k` has unique support in each
  block, equal valuations, and prime-power divisibility of the exact gap.
- `row_smooth_of_four_gap_solution`: row `j` has the sharper cap `d+k-j`.

These are premises for new attacks, not solutions of `LargeKSmoothHypothesis`.

## Pipeline audit

The campaign baseline now has 349 manifest entries and 349 generated
attestations, including 345 entries for problem 686.  The attestation emitter
parses wrapped and axiom-free reports, rejects missing theorem reports, and
accepts any subset of `[propext, Classical.choice, Quot.sound]`.

## Audit rules

1. Expand every qualitative estimate to an explicit quantified bound.
2. Give an exact witness for every `refuted` verdict.
3. Do not mark a target-equivalent missing lemma as progress.
4. Reproduce every computational claim from checked-in source using exact arithmetic.
5. Admit a result to Lean only after all relevant mandatory fixtures pass.
