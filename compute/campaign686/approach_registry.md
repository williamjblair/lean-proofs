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
| T1-CF | CF remainder identity | Substitute each exact quasi-convergent class into `P_k(X)-4P_k(Y)` and retain the signed integral remainder, not just `|alpha-X/Y|`. | active | For k=5, a genuine root must satisfy the exact floor pin `g^2=floor(5A_3/A_5)`; among 341 stored rows only three nontrivial square/divisor floors survive and none is a root. No theorem controls the infinite tail. |
| T1-VAL | p-adic valuation | A prime power `p^e | d`, `p >= k`, localizes uniquely and forces a square lift, cubic at the center; valuation concentration replaces uniqueness when `p<k`. | proved and Lean-banked | For `p>=k`, `p^(2e)<A_k*d`, with `A_k=14,17,23,26,29,35`, and the center gives `p^(3e)<A_k*d`. For `p<k`, all valuation outside one factor loses at most `1+v_p((k-1)!)`; the exact universal constant `14!*35*13^30<10^120` excludes every whole prime-power gap `d=p^e>=10^120`, including bases 2 and 3. Mixed-prime gaps remain open. |
| T1-2P | Two-prime concentration/Pell | For `d=p^e q^f`, combine global residual cleaning with the second and third local lifts. | complete two-prime-support slice closed; Lean-banked and hostile-audited | Uniformly including `p=2,3`, same owners close by coprime square multiplication; distinct owners close by a cleaned Pell relation, second obstructions, and cubic repair of reflected simultaneous zeros.  Every such gap is below `10^120`; surviving gaps have at least three distinct prime divisors. |
| T1-2O | Aggregate cleaned owners | Group arbitrary prime support by cleaned residual owner and apply the two-bucket obstruction calculus. | complete two-owner branch; Lean-banked and hostile-audited | The exact all-prime loss table is `G_k=(108,1620,136080,1224720,242494560,18914575680)`. Finite factorization, coprime bucket assembly, square divisibility, and `g<=G_k` are kernel-banked.  Global concentration chooses one assignment; at target size its nonzero cleaned owner range has no two-index cover.  Three explicit distinct live prime/owner witnesses are now extracted from that same assignment, but further owners are not discarded. |
| T1-GSQ | Global residual square lift | Recenter every lower factor as `X_i=3(n+i)-d` and retain coefficient cancellation in the exact transformed product equation. | proved and Lean-banked | `d^2 | product_i X_i` for every exact equation, with no prime-base or localization exception. Residual-progression concentration and two-bucket consequences are active. |
| T1-MOM | Global moment cancellation | Use `2^2=4` at the two signed residual centers to cancel the quadratic coefficient. | proved and Lean-banked | `d^3` divides two explicit constant-plus-linear coefficient combinations.  An exact solution shows neither raw product need be cube-divisible; the proper next use is the three-or-more-bucket regime. |
| T1-3B | Three cleaned residual buckets | Eliminate the two opposite near-square residuals from the second through fourth local lifts, then use the verified short window. | exact local restrictions through fourth order banked; short-CRT node open | Cyclically, `P|O_i`, `P^2|-3O_i+180E_i g^2(i-j)(i-l)d`, and `P^3|3bcF_i+P^2J_i`.  All 1,035 zero slopes are pairwise distinct, but an unbounded Hensel/CRT pseudo-family lifts the package through fourth order while failing the equation/window.  The next lemma must use the short window quantitatively. |
| T1-3B-Z | Zero-obstruction LCM packing | If one `O_s` vanishes, pack all three cleaned components into one coefficient product and apply the target loss bound. | repaired six-row wrapper Lean-banked and hostile-audited | The repaired ordinary-`decide` certificate checks all six target rows and gives exact coefficient bounds `<10^30,<10^18`; coprime packing yields `d|A*B*K*g^4`, excluding every designated zero at `d>=10^120`. The historical noncompiling SHA remains an immutable FAIL record. The all-nonzero short-CRT/window core remains. |
| T1-PUI | Puiseux denominator | Expand the algebraic branch solving `P_k(X)=4P_k(Y)` beyond the leading root and prove an explicit denominator/integrality trap. | blocked | After `L` terms the cleared algebraic norm grows like `Y^(2L(k-1)-2)`; ordinary norm-smallness cannot force zero without new denominator cancellation. |
| T1-UNIT | Unit equation | Use conjugate information in `Q(4^(1/k))` to bound the structured norm identity. | active | Generic Baker-Feldman bounds are disallowed unless below `10^120`. |
| T1-SCALE | Primitive CF scale | For `X=gu`, `Y=gv`, use the exact polynomial in `z=g^2`, its coefficient filters, and the discriminant square condition. | partly proved; low-order closure refuted | An explicit unbounded k=5 family passes gcd, parity, sign, support, ratio, and the first two z-adic filters while `Q(z)>0`; the discriminant square lift is the original genus-6 curve in disguise. The floor pin is the surviving proper restriction. |

## Target 2 routes

| ID | Family | Exact proposed leverage | Verdict | Evidence or gap |
|---|---|---|---|---|
| T2-MATCH | Prime-power matching | Match maximum-valuation owners across the exact lower and upper blocks, then compress their difference chunks. | proved proper compression; Lean-banked | `B(k,n)` divides `(k-1)!` times the centered-difference lcm; the row-only fallback costs two factorials. Both deep fixtures pass, but lcm mass alone has `2k-1` hosts and does not close large `d`. |
| T2-VAL | Sliding-window valuations | Compare the unique landing rows of every prime power `p^e > k` with the exponent budget from the exact equation. | active | Gross log-mass counting alone is known insufficient. |
| T2-TRANS | Row-transition rigidity | Use changes between consecutive row windows to force an unsupported prime power at an unbounded row. | active | Fixed-prefix variants are refuted. |
| T2-XFER | Transfer to centered equation | Combine double smoothness with the centered `P_k` identity to obtain structure absent from arbitrary smooth blocks. | active | Smoothness by itself is not a universal obstruction. |
| T2-REFL | Reflection gcd and owner correlation | With `S=2n+d+k+1`, combine reflection, lower/upper concentration, and matching. | proved proper restrictions; Lean-banked and hostile-audited | Besides `S | reflectionCoeff(k)*reflectionProduct(k,d)`, every residual prime power divides `|i+j-(k+1)|`; non-reflected pairs land in `lcm(1,...,k-1)`, while `j=k+1-i` remains. Also `S | reflectionCoeff(k)*(k-1)!*reflectionDiffLcm(k,d)`. The factorial-lcm and product bounds are incomparable. |
| T2-442 | Greatest-prime-factor wedge | Apply the published Nair-Shorey `P(x...(x+k-1)) > 4.42k` theorem after proving every lower term composite. | paper-rigorous; Lean-checked downstream of explicit interface | Closes the unbounded range `k >= 16`, `k <= d`, `50*(d+k-1) <= 221*k`; the Nair-Shorey theorem itself is not formalized here. |

## Stronger banked Target 2 facts

- `difference_block_below_n_of_four_solution`: `d+k-1 < n`.
- `smooth_blocks_of_four_gap_solution`: both length-`k` blocks are smooth up
  to `d+k-1`.
- `smooth_blocks_and_reflection_of_four_gap_solution`: the two blocks and
  `2*n+d+k+1` are all smooth up to `d+k-1`.
- `LargePrimeMatch`: every odd prime above `k` has unique support in each
  block, equal valuations, and prime-power divisibility of the exact gap.
- `row_smooth_of_four_gap_solution`: row `j` has the sharper cap `d+k-j`.
- `blockProduct_dvd_factorial_mul_centeredDiffLcm_four`: the exact equation
  puts the complete lower block into one centered lcm after one factorial
  allowance.
- `exists_reflection_owner_offset_restriction_four`: every reflection-center
  prime power lands on an owner offset; the reflected pair is the surviving
  alternative.
- `reflection_lcm_compression_four`: the reflection center divides one
  coefficient, one factorial, and the lcm of the positive reflected
  differences.
- `k_mul_gap_lt_five_mul_n_of_four_solution`: `kd<5n` for `k>=16`.

These are premises for new attacks, not solutions of `LargeKSmoothHypothesis`.

## Pipeline audit

The combined checkpoint has 537 manifest entries and 537 regenerated
attestations, including 459 entries for problem 686, 30 for problem 23, and
44 arithmetic-spine entries for problem 730.  The combined axiom sweep reports
963 clean headline surfaces.  The emitter
parses wrapped and axiom-free reports, rejects missing theorem reports, and
accepts any subset of `[propext, Classical.choice, Quot.sound]`.

## Audit rules

1. Expand every qualitative estimate to an explicit quantified bound.
2. Give an exact witness for every `refuted` verdict.
3. Do not mark a target-equivalent missing lemma as progress.
4. Reproduce every computational claim from checked-in source using exact arithmetic.
5. Admit a result to Lean only after all relevant mandatory fixtures pass.
