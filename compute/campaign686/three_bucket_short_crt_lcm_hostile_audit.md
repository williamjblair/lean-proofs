# Hostile audit: Erdős 686 three-bucket short-CRT LCM restriction

Verdict: **PASS for the mathematical zero-obstruction exclusion, the generic kernel node, and the exact finite arithmetic; claim-language FAIL for presenting the row-wise `abc` thresholds as new equation-level progress.**  The exported Lean module is not, by itself, a row-wise zero-exclusion theorem: its final generic theorem takes the finite coefficient bounds as hypotheses, while Python discharges those bounds.  Thus this checkpoint is not yet kernel-complete or attestation-ready under the stated intake protocol.  Mathematically, the generic theorem plus the independently reproduced finite certificate excludes every vanishing composed second obstruction at `d >= 10^120`.  The listed thresholds are valid consequences of the nonzero branch, but every exact equation tuple in scope already satisfies the vastly stronger banked inequality

```text
abc > 125*g^2*d.
```

Thus the genuinely new restriction is `O_i,O_j,O_l != 0`.  The residual short-CRT/window lemma remains unproved, and nothing audited here closes the exactly-three-bucket slice or Erdős #686.

Post-audit remediation (2026-07-10): the producer findings were edited after
the frozen audit to withdraw the novelty claim and expose the missing Lean
wrapper prominently.  The frozen findings hash below intentionally records
the pre-remediation input that was audited; the theorem and verifier inputs
remain unchanged.

## Frozen artifacts

Producer inputs were read at these SHA-256 values and were not edited:

```text
1c49e5115b1cc7a11dd2e04dda6113ed84fc74e50f7294b6836e4d45ff8bc58e  ErdosProblems/Erdos686ThreeBucketShortCrtLcm.lean
d727dd81d5eb698444abc1cb942aa79f9824831b13ae8a6d3959db92bb43c9f5  compute/campaign686/three_bucket_short_crt_lcm_verify.py
b1902029f61a02603ba8b61d1309ecb4c53b8c4773b14a1e785a575eca515fbd  compute/campaign686/test_three_bucket_short_crt_lcm_verify.py
1698ae462a464e1bd725394d90bc0ff7349d87a0281dfe20af489db42d8b6a13  compute/campaign686/three_bucket_short_crt_lcm_findings.md
95e89dc52512cb184c43523d4cfc1ab0a7a2d56cc0bd3c9616bbd4a9442a3655  docs/plans/2026-07-10-erdos686-three-bucket-short-crt-lcm.md
```

Independent audit artifacts:

```text
3743b49e0fc3efa86ea9fcc3218e84256ae7cae0b3da685990628d79edac5a15  ErdosProblems/Erdos686ThreeBucketShortCrtLcmAudit.lean
a2ba583ffd90b5bdfc9a2b85489aab88da9a2fbbf044b5f583d619ae12a74862  compute/campaign686/three_bucket_short_crt_lcm_hostile_verify.py
e2599b32e76e9b13c04ae5bf84eece607465f38ae6eb890cfc6d5b193e85bd69  compute/campaign686/test_three_bucket_short_crt_lcm_hostile_verify.py
2dc81dd8ce392e9658b69dccfdb8ff03e48f4fbcb6e384cce424fd3b84010bf0  docs/plans/2026-07-10-erdos686-three-bucket-short-crt-lcm-hostile-audit.md
```

The hostile verifier imports no producer verifier or prior audit module.  It reconstructs the signed Taylor coefficients with elementary reciprocal sums rather than the producer's polynomial route.

## Exact dependency audit

For distinct owners `i,j,l`, write the pairwise-coprime cleaned components as `P,Q,R`, their positive cofactors as `a,b,c`, and

```text
d = gPQR,
X_i = aP^2,  X_j = bQ^2,  X_l = cR^2,
t = abc.
```

For an owner `s`, let `u,v` be the other owners, set `delta_s=(s-u)(s-v)`, and define

```text
O_s = 3(C_s*t - 12*D_s*g^2*delta_s),
F_s = -3*O_s + 180*E_s*g^2*delta_s*d.
```

The checkpoint takes the cyclic divisibilities `H_s|O_s` and `H_s^2|F_s` from the previously audited three-bucket module.  Its new branch is:

```text
assume O_R=0
|
+- Z1 positive zero slope
|  `- t/g^2 = 12*D_R*delta_R/C_R > 0
|
+- Z2 denominator-cleared opposite-owner identities
|  +- D_P'*O_P = N_P*g^2, hence P | N_P*g^2
|  `- D_Q'*O_Q = N_Q*g^2, hence Q | N_Q*g^2
|
+- Z3 zero-owner third lift
|  `- R^2 | K*g^2*d
|     `- d=gPQR; cancel one positive R and remove only coprime P,Q
|        `- R | K*g^3
|
+- Z4 common-LCM packing
|  `- A|L, B|L, K|L
|     `- P,Q,R all divide L*g^3
|        `- PQR | L*g^3 and d | L*g^4
|
+- Z5 finite cutoff
|  `- L<=L_k, g<=G_k, and L_k*G_k^4 < 10^120
|     `- contradiction
|
`- N1 nonzero branch
   `- H_s<=|O_s| cyclically
      `- d <= G_k*product_s(3|C_s|t+36|D_s|G_k^2|delta_s|).
```

Per-node verdicts:

- **Z1 PASS.** `t` and `g` are positive, so only positive rational zero slopes can occur.  All nonpositive occurrences are retained in the count and rejected only at this sign step.
- **Z2 PASS.** If the reduced cross coefficient is `N/D`, substitution gives the integer identity `D*O=N*g^2`.  The proof never inverts `D` modulo a component.  The scan includes 600 positive-zero records with a nonunit denominator; the largest row denominators are reported below.
- **Z3 PASS.** One `R` cancels from `R^2 | R*(K*g^3*P*Q)`.  Only `gcd(R,PQ)=1` is used afterward.  There is no hidden `gcd(R,g)=1` premise.
- **Z4 PASS.** Pairwise coprimality is exactly sufficient to pack the three divisors into one common multiple.  Padding the two `g^2` divisibilities to `g^3` and multiplying the recovered `PQR` by the outer `g` explains the exact fourth power.
- **Z5 PASS.** The independent scan covers every owner occurrence and every sign, center, reflection, reduced denominator, row maximum, and threshold transition.
- **N1 PASS.** Once zeros are excluded, positivity and divisibility give `H_s<=|O_s|`; the absolute-value majorant is monotone in `t` and `g`.

The `g^4` loss is sharp under the generic theorem's hypotheses.  The nonunit, pairwise-coprime fixture

```text
(P,Q,R,g,A,B,K,L,d)=(2,5,27,3,2,5,1,10,810)
```

satisfies both opposite-owner divisibilities and `R^2 | K*g^2*d`; `d | L*g^4`, while `d` does not divide `L*g^3`.

## Kernel gate

The source exposes exactly nine public theorems:

```text
second_obstruction_cross_dvd_of_other_zero
sq_dvd_self_mul_cancel
pairwise_coprime_three_mul_dvd
zero_owner_third_component_dvd
three_bucket_zero_owner_gap_dvd_lcm_power
three_bucket_zero_owner_gap_lt_of_lcm_bounds
three_bucket_zero_owner_global_numeric_cutoff
three_bucket_zero_owner_coarse_numeric_cutoff
three_bucket_zero_owner_gap_lt_cutoff_of_coarse_coefficients
```

The audit importer prints all nine plus the banked comparison theorem `twice_gap_lt_n_of_four_solution`.  Their kernel assumptions are:

```text
sq_dvd_self_mul_cancel:
  [propext]
second_obstruction_cross_dvd_of_other_zero:
  [propext, Classical.choice, Quot.sound]
pairwise_coprime_three_mul_dvd:
  [propext, Quot.sound]
zero_owner_third_component_dvd:
  [propext, Quot.sound]
three_bucket_zero_owner_gap_dvd_lcm_power:
  [propext, Quot.sound]
three_bucket_zero_owner_gap_lt_of_lcm_bounds:
  [propext, Quot.sound]
three_bucket_zero_owner_global_numeric_cutoff:
  [propext, Classical.choice, Quot.sound]
three_bucket_zero_owner_coarse_numeric_cutoff:
  [propext, Classical.choice, Quot.sound]
three_bucket_zero_owner_gap_lt_cutoff_of_coarse_coefficients:
  [propext, Classical.choice, Quot.sound]
twice_gap_lt_n_of_four_solution:
  [propext, Classical.choice, Quot.sound]
```

All are within the allowed gate.  `lake build ErdosProblems.Erdos686ThreeBucketShortCrtLcm` and the audit import both succeed.  The only producer diagnostics are two style lints for redundant tactic sequencing.  There are no private declarations and no executable `sorry`, `admit`, `axiom`, `native_decide`, `of_decide`, `unsafe`, `implemented_by`, or `extern` constructs in the audited Lean and Python files.

There is an important formal-coverage boundary.  None of the nine public theorems quantifies over the six target rows, derives the raw cross and third coefficients from `localSecondConstant`, `localSecondLinear`, and `localThirdQuadratic`, or proves their required bounds.  In particular,

```text
three_bucket_zero_owner_gap_lt_cutoff_of_coarse_coefficients
```

accepts `hAmax`, `hBmax`, and `hKmax` as premises.  The exact Python scan verifies those premises for every case, but no exported Lean theorem supplies them and composes the row application.  This is consistent with the producer plan's split between a kernel-banked generic node and an external finite certificate, but it is not step 3 of the engagement's proof-intake protocol.  A row-quantified Lean wrapper using the already-banked coefficient tables is still required before attestation.

## Independent finite certificate

There are `1,035` unordered triples and `3,105` owner occurrences.  The hostile scan independently obtains `1,427` positive-zero and `1,678` nonpositive-zero occurrences.

| `k` | positive | nonpositive | center triples | reflected-pair triples | nonintegral-denominator cases | max denominator |
|---:|---:|---:|---:|---:|---:|---:|
| 5 | 12 | 18 | 6 | 6 | 0 | 1 |
| 7 | 45 | 60 | 15 | 15 | 18 | 5 |
| 9 | 112 | 140 | 28 | 28 | 54 | 35 |
| 11 | 225 | 270 | 45 | 45 | 84 | 7 |
| 13 | 396 | 462 | 66 | 66 | 150 | 77 |
| 15 | 637 | 728 | 91 | 91 | 294 | 143 |

The row maxima and exact zero bounds are:

| `k` | maximizing indices, zero owner | `L_k` | `L_k G_k^4` |
|---:|:---|---:|---:|
| 5 | `(1,4,5), 1` | 5,443,200 | 740,541,350,707,200 |
| 7 | `(1,2,7), 1` | 59,999,849,280 | 413,247,483,519,713,740,800,000 |
| 9 | `(1,8,9), 1` | 736,171,343,178,485,760 | 252,438,801,810,021,029,402,684,623,002,009,600,000 |
| 11 | `(1,10,11), 1` | 34,885,840,090,609,728,000 | 78,486,764,429,761,645,052,953,426,899,755,335,680,000,000 |
| 13 | `(1,12,13), 1` | 820,995,472,546,561,208,033,280 | 2,838,891,296,780,015,046,791,841,911,350,004,426,030,003,822,316,748,800,000 |
| 15 | `(1,14,15), 1` | 138,245,988,147,349,868,236,401,258,147,840 | 17,694,526,643,294,042,605,461,686,913,458,493,647,472,960,653,351,115,605,266,135,410,278,400,000 |

Every last-column value is strictly below `10^120`.

The independently recomputed coarse constants are exactly

```text
Cmax = 87,178,291,200
Dmax = 283,465,647,360
Emax = 392,156,797,824
Amax = 348,736,460,194,535,895,465,984,000
Kmax = 13,835,291,827,230,720.
```

The coarse product `Amax^2*Kmax*18,914,575,680^4` is also strictly below `10^120`.

For the nonzero branch, the exact threshold search reproduces:

| `k` | least majorant threshold `T_k` |
|---:|---:|
| 5 | 46,296,296,296,296,296,296,296,296,296,294,624,457 |
| 7 | 716,294,573,088,391,804,384,271,040,815,308,651 |
| 9 | 3,214,574,169,492,218,063,895,298,388,397,719 |
| 11 | 18,497,091,393,047,867,380,101,052,189,640 |
| 13 | 25,548,663,987,620,205,641,977,050,294 |
| 15 | 33,652,495,592,619,590,630,929,591 |

For every row, the maximizing threshold triple is `(1,2,k)`, and exact integer evaluation verifies

```text
max_I U_(k,I)(T_k-1) < 10^120 <= max_I U_(k,I)(T_k).
```

These are exact thresholds for this uniform majorant, not sharp lower bounds for actual equation solutions.

## Material novelty correction for `abc`

The findings' inference `abc>=T_k` is valid.  Its characterization as a new strict refinement is not.

For an exact solution with `k>=5` and `d>=k`, the already-banked theorem `twice_gap_lt_n_of_four_solution` gives `2d<n`.  Hence every selected residual

```text
X_s = 3(n+s)-d
```

is strictly greater than `5d`.  Multiplying the three selected identities gives

```text
abc*(PQR)^2 = X_i*X_j*X_l > 125*d^3.
```

Using `d=gPQR` and cancelling the positive `(PQR)^2` yields

```text
abc > 125*g^3*PQR = 125*g^2*d.
```

At `d>=10^120`, therefore,

```text
abc >= 125*10^120 + 1.
```

This exceeds every reported `T_k`; even the weakest ratio is greater than `2.7*10^84`.  Consequently:

- the row threshold calculations are correct;
- `abc<T_k` branches were already impossible in the exact equation context;
- the phrase "exact necessary lower bound" is safe only if read as "exact threshold of this chosen majorant";
- the genuinely new result is exclusion of all three zero-obstruction branches.

The findings remain honest that the short-CRT lemma is unproved, but their novelty language should be narrowed accordingly.

## Boundary and falsification replay

- **Small primes and loss sharing:** generic packing succeeds for `(P,Q,R,g)=(2,3,5,30)`, where `g` shares a prime with every cleaned component.  No cancellation from `g` is used.
- **Unit components:** `(1,2,3,6)` and `(1,1,1,7)` exercise the generic theorem's unit boundaries.  The target application separately assumes `P,Q,R>1`.
- **Fourth-power sharpness:** the `(2,5,27,3)` fixture above rules out silently replacing `g^4` by `g^3`.
- **Centers and reflections:** every center-containing and reflected-pair triple is included in the exact counts above.  A center has nonpositive zero slope when it is the proposed zero owner but remains available as either opposite owner.
- **`d=1`:** the exact telescopes `(k,n,d)=(9,2,1)` and `(15,4,1)` reproduce.  They are below the cutoff and have no three nontrivial cleaned components.
- **Below-threshold fixture:** `(k,i,j,l,P,Q,R,g,d,n)=(5,1,2,3,2,7,5,97,6790,25177)` has `abc=66,307,884,500`, exact progression, all six local and all six composed divisibilities, and the short window.  It lies below both target and `T_5` and is not an equation solution.
- **121-digit pseudo-witness:** the independent CRT reconstruction with components `(101^20,103^20,107^20)` has `d>=10^120`, exact progression, all local and composed divisibilities, and all three `O_s` nonzero.  It exceeds `T_5` but fails the short window and the equation.  It therefore survives as a falsifier of congruence-only closure, exactly as required.

## Exact remaining quantified gap

For each row

```text
(k,A_k,G_k,T_k) =
  (5,14,108,46296296296296296296296296296294624457),
  (7,17,1620,716294573088391804384271040815308651),
  (9,23,136080,3214574169492218063895298388397719),
  (11,26,1224720,18497091393047867380101052189640),
  (13,29,242494560,25548663987620205641977050294),
  (15,35,18914575680,33652495592619590630929591),
```

prove that no positive integers `d,g,P,Q,R,a,b,c` and distinct `i,j,l in [1,k]` satisfy all of:

```text
d >= 10^120,
1 <= g <= G_k,
d = gPQR,
P,Q,R > 1 and pairwise coprime,
abc >= T_k,

aP^2-bQ^2 = 3(i-j),
aP^2-cR^2 = 3(i-l),

0 < aP^2 < A_k*d,
0 < bQ^2 < A_k*d,
0 < cR^2 < A_k*d,

O_i != 0, O_j != 0, O_l != 0,
P | O_i, Q | O_j, R | O_l,
P^2 | F_i, Q^2 | F_j, R^2 | F_l,
```

where, cyclically, `delta_s=(s-u)(s-v)`,

```text
O_s = 3(C_s*abc - 12*D_s*g^2*delta_s),
F_s = -3*O_s + 180*E_s*g^2*delta_s*d.
```

This statement explicitly retains the nonzero obstructions, row threshold, exact step-three progression, all three short windows, and every cyclic first- and second-power divisibility.  It is stronger than the equation-specific slice because it omits `n` and the block equation.  It is still unproved and must not be counted as closure.

## Reproduction gates

The focused hostile suite passes `4 tests`.  The final combined producer/hostile suite, Python byte-compilation, kernel rebuild, forbidden scan, and whitespace check are recorded by the audit handoff.  No producer file, shared integration file, attestation, or git commit was changed by this audit.
