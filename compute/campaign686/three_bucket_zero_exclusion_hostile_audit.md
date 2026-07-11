# Hostile audit: Erdős 686 target-row zero-obstruction exclusion

Verdict: **FAIL for kernel intake and attestation; PASS for the independently reconstructed paper/exact conditional argument.**

The frozen producer does not compile from source.  It therefore does not export a valid `.olean`, its seven public declarations cannot be imported and axiom-checked, and it must not be added to `proofs.yaml`, the root import surface, or `attestations.json`.  This is a hard step-3 failure under the engagement protocol, not a lint or presentation issue.

Independently of that implementation failure, the mathematical reduction is sound: for every one of the `6,210` ordered target triples, a designated zero second obstruction gives two nonzero bounded cross coefficients and one nonzero bounded third coefficient; the already-banked coprime packing theorem then forces `d<10^120`.  The three cyclic owner permutations are exact.  Thus a repaired implementation under a new hash can legitimately prove the advertised conditional zero-exclusion theorem.

Even after repair, this is only a proper partial result.  It excludes the zero branch under an assumed three-owner factorization and assumed cyclic divisibilities.  It does not prove the nonzero short-CRT/window lemma, exclude four-or-more cleaned owners, or resolve Erdős #686.

## Frozen artifacts

The five producer inputs were read at the supplied SHA-256 values and were not edited:

```text
5b802dd3db2d63254b251465f96093358389c0eca4d72cdd7608d2238e549ff2  ErdosProblems/Erdos686ThreeBucketZeroExclusion.lean
106f7686c30eed5150d922fa1e0acbd1b7439f1bc000a356df541af724fb4c78  compute/campaign686/three_bucket_zero_exclusion_verify.py
6d7f2aa138e344fed21700b86a58e98a50ebbbbb3976c2d42fd95c9a66ae4810  compute/campaign686/test_three_bucket_zero_exclusion_verify.py
459f43e1d11c02186635bfe617a8bfe372acdcc5c3cc407fc7bfb7f1d78a3f20  compute/campaign686/three_bucket_zero_exclusion_findings.md
0ba5ac8c350406eeccc5e4f134f392487dd3045c4de5dd685964d49c6d22c330  docs/plans/2026-07-10-erdos686-three-bucket-zero-exclusion.md
```

Independent audit artifacts:

```text
bf2c2b7148c387f406becb931eb0f845ca4d09b7017f49d400a21846b9a4f993  ErdosProblems/Erdos686ThreeBucketZeroExclusionAudit.lean
9a56d5fab54e4423f11837967887602bd42db33802f898675d9de67e631781d7  compute/campaign686/three_bucket_zero_exclusion_hostile_verify.py
8269c61e968907998629a6a7078e5d5d2c8f1e1a4633dfbacf7939719a17a946  compute/campaign686/test_three_bucket_zero_exclusion_hostile_verify.py
53aeb83b73a2e5e107002ed7329d8bdffe53229249069cacf91ded9cde9eb24a  docs/plans/2026-07-10-erdos686-three-bucket-zero-exclusion-hostile-audit.md
```

The hostile verifier imports no producer verifier and no prior audit module.  It computes the Taylor coefficients as direct elementary-symmetric sums by omitting zero, one, or two offsets from the local product; this is independent of the producer's polynomial-multiplication implementation.

Post-audit workspace note: after this verdict was reported, remediation of the producer Lean source began under a new hash.  The historical hostile verifier preserves the frozen manifest and reports any live-path drift without pretending to re-audit it.  Every compiler finding and verdict in this document applies only to the frozen `5b802d...` Lean source; a repaired source requires a new hostile audit.

## Exact conditional statement audited

For a target row `k in {5,7,9,11,13,15}`, distinct indices `i,j,l in [1,k]`, natural `a,b,c`, positive pairwise-coprime `P,Q,R`, and positive `g` with

```text
g <= 18,914,575,680,
d = g*P*Q*R,
d >= 10^120,
```

write, cyclically,

```text
delta_s = (s-u)(s-v),
O_s = 3(C_s*abc - 12*D_s*g^2*delta_s),
F_s = -3*O_s + 180*E_s*g^2*delta_s*d.
```

The intended theorem assumes

```text
P | O_i,   Q | O_j,   R | O_l,
P^2 | F_i, Q^2 | F_j, R^2 | F_l,
```

and concludes `O_i != 0`, `O_j != 0`, and `O_l != 0`.

This is stronger than the eventual three-owner application in allowing unit components and zero cofactors.  It is also explicitly conditional: the wrapper does not derive `d=gPQR`, the owner assignment, the progression identities, the residual windows, or the six divisibilities from the block equation.

## Dependency tree and per-node verdicts

```text
assume O_l = 0
|
+- Z1 finite row certificate
|  +- 0 < |A_i|,|A_j| < 10^30
|  `- 0 < |K_l| < 10^18
+- Z2 cross elimination
|  +- P | A_i*g^2
|  `- Q | A_j*g^2
+- Z3 third conversion
|  `- R^2 | K_l*g^2*d
+- Z4 pairwise-coprime packing
|  `- d | |A_i|*|A_j|*|K_l|*g^4
+- Z5 exact cutoff
|  `- (10^30)^2*10^18*18,914,575,680^4 < 10^120
`- contradiction

repeat with (j,l,i; Q,R,P) and (i,l,j; P,R,Q)
```

- **Z1 paper/exact PASS; frozen kernel FAIL.**  The independent scan finds no zero cross or third coefficient in all `6,210` ordered cases and reproduces every bound.  The producer's exhaustive Lean proof times out at the default `200,000` heartbeats, so the certificate is not exported.
- **Z2 algebra PASS; frozen kernel composition FAIL.**  The standalone audit proves the general identity
  `C_zero*O_owner-C_owner*O_zero=A*g^2` by ring normalization, and the hostile verifier checks all `6,210` instances.  In the producer's designated theorem, however, the attempted swapped-zero proof leaves the unsolved goal `True ∨ localSecondLinear k l = 0 ∨ g = 0`.
- **Z3 algebra PASS; frozen kernel composition FAIL.**  The standalone audit proves `F_zero+3*O_zero=K*g^2*d`.  The producer cannot rewrite its `hzero` after unfolding the generic obstruction, leaving the intended equality unsolved.
- **Z4 PASS in the banked kernel dependency.**  Only pairwise coprimality among `P,Q,R` is used.  No coprimality with `g`, `2`, `3`, or any coefficient is assumed or silently used.  The exact fourth power of `g` is necessary under the generic hypotheses.
- **Z5 PASS in exact arithmetic and standalone Lean.**  The rounded majorant is
  `127993057016846539654048809041799413760000000000000000000000000000000000000000000000000000000000000000000000000000000000`,
  strictly below `10^120`; integer division of the cutoff by this majorant is `7`.
- **Cyclic permutation paper/exact PASS; frozen kernel FAIL transitively.**  The hostile verifier checks `18,630` designated-zero views, including every left/right swap and all three component orders.  The cyclic wrapper depends on the failed designated theorem, so it is not kernel-banked.

## Fresh compiler gate

The required command

```bash
lake build ErdosProblems.Erdos686ThreeBucketZeroExclusion
```

reaches the final target after rebuilding dependencies and exits `1`.  The material diagnostics are:

```text
ErdosProblems/Erdos686ThreeBucketZeroExclusion.lean:37:4:
failed to compile definition, consider marking it as 'noncomputable'
because it depends on 'localThirdQuadratic', which is 'noncomputable'

ErdosProblems/Erdos686ThreeBucketZeroExclusion.lean:42:0:
(deterministic) timeout at `whnf`, maximum number of heartbeats (200000)
has been reached

ErdosProblems/Erdos686ThreeBucketZeroExclusion.lean:138:4:
failed to compile definition, consider marking it as 'noncomputable'
because it depends on 'localThirdQuadratic', which is 'noncomputable'

ErdosProblems/Erdos686ThreeBucketZeroExclusion.lean:224:46:
unsolved goals
⊢ True ∨ localSecondLinear k l = 0 ∨ g = 0

ErdosProblems/Erdos686ThreeBucketZeroExclusion.lean:263:8:
Tactic `rewrite` failed: Did not find an occurrence of
targetThreeBucketSecondObstruction k l i j a b c g

ErdosProblems/Erdos686ThreeBucketZeroExclusion.lean:165:8:
(kernel) unknown constant
'Erdos686.Erdos686Variant.target_three_bucket_zero_coefficient_certificate'
```

Because the build fails, no producer object file exists and the audit importer cannot print the seven public declarations.  Error-recovery output inside the failed compilation is itself disqualifying: it reports

```text
target_three_bucket_designated_zero_gap_lt depends on axioms:
[propext, Classical.choice, Quot.sound,
 target_three_bucket_designated_zero_gap_lt]

target_three_bucket_all_second_obstructions_nonzero depends on axioms:
[propext, Classical.choice, Quot.sound,
 target_three_bucket_designated_zero_gap_lt]
```

The self-named dependency is a compiler recovery artifact, not an allowed kernel assumption.  It cannot be attested.  The source contains no explicit `sorry`, `admit`, `axiom`, `native_decide`, `of_decide`, `unsafe`, `implemented_by`, or `extern`; the failure is nevertheless decisive because the object does not build.

The standalone audit module omits the broken producer import, re-proves the cross identity, third identity, cutoff, and cyclic product reorderings, and prints the relevant banked dependencies.  It compiles successfully.  Every printed dependency is within the permitted gate:

```text
localSecondConstant_eq_table:
  [propext, Classical.choice, Quot.sound]
localSecondLinear_eq_table:
  [propext, Classical.choice, Quot.sound]
localThirdQuadratic_eq_table:
  [propext, Classical.choice, Quot.sound]
second_obstruction_cross_dvd_of_other_zero:
  [propext, Classical.choice, Quot.sound]
three_bucket_zero_owner_gap_dvd_lcm_power:
  [propext, Quot.sound]
three_bucket_zero_owner_gap_lt_of_lcm_bounds:
  [propext, Quot.sound]
twice_gap_lt_n_of_four_solution:
  [propext, Classical.choice, Quot.sound]
```

This confirms the underlying dependencies and algebra but cannot substitute for compiling and axiom-checking the producer declarations.

## Independent finite certificate

The exhaustive row results are:

| `k` | ordered triples | max `|A|` at `(owner,zero,other)` | max `|K|` at `(owner,zero,other)` |
|---:|---:|---:|---:|
| 5 | 60 | `691200` at `(1,5,2)` | `75600` at `(1,5,2)` |
| 7 | 210 | `1646023680` at `(1,7,2)` | `8769600` at `(1,7,2)` |
| 9 | 504 | `10180055531520` at `(1,9,2)` | `1190689920` at `(1,9,2)` |
| 11 | 990 | `138849151795200000` at `(1,11,2)` | `206607931200` at `(1,11,2)` |
| 13 | 1,716 | `3691052156423503872000` at `(1,13,2)` | `45893854955520` at `(1,13,2)` |
| 15 | 2,730 | `174368230097267947732992000` at `(1,15,2)` | `12847056696714240` at `(1,15,2)` |

Totals and identity coverage:

```text
ordered distinct target triples: 6,210
zero cross coefficients:          0
zero third coefficients:          0
cross conversion checks:          6,210
third conversion checks:          6,210
cyclic designated-zero checks:   18,630
```

The global maxima agree exactly with the producer output and are strictly below `10^30` and `10^18`.

## Boundary and falsification replay

- **`p=2`, `p=3`, and shared `g`:** `(P,Q,R,g,A,B,K)=(2,3,5,30,2,3,5)` has `gcd(g,P),gcd(g,Q),gcd(g,R)=(2,3,5)`.  Every generic premise holds and `d=900` divides `A*B*K*g^4`.  No cancellation against `g`, `2`, or `3` occurs.
- **Unit components:** `(P,Q,R,g)=(1,2,3,6)` and `(1,1,1,7)` both satisfy the generic premises and conclusion.  This matches the Lean wrapper's `0<P,Q,R`, not `1<P,Q,R`, scope.
- **Fourth-power sharpness:** `(P,Q,R,g,A,B,K)=(2,5,27,3,2,5,1)` gives `d=810`.  It divides `10*3^4=810` but does not divide `10*3^3=270`; replacing `g^4` by `g^3` is invalid.
- **`d=1` telescopes:** the exact equation solutions `(k,n,d)=(9,2,1)` and `(15,4,1)` reproduce.  Both are outside the explicit hypothesis `10^120<=d`; the wrapper makes no claim about them.
- **121-digit pseudo-witness:** for `k=5`, owners `(1,2,4)`, `g=1`, and components

  ```text
  P = 101^20 = 12201900399479668244827490915525641902001
  Q = 103^20 = 18061112346694138117573133075817258818401
  R = 107^20 = 38696844624861790832365403138487376998001
  d = 8528006514942991411329818759017663024603296760011487105481658555774743359211568625230878556970868752918452276874633718401
  ```

  an independent CRT reconstruction gives positive cofactors, the exact step-three progression, every local and composed first- and second-power divisibility, and all three `O_s` nonzero.  Its gap has `121` digits and exceeds the cutoff.  It fails the short window and the block equation.  Thus it satisfies the zero-exclusion conclusion and survives in precisely the unproved nonzero branch; no congruence-only closure follows.

## Exact remaining gap

After a repaired zero-exclusion wrapper is combined with the audited three-owner grouping, the exact remaining three-owner lemma is:

For each

```text
(k,A_k,G_k) in
{(5,14,108), (7,17,1620), (9,23,136080),
 (11,26,1224720), (13,29,242494560),
 (15,35,18914575680)},
```

prove that no positive integers `d,g,P,Q,R,a,b,c` and distinct `i,j,l in [1,k]` satisfy all of

```text
d >= 10^120,
1 <= g <= G_k,
d = g*P*Q*R,
P,Q,R > 1 and pairwise coprime,

a*P^2 - b*Q^2 = 3*(i-j),
a*P^2 - c*R^2 = 3*(i-l),

0 < a*P^2 < A_k*d,
0 < b*Q^2 < A_k*d,
0 < c*R^2 < A_k*d,

O_i != 0, O_j != 0, O_l != 0,
P | O_i, Q | O_j, R | O_l,
P^2 | F_i, Q^2 | F_j, R^2 | F_l.
```

The banked equation estimate additionally supplies `abc>125*g^2*d`, but even with that strengthening the lemma is unproved.  The four-or-more-owner regime is a separate remaining branch.  Therefore this audit records neither exactly-three-owner closure nor full Erdős #686 closure.

## Reproduction gates

```bash
# Expected FAIL on the frozen producer
lake build ErdosProblems.Erdos686ThreeBucketZeroExclusion

# PASS: standalone dependency/algebra audit
lake env lean ErdosProblems/Erdos686ThreeBucketZeroExclusionAudit.lean

# PASS: 2 producer arithmetic tests + 5 hostile tests
python3 -m pytest \
  compute/campaign686/test_three_bucket_zero_exclusion_verify.py \
  compute/campaign686/test_three_bucket_zero_exclusion_hostile_verify.py -q

python3 -m py_compile \
  compute/campaign686/three_bucket_zero_exclusion_verify.py \
  compute/campaign686/three_bucket_zero_exclusion_hostile_verify.py
```

No producer file, shared import, manifest, attestation, or commit was changed by this audit.
