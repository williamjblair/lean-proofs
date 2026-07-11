# Fresh hostile audit: repaired Erdős 686 three-bucket zero exclusion

Verdict: **PASS.  The repaired module is safe to integrate as a conditional,
zero-branch-only partial result.**

This verdict applies only to repaired producer source SHA
`de9ddc72881c...`.  The historical audit verdict remains **FAIL** for frozen
source SHA `5b802dd3db2d...`; nothing in that audit package was overwritten or
reinterpreted.

The repaired result still does not prove the nonzero three-owner branch, the
four-or-more-owner branch, or Erdős #686.

## 1. Frozen boundaries

### Repaired producer

```text
de9ddc72881c67f4ce7c7b0987eeccd71040f2ac4064deb8f0d6b70f075bd4bd
  ErdosProblems/Erdos686ThreeBucketZeroExclusion.lean
106f7686c30eed5150d922fa1e0acbd1b7439f1bc000a356df541af724fb4c78
  compute/campaign686/three_bucket_zero_exclusion_verify.py
6d7f2aa138e344fed21700b86a58e98a50ebbbbb3976c2d42fd95c9a66ae4810
  compute/campaign686/test_three_bucket_zero_exclusion_verify.py
459f43e1d11c02186635bfe617a8bfe372acdcc5c3cc407fc7bfb7f1d78a3f20
  compute/campaign686/three_bucket_zero_exclusion_findings.md
0ba5ac8c350406eeccc5e4f134f392487dd3045c4de5dd685964d49c6d22c330
  docs/plans/2026-07-10-erdos686-three-bucket-zero-exclusion.md
```

Only the producer Lean source differs from the historical frozen producer
boundary.  The verifier, tests, findings, and producer plan retain their old
hashes.

### Immutable historical FAIL evidence

```text
bf2c2b7148c387f406becb931eb0f845ca4d09b7017f49d400a21846b9a4f993
  ErdosProblems/Erdos686ThreeBucketZeroExclusionAudit.lean
9a56d5fab54e4423f11837967887602bd42db33802f898675d9de67e631781d7
  compute/campaign686/three_bucket_zero_exclusion_hostile_verify.py
8269c61e968907998629a6a7078e5d5d2c8f1e1a4633dfbacf7939719a17a946
  compute/campaign686/test_three_bucket_zero_exclusion_hostile_verify.py
44575160cd98bdb92ea9525b4df67b8d1cfcb027fd61ddb648fdd3c5b0dffc56
  compute/campaign686/three_bucket_zero_exclusion_hostile_audit.md
53aeb83b73a2e5e107002ed7329d8bdffe53229249069cacf91ded9cde9eb24a
  docs/plans/2026-07-10-erdos686-three-bucket-zero-exclusion-hostile-audit.md
```

The historical report still records its exact FAIL verdict and source SHA

```text
5b802dd3db2d63254b251465f96093358389c0eca4d72cdd7608d2238e549ff2.
```

That verdict was correct for that source: it did not compile.  The current
PASS is a new audit of a new source hash.

### Fresh repair-audit artifacts

```text
2cad6a6930bfb075291ae7ed3c5b06668c9123bbd304a2c7cc2ef20d86b5704d
  ErdosProblems/Erdos686ThreeBucketZeroExclusionRepairAudit.lean
868abce63952414aca56f6b72aa18efcc028df9c93473742bf125868b260ee5e
  compute/campaign686/three_bucket_zero_exclusion_repair_hostile_verify.py
7e52e0d7467caabb4259aa8fda94381ad7fdf02f0d11bbb470a2d307a950dab4
  compute/campaign686/test_three_bucket_zero_exclusion_repair_hostile_verify.py
0dffe6ee10a5948ab92471cad5dce45e442477e1295bcd7372304a06255a8fc5
  docs/plans/2026-07-10-erdos686-three-bucket-zero-exclusion-repair-hostile-audit.md
```

The fresh verifier imports neither producer verifier nor historical hostile
verifier.  It reconstructs each coefficient as a direct
elementary-symmetric subset sum.

## 2. Repaired public surface

The source exports sixteen public declarations: eight definitions and eight
theorem/lemma declarations.  The fresh Lean audit independently reproves all
eight theorem/lemma statements.

| Public theorem or lemma | Boundary | Fresh verdict |
|---|---|---|
| `target_three_bucket_zero_table_certificate` | Boolean rows `5,7,9,11,13,15`; ordinary `decide` | PASS |
| `target_three_bucket_zero_coefficient_certificate` | target row; three positive, pairwise-distinct owners | PASS |
| `three_bucket_zero_target_numeric_cutoff` | rounded `10^30`, `10^18`, and loss `18914575680` | PASS |
| `three_bucket_zero_gap_lt_cutoff_of_target_coefficients` | coprime packing; positive coefficients and `g`; exact divisibilities | PASS |
| `targetThreeBucketSecondObstruction_swap` | arbitrary naturals; left/right symmetry | PASS |
| `targetThreeBucketThirdObstruction_swap` | arbitrary naturals; left/right symmetry | PASS |
| `target_three_bucket_designated_zero_gap_lt` | one designated zero; target row and cyclic divisibilities | PASS |
| `target_three_bucket_all_second_obstructions_nonzero` | all three component divisibilities and `d>=10^120` | PASS |

The table certificate uses ordinary kernel `decide`, not `native_decide`.
The table definitions are computable; the definitions involving
`localThirdQuadratic` are correctly marked `noncomputable`.

## 3. Dependency tree

```text
assume designated O_l=0
|
+- R1 target-row coefficient certificate
|  +- 0<|A_i|,|A_j|<10^30
|  `- 0<|K_l|<10^18
|
+- R2 signed cross elimination
|  +- P | A_i*g^2
|  `- Q | A_j*g^2
|
+- R3 third-order conversion
|  `- R^2 | K_l*g^2*d
|
+- R4 pairwise-coprime packing
|  `- d | |A_i|*|A_j|*|K_l|*g^4
|
+- R5 numeric cutoff
|  `- product majorant <10^120
|
`- d<10^120

cycle the designated owner through i,j,l
`- if d>=10^120, O_i,O_j,O_l are all nonzero
```

Every arrow above was checked twice: by independent exact arithmetic and by
a separately named Lean proof that does not invoke the corresponding
producer theorem.

## 4. Six-row finite reconstruction

The repair verifier checks every ordered triple of distinct owners.

| `k` | triples | max `|A|` and case `(owner,zero,other)` | max `|K|` and case |
|---:|---:|---:|---:|
| 5 | 60 | `691200`, `(1,5,2)` | `75600`, `(1,5,2)` |
| 7 | 210 | `1646023680`, `(1,7,2)` | `8769600`, `(1,7,2)` |
| 9 | 504 | `10180055531520`, `(1,9,2)` | `1190689920`, `(1,9,2)` |
| 11 | 990 | `138849151795200000`, `(1,11,2)` | `206607931200`, `(1,11,2)` |
| 13 | 1716 | `3691052156423503872000`, `(1,13,2)` | `45893854955520`, `(1,13,2)` |
| 15 | 2730 | `174368230097267947732992000`, `(1,15,2)` | `12847056696714240`, `(1,15,2)` |

Totals:

```text
ordered distinct triples:          6210
zero cross coefficients:              0
zero third coefficients:              0
cross identity checks:              6210
third identity checks:              6210
second swap checks:                 6210
third swap checks:                  6210
cyclic designated-zero views:      18630
```

These maxima exactly match the producer verifier and remain strictly below
the rounded bounds.

## 5. Exact cutoff

The rounded majorant is

```text
(10^30)^2 * 10^18 * 18914575680^4
=127993057016846539654048809041799413760000000000000000000000000000000000000000000000000000000000000000000000000000000000
<10^120.
```

The integer cutoff quotient is `7`.  Both producer and audit Lean modules
kernel-check the strict inequality with `norm_num`.

## 6. Hostile boundary mutations

- **Distinct owners are load-bearing.**  At
  `(k,owner,zero,other)=(5,1,1,2)`, both the cross and third coefficients are
  exactly zero.  The coefficient theorem explicitly excludes this collision.
- **The row list is load-bearing for the chosen ceilings.**  At `k=17`, the
  maxima are `13639297797732100754689228800000` and
  `4449264976963584000`, exceeding `10^30` and `10^18` respectively.
- **Pairwise coprimality is load-bearing for packing.**  If
  `(P,Q,R,g,A,B,K)=(4,4,1,2,1,1,1)`, every displayed divisibility premise
  holds but `d=32` does not divide `A*B*K*g^4=16`.
- **The fourth power of `g` cannot be replaced by a cube.**  For
  `(P,Q,R,g,A,B,K)=(2,5,27,3,2,5,1)`, `d=810` divides the fourth-power
  product exactly and does not divide the cube product `270`.
- **No cancellation against shared `g` is used.**  Components `(2,3,5)`
  with `g=30` share all three small primes with `g`; the valid theorem does
  not assume otherwise.
- **Unit components are within the theorem surface.**  Positivity means
  `P,Q,R>=1`, not `>1`.  The packing algebra remains valid.
- **The large-gap hypothesis is essential to the final contradiction.**
  Exact `d=1` telescopes occur at `(k,n)=(9,2)` and `(15,4)` and lie outside
  `10^120<=d`.

No mutation is silently promoted into the theorem's scope.

## 7. Repair of the historical compiler failures

The fresh source build succeeds.  In particular:

- third-coefficient definitions depending on noncomputable data are marked
  `noncomputable`;
- the exhaustive proof uses a compact computable table Boolean and ordinary
  `decide`, avoiding the historical heartbeat failure;
- the swapped zero obstruction is proved by an explicit delta equality;
- the third obstruction is unfolded and rewritten at the correct surface;
- every formerly missing producer declaration is exported and importable.

The compiler emits only six `unnecessarySeqFocus` linter warnings.  There are
no unsolved goals, timeouts, missing object files, unknown constants, or
self-named recovery axioms.

## 8. Axiom and forbidden-construct gate

The repair audit prints axioms for all eight producer theorem/lemma
declarations and all eight independently re-proved audit declarations.
Every result is contained in

```text
[propext, Classical.choice, Quot.sound].
```

The ordinary Boolean table certificate needs only `[propext]`.

Source scans find no `native_decide`, `sorry`, `admit`, `of_decide`,
`unsafe`, `implemented_by`, `extern`, or custom `axiom` declaration.

## 9. Exact scope and integration verdict

It is safe to integrate the repaired module as this conditional theorem:

> In a target row with three distinct cleaned owners, positive pairwise
> coprime components `P,Q,R`, `d=gPQR>=10^120`, bounded positive `g`, and the
> six stated second/third obstruction divisibilities, all three composed
> second obstructions are nonzero.

The wrapper assumes the three-owner factorization and all six divisibilities;
it does not derive them from the original block equation.  It does not close
the remaining nonzero short-window/CRT lemma, the exactly-three-owner slice,
the four-or-more-owner slice, or Erdős #686.  Integration is therefore safe
only with this partial-result label.

No import, manifest, root documentation, attestation, or commit is changed by
this audit.

## 10. Frozen reproduction

```bash
lake env lean ErdosProblems/Erdos686ThreeBucketZeroExclusion.lean
lake env lean ErdosProblems/Erdos686ThreeBucketZeroExclusionRepairAudit.lean

python3 -m pytest \
  compute/campaign686/test_three_bucket_zero_exclusion_verify.py \
  compute/campaign686/test_three_bucket_zero_exclusion_hostile_verify.py \
  compute/campaign686/test_three_bucket_zero_exclusion_repair_hostile_verify.py -q

python3 compute/campaign686/three_bucket_zero_exclusion_repair_hostile_verify.py \
  --pretty
```

Frozen expected results:

```text
producer arithmetic:          2 passed
historical hostile evidence:  5 passed
fresh repair hostile suite:   8 passed
repaired producer Lean:       PASS
fresh independent Lean audit: PASS
```
