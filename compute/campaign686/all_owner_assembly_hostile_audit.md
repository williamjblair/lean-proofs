# Hostile audit: Erdős 686 AllOwnerAssembly

Verdict: **PASS as a complete compositional bridge.** Every one of the 30
public theorem surfaces was independently re-proved in Lean. The exact
arithmetic, full-grid transport, local lifts, composed divisibilities, target
zero exclusion, certificate constructor, and existential wrapper are safe to
integrate.

This package does **not** prove the remaining nonzero-obstruction branch, the
large-gap contradiction, or Erdős #686.

## 1. Frozen producer boundary

The producer supplied four hashes. All four reproduced exactly:

```text
a63011061fc8af531036374a238ae776ef861f3d21df937def40f156b50c88bf
  ErdosProblems/Erdos686AllOwnerAssembly.lean
29ea556f2cca67366243c283f8fbce85f18358eb157e22d221cf6d8d45b1860b
  compute/campaign686/all_owner_assembly_verify.py
57170689925795ca7315f2127135aa736aa1ee619811745f09b10026327386f8
  compute/campaign686/test_all_owner_assembly_verify.py
b87e233a080aeaf55295f2f980f80831d03734e2bf33a6f76a5c55befd5ea3a3
  docs/plans/2026-07-10-erdos686-all-owner-assembly.md
```

The handoff omitted the findings digest. This is a procedural audit defect.
The auditor froze the existing file before reading or testing it:

```text
1610f635ecdf37f8c192fbd7f4866d33d6089602f1599fced1f178be3497b3d9
  compute/campaign686/all_owner_assembly_findings.md
```

All five producer artifacts remained byte-identical through the final gate.

Fresh hostile artifacts, excluding this self-referential report:

```text
65b26b9c6ccc8983e40069f9233ee7036098642a7b718a251346ead81e428b3d
  ErdosProblems/Erdos686AllOwnerAssemblyHostileAudit.lean
0fa1a67cf2d50eff36d6cdaaee4b7faa3d378fc1d92f4803c0a32a26efe1037c
  compute/campaign686/all_owner_assembly_hostile_verify.py
a87d155c26e2398d3dc41c18a43aa4559bbd04b956a996ff1980784ba03bbdb9
  compute/campaign686/test_all_owner_assembly_hostile_verify.py
eab9eb8df595d98b7f9df8abd37eb360bb68b7d806c1dfaa5a9ed2bf8c53669c
  docs/plans/2026-07-10-erdos686-all-owner-assembly-hostile-audit.md
```

The hostile Python verifier imports no producer verifier code. Its Taylor
coefficients are reconstructed as elementary-symmetric subset sums, not by
the producer's iterative affine convolution.

## 2. Dependency tree

```text
exists_allOwnerAssemblyCertificate                              PASS
|- certified assignment exists                                 PASS upstream
|- full grid S = Icc 1 k                                       PASS
|- each retained prime power occurs at owner(p) exactly once    PASS
|- prime/owner product commutation                              PASS
|- d = g * product_{i in S} P_i                                PASS
|- P_i > 0 and g > 0                                           PASS
|- P_i | n+i and P_i^2 | localResidual_i                       PASS upstream
|- localResidual_i = a_i P_i^2 and a_i > 0                     PASS
|- signed residual difference = 3(i-j)                         PASS
|- d = P_i * (g * product_{j!=i} P_j)                          PASS
|- local second and third Taylor lifts                         PASS
|- injective Nat-to-Int full and erased product transport       PASS
|- P_i | O_i and P_i^2 | F_i for every grid index              PASS
|- target range, C_i != 0, |D_i| < 10^12                       PASS
|- localResidual_i > 5d                                        PASS
|- O_i != 0 at d >= 10^120                                     PASS
`- joint contradiction from the nonzero O_i and F_i             OPEN
```

No owner subset is selected in this tree. Every cleaned prime power is placed
on the literal grid `Icc 1 k`; multiple prime powers assigned to the same
index multiply in that bucket. Consequently no fourth or later live owner is
absorbed into a replacement loss.

## 3. Public theorem audit

The producer exposes six arithmetic/interface definitions, one certificate
structure, one certificate constructor, and 30 public theorems. The hostile
Lean module restates the 30 theorem conclusions under fresh names and proves
them without invoking the corresponding producer theorem.

| Producer theorem | Independently audited content | Verdict |
|---|---|---|
| `allOwnerBucket_pos` | every finite-product bucket, including an empty bucket, is positive | PASS |
| `allOwnerLoss_pos` | unchanged grouped loss is positive | PASS |
| `allOwnerBucket_dvd_factor` | bucket divides its assigned factor | PASS |
| `allOwnerBucket_square_dvd_residual` | bucket square divides the local residual | PASS |
| `allOwner_residual_decomposition` | exact natural quotient reconstruction | PASS |
| `allOwner_one_prime_placement` | retained power occurs at exactly its certified grid owner | PASS |
| `allOwner_bucket_product_eq_clean_product` | owner/prime product swap | PASS |
| `allOwner_gap_decomposition` | exact unchanged-loss factorization of `d` | PASS |
| `allOwner_gap_decomposition_at` | exact erased-product quotient at one owner | PASS |
| `allOwner_residual_cast` | natural subtraction casts only after positivity | PASS |
| `allOwnerCofactor_pos` | exact cofactor is positive | PASS |
| `allOwner_residual_difference` | signed step-three progression | PASS |
| `allOwner_residual_pos` | block equation and `5<=k<=d` imply positivity | PASS |
| `allOwner_second_local_lift` | local second lift with unchanged opposite product | PASS |
| `allOwner_third_local_lift` | local third lift with unchanged opposite product | PASS |
| `allOwner_natCast_mem_intGrid` | natural grid membership maps to the integer grid | PASS |
| `allOwnerIntGrid_card` | image cardinality is exactly `k` | PASS |
| `allOwnerIntGrid_exists_nat` | every integer-grid element has a natural preimage | PASS |
| `allOwnerIntGrid_prod_bucket` | full product commutes with the cast image | PASS |
| `allOwnerIntGrid_erase_prod_bucket` | erased product commutes with the cast image | PASS |
| `allOwnerIntGrid_opposite_component` | generic opposite component equals the cast erased product | PASS |
| `allOwnerIntGrid_gap_decomposition` | exact gap factorization on the integer interface | PASS |
| `allOwnerIntGrid_residual_difference` | signed progression on the integer interface | PASS |
| `allOwner_second_obstruction_dvd` | every bucket divides its composed second obstruction | PASS |
| `allOwner_third_obstruction_dvd_sq` | every bucket square divides its composed third obstruction | PASS |
| `allOwnerIntGrid_target_range` | all target indices lie in `[1,15]` | PASS |
| `allOwner_localSecondConstant_ne_zero` | structural factorial proof of `C_i != 0` | PASS |
| `allOwnerIntGrid_residual_gt_five_gap` | every reconstructed residual exceeds `5d` | PASS |
| `allOwner_second_obstruction_ne_zero` | target-scale generic zero exclusion at every grid index | PASS |
| `exists_allOwnerAssemblyCertificate` | equation-level certificate existence | PASS |

The hostile module also independently rebuilds
`allOwnerAssemblyCertificate_of_assignment`, filling all eleven certificate
fields from the fresh lemmas.

## 4. Exact arithmetic reproduction

Across `k in {5,7,9,11,13,15}`, all `1<=d<=500`, and five deterministic
assignments per factorization:

```text
gap/assignment fixtures:       15000
prime placements checked:      30240
zero-clean components:          15430
empty buckets:                 136028
```

Every loss and bucket was positive. Every retained prime appeared in exactly
one bucket. Every empty bucket was exactly one. Every fixture satisfied

```text
d = loss * product(all k buckets).
```

The exact boundary counts reproduce the producer:

```text
fixtures containing base 2:                 7500
fixtures containing base 3:                 4980
fixtures containing a prime at least k:     11950
fixtures using owner 1:                      9829
fixtures using owner k:                      5728
nonempty all-primes-one-owner fixtures:      5988
d=1 rows:                                       6
```

For every `d=1` row, the loss and every bucket are one. A separate `k=15`
fixture places fifteen independently retained prime powers at all fifteen
owners and verifies exact reconstruction, so the no-absorption claim is not
inferred from a three-owner sample.

Six full-grid CRT progressions check all 60 target owner congruences. Five
additional hostile families check 29 owner congruences with unit components,
row centers, endpoints, bases 2 and 3, permuted and negative components,
negative loss, and zero loss. All exact quotient reconstructions, pairwise
residual differences, second compositions, and third compositions pass.
These are algebra fixtures, not block-equation solutions.

## 5. Target coefficient and size audit

All 60 target owner rows were reconstructed independently:

```text
max |C_i| =  87178291200
max |D_i| = 283465647360 < 10^12
```

Every `C_i` is nonzero. The only zero linear coefficients are exactly the six
odd-row centers:

```text
(5,3), (7,4), (9,5), (11,6), (13,7), (15,8).
```

The generic zero-exclusion constant is reproduced exactly:

```text
4 * 10^12 * 3^14 * 15^14 + 1
= 558515440794946289062500000000000001
< 625 * (10^120)^2.
```

The lower-product argument uses the cardinality of the full residual grid,
not the number of nonunit buckets. This is sound: an empty bucket is `P_i=1`,
but its exact cofactor is the full positive residual and still satisfies
`5d<a_i P_i^2`. It must not be described as a fourth nontrivial cleaned
owner.

## 6. Boundary and scope audit

- **Empty buckets:** PASS. They are literal units. Their divisibilities are
  tautological, while their residual, cofactor, and nonzero obstruction facts
  remain substantive.
- **Centers:** PASS. `D_i=0` is allowed; `C_i!=0` is the load-bearing
  hypothesis in the zero exclusion.
- **Endpoints and `k=5,15`:** PASS. No proof assumes an interior owner.
- **Bases 2 and 3:** PASS. The special base-3 loss exponent is preserved; the
  ordinary-prime rule is not substituted for it.
- **`d=1`:** PASS for the arithmetic layer. The target certificate correctly
  retains the separate guard `10^120<=d`.
- **Positivity and casts:** PASS. Natural subtraction is cast only after the
  residual positivity proof. No signed identity is obtained from truncated
  subtraction.
- **Further owners:** PASS. The full product includes every grid index, and a
  fifteen-live-owner fixture confirms there is no hidden selected subset.
- **No false closure:** PASS. A 122-digit component can divide an arbitrarily
  large nonzero obstruction. Thus `P_i|O_i` plus `O_i!=0` has no standalone
  archimedean consequence.

Two prose qualifications should be retained during integration:

1. The docstring for `allOwnerIntGrid_exists_nat` says "unique," while its
   theorem statement asserts existence only. Uniqueness follows separately
   from injectivity of `Int.ofNat`, but it is not part of that theorem surface.
2. `AllOwnerAssemblyCertificate` has no below-cutoff or contradiction field
   and does not store the block equation itself. The public constructor and
   existence theorem use the block equation to build the recorded
   consequences. The structure alone must not be advertised as a complete
   contradiction certificate.

Neither qualification invalidates a theorem or a downstream use in the
producer.

## 7. Exact remaining lemma

The package stops at the single target-strength lemma stated by the producer:

```text
allOwnerCertificate_below_cutoff:
  forall k n d,
    (k=5 or k=7 or k=9 or k=11 or k=13 or k=15) ->
    blockProduct k (n+d) = 4 * blockProduct k n ->
    AllOwnerAssemblyCertificate k n d ->
    d < 10^120.
```

No proof of this lemma is present. Combined with certificate existence at
`d>=10^120`, it is equivalent in strength to closing the remaining large-gap
case. Renaming the needed joint use of the nonzero `O_i`, square-divisible
`F_i`, and short residual window would not be progress.

## 8. Kernel, test, and non-mutation gates

```text
producer tests + hostile tests:       15 passed
Python byte compilation:              PASS
producer direct Lean:                 PASS
hostile direct Lean:                  PASS
focused lake build:                   8262 jobs, PASS
producer theorem surfaces:            30
fresh hostile theorem surfaces:       30
fresh hostile constructor:             1
```

Every producer theorem, hostile theorem, and hostile constructor stays within

```text
[propext, Classical.choice, Quot.sound].
```

The producer and hostile Lean files contain no `native_decide`, `sorry`,
`admit`, custom axiom, or unsafe declaration. `git diff --check` passes.
Linter messages are pre-existing style advice or the same non-material
flexible-tactic advice on the independently repeated cast seams.

Reproduction:

```bash
python3 -m pytest \
  compute/campaign686/test_all_owner_assembly_verify.py \
  compute/campaign686/test_all_owner_assembly_hostile_verify.py -q

python3 -m py_compile \
  compute/campaign686/all_owner_assembly_verify.py \
  compute/campaign686/all_owner_assembly_hostile_verify.py \
  compute/campaign686/test_all_owner_assembly_verify.py \
  compute/campaign686/test_all_owner_assembly_hostile_verify.py

lake env lean ErdosProblems/Erdos686AllOwnerAssembly.lean
lake env lean ErdosProblems/Erdos686AllOwnerAssemblyHostileAudit.lean
lake build ErdosProblems.Erdos686AllOwnerAssembly \
  ErdosProblems.Erdos686AllOwnerAssemblyHostileAudit
```

The hostile audit did not edit a producer file, shared import, root audit,
frontier/progress document, manifest, registry, attestation, or commit.
