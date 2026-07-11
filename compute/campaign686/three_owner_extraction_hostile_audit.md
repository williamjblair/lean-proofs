# Hostile audit: Erdős 686 three-owner extraction

Verdict: **PASS for the exact extraction and equation-level wrapper.**  This
is a bookkeeping partial theorem, not a proof of Erdős 686 Target 1 and not a
three-bucket factorization of the entire gap.

## Frozen producer hashes

The five hashes were recorded before inspection and reproduced unchanged
after every audit artifact and test was created:

```text
6d056218c2d98025bdfc3a54741df01c3b35b78084d5a6d6dbcc5e1901e86b07
  ErdosProblems/Erdos686ThreeOwnerExtraction.lean
68d6518e49f005424ee1cd17bfe51d5dc09c3bee03fad17781b7bccfcee964ad
  compute/campaign686/three_owner_extraction_verify.py
124da19540d2120773af9941f521a5b3c8b4c4f32b099b83bafd14a72052d8c2
  compute/campaign686/test_three_owner_extraction_verify.py
4958de17f98b308d9de9c542b28c61cd6bee75478d5ed6e5f147df2efc4f076d
  compute/campaign686/three_owner_extraction_findings.md
4dd81a1ee3743b76891306db414fa98ba2b1a566f8c8c42ed36f20066e9c8e8b
  docs/plans/2026-07-10-erdos686-three-owner-extraction.md
```

## Audit-only artifacts

```text
1092c2eec28133295f9a45f34904fd9a093ea4b7b60125a7df7bc290e81df482
  ErdosProblems/Erdos686ThreeOwnerExtractionHostileAudit.lean
5a94c7e48b9c12a540fb363384f1d57ac8fb2e7f24fe51d5483f058da31f5d65
  compute/campaign686/three_owner_extraction_hostile_verify.py
54787126272c83434cb8e365483ef368e433f5fb5347a2bfe40fd10d5b27d729
  compute/campaign686/test_three_owner_extraction_hostile_verify.py
baeaa0bf75af182e66e7729d3d6deea26f1e5aa628f9b772faa2ce28a3986f48
  docs/plans/2026-07-10-erdos686-three-owner-extraction-hostile-audit.md
```

No producer, shared import, manifest, root audit, frontier, registry, or
attestation file was modified.

## Exact public surface

The producer exposes one structure and two theorems.

`ThreeGlobalResidualOwnerWitness k n d owner` is a `Type`, not a `Prop`.  Its
24 fields are:

```text
p, q, r;
three memberships in d.primeFactors;
three nonzero cleaned-exponent facts;
three owner-in-[1,k] facts;
three pairwise owner inequalities;
three cleaned-power divisibilities into n+owner;
three cleaned-square divisibilities into localResidual;
three pairwise coprimality facts for the cleaned powers.
```

The first theorem has the exact surface

```text
1 <= k
-> GlobalResidualOwnerAssignment k n d owner
-> (forall i j, not GlobalResidualOwnerRangeAtMostTwo k d owner i j)
-> Nonempty (ThreeGlobalResidualOwnerWitness k n d owner).
```

The second theorem has the exact surface

```text
k in {5,7,9,11,13,15}
-> blockProduct k (n+d) = 4*blockProduct k n
-> n+1 < C*d
-> A = 3*C+2
-> A <= 35
-> 10^120 <= d
-> exists owner,
     GlobalResidualOwnerAssignment k n d owner
     and Nonempty (ThreeGlobalResidualOwnerWitness k n d owner).
```

The wrapper therefore supplies one assignment and one proof-level nonempty
witness type inside that same assignment.  It does not quantify a unique
assignment or witness.

## Independent combinatorial reconstruction

On the prime-factor support, call an entry live exactly when its cleaned
exponent is nonzero.  The hostile Lean theorem reconstructs the implication

```text
not(exists i,j covering every live value)
-> exists p,q,r in the support,
     p,q,r live and value(p),value(q),value(r) pairwise distinct.
```

The proof uses the same necessary nonempty-value input as the producer, made
explicit as an abstract `anchor`; the producer obtains it from `1<=k` and
uses owner `1`.

The independent Python verifier does not import the producer verifier.  It
exhausts owner universes of sizes 1 through 6 and support lengths 0 through
6.  Exact totals are:

```text
4,729,716 finite assignments,
2,075,220 no-two-cover assignments,
2,075,220 assignments with three distinct live values,
0 equivalence mismatches.
```

An independent inclusion-exclusion formula gives the same count.  Counts by
number of distinct live values are:

```text
0:   82,206
1:  741,336
2: 1,830,954
3: 1,562,436
4:  469,104
5:   42,960
6:      720
```

The producer verifier independently reports 224,694 reduced-alphabet models
and 51,696 successful extractions.  Both producer tests and all seven hostile
tests pass together.

## Dependency tree

```text
exists_threeGlobalResidualOwnerWitness_of_target_size_solution
|- exists_globalResidualOwnerAssignment_not_two_cover
|  |- exact target-row equation and window hypotheses
|  `- one assignment with no valid two-index cover
`- threeGlobalResidualOwnerWitness_of_not_two_cover
   |- choose first live prime p, else cover by (1,1)
   |- choose live q at a distinct owner, else cover by (owner p,owner p)
   |- choose live r outside both owners, else cover by (owner p,owner q)
   |- assignment projections give the three factor and square divisibilities
   |- primeFactors membership gives primality
   |- owner inequality gives p,q,r pairwise distinct
   `- distinct prime powers are pairwise coprime
```

No private analytic, computational, or theorem-strength lemma is hidden in
this tree.

## Per-node verdicts

- First live witness: **PASS.**  Empty live support gives the valid cover
  `(1,1)` because `1<=k`.
- Second distinct live value: **PASS.**  If every live entry has owner
  `owner p`, the coincident cover `(owner p,owner p)` is valid.
- Third distinct live value: **PASS.**  If every live entry has owner
  `owner p` or `owner q`, those two in-range values form a valid cover.
- Support and liveness: **PASS.**  All three witnesses lie in
  `d.primeFactors` and have explicitly nonzero cleaned exponents.
- Owner range and distinctness: **PASS.**  All three owners lie in `[1,k]`
  and are pairwise unequal.
- Underlying prime distinctness: **PASS.**  Equal primes would have equal
  values under the same total owner function, contradicting owner
  distinctness.  The hostile Lean audit proves all three prime inequalities.
- Factor/square retention: **PASS.**  The theorem projects both facts directly
  from the same `GlobalResidualOwnerAssignment`; no owner is switched.
- Coprimality: **PASS.**  `primeFactors` membership supplies primality and
  distinct primes have coprime powers.  Bases 2 and 3 are not canceled or
  excluded.
- Equation-level composition: **PASS.**  The wrapper passes all six exact
  hypotheses unchanged to the banked no-two-cover theorem, derives `1<=k`
  from the six-row disjunction, and applies the extraction theorem.
- Theorem strength: **PASS.**  The return is `Nonempty` in an explicit witness
  type.  There is no claim that all live values are among the selected three,
  that exactly three owners exist, or that `d=gPQR`.

## Boundary audit

- Empty support and zero live values: covered by `(1,1)`; no extraction.
- Exactly one live owner value: covered with `i=j`.
- Exactly two live owner values: covered by those two values.
- Exactly three live owner values: no two-cover and extraction succeeds.
- Four or more live values: extraction returns three but leaves all further
  live values untouched.  Two kernel-checked `Fin 4` countermodels show that
  four values have neither a two-value nor a three-value cover.
- Zero-clean entry outside the selected cover: ignored by the leading
  zero-exponent disjunct, exactly as intended.
- Total-function values away from `d.primeFactors`: irrelevant because every
  quantified assignment and cover condition is restricted to that support.
- Repeated primes or entries at one owner: do not create additional live
  values.
- Endpoints `1` and `k`: included; the proof uses only membership in
  `Finset.Icc 1 k`.
- Prime bases 2 and 3: included without a unit or cancellation assumption.
- `k=0`: excluded by `1<=k` in the abstract theorem.
- `d=0`: the no-cover premise cannot supply live prime-factor support; the
  theorem is implication-safe.  The equation wrapper has `d>=10^120`.
- The `d=1` telescopes at rows 9 and 15 are outside the equation wrapper's
  target-size hypothesis.

## Kernel and source gates

- Direct producer compilation: **PASS**.
- Direct hostile-audit compilation: **PASS**.
- Joint module build: **PASS**, 8,260 jobs.
- Producer and hostile tests: **PASS**, 9 total.
- Independent Python byte compilation: **PASS**.
- Comment-aware scan of both Lean files finds no executable `sorry`, `admit`,
  `native_decide`, `axiom`, or `unsafe` declaration.
- Both producer theorems and the four non-finite audit bridge theorems use
  only `[propext, Classical.choice, Quot.sound]`.
- The two finite `Fin 4` boundary theorems use no axioms.
- All five producer hashes remain unchanged.

## Scope retained after PASS

The audited result proves that every target-size solution has at least three
distinct nontrivial cleaned owner values in one certified assignment.  It
does not prove that there are only three, does not group every remaining live
component, does not produce `d=gPQR` in the presence of further owners, and
does not close the three-bucket short-window or four-or-more-owner branches.

## Reproduction

```bash
python3 compute/campaign686/three_owner_extraction_hostile_verify.py --pretty
python3 -m pytest compute/campaign686/test_three_owner_extraction_verify.py \
  compute/campaign686/test_three_owner_extraction_hostile_verify.py -q
python3 -m py_compile \
  compute/campaign686/three_owner_extraction_verify.py \
  compute/campaign686/test_three_owner_extraction_verify.py \
  compute/campaign686/three_owner_extraction_hostile_verify.py \
  compute/campaign686/test_three_owner_extraction_hostile_verify.py
lake env lean ErdosProblems/Erdos686ThreeOwnerExtraction.lean
lake env lean ErdosProblems/Erdos686ThreeOwnerExtractionHostileAudit.lean
lake build ErdosProblems.Erdos686ThreeOwnerExtraction \
  ErdosProblems.Erdos686ThreeOwnerExtractionHostileAudit
```
