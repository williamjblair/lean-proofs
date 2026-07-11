# Erdős 686 explicit three-owner extraction

Status: **producer proof complete; independent hostile audit pending.**

The banked grouping theorem gives one assignment `owner` with

```text
forall i j, not GlobalResidualOwnerRangeAtMostTwo k d owner i j.
```

`Erdos686ThreeOwnerExtraction.lean` converts this negative cover statement
into three explicit prime divisors `p,q,r` whose cleaned exponents are
nonzero and whose owners are pairwise distinct.  It retains, for all three
components, the assignment's factor divisibility and square-residual
divisibility, and proves the three cleaned powers pairwise coprime.

The equation-level wrapper composes the extraction with
`exists_globalResidualOwnerAssignment_not_two_cover`.  Thus every target-size
solution supplies one assignment and a three-owner witness inside that same
assignment.

The proof is elementary but its scope matters:

- zero-clean components are ignored exactly as in the two-cover predicate;
- the three primes are distinct because their owner values are distinct;
- no claim says that only three owner values occur;
- the result does not construct a factorization `d=gPQR` when further live
  owner buckets exist.

The exact verifier exhausts finite owner/clean models in all six target rows
and checks that no two-index cover is equivalent to at least three live owner
values, including empty support, one/two-owner, zero-clean-outside-cover, and
four-owner fixtures.

Reproduce with:

```bash
lake build ErdosProblems.Erdos686ThreeOwnerExtraction
python3 compute/campaign686/three_owner_extraction_verify.py --pretty
python3 -m pytest compute/campaign686/test_three_owner_extraction_verify.py -q
```
