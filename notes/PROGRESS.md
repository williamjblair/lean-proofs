# Erdős #699 Progress

## 2026-07-05

- [E] Added exact Python tests for the corrected counterexample criterion. The
  tests explicitly check that primes below `i` are free in the obstruction set.
  Reproduce with: `python3 -m pytest compute/tests/test_criterion.py -q`.
- [R] Added Lean definitions `Erdos699.digit`, `Erdos699.dominated`, and
  `Erdos699.relevantPrime`, plus theorem
  `Erdos699.relevantPrime_ignores_small`. Reproduce with:
  `lake build Erdos699`.
- [R] Proved `Erdos699.dominated_iff_forall_mem_range`,
  `Erdos699.dominated_iff_forall_digits`, and
  `Erdos699.lucas_nonzero_mod_prime_iff_dominated`, giving the first
  sorry-free Lucas bridge for the decidable digit-domination predicate.
- [OPEN] T1, T2, T3, and all later rungs remain unclaimed in this branch.
