# Erdős 699 T7 Row-Bound Factor-Square Wrapper Plan

## Goal

Remove one normalized side condition from the current T7 factor-square wrappers.
The existing theorems require `2 * t <= X`; the original row hypotheses give
`2 * j <= n` with `n = F * X` and `j = F * t`. This milestone proves the
normalization step once, then packages row-bound versions of both current
branch-free wrappers.

## Rigor Tags

- [R] Lean-only target; no mathematical claim is complete until
  `lake env lean lean/Erdos699/Proved/Basic.lean` and the WIP API check pass.
- [OPEN] This does not prove full T7. It only replaces the normalized half-row
  side condition with the original row bound in already conditional wrappers.

## Implementation Steps

1. Add a WIP check for the expected theorem names:
   - `Erdos699.two_mul_t_le_X_of_factorized_half_bound`
   - `Erdos699.i_three_caseI_factor_sq_squeeze_of_half_bound_from_row_bound`
   - `Erdos699.i_three_caseI_factor_sq_squeeze_of_half_coprime_four_from_row_bound`
2. Prove `two_mul_t_le_X_of_factorized_half_bound` by cancelling the positive
   factor `F` from `2 * (F * t) <= F * X`. Derive `0 < F` from `0 < j` and
   `j = F * t`.
3. Wrap `i_three_caseI_factor_sq_squeeze_of_half_bound` with the helper.
4. Wrap `i_three_caseI_factor_sq_squeeze_of_half_coprime_four` with the helper.
5. Update `notes/PROGRESS.md` with a precise [R] entry and run the verification
   gate before committing.

## Verification

- `lake env lean lean/Erdos699/Proved/Basic.lean`
- `lake build Erdos699.Proved.Basic`
- `lake env lean lean/Erdos699/WIP/RowBoundFactorSquareCheck.lean`
- `python3 -m pytest compute/tests/test_criterion.py -q`
- `rg -n "sorry|admit" lean/Erdos699/Proved`
- `git diff --check`
- `lake build`
- `bash scripts/check_manifest.sh && bash scripts/check_axioms.sh`
- `#print axioms Erdos699.i_three_caseI_factor_sq_squeeze_of_half_coprime_four_from_row_bound`
