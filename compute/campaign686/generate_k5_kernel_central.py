#!/usr/bin/env python3
"""Emit the five-section kernel endpoint for the central k=5 puncture."""

from __future__ import annotations

import argparse
from pathlib import Path

import sympy as sp

from generate_k5_kernel_puncture import (
    LEAN_HEADER,
    elimination_difference,
    namespace,
    write_certificate_modules,
    write_elimination_modules,
)
from generate_k5_noncommon_certificate import (
    cleared_elimination_cofactors,
    cleared_multi_univariate_bezout,
    lean_int,
    lean_row,
    lean_rows,
    low_coefficients,
    resultant_poly,
    section_rows,
    sympy_section,
)
from generate_k5_puncture_certificate import emit as emit_certificate
from jet_puncture_base_locus_experiment import (
    exact_curve_section_resultant,
    exact_section_coefficients,
)
from jet_puncture_basis_experiment import construct


PREFIX = "k5P33"
MODULE_PREFIX = "Erdos686K5P33"
SECTION_COUNT = 5


def dense_add_all(terms: list[str]) -> str:
    assert terms
    if len(terms) == 1:
        return terms[0]
    return f"denseIntAdd {terms[0]} ({dense_add_all(terms[1:])})"


def compute_data() -> tuple[list[str], list[list[list[int]]]]:
    result = construct(
        5, 3, 3, 1,
        basis_mode="lagrange",
        emit_standard_basis=True,
    )
    basis = result["standard_basis"]
    assert isinstance(basis, list)
    selected = basis[:SECTION_COUNT]
    r = int(result["r"])
    x, y = sp.symbols("x y")
    block = lambda z: sp.prod(z + h for h in range(1, 6))
    curve = sp.expand(block(y) - 4 * block(x))
    curve_rows = [
        [-360, -1096, -900, -340, -60, -4],
        [274], [225], [85], [15], [1],
    ]
    section_dense = [section_rows(vector, 5, r) for vector in selected]
    section_exprs = [
        sympy_section(rows, x, y) for rows in section_dense
    ]
    resultants = [
        resultant_poly(
            exact_curve_section_resultant(
                exact_section_coefficients(vector, 5, r), 5
            ),
            x,
        )
        for vector in selected
    ]
    eliminations = [
        cleared_elimination_cofactors(section, curve, resultant, x, y)
        for section, resultant in zip(section_exprs, resultants)
    ]
    expected = sp.Poly(
        sp.prod(
            (x + h) ** (68 if h == 3 else 85)
            for h in range(1, 6)
        ),
        x,
        domain=sp.ZZ,
    )
    resultant_cofactors, target_scale = (
        cleared_multi_univariate_bezout(resultants, expected, x)
    )
    definitions = [
        f"def {PREFIX}CurveDense : DenseBivariateIntPolynomial :=\n"
        + lean_rows(curve_rows)
    ]
    for index in range(SECTION_COUNT):
        section_cofactor, curve_cofactor = eliminations[index]
        definitions.extend(
            [
                f"def {PREFIX}Section{index}Dense : "
                "DenseBivariateIntPolynomial :=\n"
                + lean_rows(section_dense[index]),
                f"def {PREFIX}SectionCofactor{index} : "
                "DenseBivariateIntPolynomial :=\n"
                + lean_rows(section_cofactor),
                f"def {PREFIX}CurveCofactor{index} : "
                "DenseBivariateIntPolynomial :=\n"
                + lean_rows(curve_cofactor),
                f"def {PREFIX}Resultant{index} : DenseIntPolynomial :=\n"
                + lean_row(low_coefficients(resultants[index], x)),
            ]
        )
    definitions.append(
        f"""def {PREFIX}Expected : DenseIntPolynomial :=
  denseIntMul (denseIntPow [1, 1] 85)
    (denseIntMul (denseIntPow [2, 1] 85)
      (denseIntMul (denseIntPow [3, 1] 68)
        (denseIntMul (denseIntPow [4, 1] 85)
          (denseIntPow [5, 1] 85))))"""
    )
    for index, cofactor in enumerate(resultant_cofactors):
        definitions.append(
            f"def {PREFIX}ResultantCofactor{index} : "
            "DenseIntPolynomial :=\n"
            + lean_row(cofactor)
        )
    definitions.append(
        f"def {PREFIX}BezoutScale : ℤ :=\n{lean_int(target_scale)}"
    )
    return definitions, eliminations


def write_noncommon_data(
    output_dir: Path, definitions: list[str]
) -> None:
    body = (
        "/-! Generated five-section non-common-zero certificate data. -/\n\n"
        "set_option maxRecDepth 100000\n"
        "set_option maxHeartbeats 0\n\n"
        + "\n\n".join(definitions)
        + "\n\n"
        + "\n\n".join(
            elimination_difference(PREFIX, index)
            for index in range(SECTION_COUNT)
        )
    )
    (output_dir / f"{MODULE_PREFIX}NoncommonData.lean").write_text(
        f"{LEAN_HEADER}\n"
        f"import ErdosProblems.{MODULE_PREFIX}Certificate\n"
        "import ErdosProblems.Erdos686DenseKernelCertificate\n\n"
        + namespace(body)
    )


def bezout_combination() -> str:
    terms = [
        f"(denseIntMul {PREFIX}ResultantCofactor{index} "
        f"{PREFIX}Resultant{index})"
        for index in range(SECTION_COUNT)
    ]
    return dense_add_all(terms)


def write_bezout(output_dir: Path) -> None:
    combination = bezout_combination()
    body = f"""set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem {PREFIX}ResultantBezoutIdentity :
    denseIntIsZero
      (denseIntSub
        ({combination})
        (denseIntScale {PREFIX}BezoutScale
          {PREFIX}Expected)) := by
  unfold denseIntIsZero
  decide +kernel"""
    (output_dir / f"{MODULE_PREFIX}BezoutKernel.lean").write_text(
        f"{LEAN_HEADER}\n"
        f"import ErdosProblems.{MODULE_PREFIX}NoncommonData\n\n"
        + namespace(body)
    )


def write_noncommon_main(output_dir: Path) -> None:
    pieces = [
        f"""set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem {PREFIX}CurveDense_toSparse :
    denseBivariateToSparse {PREFIX}CurveDense = k5CurveTerms := by
  decide +kernel"""
    ]
    for index in range(SECTION_COUNT):
        pieces.append(
            f"""theorem {PREFIX}Section{index}Dense_toSparse :
    denseBivariateToSparse {PREFIX}Section{index}Dense =
      {PREFIX}Section{index} := by
  decide +kernel

theorem {PREFIX}Resultant{index}_eval_eq_zero
    {{x y : ℤ}}
    (hsection :
      denseBivariateEval {PREFIX}Section{index}Dense x y = 0)
    (hcurve : denseBivariateEval {PREFIX}CurveDense x y = 0) :
    denseIntEval {PREFIX}Resultant{index} x = 0 := by
  have hresultantDense :=
    denseBivariate_elimination_eval_zero
      {PREFIX}EliminationIdentity{index} hsection hcurve
  simpa [denseBivariateEval] using hresultantDense

theorem {PREFIX}Section{index}Dense_eval_eq_sparse
    (n d : ℕ) :
    denseBivariateEval {PREFIX}Section{index}Dense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
      sparseBivariateEval {PREFIX}Section{index} n (n + d) := by
  calc
    denseBivariateEval {PREFIX}Section{index}Dense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
        sparseBivariateEval
          (denseBivariateToSparse {PREFIX}Section{index}Dense)
          n (n + d) :=
      (denseBivariateToSparse_eval _ _ _).symm
    _ = sparseBivariateEval {PREFIX}Section{index} n (n + d) := by
      rw [{PREFIX}Section{index}Dense_toSparse]"""
        )
    hypotheses = "\n".join(
        f"    (hresultant{index} : "
        f"denseIntEval {PREFIX}Resultant{index} x = 0)"
        for index in range(SECTION_COUNT)
    )
    simp_hypotheses = ", ".join(
        f"hresultant{index}" for index in range(SECTION_COUNT)
    )
    pieces.append(
        f"""theorem {PREFIX}Expected_scaled_eval_eq_zero
    {{x : ℤ}}
{hypotheses} :
    denseIntEval
      (denseIntScale {PREFIX}BezoutScale {PREFIX}Expected) x = 0 := by
  have hid :=
    denseInt_identity_eval {PREFIX}ResultantBezoutIdentity x
  simp only [denseIntAdd_eval, denseIntMul_eval,
    {simp_hypotheses}, mul_zero, zero_mul, add_zero, zero_add] at hid
  exact hid.symm

theorem {PREFIX}CurveDense_eval_eq_sparse
    (n d : ℕ) :
    denseBivariateEval {PREFIX}CurveDense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
      sparseBivariateEval k5CurveTerms n (n + d) := by
  calc
    denseBivariateEval {PREFIX}CurveDense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
        sparseBivariateEval
          (denseBivariateToSparse {PREFIX}CurveDense) n (n + d) :=
      (denseBivariateToSparse_eval _ _ _).symm
    _ = sparseBivariateEval k5CurveTerms n (n + d) := by
      rw [{PREFIX}CurveDense_toSparse]

theorem {PREFIX}Expected_eval_pos
    (n : ℕ) :
    0 < denseIntEval {PREFIX}Expected (n : ℤ) := by
  unfold {PREFIX}Expected
  rw [denseIntMul_eval, denseIntPow_eval,
    denseIntMul_eval, denseIntPow_eval,
    denseIntMul_eval, denseIntPow_eval,
    denseIntMul_eval, denseIntPow_eval,
    denseIntPow_eval]
  norm_num [denseIntEval]
  positivity

theorem {PREFIX}Expected_scaled_eval_ne_zero
    (n : ℕ) :
    denseIntEval
        (denseIntScale {PREFIX}BezoutScale {PREFIX}Expected)
        (n : ℤ) ≠ 0 := by
  rw [denseIntScale_eval]
  exact mul_ne_zero
    (by norm_num [{PREFIX}BezoutScale])
    (ne_of_gt ({PREFIX}Expected_eval_pos n))"""
    )
    imports = [
        f"import ErdosProblems.{MODULE_PREFIX}NoncommonData",
        *[
            f"import ErdosProblems.{MODULE_PREFIX}Elimination{index}Rows"
            for index in range(SECTION_COUNT)
        ],
        f"import ErdosProblems.{MODULE_PREFIX}BezoutKernel",
    ]
    (output_dir / f"{MODULE_PREFIX}Noncommon.lean").write_text(
        f"{LEAN_HEADER}\n" + "\n".join(imports) + "\n\n"
        + namespace(
            "/-! Kernel-checked five-section non-common-zero certificate. -/\n\n"
            + "\n\n".join(pieces)
        )
    )


def write_endpoint(output_dir: Path) -> None:
    disjunction = " ∨\n      ".join(
        f"sparseBivariateEval {PREFIX}Section{index} n (n + d) ≠ 0"
        for index in range(SECTION_COUNT)
    )
    section_zeros = []
    resultants = []
    for index in range(SECTION_COUNT):
        accessor = ".2" * index + ".1" if index < 4 else ".2" * 4
        section_zeros.append(
            f"""  have hsection{index} :
      denseBivariateEval {PREFIX}Section{index}Dense
          (n : ℤ) ((n + d : ℕ) : ℤ) = 0 := by
    rw [{PREFIX}Section{index}Dense_eval_eq_sparse]
    exact h{accessor}"""
        )
        resultants.append(
            f"""  have hresultant{index} :
      denseIntEval {PREFIX}Resultant{index} (n : ℤ) = 0 :=
    {PREFIX}Resultant{index}_eval_eq_zero hsection{index} hcurve"""
        )
    result_args = " ".join(
        f"hresultant{index}" for index in range(SECTION_COUNT)
    )
    witness_cases = []
    for index in range(SECTION_COUNT):
        witness_cases.append(
            f"""  · exact ⟨{{
      value :=
        (sparseBivariateEval {PREFIX}Section{index}
          n (n + d)).natAbs
      value_pos := Int.natAbs_pos.mpr hsection
      local_dvd :=
        {PREFIX}Section{index}_local_dvd data hfour heq
      value_bound :=
        k5_section_natAbs_bound heq
          {PREFIX}Section{index}_degreeAtMost
          {PREFIX}Section{index}_l1_le
    }}⟩"""
        )
    body = f"""set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem {PREFIX}_sections_not_all_zero
    {{n d : ℕ}}
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    {disjunction} := by
  by_contra h
  push Not at h
{chr(10).join(section_zeros)}
  have hcurve :
      denseBivariateEval {PREFIX}CurveDense
          (n : ℤ) ((n + d : ℕ) : ℤ) = 0 := by
    rw [{PREFIX}CurveDense_eval_eq_sparse]
    exact k5CurveTerms_eval_eq_zero heq
{chr(10).join(resultants)}
  have htarget :=
    {PREFIX}Expected_scaled_eval_eq_zero {result_args}
  exact {PREFIX}Expected_scaled_eval_ne_zero n htarget

theorem exists_{PREFIX}PunctureJetWitness
    {{n d t : ℕ}}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    Nonempty (K5PunctureJetWitness data 3 3) := by
  rcases {PREFIX}_sections_not_all_zero heq with
      hsection | hsection | hsection | hsection | hsection
{chr(10).join(witness_cases)}"""
    (output_dir / f"{MODULE_PREFIX}Endpoint.lean").write_text(
        f"{LEAN_HEADER}\n"
        f"import ErdosProblems.{MODULE_PREFIX}Noncommon\n\n"
        + namespace(
            "/-! Completed central puncture endpoint. -/\n\n" + body
        )
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output-dir", type=Path, default=Path("ErdosProblems")
    )
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    certificate = emit_certificate(3, 3, SECTION_COUNT, None)
    write_certificate_modules(
        certificate, args.output_dir, 3, 3, SECTION_COUNT
    )
    definitions, _ = compute_data()
    write_noncommon_data(args.output_dir, definitions)
    for index in range(SECTION_COUNT):
        write_elimination_modules(
            args.output_dir, MODULE_PREFIX, PREFIX, index
        )
    write_bezout(args.output_dir)
    write_noncommon_main(args.output_dir)
    write_endpoint(args.output_dir)


if __name__ == "__main__":
    main()
