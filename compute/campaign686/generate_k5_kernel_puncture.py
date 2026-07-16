#!/usr/bin/env python3
"""Emit a split, kernel-only Lean endpoint for a noncentral k=5 puncture."""

from __future__ import annotations

import argparse
import re
from pathlib import Path

from generate_k5_noncommon_certificate import emit as emit_noncommon
from generate_k5_puncture_certificate import emit as emit_certificate


LEAN_HEADER = "/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/"


def namespace(body: str) -> str:
    return (
        "namespace Erdos686\n"
        "namespace Erdos686Variant\n\n"
        f"{body.rstrip()}\n\n"
        "end Erdos686Variant\n"
        "end Erdos686\n"
    )


def definition_blocks(text: str, prefix: str) -> list[str]:
    lines = text.splitlines(keepends=True)
    blocks: list[str] = []
    index = 0
    while index < len(lines):
        if re.match(rf"def {re.escape(prefix)}", lines[index]):
            start = index
            index += 1
            while index < len(lines) and lines[index].strip():
                index += 1
            blocks.append("".join(lines[start:index]).rstrip())
        index += 1
    return blocks


def theorem_block(text: str, name: str) -> str:
    lines = text.splitlines(keepends=True)
    start = next(
        index for index, line in enumerate(lines)
        if line.startswith(f"theorem {name}")
    )
    index = start + 1
    while index < len(lines) and lines[index].strip():
        index += 1
    return "".join(lines[start:index]).rstrip()


def write_certificate_modules(
    text: str,
    output_dir: Path,
    puncture_j: int,
    puncture_i: int,
    section_count: int,
) -> None:
    prefix = f"k5P{puncture_j}{puncture_i}"
    module_prefix = f"Erdos686K5P{puncture_j}{puncture_i}"
    definitions = definition_blocks(text, prefix)
    expected_definitions = section_count * 25
    assert len(definitions) == expected_definitions, (
        len(definitions), expected_definitions
    )
    data_body = (
        "/-! Generated exact k=5 puncture certificate data. -/\n\n"
        + "\n\n".join(definitions)
    )
    (output_dir / f"{module_prefix}CertificateData.lean").write_text(
        f"{LEAN_HEADER}\n"
        "import ErdosProblems.Erdos686SparseJetCertificate\n\n"
        + namespace(data_body)
    )

    lines = text.splitlines(keepends=True)
    local_cells = [
        (j, i)
        for j in range(1, 6)
        for i in range(1, 6)
        if (j, i) != (puncture_j, puncture_i)
    ]
    row_modules: list[str] = []
    for section_index in range(section_count):
        section = f"{prefix}Section{section_index}"
        for j, i in local_cells:
            marker = f"theorem {section}_taylorRow0_J{j}_I{i} :"
            theorem_line = next(
                index for index, line in enumerate(lines)
                if line.startswith(marker)
            )
            start = theorem_line - 2
            boundary = next(
                index
                for index in range(theorem_line + 1, len(lines))
                if lines[index].startswith(f"def {section}QJ")
                or lines[index].startswith(
                    f"theorem {section}_degreeAtMost"
                )
                or (
                    section_index + 1 < section_count
                    and lines[index].startswith(
                        f"def {prefix}Section{section_index + 1}"
                    )
                )
            )
            body = "".join(lines[start:boundary]).rstrip()
            module = (
                f"{module_prefix}S{section_index}J{j}I{i}Rows"
            )
            row_modules.append(module)
            (output_dir / f"{module}.lean").write_text(
                f"{LEAN_HEADER}\n"
                f"import ErdosProblems.{module_prefix}CertificateData\n\n"
                + namespace(body)
            )

    metadata: list[str] = []
    for section_index in range(section_count):
        section = f"{prefix}Section{section_index}"
        start = next(
            index for index, line in enumerate(lines)
            if line.startswith(f"theorem {section}_degreeAtMost")
        )
        if section_index + 1 < section_count:
            end = next(
                index for index, line in enumerate(lines)
                if line.startswith(
                    f"def {prefix}Section{section_index + 1}"
                )
            )
        else:
            end = next(
                index for index, line in enumerate(lines)
                if line.startswith("end Erdos686Variant")
            )
        metadata.append("".join(lines[start:end]).rstrip())
    imports = [
        f"import ErdosProblems.{module_prefix}CertificateData",
        *[f"import ErdosProblems.{module}" for module in row_modules],
    ]
    main_body = (
        f"/-! Kernel-checked row assembly for the k=5 puncture "
        f"({puncture_j},{puncture_i}). -/\n\n"
        + "\n\n".join(metadata)
    )
    (output_dir / f"{module_prefix}Certificate.lean").write_text(
        f"{LEAN_HEADER}\n" + "\n".join(imports) + "\n\n"
        + namespace(main_body)
    )


def elimination_difference(prefix: str, index: int) -> str:
    return (
        f"def {prefix}EliminationDifference{index} : "
        "DenseBivariateIntPolynomial :=\n"
        "  denseBivariateSub\n"
        "    (denseBivariateAdd\n"
        f"      (denseBivariateMul {prefix}SectionCofactor{index} "
        f"{prefix}Section{index}Dense)\n"
        f"      (denseBivariateMul {prefix}CurveCofactor{index} "
        f"{prefix}CurveDense))\n"
        f"    [{prefix}Resultant{index}]"
    )


def write_elimination_modules(
    output_dir: Path,
    module_prefix: str,
    prefix: str,
    index: int,
) -> None:
    row_modules: list[str] = []
    for row in range(9):
        module = f"{module_prefix}Elimination{index}Row{row}"
        row_modules.append(module)
        body = (
            "set_option maxRecDepth 100000 in\n"
            "set_option maxHeartbeats 0 in\n"
            f"theorem {prefix}EliminationDifference{index}_row{row} :\n"
            f"    denseIntIsZero "
            f"({prefix}EliminationDifference{index}.getD {row} []) := by\n"
            "  unfold denseIntIsZero\n"
            "  decide +kernel"
        )
        (output_dir / f"{module}.lean").write_text(
            f"{LEAN_HEADER}\n"
            f"import ErdosProblems.{module_prefix}NoncommonData\n\n"
            + namespace(body)
        )
    imports = "\n".join(
        f"import ErdosProblems.{module}" for module in row_modules
    )
    exact_rows = "\n".join(
        f"  · exact {prefix}EliminationDifference{index}_row{row}"
        for row in range(9)
    )
    body = (
        f"theorem {prefix}EliminationDifference{index}_length :\n"
        f"    {prefix}EliminationDifference{index}.length = 9 := by\n"
        "  decide +kernel\n\n"
        f"theorem {prefix}EliminationDifference{index}_rows :\n"
        f"    DenseBivariateRowsCertificate "
        f"{prefix}EliminationDifference{index} := by\n"
        "  intro rowIndex hindex\n"
        f"  rw [{prefix}EliminationDifference{index}_length] at hindex\n"
        "  interval_cases rowIndex\n"
        f"{exact_rows}\n\n"
        f"theorem {prefix}EliminationIdentity{index} :\n"
        "    denseBivariateIsZero\n"
        "      (denseBivariateSub\n"
        "        (denseBivariateAdd\n"
        f"          (denseBivariateMul {prefix}SectionCofactor{index}\n"
        f"            {prefix}Section{index}Dense)\n"
        f"          (denseBivariateMul {prefix}CurveCofactor{index}\n"
        f"            {prefix}CurveDense))\n"
        f"        [{prefix}Resultant{index}]) := by\n"
        f"  change denseBivariateIsZero "
        f"{prefix}EliminationDifference{index}\n"
        "  exact denseBivariateIsZero_of_rows "
        f"{prefix}EliminationDifference{index}_rows"
    )
    (output_dir / f"{module_prefix}Elimination{index}Rows.lean").write_text(
        f"{LEAN_HEADER}\n{imports}\n\n" + namespace(body)
    )


def noncommon_main(prefix: str) -> str:
    section_theorems: list[str] = []
    for index in range(2):
        section_theorems.append(
            f"""theorem {prefix}Section{index}Dense_toSparse :
    denseBivariateToSparse {prefix}Section{index}Dense =
      {prefix}Section{index} := by
  decide +kernel

theorem {prefix}Resultant{index}_eval_eq_zero
    {{x y : ℤ}}
    (hsection :
      denseBivariateEval {prefix}Section{index}Dense x y = 0)
    (hcurve :
      denseBivariateEval {prefix}CurveDense x y = 0) :
    denseIntEval {prefix}Resultant{index} x = 0 := by
  have hresultantDense :=
    denseBivariate_elimination_eval_zero
      {prefix}EliminationIdentity{index} hsection hcurve
  simpa [denseBivariateEval] using hresultantDense

theorem {prefix}Section{index}Dense_eval_eq_sparse
    (n d : ℕ) :
    denseBivariateEval {prefix}Section{index}Dense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
      sparseBivariateEval {prefix}Section{index} n (n + d) := by
  calc
    denseBivariateEval {prefix}Section{index}Dense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
        sparseBivariateEval
          (denseBivariateToSparse {prefix}Section{index}Dense)
          n (n + d) :=
      (denseBivariateToSparse_eval _ _ _).symm
    _ = sparseBivariateEval {prefix}Section{index} n (n + d) := by
      rw [{prefix}Section{index}Dense_toSparse]"""
        )
    return f"""set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem {prefix}CurveDense_toSparse :
    denseBivariateToSparse {prefix}CurveDense = k5CurveTerms := by
  decide +kernel

{section_theorems[0]}

{section_theorems[1]}

theorem {prefix}Expected_scaled_eval_eq_zero
    {{x : ℤ}}
    (hresultant0 : denseIntEval {prefix}Resultant0 x = 0)
    (hresultant1 : denseIntEval {prefix}Resultant1 x = 0) :
    denseIntEval
      (denseIntScale {prefix}BezoutScale {prefix}Expected) x = 0 :=
  denseInt_bezout_eval_zero
    {prefix}ResultantBezoutIdentity hresultant0 hresultant1

theorem {prefix}CurveDense_eval_eq_sparse
    (n d : ℕ) :
    denseBivariateEval {prefix}CurveDense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
      sparseBivariateEval k5CurveTerms n (n + d) := by
  calc
    denseBivariateEval {prefix}CurveDense
        (n : ℤ) ((n + d : ℕ) : ℤ) =
        sparseBivariateEval
          (denseBivariateToSparse {prefix}CurveDense) n (n + d) :=
      (denseBivariateToSparse_eval _ _ _).symm
    _ = sparseBivariateEval k5CurveTerms n (n + d) := by
      rw [{prefix}CurveDense_toSparse]

theorem {prefix}Expected_eval_pos
    (n : ℕ) :
    0 < denseIntEval {prefix}Expected (n : ℤ) := by
  unfold {prefix}Expected
  rw [denseIntMul_eval, denseIntPow_eval,
    denseIntMul_eval, denseIntPow_eval,
    denseIntMul_eval, denseIntPow_eval,
    denseIntMul_eval, denseIntPow_eval,
    denseIntPow_eval]
  norm_num [denseIntEval]
  positivity

theorem {prefix}Expected_scaled_eval_ne_zero
    (n : ℕ) :
    denseIntEval
        (denseIntScale {prefix}BezoutScale {prefix}Expected)
        (n : ℤ) ≠ 0 := by
  rw [denseIntScale_eval]
  exact mul_ne_zero
    (by norm_num [{prefix}BezoutScale])
    (ne_of_gt ({prefix}Expected_eval_pos n))"""


def write_noncommon_modules(
    text: str,
    output_dir: Path,
    puncture_j: int,
    puncture_i: int,
) -> None:
    prefix = f"k5P{puncture_j}{puncture_i}"
    module_prefix = f"Erdos686K5P{puncture_j}{puncture_i}"
    definitions = definition_blocks(text, prefix)
    assert len(definitions) == 13, len(definitions)
    data_body = (
        "/-! Generated exact non-common-zero certificate data. -/\n\n"
        "set_option maxRecDepth 100000\n"
        "set_option maxHeartbeats 0\n\n"
        + "\n\n".join(definitions)
        + "\n\n"
        + elimination_difference(prefix, 0)
        + "\n\n"
        + elimination_difference(prefix, 1)
    )
    (output_dir / f"{module_prefix}NoncommonData.lean").write_text(
        f"{LEAN_HEADER}\n"
        f"import ErdosProblems.{module_prefix}Certificate\n"
        "import ErdosProblems.Erdos686DenseKernelCertificate\n\n"
        + namespace(data_body)
    )
    for index in range(2):
        write_elimination_modules(
            output_dir, module_prefix, prefix, index
        )
    bezout_body = (
        "set_option maxRecDepth 100000 in\n"
        "set_option maxHeartbeats 0 in\n"
        f"theorem {prefix}ResultantBezoutIdentity :\n"
        "    denseIntIsZero\n"
        "      (denseIntSub\n"
        "        (denseIntAdd\n"
        f"          (denseIntMul {prefix}ResultantCofactor0\n"
        f"            {prefix}Resultant0)\n"
        f"          (denseIntMul {prefix}ResultantCofactor1\n"
        f"            {prefix}Resultant1))\n"
        f"        (denseIntScale {prefix}BezoutScale\n"
        f"          {prefix}Expected)) := by\n"
        "  unfold denseIntIsZero\n"
        "  decide +kernel"
    )
    (output_dir / f"{module_prefix}BezoutKernel.lean").write_text(
        f"{LEAN_HEADER}\n"
        f"import ErdosProblems.{module_prefix}NoncommonData\n\n"
        + namespace(bezout_body)
    )
    imports = "\n".join(
        [
            f"import ErdosProblems.{module_prefix}NoncommonData",
            f"import ErdosProblems.{module_prefix}Elimination0Rows",
            f"import ErdosProblems.{module_prefix}Elimination1Rows",
            f"import ErdosProblems.{module_prefix}BezoutKernel",
        ]
    )
    (output_dir / f"{module_prefix}Noncommon.lean").write_text(
        f"{LEAN_HEADER}\n{imports}\n\n"
        + namespace(
            "/-! Kernel-checked non-common-zero certificate. -/\n\n"
            + noncommon_main(prefix)
        )
    )


def endpoint_body(
    prefix: str, puncture_j: int, puncture_i: int
) -> str:
    return f"""set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem {prefix}_sections_not_both_zero
    {{n d : ℕ}}
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    sparseBivariateEval {prefix}Section0 n (n + d) ≠ 0 ∨
      sparseBivariateEval {prefix}Section1 n (n + d) ≠ 0 := by
  by_contra h
  push Not at h
  have hsection0 :
      denseBivariateEval
        {prefix}Section0Dense (n : ℤ) ((n + d : ℕ) : ℤ) = 0 := by
    rw [{prefix}Section0Dense_eval_eq_sparse]
    exact h.1
  have hsection1 :
      denseBivariateEval
        {prefix}Section1Dense (n : ℤ) ((n + d : ℕ) : ℤ) = 0 := by
    rw [{prefix}Section1Dense_eval_eq_sparse]
    exact h.2
  have hcurve :
      denseBivariateEval
        {prefix}CurveDense (n : ℤ) ((n + d : ℕ) : ℤ) = 0 := by
    rw [{prefix}CurveDense_eval_eq_sparse]
    exact k5CurveTerms_eval_eq_zero heq
  have hresultant0 :
      denseIntEval {prefix}Resultant0 (n : ℤ) = 0 :=
    {prefix}Resultant0_eval_eq_zero hsection0 hcurve
  have hresultant1 :
      denseIntEval {prefix}Resultant1 (n : ℤ) = 0 :=
    {prefix}Resultant1_eval_eq_zero hsection1 hcurve
  have htarget :=
    {prefix}Expected_scaled_eval_eq_zero hresultant0 hresultant1
  exact {prefix}Expected_scaled_eval_ne_zero n htarget

theorem exists_{prefix}PunctureJetWitness
    {{n d t : ℕ}}
    (data : CanonicalOwnerData 5 n d t)
    (hfour : 4 ∣ n + d + t)
    (heq : blockProduct 5 (n + d) = 4 * blockProduct 5 n) :
    Nonempty (K5PunctureJetWitness data {puncture_j} {puncture_i}) := by
  rcases {prefix}_sections_not_both_zero heq with
      hsection | hsection
  · exact ⟨{{
      value :=
        (sparseBivariateEval {prefix}Section0 n (n + d)).natAbs
      value_pos := Int.natAbs_pos.mpr hsection
      local_dvd :=
        {prefix}Section0_local_dvd data hfour heq
      value_bound :=
        k5_section_natAbs_bound heq
          {prefix}Section0_degreeAtMost {prefix}Section0_l1_le
    }}⟩
  · exact ⟨{{
      value :=
        (sparseBivariateEval {prefix}Section1 n (n + d)).natAbs
      value_pos := Int.natAbs_pos.mpr hsection
      local_dvd :=
        {prefix}Section1_local_dvd data hfour heq
      value_bound :=
        k5_section_natAbs_bound heq
          {prefix}Section1_degreeAtMost {prefix}Section1_l1_le
    }}⟩"""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--j", type=int, required=True)
    parser.add_argument("--i", type=int, required=True)
    parser.add_argument(
        "--output-dir", type=Path, default=Path("ErdosProblems")
    )
    args = parser.parse_args()
    if (args.j, args.i) == (3, 3):
        raise SystemExit(
            "The central puncture needs the separate five-section generator."
        )
    certificate = emit_certificate(args.j, args.i, 2, None)
    noncommon = emit_noncommon(args.j, args.i)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    write_certificate_modules(
        certificate, args.output_dir, args.j, args.i, 2
    )
    write_noncommon_modules(
        noncommon, args.output_dir, args.j, args.i
    )
    prefix = f"k5P{args.j}{args.i}"
    module_prefix = f"Erdos686K5P{args.j}{args.i}"
    (args.output_dir / f"{module_prefix}Endpoint.lean").write_text(
        f"{LEAN_HEADER}\n"
        f"import ErdosProblems.{module_prefix}Noncommon\n\n"
        + namespace(
            f"/-! Completed puncture ({args.j},{args.i}) endpoint. -/\n\n"
            + endpoint_body(prefix, args.j, args.i)
        )
    )


if __name__ == "__main__":
    main()
