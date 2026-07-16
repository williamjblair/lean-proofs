#!/usr/bin/env python3
"""Emit kernel-checkable Lean data for a k=5 puncture jet certificate."""

from __future__ import annotations

import argparse
from fractions import Fraction
from pathlib import Path

from jet_puncture_basis_experiment import construct, local_curve_quotient


def lean_int(value: int) -> str:
    return str(value) if value >= 0 else f"({value})"


def lean_terms(terms: list[tuple[int, int, int]]) -> str:
    rendered = [
        "  { coefficient := "
        f"{lean_int(coefficient)}, xExponent := {x_degree}, "
        f"yExponent := {y_degree} }}"
        for coefficient, x_degree, y_degree in terms
        if coefficient
    ]
    if not rendered:
        return "[]"
    return "[\n" + "\n, ".join(rendered) + "\n]"


def standard_terms(vector: list[int], k: int, r: int) -> list[tuple[int, int, int]]:
    result: list[tuple[int, int, int]] = []
    index = 0
    for y_degree in range(k):
        for x_degree in range(r - y_degree + 1):
            coefficient = vector[index]
            index += 1
            if coefficient:
                result.append((coefficient, x_degree, y_degree))
    assert index == len(vector)
    return result


def quotient_terms(
    vector: list[int], k: int, r: int, j: int, i: int, mu: int
) -> list[tuple[int, int, int]]:
    quotient = local_curve_quotient(vector, k, r, j, i, mu)
    result: list[tuple[int, int, int]] = []
    for (x_degree, y_degree), coefficient in sorted(
        quotient.items(), key=lambda item: (item[0][1], item[0][0])
    ):
        assert isinstance(coefficient, Fraction)
        assert coefficient.denominator == 1
        if coefficient:
            result.append((coefficient.numerator, x_degree, y_degree))
    return result


def emit(
    puncture_j: int,
    puncture_i: int,
    section_count: int,
    local_limit: int | None,
) -> str:
    result = construct(
        5,
        puncture_j,
        puncture_i,
        1,
        basis_mode="lagrange",
        emit_standard_basis=True,
    )
    basis = result["standard_basis"]
    assert isinstance(basis, list)
    r = int(result["r"])
    mu = int(result["mu"])
    selected = basis[:section_count]
    locals_ = [
        (j, i)
        for j in range(1, 6)
        for i in range(1, 6)
        if (j, i) != (puncture_j, puncture_i)
    ]
    if local_limit is not None:
        locals_ = locals_[:local_limit]

    lines = [
        "/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/",
        "import ErdosProblems.Erdos686SparseJetCertificate",
        "",
        "namespace Erdos686",
        "namespace Erdos686Variant",
        "",
        "/-! Generated exact k=5 puncture certificate data. -/",
        "",
    ]
    prefix = f"k5P{puncture_j}{puncture_i}"
    for section_index, vector in enumerate(selected):
        section_name = f"{prefix}Section{section_index}"
        lines.extend(
            [
                f"def {section_name} : List SparseBivariateTerm :=",
                lean_terms(standard_terms(vector, 5, r)),
                "",
            ]
        )
        for j, i in locals_:
            quotient_name = f"{section_name}QJ{j}I{i}"
            lines.extend(
                [
                    f"def {quotient_name} : List SparseBivariateTerm :=",
                    lean_terms(quotient_terms(vector, 5, r, j, i, mu)),
                    "",
                ]
            )
            for a in range(mu):
                lines.extend(
                    [
                        "set_option maxRecDepth 100000 in",
                        "set_option maxHeartbeats 0 in",
                        f"theorem {section_name}_taylorRow{a}_J{j}_I{i} :",
                        f"    sparseLocalTaylorRowCheck 17 {a}",
                        f"      {section_name} {quotient_name} k5CurveTerms",
                        f"        (-{j}) (-{i}) = true := by",
                        "  decide +kernel",
                        "",
                    ]
                )
            rows_name = f"{section_name}_taylorRows_J{j}_I{i}"
            lines.extend(
                [
                    f"theorem {rows_name} :",
                    "    SparseLocalTaylorRowsCertificate 17",
                    f"      {section_name} {quotient_name} k5CurveTerms",
                    f"        (-{j}) (-{i}) := by",
                    "  intro a ha",
                    "  interval_cases a",
                ]
            )
            for a in range(mu):
                lines.append(
                    f"  · exact {section_name}_taylorRow{a}_J{j}_I{i}"
                )
            lines.append("")
        if local_limit is None:
            lines.extend(
                [
                    f"theorem {section_name}_degreeAtMost :",
                    f"    sparseBivariateDegreeAtMost 84 {section_name} :=",
                    "  sparseDegreeAtMost_of_decidable (by",
                    "    unfold sparseDecidableDegreeAtMost",
                    "    decide +kernel)",
                    "",
                    f"theorem {section_name}_l1_le :",
                    f"    sparseBivariateL1Norm {section_name} ≤",
                    "      k5PunctureCoefficientNorm := by",
                    "  decide +kernel",
                    "",
                    f"theorem {section_name}_local_dvd",
                    "    {n d t : ℕ}",
                    "    (data : CanonicalOwnerData 5 n d t)",
                    "    (hfour : 4 ∣ n + d + t)",
                    "    (heq : blockProduct 5 (n + d) =",
                    "      4 * blockProduct 5 n) :",
                    "    ∀ j ∈ Finset.Icc 1 5, ∀ i ∈ Finset.Icc 1 5,",
                    f"      (j, i) ≠ ({puncture_j}, {puncture_i}) →",
                    "        canonicalOwnerCell data j i ^ 17 ∣",
                    f"          (sparseBivariateEval {section_name}",
                    "            n (n + d)).natAbs := by",
                    "  intro j hj i hi hne",
                    "  have hx := canonicalOwnerCell_dvd_lower",
                    "    data (j := j) (i := i)",
                    "  have hy : canonicalOwnerCell data j i ∣",
                    "      n + d + i :=",
                    "    dvd_trans",
                    "      (canonicalOwnerCell_dvd_upper",
                    "        data (j := j) (i := i))",
                    "      (upperTermAfterFour_dvd_original hfour)",
                    "  rcases Finset.mem_Icc.mp hj with ⟨hjlow, hjhigh⟩",
                    "  rcases Finset.mem_Icc.mp hi with ⟨hilow, hihigh⟩",
                    "  interval_cases j <;> interval_cases i",
                ]
            )
            for j in range(1, 6):
                for i in range(1, 6):
                    if (j, i) == (puncture_j, puncture_i):
                        lines.append("  · exact (hne rfl).elim")
                    else:
                        theorem_name = (
                            f"{section_name}_taylorRows_J{j}_I{i}"
                        )
                        lines.extend(
                            [
                                "  · exact",
                                "      k5_direct_rows_certificate_pow_dvd_"
                                "section_natAbs",
                                f"        heq hx hy {theorem_name}",
                            ]
                        )
            lines.append("")
    lines.extend(
        [
            "end Erdos686Variant",
            "end Erdos686",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--j", type=int, default=1)
    parser.add_argument("--i", type=int, default=1)
    parser.add_argument("--sections", type=int, default=1)
    parser.add_argument("--local-limit", type=int)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    text = emit(args.j, args.i, args.sections, args.local_limit)
    args.output.write_text(text)


if __name__ == "__main__":
    main()
