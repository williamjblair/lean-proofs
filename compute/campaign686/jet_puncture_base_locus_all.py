#!/usr/bin/env python3
"""Exact all-puncture base-locus audit for the Erdős 686 jet sections."""

from __future__ import annotations

import argparse
import concurrent.futures
import json

from flint import fmpz_poly

from jet_puncture_base_locus_experiment import (
    exact_curve_section_resultant,
    exact_section_coefficients,
)
from jet_puncture_basis_experiment import construct


def audit_puncture(task: tuple[int, int, int, int]) -> dict[str, object]:
    k, puncture_j, puncture_i, s = task
    result = construct(
        k, puncture_j, puncture_i, s,
        basis_mode="lagrange",
        emit_standard_basis=True,
    )
    basis = result["standard_basis"]
    assert isinstance(basis, list) and len(basis) >= 2
    r = int(result["r"])
    mu = int(result["mu"])
    expected = fmpz_poly([1])
    for h in range(1, k + 1):
        exponent = mu * (k - int(h == puncture_j))
        expected *= fmpz_poly([h, 1]) ** exponent
    resultant_degrees: list[int] = []
    common = None
    sections_used = 0
    for vector in basis:
        section = exact_section_coefficients(vector, k, r)
        resultant = exact_curve_section_resultant(section, k)
        resultant_degrees.append(resultant.degree())
        common = resultant if common is None else common.gcd(resultant)
        sections_used += 1
        quotient, remainder = divmod(common, expected)
        if not remainder and quotient.degree() == 0 and bool(quotient):
            break
    assert common is not None
    quotient, remainder = divmod(common, expected)
    exact = not remainder and quotient.degree() == 0 and bool(quotient)
    return {
        "puncture": [puncture_j, puncture_i],
        "resultant_degrees": resultant_degrees,
        "sections_used": sections_used,
        "gcd_degree": common.degree(),
        "expected_degree": expected.degree(),
        "exact_prescribed_base_locus": exact,
        "constant_quotient": str(quotient) if exact else None,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=5)
    parser.add_argument("--s", type=int, default=1)
    parser.add_argument("--workers", type=int, default=1)
    args = parser.parse_args()
    tasks = [
        (args.k, j, i, args.s)
        for j in range(1, args.k + 1)
        for i in range(1, args.k + 1)
    ]
    if args.workers == 1:
        results = [audit_puncture(task) for task in tasks]
    else:
        with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers) as executor:
            results = list(executor.map(audit_puncture, tasks))
    print(json.dumps({
        "k": args.k,
        "s": args.s,
        "puncture_count": len(results),
        "all_exact_prescribed_base_locus": all(
            bool(result["exact_prescribed_base_locus"]) for result in results
        ),
        "gcd_degrees": sorted({int(result["gcd_degree"]) for result in results}),
        "constant_quotients": sorted({str(result["constant_quotient"]) for result in results}),
        "results": results,
    }, indent=2))


if __name__ == "__main__":
    main()
