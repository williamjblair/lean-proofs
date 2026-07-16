#!/usr/bin/env python3
"""Verify the frozen k=5 genus-two two-cover pair-field certificate."""

from __future__ import annotations

import argparse
import json
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from fractions import Fraction
from pathlib import Path

import sympy


HERE = Path(__file__).resolve().parent
CERTIFICATE = HERE / "two_cover_certificate.json"
MAGMA_SOURCE = HERE / "two_cover_pair_field.m"


def _fraction(value: str) -> Fraction:
    return Fraction(value)


def _polynomial(
    coefficients: list[str], variable: sympy.Symbol
) -> sympy.Poly:
    expression = sum(
        sympy.Rational(_fraction(coefficient).numerator,
                       _fraction(coefficient).denominator)
        * variable**degree
        for degree, coefficient in enumerate(coefficients)
    )
    return sympy.Poly(expression, variable, domain=sympy.QQ)


def verify_offline() -> dict[str, object]:
    data = json.loads(CERTIFICATE.read_text())
    assert data["schema"] == "erdos686.k5_genus2.two_cover_certificate.v1"

    t, z = sympy.symbols("t z")
    sextic = _polynomial(
        data["monic_sextic_coefficients_low_to_high"], t
    )
    pair_data = data["pair_resultant"]
    diagonal = _polynomial(
        pair_data["diagonal_factor_coefficients_low_to_high"], z
    )
    pair_resolvent = _polynomial(
        pair_data["pair_resolvent_coefficients_low_to_high"], z
    )

    resultant = sympy.Poly(
        sympy.resultant(sextic.as_expr(),
                        sextic.as_expr().subs(t, z - t), t),
        z,
        domain=sympy.QQ,
    )
    expected_resultant = diagonal * pair_resolvent**2
    assert resultant == expected_resultant
    assert resultant.degree() == pair_data["degree"] == 36
    assert diagonal.degree() == 6
    assert pair_resolvent.degree() == data["pair_field"]["degree"] == 15
    assert pair_data["diagonal_factor_multiplicity"] == 1
    assert pair_data["pair_resolvent_multiplicity"] == 2
    assert (
        pair_resolvent.is_irreducible
        is pair_data["pair_resolvent_irreducible"]
        is True
    )

    descent = data["two_cover_descent"]
    counts = sorted(descent["known_affine_point_class_counts_sorted"])
    assert counts == [2, 4, 4, 4, 4, 4, 6, 6]
    assert sum(counts) == descent["known_affine_point_count"] == 34
    assert descent["known_projective_point_count"] == 36
    assert descent["locally_soluble_cover_count"] == len(counts) == 8
    assert sorted(descent["representative_norms_sorted"]) == [
        1, 1, 9, 81, 81, 81, 81, 729
    ]
    assert descent["elliptic_covers_constructed"] == 8
    assert len(descent["elliptic_cover_witness_x"]) == 8
    assert len({
        _fraction(value)
        for value in descent["elliptic_cover_witness_x"]
    }) == 8
    assert data["pair_field"]["sextic_factor_degrees"] == [2, 4]
    assert data["completeness"]["rational_points_proved_complete"] is False

    return {
        "verdict": "PASS",
        "cover_count": descent["locally_soluble_cover_count"],
        "pair_resolvent_degree": pair_resolvent.degree(),
        "pair_resolvent_irreducible": pair_resolvent.is_irreducible,
        "factor_degrees": data["pair_field"]["sextic_factor_degrees"],
        "known_point_class_counts": counts,
        "elliptic_covers_constructed":
            descent["elliptic_covers_constructed"],
        "rational_points_proved_complete": False,
    }


def run_online() -> str:
    payload = urllib.parse.urlencode(
        {"input": MAGMA_SOURCE.read_text()}
    ).encode()
    request = urllib.request.Request(
        "http://magma.maths.usyd.edu.au/xml/calculator.xml",
        data=payload,
        headers={"User-Agent": "Mozilla/5.0"},
        method="POST",
    )
    with urllib.request.urlopen(request, timeout=75) as response:
        root = ET.fromstring(response.read())
    output = "\n".join(
        node.text or "" for node in root.findall("./results/line")
    )
    required = [
        "PAIR_RESULTANT_DEGREE 36",
        "PAIR_RESOLVENT_DEGREE 15",
        "PAIR_RESOLVENT_IRREDUCIBLE true",
        "FACTOR_DEGREES [ 2, 4 ]",
        "TWO_COVER_COUNT 8",
        "KNOWN_PROJECTIVE_POINT_COUNT 36",
        "KNOWN_AFFINE_POINT_COUNT 34",
        "CLASS_POINT_COUNTS_SORTED [ 2, 4, 4, 4, 4, 4, 6, 6 ]",
        "COVER_NORMS_SORTED [ 1, 1, 9, 81, 81, 81, 81, 729 ]",
        "ELLIPTIC_COVERS_CONSTRUCTED 8",
    ]
    missing = [marker for marker in required if marker not in output]
    assert missing == [], (missing, output)
    return output


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--online", action="store_true")
    args = parser.parse_args()
    result = verify_offline()
    if args.online:
        result["online_magma_output"] = run_online()
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
