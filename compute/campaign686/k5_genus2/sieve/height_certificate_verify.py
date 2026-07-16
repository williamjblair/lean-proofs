#!/usr/bin/env python3
"""Exact rational audit of the k=5 height-matrix lower bound."""

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
CERTIFICATE = HERE / "height_certificate.json"
MAGMA_SOURCE = HERE / "magma_height_certificate.m"


def rational(value: str) -> sympy.Rational:
    fraction = Fraction(value)
    return sympy.Rational(fraction.numerator, fraction.denominator)


def verify_offline() -> dict[str, object]:
    data = json.loads(CERTIFICATE.read_text())
    assert data["schema"] == "erdos686.k5_genus2.height_certificate.v1"
    matrix = sympy.Matrix([
        [rational(value) for value in row]
        for row in data["height_pairing_center"]
    ])
    assert matrix.shape == (5, 5)
    assert matrix == matrix.T

    center_lower = rational(
        data["center_matrix_lower_eigenvalue"]
    )
    shifted = matrix - center_lower * sympy.eye(5)
    leading_minors = [
        sympy.factor(shifted[:size, :size].det())
        for size in range(1, 6)
    ]
    assert all(value > 0 for value in leading_minors)

    radius = rational(data["magma_entry_enclosure_radius"])
    transferred_lower = center_lower - 5 * radius
    assert transferred_lower == rational(
        data["certified_true_matrix_lower_eigenvalue"]
    )
    assert transferred_lower > 0
    assert data["height_constant"]["certified_semantics"] == (
        "h_K(P) <= canonical_height(P) + global"
    )
    return {
        "verdict": "PASS",
        "dimension": 5,
        "center_lower_eigenvalue": str(center_lower),
        "entry_enclosure_radius": str(radius),
        "certified_true_matrix_lower_eigenvalue":
            str(transferred_lower),
        "leading_principal_minors_positive": True,
        "height_constant_is_one_sided": True,
        "global_curve_height_upper_bound_complete": False,
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
        "HEIGHT_COARSE_ENCLOSURE true",
        "REGULATOR 0.336950779310370370455955674076267237016541110667699",
        "HEIGHT_CONSTANT 7.8144270562185764398936470553",
        "HEIGHT_INFINITY 6.9326419049478548377169155136",
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
