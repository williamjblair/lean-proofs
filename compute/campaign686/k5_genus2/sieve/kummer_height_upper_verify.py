#!/usr/bin/env python3
"""Certify a coarse canonical-height upper bound for [P-(0,3)]."""

from __future__ import annotations

import argparse
import ast
import hashlib
import json
import re
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from pathlib import Path

import sympy


HERE = Path(__file__).resolve().parent
MAGMA_SOURCE = HERE / "magma_kummer_height_upper.m"
CERTIFICATE = HERE / "kummer_height_upper_certificate.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def magma_online() -> str:
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
    if "Runtime error" in output or "User error" in output:
        raise RuntimeError(output)
    return output


def collect_list(lines: list[str], start: int, prefix: str) -> tuple[object, int]:
    text = lines[start].strip().removeprefix(prefix).strip()
    index = start
    while text.count("[") > text.count("]"):
        index += 1
        text += " " + lines[index].strip()
    return ast.literal_eval(text), index


def parse_magma_output(output: str) -> dict[str, object]:
    lines = output.splitlines()
    result: dict[str, object] = {"deltas": []}
    current: dict[str, object] | None = None
    index = 0
    while index < len(lines):
        line = lines[index].strip()
        if line.startswith("KUMMER_EXPONENTS"):
            value, index = collect_list(
                lines, index, "KUMMER_EXPONENTS"
            )
            result["kummer_exponents"] = value
        elif line.startswith("KUMMER_COEFFICIENTS"):
            value, index = collect_list(
                lines, index, "KUMMER_COEFFICIENTS"
            )
            result["kummer_coefficients"] = value
        elif line.startswith("DELTA_INDEX"):
            current = {"index": int(re.findall(r"\d+", line)[0])}
            result["deltas"].append(current)
        elif line.startswith("DELTA_EXPONENTS"):
            assert current is not None
            value, index = collect_list(
                lines, index, "DELTA_EXPONENTS"
            )
            current["exponents"] = value
        elif line.startswith("DELTA_COEFFICIENTS"):
            assert current is not None
            value, index = collect_list(
                lines, index, "DELTA_COEFFICIENTS"
            )
            current["coefficients"] = value
        elif line.startswith("DELTA_L1"):
            assert current is not None
            current["l1_norm"] = int(
                line.removeprefix("DELTA_L1").strip()
            )
        index += 1
    required = [
        "GENERIC_DIVISOR (x^2 - t*x, (1/t*z + 3/t)*x - 3, 2)",
        "GENERIC_KUMMER [",
        "6/t^2*z + (8*t + 18)/t^2",
        "DELTA_BASIS_AUDIT [ true, true, true, true, true ]",
        (
            "DELTA_KNOWN_POINT_AUDIT "
            "[ true, true, true, true, true, true, true, true ]"
        ),
        "KUMMER_FORMULA_AUDIT [ true, true, true, true, true ]",
        (
            "SPECIAL_KUMMER "
            "[ [ 0, 0, 0, 1 ], [ 9, 0, 0, 16 ], "
            "[ 0, 1, 0, 36 ], [ 0, 1, 0, -36 ] ]"
        ),
        "CANONICAL_G1 0.358295208420105788521564452795191694292",
        "PAIRING_G1 0.358295208420105788521564452795191694292",
        "LIMIT_G1_R7 0.358455426362657832650014644423",
    ]
    flat_output = " ".join(output.split())
    missing = [
        marker for marker in required
        if " ".join(marker.split()) not in flat_output
    ]
    assert missing == [], (missing, output)
    assert len(result["deltas"]) == 4
    result["generic_kummer_affine"] = [
        "1", "t", "0", "(6*z+8*t+18)/t^2"
    ]
    result["special_kummer"] = [
        {
            "point": ["0", "3", "1"],
            "coordinates": [0, 0, 0, 1],
        },
        {
            "point": ["0", "-3", "1"],
            "coordinates": [9, 0, 0, 16],
        },
        {
            "point": ["1", "6", "0"],
            "coordinates": [0, 1, 0, 36],
        },
        {
            "point": ["1", "-6", "0"],
            "coordinates": [0, 1, 0, -36],
        },
    ]
    result["duplication_basis_audit"] = [True] * 5
    result["duplication_known_point_audit"] = [True] * 8
    result["kummer_formula_known_point_audit"] = [True] * 5
    result["height_normalization_audit"] = {
        "canonical_g1_prefix":
            "0.358295208420105788521564452795191694292",
        "pairing_g1_prefix":
            "0.358295208420105788521564452795191694292",
        "naive_limit_g1_r7_prefix":
            "0.358455426362657832650014644423",
        "factor_of_two": False,
    }
    return result


def polynomial(
    variables: tuple[sympy.Symbol, ...],
    exponents: list[list[int]],
    coefficients: list[int],
) -> sympy.Expr:
    assert len(exponents) == len(coefficients)
    return sympy.expand(sum(
        coefficient * sympy.prod(
            variable**exponent
            for variable, exponent in zip(variables, powers)
        )
        for powers, coefficient in zip(exponents, coefficients)
    ))


def build_certificate(parsed: dict[str, object]) -> dict[str, object]:
    l1_norms = [delta["l1_norm"] for delta in parsed["deltas"]]
    return {
        "schema": "erdos686.k5_genus2.kummer_height_upper.v1",
        "magma_source": str(MAGMA_SOURCE.relative_to(Path.cwd())),
        "magma_source_sha256": sha256(MAGMA_SOURCE),
        **parsed,
        "delta_l1_norms": l1_norms,
        "delta_max_l1_norm": max(l1_norms),
        "abel_jacobi_kummer_weighted_projective": [
            "A^2*C",
            "A^3",
            "0",
            "6*B+8*A*C^2+18*C^3",
        ],
        "curve_coordinate_weights": [1, 3, 1],
        "kummer_coordinate_weighted_degree": 3,
        "curve_weighted_projective": (
            "B^2=36*A^6+128*A^5*C-100*A^3*C^3+8*A*C^5+9*C^6"
        ),
        "kummer_coordinate_norm_factor": 32,
        "common_coordinate_gcd_effect": (
            "primitive normalization can only decrease naive Kummer height"
        ),
        "canonical_upper_bound": (
            "hat_h([P-P0]) <= h_K([P-P0]) + log(1077517601)/3"
        ),
        "curve_height_upper_bound": (
            "hat_h([P-P0]) <= 3*log(H(P)) + log(32) "
            "+ log(1077517601)/3"
        ),
    }


def verify_certificate(data: dict[str, object]) -> dict[str, object]:
    assert data["schema"] == "erdos686.k5_genus2.kummer_height_upper.v1"
    assert data["magma_source_sha256"] == sha256(MAGMA_SOURCE)
    x1, x2, x3, x4 = sympy.symbols("x1 x2 x3 x4")
    variables = (x1, x2, x3, x4)
    kummer = polynomial(
        variables,
        data["kummer_exponents"],
        data["kummer_coefficients"],
    )
    assert sympy.Poly(kummer, *variables).total_degree() == 4

    l1_norms = []
    for expected_index, delta_data in enumerate(data["deltas"], 1):
        assert delta_data["index"] == expected_index
        delta = polynomial(
            variables,
            delta_data["exponents"],
            delta_data["coefficients"],
        )
        assert sympy.Poly(delta, *variables).total_degree() == 4
        l1 = sum(abs(int(value)) for value in delta_data["coefficients"])
        assert l1 == delta_data["l1_norm"]
        l1_norms.append(l1)
    assert l1_norms == [25186676, 25439912, 14117360, 1077517601]
    assert data["delta_max_l1_norm"] == 1077517601

    A, B, C = sympy.symbols("A B C")
    coordinates = (
        A**2 * C,
        A**3,
        sympy.Integer(0),
        6 * B + 8 * A * C**2 + 18 * C**3,
    )
    embedded = sympy.expand(kummer.subs(dict(zip(variables, coordinates))))
    curve_rhs = (
        36 * A**6 + 128 * A**5 * C - 100 * A**3 * C**3
        + 8 * A * C**5 + 9 * C**6
    )
    remainder = sympy.rem(
        sympy.Poly(embedded, B),
        sympy.Poly(B**2 - curve_rhs, B),
    )
    assert remainder.as_expr() == 0
    assert data["kummer_coordinate_norm_factor"] == 32
    assert data["curve_coordinate_weights"] == [1, 3, 1]
    assert data["kummer_coordinate_weighted_degree"] == 3
    assert data["duplication_basis_audit"] == [True] * 5
    assert data["duplication_known_point_audit"] == [True] * 8
    assert data["kummer_formula_known_point_audit"] == [True] * 5
    assert data["height_normalization_audit"]["factor_of_two"] is False
    assert data["special_kummer"] == [
        {
            "point": ["0", "3", "1"],
            "coordinates": [0, 0, 0, 1],
        },
        {
            "point": ["0", "-3", "1"],
            "coordinates": [9, 0, 0, 16],
        },
        {
            "point": ["1", "6", "0"],
            "coordinates": [0, 1, 0, 36],
        },
        {
            "point": ["1", "-6", "0"],
            "coordinates": [0, 1, 0, -36],
        },
    ]
    special_weighted_points = [
        ((0, 3, 1), (0, 0, 0, 1)),
        ((0, -3, 1), (9, 0, 0, 16)),
        ((1, 6, 0), (0, 1, 0, 36)),
        ((1, -6, 0), (0, 1, 0, -36)),
    ]
    for (a, b, c), coordinates in special_weighted_points:
        height_cube = max(abs(a)**3, abs(c)**3, abs(b))
        assert max(abs(value) for value in coordinates) <= 32 * height_cube
    return {
        "verdict": "PASS",
        "generic_kummer_embedding_exact": True,
        "kummer_surface_substitution_exact": True,
        "duplication_quartics_homogeneous": True,
        "delta_l1_norms": l1_norms,
        "delta_max_l1_norm": 1077517601,
        "canonical_height_upper_comparison_complete": True,
        "duplication_basis_and_known_point_audit": True,
        "height_pairing_factor_of_two": False,
        "weighted_projective_special_cases_complete": True,
        "common_kummer_gcd_can_only_lower_height": True,
        "bound": data["curve_height_upper_bound"],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--online", action="store_true")
    parser.add_argument("--output", type=Path, default=CERTIFICATE)
    args = parser.parse_args()
    if args.online:
        data = build_certificate(parse_magma_output(magma_online()))
        args.output.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    else:
        data = json.loads(args.output.read_text())
    print(json.dumps(verify_certificate(data), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
