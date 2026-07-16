#!/usr/bin/env python3
"""Emit exact dense Bézout certificates for a k=5 puncture."""

from __future__ import annotations

import argparse
import math
from pathlib import Path

import sympy as sp

from jet_puncture_basis_experiment import construct
from jet_puncture_base_locus_experiment import (
    exact_curve_section_resultant,
    exact_section_coefficients,
)


def lean_int(value: int) -> str:
    return str(value) if value >= 0 else f"({value})"


def lean_row(row: list[int]) -> str:
    return "[" + ", ".join(lean_int(value) for value in row) + "]"


def lean_rows(rows: list[list[int]]) -> str:
    return "[\n  " + "\n, ".join(lean_row(row) for row in rows) + "\n]"


def section_rows(vector: list[int], k: int, r: int) -> list[list[int]]:
    rows: list[list[int]] = []
    index = 0
    for y_degree in range(k):
        width = r - y_degree + 1
        rows.append(vector[index:index + width])
        index += width
    assert index == len(vector)
    return rows


def sympy_section(rows: list[list[int]], x: sp.Symbol, y: sp.Symbol) -> sp.Expr:
    return sum(
        coefficient * x**x_degree * y**y_degree
        for y_degree, row in enumerate(rows)
        for x_degree, coefficient in enumerate(row)
        if coefficient
    )


def low_coefficients(poly: sp.Poly, x: sp.Symbol) -> list[int]:
    if poly.is_zero:
        return []
    return [int(poly.nth(degree)) for degree in range(poly.degree() + 1)]


def resultant_poly(resultant: object, x: sp.Symbol) -> sp.Poly:
    degree = resultant.degree()
    expression = sum(int(resultant[index]) * x**index for index in range(degree + 1))
    return sp.Poly(expression, x, domain=sp.ZZ)


def cleared_elimination_cofactors(
    section: sp.Expr,
    curve: sp.Expr,
    resultant: sp.Poly,
    x: sp.Symbol,
    y: sp.Symbol,
) -> tuple[list[list[int]], list[list[int]]]:
    field = sp.QQ.frac_field(x)
    section_y = sp.Poly(section, y, domain=field)
    curve_y = sp.Poly(curve, y, domain=field)
    section_cofactor, curve_cofactor, gcd = sp.gcdex(section_y, curve_y)
    assert gcd == sp.Poly(1, y, domain=field)

    rows: list[list[int]] = []
    split = section_cofactor.degree() + 1
    for cofactor in (section_cofactor, curve_cofactor):
        for y_degree in range(cofactor.degree() + 1):
            value = sp.cancel(cofactor.nth(y_degree).as_expr() * resultant.as_expr())
            numerator, denominator = sp.fraction(value)
            denominator_poly = sp.Poly(denominator, x, domain=sp.ZZ)
            assert denominator_poly.degree() == 0
            denominator_int = int(denominator_poly.nth(0))
            assert denominator_int in (1, -1)
            polynomial = sp.Poly(
                numerator if denominator_int == 1 else -numerator,
                x,
                domain=sp.ZZ,
            )
            rows.append(low_coefficients(polynomial, x))
    return rows[:split], rows[split:]


def cleared_univariate_bezout(
    left: sp.Poly,
    right: sp.Poly,
    expected: sp.Poly,
    x: sp.Symbol,
) -> tuple[list[int], list[int], int]:
    left_cofactor, right_cofactor, gcd = sp.gcdex(left, right)
    quotient = sp.exquo(gcd, expected)
    assert quotient.degree() == 0 and quotient.nth(0) != 0
    scalar = sp.Rational(quotient.nth(0))
    denominator = 1
    for coefficient in (
        left_cofactor.all_coeffs()
        + right_cofactor.all_coeffs()
        + [scalar]
    ):
        denominator = math.lcm(denominator, int(sp.denom(coefficient)))
    left_integer = sp.Poly(
        left_cofactor.as_expr() * denominator, x, domain=sp.ZZ
    )
    right_integer = sp.Poly(
        right_cofactor.as_expr() * denominator, x, domain=sp.ZZ
    )
    target_scale = int(scalar * denominator)
    assert left_integer * left + right_integer * right == sp.Poly(
        expected.as_expr() * target_scale, x, domain=sp.ZZ
    )
    return (
        low_coefficients(left_integer, x),
        low_coefficients(right_integer, x),
        target_scale,
    )


def cleared_multi_univariate_bezout(
    polynomials: list[sp.Poly],
    expected: sp.Poly,
    x: sp.Symbol,
) -> tuple[list[list[int]], int]:
    assert polynomials
    gcd = polynomials[0]
    cofactors = [sp.Poly(1, x, domain=sp.QQ)]
    for polynomial in polynomials[1:]:
        left, right, new_gcd = sp.gcdex(gcd, polynomial)
        cofactors = [
            sp.Poly(left.as_expr() * cofactor.as_expr(), x, domain=sp.QQ)
            for cofactor in cofactors
        ] + [sp.Poly(right, x, domain=sp.QQ)]
        gcd = sp.Poly(new_gcd, x, domain=sp.QQ)
    quotient = sp.exquo(gcd, expected)
    assert quotient.degree() == 0 and quotient.nth(0) != 0
    scalar = sp.Rational(quotient.nth(0))
    denominator = 1
    for coefficient in [
        value
        for cofactor in cofactors
        for value in cofactor.all_coeffs()
    ] + [scalar]:
        denominator = math.lcm(denominator, int(sp.denom(coefficient)))
    integer_cofactors = [
        sp.Poly(cofactor.as_expr() * denominator, x, domain=sp.ZZ)
        for cofactor in cofactors
    ]
    target_scale = int(scalar * denominator)
    combination = sum(
        (
            cofactor * polynomial
            for cofactor, polynomial in zip(integer_cofactors, polynomials)
        ),
        sp.Poly(0, x, domain=sp.ZZ),
    )
    assert combination == sp.Poly(
        expected.as_expr() * target_scale, x, domain=sp.ZZ
    )
    return (
        [low_coefficients(cofactor, x) for cofactor in integer_cofactors],
        target_scale,
    )


def emit(puncture_j: int, puncture_i: int) -> str:
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
    selected = basis[:2]
    r = int(result["r"])
    x, y = sp.symbols("x y")
    block = lambda z: sp.prod(z + h for h in range(1, 6))
    curve = sp.expand(block(y) - 4 * block(x))
    curve_rows = [
        [-360, -1096, -900, -340, -60, -4],
        [274],
        [225],
        [85],
        [15],
        [1],
    ]
    section_dense = [section_rows(vector, 5, r) for vector in selected]
    section_exprs = [sympy_section(rows, x, y) for rows in section_dense]
    resultants = [
        resultant_poly(
            exact_curve_section_resultant(
                exact_section_coefficients(vector, 5, r), 5
            ),
            x,
        )
        for vector in selected
    ]
    elimination = [
        cleared_elimination_cofactors(
            section_expr, curve, resultant, x, y
        )
        for section_expr, resultant in zip(section_exprs, resultants)
    ]
    expected = sp.Poly(
        sp.prod(
            (x + h) ** (68 if h == puncture_j else 85)
            for h in range(1, 6)
        ),
        x,
        domain=sp.ZZ,
    )
    left_bezout, right_bezout, target_scale = cleared_univariate_bezout(
        resultants[0], resultants[1], expected, x
    )

    prefix = f"k5P{puncture_j}{puncture_i}"
    lines = [
        "/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/",
        f"import ErdosProblems.Erdos686K5P{puncture_j}{puncture_i}Certificate",
        "",
        "namespace Erdos686",
        "namespace Erdos686Variant",
        "",
        "/-! Generated exact non-common-zero certificate. -/",
        "",
        "set_option maxRecDepth 100000",
        "set_option maxHeartbeats 0",
        "",
        f"def {prefix}CurveDense : DenseBivariateIntPolynomial :=",
        lean_rows(curve_rows),
        "",
        f"theorem {prefix}CurveDense_toSparse :",
        f"    denseBivariateToSparse {prefix}CurveDense = k5CurveTerms := by",
        "  decide +kernel",
        "",
    ]
    for index in range(2):
        dense_name = f"{prefix}Section{index}Dense"
        sparse_name = f"{prefix}Section{index}"
        section_cofactor, curve_cofactor = elimination[index]
        result_name = f"{prefix}Resultant{index}"
        lines.extend(
            [
                f"def {dense_name} : DenseBivariateIntPolynomial :=",
                lean_rows(section_dense[index]),
                "",
                f"theorem {dense_name}_toSparse :",
                f"    denseBivariateToSparse {dense_name} = {sparse_name} := by",
                "  decide +kernel",
                "",
                f"def {prefix}SectionCofactor{index} : "
                "DenseBivariateIntPolynomial :=",
                lean_rows(section_cofactor),
                "",
                f"def {prefix}CurveCofactor{index} : "
                "DenseBivariateIntPolynomial :=",
                lean_rows(curve_cofactor),
                "",
                f"def {result_name} : DenseIntPolynomial :=",
                lean_row(low_coefficients(resultants[index], x)),
                "",
                "set_option maxRecDepth 100000 in",
                "set_option maxHeartbeats 0 in",
                f"theorem {prefix}EliminationIdentity{index} :",
                "    denseBivariateIsZero",
                "      (denseBivariateSub",
                "        (denseBivariateAdd",
                f"          (denseBivariateMul {prefix}SectionCofactor{index}",
                f"            {dense_name})",
                f"          (denseBivariateMul {prefix}CurveCofactor{index}",
                f"            {prefix}CurveDense))",
                f"        [{result_name}]) := by",
                "  unfold denseBivariateIsZero",
                "  native_decide",
                "",
            ]
        )
    lines.extend(
        [
            f"def {prefix}Expected : DenseIntPolynomial :=",
            f"  denseIntMul (denseIntPow [1, 1] "
            f"{68 if puncture_j == 1 else 85})",
            f"    (denseIntMul (denseIntPow [2, 1] "
            f"{68 if puncture_j == 2 else 85})",
            f"      (denseIntMul (denseIntPow [3, 1] "
            f"{68 if puncture_j == 3 else 85})",
            f"        (denseIntMul (denseIntPow [4, 1] "
            f"{68 if puncture_j == 4 else 85})",
            f"          (denseIntPow [5, 1] "
            f"{68 if puncture_j == 5 else 85}))))",
            "",
            f"def {prefix}ResultantCofactor0 : DenseIntPolynomial :=",
            lean_row(left_bezout),
            "",
            f"def {prefix}ResultantCofactor1 : DenseIntPolynomial :=",
            lean_row(right_bezout),
            "",
            f"def {prefix}BezoutScale : ℤ :=",
            lean_int(target_scale),
            "",
            "set_option maxRecDepth 100000 in",
            "set_option maxHeartbeats 0 in",
            f"theorem {prefix}ResultantBezoutIdentity :",
            "    denseIntIsZero",
            "      (denseIntSub",
            "        (denseIntAdd",
            f"          (denseIntMul {prefix}ResultantCofactor0",
            f"            {prefix}Resultant0)",
            f"          (denseIntMul {prefix}ResultantCofactor1",
            f"            {prefix}Resultant1))",
            f"        (denseIntScale {prefix}BezoutScale",
            f"          {prefix}Expected)) := by",
            "  unfold denseIntIsZero",
            "  native_decide",
            "",
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
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.write_text(emit(args.j, args.i))


if __name__ == "__main__":
    main()
