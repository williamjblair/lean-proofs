#!/usr/bin/env python3
"""Search for an explicit base-locus certificate for puncture jet sections.

For a saturated integral basis F_0,...,F_g on Phi(X,Y)=0, every common affine
zero has an X-coordinate in the gcd of Res_Y(Phi,F_i).  Computing that gcd
modulo a prime is a cheap first audit: if it is supported only at
X=-1,...,-k, then the sections cannot vanish simultaneously at any positive
integral point.  An eventual Lean certificate should replace this experiment
by exact Bezout identities over Z[X].
"""

from __future__ import annotations

import argparse
import json

import sympy as sp

try:
    from flint import fmpz_poly
except ImportError:
    fmpz_poly = None

from jet_puncture_basis_experiment import construct


def poly_product(left: list[int], right: list[int]) -> list[int]:
    result = [0] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            result[i + j] += a * b
    return result


def exact_section_coefficients(
    coefficients: list[int], k: int, r: int,
) -> list[object]:
    assert fmpz_poly is not None
    result: list[object] = []
    index = 0
    for b in range(k):
        width = r - b + 1
        result.append(fmpz_poly(coefficients[index:index + width]))
        index += width
    assert index == len(coefficients)
    return result


def bareiss_determinant(matrix: list[list[object]]) -> object:
    """Fraction-free determinant over Z[X], with exact-division audits."""
    assert fmpz_poly is not None
    a = [row[:] for row in matrix]
    n = len(a)
    previous = fmpz_poly([1])
    sign = 1
    for pivot_index in range(n - 1):
        if not a[pivot_index][pivot_index]:
            swap = next(
                row for row in range(pivot_index + 1, n)
                if a[row][pivot_index]
            )
            a[pivot_index], a[swap] = a[swap], a[pivot_index]
            sign = -sign
        pivot = a[pivot_index][pivot_index]
        for row in range(pivot_index + 1, n):
            for column in range(pivot_index + 1, n):
                numerator = (
                    pivot * a[row][column]
                    - a[row][pivot_index] * a[pivot_index][column]
                )
                quotient, remainder = divmod(numerator, previous)
                assert not remainder
                a[row][column] = quotient
        previous = pivot
    determinant = a[-1][-1]
    return -determinant if sign < 0 else determinant


def exact_curve_section_resultant(
    section: list[object], k: int,
) -> object:
    """Norm determinant for F in Z[X,Y]/(B_k(Y)-4B_k(X))."""
    assert fmpz_poly is not None
    block = [1]
    for h in range(1, k + 1):
        block = poly_product(block, [h, 1])
    block_x = fmpz_poly(block)
    curve_lower = [fmpz_poly([-coefficient]) for coefficient in block[:-1]]
    curve_lower[0] += 4 * block_x

    # reduced_powers[t] is Y^t in the basis 1,Y,...,Y^(k-1).
    zero = fmpz_poly([])
    one = fmpz_poly([1])
    reduced_powers: list[list[object]] = [
        [one if row == exponent else zero for row in range(k)]
        for exponent in range(k)
    ]
    for exponent in range(k, 2 * k - 1):
        shift = exponent - k
        vector = [zero for _ in range(k)]
        for b in range(k):
            scalar = curve_lower[b]
            source = reduced_powers[shift + b]
            vector = [old + scalar * value for old, value in zip(vector, source)]
        reduced_powers.append(vector)

    multiplication = [[zero for _ in range(k)] for _ in range(k)]
    for column in range(k):
        for b, coefficient in enumerate(section):
            for row, value in enumerate(reduced_powers[column + b]):
                multiplication[row][column] += coefficient * value
    return bareiss_determinant(multiplication)


def section_polynomial(
    coefficients: list[int], k: int, r: int, x: sp.Symbol, y: sp.Symbol,
    modulus: int,
) -> sp.Poly:
    terms: dict[tuple[int, int], int] = {}
    index = 0
    for b in range(k):
        for a in range(r - b + 1):
            value = coefficients[index] % modulus
            index += 1
            if value:
                terms[(a, b)] = value
    assert index == len(coefficients)
    return sp.Poly.from_dict(terms, (x, y), modulus=modulus)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, default=5)
    parser.add_argument("--j", type=int, default=1)
    parser.add_argument("--i", type=int, default=1)
    parser.add_argument("--s", type=int, default=1)
    parser.add_argument("--prime", type=int, default=101)
    parser.add_argument("--exact", action="store_true")
    args = parser.parse_args()

    result = construct(
        args.k, args.j, args.i, args.s,
        basis_mode="lagrange",
        emit_standard_basis=True,
    )
    basis = result["standard_basis"]
    assert isinstance(basis, list)
    r = int(result["r"])

    if args.exact:
        if fmpz_poly is None:
            raise RuntimeError("--exact requires python-flint")
        exact_sections = [
            exact_section_coefficients(vector, args.k, r)
            for vector in basis
        ]
        resultants = [
            exact_curve_section_resultant(section, args.k)
            for section in exact_sections
        ]
        resultant_gcd = resultants[0]
        prefix_gcd_degrees: list[int] = []
        for resultant in resultants[1:]:
            resultant_gcd = resultant_gcd.gcd(resultant)
            prefix_gcd_degrees.append(resultant_gcd.degree())
        grid = fmpz_poly([1])
        for h in range(1, args.k + 1):
            grid *= fmpz_poly([h, 1])
        remaining = resultant_gcd
        full_grid_multiplicity = 0
        while remaining.degree() >= grid.degree():
            quotient, remainder = divmod(remaining, grid)
            if remainder:
                break
            remaining = quotient
            full_grid_multiplicity += 1
        extra: dict[str, int] = {}
        for h in range(1, args.k + 1):
            linear = fmpz_poly([h, 1])
            multiplicity = 0
            while remaining.degree() >= 1:
                quotient, remainder = divmod(remaining, linear)
                if remainder:
                    break
                remaining = quotient
                multiplicity += 1
            extra[str(h)] = multiplicity
        print(json.dumps({
            "k": args.k,
            "puncture": [args.j, args.i],
            "basis_size": len(exact_sections),
            "curve_section_resultant_degrees": [value.degree() for value in resultants],
            "resultant_max_coefficient_digits": [
                max(len(str(abs(int(coefficient)))) for coefficient in value.coeffs())
                for value in resultants
            ],
            "resultant_gcd_degree": resultant_gcd.degree(),
            "prefix_gcd_degrees": prefix_gcd_degrees,
            "full_grid_factor_multiplicity": full_grid_multiplicity,
            "extra_grid_linear_multiplicities": extra,
            "remaining_factor_degree": remaining.degree(),
            "remaining_factor": str(remaining),
        }, indent=2))
        return

    x, y = sp.symbols("x y")
    polynomials = [
        section_polynomial(vector, args.k, r, x, y, args.prime)
        for vector in basis
    ]

    block_x = sp.prod(x + h for h in range(1, args.k + 1))
    block_y = sp.prod(y + h for h in range(1, args.k + 1))
    curve = sp.Poly(block_y - 4 * block_x, (x, y), modulus=args.prime)
    resultant_gcd: sp.Poly | None = None
    resultant_degrees: list[int] = []
    for polynomial in polynomials:
        resultant_expression = sp.resultant(curve.as_expr(), polynomial.as_expr(), y)
        resultant = sp.Poly(resultant_expression, x, modulus=args.prime)
        resultant_degrees.append(resultant.degree())
        resultant_gcd = (
            resultant.monic() if resultant_gcd is None
            else sp.gcd(resultant_gcd, resultant).monic()
        )

    assert resultant_gcd is not None
    grid = sp.Poly(block_x, x, modulus=args.prime)
    remaining = resultant_gcd
    grid_multiplicity = 0
    while remaining.degree() >= grid.degree() and sp.rem(remaining, grid).is_zero:
        remaining = sp.quo(remaining, grid).monic()
        grid_multiplicity += 1
    extra_grid_multiplicities: dict[str, int] = {}
    for h in range(1, args.k + 1):
        linear = sp.Poly(x + h, x, modulus=args.prime)
        multiplicity = 0
        while remaining.degree() >= 1 and sp.rem(remaining, linear).is_zero:
            remaining = sp.quo(remaining, linear).monic()
            multiplicity += 1
        extra_grid_multiplicities[str(h)] = multiplicity

    print(json.dumps({
        "k": args.k,
        "puncture": [args.j, args.i],
        "prime": args.prime,
        "basis_size": len(polynomials),
        "curve_section_resultant_degrees": resultant_degrees,
        "resultant_gcd_degree": resultant_gcd.degree(),
        "full_grid_factor_multiplicity": grid_multiplicity,
        "extra_grid_linear_multiplicities": extra_grid_multiplicities,
        "remaining_factor_degree": remaining.degree(),
        "remaining_factor": str(remaining.as_expr()),
    }, indent=2))


if __name__ == "__main__":
    main()
