#!/usr/bin/env python3
"""Independent exact audit for the reflected second lift.

This verifier imports no producer module.  It reconstructs the local Taylor
coefficients from integer products, checks the cubic congruence exhaustively,
replays both cleaned three-owner compositions, and builds a target-range
congruence-only pseudo-fixture with an explicitly 16-smooth loss ``g=2^80``.
"""

from __future__ import annotations

from itertools import combinations
from math import gcd, prod
import json


def block_product(k: int, n: int) -> int:
    return prod(n + j for j in range(1, k + 1))


def local_cofactor(k: int, owner: int, z: int) -> int:
    return prod(z + j - owner for j in range(1, k + 1) if j != owner)


def local_coefficients(k: int, owner: int) -> tuple[int, int]:
    offsets = [j - owner for j in range(1, k + 1) if j != owner]
    constant = prod(offsets)
    linear = sum(
        prod(offsets[:position] + offsets[position + 1 :])
        for position in range(len(offsets))
    )
    return constant, linear


def local_quadratic(k: int, owner: int) -> int:
    offsets = [j - owner for j in range(1, k + 1) if j != owner]
    return sum(
        prod(
            offset
            for position, offset in enumerate(offsets)
            if position not in (left, right)
        )
        for left, right in combinations(range(len(offsets)), 2)
    )


def divisors(value: int) -> tuple[int, ...]:
    if value <= 0:
        raise ValueError("positive divisor source required")
    small: list[int] = []
    large: list[int] = []
    candidate = 1
    while candidate * candidate <= value:
        if value % candidate == 0:
            small.append(candidate)
            if candidate * candidate != value:
                large.append(value // candidate)
        candidate += 1
    return tuple(small + large[::-1])


def crt(congruences: list[tuple[int, int]]) -> tuple[int, int]:
    value = 0
    modulus = 1
    for residue, next_modulus in congruences:
        if gcd(modulus, next_modulus) != 1:
            raise ValueError("CRT moduli must be pairwise coprime")
        correction = ((residue - value) * pow(modulus, -1, next_modulus))
        correction %= next_modulus
        value += correction * modulus
        modulus *= next_modulus
        value %= modulus
    return value, modulus


def is_prime(value: int) -> bool:
    if value < 2:
        return False
    candidate = 2
    while candidate * candidate <= value:
        if value % candidate == 0:
            return False
        candidate += 1
    return True


def reflection_audit() -> dict[str, int]:
    checked = 0
    for k in range(1, 21):
        for owner in range(1, k + 1):
            reflected = k + 1 - owner
            sign = -1 if (k - 1) % 2 else 1
            for z in range(-10, 11):
                assert local_cofactor(k, reflected, z) == (
                    sign * local_cofactor(k, owner, -z)
                )
                checked += 1
    return {"cofactor_reflection_rows": checked}


def cubic_grid_audit() -> dict[str, int]:
    accepted = 0
    rejected_square_premise = 0
    exact_equations = 0
    for k in range(2, 13):
        for n in range(0, 31):
            for d in range(0, 24):
                for owner in range(1, k + 1):
                    lower = n + owner
                    upper = n + d + (k + 1 - owner)
                    for h in divisors(gcd(lower, upper)):
                        x = lower // h
                        m = (lower + upper) // h
                        residual = m + 3 * x if k % 2 == 0 else 5 * x - m
                        if residual < 0 or residual % h:
                            rejected_square_premise += 1
                            continue
                        a = residual // h
                        constant, linear = local_coefficients(k, owner)
                        obstruction = (
                            constant * a - 12 * linear * x * x
                            if k % 2 == 0
                            else constant * a + 20 * linear * x * x
                        )
                        equation_error = (
                            block_product(k, n + d) - 4 * block_product(k, n)
                        )
                        assert (
                            equation_error + h * h * obstruction
                        ) % (h**3) == 0
                        if equation_error == 0:
                            assert obstruction % h == 0
                            quadratic = local_quadratic(k, owner)
                            third = (
                                obstruction
                                + h
                                * (
                                    8 * linear * a * x
                                    - 60 * quadratic * x**3
                                )
                                if k % 2 == 0
                                else obstruction
                                - h
                                * (
                                    8 * linear * a * x
                                    + 60 * quadratic * x**3
                                )
                            )
                            assert third % (h**2) == 0
                            exact_equations += 1
                        accepted += 1
    assert accepted == 66_910
    return {
        "cubic_congruence_rows": accepted,
        "rejected_square_premise_rows": rejected_square_premise,
        "exact_equation_rows": exact_equations,
    }


def no_inverse_boundary_audit() -> dict[str, bool]:
    # Even bridge with 3 | P.  The proof multiplies by 3; it never cancels 3.
    P, Q, R, g, x, a, C, D = 6, 5, 7, 3, 1, 18, 1, 1
    assert P * a == g * Q * R + 3 * x
    assert (C * a - 12 * D * x * x) % P == 0
    assert (3 * C * a - 4 * D * g * g * Q * Q * R * R) % P == 0

    # Odd bridge with 5 | P.  Again multiplication, not inversion, is valid.
    P, Q, R, g, x, a, C, D = 10, 3, 7, 5, 23, 1, 10, 1
    assert P * a == 5 * x - g * Q * R
    assert (C * a + 20 * D * x * x) % P == 0
    assert (5 * C * a + 4 * D * g * g * Q * Q * R * R) % P == 0
    return {
        "even_bridge_survives_three_dividing_modulus": True,
        "odd_bridge_survives_five_dividing_modulus": True,
    }


def build_even_pseudo_fixture() -> dict[str, object]:
    """Build an unbounded-regime fixture satisfying every banked congruence.

    It deliberately fails the full block equation.  Thus it falsifies any
    attempt to promote the reflected lifts and their cyclic composition into
    a congruence-only Target 2 proof.
    """

    k = 16
    components = (17, 19, 23)
    owners = (1, 7, 16)
    assert all(is_prime(component) and component > k for component in components)
    assert all(gcd(left, right) == 1 for left, right in combinations(components, 2))
    center_product = prod(components)
    g = 2**80
    center = g * center_product

    square_residues: list[tuple[int, int]] = []
    for component, owner in zip(components, owners, strict=True):
        modulus = component**2
        residue = -owner - center * pow(3, -1, modulus)
        square_residues.append((residue % modulus, modulus))
    n0, modulus = crt(square_residues)
    assert modulus == center_product**2

    # Moving n by u*M^2 preserves the square residual.  Solve the next lift
    # independently modulo each cleaned component, then combine with CRT.
    u_residues: list[tuple[int, int]] = []
    for component, owner in zip(components, owners, strict=True):
        constant, linear = local_coefficients(k, owner)
        x0 = (n0 + owner) // component
        a0 = (center + 3 * (n0 + owner)) // (component**2)
        a_step = 3 * (center_product // component) ** 2
        numerator = 12 * linear * x0 * x0 - constant * a0
        denominator = constant * a_step
        u_residue = numerator * pow(denominator, -1, component)
        u_residues.append((u_residue % component, component))
    u0, u_modulus = crt(u_residues)
    assert u_modulus == center_product

    # One more owner-adic digit: write u=u0+t*M.  For each component the
    # quotient of the third obstruction by H is affine in t modulo H.
    t_residues: list[tuple[int, int]] = []
    hensel_rows: list[dict[str, int]] = []
    for component, owner in zip(components, owners, strict=True):
        constant, linear = local_coefficients(k, owner)
        quadratic = local_quadratic(k, owner)
        quotients: list[int] = []
        solutions: list[int] = []
        for t_candidate in range(component):
            u_candidate = u0 + t_candidate * center_product
            n_candidate = n0 + u_candidate * center_product**2
            x_candidate = (n_candidate + owner) // component
            a_candidate = (
                center + 3 * (n_candidate + owner)
            ) // (component**2)
            third_candidate = (
                constant * a_candidate
                - 12 * linear * x_candidate**2
                + component
                * (
                    8 * linear * a_candidate * x_candidate
                    - 60 * quadratic * x_candidate**3
                )
            )
            assert third_candidate % component == 0
            quotients.append((third_candidate // component) % component)
            if third_candidate % (component**2) == 0:
                solutions.append(t_candidate)
        assert len(solutions) == 1
        derivative = (quotients[1] - quotients[0]) % component
        assert gcd(derivative, component) == 1
        t_residues.append((solutions[0], component))
        hensel_rows.append(
            {
                "component": component,
                "owner": owner,
                "lifted_t_residue": solutions[0],
                "derivative": derivative,
            }
        )
    t0, t_modulus = crt(t_residues)
    assert t_modulus == center_product

    # Moving t by M changes n by M^4 and preserves the third digit.  Choose
    # the first such member with the exact target ratio 9d<n.
    base_u = u0 + t0 * center_product
    base_n = n0 + base_u * center_product**2
    step = center_product**4
    lower_numerator = 9 * (center - k - 1) - 19 * base_n
    s = max(0, lower_numerator // (19 * step) + 1)
    n = base_n + s * step
    d = center - 2 * n - k - 1
    assert k <= d and 9 * d < n
    assert center == 2 * n + d + k + 1

    rows: list[dict[str, int]] = []
    for component, owner in zip(components, owners, strict=True):
        constant, linear = local_coefficients(k, owner)
        quadratic = local_quadratic(k, owner)
        lower = n + owner
        upper = center - lower
        x = lower // component
        m = center // component
        a = (m + 3 * x) // component
        raw = constant * a - 12 * linear * x * x
        transformed = (
            3 * constant * a
            - 4
            * linear
            * g**2
            * (center_product // component) ** 2
        )
        third = raw + component * (
            8 * linear * a * x - 60 * quadratic * x**3
        )
        G = center // component
        cleaned_third = (
            27 * constant * a
            - 36 * linear * G**2
            + 60 * quadratic * component * G**3
        )
        assert lower % component == 0 and upper % component == 0
        assert (m + 3 * x) % component == 0
        assert raw % component == 0
        assert transformed % component == 0
        assert third % (component**2) == 0
        assert cleaned_third % (component**2) == 0
        assert component**2 * a == center + 3 * lower
        rows.append(
            {
                "component": component,
                "owner": owner,
                "constant": constant,
                "linear": linear,
                "quadratic": quadratic,
                "x": x,
                "a": a,
                "raw_obstruction": raw,
                "transformed_obstruction": transformed,
                "third_obstruction": third,
                "cleaned_third_obstruction": cleaned_third,
            }
        )

    for left, right in combinations(rows, 2):
        difference = (
            left["a"] * left["component"] ** 2
            - right["a"] * right["component"] ** 2
        )
        assert difference == 3 * (left["owner"] - right["owner"])

    abc = prod(row["a"] for row in rows)
    for position, row in enumerate(rows):
        other_rows = [candidate for index, candidate in enumerate(rows) if index != position]
        delta_left = row["owner"] - other_rows[0]["owner"]
        delta_right = row["owner"] - other_rows[1]["owner"]
        composed = 3 * (
            row["constant"] * abc
            - 12 * row["linear"] * g**2 * delta_left * delta_right
        )
        assert composed % row["component"] == 0
        row["composed_obstruction"] = composed
        composed_third = 27 * (
            row["constant"] * abc
            - 12 * row["linear"] * g**2 * delta_left * delta_right
            + 20
            * row["quadratic"]
            * g**3
            * center_product
            * delta_left
            * delta_right
        )
        assert composed_third % (row["component"] ** 2) == 0
        row["composed_third_obstruction"] = composed_third

    assert all(row["component"] ** 2 * row["a"] <= 7 * n for row in rows)
    assert 8 * abc < 343 * g**2 * center
    lower_product = block_product(k, n)
    upper_product = block_product(k, n + d)
    assert upper_product != 4 * lower_product

    return {
        "k": k,
        "n": n,
        "d": d,
        "g": g,
        "g_factorization": {"2": 80},
        "center": center,
        "components": list(components),
        "owners": list(owners),
        "crt_n0": n0,
        "crt_u0": u0,
        "hensel_rows": hensel_rows,
        "crt_t0": t0,
        "crt_s": s,
        "rows": rows,
        "abc": abc,
        "target_ratio": 9 * d < n,
        "block_equation": False,
        "block_error_digits": len(str(abs(upper_product - 4 * lower_product))),
    }


def run_audit() -> dict[str, object]:
    result: dict[str, object] = {}
    result.update(reflection_audit())
    result.update(cubic_grid_audit())
    result.update(no_inverse_boundary_audit())
    result["pseudo_fixture"] = build_even_pseudo_fixture()
    return result


if __name__ == "__main__":
    print(json.dumps(run_audit(), indent=2, sort_keys=True))
