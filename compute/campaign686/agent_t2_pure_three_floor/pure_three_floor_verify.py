#!/usr/bin/env python3
"""Exact audit for the pure three-owner floor elimination.

This file imports no producer module.  It reconstructs the first three local
cofactor coefficients, enumerates a finite prime/component grid, and checks
the two affine eliminations using integer arithmetic only.

The finite scans are diagnostics, not universal proofs.  In particular, the
two displayed CRT fixtures intentionally omit one necessary layer each:

* the square fixtures fail the reflected third composition and the equation;
* the affine CRT fixtures satisfy the pinned floor and all three new affine
  congruences but fail the square lifts and the equation.
"""

from __future__ import annotations

from itertools import combinations
from math import gcd, isqrt, prod


EVEN_COMPONENTS = (397, 311, 353)
EVEN_BASE_OWNERS = (1, 10, 150)
EVEN_BASE_H = 34_541
EVEN_BASE_N = 21_774_655

ODD_COMPONENTS = (487, 293, 313)
ODD_BASE_OWNERS = (191, 1, 222)
ODD_BASE_H = 424_559
ODD_BASE_N = 22_118_862


def is_prime(value: int) -> bool:
    return value > 1 and all(value % p for p in range(2, isqrt(value) + 1))


def block_product(k: int, n: int) -> int:
    return prod(n + i for i in range(1, k + 1))


def endpoint_window(k: int, n: int, d: int) -> bool:
    return (
        (n + d + k) ** k <= 4 * (n + k) ** k
        and 4 * (n + 1) ** k <= (n + d + 1) ** k
    )


def local_coefficients_mod(k: int, owner: int, modulus: int) -> tuple[int, int, int]:
    """Return C,D,E modulo ``modulus`` by direct polynomial multiplication."""

    constant, linear, quadratic = 1, 0, 0
    for index in range(1, k + 1):
        if index == owner:
            continue
        offset = index - owner
        constant, linear, quadratic = (
            offset * constant % modulus,
            (constant + offset * linear) % modulus,
            (linear + offset * quadratic) % modulus,
        )
    return constant, linear, quadratic


def third_residue(
    k: int,
    components: tuple[int, int, int],
    owners: tuple[int, int, int],
    center: int,
    t: int,
) -> tuple[int, int, int]:
    residues: list[int] = []
    for component, owner in zip(components, owners, strict=True):
        modulus = component**2
        constant, linear, quadratic = local_coefficients_mod(k, owner, modulus)
        other = tuple(index for index in owners if index != owner)
        delta = (owner - other[0]) * (owner - other[1])
        if k % 2 == 0:
            value = (
                9 * constant * t
                - 108 * linear * delta
                + 180 * quadratic * delta * center
            )
        else:
            value = (
                5 * constant * t
                + 100 * linear * delta
                - 60 * quadratic * delta * center
            )
        residues.append(value % modulus)
    return tuple(residues)  # type: ignore[return-value]


def affine_residue(
    k: int,
    components: tuple[int, int, int],
    owners: tuple[int, int, int],
    h: int,
    r: int,
) -> tuple[int, int, int]:
    residues: list[int] = []
    for component, owner in zip(components, owners, strict=True):
        modulus = component**2
        constant, linear, quadratic = local_coefficients_mod(k, owner, modulus)
        other = tuple(index for index in owners if index != owner)
        delta = (owner - other[0]) * (owner - other[1])
        e = h - 2 * owner
        if k % 2 == 0:
            value = (
                5 * constant * r
                + 45 * constant * e
                + 60 * delta * (quadratic * e - linear)
            )
        else:
            value = (
                3 * constant * r
                + 15 * constant * e
                + 60 * delta * (linear - quadratic * e)
            )
        residues.append(value % modulus)
    return tuple(residues)  # type: ignore[return-value]


def reflected_values(
    k: int, n: int, center: int, owners: tuple[int, int, int]
) -> tuple[int, int, int]:
    if k % 2 == 0:
        return tuple(center + 3 * (n + owner) for owner in owners)  # type: ignore[return-value]
    return tuple(5 * (n + owner) - center for owner in owners)  # type: ignore[return-value]


def check_square_fixture(
    k: int,
    components: tuple[int, int, int],
    owners: tuple[int, int, int],
    h: int,
    n: int,
) -> dict[str, object]:
    center = prod(components)
    d = h - k - 1
    assert center == 2 * n + d + k + 1
    assert k <= d and 9 * d < n and k * d < 5 * n
    assert len(set(owners)) == 3
    assert all(is_prime(component) and component > k for component in components)
    assert all(gcd(left, right) == 1 for left, right in combinations(components, 2))
    values = reflected_values(k, n, center, owners)
    assert all(
        value > 0 and value % component**2 == 0
        for value, component in zip(values, components, strict=True)
    )
    cofactors = tuple(
        value // component**2
        for value, component in zip(values, components, strict=True)
    )
    t = prod(cofactors)
    floor, r = divmod(t, center)
    assert floor == (15 if k % 2 == 0 else 3)
    assert 0 < r < center
    residues = third_residue(k, components, owners, center, t)
    affine = affine_residue(k, components, owners, h, r)
    # The Lean elimination says zero third residue implies zero affine
    # residue.  The stronger pointwise unit equivalence also holds here.
    assert tuple(value == 0 for value in residues) == tuple(
        value == 0 for value in affine
    )
    return {
        "k": k,
        "components": components,
        "owners": owners,
        "h": h,
        "n": n,
        "d": d,
        "cofactors": cofactors,
        "t": t,
        "r": r,
        "third_residues": residues,
        "endpoint_window": endpoint_window(k, n, d),
        "equation": block_product(k, n + d) == 4 * block_product(k, n),
    }


def weak_square_scan(k: int) -> tuple[int, list[dict[str, object]]]:
    """Exhaust the prime triples in ``k < p < 501`` under the weak bounds.

    The enumeration starts with the largest component.  Its square congruence
    pins ``h`` to one residue class per owner; the loop then checks every such
    representative in the exact target-inequality interval.  Thus no owner
    triple in the finite grid is skipped.
    """

    primes = tuple(value for value in range(k + 1, 501) if is_prime(value))
    triple_count = 0
    fixtures: list[dict[str, object]] = []
    for small, middle, large in combinations(primes, 3):
        triple_count += 1
        center = small * middle * large
        lower_h = 2 * k + 1
        upper_nine = (center + 18 * (k + 1) - 1) // 19
        upper_kd = (5 * center + 2 * k * (k + 1) - 1) // (2 * k + 5)
        upper_h = min(upper_nine, upper_kd)
        modulus = large**2
        if k % 2 == 0:
            shift = 5 * center * pow(3, -1, modulus) % modulus
        else:
            shift = 3 * center * pow(5, -1, modulus) % modulus

        for large_owner in range(1, k + 1):
            h = (2 * large_owner + shift) % modulus
            if h < lower_h:
                h += ((lower_h - h + modulus - 1) // modulus) * modulus
            while h <= upper_h:
                if (h - center) % 2 == 0:
                    owners = [large_owner]
                    for component in (small, middle):
                        owner = h * pow(2, -1, component) % component
                        if not 1 <= owner <= k:
                            break
                        square_numerator = (
                            3 * (h - 2 * owner) - 5 * center
                            if k % 2 == 0
                            else 5 * (h - 2 * owner) - 3 * center
                        )
                        if square_numerator % component**2:
                            break
                        owners.append(owner)
                    else:
                        owner_tuple = tuple(owners)
                        if len(set(owner_tuple)) == 3:
                            n = (center - h) // 2
                            fixture = check_square_fixture(
                                k,
                                (large, small, middle),
                                owner_tuple,  # type: ignore[arg-type]
                                h,
                                n,
                            )
                            fixtures.append(fixture)
                h += modulus
    return triple_count, fixtures


def translated_family_audit() -> dict[str, object]:
    """Replay both exact square families through every ``220 <= k <= 240``."""

    rows: list[dict[str, object]] = []
    for k in range(220, 241):
        if k % 2 == 0:
            count = k - 149
            components = EVEN_COMPONENTS
            base_owners = EVEN_BASE_OWNERS
            base_h, base_n = EVEN_BASE_H, EVEN_BASE_N
        elif k >= 223:
            count = k - 221
            components = ODD_COMPONENTS
            base_owners = ODD_BASE_OWNERS
            base_h, base_n = ODD_BASE_H, ODD_BASE_N
        else:
            count = 0
            components = EVEN_COMPONENTS
            base_owners = EVEN_BASE_OWNERS
            base_h, base_n = EVEN_BASE_H, EVEN_BASE_N
        component_zero = 0
        for shift in range(count):
            fixture = check_square_fixture(
                k,
                components,
                tuple(owner + shift for owner in base_owners),  # type: ignore[arg-type]
                base_h + 2 * shift,
                base_n - shift,
            )
            component_zero += sum(value == 0 for value in fixture["third_residues"])
        rows.append(
            {"k": k, "square_rows": count, "zero_third_components": component_zero}
        )
    assert sum(int(row["square_rows"]) for row in rows) == 981
    assert all(row["zero_third_components"] == 0 for row in rows)
    return {"rows": rows, "total_square_rows": 981}


def crt(congruences: list[tuple[int, int]]) -> tuple[int, int]:
    value, modulus = 0, 1
    for residue, next_modulus in congruences:
        assert gcd(modulus, next_modulus) == 1
        value += (
            (residue - value) * pow(modulus, -1, next_modulus) % next_modulus
        ) * modulus
        modulus *= next_modulus
        value %= modulus
    return value, modulus


def affine_line(k: int, components: tuple[int, int, int], owners: tuple[int, int, int]) -> tuple[int, int, int]:
    """Return ``r = intercept + slope*h (mod S^2)`` for the three forms."""

    intercept_rows: list[tuple[int, int]] = []
    slope_rows: list[tuple[int, int]] = []
    for component, owner in zip(components, owners, strict=True):
        modulus = component**2
        constant, linear, quadratic = local_coefficients_mod(k, owner, modulus)
        other = tuple(index for index in owners if index != owner)
        delta = (owner - other[0]) * (owner - other[1])
        if k % 2 == 0:
            a = 5 * constant
            b = 45 * constant + 60 * delta * quadratic
            c = -2 * owner * b - 60 * delta * linear
        else:
            a = 3 * constant
            b = 15 * constant - 60 * delta * quadratic
            c = -2 * owner * b + 60 * delta * linear
        inverse = pow(a, -1, modulus)
        intercept_rows.append((-c * inverse % modulus, modulus))
        slope_rows.append((-b * inverse % modulus, modulus))
    intercept, modulus = crt(intercept_rows)
    slope, slope_modulus = crt(slope_rows)
    assert slope_modulus == modulus == prod(components) ** 2
    return intercept, slope, modulus


def affine_only_fixture_audit() -> tuple[dict[str, object], dict[str, object]]:
    fixtures = (
        (220, EVEN_COMPONENTS, (127, 61, 85), 79_117, 16_656_394),
        (223, ODD_COMPONENTS, (69, 151, 68), 266_147, 27_492_810),
    )
    output: list[dict[str, object]] = []
    for k, components, owners, h, r in fixtures:
        center = prod(components)
        n = (center - h) // 2
        d = h - k - 1
        t = (15 if k % 2 == 0 else 3) * center + r
        assert 0 < r < center
        assert k <= d and 9 * d < n and k * d < 5 * n
        assert affine_residue(k, components, owners, h, r) == (0, 0, 0)
        intercept, slope, modulus = affine_line(k, components, owners)
        assert r == (intercept + slope * h) % modulus
        values = reflected_values(k, n, center, owners)
        square_residues = tuple(
            value % component**2
            for value, component in zip(values, components, strict=True)
        )
        assert all(value != 0 for value in square_residues)
        assert block_product(k, n + d) != 4 * block_product(k, n)
        output.append(
            {
                "k": k,
                "components": components,
                "owners": owners,
                "h": h,
                "n": n,
                "d": d,
                "t": t,
                "r": r,
                "square_residues": square_residues,
                "equation": False,
            }
        )
    return output[0], output[1]


def third_only_fixture_audit() -> tuple[dict[str, object], dict[str, object]]:
    """Replay floor-plus-third fixtures that fail only the square/equation layer.

    These are stronger boundary witnesses than the affine-only fixtures: the
    exact endpoint window and the original cyclic third-composition
    congruences all hold.  They do *not* satisfy the component-square
    decompositions, so they make no claim against the simultaneous system.
    """

    fixtures = (
        (220, (233, 239, 241), (188, 71, 129), 42_505, 1_620_216),
        (223, (227, 229, 233), (76, 45, 29), 37_871, 7_122_339),
    )
    output: list[dict[str, object]] = []
    for k, components, owners, h, r in fixtures:
        center = prod(components)
        n = (center - h) // 2
        d = h - k - 1
        t = (15 if k % 2 == 0 else 3) * center + r
        assert all(is_prime(component) and component > k for component in components)
        assert all(gcd(left, right) == 1 for left, right in combinations(components, 2))
        assert 0 < r < center
        assert k <= d and 9 * d < n and k * d < 5 * n
        assert endpoint_window(k, n, d)
        assert third_residue(k, components, owners, center, t) == (0, 0, 0)
        values = reflected_values(k, n, center, owners)
        square_residues = tuple(
            value % component**2
            for value, component in zip(values, components, strict=True)
        )
        assert all(value != 0 for value in square_residues)
        assert block_product(k, n + d) != 4 * block_product(k, n)
        output.append(
            {
                "k": k,
                "components": components,
                "owners": owners,
                "h": h,
                "n": n,
                "d": d,
                "t": t,
                "r": r,
                "third_residues": (0, 0, 0),
                "square_residues": square_residues,
                "endpoint_window": True,
                "equation": False,
            }
        )
    return output[0], output[1]


def campaign_summary() -> dict[str, object]:
    triples_even, even = weak_square_scan(220)
    triples_odd, odd = weak_square_scan(223)
    assert triples_even == 17_296 and len(even) == 71
    assert triples_odd == 16_215 and len(odd) == 2
    assert all(not fixture["endpoint_window"] for fixture in even + odd)
    assert all(not fixture["equation"] for fixture in even + odd)
    assert all(
        all(value != 0 for value in fixture["third_residues"])
        for fixture in even + odd
    )
    return {
        "exhaustive_prime_triples": triples_even + triples_odd,
        "k220_square_rows": len(even),
        "k223_square_rows": len(odd),
        "square_rows_with_endpoint_window": 0,
        "square_rows_with_any_third_component": 0,
        "translated": translated_family_audit(),
        "third_only_fixtures": third_only_fixture_audit(),
        "affine_only_fixtures": affine_only_fixture_audit(),
    }


def main() -> None:
    print(campaign_summary())


if __name__ == "__main__":
    main()
