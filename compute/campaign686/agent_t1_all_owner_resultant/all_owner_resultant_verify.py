#!/usr/bin/env python3
"""Exact hostile verifier for the all-owner Vandermonde/resultant route.

The verifier deliberately reconstructs the local coefficients from

    product_{j != i} (z + j - i)

and does not import any campaign producer.  All arithmetic is over Python
integers (and ``Fraction`` for the fixed-alpha nullspace check).
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import re
import sys
from collections import Counter
from fractions import Fraction
from pathlib import Path
from typing import Callable, Iterable, Sequence


TARGET_K = (5, 7, 9, 11, 13, 15)
TARGET_CUTOFF = 10**120
RESIDUAL_FLOOR = {5: 8, 7: 12, 9: 15, 11: 20, 13: 23, 15: 29}
RESIDUAL_CEILING = {5: 14, 7: 17, 9: 23, 11: 26, 13: 29, 15: 35}
LOSS_BOUND = {
    5: 108,
    7: 1620,
    9: 136080,
    11: 1224720,
    13: 242494560,
    15: 18914575680,
}


def sign(x: int) -> int:
    return (x > 0) - (x < 0)


def product(values: Iterable[int]) -> int:
    return math.prod(values)


def poly_add(a: Sequence[int], b: Sequence[int]) -> list[int]:
    out = [0] * max(len(a), len(b))
    for i, value in enumerate(a):
        out[i] += value
    for i, value in enumerate(b):
        out[i] += value
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def poly_scale(a: Sequence[int], scalar: int) -> list[int]:
    out = [scalar * value for value in a]
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def poly_mul(a: Sequence[int], b: Sequence[int]) -> list[int]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return out


def poly_eval(a: Sequence[int], x: int) -> int:
    out = 0
    for coefficient in reversed(a):
        out = out * x + coefficient
    return out


def poly_degree(a: Sequence[int]) -> int:
    return -1 if not any(a) else len(a) - 1


def offset_coefficients(k: int, owner: int) -> tuple[int, ...]:
    """Coefficients of product_{j in [1,k],j!=owner}(z+j-owner)."""
    coefficients = [1]
    for j in range(1, k + 1):
        if j != owner:
            coefficients = poly_mul(coefficients, [j - owner, 1])
    return tuple(coefficients)


def local_coefficients(k: int, owner: int) -> tuple[int, int, int]:
    coefficients = offset_coefficients(k, owner)
    return coefficients[0], coefficients[1], coefficients[2]


def owner_delta(k: int, owner: int) -> int:
    return product(owner - j for j in range(1, k + 1) if j != owner)


def vandermonde(owners: Sequence[int]) -> int:
    return product(owners[j] - owners[i]
                   for i in range(len(owners))
                   for j in range(i + 1, len(owners)))


def bareiss_det(matrix: Sequence[Sequence[int]]) -> int:
    """Fraction-free exact determinant."""
    n = len(matrix)
    if n == 0:
        return 1
    a = [list(row) for row in matrix]
    if any(len(row) != n for row in a):
        raise ValueError("determinant matrix must be square")
    sign_factor = 1
    previous = 1
    for pivot_col in range(n - 1):
        pivot_row = next((r for r in range(pivot_col, n)
                          if a[r][pivot_col] != 0), None)
        if pivot_row is None:
            return 0
        if pivot_row != pivot_col:
            a[pivot_col], a[pivot_row] = a[pivot_row], a[pivot_col]
            sign_factor *= -1
        pivot = a[pivot_col][pivot_col]
        for i in range(pivot_col + 1, n):
            for j in range(pivot_col + 1, n):
                numerator = a[i][j] * pivot - a[i][pivot_col] * a[pivot_col][j]
                if numerator % previous:
                    raise ArithmeticError("Bareiss exact division failed")
                a[i][j] = numerator // previous
        previous = pivot
        for i in range(pivot_col + 1, n):
            a[i][pivot_col] = 0
    return sign_factor * a[-1][-1]


def primitive_vector(values: Sequence[int]) -> tuple[int, ...]:
    divisor = 0
    for value in values:
        divisor = math.gcd(divisor, abs(value))
    if divisor == 0:
        return tuple(values)
    out = [value // divisor for value in values]
    first = next(value for value in out if value)
    if first < 0:
        out = [-value for value in out]
    return tuple(out)


def circuit_for_four(k: int, owners: Sequence[int]) -> tuple[int, ...]:
    """Primitive null circuit of the raw rows (C_i,C_i D_i,C_i E_i)."""
    if len(owners) != 4:
        raise ValueError("a four-owner circuit needs four owners")
    rows = []
    for owner in owners:
        c, d_coefficient, e_coefficient = local_coefficients(k, owner)
        rows.append((c, c * d_coefficient, c * e_coefficient))
    weights = []
    for omitted in range(4):
        minor = [row for r, row in enumerate(rows) if r != omitted]
        weights.append((-1) ** omitted * bareiss_det(minor))
    return primitive_vector(weights)


def coefficient_triple_determinant(k: int, owners: Sequence[int]) -> int:
    rows = []
    for owner in owners:
        _, d_coefficient, e_coefficient = local_coefficients(k, owner)
        rows.append((1, d_coefficient, e_coefficient))
    return bareiss_det(rows)


def x_polynomial(owner: int) -> list[int]:
    """X_owner = alpha + 3*owner, coefficients low degree first."""
    return [3 * owner, 1]


def elementary_symmetric_x_polynomial(k: int, degree: int) -> list[int]:
    """e_degree(X_1,...,X_k), as a polynomial in alpha."""
    if degree < 0 or degree > k:
        return [0]
    result = [0]
    for owners in itertools.combinations(range(1, k + 1), degree):
        term = [1]
        for owner in owners:
            term = poly_mul(term, x_polynomial(owner))
        result = poly_add(result, term)
    return result


def dpoly_add(
    a: Sequence[Sequence[int]], b: Sequence[Sequence[int]]
) -> list[list[int]]:
    """Add polynomials in d whose coefficients are polynomials in alpha."""
    out = [[0] for _ in range(max(len(a), len(b)))]
    for i, coefficient in enumerate(a):
        out[i] = poly_add(out[i], coefficient)
    for i, coefficient in enumerate(b):
        out[i] = poly_add(out[i], coefficient)
    while len(out) > 1 and out[-1] == [0]:
        out.pop()
    return out


def dpoly_scale(a: Sequence[Sequence[int]], scalar: int) -> list[list[int]]:
    return [poly_scale(coefficient, scalar) for coefficient in a]


def dpoly_mul(
    a: Sequence[Sequence[int]], b: Sequence[Sequence[int]]
) -> list[list[int]]:
    out = [[0] for _ in range(len(a) + len(b) - 1)]
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] = poly_add(out[i + j], poly_mul(x, y))
    while len(out) > 1 and out[-1] == [0]:
        out.pop()
    return out


def shifted_block_dpolynomial(k: int, shift: int) -> list[list[int]]:
    """product_i (X_i + shift*d), polynomial first in d then alpha."""
    result = [[1]]
    for owner in range(1, k + 1):
        result = dpoly_mul(result, [x_polynomial(owner), [shift]])
    return result


def block_difference_dpolynomial(k: int) -> list[list[int]]:
    return dpoly_add(
        shifted_block_dpolynomial(k, 4),
        dpoly_scale(shifted_block_dpolynomial(k, 1), -4),
    )


def expected_block_difference_dpolynomial(k: int) -> list[list[int]]:
    """Exact elementary-symmetric expansion, including the d^4 tail."""
    return [
        poly_scale(elementary_symmetric_x_polynomial(k, k - power),
                   4**power - 4)
        for power in range(k + 1)
    ]


def functional_polynomial(
    owners: Sequence[int], values: Callable[[int], int]
) -> list[int]:
    """L_S(values)=det[values_i, X_i, iX_i, ..., i^(s-2)X_i]."""
    owners = tuple(owners)
    result = [0]
    for row, owner in enumerate(owners):
        other_owners = owners[:row] + owners[row + 1:]
        opposite_x_product = [1]
        for other in other_owners:
            opposite_x_product = poly_mul(opposite_x_product,
                                            x_polynomial(other))
        cofactor = ((-1) ** row) * vandermonde(other_owners) * values(owner)
        result = poly_add(result, poly_scale(opposite_x_product, cofactor))
    return result


def direct_functional_det(
    owners: Sequence[int], values: Callable[[int], int], alpha: int
) -> int:
    size = len(owners)
    matrix = []
    for owner in owners:
        x = alpha + 3 * owner
        matrix.append([values(owner)] +
                      [owner**power * x for power in range(size - 1)])
    return bareiss_det(matrix)


def normalized_obstructions(
    k: int, d: int, g: int, cofactor_product: int
) -> dict[int, tuple[int, int]]:
    """Return O_i and F_i for the complete consecutive owner grid."""
    out = {}
    for owner in range(1, k + 1):
        c, d_coefficient, e_coefficient = local_coefficients(k, owner)
        delta = owner_delta(k, owner)
        correction = (-3) ** (k - 1) * delta
        second = (3 * c * cofactor_product
                  - 4 * d_coefficient * g**2 * correction)
        third = (-3 * second
                 + 20 * e_coefficient * g**2 * d * correction)
        out[owner] = second, third
    return out


def parse_lean_coefficient_tables(repo_root: Path) -> tuple[dict, dict]:
    second_path = repo_root / "ErdosProblems/Erdos686TwoPrimeSecondLift.lean"
    third_path = repo_root / "ErdosProblems/Erdos686GlobalResidualTwoPrime.lean"
    second_text = second_path.read_text()
    third_text = third_path.read_text()
    second_pattern = re.compile(
        r"^\s*\|\s*(\d+),\s*(\d+)\s*=>\s*\((-?\d+),\s*(-?\d+)\)",
        re.MULTILINE,
    )
    third_pattern = re.compile(
        r"^\s*\|\s*(\d+),\s*(\d+)\s*=>\s*(-?\d+)\s*$",
        re.MULTILINE,
    )
    second = {(int(k), int(i)): (int(c), int(d))
              for k, i, c, d in second_pattern.findall(second_text)
              if int(k) in TARGET_K and 1 <= int(i) <= int(k)}
    third = {(int(k), int(i)): int(e)
             for k, i, e in third_pattern.findall(third_text)
             if int(k) in TARGET_K and 1 <= int(i) <= int(k)}
    return second, third


def verify_lean_tables(repo_root: Path) -> dict:
    second, third = parse_lean_coefficient_tables(repo_root)
    expected_count = sum(TARGET_K)
    mismatches = []
    for k in TARGET_K:
        for owner in range(1, k + 1):
            c, d_coefficient, e_coefficient = local_coefficients(k, owner)
            if second.get((k, owner)) != (c, d_coefficient):
                mismatches.append((k, owner, "second",
                                   second.get((k, owner)),
                                   (c, d_coefficient)))
            if third.get((k, owner)) != e_coefficient:
                mismatches.append((k, owner, "third",
                                   third.get((k, owner)), e_coefficient))
            if owner_delta(k, owner) != c:
                mismatches.append((k, owner, "delta", owner_delta(k, owner), c))
    encoded = json.dumps(
        {f"{k}:{i}": (*second[(k, i)], third[(k, i)])
         for k in TARGET_K for i in range(1, k + 1)},
        sort_keys=True,
        separators=(",", ":"),
    ).encode()
    return {
        "expected_rows": expected_count,
        "parsed_second_rows": len(second),
        "parsed_third_rows": len(third),
        "mismatches": mismatches,
        "table_sha256": hashlib.sha256(encoded).hexdigest(),
    }


def fixed_alpha_annihilator(owners: Sequence[int], alpha: int) -> tuple[Fraction, ...]:
    """A generator for annihilators of X_i*q(i), deg(q)<=s-2."""
    out = []
    for owner in owners:
        x = alpha + 3 * owner
        derivative = product(owner - other for other in owners if other != owner)
        out.append(Fraction(1, x * derivative))
    return tuple(out)


def verify_nullspace(owners: Sequence[int], alpha: int) -> dict:
    weights = fixed_alpha_annihilator(owners, alpha)
    moments = []
    for power in range(len(owners) - 1):
        moments.append(sum(weight * (alpha + 3 * owner) * owner**power
                           for owner, weight in zip(owners, weights)))
    constant_moment = sum(weights)
    expected_constant = Fraction(
        (-3) ** (len(owners) - 1),
        product(alpha + 3 * owner for owner in owners),
    )
    return {
        "annihilated_moments": [str(value) for value in moments],
        "constant_moment": str(constant_moment),
        "expected_constant_moment": str(expected_constant),
        "constant_survives": constant_moment != 0,
    }


def enumerate_row(k: int) -> dict:
    owner_grid = tuple(range(1, k + 1))

    triple_values = []
    zero_triples = []
    quotient_values = []
    for owners in itertools.combinations(owner_grid, 3):
        determinant = coefficient_triple_determinant(k, owners)
        triple_values.append(abs(determinant))
        if determinant == 0:
            zero_triples.append(owners)
        else:
            v = vandermonde(owners)
            if determinant % v:
                raise ArithmeticError("coefficient determinant is not Vandermonde-divisible")
            quotient_values.append(abs(determinant // v))

    mixed_circuits = 0
    one_sided_circuits = 0
    circuits_with_zero_weight = []
    for owners in itertools.combinations(owner_grid, 4):
        weights = circuit_for_four(k, owners)
        terms = []
        for owner, weight in zip(owners, weights):
            c, _, _ = local_coefficients(k, owner)
            terms.append(weight * (-sign(c)))
        nonzero_terms = [term for term in terms if term]
        if nonzero_terms and (all(term > 0 for term in nonzero_terms)
                              or all(term < 0 for term in nonzero_terms)):
            one_sided_circuits += 1
        else:
            mixed_circuits += 1
        if any(weight == 0 for weight in weights):
            circuits_with_zero_weight.append({
                "owners": owners,
                "weights": weights,
            })

    degree_by_size: dict[str, dict[str, int]] = {}
    subset_count = 0
    l1_failures = []
    for size in range(4, k + 1):
        counter: Counter[tuple[int, int]] = Counter()
        for owners in itertools.combinations(owner_grid, size):
            subset_count += 1
            d_poly = functional_polynomial(
                owners, lambda owner: local_coefficients(k, owner)[1])
            e_poly = functional_polynomial(
                owners, lambda owner: local_coefficients(k, owner)[2])
            counter[(poly_degree(d_poly), poly_degree(e_poly))] += 1
            l1 = functional_polynomial(owners, lambda _owner: 1)
            expected = [3 ** (size - 1) * vandermonde(owners)]
            if l1 != expected:
                l1_failures.append((owners, l1, expected))
        degree_by_size[str(size)] = {
            f"D{d_degree}:E{e_degree}": count
            for (d_degree, e_degree), count in sorted(counter.items())
        }

    full_d = functional_polynomial(
        owner_grid, lambda owner: local_coefficients(k, owner)[1])
    full_e = functional_polynomial(
        owner_grid, lambda owner: local_coefficients(k, owner)[2])
    full_vandermonde = vandermonde(owner_grid)
    expected_full_d = poly_scale(
        elementary_symmetric_x_polynomial(k, k - 2),
        3 * full_vandermonde,
    )
    expected_full_e = poly_scale(
        elementary_symmetric_x_polynomial(k, k - 3),
        9 * full_vandermonde,
    )
    block_expansion = block_difference_dpolynomial(k)
    expected_block_expansion = expected_block_difference_dpolynomial(k)
    direct_checks = []
    for alpha in (1, 10**6 + k):
        direct_checks.append({
            "alpha": alpha,
            "D_matches": poly_eval(full_d, alpha) == direct_functional_det(
                owner_grid, lambda owner: local_coefficients(k, owner)[1], alpha),
            "E_matches": poly_eval(full_e, alpha) == direct_functional_det(
                owner_grid, lambda owner: local_coefficients(k, owner)[2], alpha),
        })

    return {
        "k": k,
        "subset_count_size_4_through_k": subset_count,
        "four_circuit_count": math.comb(k, 4),
        "mixed_sign_circuits": mixed_circuits,
        "one_sided_sign_circuits": one_sided_circuits,
        "circuits_with_zero_weight": circuits_with_zero_weight,
        "zero_coefficient_triples": zero_triples,
        "min_abs_nonzero_triple_determinant": min(
            value for value in triple_values if value),
        "max_abs_triple_determinant": max(triple_values),
        "min_abs_vandermonde_quotient": min(quotient_values),
        "max_abs_vandermonde_quotient": max(quotient_values),
        "resultant_degree_distribution_by_subset_size": degree_by_size,
        "L_one_identity_failures": l1_failures,
        "full_grid_D_degree": poly_degree(full_d),
        "full_grid_E_degree": poly_degree(full_e),
        "full_grid_LD_equals_3V_e_k_minus_2": full_d == expected_full_d,
        "full_grid_LE_equals_9V_e_k_minus_3": full_e == expected_full_e,
        "block_expansion_identity": block_expansion == expected_block_expansion,
        "block_d_coefficients_zero_through_three": {
            "d0_multiplier": -3,
            "d1_multiplier": 0,
            "d2_multiplier": 12,
            "d3_multiplier": 60,
        },
        "high_remainder_minimum_d_degree": next(
            power for power, coefficient in enumerate(block_expansion[4:], start=4)
            if coefficient != [0]
        ),
        "full_grid_size_exponent": k - 2,
        "full_grid_modulus_exponent": 2,
        "exponent_excess_at_10_pow_120": 120 * (k - 4),
        "direct_determinant_checks": direct_checks,
        "nullspace_checks": {
            "alpha_1": verify_nullspace(owner_grid, 1),
            "alpha_10_pow_120": verify_nullspace(owner_grid, 10**120),
        },
    }


def k5_window_fixture() -> dict:
    k = 5
    d = 6790
    n = 25177
    g = 97
    buckets = {1: 2, 2: 7, 3: 5, 4: 1, 5: 1}
    residuals = {owner: 3 * (n + owner) - d for owner in range(1, k + 1)}
    cofactors = {
        owner: residuals[owner] // buckets[owner] ** 2
        for owner in range(1, k + 1)
    }
    cofactor_product = product(cofactors.values())
    obstructions = normalized_obstructions(k, d, g, cofactor_product)
    grid = tuple(range(1, k + 1))
    c_product = product(local_coefficients(k, owner)[0] for owner in grid)

    subset_resultants = []
    for size in range(4, k + 1):
        for owners in itertools.combinations(grid, size):
            matrix = []
            for owner in owners:
                x = residuals[owner]
                f = obstructions[owner][1]
                c = local_coefficients(k, owner)[0]
                scaled_f = (c_product // c) * f
                matrix.append([scaled_f] +
                              [owner**power * x for power in range(size - 1)])
            resultant = bareiss_det(matrix)
            modulus = product(buckets[owner] ** 2 for owner in owners)
            subset_resultants.append({
                "owners": owners,
                "modulus": modulus,
                "resultant_remainder": resultant % modulus,
            })

    def block(start: int) -> int:
        return product(start + owner for owner in grid)

    pairwise_gcds = {
        f"{i},{j}": math.gcd(buckets[i], buckets[j])
        for i in grid for j in grid if i < j
    }
    obstruction_rows = {}
    for owner in grid:
        second, third = obstructions[owner]
        c, _, _ = local_coefficients(k, owner)
        obstruction_rows[str(owner)] = {
            "P": buckets[owner],
            "a": cofactors[owner],
            "X": residuals[owner],
            "O": second,
            "F": third,
            "O_nonzero": second != 0,
            "F_nonzero": third != 0,
            "P_divides_O": second % buckets[owner] == 0,
            "P_squared_divides_F": third % buckets[owner] ** 2 == 0,
            "third_sign_is_minus_C_sign": sign(third) == -sign(c),
        }

    return {
        "k": k,
        "n": n,
        "d": d,
        "g": g,
        "buckets": buckets,
        "cofactors": cofactors,
        "residuals": residuals,
        "cofactor_product": cofactor_product,
        "residual_decomposition_ok": all(
            residuals[owner] == cofactors[owner] * buckets[owner] ** 2
            for owner in grid
        ),
        "gap_reconstruction": g * product(buckets.values()),
        "gap_reconstruction_ok": d == g * product(buckets.values()),
        "loss_bound": LOSS_BOUND[k],
        "loss_bound_ok": g <= LOSS_BOUND[k],
        "pairwise_bucket_gcds": pairwise_gcds,
        "pairwise_coprime": all(value == 1 for value in pairwise_gcds.values()),
        "lower_window_ok": RESIDUAL_FLOOR[k] * d <= min(residuals.values()),
        "upper_window_ok": max(residuals.values()) < RESIDUAL_CEILING[k] * d,
        "step_three_ok": all(residuals[i + 1] - residuals[i] == 3
                             for i in range(1, k)),
        "obstruction_rows": obstruction_rows,
        "all_subset_resultants_divisible": all(
            row["resultant_remainder"] == 0 for row in subset_resultants),
        "subset_resultants": subset_resultants,
        "block_equation_difference": block(n + d) - 4 * block(n),
        "block_equation_holds": block(n + d) == 4 * block(n),
        "target_cutoff_ok": d >= TARGET_CUTOFF,
        "exact_failed_fields": [
            "blockProduct k (n+d) = 4*blockProduct k n",
            "10^120 <= d",
        ],
    }


def replay_named_boundaries(repo_root: Path) -> dict:
    """Replay frozen falsification fixtures; no result is imported as a premise."""
    if str(repo_root) not in sys.path:
        sys.path.insert(0, str(repo_root))
    from compute.campaign686.fourth_local_lift_hostile_verify import crt_witness
    from compute.campaign686.multi_owner_extension_hostile_verify import (
        reconstruct_crt_falsifier,
    )

    def block(k: int, n: int) -> int:
        return product(n + owner for owner in range(1, k + 1))

    telescopes = []
    for k, n, d in ((9, 2, 1), (15, 4, 1)):
        telescopes.append({
            "k": k,
            "n": n,
            "d": d,
            "block_equation_holds": block(k, n + d) == 4 * block(k, n),
            "target_cutoff_ok": d >= TARGET_CUTOFF,
        })

    three = crt_witness(20)
    four = reconstruct_crt_falsifier()
    return {
        "d_equals_one_telescopes": telescopes,
        "three_owner_121_digit": {
            "gap_digits": three["gap_digits"],
            "all_local_checks": three["all_local_checks"],
            "all_composed_checks": three["all_composed_checks"],
            "coarse_upper_residual_window": three["all_short_window_inequalities"],
            "block_equation_holds": three["block_equation"],
        },
        "four_owner_130_digit": {
            "gap_digits": four["gap_digits"],
            "all_local_checks": four["all_local_congruences_hold"],
            "all_composed_checks": four["all_composed_congruences_hold"],
            "coarse_upper_residual_window": four["upper_window_holds"],
            "block_equation_holds": four["block_equation_holds"],
        },
    }


def build_report(repo_root: Path) -> dict:
    table_check = verify_lean_tables(repo_root)
    rows = [enumerate_row(k) for k in TARGET_K]
    fixture = k5_window_fixture()
    return {
        "arithmetic": "Python exact integers; Fraction only for nullspace identities",
        "lean_table_check": table_check,
        "rows": rows,
        "totals": {
            "target_owner_rows": sum(TARGET_K),
            "subsets_size_4_through_k": sum(
                row["subset_count_size_4_through_k"] for row in rows),
            "four_owner_circuits": sum(row["four_circuit_count"] for row in rows),
            "one_sided_sign_circuits": sum(
                row["one_sided_sign_circuits"] for row in rows),
            "circuits_with_zero_weight": sum(
                len(row["circuits_with_zero_weight"]) for row in rows),
            "L_one_identity_failures": sum(
                len(row["L_one_identity_failures"]) for row in rows),
        },
        "quantified_obstruction": {
            "family": (
                "For any owner subset S of size s>=2 and nonzero "
                "X_i=alpha+3i, the annihilator over Q of the s-1 vectors "
                "(X_i*i^r)_{i in S}, 0<=r<=s-2, is one-dimensional."
            ),
            "generator": "lambda_i = 1/(X_i*product_{j!=i}(i-j))",
            "common_term_moment": (
                "sum_i lambda_i = (-3)^(s-1)/product_i X_i != 0"
            ),
            "consequence": (
                "Every nonzero Vandermonde resultant whose auxiliary columns "
                "are X_i*q(i), deg q<=s-2, retains the common A term."
            ),
            "full_grid_scale": (
                "After A*d^2=g^2*product_i X_i, both surviving terms have "
                "scale g^2*d^(k-2), while the square modulus has scale "
                "d^2/g^2. For k>=5 the size/modulus exponent excess is k-4."
            ),
            "equation_level_collapse": (
                "On the full grid L(D)=3*V*e_(k-2)(X) and "
                "L(E)=9*V*e_(k-3)(X). Therefore (d/g)^2*L(H) is a "
                "fixed factor times the d-degree-at-most-3 truncation of "
                "product(X_i+4d)-4*product(X_i+d). Under the block equation "
                "it equals minus the tail sum over r>=4; that tail contains "
                "d^4, so the induced fourth-power bucket divisibility is "
                "automatic from d=g*product(P_i)."
            ),
            "proper_subset_gap": (
                "For S strictly smaller than the complete owner grid, the "
                "certificate gives no positive lower bound for product_{i in S} P_i."
            ),
        },
        "k5_window_fixture": fixture,
        "named_boundary_replays": replay_named_boundaries(repo_root),
    }


def report_digest(report: dict) -> str:
    encoded = json.dumps(report, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def assert_report(report: dict) -> None:
    table = report["lean_table_check"]
    assert table["parsed_second_rows"] == table["expected_rows"] == 60
    assert table["parsed_third_rows"] == 60
    assert table["mismatches"] == []
    assert report["totals"] == {
        "target_owner_rows": 60,
        "subsets_size_4_through_k": 42274,
        "four_owner_circuits": 2576,
        "one_sided_sign_circuits": 0,
        "circuits_with_zero_weight": 4,
        "L_one_identity_failures": 0,
    }
    expected_subset_counts = {5: 6, 7: 64, 9: 382, 11: 1816, 13: 7814, 15: 32192}
    expected_quotient_ranges = {
        5: (50, 350),
        7: (980, 244020),
        9: (40824, 629342784),
        11: (22302720, 4383765492480),
        13: (28268697600, 67621441024051200),
        15: (24115553280000, 2022760403369072640000),
    }
    for row in report["rows"]:
        k = row["k"]
        assert row["subset_count_size_4_through_k"] == expected_subset_counts[k]
        assert (row["min_abs_vandermonde_quotient"],
                row["max_abs_vandermonde_quotient"]) == expected_quotient_ranges[k]
        assert row["zero_coefficient_triples"] == ([(2, 4, 6)] if k == 7 else [])
        assert row["full_grid_D_degree"] == k - 2
        assert row["full_grid_E_degree"] == k - 3
        assert row["full_grid_LD_equals_3V_e_k_minus_2"]
        assert row["full_grid_LE_equals_9V_e_k_minus_3"]
        assert row["block_expansion_identity"]
        assert row["high_remainder_minimum_d_degree"] == 4
        assert all(check["D_matches"] and check["E_matches"]
                   for check in row["direct_determinant_checks"])
        assert all(check["constant_survives"]
                   and set(check["annihilated_moments"]) == {"0"}
                   and check["constant_moment"] == check["expected_constant_moment"]
                   for check in row["nullspace_checks"].values())
    fixture = report["k5_window_fixture"]
    assert fixture["gap_reconstruction_ok"]
    assert fixture["residual_decomposition_ok"]
    assert fixture["loss_bound_ok"]
    assert fixture["pairwise_coprime"]
    assert fixture["lower_window_ok"] and fixture["upper_window_ok"]
    assert fixture["step_three_ok"]
    assert fixture["all_subset_resultants_divisible"]
    assert all(row["O_nonzero"] and row["F_nonzero"]
               and row["P_divides_O"] and row["P_squared_divides_F"]
               and row["third_sign_is_minus_C_sign"]
               for row in fixture["obstruction_rows"].values())
    assert not fixture["block_equation_holds"]
    assert not fixture["target_cutoff_ok"]
    boundaries = report["named_boundary_replays"]
    assert all(row["block_equation_holds"] and not row["target_cutoff_ok"]
               for row in boundaries["d_equals_one_telescopes"])
    for key, digits in (("three_owner_121_digit", 121),
                        ("four_owner_130_digit", 130)):
        row = boundaries[key]
        assert row["gap_digits"] == digits
        assert row["all_local_checks"] and row["all_composed_checks"]
        assert not row["coarse_upper_residual_window"]
        assert not row["block_equation_holds"]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parents[3],
    )
    parser.add_argument("--compact", action="store_true")
    args = parser.parse_args()
    report = build_report(args.repo_root)
    assert_report(report)
    envelope = {"report_sha256": report_digest(report), "report": report}
    print(json.dumps(envelope, sort_keys=True,
                     indent=None if args.compact else 2))


if __name__ == "__main__":
    main()
