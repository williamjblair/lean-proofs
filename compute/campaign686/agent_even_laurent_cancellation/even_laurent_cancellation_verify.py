#!/usr/bin/env python3
"""Exact Laurent/Padé cancellation audit for the first live even rows.

The rows are k = 2r with r in {11, 13, 15, 17}.  Every claimed arithmetic
identity is reconstructed with ``Fraction`` and Python integers.  The script
does not search for block-product solutions and does not claim a Lean proof.

For a rational approximant P/B to sqrt(S), put H = P^2 - B^2 S.  At a
hypothetical equation S(w) = 4 S(v), the two integer eliminants satisfy

  (B(v)P(w)-2B(w)P(v)) (B(v)P(w)+2B(w)P(v))
    = B(v)^2 H(w) - 4 B(w)^2 H(v).

The audit computes primitive P,B, the exact odd-center fixed divisor of the
first factor, and the exact first-complement center windows.  It also audits
the stronger variable congruence retained by the first negative Laurent term.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from functools import lru_cache
from math import gcd, lcm
from typing import Iterable


ROWS = (11, 13, 15, 17)
K22_ROOT_FIXTURES = (
    (28_643_526_033, -3, -1),
    (19_687_413_989, -7, -1),
    (3_809_308_513, 13, 15),
)


def trim(poly: list[Fraction]) -> list[Fraction]:
    while len(poly) > 1 and poly[-1] == 0:
        poly.pop()
    return poly


def poly_mul(left: list[Fraction], right: list[Fraction]) -> list[Fraction]:
    out = [Fraction(0)] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            out[i + j] += a * b
    return trim(out)


def poly_sub(left: list[Fraction], right: list[Fraction]) -> list[Fraction]:
    out = [Fraction(0)] * max(len(left), len(right))
    for i in range(len(out)):
        out[i] = (
            (left[i] if i < len(left) else Fraction(0))
            - (right[i] if i < len(right) else Fraction(0))
        )
    return trim(out)


def poly_eval(poly: Iterable[int | Fraction], value: int) -> int | Fraction:
    out: int | Fraction = 0
    for coefficient in reversed(list(poly)):
        out = out * value + coefficient
    return out


def centered_polynomial(r: int) -> list[Fraction]:
    out = [Fraction(1)]
    for odd in range(1, 2 * r, 2):
        out = poly_mul(out, [Fraction(-(odd**2)), Fraction(0), Fraction(1)])
    return out


def normalized_source(r: int) -> list[Fraction]:
    """prod_j (1-(2j-1)^2 z), for the Laurent recurrence."""
    out = [Fraction(1)]
    for odd in range(1, 2 * r, 2):
        out = poly_mul(out, [Fraction(1), Fraction(-(odd**2))])
    return out


def square_root_series(r: int, last_index: int) -> list[Fraction]:
    """c_n in sqrt(S(x)) = x^r sum_n c_n x^(-2n)."""
    source = normalized_source(r)
    out = [Fraction(1)]
    for n in range(1, last_index + 1):
        source_n = source[n] if n < len(source) else Fraction(0)
        cross = sum(out[i] * out[n - i] for i in range(1, n))
        out.append((source_n - cross) / 2)
    return out


def canonical_polynomial_part(r: int) -> list[Fraction]:
    assert r % 2 == 1
    s = (r - 1) // 2
    series = square_root_series(r, s)
    out = [Fraction(0)] * (r + 1)
    for n, coefficient in enumerate(series):
        out[r - 2 * n] = coefficient
    return out


def primitive_integral_pair(
    rational_p: list[Fraction], rational_b: list[Fraction]
) -> tuple[list[int], list[int], int]:
    scale = 1
    for coefficient in rational_p + rational_b:
        scale = lcm(scale, coefficient.denominator)
    p = [int(scale * coefficient) for coefficient in rational_p]
    b = [int(scale * coefficient) for coefficient in rational_b]
    common = 0
    for coefficient in p + b:
        common = gcd(common, abs(coefficient))
    assert common > 0
    p = [coefficient // common for coefficient in p]
    b = [coefficient // common for coefficient in b]
    scale //= common
    assert p[-1] == scale == b[-1]
    return p, b, scale


def integral_deficit(p: list[int], b: list[int], r: int) -> list[int]:
    source = centered_polynomial(r)
    deficit = poly_sub(
        poly_mul([Fraction(x) for x in p], [Fraction(x) for x in p]),
        poly_mul(
            poly_mul([Fraction(x) for x in b], [Fraction(x) for x in b]),
            source,
        ),
    )
    assert all(coefficient.denominator == 1 for coefficient in deficit)
    return [int(coefficient) for coefficient in deficit]


def polynomial_degree(poly: list[int]) -> int:
    return max(i for i, coefficient in enumerate(poly) if coefficient)


def odd_fixed_divisor(poly: list[int]) -> int:
    """Fixed divisor of poly(2a+1), using degree+1 consecutive values."""
    degree = len(poly) - 1
    answer = 0
    for a in range(degree + 1):
        answer = gcd(answer, abs(int(poly_eval(poly, 2 * a + 1))))
    assert answer > 0
    for a in range(-degree - 3, 2 * degree + 4):
        assert int(poly_eval(poly, 2 * a + 1)) % answer == 0
    return answer


def eliminant_fixed_divisor(p: list[int], b: list[int]) -> int:
    """Fixed divisor of B(v)P(w)-2B(w)P(v) on odd v,w.

    After v=2a+1 and w=2c+1, the bivariate degree in each variable is at
    most max(deg P,deg B).  Its fixed divisor is therefore the gcd on the
    corresponding consecutive square grid.
    """
    degree = max(len(p), len(b)) - 1
    answer = 0
    for a in range(degree + 1):
        v = 2 * a + 1
        pv = int(poly_eval(p, v))
        bv = int(poly_eval(b, v))
        for c in range(degree + 1):
            w = 2 * c + 1
            value = bv * int(poly_eval(p, w)) - 2 * int(poly_eval(b, w)) * pv
            answer = gcd(answer, abs(value))
    assert answer > 0
    for a in range(-3, degree + 4):
        for c in range(-3, degree + 4):
            v, w = 2 * a + 1, 2 * c + 1
            value = (
                int(poly_eval(b, v)) * int(poly_eval(p, w))
                - 2 * int(poly_eval(b, w)) * int(poly_eval(p, v))
            )
            assert value % answer == 0
    return answer


def solve_fraction_system(
    matrix: list[list[Fraction]], target: list[Fraction]
) -> list[Fraction]:
    n = len(target)
    augmented = [list(matrix[i]) + [target[i]] for i in range(n)]
    for column in range(n):
        pivot = next(i for i in range(column, n) if augmented[i][column])
        augmented[column], augmented[pivot] = augmented[pivot], augmented[column]
        divisor = augmented[column][column]
        augmented[column] = [value / divisor for value in augmented[column]]
        for row in range(n):
            if row == column or augmented[row][column] == 0:
                continue
            multiplier = augmented[row][column]
            augmented[row] = [
                augmented[row][j] - multiplier * augmented[column][j]
                for j in range(n + 1)
            ]
    return [augmented[i][-1] for i in range(n)]


def even_pade_pair(
    r: int, order: int
) -> tuple[list[int], list[int], int, Fraction, list[Fraction]]:
    """Canonical even denominator of degree 2*order at infinity.

    B=x^(2m)+beta_1*x^(2m-2)+...+beta_m is chosen so the first m
    negative coefficients of B*sqrt(S) vanish.  P is its polynomial part.
    """
    assert order >= 1 and r % 2 == 1
    s = (r - 1) // 2
    series = square_root_series(r, s + 2 * order + 1)
    equations = list(range(s + order + 1, s + 2 * order + 1))
    beta_tail = solve_fraction_system(
        [[series[n - j] for j in range(1, order + 1)] for n in equations],
        [-series[n] for n in equations],
    )
    beta = [Fraction(1)] + beta_tail

    convolution: list[Fraction] = []
    for n in range(s + 2 * order + 2):
        convolution.append(
            sum(beta[j] * series[n - j] for j in range(min(order, n) + 1))
        )
    assert all(convolution[n] == 0 for n in equations)

    rational_b = [Fraction(0)] * (2 * order + 1)
    for j, coefficient in enumerate(beta):
        rational_b[2 * order - 2 * j] = coefficient
    rational_p = [Fraction(0)] * (r + 2 * order + 1)
    for n in range(s + order + 1):
        rational_p[r + 2 * order - 2 * n] = convolution[n]

    p, b, scale = primitive_integral_pair(rational_p, rational_b)
    first_remainder = convolution[s + 2 * order + 1]
    assert first_remainder != 0
    return p, b, scale, first_remainder, beta


def first_negative_pair(
    r: int,
) -> tuple[list[int], list[int], int, Fraction, Fraction]:
    """P/x = Q + c_(s+1)/x, including the first negative term."""
    s = (r - 1) // 2
    series = square_root_series(r, s + 2)
    q = canonical_polynomial_part(r)
    first_negative = series[s + 1]
    next_remainder = series[s + 2]
    rational_p = [first_negative] + q
    rational_b = [Fraction(0), Fraction(1)]
    p, b, scale = primitive_integral_pair(rational_p, rational_b)
    return p, b, scale, first_negative, next_remainder


def first_complement_window(r: int) -> dict[str, int]:
    k = 2 * r
    d = k * k // 18 + 1
    n = 0
    while (n + d + k) ** k > 4 * (n + k) ** k:
        n += 1
    least = n
    while 4 * (n + 1) ** k <= (n + d + 1) ** k:
        n += 1
    greatest = n - 1

    assert (least - 1 + d + k) ** k > 4 * (least - 1 + k) ** k
    assert (least + d + k) ** k <= 4 * (least + k) ** k
    assert 4 * (greatest + 1) ** k <= (greatest + d + 1) ** k
    assert 4 * (greatest + 2) ** k > (greatest + d + 2) ** k
    assert 18 * (d - 1) <= k * k < 18 * d
    return {
        "k": k,
        "d": d,
        "least_n": least,
        "greatest_n": greatest,
        "least_center": 2 * least + k + 1,
        "greatest_center": 2 * greatest + k + 1,
        "candidate_count": greatest - least + 1,
    }


def distance_to_multiple(value: int, modulus: int) -> int:
    residue = value % modulus
    return min(residue, modulus - residue)


def pair_identity_values(
    p: list[int], b: list[int], h: list[int], source: list[int], v: int, w: int
) -> tuple[int, int, int]:
    pv, pw = int(poly_eval(p, v)), int(poly_eval(p, w))
    bv, bw = int(poly_eval(b, v)), int(poly_eval(b, w))
    e = bv * pw - 2 * bw * pv
    f = bv * pw + 2 * bw * pv
    residual = bv * bv * int(poly_eval(h, w)) - 4 * bw * bw * int(poly_eval(h, v))
    source_error = int(poly_eval(source, w)) - 4 * int(poly_eval(source, v))
    assert e * f == residual + bv * bv * bw * bw * source_error
    return e, f, residual


def boundary_fixed_divisor_audit(
    r: int, p: list[int], b: list[int], h: list[int], fixed_divisor: int
) -> dict[str, object]:
    window = first_complement_window(r)
    source = [int(x) for x in centered_polynomial(r)]
    successes = 0
    zero_residuals = 0
    closest: tuple[int, int, int, int, int] | None = None
    for n in range(window["least_n"], window["greatest_n"] + 1):
        v = 2 * n + 2 * r + 1
        w = v + 2 * window["d"]
        e, f, residual = pair_identity_values(p, b, h, source, v, w)
        assert e % fixed_divisor == 0
        assert f > 0
        if residual == 0:
            zero_residuals += 1
        if 0 < abs(residual) < fixed_divisor * f:
            successes += 1
        excess = abs(residual) - fixed_divisor * f
        record = (excess, n, v, w, abs(residual) // (fixed_divisor * f))
        if closest is None or record < closest:
            closest = record
    assert closest is not None
    return {
        "tested_pairs": window["candidate_count"],
        "fixed_divisor_successes": successes,
        "zero_residuals": zero_residuals,
        "closest_fixed_failure": {
            "n": closest[1],
            "v": closest[2],
            "w": closest[3],
            "excess": closest[0],
            "ratio_floor": closest[4],
        },
    }


def variable_congruence_boundary_audit(
    r: int,
    canonical_t: list[int],
    canonical_scale: int,
    canonical_lead: int,
    canonical_fixed_divisor: int,
) -> dict[str, object]:
    """Strong residue-class audit retained after the first Laurent term."""
    window = first_complement_window(r)
    source = [int(x) for x in centered_polynomial(r)]

    # U/(2C^2*x) = Q + b/x with b=-L/(2C^2).
    u = [-canonical_lead] + [2 * canonical_scale * x for x in canonical_t]
    scaled_denominator = [0, 2 * canonical_scale**2]
    h = integral_deficit(u, scaled_denominator, r)

    successes = 0
    zero_distances = 0
    closest: tuple[int, int, int, int, int, int] | None = None
    for n in range(window["least_n"], window["greatest_n"] + 1):
        v = 2 * n + 2 * r + 1
        w = v + 2 * window["d"]
        uv, uw = int(poly_eval(u, v)), int(poly_eval(u, w))
        e = v * uw - 2 * w * uv
        f = v * uw + 2 * w * uv
        residual = v * v * int(poly_eval(h, w)) - 4 * w * w * int(poly_eval(h, v))
        source_error = int(poly_eval(source, w)) - 4 * int(poly_eval(source, v))
        assert e * f == residual + (
            4 * canonical_scale**4 * v * v * w * w * source_error
        )
        assert f > 0
        modulus = 2 * canonical_scale * canonical_fixed_divisor * v * w
        target = -canonical_lead * (v - 2 * w)
        assert e % modulus == target % modulus
        distance = distance_to_multiple(target, modulus)
        if distance == 0:
            zero_distances += 1
        if distance > 0 and 0 < abs(residual) < distance * f:
            successes += 1
        excess = abs(residual) - distance * f
        denominator = max(1, distance * f)
        record = (excess, n, v, w, distance, abs(residual) // denominator)
        if closest is None or record < closest:
            closest = record
    assert closest is not None
    return {
        "variable_congruence_successes": successes,
        "zero_congruence_distances": zero_distances,
        "closest_variable_failure": {
            "n": closest[1],
            "v": closest[2],
            "w": closest[3],
            "distance": closest[4],
            "excess": closest[0],
            "ratio_floor": closest[5],
        },
    }


def construction_digest(p: list[int], b: list[int], h: list[int]) -> str:
    encoded = json.dumps([p, b, h], separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def canonical_data(r: int) -> tuple[dict[str, int], list[int]]:
    q = canonical_polynomial_part(r)
    p, b, scale = primitive_integral_pair(q, [Fraction(1)])
    assert b == [scale]
    deficit = integral_deficit(p, b, r)
    degree = polynomial_degree(deficit)
    fixed = odd_fixed_divisor(p)
    s = (r - 1) // 2
    first_negative = square_root_series(r, s + 1)[s + 1]
    assert Fraction(deficit[degree]) == -2 * scale**2 * first_negative
    return (
        {
            "scale": scale,
            "deficit_degree": degree,
            "deficit_leading_coefficient": deficit[degree],
            "odd_fixed_divisor": fixed,
        },
        p,
    )


def row_audit(r: int) -> dict[str, object]:
    canonical, canonical_t = canonical_data(r)

    first_p, first_b, first_scale, first_coefficient, next_remainder = (
        first_negative_pair(r)
    )
    first_h = integral_deficit(first_p, first_b, r)
    first_degree = polynomial_degree(first_h)
    assert first_degree == r - 1
    assert Fraction(first_h[first_degree]) == -2 * first_scale**2 * next_remainder
    first_fixed = eliminant_fixed_divisor(first_p, first_b)
    first_boundary = boundary_fixed_divisor_audit(
        r, first_p, first_b, first_h, first_fixed
    )
    first_boundary.update(
        variable_congruence_boundary_audit(
            r,
            canonical_t,
            canonical["scale"],
            canonical["deficit_leading_coefficient"],
            canonical["odd_fixed_divisor"],
        )
    )

    pade: dict[str, object] = {}
    for order in range(1, 5):
        p, b, scale, remainder, beta = even_pade_pair(r, order)
        h = integral_deficit(p, b, r)
        degree = polynomial_degree(h)
        assert degree == r - 1
        assert Fraction(h[degree]) == -2 * scale**2 * remainder
        fixed = eliminant_fixed_divisor(p, b)
        entry: dict[str, object] = {
            "denominator_degree": 2 * order,
            "primitive_scale": scale,
            "denominator_coefficients_monic": [str(value) for value in beta],
            "first_uncancelled_remainder": str(remainder),
            "deficit_degree": degree,
            "deficit_leading_coefficient": h[degree],
            "eliminant_odd_fixed_divisor": fixed,
            "optimistic_leading_center": 10 * abs(h[degree]) // fixed + 1,
            "construction_sha256": construction_digest(p, b, h),
        }
        if order == 1:
            entry["boundary_lattice_audit"] = boundary_fixed_divisor_audit(
                r, p, b, h, fixed
            )
        pade[str(order)] = entry

    return {
        "r": r,
        "first_complement_window": first_complement_window(r),
        "canonical": canonical,
        "first_negative": {
            "first_negative_coefficient": str(first_coefficient),
            "primitive_scale": first_scale,
            "deficit_degree": first_degree,
            "deficit_leading_coefficient": first_h[first_degree],
            "deficit_coefficient_abs_sum": sum(abs(value) for value in first_h),
            "eliminant_odd_fixed_divisor": first_fixed,
            "optimistic_leading_center": (
                10 * abs(first_h[first_degree]) // first_fixed + 1
            ),
            "construction_sha256": construction_digest(first_p, first_b, first_h),
            "boundary_lattice_audit": first_boundary,
        },
        "pade_even_orders": pade,
    }


def root_fixture_audit(row11: dict[str, object]) -> list[dict[str, int]]:
    _ = row11
    canonical, t_poly = canonical_data(11)
    source = [int(x) for x in centered_polynomial(11)]
    fixed = canonical["odd_fixed_divisor"]
    out = []
    for t, w, v in K22_ROOT_FIXTURES:
        assert poly_eval(source, w) == 0 == poly_eval(source, v)
        assert poly_eval(t_poly, w) - 2 * poly_eval(t_poly, v) == -fixed * t
        out.append({"t": t, "w": w, "v": v})
    return out


@lru_cache(maxsize=1)
def audit() -> dict[str, object]:
    rows = {str(r): row_audit(r) for r in ROWS}
    assert rows["17"]["first_complement_window"]["least_center"] == 3091
    assert rows["17"]["first_complement_window"]["greatest_center"] == 3155
    return {
        "rows": rows,
        "k22_root_fixtures": root_fixture_audit(rows["11"]),
        "quantified_scope": {
            "rows": list(ROWS),
            "first_negative_denominator_degree": 1,
            "even_pade_orders_audited": [1, 2, 3, 4],
            "boundary_claim": (
                "zero fixed-divisor or variable-congruence trap successes "
                "on every exact first-complement power-window pair"
            ),
        },
        "verdict": (
            "the first negative term and the first four canonical parity-Pade "
            "denominators retain degree r-1 deficit; the two strongest "
            "integer traps tested do not bridge the quadratic boundary"
        ),
    }


def payload_sha256(payload: dict[str, object]) -> str:
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    payload = audit()
    print(
        json.dumps(
            {"payload_sha256": payload_sha256(payload), "payload": payload},
            sort_keys=True,
            indent=2 if args.pretty else None,
        )
    )


if __name__ == "__main__":
    main()
