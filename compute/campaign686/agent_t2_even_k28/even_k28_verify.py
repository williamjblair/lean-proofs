#!/usr/bin/env python3
"""Exact independent verifier for the unconditional Erdős 686 row ``k=28``.

The verifier reconstructs the centered square-root polynomial, proves the
large-gap shifted-coefficient trap with integer arithmetic, checks every
finite-strip point, and replays the complete prime-field cover.  It imports no
campaign producer and uses neither floating point arithmetic nor probabilistic
primality tests.
"""

from __future__ import annotations

import hashlib
import json
import math
from fractions import Fraction
from functools import reduce
from typing import Iterable


K = 28
R = 14
FIXED = 50_176
SPLIT_GAP = 384
V0 = 14_567
W0 = 15_335
TRAP = 52_682_724_273
CANDIDATE_COUNT = 1_049_958
GREEDY_COVER = [29, 971, 991, 977, 773, 853, 919, 797, 827, 353, 331]
GREEDY_COVER_COUNTS = [
    1_049_958,
    144_821,
    48_916,
    16_531,
    5_589,
    1_901,
    642,
    203,
    62,
    17,
    3,
    0,
]
KERNEL_COVER = [
    29,
    349,
    347,
    317,
    331,
    353,
    283,
    337,
    293,
    281,
    307,
    257,
    271,
    239,
    197,
    313,
    241,
    277,
    5,
    37,
]
KERNEL_COVER_COUNTS = [
    1_049_958,
    144_821,
    70_952,
    35_763,
    18_323,
    9_881,
    5_345,
    2_868,
    1_616,
    933,
    531,
    302,
    167,
    92,
    52,
    27,
    12,
    6,
    2,
    1,
    0,
]

# The lower-peak-memory cover used by the Lean graph.
COVER = KERNEL_COVER
COVER_COUNTS = KERNEL_COVER_COUNTS


Poly = dict[int, int]


def add_term(poly: Poly, degree: int, value: int) -> None:
    poly[degree] = poly.get(degree, 0) + value
    if poly[degree] == 0:
        del poly[degree]


def mul_poly(a: Poly, b: Poly) -> Poly:
    out: Poly = {}
    for i, ai in a.items():
        for j, bj in b.items():
            add_term(out, i + j, ai * bj)
    return out


def eval_poly(poly: Poly, x: int) -> int:
    return sum(coefficient * x**degree for degree, coefficient in poly.items())


def shift_poly(poly: Poly, shift: int) -> Poly:
    out: Poly = {}
    for degree, coefficient in poly.items():
        for j in range(degree + 1):
            add_term(
                out,
                j,
                coefficient * math.comb(degree, j) * shift ** (degree - j),
            )
    return out


def elementary(values: Iterable[int]) -> list[int]:
    out = [1]
    for value in values:
        out.append(0)
        for j in range(len(out) - 1, 0, -1):
            out[j] += value * out[j - 1]
    return out


def reconstruct_polynomials() -> tuple[Poly, Poly, Poly]:
    roots_squared = [(2 * j - 1) ** 2 for j in range(1, R + 1)]
    es = elementary(roots_squared)
    s_poly = {2 * R - 2 * j: (-1) ** j * es[j] for j in range(R + 1)}
    q = [(-1) ** j * es[j] for j in range(R + 1)]
    sqrt_coefficients = [Fraction(1)]
    for n in range(1, R // 2 + 1):
        cross = sum(
            sqrt_coefficients[i] * sqrt_coefficients[n - i]
            for i in range(1, n)
        )
        sqrt_coefficients.append((Fraction(q[n]) - cross) / 2)
    assert all(value.denominator == 1 for value in sqrt_coefficients)
    t_poly = {
        R - 2 * j: int(value) for j, value in enumerate(sqrt_coefficients)
    }
    d_poly = mul_poly(t_poly, t_poly)
    for degree, coefficient in s_poly.items():
        add_term(d_poly, degree, -coefficient)
    return s_poly, t_poly, d_poly


S_POLY, T_POLY, D_POLY = reconstruct_polynomials()


def add_bivariate_term(
    poly: dict[tuple[int, int], int], degrees: tuple[int, int], value: int
) -> None:
    poly[degrees] = poly.get(degrees, 0) + value
    if poly[degrees] == 0:
        del poly[degrees]


def shifted_two_variable(poly: Poly, base: int) -> dict[tuple[int, int], int]:
    """Coefficients of ``p(base+a+b)``, indexed by powers of ``a,b``."""
    out: dict[tuple[int, int], int] = {}
    for degree, coefficient in poly.items():
        for total in range(degree + 1):
            base_part = (
                coefficient
                * math.comb(degree, total)
                * base ** (degree - total)
            )
            for a_degree in range(total + 1):
                add_bivariate_term(
                    out,
                    (a_degree, total - a_degree),
                    base_part * math.comb(total, a_degree),
                )
    return out


def trap_components(v0: int, w0: int) -> tuple[dict, dict]:
    base = shifted_two_variable(D_POLY, w0)
    for degree, coefficient in shift_poly(D_POLY, v0).items():
        add_bivariate_term(base, (degree, 0), -4 * coefficient)
    slope = shifted_two_variable(T_POLY, w0)
    for degree, coefficient in shift_poly(T_POLY, v0).items():
        add_bivariate_term(slope, (degree, 0), 2 * coefficient)
    return base, slope


def least_positive_trap(v0: int, w0: int) -> tuple[int, tuple[int, int]]:
    base, slope = trap_components(v0, w0)
    assert min(slope.values()) > 0
    best = 0
    best_degree = (0, 0)
    for degrees in set(base) | set(slope):
        base_value = base.get(degrees, 0)
        slope_value = slope.get(degrees, 0)
        assert slope_value > 0
        required = 0 if base_value > 0 else (-base_value) // slope_value + 1
        if required > best:
            best = required
            best_degree = degrees
    return best, best_degree


def archimedean_certificate() -> dict:
    # Upper ratio bracket, lower ratio bracket, and coarse D-sign bracket.
    assert 4 * 19**K < 20**K
    assert 83**K < 4 * 79**K
    assert 11**12 < 4 * 10**12
    assert V0 == 38 * SPLIT_GAP - 25
    assert W0 == V0 + 2 * SPLIT_GAP

    least, degree = least_positive_trap(V0, W0)
    assert least == TRAP and degree == (0, 0)
    base, slope = trap_components(V0, W0)
    positive = {
        key: base.get(key, 0) + TRAP * slope.get(key, 0)
        for key in set(base) | set(slope)
    }
    assert len(positive) == 120 and min(positive.values()) > 0

    # Conservative upper bound for 10^12*(D(w)-4D(v)) under 10w<=11v.
    denominator, numerator = 10, 11
    degree_d = max(D_POLY)
    leading = D_POLY[degree_d]
    upper: Poly = {
        degree_d: leading * numerator**degree_d
        - 4 * leading * denominator**degree_d
    }
    for degree_i, coefficient in D_POLY.items():
        if degree_i in (degree_d, 0):
            continue
        if coefficient > 0:
            add_term(
                upper,
                degree_i,
                coefficient
                * denominator ** (degree_d - degree_i)
                * numerator**degree_i,
            )
        else:
            add_term(
                upper,
                degree_i,
                (-4 * coefficient) * denominator**degree_d,
            )
    negative_shift = {
        degree_i: -coefficient
        for degree_i, coefficient in shift_poly(upper, V0).items()
    }
    assert len(negative_shift) == 13 and min(negative_shift.values()) > 0
    assert min(shift_poly(T_POLY, V0).values()) > 0
    assert min(shift_poly(T_POLY, W0).values()) > 0
    assert (TRAP - 1) // FIXED == CANDIDATE_COUNT
    assert FIXED * CANDIDATE_COUNT < TRAP <= FIXED * (CANDIDATE_COUNT + 1)
    return {
        "split_gap": SPLIT_GAP,
        "v0": V0,
        "w0": W0,
        "trap": TRAP,
        "least_trap_degree": degree,
        "trap_terms": len(positive),
        "trap_min_coefficient": min(positive.values()),
        "trap_constant": positive[(0, 0)],
        "negative_terms": len(negative_shift),
        "negative_min_coefficient": min(negative_shift.values()),
        "negative_constant": negative_shift[0],
        "candidate_count": CANDIDATE_COUNT,
    }


def fixed_divisor_certificate() -> dict:
    values = [eval_poly(T_POLY, 2 * t + 1) for t in range(R + 1)]
    fixed = reduce(math.gcd, (abs(value) for value in values), 0)
    assert fixed == FIXED
    for t in range(-R - 2, 2 * R + 3):
        assert eval_poly(T_POLY, 2 * t + 1) % FIXED == 0
    return {
        "fixed_divisor": fixed,
        "factorization": {"2": 10, "7": 2},
        "values_used": len(values),
    }


def finite_strip_certificate() -> dict:
    assert 4 * 19**K < 20**K
    assert 83**K < 4 * 79**K
    checked = 0
    minimum: tuple[int, int, int, int] | None = None
    per_gap = {}
    for d in range(K, SPLIT_GAP):
        lower = 19 * d - 27
        upper = (79 * d - 5) // 4
        per_gap[d] = upper - lower + 1
        for n in range(lower, upper + 1):
            v = 2 * n + 29
            w = v + 2 * d
            error = eval_poly(S_POLY, w) - 4 * eval_poly(S_POLY, v)
            assert error != 0
            candidate = (abs(error), d, n, error)
            if minimum is None or candidate < minimum:
                minimum = candidate
            checked += 1
    assert checked == 64_258 and minimum is not None
    return {
        "gap_lo": K,
        "gap_hi": SPLIT_GAP - 1,
        "checked": checked,
        "minimum_abs_error": minimum[0],
        "minimum_d": minimum[1],
        "minimum_n": minimum[2],
        "minimum_signed_error": minimum[3],
        "d28_candidates": per_gap[28],
        "d383_candidates": per_gap[383],
    }


def allowed_data(p: int) -> tuple[set[int], set[int], dict[int, tuple[int, int]]]:
    assert p > 3 and FIXED % p
    s_values = [eval_poly(S_POLY, x) % p for x in range(p)]
    t_values = [eval_poly(T_POLY, x) % p for x in range(p)]
    buckets: dict[int, list[int]] = {}
    for w, value in enumerate(s_values):
        buckets.setdefault(value, []).append(w)
    m_values: set[int] = set()
    witnesses: dict[int, tuple[int, int]] = {}
    for v in range(p):
        for w in buckets.get(4 * s_values[v] % p, ()):
            m = (t_values[w] - 2 * t_values[v]) % p
            m_values.add(m)
            witnesses.setdefault(m, (w, v))
    inverse = pow((-FIXED) % p, -1, p)
    t_values_allowed = {m * inverse % p for m in m_values}
    return t_values_allowed, m_values, witnesses


def mask(values: Iterable[int]) -> int:
    return sum(1 << value for value in values)


def cover_certificate(primes: list[int], expected_counts: list[int]) -> dict:
    survivors = list(range(1, CANDIDATE_COUNT + 1))
    counts = [len(survivors)]
    rows = []
    for p in primes:
        allowed_t, allowed_m, witnesses = allowed_data(p)
        assert all(m in witnesses for m in allowed_m)
        previous = survivors
        survivors = [t for t in previous if t % p in allowed_t]
        assert all(t % p in allowed_t for t in survivors)
        assert all(t % p not in allowed_t for t in set(previous) - set(survivors))
        counts.append(len(survivors))
        rows.append(
            {
                "p": p,
                "allowed_t_count": len(allowed_t),
                "allowed_m_count": len(allowed_m),
                "allowed_m_mask": mask(allowed_m),
                "survivors": len(survivors),
            }
        )
    assert counts == expected_counts and survivors == []
    p29_allowed, _, _ = allowed_data(29)
    return {
        "primes": primes,
        "survivor_counts": counts,
        "p29_classes": sorted(p29_allowed),
        "q_bound_exclusive": CANDIDATE_COUNT // 29 + 1,
        "rows": rows,
    }


def boundary_certificate() -> dict:
    # At d=1 telescoping would force n+29=4(n+1); 25 is not divisible by 3.
    assert (K + 1 - 4) % 3 != 0
    d = 27
    d27_checked = 0
    for n in range(19 * d - 27, (79 * d - 5) // 4 + 1):
        v = 2 * n + 29
        w = v + 2 * d
        assert eval_poly(S_POLY, w) != 4 * eval_poly(S_POLY, v)
        d27_checked += 1
    return {
        "d1_integral_telescope": False,
        "d27_in_theorem_scope": False,
        "d27_ratio_candidates_checked": d27_checked,
        "d28_in_finite_strip": True,
        "d383_in_finite_strip": True,
        "d384_in_large_gap": True,
        "excluded_fixed_primes": [2, 7],
        "strict_trap_endpoints": [-TRAP, 0],
        "quotient_endpoints": [1, CANDIDATE_COUNT],
    }


def audit() -> dict:
    identity = mul_poly(T_POLY, T_POLY)
    reconstructed = dict(S_POLY)
    for degree, coefficient in D_POLY.items():
        add_term(reconstructed, degree, coefficient)
    assert identity == reconstructed
    assert max(D_POLY) == 12
    report = {
        "row": K,
        "scale": 1,
        "degrees": {"S": max(S_POLY), "T": max(T_POLY), "D": max(D_POLY)},
        "T": T_POLY,
        "D": D_POLY,
        "fixed_divisor": fixed_divisor_certificate(),
        "archimedean": archimedean_certificate(),
        "finite_strip": finite_strip_certificate(),
        "cover": cover_certificate(KERNEL_COVER, KERNEL_COVER_COUNTS),
        "exploratory_greedy_cover": cover_certificate(
            GREEDY_COVER, GREEDY_COVER_COUNTS
        ),
        "boundaries": boundary_certificate(),
    }
    encoded = json.dumps(report, sort_keys=True, separators=(",", ":")).encode()
    report["payload_sha256"] = hashlib.sha256(encoded).hexdigest()
    return report


def main() -> None:
    print(json.dumps(audit(), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
