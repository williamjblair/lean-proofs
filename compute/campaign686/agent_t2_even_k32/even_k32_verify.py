#!/usr/bin/env python3
"""Exact verifier for the unconditional Erdős 686 row k=32 route.

All certified arithmetic uses Python integers and ``Fraction``.  The module
reconstructs the square-root polynomial part, proves the shifted-coefficient
trap, checks the finite strip, and replays the complete prime-field cover.
It imports no campaign producer.
"""

from __future__ import annotations

import hashlib
import json
import math
from fractions import Fraction
from functools import reduce
from itertools import combinations
from pathlib import Path
from typing import Iterable, Sequence


K = 32
R = 16
FIXED = 3_221_225_472
SPLIT_GAP = 128
V0 = 5_603
W0 = 5_859
TRAP = 1_388_955_148_309_984
CANDIDATE_COUNT = 431_188
COVER = [17, 521, 509, 491, 457, 463, 487, 383, 449,
         439, 499, 443, 7, 431, 397, 467, 409]
COVER_COUNTS = [431_188, 177_548, 86_232, 42_235, 21_029, 10_678,
                5_404, 2_769, 1_444, 743, 375, 179, 89, 47, 23, 10, 4, 0]
P17_CLASSES = [0, 3, 6, 7, 10, 13, 14]


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
            add_term(out, j, coefficient * math.comb(degree, j) * shift ** (degree - j))
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
        cross = sum(sqrt_coefficients[i] * sqrt_coefficients[n - i]
                    for i in range(1, n))
        sqrt_coefficients.append((Fraction(q[n]) - cross) / 2)
    assert all(value.denominator == 1 for value in sqrt_coefficients)
    t_poly = {R - 2 * j: int(value) for j, value in enumerate(sqrt_coefficients)}
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
    """Coefficients of p(base+a+b), indexed by powers of a,b."""
    out: dict[tuple[int, int], int] = {}
    for degree, coefficient in poly.items():
        for total in range(degree + 1):
            base_part = coefficient * math.comb(degree, total) * base ** (degree - total)
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
    assert 4 * 22**K < 23**K
    assert 49**K < 4 * 47**K
    assert 4 * 45**K < 47**K
    assert V0 == 44 * SPLIT_GAP - 29
    assert W0 == V0 + 2 * SPLIT_GAP

    least, degree = least_positive_trap(V0, W0)
    assert least == TRAP and degree == (0, 0)
    base, slope = trap_components(V0, W0)
    positive = {
        key: base.get(key, 0) + TRAP * slope.get(key, 0)
        for key in set(base) | set(slope)
    }
    assert len(positive) == 153 and min(positive.values()) > 0

    # Conservative upper bound for 22^14*(D(w)-4D(v)) under 22w<=23v.
    denominator, numerator = 22, 23
    degree_d = max(D_POLY)
    leading = D_POLY[degree_d]
    upper: Poly = {
        degree_d: leading * numerator**degree_d - 4 * leading * denominator**degree_d
    }
    for degree_i, coefficient in D_POLY.items():
        if degree_i in (degree_d, 0):
            continue
        if coefficient > 0:
            add_term(
                upper,
                degree_i,
                coefficient * denominator ** (degree_d - degree_i) * numerator**degree_i,
            )
        else:
            add_term(upper, degree_i, (-4 * coefficient) * denominator**degree_d)
    negative_shift = {degree_i: -coefficient
                      for degree_i, coefficient in shift_poly(upper, V0).items()}
    assert len(negative_shift) == 15 and min(negative_shift.values()) > 0
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
        "factorization": {"2": 30, "3": 1},
        "values_used": len(values),
    }


def finite_strip_certificate() -> dict:
    assert 4 * 22**K < 23**K
    assert 49**K < 4 * 47**K
    checked = 0
    minimum: tuple[int, int, int, int] | None = None
    per_gap = {}
    for d in range(K, SPLIT_GAP):
        lower = 22 * d - 31
        upper = (47 * d - 3) // 2
        per_gap[d] = upper - lower + 1
        for n in range(lower, upper + 1):
            v = 2 * n + 33
            w = v + 2 * d
            error = eval_poly(S_POLY, w) - 4 * eval_poly(S_POLY, v)
            assert error != 0
            candidate = (abs(error), d, n, error)
            if minimum is None or candidate < minimum:
                minimum = candidate
            checked += 1
    assert checked == 14_352 and minimum is not None
    return {
        "gap_lo": K,
        "gap_hi": SPLIT_GAP - 1,
        "checked": checked,
        "minimum_abs_error": minimum[0],
        "minimum_d": minimum[1],
        "minimum_n": minimum[2],
        "minimum_signed_error": minimum[3],
        "d32_candidates": per_gap[32],
        "d127_candidates": per_gap[127],
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


def cover_certificate() -> dict:
    survivors = list(range(1, CANDIDATE_COUNT + 1))
    counts = [len(survivors)]
    rows = []
    for p in COVER:
        allowed_t, allowed_m, witnesses = allowed_data(p)
        assert all(m in witnesses for m in allowed_m)
        survivors = [t for t in survivors if t % p in allowed_t]
        counts.append(len(survivors))
        rows.append({
            "p": p,
            "allowed_t_count": len(allowed_t),
            "allowed_m_count": len(allowed_m),
            "allowed_m_mask": mask(allowed_m),
            "survivors": len(survivors),
        })
    assert counts == COVER_COUNTS and survivors == []
    p17_allowed, _, _ = allowed_data(17)
    assert sorted(p17_allowed) == P17_CLASSES
    return {
        "primes": COVER,
        "survivor_counts": counts,
        "p17_classes": P17_CLASSES,
        "q_bound_exclusive": CANDIDATE_COUNT // 17 + 1,
        "rows": rows,
    }


def boundary_certificate() -> dict:
    # d=1 telescopes to n+33=4(n+1), which has no integral n.
    assert (K + 1 - 4) % 3 != 0
    # d=31 is outside the theorem but is replayed over its exact ratio strip.
    d = 31
    d31_checked = 0
    for n in range(22 * d - 31, (47 * d - 3) // 2 + 1):
        v = 2 * n + 33
        w = v + 2 * d
        assert eval_poly(S_POLY, w) != 4 * eval_poly(S_POLY, v)
        d31_checked += 1
    return {
        "d1_integral_telescope": False,
        "d31_in_theorem_scope": False,
        "d31_ratio_candidates_checked": d31_checked,
        "d32_in_finite_strip": True,
        "d128_in_large_gap": True,
        "excluded_fixed_primes": [2, 3],
        "quotient_endpoints": [1, CANDIDATE_COUNT],
    }


def audit() -> dict:
    identity = mul_poly(T_POLY, T_POLY)
    reconstructed = dict(S_POLY)
    for degree, coefficient in D_POLY.items():
        add_term(reconstructed, degree, coefficient)
    assert identity == reconstructed
    assert max(D_POLY) == 14
    report = {
        "row": K,
        "scale": 1,
        "degrees": {"S": max(S_POLY), "T": max(T_POLY), "D": max(D_POLY)},
        "T": T_POLY,
        "D": D_POLY,
        "fixed_divisor": fixed_divisor_certificate(),
        "archimedean": archimedean_certificate(),
        "finite_strip": finite_strip_certificate(),
        "cover": cover_certificate(),
        "boundaries": boundary_certificate(),
    }
    encoded = json.dumps(report, sort_keys=True, separators=(",", ":")).encode()
    report["payload_sha256"] = hashlib.sha256(encoded).hexdigest()
    return report


def main() -> None:
    print(json.dumps(audit(), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
