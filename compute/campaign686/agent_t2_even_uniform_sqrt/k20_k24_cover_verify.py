#!/usr/bin/env python3
"""Exact square-root traps and finite-field covers for k=20 and k=24."""

from __future__ import annotations

from typing import Dict

from even_uniform_sqrt_verify import (
    add_bivariate_term,
    add_term,
    eval_poly,
    eval_shift_coefficients,
    make_data,
    shifted_w_coefficients,
)


ROWS = {
    20: {
        "trap": 5_853_806,
        "upper_den": 13,  # 13w <= 14v
        "upper_num": 14,
        "ratio_A": 29,
        "ratio_B": 27,
        "cover": [227, 199, 233, 239, 211, 197, 241],
        "counts": [1829, 811, 355, 165, 73, 26, 9, 0],
    },
    24: {
        "trap": 5_993_518_490,
        "upper_den": 16,  # 16w <= 17v
        "upper_num": 17,
        "ratio_A": 35,
        "ratio_B": 33,
        "cover": [13, 191, 157, 227, 239, 241, 131, 197, 71],
        "counts": [564, 304, 170, 96, 51, 26, 11, 5, 1, 0],
    },
}


def trap_certificate(k: int) -> dict[str, int]:
    row = make_data(k)
    cfg = ROWS[k]
    trap = cfg["trap"]
    v0 = row.first_admissible_odd_center
    w0 = v0 + 2 * k

    # Exact lower inequality B*X + D(w)-4D(v)>0 on
    # v=v0+a, w=w0+a+b, a,b>=0.
    wpoly = dict(row.d_poly)
    for e, c in row.t_poly.items():
        add_term(wpoly, e, trap * c)
    coeffs = shifted_w_coefficients(wpoly, w0)
    vpoly: Dict[int, int] = {}
    for e, c in row.t_poly.items():
        add_term(vpoly, e, 2 * trap * c)
    for e, c in row.d_poly.items():
        add_term(vpoly, e, -4 * c)
    for i, c in eval_shift_coefficients(vpoly, v0).items():
        add_bivariate_term(coeffs, (i, 0), c)
    assert min(coeffs.values()) > 0

    # Conservative exact upper polynomial for den^deg*(D(w)-4D(v)).
    # Keep the negative leading comparison, discard every other negative
    # term, and bound each surviving w^e by (num/den)^e*v^e.
    den = cfg["upper_den"]
    num = cfg["upper_num"]
    degree = max(row.d_poly)
    leading = row.d_poly[degree]
    upper: Dict[int, int] = {
        degree: leading * num**degree - 4 * leading * den**degree
    }
    for e, c in row.d_poly.items():
        if e in (degree, 0):
            continue
        if c > 0:
            add_term(upper, e, c * den ** (degree - e) * num**e)
        else:
            add_term(upper, e, (-4 * c) * den**degree)
    negative_shift = {
        e: -c for e, c in eval_shift_coefficients(upper, v0).items()
    }
    assert min(negative_shift.values()) > 0

    # The rational bracket and candidate count are exact.
    assert 4 * cfg["ratio_B"] ** k < cfg["ratio_A"] ** k
    candidate_count = (trap - 1) // row.fixed_divisor_odd
    assert candidate_count == cfg["counts"][0]
    return {
        "k": k,
        "trap": trap,
        "fixed": row.fixed_divisor_odd,
        "candidate_count": candidate_count,
        "v0": v0,
        "lower_terms": len(coeffs),
        "lower_min": min(coeffs.values()),
        "negative_terms": len(negative_shift),
        "negative_min": min(negative_shift.values()),
    }


def allowed_t_residues(k: int, p: int) -> set[int]:
    row = make_data(k)
    fixed = row.fixed_divisor_odd
    assert fixed % p
    s = [int(eval_poly(row.s_poly, x)) % p for x in range(p)]
    tpoly = [int(eval_poly(row.t_poly, x)) % p for x in range(p)]
    buckets: dict[int, list[int]] = {}
    for w, value in enumerate(s):
        buckets.setdefault(value, []).append(w)
    residues: set[int] = set()
    for v in range(p):
        for w in buckets.get(4 * s[v] % p, ()):
            residues.add((tpoly[w] - 2 * tpoly[v]) % p)
    inv = pow((-fixed) % p, -1, p)
    return {r * inv % p for r in residues}


def cover_certificate(k: int) -> list[int]:
    cfg = ROWS[k]
    survivors = set(range(1, cfg["counts"][0] + 1))
    counts = [len(survivors)]
    for p in cfg["cover"]:
        allowed = allowed_t_residues(k, p)
        survivors = {t for t in survivors if t % p in allowed}
        counts.append(len(survivors))
    assert counts == cfg["counts"]
    assert not survivors
    return counts


def audit() -> dict[int, dict[str, int]]:
    out = {}
    for k in sorted(ROWS):
        out[k] = trap_certificate(k)
        cover_certificate(k)
    return out


def main() -> None:
    for k, cert in audit().items():
        print("row", cert)
        print("cover primes", ROWS[k]["cover"])
        print("survivor counts", ROWS[k]["counts"])


if __name__ == "__main__":
    main()
