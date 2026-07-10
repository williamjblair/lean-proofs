#!/usr/bin/env python3
"""Exact diagnostics for the #730 uniform incomplete-block claim.

Reconstruct all four branch maps for p=5,7,11, check the quadratic expansion
and p-adic permutation property, then scan translated Q-branch intervals at
a=2r.  All digit and interval counts are exact integers; float is used only
to print the proposed RHS containing log.
"""

from math import gcd, log

import numpy as np


T = 5289
A = 3024 * T * T

BRANCHES = {
    "P": {
        "lam": 42 * T,
        "mu": 11,
        "den": 7,
        "num": lambda pa, c: 12 * pa * c * c - 41 * c,
        "u": lambda c0: 144 * T * c0,
        "b": -246 * T,
    },
    "Q": {
        "lam": 72 * T,
        "mu": 13,
        "den": 12,
        "num": lambda pa, c: 7 * pa * c * c + 41 * c,
        "u": lambda c0: 84 * T * c0,
        "b": 246 * T,
    },
    "R": {
        "lam": 28 * T,
        "mu": 5,
        "den": 14,
        "num": lambda pa, c: 54 * pa * c * c + 129 * c - 7,
        "u": lambda c0: 216 * T * c0,
        "b": 258 * T,
    },
    "S": {
        "lam": 72 * T,
        "mu": 19,
        "den": 12,
        "num": lambda pa, c: 7 * pa * c * c - 43 * c - 6,
        "u": lambda c0: 84 * T * c0,
        "b": -258 * T,
    },
}


def root_data(branch: dict, p: int, a: int) -> tuple[int, int]:
    """Return the least x0 mod p^a and c0=L(x0)/p^a."""
    pa = p**a
    lam = branch["lam"]
    mu = branch["mu"]
    if gcd(lam, p) != 1:
        raise ValueError("branch has no invertible-slope root")
    x0 = (-mu * pow(lam, -1, pa)) % pa
    c0 = (lam * x0 + mu) // pa
    assert lam * x0 + mu == pa * c0
    return x0, c0


def phi(branch: dict, pa: int, c: int) -> int:
    numerator = branch["num"](pa, c)
    assert numerator % branch["den"] == 0
    return numerator // branch["den"]


def expanded_value(branch: dict, p: int, a: int, c0: int, k: int) -> int:
    pa = p**a
    return (
        A * pa * k * k
        + (pa * branch["u"](c0) + branch["b"]) * k
        + phi(branch, pa, c0)
    )


def validate_maps() -> None:
    checked = 0
    skipped = []
    for p in (5, 7, 11):
        for a in (1, 2, 3):
            pa = p**a
            for name, branch in BRANCHES.items():
                if gcd(branch["lam"], p) != 1:
                    assert branch["mu"] % p != 0
                    skipped.append((p, a, name, "no admissible root"))
                    continue
                checked += 1
                _, c0 = root_data(branch, p, a)
                for k in range(-10, 11):
                    c = c0 + branch["lam"] * k
                    assert phi(branch, pa, c) == expanded_value(
                        branch, p, a, c0, k
                    )

                modulus = p**3
                values = {
                    expanded_value(branch, p, a, c0, k) % modulus
                    for k in range(modulus)
                }
                assert len(values) == modulus

    print(f"MAP_RECONSTRUCTION_OK cases={checked} A={A}")
    print(f"skipped={skipped}")
    print("b=" + repr({name: branch["b"] for name, branch in BRANCHES.items()}))


def restricted_mask(values: np.ndarray, p: int, digits: int) -> np.ndarray:
    threshold = (p + 1) // 2
    result = np.ones(len(values), dtype=np.int8)
    work = values.copy()
    for _ in range(digits):
        result &= work % p < threshold
        work //= p
    return result


def max_cyclic_window(mask: np.ndarray, width: int) -> tuple[int, int]:
    extended = np.concatenate((mask, mask[: width - 1])).astype(np.int64)
    cumulative = np.concatenate(
        (np.array([0], dtype=np.int64), np.cumsum(extended))
    )
    windows = cumulative[width:] - cumulative[:-width]
    start = int(windows.argmax())
    return start, int(windows[start])


def q_branch_scan(p: int, r: int) -> dict:
    branch = BRANCHES["Q"]
    a = 2 * r
    pa = p**a
    modulus = p ** (2 * r)
    width = p**r
    threshold = (p + 1) // 2
    x0, c0 = root_data(branch, p, a)
    v = phi(branch, pa, c0)

    k = np.arange(modulus, dtype=np.int64)
    values = (branch["b"] * k + (v % modulus)) % modulus
    good = restricted_mask(values, p, 2 * r)
    exact_valuation = (
        (c0 % p) + (branch["lam"] % p) * (k % p)
    ) % p != 0

    start_all, count_all = max_cyclic_window(good, width)
    start_exact, count_exact = max_cyclic_window(good & exact_valuation, width)

    main_term = width * (threshold / p) ** (2 * r)
    concrete_rhs = main_term * (1 + 1 / log(p**r))
    hits = []
    for offset in range(width):
        kk = (start_exact + offset) % modulus
        if good[kk] and exact_valuation[kk]:
            hits.append(start_exact + offset)

    for kk in hits:
        c = c0 + branch["lam"] * kk
        value = phi(branch, pa, c) % modulus
        assert c % p != 0
        assert all(
            (value // (p**i)) % p < threshold for i in range(2 * r)
        )

    return {
        "p": p,
        "r": r,
        "a": a,
        "q": modulus,
        "N": width,
        "x0": x0,
        "c0": c0,
        "max_all_start": start_all,
        "max_all": count_all,
        "max_exact_start": start_exact,
        "max_exact": count_exact,
        "main": main_term,
        "rhs_1_plus_invlog": concrete_rhs,
        "hits": hits,
    }


def main() -> None:
    validate_maps()
    for p in (5, 7, 11):
        for r in (1, 2, 3):
            row = q_branch_scan(p, r)
            print(
                "p={p} r={r} a={a} q={q} N={N} "
                "main_float_diagnostic={main:.6f} max_all={max_all} "
                "max_exact={max_exact} exact_start={max_exact_start} "
                "rhs_float_diagnostic={rhs_1_plus_invlog:.6f}".format(**row)
            )

    selected = [q_branch_scan(5, 2), q_branch_scan(7, 3), q_branch_scan(11, 2)]
    expected = {(5, 2): (137, 6), (7, 3): (16138, 16), (11, 2): (1461, 14)}
    for row in selected:
        key = (row["p"], row["r"])
        assert (row["max_exact_start"], row["max_exact"]) == expected[key]
        assert row["max_exact"] > row["rhs_1_plus_invlog"]
        print(f"EXACT_COUNTEREXAMPLE {row}")


if __name__ == "__main__":
    main()
