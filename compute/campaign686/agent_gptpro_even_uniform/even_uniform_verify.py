#!/usr/bin/env python3
"""Exact verifier for the reflected-center, gcd, lcm, and strip claims.

All arithmetic is Python integer arithmetic.  There is no floating point,
probabilistic primality test, or search used as a theorem premise.
"""

from __future__ import annotations

import argparse
import json
from math import comb, factorial, gcd, lcm, prod


def block_product(k: int, n: int) -> int:
    return prod(range(n + 1, n + k + 1))


def odd_double_factorial(k_minus_one: int) -> int:
    return prod(range(1, k_minus_one + 1, 2))


def initial_lcm(n: int) -> int:
    value = 1
    for x in range(1, n + 1):
        value = lcm(value, x)
    return value


def centered_lcm(k: int, d: int) -> int:
    value = 1
    for x in range(d - k + 1, d + k):
        value = lcm(value, x)
    return value


def centered_product(k: int, d: int) -> int:
    return prod(range(d - k + 1, d + k))


def factor(n: int) -> dict[int, int]:
    result: dict[int, int] = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        result[n] = result.get(n, 0) + 1
    return result


def is_prime(n: int) -> bool:
    return n >= 2 and factor(n) == {n: 1}


def log2_floor(k: int) -> int:
    assert k > 0
    return k.bit_length() - 1


def strip_certificate(k: int, d: int) -> bool:
    return 2**k * 8 ** (d + k - 1) <= k * d**k


def lcm_audit(max_n: int) -> dict[str, int | bool]:
    current = 1
    maximum_ratio_numerator = 0
    for n in range(max_n + 1):
        if n:
            current = lcm(current, n)
        assert current == initial_lcm(n)
        assert current <= 8**n
        assert current <= 4**n
        if n >= 2:
            m = n // 2
            recurrence_rhs = initial_lcm(m) * (n + 1) * comb(n, m)
            assert recurrence_rhs % current == 0
            sharp_m = (n + 1) // 2
            sharp_rhs = initial_lcm(sharp_m) * comb(n, sharp_m)
            assert sharp_rhs % current == 0
        maximum_ratio_numerator = max(maximum_ratio_numerator, current)
    return {
        "max_n": max_n,
        "all_initial_lcm_bounds": True,
        "all_half_binomial_divisibilities": True,
        "all_sharp_half_binomial_divisibilities": True,
        "initial_lcm_at_max_n_digits": len(str(maximum_ratio_numerator)),
    }


def strip_audit(max_k: int) -> dict[str, object]:
    proposed = []
    extended = []
    for k in range(256, max_k + 1):
        ell = log2_floor(k)
        d_proposed = k * ell // 6
        d_extended = k * (ell - 4) // 3
        assert k <= d_proposed <= d_extended
        assert 6 * d_proposed <= k * ell
        assert 3 * d_extended <= k * (ell - 4)
        assert strip_certificate(k, d_proposed)
        assert strip_certificate(k, d_extended)
        proposed.append(d_proposed)
        extended.append(d_extended)

    k = 256
    ell = log2_floor(k)
    d = k * (ell - 4) // 3
    assert (k, ell, d) == (256, 8, 341)
    lhs = k * d**k
    rhs = 2**k * 8 ** (d + k - 1)
    assert rhs == 2**2044
    assert lhs > rhs
    return {
        "k_min": 256,
        "k_max": max_k,
        "rows_checked_all_parities": max_k - 255,
        "proposed_min_endpoint": min(proposed),
        "proposed_max_endpoint": max(proposed),
        "extended_min_endpoint": min(extended),
        "extended_max_endpoint": max(extended),
        "boundary": {
            "k": k,
            "ell": ell,
            "d": d,
            "rhs_power_of_two_exponent": 2044,
            "lhs_digits": len(str(lhs)),
            "rhs_digits": len(str(rhs)),
            "certificate": True,
        },
    }


def exact_solution_audit() -> dict[str, object]:
    exact_even = [(6, 1, 1), (12, 3, 1)]
    rows = []
    for k, n, d in exact_even:
        lower = block_product(k, n)
        upper = block_product(k, n + d)
        assert upper == 4 * lower
        h = 2 * n + d + k + 1
        g = gcd(d, h)
        odd_df = odd_double_factorial(k - 1)
        assert odd_df % g == 0
        rows.append({"k": k, "n": n, "d": d, "H": h, "gcd": g})

    # GPT Pro's boxed B is false without the inherited even/large-gap scope.
    k, n, d = 3, 0, 1
    assert block_product(k, n + d) == 4 * block_product(k, n)
    h = 2 * n + d + k + 1
    assert h == 5 and is_prime(h) and 23 <= 8 * h
    return {
        "even_d1_telescopes": rows,
        "standalone_B_counterexample": {
            "k": k,
            "n": n,
            "d": d,
            "H": h,
            "equation": True,
            "twenty_three_le_eight_q": True,
        },
    }


def mandatory_fixture_audit() -> dict[str, object]:
    fixtures = {
        "prefix_984": (984, 3_177_026, 4_480),
        "prefix_244": (244, 48_502, 277),
        "pseudo_22": (22, 11_274_465_968_418, 733_303_549_440),
    }
    result: dict[str, object] = {}
    for name, (k, n, d) in fixtures.items():
        h = 2 * n + d + k + 1
        g = gcd(d, h)
        equation = block_product(k, n + d) == 4 * block_product(k, n)
        assert not equation
        row: dict[str, object] = {
            "k": k,
            "n": n,
            "d": d,
            "H": h,
            "gcd_d_H": g,
            "equation": equation,
        }
        row["quadratic_strip_applies"] = (
            k >= 16 and k <= d and 18 * d <= k * k
        )
        if row["quadratic_strip_applies"]:
            assert quadratic_pair_unit(k, d)
            assert quadratic_certificate(k, d)
        if k % 2 == 0:
            assert odd_double_factorial(k - 1) % g == 0
            row["gcd_condition"] = True
        if k >= 256:
            ell = log2_floor(k)
            row["proposed_endpoint"] = k * ell // 6
            row["extended_endpoint"] = k * (ell - 4) // 3
            assert d > row["proposed_endpoint"]
            assert d > row["extended_endpoint"]
        result[name] = row

    h984 = int(result["prefix_984"]["H"])
    assert h984 == 6_359_517
    assert factor(h984) == {3: 2, 706_613: 1}
    assert is_prime(706_613)
    q, a = 706_613, 9
    assert h984 == a * q
    assert 23 * a <= 8 * q
    assert 5 * a <= 2 * q
    result["prefix_984"]["H_factorization"] = {"3": 2, "706613": 1}
    result["prefix_984"]["dominant_component_conditions"] = True
    assert result["prefix_984"]["quadratic_strip_applies"]

    h244 = int(result["prefix_244"]["H"])
    assert h244 == 97_526
    assert factor(h244) == {2: 1, 11: 2, 13: 1, 31: 1}
    assert max(factor(h244)) < 244
    result["prefix_244"]["no_prime_base_above_k"] = True
    assert result["prefix_244"]["quadratic_strip_applies"]
    assert not result["pseudo_22"]["quadratic_strip_applies"]

    # The strict reflected geometry survives the hostile d=k,i=k boundary.
    for k in range(2, 302, 2):
        n, d, i = k + 7, k, k
        h = 2 * n + d + k + 1
        lower_owner = n + i
        assert h - 2 * lower_owner == 1
        odd_df = odd_double_factorial(k - 1)
        for p in range(k, k + 100):
            if is_prime(p):
                assert odd_df % p != 0
    result["boundary_d_eq_k_i_eq_k"] = True
    result["prime_ge_k_support_scan_even_k_through"] = 300
    return result


def centered_lcm_audit(max_k: int) -> dict[str, object]:
    cases = 0
    for k in range(1, max_k + 1):
        for d in (k, k + 1, 2 * k, 5 * k + 3):
            c = centered_lcm(k, d)
            init = initial_lcm(d + k - 1)
            assert init % c == 0
            assert c <= 8 ** (d + k - 1)
            assert c <= 4 ** (d + k - 1)
            cases += 1
    return {"max_k": max_k, "cases": cases, "all_divisibilities": True}


def interval_compression_audit(max_m: int, max_a: int) -> dict[str, object]:
    cases = 0
    for m in range(1, max_m + 1):
        lam = initial_lcm(m)
        for a in range(1, max_a + 1):
            interval = list(range(a, a + m))
            interval_product = prod(interval)
            interval_lcm = 1
            for x in interval:
                interval_lcm = lcm(interval_lcm, x)
            lhs = factorial(m) * interval_lcm
            rhs = interval_product * lam
            assert rhs % lhs == 0
            cases += 1
    return {
        "max_m": max_m,
        "max_a": max_a,
        "cases": cases,
        "all_factorial_lcm_divisibilities": True,
    }


def quadratic_certificate(k: int, d: int) -> bool:
    m = 2 * k - 1
    lhs = 20**k * factorial(k - 1) * (4 * d) ** m
    rhs = factorial(m) * (13 * k * d) ** k
    return lhs <= rhs


def quadratic_pair_unit(k: int, d: int) -> bool:
    lhs = 20**2 * (4 * d) ** 4
    rhs = k * (2 * k - 1) * (13 * k * d) ** 2
    return lhs <= rhs


def quadratic_strip_audit(max_k: int) -> dict[str, object]:
    assert max_k >= 18
    rows = 0
    certificates = 0
    first_nonempty: tuple[int, int] | None = None
    for k in range(16, max_k + 1):
        d_max = k * k // 18
        if d_max < k:
            assert k in (16, 17)
            continue
        if first_nonempty is None:
            first_nonempty = (k, d_max)
        rows += 1
        sample = {k, d_max, (k + d_max) // 2}
        for d in sorted(sample):
            assert k <= d and 18 * d <= k * k
            assert quadratic_pair_unit(k, d)
            assert quadratic_certificate(k, d)
            certificates += 1

    assert first_nonempty == (18, 18)
    assert quadratic_certificate(18, 18)
    return {
        "k_min": 16,
        "k_max": max_k,
        "rows_with_nonempty_strip": rows,
        "sampled_exact_certificates": certificates,
        "first_nonempty_boundary": {"k": 18, "d": 18},
        "all_parities": True,
    }


def verify(max_k: int = 2000, max_n: int = 1000) -> dict[str, object]:
    return {
        "arithmetic": "exact integers only",
        "lcm": lcm_audit(max_n),
        "centered_lcm": centered_lcm_audit(100),
        "interval_compression": interval_compression_audit(30, 80),
        "strips": strip_audit(max_k),
        "quadratic_strip": quadratic_strip_audit(max_k),
        "solutions": exact_solution_audit(),
        "fixtures": mandatory_fixture_audit(),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-k", type=int, default=2000)
    parser.add_argument("--max-n", type=int, default=1000)
    args = parser.parse_args()
    print(json.dumps(verify(args.max_k, args.max_n), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
