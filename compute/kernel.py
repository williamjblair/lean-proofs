from __future__ import annotations

import argparse
import json
import math
from typing import Any

from compute.erdos699 import criterion_obstruction_primes, digit, primes_upto


_MR_BASES_64 = (
    2,
    3,
    5,
    7,
    11,
    13,
    17,
    325,
    9375,
    28178,
    450775,
    9780504,
    1795265022,
)

_CERTIFIED_PRIME_LIMIT = 2**64
_UNCERTIFIED_PRIME_FACTOR_REASON = (
    "prime_power_factorization cannot certify primality for factor >= 2^64"
)
_POLLARD_RHO_LIMIT_REASON = "pollard rho step limit exceeded"
_POCKLINGTON_WITNESS_LIMIT = 256


def _empty_factorization_certification_summary() -> dict[str, int | None]:
    return {
        "deterministic_prime_count": 0,
        "pocklington_prime_count": 0,
        "largest_deterministic_prime": None,
        "largest_pocklington_prime": None,
    }


def _record_certified_prime(
    summary: dict[str, int | None], prime: int, method: str
) -> None:
    count_key = f"{method}_prime_count"
    largest_key = f"largest_{method}_prime"
    summary[count_key] = int(summary[count_key] or 0) + 1
    largest = summary[largest_key]
    if largest is None or prime > largest:
        summary[largest_key] = prime


def _merge_factorization_certification_summary(
    target: dict[str, int | None], source: dict[str, int | None]
) -> None:
    for method in ("deterministic", "pocklington"):
        count_key = f"{method}_prime_count"
        largest_key = f"largest_{method}_prime"
        target[count_key] = int(target[count_key] or 0) + int(
            source[count_key] or 0
        )
        source_largest = source[largest_key]
        target_largest = target[largest_key]
        if source_largest is not None and (
            target_largest is None or source_largest > target_largest
        ):
            target[largest_key] = source_largest


def _passes_miller_rabin_bases(n: int) -> bool:
    if n < 2:
        return False
    small_primes = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for p in small_primes:
        if n == p:
            return True
        if n % p == 0:
            return False
    d = n - 1
    s = 0
    while d % 2 == 0:
        s += 1
        d //= 2
    for base in _MR_BASES_64:
        a = base % n
        if a == 0:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


def _is_certified_prime(n: int) -> bool:
    if n >= _CERTIFIED_PRIME_LIMIT:
        raise ValueError(_UNCERTIFIED_PRIME_FACTOR_REASON)
    return _passes_miller_rabin_bases(n)


def _pocklington_witness_for_prime_factor(n: int, q: int) -> int | None:
    exponent = (n - 1) // q
    for a in range(2, _POCKLINGTON_WITNESS_LIMIT + 1):
        if math.gcd(a, n) != 1:
            continue
        if pow(a, n - 1, n) != 1:
            return None
        if math.gcd(pow(a, exponent, n) - 1, n) == 1:
            return a
    return None


def _is_pocklington_certified_prime(
    n: int,
    summary: dict[str, int | None],
    max_pollard_rho_steps: int | None = None,
) -> bool:
    if n < 2:
        return False
    if n < _CERTIFIED_PRIME_LIMIT:
        return _is_certified_prime(n)
    try:
        factors = _prime_power_factorization_with_summary(
            n - 1, summary, max_pollard_rho_steps=max_pollard_rho_steps
        )
    except ValueError as exc:
        if str(exc) == _POLLARD_RHO_LIMIT_REASON:
            raise
        return False
    factor_product = 1
    for _prime, prime_power in factors:
        factor_product *= prime_power
    if factor_product != n - 1 or factor_product * factor_product <= n:
        return False
    return all(
        _pocklington_witness_for_prime_factor(n, prime) is not None
        for prime, _prime_power in factors
    )


def _pollard_rho_factor(n: int, max_steps: int | None = None) -> int:
    if n % 2 == 0:
        return 2
    if n % 3 == 0:
        return 3
    if max_steps is not None and max_steps < 0:
        raise ValueError("max_steps must be nonnegative")
    steps = 0
    c = 1
    while True:
        x = 2
        y = 2
        d = 1
        while d == 1:
            if max_steps is not None and steps >= max_steps:
                raise ValueError(_POLLARD_RHO_LIMIT_REASON)
            steps += 1
            x = (x * x + c) % n
            y = (y * y + c) % n
            y = (y * y + c) % n
            d = math.gcd(abs(x - y), n)
        if d != n:
            return d
        c += 1


def _collect_prime_factors(
    n: int,
    factors: list[int],
    summary: dict[str, int | None],
    max_pollard_rho_steps: int | None = None,
) -> None:
    if n == 1:
        return
    if n < _CERTIFIED_PRIME_LIMIT and _is_certified_prime(n):
        factors.append(n)
        _record_certified_prime(summary, n, "deterministic")
        return
    if n >= _CERTIFIED_PRIME_LIMIT and _passes_miller_rabin_bases(n):
        if _is_pocklington_certified_prime(
            n, summary, max_pollard_rho_steps=max_pollard_rho_steps
        ):
            factors.append(n)
            _record_certified_prime(summary, n, "pocklington")
            return
        raise ValueError(_UNCERTIFIED_PRIME_FACTOR_REASON)
    factor = _pollard_rho_factor(n, max_steps=max_pollard_rho_steps)
    _collect_prime_factors(
        factor, factors, summary, max_pollard_rho_steps=max_pollard_rho_steps
    )
    _collect_prime_factors(
        n // factor, factors, summary, max_pollard_rho_steps=max_pollard_rho_steps
    )


def _prime_power_factorization_with_summary(
    n: int,
    summary: dict[str, int | None],
    max_pollard_rho_steps: int | None = None,
) -> list[tuple[int, int]]:
    if n < 1:
        raise ValueError("n must be positive")
    if max_pollard_rho_steps is not None and max_pollard_rho_steps < 0:
        raise ValueError("max_pollard_rho_steps must be nonnegative")
    prime_factors: list[int] = []
    _collect_prime_factors(
        n, prime_factors, summary, max_pollard_rho_steps=max_pollard_rho_steps
    )
    prime_factors.sort()
    factors: list[tuple[int, int]] = []
    i = 0
    while i < len(prime_factors):
        p = prime_factors[i]
        power = 1
        while i < len(prime_factors) and prime_factors[i] == p:
            power *= p
            i += 1
        factors.append((p, power))
    return factors


def prime_power_factorization(
    n: int, max_pollard_rho_steps: int | None = None
) -> list[tuple[int, int]]:
    summary = _empty_factorization_certification_summary()
    return _prime_power_factorization_with_summary(
        n, summary, max_pollard_rho_steps=max_pollard_rho_steps
    )


def _is_power_of_two(n: int) -> bool:
    return 0 < n and (n & (n - 1)) == 0


def _crt_pair_coprime(residue: int, modulus: int, target: int, factor: int) -> int:
    step = ((target - residue) % factor) * pow(modulus, -1, factor) % factor
    return residue + modulus * step


def _first_representative_at_least(residue: int, modulus: int, lower: int) -> int:
    if residue >= lower:
        return residue
    return residue + ((lower - residue + modulus - 1) // modulus) * modulus


def consecutive_kernel_holds(
    n1: int, n2: int, bound: int, t: int, min_t: int = 0
) -> bool:
    if n1 < 1 or n2 < 1:
        raise ValueError("n1 and n2 must be positive")
    if bound < 0 or t < 0 or min_t < 0:
        raise ValueError("bound, t, and min_t must be nonnegative")
    return (
        min_t <= t
        and 2 * t <= bound
        and (t * (t - 1)) % n1 == 0
        and (t * (t - 1) * (t - 2)) % n2 == 0
    )


def squeezed_normalized_case_i_kernel_holds(F: int, X: int, t: int, g: int) -> bool:
    if F < 0 or X < 0 or t < 0 or g < 0:
        raise ValueError("F, X, t, and g must be nonnegative")
    if F == 0 or X == 0 or t == 0:
        return False
    if F % 2 == 0 or X % 4 != 0 or F < 3:
        return False
    if 2 * t >= X or 4 * F > X or 2 * (F * F) > X:
        return False
    n = F * X
    return (
        t * (X - t) == g * (n - 1)
        and (g * (X - 2 * t)) % (n // 2 - 1) == 0
    )


def power_two_quotient_kernel_holds(A: int, B: int, v: int, h: int) -> bool:
    if A < 0 or B < 0 or v < 0 or h < 0:
        raise ValueError("A, B, v, and h must be nonnegative")
    if A % 4 != 0 or not _is_power_of_two(A):
        return False
    if B % 2 == 0 or B < 3:
        return False
    if v == 0 or A - 2 * v <= 0:
        return False
    row_one_modulus = B * A - 1
    half_row_modulus = B * (A // 2) - 1
    return (
        v * (A - v) == h * row_one_modulus
        and (h * (A - 2 * v)) % half_row_modulus == 0
    )


def squeezed_candidate_original_row_three_obstructions(
    F: int, X: int, t: int, prime_limit: int
) -> list[int]:
    if F < 0 or X < 0 or t < 0 or prime_limit < 0:
        raise ValueError("F, X, t, and prime_limit must be nonnegative")
    n = F * X
    j = F * t
    return criterion_obstruction_primes(n, 3, j, primes=primes_upto(prime_limit))


def _first_digit_failure(k: int, n: int, p: int) -> dict[str, int] | None:
    m = max(k, n)
    level = 0
    while p**level <= m:
        k_digit = digit(k, p, level)
        n_digit = digit(n, p, level)
        if k_digit > n_digit:
            return {"level": level, "k_digit": k_digit, "n_digit": n_digit}
        level += 1
    return None


def squeezed_candidate_original_row_three_obstruction_witnesses(
    F: int, X: int, t: int, prime_limit: int
) -> list[dict[str, Any]]:
    if F < 0 or X < 0 or t < 0 or prime_limit < 0:
        raise ValueError("F, X, t, and prime_limit must be nonnegative")
    n = F * X
    j = F * t
    witnesses: list[dict[str, Any]] = []
    for p in squeezed_candidate_original_row_three_obstructions(F, X, t, prime_limit):
        i_failure = _first_digit_failure(3, n, p)
        j_failure = _first_digit_failure(j, n, p)
        if i_failure is None or j_failure is None:
            raise AssertionError("obstruction prime must fail both digit dominations")
        witnesses.append(
            {"prime": p, "i_failure": i_failure, "j_failure": j_failure}
        )
    return witnesses


def diagnose_squeezed_normalized_candidate(
    F: int,
    X: int,
    t: int,
    g: int,
    original_obstruction_prime_limit: int | None = None,
    include_original_obstruction_witnesses: bool = False,
) -> dict[str, Any]:
    if F < 0 or X < 0 or t < 0 or g < 0:
        raise ValueError("F, X, t, and g must be nonnegative")
    if original_obstruction_prime_limit is not None and original_obstruction_prime_limit < 0:
        raise ValueError("original_obstruction_prime_limit must be nonnegative")
    n = F * X
    j = F * t
    diagnostic: dict[str, Any] = {
        "F": F,
        "X": X,
        "t": t,
        "g": g,
        "n": n,
        "j": j,
        "row_one_holds": t * (X - t) == g * (n - 1),
        "squeezed_normalized_case_i_kernel_holds":
            squeezed_normalized_case_i_kernel_holds(F, X, t, g),
        "original_row_three_point_in_range": 1 <= 3 < j <= n // 2,
    }
    if original_obstruction_prime_limit is not None:
        obstructions = squeezed_candidate_original_row_three_obstructions(
            F, X, t, original_obstruction_prime_limit
        )
        diagnostic.update(
            {
                "original_obstruction_prime_limit": original_obstruction_prime_limit,
                "original_row_three_obstruction_primes": obstructions,
                "original_row_three_has_obstruction": bool(obstructions),
                "original_row_three_digit_compatible_under_cap": not obstructions,
            }
        )
        if include_original_obstruction_witnesses:
            diagnostic["original_row_three_obstruction_witnesses"] = (
                squeezed_candidate_original_row_three_obstruction_witnesses(
                    F, X, t, original_obstruction_prime_limit
                )
            )
    elif include_original_obstruction_witnesses:
        raise ValueError(
            "include_original_obstruction_witnesses requires "
            "original_obstruction_prime_limit"
        )
    return diagnostic


def _squeezed_candidate_diagnostic(
    candidate: dict[str, int],
    original_obstruction_prime_limit: int | None = None,
) -> dict[str, Any]:
    F = candidate["F"]
    X = candidate["X"]
    t = candidate["t"]
    g = candidate["g"]
    half_row = F * X // 2 - 1
    gap = X - 2 * t
    half_row_value = g * gap
    half_row_remainder = half_row_value % half_row
    diagnostic = {
        **candidate,
        "half_row": half_row,
        "gap": gap,
        "half_row_value": half_row_value,
        "half_row_remainder": half_row_remainder,
        "half_row_gcd": math.gcd(half_row_value, half_row),
        "survives_half_row": half_row_remainder == 0,
    }
    if original_obstruction_prime_limit is not None:
        obstructions = squeezed_candidate_original_row_three_obstructions(
            F, X, t, original_obstruction_prime_limit
        )
        diagnostic.update(
            {
                "original_n": F * X,
                "original_j": F * t,
                "original_obstruction_prime_limit": original_obstruction_prime_limit,
                "original_row_three_obstruction_primes": obstructions,
                "original_row_three_has_obstruction": bool(obstructions),
            }
        )
    return diagnostic


def _squeezed_candidate_summary(
    candidate_diagnostics: list[dict[str, Any]],
) -> dict[str, Any]:
    gcd_counts: dict[int, int] = {}
    first_obstruction_counts: dict[int, int] = {}
    surviving_half_row_count = 0
    original_obstruction_prime_limit: int | None = None
    with_original_obstruction_count = 0
    for candidate in candidate_diagnostics:
        half_row_gcd = candidate["half_row_gcd"]
        gcd_counts[half_row_gcd] = gcd_counts.get(half_row_gcd, 0) + 1
        if candidate["survives_half_row"]:
            surviving_half_row_count += 1
        if "original_row_three_obstruction_primes" in candidate:
            original_obstruction_prime_limit = candidate["original_obstruction_prime_limit"]
            obstructions = candidate["original_row_three_obstruction_primes"]
            if obstructions:
                with_original_obstruction_count += 1
                first = obstructions[0]
                first_obstruction_counts[first] = first_obstruction_counts.get(first, 0) + 1
    candidate_count = len(candidate_diagnostics)
    summary = {
        "candidate_count": candidate_count,
        "surviving_half_row_count": surviving_half_row_count,
        "failed_half_row_count": candidate_count - surviving_half_row_count,
        "half_row_gcd_histogram": [
            {"half_row_gcd": half_row_gcd, "count": gcd_counts[half_row_gcd]}
            for half_row_gcd in sorted(gcd_counts)
        ],
    }
    if original_obstruction_prime_limit is not None:
        original_obstruction_summary = {
            "prime_limit": original_obstruction_prime_limit,
            "candidate_count": candidate_count,
            "with_obstruction_count": with_original_obstruction_count,
            "without_obstruction_count": candidate_count - with_original_obstruction_count,
            "first_obstruction_prime_histogram": [
                {"prime": prime, "count": first_obstruction_counts[prime]}
                for prime in sorted(first_obstruction_counts)
            ],
        }
        summary["original_row_three_obstruction_summary"] = original_obstruction_summary
    return summary


def squeezed_row_one_candidates_discriminant(F: int, X: int) -> list[dict[str, int]]:
    if F < 0 or X < 0:
        raise ValueError("F and X must be nonnegative")
    if F == 0 or X == 0:
        return []
    if F % 2 == 0 or F < 3 or X % 4 != 0:
        return []
    if 4 * F > X or 2 * (F * F) > X:
        return []
    n1 = F * X - 1
    max_g = (X * X - 1) // (4 * n1)
    candidates: list[dict[str, int]] = []
    for g in range(1, max_g + 1):
        discriminant = X * X - 4 * g * n1
        gap = math.isqrt(discriminant)
        if gap == 0 or gap * gap != discriminant:
            continue
        if (X - gap) % 2 != 0:
            continue
        t = (X - gap) // 2
        if t == 0 or 2 * t >= X:
            continue
        if t * (X - t) != g * n1:
            continue
        candidates.append({"F": F, "X": X, "t": t, "g": g})
    return sorted(candidates, key=lambda item: (item["t"], item["g"]))


def scan_squeezed_normalized_case_i_kernel(
    max_f: int,
    max_x: int,
    include_candidates: bool = False,
    include_candidate_diagnostics: bool = False,
    include_candidate_summary: bool = False,
    original_obstruction_prime_limit: int | None = None,
) -> dict[str, Any]:
    if max_f < 0 or max_x < 0:
        raise ValueError("max_f and max_x must be nonnegative")
    if original_obstruction_prime_limit is not None and original_obstruction_prime_limit < 0:
        raise ValueError("original_obstruction_prime_limit must be nonnegative")
    candidates: list[dict[str, int]] = []
    survivors: list[dict[str, int]] = []
    for F in range(3, max_f + 1, 2):
        min_x = max(4 * F, 2 * F * F)
        first_x = ((min_x + 3) // 4) * 4
        for X in range(first_x, max_x + 1, 4):
            for candidate in squeezed_row_one_candidates_discriminant(F, X):
                candidates.append(candidate)
                t = candidate["t"]
                g = candidate["g"]
                if squeezed_normalized_case_i_kernel_holds(F, X, t, g):
                    survivors.append(candidate)
    result: dict[str, Any] = {
        "mode": "squeezed_normalized_case_i_kernel",
        "algorithm": "bounded_discriminant_scan",
        "max_f": max_f,
        "max_x": max_x,
        "candidate_count": len(candidates),
        "survivor_count": len(survivors),
        "survivors": survivors,
    }
    if include_candidates:
        result["candidates"] = candidates
    if include_candidate_diagnostics or include_candidate_summary:
        candidate_diagnostics = [
            _squeezed_candidate_diagnostic(candidate, original_obstruction_prime_limit)
            for candidate in candidates
        ]
        if include_candidate_diagnostics:
            result["candidate_diagnostics"] = candidate_diagnostics
        if include_candidate_summary:
            result["candidate_summary"] = _squeezed_candidate_summary(
                candidate_diagnostics
            )
    return result


def _power_two_quotient_residue(zero_part: int, one_part: int, A: int) -> int:
    if one_part == 1:
        return 0
    if zero_part == 1:
        return A % one_part
    step = ((A % one_part) * pow(zero_part, -1, one_part)) % one_part
    return zero_part * step


def _power_two_quotient_row_one_candidates(
    exponent: int,
    A: int,
    B: int,
    max_pollard_rho_steps: int | None = None,
) -> tuple[list[dict[str, int]], dict[str, int | None]]:
    row_one_modulus = B * A - 1
    certification_summary = _empty_factorization_certification_summary()
    prime_powers = [
        prime_power
        for _p, prime_power in _prime_power_factorization_with_summary(
            row_one_modulus,
            certification_summary,
            max_pollard_rho_steps=max_pollard_rho_steps,
        )
    ]
    candidates: dict[int, dict[str, int]] = {}

    def visit(index: int, zero_part: int, one_part: int) -> None:
        if index == len(prime_powers):
            residue = _power_two_quotient_residue(zero_part, one_part, A)
            v = residue % row_one_modulus
            if not (0 < v and 2 * v < A):
                return
            product = v * (A - v)
            if product % row_one_modulus != 0:
                return
            h = product // row_one_modulus
            candidates[v] = {
                "exponent": exponent,
                "A": A,
                "B": B,
                "v": v,
                "h": h,
            }
            return
        prime_power = prime_powers[index]
        visit(index + 1, zero_part * prime_power, one_part)
        visit(index + 1, zero_part, one_part * prime_power)

    visit(0, 1, 1)
    return (
        sorted(candidates.values(), key=lambda item: item["v"]),
        certification_summary,
    )


def _power_two_reduced_divisor_gap_diagnostic(
    candidate: dict[str, int],
) -> dict[str, int | str | bool]:
    A = candidate["A"]
    B = candidate["B"]
    v = candidate["v"]
    row_one_modulus = B * A - 1
    half_row_modulus = B * (A // 2) - 1
    r = math.gcd(row_one_modulus, v)
    s = row_one_modulus // r
    l = v // r
    m = (A - v) // s
    alpha = r - B * m
    beta = s - B * l
    c = math.gcd(alpha, beta)
    gcd_quotient_x = alpha // c
    gcd_quotient_y = beta // c
    d = math.gcd(c, half_row_modulus)
    reduced_divisor = half_row_modulus // d
    l_times_m = l * m
    gap_margin = reduced_divisor - l_times_m
    c_is_even = c % 2 == 0
    parity_gcd_bound = c // 2 if c_is_even else c
    if parity_gcd_bound <= 0:
        raise AssertionError("positive split diagnostic must have positive gcd bound")
    parity_reduced_divisor_lower_bound = half_row_modulus // parity_gcd_bound
    parity_gap_margin = parity_reduced_divisor_lower_bound - l_times_m
    parity_product_bound = parity_gcd_bound * (l_times_m + 1)
    parity_product_margin = half_row_modulus - parity_product_bound
    quotient_gap_rhs = (
        2 * c * (gcd_quotient_x * gcd_quotient_y)
        + B * (gcd_quotient_x * l + gcd_quotient_y * m)
    )
    quotient_gap_required = (
        l_times_m + 1 if c_is_even else 2 * (l_times_m + 1)
    )
    quotient_gap_margin = quotient_gap_rhs - quotient_gap_required
    linear_gap_rhs = B * (gcd_quotient_x * l + gcd_quotient_y * m)
    linear_gap_required = quotient_gap_required
    linear_gap_margin = linear_gap_rhs - linear_gap_required
    scaled_deficit_threshold = 2 * l if not c_is_even else l
    scaled_deficit_y_cover = B * gcd_quotient_y
    scaled_deficit_deficit = max(
        0, scaled_deficit_threshold - scaled_deficit_y_cover
    )
    scaled_deficit_x_cover = B * gcd_quotient_x
    if scaled_deficit_x_cover <= 0:
        raise AssertionError("positive split diagnostic must have positive x-cover")
    scaled_deficit_min_q = (
        0
        if scaled_deficit_deficit == 0
        else (m + scaled_deficit_x_cover - 1) // scaled_deficit_x_cover
    )
    scaled_deficit_margin = l - scaled_deficit_min_q * scaled_deficit_deficit
    return {
        "exponent": candidate["exponent"],
        "A": A,
        "B": B,
        "v": v,
        "h": candidate["h"],
        "r": r,
        "s": s,
        "l": l,
        "m": m,
        "alpha": alpha,
        "beta": beta,
        "c": c,
        "gcd_quotient_x": gcd_quotient_x,
        "gcd_quotient_y": gcd_quotient_y,
        "d": d,
        "reduced_divisor": reduced_divisor,
        "l_times_m": l_times_m,
        "gap_margin": gap_margin,
        "gap_holds": l_times_m < reduced_divisor,
        "c_parity": "even" if c_is_even else "odd",
        "parity_gcd_bound": parity_gcd_bound,
        "parity_reduced_divisor_lower_bound": parity_reduced_divisor_lower_bound,
        "parity_gap_margin": parity_gap_margin,
        "parity_gap_holds": l_times_m < parity_reduced_divisor_lower_bound,
        "parity_product_bound": parity_product_bound,
        "parity_product_margin": parity_product_margin,
        "parity_product_gap_holds": parity_product_bound <= half_row_modulus,
        "quotient_gap_rhs": quotient_gap_rhs,
        "quotient_gap_required": quotient_gap_required,
        "quotient_gap_margin": quotient_gap_margin,
        "quotient_gap_holds": quotient_gap_required <= quotient_gap_rhs,
        "linear_gap_rhs": linear_gap_rhs,
        "linear_gap_required": linear_gap_required,
        "linear_gap_margin": linear_gap_margin,
        "linear_gap_holds": linear_gap_required <= linear_gap_rhs,
        "scaled_deficit_threshold": scaled_deficit_threshold,
        "scaled_deficit_y_cover": scaled_deficit_y_cover,
        "scaled_deficit_deficit": scaled_deficit_deficit,
        "scaled_deficit_x_cover": scaled_deficit_x_cover,
        "scaled_deficit_min_q": scaled_deficit_min_q,
        "scaled_deficit_margin": scaled_deficit_margin,
        "scaled_deficit_holds": 0 < scaled_deficit_margin,
    }


def _power_two_parity_branch_gap_summary(
    diagnostics: list[dict[str, int | str | bool]],
) -> dict[str, Any]:
    def branch_y_coverage_margin(item: dict[str, int | str | bool]) -> int:
        threshold = int(item["l"])
        if item["c_parity"] == "odd":
            threshold *= 2
        return int(item["B"]) * int(item["gcd_quotient_y"]) - threshold

    def branch_y_or_x_coverage_holds(item: dict[str, int | str | bool]) -> bool:
        B = int(item["B"])
        x = int(item["gcd_quotient_x"])
        y = int(item["gcd_quotient_y"])
        l = int(item["l"])
        m = int(item["m"])
        if item["c_parity"] == "odd":
            return 2 * l <= B * y or (l < B * y and m <= B * x)
        return l <= B * y or m <= B * x

    def branch_scaled_deficit_min_q(
        item: dict[str, int | str | bool],
    ) -> int | None:
        if item["scaled_deficit_holds"]:
            return int(item["scaled_deficit_min_q"])
        return None

    parity_gap_holds_count = sum(
        1 for item in diagnostics if item["parity_gap_holds"]
    )
    parity_product_gap_holds_count = sum(
        1 for item in diagnostics if item["parity_product_gap_holds"]
    )
    quotient_gap_holds_count = sum(
        1 for item in diagnostics if item["quotient_gap_holds"]
    )
    linear_gap_holds_count = sum(
        1 for item in diagnostics if item["linear_gap_holds"]
    )
    min_parity_gap_candidate = min(
        diagnostics,
        key=lambda item: int(item["parity_gap_margin"]),
        default=None,
    )
    min_parity_product_candidate = min(
        diagnostics,
        key=lambda item: int(item["parity_product_margin"]),
        default=None,
    )
    min_quotient_gap_candidate = min(
        diagnostics,
        key=lambda item: int(item["quotient_gap_margin"]),
        default=None,
    )
    min_linear_gap_candidate = min(
        diagnostics,
        key=lambda item: int(item["linear_gap_margin"]),
        default=None,
    )
    y_coverage_holds_count = sum(
        1 for item in diagnostics if branch_y_coverage_margin(item) >= 0
    )
    y_coverage_failures = [
        item for item in diagnostics if branch_y_coverage_margin(item) < 0
    ]
    odd_y_coverage_failures = [
        item for item in y_coverage_failures if item["c_parity"] == "odd"
    ]
    even_y_coverage_failures = [
        item for item in y_coverage_failures if item["c_parity"] == "even"
    ]
    min_y_coverage_candidate = min(
        diagnostics,
        key=branch_y_coverage_margin,
        default=None,
    )
    y_or_x_coverage_holds_count = sum(
        1 for item in diagnostics if branch_y_or_x_coverage_holds(item)
    )
    y_or_x_coverage_failures = [
        item for item in diagnostics if not branch_y_or_x_coverage_holds(item)
    ]
    odd_y_or_x_coverage_failures = [
        item for item in y_or_x_coverage_failures if item["c_parity"] == "odd"
    ]
    even_y_or_x_coverage_failures = [
        item for item in y_or_x_coverage_failures if item["c_parity"] == "even"
    ]
    min_y_or_x_failure_candidate = min(
        y_or_x_coverage_failures,
        key=lambda item: int(item["linear_gap_margin"]),
        default=None,
    )
    scaled_deficit_records = [
        (q, item)
        for item in diagnostics
        if (q := branch_scaled_deficit_min_q(item)) is not None
    ]
    positive_scaled_deficit_records = [
        (q, item) for q, item in scaled_deficit_records if q > 0
    ]
    scaled_deficit_failures = [
        item for item in diagnostics if branch_scaled_deficit_min_q(item) is None
    ]
    odd_scaled_deficit_failures = [
        item for item in scaled_deficit_failures if item["c_parity"] == "odd"
    ]
    even_scaled_deficit_failures = [
        item for item in scaled_deficit_failures if item["c_parity"] == "even"
    ]
    max_scaled_deficit_record = max(
        positive_scaled_deficit_records,
        key=lambda record: record[0],
        default=None,
    )
    min_scaled_deficit_margin_candidate = min(
        diagnostics,
        key=lambda item: int(item["scaled_deficit_margin"]),
        default=None,
    )
    denominator_le_B_sq_count = sum(
        1
        for item in diagnostics
        if int(item["parity_gcd_bound"]) <= int(item["B"]) * int(item["B"])
    )
    denominator_exceptions = [
        item
        for item in diagnostics
        if int(item["parity_gcd_bound"]) > int(item["B"]) * int(item["B"])
    ]
    odd_denominator_exceptions = [
        item for item in denominator_exceptions if item["c_parity"] == "odd"
    ]
    even_denominator_exceptions = [
        item for item in denominator_exceptions if item["c_parity"] == "even"
    ]
    max_denominator_exception = max(
        denominator_exceptions,
        key=lambda item: int(item["parity_gcd_bound"]) - int(item["B"]) * int(item["B"]),
        default=None,
    )
    return {
        "candidate_count": len(diagnostics),
        "odd_c_count": sum(1 for item in diagnostics if item["c_parity"] == "odd"),
        "even_c_count": sum(1 for item in diagnostics if item["c_parity"] == "even"),
        "parity_gap_holds_count": parity_gap_holds_count,
        "parity_gap_failure_count": len(diagnostics) - parity_gap_holds_count,
        "min_parity_gap_margin": (
            None
            if min_parity_gap_candidate is None
            else min_parity_gap_candidate["parity_gap_margin"]
        ),
        "parity_product_gap_holds_count": parity_product_gap_holds_count,
        "parity_product_gap_failure_count": (
            len(diagnostics) - parity_product_gap_holds_count
        ),
        "min_parity_product_margin": (
            None
            if min_parity_product_candidate is None
            else min_parity_product_candidate["parity_product_margin"]
        ),
        "quotient_gap_holds_count": quotient_gap_holds_count,
        "quotient_gap_failure_count": len(diagnostics) - quotient_gap_holds_count,
        "min_quotient_gap_margin": (
            None
            if min_quotient_gap_candidate is None
            else min_quotient_gap_candidate["quotient_gap_margin"]
        ),
        "linear_gap_holds_count": linear_gap_holds_count,
        "linear_gap_failure_count": len(diagnostics) - linear_gap_holds_count,
        "min_linear_gap_margin": (
            None
            if min_linear_gap_candidate is None
            else min_linear_gap_candidate["linear_gap_margin"]
        ),
        "branch_y_coverage_holds_count": y_coverage_holds_count,
        "branch_y_coverage_failure_count": (
            len(diagnostics) - y_coverage_holds_count
        ),
        "odd_branch_y_coverage_failure_count": len(odd_y_coverage_failures),
        "even_branch_y_coverage_failure_count": len(even_y_coverage_failures),
        "min_branch_y_coverage_margin": (
            None
            if min_y_coverage_candidate is None
            else branch_y_coverage_margin(min_y_coverage_candidate)
        ),
        "min_branch_y_coverage_candidate": min_y_coverage_candidate,
        "branch_y_or_x_coverage_holds_count": y_or_x_coverage_holds_count,
        "branch_y_or_x_coverage_failure_count": (
            len(diagnostics) - y_or_x_coverage_holds_count
        ),
        "odd_branch_y_or_x_coverage_failure_count": len(
            odd_y_or_x_coverage_failures
        ),
        "even_branch_y_or_x_coverage_failure_count": len(
            even_y_or_x_coverage_failures
        ),
        "min_branch_y_or_x_failure_linear_margin": (
            None
            if min_y_or_x_failure_candidate is None
            else min_y_or_x_failure_candidate["linear_gap_margin"]
        ),
        "min_branch_y_or_x_failure_candidate": min_y_or_x_failure_candidate,
        "branch_scaled_deficit_coverage_holds_count": len(
            scaled_deficit_records
        ),
        "branch_scaled_deficit_coverage_failure_count": (
            len(diagnostics) - len(scaled_deficit_records)
        ),
        "odd_branch_scaled_deficit_coverage_failure_count": len(
            odd_scaled_deficit_failures
        ),
        "even_branch_scaled_deficit_coverage_failure_count": len(
            even_scaled_deficit_failures
        ),
        "max_branch_scaled_deficit_min_q": (
            None if max_scaled_deficit_record is None else max_scaled_deficit_record[0]
        ),
        "max_branch_scaled_deficit_min_q_candidate": (
            None if max_scaled_deficit_record is None else max_scaled_deficit_record[1]
        ),
        "min_branch_scaled_deficit_margin": (
            None
            if min_scaled_deficit_margin_candidate is None
            else min_scaled_deficit_margin_candidate["scaled_deficit_margin"]
        ),
        "min_branch_scaled_deficit_margin_candidate": (
            min_scaled_deficit_margin_candidate
        ),
        "parity_denominator_le_B_sq_count": denominator_le_B_sq_count,
        "parity_denominator_gt_B_sq_count": (
            len(diagnostics) - denominator_le_B_sq_count
        ),
        "odd_parity_denominator_gt_B_sq_count": len(odd_denominator_exceptions),
        "even_parity_denominator_gt_B_sq_count": len(even_denominator_exceptions),
        "max_parity_denominator_over_B_sq_candidate": max_denominator_exception,
        "min_parity_gap_candidate": min_parity_gap_candidate,
        "min_parity_product_candidate": min_parity_product_candidate,
        "min_quotient_gap_candidate": min_quotient_gap_candidate,
        "min_linear_gap_candidate": min_linear_gap_candidate,
    }


def _power_two_reduced_divisor_gap_summary(
    candidates: list[dict[str, int]],
) -> dict[str, Any]:
    diagnostics = [
        _power_two_reduced_divisor_gap_diagnostic(candidate)
        for candidate in candidates
    ]
    gap_holds_count = sum(1 for item in diagnostics if item["gap_holds"])
    min_gap_candidate = min(
        diagnostics, key=lambda item: int(item["gap_margin"]), default=None
    )
    return {
        "candidate_count": len(diagnostics),
        "gap_holds_count": gap_holds_count,
        "gap_failure_count": len(diagnostics) - gap_holds_count,
        "min_gap_margin": (
            None if min_gap_candidate is None else min_gap_candidate["gap_margin"]
        ),
        "min_gap_candidate": min_gap_candidate,
        "parity_branch_gap_summary": _power_two_parity_branch_gap_summary(
            diagnostics
        ),
    }


def scan_power_two_quotient_kernel(
    max_exponent: int,
    max_b: int,
    min_exponent: int = 2,
    skip_factorization_failures: bool = False,
    max_pollard_rho_steps: int | None = None,
) -> dict[str, Any]:
    if min_exponent < 0 or max_exponent < min_exponent or max_b < 0:
        raise ValueError("require 0 <= min_exponent <= max_exponent and 0 <= max_b")
    if max_pollard_rho_steps is not None and max_pollard_rho_steps < 0:
        raise ValueError("max_pollard_rho_steps must be nonnegative")
    row_one_candidates: list[dict[str, int]] = []
    survivors: list[dict[str, int]] = []
    skipped_instances: list[dict[str, int | str]] = []
    instance_count = 0
    factorized_instance_count = 0
    factorization_certification_summary = (
        _empty_factorization_certification_summary()
    )
    for exponent in range(min_exponent, max_exponent + 1):
        A = 2**exponent
        for B in range(3, max_b + 1, 2):
            instance_count += 1
            try:
                candidates, certification_summary = (
                    _power_two_quotient_row_one_candidates(
                        exponent,
                        A,
                        B,
                        max_pollard_rho_steps=max_pollard_rho_steps,
                    )
                )
            except ValueError as exc:
                if not skip_factorization_failures:
                    raise
                skipped_instances.append(
                    {
                        "exponent": exponent,
                        "A": A,
                        "B": B,
                        "row_one_modulus": B * A - 1,
                        "reason": str(exc),
                    }
                )
                continue
            factorized_instance_count += 1
            _merge_factorization_certification_summary(
                factorization_certification_summary, certification_summary
            )
            for candidate in candidates:
                row_one_candidates.append(candidate)
                if power_two_quotient_kernel_holds(
                    candidate["A"], candidate["B"], candidate["v"], candidate["h"]
                ):
                    survivors.append(candidate)
    return {
        "mode": "power_two_quotient_kernel",
        "algorithm": "power_two_quotient_divisor_split",
        "min_exponent": min_exponent,
        "max_exponent": max_exponent,
        "max_b": max_b,
        "instance_count": instance_count,
        "factorized_instance_count": factorized_instance_count,
        "factorization_certification_summary": factorization_certification_summary,
        "skipped_instance_count": len(skipped_instances),
        "skipped_instances": skipped_instances,
        "row_one_candidate_count": len(row_one_candidates),
        "survivor_count": len(survivors),
        "row_one_candidates": row_one_candidates,
        "survivors": survivors,
        "reduced_divisor_gap_summary": _power_two_reduced_divisor_gap_summary(
            row_one_candidates
        ),
    }


def kernel_survivors_bruteforce(
    n1: int, n2: int, bound: int, min_t: int = 0
) -> list[int]:
    if n1 < 1 or n2 < 1:
        raise ValueError("n1 and n2 must be positive")
    if bound < 0 or min_t < 0:
        raise ValueError("bound and min_t must be nonnegative")
    return [
        t
        for t in range(min_t, bound // 2 + 1)
        if consecutive_kernel_holds(n1, n2, bound, t, min_t=min_t)
    ]


def _row_one_residue_classes(n1: int) -> tuple[list[int], int]:
    classes = [0]
    modulus = 1
    for _p, prime_power in prime_power_factorization(n1):
        next_classes: list[int] = []
        for residue in classes:
            next_classes.append(_crt_pair_coprime(residue, modulus, 0, prime_power))
            next_classes.append(_crt_pair_coprime(residue, modulus, 1, prime_power))
        modulus *= prime_power
        classes = sorted(set(value % modulus for value in next_classes))
    return classes, modulus


def _product(values: list[int]) -> int:
    result = 1
    for value in values:
        result *= value
    return result


def _row_one_split_diagnostic(
    factors: list[tuple[int, int]], n1: int, n2: int, t: int
) -> dict[str, Any]:
    zero_prime_powers: list[int] = []
    one_prime_powers: list[int] = []
    for _p, prime_power in factors:
        if t % prime_power == 0:
            zero_prime_powers.append(prime_power)
        elif (t - 1) % prime_power == 0:
            one_prime_powers.append(prime_power)
        else:
            raise ValueError("t is not a row-one CRT candidate")
    row_one_product = t * (t - 1)
    if row_one_product % n1 != 0:
        raise ValueError("t is not a row-one CRT candidate")
    row_one_quotient = row_one_product // n1
    row_one_quotient_gcd = math.gcd(row_one_quotient, n2)
    gap_gcd = math.gcd(t - 2, n2)
    quotient_gap_gcd_product = row_one_quotient_gcd * gap_gcd
    row_two_product = t * (t - 1) * (t - 2)
    row_two_remainder = row_two_product % n2
    return {
        "t": t,
        "zero_prime_powers": zero_prime_powers,
        "one_prime_powers": one_prime_powers,
        "zero_product": _product(zero_prime_powers),
        "one_product": _product(one_prime_powers),
        "row_one_quotient": row_one_quotient,
        "row_one_quotient_gcd": row_one_quotient_gcd,
        "gap_gcd": gap_gcd,
        "quotient_gap_gcd_product": quotient_gap_gcd_product,
        "quotient_gap_gcd_product_lt_n2": quotient_gap_gcd_product < n2,
        "row_two_remainder": row_two_remainder,
        "row_two_gcd": math.gcd(row_two_product, n2),
        "survives_row_two": row_two_remainder == 0,
    }


def _row_one_split_summary(splits: list[dict[str, Any]]) -> dict[str, Any]:
    gcd_counts: dict[int, int] = {}
    surviving_split_count = 0
    for split in splits:
        row_two_gcd = split["row_two_gcd"]
        gcd_counts[row_two_gcd] = gcd_counts.get(row_two_gcd, 0) + 1
        if split["survives_row_two"]:
            surviving_split_count += 1
    candidate_count = len(splits)
    return {
        "candidate_count": candidate_count,
        "surviving_split_count": surviving_split_count,
        "failed_split_count": candidate_count - surviving_split_count,
        "row_two_gcd_histogram": [
            {"row_two_gcd": row_two_gcd, "count": gcd_counts[row_two_gcd]}
            for row_two_gcd in sorted(gcd_counts)
        ],
    }


def _merge_row_one_split_summaries(summaries: list[dict[str, Any]]) -> dict[str, Any]:
    gcd_counts: dict[int, int] = {}
    candidate_count = 0
    surviving_split_count = 0
    failed_split_count = 0
    for summary in summaries:
        candidate_count += summary["candidate_count"]
        surviving_split_count += summary["surviving_split_count"]
        failed_split_count += summary["failed_split_count"]
        for row in summary["row_two_gcd_histogram"]:
            row_two_gcd = row["row_two_gcd"]
            gcd_counts[row_two_gcd] = gcd_counts.get(row_two_gcd, 0) + row["count"]
    return {
        "candidate_count": candidate_count,
        "surviving_split_count": surviving_split_count,
        "failed_split_count": failed_split_count,
        "row_two_gcd_histogram": [
            {"row_two_gcd": row_two_gcd, "count": gcd_counts[row_two_gcd]}
            for row_two_gcd in sorted(gcd_counts)
        ],
    }


def _relative_product_is_larger(
    candidate: dict[str, int], current: dict[str, int]
) -> bool:
    candidate_product = candidate["quotient_gap_gcd_product"]
    current_product = current["quotient_gap_gcd_product"]
    left = candidate_product * current["n2"]
    right = current_product * candidate["n2"]
    return left > right


def _quotient_gap_summary(
    splits: list[dict[str, Any]], n2: int
) -> dict[str, Any]:
    product_counts: dict[int, int] = {}
    strict_lt_n2_count = 0
    max_quotient_gap_gcd_product = 0
    max_relative_product: dict[str, int] | None = None
    for split in splits:
        product = split["quotient_gap_gcd_product"]
        product_counts[product] = product_counts.get(product, 0) + 1
        if product < n2:
            strict_lt_n2_count += 1
        if product > max_quotient_gap_gcd_product:
            max_quotient_gap_gcd_product = product
        relative_product = {
            "t": split["t"],
            "n2": n2,
            "quotient_gap_gcd_product": product,
        }
        if max_relative_product is None or _relative_product_is_larger(
            relative_product, max_relative_product
        ):
            max_relative_product = relative_product
    candidate_count = len(splits)
    non_strict_lt_n2_count = candidate_count - strict_lt_n2_count
    return {
        "candidate_count": candidate_count,
        "strict_lt_n2_count": strict_lt_n2_count,
        "non_strict_lt_n2_count": non_strict_lt_n2_count,
        "all_strict_lt_n2": non_strict_lt_n2_count == 0,
        "max_quotient_gap_gcd_product": max_quotient_gap_gcd_product,
        "quotient_gap_gcd_product_histogram": [
            {"quotient_gap_gcd_product": product, "count": product_counts[product]}
            for product in sorted(product_counts)
        ],
        "max_relative_product": max_relative_product,
    }


def _add_quotient_gap_summary_context(
    summary: dict[str, Any], context: dict[str, int]
) -> dict[str, Any]:
    max_relative_product = summary["max_relative_product"]
    if max_relative_product is None:
        return dict(summary)
    return {
        **summary,
        "max_relative_product": {**context, **max_relative_product},
    }


def _merge_quotient_gap_summaries(summaries: list[dict[str, Any]]) -> dict[str, Any]:
    product_counts: dict[int, int] = {}
    candidate_count = 0
    strict_lt_n2_count = 0
    non_strict_lt_n2_count = 0
    max_quotient_gap_gcd_product = 0
    max_relative_product: dict[str, int] | None = None
    for summary in summaries:
        candidate_count += summary["candidate_count"]
        strict_lt_n2_count += summary["strict_lt_n2_count"]
        non_strict_lt_n2_count += summary["non_strict_lt_n2_count"]
        max_quotient_gap_gcd_product = max(
            max_quotient_gap_gcd_product,
            summary["max_quotient_gap_gcd_product"],
        )
        for row in summary["quotient_gap_gcd_product_histogram"]:
            product = row["quotient_gap_gcd_product"]
            product_counts[product] = product_counts.get(product, 0) + row["count"]
        candidate_relative_product = summary["max_relative_product"]
        if candidate_relative_product is None:
            continue
        if max_relative_product is None or _relative_product_is_larger(
            candidate_relative_product, max_relative_product
        ):
            max_relative_product = candidate_relative_product
    return {
        "candidate_count": candidate_count,
        "strict_lt_n2_count": strict_lt_n2_count,
        "non_strict_lt_n2_count": non_strict_lt_n2_count,
        "all_strict_lt_n2": non_strict_lt_n2_count == 0,
        "max_quotient_gap_gcd_product": max_quotient_gap_gcd_product,
        "quotient_gap_gcd_product_histogram": [
            {"quotient_gap_gcd_product": product, "count": product_counts[product]}
            for product in sorted(product_counts)
        ],
        "max_relative_product": max_relative_product,
    }


def scan_kernel_crt(
    n1: int,
    n2: int,
    bound: int,
    min_t: int = 0,
    include_row_one_candidates: bool = False,
    include_row_one_splits: bool = False,
    include_row_one_split_summary: bool = False,
    include_quotient_gap_summary: bool = False,
) -> dict[str, Any]:
    if n1 < 1 or n2 < 1:
        raise ValueError("n1 and n2 must be positive")
    if bound < 0 or min_t < 0:
        raise ValueError("bound and min_t must be nonnegative")
    classes, modulus = _row_one_residue_classes(n1)
    row_one_candidates: list[int] = []
    survivors: list[int] = []
    limit = bound // 2
    for residue in classes:
        t = _first_representative_at_least(residue, modulus, min_t)
        while t <= limit:
            if (t * (t - 1)) % n1 == 0:
                row_one_candidates.append(t)
                if (t * (t - 1) * (t - 2)) % n2 == 0:
                    survivors.append(t)
            t += modulus
    row_one_candidates = sorted(set(row_one_candidates))
    survivors = sorted(set(survivors))
    result: dict[str, Any] = {
        "mode": "kernel_crt",
        "algorithm": "row_one_prime_power_crt",
        "n1": n1,
        "n2": n2,
        "bound": bound,
        "min_t": min_t,
        "row_one_modulus": modulus,
        "row_one_class_count": len(classes),
        "row_one_candidate_count": len(row_one_candidates),
        "survivor_count": len(survivors),
        "survivors": survivors,
    }
    if include_row_one_candidates:
        result["row_one_candidates"] = row_one_candidates
    if (
        include_row_one_splits
        or include_row_one_split_summary
        or include_quotient_gap_summary
    ):
        factors = prime_power_factorization(n1)
        row_one_candidate_splits = [
            _row_one_split_diagnostic(factors, n1, n2, t)
            for t in row_one_candidates
        ]
        if include_row_one_splits:
            result["row_one_candidate_splits"] = row_one_candidate_splits
        if include_row_one_split_summary:
            result["row_one_split_summary"] = _row_one_split_summary(
                row_one_candidate_splits
            )
        if include_quotient_gap_summary:
            result["quotient_gap_summary"] = _quotient_gap_summary(
                row_one_candidate_splits, n2
            )
    return result


def scan_case_i_power_two_kernel(
    max_exponent: int,
    min_exponent: int = 2,
    min_t: int = 4,
    include_row_one_candidates: bool = False,
    include_row_one_splits: bool = False,
    include_row_one_split_summary: bool = False,
    include_quotient_gap_summary: bool = False,
) -> dict[str, Any]:
    if min_exponent < 0 or max_exponent < min_exponent:
        raise ValueError("require 0 <= min_exponent <= max_exponent")
    if min_t < 0:
        raise ValueError("min_t must be nonnegative")
    instances: list[dict[str, Any]] = []
    for exponent in range(min_exponent, max_exponent + 1):
        n = 3 * (2**exponent)
        scan = scan_kernel_crt(
            n - 1,
            n // 2 - 1,
            n,
            min_t=min_t,
            include_row_one_candidates=include_row_one_candidates,
            include_row_one_splits=include_row_one_splits,
            include_row_one_split_summary=include_row_one_split_summary,
            include_quotient_gap_summary=include_quotient_gap_summary,
        )
        if include_quotient_gap_summary:
            scan["quotient_gap_summary"] = _add_quotient_gap_summary_context(
                scan["quotient_gap_summary"],
                {"exponent": exponent, "n": n},
            )
        instances.append({"exponent": exponent, "n": n, **scan})
    result: dict[str, Any] = {
        "mode": "case_i_power_two_kernel",
        "algorithm": "case_i_power_two_kernel_crt",
        "min_exponent": min_exponent,
        "max_exponent": max_exponent,
        "min_t": min_t,
        "instance_count": len(instances),
        "total_row_one_candidate_count": sum(
            item["row_one_candidate_count"] for item in instances
        ),
        "survivor_count": sum(item["survivor_count"] for item in instances),
        "instances": instances,
    }
    if include_row_one_split_summary:
        result["row_one_split_summary"] = _merge_row_one_split_summaries(
            [item["row_one_split_summary"] for item in instances]
        )
    if include_quotient_gap_summary:
        result["quotient_gap_summary"] = _merge_quotient_gap_summaries(
            [item["quotient_gap_summary"] for item in instances]
        )
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Exact CRT scanner for the Erdős #699 consecutive-divisor kernel."
    )
    parser.add_argument("--n1", type=int)
    parser.add_argument("--n2", type=int)
    parser.add_argument("--bound", type=int)
    parser.add_argument("--min-t", type=int)
    parser.add_argument("--case-i-power-two", action="store_true")
    parser.add_argument("--squeezed-normalized-case-i", action="store_true")
    parser.add_argument("--power-two-quotient-kernel", action="store_true")
    parser.add_argument("--diagnose-squeezed-candidate", action="store_true")
    parser.add_argument("--candidate-f", type=int)
    parser.add_argument("--candidate-x", type=int)
    parser.add_argument("--candidate-t", type=int)
    parser.add_argument("--candidate-g", type=int)
    parser.add_argument("--max-f", type=int)
    parser.add_argument("--max-x", type=int)
    parser.add_argument("--max-b", type=int)
    parser.add_argument("--min-exponent", type=int, default=2)
    parser.add_argument("--max-exponent", type=int)
    parser.add_argument("--include-candidates", action="store_true")
    parser.add_argument("--include-candidate-diagnostics", action="store_true")
    parser.add_argument("--include-candidate-summary", action="store_true")
    parser.add_argument("--include-row-one-candidates", action="store_true")
    parser.add_argument("--include-row-one-splits", action="store_true")
    parser.add_argument("--include-row-one-split-summary", action="store_true")
    parser.add_argument("--include-quotient-gap-summary", action="store_true")
    parser.add_argument("--original-obstruction-prime-limit", type=int)
    parser.add_argument("--include-original-obstruction-witnesses", action="store_true")
    parser.add_argument("--skip-factorization-failures", action="store_true")
    parser.add_argument("--max-pollard-rho-steps", type=int)
    args = parser.parse_args(argv)
    if args.diagnose_squeezed_candidate:
        if (
            args.candidate_f is None
            or args.candidate_x is None
            or args.candidate_t is None
            or args.candidate_g is None
        ):
            parser.error(
                "--diagnose-squeezed-candidate requires --candidate-f, "
                "--candidate-x, --candidate-t, and --candidate-g"
            )
        result = diagnose_squeezed_normalized_candidate(
            args.candidate_f,
            args.candidate_x,
            args.candidate_t,
            args.candidate_g,
            original_obstruction_prime_limit=args.original_obstruction_prime_limit,
            include_original_obstruction_witnesses=args.include_original_obstruction_witnesses,
        )
    elif args.case_i_power_two:
        if args.max_exponent is None:
            parser.error("--case-i-power-two requires --max-exponent")
        min_t = 4 if args.min_t is None else args.min_t
        result = scan_case_i_power_two_kernel(
            args.max_exponent,
            min_exponent=args.min_exponent,
            min_t=min_t,
            include_row_one_candidates=args.include_row_one_candidates,
            include_row_one_splits=args.include_row_one_splits,
            include_row_one_split_summary=args.include_row_one_split_summary,
            include_quotient_gap_summary=args.include_quotient_gap_summary,
        )
    elif args.squeezed_normalized_case_i:
        if args.max_f is None or args.max_x is None:
            parser.error("--squeezed-normalized-case-i requires --max-f and --max-x")
        result = scan_squeezed_normalized_case_i_kernel(
            args.max_f,
            args.max_x,
            include_candidates=args.include_candidates,
            include_candidate_diagnostics=args.include_candidate_diagnostics,
            include_candidate_summary=args.include_candidate_summary,
            original_obstruction_prime_limit=args.original_obstruction_prime_limit,
        )
    elif args.power_two_quotient_kernel:
        if args.max_exponent is None or args.max_b is None:
            parser.error(
                "--power-two-quotient-kernel requires --max-exponent and --max-b"
            )
        result = scan_power_two_quotient_kernel(
            args.max_exponent,
            args.max_b,
            min_exponent=args.min_exponent,
            skip_factorization_failures=args.skip_factorization_failures,
            max_pollard_rho_steps=args.max_pollard_rho_steps,
        )
    else:
        if args.n1 is None or args.n2 is None or args.bound is None:
            parser.error("scalar scan requires --n1, --n2, and --bound")
        min_t = 0 if args.min_t is None else args.min_t
        result = scan_kernel_crt(
            args.n1,
            args.n2,
            args.bound,
            min_t=min_t,
            include_row_one_candidates=args.include_row_one_candidates,
            include_row_one_splits=args.include_row_one_splits,
            include_row_one_split_summary=args.include_row_one_split_summary,
            include_quotient_gap_summary=args.include_quotient_gap_summary,
        )
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
