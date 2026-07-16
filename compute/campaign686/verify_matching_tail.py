#!/usr/bin/env python3
"""Independent exact/interval verifier for the Erdős 686 matching tail.

Acceptance never depends on a binary floating-point logarithm.  The finite
scan uses Python Decimal's correctly rounded ``ln`` and widens every value by
one representable Decimal on both sides.  All subsequent arithmetic is
directed outward.  If a resulting interval contains zero, the verifier falls
back to the exact cleared integer inequality.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import sys
from decimal import (
    Context,
    Decimal,
    ROUND_CEILING,
    ROUND_FLOOR,
    ROUND_HALF_EVEN,
)
from pathlib import Path


ROOT = Path(__file__).resolve().parent
THRESHOLD_CERT = ROOT / "matching_tail_threshold.json"
SECANT_CERT = ROOT / "secant_pairing_certificate.json"
TANGENT_CERT = ROOT / "tangent_defect_crt_certificate.json"

SCAN_START = 16
ANALYTIC_TAIL_START = 1_000_000
PRECISION = 42

sys.set_int_max_str_digits(0)

NEAR = Context(prec=PRECISION, rounding=ROUND_HALF_EVEN)
DOWN = Context(prec=PRECISION, rounding=ROUND_FLOOR)
UP = Context(prec=PRECISION, rounding=ROUND_CEILING)

Interval = tuple[Decimal, Decimal]


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sieve_prime_counts(limit: int) -> tuple[list[int], bytes]:
    composite = bytearray(limit + 1)
    composite[0:2] = b"\x01\x01"
    bound = math.isqrt(limit)
    for p in range(2, bound + 1):
        if not composite[p]:
            start = p * p
            composite[start : limit + 1 : p] = b"\x01" * (
                (limit - start) // p + 1
            )
    counts = [0] * (limit + 1)
    total = 0
    for k in range(limit + 1):
        if not composite[k]:
            total += 1
        counts[k] = total
    return counts, bytes(composite)


def ln_interval(x: int) -> Interval:
    if x <= 0:
        raise ValueError(f"ln input must be positive, got {x}")
    rounded = NEAR.ln(Decimal(x))
    return NEAR.next_minus(rounded), NEAR.next_plus(rounded)


def add_interval(a: Interval, b: Interval) -> Interval:
    return DOWN.add(a[0], b[0]), UP.add(a[1], b[1])


def scale_interval(c: int, a: Interval) -> Interval:
    if c < 0:
        lo = DOWN.multiply(Decimal(c), a[1])
        hi = UP.multiply(Decimal(c), a[0])
        return lo, hi
    return (
        DOWN.multiply(Decimal(c), a[0]),
        UP.multiply(Decimal(c), a[1]),
    )


def sub_interval(a: Interval, b: Interval) -> Interval:
    return DOWN.subtract(a[0], b[1]), UP.subtract(a[1], b[0])


def exact_sides(k: int, p: int) -> tuple[int, int, dict[str, int]]:
    q = k // 2
    delta = k % 2
    d0 = (708_827 * k * k) // 5_000_000 + 1
    exponent = k - p - q - delta
    if exponent <= 0:
        raise AssertionError((k, p, q, delta, exponent))
    lhs = (
        pow(k, k - p)
        * pow(d0, exponent)
        * pow(2, delta)
        * pow(q, q)
    )
    rhs = (
        factorial(k - 1)
        * pow(3, p + delta)
        * pow(2, q + k - 2 * p)
        * pow(k - 1, q)
        * pow(q + 2 * k + 2, q)
    )
    return lhs, rhs, {
        "k": k,
        "pi_k": p,
        "q": q,
        "delta": delta,
        "d0": d0,
        "exponent": exponent,
    }


_factorial_cache: dict[int, int] = {0: 1, 1: 1}


def factorial(n: int) -> int:
    if n in _factorial_cache:
        return _factorial_cache[n]
    start = max(_factorial_cache)
    value = _factorial_cache[start]
    for j in range(start + 1, n + 1):
        value *= j
        _factorial_cache[j] = value
    return value


def exact_boundary_record(k: int, p: int) -> dict[str, object]:
    lhs, rhs, meta = exact_sides(k, p)
    passed = lhs > rhs
    larger, smaller = (lhs, rhs) if passed else (rhs, lhs)
    return {
        **meta,
        "verdict": "pass" if passed else "fail",
        "larger_over_smaller_floor": larger // smaller,
        "lhs_bits": lhs.bit_length(),
        "rhs_bits": rhs.bit_length(),
        "lhs_sha256": sha256_bytes(str(lhs).encode("ascii")),
        "rhs_sha256": sha256_bytes(str(rhs).encode("ascii")),
    }


def verify_block_pairing_certificate(cert: dict[str, object]) -> None:
    for block_name, size in (("four_block", 4), ("six_block", 6)):
        block = cert[block_name]
        pairs = [tuple(pair) for pair in block["pairs"]]
        flattened = [i for pair in pairs for i in pair]
        if sorted(flattened) != list(range(size)):
            raise AssertionError(f"{block_name}: endpoints do not partition block")
        if len(flattened) != len(set(flattened)):
            raise AssertionError(f"{block_name}: repeated endpoint")
        if any(abs(b - a) < 2 for a, b in pairs):
            raise AssertionError(f"{block_name}: selected pair can have unit gap")

        # Coefficient of each adjacent positive gap in the total pair cost.
        coefficients = [0] * (size - 1)
        for a, b in pairs:
            lo, hi = sorted((a, b))
            for gap in range(lo, hi):
                coefficients[gap] += 1
        if coefficients != block["adjacent_gap_coefficients"]:
            raise AssertionError(f"{block_name}: coefficient record mismatch")
        if any(c > 2 for c in coefficients):
            raise AssertionError(f"{block_name}: cost exceeds twice block span")


def poly_add(a: dict[tuple[int, ...], int], b: dict[tuple[int, ...], int]):
    out = dict(a)
    for monomial, coefficient in b.items():
        out[monomial] = out.get(monomial, 0) + coefficient
        if out[monomial] == 0:
            del out[monomial]
    return out


def poly_scale(c: int, a: dict[tuple[int, ...], int]):
    return {m: c * v for m, v in a.items() if c * v}


def verify_tangent_certificate(cert: dict[str, object]) -> None:
    # Variable order: L, x, y, phiPrime, b, signedFourA.
    L = {(1, 0, 0, 0, 0, 0): 1}
    x = {(0, 1, 0, 0, 0, 0): 1}
    y = {(0, 0, 1, 0, 0, 0): 1}
    phi = {(0, 0, 0, 1, 0, 0): 1}
    b = {(0, 0, 0, 0, 1, 0): 1}
    four_a = {(0, 0, 0, 0, 0, 1): 1}

    def mul(a, c):
        out: dict[tuple[int, ...], int] = {}
        for ma, ca in a.items():
            for mb, cb in c.items():
                m = tuple(u + v for u, v in zip(ma, mb))
                out[m] = out.get(m, 0) + ca * cb
        return {m: v for m, v in out.items() if v}

    # R Taylor representative: (L-phi')x + Ly.
    r = poly_add(mul(poly_add(L, poly_scale(-1, phi)), x), mul(L, y))
    left = mul(b, r)
    kappa = poly_add(mul(four_a, L), poly_scale(-1, mul(b, phi)))
    defect = poly_add(left, poly_scale(-1, mul(kappa, x)))

    # It must equal L * (b*y - (signedFourA-b)*x).
    normalized = poly_add(
        mul(b, y),
        poly_scale(-1, mul(poly_add(four_a, poly_scale(-1, b)), x)),
    )
    expected = mul(L, normalized)
    if defect != expected:
        raise AssertionError("tangent-defect symbolic identity failed")
    if cert["defect_polynomial_terms"] != len(defect):
        raise AssertionError("tangent-defect term count mismatch")


def scan_threshold(prime_counts: list[int]) -> dict[str, object]:
    ln2 = ln_interval(2)
    ln3 = ln_interval(3)
    log_factorial: Interval = (Decimal(0), Decimal(0))
    for j in range(2, SCAN_START):
        log_factorial = add_interval(log_factorial, ln_interval(j))

    last_failure = None
    first_pass = None
    ambiguous_exact: list[int] = []
    verdict_bits = bytearray((ANALYTIC_TAIL_START - SCAN_START + 7) // 8)
    previous_lnk = ln_interval(SCAN_START - 1)
    previous_q = None
    lnq: Interval | None = None

    for k in range(SCAN_START, ANALYTIC_TAIL_START):
        p = prime_counts[k]
        q = k // 2
        delta = k % 2
        d0 = (708_827 * k * k) // 5_000_000 + 1
        exponent = k - p - q - delta
        if exponent <= 0:
            raise AssertionError(f"nonpositive d exponent at k={k}")

        if k == SCAN_START:
            lnkm1 = previous_lnk
        else:
            lnkm1 = previous_lnk
            log_factorial = add_interval(log_factorial, lnkm1)
        lnk = ln_interval(k)
        previous_lnk = lnk
        if q != previous_q:
            lnq = ln_interval(q)
            previous_q = q
        assert lnq is not None

        lhs_log: Interval = (Decimal(0), Decimal(0))
        for coefficient, value in (
            (k - p, lnk),
            (exponent, ln_interval(d0)),
            (delta, ln2),
            (q, lnq),
        ):
            lhs_log = add_interval(lhs_log, scale_interval(coefficient, value))

        rhs_log = log_factorial
        for coefficient, value in (
            (p + delta, ln3),
            (q + k - 2 * p, ln2),
            (q, lnkm1),
            (q, ln_interval(q + 2 * k + 2)),
        ):
            rhs_log = add_interval(rhs_log, scale_interval(coefficient, value))

        margin = sub_interval(lhs_log, rhs_log)
        if margin[0] > 0:
            passed = True
        elif margin[1] < 0:
            passed = False
        else:
            ambiguous_exact.append(k)
            lhs, rhs, _ = exact_sides(k, p)
            passed = lhs > rhs

        index = k - SCAN_START
        if passed:
            verdict_bits[index // 8] |= 1 << (index % 8)
            if first_pass is None:
                first_pass = k
        else:
            last_failure = k

    if last_failure is None or first_pass is None:
        raise AssertionError("threshold scan did not contain both verdicts")
    return {
        "first_pass": first_pass,
        "last_failure": last_failure,
        "K0": last_failure + 1,
        "ambiguous_exact": ambiguous_exact,
        "verdict_bitset_sha256": sha256_bytes(bytes(verdict_bits)),
    }


def load_json(path: Path) -> dict[str, object]:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--print-values",
        action="store_true",
        help="print recomputed certificate values as JSON",
    )
    args = parser.parse_args()

    threshold_cert = load_json(THRESHOLD_CERT)
    secant_cert = load_json(SECANT_CERT)
    tangent_cert = load_json(TANGENT_CERT)
    verify_block_pairing_certificate(secant_cert)
    verify_tangent_certificate(tangent_cert)

    counts, sieve_bytes = sieve_prime_counts(ANALYTIC_TAIL_START)
    scan = scan_threshold(counts)
    recomputed = {
        "scan": scan,
        "pi_1000000": counts[ANALYTIC_TAIL_START],
        "sieve_sha256": sha256_bytes(sieve_bytes),
        "boundary": [
            exact_boundary_record(18_985, counts[18_985]),
            exact_boundary_record(18_986, counts[18_986]),
        ],
        "analytic_seed_even": (
            4 * 7**4 * 10**12 > 3 * 50**4 * 10**5
        ),
        "analytic_seed_odd": (
            4 * 7**4 * 10**12 > 3 * 50**4 * 11**5
        ),
    }
    if args.print_values:
        print(json.dumps(recomputed, indent=2))

    for key in (
        "pi_1000000",
        "sieve_sha256",
        "boundary",
        "analytic_seed_even",
        "analytic_seed_odd",
    ):
        if threshold_cert[key] != recomputed[key]:
            raise AssertionError(f"threshold certificate mismatch: {key}")
    for key in (
        "first_pass",
        "last_failure",
        "K0",
        "ambiguous_exact",
        "verdict_bitset_sha256",
    ):
        if threshold_cert["scan"][key] != scan[key]:
            raise AssertionError(f"threshold scan mismatch: {key}")

    print("PASS: matching-tail certificates verified")
    print(
        f"exact pi({ANALYTIC_TAIL_START}) = "
        f"{counts[ANALYTIC_TAIL_START]}"
    )
    print(
        f"last failure = {scan['last_failure']}; "
        f"minimal certified suffix K0 = {scan['K0']}"
    )
    print(
        f"ambiguous interval cases resolved exactly: "
        f"{len(scan['ambiguous_exact'])}"
    )
    print("No floating-point acceptance conditions were used.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
