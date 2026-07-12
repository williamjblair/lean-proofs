#!/usr/bin/env python3
"""Exact CF/primitive-scale audit for the odd tails of Erdos 686.

This verifier uses only Python integers.  It combines three proper
consequences of a hypothetical centered solution

    P_k(g*u) = 4 P_k(g*v),  gcd(u,v) = 1,  z = g^2,

for odd ``k = 2*r+1``:

* the constant scale coefficient gives ``z | (r!)^2 * (4*v-u)``;
* the alternating scale polynomial pins
  ``z = floor(e_1*A_(k-2)/A_k)`` once its explicit coefficient chain holds;
* the already-proved CF confinement lists finitely many reduced pairs in
  each interval ``q_m <= v < q_(m+1)``.

The target gap bound forces ``v >= 10^77``.  The 341 checked-in CF rows then
give an exact exclusion through ``v < q_340``.  Together with the banked
uniform lower ratio ``X/Y > 109651/100000`` this covers the genuinely new
gap band ``10^120 <= d < 10^166`` for all six odd k.

The script does not claim an infinite-tail proof.  It emits all counts and
source hashes needed to reproduce the finite computation exactly.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
ARTIFACT_DIR = REPO_ROOT / "compute" / "artifacts"

TARGET_K = (5, 7, 9, 11, 13, 15)
TARGET_GAP_LOWER = 10**120
NEW_GAP_UPPER = 10**166
PRIMITIVE_DENOMINATOR_LOWER = 10**77

# The weakest banked centered-ratio lower bound is the k=15 bound.
UNIFORM_RATIO_LOWER_NUMERATOR = 109_651
UNIFORM_RATIO_LOWER_DENOMINATOR = 100_000

# e_r = product(1^2,...,r^2) = (r!)^2; the maximum occurs at r=7.
MAX_CONSTANT_COEFFICIENT = 25_401_600

EXPECTED_ARTIFACT_SHA256 = {
    5: "d2c4dc4d5cc1a4da808223513de008a69cd1eab133d7b715632d1f26f73e0873",
    7: "8cd0b87e05ed6ec08cebe3ad2f43935882afcafc31acc23b01a4523945316ea2",
    9: "e86fc380e2aa40969da43ac0014217783a0f58771bcd220cdee82fe6ebf38fd0",
    11: "33c9bcfa2020f8bb334529807fcf69c62aa1fdf214e53c00a95a5430dd9ed863",
    13: "356dc2cf29b353329b4b114071ead0ccdbd5d42a5c840df345e1692ee4fd69b1",
    15: "89e0969a2f912d7c5abf6ff0946b987fab0ecfa2079217fb0b8d48c21e31b2d3",
}


EXPECTED_COUNTS = {
    5: {
        "candidate_pairs": 433,
        "below_alpha": 219,
        "reduced_below_alpha": 219,
        "eligible_denominator": 118,
        "positive_floor": 64,
        "square_floor": 38,
        "square_floor_g_ge_2": 2,
        "constant_divisor_pass": 37,
    },
    7: {
        "candidate_pairs": 529,
        "below_alpha": 267,
        "reduced_below_alpha": 267,
        "eligible_denominator": 154,
        "positive_floor": 115,
        "square_floor": 64,
        "square_floor_g_ge_2": 5,
        "constant_divisor_pass": 63,
    },
    9: {
        "candidate_pairs": 648,
        "below_alpha": 316,
        "reduced_below_alpha": 297,
        "eligible_denominator": 183,
        "positive_floor": 136,
        "square_floor": 81,
        "square_floor_g_ge_2": 14,
        "constant_divisor_pass": 79,
    },
    11: {
        "candidate_pairs": 853,
        "below_alpha": 422,
        "reduced_below_alpha": 393,
        "eligible_denominator": 211,
        "positive_floor": 165,
        "square_floor": 94,
        "square_floor_g_ge_2": 14,
        "constant_divisor_pass": 93,
    },
    13: {
        "candidate_pairs": 996,
        "below_alpha": 495,
        "reduced_below_alpha": 458,
        "eligible_denominator": 266,
        "positive_floor": 204,
        "square_floor": 114,
        "square_floor_g_ge_2": 20,
        "constant_divisor_pass": 114,
    },
    15: {
        "candidate_pairs": 1217,
        "below_alpha": 596,
        "reduced_below_alpha": 533,
        "eligible_denominator": 281,
        "positive_floor": 217,
        "square_floor": 120,
        "square_floor_g_ge_2": 23,
        "constant_divisor_pass": 120,
    },
}


@dataclass(frozen=True)
class CandidateSource:
    kind: str
    index: int
    first: int
    second: int


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def centered_polynomial(k: int, value: int) -> int:
    result = value
    for j in range(1, (k - 1) // 2 + 1):
        result *= value * value - j * j
    return result


def elementary_square_coefficients(k: int) -> list[int]:
    """Elementary symmetric coefficients of 1^2,...,r^2."""
    coefficients = [1]
    for square in (j * j for j in range(1, (k - 1) // 2 + 1)):
        coefficients.append(0)
        for index in range(len(coefficients) - 1, 0, -1):
            coefficients[index] += square * coefficients[index - 1]
    return coefficients


def a_value(u: int, v: int, exponent: int) -> int:
    return 4 * v**exponent - u**exponent


def scale_residual(k: int, u: int, v: int, g: int) -> int:
    """Reduced form of P_k(g*u)-4*P_k(g*v), divided by g."""
    r = (k - 1) // 2
    z = g * g
    coefficients = elementary_square_coefficients(k)
    return sum(
        (-1) ** j
        * coefficients[j]
        * z ** (r - j)
        * (u ** (k - 2 * j) - 4 * v ** (k - 2 * j))
        for j in range(r + 1)
    )


def verify_cf_artifact(k: int, path: Path) -> dict[str, Any]:
    digest = sha256(path)
    if digest != EXPECTED_ARTIFACT_SHA256[k]:
        raise AssertionError(f"k={k}: source artifact SHA-256 changed")
    payload = json.loads(path.read_text())
    if payload["k"] != k or payload["num_rows"] != 341:
        raise AssertionError(f"unexpected k={k} artifact shape")
    if payload["index_range"] != [0, 340]:
        raise AssertionError(f"unexpected k={k} index range")
    if payload["generated_by"] != "compute/theory/gen_thue_convergents.py":
        raise AssertionError(f"unexpected k={k} generator")

    rows = payload["data"]
    for index, row in enumerate(rows):
        p, q, declared_difference, next_partial_quotient = map(int, row)
        difference = p**k - 4 * q**k
        if difference != declared_difference:
            raise AssertionError(f"k={k}, row={index}: power difference changed")
        if (difference < 0) != (index % 2 == 0):
            raise AssertionError(f"k={k}, row={index}: side alternation failed")
        if math.gcd(p, q) != 1:
            raise AssertionError(f"k={k}, row={index}: convergent not reduced")
        if index:
            pp, qq = map(int, rows[index - 1][:2])
            if p * qq - pp * q != (-1) ** (index - 1):
                raise AssertionError(f"k={k}, row={index}: determinant failed")

        if index < len(rows) - 1:
            previous_p, previous_q = (
                (1, 0) if index == 0 else tuple(map(int, rows[index - 1][:2]))
            )
            next_p, next_q = map(int, rows[index + 1][:2])
            if next_partial_quotient < 1:
                raise AssertionError(f"k={k}, row={index}: invalid CF digit")
            if (
                next_p != next_partial_quotient * p + previous_p
                or next_q != next_partial_quotient * q + previous_q
            ):
                raise AssertionError(f"k={k}, row={index}: CF recurrence failed")

            # The next semiconvergent crosses alpha.  Together with the
            # recurrence and monotonicity of x |-> x^k this pins the digit.
            crossed_p, crossed_q = next_p + p, next_q + q
            crossed_difference = crossed_p**k - 4 * crossed_q**k
            if (crossed_difference < 0) != (index % 2 == 0):
                raise AssertionError(
                    f"k={k}, row={index}: semiconvergent straddle failed"
                )

    q340 = int(rows[340][1])
    if not 11 * NEW_GAP_UPPER < q340:
        raise AssertionError(f"k={k}: q_340 does not cover the stated gap band")
    return {
        "path": str(path.relative_to(REPO_ROOT)),
        "sha256": digest,
        "headline_C": payload["headline_C"],
        "q_340": q340,
        "q_340_digits": len(str(q340)),
    }


def confinement_candidates(
    payload: dict[str, Any],
) -> dict[tuple[int, int], CandidateSource]:
    """Enumerate the exact self-contained confinement superset.

    For ``q_m <= v < q_(m+1)``, the three cases are

      1. (u,v) = (p_m,q_m), after reduction;
      2. (u,v) = r*(p_(m+1),q_(m+1))-t*(p_m,q_m);
      3. (u,v) = s*(p_m,q_m)-r*(p_(m+1),q_(m+1)).

    The loop bounds and inequalities are exactly those in the proved
    confinement statement recorded in ``compute/theory/oddk_9/note.md``.
    """
    numerator, denominator = map(int, payload["headline_C"])
    rows = payload["data"]
    candidates: dict[tuple[int, int], CandidateSource] = {}

    for index in range(len(rows) - 1):
        p, q = map(int, rows[index][:2])
        next_p, next_q = map(int, rows[index + 1][:2])
        cap = numerator * (q + next_q)

        candidates.setdefault(
            (p, q), CandidateSource("pure", index, 1, 0)
        )

        t = 1
        while t * q * denominator < cap:
            r = -((-(1 + t) * q) // next_q)
            v = r * next_q - t * q
            u = r * next_p - t * p
            if (
                1 <= r <= t
                and q <= v < next_q
                and t * v * denominator < cap
            ):
                candidates.setdefault(
                    (u, v), CandidateSource("forward-minus", index, r, t)
                )
            t += 1

        s = 2
        while s * q * denominator < cap:
            r = ((s - 1) * q) // next_q
            if r >= 1:
                v = s * q - r * next_q
                u = s * p - r * next_p
                if (
                    1 <= r <= s - 1
                    and q <= v < next_q
                    and s * v * denominator < cap
                ):
                    candidates.setdefault(
                        (u, v), CandidateSource("reverse-minus", index, s, r)
                    )
            s += 1

    return candidates


def pin_conditions(k: int, a_values: list[int]) -> bool:
    """Check the explicit sufficient chain for the signed floor pin."""
    coefficients = elementary_square_coefficients(k)
    r = (k - 1) // 2
    if not all(value > 0 for value in a_values):
        return False

    # The first omitted term is less than half of the leading correction.
    if not 2 * coefficients[2] * a_values[2] < coefficients[1] * a_values[1]:
        return False

    # Every later term of the alternating tail is strictly smaller than its
    # predecessor already at z=1, hence also at every z>=1.
    return all(
        coefficients[j] * a_values[j]
        > coefficients[j + 1] * a_values[j + 1]
        for j in range(2, r)
    )


def scan_one_k(k: int) -> dict[str, Any]:
    path = ARTIFACT_DIR / f"thue_convergents_k{k}.json"
    artifact = verify_cf_artifact(k, path)
    payload = json.loads(path.read_text())
    candidates = confinement_candidates(payload)
    coefficients = elementary_square_coefficients(k)
    r = (k - 1) // 2

    counts = {
        "candidate_pairs": len(candidates),
        "below_alpha": 0,
        "reduced_below_alpha": 0,
        "eligible_denominator": 0,
        "positive_floor": 0,
        "square_floor": 0,
        "square_floor_g_ge_2": 0,
        "constant_divisor_pass": 0,
        "exact_roots": 0,
    }
    nontrivial_square_floors: list[dict[str, Any]] = []

    for (u, v), source in candidates.items():
        if not (u > v and u**k < 4 * v**k):
            continue
        counts["below_alpha"] += 1
        if math.gcd(u, v) != 1:
            continue
        counts["reduced_below_alpha"] += 1
        if v < PRIMITIVE_DENOMINATOR_LOWER:
            continue
        counts["eligible_denominator"] += 1

        values = [a_value(u, v, k - 2 * j) for j in range(r + 1)]
        if not pin_conditions(k, values):
            raise AssertionError(f"k={k}, source={source}: floor-pin chain failed")

        z = (coefficients[1] * values[1]) // values[0]
        if z < 1:
            continue
        counts["positive_floor"] += 1
        g = math.isqrt(z)
        if g * g != z:
            continue
        counts["square_floor"] += 1
        if g >= 2:
            counts["square_floor_g_ge_2"] += 1

        constant_term = coefficients[-1] * values[-1]
        if constant_term % z:
            continue
        counts["constant_divisor_pass"] += 1

        if g >= 2:
            nontrivial_square_floors.append(
                {
                    "source": asdict(source),
                    "z": z,
                    "g": g,
                    "v_digits": len(str(v)),
                    "constant_quotient": constant_term // z,
                }
            )

        if scale_residual(k, u, v, g) == 0:
            counts["exact_roots"] += 1

    expected = EXPECTED_COUNTS[k]
    for key, value in expected.items():
        if counts[key] != value:
            raise AssertionError(
                f"k={k}: {key} changed from {value} to {counts[key]}"
            )
    if counts["exact_roots"] != 0:
        raise AssertionError(f"k={k}: an exact root was found")

    return {
        "k": k,
        "artifact": artifact,
        "coefficients": coefficients,
        "counts": counts,
        "nontrivial_square_floor_survivors_before_full_equation":
            nontrivial_square_floors,
    }


def telescope_checks() -> list[dict[str, Any]]:
    checks: list[dict[str, Any]] = []
    for k, v, u in ((9, 7, 8), (15, 12, 13)):
        coefficients = elementary_square_coefficients(k)
        r = (k - 1) // 2
        values = [a_value(u, v, k - 2 * j) for j in range(r + 1)]
        z = (coefficients[1] * values[1]) // values[0]
        checks.append(
            {
                "k": k,
                "u": u,
                "v": v,
                "g": 1,
                "z": z,
                "d": u - v,
                "large_denominator_sufficient_pin_conditions": pin_conditions(k, values),
                "floor_pin_holds": z == 1,
                "scale_residual": scale_residual(k, u, v, 1),
                "centered_equation": centered_polynomial(k, u)
                == 4 * centered_polynomial(k, v),
                "outside_disjoint_domain": u - v < k,
            }
        )
    if not all(
        check["z"] == 1
        and check["floor_pin_holds"]
        and check["scale_residual"] == 0
        and check["centered_equation"]
        and check["outside_disjoint_domain"]
        for check in checks
    ):
        raise AssertionError("a named d=1 telescope audit failed")
    return checks


def full_report() -> dict[str, Any]:
    # If v < 10^77, the scale bound d^2 < 3*(r!)^2*v^3 is incompatible
    # with d >= 10^120, uniformly since (r!)^2 <= 7!^2.
    denominator_margin = TARGET_GAP_LOWER**2 - (
        3 * MAX_CONSTANT_COEFFICIENT * PRIMITIVE_DENOMINATOR_LOWER**3
    )
    if denominator_margin <= 0:
        raise AssertionError("primitive denominator threshold is not certified")

    # 109651/100000 > 1 + 1/11, so v < 11*(u-v) <= 11*d.
    ratio_margin = 11 * (
        UNIFORM_RATIO_LOWER_NUMERATOR - UNIFORM_RATIO_LOWER_DENOMINATOR
    ) - UNIFORM_RATIO_LOWER_DENOMINATOR
    if ratio_margin <= 0:
        raise AssertionError("uniform ratio does not imply v < 11*(u-v)")

    scans = [scan_one_k(k) for k in TARGET_K]
    return {
        "status": "finite band excluded; infinite tail remains open",
        "exact_band": {
            "gap_lower_inclusive": TARGET_GAP_LOWER,
            "gap_upper_exclusive": NEW_GAP_UPPER,
            "primitive_denominator_lower": PRIMITIVE_DENOMINATOR_LOWER,
            "uniform_ratio_lower": [
                UNIFORM_RATIO_LOWER_NUMERATOR,
                UNIFORM_RATIO_LOWER_DENOMINATOR,
            ],
            "denominator_margin": denominator_margin,
            "ratio_to_v_lt_11_gap_margin": ratio_margin,
        },
        "telescope_checks": telescope_checks(),
        "per_k": scans,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--indent", type=int, default=2)
    args = parser.parse_args()
    report = full_report()
    rendered = json.dumps(report, indent=args.indent, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
