#!/usr/bin/env python3
"""Exact audit of the odd-tail scale-polynomial filters for Erdős 686.

For k = 5, write X = g*u, Y = g*v, z = g^2, gcd(u,v) = 1, and

    A_j = 4*v^j - u^j.

The centered equation P_5(X) = 4 P_5(Y) is exactly

    Q(z) = A_5*z^2 - 5*A_3*z + 4*A_1 = 0.

This module supplies three independently checkable artifacts:

* an infinite exact family with unbounded square z satisfying the correct
  ratio window, parity, gcd, constant-term congruence, and next-coefficient
  congruence, while Q(z) is provably positive;
* the exact k=5 floor-pinning lemma checker for a genuine root of Q;
* reproduction of the 341-convergent k=5 floor counts and the six stored
  odd-k z-adic scale-ladder counts.

No floating point is used anywhere.
"""

from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
ARTIFACT_DIR = REPO_ROOT / "compute" / "artifacts"
K5_CONVERGENTS = ARTIFACT_DIR / "thue_convergents_k5.json"

# G0 is divisible by 4*51, 71, and 251.  Those factors make the integrality,
# parity, and gcd proof for the parametric family uniform in t >= 1.
BASE_G = 204 * 71 * 251
BASE_Z = BASE_G**2

POSITIVITY_DENOMINATOR = 2_255_067
POSITIVITY_NEGATIVE_COEFFICIENT_SUM = 7_151_859_139_313_955

# Coefficients of R(z), highest degree first, in
#
#   POSITIVITY_DENOMINATOR * Q(z) = z^2 * R(z)
#
# after substituting the counterfamily u(z), v(z).
POSITIVITY_COEFFICIENTS = (
    907,
    -48_828_125,
    -14_943_141_610,
    -2_287_628_906_250,
    -175_247_492_914_005,
    -5_388_707_299_519_560,
    -1_430_018_958_108_645,
    -152_229_859_332_345,
    -3_352_908_563_415,
    544_813_575_120,
    38_300_057_928,
)

LEAN_Y_MIN = {
    5: 665,
    7: 887,
    9: 1109,
    11: 1552,
    13: 1774,
    15: 2217,
}

EXPECTED_SCALE_LADDER = {
    5: {"candidate_scales_g_ge_2": 161, "z_adic_passes": [83, 69]},
    7: {"candidate_scales_g_ge_2": 292, "z_adic_passes": [182, 115, 45]},
    9: {"candidate_scales_g_ge_2": 343, "z_adic_passes": [274, 195, 141, 89]},
    11: {
        "candidate_scales_g_ge_2": 462,
        "z_adic_passes": [352, 242, 189, 117, 27],
    },
    13: {
        "candidate_scales_g_ge_2": 505,
        "z_adic_passes": [474, 411, 324, 241, 230, 200],
    },
    15: {
        "candidate_scales_g_ge_2": 582,
        "z_adic_passes": [564, 477, 403, 317, 301, 254, 111],
    },
}

T1_FIXTURE = {
    "g": 3_635_484,
    "z": 13_216_743_914_256,
    "u": 85_628_588_086_786_850_048_487_604,
    "v": 65_077_726_945_204_651_633_737_985,
}


@dataclass(frozen=True)
class ScalePoint:
    t: int
    g: int
    z: int
    u: int
    v: int


def a_value(u: int, v: int, exponent: int) -> int:
    """Return A_exponent = 4*v^exponent - u^exponent exactly."""
    return 4 * v**exponent - u**exponent


def centered_polynomial(k: int, value: int) -> int:
    """P_k(T) = T * product_{1 <= j <= (k-1)/2} (T^2-j^2)."""
    result = value
    for j in range(1, (k - 1) // 2 + 1):
        result *= value * value - j * j
    return result


def elementary_square_coefficients(k: int) -> list[int]:
    """Elementary symmetric coefficients of 1^2,...,((k-1)/2)^2."""
    coefficients = [1]
    for square in (j * j for j in range(1, (k - 1) // 2 + 1)):
        coefficients.append(0)
        for index in range(len(coefficients) - 1, 0, -1):
            coefficients[index] += square * coefficients[index - 1]
    return coefficients


def k5_scale_residual(u: int, v: int, z: int) -> int:
    """Q(z) = A_5*z^2 - 5*A_3*z + 4*A_1."""
    return z * z * a_value(u, v, 5) - 5 * z * a_value(u, v, 3) + 4 * a_value(u, v, 1)


def scale_residual(k: int, u: int, v: int, g: int) -> int:
    """The full reduced scale polynomial for P_k(g*u) = 4 P_k(g*v)."""
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


def counterfamily_point(t: int) -> ScalePoint:
    """Return the t-th member of the unbounded exact counterfamily."""
    if t < 1:
        raise ValueError("t must be at least 1")
    g = BASE_G * t
    z = g * g
    if z % 51 != 0:
        raise AssertionError("BASE_G must make z/51 integral")
    v = 1 + 19 * z * z // 51
    u = 4 + 75 * z + 25 * z * z // 51
    return ScalePoint(t=t, g=g, z=z, u=u, v=v)


def positivity_polynomial(z: int) -> int:
    """Evaluate R(z) by Horner's rule."""
    result = 0
    for coefficient in POSITIVITY_COEFFICIENTS:
        result = result * z + coefficient
    return result


def two_adic_valuation(value: int) -> int:
    if value <= 0:
        raise ValueError("value must be positive")
    return (value & -value).bit_length() - 1


def verify_counterfamily(point: ScalePoint) -> dict[str, Any]:
    """Check every exact identity and inequality used by the falsification."""
    t, g, z, u, v = point.t, point.g, point.z, point.u, point.v
    if g != BASE_G * t or z != g * g:
        raise AssertionError("incorrect scale parametrization")
    if 51 * v != 51 + 19 * z * z:
        raise AssertionError("incorrect v parametrization")
    if 51 * u != 204 + 3_825 * z + 25 * z * z:
        raise AssertionError("incorrect u parametrization")

    a1 = a_value(u, v, 1)
    a3 = a_value(u, v, 3)
    a5 = a_value(u, v, 5)
    if a1 != z * (z - 75):
        raise AssertionError("A1 identity failed")
    if math.gcd(u, v) != 1:
        raise AssertionError("u and v must be coprime")
    if v % 2 != 1 or two_adic_valuation(u) != 2:
        raise AssertionError("required parity pattern failed")

    # Exact ratio window and exact algebraic-side certificate.
    if not 100 * u > 131 * v:
        raise AssertionError("lower ratio window failed")
    if not 160 * u < 211 * v:
        raise AssertionError("strong upper ratio window failed")
    if not 211**5 < 4 * 160**5:
        raise AssertionError("211/160 must lie below 4^(1/5)")
    if not 500 * u < 661 * v:
        raise AssertionError("headline upper ratio window failed")
    if not (a1 > 0 and a3 > 0 and a5 > 0):
        raise AssertionError("wrong side of an A_j sign condition")

    constant_congruence = (4 * a1) % z
    next_congruence = (4 * a1 - 5 * z * a3) % (z * z)
    if constant_congruence != 0 or next_congruence != 0:
        raise AssertionError("scale-polynomial congruence failed")

    # The large support of g is already separated from u, v, and u-v.
    if math.gcd(g, v) != 1:
        raise AssertionError("g and v support separation failed")
    if any(prime >= 5 for prime in _trial_prime_divisors(math.gcd(g, u - v))):
        raise AssertionError("large support of g met the reduced gap")

    q_value = k5_scale_residual(u, v, z)
    polynomial = positivity_polynomial(z)
    if POSITIVITY_DENOMINATOR * q_value != z * z * polynomial:
        raise AssertionError("explicit residual-polynomial identity failed")
    if POSITIVITY_NEGATIVE_COEFFICIENT_SUM != sum(
        -coefficient for coefficient in POSITIVITY_COEFFICIENTS[1:] if coefficient < 0
    ):
        raise AssertionError("negative-coefficient sum changed")
    positivity_margin = 907 * z - POSITIVITY_NEGATIVE_COEFFICIENT_SUM
    if positivity_margin <= 0 or polynomial <= 0 or q_value <= 0:
        raise AssertionError("explicit positivity certificate failed")

    return {
        **asdict(point),
        "gcd_u_v": math.gcd(u, v),
        "gcd_g_v": math.gcd(g, v),
        "gcd_g_reduced_gap": math.gcd(g, u - v),
        "v_is_odd": v % 2 == 1,
        "v2_u": two_adic_valuation(u),
        "ratio_lower_margin_100u_minus_131v": 100 * u - 131 * v,
        "ratio_upper_margin_211v_minus_160u": 211 * v - 160 * u,
        "alpha_side_margin_4x160pow5_minus_211pow5": 4 * 160**5 - 211**5,
        "A1": a1,
        "A3": a3,
        "A5": a5,
        "constant_congruence_remainder": constant_congruence,
        "next_congruence_remainder": next_congruence,
        "positivity_margin_907z_minus_negative_sum": positivity_margin,
        "Q": q_value,
        "Q_positive": q_value > 0,
    }


def _trial_prime_divisors(value: int) -> list[int]:
    """Small helper sufficient for gcds of the fixed counterfamily."""
    value = abs(value)
    result: list[int] = []
    candidate = 2
    while candidate * candidate <= value:
        if value % candidate == 0:
            result.append(candidate)
            while value % candidate == 0:
                value //= candidate
        candidate = 3 if candidate == 2 else candidate + 2
    if value > 1:
        result.append(value)
    return result


def k5_floor_pin(u: int, v: int, z: int) -> int:
    """Certify z = floor(5*A3/A5) under the exact k=5 root hypotheses.

    Hypotheses are v >= 2, z >= 1, 3*u < 4*v, A5 > 0, and Q(z) = 0.
    The proof is the integer inequality chain recorded in
    scale_filter_findings.md.
    """
    if v < 2 or z < 1 or not 3 * u < 4 * v:
        raise ValueError("floor-pin size hypotheses failed")
    a1 = a_value(u, v, 1)
    a3 = a_value(u, v, 3)
    a5 = a_value(u, v, 5)
    if a5 <= 0 or k5_scale_residual(u, v, z) != 0:
        raise ValueError("floor-pin equation hypotheses failed")

    # From 3u < 4v: 27*A3 > 44*v^3.  Together with A1 < 4v and
    # v >= 2 this gives 5*A3 > 8*A1.
    if not 27 * a3 > 44 * v**3:
        raise AssertionError("cubic lower bound failed")
    if not 220 * v**3 > 864 * v:
        raise AssertionError("v >= 2 comparison failed")
    if not 5 * a3 > 8 * a1:
        raise AssertionError("5*A3 > 8*A1 failed")

    # If z*A5 <= 4*A1, Q(z)=0 would imply 5*A3 <= 8*A1.
    if z * a5 <= 4 * a1:
        if not 5 * z * a3 <= 8 * z * a1:
            raise AssertionError("internal contradiction derivation failed")
        raise AssertionError("inconsistent root hypotheses")

    difference = 5 * a3 - z * a5
    if z * difference != 4 * a1:
        raise AssertionError("root rearrangement failed")
    if not 0 < difference < a5:
        raise AssertionError("floor interval failed")
    if (5 * a3) // a5 != z:
        raise AssertionError("floor conclusion failed")
    return z


def k5_convergent_floor_summary(path: Path = K5_CONVERGENTS) -> dict[str, Any]:
    """Reproduce the exact floor-filter counts on all 341 stored k=5 rows."""
    payload = json.loads(path.read_text())
    if payload["k"] != 5 or payload["num_rows"] != 341:
        raise AssertionError("unexpected k=5 convergent artifact")
    if payload["generated_by"] != "compute/theory/gen_thue_convergents.py":
        raise AssertionError("unexpected convergent generator")

    counts = {
        "rows": len(payload["data"]),
        "below_side_A5_positive": 0,
        "positive_floor": 0,
        "square_floor": 0,
        "square_floor_ge_4": 0,
        "square_floor_and_divides_4A1": 0,
        "square_floor_ge_4_and_divides_4A1": 0,
        "floor_candidate_exact_roots": 0,
    }
    square_ge_4: list[list[int]] = []
    square_divisor_ge_4: list[list[int]] = []

    for index, row in enumerate(payload["data"]):
        u, v = int(row[0]), int(row[1])
        a1 = a_value(u, v, 1)
        a3 = a_value(u, v, 3)
        a5 = a_value(u, v, 5)
        if a5 <= 0:
            continue
        counts["below_side_A5_positive"] += 1
        z = (5 * a3) // a5
        if z < 1:
            continue
        counts["positive_floor"] += 1
        if math.isqrt(z) ** 2 != z:
            continue
        counts["square_floor"] += 1
        if z >= 4:
            counts["square_floor_ge_4"] += 1
            square_ge_4.append([index, z])
        if (4 * a1) % z != 0:
            continue
        counts["square_floor_and_divides_4A1"] += 1
        if z >= 4:
            counts["square_floor_ge_4_and_divides_4A1"] += 1
            square_divisor_ge_4.append([index, z])
        if k5_scale_residual(u, v, z) == 0:
            counts["floor_candidate_exact_roots"] += 1

    return {
        "source": str(path.relative_to(REPO_ROOT)),
        "generated_by": payload["generated_by"],
        "index_range": payload["index_range"],
        **counts,
        "square_floor_ge_4_indices_and_z": square_ge_4,
        "square_floor_ge_4_divisor_indices_and_z": square_divisor_ge_4,
    }


def scale_ladder_summary(k: int, artifact_dir: Path = ARTIFACT_DIR) -> dict[str, Any]:
    """Reproduce z-adic necessary-filter counts on one 341-row artifact."""
    path = artifact_dir / f"thue_convergents_k{k}.json"
    payload = json.loads(path.read_text())
    if payload["k"] != k or payload["num_rows"] != 341:
        raise AssertionError(f"unexpected k={k} convergent artifact")
    numerator, denominator = map(int, payload["headline_C"])
    rows = payload["data"]
    r = (k - 1) // 2
    coefficients = elementary_square_coefficients(k)
    passes = [0] * r
    candidates = 0
    roots: list[list[int]] = []

    for index, row in enumerate(rows[:-1]):
        u, v = int(row[0]), int(row[1])
        next_v = int(rows[index + 1][1])
        g = 2
        while denominator * g * g * v < numerator * (v + next_v):
            if g * v >= LEAN_Y_MIN[k]:
                candidates += 1
                z = g * g
                alive = True
                for depth in range(1, r + 1):
                    truncated = sum(
                        (-1) ** j
                        * coefficients[j]
                        * z ** (r - j)
                        * (u ** (k - 2 * j) - 4 * v ** (k - 2 * j))
                        for j in range(r - depth + 1, r + 1)
                    )
                    alive = alive and truncated % (z**depth) == 0
                    if alive:
                        passes[depth - 1] += 1
                if scale_residual(k, u, v, g) == 0:
                    roots.append([index, g, u, v])
            g += 1

    return {
        "source": str(path.relative_to(REPO_ROOT)),
        "generated_by": payload["generated_by"],
        "rows": len(rows),
        "Y_min": LEAN_Y_MIN[k],
        "candidate_scales_g_ge_2": candidates,
        "z_adic_passes": passes,
        "exact_roots": roots,
    }


def telescope_checks() -> list[dict[str, int | bool]]:
    result: list[dict[str, int | bool]] = []
    for k, y, x in ((9, 7, 8), (15, 12, 13)):
        lhs = centered_polynomial(k, x)
        rhs = 4 * centered_polynomial(k, y)
        result.append(
            {
                "k": k,
                "Y": y,
                "X": x,
                "g": math.gcd(x, y),
                "z": math.gcd(x, y) ** 2,
                "d": x - y,
                "equation_holds": lhs == rhs,
                "outside_disjoint_domain": x - y < k,
            }
        )
    return result


def full_report(t: int = 1) -> dict[str, Any]:
    point = counterfamily_point(t)
    ladder = {str(k): scale_ladder_summary(k) for k in LEAN_Y_MIN}
    return {
        "counterfamily": verify_counterfamily(point),
        "positivity_certificate": {
            "denominator": POSITIVITY_DENOMINATOR,
            "negative_coefficient_sum": POSITIVITY_NEGATIVE_COEFFICIENT_SUM,
            "base_z": BASE_Z,
            "907_base_z": 907 * BASE_Z,
            "strict_margin": 907 * BASE_Z - POSITIVITY_NEGATIVE_COEFFICIENT_SUM,
        },
        "k5_341_convergent_floor_summary": k5_convergent_floor_summary(),
        "six_artifact_scale_ladder": ladder,
        "telescope_checks": telescope_checks(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--t", type=int, default=1, help="counterfamily index")
    parser.add_argument("--indent", type=int, default=2)
    args = parser.parse_args()
    print(json.dumps(full_report(args.t), indent=args.indent, sort_keys=True))


if __name__ == "__main__":
    main()

