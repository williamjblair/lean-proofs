#!/usr/bin/env python3
"""Enumerate exact MW-sieve lifts under a certified curve-height bound."""

from __future__ import annotations

import argparse
import json
import math
from fractions import Fraction
from pathlib import Path

try:
    from .verify_packets import normalize, phi
except ImportError:
    from verify_packets import normalize, phi


HERE = Path(__file__).resolve().parent
PACKETS = HERE / "packets.json"
HEIGHT_CERTIFICATE = HERE / "kummer_height_upper_certificate.json"


def integer_vectors_in_ball(bound: int):
    radius = math.isqrt(bound)
    for a in range(-radius, radius + 1):
        for b in range(-radius, radius + 1):
            partial2 = a*a + b*b
            if partial2 > bound:
                continue
            for c in range(-radius, radius + 1):
                partial3 = partial2 + c*c
                if partial3 > bound:
                    continue
                for d in range(-radius, radius + 1):
                    partial4 = partial3 + d*d
                    if partial4 > bound:
                        continue
                    last_radius = math.isqrt(bound - partial4)
                    for e in range(-last_radius, last_radius + 1):
                        yield (a, b, c, d, e)


def coefficient_ball_bound(
    curve_height_bound: int,
    delta_max_l1_norm: int,
) -> dict[str, object]:
    height_power = max(1, (curve_height_bound - 1).bit_length())
    assert curve_height_bound < 2**height_power
    delta_power = max(1, (delta_max_l1_norm - 1).bit_length())
    assert delta_max_l1_norm < 2**delta_power
    # log(2) < 1 gives a completely rational, deliberately coarse bound.
    canonical_upper = (
        Fraction(3 * height_power + 5, 1)
        + Fraction(delta_power, 3)
    )
    squared_norm_upper = Fraction(200, 43) * canonical_upper
    squared_norm_bound = (
        squared_norm_upper.numerator // squared_norm_upper.denominator
    )
    return {
        "curve_multiplicative_height_bound": curve_height_bound,
        "curve_height_power_of_two_exponent": height_power,
        "delta_power_of_two_exponent": delta_power,
        "canonical_height_upper_rational": str(canonical_upper),
        "squared_coefficient_norm_upper_rational":
            str(squared_norm_upper),
        "squared_coefficient_norm_bound": squared_norm_bound,
        "log_two_bound_used": "log(2) < 1",
    }


def run(curve_height_bound: int) -> dict[str, object]:
    packet_data = json.loads(PACKETS.read_text())
    height_data = json.loads(HEIGHT_CERTIFICATE.read_text())
    bound_data = coefficient_ball_bound(
        curve_height_bound,
        int(height_data["delta_max_l1_norm"]),
    )
    squared_bound = int(bound_data["squared_coefficient_norm_bound"])

    packets = []
    for prime_text, packet in sorted(
        packet_data["packets"].items(), key=lambda item: int(item[0])
    ):
        invariants = tuple(packet["invariants"])
        packets.append({
            "prime": int(prime_text),
            "invariants": invariants,
            "basis": [
                normalize(generator, invariants)
                for generator in packet["basis"]
            ],
            "image": {
                normalize(element, invariants)
                for element in packet["image"]
            },
        })

    known = {
        tuple(point["vector"])
        for point in packet_data["known_affine_points"]
    }
    known.update(
        tuple(point["vector"])
        for point in packet_data["known_infinity_points"]["points"]
    )
    stage_counts = [0] * (len(packets) + 1)
    survivors = []
    for vector in integer_vectors_in_ball(squared_bound):
        stage_counts[0] += 1
        for stage, packet in enumerate(packets, 1):
            image = phi(
                vector, packet["basis"], packet["invariants"]
            )
            if image not in packet["image"]:
                break
            stage_counts[stage] += 1
        else:
            survivors.append(vector)

    assert set(survivors) == known
    first_exact_stage = next(
        stage for stage, count in enumerate(stage_counts)
        if count == len(known)
    )
    return {
        "verdict": "PASS",
        **bound_data,
        "integer_vectors_in_ball": stage_counts[0],
        "packet_primes": [packet["prime"] for packet in packets],
        "incremental_survivor_counts": stage_counts,
        "first_exact_packet_stage": first_exact_stage,
        "first_exact_packet_prime": packets[first_exact_stage - 1]["prime"],
        "surviving_vector_count": len(survivors),
        "surviving_vectors": [list(vector) for vector in sorted(survivors)],
        "known_projective_vector_count": len(known),
        "survivors_equal_known_projective_vectors": True,
        "absolute_curve_height_bound_proved": False,
        "rational_points_proved_complete": False,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--curve-height-bound", type=int, default=20000)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run(args.curve_height_bound)
    if args.output is not None:
        args.output.write_text(
            json.dumps(result, indent=2, sort_keys=True) + "\n"
        )
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
