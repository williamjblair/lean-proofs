#!/usr/bin/env python3
"""Hostile exact verifier for the k=5 Mordell-Weil sieve packets."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from collections import defaultdict, deque
from fractions import Fraction
from pathlib import Path
from typing import Iterable


HERE = Path(__file__).resolve().parent
PACKETS = HERE / "packets.json"

GroupElement = tuple[int, ...]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def determinant(matrix: list[list[int]]) -> int:
    """Exact Bareiss determinant."""
    work = [row[:] for row in matrix]
    size = len(work)
    sign = 1
    denominator = 1
    for column in range(size - 1):
        pivot = next(
            (row for row in range(column, size)
             if work[row][column] != 0),
            None,
        )
        if pivot is None:
            return 0
        if pivot != column:
            work[column], work[pivot] = work[pivot], work[column]
            sign = -sign
        pivot_value = work[column][column]
        for row in range(column + 1, size):
            for index in range(column + 1, size):
                work[row][index] = (
                    work[row][index] * pivot_value
                    - work[row][column] * work[column][index]
                ) // denominator
            work[row][column] = 0
        denominator = pivot_value
    return sign * work[-1][-1]


def normalize(
    element: Iterable[int], invariants: tuple[int, ...]
) -> GroupElement:
    values = tuple(element)
    assert len(values) == len(invariants)
    return tuple(value % modulus
                 for value, modulus in zip(values, invariants))


def add(
    left: GroupElement,
    right: GroupElement,
    invariants: tuple[int, ...],
) -> GroupElement:
    return tuple(
        (a + b) % modulus
        for a, b, modulus in zip(left, right, invariants)
    )


def generated_subgroup(
    generators: list[GroupElement],
    invariants: tuple[int, ...],
) -> set[GroupElement]:
    zero = (0,) * len(invariants)
    subgroup = {zero}
    queue = deque([zero])
    while queue:
        current = queue.popleft()
        for generator in generators:
            following = add(current, generator, invariants)
            if following not in subgroup:
                subgroup.add(following)
                queue.append(following)
    return subgroup


def phi(
    vector: list[int],
    basis: list[GroupElement],
    invariants: tuple[int, ...],
) -> GroupElement:
    assert len(vector) == len(basis) == 5
    return tuple(
        sum(vector[index] * basis[index][coordinate]
            for index in range(5)) % invariants[coordinate]
        for coordinate in range(len(invariants))
    )


def fraction_string(numerator: int, denominator: int) -> str:
    return str(Fraction(numerator, denominator))


def verify_curve_point(x_text: str, y_text: str) -> None:
    x = Fraction(x_text)
    y = Fraction(y_text)
    rhs = (
        9 * x**6 + 64 * x**5 - 200 * x**3 + 64 * x + 144
    )
    assert y**2 == rhs


def verify_packets() -> dict[str, object]:
    data = json.loads(PACKETS.read_text())
    assert data["schema"] == (
        "erdos686.k5_genus2.mordell_weil_sieve_packets.v1"
    )
    known = data["known_affine_points"]
    assert len(known) == 34
    assert len({
        (point["x"], point["y"], tuple(point["vector"]))
        for point in known
    }) == 34
    for point in known:
        assert len(point["vector"]) == 5
        verify_curve_point(point["x"], point["y"])

    point_lookup = {
        (point["x"], point["y"]): point["vector"]
        for point in known
    }
    unimodular_points = [
        ("-20", "19308"),
        ("-20", "-19308"),
        ("-38/5", "55764/125"),
        ("-2", "12"),
        ("-1", "15"),
    ]
    unimodular_matrix = [
        point_lookup[point] for point in unimodular_points
    ]
    assert abs(determinant(unimodular_matrix)) == 1

    packet_results: dict[str, object] = {}
    surjective_primes: list[int] = []
    nonsurjective_primes: list[int] = []
    all_known_survive = True

    for prime_text, packet in sorted(
        data["packets"].items(), key=lambda item: int(item[0])
    ):
        prime = int(prime_text)
        invariants = tuple(int(value)
                           for value in packet["invariants"])
        assert invariants
        assert all(modulus > 1 for modulus in invariants)
        assert all(
            following % current == 0
            for current, following
            in zip(invariants, invariants[1:])
        )

        basis_raw = packet["basis"]
        assert len(basis_raw) == 5
        basis = [
            normalize(generator, invariants)
            for generator in basis_raw
        ]
        assert basis_raw == [list(generator) for generator in basis]

        image_raw = packet["image"]
        image = {
            normalize(element, invariants)
            for element in image_raw
        }
        assert len(image_raw) == len(image)
        assert image_raw == [list(element) for element in sorted(image)]

        subgroup = generated_subgroup(basis, invariants)
        ambient_order = math.prod(invariants)
        subgroup_order = len(subgroup)
        assert ambient_order % subgroup_order == 0
        surjective = subgroup_order == ambient_order
        if surjective:
            surjective_primes.append(prime)
        else:
            nonsurjective_primes.append(prime)

        reachable_image = image & subgroup
        unreachable_image = image - subgroup
        known_classes: dict[GroupElement, list[int]] = defaultdict(list)
        failed_points: list[dict[str, object]] = []
        for index, point in enumerate(known):
            reduction = phi(point["vector"], basis, invariants)
            known_classes[reduction].append(index)
            if reduction not in image:
                failed_points.append({
                    "index": index,
                    "x": point["x"],
                    "y": point["y"],
                    "vector": point["vector"],
                    "reduction": list(reduction),
                })
        if failed_points:
            all_known_survive = False

        packet_results[prime_text] = {
            "invariants": list(invariants),
            "ambient_group_order": ambient_order,
            "reduction_image_order": subgroup_order,
            "surjective": surjective,
            "curve_image_size": len(image),
            "reachable_curve_image_size": len(reachable_image),
            "unreachable_curve_image_size": len(unreachable_image),
            "raw_packet_ratio": fraction_string(
                len(image), subgroup_order
            ),
            "effective_density": fraction_string(
                len(reachable_image), subgroup_order
            ),
            "all_known_points_survive": not failed_points,
            "failed_known_points": failed_points,
            "known_class_count": len(known_classes),
            "known_class_multiplicities": sorted(
                len(indices) for indices in known_classes.values()
            ),
            "known_class_merges": [
                {
                    "class": list(group_class),
                    "point_indices": indices,
                }
                for group_class, indices in sorted(known_classes.items())
                if len(indices) > 1
            ],
            "unreachable_curve_image": [
                list(element) for element in sorted(unreachable_image)
            ],
        }

    assert all_known_survive
    assert surjective_primes == [
        7, 11, 13, 17, 19, 23, 29, 31, 41, 43, 47, 53, 59
    ]
    assert nonsurjective_primes == [37]
    assert packet_results["37"]["reachable_curve_image_size"] == 27

    return {
        "verdict": "PASS",
        "packet_file": str(PACKETS.relative_to(HERE.parents[3])),
        "packet_sha256": sha256(PACKETS),
        "packet_count": len(packet_results),
        "known_affine_point_count": len(known),
        "unimodular_known_basis_determinant":
            determinant(unimodular_matrix),
        "all_known_points_survive": all_known_survive,
        "surjective_primes": surjective_primes,
        "nonsurjective_primes": nonsurjective_primes,
        "packets": packet_results,
        "infinity_vectors_certified": bool(
            data["known_infinity_points"].get("points")
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = verify_packets()
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        args.output.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
