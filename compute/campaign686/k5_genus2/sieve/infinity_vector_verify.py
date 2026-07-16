#!/usr/bin/env python3
"""Verify the two infinity vectors in the fixed reduced Magma basis."""

from __future__ import annotations

import argparse
import json
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from pathlib import Path

try:
    from .verify_packets import normalize, phi
except ImportError:
    from verify_packets import normalize, phi


HERE = Path(__file__).resolve().parent
PACKETS = HERE / "packets.json"
MAGMA_SOURCE = HERE / "magma_infinity_vectors.m"


def verify_offline() -> dict[str, object]:
    data = json.loads(PACKETS.read_text())
    infinity = data["known_infinity_points"]["points"]
    assert len(infinity) == 2
    expected = {
        ("1", "-3", "0"): [0, 1, 0, 1, 0],
        ("1", "3", "0"): [-2, 0, 0, 0, 0],
    }
    assert {
        tuple(point["original_weighted_projective"]): point["vector"]
        for point in infinity
    } == expected
    for point in infinity:
        original = [int(value)
                    for value in point["original_weighted_projective"]]
        reduced = [int(value)
                   for value in point["reduced_weighted_projective"]]
        assert original[2] == reduced[2] == 0
        assert original[1] ** 2 == 9 * original[0] ** 6
        assert reduced[1] ** 2 == 36 * reduced[0] ** 6
        assert len(point["vector"]) == 5

    failures: list[dict[str, object]] = []
    for prime_text, packet in sorted(
        data["packets"].items(), key=lambda item: int(item[0])
    ):
        invariants = tuple(packet["invariants"])
        basis = [
            normalize(generator, invariants)
            for generator in packet["basis"]
        ]
        image = {
            normalize(element, invariants)
            for element in packet["image"]
        }
        for point in infinity:
            reduction = phi(point["vector"], basis, invariants)
            if reduction not in image:
                failures.append({
                    "prime": int(prime_text),
                    "point": point["original_weighted_projective"],
                    "reduction": list(reduction),
                })
    assert failures == []

    projective_vectors = [
        tuple(point["vector"]) for point in data["known_affine_points"]
    ] + [tuple(point["vector"]) for point in infinity]
    assert len(projective_vectors) == 36
    assert len(set(projective_vectors)) == 36
    return {
        "verdict": "PASS",
        "infinity_point_count": 2,
        "known_projective_vector_count": 36,
        "vectors": [
            {
                "original_weighted_projective": list(point),
                "vector": vector,
            }
            for point, vector in sorted(expected.items())
        ],
        "all_infinity_vectors_survive_all_packets": True,
    }


def run_online() -> str:
    payload = urllib.parse.urlencode(
        {"input": MAGMA_SOURCE.read_text()}
    ).encode()
    request = urllib.request.Request(
        "http://magma.maths.usyd.edu.au/xml/calculator.xml",
        data=payload,
        headers={"User-Agent": "Mozilla/5.0"},
        method="POST",
    )
    with urllib.request.urlopen(request, timeout=75) as response:
        root = ET.fromstring(response.read())
    output = "\n".join(
        node.text or "" for node in root.findall("./results/line")
    )
    required = [
        "MW_INVARIANTS [ 0, 0, 0, 0, 0 ]",
        "FINITE_INDEX true",
        "PROVED true",
        "RANK_BOUND 5",
        "INFINITY_PLUS_COORDINATES [ -2, 0, 0, 0, 0 ]",
        "INFINITY_MINUS_COORDINATES [ 0, 1, 0, 1, 0 ]",
    ]
    missing = [marker for marker in required if marker not in output]
    assert missing == [], (missing, output)
    return output


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--online", action="store_true")
    args = parser.parse_args()
    result = verify_offline()
    if args.online:
        result["online_magma_output"] = run_online()
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
