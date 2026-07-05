from __future__ import annotations

import argparse
import json
from collections.abc import Iterable
from typing import Any

from compute.erdos699 import counterexample_candidate, primes_upto


def _sorted_i_values(i_values: Iterable[int] | None) -> list[int] | None:
    if i_values is None:
        return None
    values = sorted(set(i_values))
    for i in values:
        if i < 1:
            raise ValueError("i values must be positive")
    return values


def scan_full(limit: int, i_values: Iterable[int] | None = None) -> dict[str, Any]:
    if limit < 0:
        raise ValueError("limit must be nonnegative")
    selected_i = _sorted_i_values(i_values)
    primes = primes_upto(limit)
    candidates: list[dict[str, int]] = []
    checked_triples = 0

    for n in range(1, limit + 1):
        half = n // 2
        if selected_i is None:
            row_i_values = range(1, half)
        else:
            row_i_values = (i for i in selected_i if i < half)
        for i in row_i_values:
            for j in range(i + 1, half + 1):
                checked_triples += 1
                if counterexample_candidate(n, i, j, primes=primes):
                    candidates.append({"n": n, "i": i, "j": j})

    return {
        "mode": "full",
        "algorithm": "short_circuit_obstruction",
        "limit": limit,
        "i_values": selected_i,
        "checked_triples": checked_triples,
        "candidate_count": len(candidates),
        "candidates": candidates,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Exact Erdős #699 Lucas-criterion full sweep."
    )
    parser.add_argument("--limit", type=int, required=True)
    parser.add_argument("--i", dest="i_values", type=int, action="append")
    args = parser.parse_args(argv)

    result = scan_full(args.limit, i_values=args.i_values)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
