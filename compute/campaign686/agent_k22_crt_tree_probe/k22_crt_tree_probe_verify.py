#!/usr/bin/env python3
"""Exact size audit for simple CRT trees in the bounded k=22 sieve.

The previously banked k=22 probe reduces the d >= 250 tail to

    1 <= t <= 3_795_146_531,
    t mod 46 in {17, 21, 25, 29},

and supplies 132 nontrivial prime masks A_p for p <= 953.  This verifier
asks whether those masks can be arranged as a small, proof-producing CRT
tree.  A simple tree chooses one unused prime at a live residue-class node,
branches over its locally allowed residues, and discards a child precisely
when its least positive CRT representative exceeds the bound.

All arithmetic here is integer arithmetic.  The result is a negative design
audit, not a Lean theorem and not a closure of row k=22.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import sys
from functools import lru_cache
from pathlib import Path
from typing import Iterable


CANDIDATE_BOUND = 3_795_146_531
BASE_MODULUS = 46
BASE_RESIDUES = (17, 21, 25, 29)
PRIME_LIMIT = 953
SIMPLE_NODE_TARGET = 1_000_000


def _load_sieve_probe():
    source = (
        Path(__file__).resolve().parents[1]
        / "agent_k22_sieve_probe"
        / "k22_sieve_probe_verify.py"
    )
    name = "_agent_k22_sieve_probe_verify"
    existing = sys.modules.get(name)
    if existing is not None:
        return existing
    spec = importlib.util.spec_from_file_location(name, source)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    # dataclasses inspect sys.modules while the imported module is executing.
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


SIEVE = _load_sieve_probe()


@lru_cache(maxsize=1)
def active_masks() -> tuple[tuple[int, frozenset[int]], ...]:
    """The exact nontrivial prime masks used by the p <= 953 sieve."""
    out: list[tuple[int, frozenset[int]]] = []
    for prime in SIEVE.primes_through(PRIME_LIMIT):
        if prime in (2, 3, 11, 23):
            continue
        allowed = SIEVE.local_allowed_t_residues(prime)
        if len(allowed) < prime:
            out.append((prime, allowed))
    return tuple(out)


def mask_inventory_sha256(masks: Iterable[tuple[int, frozenset[int]]]) -> str:
    payload = [[prime, sorted(allowed)] for prime, allowed in masks]
    encoded = json.dumps(payload, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def minimum_cyclic_window_hits(
    allowed: frozenset[int], prime: int, multiplier: int, length: int
) -> int:
    """Minimum hits in a cyclic interval after multiplying a residue mask.

    At a node t = r + Mq, a new p-mask becomes

        q in M^-1 A_p - M^-1 r  (mod p).

    The last term is an arbitrary translation for purposes of a uniform
    lower bound.  This function minimizes exactly over all p translations.
    It is called only when 0 < length < p.
    """
    assert 0 < length < prime
    assert 1 <= multiplier < prime
    marks = bytearray(prime)
    for residue in allowed:
        marks[(multiplier * residue) % prime] = 1
    assert sum(marks) == len(allowed)

    current = sum(marks[:length])
    answer = current
    for start in range(1, prime):
        current -= marks[start - 1]
        current += marks[(start + length - 1) % prime]
        answer = min(answer, current)
    return answer


def third_level_child_lower_bound(
    pair_modulus: int,
    interval_length: int,
    prime: int,
    allowed: frozenset[int],
) -> tuple[int, str]:
    """Uniform live-child lower bound for one third prime.

    Each second-level residue node has at least floor(B/M) representatives,
    written r + Mq with consecutive q starting at zero.  If that length is at
    least p, every allowed q residue occurs and the number of live CRT child
    classes is |A_p|.  Otherwise it is an exact cyclic-window minimum.
    """
    if interval_length >= prime:
        return len(allowed), "all_residues"
    multiplier = pow(pair_modulus % prime, -1, prime)
    return (
        minimum_cyclic_window_hits(
            allowed, prime, multiplier, interval_length
        ),
        "cyclic_window",
    )


def _record_dict(record: tuple[object, ...]) -> dict[str, object]:
    (
        total,
        p1,
        p2,
        a1,
        a2,
        pair_modulus,
        interval_length,
        third_children,
        p3,
        mode,
    ) = record
    return {
        "four_root_live_children": total,
        "one_root_live_children": total // len(BASE_RESIDUES),
        "p1": p1,
        "p2": p2,
        "p3": p3,
        "allowed_sizes": [a1, a2, third_children],
        "pair_modulus": pair_modulus,
        "minimum_node_interval_length": interval_length,
        "third_child_mode": mode,
    }


@lru_cache(maxsize=1)
def adaptive_three_level_certificate() -> dict[str, object]:
    """Optimize the rigorous third-level lower bound over all prime pairs.

    The scan permits p2 to vary from one p1-child to another and p3 to vary
    from one (p1,p2)-child to another.  For each pair it minimizes over every
    unused active p3 and over every possible translation of its q-mask.

    An exact cyclic-window computation is skipped only when the elementary
    cardinality lower bound max(0, |A| + L - p) cannot beat the best p3
    already found for that pair.
    """
    masks = active_masks()
    pair_count = 0
    exact_window_evaluations = 0
    global_record: tuple[object, ...] | None = None
    zero_third_child_pairs = 0

    for i, (p1, allowed1) in enumerate(masks):
        for p2, allowed2 in masks[i + 1 :]:
            pair_count += 1
            pair_modulus = BASE_MODULUS * p1 * p2
            interval_length = CANDIDATE_BOUND // pair_modulus
            best: tuple[int, int, str] | None = None

            for p3, allowed3 in masks:
                if p3 in (p1, p2):
                    continue

                if interval_length >= p3:
                    children = len(allowed3)
                    mode = "all_residues"
                else:
                    generic_lower = max(
                        0, len(allowed3) + interval_length - p3
                    )
                    if best is not None and generic_lower >= best[0]:
                        continue
                    children, mode = third_level_child_lower_bound(
                        pair_modulus, interval_length, p3, allowed3
                    )
                    exact_window_evaluations += 1

                candidate = (children, p3, mode)
                if best is None or candidate < best:
                    best = candidate

            assert best is not None
            if best[0] == 0:
                zero_third_child_pairs += 1

            total = (
                len(BASE_RESIDUES)
                * len(allowed1)
                * len(allowed2)
                * best[0]
            )
            record: tuple[object, ...] = (
                total,
                p1,
                p2,
                len(allowed1),
                len(allowed2),
                pair_modulus,
                interval_length,
                best[0],
                best[1],
                best[2],
            )
            if global_record is None or record < global_record:
                global_record = record

    assert global_record is not None
    assert pair_count == len(masks) * (len(masks) - 1) // 2
    return {
        "unordered_pair_count": pair_count,
        "potential_pair_third_tests": pair_count * (len(masks) - 2),
        "exact_cyclic_window_evaluations": exact_window_evaluations,
        "zero_third_child_pairs": zero_third_child_pairs,
        "global_minimum": _record_dict(global_record),
    }


def base_certificate() -> dict[str, object]:
    lengths = SIEVE.compressed_branch_lengths(CANDIDATE_BOUND)
    assert tuple(sorted(lengths)) == BASE_RESIDUES
    return {
        "candidate_bound": CANDIDATE_BOUND,
        "base_modulus": BASE_MODULUS,
        "base_residues": list(BASE_RESIDUES),
        "branch_lengths": {str(k): v for k, v in sorted(lengths.items())},
        "candidate_integer_count": sum(lengths.values()),
    }


@lru_cache(maxsize=1)
def audit() -> dict[str, object]:
    masks = active_masks()
    sizes = sorted((len(allowed), prime) for prime, allowed in masks)
    assert len(masks) == 132
    assert sizes[:3] == [(81, 83), (95, 97), (99, 101)]

    max_pair_modulus = max(
        BASE_MODULUS * p1 * p2
        for i, (p1, _) in enumerate(masks)
        for p2, _ in masks[i + 1 :]
    )
    # Hence no first- or second-level CRT child can be interval-pruned.
    assert max_pair_modulus == 41_514_586 < CANDIDATE_BOUND

    adaptive = adaptive_three_level_certificate()
    minimum = adaptive["global_minimum"]
    assert minimum == {
        "four_root_live_children": 3_047_220,
        "one_root_live_children": 761_805,
        "p1": 83,
        "p2": 97,
        "p3": 101,
        "allowed_sizes": [81, 95, 99],
        "pair_modulus": 370_346,
        "minimum_node_interval_length": 10_247,
        "third_child_mode": "all_residues",
    }
    assert adaptive["zero_third_child_pairs"] == 0
    assert minimum["four_root_live_children"] > SIMPLE_NODE_TARGET

    optimal_fixed_order = {
        "primes": [83, 97, 101],
        "moduli_by_level": [46, 3_818, 370_346, 37_404_946],
        "live_nodes_by_level": [4, 324, 30_780, 3_047_220],
    }

    return {
        "scope": {
            "prime_limit": PRIME_LIMIT,
            "active_prime_mask_count": len(masks),
            "mask_inventory_sha256": mask_inventory_sha256(masks),
            "tree_model": "one unused active prime mask per live CRT node",
        },
        "base": base_certificate(),
        "largest_two_prime_modulus": max_pair_modulus,
        "adaptive_three_level_scan": adaptive,
        "optimal_fixed_three_prime_prefix": optimal_fixed_order,
        "simple_node_target": SIMPLE_NODE_TARGET,
        "verdict": (
            "no explicit one-prime-at-a-time CRT tree over the active "
            "p<=953 masks can stay below one million nodes"
        ),
    }


def payload_sha256(payload: dict[str, object]) -> str:
    encoded = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(encoded).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()
    payload = audit()
    wrapped = {"payload_sha256": payload_sha256(payload), "payload": payload}
    print(json.dumps(wrapped, indent=2 if args.pretty else None, sort_keys=True))


if __name__ == "__main__":
    main()
