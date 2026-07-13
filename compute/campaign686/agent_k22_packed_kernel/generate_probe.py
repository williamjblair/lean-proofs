#!/usr/bin/env python3
"""Generate one ordinary-kernel packed k=22 cover shard.

This is deliberately a probe generator.  It uses the exact local masks from
the audited k=22 verifier and emits a single one-million-index branch shard,
plus the theorem connecting the zero bitvector certificate to the generic
packed-cover semantics.
"""

from __future__ import annotations

import importlib.util
import argparse
import sys
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
VERIFIER = ROOT / "compute/campaign686/agent_k22_sieve_probe/k22_sieve_probe_verify.py"
OUT = HERE / "ActualShardProbe.lean"


def load_verifier():
    spec = importlib.util.spec_from_file_location("k22_sieve_probe_verify", VERIFIER)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def active_items(verifier, branch: int) -> list[tuple[int, int]]:
    items: list[tuple[int, int]] = []
    for prime in verifier.primes_through(953):
        if prime in (2, 3, 11, 23):
            continue
        allowed = verifier.local_allowed_t_residues(prime)
        if len(allowed) == prime:
            continue
        inverse = pow(46, -1, prime)
        residues = {
            ((allowed_residue - branch) * inverse) % prime
            for allowed_residue in allowed
        }
        pattern = sum(1 << residue for residue in residues)
        items.append((prime, pattern))
    return items


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--width", type=int, default=1_000_000)
    parser.add_argument("--exponent", type=int, default=14)
    args = parser.parse_args()
    width = args.width
    exponent = args.exponent
    assert 83 * 2**exponent >= width
    verifier = load_verifier()
    items = active_items(verifier, 17)
    assert len(items) == 132
    rows = ",\n".join(f"  ({prime}, {pattern})" for prime, pattern in items)
    OUT.write_text(
        "import «compute».campaign686.agent_k22_packed_kernel.PackedPeriodicCover\n\n"
        "namespace Erdos686.K22PackedKernel\n\n"
        "def actualShardItems : List (ℕ × ℕ) := [\n"
        f"{rows}\n]\n\n"
        f"def actualShardIntersection : BitVec {width} :=\n"
        f"  intersectPeriodicItems {width} {exponent} (BitVec.allOnes {width}) "
        "actualShardItems\n\n"
        "set_option maxHeartbeats 1000000000 in\n"
        "set_option maxRecDepth 1000000 in\n"
        "theorem actualShardIntersection_zero :\n"
        f"    actualShardIntersection = BitVec.zero {width} := by\n"
        "  decide +kernel\n\n"
        "/-- The computational zero theorem excludes every index satisfying all\n"
        "132 exact residue-mask bits. -/\n"
        f"theorem actualShard_no_index (i : ℕ) (hi : i < {width})\n"
        "    (hitem : ∀ item ∈ actualShardItems,\n"
        f"      i < item.1 * 2 ^ {exponent} ∧\n"
        "        item.2.testBit (i % item.1) = true) : False := by\n"
        "  exact no_index_of_intersection_zero hi actualShardIntersection_zero hitem\n\n"
        "#print axioms actualShardIntersection_zero\n"
        "#print axioms actualShard_no_index\n\n"
        "end Erdos686.K22PackedKernel\n"
    )


if __name__ == "__main__":
    main()
