#!/usr/bin/env python3
"""Rank candidate MW-sieve primes using invariant and basis data only."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from pathlib import Path

import sympy

try:
    from .combined_sieve import packet_kernel_update
    from .verify_packets import generated_subgroup, normalize
except ImportError:
    from combined_sieve import packet_kernel_update
    from verify_packets import generated_subgroup, normalize


HERE = Path(__file__).resolve().parent
PACKETS = HERE / "packets.json"
COMBINED = HERE / "combined_sieve.json"
MAGMA_SOURCE = HERE / "magma_invariant_scout.m"


def magma_online() -> str:
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
    if "Runtime error" in output:
        raise RuntimeError(output)
    return output


def parse_integer_list(text: str) -> list[int]:
    return [int(value) for value in re.findall(r"-?\d+", text)]


def parse_magma_output(output: str) -> dict[int, dict[str, object]]:
    records: dict[int, dict[str, object]] = {}
    current_prime: int | None = None
    basis_lines: list[str] = []
    collecting_basis = False

    def finish_basis() -> None:
        nonlocal basis_lines, collecting_basis
        if current_prime is None or not basis_lines:
            return
        rows = re.findall(r"\[([^\[\]]*)\]", " ".join(basis_lines))
        records[current_prime]["basis"] = [
            parse_integer_list(row) for row in rows
        ]
        basis_lines = []
        collecting_basis = False

    for raw_line in output.splitlines():
        line = raw_line.strip()
        if line.startswith("SCOUT_BAD_PRIME"):
            finish_basis()
            prime = parse_integer_list(line)[0]
            records[prime] = {"bad_prime": True}
        elif line.startswith("SCOUT_PRIME"):
            finish_basis()
            current_prime = parse_integer_list(line)[0]
            records[current_prime] = {"bad_prime": False}
        elif line.startswith("SCOUT_INVARIANTS"):
            assert current_prime is not None
            records[current_prime]["invariants"] = parse_integer_list(line)
        elif line.startswith("SCOUT_BASIS"):
            assert current_prime is not None
            collecting_basis = True
            basis_lines = [line.removeprefix("SCOUT_BASIS").strip()]
            if line.endswith("]") and line.count("[") == line.count("]"):
                finish_basis()
        elif collecting_basis:
            basis_lines.append(line)
            if (
                " ".join(basis_lines).count("[")
                == " ".join(basis_lines).count("]")
            ):
                finish_basis()
    finish_basis()

    for prime, record in records.items():
        if record["bad_prime"]:
            continue
        assert record.get("invariants"), prime
        assert len(record.get("basis", [])) == 5, (prime, record)
        width = len(record["invariants"])
        assert all(len(row) == width for row in record["basis"])
    return records


def factorization(value: int) -> dict[str, int]:
    return {
        str(int(prime)): int(exponent)
        for prime, exponent in sympy.factorint(value).items()
    }


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rank_records(
    records: dict[int, dict[str, object]]
) -> dict[str, object]:
    packet_data = json.loads(PACKETS.read_text())
    combined = json.loads(COMBINED.read_text())
    lattice = sympy.Matrix(combined["combined_lattice_column_hnf"])
    current_index = int(combined["combined_lattice_index"])
    current_factors = {
        int(prime): int(exponent)
        for prime, exponent
        in combined["combined_index_factorization"].items()
    }
    ranked = []
    for prime, record in sorted(records.items()):
        if record["bad_prime"]:
            ranked.append({"prime": prime, "bad_prime": True})
            continue
        invariants = tuple(record["invariants"])
        basis = [
            normalize(row, invariants) for row in record["basis"]
        ]
        subgroup_order = len(generated_subgroup(basis, invariants))
        updated = packet_kernel_update(
            lattice,
            {"invariants": list(invariants), "basis": [list(r) for r in basis]},
        )
        updated_index = abs(int(updated.det()))
        assert updated_index % current_index == 0
        relative_gain = updated_index // current_index
        assert subgroup_order % relative_gain == 0
        gain_factors = {
            int(q): int(e)
            for q, e in sympy.factorint(relative_gain).items()
        }
        new_prime_factors = {
            str(q): e for q, e in gain_factors.items()
            if q not in current_factors
        }
        novel_factor_product = math.prod(
            q**e for q, e in gain_factors.items()
            if q not in current_factors
        )
        ranked.append({
            "prime": prime,
            "bad_prime": False,
            "invariants": list(invariants),
            "basis": [list(row) for row in basis],
            "ambient_order": math.prod(invariants),
            "reduction_image_order": subgroup_order,
            "relative_kernel_index_gain": relative_gain,
            "relative_gain_factorization": factorization(relative_gain),
            "overlap_factor": subgroup_order // relative_gain,
            "new_prime_factors": new_prime_factors,
            "novel_factor_product": novel_factor_product,
        })
    good = [record for record in ranked if not record["bad_prime"]]
    recommendations = sorted(
        good,
        key=lambda record: (
            record["novel_factor_product"],
            record["relative_kernel_index_gain"],
        ),
        reverse=True,
    )
    return {
        "verdict": "PASS",
        "candidate_count": len(records),
        "magma_source": str(MAGMA_SOURCE.relative_to(Path.cwd())),
        "magma_source_sha256": sha256(MAGMA_SOURCE),
        "current_packet_primes": sorted(
            int(prime) for prime in packet_data["packets"]
        ),
        "current_combined_index": current_index,
        "current_combined_index_factorization": {
            str(q): e for q, e in sorted(current_factors.items())
        },
        "ranked_by_prime": ranked,
        "recommendations": recommendations,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--magma-output", type=Path)
    parser.add_argument("--online", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.online:
        output = magma_online()
    elif args.magma_output is not None:
        output = args.magma_output.read_text()
    else:
        parser.error("use --online or --magma-output")
    result = rank_records(parse_magma_output(output))
    if args.output is not None:
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
