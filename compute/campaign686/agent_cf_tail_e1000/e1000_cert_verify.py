#!/usr/bin/env python3
"""Exact, Lean-output-independent audit of the six e1000 Farey certificates.

The workspace ``erdos686_k*_farey_cert_e1000.lean`` files are generated data:
large ``FareyTree`` literals consumed by the kernel-checked checker.  This
script imports the generator as a library, rebuilds each tree in memory, runs
the generator's separate semantic verifier, cross-checks the continued-
fraction artifact, renders the Lean source, and requires byte-for-byte
identity with the current workspace artifact.

Only Python integers are used.  The audit never invokes Lean and never writes
an artifact.  It also makes the ``d < 10^1000`` handoff and the missing
``d = 10^1000`` boundary rows explicit, and preserves the two known ``d = 1``
telescopes as negative test fixtures.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import sys
from collections import Counter
from contextlib import contextmanager
from pathlib import Path
from typing import Any, Iterator


REPO_ROOT = Path(__file__).resolve().parents[3]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from compute import erdos686_thue_gen_lean as generator  # noqa: E402


EXPONENT = 1000
POWER = 10**EXPONENT
TARGET_K = (5, 7, 9, 11, 13, 15)

GENERATOR_PATH = REPO_ROOT / "compute" / "erdos686_thue_gen_lean.py"
EXPECTED_GENERATOR_SHA256 = (
    "112ba748aa90e8688f7320ce3418e3b5a6430551bceaf3178e319da48209ddba"
)
EXPECTED_ARTIFACT_SET_SHA256 = (
    "05615d9932db7c21a0954af9baf18ace8b6136d84f89f85c29a91867e2eac670"
)

EXPECTED_ARTIFACTS = {
    5: {
        "bytes": 474_690,
        "sha256": "e3c69ece7adc08f321897faf01b869f5503a5eb5c126181e34f5e8d019c45a0b",
    },
    7: {
        "bytes": 311_799,
        "sha256": "f6f62ae65dd587bf1d310639666ca71224fdfd3f77a94b531c1106ebed283100",
    },
    9: {
        "bytes": 796_285,
        "sha256": "e9b99425f9d190053da1f5a8a107c3bb5579c9577855bdf6d3508994f2c96eb1",
    },
    11: {
        "bytes": 416_396,
        "sha256": "7f948ee46662034e86f449a1045acea5f418df45899571ce97b38cab30ad9f74",
    },
    13: {
        "bytes": 334_419,
        "sha256": "036e65784bd4696ff44136a1082ac260e01687911a109bad986c1ec1fe1bbf58",
    },
    15: {
        "bytes": 448_143,
        "sha256": "f94ea813afb100ad5299fa9abbc491b808c64c4b11364241cb5378aa77e6d836",
    },
}

# Filled from a clean exact regeneration and then frozen as regression data.
# ``tree_shape`` below independently recomputes every field except ``spine``,
# which is a legacy generator counter that is identically zero.
EXPECTED_STATS: dict[int, dict[str, int]] = {
    5: {
        "nodes": 57_537,
        "kills": 28_764,
        "highs": 5,
        "splits": 28_768,
        "cands": 2_606,
        "skipped": 6,
        "max_depth": 27_203,
        "gmax_max": 77,
        "gmax_sum": 2_612,
        "spine": 0,
        "maxbits": 16_621,
        "mediants": 28_768,
        "json_matched": 339,
        "json_total": 341,
        "chunk_defs": 229,
    },
    7: {
        "nodes": 37_857,
        "kills": 18_927,
        "highs": 2,
        "splits": 18_928,
        "cands": 3_601,
        "skipped": 9,
        "max_depth": 16_796,
        "gmax_max": 36,
        "gmax_sum": 3_610,
        "spine": 0,
        "maxbits": 23_263,
        "mediants": 18_928,
        "json_matched": 339,
        "json_total": 341,
        "chunk_defs": 141,
    },
    9: {
        "nodes": 96_555,
        "kills": 48_274,
        "highs": 4,
        "splits": 48_277,
        "cands": 4_893,
        "skipped": 15,
        "max_depth": 45_246,
        "gmax_max": 166,
        "gmax_sum": 4_908,
        "spine": 0,
        "maxbits": 29_918,
        "mediants": 48_277,
        "json_matched": 340,
        "json_total": 341,
        "chunk_defs": 381,
    },
    11: {
        "nodes": 50_557,
        "kills": 25_273,
        "highs": 6,
        "splits": 25_278,
        "cands": 5_846,
        "skipped": 14,
        "max_depth": 21_688,
        "gmax_max": 57,
        "gmax_sum": 5_860,
        "spine": 0,
        "maxbits": 36_573,
        "mediants": 25_278,
        "json_matched": 339,
        "json_total": 341,
        "chunk_defs": 183,
    },
    13: {
        "nodes": 40_677,
        "kills": 20_336,
        "highs": 3,
        "splits": 20_338,
        "cands": 6_949,
        "skipped": 18,
        "max_depth": 16_232,
        "gmax_max": 35,
        "gmax_sum": 6_967,
        "spine": 0,
        "maxbits": 43_223,
        "mediants": 20_338,
        "json_matched": 340,
        "json_total": 341,
        "chunk_defs": 137,
    },
    15: {
        "nodes": 54_483,
        "kills": 27_240,
        "highs": 2,
        "splits": 27_241,
        "cands": 8_112,
        "skipped": 19,
        "max_depth": 22_319,
        "gmax_max": 55,
        "gmax_sum": 8_131,
        "spine": 0,
        "maxbits": 49_871,
        "mediants": 27_241,
        "json_matched": 339,
        "json_total": 341,
        "chunk_defs": 188,
    },
}


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


@contextmanager
def repository_cwd() -> Iterator[None]:
    """Make the generator's relative JSON lookup independent of caller cwd."""

    previous = Path.cwd()
    os.chdir(REPO_ROOT)
    try:
        yield
    finally:
        os.chdir(previous)


def configure_generator(k: int) -> dict[str, Any]:
    cfg = generator.CONFIGS[k]
    generator.K = k
    generator.E = k - 2
    generator.N = 4
    generator.CNUM = cfg["CNUM"]
    generator.CDEN = cfg["CDEN"]
    generator.YLO = cfg["YLO"]
    generator.ROOT = cfg["ROOT"]
    generator.CERT_NAME = f"k{k}FareyCert"
    generator.eq_holds = cfg["eq"]
    return cfg


def centered_polynomial(k: int, value: int) -> int:
    result = value
    for j in range(1, (k - 1) // 2 + 1):
        result *= value * value - j * j
    return result


def block_product(k: int, n: int) -> int:
    return math.prod(range(n + 1, n + k + 1))


def boundary_semantics(k: int, qhi: int) -> dict[str, Any]:
    """Audit the exact integer conversion from ``d < 10^1000`` to Ymax.

    The banked upper confinement is ``n + 1 < qhi*d`` and the centered
    coordinate is ``Y = n + h``.  Strictness and integrality are both used;
    replacing the target by ``d <= 10^1000`` loses exactly the rows listed in
    ``equality_uncovered_r``.
    """

    h = (k + 1) // 2
    ymax = qhi * POWER

    # d < POWER gives d <= POWER-1.  Since n+1 and qhi*d are integers,
    # n+1 < qhi*d gives n+1 <= qhi*d-1.
    strict_max_n_plus_one = qhi * (POWER - 1) - 1
    strict_max_y = strict_max_n_plus_one + h - 1
    strict_slack = qhi - h + 2
    assert strict_max_y == ymax - strict_slack
    assert strict_slack > 0

    # At d=POWER write n+1=qhi*POWER-r.  Upper confinement permits every
    # r>=1, while the certificate's Y<=Ymax condition requires r>=h-1.
    equality_uncovered_r = list(range(1, h - 1))
    equality_excess_y = [h - 1 - r for r in equality_uncovered_r]
    for r, excess in zip(equality_uncovered_r, equality_excess_y, strict=True):
        n_plus_one = qhi * POWER - r
        y = n_plus_one + h - 1
        assert y == ymax + excess
        assert 1 <= excess <= h - 2

    equality_first_covered_r = h - 1
    assert qhi * POWER - equality_first_covered_r + h - 1 == ymax
    return {
        "k": k,
        "h": h,
        "qhi": qhi,
        "target": "d < 10^1000",
        "certificate_ymax": "qhi * 10^1000",
        "strict_y_slack_below_ymax": strict_slack,
        "equality_first_covered_r": equality_first_covered_r,
        "equality_uncovered_r": equality_uncovered_r,
        "equality_uncovered_y_excess": equality_excess_y,
        "equality_uncovered_count": len(equality_uncovered_r),
    }


def telescope_checks() -> list[dict[str, Any]]:
    expected = {9: (7, 8), 15: (12, 13)}  # k -> (Y, X)
    assert {
        k: generator.CONFIGS[k]["TELESCOPE"]
        for k in TARGET_K
        if generator.CONFIGS[k]["TELESCOPE"] is not None
    } == expected

    rows: list[dict[str, Any]] = []
    for k, (y, x) in expected.items():
        cfg = generator.CONFIGS[k]
        h = (k + 1) // 2
        n = y - h
        d = x - y
        centered_residual = centered_polynomial(k, x) - 4 * centered_polynomial(k, y)
        block_residual = block_product(k, n + d) - 4 * block_product(k, n)
        assert math.gcd(x, y) == 1
        assert d == 1
        assert cfg["eq"](x, y)
        assert centered_residual == 0
        assert block_residual == 0
        assert y < cfg["YLO"]
        assert d < 221
        rows.append(
            {
                "k": k,
                "X": x,
                "Y": y,
                "n": n,
                "d": d,
                "gcd_XY": math.gcd(x, y),
                "centered_residual": centered_residual,
                "block_residual": block_residual,
                "Ylo": cfg["YLO"],
                "below_Ylo_by": cfg["YLO"] - y,
                "outside_tail_d_ge_221": d < 221,
            }
        )
    return rows


def empty_shape() -> dict[str, Any]:
    return {
        "nodes": 0,
        "kills": 0,
        "highs": 0,
        "splits": 0,
        "cands": 0,
        "skipped": 0,
        "max_depth": 0,
        "gmax_max": 0,
        "gmax_sum": 0,
        "maxbits": 0,
        "mediants": set(),
    }


def tree_shape(
    tree: tuple[Any, ...],
    a: int,
    b: int,
    c: int,
    d: int,
    *,
    k: int,
    ylo: int,
    ymax: int,
) -> dict[str, Any]:
    """Independently traverse a finished tree and reproduce its statistics.

    This is deliberately iterative: the e1000 k=9 tree has depth 45,246, and
    accumulating a fresh mediant set at every recursive return would obscure
    the linear-time nature of the check.
    """

    shape = empty_shape()
    stack = [(tree, a, b, c, d, 1)]
    while stack:
        current, left_num, left_den, right_num, right_den, depth = stack.pop()
        shape["nodes"] += 1
        shape["max_depth"] = max(shape["max_depth"], depth)
        tag = current[0]
        if tag == "high":
            shape["highs"] += 1
            continue

        shape["maxbits"] = max(
            shape["maxbits"],
            (right_num**k).bit_length(),
            (left_num**k).bit_length(),
        )
        if tag == "kill":
            shape["kills"] += 1
            continue

        if tag != "node" or len(current) != 4:
            raise AssertionError(f"unexpected tree node {tag!r}")
        _, gmax, left, right = current
        mediant_num, mediant_den = left_num + right_num, left_den + right_den
        shape["splits"] += 1
        shape["gmax_max"] = max(shape["gmax_max"], gmax)
        shape["gmax_sum"] += gmax
        shape["mediants"].add((mediant_num, mediant_den))

        first = max(1, (ylo + mediant_den - 1) // mediant_den)
        last = min(gmax, ymax // mediant_den)
        in_range = max(0, last - first + 1)
        shape["cands"] += in_range
        shape["skipped"] += gmax - in_range

        stack.append(
            (right, mediant_num, mediant_den, right_num, right_den, depth + 1)
        )
        stack.append(
            (left, left_num, left_den, mediant_num, mediant_den, depth + 1)
        )
    return shape


def audit_certificate(k: int) -> dict[str, Any]:
    cfg = configure_generator(k)
    generator.check_lean_constants()
    h = (k + 1) // 2
    if cfg["YLO"] != cfg["QLO"] * 221 + h - 1:
        raise AssertionError(f"k={k}: lower-bound handoff changed")
    ymax = cfg["QHI"] * POWER
    stats = generator.Stats()
    build_mediants: set[tuple[int, int]] = set()
    tree = generator.build(*generator.ROOT, ymax, stats, 1, build_mediants)
    if not generator.verify(tree, *generator.ROOT, ymax):
        raise AssertionError(f"k={k}: independent fareyCheck replay failed")

    shape = tree_shape(
        tree,
        *generator.ROOT,
        k=k,
        ylo=cfg["YLO"],
        ymax=ymax,
    )
    if shape["mediants"] != build_mediants:
        raise AssertionError(f"k={k}: independent mediant set changed")

    generated_stats = {
        field: getattr(stats, field) for field in generator.Stats.__slots__
    }
    shape_stats = {key: value for key, value in shape.items() if key != "mediants"}
    comparable_generated = {
        key: value for key, value in generated_stats.items() if key != "spine"
    }
    if shape_stats != comparable_generated:
        raise AssertionError(
            f"k={k}: independent tree statistics differ: "
            f"{shape_stats!r} != {comparable_generated!r}"
        )
    if generated_stats["spine"] != 0:
        raise AssertionError(f"k={k}: legacy spine counter is no longer zero")

    if generated_stats["nodes"] != 2 * generated_stats["splits"] + 1:
        raise AssertionError(f"k={k}: tree is not full binary")
    if generated_stats["kills"] + generated_stats["highs"] != (
        generated_stats["splits"] + 1
    ):
        raise AssertionError(f"k={k}: leaf count identity failed")
    if generated_stats["nodes"] != (
        generated_stats["splits"]
        + generated_stats["kills"]
        + generated_stats["highs"]
    ):
        raise AssertionError(f"k={k}: node partition failed")

    with repository_cwd():
        matched, total = generator.crosscheck_json(build_mediants, ymax)

    rendered = generator.render(tree, EXPONENT).encode("utf-8")
    artifact_path = (
        REPO_ROOT
        / "compute"
        / "artifacts"
        / f"erdos686_k{k}_farey_cert_e{EXPONENT}.lean"
    )
    artifact = artifact_path.read_bytes()
    expected = EXPECTED_ARTIFACTS[k]
    if len(artifact) != expected["bytes"]:
        raise AssertionError(f"k={k}: artifact byte length changed")
    artifact_sha256 = sha256_bytes(artifact)
    if artifact_sha256 != expected["sha256"]:
        raise AssertionError(f"k={k}: artifact SHA-256 changed")
    if rendered != artifact:
        raise AssertionError(f"k={k}: deterministic regeneration differs bytewise")

    text = artifact.decode("utf-8")
    chunk_prefix = f"private def k{k}FareyCertC"
    declared_chunks = [
        line.split()[2]
        for line in text.splitlines()
        if line.startswith(chunk_prefix)
    ]
    chunk_defs = len(declared_chunks)
    expected_chunk_names = [f"k{k}FareyCertC{i}" for i in range(chunk_defs)]
    if declared_chunks != expected_chunk_names:
        raise AssertionError(f"k={k}: private chunk names are not contiguous")
    chunk_tokens = [
        token
        for token in text.replace("(", " ").replace(")", " ").split()
        if token.startswith(f"k{k}FareyCertC")
    ]
    chunk_counts = Counter(chunk_tokens)
    if chunk_counts != Counter({name: 2 for name in expected_chunk_names}):
        raise AssertionError(f"k={k}: a private chunk is missing, shared, or duplicated")
    final_defs = sum(
        line == f"def k{k}FareyCert : FareyTree :=" for line in text.splitlines()
    )
    if final_defs != 1:
        raise AssertionError(f"k={k}: expected exactly one public certificate def")

    regression_stats = {
        **generated_stats,
        "mediants": len(build_mediants),
        "json_matched": matched,
        "json_total": total,
        "chunk_defs": chunk_defs,
    }
    if EXPECTED_STATS and regression_stats != EXPECTED_STATS[k]:
        raise AssertionError(
            f"k={k}: frozen tree statistics changed: "
            f"{regression_stats!r} != {EXPECTED_STATS[k]!r}"
        )

    return {
        "k": k,
        "artifact": str(artifact_path.relative_to(REPO_ROOT)),
        "bytes": len(artifact),
        "sha256": artifact_sha256,
        "render_matches_artifact": True,
        "semantic_verify": True,
        "root": list(cfg["ROOT"]),
        "CNUM": cfg["CNUM"],
        "CDEN": cfg["CDEN"],
        "Ylo": cfg["YLO"],
        "Qlo": cfg["QLO"],
        "Qhi": cfg["QHI"],
        "tree": regression_stats,
        "chunk_reference_multiplicity": 2,
        "full_binary_identities": True,
        "boundary": boundary_semantics(k, cfg["QHI"]),
    }


def full_report() -> dict[str, Any]:
    generator_sha256 = sha256_path(GENERATOR_PATH)
    if generator_sha256 != EXPECTED_GENERATOR_SHA256:
        raise AssertionError("generator SHA-256 changed")

    rows = [audit_certificate(k) for k in TARGET_K]
    aggregate_payload = "".join(
        f"{row['k']}:{row['sha256']}\n" for row in rows
    ).encode("ascii")
    artifact_set_sha256 = sha256_bytes(aggregate_payload)
    if artifact_set_sha256 != EXPECTED_ARTIFACT_SET_SHA256:
        raise AssertionError("aggregate artifact-set SHA-256 changed")
    return {
        "audit": "Erdos 686 odd-k e1000 Farey certificate regeneration",
        "arithmetic": "exact Python integers; no Lean output consumed",
        "generator": {
            "path": str(GENERATOR_PATH.relative_to(REPO_ROOT)),
            "sha256": generator_sha256,
        },
        "exponent": EXPONENT,
        "per_k": rows,
        "artifact_set_sha256": artifact_set_sha256,
        "telescopes": telescope_checks(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="print the full JSON report")
    args = parser.parse_args()
    report = full_report()
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
        return

    print("[PASS] exact e1000 Farey certificate audit")
    print(f"generator sha256={report['generator']['sha256']}")
    for row in report["per_k"]:
        tree = row["tree"]
        boundary = row["boundary"]
        print(
            f"k={row['k']:2d} sha256={row['sha256']} bytes={row['bytes']} "
            f"nodes={tree['nodes']} depth={tree['max_depth']} "
            f"chunks={tree['chunk_defs']} strict_slack={boundary['strict_y_slack_below_ymax']} "
            f"equality_residual={boundary['equality_uncovered_r']}"
        )
    print(f"artifact-set sha256={report['artifact_set_sha256']}")
    print("telescopes: k=9 (X,Y)=(8,7), k=15 (13,12), exact residual 0, d=1")


if __name__ == "__main__":
    main()
