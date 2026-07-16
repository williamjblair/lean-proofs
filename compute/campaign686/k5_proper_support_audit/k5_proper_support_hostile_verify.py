#!/usr/bin/env python3
"""Independent structural and kernel audit for the k=5 puncture theorem.

This verifier imports no campaign generator.  It checks the emitted Lean
surface directly, verifies the complete puncture/module census, rejects
compiler-trusted proof shortcuts, confirms that every expected artifact has
an olean, and asks Lean for the public theorem's actual axiom footprint.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
ERDOS = ROOT / "ErdosProblems"
BUILD = ROOT / ".lake" / "build" / "lib" / "lean"
AUDIT_DIR = Path(__file__).resolve().parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = ("native_decide", "sorry", "admit")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def generated_sources() -> list[Path]:
    return sorted(ERDOS.glob("Erdos686K5P??*.lean"))


def exact_regex_count(pattern: str, paths: list[Path]) -> int:
    regex = re.compile(pattern)
    return sum(bool(regex.fullmatch(path.name)) for path in paths)


def parse_axioms(report: str) -> list[str]:
    marker = "depends on axioms:"
    if "does not depend on any axioms" in report:
        return []
    start = report.find(marker)
    if start < 0:
        raise AssertionError("missing axiom report")
    payload = report[start + len(marker) :]
    left = payload.find("[")
    right = payload.find("]", left)
    if left < 0 or right < 0:
        raise AssertionError("malformed axiom report")
    return [
        item.strip()
        for item in payload[left + 1 : right].replace("\n", " ").split(",")
        if item.strip()
    ]


def verify() -> dict[str, object]:
    sources = generated_sources()
    aggregate = ERDOS / "Erdos686K5AllPunctures.lean"
    assert aggregate.is_file()

    counts = {
        "puncture_endpoints": exact_regex_count(
            r"Erdos686K5P\d\dEndpoint\.lean", sources
        ),
        "certificate_data": exact_regex_count(
            r"Erdos686K5P\d\dCertificateData\.lean", sources
        ),
        "certificate_assemblies": exact_regex_count(
            r"Erdos686K5P\d\dCertificate\.lean", sources
        ),
        "local_row_modules": exact_regex_count(
            r"Erdos686K5P\d\dS\dJ\dI\dRows\.lean", sources
        ),
        "elimination_leaves": exact_regex_count(
            r"Erdos686K5P\d\dElimination\dRow\d\.lean", sources
        ),
        "elimination_assemblies": exact_regex_count(
            r"Erdos686K5P\d\dElimination\dRows\.lean", sources
        ),
        "bezout_kernels": exact_regex_count(
            r"Erdos686K5P\d\dBezoutKernel\.lean", sources
        ),
        "noncommon_data": exact_regex_count(
            r"Erdos686K5P\d\dNoncommonData\.lean", sources
        ),
        "noncommon_assemblies": exact_regex_count(
            r"Erdos686K5P\d\dNoncommon\.lean", sources
        ),
    }
    expected = {
        "puncture_endpoints": 25,
        "certificate_data": 25,
        "certificate_assemblies": 25,
        "local_row_modules": 1272,
        "elimination_leaves": 477,
        "elimination_assemblies": 53,
        "bezout_kernels": 25,
        "noncommon_data": 25,
        "noncommon_assemblies": 25,
    }
    assert counts == expected, (counts, expected)

    central_local = exact_regex_count(
        r"Erdos686K5P33S\dJ\dI\dRows\.lean", sources
    )
    noncentral_local = counts["local_row_modules"] - central_local
    assert central_local == 120
    assert noncentral_local == 1152

    forbidden_hits: list[str] = []
    for path in [*sources, aggregate]:
        text = path.read_text()
        for token in FORBIDDEN:
            if re.search(rf"\b{re.escape(token)}\b", text):
                forbidden_hits.append(f"{path.relative_to(ROOT)}:{token}")
    assert forbidden_hits == [], forbidden_hits

    aggregate_text = aggregate.read_text()
    imports = re.findall(
        r"^import ErdosProblems\.Erdos686K5P(\d\d)Endpoint$",
        aggregate_text,
        flags=re.MULTILINE,
    )
    expected_punctures = [f"{j}{i}" for j in range(1, 6) for i in range(1, 6)]
    assert imports == expected_punctures
    witness_calls = re.findall(
        r"exists_k5P(\d\d)PunctureJetWitness", aggregate_text
    )
    assert witness_calls == expected_punctures
    assert "theorem no_k5_tail_solution_of_proper_support" in aggregate_text

    missing_oleans: list[str] = []
    for source in [*sources, aggregate]:
        relative = source.relative_to(ROOT).with_suffix(".olean")
        if not (BUILD / relative).is_file():
            missing_oleans.append(str(relative))
    assert missing_oleans == [], missing_oleans

    axiom_run = subprocess.run(
        [
            "lake",
            "env",
            "lean",
            str(AUDIT_DIR / "AxiomCheck.lean"),
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    axiom_report = axiom_run.stdout + axiom_run.stderr
    axioms = parse_axioms(axiom_report)
    assert set(axioms).issubset(ALLOWED_AXIOMS), axioms

    manifest = {
        str(path.relative_to(ROOT)): sha256(path)
        for path in [*sources, aggregate]
    }
    manifest_digest = hashlib.sha256(
        json.dumps(manifest, sort_keys=True).encode()
    ).hexdigest()

    return {
        "verdict": "PASS",
        "counts": counts,
        "central_local_modules": central_local,
        "noncentral_local_modules": noncentral_local,
        "forbidden_hits": forbidden_hits,
        "missing_oleans": missing_oleans,
        "axioms": axioms,
        "source_count": len(manifest),
        "source_manifest_sha256": manifest_digest,
    }


def main() -> None:
    print(json.dumps(verify(), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
