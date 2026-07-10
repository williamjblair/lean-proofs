#!/usr/bin/env python3
"""Emit attestations.json: tamper-evident proof evidence for the hosted proofs.

For each proof in proofs.yaml this records the sha256 of the proof file, the
axiom footprint reported by `lake env lean Audit.lean`, and whether it is
kernel-clean; it also pins the lake-manifest hash and the audit-output hash.

This is a CI attestation (the proof compiled clean against the pinned Mathlib
with kernel-only axioms), NOT an independent reproduction. Run it after
`lake build` (it invokes `lake env lean Audit.lean`). CI verifies that the
committed attestations.json matches a fresh regeneration, so it never drifts.

No timestamp is recorded: the file changes only when the proofs or their axiom
footprints change, so a green tree commits no churn.
"""
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

import yaml

ALLOWED = ["Classical.choice", "Quot.sound", "propext"]
ALLOWED_SET = set(ALLOWED)
ROOT = Path(__file__).resolve().parent.parent


def sha256_file(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def sha256_text(text: str) -> str:
    return "sha256:" + hashlib.sha256(text.encode()).hexdigest()


def parse_axiom_report(report: str) -> dict[str, list[str]]:
    """Parse Lean's possibly wrapped ``#print axioms`` output.

    Lean wraps long theorem names and axiom lists across lines.  It also emits
    ``does not depend on any axioms`` for an empty footprint.  Both forms must
    be represented: omission would turn a successful audit into a missing
    attestation.
    """
    lines = report.splitlines()
    axioms_by_theorem: dict[str, list[str]] = {}
    index = 0
    theorem_token = r"(?:'([^']+)'|([\w.']+))"
    depends = re.compile(rf"^{theorem_token}\s+depends on axioms:\s*\[(.*)$")
    none = re.compile(rf"^{theorem_token}\s+does not depend on any axioms\s*$")
    while index < len(lines):
        line = lines[index]
        empty_match = none.search(line)
        if empty_match:
            theorem = empty_match.group(1) or empty_match.group(2)
            axioms_by_theorem[theorem] = []
            index += 1
            continue

        match = depends.search(line)
        if not match:
            index += 1
            continue

        theorem = match.group(1) or match.group(2)
        payload = match.group(3)
        while "]" not in payload:
            index += 1
            if index >= len(lines):
                raise ValueError(f"unterminated axiom report for {theorem}")
            payload += " " + lines[index].strip()
        payload = payload.split("]", 1)[0]
        axioms_by_theorem[theorem] = [
            axiom.strip() for axiom in payload.split(",") if axiom.strip()
        ]
        index += 1
    return axioms_by_theorem


def axiom_footprint_is_clean(footprint: list[str]) -> bool:
    """The kernel gate permits any subset of the three standard axioms."""
    return set(footprint).issubset(ALLOWED_SET)


def main() -> int:
    doc = yaml.safe_load((ROOT / "proofs.yaml").read_text()) or {}
    report = subprocess.run(
        ["lake", "env", "lean", "Audit.lean"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
    ).stdout

    proofs = doc.get("proofs", [])
    axioms_by_theorem = parse_axiom_report(report)
    missing = [
        proof["theorem"]
        for proof in proofs
        if proof["theorem"] not in axioms_by_theorem
    ]
    if missing:
        print("missing axiom report for manifest theorem(s):", file=sys.stderr)
        for theorem in missing:
            print(f"  {theorem}", file=sys.stderr)
        return 1

    manifest_report = ""
    for proof in proofs:
        theorem = proof["theorem"]
        footprint = axioms_by_theorem.get(theorem)
        if footprint is not None:
            manifest_report += f"'{theorem}' depends on axioms: [{', '.join(footprint)}]\n"

    out = {
        "schema": "lean-proofs.attestations.v0.1",
        "repo": doc.get("repo"),
        "toolchain": doc.get("toolchain"),
        "mathlib": doc.get("mathlib"),
        "verifier_method": "lean_kernel",
        "verifier_actor": "ci:github-actions:willblair0708/lean-proofs",
        "lake_manifest_hash": sha256_file(ROOT / "lake-manifest.json"),
        "verifier_output_hash": sha256_text(manifest_report),
        "attestations": [],
    }
    for proof in proofs:
        theorem = proof["theorem"]
        footprint = axioms_by_theorem.get(theorem)
        out["attestations"].append(
            {
                "problem": proof["problem"],
                "theorem": theorem,
                "file": proof["file"],
                "proof_hash": sha256_file(ROOT / proof["file"]),
                "axiom_footprint": footprint,
                "axioms_clean": footprint is not None and axiom_footprint_is_clean(footprint),
            }
        )

    (ROOT / "attestations.json").write_text(json.dumps(out, indent=2) + "\n")
    print(f"wrote attestations.json: {len(out['attestations'])} attestation(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
