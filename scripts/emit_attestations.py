#!/usr/bin/env python3
"""Emit attestations.json: tamper-evident proof evidence for the hosted proofs.

For each proof in proofs.yaml this records the sha256 of the proof file, the
axiom footprint reported by `lake env lean Audit.lean`, and whether it is
kernel-clean; it also pins the lake-manifest hash and the audit-output hash.

This is a CI attestation (the proof compiled clean against the pinned Mathlib
with kernel-only axioms), NOT an independent reproduction. Run it after
`lake build` (it invokes `lake env lean Audit.lean`). check_manifest.sh verifies
the committed attestations.json matches a fresh regeneration, so it never drifts.

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
ROOT = Path(__file__).resolve().parent.parent


def sha256_file(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def sha256_text(text: str) -> str:
    return "sha256:" + hashlib.sha256(text.encode()).hexdigest()


def main() -> int:
    doc = yaml.safe_load((ROOT / "proofs.yaml").read_text()) or {}
    report = subprocess.run(
        ["lake", "env", "lean", "Audit.lean"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
    ).stdout

    # Parse "'<theorem>' depends on axioms: [a, b, c]" lines into theorem -> footprint.
    axioms_by_theorem: dict[str, list[str]] = {}
    for line in report.splitlines():
        m = re.search(r"'?([\w.]+)'?\s+depends on axioms:\s*\[(.*)\]", line)
        if m:
            axioms_by_theorem[m.group(1)] = [a.strip() for a in m.group(2).split(",") if a.strip()]

    proofs = doc.get("proofs", [])
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
                "axioms_clean": footprint is not None and sorted(footprint) == ALLOWED,
            }
        )

    (ROOT / "attestations.json").write_text(json.dumps(out, indent=2) + "\n")
    print(f"wrote attestations.json: {len(out['attestations'])} attestation(s)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
