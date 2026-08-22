#!/usr/bin/env python3
"""Fail-closed verifier for the two Lean Correspondence v0 candidate packets."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path


STANDARD_AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
HEX40 = re.compile(r"^[0-9a-f]{40}$")
HEX64 = re.compile(r"^[0-9a-f]{64}$")


class PacketError(RuntimeError):
    pass


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_json(path: Path) -> dict:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise PacketError(f"cannot read {path}: {exc}") from exc


def require(condition: bool, message: str) -> None:
    if not condition:
        raise PacketError(message)


def check_digest(path: Path, expected: str) -> None:
    require(HEX64.fullmatch(expected) is not None, f"invalid sha256 for {path}")
    try:
        actual = sha256(path.read_bytes())
    except OSError as exc:
        raise PacketError(f"cannot read rooted file {path}: {exc}") from exc
    require(actual == expected, f"digest mismatch for {path}: {actual} != {expected}")


def validate_common(packet: dict, case_id: str) -> None:
    require(packet.get("schema") == "lean-correspondence.candidate-packet.v0", f"{case_id}: schema")
    require(packet.get("case_id") == case_id, f"{case_id}: id")
    require(packet.get("authority_effect") == "none", f"{case_id}: authority effect")
    require(packet.get("relation", {}).get("status") == "verified_at_pins", f"{case_id}: status")
    require(packet.get("known_uncertainty"), f"{case_id}: uncertainty must be nonempty")
    require(packet.get("does_not_establish"), f"{case_id}: claim exclusions must be nonempty")
    require(len(packet.get("mutation_tests", [])) == 5, f"{case_id}: five mutation classes required")


def validate_erdos(bundle: Path, packet: dict) -> None:
    validate_common(packet, "erdos-730-affirmative-rhs")
    require(packet["relation"]["type"] == "proposition_identity_plus_term_witness", "erdos: relation")
    witness = bundle / "cases/erdos-730" / packet["witness"]["file"]
    check_digest(witness, packet["witness"]["sha256"])
    fc = packet["roots"]["formal_conjectures"]
    lp = packet["roots"]["lean_proofs"]
    require(HEX40.fullmatch(fc["commit"]) is not None, "erdos: FC commit")
    require(HEX40.fullmatch(lp["commit"]) is not None, "erdos: lean-proofs commit")
    require(fc["mathlib_revision"] != lp["mathlib_revision"], "erdos: environments must remain explicit")
    require(lp["additional_dependency"]["name"] == "PrimeNumberTheoremAnd", "erdos: external assumption")
    require(len(packet["atomic_facts"]) == 4, "erdos: atomic inventory")


def parse_digest_inventory(path: Path) -> dict[str, str]:
    result: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line:
            continue
        digest, name = line.split("  ", 1)
        require(HEX64.fullmatch(digest) is not None, f"invalid generated digest: {line}")
        require(name not in result, f"duplicate generated path: {name}")
        result[name] = digest
    return result


def validate_fc_leaneval(bundle: Path, packet: dict) -> None:
    validate_common(packet, "fc-leaneval-oeis-303656")
    require(packet["relation"]["type"] == "deterministic_generated_challenge_lineage", "inheritance: relation")
    case = bundle / "cases/fc-leaneval-oeis-303656"
    frozen = case / "frozen"
    for relative, digest in packet["frozen_bytes"].items():
        check_digest(frozen / relative, digest)
    history = packet["historical_source_change"]
    check_digest(case / history["witness"]["file"], history["witness"]["sha256"])

    request = read_json(frozen / "request.json")
    provenance = read_json(frozen / "fc-provenance.json")
    source = packet["roots"]["formal_conjectures_source"]
    target = packet["roots"]["lean_eval_target"]
    problem = request.get("problems", [{}])[0]
    require(request.get("schemaVersion") == 1, "inheritance: request schema")
    require(request.get("leanToolchain") == target["lean_toolchain"], "inheritance: forged target toolchain")
    require(request.get("mathlib", {}).get("rev") == target["mathlib_revision"], "inheritance: forged target Mathlib")
    require(problem.get("title") == source["declaration"], "inheritance: substituted declaration title")
    require(problem.get("resolvedHoles", [{}])[0].get("declarationName") == "conjecture", "inheritance: substituted hole")
    require(problem.get("resolvedHoles", [{}])[0].get("explicitParameters") == ["n", "hn"], "inheritance: missing parameters")
    require(problem.get("resolvedHoles", [{}])[0].get("sameModuleDependencies") == source["copied_dependencies"], "inheritance: missing dependency")
    context = (frozen / "context/OeisA303656_conjecture.lean").read_text(encoding="utf-8")
    require(problem.get("moduleContent") == context, "inheritance: request/context drift")
    require(provenance.get("permitted_axioms") == STANDARD_AXIOMS, "inheritance: missing or forged assumptions")
    require(provenance.get("source", {}).get("commit") == source["commit"], "inheritance: stale source commit")
    require(provenance.get("source", {}).get("blob_sha") == source["blob"], "inheritance: substituted source blob")
    require(provenance.get("source", {}).get("declaration") == source["declaration"], "inheritance: substituted source declaration")
    require(provenance.get("source", {}).get("lean_toolchain") == source["lean_toolchain"], "inheritance: forged source toolchain")
    require(provenance.get("source", {}).get("mathlib_revision") == source["mathlib_revision"], "inheritance: forged source Mathlib")
    require(provenance.get("source", {}).get("copied_dependencies") == source["copied_dependencies"], "inheritance: provenance dependency loss")
    require(provenance.get("digests", {}).get("module") == sha256(context.encode()), "inheritance: drifted module digest")

    generated = parse_digest_inventory(frozen / "generated-files.sha256")
    require(set(generated) == set([
        "Challenge.lean", "ChallengeDeps.lean", "README.md", "Solution.lean",
        "Submission.lean", "Submission/Helpers.lean", "WorkspaceTest.lean",
        "config.json", "holes.json", "lakefile.toml", "lean-toolchain"
    ]), "inheritance: generated response inventory is not closed")
    for retained in ("Challenge.lean", "ChallengeDeps.lean", "Solution.lean", "config.json", "holes.json", "lakefile.toml", "lean-toolchain"):
        check_digest(frozen / "generated" / retained, generated[retained])
    config = read_json(frozen / "generated/config.json")
    require(config.get("theorem_names") == ["conjecture"], "inheritance: substituted generated theorem")
    require(config.get("permitted_axioms") == STANDARD_AXIOMS, "inheritance: generated assumptions")
    require(len(packet["environment_drift_cases"]) >= 2, "inheritance: drift calibration")
    require(history["classification"] == "meaning_preserved_with_witness", "inheritance: history classification")
    require(set(packet["watcher_classification"]) == {
        "unchanged_semantics", "meaning_change", "environment_only_invalidation", "unprovable_state"
    }, "inheritance: watcher states")


def load_packets(bundle: Path) -> tuple[dict, dict]:
    return (
        read_json(bundle / "cases/erdos-730/packet.json"),
        read_json(bundle / "cases/fc-leaneval-oeis-303656/packet.json"),
    )


def validate_bundle(bundle: Path, packets: tuple[dict, dict] | None = None) -> None:
    erdos, inheritance = packets if packets is not None else load_packets(bundle)
    validate_erdos(bundle, erdos)
    validate_fc_leaneval(bundle, inheritance)


def run_git(repo: Path, *args: str, binary: bool = False) -> bytes | str:
    proc = subprocess.run(
        ["git", "-C", str(repo), *args], capture_output=True, check=False
    )
    if proc.returncode:
        raise PacketError(f"git {' '.join(args)} failed in {repo}: {proc.stderr.decode(errors='replace').strip()}")
    return proc.stdout if binary else proc.stdout.decode().strip()


def normalized_url(url: str) -> str:
    return url.removesuffix(".git").rstrip("/")


def require_remote(repo: Path, expected: str) -> None:
    remotes = run_git(repo, "remote", "-v")
    urls = {normalized_url(line.split()[1]) for line in str(remotes).splitlines() if len(line.split()) >= 2}
    require(normalized_url(expected) in urls, f"expected remote {expected} absent in {repo}")


def verify_git_file(repo: Path, commit: str, path: str, blob: str, digest: str) -> None:
    require(HEX40.fullmatch(commit) is not None, f"invalid commit {commit}")
    run_git(repo, "cat-file", "-e", f"{commit}^{{commit}}")
    listing = str(run_git(repo, "ls-tree", commit, "--", path)).split()
    require(len(listing) >= 4 and listing[1] == "blob" and listing[2] == blob, f"blob mismatch {commit}:{path}")
    data = run_git(repo, "show", f"{commit}:{path}", binary=True)
    require(sha256(data) == digest, f"content mismatch {commit}:{path}")


def verify_live(bundle: Path, lean_proofs: Path, formal_conjectures: Path, lean_eval: Path, generator: Path | None) -> None:
    erdos, inheritance = load_packets(bundle)
    fc_root = erdos["roots"]["formal_conjectures"]
    require_remote(formal_conjectures, fc_root["repository"])
    for item in fc_root["files"]:
        verify_git_file(formal_conjectures, fc_root["commit"], item["path"], item["blob"], item["sha256"])
    lp_root = erdos["roots"]["lean_proofs"]
    require_remote(lean_proofs, lp_root["repository"])
    for item in lp_root["files"]:
        verify_git_file(lean_proofs, lp_root["commit"], item["path"], item["blob"], item["sha256"])

    source = inheritance["roots"]["formal_conjectures_source"]
    verify_git_file(formal_conjectures, source["commit"], source["path"], source["blob"], source["sha256"])
    verify_git_file(formal_conjectures, source["commit"], "lean-toolchain", source["lean_toolchain_blob"], source["lean_toolchain_sha256"])
    verify_git_file(formal_conjectures, source["commit"], "lake-manifest.json", source["lake_manifest_blob"], source["lake_manifest_sha256"])
    adapter = inheritance["roots"]["formal_conjectures_adapter"]
    require_remote(formal_conjectures, adapter["repository"])
    for path, blob, digest in adapter["files"]:
        verify_git_file(formal_conjectures, adapter["commit"], path, blob, digest)
    history = inheritance["historical_source_change"]
    verify_git_file(formal_conjectures, history["parent"], source["path"], history["before_blob"], history["before_sha256"])
    verify_git_file(formal_conjectures, history["commit"], source["path"], history["after_blob"], history["after_sha256"])

    target = inheritance["roots"]["lean_eval_target"]
    require_remote(lean_eval, target["repository"])
    verify_git_file(lean_eval, target["commit"], "lean-toolchain", target["lean_toolchain_blob"], target["lean_toolchain_sha256"])
    verify_git_file(lean_eval, target["commit"], "lake-manifest.json", target["lake_manifest_blob"], target["lake_manifest_sha256"])
    if generator is not None:
        gen = inheritance["roots"]["generator"]
        require_remote(generator, gen["repository"])
        run_git(generator, "cat-file", "-e", f"{gen['commit']}^{{commit}}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean-proofs", type=Path)
    parser.add_argument("--formal-conjectures", type=Path)
    parser.add_argument("--lean-eval", type=Path)
    parser.add_argument("--generator", type=Path)
    args = parser.parse_args()
    bundle = Path(__file__).resolve().parent
    validate_bundle(bundle)
    live = (args.lean_proofs, args.formal_conjectures, args.lean_eval)
    require(all(value is not None for value in live) or all(value is None for value in live), "supply all three live repositories or none")
    if all(value is not None for value in live):
        verify_live(bundle, args.lean_proofs, args.formal_conjectures, args.lean_eval, args.generator)
    print("PASS: two closed candidate packets verified; authority_effect=none")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
