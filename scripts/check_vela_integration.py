#!/usr/bin/env python3
"""Check lean-proofs semantics after Vela Core validates the shared waist."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import sys
import tomllib
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
OUTPUT_SCHEMA = "lean-proofs.verification-input.v0.1"
EXPECTED_REPOSITORY = "https://github.com/williamjblair/lean-proofs.git"
EXPECTED_NATIVE_REVISION = "a8c2872a27cf8d11cf6744ca4a2c5b49ace5fea0"
EXPECTED_CORE_REPOSITORY = "https://github.com/vela-science/vela.git"
EXPECTED_CORE_REVISION = "329487f29ad4c6313a2be7c091d46085b61ff03b"
EXPECTED_CORE_VERSION = "0.976.1"
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.29.1"
EXPECTED_MATHLIB = "5e932f97dd25535344f80f9dd8da3aab83df0fe6"
SELECTED_THEOREM = "Erdos154.erdos_154_sumset"
SELECTED_SOURCE = "ErdosProblems/Erdos154Sumset.lean"
EXPECTED_LOCAL_REFERENCES = {
    "lakefile.toml": {
        "schema": "vela.exact-reference.v0.1",
        "native_identity": {
            "system": "git+lean4",
            "object_kind": "project_configuration",
            "identifier": "lakefile.toml",
        },
        "revision": {"kind": "git_commit", "value": EXPECTED_NATIVE_REVISION},
        "content_fixity": {
            "media_type": "application/toml",
            "digest": "sha256:59cdf241ac34e762631b3c7d0c39d51a27146eff6405a4b86caaff739be90ef1",
            "size": 586,
        },
        "selector": {"kind": "path", "value": "lakefile.toml"},
        "locator": {
            "uri": (
                "https://github.com/williamjblair/lean-proofs/blob/"
                f"{EXPECTED_NATIVE_REVISION}/lakefile.toml"
            ),
            "mutable": False,
            "authentication": "public",
        },
    },
    SELECTED_THEOREM: {
        "schema": "vela.exact-reference.v0.1",
        "native_identity": {
            "system": "git+lean4",
            "object_kind": "theorem",
            "identifier": SELECTED_THEOREM,
        },
        "revision": {"kind": "git_commit", "value": EXPECTED_NATIVE_REVISION},
        "content_fixity": {
            "media_type": "text/x-lean",
            "digest": "sha256:9ac3fc83bbeba2df4739b5f3d69130876d99ea09c47d0c30977339904d74f457",
            "size": 25003,
        },
        "selector": {"kind": "lean_declaration", "value": SELECTED_THEOREM},
        "locator": {
            "uri": (
                "https://github.com/williamjblair/lean-proofs/blob/"
                f"{EXPECTED_NATIVE_REVISION}/{SELECTED_SOURCE}"
            ),
            "mutable": False,
            "authentication": "public",
        },
    },
}
EXPECTED_EXTERNAL_REFERENCE = {
    "schema": "vela.exact-reference.v0.1",
    "native_identity": {
        "system": "git+lean4",
        "object_kind": "theorem",
        "identifier": "FormalConjectures.erdos_154",
    },
    "revision": {
        "kind": "git_commit",
        "value": "96eeecf40bc06ddc8bae6d106f461d4fd774858a",
    },
    "content_fixity": {
        "media_type": "text/x-lean",
        "digest": "sha256:cb6c207f5a6d9710a50b876e5719a13498315b2f539a34230ca4ec6813136032",
        "size": 3752,
    },
    "selector": {"kind": "lean_declaration", "value": "FormalConjectures.erdos_154"},
    "locator": {
        "uri": "https://github.com/williamjblair/formal-conjectures/blob/96eeecf40bc06ddc8bae6d106f461d4fd774858a/FormalConjectures/ErdosProblems/154.lean",
        "mutable": False,
        "authentication": "public",
    },
}
EXPECTED_CLOSURE = [
    {
        "path": "ErdosProblems/Erdos154Sumset.lean",
        "digest": "sha256:9ac3fc83bbeba2df4739b5f3d69130876d99ea09c47d0c30977339904d74f457",
        "size": 25003,
    },
    {
        "path": "ErdosProblems/Erdos154.lean",
        "digest": "sha256:985900ccba24e5ba4d145e74da5b84ceb94338ba627b41688fc3892cae091822",
        "size": 76921,
    },
    {
        "path": "proofs.yaml",
        "digest": "sha256:c3902930f1e3a910fc2bf4a10397fda769c84e0b1b7b84de0cb109d5488110a3",
        "size": 35553,
    },
    {
        "path": "Audit.lean",
        "digest": "sha256:59df59b5cf150b3048a32a85f843dd4d07fbe91eb086a2f1cda8d20b93aebc65",
        "size": 4412,
    },
    {
        "path": "lean-toolchain",
        "digest": "sha256:7dc000621e0046d1aada809e2b7177e64454645cf4c741e9daaf79c99ec2e7a2",
        "size": 25,
    },
    {
        "path": "lakefile.toml",
        "digest": "sha256:59cdf241ac34e762631b3c7d0c39d51a27146eff6405a4b86caaff739be90ef1",
        "size": 586,
    },
    {
        "path": "lake-manifest.json",
        "digest": "sha256:f4c3e1fea9e745548c15b78b91015489277625c3dee15ab1ebe8bf6acf57b320",
        "size": 4736,
    },
]


class ValidationError(ValueError):
    """A Core or source-owned semantic check failed closed."""


def sha256_file(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def retained_file(root: Path, raw: str | Path) -> Path:
    """Resolve a source-owned retained input without following repository links."""

    raw_text = str(raw)
    relative = Path(raw_text)
    rendered = relative.as_posix()
    if (
        relative.is_absolute()
        or rendered in {"", "."}
        or any(part in {"", ".", ".."} for part in relative.parts)
        or raw_text != rendered
    ):
        raise ValidationError(f"non-canonical retained path: {raw}")
    repository = root.resolve(strict=True)
    candidate = repository / relative
    current = repository
    for part in relative.parts:
        current = current / part
        if current.is_symlink():
            raise ValidationError(f"retained file must not be a symlink: {rendered}")
    try:
        resolved = candidate.resolve(strict=True)
        resolved.relative_to(repository)
    except (FileNotFoundError, ValueError) as error:
        raise ValidationError(
            f"retained file is missing or escapes repository: {rendered}"
        ) from error
    if not stat.S_ISREG(candidate.lstat().st_mode):
        raise ValidationError(f"retained path is not a regular file: {rendered}")
    return candidate


def load_toml(root: Path, relative: str) -> dict[str, Any]:
    with retained_file(root, relative).open("rb") as handle:
        return tomllib.load(handle)


def run_core_check(root: Path, vela_bin: str) -> dict[str, Any]:
    """Delegate the shared Manifest/Profile/Binding/Method waist to Core."""

    try:
        version = subprocess.run(
            [vela_bin, "--version"],
            check=False,
            capture_output=True,
            text=True,
        )
        if version.returncode != 0 or version.stdout.strip() != (
            f"vela {EXPECTED_CORE_VERSION}"
        ):
            raise ValidationError(
                "Vela Core binary version drift from the pinned published checker"
            )
        completed = subprocess.run(
            [vela_bin, "integration", "check", str(root), "--json"],
            check=False,
            capture_output=True,
            text=True,
        )
    except OSError as error:
        raise ValidationError(
            f"cannot execute Vela Core integration checker: {error}"
        ) from error
    if completed.returncode != 0:
        detail = completed.stderr.strip() or completed.stdout.strip()
        raise ValidationError(f"Vela Core integration check failed: {detail}")
    try:
        result = json.loads(completed.stdout)
    except json.JSONDecodeError as error:
        raise ValidationError(
            "Vela Core integration check returned non-JSON output"
        ) from error
    if (
        result.get("schema") != "vela.cli.integration-check.v1"
        or result.get("ok") is not True
        or result.get("command") != "integration check"
        or result.get("authority_effect") != "none"
    ):
        raise ValidationError(
            "Vela Core integration check did not return a successful check result"
        )
    return result


def parse_scalar(raw: str) -> Any:
    raw = raw.strip()
    if len(raw) >= 2 and raw[0] == raw[-1] == '"':
        return json.loads(raw)
    if raw == "true":
        return True
    if raw == "false":
        return False
    if re.fullmatch(r"[0-9]+", raw):
        return int(raw)
    return raw


def parse_proofs(path: Path) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    header: dict[str, Any] = {}
    proofs: list[dict[str, Any]] = []
    current: dict[str, Any] | None = None
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        start = re.match(r"^  - ([a-z_]+):\s*(.+)$", line)
        if start:
            current = {start.group(1): parse_scalar(start.group(2))}
            proofs.append(current)
            continue
        field = re.match(r"^    ([a-z_]+):\s*(.*)$", line)
        if field and current is not None:
            value = field.group(2)
            if value in {">-", "|"}:
                current[field.group(1)] = value
            elif value:
                current[field.group(1)] = parse_scalar(value)
            continue
        top = re.match(r"^([a-z_]+):\s*(.+)$", line)
        if top and top.group(1) != "proofs":
            header[top.group(1)] = parse_scalar(top.group(2))
    return header, proofs


def audit_targets(path: Path) -> set[str]:
    targets: set[str] = set()
    active = False
    for line in path.read_text(encoding="utf-8").splitlines():
        if line == "-- Manifest-tracked formal proof targets.":
            active = True
        elif line.startswith("-- Conditional research surfaces"):
            active = False
        elif active and line.startswith("#print axioms "):
            targets.add(line.removeprefix("#print axioms ").strip())
    return targets


def declaration_is_present(source: str, theorem: str) -> bool:
    namespace: list[str] = []
    for line in source.splitlines():
        opened = re.match(r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$", line)
        if opened:
            namespace.extend(opened.group(1).split("."))
            continue
        declaration = re.match(
            r"^\s*(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_']*)(?:\s|:|\(|$)",
            line,
        )
        if declaration and ".".join([*namespace, declaration.group(1)]) == theorem:
            return True
        ended = re.match(r"^\s*end\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$", line)
        if ended:
            parts = ended.group(1).split(".")
            if namespace[-len(parts) :] == parts:
                del namespace[-len(parts) :]
    return False


def proof_source(root: Path, raw: str) -> Path:
    relative = Path(raw)
    if relative.is_absolute() or ".." in relative.parts:
        raise ValidationError(f"unsupported proof source path: {raw}")
    if not (raw.startswith("ErdosProblems/") or raw.startswith("starfleet/")):
        raise ValidationError(f"unsupported proof source path: {raw}")
    return retained_file(root, relative)


def validate_proof_index(root: Path) -> list[dict[str, Any]]:
    header, proofs = parse_proofs(retained_file(root, "proofs.yaml"))
    toolchain = (
        retained_file(root, "lean-toolchain").read_text(encoding="utf-8").strip()
    )
    if header != {
        "repo": "williamjblair/lean-proofs",
        "toolchain": toolchain,
        "mathlib": "v4.29.1",
    }:
        raise ValidationError(f"proof index header drift: {header}")
    if toolchain != EXPECTED_TOOLCHAIN or len(proofs) != 79:
        raise ValidationError("toolchain or proof index count drift")
    manifest = json.loads(
        retained_file(root, "lake-manifest.json").read_text(encoding="utf-8")
    )
    packages = {package["name"]: package for package in manifest["packages"]}
    if packages.get("mathlib", {}).get("rev") != EXPECTED_MATHLIB:
        raise ValidationError("root Mathlib revision drift")
    required = {
        "problem",
        "source",
        "file",
        "theorem",
        "statement",
        "axioms_clean",
        "fc_target",
    }
    root_audit = audit_targets(retained_file(root, "Audit.lean"))
    root_theorems: set[str] = set()
    for proof in proofs:
        missing = required - set(proof)
        if missing:
            raise ValidationError(
                f"proof entry missing {sorted(missing)}: {proof.get('theorem')}"
            )
        source_path = str(proof["file"])
        source = proof_source(root, source_path).read_text(encoding="utf-8")
        theorem = str(proof["theorem"])
        if not declaration_is_present(source, theorem):
            raise ValidationError(f"theorem drift: {theorem} not in {source_path}")
        if proof["axioms_clean"] is not True:
            raise ValidationError(f"false clean state for {theorem}")
        target = Path(str(proof["fc_target"]))
        if (
            target.is_absolute()
            or ".." in target.parts
            or not str(target).startswith("FormalConjectures/")
        ):
            raise ValidationError(f"external identity drift for {theorem}")
        if source_path.startswith("ErdosProblems/"):
            if re.search(r"\b(?:sorry|admit)\b", source):
                raise ValidationError(f"false axioms_clean claim: {theorem}")
            root_theorems.add(theorem)
            if theorem not in root_audit:
                raise ValidationError(f"missing axiom audit coverage: {theorem}")
            if proof.get("toolchain", toolchain) != toolchain:
                raise ValidationError(f"root toolchain drift for {theorem}")
        else:
            project = Path(*Path(source_path).parts[:2])
            project_toolchain = (
                retained_file(root, project / "lean-toolchain")
                .read_text(encoding="utf-8")
                .strip()
            )
            if proof.get("toolchain") != project_toolchain:
                raise ValidationError(f"Starfleet toolchain drift for {theorem}")
            if proof.get("mathlib") != "git#fabf563a7c95a166b8d7b6efca11c8b4dc9d911f":
                raise ValidationError(f"Starfleet Mathlib drift for {theorem}")
            project_audit = retained_file(root, project / "Audit.lean").read_text(
                encoding="utf-8"
            )
            if f"#print axioms {theorem}" not in project_audit:
                raise ValidationError(
                    f"missing Starfleet axiom audit coverage: {theorem}"
                )
    if root_theorems != root_audit:
        raise ValidationError("proofs.yaml and root Audit.lean disagree")
    return proofs


def validate_local_reference(
    root: Path, reference: dict[str, Any], proofs: list[dict[str, Any]]
) -> None:
    identifier = reference.get("native_identity", {}).get("identifier")
    expected = EXPECTED_LOCAL_REFERENCES.get(str(identifier))
    if expected is None or reference != expected:
        raise ValidationError("local Exact Reference drift from pinned source revision")
    if identifier == "lakefile.toml":
        source_path = "lakefile.toml"
    else:
        matches = [proof for proof in proofs if proof.get("theorem") == identifier]
        if len(matches) != 1:
            raise ValidationError(
                "Binding theorem is not an exact proofs.yaml identity"
            )
        source_path = str(matches[0]["file"])
        source_text = proof_source(root, source_path).read_text(encoding="utf-8")
        if not declaration_is_present(source_text, str(identifier)):
            raise ValidationError("Binding theorem declaration drift")
    source = retained_file(root, source_path)
    fixity = reference["content_fixity"]
    if (
        sha256_file(source) != fixity["digest"]
        or source.stat().st_size != fixity["size"]
    ):
        raise ValidationError("Binding content fixity does not resolve to source bytes")


def validate_example(root: Path, proofs: list[dict[str, Any]]) -> dict[str, Any]:
    example = load_toml(root, ".vela/examples/erdos-154-exact-reference.toml")
    validate_local_reference(root, example["reference"], proofs)
    if example["external_reference"] != EXPECTED_EXTERNAL_REFERENCE:
        raise ValidationError("external Formal Conjectures Exact Reference drift")
    if example["mapping"] != {"relation": "close"} or example["translation"] != {
        "disposition": "normalized"
    }:
        raise ValidationError("selected semantic mapping or translation drift")
    if (
        example["availability"].get("class") != "public"
        or example["availability"].get("private_context_required") is not False
    ):
        raise ValidationError("selected evidence availability drift")
    if example["closure"] != EXPECTED_CLOSURE:
        raise ValidationError("selected portable closure drift")
    for item in EXPECTED_CLOSURE:
        path = retained_file(root, item["path"])
        if sha256_file(path) != item["digest"] or path.stat().st_size != item["size"]:
            raise ValidationError(f"closure drift: {item['path']}")
    encoded = json.dumps(example, ensure_ascii=False).encode("utf-8")
    if b"/Users/" in encoded or b"/private/" in encoded or b"file://" in encoded:
        raise ValidationError("private path in portable example")
    return example


def validate_source_bindings(
    root: Path, proofs: list[dict[str, Any]], example: dict[str, Any]
) -> dict[str, Any]:
    project = load_toml(root, ".vela/bindings/lean-project.toml")
    formal = load_toml(root, ".vela/bindings/formal-proof.toml")
    if project["references"] != [EXPECTED_LOCAL_REFERENCES["lakefile.toml"]]:
        raise ValidationError("lean-project Binding reference drift")
    validate_local_reference(root, project["references"][0], proofs)
    if formal["references"] != [example["reference"]]:
        raise ValidationError(
            "selected example and formal-proof Binding reference drift"
        )
    selected = [proof for proof in proofs if proof.get("problem") == 154]
    if len(selected) != 1 or selected[0].get("theorem") != SELECTED_THEOREM:
        raise ValidationError("selected Erdos 154 proof index drift")
    if selected[0].get("fc_target") != "FormalConjectures/ErdosProblems/154.lean":
        raise ValidationError("selected Erdos 154 external target drift")
    expected_target = (
        "williamjblair/formal-conjectures@96eeecf40bc06ddc8bae6d106f461d4fd774858a:"
        "FormalConjectures.erdos_154"
    )
    if not any(
        mapping
        == {"source": SELECTED_THEOREM, "target": expected_target, "relation": "close"}
        for mapping in formal["mappings"]
    ):
        raise ValidationError("selected Erdos 154 semantic mapping drift")
    if {method["id"] for method in formal["methods"]} != {
        "lean-build",
        "axiom-audit",
        "integration-validator",
    }:
        raise ValidationError("selected formal-proof Method coverage drift")
    return formal


def validate_method_semantics(root: Path) -> dict[str, dict[str, Any]]:
    methods = {
        name: load_toml(root, f".vela/methods/{name}.toml")
        for name in ("lean-build", "axiom-audit", "integration-validator")
    }
    if methods["lean-build"]["environment"] != {
        "kind": "exact",
        "revision": EXPECTED_NATIVE_REVISION,
        "toolchain": EXPECTED_TOOLCHAIN,
        "mathlib_revision": EXPECTED_MATHLIB,
    }:
        raise ValidationError("lean build environment drift")
    audit = methods["axiom-audit"]["environment"]
    if (
        audit.get("revision") != EXPECTED_NATIVE_REVISION
        or audit.get("toolchain") != EXPECTED_TOOLCHAIN
    ):
        raise ValidationError("axiom audit environment drift")
    if audit.get("allowed_axioms") != ["propext", "Classical.choice", "Quot.sound"]:
        raise ValidationError("axiom audit policy drift")
    integration = methods["integration-validator"]
    expected_core_input = f"Vela Core integration checker@{EXPECTED_CORE_REVISION}"
    if expected_core_input not in integration["inputs"]:
        raise ValidationError("integration validator Core input revision drift")
    if integration["environment"].get("core") != {
        "repository": EXPECTED_CORE_REPOSITORY,
        "revision": EXPECTED_CORE_REVISION,
        "binary": "vela",
        "version": EXPECTED_CORE_VERSION,
        "command": "vela integration check <repository> --json",
    }:
        raise ValidationError("integration validator Core environment drift")
    return methods


def build_verification_input(
    reference: dict[str, Any], method_root: str, artifacts: list[dict[str, Any]]
) -> dict[str, Any]:
    return {
        "schema": OUTPUT_SCHEMA,
        "document_kind": "source_owned_verification_input",
        "subject": reference,
        "method_root": method_root,
        "artifacts": artifacts,
        "check_request": {
            "method_id": "axiom-audit",
            "command": ["bash", "scripts/check_axioms.sh"],
            "expected_exit_code": 0,
        },
        "scope": "Request a pinned axiom audit of the selected declaration",
        "nonclaims": [
            "This input records no check outcome or evidence availability.",
            "Any resulting scoped check is not scientific acceptance, a Vela Decision, or Standing.",
        ],
        "provenance": {
            "agent": "local:verification-input-builder",
            "activity": "construct-verification-input",
            "entities": [f"method:{method_root}"],
            "role": "producer",
        },
        "authority_effect": "none",
    }


def validate_verification_input(
    value: dict[str, Any],
    reference: dict[str, Any],
    method_root: str,
    artifacts: list[dict[str, Any]],
) -> None:
    expected = build_verification_input(reference, method_root, artifacts)
    if value != expected:
        raise ValidationError("source-owned verification input drift")
    forbidden = {
        "result_root",
        "verification_input_root",
        "outcome",
        "observed_outcome",
        "evidence_availability",
        "accepted",
        "standing",
    }
    if forbidden.intersection(value):
        raise ValidationError(
            "source-owned verification input claims an unperformed result"
        )


def validate_repository(root: Path = ROOT, vela_bin: str = "vela") -> dict[str, Any]:
    core = run_core_check(root, vela_bin)
    manifest = load_toml(root, "vela.toml")
    if manifest["repository"] != {
        "identity": EXPECTED_REPOSITORY,
        "revision_policy": "exact_git_commit",
        "revision": EXPECTED_NATIVE_REVISION,
    }:
        raise ValidationError("source repository identity or revision drift")
    proofs = validate_proof_index(root)
    example = validate_example(root, proofs)
    binding = validate_source_bindings(root, proofs, example)
    methods = validate_method_semantics(root)
    return {
        "core": core,
        "manifest": manifest,
        "proofs": proofs,
        "binding": binding,
        "methods": methods,
        "example": example,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--vela-bin", default=os.environ.get("VELA_BIN", "vela"))
    parser.add_argument("--emit", type=Path)
    args = parser.parse_args()
    try:
        packet = validate_repository(args.root.resolve(), args.vela_bin)
        if args.emit:
            method_root = packet["methods"]["axiom-audit"]["method_root"]
            value = build_verification_input(
                packet["example"]["reference"],
                method_root,
                packet["example"]["closure"],
            )
            validate_verification_input(
                value,
                packet["example"]["reference"],
                method_root,
                packet["example"]["closure"],
            )
            args.emit.write_text(
                json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
                encoding="utf-8",
            )
        print(
            "Vela Core waist + lean-proofs semantics: ok (79 proofs; authority_effect none)"
        )
        return 0
    except (
        KeyError,
        OSError,
        TypeError,
        ValidationError,
        json.JSONDecodeError,
        tomllib.TOMLDecodeError,
    ) as error:
        print(f"Vela native integration: FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
