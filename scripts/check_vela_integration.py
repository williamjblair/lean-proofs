#!/usr/bin/env python3
"""Validate the source-owned, non-authoritative Vela integration packet.

The draft root framing matches Vela INT-00: parse TOML, replace the document's
root field with the empty string, encode canonical JSON, prefix the UTF-8 schema
tag plus NUL, and SHA-256 the framed bytes. This validator is intentionally
repository-local until two maintained consumers justify Core extraction.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
SCHEMAS = {
    "manifest": "vela.integration-manifest.v0.1",
    "profile": "vela.integration-profile.v0.1",
    "binding": "vela.integration-binding.v0.1",
    "method": "vela.integration-method.v0.1",
    "result": "vela.integration-check-result.v0.1",
}
ROOT_FIELDS = {kind: f"{kind}_root" for kind in SCHEMAS}
FULL_ROOT = re.compile(r"sha256:[0-9a-f]{64}\Z")
COMMIT = re.compile(r"[0-9a-f]{40}\Z")
MAPPINGS = {"exact", "close", "broader", "narrower", "related"}
TRANSLATIONS = {
    "preserved", "normalized", "derived", "approximated", "omitted",
    "unsupported", "assumed", "unresolved",
}
OUTPUTS = {"exact_reference", "submission_draft", "verification_input"}
AUTHORITY_FIELDS = {
    "authority", "authority_key", "decision", "event", "repository_id",
    "standing", "accepted", "acceptance",
}
EXPECTED_REPOSITORY = "https://github.com/williamjblair/lean-proofs.git"
EXPECTED_NATIVE_REVISION = "a8c2872a27cf8d11cf6744ca4a2c5b49ace5fea0"


class ValidationError(ValueError):
    """A contract or native-source invariant failed closed."""


def canonical_bytes(value: Any) -> bytes:
    """Canonical JSON for the I-JSON subset used by these TOML documents."""

    return json.dumps(
        value,
        ensure_ascii=False,
        allow_nan=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")


def document_root(kind: str, value: dict[str, Any]) -> str:
    rooted = copy.deepcopy(value)
    rooted[ROOT_FIELDS[kind]] = ""
    framed = SCHEMAS[kind].encode("utf-8") + b"\0" + canonical_bytes(rooted)
    return "sha256:" + hashlib.sha256(framed).hexdigest()


def sha256_file(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def closed(value: dict[str, Any], fields: set[str], label: str) -> None:
    missing = fields - set(value)
    unknown = set(value) - fields
    if missing or unknown:
        raise ValidationError(
            f"{label} fields: missing={sorted(missing)} unknown={sorted(unknown)}"
        )


def local_file(root: Path, raw: str) -> Path:
    relative = Path(raw)
    if not raw or relative.is_absolute() or ".." in relative.parts:
        raise ValidationError(f"path escape: {raw!r}")
    candidate = root / relative
    if candidate.is_symlink() or not candidate.is_file():
        raise ValidationError(f"missing or non-regular path: {raw}")
    if root.resolve() not in candidate.resolve().parents:
        raise ValidationError(f"path escape after resolution: {raw}")
    return candidate


def load_toml(root: Path, raw: str) -> dict[str, Any]:
    with local_file(root, raw).open("rb") as handle:
        return tomllib.load(handle)


def reject_authority_fields(value: Any, path: str = "$") -> None:
    if isinstance(value, dict):
        for key, child in value.items():
            if key.lower() in AUTHORITY_FIELDS:
                raise ValidationError(f"authority field {path}.{key}")
            reject_authority_fields(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            reject_authority_fields(child, f"{path}[{index}]")


def validate_rooted(kind: str, value: dict[str, Any]) -> None:
    if value.get("schema") != SCHEMAS[kind]:
        raise ValidationError(f"unsupported {kind} schema")
    field = ROOT_FIELDS[kind]
    root = str(value.get(field, ""))
    if not FULL_ROOT.fullmatch(root) or root != document_root(kind, value):
        raise ValidationError(f"{kind} root or root domain mismatch")
    if value.get("authority_effect") != "none":
        raise ValidationError(f"{kind} authority effect")
    reject_authority_fields(value)


def validate_reference(reference: dict[str, Any], expected_revision: str) -> None:
    closed(
        reference,
        {"schema", "native_identity", "revision", "content_fixity", "selector", "locator"},
        "Exact Reference",
    )
    if reference["schema"] != "vela.exact-reference.v0.1":
        raise ValidationError("unsupported Exact Reference schema")
    identity = reference["native_identity"]
    closed(identity, {"system", "object_kind", "identifier"}, "native identity")
    revision = reference["revision"]
    closed(revision, {"kind", "value"}, "revision")
    if revision != {"kind": "git_commit", "value": expected_revision}:
        raise ValidationError("mutable identity or revision drift")
    fixity = reference["content_fixity"]
    closed(fixity, {"media_type", "digest", "size"}, "content fixity")
    if not FULL_ROOT.fullmatch(str(fixity["digest"])):
        raise ValidationError("content fixity digest")
    if not isinstance(fixity["size"], int) or isinstance(fixity["size"], bool) or fixity["size"] < 0:
        raise ValidationError("content fixity size")
    selector = reference["selector"]
    closed(selector, {"kind", "value"}, "selector")
    if selector["value"] != identity["identifier"]:
        raise ValidationError("selector drift")
    locator = reference["locator"]
    closed(locator, {"uri", "mutable", "authentication"}, "locator")
    if locator["mutable"] is not False or locator["authentication"] != "public":
        raise ValidationError("mutable or authenticated exact locator")
    if f"/blob/{expected_revision}/" not in locator["uri"]:
        raise ValidationError("locator does not carry exact revision")


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
    """Parse the deliberately small proofs.yaml surface without a YAML runtime."""

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
    leaf = re.escape(theorem.rsplit(".", 1)[-1])
    return bool(re.search(rf"(?m)^\s*(?:theorem|lemma)\s+{leaf}(?:\s|:|\()", source))


def validate_proof_index(root: Path) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    header, proofs = parse_proofs(local_file(root, "proofs.yaml"))
    expected_toolchain = local_file(root, "lean-toolchain").read_text(encoding="utf-8").strip()
    if header != {
        "repo": "williamjblair/lean-proofs",
        "toolchain": expected_toolchain,
        "mathlib": "v4.29.1",
    }:
        raise ValidationError(f"proof index header drift: {header}")
    if len(proofs) != 79:
        raise ValidationError(f"proof index count drift: {len(proofs)}")
    required = {"problem", "source", "file", "theorem", "statement", "axioms_clean", "fc_target"}
    root_audit = audit_targets(local_file(root, "Audit.lean"))
    root_theorems: set[str] = set()
    for proof in proofs:
        missing = required - set(proof)
        if missing:
            raise ValidationError(f"proof entry missing {sorted(missing)}: {proof.get('theorem')}")
        source_path = str(proof["file"])
        source = local_file(root, source_path).read_text(encoding="utf-8")
        theorem = str(proof["theorem"])
        if not declaration_is_present(source, theorem):
            raise ValidationError(f"theorem drift: {theorem} not in {source_path}")
        if proof["axioms_clean"] is not True:
            raise ValidationError(f"false clean state for {theorem}")
        target = Path(str(proof["fc_target"]))
        if target.is_absolute() or ".." in target.parts or not str(target).startswith("FormalConjectures/"):
            raise ValidationError(f"external identity drift for {theorem}")
        if source_path.startswith("ErdosProblems/"):
            if re.search(r"\b(?:sorry|admit)\b", source):
                raise ValidationError(f"false axioms_clean claim: {theorem}")
            root_theorems.add(theorem)
            if theorem not in root_audit:
                raise ValidationError(f"missing axiom audit coverage: {theorem}")
            if proof.get("toolchain", expected_toolchain) != expected_toolchain:
                raise ValidationError(f"root toolchain drift for {theorem}")
        elif source_path.startswith("starfleet/"):
            project = Path(*Path(source_path).parts[:2])
            project_toolchain = local_file(root, str(project / "lean-toolchain")).read_text(encoding="utf-8").strip()
            if proof.get("toolchain") != project_toolchain:
                raise ValidationError(f"Starfleet toolchain drift for {theorem}")
            if proof.get("mathlib") != "git#fabf563a7c95a166b8d7b6efca11c8b4dc9d911f":
                raise ValidationError(f"Starfleet Mathlib drift for {theorem}")
            project_audit = local_file(root, str(project / "Audit.lean")).read_text(encoding="utf-8")
            if f"#print axioms {theorem}" not in project_audit:
                raise ValidationError(f"missing Starfleet axiom audit coverage: {theorem}")
        else:
            raise ValidationError(f"unsupported proof source path: {source_path}")
    if root_theorems != root_audit:
        raise ValidationError("proofs.yaml and root Audit.lean disagree")
    return header, proofs


def validate_method(root: Path, method: dict[str, Any], revision: str) -> None:
    closed(
        method,
        {
            "schema", "method_root", "method_id", "version", "implementation",
            "environment", "inputs", "outputs", "limitations", "nonclaims",
            "authority_effect",
        },
        "Method",
    )
    if method["version"] != "0.1":
        raise ValidationError("unsupported Method version")
    implementation = method["implementation"]
    closed(implementation, {"path", "digest"}, "Method implementation")
    if sha256_file(local_file(root, implementation["path"])) != implementation["digest"]:
        raise ValidationError(f"Method implementation drift: {method['method_id']}")
    environment = method["environment"]
    if environment.get("kind") != "exact" or environment.get("revision") != revision:
        raise ValidationError(f"Method environment drift: {method['method_id']}")
    if not method["inputs"] or not method["outputs"] or not method["nonclaims"]:
        raise ValidationError(f"incomplete Method: {method['method_id']}")
    if any("acceptance" in claim.lower() and "not" not in claim.lower() for claim in method["nonclaims"]):
        raise ValidationError("Method presents a check as acceptance")


def validate_profile(profile: dict[str, Any]) -> None:
    closed(
        profile,
        {
            "schema", "profile_root", "profile_id", "version", "conformance",
            "rights", "limitations", "nonclaims", "authority_effect",
        },
        "Profile",
    )
    if profile["version"] != "0.1" or not profile["rights"]:
        raise ValidationError("unsupported or rights-free Profile")
    if not profile["conformance"] or not profile["limitations"] or not profile["nonclaims"]:
        raise ValidationError("incomplete Profile")


def validate_binding(
    binding: dict[str, Any], profiles: dict[str, dict[str, Any]],
    methods: dict[str, dict[str, Any]], revision: str,
) -> None:
    closed(
        binding,
        {
            "schema", "binding_root", "binding_id", "profile", "references",
            "mappings", "translations", "methods", "outputs", "authority_effect",
        },
        "Binding",
    )
    claimed_profile = binding["profile"]
    closed(claimed_profile, {"id", "version", "root"}, "Binding Profile")
    profile = profiles.get(claimed_profile["id"])
    if profile is None or claimed_profile != {
        "id": profile["profile_id"], "version": profile["version"], "root": profile["profile_root"]
    }:
        raise ValidationError("Profile root or version drift")
    if not binding["references"]:
        raise ValidationError("Binding has no Exact Reference")
    for reference in binding["references"]:
        validate_reference(reference, revision)
    for mapping in binding["mappings"]:
        closed(mapping, {"source", "target", "relation"}, "mapping")
        if mapping["relation"] not in MAPPINGS:
            raise ValidationError("mapping relation")
    for translation in binding["translations"]:
        closed(translation, {"source", "target", "disposition"}, "translation")
        if translation["disposition"] not in TRANSLATIONS:
            raise ValidationError("translation disposition")
    for required_method in binding["methods"]:
        closed(required_method, {"id", "root"}, "Binding Method")
        method = methods.get(required_method["id"])
        if method is None or required_method["root"] != method["method_root"]:
            raise ValidationError("missing Method or Method root drift")
    if not set(binding["outputs"]).issubset(OUTPUTS):
        raise ValidationError("authority output")


def validate_example(root: Path, revision: str) -> dict[str, Any]:
    example = load_toml(root, ".vela/examples/erdos-154-exact-reference.toml")
    closed(example, {"reference", "closure", "external_reference", "mapping", "translation", "availability", "nonclaims"}, "example")
    validate_reference(example["reference"], revision)
    validate_reference(example["external_reference"], "96eeecf40bc06ddc8bae6d106f461d4fd774858a")
    if example["mapping"] != {"relation": "close"} or example["translation"] != {"disposition": "normalized"}:
        raise ValidationError("example mapping and translation collapse")
    if example["availability"].get("class") != "public" or example["availability"].get("private_context_required") is not False:
        raise ValidationError("example availability")
    for item in example["closure"]:
        closed(item, {"path", "digest", "size"}, "closure item")
        path = local_file(root, item["path"])
        if sha256_file(path) != item["digest"] or path.stat().st_size != item["size"]:
            raise ValidationError(f"closure drift: {item['path']}")
    encoded = canonical_bytes(example)
    if b"/Users/" in encoded or b"/private/" in encoded or b"file://" in encoded:
        raise ValidationError("private path in portable example")
    if not example["nonclaims"]:
        raise ValidationError("example nonclaims")
    return example


def validate_result(result: dict[str, Any], reference: dict[str, Any], method_root: str) -> None:
    validate_rooted("result", result)
    closed(
        result,
        {
            "schema", "result_root", "subject", "method_root", "evidence_availability",
            "outcome", "scope", "nonclaims", "provenance", "authority_effect",
        },
        "result",
    )
    if result["subject"] != reference or result["method_root"] != method_root:
        raise ValidationError("result subject or Method drift")
    if result["evidence_availability"] == "unavailable" and result["outcome"] != "unavailable":
        raise ValidationError("unavailable evidence converted to result")
    if result["outcome"] not in {"pass", "fail", "inconclusive", "error", "unavailable"}:
        raise ValidationError("check result presented as acceptance")
    if not result["nonclaims"]:
        raise ValidationError("missing result nonclaims")
    closed(result["provenance"], {"agent", "activity", "entities", "role"}, "provenance")


def build_result(reference: dict[str, Any], method_root: str) -> dict[str, Any]:
    result = {
        "schema": SCHEMAS["result"],
        "result_root": "",
        "subject": reference,
        "method_root": method_root,
        "evidence_availability": "available",
        "outcome": "pass",
        "scope": "Pinned Lean build and selected declaration axiom audit",
        "nonclaims": [
            "This scoped check is not scientific acceptance, a Vela Decision, or Standing."
        ],
        "provenance": {
            "agent": "local:cold-consumer",
            "activity": "lean-build-and-axiom-audit",
            "entities": ["tool:leanprover/lean4:v4.29.1", f"method:{method_root}"],
            "role": "verifier",
        },
        "authority_effect": "none",
    }
    result["result_root"] = document_root("result", result)
    return result


def validate_repository(root: Path = ROOT) -> dict[str, Any]:
    manifest = load_toml(root, "vela.toml")
    validate_rooted("manifest", manifest)
    closed(
        manifest,
        {
            "schema", "manifest_root", "repository", "profiles", "bindings", "methods",
            "rights", "availability", "outputs", "authority_effect",
        },
        "Manifest",
    )
    repository = manifest["repository"]
    closed(repository, {"identity", "revision_policy", "revision"}, "repository")
    if repository != {
        "identity": EXPECTED_REPOSITORY,
        "revision_policy": "exact_git_commit",
        "revision": EXPECTED_NATIVE_REVISION,
    }:
        raise ValidationError("repository identity or revision drift")
    if not manifest["rights"] or not manifest["availability"]:
        raise ValidationError("rights or availability omitted")
    if not set(manifest["outputs"]).issubset(OUTPUTS):
        raise ValidationError("authority output")
    forbidden = [
        ".vela/repository.json", ".vela/origin.json", ".vela/authority", "records"
    ]
    if any((root / path).exists() for path in forbidden):
        raise ValidationError("authority state present in native repository")

    profiles: dict[str, dict[str, Any]] = {}
    for item in manifest["profiles"]:
        closed(item, {"id", "version", "path", "root"}, "Profile inventory")
        profile = load_toml(root, item["path"])
        validate_rooted("profile", profile)
        validate_profile(profile)
        if item != {
            "id": profile["profile_id"], "version": profile["version"],
            "path": item["path"], "root": profile["profile_root"],
        }:
            raise ValidationError("Profile inventory drift")
        profiles[profile["profile_id"]] = profile

    methods: dict[str, dict[str, Any]] = {}
    for item in manifest["methods"]:
        closed(item, {"id", "path", "root"}, "Method inventory")
        method = load_toml(root, item["path"])
        validate_rooted("method", method)
        validate_method(root, method, repository["revision"])
        if item["id"] != method["method_id"] or item["root"] != method["method_root"]:
            raise ValidationError("Method inventory drift")
        methods[method["method_id"]] = method

    bindings: dict[str, dict[str, Any]] = {}
    for item in manifest["bindings"]:
        closed(item, {"path", "root"}, "Binding inventory")
        binding = load_toml(root, item["path"])
        validate_rooted("binding", binding)
        validate_binding(binding, profiles, methods, repository["revision"])
        if item["root"] != binding["binding_root"]:
            raise ValidationError("Binding inventory drift")
        bindings[binding["binding_id"]] = binding

    validate_proof_index(root)
    example = validate_example(root, repository["revision"])
    return {"manifest": manifest, "profiles": profiles, "methods": methods, "bindings": bindings, "example": example}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--emit", type=Path)
    args = parser.parse_args()
    try:
        packet = validate_repository(args.root.resolve())
        if args.emit:
            result = build_result(
                packet["example"]["reference"],
                packet["methods"]["axiom-audit"]["method_root"],
            )
            validate_result(result, packet["example"]["reference"], packet["methods"]["axiom-audit"]["method_root"])
            args.emit.write_text(
                json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
                encoding="utf-8",
            )
        print("Vela native integration: ok (79 proofs; authority_effect none)")
        return 0
    except (KeyError, OSError, TypeError, ValidationError, tomllib.TOMLDecodeError) as error:
        print(f"Vela native integration: FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
