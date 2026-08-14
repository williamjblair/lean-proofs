from __future__ import annotations

import copy
import importlib.util
import json
from pathlib import Path
import re
import shutil
import tempfile
import tomllib
import unittest


SOURCE = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location(
    "check_vela_integration", SOURCE / "scripts" / "check_vela_integration.py"
)
assert SPEC and SPEC.loader
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)


def replace_once(path: Path, old: str, new: str) -> None:
    text = path.read_text(encoding="utf-8")
    if text.count(old) < 1:
        raise AssertionError(f"fixture text not found in {path}: {old}")
    path.write_text(text.replace(old, new, 1), encoding="utf-8")


class IntegrationHostileTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="lean-proofs-integration-test-")
        self.root = Path(self.temp.name)
        shutil.copytree(SOURCE / ".vela", self.root / ".vela")
        for raw in (
            "vela.toml", "proofs.yaml", "Audit.lean", "lean-toolchain",
            "lakefile.toml", "lake-manifest.json",
            "scripts/check_axioms.sh", "scripts/check_vela_integration.py",
            "ErdosProblems/Erdos154.lean",
        ):
            target = self.root / raw
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(SOURCE / raw, target)
        _, proofs = CHECK.parse_proofs(SOURCE / "proofs.yaml")
        for proof in proofs:
            raw = str(proof["file"])
            target = self.root / raw
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(SOURCE / raw, target)
            if raw.startswith("starfleet/"):
                project = Path(*Path(raw).parts[:2])
                for name in ("Audit.lean", "lean-toolchain"):
                    project_target = self.root / project / name
                    project_target.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copy2(SOURCE / project / name, project_target)

    def tearDown(self) -> None:
        self.temp.cleanup()

    def assert_refused(self, pattern: str) -> None:
        with self.assertRaisesRegex(CHECK.ValidationError, pattern):
            CHECK.validate_repository(self.root)

    def test_clean_packet_passes(self) -> None:
        packet = CHECK.validate_repository(self.root)
        self.assertEqual(packet["manifest"]["authority_effect"], "none")
        self.assertEqual(len(packet["profiles"]), 2)

    def test_wrong_or_short_manifest_root_refuses(self) -> None:
        replace_once(
            self.root / "vela.toml",
            "sha256:af09cd762db00af7acdc94a92aa2f63ec1d2b4cdeb6d70c11888ccab616c4b0d",
            "sha256:1234",
        )
        self.assert_refused("manifest root")

    def test_theorem_drift_refuses(self) -> None:
        replace_once(
            self.root / "proofs.yaml",
            "theorem: Erdos154.erdos_154_sumset",
            "theorem: Erdos154.not_the_selected_theorem",
        )
        self.assert_refused("theorem drift")

    def test_coherently_rerooted_fake_binding_reference_refuses(self) -> None:
        packet = CHECK.validate_repository(self.root)
        binding = copy.deepcopy(packet["bindings"]["formal-proof-index"])
        reference = binding["references"][0]
        reference["native_identity"]["identifier"] = "Erdos154.nonexistent"
        reference["selector"]["value"] = "Erdos154.nonexistent"
        reference["content_fixity"]["digest"] = "sha256:" + "0" * 64
        binding["binding_root"] = CHECK.document_root("binding", binding)
        CHECK.validate_rooted("binding", binding)
        _, proofs = CHECK.validate_proof_index(self.root)
        with self.assertRaisesRegex(CHECK.ValidationError, "exact proofs.yaml identity"):
            CHECK.validate_binding(
                self.root, binding, packet["profiles"], packet["methods"],
                CHECK.EXPECTED_NATIVE_REVISION, proofs,
            )

    def test_coherently_fake_external_reference_refuses(self) -> None:
        reference = copy.deepcopy(CHECK.EXPECTED_EXTERNAL_REFERENCE)
        reference["native_identity"]["identifier"] = "FormalConjectures.nonexistent"
        reference["selector"]["value"] = "FormalConjectures.nonexistent"
        reference["content_fixity"]["digest"] = "sha256:" + "0" * 64
        CHECK.validate_reference(
            reference, "96eeecf40bc06ddc8bae6d106f461d4fd774858a"
        )
        with self.assertRaisesRegex(CHECK.ValidationError, "external Formal Conjectures"):
            CHECK.validate_external_reference(reference)

    def test_coherent_namespace_and_fixity_drift_refuses(self) -> None:
        packet = CHECK.validate_repository(self.root)
        binding = copy.deepcopy(packet["bindings"]["formal-proof-index"])
        source = self.root / "ErdosProblems" / "Erdos154Sumset.lean"
        replace_once(source, "namespace Erdos154", "namespace WrongNamespace")
        reference = binding["references"][0]
        reference["content_fixity"]["digest"] = CHECK.sha256_file(source)
        reference["content_fixity"]["size"] = source.stat().st_size
        binding["binding_root"] = CHECK.document_root("binding", binding)
        CHECK.validate_rooted("binding", binding)
        _, proofs = CHECK.parse_proofs(self.root / "proofs.yaml")
        with self.assertRaisesRegex(CHECK.ValidationError, "declaration drift"):
            CHECK.validate_binding(
                self.root, binding, packet["profiles"], packet["methods"],
                CHECK.EXPECTED_NATIVE_REVISION, proofs,
            )

    def test_coherently_rerooted_locator_drift_refuses(self) -> None:
        packet = CHECK.validate_repository(self.root)
        binding = copy.deepcopy(packet["bindings"]["formal-proof-index"])
        reference = binding["references"][0]
        reference["locator"]["uri"] = (
            "https://example.invalid/wrong-owner/wrong-repo/blob/"
            f"{CHECK.EXPECTED_NATIVE_REVISION}/ErdosProblems/Erdos154Sumset.lean"
        )
        binding["binding_root"] = CHECK.document_root("binding", binding)
        CHECK.validate_rooted("binding", binding)
        _, proofs = CHECK.validate_proof_index(self.root)
        with self.assertRaisesRegex(CHECK.ValidationError, "locator does not resolve"):
            CHECK.validate_binding(
                self.root, binding, packet["profiles"], packet["methods"],
                CHECK.EXPECTED_NATIVE_REVISION, proofs,
            )

    def test_toolchain_drift_refuses(self) -> None:
        replace_once(
            self.root / "lean-toolchain",
            "leanprover/lean4:v4.29.1",
            "leanprover/lean4:v4.29.0",
        )
        self.assert_refused("header drift")

    def test_missing_audit_coverage_refuses(self) -> None:
        replace_once(
            self.root / "Audit.lean",
            "#print axioms Erdos154.erdos_154_sumset\n",
            "",
        )
        self.assert_refused("missing axiom audit coverage")

    def test_false_clean_source_refuses(self) -> None:
        source = self.root / "ErdosProblems" / "Erdos154Sumset.lean"
        source.write_text(
            source.read_text(encoding="utf-8")
            + "\ntheorem hostileFalseClean : True := by sorry\n",
            encoding="utf-8",
        )
        self.assert_refused("false axioms_clean claim")

    def test_private_unavailable_path_refuses(self) -> None:
        example = self.root / ".vela" / "examples" / "erdos-154-exact-reference.toml"
        replace_once(
            example,
            "The Erdős 730 original local attachment is outside this selected proof and is not converted to a result.",
            "/Users/private/.codex/attachments/evidence.txt",
        )
        self.assert_refused("private path")

    def test_direct_emission_cannot_claim_unperformed_result(self) -> None:
        packet = CHECK.validate_repository(self.root)
        method_root = packet["methods"]["axiom-audit"]["method_root"]
        reference = packet["example"]["reference"]
        artifacts = packet["example"]["closure"]
        result = CHECK.build_verification_input(reference, method_root, artifacts)
        self.assertNotIn("observed_outcome", result)
        self.assertNotIn("evidence_availability", result)
        for field, value in (("observed_outcome", "pass"), ("evidence_availability", "available")):
            with self.subTest(field=field):
                mutated = copy.deepcopy(result)
                mutated[field] = value
                with self.assertRaisesRegex(CHECK.ValidationError, "unknown"):
                    CHECK.validate_verification_input(
                        mutated, reference, method_root, artifacts
                    )

    def test_portable_output_is_source_owned_and_unrooted(self) -> None:
        packet = CHECK.validate_repository(self.root)
        output = CHECK.build_verification_input(
            packet["example"]["reference"],
            packet["methods"]["axiom-audit"]["method_root"],
            packet["example"]["closure"],
        )
        CHECK.validate_verification_input(
            output, packet["example"]["reference"],
            packet["methods"]["axiom-audit"]["method_root"],
            packet["example"]["closure"],
        )
        self.assertEqual(output["schema"], "lean-proofs.verification-input.v0.1")
        self.assertNotIn("result_root", output)
        self.assertNotIn("verification_input_root", output)

    def test_authority_state_refuses(self) -> None:
        authority = self.root / ".vela" / "repository.json"
        authority.write_text("{}\n", encoding="utf-8")
        self.assert_refused("authority state")


if __name__ == "__main__":
    unittest.main()
