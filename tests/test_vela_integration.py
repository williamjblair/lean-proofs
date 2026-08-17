from __future__ import annotations

import copy
import importlib.util
import os
from pathlib import Path
import shutil
import tempfile
import unittest


SOURCE = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location(
    "check_vela_integration", SOURCE / "scripts" / "check_vela_integration.py"
)
assert SPEC and SPEC.loader
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)
VELA_BIN = os.environ.get("VELA_BIN", "vela")


def replace_once(path: Path, old: str, new: str) -> None:
    text = path.read_text(encoding="utf-8")
    if old not in text:
        raise AssertionError(f"fixture text not found in {path}: {old}")
    path.write_text(text.replace(old, new, 1), encoding="utf-8")


class IntegrationHostileTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory(prefix="lean-proofs-integration-test-")
        self.root = Path(self.temp.name) / "repo"
        self.root.mkdir()
        shutil.copytree(SOURCE / ".vela", self.root / ".vela")
        for raw in (
            "vela.toml",
            "proofs.yaml",
            "Audit.lean",
            "lean-toolchain",
            "lakefile.toml",
            "lake-manifest.json",
            "scripts/check_axioms.sh",
            "scripts/check_vela_integration.py",
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

    def validate(self) -> dict[str, object]:
        return CHECK.validate_repository(self.root, VELA_BIN)

    def assert_refused(self, pattern: str) -> None:
        with self.assertRaisesRegex(CHECK.ValidationError, pattern):
            self.validate()

    def test_clean_packet_passes_through_core_and_source_checks(self) -> None:
        packet = self.validate()
        self.assertTrue(packet["core"]["ok"])
        self.assertEqual(packet["core"]["schema"], "vela.cli.integration-check.v1")
        self.assertEqual(packet["core"]["authority_effect"], "none")
        self.assertEqual(len(packet["proofs"]), 79)

    def test_retained_proof_index_symlink_escape_refuses(self) -> None:
        outside = Path(self.temp.name) / "outside-proofs.yaml"
        proof_index = self.root / "proofs.yaml"
        proof_index.replace(outside)
        proof_index.symlink_to(outside)
        self.assert_refused("retained file must not be a symlink")

    def test_core_owns_shared_root_refusal(self) -> None:
        replace_once(
            self.root / "vela.toml",
            "sha256:b02b963f1064916052491737e810bc001b2363fba443c340c1ff5f1399548c42",
            "sha256:1234",
        )
        self.assert_refused("Vela Core integration check failed")

    def test_theorem_drift_refuses(self) -> None:
        replace_once(
            self.root / "proofs.yaml",
            "theorem: Erdos154.erdos_154_sumset",
            "theorem: Erdos154.not_the_selected_theorem",
        )
        self.assert_refused("theorem drift")

    def test_coherently_fake_local_reference_refuses(self) -> None:
        _, proofs = CHECK.parse_proofs(self.root / "proofs.yaml")
        reference = copy.deepcopy(
            CHECK.EXPECTED_LOCAL_REFERENCES[CHECK.SELECTED_THEOREM]
        )
        reference["native_identity"]["identifier"] = "Erdos154.nonexistent"
        reference["selector"]["value"] = "Erdos154.nonexistent"
        reference["content_fixity"]["digest"] = "sha256:" + "0" * 64
        with self.assertRaisesRegex(
            CHECK.ValidationError, "local Exact Reference drift"
        ):
            CHECK.validate_local_reference(self.root, reference, proofs)

    def test_coherently_fake_external_reference_refuses(self) -> None:
        reference = copy.deepcopy(CHECK.EXPECTED_EXTERNAL_REFERENCE)
        reference["native_identity"]["identifier"] = "FormalConjectures.nonexistent"
        reference["selector"]["value"] = "FormalConjectures.nonexistent"
        example = CHECK.load_toml(
            self.root, ".vela/examples/erdos-154-exact-reference.toml"
        )
        example["external_reference"] = reference
        _, proofs = CHECK.parse_proofs(self.root / "proofs.yaml")
        with self.assertRaisesRegex(
            CHECK.ValidationError, "external Formal Conjectures"
        ):
            original = CHECK.load_toml
            CHECK.load_toml = lambda root, relative: example
            try:
                CHECK.validate_example(self.root, proofs)
            finally:
                CHECK.load_toml = original

    def test_coherent_namespace_and_fixity_drift_refuses(self) -> None:
        source = self.root / CHECK.SELECTED_SOURCE
        replace_once(source, "namespace Erdos154", "namespace WrongNamespace")
        _, proofs = CHECK.parse_proofs(self.root / "proofs.yaml")
        reference = copy.deepcopy(
            CHECK.EXPECTED_LOCAL_REFERENCES[CHECK.SELECTED_THEOREM]
        )
        reference["content_fixity"]["digest"] = CHECK.sha256_file(source)
        reference["content_fixity"]["size"] = source.stat().st_size
        with self.assertRaisesRegex(
            CHECK.ValidationError, "local Exact Reference drift"
        ):
            CHECK.validate_local_reference(self.root, reference, proofs)

    def test_toolchain_drift_refuses(self) -> None:
        replace_once(
            self.root / "lean-toolchain",
            "leanprover/lean4:v4.29.1",
            "leanprover/lean4:v4.29.0",
        )
        self.assert_refused("toolchain")

    def test_source_closes_published_core_revision(self) -> None:
        method = self.root / ".vela/methods/integration-validator.toml"
        replace_once(
            method,
            CHECK.EXPECTED_CORE_REVISION,
            "0" * 40,
        )
        with self.assertRaisesRegex(
            CHECK.ValidationError, "integration validator Core input revision drift"
        ):
            CHECK.validate_method_semantics(self.root)

    def test_missing_audit_coverage_refuses(self) -> None:
        replace_once(
            self.root / "Audit.lean",
            "#print axioms Erdos154.erdos_154_sumset\n",
            "",
        )
        self.assert_refused("missing axiom audit coverage")

    def test_false_clean_source_refuses(self) -> None:
        source = self.root / CHECK.SELECTED_SOURCE
        source.write_text(
            source.read_text(encoding="utf-8")
            + "\ntheorem hostileFalseClean : True := by sorry\n",
            encoding="utf-8",
        )
        self.assert_refused("false axioms_clean claim")

    def test_private_unavailable_path_refuses(self) -> None:
        example = self.root / ".vela/examples/erdos-154-exact-reference.toml"
        replace_once(
            example,
            "The Erdős 730 original local attachment is outside this selected proof and is not converted to a result.",
            "/Users/private/.codex/attachments/evidence.txt",
        )
        self.assert_refused("private path")

    def test_direct_emission_is_outcome_free_and_unrooted(self) -> None:
        packet = self.validate()
        method_root = packet["methods"]["axiom-audit"]["method_root"]
        value = CHECK.build_verification_input(
            packet["example"]["reference"], method_root, packet["example"]["closure"]
        )
        CHECK.validate_verification_input(
            value,
            packet["example"]["reference"],
            method_root,
            packet["example"]["closure"],
        )
        for forbidden in (
            "result_root",
            "verification_input_root",
            "outcome",
            "observed_outcome",
            "evidence_availability",
            "accepted",
            "standing",
        ):
            self.assertNotIn(forbidden, value)


if __name__ == "__main__":
    unittest.main()
