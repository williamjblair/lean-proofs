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
            "sha256:ae23f6b3d4b074fe4bc663420746117044328c01f332d681b6c03e855d05e03a",
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

    def test_unavailable_evidence_cannot_become_pass_fail_or_zero(self) -> None:
        packet = CHECK.validate_repository(self.root)
        method_root = packet["methods"]["axiom-audit"]["method_root"]
        reference = packet["example"]["reference"]
        for outcome in ("pass", "fail", 0):
            with self.subTest(outcome=outcome):
                result = CHECK.build_result(reference, method_root)
                result["evidence_availability"] = "unavailable"
                result["outcome"] = outcome
                result["result_root"] = CHECK.document_root("result", result)
                with self.assertRaisesRegex(CHECK.ValidationError, "unavailable evidence"):
                    CHECK.validate_result(result, reference, method_root)

    def test_authority_state_refuses(self) -> None:
        authority = self.root / ".vela" / "repository.json"
        authority.write_text("{}\n", encoding="utf-8")
        self.assert_refused("authority state")


if __name__ == "__main__":
    unittest.main()
