from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest


SOURCE = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location(
    "emit_attestations", SOURCE / "scripts" / "emit_attestations.py"
)
assert SPEC and SPEC.loader
EMIT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(EMIT)


class AttestationAttributionTests(unittest.TestCase):
    def test_metadata_names_the_actual_local_projection_actor(self) -> None:
        metadata = EMIT.attestation_metadata(
            {
                "repo": "williamjblair/lean-proofs",
                "toolchain": "leanprover/lean4:v4.33.0",
                "mathlib": "db584cd6d46c92f209a44c0f1c829460d327499d",
            },
            "audit output\n",
        )

        self.assertEqual(metadata["schema"], "lean-proofs.attestations.v0.2")
        self.assertEqual(metadata["verification_method"], "lean_kernel")
        self.assertEqual(metadata["evidence_generator"], "local:openai-codex")

    def test_metadata_does_not_claim_a_ci_verifier_actor(self) -> None:
        metadata = EMIT.attestation_metadata({}, "")

        self.assertNotIn("verifier_actor", metadata)
        self.assertNotIn("verifier_method", metadata)
        self.assertNotIn("ci:github-actions", metadata.values())


if __name__ == "__main__":
    unittest.main()
