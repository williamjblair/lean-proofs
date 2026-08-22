import copy
import importlib.util
import sys
import unittest
from pathlib import Path


BUNDLE = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("verify_packets", BUNDLE / "verify_packets.py")
VERIFY = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = VERIFY
SPEC.loader.exec_module(VERIFY)


class PacketMutationTest(unittest.TestCase):
    def setUp(self):
        self.packets = VERIFY.load_packets(BUNDLE)

    def assert_rejected(self, mutate):
        packets = copy.deepcopy(self.packets)
        mutate(*packets)
        with self.assertRaises(VERIFY.PacketError):
            VERIFY.validate_bundle(BUNDLE, packets)

    def test_frozen_packets_pass(self):
        VERIFY.validate_bundle(BUNDLE, self.packets)

    def test_stale_commit_is_rejected(self):
        self.assert_rejected(lambda _a, b: b["roots"]["formal_conjectures_source"].__setitem__("commit", "0" * 40))

    def test_substituted_declaration_is_rejected(self):
        self.assert_rejected(lambda _a, b: b["roots"]["formal_conjectures_source"].__setitem__("declaration", "OeisA303656.a_25"))

    def test_forged_environment_is_rejected(self):
        self.assert_rejected(lambda _a, b: b["roots"]["lean_eval_target"].__setitem__("mathlib_revision", "f" * 40))

    def test_missing_assumption_is_rejected(self):
        self.assert_rejected(lambda _a, b: b["roots"]["formal_conjectures_source"].__setitem__("copied_dependencies", []))

    def test_drifted_witness_is_rejected(self):
        self.assert_rejected(lambda a, _b: a["witness"].__setitem__("sha256", "0" * 64))


if __name__ == "__main__":
    unittest.main()
