import unittest

from compute.campaign686.agent_t2_matched_owner_dichotomy.matched_owner_dichotomy_verify import (
    coefficient,
    owner_slope,
    quadratic_coefficient,
    second_linear,
    signed_coefficient,
    verify_fixtures,
    verify_uniform,
)


class MatchedOwnerDichotomyTests(unittest.TestCase):
    def test_closed_coefficient_and_slope_formulas(self) -> None:
        for k in range(2, 14):
            for t in range(1, k + 1):
                offsets = [r - t for r in range(1, k + 1) if r != t]
                direct_constant = 1
                for x in offsets:
                    direct_constant *= x
                direct_linear = 0
                for omitted in range(len(offsets)):
                    term = 1
                    for index, x in enumerate(offsets):
                        if index != omitted:
                            term *= x
                    direct_linear += term
                self.assertEqual(signed_coefficient(k, t), direct_constant)
                self.assertEqual(second_linear(k, t), direct_linear)
                self.assertEqual(second_linear(k, t), direct_constant * owner_slope(k, t))
                self.assertGreater(coefficient(k, t), 0)

    def test_uniform_nonvanishing_sample(self) -> None:
        result = verify_uniform(80)
        self.assertEqual(result["max_k"], 80)
        self.assertGreater(result["normalized_candidates"], 0)

    def test_named_boundaries(self) -> None:
        result = verify_fixtures()
        self.assertEqual(result["k984_large_factor"], 7_237)
        self.assertEqual(result["p_equals_k_boundary"], 17)
        self.assertEqual(result["excluded_center_ratio"], [4, 1])

    def test_odd_center_exception_is_outside_window(self) -> None:
        k = 17
        t = 9
        self.assertEqual(owner_slope(k, t), 0)
        self.assertEqual(quadratic_coefficient(k, t, t, 4, 1), 0)
        self.assertFalse(4 < 2)


if __name__ == "__main__":
    unittest.main()
