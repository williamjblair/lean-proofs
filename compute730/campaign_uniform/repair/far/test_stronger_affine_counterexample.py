from fractions import Fraction
from math import gcd

from compute730.campaign_uniform.repair.far.stronger_affine_counterexample import (
    advertised_rhs_upper,
    explicit_p5_certificate,
    progression_hit_lower_bound,
    q_branch_linear_coefficient,
    separated_far_exact,
)
from compute730.campaign_uniform.test_uniformity import (
    BRANCHES,
    expanded_value,
    phi,
    root_data,
)


def test_progression_identity_exactly_on_small_moduli() -> None:
    """The nonlinear difference vanishes on every ``p^s`` progression."""

    branch = BRANCHES["Q"]
    b = int(branch["b"])
    for p, r, s, k0 in ((5, 4, 2, 17), (7, 3, 2, 31), (11, 3, 1, 53)):
        a = 2 * r - s
        modulus = p ** (2 * r)
        x0, c0 = root_data(branch, p, a)
        assert int(branch["lam"]) * x0 + int(branch["mu"]) == p**a * c0

        def polynomial(k: int) -> int:
            return expanded_value(branch, p, a, c0, k)

        for j in range(-9, 10):
            t = p**s * j
            assert (polynomial(k0 + t) - polynomial(k0) - b * t) % modulus == 0

        # The expanded map is the exact Q-branch Phi map at the lifted root.
        for k in range(-5, 6):
            c = c0 + int(branch["lam"]) * k
            assert polynomial(k) == phi(branch, p**a, c)


def test_output_digit_one_is_the_exact_valuation_guard() -> None:
    branch = BRANCHES["Q"]
    for p, r, s in ((5, 4, 2), (7, 3, 2), (11, 3, 1)):
        a = 2 * r - s
        _, c0 = root_data(branch, p, a)
        v = phi(branch, p**a, c0)
        b = int(branch["b"])
        k = ((1 - v) * pow(b, -1, p)) % p
        assert expanded_value(branch, p, a, c0, k) % p == 1
        assert (c0 + int(branch["lam"]) * k) % p != 0


def test_pigeonhole_lower_bound_is_the_stronger_scale() -> None:
    b = q_branch_linear_coefficient()
    for p, r, s in ((5, 21, 8), (7, 18, 7), (11, 16, 6)):
        H = (p + 1) // 2
        lower = progression_hit_lower_bound(p, r, s, b)
        assert lower * b >= H ** (r - s)
        assert (lower - 1) * b < H ** (r - s)


def test_exact_p5_witness_refutes_zero_error_far_inequality() -> None:
    certificate = explicit_p5_certificate()
    assert certificate["branch_admissible"]
    assert certificate["root_exact"]
    assert certificate["root_in_range"]
    assert certificate["output_digit_one_realized"]
    assert certificate["output_digit_one_forces_exact_valuation"]
    assert certificate["progression_modulus_identity"]
    assert gcd(q_branch_linear_coefficient(), 5) == 1
    assert certificate["separated"]
    assert certificate["compact_separation"]
    assert certificate["compact_divergence"]
    assert certificate["rho_fits_modulus"]
    assert certificate["hit_span_lt_p_to_r"]
    assert certificate["critical_length_covers_p_to_r"]
    assert certificate["log_interval_ordered"]
    assert certificate["counterexample"]
    assert certificate["cleared_margin"] > 0
    assert Fraction(certificate["hit_lower_bound"], 1) > advertised_rhs_upper(5, 432)


def test_split_threshold_really_exceeds_kappa_plus_one_twelfth() -> None:
    # s/r=11/27 is on the far side of kappa_5+1/12, while
    # p^27>H^(27+11) certifies it is below kappa_5/(1-kappa_5).
    assert separated_far_exact(5, 432, 176)
    assert 5**27 > 3**38
