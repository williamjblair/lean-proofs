from compute.campaign686.agent_t2_even_tail.even_tail_verify import (
    certificate,
    ratio_power_bound_holds,
)


def test_exact_polynomial_certificates_through_k_40() -> None:
    for r in range(2, 21):
        cert = certificate(r)
        assert cert.deficit_degree < r
        assert cert.threshold > 10 * cert.deficit_norm


def test_known_deficit_degrees_and_denominators() -> None:
    expected = {
        8: (1, 6),      # k=16
        9: (128, 8),    # k=18
        10: (1, 8),     # k=20
        12: (1, 10),    # k=24
    }
    for r, (denominator, degree) in expected.items():
        cert = certificate(r)
        assert cert.denominator == denominator
        assert cert.deficit_degree == degree


def test_ratio_power_bound_exactly() -> None:
    for r in range(2, 100):
        for v in (r, 10 * r + 1, 10_000 + r):
            # Largest integer w satisfying (r-1)w < rv.
            w = (r * v - 1) // (r - 1)
            for q in range(r):
                assert ratio_power_bound_holds(r, v, w, q)


def test_centered_ratio_from_equation_window_boundary() -> None:
    # The elementary equation window gives
    # v >= 2r(d-1)+2 and w=v+2d.  Check the strict rational implication at
    # the smallest admissible d and at displaced exact boundaries.
    for r in range(2, 100):
        for d in (2 * r, 2 * r + 1, 10_000 + r):
            v = 2 * r * (d - 1) + 2
            w = v + 2 * d
            assert (r - 1) * w < r * v
            for q in (0, r // 2, r - 1):
                assert ratio_power_bound_holds(r, v, w, q)
