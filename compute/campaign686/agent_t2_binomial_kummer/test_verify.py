from verify import (
    mandatory_fixture_report,
    verify_block_binomial_bridge,
    verify_chain_has_no_arithmetic_model,
    verify_exact_power_bracket,
    verify_infinite_family_dominance,
    verify_lucas_endpoint_restriction,
    verify_kummer_equation_restriction,
    verify_lucas_delta_and_unit_formula,
    verify_proper_component_examples_and_boundaries,
    verify_upper_window_linearization,
)


def test_block_binomial_bridge() -> None:
    verify_block_binomial_bridge()


def test_lucas_and_kummer_unit_formula() -> None:
    verify_lucas_delta_and_unit_formula()


def test_lucas_endpoint_restriction() -> None:
    verify_lucas_endpoint_restriction()


def test_kummer_equation_restriction() -> None:
    verify_kummer_equation_restriction()


def test_power_bracket() -> None:
    verify_exact_power_bracket()


def test_upper_window() -> None:
    verify_upper_window_linearization()


def test_infinite_family() -> None:
    verify_infinite_family_dominance()


def test_boundaries() -> None:
    verify_proper_component_examples_and_boundaries()


def test_post_lift_chain() -> None:
    verify_chain_has_no_arithmetic_model()


def test_fixtures() -> None:
    assert mandatory_fixture_report() == {
        "deep_984": [],
        "cluster_48502": [(277, 1, False)],
        "odd_telescopes_in_domain": False,
    }
