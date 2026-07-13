from quadratic_tail_bridge_verify import audit


REPORT = audit()


def test_quadratic_boundary_and_first_correction() -> None:
    assert REPORT["quadratic_boundary"] == {
        "last_gap": 64,
        "first_complement_gap": 65,
        "18_last_gap": 1152,
        "k_squared": 1156,
        "18_first_complement_gap": 1170,
    }
    assert REPORT["first_correction"] == {
        "odd_square_sum": 6545,
        "q_r_minus_1": 0,
        "q_r_minus_2": "-6545/2",
        "structural_threshold_lower_bound": 6545,
    }


def test_canonical_k34_certificate_numbers() -> None:
    assert REPORT["canonical_certificate"] == {
        "minimal_denominator": 32768,
        "deficit_degree": 16,
        "leading_deficit_abs": 188162318421570695167361039564800,
        "A": 2524860515553128032111517,
        "E": 6375143223540100100577353665680166719158383844425,
        "F": 6375143223540099912415035244109471551797344279625,
        "minimal_threshold": 63751432235401001005773536656801667191583838444251,
        "odd_center_fixed_divisor": 255,
    }


def test_sharp_ratio_and_rescaling_obstruction() -> None:
    assert REPORT["sharp_ratio_boundary"] == {
        "d": 65,
        "least_n": 1453,
        "least_center": 2941,
        "left": 2692759030,
        "predecessor_right": 2691938304,
        "right": 2693792256,
    }
    assert REPORT["equation_power_window"] == {
        "d": 65,
        "root_lower_numerator": 1041616,
        "root_upper_numerator": 1041617,
        "root_denominator": 1000000,
        "least_n": 1528,
        "greatest_n": 1560,
        "least_center": 3091,
        "greatest_center": 3155,
    }
    assert REPORT["parity_rescaling_obstruction"] == {
        "optimistic_leading_only_center": 225186598141623936273745117,
        "full_norm_center": 7629565936566640936850578356790181141762389,
    }


def test_general_lcm_exponent_ceiling() -> None:
    assert REPORT["ideal_general_lcm_ceiling"] == {
        "last_gap_excluded_by_size_sandwich": 1204,
        "first_gap_not_reached": 1205,
    }
