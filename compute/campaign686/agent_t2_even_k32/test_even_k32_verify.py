import even_k32_verify as verify


def test_square_root_polynomial_reconstruction():
    report = verify.audit()
    assert report["degrees"] == {"S": 32, "T": 16, "D": 14}
    assert report["scale"] == 1


def test_fixed_divisor():
    report = verify.audit()
    assert report["fixed_divisor"] == {
        "fixed_divisor": 3_221_225_472,
        "factorization": {"2": 30, "3": 1},
        "values_used": 17,
    }


def test_large_gap_archimedean_trap():
    cert = verify.audit()["archimedean"]
    assert cert["split_gap"] == 128
    assert cert["v0"] == 5603 and cert["w0"] == 5859
    assert cert["trap"] == 1_388_955_148_309_984
    assert cert["least_trap_degree"] == (0, 0)
    assert cert["candidate_count"] == 431_188
    assert cert["trap_terms"] == 153
    assert cert["negative_terms"] == 15


def test_finite_strip_is_exhaustive():
    strip = verify.audit()["finite_strip"]
    assert strip["gap_lo"] == 32 and strip["gap_hi"] == 127
    assert strip["checked"] == 14_352
    assert (strip["minimum_d"], strip["minimum_n"]) == (33, 729)


def test_prime_field_cover_closes_every_trapped_multiple():
    cover = verify.audit()["cover"]
    assert cover["primes"] == verify.COVER
    assert cover["survivor_counts"] == verify.COVER_COUNTS
    assert cover["survivor_counts"][-1] == 0
    assert cover["p17_classes"] == [0, 3, 6, 7, 10, 13, 14]
    assert cover["q_bound_exclusive"] == 25_365


def test_named_boundaries():
    boundary = verify.audit()["boundaries"]
    assert not boundary["d1_integral_telescope"]
    assert not boundary["d31_in_theorem_scope"]
    assert boundary["d32_in_finite_strip"]
    assert boundary["d128_in_large_gap"]
    assert boundary["excluded_fixed_primes"] == [2, 3]
