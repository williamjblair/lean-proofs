from __future__ import annotations

from functools import lru_cache

from k22_sieve_probe_verify import (
    ROOT_FIXTURES,
    audit,
    compressed_branch_lengths,
    eval_poly,
    local_allowed_t_residues,
    make_row_data,
    minimal_coefficientwise_bound,
    payload_sha256,
    quadratic_strip_certificate,
    root_fixture_certificate,
    trap_coefficients,
)


@lru_cache(maxsize=1)
def audited_payload():
    return audit()


def test_row_polynomial_part_and_fixed_divisor() -> None:
    row = make_row_data()
    assert row.scale == 256
    assert max(row.d_poly) == 10
    assert row.odd_fixed_divisor == 33
    for value in range(-31, 32, 2):
        assert eval_poly(row.t_poly, value) % 33 == 0


def test_quadratic_strip_exact_boundary() -> None:
    cert = quadratic_strip_certificate()
    assert cert["closed_gaps"] == [22, 23, 24, 25, 26]
    assert cert["first_live_gap"] == 27
    assert cert["boundary"] == [468, 484, 486]


def test_unrestricted_local_masks_have_integral_root_fixtures() -> None:
    fixtures = root_fixture_certificate()
    assert [row["t"] for row in fixtures] == [fixture[0] for fixture in ROOT_FIXTURES]
    # Exact integer witnesses survive every modulus, including prime powers;
    # these samples exercise the reduction directly.
    for modulus in (2, 3, 5, 9, 11, 23, 23**2, 121, 997, 1024):
        for fixture in fixtures:
            assert fixture["m"] % modulus == (-33 * fixture["t"]) % modulus


def test_mod_23_mask_and_parity_compression() -> None:
    assert local_allowed_t_residues(23) == frozenset({2, 6, 17, 21})
    lengths = compressed_branch_lengths(3_795_146_531)
    assert lengths == {17: 82_503_186, 21: 82_503_186, 25: 82_503_185, 29: 82_503_185}
    assert sum(lengths.values()) == 330_012_742


def test_coefficientwise_bounds_are_strict_and_minimal() -> None:
    assert minimal_coefficientwise_bound(27) == 1_161_715_983_142
    assert minimal_coefficientwise_bound(250) == 125_239_835_548
    for gap, bound in ((27, 1_161_715_983_142), (250, 125_239_835_548)):
        assert min(trap_coefficients(gap, bound).values()) > 0
        assert min(trap_coefficients(gap, bound - 1).values()) <= 0


def test_finite_strip_and_bounded_sieve_reproduce() -> None:
    payload = audited_payload()
    assert payload["finite_strip"]["pair_count"] == 16_859
    assert payload["finite_strip"]["minimum_at"] == [28, 419]
    assert payload["bounded_local_sieve"]["initial_count"] == 330_012_742
    assert payload["bounded_local_sieve"]["kill_prime"] == 953
    assert payload["bounded_local_sieve"]["tail_counts"][-1] == [953, 0]


def test_payload_digest_is_deterministic() -> None:
    digest = payload_sha256(audited_payload())
    assert len(digest) == 64
    assert digest == "322a6e04727cb85cf097938fed19f57698fb10bbaf9a1ae4b7813c84114e3ed4"
