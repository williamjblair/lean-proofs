from compute.erdos699 import (
    binom_mod_prime_nonzero_by_lucas,
    counterexample_candidate,
    criterion_obstruction_primes,
    dominated,
    has_obstruction_prime,
    primes_upto,
)


def test_primes_below_i_are_free_in_counterexample_criterion() -> None:
    n, i, j = 10, 4, 5
    assert 2 < i and 3 < i
    assert dominated(i, n, 2) is False
    assert dominated(j, n, 3) is False
    obstructions = criterion_obstruction_primes(n, i, j)
    assert 2 not in obstructions
    assert 3 not in obstructions
    assert 7 in obstructions
    assert counterexample_candidate(n, i, j) is False


def test_i_three_does_not_constrain_two() -> None:
    n, i, j = 8, 3, 4
    assert 2 < i
    assert dominated(i, n, 2) is False
    obstructions = criterion_obstruction_primes(n, i, j)
    assert 2 not in obstructions
    assert 7 in obstructions
    assert counterexample_candidate(n, i, j) is False


def test_gpt_pro_pure_c2_survivor_fails_row_three_digit_constraints() -> None:
    n = 54_734_052
    i = 3
    j = 8_748_251
    row_n_primes = [541, 8_431]

    assert 1 <= i < j <= n // 2
    assert n == 2**2 * 3 * 541 * 8_431
    for p in row_n_primes:
        assert i <= p
        assert n % p == 0
        assert j % p != 0
        assert dominated(i, n, p) is False
        assert dominated(j, n, p) is False

    assert criterion_obstruction_primes(n, i, j, primes=row_n_primes) == row_n_primes
    assert counterexample_candidate(n, i, j, primes=row_n_primes) is False


def test_normalized_positive_survivor_fails_original_row_three_digit_constraints() -> None:
    F = 3
    X = 432_184_014_644
    u = 186_954_166_997
    n = F * X
    i = 3
    j = F * u
    p = 5

    assert n == 1_296_552_043_932
    assert j == 560_862_500_991
    assert 1 <= i < j <= n // 2
    assert dominated(i, n, p) is False
    assert dominated(j, n, p) is False
    assert criterion_obstruction_primes(n, i, j, primes=[p]) == [p]
    assert counterexample_candidate(n, i, j, primes=[p]) is False


def test_lucas_digit_predicate_matches_binomial_mod_prime_for_small_values() -> None:
    for p in primes_upto(13):
        for n in range(0, 60):
            for k in range(0, n + 1):
                assert binom_mod_prime_nonzero_by_lucas(n, k, p) == dominated(k, n, p)


def test_short_circuit_obstruction_matches_obstruction_list() -> None:
    for n in range(1, 90):
        primes = primes_upto(n)
        for i in range(1, n // 2):
            for j in range(i + 1, n // 2 + 1):
                obstructions = criterion_obstruction_primes(n, i, j, primes=primes)
                assert has_obstruction_prime(n, i, j, primes=primes) == bool(
                    obstructions
                )
                assert counterexample_candidate(n, i, j, primes=primes) == (
                    not obstructions
                )
