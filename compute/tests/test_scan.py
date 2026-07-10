import json
import subprocess
import sys

from compute.scan import (
    power_two_family_values,
    scan_full,
    scan_full_short_circuit,
    scan_n_values,
    scan_power_two_family,
    scan_rows,
)


def test_scan_full_small_bound_has_no_candidates() -> None:
    result = scan_full(40)
    assert result["mode"] == "full"
    assert result["limit"] == 40
    assert result["checked_triples"] == sum(
        max(0, n // 2 - i) for n in range(1, 41) for i in range(1, n // 2)
    )
    assert result["candidates"] == []


def test_scan_full_can_restrict_i_values() -> None:
    result = scan_full(60, i_values=[3, 4])
    assert result["mode"] == "full"
    assert result["i_values"] == [3, 4]
    assert result["candidates"] == []


def test_scan_full_uses_bitset_algorithm_metadata() -> None:
    result = scan_full(20)
    assert result["algorithm"] == "bitset_domination"


def test_bitset_scan_matches_short_circuit_scan() -> None:
    bitset = scan_full(75)
    reference = scan_full_short_circuit(75)
    assert bitset["checked_triples"] == reference["checked_triples"]
    assert bitset["candidates"] == reference["candidates"]


def test_bitset_scan_matches_short_circuit_scan_with_i_filter() -> None:
    bitset = scan_full(120, i_values=[3, 4, 5])
    reference = scan_full_short_circuit(120, i_values=[3, 4, 5])
    assert bitset["checked_triples"] == reference["checked_triples"]
    assert bitset["candidates"] == reference["candidates"]


def test_row_scan_matches_full_scan_for_single_row() -> None:
    rows = scan_rows(90, [3])
    full = scan_full(90, i_values=[3])
    assert rows["mode"] == "rows"
    assert rows["algorithm"] == "row_obstruction_primes"
    assert rows["checked_triples"] == full["checked_triples"]
    assert rows["candidates"] == full["candidates"]


def test_row_scan_matches_full_scan_for_multiple_rows() -> None:
    rows = scan_rows(110, [3, 4, 5])
    full = scan_full(110, i_values=[3, 4, 5])
    assert rows["checked_triples"] == full["checked_triples"]
    assert rows["candidates"] == full["candidates"]


def test_scan_cli_emits_json() -> None:
    completed = subprocess.run(
        [sys.executable, "-m", "compute.scan", "--limit", "35"],
        check=True,
        text=True,
        capture_output=True,
    )
    payload = json.loads(completed.stdout)
    assert payload["mode"] == "full"
    assert payload["limit"] == 35
    assert payload["candidates"] == []


def test_scan_cli_can_use_row_strategy() -> None:
    completed = subprocess.run(
        [sys.executable, "-m", "compute.scan", "--limit", "80", "--i", "3", "--row-scan"],
        check=True,
        text=True,
        capture_output=True,
    )
    payload = json.loads(completed.stdout)
    assert payload["mode"] == "rows"
    assert payload["algorithm"] == "row_obstruction_primes"
    assert payload["i_values"] == [3]
    assert payload["candidates"] == []


def test_sparse_n_value_scan_matches_full_scan_on_small_values() -> None:
    n_values = [12, 18, 24, 30]
    sparse = scan_n_values(n_values, [3, 4])
    full = scan_full(max(n_values), i_values=[3, 4])
    n_value_set = set(n_values)
    expected_candidates = [
        candidate for candidate in full["candidates"] if candidate["n"] in n_value_set
    ]
    expected_checked = sum(
        max(0, n // 2 - i) for n in n_values for i in [3, 4] if i < n // 2
    )
    assert sparse["mode"] == "n_values"
    assert sparse["algorithm"] == "factor_crt_row_obstruction"
    assert sparse["checked_triples"] == expected_checked
    assert sparse["candidates"] == expected_candidates


def test_power_two_family_values_are_bounded_and_sorted() -> None:
    values = power_two_family_values(8, [1, 3, 5])
    assert values == sorted(set(values))
    assert all(n <= 2**8 for n in values)
    assert {1, 3, 5, 8, 24, 40, 128}.issubset(set(values))


def test_power_two_family_scan_matches_sparse_scan_on_small_family() -> None:
    family = scan_power_two_family(8, [1, 3, 5], [3, 4])
    sparse = scan_n_values(power_two_family_values(8, [1, 3, 5]), [3, 4])
    assert family["mode"] == "power_two_family"
    assert family["algorithm"] == "factor_crt_row_obstruction"
    assert family["family_limit"] == 2**8
    assert family["checked_triples"] == sparse["checked_triples"]
    assert family["candidates"] == sparse["candidates"]


def test_scan_cli_can_use_power_two_family_strategy() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "compute.scan",
            "--power-two-family",
            "--family-max-exponent",
            "8",
            "--multiplier",
            "1",
            "--multiplier",
            "3",
            "--i",
            "3",
        ],
        check=True,
        text=True,
        capture_output=True,
    )
    payload = json.loads(completed.stdout)
    assert payload["mode"] == "power_two_family"
    assert payload["family_limit"] == 2**8
    assert payload["multipliers"] == [1, 3]
    assert payload["i_values"] == [3]
    assert payload["candidates"] == []
