import json
import subprocess
import sys

from compute.scan import scan_full, scan_full_short_circuit, scan_rows


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
