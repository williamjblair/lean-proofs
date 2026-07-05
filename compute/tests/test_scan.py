import json
import subprocess
import sys

from compute.scan import scan_full


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


def test_scan_full_uses_short_circuit_algorithm_metadata() -> None:
    result = scan_full(20)
    assert result["algorithm"] == "short_circuit_obstruction"


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
