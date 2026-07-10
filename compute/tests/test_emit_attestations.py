from __future__ import annotations

import pytest

from scripts.emit_attestations import axiom_footprint_is_clean, parse_axiom_report


def test_parse_axiom_report_handles_single_line_wrapped_and_empty() -> None:
    report = """\
'A.short' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos686.Erdos686Variant.a_very_long_theorem_name' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'A.kernel' does not depend on any axioms
"""
    assert parse_axiom_report(report) == {
        "A.short": ["propext", "Classical.choice", "Quot.sound"],
        "Erdos686.Erdos686Variant.a_very_long_theorem_name": [
            "propext",
            "Classical.choice",
            "Quot.sound",
        ],
        "A.kernel": [],
    }


def test_parse_axiom_report_rejects_unterminated_list() -> None:
    with pytest.raises(ValueError, match="unterminated axiom report"):
        parse_axiom_report("'A.bad' depends on axioms: [propext,")


def test_axiom_gate_accepts_subsets_and_rejects_extra_axioms() -> None:
    assert axiom_footprint_is_clean([])
    assert axiom_footprint_is_clean(["propext"])
    assert axiom_footprint_is_clean(["propext", "Classical.choice", "Quot.sound"])
    assert not axiom_footprint_is_clean(["propext", "sorryAx"])
