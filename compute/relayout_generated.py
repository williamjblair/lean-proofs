#!/usr/bin/env python3
"""Move freshly generated flat Lean files into the per-problem tree.

The table/shard generators under ``compute/`` still write flat module names
(``Erdos686EvenK22TableP101.lean``) straight into ``ErdosProblems/``.  Run this
afterwards to move each one to its canonical nested path and rewrite the import
lines it emitted, so a regenerate reproduces the committed layout:

    python3 compute/campaign686/agent_t2_even_k32/generate_lean.py
    python3 compute/relayout_generated.py

Idempotent.  Only touches flat ``ErdosProblems/Erdos<N><rest>.lean`` files; the
bare problem roots (``Erdos686.lean`` and friends) and anything already nested
are left alone.
"""
from __future__ import annotations

import re
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
ROOT = REPO / "ErdosProblems"
BARE_ROOTS = {"Erdos154", "Erdos617", "Erdos686", "Erdos699", "Erdos727"}
EVEN_K = ("16", "18", "20", "22", "24", "28", "32")


def _evenk(rest: str) -> list[str]:
    if rest == "":
        return ["EvenK", "Base"]
    for k in sorted(EVEN_K, key=len, reverse=True):
        if rest.startswith(k):
            tail = rest[len(k):]
            if tail == "" or tail[0].isdigit():
                return ["EvenK", f"K{rest}"]
            for bucket in ("Table", "Packed"):
                if tail.startswith(bucket):
                    return ["EvenK", f"K{k}", bucket, tail]
            return ["EvenK", f"K{k}", tail]
    return ["EvenK", rest]


def _k5(rest: str) -> list[str]:
    m = re.match(r"^(P\d+)(.*)$", rest)
    return ["K5", m.group(1), rest] if m else ["K5", rest]


def components(num: str, rest: str) -> list[str] | None:
    """Directory+file components under ErdosProblems/ErdosN.  None => bare root."""
    if rest == "":
        return None
    if num == "686":
        if rest.startswith("EvenK"):
            return _evenk(rest[len("EvenK"):])
        if rest.startswith("K5"):
            return _k5(rest[len("K5"):])
        return ["Core", rest]
    if num == "730":
        if rest.endswith("Audit") and rest != "Audit":
            return ["Audit", rest[: -len("Audit")]]
        return [rest]
    return [rest]


def new_module(stem: str) -> str | None:
    m = re.match(r"^Erdos(\d+)(.*)$", stem)
    if not m:
        return None
    comps = components(m.group(1), m.group(2))
    if comps is None:
        return None
    return ".".join(["ErdosProblems", f"Erdos{m.group(1)}"] + comps)


def main() -> None:
    flat = [p for p in ROOT.glob("Erdos*.lean") if p.stem not in BARE_ROOTS]
    if not flat:
        print("no flat generated files to relayout")
        return

    imp = re.compile(r"^(\s*import\s+)(\S+)(.*)$")

    def remap_import(target: str) -> str | None:
        """Rewrite a flat generated import to its nested module, else None."""
        if not target.startswith("ErdosProblems."):
            return None
        stem = target[len("ErdosProblems."):]
        if "." in stem:            # already nested
            return None
        nm = new_module(stem)      # None for bare roots — leave those alone
        return nm if nm and nm != target else None

    moved = 0
    for p in flat:
        mod = new_module(p.stem)
        if mod is None:
            continue
        dest = REPO / (mod.replace(".", "/") + ".lean")
        dest.parent.mkdir(parents=True, exist_ok=True)
        lines = p.read_text().splitlines(keepends=True)
        for i, line in enumerate(lines):
            m = imp.match(line)
            if not m:
                continue
            nm = remap_import(m.group(2))
            if nm:
                lines[i] = f"{m.group(1)}{nm}{m.group(3)}" + (
                    "\n" if line.endswith("\n") else "")
        dest.write_text("".join(lines))
        if dest != p:
            p.unlink()
        moved += 1
    print(f"relaid out {moved} generated file(s); run scripts/gen_aggregates.py next")


if __name__ == "__main__":
    main()
