#!/usr/bin/env python3
"""Mechanical half of the faithfulness gate.

Compares the definitions a hosted Star Fleet project relies on against the
definitions in the corresponding Formal Conjectures file, so a human reading the
two statements has the definitional diff in front of them rather than having to
reconstruct it.

This does not decide faithfulness. It reports which supporting definitions exist
on both sides and whether their bodies agree once whitespace, line wrapping and
docstrings are normalised away. Deciding whether the statement is the problem is
still a read.

Usage:
    faithfulness_diff.py <problem> --fc <path to formal-conjectures checkout>

Exit status is 0 whatever it finds; this is a reporting tool, not a gate.
"""

import argparse
import pathlib
import re
import sys

DECL = re.compile(
    r"^(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(def|abbrev|structure|theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_.'!]*)"
)
SKIP_LINE = re.compile(r"^\s*(--|/-)")


def declarations(path: pathlib.Path) -> dict[str, str]:
    """Map declaration name -> normalised body text."""
    out: dict[str, str] = {}
    name: str | None = None
    buf: list[str] = []
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        m = DECL.match(line)
        if m:
            if name:
                out.setdefault(name, normalise(buf))
            name, buf = m.group(2), [line]
        elif name is not None:
            if line and not line[0].isspace() and not SKIP_LINE.match(line):
                out.setdefault(name, normalise(buf))
                name, buf = None, []
            else:
                buf.append(line)
    if name:
        out.setdefault(name, normalise(buf))
    return out


def normalise(lines: list[str]) -> str:
    kept = [l for l in lines if not SKIP_LINE.match(l)]
    return re.sub(r"\s+", " ", " ".join(kept)).strip()


def collect(root: pathlib.Path) -> dict[str, str]:
    merged: dict[str, str] = {}
    for f in sorted(root.rglob("*.lean")):
        for k, v in declarations(f).items():
            merged.setdefault(k, v)
    return merged


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("problem")
    ap.add_argument("--fc", required=True, help="path to a formal-conjectures checkout")
    args = ap.parse_args()

    here = pathlib.Path(__file__).resolve().parent.parent
    hosted_root = here / f"erdos-{args.problem}"
    fc_file = pathlib.Path(args.fc) / "FormalConjectures/ErdosProblems" / f"{args.problem}.lean"

    if not hosted_root.is_dir():
        print(f"no mirrored project at {hosted_root}")
        return 0
    if not fc_file.is_file():
        print(f"no Formal Conjectures statement at {fc_file}")
        print("faithfulness against FC is not applicable until one is written.")
        return 0

    hosted, fc = collect(hosted_root), declarations(fc_file)
    shared = sorted(set(hosted) & set(fc))

    print(f"problem {args.problem}: {len(hosted)} hosted decls, {len(fc)} FC decls, "
          f"{len(shared)} shared by name\n")
    if shared:
        for n in shared:
            same = hosted[n] == fc[n]
            print(f"  {'same ' if same else 'DIFFERS'}  {n}")
            if not same:
                print(f"      FC: {fc[n][:160]}")
                print(f"      HO: {hosted[n][:160]}")
    else:
        print("  no shared definition names: the two sides are written independently,")
        print("  so the statements have to be compared directly rather than by diff.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
