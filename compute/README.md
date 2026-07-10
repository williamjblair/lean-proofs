# compute/ — problem-specific computational artifacts

This package mixes two campaigns for historical reasons (documented
reproduction commands depend on these exact paths):

- `erdos686_*.py`, `artifacts/`, `theory/`, `structure_hunt_src/` — the
  Erdős #686 campaign (see PROGRESS_Erdos686.md).
- `erdos699.py`, `kernel.py`, `scan.py`, `tests/`, `__init__.py` — the
  Erdős #699 campaign python package, invoked as `python3 -m compute.kernel`
  etc. (see PROGRESS_Erdos699.md).

Other campaigns use their own top-level directories:
- `compute617/` — Erdős #617 (K_26 coloring search; live campaign)
- `compute23/`  — Erdős #23 (flag certificate reproduction + gates)
- `compute730/` — Erdős #730 (capped proof audit)
