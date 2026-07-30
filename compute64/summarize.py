"""Aggregate Erdős #64 campaign search results into results.json + a table.

Reads:
- wp2/stats_low_<n>.txt, wp2/stats<n>_<part>.txt  (general C4-free δ≥3 sieve)
- stats_cubic_<n>.txt                              (full cubic sieve)
- census scan summary (if present)

The stats format is checkc.c stderr: total=A no_c4=B no_c4c8=C survivors=D
For the general sieve, geng -c -f -d3 guarantees the input class; checkc
re-verifies C4-freeness (total == no_c4 is asserted as a consistency check).
"""
from __future__ import annotations
import glob
import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
PAT = re.compile(r"total=(\d+) no_c4=(\d+) no_c4c8=(\d+) survivors=(\d+)")


def read_stats(path):
    m = PAT.search(open(path).read())
    return tuple(int(g) for g in m.groups()) if m else None


def main():
    results = {"general_c4free_mindeg3": {}, "cubic_all": {}}

    for path in glob.glob(os.path.join(HERE, "wp2", "stats_low_*.txt")):
        n = int(re.search(r"stats_low_(\d+)", path).group(1))
        s = read_stats(path)
        if s:
            results["general_c4free_mindeg3"][n] = {
                "graphs": s[0], "no_c4c8": s[2], "survivors": s[3],
                "parts": 1}

    part_totals: dict[int, list] = {}
    for path in glob.glob(os.path.join(HERE, "wp2", "stats[0-9]*_*.txt")):
        m = re.search(r"stats(\d+)_(\d+)\.txt", os.path.basename(path))
        if not m:
            continue
        n = int(m.group(1))
        s = read_stats(path)
        if s:
            part_totals.setdefault(n, []).append(s)
    for n, parts in part_totals.items():
        agg = [sum(p[i] for p in parts) for i in range(4)]
        assert agg[0] == agg[1], f"n={n}: C4-free input violated"
        results["general_c4free_mindeg3"][n] = {
            "graphs": agg[0], "no_c4c8": agg[2], "survivors": agg[3],
            "parts": len(parts)}

    for path in glob.glob(os.path.join(HERE, "stats_cubic_*.txt")):
        m = re.search(r"stats_cubic_(\d+)\.txt", os.path.basename(path))
        if not m:
            continue
        n = int(m.group(1))
        s = read_stats(path)
        if s:
            results["cubic_all"][n] = {
                "graphs": s[0], "c4_free": s[1], "c4c8_free": s[2],
                "survivors": s[3]}

    out = os.path.join(HERE, "results.json")
    with open(out, "w") as f:
        json.dump(results, f, indent=2, sort_keys=True)

    print("General δ≥3, C4-free, connected (geng -c -f -d3 | checkc):")
    gen = results["general_c4free_mindeg3"]
    for n in sorted(gen):
        r = gen[n]
        print(f"  n={n:2d}: {r['graphs']:>12,} graphs  "
              f"{r['no_c4c8']:>4} lacked C8  {r['survivors']} survivors  "
              f"[{r['parts']} part(s)]")
    clean = [n for n in sorted(gen) if gen[n]["survivors"] == 0]
    if clean and clean == list(range(min(clean), max(clean) + 1)):
        print(f"  => no Erdős-64 counterexample on ≤ {max(clean)} vertices "
              f"(orders {min(clean)}..{max(clean)} exhausted; "
              f"orders < 10 have no C4-free δ≥3 graphs)")

    print("All cubic connected (snarkhunter n 3 s o g | checkc):")
    cub = results["cubic_all"]
    for n in sorted(cub):
        r = cub[n]
        print(f"  n={n:2d}: {r['graphs']:>13,} graphs  "
              f"{r['c4_free']:>9,} C4-free  {r['c4c8_free']:>4} {{C4,C8}}-free  "
              f"{r['survivors']} survivors")


if __name__ == "__main__":
    main()
