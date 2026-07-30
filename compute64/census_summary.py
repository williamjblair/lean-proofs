"""Summarize the PSV census scan witness file for the campaign report."""
from __future__ import annotations
import gzip
import json
import sys
from collections import Counter


def main(path):
    by_L = Counter()
    by_verdict = Counter()
    cayley_kills = Counter()
    max_order = 0
    orders = Counter()
    total = 0
    for line in gzip.open(path, "rt"):
        rec = json.loads(line)
        total += 1
        by_verdict[rec["verdict"]] += 1
        max_order = max(max_order, rec["n"])
        orders[rec["n"] <= 1280] += 1
        if rec["verdict"] == "killed":
            by_L[rec["L"]] += 1
            if rec.get("cayley"):
                cayley_kills[rec["L"]] += 1
    print(f"total records: {total}   max order: {max_order}")
    print(f"orders <= 1280: {orders[True]}   orders 1281..2048: {orders[False]}")
    print(f"verdicts: {dict(by_verdict)}")
    print("witness cycle length distribution (all):")
    for L in sorted(by_L):
        print(f"  C{L}: {by_L[L]:>7,}")
    print("witness cycle length distribution (Cayley graphs only):")
    for L in sorted(cayley_kills):
        print(f"  C{L}: {cayley_kills[L]:>7,}")


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "witnesses.jsonl.gz")
