"""T5 - d <= 220 finite core witnesses (Erdos #686, N = 4 branch).

Enumerate ALL (k,n,d) with 5 <= k <= 15, k <= d <= 220, n >= 1 satisfying the
exact ratio window
    (n+d+k)^k <= 4*(n+k)^k   and   4*(n+1)^k <= (n+d+1)^k.
For each triple, record the SMALLEST j in 1..k with
    NOT (n+j) | shiftedDiffProductAt(k,d,j)
(shiftedDiffProductAt(k,d,j) = prod_{i=1..k} (d+i-j), natural subtraction).

Enumeration strategy (exact): for each (k,d), the two window inequalities are
monotone in n, so the window n-range is an interval found by integer
bisection (endpoints re-verified); only that interval is scanned.

Expected (per PROGRESS): 20,779 triples, all with n < 2640, first-failure
histogram j=1:15434, j=2:4269, j=3:863, j=4:182, j=5:31, and no triple
surviving rows j <= 5.

Artifacts:
    compute/artifacts/small_core_witnesses.json
    compute/artifacts/small_core_witnesses.csv
    compute/artifacts/small_core_witnesses_lean.txt   (Lean-ready list)
"""

import csv
import json
import os
import time
from collections import Counter

from erdos686_exact_core import (
    n_window_interval, window_n, shifted_diff_product_at,
)

HERE = os.path.dirname(os.path.abspath(__file__))
ART = os.path.join(HERE, "artifacts")

EXPECTED_TOTAL = 20779
EXPECTED_HIST = {1: 15434, 2: 4269, 3: 863, 4: 182, 5: 31}
EXPECTED_N_MAX_LT = 2640


def first_failing_row(k: int, n: int, d: int):
    """Smallest j in 1..k with NOT (n+j) | shiftedDiffProductAt(k,d,j),
    or None if every row divides."""
    for j in range(1, k + 1):
        if shifted_diff_product_at(k, d, j) % (n + j) != 0:
            return j
    return None


def run():
    t0 = time.time()
    witnesses = []
    no_failure = []
    hist = Counter()
    n_max = 0

    for k in range(5, 16):
        for d in range(k, 221):
            iv = n_window_interval(k, d)
            if iv is None:
                continue
            n_lo, n_hi = iv
            # endpoint re-verification (window really holds inside, not out)
            assert window_n(k, n_lo, d) and window_n(k, n_hi, d)
            assert n_lo == 1 or not window_n(k, n_lo - 1, d)
            assert not window_n(k, n_hi + 1, d)
            for n in range(n_lo, n_hi + 1):
                j = first_failing_row(k, n, d)
                if j is None:
                    no_failure.append((k, n, d))
                    continue
                witnesses.append((k, n, d, j))
                hist[j] += 1
                if n > n_max:
                    n_max = n

    elapsed = time.time() - t0
    total = len(witnesses) + len(no_failure)
    print(f"window triples:      {total} "
          f"(expected {EXPECTED_TOTAL}) "
          f"{'OK' if total == EXPECTED_TOTAL else 'MISMATCH'}")
    print(f"triples with no row failure: {len(no_failure)} (expected 0)")
    if no_failure:
        for t in no_failure[:20]:
            print("  NO-FAILURE TRIPLE:", t)
    hist_view = {j: hist.get(j, 0) for j in sorted(set(hist) | set(EXPECTED_HIST))}
    print(f"first-failure histogram: {hist_view}")
    print(f"expected histogram:      {EXPECTED_HIST} "
          f"{'OK' if hist_view == EXPECTED_HIST else 'MISMATCH'}")
    print(f"max n: {n_max} (< {EXPECTED_N_MAX_LT}: "
          f"{'OK' if n_max < EXPECTED_N_MAX_LT else 'FAIL'})")
    print(f"max first-failure j: {max(hist) if hist else None}")
    print(f"elapsed={elapsed:.2f}s")

    os.makedirs(ART, exist_ok=True)
    payload = {
        "description": "Finite core for d <= 220: every exact-ratio-window "
                       "triple (k,n,d) with 5<=k<=15, k<=d<=220, n>=1, "
                       "together with the smallest row j in 1..k whose "
                       "divisibility (n+j) | shiftedDiffProductAt(k,d,j) "
                       "fails.",
        "window": "(n+d+k)^k <= 4*(n+k)^k and 4*(n+1)^k <= (n+d+1)^k",
        "total_window_triples": total,
        "expected_total": EXPECTED_TOTAL,
        "no_failure_triples": [list(t) for t in no_failure],
        "first_failure_histogram": {str(j): c for j, c
                                    in sorted(hist.items())},
        "expected_histogram": {str(j): c for j, c
                               in sorted(EXPECTED_HIST.items())},
        "n_max": n_max,
        "witness_format": ["k", "n", "d", "j"],
        "witnesses": [list(t) for t in witnesses],
        "elapsed_seconds": round(elapsed, 3),
    }
    jpath = os.path.join(ART, "small_core_witnesses.json")
    with open(jpath, "w") as f:
        json.dump(payload, f)
    cpath = os.path.join(ART, "small_core_witnesses.csv")
    with open(cpath, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["k", "n", "d", "j"])
        w.writerows(witnesses)
    # compact Lean-ready certificate: list of (k, n, d, j) 4-tuples
    lpath = os.path.join(ART, "small_core_witnesses_lean.txt")
    with open(lpath, "w") as f:
        f.write("-- Erdos 686 small-core witnesses: (k, n, d, j) with\n")
        f.write("-- 5 <= k <= 15, k <= d <= 220, exact N=4 ratio window,\n")
        f.write("-- and j = least row in 1..k with\n")
        f.write("--   ¬ (n + j ∣ shiftedDiffProductAt k d j).\n")
        f.write(f"-- count = {len(witnesses)}, n_max = {n_max}, "
                f"j_max = {max(hist) if hist else 0}\n")
        f.write("def smallCoreWitnesses : List (Nat × Nat × Nat × Nat) :=\n")
        f.write("  [")
        chunks = [f"({k}, {n}, {d}, {j})" for (k, n, d, j) in witnesses]
        line = ""
        lines = []
        for c in chunks:
            if len(line) + len(c) + 2 > 96:
                lines.append(line)
                line = ""
            line += (", " if line else "") + c
        if line:
            lines.append(line)
        f.write((",\n   ").join(lines))
        f.write("]\n")
    print(f"wrote {jpath}")
    print(f"wrote {cpath}")
    print(f"wrote {lpath}")
    return witnesses, hist, n_max, no_failure


if __name__ == "__main__":
    run()
