"""Cross-validate t1_scan (C) against an independent exact Python scan.

Python side uses the banked A_window_interval (bignum window predicate,
NOT the floor(c*d) shortcut) and exact big-int divisibility — a fully
independent implementation path.  Compares:
  - the set of {0,1}-survivors (per variant),
  - all bucket counters.
Range: d in [221, DMAX] for every k in 5..15.
"""
import csv
import json
import math
import os
import subprocess
import sys

sys.path.insert(0, "/Users/williamblair/personal/lean-proofs/compute")
from erdos686_exact_core import A_window_interval

SRC = "/Users/williamblair/personal/lean-proofs/compute/structure_hunt_src"
OUT = "/Users/williamblair/personal/lean-proofs/compute/artifacts/structure_hunt"
LAMBDA = {5: 4, 6: 4, 7: 5, 8: 6, 9: 7, 10: 7, 11: 8, 12: 9, 13: 9,
          14: 10, 15: 11}
DMAX = 3000

# exact half-decade thresholds 10^(b/2)
THRESH = []
for b in range(19):
    p10 = 10 ** (b // 2)
    THRESH.append(p10 if b % 2 == 0 else math.isqrt(10 ** b))


def bucket_of(d):
    b = 0
    while b + 1 < 19 and THRESH[b + 1] <= d:
        b += 1
    return b


def py_scan(k):
    lam = LAMBDA[k]
    q = lam - 1
    counts = {}   # bucket -> dict
    surv01 = []
    for d in range(221, DMAX + 1):
        iv = A_window_interval(k, d)
        if iv is None:
            continue
        b = bucket_of(d)
        c = counts.setdefault(b, dict(w=0, l0=0, l01=0, l012=0,
                                      q0=0, q01=0, q012=0,
                                      r0=0, r01=0, r012=0))
        for A in range(iv[0], iv[1] + 1):
            c["w"] += 1
            flags = {}
            for name, fac in (("l", lam ** k), ("q", q ** k), ("r", 1)):
                ps = []
                for t in range(3):
                    G = 1
                    for i in range(k):
                        G *= d - t + i
                    ps.append((fac * G) % (A + t) == 0)
                flags[name] = ps
            for name in ("l", "q", "r"):
                ps = flags[name]
                c[name + "0"] += ps[0]
                c[name + "01"] += ps[0] and ps[1]
                c[name + "012"] += ps[0] and ps[1] and ps[2]
            if (flags["l"][0] and flags["l"][1]) or \
               (flags["q"][0] and flags["q"][1]):
                surv01.append((d, A,
                               int(flags["l"][0] and flags["l"][1]),
                               int(flags["q"][0] and flags["q"][1]),
                               int(flags["r"][0] and flags["r"][1]),
                               int(all(flags["l"])), int(all(flags["q"])),
                               int(all(flags["r"]))))
    return counts, surv01


def main():
    cfg = json.load(open(os.path.join(OUT, "c_scaled_small_k.json")))
    p_lo = {int(k): v for k, v in cfg["p_lo"].items()}
    tmpdir = os.path.join(SRC, "validate_tmp")
    os.makedirs(tmpdir, exist_ok=True)
    all_ok = True
    for k in range(5, 16):
        lam = LAMBDA[k]
        pref = os.path.join(tmpdir, f"v{k}")
        subprocess.run([os.path.join(SRC, "t1_scan"), str(k), str(lam),
                        str(p_lo[k]), "221", str(DMAX), pref], check=True)
        # ambig must be empty
        assert os.path.getsize(pref + ".ambig") == 0, f"ambig nonempty k={k}"
        # read C survivors
        c_surv = []
        with open(pref + ".surv01.csv") as f:
            rd = csv.DictReader(f)
            for row in rd:
                c_surv.append((int(row["d"]), int(row["A"]),
                               int(row["p01_lam"]), int(row["p01_q"]),
                               int(row["p01_raw"]), int(row["p012_lam"]),
                               int(row["p012_q"]), int(row["p012_raw"])))
        # read C counts
        c_counts = {}
        with open(pref + ".counts") as f:
            for line in f:
                if line.startswith("#") or line.startswith("bucket"):
                    continue
                v = line.strip().split(",")
                c_counts[int(v[0])] = dict(
                    w=int(v[2]), l0=int(v[3]), l01=int(v[4]), l012=int(v[5]),
                    q0=int(v[6]), q01=int(v[7]), q012=int(v[8]),
                    r0=int(v[9]), r01=int(v[10]), r012=int(v[11]))
        py_counts, py_surv = py_scan(k)
        ok = (c_counts == py_counts) and (sorted(c_surv) == sorted(py_surv))
        if not ok:
            all_ok = False
            print(f"k={k} MISMATCH")
            print("  C counts:", c_counts)
            print("  P counts:", py_counts)
            print("  C surv:", sorted(c_surv)[:20])
            print("  P surv:", sorted(py_surv)[:20])
        else:
            tot01 = sum(1 for s in py_surv if s[2] or s[3])
            print(f"k={k} OK  window_pairs={sum(c['w'] for c in py_counts.values())}"
                  f" surv01(any)={tot01}")
    print("VALIDATION", "PASS" if all_ok else "FAIL")


if __name__ == "__main__":
    main()
