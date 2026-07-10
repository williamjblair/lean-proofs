"""Production T1 driver: scan d in [221, 10^9] for every k in 5..15.

Chunks of 5*10^7 per job, at most MAXWORKERS concurrent t1_scan processes.
Merges per-bucket counters and per-k {0,1}-survivor CSVs into
artifacts/structure_hunt/.  Any ambiguous-floor d (bracket undecided at
scale 2^60) is resolved exactly in Python afterwards; expected count 0.
"""
import csv
import json
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

SRC = "/Users/williamblair/personal/lean-proofs/compute/structure_hunt_src"
OUT = "/Users/williamblair/personal/lean-proofs/compute/artifacts/structure_hunt"
WORK = os.path.join(SRC, "t1_work")
LAMBDA = {5: 4, 6: 4, 7: 5, 8: 6, 9: 7, 10: 7, 11: 8, 12: 9, 13: 9,
          14: 10, 15: 11}
DMAX_K = {5: 10 ** 8, 6: 10 ** 8, 7: 10 ** 8, 8: 10 ** 8, 9: 10 ** 8,
          10: 3 * 10 ** 8, 11: 10 ** 9, 12: 3 * 10 ** 8, 13: 10 ** 9,
          14: 3 * 10 ** 8, 15: 3 * 10 ** 8}
CHUNK = 5 * 10 ** 7
MAXWORKERS = 4

cfg = json.load(open(os.path.join(OUT, "c_scaled_small_k.json")))
P_LO = {int(k): v for k, v in cfg["p_lo"].items()}


def jobs():
    out = []
    for k in sorted(LAMBDA, key=lambda kk: -kk):   # big k first (longest)
        lo = 221
        i = 0
        while lo <= DMAX_K[k]:
            hi = min(lo + CHUNK - 1, DMAX_K[k])
            out.append((k, lo, hi, os.path.join(WORK, f"k{k}_c{i:03d}")))
            lo = hi + 1
            i += 1
    return out


def run_job(job):
    k, lo, hi, pref = job
    if os.path.exists(pref + ".counts"):
        return job, "cached"
    r = subprocess.run([os.path.join(SRC, "t1_scan"), str(k),
                        str(LAMBDA[k]), str(P_LO[k]), str(lo), str(hi),
                        pref + ".part"], capture_output=True, text=True)
    if r.returncode != 0:
        return job, "FAIL: " + r.stderr[:200]
    for ext in (".counts", ".surv01.csv", ".ambig"):
        os.rename(pref + ".part" + ext, pref + ext)
    return job, "ok"


def main():
    os.makedirs(WORK, exist_ok=True)
    jl = jobs()
    print(f"{len(jl)} jobs")
    fails = []
    with ThreadPoolExecutor(MAXWORKERS) as ex:
        for job, status in ex.map(run_job, jl):
            if status.startswith("FAIL"):
                fails.append((job, status))
            print(f"k={job[0]} [{job[1]},{job[2]}] {status}", flush=True)
    if fails:
        print("FAILURES:", fails)
        sys.exit(1)

    # ---- merge ----
    counts = {}   # k -> bucket -> [11 counters]
    ambig = []
    for k, lo, hi, pref in jl:
        with open(pref + ".counts") as f:
            for line in f:
                if line.startswith("#") or line.startswith("bucket"):
                    continue
                v = line.strip().split(",")
                b = int(v[0])
                tgt = counts.setdefault(k, {}).setdefault(
                    b, [0] * 11)
                for i in range(11):
                    tgt[i] += int(v[i + 1])
        with open(pref + ".ambig") as f:
            for line in f:
                ambig.append((k, int(line)))
    cols = ["bucket_lo", "window", "c0_lam", "c01_lam", "c012_lam",
            "c0_q", "c01_q", "c012_q", "c0_raw", "c01_raw", "c012_raw"]
    payload = {"dmax": {str(k): v for k, v in DMAX_K.items()},
               "columns": cols,
               "buckets": {str(k): {str(b): v for b, v in sorted(bs.items())}
                           for k, bs in sorted(counts.items())},
               "ambiguous_d": ambig}
    with open(os.path.join(OUT, "t1_counts.json"), "w") as f:
        json.dump(payload, f, indent=1)

    for k in sorted(LAMBDA):
        rows = []
        for kk, lo, hi, pref in jl:
            if kk != k:
                continue
            with open(pref + ".surv01.csv") as f:
                rd = csv.reader(f)
                head = next(rd)
                rows.extend(rd)
        rows.sort(key=lambda r: (int(r[1]), int(r[2])))
        with open(os.path.join(OUT, f"t1_surv01_k{k}.csv"), "w",
                  newline="") as f:
            w = csv.writer(f)
            w.writerow(head)
            w.writerows(rows)
        n012l = sum(1 for r in rows if r[6] == "1")
        n012q = sum(1 for r in rows if r[7] == "1")
        print(f"k={k}: surv01_any={len(rows)} surv012_lam={n012l} "
              f"surv012_q={n012q}")
    print("ambiguous d count:", len(ambig))
    print("MERGE DONE")


if __name__ == "__main__":
    main()
