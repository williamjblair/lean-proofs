"""T4 driver: k in [16,3000], N in [2,10^7], 12 N-slices (cost-balanced by
N^{3/2}), MAXWORKERS concurrent t4_scan processes.  Merges survivor CSVs
and per-k first-fail histograms into artifacts/structure_hunt/."""
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

SRC = "/Users/williamblair/personal/lean-proofs/compute/structure_hunt_src"
OUT = "/Users/williamblair/personal/lean-proofs/compute/artifacts/structure_hunt"
GAMMA = os.path.join(OUT, "gamma_scaled_large_k.txt")
WORK = os.path.join(SRC, "t4_work")
NMAX = 10 ** 7
SIEVE = NMAX + 31
NSLICES = 12
MAXWORKERS = int(sys.argv[1]) if len(sys.argv) > 1 else 2


def slices():
    cuts = [2]
    for i in range(1, NSLICES):
        cuts.append(int((i / NSLICES) ** (2 / 3) * NMAX))
    cuts.append(NMAX)
    return [(cuts[i] + (1 if i else 0), cuts[i + 1])
            for i in range(NSLICES)]


def run_job(job):
    i, (nlo, nhi) = job
    pref = os.path.join(WORK, f"s{i:02d}")
    if os.path.exists(pref + ".hist"):
        return job, "cached"
    r = subprocess.run([os.path.join(SRC, "t4_scan"), GAMMA, "16", "3000",
                        str(nlo), str(nhi), str(SIEVE), pref + ".part"],
                       capture_output=True, text=True)
    if r.returncode != 0:
        return job, "FAIL " + r.stderr[:300]
    for ext in (".surv.csv", ".hist", ".ambig"):
        os.rename(pref + ".part" + ext, pref + ext)
    return job, "ok"


def main():
    os.makedirs(WORK, exist_ok=True)
    sl = slices()
    jobs = list(enumerate(sl))
    with ThreadPoolExecutor(MAXWORKERS) as ex:
        for job, status in ex.map(run_job, jobs):
            print(f"slice {job[0]} N={job[1]} {status}", flush=True)
            if status.startswith("FAIL"):
                sys.exit(1)

    # merge survivors
    lines = []
    ambig = []
    hist = {}     # k -> [18]
    meta = {"npoints": 0, "degenerate": 0}
    for i, (nlo, nhi) in jobs:
        pref = os.path.join(WORK, f"s{i:02d}")
        with open(pref + ".surv.csv") as f:
            head = next(f)
            lines.extend(f.read().splitlines())
        with open(pref + ".ambig") as f:
            ambig.extend(f.read().split())
        with open(pref + ".hist") as f:
            for ln in f:
                if ln.startswith("#"):
                    parts = ln.split()
                    meta["npoints"] += int(parts[1].split("=")[1])
                    meta["degenerate"] += int(parts[2].split("=")[1])
                    continue
                if ln.startswith("k,"):
                    continue
                v = [int(x) for x in ln.split(",")]
                h = hist.setdefault(v[0], [0] * 17)
                for a in range(17):
                    h[a] += v[a + 1]
    lines.sort(key=lambda s: (int(s.split(",")[1]), int(s.split(",")[0])))
    with open(os.path.join(OUT, "t4_prefix_survivors.csv"), "w") as f:
        f.write(head)
        f.write("\n".join(lines) + "\n")
    with open(os.path.join(OUT, "t4_firstfail_hist.csv"), "w") as f:
        f.write("# merged; npoints=%d degenerate=%d ambig=%d\n"
                % (meta["npoints"], meta["degenerate"], len(ambig)))
        f.write("k,ff1,ff2,ff3,ff4,ff5,ff6,ff7,ff8,ff9,ff10,ff11,ff12,"
                "ff13,ff14,ff15,ff16,none\n")
        for k in sorted(hist):
            f.write(str(k) + "," + ",".join(map(str, hist[k])) + "\n")
    print(f"survivor lines: {len(lines)}  ambig: {len(ambig)}  "
          f"npoints={meta['npoints']} degenerate={meta['degenerate']}")
    print("T4 MERGE DONE")


if __name__ == "__main__":
    main()
