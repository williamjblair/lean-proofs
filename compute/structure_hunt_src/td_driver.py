"""T-D driver: scan the two regions the previous T4 scan did not cover.

  Region A: k in [3001, 6500], N in [2, 10^7]
            (old scan capped k at 3000, but d >= k is feasible up to
             k ~ sqrt(ln4 * N) ~ 3722 at N = 10^7)
  Region B: k in [16, 6500],  N in [10^7 + 1, 3*10^7]

Slices cost-balanced by N^{3/2}; results merged with the old
t4_prefix_survivors.csv (rows with first_fail_pure in {16,17}) by
td_anatomy.py.  Outputs td_deep_survivors.csv + td_firstfail_hist.csv.
"""
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor

SRC = "/Users/williamblair/personal/lean-proofs/compute/structure_hunt_src"
OUT = "/Users/williamblair/personal/lean-proofs/compute/artifacts/structure_hunt"
GAMMA = os.path.join(OUT, "gamma_scaled_large_k.txt")
WORK = os.path.join(SRC, "td_work")
MAXWORKERS = int(sys.argv[1]) if len(sys.argv) > 1 else 6

NLO_B, NHI_B = 10 ** 7 + 1, 3 * 10 ** 7
NSLICES_B = 12


def jobs():
    out = [("A00", 3001, 6500, 2, 10 ** 7)]
    c0, c1 = NLO_B ** 1.5, NHI_B ** 1.5
    cuts = [NLO_B - 1]
    for i in range(1, NSLICES_B):
        cuts.append(int((c0 + (c1 - c0) * i / NSLICES_B) ** (2 / 3)))
    cuts.append(NHI_B)
    for i in range(NSLICES_B):
        out.append((f"B{i:02d}", 16, 6500, cuts[i] + 1, cuts[i + 1]))
    return out


def run_job(job):
    tag, kmin, kmax, nlo, nhi = job
    pref = os.path.join(WORK, tag)
    if os.path.exists(pref + ".hist"):
        return job, "cached"
    r = subprocess.run([os.path.join(SRC, "td_scan"), GAMMA, str(kmin),
                        str(kmax), str(nlo), str(nhi), str(nhi + 31),
                        pref + ".part"], capture_output=True, text=True)
    if r.returncode != 0:
        return job, "FAIL " + r.stderr[:300]
    for ext in (".deep.csv", ".hist", ".ambig"):
        os.rename(pref + ".part" + ext, pref + ext)
    return job, "ok"


def main():
    os.makedirs(WORK, exist_ok=True)
    jl = jobs()
    with ThreadPoolExecutor(MAXWORKERS) as ex:
        for job, status in ex.map(run_job, jl):
            print(f"{job[0]} k=[{job[1]},{job[2]}] N=[{job[3]},{job[4]}] "
                  f"{status}", flush=True)
            if status.startswith("FAIL"):
                sys.exit(1)

    lines, ambig = [], []
    hist = {}
    meta = {"npoints": 0, "degenerate": 0}
    for tag, kmin, kmax, nlo, nhi in jl:
        pref = os.path.join(WORK, tag)
        with open(pref + ".deep.csv") as f:
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
                h = hist.setdefault(v[0], [0] * 19)
                for a in range(19):
                    h[a] += v[a + 1]
    lines.sort(key=lambda s: (int(s.split(",")[1]), int(s.split(",")[0]),
                              int(s.split(",")[2])))
    with open(os.path.join(OUT, "td_deep_survivors_new_regions.csv"), "w") as f:
        f.write(head)
        f.write("\n".join(lines) + ("\n" if lines else ""))
    with open(os.path.join(OUT, "td_firstfail_hist_new_regions.csv"), "w") as f:
        f.write("# regions: k[3001,6500]xN[2,1e7] + k[16,6500]xN[1e7+1,3e7]; "
                "npoints=%d degenerate=%d ambig=%d\n"
                % (meta["npoints"], meta["degenerate"], len(ambig)))
        f.write("k," + ",".join(f"ff{a}" for a in range(1, 19)) + ",none\n")
        for k in sorted(hist):
            f.write(str(k) + "," + ",".join(map(str, hist[k])) + "\n")
    print(f"deep survivor lines: {len(lines)}  ambig: {len(ambig)}  "
          f"npoints={meta['npoints']} degenerate={meta['degenerate']}")
    print("TD MERGE DONE")


if __name__ == "__main__":
    main()
