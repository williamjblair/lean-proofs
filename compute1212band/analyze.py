"""Aggregate every measurement into the tables used by band_report.md."""
import glob
import json
import math
import numpy as np

ALL = []


def load(pat):
    for f in sorted(glob.glob(pat)):
        yield f, json.load(open(f))


print("=" * 78)
print("RATCHET RUNS  (band starts at Y0, grows by the measured dY at each trap)")
print("=" * 78)
print(f"{'file':22} {'Y0':>5} {'reach':>10} {'traps':>6} {'endband':>8} {'sec':>7}")
for f, r in load("r*_ratchet.json") :
    print(f"{f:22} {r['Y']:>5} {r['reach_max']:>10} {r['n_traps']:>6} "
          f"{r['final_band']:>8} {r['seconds']:>7}")
    ALL.extend(r["traps"])
for f, r in load("r*_far.json"):
    print(f"{f:22} {r['Y']:>5} {r['reach_max']:>10} {r['n_traps']:>6} "
          f"{r['final_band']:>8} {r['seconds']:>7}")
    ALL.extend(r["traps"])

print()
print("per-trap detail (ratchet):")
print(f"{'a*':>10} {'log10':>6} {'band':>6} {'run(cols)':>10} {'dY_pass':>8} "
      f"{'dY_L':>6} {'open':>5} {'reach':>6} {'wall':>5} {'3|a*':>5}")
for f, r in list(load("r*_ratchet.json")) + list(load("r*_far.json")):
    for t in r["traps"]:
        print(f"{t['a_star']:>10} {math.log10(t['a_star']):>6.2f} {t['band']:>6} "
              f"{t['run_len_cols']:>10} {str(t.get('delta_pass')):>8} "
              f"{str(t.get('delta_L')):>6} {t['open_rows']:>5} "
              f"{t['reach_rows']:>6} {str(t['is_wall']):>5} "
              f"{str(t['col_div3']):>5}")

print()
print("=" * 78)
print("FIXED-BAND FLOOD RUNS  (maximally generous frontier, band never grows)")
print("=" * 78)
hdr = (f"{'Y':>5} {'dec':>4} {'cols':>8} {'traps':>6} {'/1e5c':>9} "
       f"{'runmed':>8} {'runmax':>9} {'walls':>6} {'dYLmed':>7} {'dYLmax':>7} "
       f"{'dYL=inf':>8}")
print(hdr)
flood = {}
for f, r in load("flood_*.json"):
    for tag, s in sorted(r.items()):
        print(f"{s['Y']:>5} {tag:>4} {s['cols_covered']:>8} {s['n_traps']:>6} "
              f"{s['traps_per_1e5_cols']:>9} {str(s['run_len_median']):>8} "
              f"{str(s['run_len_max']):>9} {s['n_wall']:>6} "
              f"{str(s['dY_L_median']):>7} {str(s['dY_L_max']):>7} "
              f"{s['dY_L_unbounded']:>8}")
        flood[(s["Y"], tag)] = s
        ALL.extend(s["traps"])

print()
print("=" * 78)
print(f"TRAP MECHANISM CENSUS   (all {len(ALL)} traps from every run)")
print("=" * 78)
n = len(ALL)
wall = sum(t["is_wall"] for t in ALL)
d3 = sum(t["col_div3"] for t in ALL)
nov = sum(1 for t in ALL if t.get("frontier_vert_moves", 0) == 0)
nov3 = sum(1 for t in ALL if t.get("frontier_vert_moves", 0) == 0 and t["col_div3"])
print(f"  traps                                   {n}")
print(f"  genuine Wall-Lemma columns (open==0)    {wall}  ({100*wall/n:.2f}%)")
print(f"  local traps (open>0, unreachable)       {n-wall}  ({100*(n-wall)/n:.2f}%)")
print(f"  3 | a*  (no vertical move in a* at all) {d3}  ({100*d3/n:.1f}%)")
print(f"  frontier had NO vertical move at a*     {nov}  ({100*nov/n:.1f}%)")
print(f"     ... of those, because 3 | a*         {nov3}  ({100*nov3/max(nov,1):.1f}%)")
print(f"  frontier COULD move vertically at a*    {n-nov}  ({100*(n-nov)/n:.1f}%)")
op = np.array([t["open_rows"] for t in ALL])
rr = np.array([t["reach_rows"] for t in ALL])
print(f"  open rows at a*:  median {int(np.median(op))}  mean {op.mean():.1f}  "
      f"min {op.min()}  max {op.max()}")
print(f"  reachable rows at a*: median {int(np.median(rr))} mean {rr.mean():.1f} "
      f"min {rr.min()} max {rr.max()}")
gap = np.array([t["row_gap"] for t in ALL if "row_gap" in t])
print(f"  row distance frontier -> nearest open row: median {int(np.median(gap))} "
      f"mean {gap.mean():.1f} max {gap.max()}")
print()
print("  spf(a*) distribution (smallest odd prime factor of the trap column):")
from collections import Counter
c = Counter(t["spf_a"] if t["spf_a"] <= 13 else 99 for t in ALL)
for k in sorted(c):
    lbl = ">13" if k == 99 else str(k)
    print(f"    spf={lbl:>3}: {c[k]:>5} ({100*c[k]/n:.1f}%)")
print("  divisibility of the column and its two successors:")
for nm, key in (("3|a*", "col_div3"), ("5|a*", "col_div5"), ("7|a*", "col_div7")):
    v = sum(t[key] for t in ALL)
    base = {"3|a*": 33.3, "5|a*": 20.0, "7|a*": 14.3}[nm]
    print(f"    {nm:>5}: {v:>5} ({100*v/n:.1f}%)   [odd a at random: {base}%]")

print()
print("=" * 78)
print("ESCAPE COST dY  (all traps where it was measured)")
print("=" * 78)
dp = np.array([t["delta_pass"] for t in ALL if t.get("delta_pass") is not None])
dl = np.array([t["delta_L"] for t in ALL if t.get("delta_L") is not None])
nn = sum(1 for t in ALL if "delta_L" in t and t["delta_L"] is None)
print(f"  dY_pass (reach a*+2):     n={dp.size} mean={dp.mean():.1f} "
      f"median={np.median(dp):.0f} p90={np.percentile(dp,90):.0f} max={dp.max()}")
print(f"  dY_L    (sustain 1000c):  n={dl.size} mean={dl.mean():.1f} "
      f"median={np.median(dl):.0f} p90={np.percentile(dl,90):.0f} max={dl.max()}")
print(f"  dY_L unbounded at the cap: {nn}")
print()
print("  dY_L by base band Y:")
bands = {}
for t in ALL:
    if t.get("delta_L") is not None:
        bands.setdefault((t["band"] + 1) // 200 * 200, []).append(
            (t["delta_L"], t["delta_L"] / t["band"]))
for k in sorted(bands):
    v = np.array([a for a, _ in bands[k]])
    rr2 = np.array([r for _, r in bands[k]])
    print(f"    band ~{k:>5} n={v.size:>4} median={np.median(v):>6.0f} "
          f"mean={v.mean():>7.1f} max={v.max():>5}  median(dY/Y)="
          f"{np.median(rr2):.3f}")
print()
print("  dY_L by decade of a*:")
dec = {}
for t in ALL:
    if t.get("delta_L") is not None:
        dec.setdefault(int(math.log10(t["a_star"])), []).append(t["delta_L"])
for k in sorted(dec):
    v = np.array(dec[k])
    print(f"    10^{k}-10^{k+1}: n={v.size:>4} median={np.median(v):>6.0f} "
          f"mean={v.mean():>7.1f} max={v.max():>5}")

print()
print("=" * 78)
print("BAND TRAJECTORY UNDER THE RATCHET   Y(x) after each extension")
print("=" * 78)
for f, r in list(load("r*_ratchet.json")) + list(load("r*_far.json")):
    pts = [(r["start"], r["Y"])]
    for t in r["traps"]:
        if t.get("delta_L") is not None:
            pts.append((t["a_star"], t["band"] + t["delta_L"]))
    pts.append((r["reach_max"], r["final_band"]))
    print(f"  {f}:")
    for a, y in pts:
        print(f"     x={a:>10}  log10 x={math.log10(max(a,3)):>5.2f}   band={y}")
    if len(pts) >= 3:
        xs = np.log(np.array([max(a, 3) for a, _ in pts[1:]], float))
        ys = np.array([y for _, y in pts[1:]], float)
        if np.ptp(xs) > 0:
            c = np.polyfit(xs, ys, 1)
            print(f"     least-squares fit  Y ~ {c[0]:.0f}*ln(x) + {c[1]:.0f}"
                  f"   (rows per e-fold of x: {c[0]:.0f})")
