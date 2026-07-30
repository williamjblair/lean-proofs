"""Fixed-band trap census across decades (mode 'flood').

For each band Y and each decade window, seed the frontier with EVERY vertex of
the starting column (maximally generous, path independent), run until the band
stalls, record the trap and its escape cost, then re-flood just past the trap.
The runs measured this way are the longest column-runs band Y can traverse at
that scale, so the trap density is a lower bound on what any path must face.
"""
import json
import sys
import numpy as np
from census import run

WINDOWS = [("D4", 10_001, 100_001),
           ("D5", 100_001, 1_000_001),
           ("D6", 1_000_001, 2_000_001),
           ("D7", 10_000_001, 11_000_001)]

Y = int(sys.argv[1])
out = {}
for tag, a0, a1 in WINDOWS:
    r = run(Y, a1, W=5000, L=1000, Ycap=max(4 * Y, Y + 2000), budget=30,
            mode="flood", a_start=a0, verbose=False)
    cols = (min(r["reach_max"], a1) - a0) // 2
    runs = r["runs"]
    dp = [t["delta_pass"] for t in r["traps"] if t.get("delta_pass") is not None]
    dl = [t["delta_L"] for t in r["traps"] if t.get("delta_L") is not None]
    nwall = sum(1 for t in r["traps"] if t["is_wall"])
    n3 = sum(1 for t in r["traps"] if t["col_div3"])
    out[tag] = {
        "Y": Y, "a0": a0, "a1": a1, "cols_covered": cols,
        "n_traps": r["n_traps"],
        "traps_per_1e5_cols": round(r["n_traps"] / max(cols, 1) * 1e5, 3),
        "run_len_median": int(np.median(runs)) if runs else None,
        "run_len_mean": int(np.mean(runs)) if runs else None,
        "run_len_max": int(max(runs)) if runs else None,
        "n_wall": nwall, "n_div3": n3,
        "dY_pass_median": float(np.median(dp)) if dp else None,
        "dY_pass_max": int(max(dp)) if dp else None,
        "dY_L_median": float(np.median(dl)) if dl else None,
        "dY_L_mean": round(float(np.mean(dl)), 1) if dl else None,
        "dY_L_max": int(max(dl)) if dl else None,
        "dY_L_unbounded": sum(1 for t in r["traps"] if t.get("delta_L") is None),
        "cap_band": max(4 * Y, Y + 2000),
        "traps": r["traps"],
        "seconds": r["seconds"],
    }
    s = out[tag]
    print(f"Y={Y} {tag} a in [{a0},{a1}] cols={cols} traps={s['n_traps']} "
          f"/1e5c={s['traps_per_1e5_cols']} runmed={s['run_len_median']} "
          f"walls={nwall} dYL med={s['dY_L_median']} max={s['dY_L_max']} "
          f"none={s['dY_L_unbounded']} ({s['seconds']}s)", flush=True)
json.dump(out, open(f"flood_{Y}.json", "w"), indent=1)
