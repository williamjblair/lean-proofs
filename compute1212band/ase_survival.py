#!/usr/bin/env python3
"""ASE survival measurement.

For each interface i, measure the ONE-STEP SURVIVAL PROBABILITY

    q_i = #{c in B_i : some block column of row i+1 lies in the climb-free
                        interval around c} / |B_i|

so that (first moment) the expected number of full dual staircases is

    #staircases ~ |B_1| * prod_i q_i.

ASE holds at these parameters when that product is < 1; the interesting output
is how q scales with the row modulus Z, since at true scale Z = Y^{5/2-eta}
while climb-free gaps stay polylogarithmic.
"""
import sys
import numpy as np
from sympy import factorint
from ase_surrogate import build_rows, prime_mask, climb_mask, block_cols

def survival(H, E, Z, A, L):
    rows = build_rows(H, E, Z)
    K = len(rows)
    if K < 3:
        return None
    isp = prime_mask(A, L)
    B = [block_cols(A, L, ps) for _, ps in rows]
    qs, gaps, pmins = [], [], []
    for i in range(K - 1):
        climbs = np.flatnonzero(climb_mask(A, L, rows[i][0], rows[i + 1][0], isp)) + A
        if len(climbs) < 2:
            qs.append(1.0); continue
        cur, nxt = B[i], B[i + 1]
        lo_i = np.searchsorted(climbs, cur, side='left') - 1
        hi_i = np.searchsorted(climbs, cur, side='right')
        lo = np.where(lo_i >= 0, climbs[np.clip(lo_i, 0, len(climbs) - 1)], A)
        hi = np.where(hi_i < len(climbs), climbs[np.clip(hi_i, 0, len(climbs) - 1)],
                      A + L - 1)
        s = np.searchsorted(nxt, lo, side='left')
        e = np.searchsorted(nxt, hi, side='right')
        qs.append(float(np.mean(e > s)))
        gaps.append(float(np.mean(np.diff(climbs))))
        pmins.append(min(rows[i + 1][1]))
    qs = np.array(qs)
    logprod = float(np.sum(np.log(np.maximum(qs, 1e-300))))
    exp_stairs = np.log(len(B[0])) + logprod
    print(f"  Z={Z:5d} K={K:3d}  q: mean={qs.mean():.4f} max={qs.max():.4f}  "
          f"mean climb-free gap={np.mean(gaps):.1f}  median p_min={int(np.median(pmins))}")
    print(f"          predicted q ~ gap*6/p = {np.mean(gaps)*6/np.median(pmins):.4f}")
    print(f"          log(expected #staircases) = {exp_stairs:.1f}  "
          f"({'ASE HOLDS (first moment)' if exp_stairs < 0 else 'STAIRCASES EXPECTED'})")
    return dict(Z=Z, K=K, qmean=float(qs.mean()), logexp=exp_stairs)

if __name__ == '__main__':
    H, A = 10 ** 9, 10 ** 7
    L = int(sys.argv[1]) if len(sys.argv) > 1 else 2 * 10 ** 6
    print(f"columns [{A},{A+L}), reservoir height ~1e9")
    for Z in (300, 600, 1200, 2400, 4800):
        survival(H, max(Z, 600), Z, A, L)
