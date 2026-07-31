#!/usr/bin/env python3
"""O1/O2 verification for the low-band ladder (vertical_ladder_proof.md).

O1: rough-composite supply and close-pair supply in the box [z^2, z^2+z^5].
O2: killer-sum distribution over close pairs (R,R'):
    S(R,R') = sum of 1/P over primes P > d dividing some m in [R, R'].
    Theory: average O(1/log d); good pairs (<= 3x avg) >= 2/3.
"""
import numpy as np, math, random, sys

def primes_upto(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n**0.5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]

def box_analysis(z, seed=1212):
    lo, width = z * z, z ** 5
    hi = lo + width
    P = primes_upto(int(math.isqrt(hi)) + 1)
    small = P[P <= z]
    mid = P[P > z]
    hasfac_z = np.zeros(width + 1, dtype=bool)
    hasfac_sq = np.zeros(width + 1, dtype=bool)
    for p in small:
        st = (-lo) % p
        hasfac_z[st::p] = True
    hasfac_sq |= hasfac_z
    for p in mid:
        st = (-lo) % p
        # only mark proper factors (p < n), n=lo+idx; p >= n only if idx small
        hasfac_sq[st::p] = True
        if lo + st == p and st <= width:  # p itself in window: not a proper factor
            hasfac_sq[st] = False if not hasfac_z[st] and True else hasfac_sq[st]
    # correct: n prime <=> n>1 and no proper prime factor <= sqrt(hi).
    # marking p at its own position wrongly labels p composite; fix:
    for p in mid:
        if lo <= p <= hi:
            idx = p - lo
            # p has no other factor; recompute: composite iff any q<p divides
            hasfac_sq[idx] = any(p % int(q) == 0 for q in small)  # False
    rough = ~hasfac_z
    rough_comp = rough & hasfac_sq
    idx = np.nonzero(rough_comp)[0]
    vals = idx + lo
    n_rough = int(rough.sum()); n_rc = len(vals)
    logz = math.log(z)
    print(f"z={z} box=[{lo},{hi}] width={width}")
    print(f"  rough={n_rough} ({n_rough*logz/width:.3f} * w/log z; theory>=0.5)")
    print(f"  rough composites={n_rc} ({n_rc*logz/width:.3f} * w/log z; theory>=0.1)")
    gaps = np.diff(vals)
    print(f"  gaps: mean={gaps.mean():.1f} median={np.median(gaps):.0f} max={gaps.max()} (z^2={z*z})")
    for mult in (1, 2, 4, 8):
        d = mult * logz
        frac = float((gaps <= d).mean())
        print(f"  close pairs |R-R'|<= {mult}*log z ({d:.1f}): {int((gaps<=d).sum())} ({frac:.2%} of gaps)")
    # O2: killer sums on sampled close pairs, d = 4 log z
    d = max(3, int(4 * logz))
    close = np.nonzero(gaps <= d)[0]
    random.seed(seed)
    sample = random.sample(list(close), min(3000, len(close)))
    Plist = [int(p) for p in P]
    sums = []
    for i in sample:
        R, R2 = int(vals[i]), int(vals[i + 1])
        s = 0.0
        for m in range(R, R2 + 1):
            mm = m
            for p in Plist:
                if p * p > mm: break
                if mm % p == 0:
                    while mm % p == 0: mm //= p
                    if p > d: s += 1.0 / p
            if mm > 1 and mm > d: s += 1.0 / mm
        sums.append(s)
    sums = np.array(sums)
    avg = sums.mean()
    print(f"  O2 killer sums (d={d}, n={len(sums)}): avg={avg:.4f} "
          f"(x log d = {avg*math.log(d):.3f}; theory O(1))")
    print(f"     median={np.median(sums):.4f} p90={np.percentile(sums,90):.4f} max={sums.max():.3f}")
    good = float((sums <= 3 * avg).mean())
    # candidate density at level d is ~c/log d with c>=0.1-ish; survival needs
    # killed density (=S) < candidate density. Compare S vs 1/(2 log d):
    thr = 1.0 / (2 * math.log(d))
    print(f"     good pairs (S<=3avg): {good:.2%}; pairs with S < 1/(2 log d)={thr:.3f}: "
          f"{float((sums<thr).mean()):.2%}")
    return vals, gaps

for z in (int(x) for x in sys.argv[1:] or (20, 30)):
    box_analysis(z)
    print()
