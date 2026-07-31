#!/usr/bin/env python3
"""Lemma E check: killer-mass equidistribution.
Range [z^2, z^2+L]; windows of span D; S_kill(W) = sum 1/P over distinct
primes P > D dividing some m in W. Check avg*log D <= ~1, bad fraction
(S > 8/log D) <= 1/4 in every D^{1+eps} stretch, and max bad-run length."""
import math, sys
import numpy as np

def primes_upto(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n**0.5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]

z = int(sys.argv[1]) if len(sys.argv) > 1 else 30
L = int(sys.argv[2]) if len(sys.argv) > 2 else 2_000_000
D = int(sys.argv[3]) if len(sys.argv) > 3 else 100
lo = z * z; hi = lo + L
P = primes_upto(int(math.isqrt(hi)) + 1)
rem = np.arange(lo, hi + 1, dtype=np.int64)
nw = L // D + 1
S = np.zeros(nw)
seen = [set() for _ in range(nw)]  # dedupe primes per window
for p in P:
    st = (-lo) % p
    for idx in range(st, L + 1, p):
        w = idx // D
        if p > D and p not in seen[w]:
            seen[w].add(p); S[w] += 1.0 / p
        while rem[idx] % p == 0: rem[idx] //= p
# remainders > 1 are single large prime factors
for idx in np.nonzero(rem > 1)[0]:
    p = int(rem[idx]); w = idx // D
    if p > D and p not in seen[w]:
        seen[w].add(p); S[w] += 1.0 / p
logD = math.log(D)
thr = 8.0 / logD
bad = S > thr
runs, cur = [], 0
for b in bad:
    cur = cur + 1 if b else 0
    if cur: runs.append(cur)
maxrun = max(runs) if runs else 0
print(f"z={z} L={L} D={D}: windows={nw}")
print(f"  S_kill: avg*logD={S.mean()*logD:.3f} (Lemma E predicts <=~1+eps)")
print(f"  p95*logD={np.percentile(S,95)*logD:.3f} max*logD={S.max()*logD:.3f}")
print(f"  bad (S>8/logD={thr:.3f}): {bad.mean():.3%} of windows (bound 25%)")
print(f"  max bad-run length: {maxrun} windows (= {maxrun*D} integers; D^1.2={D**1.2:.0f})")
