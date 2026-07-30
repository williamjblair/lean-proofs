r"""Erdős #848 finite-side scalability study (Deliverable 2).

Benchmarks + prototypes for pushing the finite verification toward
N0 ~ 10^9-10^10.  Components:

  universe : r_p mod p^2 for p = 1 mod 4 -- sympy sqrt_mod vs direct
             Tonelli (c^((p-1)/4) with c a QNR) + Hensel; full universe
             build wall-clock; outsider density |O(M)|/M.
  compat   : naive per-outsider compat sieve (one modular inverse per prime
             q <= sqrt(xM)); cost model alpha * pi(sqrt(xM)).
  hybrid   : per-x compat via small-q sieve (q <= S0) + large-square
             k-enumeration:  x*a+1 = k*s^2 with s > S0 forces
             k <= (xM+1)/S0^2 and s^2 = k^{-1} (mod x); enumerate s in the
             O(2^omega(x)) square-root classes mod x.  Every candidate hit
             is genuinely non-squarefree (s^2 | xa+1, s >= 2 -- primality of
             s NOT required), and every hit with a prime witness q > S0 is
             found (k = (xa+1)/q^2), so hybrid = naive exactly.
             Cost ~ pi(S0) inverses + K0 sqrt_mod(x) + 2^omega * 2M/S0
             candidates, vs pi(sqrt(xM)) inverses for naive.
  batchq   : the prompt's global large-q design: for fixed q (q^2 > M) get
             a0(x) = -x^{-1} mod q^2 for ALL outsiders x at once via
             Montgomery batch inversion (1 modpow + 3|O| mulmods) instead
             of |O| modpows.
  nuglob   : empirical test that the GLOBAL case-1 matching restricted to
             compat(x) already covers the b0 deficit of every escalated
             outsider (the pair (a_i,b_i) argument is x-independent!) --
             evidence that the expensive per-x b1 matching could be
             replaced by one global object + an analytic lemma.
  project  : assemble measured constants into 16-core wall-clock
             projections for M = 10^8, 10^9, 10^10.

Usage: python finite_scale.py all --M 1000000
       python finite_scale.py hybrid --M 1000000 --sample 8
"""
from __future__ import annotations

import argparse
import json
import math
import os
import random
import sys
import time
from math import isqrt, gcd

import numpy as np

from finite_verify import (primes_upto, squarefree, build_universe_mask,
                           compat_mask, root_minus1_modp2, _root_minus1_modp,
                           m7, m18, _ensure_sf_primes)


# ----------------------------------------------------------------------------
# (a) universe construction
# ----------------------------------------------------------------------------

def bench_universe(M: int) -> dict:
    print(f"--- universe benchmark, M = {M} ---")
    ps = [int(p) for p in primes_upto(min(M, 2 * 10 ** 6)) if p % 4 == 1]
    sample = ps if len(ps) <= 20000 else random.Random(1).sample(ps, 20000)

    from sympy import sqrt_mod as sympy_sqrt_mod
    t = time.perf_counter()
    for p in sample:
        sympy_sqrt_mod(-1, p)
    t_sympy = (time.perf_counter() - t) / len(sample)

    t = time.perf_counter()
    for p in sample:
        _root_minus1_modp(p)
    t_own = (time.perf_counter() - t) / len(sample)

    t = time.perf_counter()
    for p in sample[:5000]:
        root_minus1_modp2(p)
    t_lift = (time.perf_counter() - t) / 5000

    print(f"  sqrt(-1) mod p:  sympy {t_sympy*1e6:.1f} us/p, "
          f"direct c^((p-1)/4) {t_own*1e6:.1f} us/p "
          f"(x{t_sympy/t_own:.1f}); with Hensel lift {t_lift*1e6:.1f} us/p")

    t = time.perf_counter()
    U = build_universe_mask(M)
    t_build = time.perf_counter() - t
    dens = []
    for Mi in (10 ** 5, 10 ** 6, 10 ** 7):
        if Mi <= M:
            cls = np.zeros(Mi + 1, dtype=bool)
            cls[7::25] = True
            cls[18::25] = True
            nO = int((U[: Mi + 1] & ~cls).sum())
            dens.append((Mi, nO, nO / Mi))
            print(f"  |O({Mi:.0e})| = {nO}  density {nO/Mi:.5f}")
    print(f"  full universe build at M={M}: {t_build:.1f}s "
          f"(python; root computation is O(pi(M)/2) modexp, sieve marks "
          f"~0.052*M -- trivially C/parallel)")
    return {"t_sympy_us": t_sympy * 1e6, "t_own_us": t_own * 1e6,
            "t_lift_us": t_lift * 1e6, "t_build_s": t_build,
            "outsider_density": dens}


# ----------------------------------------------------------------------------
# (b) per-outsider compat: naive sieve cost
# ----------------------------------------------------------------------------

def bench_compat(M: int, n_sample: int = 12) -> dict:
    print(f"--- naive per-x compat sieve benchmark, M = {M} ---")
    U = build_universe_mask(M)
    cls = np.zeros(M + 1, dtype=bool)
    cls[7::25] = True
    cls[18::25] = True
    outs = np.flatnonzero(U & ~cls)
    primes_list = [int(p) for p in primes_upto(M)]
    rng = random.Random(848)
    xs = sorted(int(v) for v in rng.sample(list(outs), n_sample))
    rows = []
    for x in xs:
        t = time.perf_counter()
        cm = compat_mask(x, M, primes_list)
        dt = time.perf_counter() - t
        npr = np.searchsorted(primes_list, isqrt(x * M + 1), "right")
        rows.append((x, dt, int(npr), int((cm & U).sum())))
        print(f"  x={x:>9}  {dt*1e3:7.1f} ms   pi(sqrt(xM))={npr:>7}  "
              f"|compat&U|={rows[-1][3]:>7}  ({dt/npr*1e9:.0f} ns/prime)")
    alpha = np.mean([dt / npr for _, dt, npr, _ in rows])
    print(f"  cost model: t_x ~ {alpha*1e9:.0f} ns * pi(sqrt(xM))  (python)")
    return {"alpha_ns": alpha * 1e9, "rows": rows}


# ----------------------------------------------------------------------------
# (b') hybrid: small-q sieve + large-square k-enumeration
# ----------------------------------------------------------------------------

def compat_set_hybrid(x: int, M: int, primes_list: list[int], S0: int):
    """Exact compat(x) & [1,M] with per-prime work only up to S0.
    Returns (mask, stats)."""
    from sympy import sqrt_mod as sympy_sqrt_mod
    S0 = min(S0, isqrt(x * M + 1))
    marked = np.zeros(M + 1, dtype=bool)
    n_inv = 0
    for q in primes_list:
        if q > S0:
            break
        if x % q == 0:
            continue
        q2 = q * q
        a0 = q2 - pow(x, -1, q2)
        n_inv += 1
        if q2 <= M:
            marked[a0:: q2] = True
        elif a0 <= M:
            marked[a0] = True
    # large-square part: x*a+1 = k*s^2, s > S0  =>  k <= (xM+1)/S0^2,
    # s^2 = k^{-1} (mod x).  Any candidate with exact division is a genuine
    # non-squarefree witness (s^2 | xa+1); completeness for prime s > S0.
    K0 = (x * M + 1) // (S0 * S0)
    n_sqrt = n_cand = 0
    for k in range(1, K0 + 1):
        if gcd(k, x) != 1:
            continue
        n_sqrt += 1
        roots = sympy_sqrt_mod(pow(k, -1, x), x, all_roots=True) or []
        Qmax = isqrt((x * M + 1) // k)
        for r in roots:
            s = r
            if s < 2:
                s += x
            while s <= Qmax:
                if s > S0:
                    n_cand += 1
                    a = (k * s * s - 1) // x
                    if 1 <= a <= M:
                        marked[a] = True
                s += x
    return marked, {"n_inv": n_inv, "K0": int(K0), "n_sqrt": n_sqrt,
                    "n_cand": n_cand}


def bench_hybrid(M: int, n_sample: int = 6) -> dict:
    print(f"--- hybrid (small-q sieve + k-enumeration) benchmark, M = {M} ---")
    U = build_universe_mask(M)
    cls = np.zeros(M + 1, dtype=bool)
    cls[7::25] = True
    cls[18::25] = True
    outs = np.flatnonzero(U & ~cls)
    primes_list = [int(p) for p in primes_upto(M)]
    rng = random.Random(4242)
    xs = sorted(int(v) for v in rng.sample(list(outs[outs > M // 4]),
                                           n_sample))
    out = []
    for x in xs:
        t = time.perf_counter()
        cm_naive = compat_mask(x, M, primes_list)
        t_naive = time.perf_counter() - t
        # S0 ~ (x*M)^{1/3} * const balances pi(S0) against K0 sqrt_mod calls
        S0 = max(1000, int((x * M) ** (1 / 3)))
        t = time.perf_counter()
        cm_h, st = compat_set_hybrid(x, M, primes_list, S0)
        t_h = time.perf_counter() - t
        same = bool((cm_naive == cm_h).all())
        assert same, f"hybrid mismatch at x={x}"
        npr = int(np.searchsorted(primes_list, isqrt(x * M + 1), "right"))
        print(f"  x={x:>9} S0={S0:>7}: naive {t_naive*1e3:7.1f} ms "
              f"(pi={npr}), hybrid {t_h*1e3:7.1f} ms "
              f"(inv={st['n_inv']}, sqrtmod={st['n_sqrt']}, "
              f"cand={st['n_cand']})  EXACT-EQUAL={same}")
        out.append({"x": x, "S0": S0, "t_naive_ms": t_naive * 1e3,
                    "t_hybrid_ms": t_h * 1e3, **st, "pi_naive": npr})
    return {"rows": out}


# ----------------------------------------------------------------------------
# (b'') global large-q batching: Montgomery batch inversion over outsiders
# ----------------------------------------------------------------------------

def batch_inverse(vals: list[int], mod: int) -> list[int]:
    pref = [1] * (len(vals) + 1)
    acc = 1
    for i, v in enumerate(vals):
        acc = acc * v % mod
        pref[i + 1] = acc
    inv = pow(acc, -1, mod)
    out = [0] * len(vals)
    for i in range(len(vals) - 1, -1, -1):
        out[i] = pref[i] * inv % mod
        inv = inv * vals[i] % mod
    return out


def bench_batchq(M: int, n_q: int = 40) -> dict:
    print(f"--- large-q global batching benchmark, M = {M} ---")
    U = build_universe_mask(M)
    cls = np.zeros(M + 1, dtype=bool)
    cls[7::25] = True
    cls[18::25] = True
    outs = [int(v) for v in np.flatnonzero(U & ~cls)]
    print(f"  |O| = {len(outs)}")
    qlo = isqrt(M) + 1
    qs = [int(p) for p in primes_upto(3 * qlo) if p > qlo][:n_q]

    t = time.perf_counter()
    hits_a = 0
    for q in qs:
        q2 = q * q
        xs = [x for x in outs if x % q]
        for x in xs:
            a0 = q2 - pow(x, -1, q2)
            if a0 <= M:
                hits_a += 1
    t_pow = time.perf_counter() - t

    t = time.perf_counter()
    hits_b = 0
    for q in qs:
        q2 = q * q
        xs = [x for x in outs if x % q]
        invs = batch_inverse(xs, q2)
        for x, iv in zip(xs, invs):
            a0 = q2 - iv
            if a0 <= M:
                hits_b += 1
    t_batch = time.perf_counter() - t
    assert hits_a == hits_b
    per_pair_pow = t_pow / (len(qs) * len(outs))
    per_pair_batch = t_batch / (len(qs) * len(outs))
    print(f"  {len(qs)} primes q in ({qlo}, ...): hits(a0<=M) = {hits_a}")
    print(f"  per (q,x): pow(x,-1,q^2) {per_pair_pow*1e9:.0f} ns | "
          f"batch-inversion {per_pair_batch*1e9:.0f} ns "
          f"(x{per_pair_pow/per_pair_batch:.2f} python; in C the gap is "
          f"~10-20x: 3 mulmods vs one gcd-inverse)")
    return {"per_pair_pow_ns": per_pair_pow * 1e9,
            "per_pair_batch_ns": per_pair_batch * 1e9,
            "hits": hits_a, "n_q": len(qs), "n_out": len(outs)}


# ----------------------------------------------------------------------------
# nuglob: does the GLOBAL case-1 matching close all outsider escalations?
# ----------------------------------------------------------------------------

def replay_global_matching(cert: dict) -> list[tuple[int, int]]:
    match_a: dict[int, int] = {}
    match_b: dict[int, int] = {}
    for ev in cert["mixed_case"]["events"]:
        p = ev["path"]
        for i in range(0, len(p) - 1, 2):
            bb, aa = p[i], p[i + 1]
            old = match_b.pop(bb, None)
            if old is not None:
                match_a.pop(old, None)
            match_b[bb] = aa
            match_a[aa] = bb
    return sorted((a, b) for b, a in match_b.items())


def bench_nuglob(cert_path: str) -> dict:
    """For every escalated outsider x and EVERY b0-failing jump point N,
    check nu_glob(x,N) >= deficit(x,N), where nu_glob counts global case-1
    matching pairs with both endpoints in compat(x) and <= N, and
    deficit = b0(x,N) - m7(N).  (b1 with the global pairs closes N iff
    nu_glob >= deficit.)"""
    print(f"--- nu_glob test on {cert_path} (all fail points) ---")
    cert = json.load(open(cert_path))
    M = cert["M"]
    pairs_arr = np.array(replay_global_matching(cert))
    pmax = pairs_arr.max(axis=1)
    U = build_universe_mask(M)
    primes_list = [int(p) for p in primes_upto(M)]
    esc = cert["outsider_case"]["escalations"]
    closed_x = 0
    n_pts = n_pts_closed = 0
    worst = None
    t = time.perf_counter()
    for r in esc:
        x = r["x"]
        cm = compat_mask(x, M, primes_list)
        # recompute b0 jump-point margins (as in check_outsider)
        Ly = np.flatnonzero(cm & U)
        Ly = Ly[Ly != x]
        below = int((Ly < x).sum())
        Ns = np.concatenate(([x], Ly[Ly > x])).astype(np.int64)
        counts = 1 + below + np.arange(len(Ns), dtype=np.int64)
        deficits = counts - (Ns + 18) // 25
        fail = deficits > 0
        Nf, df = Ns[fail], deficits[fail]
        # nu_glob prefix counts over both-compat pairs sorted by max endpoint
        both = cm[pairs_arr[:, 0]] & cm[pairs_arr[:, 1]]
        mx = np.sort(pmax[both])
        nug = np.searchsorted(mx, Nf, "right")
        marg = nug - df
        n_pts += len(Nf)
        n_pts_closed += int((marg >= 0).sum())
        ok = bool((marg >= 0).all())
        closed_x += ok
        k = int(marg.argmin())
        if worst is None or marg[k] < worst[1]:
            worst = (x, int(marg[k]), int(nug[k]), int(df[k]), int(Nf[k]))
    print(f"  nu_glob >= deficit at ALL fail points for {closed_x}/{len(esc)}"
          f" escalated x; points closed {n_pts_closed}/{n_pts} "
          f"({time.perf_counter()-t:.1f}s)")
    print(f"  worst (x, nu_glob-deficit, nu_glob, deficit, N): {worst}")
    return {"closed_x": closed_x, "total_x": len(esc), "pts": n_pts,
            "pts_closed": n_pts_closed, "worst": worst}


# ----------------------------------------------------------------------------
# projections
# ----------------------------------------------------------------------------

def project() -> None:
    """16-core wall-clock projections from measured constants + a stated
    C cost model.  Two variants of the escalation phase:
      b1-direct : per-x greedy matchings sized to the b0 deficit
                  (sum_x deficit ~ 9.2e-6 * M^2 pairs, measured at 1e5),
                  each matched pair costing ~1.6 certified squarefree
                  tests of v ~ M^2 (trial division to v^{1/3}).
      b1-nuglob : count the global case-1 matching restricted to compat(x)
                  during the b0 enumeration (measured to cover 574/580
                  escalations at 1e5, residual deficits ~200x smaller).
    """
    print("--- projections (formulas in finite_report.md) ---")
    OUT_DENS = 0.0251                   # |O|/M, measured stable 1e5..1e7
    DEFICIT_C = 91919 / (10 ** 5) ** 2  # sum_x b0 deficit ~ c*M^2 (1e5)
    NUGLOB_SAVE = 50                    # residual pair factor (1e5: ~54x,
                                        # 28/580 x need top-ups <= 87 pairs)
    ROW_FRAC = 0.40                     # case-1 rows actually demanded
    NS_INV = 60        # ns  modular inverse mod q^2 (Lehmer gcd, C)
    NS_MUL = 3         # ns  mulmod (__int128)
    NS_SQRTMOD = 2000  # ns  all sqrt roots mod composite x (Tonelli+CRT)
    NS_DIV = 1.2       # ns  one trial-division step in squarefree()
    for M in (10 ** 8, 10 ** 9, 10 ** 10):
        nO = OUT_DENS * M
        t_uni = (M / math.log(M) / 2 * 30 * NS_MUL + 0.052 * M) * 1e-9
        # hybrid b0 per x (x~M): balance pi(S0)*NS_INV vs K0*NS_SQRTMOD
        S0 = (2 * (NS_SQRTMOD / NS_INV) * M * M * 14) ** (1 / 3)
        piS0 = S0 / math.log(S0)
        K0 = M * M / S0 ** 2
        t_b0_x = (piS0 * NS_INV + K0 * NS_SQRTMOD + 16 * M / S0 * 5) * 1e-9
        t_b0 = nO * t_b0_x
        n_pairs = DEFICIT_C * M ** 2
        cbrt = (M * M) ** (1 / 3)
        t_test = (cbrt / math.log(cbrt)) * NS_DIV * 1e-9
        t_b1_direct = n_pairs * 1.6 * t_test
        t_b1_nuglob = t_b1_direct / NUGLOB_SAVE + t_b0  # counting ~ b0 cost
        t_c1 = ROW_FRAC * (M / 25) * t_b0_x             # hybrid row sieves
        for tag, t_b1 in (("direct", t_b1_direct), ("nuglob", t_b1_nuglob)):
            tot = (t_uni + t_b0 + t_b1 + t_c1) / 16
            print(f"  M=1e{round(math.log10(M))} [{tag:6s}] "
                  f"universe {t_uni/3600:8.2g} ch | "
                  f"b0 {t_b0/3600:8.3g} ch | b1 {t_b1/3600:9.3g} ch | "
                  f"case1 {t_c1/3600:8.3g} ch | wall/16c "
                  f"{tot/86400:9.3g} days")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("what", choices=["universe", "compat", "hybrid", "batchq",
                                     "nuglob", "project", "all"])
    ap.add_argument("--M", type=int, default=10 ** 6)
    ap.add_argument("--sample", type=int, default=8)
    ap.add_argument("--cert", type=str, default="finite_cert_100000.json")
    args = ap.parse_args()
    _ensure_sf_primes(args.M * args.M + 1)
    res = {}
    if args.what in ("universe", "all"):
        res["universe"] = bench_universe(args.M)
    if args.what in ("compat", "all"):
        res["compat"] = bench_compat(args.M, args.sample)
    if args.what in ("hybrid", "all"):
        res["hybrid"] = bench_hybrid(args.M, min(args.sample, 6))
    if args.what in ("batchq", "all"):
        res["batchq"] = bench_batchq(args.M)
    if args.what in ("nuglob", "all") and os.path.exists(args.cert):
        res["nuglob"] = bench_nuglob(args.cert)
    if args.what in ("project", "all"):
        project()


if __name__ == "__main__":
    main()
