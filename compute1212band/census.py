"""Band-limited exact search over H: trap census + escape-cost measurement.

Bands are [3, Y].  b = 3 is the floor of H, so a band can only be extended
UPWARD; there is no downward direction to report.

Two modes:

  ratchet  ride band Y until the search stalls at a confirmed trap column a*,
           then bisect the minimal number of extra rows dY so that the search
           reaches a*+2 (delta_pass) and sustains L further columns (delta_L).
           Keep the enlarged band and continue.  Reachability is monotone in
           the band (extra rows only add vertices and edges), so bisection is
           valid.

  restart  fixed band Y: on a stall, record the trap, then restart from the
           leftmost vertex of the widest-spanning component of the next seed
           box.  Measures pure trap density / run length at fixed Y.

Blocks are W hub-columns wide and the search is EXACT inside a block (free
backtracking); the interface carries the exact reachable row-set.  Every stall
is re-confirmed from the previous block checkpoint over a longer span before
being recorded, which removes block-boundary artefacts.  Escape costs are
measured from a checkpoint BACK columns behind the trap, so backtracking
further than BACK columns is not explored: reported dY are upper bounds.
"""
import argparse
import json
import time
import numpy as np
from hub import (prime_mask, Builder, TBlock, reach_t, maxcol_t,
                 odd_prime_factors)

BACK = 1200      # columns of backtrack room allowed behind a trap when escaping
MARGIN = 400     # extra columns built past the escape target


def best_start(B, nb, a_lo, SB):
    """(a, rows, span_end) for the largest column-span component of the box
    starting at column a_lo, SB columns wide."""
    from scipy.sparse import coo_matrix
    from scipy.sparse.csgraph import connected_components
    aa, V, Hm, Vm = B.build(a_lo, SB, nb=nb)
    vid = (np.cumsum(V.ravel(), dtype=np.int32) - 1).reshape(nb, SB)
    nv = int(vid[-1, -1]) + 1
    vf = vid.ravel()
    fh = np.flatnonzero(Hm.ravel())
    fv = np.flatnonzero(Vm.ravel())
    s = np.concatenate([vf[fh], vf[fv]])
    d = np.concatenate([vf[fh + 1], vf[fv + SB]])
    g = coo_matrix((np.ones(s.size, np.int8), (s, d)), shape=(nv, nv))
    n, lab = connected_components(g, directed=False)
    cols = np.broadcast_to(np.arange(SB, dtype=np.int32),
                           (nb, SB)).ravel()[V.ravel()]
    cmax = np.full(n, -1, np.int32)
    cmin = np.full(n, SB, np.int32)
    np.maximum.at(cmax, lab, cols)
    np.minimum.at(cmin, lab, cols)
    c = int(np.argmax(cmax - cmin))
    i0 = int(cmin[c])
    j0 = np.array([j for j in np.flatnonzero(V[:, i0]) if lab[vid[j, i0]] == c])
    return int(aa[i0]), j0, int(aa[int(cmax[c])])


def diagnose(T, i_star, R, nb, bb):
    a_star = int(T.aa[i_star])
    openj = np.flatnonzero(T.Ht[i_star, :nb])
    rj = np.flatnonzero(R[i_star])
    mt = T.Mt[i_star, :nb - 1]
    d = {
        "a_star": a_star,
        "band": int(2 * nb - 1),
        "open_rows": int(openj.size),
        "reach_rows": int(rj.size),
        "vertices_in_col": int(T.Vt[i_star, :nb].sum()),
        "vert_edges_in_col": int(mt.sum()),
        "vert_runs": int((~mt).sum()) + 1,
        "is_wall": bool(openj.size == 0),
        "col_div3": bool(a_star % 3 == 0),
        "col_div5": bool(a_star % 5 == 0),
        "col_div7": bool(a_star % 7 == 0),
        "spf_a": int(min(odd_prime_factors(a_star) or [a_star])),
        "spf_a1": int(min(odd_prime_factors(a_star + 1) or [0])),
        "spf_a2": int(min(odd_prime_factors(a_star + 2) or [0])),
    }
    if rj.size:
        d["reach_b_min"] = int(bb[rj[0]])
        d["reach_b_max"] = int(bb[rj[-1]])
        d["frontier_vert_moves"] = int(mt[rj[rj < nb - 1]].sum())
    if openj.size and rj.size:
        d["open_b_min"] = int(bb[openj[0]])
        d["open_b_max"] = int(bb[openj[-1]])
        d["row_gap"] = int(np.abs(bb[openj][None, :] - bb[rj][:, None]).min())
    return d


def run(Y, Amax, W, L, Ycap, budget, mode, a_start=0, verbose=True):
    t0 = time.time()
    pr = prime_mask(Amax + 8 * W + 16)
    Bcap = Builder(Ycap, pr)
    nb_base = (Y - 1) // 2 + 1
    nbcap = Bcap.nb
    bb = Bcap.bb
    SB = min(16000, max(2500, 24_000_000 // max(nb_base, 1)))

    if mode == "flood":
        a0 = a_start or 3
        a0 += (a0 % 2 == 0)
        j0, aspan = np.arange(nb_base), a0
    else:
        a0, j0, aspan = best_start(Bcap, nb_base, 1, SB)
    if verbose:
        print(f"[Y={Y} {mode}] seedbox a<={2*SB-1}: start a={a0} "
              f"rows={[int(bb[j]) for j in j0][:5]} spans to a={aspan}", flush=True)

    c_prev, F_prev = a0, j0
    c, F = a0, j0
    nb_cur = nb_base
    traps, runs = [], []
    run_start, reach_max, nblk = a0, a0, 0

    while c < Amax and len(traps) < budget:
        na = min(W, (Amax - c) // 2 + 1)
        if na < 8:
            break
        T = TBlock(*Bcap.build(c, na, nb=nb_cur))
        R = reach_t(T, F, nb_cur)
        if R[na - 1].any():
            c_prev, F_prev = c, F
            c = int(T.aa[na - 1])
            F = np.flatnonzero(R[na - 1])
            reach_max = max(reach_max, c)
            nblk += 1
            if verbose and nblk % 20 == 0:
                print(f"   a={c} band={2*nb_cur-1} front={F.size} "
                      f"({time.time()-t0:.0f}s)", flush=True)
            continue

        # ---- stall: confirm from the previous block checkpoint, longer span
        i_s = maxcol_t(R)
        a_star = int(T.aa[i_s])
        span = (a_star - c_prev) // 2 + 1 + L + MARGIN
        T2 = TBlock(*Bcap.build(c_prev, span, nb=nb_cur))
        R2 = reach_t(T2, F_prev, nb_cur)
        i2 = maxcol_t(R2)
        a2 = int(T2.aa[i2])
        if a2 > a_star and i2 == span - 1:   # block-boundary artefact
            c_prev, F_prev = c, F
            c = a2
            F = np.flatnonzero(R2[i2])
            reach_max = max(reach_max, c)
            continue
        # always adopt the confirmation block: it starts BACK/W columns earlier
        T, R, a_star, i_s = T2, R2, a2, i2
        reach_max = max(reach_max, a_star)
        d = diagnose(T, i_s, R, nb_cur, bb)
        d["from_checkpoint"] = int(T.aa[0])
        d["backtrack_cols"] = int(i_s)
        d["run_start"] = int(run_start)
        d["run_len_cols"] = int((a_star - run_start) // 2)
        runs.append(d["run_len_cols"])

        if mode == "restart":
            traps.append(d)
            if verbose:
                print(f"  TRAP a*={a_star} run={d['run_len_cols']}c "
                      f"open={d['open_rows']} reach={d['reach_rows']} "
                      f"wall={d['is_wall']} 3|a={d['col_div3']}", flush=True)
            a0b, j0b, _ = best_start(Bcap, nb_cur, a_star + 2, SB)
            c_prev, F_prev = a0b, j0b
            c, F = a0b, j0b
            run_start = a0b
            continue

        # ---- escape: bisect on band size from a checkpoint BACK cols behind
        ib = max(0, i_s - BACK)
        while ib > 0 and not R[ib].any():
            ib -= 1
        cE = int(T.aa[ib])
        seedE = np.flatnonzero(R[ib])
        spanE = (a_star - cE) // 2 + 1 + L + MARGIN
        TE = TBlock(*Bcap.build(cE, spanE, nb=nbcap))
        cache = {}

        def mc(nbq):
            if nbq not in cache:
                Rq = reach_t(TE, seedE, nbq)
                cache[nbq] = (int(TE.aa[maxcol_t(Rq)]), Rq)
            return cache[nbq]

        def gallop(target):
            if mc(nb_cur)[0] >= target:
                return nb_cur
            lo, step, hi = nb_cur, 1, None
            while True:
                q = min(nb_cur + step, nbcap)
                if mc(q)[0] >= target:
                    hi = q
                    break
                lo = q
                if q == nbcap:
                    return None
                step *= 2
            while lo + 1 < hi:
                mid = (lo + hi) // 2
                if mc(mid)[0] >= target:
                    hi = mid
                else:
                    lo = mid
            return hi

        nb_pass = gallop(a_star + 2)
        nb_L = gallop(a_star + 2 * L)
        d["delta_pass"] = None if nb_pass is None else int(2 * (nb_pass - nb_cur))
        d["delta_L"] = None if nb_L is None else int(2 * (nb_L - nb_cur))
        d["L_cols"] = L
        d["cap_band"] = int(2 * nbcap - 1)
        d["cap_reach"] = int(mc(nbcap)[0]) if nb_L is None else None
        d["escape_from"] = cE
        traps.append(d)
        if verbose:
            print(f"  TRAP a*={a_star} band={d['band']} run={d['run_len_cols']}c "
                  f"open={d['open_rows']} reach={d['reach_rows']} "
                  f"wall={d['is_wall']} 3|a={d['col_div3']} "
                  f"dY_pass={d['delta_pass']} dY_L={d['delta_L']} "
                  f"({time.time()-t0:.0f}s)", flush=True)
        if mode == "flood":
            # fixed band: restart from a maximally generous frontier just past
            # the trap (all vertices of column a*+2 in the base band)
            c = a_star + 2
            F = np.arange(nb_base)
            c_prev, F_prev = c, F
            run_start = c
            reach_max = max(reach_max, c)
            del cache, TE
            continue
        if nb_L is None:
            break
        RL = mc(nb_L)[1]
        i_land = int((a_star + 2 * L - cE) // 2)   # the verified sustain point
        i_land = min(i_land, maxcol_t(RL))
        nb_cur = nb_L
        c = int(TE.aa[i_land])
        F = np.flatnonzero(RL[i_land])
        run_start = c
        i_bk = max(0, i_land - BACK)
        while i_bk > 0 and not RL[i_bk].any():
            i_bk -= 1
        c_prev, F_prev = int(TE.aa[i_bk]), np.flatnonzero(RL[i_bk])
        reach_max = max(reach_max, c)
        del cache, TE
    return {
        "Y": Y, "Amax": Amax, "W": W, "L": L, "Ycap": Ycap, "mode": mode,
        "start": a0, "reach_max": int(reach_max),
        "final_band": int(2 * nb_cur - 1),
        "n_traps": len(traps), "traps": traps, "runs": runs,
        "seconds": round(time.time() - t0, 1),
    }


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("Y", type=int)
    p.add_argument("Amax", type=int)
    p.add_argument("--W", type=int, default=5000)
    p.add_argument("--L", type=int, default=1000)
    p.add_argument("--cap", type=int, default=0)
    p.add_argument("--budget", type=int, default=60)
    p.add_argument("--mode", default="ratchet")
    p.add_argument("--a0", type=int, default=0)
    p.add_argument("--out", default="")
    A = p.parse_args()
    cap = A.cap or max(4 * A.Y, A.Y + 2000)
    res = run(A.Y, A.Amax, A.W, A.L, cap, A.budget, A.mode, A.a0)
    print(json.dumps({k: v for k, v in res.items()
                      if k not in ("traps", "runs")}, indent=1))
    if A.out:
        json.dump(res, open(A.out, "w"), indent=1)
        print("wrote", A.out)
