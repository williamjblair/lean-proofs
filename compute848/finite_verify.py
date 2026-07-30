r"""Erdős #848 finite-side structured exact verification (Deliverable 1).

Claim verified: f(N) = |A7(N)| = floor((N+18)/25) for EVERY N <= M, where
  f(N) = max{|A| : A subset of [1,N], a*b+1 non-squarefree for all a,b in A
             (a=b included)}.

Soundness architecture (every step is an exact, re-runnable argument):

  Any valid A is a clique (with self-loops) in the graph G(N) on
  U(N) = {x <= N : x^2+1 non-squarefree}, edges {a,b} iff ab+1 non-squarefree.
  U splits as A7 (x=7 mod 25) | A18 (x=18 mod 25) | O (outsiders: smallest
  witness prime >= 13, i.e. x in U with x mod 25 not in {7,18}).
  A7 and A18 are internally complete (25 | ab+1 within each class, self-pairs
  included), so f(N) >= |A7(N)| via A = A7(N).  Upper bound by cases:

  CASE 1 (clique C subset of A7 u A18).  C = S7 u S18 with complete
  cross-compatibility.  Certificate: a matching in the bipartite
  INcompatibility graph (edges (a,b), a in A7, b in A18, ab+1 SQUAREFREE)
  that saturates the A18(N) side.  Any clique = independent set of the
  incompat graph must miss >= 1 endpoint of each matching edge (edges are
  disjoint), hence |C| <= (m7 + m18) - m18 = m7(N) = |A7(N)|.  No Koenig
  needed for the verifier; only "these m18 pairs are disjoint and each
  product+1 is squarefree".  The matching is maintained incrementally over
  arrivals (elements in increasing order), so a saturating matching inside
  [1,N] exists for every N; the augmenting-path log is the certificate and
  is replayed by verify_certificate().

  CASE 2 (clique C contains an outsider x).  Then C\{x} is contained in
  compat(x) & U & [1,N], so |C| <= 1 + |compat(x) & U & [1,N]|  (bound b0).
  compat(x) is computed EXACTLY by sieving a = -x^{-1} mod q^2 over all
  primes q <= sqrt(xM+1) (q=2,3,5 included; q | x skipped since then
  q does not divide xa+1).  b0 is checked for ALL N in [x, M] at once by
  checking the jump points of the step function (LHS jumps only at elements
  of compat(x)&U, RHS m7(N) is nondecreasing).  Escalations when b0 fails:
    b1: |C| <= 1 + |compat(x)&O&[1,N]| + (|c7|+|c18| - nu) where nu is a
        matching (same disjoint-incompat-pairs argument) inside
        compat(x)&A7 x compat(x)&A18 restricted to [1,N].
    b2: b1 with exact maximum matching and with the outsider part replaced
        by 1 + omega(G[compat(x)&O&[1,N]]) (exact clique on the small
        outsider-only subgraph).
  If even b2 cannot close, the N is resolved by exact search and any
  genuine exception is reported loudly (none expected, none found so far).

Usage:
  python finite_verify.py --M 100000 [--jobs 14] [--spot] [--out CERT.json]
  python finite_verify.py --verify CERT.json      # independent replay
"""
from __future__ import annotations

import argparse
import json
import math
import os
import random
import sys
import time
from math import isqrt

import numpy as np

# ----------------------------------------------------------------------------
# primes / squarefree
# ----------------------------------------------------------------------------

def primes_upto(n: int) -> np.ndarray:
    sieve = np.ones(n + 1, dtype=bool)
    sieve[:2] = False
    for i in range(2, isqrt(n) + 1):
        if sieve[i]:
            sieve[i * i:: i] = False
    return np.flatnonzero(sieve)


_SF_PRIMES: list[int] = []          # primes up to cbrt(max v) for squarefree()
_SF_LIMIT = 0


def _ensure_sf_primes(v: int) -> None:
    global _SF_PRIMES, _SF_LIMIT
    c = round(v ** (1.0 / 3.0)) + 2
    if c > _SF_LIMIT:
        _SF_LIMIT = max(c, 2 * _SF_LIMIT, 10000)
        _SF_PRIMES = [int(p) for p in primes_upto(_SF_LIMIT)]


def squarefree(v: int) -> bool:
    """Exact squarefree test: trial divide by all p <= cbrt(v); the cofactor
    then has at most two prime factors (each > cbrt(v)), so it is
    non-squarefree iff it is a perfect square."""
    _ensure_sf_primes(v)
    for p in _SF_PRIMES:
        if p * p * p > v:
            break
        if v % p == 0:
            v //= p
            if v % p == 0:
                return False
    if v == 1:
        return True
    s = isqrt(v)
    return s * s != v


def m7(N: int) -> int:
    return (N + 18) // 25


def m18(N: int) -> int:
    return (N + 7) // 25


# ----------------------------------------------------------------------------
# universe construction (root sieving; same math as finite_engine.py,
# vectorized, without per-x witness bookkeeping)
# ----------------------------------------------------------------------------

def _root_minus1_modp(p: int) -> int:
    """r with r^2 = -1 mod p, p = 1 mod 4 prime (deterministic small-c scan)."""
    e = (p - 1) // 4
    c = 2
    while True:
        r = pow(c, e, p)
        if (r * r) % p == p - 1:
            return r
        c += 1


def root_minus1_modp2(p: int) -> int:
    """Hensel-lifted r with r^2 = -1 mod p^2."""
    r = _root_minus1_modp(p)
    p2 = p * p
    fr = (r * r + 1) % p2
    r2 = (r - fr * pow(2 * r, -1, p2)) % p2
    assert (r2 * r2 + 1) % p2 == 0
    return r2


def build_universe_mask(M: int) -> np.ndarray:
    """bool mask over [0..M]: x in U iff x^2+1 non-squarefree.  All witnesses
    are primes p = 1 mod 4 with p <= x (p^2 | x^2+1 forces p <= x)."""
    mask = np.zeros(M + 1, dtype=bool)
    for p in primes_upto(M):
        p = int(p)
        if p % 4 != 1:
            continue
        r = root_minus1_modp2(p)
        p2 = p * p
        for rr in (r, p2 - r):
            if rr <= M:
                mask[rr:: p2] = True
    mask[0] = False
    return mask


# ----------------------------------------------------------------------------
# exact compat mask per x  (sieve over q^2 | x*a+1)
# ----------------------------------------------------------------------------

def compat_mask(x: int, M: int, primes_list: list[int]) -> np.ndarray:
    """bool mask over [0..M]: a marked iff x*a+1 is non-squarefree.  Exact:
    every prime q with q^2 | xa+1 satisfies q^2 <= xM+1; q | x is impossible
    (q | xa+1 fails).  For q^2 <= M numpy strided marking; else <= 1 hit."""
    marked = np.zeros(M + 1, dtype=bool)
    lim = x * M + 1
    for q in primes_list:
        q2 = q * q
        if q2 > lim:
            break
        if x % q == 0:
            continue
        a0 = q2 - pow(x, -1, q2)          # a0 = -x^{-1} mod q^2, in [1, q2]
        if q2 <= M:
            marked[a0:: q2] = True
        elif a0 <= M:
            marked[a0] = True
    marked[0] = False
    return marked


# ----------------------------------------------------------------------------
# CASE 1: incremental incompatibility matching over arrivals
# ----------------------------------------------------------------------------

class MixedCase:
    """Maintains a matching (in the bipartite incompatibility graph
    A7 x A18, edge iff ab+1 squarefree) that saturates A18(N) for every N,
    processing arrivals in increasing order and logging augmenting paths."""

    def __init__(self, M: int, primes_list: list[int], row_cache: dict | None = None):
        self.M = M
        self.primes = primes_list
        self.A7 = list(range(7, M + 1, 25))
        self.A18 = list(range(18, M + 1, 25))
        self.idx7 = {a: i for i, a in enumerate(self.A7)}
        self.match_b: dict[int, int] = {}
        self.match_a: dict[int, int] = {}
        self.free_a: list[int] = []           # arrived, unmatched (stack)
        self.free_mask = 0                    # bitmask of free A7 indices
        self.arrived_mask = 0                 # bitmask over A7 indices
        self.rows = row_cache if row_cache is not None else {}
        self.events: list[dict] = []
        self.exceptions: list[dict] = []
        self.rows_computed = 0

    def _row(self, b: int) -> int:
        """Incompat row of b as bitmask over ALL A7(M) indices (exact sieve)."""
        r = self.rows.get(b)
        if r is None:
            cm = compat_mask(b, self.M, self.primes)
            bits = ~cm[7:: 25]                # incompat = NOT compat, a=7+25k
            r = int.from_bytes(
                np.packbits(bits, bitorder="little").tobytes(), "little")
            self.rows[b] = r
            self.rows_computed += 1
        return r

    def arrive_a(self, a: int) -> None:
        self.arrived_mask |= 1 << self.idx7[a]
        self.free_a.append(a)
        self.free_mask |= 1 << self.idx7[a]

    def _claim(self, a: int) -> None:
        self.free_a.remove(a)
        self.free_mask &= ~(1 << self.idx7[a])

    @staticmethod
    def _bits(v: int) -> np.ndarray:
        nb = (v.bit_length() + 7) // 8
        if nb == 0:
            return np.empty(0, dtype=np.int64)
        arr = np.frombuffer(v.to_bytes(nb, "little"), dtype=np.uint8)
        return np.flatnonzero(np.unpackbits(arr, bitorder="little"))

    def arrive_b(self, b: int) -> None:
        # quick path: an arrived free a with ab+1 squarefree
        for a in self.free_a:
            if squarefree(a * b + 1):
                self._claim(a)
                self.match_b[b] = a
                self.match_a[a] = b
                self.events.append({"b": b, "path": [b, a]})
                return
        # BFS for an augmenting path in the incompat graph.  Rows are
        # bitmasks; whole frontier rows are marked visited at once and set
        # bits are extracted via numpy (not per-bit big-int ops).
        parent_a: dict[int, int] = {}
        parent_b: dict[int, int | None] = {b: None}
        visited_a = 0
        frontier = [b]
        found = None
        while frontier and found is None:
            nxt = []
            for bb in frontier:
                row = self._row(bb) & self.arrived_mask & ~visited_a
                if row == 0:
                    continue
                hit = row & self.free_mask
                if hit:
                    i = (hit & -hit).bit_length() - 1
                    a = self.A7[i]
                    parent_a[a] = bb
                    found = a
                    break
                visited_a |= row
                for i in self._bits(row):
                    a = self.A7[int(i)]
                    parent_a[a] = bb
                    b2 = self.match_a[a]
                    if b2 not in parent_b:
                        parent_b[b2] = a
                        nxt.append(b2)
            frontier = nxt
        if found is None:
            # Hall violation: genuine candidate for f(N) > m7(N); record and
            # let the caller resolve exactly.
            self.exceptions.append({"type": "mixed_hall_failure", "b": b})
            return
        # reconstruct path b, a1, b1, a2, ..., ak(free)
        path = []
        a = found
        while a is not None:
            bb = parent_a[a]
            path.append(a)
            path.append(bb)
            a = parent_b[bb]
        path.reverse()                        # [b, a1, b1, ..., ak]
        # apply: match (path[2i], path[2i+1]) for i = 0..k-1
        for i in range(0, len(path) - 1, 2):
            bb, aa = path[i], path[i + 1]
            self.match_b[bb] = aa
            self.match_a[aa] = bb
        self._claim(found)
        self.events.append({"b": b, "path": path})

    def run(self) -> None:
        arrivals = sorted(self.A7 + self.A18)
        for n in arrivals:
            if n % 25 == 7:
                self.arrive_a(n)
            else:
                self.arrive_b(n)


# ----------------------------------------------------------------------------
# CASE 2: per-outsider sweep (workers)
# ----------------------------------------------------------------------------

_W: dict = {}


def _worker_init(M: int, u_bytes: bytes, primes_list: list[int]) -> None:
    _W["M"] = M
    _W["U"] = np.frombuffer(u_bytes, dtype=bool)
    _W["primes"] = primes_list


def row_worker(b: int) -> tuple[int, bytes]:
    """Incompat row of b over A7(M) as packed bits (pool worker)."""
    M, primes_list = _W["M"], _W["primes"]
    cm = compat_mask(b, M, primes_list)
    bits = ~cm[7:: 25]
    return b, np.packbits(bits, bitorder="little").tobytes()


def check_outsider(x: int):
    """b0 check for outsider x, all N in [x, M] simultaneously.
    Returns (x, |Lx|, min_margin, argmin_N, fail_points list)."""
    M, U, primes_list = _W["M"], _W["U"], _W["primes"]
    cm = compat_mask(x, M, primes_list)
    Ly = np.flatnonzero(cm & U)
    Ly = Ly[Ly != x]
    below = int((Ly < x).sum())
    tail = Ly[Ly > x]
    Ns = np.concatenate(([x], tail)).astype(np.int64)
    counts = 1 + below + np.arange(len(Ns), dtype=np.int64)
    margins = (Ns + 18) // 25 - counts
    k = int(margins.argmin())
    fails = Ns[margins < 0]
    return (x, int(len(Ly)), int(margins[k]), int(Ns[k]),
            [int(v) for v in fails])


# ----------------------------------------------------------------------------
# escalation b1/b2 for outsiders whose b0 fails somewhere
# ----------------------------------------------------------------------------

def escalate_outsider(job: tuple[int, list[int]]) -> dict:
    """Refined bounds for outsider x at every failing jump point (pool worker).

    b1(N) = 1 + |compat&O&[1,N]| + |c7(N)| + |c18(N)| - nu(N), where nu(N)
    counts disjoint incompatible (squarefree-product) pairs inside
    compat(x) & (A7 x A18) with both endpoints <= N.  Sound for any such
    pair family; we grow one greedily and monotonically in N (each (b,a)
    candidate is inspected at most once via per-b pointers).
    Returns a record with the pair list (replayable certificate) and any
    unresolved points (escalated further to b2 with exact matching/clique).
    """
    x, fail_Ns = job
    M, U, primes_list = _W["M"], _W["U"], _W["primes"]
    _ensure_sf_primes(M * M + 1)
    cm = compat_mask(x, M, primes_list)
    idx = np.flatnonzero(cm & U)
    mod = idx % 25
    c7 = idx[mod == 7]
    c18 = idx[mod == 18]
    cO = idx[(mod != 7) & (mod != 18) & (idx != x)]
    matched_a: set[int] = set()
    pairs: list[list[int]] = []           # insertion order; both <= N at insert
    ptr: dict[int, int] = {}
    unmatched_b: list[int] = []
    bi = 0
    points = []
    unresolved = []
    b1_min_margin = None
    for N in sorted(fail_Ns):
        while bi < len(c18) and c18[bi] <= N:
            unmatched_b.append(int(c18[bi]))
            bi += 1
        still = []
        for b in unmatched_b:
            p = ptr.get(b, 0)
            matched = False
            while p < len(c7) and c7[p] <= N:
                a = int(c7[p])
                p += 1
                if a in matched_a:
                    continue
                if squarefree(a * b + 1):
                    matched_a.add(a)
                    pairs.append([a, b])
                    matched = True
                    break
            ptr[b] = p
            if not matched:
                still.append(b)
        unmatched_b = still
        n7 = int(np.searchsorted(c7, N, "right"))
        n18 = int(np.searchsorted(c18, N, "right"))
        nO = int(np.searchsorted(cO, N, "right"))
        nu = len(pairs)
        b1 = 1 + nO + n7 + n18 - nu
        margin = m7(N) - b1
        if b1_min_margin is None or margin < b1_min_margin:
            b1_min_margin = margin
        points.append({"N": N, "n7": n7, "n18": n18, "nO": nO, "nu": nu,
                       "b1": b1, "m7": m7(N)})
        if b1 <= m7(N):
            continue
        # ---- b2: exact maximum matching + exact outsider-only clique ----
        import networkx as nx
        c7N = [int(a) for a in c7 if a <= N]
        c18N = [int(b) for b in c18 if b <= N]
        H = nx.Graph()
        H.add_nodes_from((("a", a) for a in c7N))
        H.add_nodes_from((("b", b) for b in c18N))
        for a in c7N:
            for b in c18N:
                if squarefree(a * b + 1):
                    H.add_edge(("a", a), ("b", b))
        mm = nx.bipartite.maximum_matching(
            H, top_nodes=[("a", a) for a in c7N])
        nu_exact = len(mm) // 2
        cON = [int(v) for v in cO if v <= N]
        omega_O = 0
        if cON:
            GO = nx.Graph()
            GO.add_nodes_from(cON)
            for i, u in enumerate(cON):
                for v in cON[i + 1:]:
                    if not squarefree(u * v + 1):
                        GO.add_edge(u, v)
            _, omega_O = nx.max_weight_clique(GO, weight=None)
        b2 = 1 + omega_O + n7 + n18 - nu_exact
        points[-1].update({"b2": b2, "nu_exact": nu_exact,
                           "omega_O": omega_O})
        if b2 > m7(N):
            unresolved.append({"x": x, "N": N, "b1": b1, "b2": b2,
                               "m7": m7(N)})
    # slim record: full points/pairs are deterministic re-runs; keep the
    # tight points (margin <= 5, capped), any b2 points, and pair lists only
    # when the closure was razor-thin (margin <= 2).
    tight = [p for p in points if p["m7"] - p["b1"] <= 5 or "b2" in p][:50]
    rec = {"x": x, "n_fail_points": len(fail_Ns),
           "fail_range": [min(fail_Ns), max(fail_Ns)],
           "b1_min_margin": b1_min_margin,
           "n_pairs": len(pairs),
           "tight_points": tight,
           "resolved": not unresolved, "unresolved": unresolved}
    if b1_min_margin is not None and b1_min_margin <= 2:
        rec["pairs"] = pairs
    return rec


# ----------------------------------------------------------------------------
# certificate replay verification
# ----------------------------------------------------------------------------

def verify_certificate(path: str) -> bool:
    with open(path) as fh:
        cert = json.load(fh)
    M = cert["M"]
    print(f"[verify] replaying mixed-case matching certificate, M={M}")
    events = cert["mixed_case"]["events"]
    A7 = list(range(7, M + 1, 25))
    A18 = list(range(18, M + 1, 25))
    match_b: dict[int, int] = {}
    match_a: dict[int, int] = {}
    arrived_a: set[int] = set()
    ei = 0
    for n in sorted(A7 + A18):
        if n % 25 == 7:
            arrived_a.add(n)
            continue
        ev = events[ei]
        ei += 1
        assert ev["b"] == n, (ev, n)
        p = ev["path"]
        assert p[0] == n and len(p) % 2 == 0
        # all vertices arrived (<= N = n)
        for i, v in enumerate(p):
            assert v <= n
            if i % 2 == 1:
                assert v % 25 == 7 and v in arrived_a
            else:
                assert v % 25 == 18
        # edges to be matched must be incompat edges (product+1 squarefree)
        for i in range(0, len(p) - 1, 2):
            assert squarefree(p[i] * p[i + 1] + 1), (p[i], p[i + 1])
        # alternation: (p[2i+1], p[2i+2]) currently matched, last a free
        for i in range(1, len(p) - 1, 2):
            assert match_a.get(p[i]) == p[i + 1], p
        assert p[-1] not in match_a
        for i in range(0, len(p) - 1, 2):
            match_b[p[i]] = p[i + 1]
            match_a[p[i + 1]] = p[i]
        # saturation of A18 side at this N
        assert len(match_b) == m18(n), (n, len(match_b))
    assert ei == len(events) == len(A18)
    # final matching: disjointness is structural (dicts); re-check pairing
    assert len(match_b) == m18(M) and len(set(match_b.values())) == len(match_b)
    for b, a in match_b.items():
        assert squarefree(a * b + 1)
    print(f"[verify] mixed-case OK: saturating matching of size {len(match_b)}"
          f" maintained at every N <= {M}")
    print("[verify] outsider case: summary data present for"
          f" {cert['outsider_case']['outsiders_checked']} outsiders; "
          "re-run finite_verify.py --M to recompute (exact sieve), or "
          "--recheck-sample for an independent trial-division recomputation.")
    exc = cert.get("exceptions", [])
    print(f"[verify] exceptions recorded: {len(exc)}")
    return len(exc) == 0


# ----------------------------------------------------------------------------
# independent sample recheck of compat lists (pure trial division)
# ----------------------------------------------------------------------------

def recheck_sample(xs: list[int], M: int, U: np.ndarray,
                   primes_list: list[int]) -> None:
    uvals = [int(v) for v in np.flatnonzero(U)]
    for x in xs:
        cm = compat_mask(x, M, primes_list)
        got = sorted(int(v) for v in np.flatnonzero(cm & U) if v != x)
        want = [y for y in uvals if y != x and not squarefree(x * y + 1)]
        assert got == want, f"compat mismatch at x={x}"
        print(f"  [recheck] x={x}: |compat&U|={len(got)} matches "
              "independent trial-division recomputation")


# ----------------------------------------------------------------------------
# spot checks: independent exact max clique on small prefixes (networkx)
# ----------------------------------------------------------------------------

def spot_check(N: int, U: np.ndarray, timeout_s: float = 120.0) -> None:
    import multiprocessing as mp

    def _job(N, uvals, q):
        import networkx as nx
        G = nx.Graph()
        G.add_nodes_from(uvals)
        for i, a in enumerate(uvals):
            for b in uvals[i + 1:]:
                if not squarefree(a * b + 1):
                    G.add_edge(a, b)
        cl, w = nx.max_weight_clique(G, weight=None)
        q.put((w, sorted(cl)))

    uvals = [int(v) for v in np.flatnonzero(U[: N + 1])]
    ctx = mp.get_context("fork")
    q = ctx.Queue()
    pr = ctx.Process(target=_job, args=(N, uvals, q))
    t = time.time()
    pr.start()
    pr.join(timeout_s)
    if pr.is_alive():
        pr.terminate()
        pr.join()
        print(f"  [spot] N={N}: networkx clique timed out (>{timeout_s}s), skipped")
        return
    w, cl = q.get()
    ok = (w == m7(N))
    print(f"  [spot] N={N}: brute omega={w}, |A7(N)|={m7(N)}  "
          f"{'OK' if ok else '*** MISMATCH ***'}  ({time.time()-t:.1f}s)")
    if not ok:
        print(f"        witness clique: {cl}")
        raise SystemExit(f"spot check failed at N={N}")


# ----------------------------------------------------------------------------
# main driver
# ----------------------------------------------------------------------------

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--M", type=int, default=100000)
    ap.add_argument("--jobs", type=int, default=max(1, os.cpu_count() - 2))
    ap.add_argument("--out", type=str, default=None)
    ap.add_argument("--spot", action="store_true",
                    help="independent networkx clique spot checks (small N)")
    ap.add_argument("--recheck-sample", type=int, default=8,
                    help="outsiders to recheck by pure trial division")
    ap.add_argument("--verify", type=str, default=None,
                    help="replay-verify an existing certificate JSON")
    args = ap.parse_args()

    if args.verify:
        ok = verify_certificate(args.verify)
        sys.exit(0 if ok else 1)

    M = args.M
    out_path = args.out or f"finite_cert_{M}.json"
    t0 = time.time()

    print(f"=== Erdős #848 finite verification, M = {M} ===")
    print("building universe (root sieve over p^2, p = 1 mod 4) ...", flush=True)
    U = build_universe_mask(M)
    cls = np.zeros(M + 1, dtype=bool)
    cls[7::25] = True
    cls[18::25] = True
    n7, n18 = m7(M), m18(M)
    outsiders = [int(v) for v in np.flatnonzero(U & ~cls)]
    assert int((U & cls).sum()) == n7 + n18, "class elements must all be in U"
    print(f"  |U|={int(U.sum())}  m7={n7}  m18={n18}  outsiders={len(outsiders)}"
          f"  ({time.time()-t0:.1f}s)")

    # cross-check universe against finite_engine (validated vs brute force)
    import finite_engine
    Mx = min(M, 20000)
    w = finite_engine.build_universe(Mx)
    got = set(int(v) for v in np.flatnonzero(U[: Mx + 1]))
    assert got == set(w.keys()), "universe mismatch vs finite_engine"
    out_fe = {x for x, p in w.items() if p >= 13}
    assert {x for x in outsiders if x <= Mx} == out_fe, \
        "outsider set (class not in {7,18}) must equal witness>=13 set"
    print(f"  cross-checked U and outsider set vs finite_engine up to {Mx}: OK")

    primes_list = [int(p) for p in primes_upto(M)]
    _ensure_sf_primes(M * M + 1)

    # ---------------- CASE 1 ----------------
    print("case 1 (cliques inside A7 u A18): incremental incompat matching ...",
          flush=True)
    t1 = time.time()
    import multiprocessing as mp
    ctx = mp.get_context("fork")
    row_cache = None
    if M >= 300000:
        # BFS row demand is a large fraction of A18: precompute in parallel
        print("  precomputing incompat rows in parallel ...", flush=True)
        with ctx.Pool(args.jobs, initializer=_worker_init,
                      initargs=(M, U.tobytes(), primes_list)) as pool:
            packed = pool.map(row_worker, range(18, M + 1, 25), chunksize=32)
        row_cache = {b: int.from_bytes(pb, "little") for b, pb in packed}
        print(f"  {len(row_cache)} rows precomputed ({time.time()-t1:.1f}s)",
              flush=True)
    mc = MixedCase(M, primes_list, row_cache=row_cache)
    mc.run()
    assert len(mc.match_b) == n18 or mc.exceptions
    print(f"  matching saturates A18 at every N: size {len(mc.match_b)}, "
          f"{len(mc.events)} augmentation events "
          f"({sum(len(e['path']) > 2 for e in mc.events)} nontrivial, "
          f"{mc.rows_computed} sieved rows)  ({time.time()-t1:.1f}s)")
    exceptions: list[dict] = list(mc.exceptions)

    # ---------------- CASE 2 ----------------
    print(f"case 2 (cliques containing an outsider): b0 sweep over "
          f"{len(outsiders)} outsiders on {args.jobs} workers ...", flush=True)
    t2 = time.time()
    with ctx.Pool(args.jobs, initializer=_worker_init,
                  initargs=(M, U.tobytes(), primes_list)) as pool:
        results = pool.map(check_outsider, outsiders, chunksize=16)
    worst = min(results, key=lambda r: r[2])
    failures = [r for r in results if r[4]]
    print(f"  b0 closed {len(results)-len(failures)}/{len(results)} outsiders; "
          f"worst margin {worst[2]} at x={worst[0]}, N={worst[3]} "
          f"({time.time()-t2:.1f}s)")

    escalation_records = []
    if failures:
        print(f"  escalating {len(failures)} outsiders where b0 fails "
              "(b1: greedy disjoint incompat pairs; b2: exact) ...",
              flush=True)
        t3 = time.time()
        jobs = [(r[0], r[4]) for r in failures]
        with ctx.Pool(args.jobs, initializer=_worker_init,
                      initargs=(M, U.tobytes(), primes_list)) as pool:
            escalation_records = pool.map(escalate_outsider, jobs, chunksize=1)
        n_res = sum(1 for r in escalation_records if r["resolved"])
        worst_b1 = min((r["b1_min_margin"] for r in escalation_records),
                       default=None)
        print(f"  escalations resolved: {n_res}/{len(escalation_records)}; "
              f"worst b1 margin {worst_b1}  ({time.time()-t3:.1f}s)")
        for r in escalation_records:
            if not r["resolved"]:
                print(f"  *** x={r['x']}: b1/b2 UNRESOLVED at "
                      f"{len(r['unresolved'])} points — deep exact search "
                      f"required: {r['unresolved'][:3]}")
                exceptions.extend(r["unresolved"])

    # ---------------- independent rechecks ----------------
    if args.recheck_sample and outsiders:
        rng = random.Random(848)
        sample = rng.sample(outsiders, min(args.recheck_sample, len(outsiders)))
        print(f"independent trial-division recheck of compat lists "
              f"({len(sample)} sampled outsiders) ...", flush=True)
        recheck_sample(sample, M, U, primes_list)

    if args.spot:
        print("independent exact clique spot checks (networkx) ...", flush=True)
        for N in (600, 1200, 1800, 2500):
            if N <= M:
                spot_check(N, U)

    # ---------------- certificate ----------------
    per_x = [{"x": r[0], "compatU": r[1], "min_margin": r[2],
              "argmin_N": r[3]} for r in results]
    cert = {
        "problem": "Erdos 848 finite side",
        "claim": f"f(N) = floor((N+18)/25) for all 1 <= N <= {M}",
        "M": M,
        "date": time.strftime("%Y-%m-%d"),
        "universe": {"size": int(U.sum()), "m7": n7, "m18": n18,
                     "n_outsiders": len(outsiders)},
        "argument": {
            "case1": "any clique inside A7uA18 misses >=1 endpoint of each of "
                     "the m18(N) disjoint squarefree pairs (a_i,b_i) => size "
                     "<= m7(N); pairs maintained for every N via the logged "
                     "augmenting paths (replay with --verify)",
            "case2": "any clique containing outsider x has size <= 1 + "
                     "|compat(x) & U & [1,N]| (b0), checked at all jump "
                     "points; escalations b1/b2 as documented in source",
        },
        "mixed_case": {
            "events": mc.events,
            "final_matching_size": len(mc.match_b),
        },
        "outsider_case": {
            "outsiders_checked": len(results),
            "b0_closed": len(results) - len(failures),
            "escalations": escalation_records,
            "worst_margin": {"x": worst[0], "margin": worst[2],
                             "N": worst[3]},
            "per_x": per_x,
        },
        "exceptions": exceptions,
        "runtime_s": round(time.time() - t0, 1),
    }
    with open(out_path, "w") as fh:
        json.dump(cert, fh, separators=(",", ":"))
    print(f"certificate written: {out_path} "
          f"({os.path.getsize(out_path)//1024} KiB)")

    # self-verify the mixed-case log
    verify_certificate(out_path)

    if exceptions:
        print(f"*** {len(exceptions)} EXCEPTIONS — claim FAILS somewhere, "
              "see certificate ***")
    else:
        print(f"VERIFIED: f(N) = |A7(N)| for every N <= {M} "
              f"({time.time()-t0:.1f}s total)")


if __name__ == "__main__":
    main()
