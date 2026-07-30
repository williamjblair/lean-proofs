"""Erdős #64 scan of the Potočnik–Spiga–Verret census of cubic vertex-transitive
graphs (Zenodo 6576526). For each graph, find a witness cycle of length exactly
2^k (4 <= 2^k <= n) — or flag the graph as a survivor (counterexample candidate).

Soundness design:
- Kills are certified by an explicit vertex list (checked: distinct vertices,
  consecutive adjacency, closing edge, length 2^k). We never trust census
  metadata (girth etc.) for a kill.
- Root-0 search first (complete for vertex-transitive graphs); if nothing is
  found for any length, escalate to an all-roots search for every length
  before declaring a survivor — so survivor status does not depend on the
  census's vertex-transitivity claim either.
- Lengths >= 64 use meet-in-the-middle; if a graph survives all lengths that
  MITM can reach, it is logged for deep analysis (needs_deep) rather than
  being silently passed.

Output: witnesses.jsonl.gz (one record per graph), survivors/needs_deep to
stdout + summary. An independent verifier (verify_witnesses.py) rechecks every
certificate from the raw sparse6.
"""
from __future__ import annotations
import gzip
import json
import sqlite3
import sys
import time
from collections import deque

MITM_MAX_HALF = 1 << 22   # cap on stored half-paths (memory guard)


# ---------------------------------------------------------------- sparse6

def parse_sparse6(s: str):
    """Parse sparse6 string (':...') -> (n, adjacency list of sorted neighbors).
    Follows the format spec of McKay's nauty."""
    assert s.startswith(":")
    data = [ord(c) - 63 for c in s[1:]]
    for d in data:
        assert 0 <= d < 64, "bad sparse6 char"
    if data[0] < 63:
        n = data[0]
        idx = 1
    else:
        assert data[1] < 63 or len(data) > 4
        if data[1] < 63:
            n = (data[1] << 12) | (data[2] << 6) | data[3]
            idx = 4
        else:
            n = (data[2] << 30) | (data[3] << 24) | (data[4] << 18) | \
                (data[5] << 12) | (data[6] << 6) | data[7]
            idx = 8
    k = max(1, (n - 1).bit_length())
    bits = []
    for d in data[idx:]:
        bits.extend((d >> (5 - i)) & 1 for i in range(6))
    edges = set()
    v = 0
    pos = 0
    while pos + k < len(bits):
        b = bits[pos]
        pos += 1
        x = 0
        for i in range(k):
            x = (x << 1) | bits[pos + i]
        pos += k
        if b:
            v += 1
        if x > v:
            v = x
        elif v < n:
            if x != v:
                edges.add((min(x, v), max(x, v)))
            else:
                edges.add((x, v))  # loop; shouldn't occur in simple census
        if v >= n:
            break
    adj = [[] for _ in range(n)]
    for a, b2 in edges:
        if a == b2:
            continue
        adj[a].append(b2)
        adj[b2].append(a)
    for l in adj:
        l.sort()
    return n, adj


# ------------------------------------------------------------ certificates

def check_witness(adj, cyc, L):
    """Certificate check: cyc is a simple cycle of length exactly L."""
    if len(cyc) != L or len(set(cyc)) != L:
        return False
    for i in range(L):
        a, b = cyc[i], cyc[(i + 1) % L]
        if b not in adj[a]:
            return False
    return True


def bfs_dist(adj, n, src):
    dist = [-1] * n
    dist[src] = 0
    q = deque([src])
    while q:
        u = q.popleft()
        for w in adj[u]:
            if dist[w] < 0:
                dist[w] = dist[u] + 1
                q.append(w)
    return dist


def dfs_cycle_from_root(adj, n, L, root, restrict_gt=None):
    """Witness cycle of length exactly L through `root`, or None.
    If restrict_gt is not None, all non-root vertices must be > restrict_gt
    (min-vertex-rooted mode for all-roots completeness)."""
    dist = bfs_dist(adj, n, root)
    lo = -1 if restrict_gt is None else restrict_gt
    path = [root]
    on_path = [False] * n
    on_path[root] = True

    def rec(u, depth):
        remain = L - depth
        if remain == 1:
            if root in adj[u]:
                return True
            return False
        for w in adj[u]:
            if w <= lo and w != root:
                continue
            if on_path[w]:
                continue
            d = dist[w]
            if d < 0 or d > remain - 1:
                continue
            on_path[w] = True
            path.append(w)
            if rec(w, depth + 1):
                return True
            path.pop()
            on_path[w] = False
        return False

    if rec(root, 0):
        return list(path)
    return None


def mitm_cycle_from_root(adj, n, L, root):
    """Witness cycle of length exactly L through `root` via meet-in-the-middle.
    Sound and complete for cycles through root. Returns list or None,
    or the string 'overflow' if the half-path store exceeds the cap."""
    a = L // 2
    b = L - a

    def half_paths(length):
        """Non-self-intersecting paths of `length` edges from root.
        Returns dict endpoint -> list of (bitmask_excluding_root_and_endpoint,
        tuple path interior)."""
        out = {}
        count = 0
        path = [root]
        mask = [1 << root]

        def rec(u, depth):
            nonlocal count
            if depth == length:
                interior = tuple(path[1:-1])
                m = mask[0] & ~(1 << u) & ~(1 << root)
                out.setdefault(u, []).append((m, interior))
                count += 1
                if count > MITM_MAX_HALF:
                    raise OverflowError
                return
            for w in adj[u]:
                if mask[0] >> w & 1:
                    continue
                mask[0] |= 1 << w
                path.append(w)
                rec(w, depth + 1)
                path.pop()
                mask[0] &= ~(1 << w)

        rec(root, 0)
        return out

    try:
        pa = half_paths(a)
        pb = half_paths(b) if b != a else pa
    except OverflowError:
        return "overflow"

    for end, la in pa.items():
        if end == root:
            continue
        lb = pb.get(end)
        if not lb:
            continue
        for m1, int1 in la:
            for m2, int2 in lb:
                if m1 & m2:
                    continue
                if b == a and int1 == int2:
                    continue
                cyc = [root] + list(int1) + [end] + list(reversed(int2))
                if len(cyc) == L and check_witness(adj, cyc, L):
                    return cyc
    return None


def find_pow2_witness(adj, n, root_only=True):
    """Try each L = 4,8,16,... <= n ascending; return (L, cycle) or (None, None)
    or ('deep', Ls_unreachable) if some lengths couldn't be decided."""
    L = 4
    unreachable = []
    while L <= n:
        if L <= 20:
            cyc = dfs_cycle_from_root(adj, n, L, 0) if root_only else None
            if not root_only:
                for r in range(n - L + 1):
                    cyc = dfs_cycle_from_root(adj, n, L, r, restrict_gt=r)
                    if cyc:
                        break
        else:
            if root_only:
                cyc = mitm_cycle_from_root(adj, n, L, 0)
            else:
                cyc = None
                for r in range(n):
                    cyc = mitm_cycle_from_root(adj, n, L, r)
                    if cyc:
                        break
        if cyc == "overflow":
            unreachable.append(L)
        elif cyc:
            return L, cyc
        L *= 2
    if unreachable:
        return "deep", unreachable
    return None, None


# ---------------------------------------------------------------- driver

def main(db_path: str, out_path: str, limit: int | None = None):
    con = sqlite3.connect(db_path)
    cur = con.execute(
        "SELECT id, name, graph_order, data, girth, is_cayley, cvt_index "
        "FROM Graph ORDER BY graph_order, cvt_index"
    )
    t0 = time.time()
    total = kills = survivors = deep = 0
    girth_mismatch = []
    out = gzip.open(out_path, "wt")
    for gid, name, order, data, girth, is_cayley, cvt_index in cur:
        if limit and total >= limit:
            break
        total += 1
        n, adj = parse_sparse6(data)
        assert n == order, (gid, n, order)
        assert all(len(a) == 3 for a in adj), (gid, "not cubic")
        base = {"cayley": is_cayley, "girth_db": girth}
        L, cyc = find_pow2_witness(adj, n, root_only=True)
        if L == "deep":
            rec = {"id": gid, "name": name, "n": n, "verdict": "needs_deep",
                   "unreachable": cyc, **base}
            deep += 1
            print(f"NEEDS_DEEP id={gid} name={name!r} n={n} girth={girth} "
                  f"unreachable={cyc}", flush=True)
        elif L is None:
            # escalate: full all-roots search before declaring survivor
            L2, cyc2 = find_pow2_witness(adj, n, root_only=False)
            if L2 not in (None, "deep"):
                assert check_witness(adj, cyc2, L2)
                rec = {"id": gid, "name": name, "n": n, "verdict": "killed",
                       "L": L2, "cycle": cyc2, "note": "non-root0", **base}
                kills += 1
                print(f"NOTE kill only via non-root0 (VT violation?) id={gid}",
                      flush=True)
            else:
                rec = {"id": gid, "name": name, "n": n, "verdict": "SURVIVOR", **base}
                survivors += 1
                print(f"SURVIVOR id={gid} name={name!r} n={n} girth={girth}",
                      flush=True)
        else:
            assert check_witness(adj, cyc, L)
            rec = {"id": gid, "name": name, "n": n, "verdict": "killed",
                   "L": L, "cycle": cyc, **base}
            kills += 1
            if girth is not None and girth == L and False:
                pass
        out.write(json.dumps(rec) + "\n")
        if total % 2000 == 0:
            el = time.time() - t0
            print(f"[{el:8.1f}s] {total} scanned (n<={n}), kills={kills} "
                  f"survivors={survivors} deep={deep}", flush=True)
    out.close()
    el = time.time() - t0
    print(f"DONE {total} graphs in {el:.1f}s: kills={kills} "
          f"survivors={survivors} needs_deep={deep}", flush=True)
    if girth_mismatch:
        print("girth mismatches:", girth_mismatch[:20])


if __name__ == "__main__":
    db = sys.argv[1]
    out = sys.argv[2] if len(sys.argv) > 2 else "witnesses.jsonl.gz"
    lim = int(sys.argv[3]) if len(sys.argv) > 3 else None
    main(db, out, lim)
