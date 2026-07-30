"""Independent verifier for the Erdős #64 census scan.

Reads the census sqlite and witnesses.jsonl.gz produced by scan_census.py and
re-checks every certificate using networkx's sparse6 parser (independent of
the scanner's hand-rolled parser) and a from-scratch cycle check.

Checks:
1. Coverage: every Graph row id appears exactly once in the witness file.
2. Every 'killed' record: the cycle is a simple cycle of the graph, its
   length is a power of two >= 4 and <= n.
3. Survivors / needs_deep records are listed for human follow-up.
"""
from __future__ import annotations
import gzip
import json
import sqlite3
import sys
import networkx as nx


def main(db_path: str, wit_path: str):
    con = sqlite3.connect(db_path)
    cur = con.execute("SELECT id, data, graph_order FROM Graph")
    graphs = {gid: (data, order) for gid, data, order in cur}
    seen = set()
    kills = survivors = deep = 0
    bad = []
    with gzip.open(wit_path, "rt") as f:
        for line in f:
            rec = json.loads(line)
            gid = rec["id"]
            if gid in seen:
                bad.append((gid, "duplicate record"))
                continue
            seen.add(gid)
            data, order = graphs[gid]
            if rec["verdict"] == "killed":
                G = nx.from_sparse6_bytes(data.encode())
                n = G.number_of_nodes()
                cyc = rec["cycle"]
                L = rec["L"]
                ok = (
                    n == order == rec["n"]
                    and L >= 4 and (L & (L - 1)) == 0 and L <= n
                    and len(cyc) == L and len(set(cyc)) == L
                    and all(G.has_edge(cyc[i], cyc[(i + 1) % L]) for i in range(L))
                )
                if not ok:
                    bad.append((gid, "invalid certificate"))
                kills += 1
            elif rec["verdict"] == "SURVIVOR":
                survivors += 1
                print(f"SURVIVOR: {rec}")
            elif rec["verdict"] == "needs_deep":
                deep += 1
                print(f"NEEDS_DEEP: {rec}")
            else:
                bad.append((gid, f"unknown verdict {rec['verdict']}"))
    missing = set(graphs) - seen
    print(f"rows in db: {len(graphs)}; records verified: {len(seen)}; "
          f"kills={kills} survivors={survivors} needs_deep={deep}")
    if missing:
        print(f"MISSING {len(missing)} graph ids: {sorted(missing)[:20]} ...")
    if bad:
        print(f"BAD RECORDS: {bad[:50]}")
    if not missing and not bad:
        print("VERIFICATION PASSED: every census graph has a valid power-of-2 "
              "cycle certificate or is explicitly flagged.")
        return 0
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1], sys.argv[2]))
