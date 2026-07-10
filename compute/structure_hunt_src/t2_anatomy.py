"""T2 — anatomy of the 45 banked three-row survivors.

For each survivor (k,q,d,A) and each row t=0,1,2 (modulus M=A+t, factors
m_i = d-t+i, i=0..k-1, slack q^k and lambda^k with lambda=q+1):
  * factor M, each m_i, A-side numbers;
  * for each prime power p^e || M, list the exact covering:
        e <= v_p(slack) + sum_i v_p(m_i)   (which terms contribute what);
  * compute gcd-profile g_i = gcd(M, m_i) and the minimal number of
    m_i-terms needed to cover M/gcd(M, slack^inf);
  * check raw divisibility (slack needed at all?).
Everything exact.  Output: JSON + human-readable text report.
"""
import json
import os
import sys
from math import gcd, prod

sys.path.insert(0, "/Users/williamblair/personal/lean-proofs/compute")
from erdos686_exact_core import factorize

ART = "/Users/williamblair/personal/lean-proofs/compute/artifacts"
OUT = os.path.join(ART, "structure_hunt")


def vp(x, p):
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


def fmt_fact(fl):
    return "*".join((f"{p}^{e}" if e > 1 else str(p)) for p, e in fl)


def analyze(k, q, d, A):
    lam = q + 1
    rows = []
    for t in range(3):
        M = A + t
        ms = [d - t + i for i in range(k)]
        fM = factorize(M)
        cover = []
        slack_needed_q = {}
        slack_needed_lam = {}
        for p, e in fM:
            contrib = [(i, vp(m, p)) for i, m in enumerate(ms) if m % p == 0]
            tot = sum(v for _, v in contrib)
            sq = k * vp(q, p)
            sl = k * vp(lam, p)
            cover.append({
                "p": p, "e": e, "from_terms": contrib,
                "terms_total": tot, "v_q_slack": sq, "v_lam_slack": sl,
                "covered_raw": tot >= e,
                "covered_q": tot + sq >= e,
                "covered_lam": tot + sl >= e,
            })
            if tot < e:
                slack_needed_q[p] = e - tot
                slack_needed_lam[p] = e - tot
        # gcd profile & greedy minimal aligned-divisor cover
        gs = [gcd(M, m) for m in ms]
        # residual after removing slack-covered part: for the q-variant
        raw_ok = all(c["covered_raw"] for c in cover)
        q_ok = all(c["covered_q"] for c in cover)
        lam_ok = all(c["covered_lam"] for c in cover)
        # minimal number of terms to cover M by per-prime assignment:
        # count distinct terms used when each prime power is assigned to
        # terms greedily (largest v first)
        used_terms = set()
        for c in cover:
            need = c["e"] - (0 if raw_ok is None else 0)
            need = c["e"]
            # subtract slack (q variant) only if raw fails for this prime
            if not c["covered_raw"]:
                need = max(0, c["e"] - c["v_q_slack"])
            got = 0
            for i, v in sorted(c["from_terms"], key=lambda x: -x[1]):
                if got >= need:
                    break
                used_terms.add(i)
                got += v
        rows.append({
            "t": t, "M": M, "M_fact": fmt_fact(fM),
            "raw_ok": raw_ok, "q_ok": q_ok, "lam_ok": lam_ok,
            "cover": cover,
            "gcds": gs,
            "n_terms_used": len(used_terms),
            "terms_used": sorted(used_terms),
        })
    return rows


def main():
    surv = json.load(open(os.path.join(ART, "constant_prefix3_survivors.json")))
    out = []
    txt = []
    for s in surv["survivors"]:
        k, q, d, A = s["k"], s["q"], s["d"], s["A"]
        rows = analyze(k, q, d, A)
        rec = {"k": k, "q": q, "d": d, "A": A, "u": (q + 1) * d - A,
               "rows": rows}
        out.append(rec)
        txt.append(f"== k={k} q={q} d={d} A={A}  (u=(q+1)d-A={rec['u']}, "
                   f"A-qd={A - q * d})")
        txt.append(f"   A..A+2 = {fmt_fact(factorize(A))} | "
                   f"{fmt_fact(factorize(A + 1))} | "
                   f"{fmt_fact(factorize(A + 2))}")
        for r in rows:
            t = r["t"]
            gl = [(i, g) for i, g in enumerate(r["gcds"]) if g > 1]
            txt.append(f"   t={t} M={r['M']}={r['M_fact']} raw={int(r['raw_ok'])}"
                       f" q={int(r['q_ok'])} lam={int(r['lam_ok'])} "
                       f"terms_used={r['terms_used']}")
            for c in r["cover"]:
                if c["e"] == 0:
                    continue
                src = " ".join(f"m[{i}]=d-{t}+{i}:{v}" for i, v in
                               c["from_terms"])
                flag = "" if c["covered_raw"] else \
                    f"  NEEDS SLACK (q^k gives {c['v_q_slack']}, lam^k {c['v_lam_slack']})"
                txt.append(f"      p={c['p']}^{c['e']}: terms {src or '-'} "
                           f"total={c['terms_total']}{flag}")
    with open(os.path.join(OUT, "t2_covering_patterns.json"), "w") as f:
        json.dump(out, f, indent=1)
    with open(os.path.join(OUT, "t2_covering_patterns.txt"), "w") as f:
        f.write("\n".join(txt) + "\n")

    # summary stats
    nterm_hist = {}
    for rec in out:
        for r in rec["rows"]:
            nterm_hist[r["n_terms_used"]] = \
                nterm_hist.get(r["n_terms_used"], 0) + 1
    print("terms-used histogram (per row):", dict(sorted(nterm_hist.items())))
    print(f"wrote {len(out)} survivor anatomies")


if __name__ == "__main__":
    main()
