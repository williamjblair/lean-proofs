"""T-B: structure hunt on the q-relaxed two-row survivors (t1 CSVs).

For every survivor (k, d, A) with p01_q = 1:
  1. rational reconstruction: reduced fraction A/d compared against the
     convergents AND semiconvergents of c_k (interval CF from the exact
     Fraction bracket c_bounds(k, 60); terms only emitted while both
     endpoints agree, so every emitted term is certified);
  2. small linear relations a*X + b*d = c0 for X in {A, A+1, A+2},
     1 <= a <= 200, |b| <= 200, |c0| <= 5000 (primitive forms, clustered
     across survivors; significance assessed against the chance rate
     ~ (2*5000+1)*200/d per survivor);
  3. slack cofactor structure: s_t = prod_{p^e || A+t} p^{max(0, e - v_p(G_t))}
     for t = 0, 1  (the exact part of A+t that the q^k slack must cover;
     s_t | q^k always, s_t = 1 iff the row passes raw);
  4. divisor anatomy: full factorization of A and A+1; per prime power the
     window elements that cover it; pattern code = for each row the sorted
     large-prime block profile (primes p > k, binned by log10(p^e));
  5. recurrence / growth: half-decade counts (cross-checked against
     t1_counts.json c01_q), consecutive-gap ratios, shared reduced slopes
     A/d, and a same-slope-scaling family census (A_i*d_j == A_j*d_i).

Everything decision-relevant is exact; floats appear only in report fields.
Output: tb_family_report.json (+ per-survivor tb_survivor_details.json).
"""
import csv
import json
import math
import os
import sys
from fractions import Fraction
from math import gcd

sys.path.insert(0, "/Users/williamblair/personal/lean-proofs/compute")
from erdos686_exact_core import c_bounds

OUT = "/Users/williamblair/personal/lean-proofs/compute/artifacts/structure_hunt"
LAMBDA = {5: 4, 6: 4, 7: 5, 8: 6, 9: 7, 10: 7, 11: 8, 12: 9, 13: 9,
          14: 10, 15: 11}
DMAX_K = {5: 10 ** 8, 6: 10 ** 8, 7: 10 ** 8, 8: 10 ** 8, 9: 10 ** 8,
          10: 3 * 10 ** 8, 11: 10 ** 9, 12: 3 * 10 ** 8, 13: 10 ** 9,
          14: 3 * 10 ** 8, 15: 3 * 10 ** 8}

# ---- primes for factoring A+t <= 1.04e10 (isqrt < 102000) ----
_SIEVE_N = 102000
_sv = bytearray([1]) * 0
_sv = bytearray([1]) * 0


def _primes(n):
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    for i in range(2, math.isqrt(n) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(2, n + 1) if s[i]]


PRIMES = _primes(_SIEVE_N)


def factorize(m):
    out = []
    for p in PRIMES:
        if p * p > m:
            break
        if m % p == 0:
            e = 0
            while m % p == 0:
                m //= p
                e += 1
            out.append((p, e))
    if m > 1:
        out.append((m, 1))
    return out


def vp(x, p):
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v


# ---- certified CF of c_k from the exact bracket ----
def cf_terms_interval(lo: Fraction, hi: Fraction, maxterms=40):
    terms = []
    while len(terms) < maxterms:
        alo, ahi = lo.__floor__(), hi.__floor__()
        if alo != ahi:
            break
        terms.append(alo)
        flo, fhi = lo - alo, hi - alo
        if flo == 0 or fhi == 0:
            break
        lo, hi = 1 / fhi, 1 / flo
    return terms


def convergents_semis(terms):
    """Returns (convergents, semiconvergents) as sets of (p, q)."""
    conv = []
    h0, h1 = 1, terms[0]
    k0, k1 = 0, 1
    conv.append((h1, k1))
    semis = set()
    for a in terms[1:]:
        for m in range(1, a):
            semis.add((h0 + m * h1, k0 + m * k1))
        h0, h1 = h1, a * h1 + h0
        k0, k1 = k1, a * k1 + k0
        conv.append((h1, k1))
    return conv, semis


def load_q_survivors(k):
    rows = []
    with open(os.path.join(OUT, f"t1_surv01_k{k}.csv")) as f:
        for r in csv.DictReader(f):
            if int(r["p01_q"]) == 1:
                rows.append((int(r["d"]), int(r["A"]),
                             int(r["p012_q"]), int(r["p01_raw"])))
    rows.sort()
    return rows


def linear_relations(X, d):
    """Primitive (a, b, c0), 1<=a<=200, |b|<=200, |c0|<=5000, a*X+b*d=c0."""
    rels = set()
    for a in range(1, 201):
        b0 = -((a * X + d // 2) // d)   # nearest integer to -aX/d
        for b in (b0 - 1, b0, b0 + 1):
            if abs(b) > 200:
                continue
            c0 = a * X + b * d
            if abs(c0) <= 5000:
                g = gcd(a, abs(b)) if b else a
                rels.add((a // g, b // g, c0 // g))
    return rels


def analyze_k(k):
    lam = LAMBDA[k]
    q = lam - 1
    qk = q ** k
    surv = load_q_survivors(k)
    c2, c1, _, _ = c_bounds(k, 60)
    terms = cf_terms_interval(c2, c1, 40)
    conv, semis = convergents_semis(terms)
    convset = set(conv)

    details = []
    slope_map = {}          # reduced (p,q) -> [d, ...]
    pattern_hist = {}       # anatomy pattern code -> count
    slack_hist = {}         # (s0, s1) -> count
    rel_hist = {}           # (X_shift, a, b, c0) -> [d, ...]
    cf_hits = []
    for d, A, p012q, p01raw in surv:
        g = gcd(A, d)
        red = (A // g, d // g)
        slope_map.setdefault(red, []).append(d)
        is_conv = red in convset
        is_semi = red in semis
        if is_conv or is_semi:
            cf_hits.append({"d": d, "A": A, "frac": red,
                            "type": "convergent" if is_conv else
                            "semiconvergent"})
        # linear relations
        my_rels = {}
        for t in range(3):
            for rel in linear_relations(A + t, d):
                my_rels.setdefault(t, []).append(rel)
                rel_hist.setdefault((t,) + rel, []).append(d)
        # slack cofactors + anatomy for rows 0, 1
        rowinfo = []
        s_pair = []
        for t in range(2):
            M = A + t
            fM = factorize(M)
            s_t = 1
            blocks = []
            per_prime = []
            for p, e in fM:
                vG = 0
                contrib = []
                # window elements divisible by p
                start = (d - t) + ((-(d - t)) % p)
                for x in range(start, d - t + k, p):
                    v = vp(x, p)
                    vG += v
                    contrib.append((x - (d - t), v))
                if vG < e:
                    s_t *= p ** (e - vG)
                per_prime.append({"p": p, "e": e, "v_window": vG,
                                  "cover": contrib})
                if p > k:
                    blocks.append(p ** e)
            blocks.sort(reverse=True)
            code = tuple(int(math.log10(b)) for b in blocks)
            rowinfo.append({"t": t, "fact": fM, "slack_part": s_t,
                            "large_blocks": blocks, "block_code": code,
                            "per_prime": per_prime})
            s_pair.append(s_t)
        pat = (rowinfo[0]["block_code"], rowinfo[1]["block_code"])
        pattern_hist[pat] = pattern_hist.get(pat, 0) + 1
        slack_hist[tuple(s_pair)] = slack_hist.get(tuple(s_pair), 0) + 1
        details.append({"k": k, "d": d, "A": A, "p012_q": p012q,
                        "p01_raw": p01raw, "reduced_A_over_d": red,
                        "cf_convergent": is_conv, "cf_semiconvergent": is_semi,
                        "slack_parts": s_pair,
                        "linear_relations": {str(t): sorted(v) for t, v in
                                             my_rels.items()},
                        "rows": rowinfo})

    # ---- growth / gaps / recurrence ----
    ds = [s[0] for s in surv]
    halfdec = {}
    for d in ds:
        b = 0
        while 10 ** ((b + 1) / 2) <= d:   # report-only float; d<=1e9 safe
            b += 1
        halfdec[b] = halfdec.get(b, 0) + 1
    gaps = [(ds[i + 1], round(ds[i + 1] / ds[i], 4))
            for i in range(len(ds) - 1)] if len(ds) > 1 else []
    # same-slope scaling families
    slope_fams = {str(red): dv for red, dv in slope_map.items()
                  if len(dv) >= 2}
    # d'/d ratio repetition (exact fractions)
    ratio_hist = {}
    for i in range(len(surv) - 1):
        r = Fraction(surv[i + 1][0], surv[i][0])
        if r.denominator <= 50:
            key = f"{r.numerator}/{r.denominator}"
            ratio_hist[key] = ratio_hist.get(key, 0) + 1

    # significant relations: shared by >= 3 survivors incl. one with d > 1e7
    sig_rels = {}
    for key, dv in rel_hist.items():
        if len(dv) >= 3 and max(dv) > 10 ** 7:
            sig_rels[str(key)] = sorted(dv)

    report = {
        "k": k, "lambda": lam, "q": q, "n_q_survivors": len(surv),
        "dmax_scanned": DMAX_K[k],
        "cf_terms": terms[:18],
        "convergents": conv[:12],
        "cf_hits": cf_hits,
        "n_cf_hits": len(cf_hits),
        "halfdecade_counts": {str(b): c for b, c in sorted(halfdec.items())},
        "largest_survivor_d": ds[-1] if ds else None,
        "consecutive_d_ratios": gaps,
        "repeated_exact_d_ratios(den<=50)": {kk: v for kk, v in
                                             sorted(ratio_hist.items())
                                             if v >= 2},
        "same_slope_families": slope_fams,
        "significant_shared_linear_relations": sig_rels,
        "slack_pair_hist": {str(kk): v for kk, v in
                            sorted(slack_hist.items(),
                                   key=lambda z: -z[1])[:12]},
        "block_pattern_hist_top": {str(kk): v for kk, v in
                                   sorted(pattern_hist.items(),
                                          key=lambda z: -z[1])[:15]},
    }
    return report, details


def main():
    reports = {}
    all_details = {}
    for k in sorted(LAMBDA):
        rep, det = analyze_k(k)
        reports[k] = rep
        all_details[k] = det
        print(f"k={k}: n_q={rep['n_q_survivors']} cf_hits={rep['n_cf_hits']} "
              f"slope_fams={len(rep['same_slope_families'])} "
              f"sig_rels={len(rep['significant_shared_linear_relations'])}",
              flush=True)

    # cross-check half-decade counts against t1_counts c01_q
    j = json.load(open(os.path.join(OUT, "t1_counts.json")))
    for k in sorted(LAMBDA):
        mine = reports[k]["halfdecade_counts"]
        theirs = {b: v[6] for b, v in j["buckets"][str(k)].items()
                  if v[6] > 0}
        ok = {int(b): c for b, c in mine.items()} == \
             {int(b): v for b, v in theirs.items()}
        reports[k]["halfdec_matches_t1_counts_c01q"] = ok
        if not ok:
            print(f"k={k} halfdec mismatch: mine={mine} t1={theirs}")

    with open(os.path.join(OUT, "tb_family_report.json"), "w") as f:
        json.dump(reports, f, indent=1, default=str)
    with open(os.path.join(OUT, "tb_survivor_details.json"), "w") as f:
        json.dump(all_details, f, default=str)
    print("wrote tb_family_report.json, tb_survivor_details.json")


if __name__ == "__main__":
    main()
