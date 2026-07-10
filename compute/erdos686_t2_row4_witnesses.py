"""T2 - row-4 escape witnesses for the 45 constant-quotient prefix-three
survivors (Erdos #686, N = 4 branch).

For each survivor (k,q,d,u,A) from T1:
  1. verify the row-4 residual FAILS:
         NOT (A+3) | residualRowPoly(k, q, d-u+3*(q+1))
  2. produce an affine-saturation prime witness: a prime p and e >= 1 with
         p^e | (A+3) // gcd(A+3, q^k),      p does not divide q,
         v_p(affineResidualPoly(k,q,u,3)) < e.
     (We take e = v_p(affine) + 1, which then satisfies e <= v_p(A+3).)

Soundness of the witness (per-factor identity, verified in the core module):
    (q+1)^k * residualRowPoly(k,q,d-u+3(q+1)) = liftedAffineResidualPoly(...,A+3)
and liftedAffineResidualPoly == q^k * affineResidualPoly  (mod A+3).
If p^e | A+3 with p not dividing q and v_p(affine) < e, then
v_p(lifted) = v_p(q^k * affine) = v_p(affine) < e, so (A+3) cannot divide
the row-4 residual (its (q+1)^k-multiple already fails at p).

All arithmetic exact.  Reads T1's JSON artifact (regenerates it if absent).

Artifacts:
    compute/artifacts/constant_prefix3_row4_witnesses.json
    compute/artifacts/constant_prefix3_row4_witnesses.csv
"""

import csv
import json
import math
import os
import time

from erdos686_exact_core import (
    residual_row_poly, affine_residual_poly, lifted_affine_residual_poly,
    factorize, padic_valuation, verify_per_factor_identity,
    verify_lifted_product_identity,
)

HERE = os.path.dirname(os.path.abspath(__file__))
ART = os.path.join(HERE, "artifacts")
T1_JSON = os.path.join(ART, "constant_prefix3_survivors.json")


def load_survivors():
    if not os.path.exists(T1_JSON):
        import erdos686_t1_constant_prefix3 as t1
        t1.run()
    with open(T1_JSON) as f:
        return json.load(f)["survivors"]


def find_witness(k, q, d, u, A):
    """Return witness dict or None.  Also returns diagnostic fields."""
    M = A + 3
    aff = affine_residual_poly(k, q, u, 3)
    reduced = M // math.gcd(M, q ** k)
    for (p, eM) in factorize(M):
        if q % p == 0:
            continue  # witness prime must not divide q
        # for p not dividing q, v_p(reduced) == v_p(M) = eM
        assert padic_valuation(reduced, p) == eM
        vp_aff = padic_valuation(aff, p)  # None means aff == 0 (v_p infinite)
        if vp_aff is None:
            continue
        if vp_aff < eM:
            e = vp_aff + 1
            assert 1 <= e <= eM and reduced % p ** e == 0
            return {"p": p, "e": e, "vpAffine": vp_aff,
                    "vp_A_plus_3": eM, "affine_poly_zero": False}
    return None


def run():
    assert verify_per_factor_identity(), "per-factor identity FAILED"
    t0 = time.time()
    survivors = load_survivors()
    assert len(survivors) == 45, f"expected 45 survivors, got {len(survivors)}"

    rows = []
    failures = []
    for s in survivors:
        k, q, d, u, A = s["k"], s["q"], s["d"], s["u"], s["A"]
        # 1. row-4 residual must fail
        R3 = d - u + 3 * (q + 1)
        row4_poly = residual_row_poly(k, q, R3)
        row4_fails = (row4_poly % (A + 3) != 0)
        # sanity: lifted product identity for this survivor at t = 3
        assert verify_lifted_product_identity(k, q, d, u, 3)
        lifted = lifted_affine_residual_poly(k, q, u, 3, A + 3)
        aff = affine_residual_poly(k, q, u, 3)
        assert (lifted - q ** k * aff) % (A + 3) == 0
        # 2. affine-saturation prime witness
        wit = find_witness(k, q, d, u, A)
        rec = {"k": k, "q": q, "d": d, "u": u, "A": A,
               "row4_residual_fails": row4_fails,
               "affine_poly_is_zero": aff == 0}
        if wit is not None:
            rec.update(wit)
            # cross-check that the witness indeed certifies row-4 failure
            assert row4_fails, (
                f"witness exists but row-4 residual divides for {rec}")
        rows.append(rec)
        if not row4_fails or wit is None:
            failures.append(rec)

    elapsed = time.time() - t0
    n_row4 = sum(1 for r in rows if r["row4_residual_fails"])
    n_wit = sum(1 for r in rows if "p" in r)
    print(f"survivors checked:          {len(rows)}")
    print(f"row-4 residual fails:       {n_row4} / {len(rows)}")
    print(f"prime witnesses found:      {n_wit} / {len(rows)}")
    print(f"affine poly zero cases:     "
          f"{sum(1 for r in rows if r['affine_poly_is_zero'])}")
    if failures:
        print("SURVIVORS WITHOUT COMPLETE WITNESS:")
        for r in failures:
            print("  ", r)
    else:
        print("every survivor has row-4 failure and a prime witness")
    print(f"elapsed={elapsed:.2f}s")

    os.makedirs(ART, exist_ok=True)
    payload = {
        "description": "Row-4 escape witnesses for the 45 constant-quotient "
                       "prefix-three survivors: row-4 residual failure plus "
                       "an affine-saturation prime witness (p,e) with "
                       "p^e | (A+3)/gcd(A+3,q^k), p not dividing q, and "
                       "v_p(affineResidualPoly(k,q,u,3)) < e.",
        "witness_soundness": "(q+1)^k * residualRowPoly(k,q,d-u+3(q+1)) == "
                             "liftedAffineResidualPoly(k,q,u,3,A+3) and the "
                             "lifted poly is congruent to q^k * "
                             "affineResidualPoly(k,q,u,3) mod A+3.",
        "count": len(rows),
        "all_witnessed": not failures,
        "witnesses": rows,
        "failures": failures,
        "elapsed_seconds": round(elapsed, 3),
    }
    jpath = os.path.join(ART, "constant_prefix3_row4_witnesses.json")
    with open(jpath, "w") as f:
        json.dump(payload, f, indent=1)
    cpath = os.path.join(ART, "constant_prefix3_row4_witnesses.csv")
    with open(cpath, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["k", "q", "d", "u", "A", "p", "e", "vpAffine",
                    "vp_A_plus_3", "row4_residual_fails"])
        for r in rows:
            w.writerow([r["k"], r["q"], r["d"], r["u"], r["A"],
                        r.get("p", ""), r.get("e", ""),
                        r.get("vpAffine", ""), r.get("vp_A_plus_3", ""),
                        int(r["row4_residual_fails"])])
    print(f"wrote {jpath}")
    print(f"wrote {cpath}")
    return rows, failures


if __name__ == "__main__":
    run()
