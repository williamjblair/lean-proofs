#!/usr/bin/env python3
"""Generate ErdosProblems/Erdos686ConstantSurvivors.lean.

Band parameters come from compute/erdos686_e9s_uband.py (see
compute/artifacts/constant_uband_params.json); this script re-derives and
re-verifies them, then emits the Lean module (survivor lists, banded kernel
certificates, dispatch lemmas, and the packaged theorems).
"""

import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
ART = os.path.join(HERE, "artifacts")
OUT = os.path.join(ROOT, "ErdosProblems", "Erdos686ConstantSurvivors.lean")

PAIRS = [(5, 3), (6, 3), (7, 4), (8, 5), (9, 6), (10, 6),
         (11, 7), (12, 8), (13, 8), (14, 9), (15, 10)]
BOUND = {(5, 3): 220, (6, 3): 220, (7, 4): 220, (8, 5): 220, (9, 6): 220,
         (10, 6): 266, (11, 7): 7029, (12, 8): 2695, (13, 8): 4467,
         (14, 9): 2811, (15, 10): 2915}

# active-pair band brackets: p1/r1 > 4^(1/k) > p2/r2 (verified exactly below)
BAND = {
    (10, 6): dict(p1=224, r1=195, p2=85, r2=74, W=10, chunks=[(221, 46)]),
    (11, 7): dict(p1=1081, r1=953, p2=3167, r2=2792, W=11,
                  chunks=[(221, 973), (1194, 973), (2167, 973), (3140, 973),
                          (4113, 973), (5086, 973), (6059, 971)]),
    (12, 8): dict(p1=3483, r1=3103, p2=1769, r2=1576, W=12,
                  chunks=[(221, 825), (1046, 825), (1871, 825)]),
    (13, 8): dict(p1=435, r1=391, p2=524, r2=471, W=14,
                  chunks=[(221, 850), (1071, 850), (1921, 850), (2771, 850),
                          (3621, 847)]),
    (14, 9): dict(p1=647, r1=586, p2=297, r2=269, W=15,
                  chunks=[(221, 864), (1085, 864), (1949, 863)]),
    (15, 10): dict(p1=691, r1=630, p2=725, r2=661, W=15,
                   chunks=[(221, 899), (1120, 899), (2019, 897)]),
}

# u = d line cap brackets: p1/r1 > 4^(1/k), with r1*(q+1) - p1*q > 0
CAPS = {(5, 3): (33, 25), (6, 3): (63, 50), (7, 4): (50, 41), (8, 5): (25, 21),
        (9, 6): (1415, 1213), (10, 6): (54, 47), (11, 7): (42, 37),
        (12, 8): (174, 155), (13, 8): (49, 44), (14, 9): (53, 48),
        (15, 10): (45, 41)}

BAND_EXTRAS = [(11, 7, 1517, 852, 11284), (11, 7, 1936, 1084, 14404),
               (12, 8, 299, 261, 2430), (13, 8, 4466, 506, 39688),
               (14, 9, 925, 377, 8873), (14, 9, 1103, 448, 10582)]

CHUNK_TAGS = "abcdefghijklmnop"


def residual_prod(k, q, r):
    p = 1
    for s in range(k):
        p *= abs(q * s - r)
    return p


def verify():
    with open(os.path.join(ART, "constant_prefix3_survivors.json")) as f:
        survivors = [(s["k"], s["q"], s["d"], s["u"], s["A"])
                     for s in json.load(f)["survivors"]]
    assert len(survivors) == 45
    full = survivors + BAND_EXTRAS
    fullset = set(full)

    for (k, q), b in BAND.items():
        p1, r1, p2, r2, W = b["p1"], b["r1"], b["p2"], b["r2"], b["W"]
        assert 4 * r1 ** k < p1 ** k and p2 ** k < 4 * r2 ** k
        e1, e2 = p1 - r1, p2 - r2
        c1, c2 = (q + 1) * e1 - r1, (q + 1) * e2 - r2
        assert c1 > 0 and c2 > 0
        b["e1"], b["e2"], b["c1"], b["c2"] = e1, e2, c1, c2
        bound = BOUND[(k, q)]
        # chunk cover check
        ds = [d for s, n in b["chunks"] for d in range(s, s + n)]
        assert ds == list(range(221, bound + 1)), (k, q)
        # width check and full band-cert truth check
        for d in range(221, bound + 1):
            lo = c2 * d // e2 + 1
            assert c1 * d // e1 + (k - 1) - lo < W
            for i in range(W):
                u = lo + i
                A = (q + 1) * d - u
                if not (u < d):
                    continue
                if all(residual_prod(k, q, (d - u) + (q + 1) * t) % (A + t) == 0
                       for t in range(3)):
                    assert (k, q, d, u, A) in fullset, (k, q, d, u, A)
        # survivors inside band
        for (kk, qq, d, u, A) in full:
            if (kk, qq) != (k, q):
                continue
            lo = c2 * d // e2 + 1
            assert lo <= u < lo + W and 221 <= d <= bound, (kk, qq, d, u)

    # u = d caps
    for (k, q), (p1, r1) in CAPS.items():
        assert 4 * r1 ** k < p1 ** k
        m = r1 * (q + 1) - p1 * q
        assert m > 0
        cap = ((k - 1) * (p1 - r1) - 1) // m
        if (k, q) == (9, 6):
            assert cap == 1615
            C1 = residual_prod(9, 6, 7)
            C2 = residual_prod(9, 6, 14)
            for d in range(221, cap + 1):
                assert not (C1 % (6 * d + 1) == 0 and C2 % (6 * d + 2) == 0), d
        else:
            assert cap < 221, (k, q, cap)

    # row-4 escape over the full band list
    for (k, q, d, u, A) in full:
        r3 = (d - u) + 3 * (q + 1)
        assert residual_prod(k, q, r3) % (A + 3) != 0, (k, q, d, u, A)
    return survivors


def fmt_tuples(tuples, indent):
    parts = [f"({k}, {q}, {d}, {u}, {A})" for (k, q, d, u, A) in tuples]
    lines, cur = [], ""
    for i, p in enumerate(parts):
        item = p + ("," if i + 1 < len(parts) else "]")
        if not cur:
            cur = " " * indent + item
        elif len(cur) + 1 + len(item) <= 98:
            cur += " " + item
        else:
            lines.append(cur)
            cur = " " * indent + item
    lines.append(cur)
    lines[0] = lines[0].lstrip()
    return "\n".join(" " * indent + l if i else l for i, l in
                     enumerate(x.strip() for x in lines))


def gen(survivors):
    L = []
    o = L.append
    o("/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/")
    o("import ErdosProblems.Erdos686ConstantQuotient")
    o("")
    o("/-!")
    o("# Erdős Problem 686: constant-quotient prefix-three survivors")
    o("")
    o("Banded kernel certificates for the constant-quotient branch of the")
    o("`N = 4` exclusion.  For each tabulated pair `(k, q)` with per-case gap")
    o("bound `constantPrefixThreeBound`, the exact ratio window pins the")
    o("deficiency `u = (q+1)·d − A` inside an explicit linear band")
    o("`c₂·d/e₂ < u ≤ c₁·d/e₁ + (k−1)` (derived from rational brackets around")
    o("`4^(1/k)` via the linearization lemmas).  Kernel `decide` certificates")
    o("sweep the whole band and certify that every point passing the residual")
    o("divisibilities of rows one to three is one of finitely many listed")
    o("survivors — and a second certificate checks that every listed survivor")
    o("fails the row-four residual divisibility.  The top edge `u = d`")
    o("(`A = q·d`) is handled separately: the upper window kills it outright")
    o("for ten of the eleven pairs, and for `(9, 6)` a dedicated certificate")
    o("refutes the fixed row-two/row-three divisor coincidences up to the")
    o("window crossover `d ≤ 1615`.")
    o("-/")
    o("")
    o("namespace Erdos686")
    o("")
    o("namespace Erdos686Variant")
    o("")
    o("/-- Per-case gap bounds for the constant-quotient prefix-three")
    o("analysis. -/")
    o("def constantPrefixThreeBound : ℕ → ℕ → ℕ")
    for (k, q) in PAIRS:
        o(f"  | {k}, {q} => {BOUND[(k, q)]}")
    o("  | _, _ => 0")
    o("")
    o("/-- The eleven constant-quotient pairs `(k, q)` of the `N = 4`")
    o("branch. -/")
    o("def constantQuotientPairs : List (ℕ × ℕ) :=")
    o("  [" + ", ".join(f"({k}, {q})" for (k, q) in PAIRS) + "]")
    o("")
    o("/-- Membership in the constant-quotient pair table. -/")
    o("def constantQuotientPairMem (k q : ℕ) : Prop :=")
    o("  (k, q) ∈ constantQuotientPairs")
    o("")
    o("instance (k q : ℕ) : Decidable (constantQuotientPairMem k q) :=")
    o("  inferInstanceAs (Decidable ((k, q) ∈ constantQuotientPairs))")
    o("")
    o("/-- The 45 window points `(k, q, d, u, A)` surviving the residual")
    o("divisibilities of rows one to three (exact-arithmetic scan artifact")
    o("`compute/artifacts/constant_prefix3_survivors.json`). -/")
    o("def constantPrefixThreeSurvivors : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=")
    o("  [" + fmt_tuples(survivors, 3))
    o("")
    o("/-- Six additional residual-passing points of the linear band that lie")
    o("just outside the exact ratio window (each is a `d ± 1` shadow of a true")
    o("survivor at the same `A`); the banded certificates must list them")
    o("too. -/")
    o("def constantPrefixThreeBandExtras : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=")
    o("  [" + fmt_tuples(BAND_EXTRAS, 3))
    o("")
    o("/-- All residual-passing band points: survivors plus band shadows. -/")
    o("def constantPrefixThreeBandSurvivors : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=")
    o("  constantPrefixThreeSurvivors ++ constantPrefixThreeBandExtras")
    o("")
    o("/-- `ℕ`-valued absolute residual row product")
    o("`∏_{s<k} |q·s − r|`, in kernel-friendly recursive form. -/")
    o("def residualProdNat : ℕ → ℕ → ℕ → ℕ")
    o("  | 0, _, _ => 1")
    o("  | m + 1, q, r => residualProdNat m q r * Nat.dist (q * m) r")
    o("")
    o("private lemma natAbs_natCast_sub_natCast (a b : ℕ) :")
    o("    ((a : ℤ) - (b : ℤ)).natAbs = Nat.dist a b := by")
    o("  rcases Nat.le_total a b with h | h")
    o("  · rw [Nat.dist_eq_sub_of_le h,")
    o("      show (a : ℤ) - (b : ℤ) = -(((b - a : ℕ) : ℤ)) from by")
    o("        rw [Nat.cast_sub h]; ring,")
    o("      Int.natAbs_neg, Int.natAbs_natCast]")
    o("  · rw [Nat.dist_eq_sub_of_le_right h,")
    o("      show (a : ℤ) - (b : ℤ) = ((a - b : ℕ) : ℤ) from by")
    o("        rw [Nat.cast_sub h],")
    o("      Int.natAbs_natCast]")
    o("")
    o("/-- The absolute value of the residual row polynomial is the `ℕ`")
    o("distance product. -/")
    o("lemma residualRowPoly_natAbs (k q r : ℕ) :")
    o("    (residualRowPoly k q r).natAbs")
    o("      = ∏ s ∈ Finset.range k, Nat.dist (q * s) r := by")
    o("  unfold residualRowPoly")
    o("  induction k with")
    o("  | zero => simp")
    o("  | succ m ih =>")
    o("      rw [Finset.prod_range_succ, Finset.prod_range_succ,")
    o("        Int.natAbs_mul, ih]")
    o("      congr 1")
    o("      rw [show (q : ℤ) * (m : ℤ) - (r : ℤ)")
    o("            = ((q * m : ℕ) : ℤ) - ((r : ℕ) : ℤ) from by push_cast; ring]")
    o("      exact natAbs_natCast_sub_natCast (q * m) r")
    o("")
    o("private lemma residualProdNat_eq_prod (k q r : ℕ) :")
    o("    residualProdNat k q r = ∏ s ∈ Finset.range k, Nat.dist (q * s) r := by")
    o("  induction k with")
    o("  | zero => rfl")
    o("  | succ m ih => rw [residualProdNat, ih, Finset.prod_range_succ]")
    o("")
    o("/-- Kernel-friendly transfer: `ℤ`-divisibility of the residual row")
    o("polynomial by a natural number is `ℕ`-divisibility of the distance")
    o("product. -/")
    o("lemma int_natCast_dvd_residualRowPoly_iff (m k q r : ℕ) :")
    o("    ((m : ℤ) ∣ residualRowPoly k q r) ↔ m ∣ residualProdNat k q r := by")
    o("  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast, residualRowPoly_natAbs,")
    o("    residualProdNat_eq_prod]")
    o("")
    o("set_option maxRecDepth 10000 in")
    o("set_option maxHeartbeats 1000000 in")
    o("-- Kernel check: every listed band survivor fails the row-four residual.")
    o("private theorem constant_band_survivors_row4_escape_cert :")
    o("    ∀ x ∈ constantPrefixThreeBandSurvivors,")
    o("      ¬ (x.2.2.2.2 + 3)")
    o("          ∣ residualProdNat x.1 x.2.1 (x.2.2.1 - x.2.2.2.1 + 3 * (x.2.1 + 1)) := by")
    o("  decide")
    o("")
    o("/-- **Row-four escape** for every listed band survivor. -/")
    o("theorem constant_prefix_three_band_survivors_row4_escape")
    o("    {k q d u A : ℕ}")
    o("    (hmem : (k, q, d, u, A) ∈ constantPrefixThreeBandSurvivors) :")
    o("    ¬ (((A + 3 : ℕ) : ℤ) ∣ residualRowPoly k q (d - u + 3 * (q + 1))) := by")
    o("  rw [int_natCast_dvd_residualRowPoly_iff]")
    o("  exact constant_band_survivors_row4_escape_cert _ hmem")
    o("")
    o("/-- **D2: row-four escape** for every one of the 45 exact-window")
    o("survivors. -/")
    o("theorem constant_prefix_three_survivors_row4_escape")
    o("    {k q d u A : ℕ}")
    o("    (hmem : (k, q, d, u, A) ∈ constantPrefixThreeSurvivors) :")
    o("    ¬ (((A + 3 : ℕ) : ℤ) ∣ residualRowPoly k q (d - u + 3 * (q + 1))) :=")
    o("  constant_prefix_three_band_survivors_row4_escape")
    o("    (List.mem_append_left constantPrefixThreeBandExtras hmem)")
    o("")
    o("/-- Banded point predicate decided by the kernel certificates: if the")
    o("point `u` at gap `d` lies below `d` and passes the residual")
    o("divisibilities of rows one to three, it is a listed band survivor. -/")
    o("def BandPoint (k q d u : ℕ) : Prop :=")
    o("  u < d →")
    o("  ((q + 1) * d - u) ∣ residualProdNat k q (d - u) →")
    o("  ((q + 1) * d - u + 1) ∣ residualProdNat k q (d - u + (q + 1)) →")
    o("  ((q + 1) * d - u + 2) ∣ residualProdNat k q (d - u + 2 * (q + 1)) →")
    o("  (k, q, d, u, (q + 1) * d - u) ∈ constantPrefixThreeBandSurvivors")
    o("")
    o("instance (k q d u : ℕ) : Decidable (BandPoint k q d u) :=")
    o("  inferInstanceAs (Decidable")
    o("    (u < d →")
    o("      ((q + 1) * d - u) ∣ residualProdNat k q (d - u) →")
    o("      ((q + 1) * d - u + 1) ∣ residualProdNat k q (d - u + (q + 1)) →")
    o("      ((q + 1) * d - u + 2) ∣ residualProdNat k q (d - u + 2 * (q + 1)) →")
    o("      (k, q, d, u, (q + 1) * d - u) ∈ constantPrefixThreeBandSurvivors))")
    o("")
    o("private lemma bandPoint_elim {k q d u A : ℕ}")
    o("    (hb : BandPoint k q d u)")
    o("    (hud : u < d)")
    o("    (hA : A = (q + 1) * d - u)")
    o("    (h0 : A ∣ residualProdNat k q (d - u))")
    o("    (h1 : (A + 1) ∣ residualProdNat k q (d - u + (q + 1)))")
    o("    (h2 : (A + 2) ∣ residualProdNat k q (d - u + 2 * (q + 1))) :")
    o("    (k, q, d, u, A) ∈ constantPrefixThreeBandSurvivors := by")
    o("  subst hA")
    o("  exact hb hud h0 h1 h2")

    # per-pair certs + dispatch
    for (k, q) in [(10, 6), (11, 7), (12, 8), (13, 8), (14, 9), (15, 10)]:
        b = BAND[(k, q)]
        c2, e2, W = b["c2"], b["e2"], b["W"]
        um = f"{c2} * d / {e2}"
        bound = BOUND[(k, q)]
        o("")
        for j, (start, size) in enumerate(b["chunks"]):
            tag = CHUNK_TAGS[j]
            o(f"set_option maxRecDepth 200000 in")
            o(f"set_option maxHeartbeats 6000000 in")
            o(f"-- Banded kernel certificate, pair ({k}, {q}), "
              f"gaps {start}..{start + size - 1}.")
            o(f"private theorem constant_band_cert_{k}_{q}_{tag} :")
            o(f"    ∀ (dr : Fin {size}) (i : Fin {W}),")
            o(f"      BandPoint {k} {q} ({start} + (dr : ℕ))")
            o(f"        ({c2} * ({start} + (dr : ℕ)) / {e2} + 1 + (i : ℕ)) := by")
            o(f"  decide")
            o("")
        o(f"private theorem constant_band_mem_{k}_{q} {{d u : ℕ}}")
        o(f"    (hd221 : 221 ≤ d) (hdB : d ≤ {bound})")
        o(f"    (hblo : {um} + 1 ≤ u) (hbW : u - ({um} + 1) < {W}) :")
        o(f"    BandPoint {k} {q} d u := by")
        o(f"  have hu_eq : {um} + 1 + (u - ({um} + 1)) = u := by omega")
        chunks = b["chunks"]
        for j, (start, size) in enumerate(chunks):
            tag = CHUNK_TAGS[j]
            last = j + 1 == len(chunks)
            if not last:
                hi = start + size - 1
                o(f"  by_cases hc{j} : d ≤ {hi}")
                bullet, body_ind = "  · ", "    "
            else:
                bullet, body_ind = "  ", "  "
            dm = f"{start} + (d - {start})"
            o(f"{bullet}have hb : BandPoint {k} {q} ({dm})")
            o(f"{body_ind}    ({c2} * ({dm}) / {e2} + 1 + (u - ({um} + 1))) :=")
            o(f"{body_ind}  constant_band_cert_{k}_{q}_{tag} ⟨d - {start}, by omega⟩")
            o(f"{body_ind}    ⟨u - ({um} + 1), hbW⟩")
            o(f"{body_ind}rw [show {dm} = d from by omega] at hb")
            o(f"{body_ind}rwa [hu_eq] at hb")

    # D3
    o("")
    o("/-- **D3: bounded membership certificate.**  Any constant-quotient")
    o("point of a tabulated pair with `221 ≤ d ≤ constantPrefixThreeBound k q`")
    o("that satisfies the exact ratio window and the residual divisibilities")
    o("of rows one to three is one of the listed band survivors. -/")
    o("set_option linter.unusedVariables false in")
    o("theorem constant_bounded_prefix_three_survivor_mem")
    o("    {k q d u A n : ℕ}")
    o("    (hkq : constantQuotientPairMem k q)")
    o("    (hd221 : 221 ≤ d)")
    o("    (hdB : d ≤ constantPrefixThreeBound k q)")
    o("    (hu1 : 1 ≤ u) (hud : u < d)")
    o("    (hA : A = (q + 1) * d - u)")
    o("    (hn : n + 1 = A)")
    o("    (hup : (n + d + k) ^ k ≤ 4 * (n + k) ^ k)")
    o("    (hlo : 4 * (n + 1) ^ k ≤ (n + d + 1) ^ k)")
    o("    (h0 : ((A : ℤ) ∣ residualRowPoly k q (d - u)))")
    o("    (h1 : (((A + 1 : ℕ) : ℤ) ∣ residualRowPoly k q (d - u + (q + 1))))")
    o("    (h2 : (((A + 2 : ℕ) : ℤ) ∣ residualRowPoly k q (d - u + 2 * (q + 1)))) :")
    o("    (k, q, d, u, A) ∈ constantPrefixThreeBandSurvivors := by")
    o("  have h0' := (int_natCast_dvd_residualRowPoly_iff A k q (d - u)).mp h0")
    o("  have h1' := (int_natCast_dvd_residualRowPoly_iff (A + 1) k q")
    o("    (d - u + (q + 1))).mp h1")
    o("  have h2' := (int_natCast_dvd_residualRowPoly_iff (A + 2) k q")
    o("    (d - u + 2 * (q + 1))).mp h2")
    o("  have hcases : (k = 5 ∧ q = 3) ∨ (k = 6 ∧ q = 3) ∨ (k = 7 ∧ q = 4) ∨")
    o("      (k = 8 ∧ q = 5) ∨ (k = 9 ∧ q = 6) ∨ (k = 10 ∧ q = 6) ∨")
    o("      (k = 11 ∧ q = 7) ∨ (k = 12 ∧ q = 8) ∨ (k = 13 ∧ q = 8) ∨")
    o("      (k = 14 ∧ q = 9) ∨ (k = 15 ∧ q = 10) := by")
    o("    simpa [constantQuotientPairMem, constantQuotientPairs, List.mem_cons,")
    o("      Prod.mk.injEq] using hkq")
    o("  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |")
    o("    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |")
    o("    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩")
    for (k, q) in PAIRS:
        if BOUND[(k, q)] == 220:
            o("  · exact absurd (hd221.trans hdB) (by decide)")
        else:
            b = BAND[(k, q)]
            um = f"{b['c2']} * d / {b['e2']}"
            o(f"  · have hdB' : d ≤ {BOUND[(k, q)]} := le_trans hdB (by decide)")
            o(f"    have hlin1 := ratio_window_linearize_of_pow_bracket")
            o(f"      (N := 4) (A := {b['p1']}) (B := {b['r1']}) (k := {k})")
            o(f"      (n := n) (d := d) (by norm_num) (by norm_num) hup")
            o(f"    have hlin2 := ratio_window_upper_linearize_of_pow_bracket")
            o(f"      (N := 4) (A := {b['p2']}) (B := {b['r2']}) (k := {k})")
            o(f"      (n := n) (d := d) (by norm_num) (by norm_num) hlo")
            o(f"    have hblo : {um} + 1 ≤ u := by omega")
            o(f"    have hbW : u - ({um} + 1) < {b['W']} := by omega")
            o(f"    exact bandPoint_elim (constant_band_mem_{k}_{q} hd221 hdB'")
            o(f"      hblo hbW) hud hA h0' h1' h2'")

    # u = d line
    o("")
    o("set_option maxRecDepth 400000 in")
    o("set_option maxHeartbeats 2000000 in")
    o("-- Kernel certificate for the `(9, 6)` top edge `u = d`: no gap")
    o("-- `d ∈ [221, 1615]` passes the fixed row-two and row-three residual")
    o("-- divisor conditions on the line `A = 6d`.")
    o("private theorem k_nine_u_eq_d_cert :")
    o("    ∀ dr : Fin 1395,")
    o("      ¬ ((6 * (221 + (dr : ℕ)) + 1) ∣ residualProdNat 9 6 (6 + 1) ∧")
    o("         (6 * (221 + (dr : ℕ)) + 2) ∣ residualProdNat 9 6 (2 * (6 + 1))) := by")
    o("  decide")
    o("")
    o("/-- **Top edge `u = d`.**  A constant-quotient point on the boundary")
    o("line `u = d` (that is, `A = q·d`) with `d ≥ 221` inside the upper ratio")
    o("window cannot pass the row-two and row-three residual divisibilities:")
    o("for ten of the eleven pairs the window already fails, and for `(9, 6)`")
    o("the kernel certificate refutes the divisor coincidences up to the")
    o("window crossover.  (On this line the row-one residual is trivially")
    o("satisfied, since `residualRowPoly k q 0 = 0`.) -/")
    o("theorem constant_u_eq_d_no_prefix_three")
    o("    {k q d A n : ℕ}")
    o("    (hkq : constantQuotientPairMem k q)")
    o("    (hd221 : 221 ≤ d)")
    o("    (hA : A = q * d)")
    o("    (hn : n + 1 = A)")
    o("    (hup : (n + d + k) ^ k ≤ 4 * (n + k) ^ k)")
    o("    (h1 : (((A + 1 : ℕ) : ℤ) ∣ residualRowPoly k q (q + 1)))")
    o("    (h2 : (((A + 2 : ℕ) : ℤ) ∣ residualRowPoly k q (2 * (q + 1)))) :")
    o("    False := by")
    o("  have h1' := (int_natCast_dvd_residualRowPoly_iff (A + 1) k q (q + 1)).mp h1")
    o("  have h2' := (int_natCast_dvd_residualRowPoly_iff (A + 2) k q")
    o("    (2 * (q + 1))).mp h2")
    o("  subst hA")
    o("  have hcases : (k = 5 ∧ q = 3) ∨ (k = 6 ∧ q = 3) ∨ (k = 7 ∧ q = 4) ∨")
    o("      (k = 8 ∧ q = 5) ∨ (k = 9 ∧ q = 6) ∨ (k = 10 ∧ q = 6) ∨")
    o("      (k = 11 ∧ q = 7) ∨ (k = 12 ∧ q = 8) ∨ (k = 13 ∧ q = 8) ∨")
    o("      (k = 14 ∧ q = 9) ∨ (k = 15 ∧ q = 10) := by")
    o("    simpa [constantQuotientPairMem, constantQuotientPairs, List.mem_cons,")
    o("      Prod.mk.injEq] using hkq")
    o("  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |")
    o("    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |")
    o("    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩")
    for (k, q) in PAIRS:
        p1, r1 = CAPS[(k, q)]
        o(f"  · have hlin := ratio_window_linearize_of_pow_bracket")
        o(f"      (N := 4) (A := {p1}) (B := {r1}) (k := {k})")
        o(f"      (n := n) (d := d) (by norm_num) (by norm_num) hup")
        if (k, q) != (9, 6):
            o("    omega")
        else:
            o("    have hcert : ¬ ((6 * (221 + (d - 221)) + 1)")
            o("          ∣ residualProdNat 9 6 (6 + 1) ∧")
            o("        (6 * (221 + (d - 221)) + 2)")
            o("          ∣ residualProdNat 9 6 (2 * (6 + 1))) :=")
            o("      k_nine_u_eq_d_cert ⟨d - 221, by omega⟩")
            o("    rw [show 221 + (d - 221) = d from by omega] at hcert")
            o("    exact hcert ⟨h1', h2'⟩")

    # D4
    o("")
    o("/-- **D4: packaged row-four escape.**  Under the bounded")
    o("constant-quotient hypotheses, the residual divisibilities of rows one")
    o("to three force the row-four residual divisibility to fail. -/")
    o("theorem constant_case_row4_escape_of_prefix_three_bound")
    o("    {k q d u A n : ℕ}")
    o("    (hkq : constantQuotientPairMem k q)")
    o("    (hd221 : 221 ≤ d)")
    o("    (hdB : d ≤ constantPrefixThreeBound k q)")
    o("    (hu1 : 1 ≤ u) (hud : u < d)")
    o("    (hA : A = (q + 1) * d - u)")
    o("    (hn : n + 1 = A)")
    o("    (hup : (n + d + k) ^ k ≤ 4 * (n + k) ^ k)")
    o("    (hlo : 4 * (n + 1) ^ k ≤ (n + d + 1) ^ k)")
    o("    (h0 : ((A : ℤ) ∣ residualRowPoly k q (d - u)))")
    o("    (h1 : (((A + 1 : ℕ) : ℤ) ∣ residualRowPoly k q (d - u + (q + 1))))")
    o("    (h2 : (((A + 2 : ℕ) : ℤ) ∣ residualRowPoly k q (d - u + 2 * (q + 1)))) :")
    o("    ¬ (((A + 3 : ℕ) : ℤ) ∣ residualRowPoly k q (d - u + 3 * (q + 1))) :=")
    o("  constant_prefix_three_band_survivors_row4_escape")
    o("    (constant_bounded_prefix_three_survivor_mem hkq hd221 hdB hu1 hud hA")
    o("      hn hup hlo h0 h1 h2)")
    o("")
    o("end Erdos686Variant")
    o("")
    o("end Erdos686")
    o("")
    return "\n".join(L)


def main():
    survivors = verify()
    print("verification OK; generating", OUT)
    with open(OUT, "w") as f:
        f.write(gen(survivors))
    print("wrote", OUT)


if __name__ == "__main__":
    main()
