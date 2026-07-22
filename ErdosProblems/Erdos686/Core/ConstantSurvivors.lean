/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import ErdosProblems.Erdos686.Core.ConstantQuotient

/-!
# Erdős Problem 686: constant-quotient prefix-three survivors

Banded kernel certificates for the constant-quotient branch of the
`N = 4` exclusion.  For each tabulated pair `(k, q)` with per-case gap
bound `constantPrefixThreeBound`, the exact ratio window pins the
deficiency `u = (q+1)·d − A` inside an explicit linear band
`c₂·d/e₂ < u ≤ c₁·d/e₁ + (k−1)` (derived from rational brackets around
`4^(1/k)` via the linearization lemmas).  Kernel `decide` certificates
sweep the whole band and certify that every point passing the residual
divisibilities of rows one to three is one of finitely many listed
survivors — and a second certificate checks that every listed survivor
fails the row-four residual divisibility.  The top edge `u = d`
(`A = q·d`) is handled separately: the upper window kills it outright
for ten of the eleven pairs, and for `(9, 6)` a dedicated certificate
refutes the fixed row-two/row-three divisor coincidences up to the
window crossover `d ≤ 1615`.
-/

namespace Erdos686

namespace Erdos686Variant

/-- Per-case gap bounds for the constant-quotient prefix-three
analysis. -/
def constantPrefixThreeBound : ℕ → ℕ → ℕ
  | 5, 3 => 220
  | 6, 3 => 220
  | 7, 4 => 220
  | 8, 5 => 220
  | 9, 6 => 220
  | 10, 6 => 266
  | 11, 7 => 7029
  | 12, 8 => 2695
  | 13, 8 => 4467
  | 14, 9 => 2811
  | 15, 10 => 2915
  | _, _ => 0

/-- The eleven constant-quotient pairs `(k, q)` of the `N = 4`
branch. -/
def constantQuotientPairs : List (ℕ × ℕ) :=
  [(5, 3), (6, 3), (7, 4), (8, 5), (9, 6), (10, 6), (11, 7), (12, 8), (13, 8), (14, 9), (15, 10)]

/-- Membership in the constant-quotient pair table. -/
def constantQuotientPairMem (k q : ℕ) : Prop :=
  (k, q) ∈ constantQuotientPairs

instance (k q : ℕ) : Decidable (constantQuotientPairMem k q) :=
  inferInstanceAs (Decidable ((k, q) ∈ constantQuotientPairs))

/-- The 45 window points `(k, q, d, u, A)` surviving the residual
divisibilities of rows one to three (exact-arithmetic scan artifact
`compute/artifacts/constant_prefix3_survivors.json`). -/
def constantPrefixThreeSurvivors : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(10, 6, 253, 71, 1700), (10, 6, 254, 78, 1700), (10, 6, 266, 82, 1780),
   (11, 7, 371, 214, 2754), (11, 7, 512, 290, 3806), (11, 7, 1329, 744, 9888),
   (11, 7, 1482, 832, 11024), (11, 7, 1516, 844, 11284), (11, 7, 1935, 1076, 14404),
   (11, 7, 7029, 3907, 52325), (12, 8, 298, 252, 2430), (12, 8, 438, 367, 3575),
   (12, 8, 439, 376, 3575), (12, 8, 1333, 1118, 10879), (12, 8, 2695, 2255, 22000),
   (13, 8, 244, 38, 2158), (13, 8, 398, 48, 3534), (13, 8, 399, 57, 3534), (13, 8, 711, 81, 6318),
   (13, 8, 1468, 173, 13039), (13, 8, 2201, 259, 19550), (13, 8, 4467, 515, 39688),
   (14, 9, 354, 140, 3400), (14, 9, 355, 150, 3400), (14, 9, 453, 180, 4350),
   (14, 9, 454, 190, 4350), (14, 9, 465, 186, 4464), (14, 9, 655, 262, 6288),
   (14, 9, 924, 367, 8873), (14, 9, 1102, 438, 10582), (14, 9, 1880, 746, 18054),
   (14, 9, 2811, 1111, 26999), (15, 10, 235, 167, 2418), (15, 10, 236, 166, 2430),
   (15, 10, 238, 170, 2448), (15, 10, 242, 163, 2499), (15, 10, 243, 174, 2499),
   (15, 10, 282, 192, 2910), (15, 10, 283, 203, 2910), (15, 10, 493, 341, 5082),
   (15, 10, 771, 527, 7954), (15, 10, 1108, 750, 11438), (15, 10, 1766, 1187, 18239),
   (15, 10, 1767, 1198, 18239), (15, 10, 2915, 1966, 30099)]

/-- Six additional residual-passing points of the linear band that lie
just outside the exact ratio window (each is a `d ± 1` shadow of a true
survivor at the same `A`); the banded certificates must list them
too. -/
def constantPrefixThreeBandExtras : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(11, 7, 1517, 852, 11284), (11, 7, 1936, 1084, 14404), (12, 8, 299, 261, 2430),
   (13, 8, 4466, 506, 39688), (14, 9, 925, 377, 8873), (14, 9, 1103, 448, 10582)]

/-- All residual-passing band points: survivors plus band shadows. -/
def constantPrefixThreeBandSurvivors : List (ℕ × ℕ × ℕ × ℕ × ℕ) :=
  constantPrefixThreeSurvivors ++ constantPrefixThreeBandExtras

/-- `ℕ`-valued absolute residual row product
`∏_{s<k} |q·s − r|`, in kernel-friendly recursive form. -/
def residualProdNat : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | m + 1, q, r => residualProdNat m q r * Nat.dist (q * m) r

private lemma natAbs_natCast_sub_natCast (a b : ℕ) :
    ((a : ℤ) - (b : ℤ)).natAbs = Nat.dist a b := by
  rcases Nat.le_total a b with h | h
  · rw [Nat.dist_eq_sub_of_le h,
      show (a : ℤ) - (b : ℤ) = -(((b - a : ℕ) : ℤ)) from by
        rw [Nat.cast_sub h]; ring,
      Int.natAbs_neg, Int.natAbs_natCast]
  · rw [Nat.dist_eq_sub_of_le_right h,
      show (a : ℤ) - (b : ℤ) = ((a - b : ℕ) : ℤ) from by
        rw [Nat.cast_sub h],
      Int.natAbs_natCast]

/-- The absolute value of the residual row polynomial is the `ℕ`
distance product. -/
lemma residualRowPoly_natAbs (k q r : ℕ) :
    (residualRowPoly k q r).natAbs
      = ∏ s ∈ Finset.range k, Nat.dist (q * s) r := by
  unfold residualRowPoly
  induction k with
  | zero => simp
  | succ m ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ,
        Int.natAbs_mul, ih]
      congr 1
      rw [show (q : ℤ) * (m : ℤ) - (r : ℤ)
            = ((q * m : ℕ) : ℤ) - ((r : ℕ) : ℤ) from by push_cast; ring]
      exact natAbs_natCast_sub_natCast (q * m) r

private lemma residualProdNat_eq_prod (k q r : ℕ) :
    residualProdNat k q r = ∏ s ∈ Finset.range k, Nat.dist (q * s) r := by
  induction k with
  | zero => rfl
  | succ m ih => rw [residualProdNat, ih, Finset.prod_range_succ]

/-- Kernel-friendly transfer: `ℤ`-divisibility of the residual row
polynomial by a natural number is `ℕ`-divisibility of the distance
product. -/
lemma int_natCast_dvd_residualRowPoly_iff (m k q r : ℕ) :
    ((m : ℤ) ∣ residualRowPoly k q r) ↔ m ∣ residualProdNat k q r := by
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast, residualRowPoly_natAbs,
    residualProdNat_eq_prod]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
-- Kernel check: every listed band survivor fails the row-four residual.
private theorem constant_band_survivors_row4_escape_cert :
    ∀ x ∈ constantPrefixThreeBandSurvivors,
      ¬ (x.2.2.2.2 + 3)
          ∣ residualProdNat x.1 x.2.1 (x.2.2.1 - x.2.2.2.1 + 3 * (x.2.1 + 1)) := by
  decide

/-- **Row-four escape** for every listed band survivor. -/
theorem constant_prefix_three_band_survivors_row4_escape
    {k q d u A : ℕ}
    (hmem : (k, q, d, u, A) ∈ constantPrefixThreeBandSurvivors) :
    ¬ (((A + 3 : ℕ) : ℤ) ∣ residualRowPoly k q (d - u + 3 * (q + 1))) := by
  rw [int_natCast_dvd_residualRowPoly_iff]
  exact constant_band_survivors_row4_escape_cert _ hmem

/-- **D2: row-four escape** for every one of the 45 exact-window
survivors. -/
theorem constant_prefix_three_survivors_row4_escape
    {k q d u A : ℕ}
    (hmem : (k, q, d, u, A) ∈ constantPrefixThreeSurvivors) :
    ¬ (((A + 3 : ℕ) : ℤ) ∣ residualRowPoly k q (d - u + 3 * (q + 1))) :=
  constant_prefix_three_band_survivors_row4_escape
    (List.mem_append_left constantPrefixThreeBandExtras hmem)

/-- Banded point predicate decided by the kernel certificates: if the
point `u` at gap `d` lies below `d` and passes the residual
divisibilities of rows one to three, it is a listed band survivor. -/
def BandPoint (k q d u : ℕ) : Prop :=
  u < d →
  ((q + 1) * d - u) ∣ residualProdNat k q (d - u) →
  ((q + 1) * d - u + 1) ∣ residualProdNat k q (d - u + (q + 1)) →
  ((q + 1) * d - u + 2) ∣ residualProdNat k q (d - u + 2 * (q + 1)) →
  (k, q, d, u, (q + 1) * d - u) ∈ constantPrefixThreeBandSurvivors

instance (k q d u : ℕ) : Decidable (BandPoint k q d u) :=
  inferInstanceAs (Decidable
    (u < d →
      ((q + 1) * d - u) ∣ residualProdNat k q (d - u) →
      ((q + 1) * d - u + 1) ∣ residualProdNat k q (d - u + (q + 1)) →
      ((q + 1) * d - u + 2) ∣ residualProdNat k q (d - u + 2 * (q + 1)) →
      (k, q, d, u, (q + 1) * d - u) ∈ constantPrefixThreeBandSurvivors))

private lemma bandPoint_elim {k q d u A : ℕ}
    (hb : BandPoint k q d u)
    (hud : u < d)
    (hA : A = (q + 1) * d - u)
    (h0 : A ∣ residualProdNat k q (d - u))
    (h1 : (A + 1) ∣ residualProdNat k q (d - u + (q + 1)))
    (h2 : (A + 2) ∣ residualProdNat k q (d - u + 2 * (q + 1))) :
    (k, q, d, u, A) ∈ constantPrefixThreeBandSurvivors := by
  subst hA
  exact hb hud h0 h1 h2

set_option maxRecDepth 200000 in
set_option maxHeartbeats 6000000 in
-- Banded kernel certificate, pair (10, 6), gaps 221..266.
private theorem constant_band_cert_10_6_a :
    ∀ (dr : Fin 46) (i : Fin 10),
      BandPoint 10 6 (221 + (dr : ℕ))
        (3 * (221 + (dr : ℕ)) / 11 + 1 + (i : ℕ)) := by
  decide

private theorem constant_band_mem_10_6 {d u : ℕ}
    (hd221 : 221 ≤ d) (hdB : d ≤ 266)
    (hblo : 3 * d / 11 + 1 ≤ u) (hbW : u - (3 * d / 11 + 1) < 10) :
    BandPoint 10 6 d u := by
  have hu_eq : 3 * d / 11 + 1 + (u - (3 * d / 11 + 1)) = u := by omega
  have hb : BandPoint 10 6 (221 + (d - 221))
      (3 * (221 + (d - 221)) / 11 + 1 + (u - (3 * d / 11 + 1))) :=
    constant_band_cert_10_6_a ⟨d - 221, by omega⟩
      ⟨u - (3 * d / 11 + 1), hbW⟩
  rw [show 221 + (d - 221) = d from by omega] at hb
  rwa [hu_eq] at hb

set_option maxRecDepth 200000 in
set_option maxHeartbeats 6000000 in
-- Banded kernel certificate, pair (11, 7), gaps 221..1193.
private theorem constant_band_cert_11_7_a :
    ∀ (dr : Fin 973) (i : Fin 11),
      BandPoint 11 7 (221 + (dr : ℕ))
        (208 * (221 + (dr : ℕ)) / 375 + 1 + (i : ℕ)) := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 6000000 in
-- Banded kernel certificate, pair (11, 7), gaps 1194..2166.
private theorem constant_band_cert_11_7_b :
    ∀ (dr : Fin 973) (i : Fin 11),
      BandPoint 11 7 (1194 + (dr : ℕ))
        (208 * (1194 + (dr : ℕ)) / 375 + 1 + (i : ℕ)) := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 6000000 in
-- Banded kernel certificate, pair (11, 7), gaps 2167..3139.
private theorem constant_band_cert_11_7_c :
    ∀ (dr : Fin 973) (i : Fin 11),
      BandPoint 11 7 (2167 + (dr : ℕ))
        (208 * (2167 + (dr : ℕ)) / 375 + 1 + (i : ℕ)) := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 6000000 in
-- Banded kernel certificate, pair (11, 7), gaps 3140..4112.
private theorem constant_band_cert_11_7_d :
    ∀ (dr : Fin 973) (i : Fin 11),
      BandPoint 11 7 (3140 + (dr : ℕ))
        (208 * (3140 + (dr : ℕ)) / 375 + 1 + (i : ℕ)) := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 6000000 in
-- Banded kernel certificate, pair (11, 7), gaps 4113..5085.
private theorem constant_band_cert_11_7_e :
    ∀ (dr : Fin 973) (i : Fin 11),
      BandPoint 11 7 (4113 + (dr : ℕ))
        (208 * (4113 + (dr : ℕ)) / 375 + 1 + (i : ℕ)) := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 6000000 in
-- Banded kernel certificate, pair (11, 7), gaps 5086..6058.
private theorem constant_band_cert_11_7_f :
    ∀ (dr : Fin 973) (i : Fin 11),
      BandPoint 11 7 (5086 + (dr : ℕ))
        (208 * (5086 + (dr : ℕ)) / 375 + 1 + (i : ℕ)) := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 6000000 in
-- Banded kernel certificate, pair (11, 7), gaps 6059..7029.
private theorem constant_band_cert_11_7_g :
    ∀ (dr : Fin 971) (i : Fin 11),
      BandPoint 11 7 (6059 + (dr : ℕ))
        (208 * (6059 + (dr : ℕ)) / 375 + 1 + (i : ℕ)) := by
  decide

private theorem constant_band_mem_11_7 {d u : ℕ}
    (hd221 : 221 ≤ d) (hdB : d ≤ 7029)
    (hblo : 208 * d / 375 + 1 ≤ u) (hbW : u - (208 * d / 375 + 1) < 11) :
    BandPoint 11 7 d u := by
  have hu_eq : 208 * d / 375 + 1 + (u - (208 * d / 375 + 1)) = u := by omega
  by_cases hc0 : d ≤ 1193
  · have hb : BandPoint 11 7 (221 + (d - 221))
        (208 * (221 + (d - 221)) / 375 + 1 + (u - (208 * d / 375 + 1))) :=
      constant_band_cert_11_7_a ⟨d - 221, by omega⟩
        ⟨u - (208 * d / 375 + 1), hbW⟩
    rw [show 221 + (d - 221) = d from by omega] at hb
    rwa [hu_eq] at hb
  by_cases hc1 : d ≤ 2166
  · have hb : BandPoint 11 7 (1194 + (d - 1194))
        (208 * (1194 + (d - 1194)) / 375 + 1 + (u - (208 * d / 375 + 1))) :=
      constant_band_cert_11_7_b ⟨d - 1194, by omega⟩
        ⟨u - (208 * d / 375 + 1), hbW⟩
    rw [show 1194 + (d - 1194) = d from by omega] at hb
    rwa [hu_eq] at hb
  by_cases hc2 : d ≤ 3139
  · have hb : BandPoint 11 7 (2167 + (d - 2167))
        (208 * (2167 + (d - 2167)) / 375 + 1 + (u - (208 * d / 375 + 1))) :=
      constant_band_cert_11_7_c ⟨d - 2167, by omega⟩
        ⟨u - (208 * d / 375 + 1), hbW⟩
    rw [show 2167 + (d - 2167) = d from by omega] at hb
    rwa [hu_eq] at hb
  by_cases hc3 : d ≤ 4112
  · have hb : BandPoint 11 7 (3140 + (d - 3140))
        (208 * (3140 + (d - 3140)) / 375 + 1 + (u - (208 * d / 375 + 1))) :=
      constant_band_cert_11_7_d ⟨d - 3140, by omega⟩
        ⟨u - (208 * d / 375 + 1), hbW⟩
    rw [show 3140 + (d - 3140) = d from by omega] at hb
    rwa [hu_eq] at hb
  by_cases hc4 : d ≤ 5085
  · have hb : BandPoint 11 7 (4113 + (d - 4113))
        (208 * (4113 + (d - 4113)) / 375 + 1 + (u - (208 * d / 375 + 1))) :=
      constant_band_cert_11_7_e ⟨d - 4113, by omega⟩
        ⟨u - (208 * d / 375 + 1), hbW⟩
    rw [show 4113 + (d - 4113) = d from by omega] at hb
    rwa [hu_eq] at hb
  by_cases hc5 : d ≤ 6058
  · have hb : BandPoint 11 7 (5086 + (d - 5086))
        (208 * (5086 + (d - 5086)) / 375 + 1 + (u - (208 * d / 375 + 1))) :=
      constant_band_cert_11_7_f ⟨d - 5086, by omega⟩
        ⟨u - (208 * d / 375 + 1), hbW⟩
    rw [show 5086 + (d - 5086) = d from by omega] at hb
    rwa [hu_eq] at hb
  have hb : BandPoint 11 7 (6059 + (d - 6059))
      (208 * (6059 + (d - 6059)) / 375 + 1 + (u - (208 * d / 375 + 1))) :=
    constant_band_cert_11_7_g ⟨d - 6059, by omega⟩
      ⟨u - (208 * d / 375 + 1), hbW⟩
  rw [show 6059 + (d - 6059) = d from by omega] at hb
  rwa [hu_eq] at hb

set_option maxRecDepth 200000 in
set_option maxHeartbeats 6000000 in
-- Banded kernel certificate, pair (12, 8), gaps 221..1045.
private theorem constant_band_cert_12_8_a :
    ∀ (dr : Fin 825) (i : Fin 12),
      BandPoint 12 8 (221 + (dr : ℕ))
        (161 * (221 + (dr : ℕ)) / 193 + 1 + (i : ℕ)) := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 6000000 in
-- Banded kernel certificate, pair (12, 8), gaps 1046..1870.
private theorem constant_band_cert_12_8_b :
    ∀ (dr : Fin 825) (i : Fin 12),
      BandPoint 12 8 (1046 + (dr : ℕ))
        (161 * (1046 + (dr : ℕ)) / 193 + 1 + (i : ℕ)) := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 6000000 in
-- Banded kernel certificate, pair (12, 8), gaps 1871..2695.
private theorem constant_band_cert_12_8_c :
    ∀ (dr : Fin 825) (i : Fin 12),
      BandPoint 12 8 (1871 + (dr : ℕ))
        (161 * (1871 + (dr : ℕ)) / 193 + 1 + (i : ℕ)) := by
  decide

private theorem constant_band_mem_12_8 {d u : ℕ}
    (hd221 : 221 ≤ d) (hdB : d ≤ 2695)
    (hblo : 161 * d / 193 + 1 ≤ u) (hbW : u - (161 * d / 193 + 1) < 12) :
    BandPoint 12 8 d u := by
  have hu_eq : 161 * d / 193 + 1 + (u - (161 * d / 193 + 1)) = u := by omega
  by_cases hc0 : d ≤ 1045
  · have hb : BandPoint 12 8 (221 + (d - 221))
        (161 * (221 + (d - 221)) / 193 + 1 + (u - (161 * d / 193 + 1))) :=
      constant_band_cert_12_8_a ⟨d - 221, by omega⟩
        ⟨u - (161 * d / 193 + 1), hbW⟩
    rw [show 221 + (d - 221) = d from by omega] at hb
    rwa [hu_eq] at hb
  by_cases hc1 : d ≤ 1870
  · have hb : BandPoint 12 8 (1046 + (d - 1046))
        (161 * (1046 + (d - 1046)) / 193 + 1 + (u - (161 * d / 193 + 1))) :=
      constant_band_cert_12_8_b ⟨d - 1046, by omega⟩
        ⟨u - (161 * d / 193 + 1), hbW⟩
    rw [show 1046 + (d - 1046) = d from by omega] at hb
    rwa [hu_eq] at hb
  have hb : BandPoint 12 8 (1871 + (d - 1871))
      (161 * (1871 + (d - 1871)) / 193 + 1 + (u - (161 * d / 193 + 1))) :=
    constant_band_cert_12_8_c ⟨d - 1871, by omega⟩
      ⟨u - (161 * d / 193 + 1), hbW⟩
  rw [show 1871 + (d - 1871) = d from by omega] at hb
  rwa [hu_eq] at hb

set_option maxRecDepth 200000 in
set_option maxHeartbeats 6000000 in
-- Banded kernel certificate, pair (13, 8), gaps 221..1070.
private theorem constant_band_cert_13_8_a :
    ∀ (dr : Fin 850) (i : Fin 14),
      BandPoint 13 8 (221 + (dr : ℕ))
        (6 * (221 + (dr : ℕ)) / 53 + 1 + (i : ℕ)) := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 6000000 in
-- Banded kernel certificate, pair (13, 8), gaps 1071..1920.
private theorem constant_band_cert_13_8_b :
    ∀ (dr : Fin 850) (i : Fin 14),
      BandPoint 13 8 (1071 + (dr : ℕ))
        (6 * (1071 + (dr : ℕ)) / 53 + 1 + (i : ℕ)) := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 6000000 in
-- Banded kernel certificate, pair (13, 8), gaps 1921..2770.
private theorem constant_band_cert_13_8_c :
    ∀ (dr : Fin 850) (i : Fin 14),
      BandPoint 13 8 (1921 + (dr : ℕ))
        (6 * (1921 + (dr : ℕ)) / 53 + 1 + (i : ℕ)) := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 6000000 in
-- Banded kernel certificate, pair (13, 8), gaps 2771..3620.
private theorem constant_band_cert_13_8_d :
    ∀ (dr : Fin 850) (i : Fin 14),
      BandPoint 13 8 (2771 + (dr : ℕ))
        (6 * (2771 + (dr : ℕ)) / 53 + 1 + (i : ℕ)) := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 6000000 in
-- Banded kernel certificate, pair (13, 8), gaps 3621..4467.
private theorem constant_band_cert_13_8_e :
    ∀ (dr : Fin 847) (i : Fin 14),
      BandPoint 13 8 (3621 + (dr : ℕ))
        (6 * (3621 + (dr : ℕ)) / 53 + 1 + (i : ℕ)) := by
  decide

private theorem constant_band_mem_13_8 {d u : ℕ}
    (hd221 : 221 ≤ d) (hdB : d ≤ 4467)
    (hblo : 6 * d / 53 + 1 ≤ u) (hbW : u - (6 * d / 53 + 1) < 14) :
    BandPoint 13 8 d u := by
  have hu_eq : 6 * d / 53 + 1 + (u - (6 * d / 53 + 1)) = u := by omega
  by_cases hc0 : d ≤ 1070
  · have hb : BandPoint 13 8 (221 + (d - 221))
        (6 * (221 + (d - 221)) / 53 + 1 + (u - (6 * d / 53 + 1))) :=
      constant_band_cert_13_8_a ⟨d - 221, by omega⟩
        ⟨u - (6 * d / 53 + 1), hbW⟩
    rw [show 221 + (d - 221) = d from by omega] at hb
    rwa [hu_eq] at hb
  by_cases hc1 : d ≤ 1920
  · have hb : BandPoint 13 8 (1071 + (d - 1071))
        (6 * (1071 + (d - 1071)) / 53 + 1 + (u - (6 * d / 53 + 1))) :=
      constant_band_cert_13_8_b ⟨d - 1071, by omega⟩
        ⟨u - (6 * d / 53 + 1), hbW⟩
    rw [show 1071 + (d - 1071) = d from by omega] at hb
    rwa [hu_eq] at hb
  by_cases hc2 : d ≤ 2770
  · have hb : BandPoint 13 8 (1921 + (d - 1921))
        (6 * (1921 + (d - 1921)) / 53 + 1 + (u - (6 * d / 53 + 1))) :=
      constant_band_cert_13_8_c ⟨d - 1921, by omega⟩
        ⟨u - (6 * d / 53 + 1), hbW⟩
    rw [show 1921 + (d - 1921) = d from by omega] at hb
    rwa [hu_eq] at hb
  by_cases hc3 : d ≤ 3620
  · have hb : BandPoint 13 8 (2771 + (d - 2771))
        (6 * (2771 + (d - 2771)) / 53 + 1 + (u - (6 * d / 53 + 1))) :=
      constant_band_cert_13_8_d ⟨d - 2771, by omega⟩
        ⟨u - (6 * d / 53 + 1), hbW⟩
    rw [show 2771 + (d - 2771) = d from by omega] at hb
    rwa [hu_eq] at hb
  have hb : BandPoint 13 8 (3621 + (d - 3621))
      (6 * (3621 + (d - 3621)) / 53 + 1 + (u - (6 * d / 53 + 1))) :=
    constant_band_cert_13_8_e ⟨d - 3621, by omega⟩
      ⟨u - (6 * d / 53 + 1), hbW⟩
  rw [show 3621 + (d - 3621) = d from by omega] at hb
  rwa [hu_eq] at hb

set_option maxRecDepth 200000 in
set_option maxHeartbeats 6000000 in
-- Banded kernel certificate, pair (14, 9), gaps 221..1084.
private theorem constant_band_cert_14_9_a :
    ∀ (dr : Fin 864) (i : Fin 15),
      BandPoint 14 9 (221 + (dr : ℕ))
        (11 * (221 + (dr : ℕ)) / 28 + 1 + (i : ℕ)) := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 6000000 in
-- Banded kernel certificate, pair (14, 9), gaps 1085..1948.
private theorem constant_band_cert_14_9_b :
    ∀ (dr : Fin 864) (i : Fin 15),
      BandPoint 14 9 (1085 + (dr : ℕ))
        (11 * (1085 + (dr : ℕ)) / 28 + 1 + (i : ℕ)) := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 6000000 in
-- Banded kernel certificate, pair (14, 9), gaps 1949..2811.
private theorem constant_band_cert_14_9_c :
    ∀ (dr : Fin 863) (i : Fin 15),
      BandPoint 14 9 (1949 + (dr : ℕ))
        (11 * (1949 + (dr : ℕ)) / 28 + 1 + (i : ℕ)) := by
  decide

private theorem constant_band_mem_14_9 {d u : ℕ}
    (hd221 : 221 ≤ d) (hdB : d ≤ 2811)
    (hblo : 11 * d / 28 + 1 ≤ u) (hbW : u - (11 * d / 28 + 1) < 15) :
    BandPoint 14 9 d u := by
  have hu_eq : 11 * d / 28 + 1 + (u - (11 * d / 28 + 1)) = u := by omega
  by_cases hc0 : d ≤ 1084
  · have hb : BandPoint 14 9 (221 + (d - 221))
        (11 * (221 + (d - 221)) / 28 + 1 + (u - (11 * d / 28 + 1))) :=
      constant_band_cert_14_9_a ⟨d - 221, by omega⟩
        ⟨u - (11 * d / 28 + 1), hbW⟩
    rw [show 221 + (d - 221) = d from by omega] at hb
    rwa [hu_eq] at hb
  by_cases hc1 : d ≤ 1948
  · have hb : BandPoint 14 9 (1085 + (d - 1085))
        (11 * (1085 + (d - 1085)) / 28 + 1 + (u - (11 * d / 28 + 1))) :=
      constant_band_cert_14_9_b ⟨d - 1085, by omega⟩
        ⟨u - (11 * d / 28 + 1), hbW⟩
    rw [show 1085 + (d - 1085) = d from by omega] at hb
    rwa [hu_eq] at hb
  have hb : BandPoint 14 9 (1949 + (d - 1949))
      (11 * (1949 + (d - 1949)) / 28 + 1 + (u - (11 * d / 28 + 1))) :=
    constant_band_cert_14_9_c ⟨d - 1949, by omega⟩
      ⟨u - (11 * d / 28 + 1), hbW⟩
  rw [show 1949 + (d - 1949) = d from by omega] at hb
  rwa [hu_eq] at hb

set_option maxRecDepth 200000 in
set_option maxHeartbeats 6000000 in
-- Banded kernel certificate, pair (15, 10), gaps 221..1119.
private theorem constant_band_cert_15_10_a :
    ∀ (dr : Fin 899) (i : Fin 15),
      BandPoint 15 10 (221 + (dr : ℕ))
        (43 * (221 + (dr : ℕ)) / 64 + 1 + (i : ℕ)) := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 6000000 in
-- Banded kernel certificate, pair (15, 10), gaps 1120..2018.
private theorem constant_band_cert_15_10_b :
    ∀ (dr : Fin 899) (i : Fin 15),
      BandPoint 15 10 (1120 + (dr : ℕ))
        (43 * (1120 + (dr : ℕ)) / 64 + 1 + (i : ℕ)) := by
  decide

set_option maxRecDepth 200000 in
set_option maxHeartbeats 6000000 in
-- Banded kernel certificate, pair (15, 10), gaps 2019..2915.
private theorem constant_band_cert_15_10_c :
    ∀ (dr : Fin 897) (i : Fin 15),
      BandPoint 15 10 (2019 + (dr : ℕ))
        (43 * (2019 + (dr : ℕ)) / 64 + 1 + (i : ℕ)) := by
  decide

private theorem constant_band_mem_15_10 {d u : ℕ}
    (hd221 : 221 ≤ d) (hdB : d ≤ 2915)
    (hblo : 43 * d / 64 + 1 ≤ u) (hbW : u - (43 * d / 64 + 1) < 15) :
    BandPoint 15 10 d u := by
  have hu_eq : 43 * d / 64 + 1 + (u - (43 * d / 64 + 1)) = u := by omega
  by_cases hc0 : d ≤ 1119
  · have hb : BandPoint 15 10 (221 + (d - 221))
        (43 * (221 + (d - 221)) / 64 + 1 + (u - (43 * d / 64 + 1))) :=
      constant_band_cert_15_10_a ⟨d - 221, by omega⟩
        ⟨u - (43 * d / 64 + 1), hbW⟩
    rw [show 221 + (d - 221) = d from by omega] at hb
    rwa [hu_eq] at hb
  by_cases hc1 : d ≤ 2018
  · have hb : BandPoint 15 10 (1120 + (d - 1120))
        (43 * (1120 + (d - 1120)) / 64 + 1 + (u - (43 * d / 64 + 1))) :=
      constant_band_cert_15_10_b ⟨d - 1120, by omega⟩
        ⟨u - (43 * d / 64 + 1), hbW⟩
    rw [show 1120 + (d - 1120) = d from by omega] at hb
    rwa [hu_eq] at hb
  have hb : BandPoint 15 10 (2019 + (d - 2019))
      (43 * (2019 + (d - 2019)) / 64 + 1 + (u - (43 * d / 64 + 1))) :=
    constant_band_cert_15_10_c ⟨d - 2019, by omega⟩
      ⟨u - (43 * d / 64 + 1), hbW⟩
  rw [show 2019 + (d - 2019) = d from by omega] at hb
  rwa [hu_eq] at hb

set_option linter.unusedVariables false in
/-- **D3: bounded membership certificate.**  Any constant-quotient
point of a tabulated pair with `221 ≤ d ≤ constantPrefixThreeBound k q`
that satisfies the exact ratio window and the residual divisibilities
of rows one to three is one of the listed band survivors. -/
theorem constant_bounded_prefix_three_survivor_mem
    {k q d u A n : ℕ}
    (hkq : constantQuotientPairMem k q)
    (hd221 : 221 ≤ d)
    (hdB : d ≤ constantPrefixThreeBound k q)
    (hu1 : 1 ≤ u) (hud : u < d)
    (hA : A = (q + 1) * d - u)
    (hn : n + 1 = A)
    (hup : (n + d + k) ^ k ≤ 4 * (n + k) ^ k)
    (hlo : 4 * (n + 1) ^ k ≤ (n + d + 1) ^ k)
    (h0 : ((A : ℤ) ∣ residualRowPoly k q (d - u)))
    (h1 : (((A + 1 : ℕ) : ℤ) ∣ residualRowPoly k q (d - u + (q + 1))))
    (h2 : (((A + 2 : ℕ) : ℤ) ∣ residualRowPoly k q (d - u + 2 * (q + 1)))) :
    (k, q, d, u, A) ∈ constantPrefixThreeBandSurvivors := by
  have h0' := (int_natCast_dvd_residualRowPoly_iff A k q (d - u)).mp h0
  have h1' := (int_natCast_dvd_residualRowPoly_iff (A + 1) k q
    (d - u + (q + 1))).mp h1
  have h2' := (int_natCast_dvd_residualRowPoly_iff (A + 2) k q
    (d - u + 2 * (q + 1))).mp h2
  have hcases : (k = 5 ∧ q = 3) ∨ (k = 6 ∧ q = 3) ∨ (k = 7 ∧ q = 4) ∨
      (k = 8 ∧ q = 5) ∨ (k = 9 ∧ q = 6) ∨ (k = 10 ∧ q = 6) ∨
      (k = 11 ∧ q = 7) ∨ (k = 12 ∧ q = 8) ∨ (k = 13 ∧ q = 8) ∨
      (k = 14 ∧ q = 9) ∨ (k = 15 ∧ q = 10) := by
    simpa [constantQuotientPairMem, constantQuotientPairs, List.mem_cons,
      Prod.mk.injEq] using hkq
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact absurd (hd221.trans hdB) (by decide)
  · exact absurd (hd221.trans hdB) (by decide)
  · exact absurd (hd221.trans hdB) (by decide)
  · exact absurd (hd221.trans hdB) (by decide)
  · exact absurd (hd221.trans hdB) (by decide)
  · have hdB' : d ≤ 266 := le_trans hdB (by decide)
    have hlin1 := ratio_window_linearize_of_pow_bracket
      (N := 4) (A := 224) (B := 195) (k := 10)
      (n := n) (d := d) (by norm_num) (by norm_num) hup
    have hlin2 := ratio_window_upper_linearize_of_pow_bracket
      (N := 4) (A := 85) (B := 74) (k := 10)
      (n := n) (d := d) (by norm_num) (by norm_num) hlo
    have hblo : 3 * d / 11 + 1 ≤ u := by omega
    have hbW : u - (3 * d / 11 + 1) < 10 := by omega
    exact bandPoint_elim (constant_band_mem_10_6 hd221 hdB'
      hblo hbW) hud hA h0' h1' h2'
  · have hdB' : d ≤ 7029 := le_trans hdB (by decide)
    have hlin1 := ratio_window_linearize_of_pow_bracket
      (N := 4) (A := 1081) (B := 953) (k := 11)
      (n := n) (d := d) (by norm_num) (by norm_num) hup
    have hlin2 := ratio_window_upper_linearize_of_pow_bracket
      (N := 4) (A := 3167) (B := 2792) (k := 11)
      (n := n) (d := d) (by norm_num) (by norm_num) hlo
    have hblo : 208 * d / 375 + 1 ≤ u := by omega
    have hbW : u - (208 * d / 375 + 1) < 11 := by omega
    exact bandPoint_elim (constant_band_mem_11_7 hd221 hdB'
      hblo hbW) hud hA h0' h1' h2'
  · have hdB' : d ≤ 2695 := le_trans hdB (by decide)
    have hlin1 := ratio_window_linearize_of_pow_bracket
      (N := 4) (A := 3483) (B := 3103) (k := 12)
      (n := n) (d := d) (by norm_num) (by norm_num) hup
    have hlin2 := ratio_window_upper_linearize_of_pow_bracket
      (N := 4) (A := 1769) (B := 1576) (k := 12)
      (n := n) (d := d) (by norm_num) (by norm_num) hlo
    have hblo : 161 * d / 193 + 1 ≤ u := by omega
    have hbW : u - (161 * d / 193 + 1) < 12 := by omega
    exact bandPoint_elim (constant_band_mem_12_8 hd221 hdB'
      hblo hbW) hud hA h0' h1' h2'
  · have hdB' : d ≤ 4467 := le_trans hdB (by decide)
    have hlin1 := ratio_window_linearize_of_pow_bracket
      (N := 4) (A := 435) (B := 391) (k := 13)
      (n := n) (d := d) (by norm_num) (by norm_num) hup
    have hlin2 := ratio_window_upper_linearize_of_pow_bracket
      (N := 4) (A := 524) (B := 471) (k := 13)
      (n := n) (d := d) (by norm_num) (by norm_num) hlo
    have hblo : 6 * d / 53 + 1 ≤ u := by omega
    have hbW : u - (6 * d / 53 + 1) < 14 := by omega
    exact bandPoint_elim (constant_band_mem_13_8 hd221 hdB'
      hblo hbW) hud hA h0' h1' h2'
  · have hdB' : d ≤ 2811 := le_trans hdB (by decide)
    have hlin1 := ratio_window_linearize_of_pow_bracket
      (N := 4) (A := 647) (B := 586) (k := 14)
      (n := n) (d := d) (by norm_num) (by norm_num) hup
    have hlin2 := ratio_window_upper_linearize_of_pow_bracket
      (N := 4) (A := 297) (B := 269) (k := 14)
      (n := n) (d := d) (by norm_num) (by norm_num) hlo
    have hblo : 11 * d / 28 + 1 ≤ u := by omega
    have hbW : u - (11 * d / 28 + 1) < 15 := by omega
    exact bandPoint_elim (constant_band_mem_14_9 hd221 hdB'
      hblo hbW) hud hA h0' h1' h2'
  · have hdB' : d ≤ 2915 := le_trans hdB (by decide)
    have hlin1 := ratio_window_linearize_of_pow_bracket
      (N := 4) (A := 691) (B := 630) (k := 15)
      (n := n) (d := d) (by norm_num) (by norm_num) hup
    have hlin2 := ratio_window_upper_linearize_of_pow_bracket
      (N := 4) (A := 725) (B := 661) (k := 15)
      (n := n) (d := d) (by norm_num) (by norm_num) hlo
    have hblo : 43 * d / 64 + 1 ≤ u := by omega
    have hbW : u - (43 * d / 64 + 1) < 15 := by omega
    exact bandPoint_elim (constant_band_mem_15_10 hd221 hdB'
      hblo hbW) hud hA h0' h1' h2'

set_option maxRecDepth 400000 in
set_option maxHeartbeats 2000000 in
-- Kernel certificate for the `(9, 6)` top edge `u = d`: no gap
-- `d ∈ [221, 1615]` passes the fixed row-two and row-three residual
-- divisor conditions on the line `A = 6d`.
private theorem k_nine_u_eq_d_cert :
    ∀ dr : Fin 1395,
      ¬ ((6 * (221 + (dr : ℕ)) + 1) ∣ residualProdNat 9 6 (6 + 1) ∧
         (6 * (221 + (dr : ℕ)) + 2) ∣ residualProdNat 9 6 (2 * (6 + 1))) := by
  decide

/-- **Top edge `u = d`.**  A constant-quotient point on the boundary
line `u = d` (that is, `A = q·d`) with `d ≥ 221` inside the upper ratio
window cannot pass the row-two and row-three residual divisibilities:
for ten of the eleven pairs the window already fails, and for `(9, 6)`
the kernel certificate refutes the divisor coincidences up to the
window crossover.  (On this line the row-one residual is trivially
satisfied, since `residualRowPoly k q 0 = 0`.) -/
theorem constant_u_eq_d_no_prefix_three
    {k q d A n : ℕ}
    (hkq : constantQuotientPairMem k q)
    (hd221 : 221 ≤ d)
    (hA : A = q * d)
    (hn : n + 1 = A)
    (hup : (n + d + k) ^ k ≤ 4 * (n + k) ^ k)
    (h1 : (((A + 1 : ℕ) : ℤ) ∣ residualRowPoly k q (q + 1)))
    (h2 : (((A + 2 : ℕ) : ℤ) ∣ residualRowPoly k q (2 * (q + 1)))) :
    False := by
  have h1' := (int_natCast_dvd_residualRowPoly_iff (A + 1) k q (q + 1)).mp h1
  have h2' := (int_natCast_dvd_residualRowPoly_iff (A + 2) k q
    (2 * (q + 1))).mp h2
  subst hA
  have hcases : (k = 5 ∧ q = 3) ∨ (k = 6 ∧ q = 3) ∨ (k = 7 ∧ q = 4) ∨
      (k = 8 ∧ q = 5) ∨ (k = 9 ∧ q = 6) ∨ (k = 10 ∧ q = 6) ∨
      (k = 11 ∧ q = 7) ∨ (k = 12 ∧ q = 8) ∨ (k = 13 ∧ q = 8) ∨
      (k = 14 ∧ q = 9) ∨ (k = 15 ∧ q = 10) := by
    simpa [constantQuotientPairMem, constantQuotientPairs, List.mem_cons,
      Prod.mk.injEq] using hkq
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hlin := ratio_window_linearize_of_pow_bracket
      (N := 4) (A := 33) (B := 25) (k := 5)
      (n := n) (d := d) (by norm_num) (by norm_num) hup
    omega
  · have hlin := ratio_window_linearize_of_pow_bracket
      (N := 4) (A := 63) (B := 50) (k := 6)
      (n := n) (d := d) (by norm_num) (by norm_num) hup
    omega
  · have hlin := ratio_window_linearize_of_pow_bracket
      (N := 4) (A := 50) (B := 41) (k := 7)
      (n := n) (d := d) (by norm_num) (by norm_num) hup
    omega
  · have hlin := ratio_window_linearize_of_pow_bracket
      (N := 4) (A := 25) (B := 21) (k := 8)
      (n := n) (d := d) (by norm_num) (by norm_num) hup
    omega
  · have hlin := ratio_window_linearize_of_pow_bracket
      (N := 4) (A := 1415) (B := 1213) (k := 9)
      (n := n) (d := d) (by norm_num) (by norm_num) hup
    have hcert : ¬ ((6 * (221 + (d - 221)) + 1)
          ∣ residualProdNat 9 6 (6 + 1) ∧
        (6 * (221 + (d - 221)) + 2)
          ∣ residualProdNat 9 6 (2 * (6 + 1))) :=
      k_nine_u_eq_d_cert ⟨d - 221, by omega⟩
    rw [show 221 + (d - 221) = d from by omega] at hcert
    exact hcert ⟨h1', h2'⟩
  · have hlin := ratio_window_linearize_of_pow_bracket
      (N := 4) (A := 54) (B := 47) (k := 10)
      (n := n) (d := d) (by norm_num) (by norm_num) hup
    omega
  · have hlin := ratio_window_linearize_of_pow_bracket
      (N := 4) (A := 42) (B := 37) (k := 11)
      (n := n) (d := d) (by norm_num) (by norm_num) hup
    omega
  · have hlin := ratio_window_linearize_of_pow_bracket
      (N := 4) (A := 174) (B := 155) (k := 12)
      (n := n) (d := d) (by norm_num) (by norm_num) hup
    omega
  · have hlin := ratio_window_linearize_of_pow_bracket
      (N := 4) (A := 49) (B := 44) (k := 13)
      (n := n) (d := d) (by norm_num) (by norm_num) hup
    omega
  · have hlin := ratio_window_linearize_of_pow_bracket
      (N := 4) (A := 53) (B := 48) (k := 14)
      (n := n) (d := d) (by norm_num) (by norm_num) hup
    omega
  · have hlin := ratio_window_linearize_of_pow_bracket
      (N := 4) (A := 45) (B := 41) (k := 15)
      (n := n) (d := d) (by norm_num) (by norm_num) hup
    omega

/-- **D4: packaged row-four escape.**  Under the bounded
constant-quotient hypotheses, the residual divisibilities of rows one
to three force the row-four residual divisibility to fail. -/
theorem constant_case_row4_escape_of_prefix_three_bound
    {k q d u A n : ℕ}
    (hkq : constantQuotientPairMem k q)
    (hd221 : 221 ≤ d)
    (hdB : d ≤ constantPrefixThreeBound k q)
    (hu1 : 1 ≤ u) (hud : u < d)
    (hA : A = (q + 1) * d - u)
    (hn : n + 1 = A)
    (hup : (n + d + k) ^ k ≤ 4 * (n + k) ^ k)
    (hlo : 4 * (n + 1) ^ k ≤ (n + d + 1) ^ k)
    (h0 : ((A : ℤ) ∣ residualRowPoly k q (d - u)))
    (h1 : (((A + 1 : ℕ) : ℤ) ∣ residualRowPoly k q (d - u + (q + 1))))
    (h2 : (((A + 2 : ℕ) : ℤ) ∣ residualRowPoly k q (d - u + 2 * (q + 1)))) :
    ¬ (((A + 3 : ℕ) : ℤ) ∣ residualRowPoly k q (d - u + 3 * (q + 1))) :=
  constant_prefix_three_band_survivors_row4_escape
    (constant_bounded_prefix_three_survivor_mem hkq hd221 hdB hu1 hud hA
      hn hup hlo h0 h1 h2)

end Erdos686Variant

end Erdos686
