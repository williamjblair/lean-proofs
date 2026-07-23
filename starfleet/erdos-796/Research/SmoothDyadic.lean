import Research.SmoothClassification

namespace Erdos796

/-- A three-factor decomposition can be sorted without changing its product. -/
theorem exists_sorted_three_large {z d : ℕ}
    (h : HasThreeLargeFactors z d) :
    ∃ x y w : ℕ,
      z < x ∧ z < y ∧ z < w ∧ x ≤ y ∧ y ≤ w ∧ d = x * y * w := by
  rcases h with ⟨a, b, c, ha, hb, hc, habc⟩
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · exact ⟨a, b, c, ha, hb, hc, hab, hbc, habc⟩
    · rcases le_total a c with hac | hca
      · exact ⟨a, c, b, ha, hc, hb, hac, hcb, by
          calc d = a * b * c := habc
               _ = a * c * b := by ring⟩
      · exact ⟨c, a, b, hc, ha, hb, hca, hab, by
          calc d = a * b * c := habc
               _ = c * a * b := by ring⟩
  · rcases le_total a c with hac | hca
    · exact ⟨b, a, c, hb, ha, hc, hba, hac, by
        calc d = a * b * c := habc
             _ = b * a * c := by ring⟩
    · rcases le_total b c with hbc | hcb
      · exact ⟨b, c, a, hb, hc, ha, hbc, hca, by
          calc d = a * b * c := habc
               _ = b * c * a := by ring⟩
      · exact ⟨c, b, a, hc, hb, ha, hcb, hba, by
          calc d = a * b * c := habc
               _ = c * b * a := by ring⟩

lemma exists_sorted_three_large_tuple {z d : ℕ}
    (h : HasThreeLargeFactors z d) :
    ∃ e : ℕ × (ℕ × ℕ),
      z < e.1 ∧ z < e.2.1 ∧ z < e.2.2 ∧
      e.1 ≤ e.2.1 ∧ e.2.1 ≤ e.2.2 ∧
      d = e.1 * e.2.1 * e.2.2 := by
  rcases exists_sorted_three_large h with ⟨x, y, w, hx, hy, hw, hxy, hyw, hd⟩
  exact ⟨(x, (y, w)), hx, hy, hw, hxy, hyw, hd⟩

/-- Canonical sorted witness for the three-large-factor property. -/
noncomputable def sortedThreeFactors (z d : ℕ) : ℕ × (ℕ × ℕ) := by
  classical
  exact if h : HasThreeLargeFactors z d then
    Classical.choose (exists_sorted_three_large_tuple h)
  else (1, (1, 1))

lemma sortedThreeFactors_spec {z d : ℕ} (h : HasThreeLargeFactors z d) :
    z < (sortedThreeFactors z d).1 ∧
    z < (sortedThreeFactors z d).2.1 ∧
    z < (sortedThreeFactors z d).2.2 ∧
    (sortedThreeFactors z d).1 ≤ (sortedThreeFactors z d).2.1 ∧
    (sortedThreeFactors z d).2.1 ≤ (sortedThreeFactors z d).2.2 ∧
    d = (sortedThreeFactors z d).1 *
      (sortedThreeFactors z d).2.1 * (sortedThreeFactors z d).2.2 := by
  classical
  rw [sortedThreeFactors, dif_pos h]
  exact Classical.choose_spec (exists_sorted_three_large_tuple h)

/-- Half-open dyadic interval `[2^i,2^(i+1))`. -/
def dyadicInterval (i : ℕ) : Finset ℕ :=
  Finset.Ico (2 ^ i) (2 ^ (i + 1))

@[simp] theorem dyadicInterval_card (i : ℕ) :
    (dyadicInterval i).card = 2 ^ i := by
  simp [dyadicInterval, pow_succ]
  omega

lemma mem_dyadicInterval_log2 {d : ℕ} (hd : d ≠ 0) :
    d ∈ dyadicInterval (Nat.log2 d) := by
  rw [dyadicInterval, Finset.mem_Ico]
  constructor
  · rw [Nat.log2_eq_log_two]
    exact Nat.pow_log_le_self 2 hd
  · rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self Nat.one_lt_two d

lemma log2_mono_of_le {a b : ℕ} (ha : a ≠ 0) (hab : a ≤ b) :
    Nat.log2 a ≤ Nat.log2 b := by
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  apply Nat.le_log_of_pow_le Nat.one_lt_two
  exact (Nat.pow_log_le_self 2 ha).trans hab

/-- An occupied dyadic factor triple lies below the ambient dyadic logarithm. -/
lemma sortedThreeFactors_log2_le {z d n : ℕ}
    (h : HasThreeLargeFactors z d) (hdn : d ≤ n) :
    Nat.log2 (sortedThreeFactors z d).1 ≤ Nat.log2 n ∧
    Nat.log2 (sortedThreeFactors z d).2.1 ≤ Nat.log2 n ∧
    Nat.log2 (sortedThreeFactors z d).2.2 ≤ Nat.log2 n := by
  have hs := sortedThreeFactors_spec h
  have hxpos : 0 < (sortedThreeFactors z d).1 := by omega
  have hypos : 0 < (sortedThreeFactors z d).2.1 := by omega
  have hwpos : 0 < (sortedThreeFactors z d).2.2 := by omega
  have hxle : (sortedThreeFactors z d).1 ≤ d := by
    calc
      _ ≤ (sortedThreeFactors z d).1 *
          ((sortedThreeFactors z d).2.1 * (sortedThreeFactors z d).2.2) :=
        Nat.le_mul_of_pos_right _ (Nat.mul_pos hypos hwpos)
      _ = (sortedThreeFactors z d).1 * (sortedThreeFactors z d).2.1 *
          (sortedThreeFactors z d).2.2 := by ring
      _ = d := hs.2.2.2.2.2.symm
  have hyle : (sortedThreeFactors z d).2.1 ≤ d := by
    calc
      _ ≤ (sortedThreeFactors z d).1 * (sortedThreeFactors z d).2.1 :=
        Nat.le_mul_of_pos_left _ hxpos
      _ ≤ (sortedThreeFactors z d).1 * (sortedThreeFactors z d).2.1 *
          (sortedThreeFactors z d).2.2 :=
        Nat.le_mul_of_pos_right _ hwpos
      _ = d := hs.2.2.2.2.2.symm
  have hwle : (sortedThreeFactors z d).2.2 ≤ d := by
    calc
      _ ≤ (sortedThreeFactors z d).2.1 * (sortedThreeFactors z d).2.2 :=
        Nat.le_mul_of_pos_left _ hypos
      _ ≤ (sortedThreeFactors z d).1 *
          ((sortedThreeFactors z d).2.1 * (sortedThreeFactors z d).2.2) :=
        Nat.le_mul_of_pos_left _ hxpos
      _ = (sortedThreeFactors z d).1 * (sortedThreeFactors z d).2.1 *
          (sortedThreeFactors z d).2.2 := by ring
      _ = d := hs.2.2.2.2.2.symm
  exact ⟨log2_mono_of_le (Nat.ne_of_gt hxpos) (hxle.trans hdn),
    log2_mono_of_le (Nat.ne_of_gt hypos) (hyle.trans hdn),
    log2_mono_of_le (Nat.ne_of_gt hwpos) (hwle.trans hdn)⟩

/-- Elementary simplification of the unbalanced cube-free expression. -/
theorem cubeExpression_le
    {X Y Z N : ℝ} (hX : 0 < X) (hY : 1 ≤ Y)
    (hYZ : Y ≤ Z) (hprod : X * Y * Z ≤ N) :
    Y * Z + X * Real.sqrt (Y * Z * (Y + Z * Real.sqrt Y)) ≤
      N / X + 2 * N / Real.sqrt (Real.sqrt Y) := by
  have hY0 : 0 ≤ Y := hY.trans' (by norm_num)
  have hZ0 : 0 ≤ Z := hY0.trans hYZ
  have hsY0 : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg _
  have hsY1 : 1 ≤ Real.sqrt Y := by
    rw [Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) hY0]
    norm_num
    exact hY
  have hdom : Y ≤ Z * Real.sqrt Y := by
    calc
      Y = Y * 1 := by ring
      _ ≤ Z * Real.sqrt Y :=
        mul_le_mul hYZ hsY1 (by norm_num) hZ0
  have hins : Y * Z * (Y + Z * Real.sqrt Y) ≤
      2 * Y * Z ^ 2 * Real.sqrt Y := by
    have hadd : Y + Z * Real.sqrt Y ≤ 2 * (Z * Real.sqrt Y) := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hadd (mul_nonneg hY0 hZ0)
    nlinarith
  have hspos : 0 < Real.sqrt (Real.sqrt Y) := Real.sqrt_pos.2 (by positivity)
  have hsYsq : (Real.sqrt Y) ^ 2 = Y := Real.sq_sqrt hY0
  have hssq : (Real.sqrt (Real.sqrt Y)) ^ 2 = Real.sqrt Y :=
    Real.sq_sqrt hsY0
  have hsqrt : Real.sqrt (Y * Z * (Y + Z * Real.sqrt Y)) ≤
      2 * Z * Y / Real.sqrt (Real.sqrt Y) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hden : Real.sqrt (Real.sqrt Y) ≠ 0 := ne_of_gt hspos
      apply hins.trans
      rw [div_pow, hssq]
      have hsYpos : 0 < Real.sqrt Y := by positivity
      field_simp [ne_of_gt hsYpos]
      nlinarith [hsYsq]
  have hYZprod : Y * Z ≤ N / X := by
    apply (le_div_iff₀ hX).2
    nlinarith
  have hmain : X * Real.sqrt (Y * Z * (Y + Z * Real.sqrt Y)) ≤
      2 * N / Real.sqrt (Real.sqrt Y) := by
    have hxmul := mul_le_mul_of_nonneg_left hsqrt hX.le
    apply hxmul.trans
    rw [show X * (2 * Z * Y / Real.sqrt (Real.sqrt Y)) =
      (2 * (X * Y * Z)) / Real.sqrt (Real.sqrt Y) by ring]
    exact div_le_div_of_nonneg_right (by nlinarith [hprod]) hspos.le
  linarith

/-- One dyadic box of canonical sorted three-factor encodings. -/
noncomputable def threeLargeDyadicBox
    (A : Finset ℕ) (z i j k : ℕ) : Finset ℕ := by
  classical
  exact (threeLargePart A z).filter fun d =>
    Nat.log2 (sortedThreeFactors z d).1 = i ∧
    Nat.log2 (sortedThreeFactors z d).2.1 = j ∧
    Nat.log2 (sortedThreeFactors z d).2.2 = k

/-- Quantitative K222 bound for one smooth dyadic box. -/
theorem threeLargeDyadicBox_card_le
    (A : Finset ℕ) (hA : HasRepBound 3 A) (z i j k : ℕ) :
    ((threeLargeDyadicBox A z i j k).card : ℝ) ≤
      ((2 ^ j : ℕ) : ℝ) * (2 ^ k : ℕ) +
      ((2 ^ i : ℕ) : ℝ) *
        Real.sqrt (((2 ^ j : ℕ) : ℝ) * (2 ^ k : ℕ) *
          (((2 ^ j : ℕ) : ℝ) +
            (2 ^ k : ℕ) * Real.sqrt ((2 ^ j : ℕ) : ℝ))) := by
  classical
  let Δ := ↥(threeLargeDyadicBox A z i j k)
  let X := ↥(dyadicInterval i)
  let Y := ↥(dyadicInterval j)
  let Z := ↥(dyadicInterval k)
  let value : Δ → ℕ := fun d => d.1
  let enc : Δ → X × (Y × Z) := fun d =>
    let f := sortedThreeFactors z d.1
    (⟨f.1, by
      have hdmem := Finset.mem_filter.mp d.2
      have hthree := (Finset.mem_filter.mp hdmem.1).2
      have hs := sortedThreeFactors_spec hthree
      have hxpos : 0 < f.1 := lt_of_le_of_lt (Nat.zero_le z) hs.1
      have hm := mem_dyadicInterval_log2 (Nat.ne_of_gt hxpos)
      rw [hdmem.2.1] at hm
      exact hm⟩,
     (⟨f.2.1, by
       have hdmem := Finset.mem_filter.mp d.2
       have hthree := (Finset.mem_filter.mp hdmem.1).2
       have hs := sortedThreeFactors_spec hthree
       have hypos : 0 < f.2.1 := lt_of_le_of_lt (Nat.zero_le z) hs.2.1
       have hm := mem_dyadicInterval_log2 (Nat.ne_of_gt hypos)
       rw [hdmem.2.2.1] at hm
       exact hm⟩,
      ⟨f.2.2, by
       have hdmem := Finset.mem_filter.mp d.2
       have hthree := (Finset.mem_filter.mp hdmem.1).2
       have hs := sortedThreeFactors_spec hthree
       have hwpos : 0 < f.2.2 := lt_of_le_of_lt (Nat.zero_le z) hs.2.2.1
       have hm := mem_dyadicInterval_log2 (Nat.ne_of_gt hwpos)
       rw [hdmem.2.2.2] at hm
       exact hm⟩))
  have hvalueA : ∀ d : Δ, value d ∈ A := by
    intro d
    exact (Finset.mem_filter.mp
      (Finset.mem_filter.mp d.2).1).1
  have hrecon : ∀ d : Δ,
      ((enc d).1 : ℕ) * ((enc d).2.1 : ℕ) * ((enc d).2.2 : ℕ) = value d := by
    intro d
    have hdmem := Finset.mem_filter.mp d.2
    have hthree := (Finset.mem_filter.mp hdmem.1).2
    have hs := sortedThreeFactors_spec hthree
    exact hs.2.2.2.2.2.symm
  have hb := admissibleThreeFactorEncoding_card_le
    (Δ := Δ) (X := X) (Y := Y) (Z := Z)
    A hA value (by intro d e h; exact Subtype.ext h) hvalueA enc
    (fun x : X => x.1) (fun y : Y => y.1) (fun w : Z => w.1) hrecon
  dsimp [Δ, X, Y, Z] at hb
  simp only [Fintype.card_coe, dyadicInterval_card] at hb
  exact hb

/-- A nonempty dyadic box enjoys a product-sensitive bound.  Unlike a
uniform ambient-box estimate, this retains the hyperbolic constraint that the
three lower dyadic endpoints have product at most `n`. -/
theorem threeLargeDyadicBox_card_le_product
    (A : Finset ℕ) (hA : HasRepBound 3 A) {n z i j k : ℕ}
    (hAint : A ⊆ Finset.Icc 1 n) :
    ((threeLargeDyadicBox A z i j k).card : ℝ) ≤
      (n : ℝ) / (2 ^ i : ℕ) +
        2 * (n : ℝ) /
          Real.sqrt (Real.sqrt ((2 ^ j : ℕ) : ℝ)) := by
  classical
  by_cases hempty : threeLargeDyadicBox A z i j k = ∅
  · rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · have hnon : (threeLargeDyadicBox A z i j k).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    rcases hnon with ⟨d, hd⟩
    have hdf := Finset.mem_filter.mp hd
    have hdthree := (Finset.mem_filter.mp hdf.1).2
    have hdA := (Finset.mem_filter.mp hdf.1).1
    have hdle : d ≤ n := (Finset.mem_Icc.mp (hAint hdA)).2
    have hs := sortedThreeFactors_spec hdthree
    let x := (sortedThreeFactors z d).1
    let y := (sortedThreeFactors z d).2.1
    let w := (sortedThreeFactors z d).2.2
    have hxpos : 0 < x := by dsimp [x]; omega
    have hypos : 0 < y := by dsimp [y]; omega
    have hwpos : 0 < w := by dsimp [w]; omega
    have hxi : x ∈ dyadicInterval i := by
      have hm := mem_dyadicInterval_log2 (Nat.ne_of_gt hxpos)
      rw [hdf.2.1] at hm
      exact hm
    have hyj : y ∈ dyadicInterval j := by
      have hm := mem_dyadicInterval_log2 (Nat.ne_of_gt hypos)
      rw [hdf.2.2.1] at hm
      exact hm
    have hwk : w ∈ dyadicInterval k := by
      have hm := mem_dyadicInterval_log2 (Nat.ne_of_gt hwpos)
      rw [hdf.2.2.2] at hm
      exact hm
    have hix : 2 ^ i ≤ x := (Finset.mem_Ico.mp hxi).1
    have hjy : 2 ^ j ≤ y := (Finset.mem_Ico.mp hyj).1
    have hkw : 2 ^ k ≤ w := (Finset.mem_Ico.mp hwk).1
    have hij : i ≤ j := by
      rw [← hdf.2.1, ← hdf.2.2.1]
      exact log2_mono_of_le (Nat.ne_of_gt hxpos) hs.2.2.2.1
    have hjk : j ≤ k := by
      rw [← hdf.2.2.1, ← hdf.2.2.2]
      exact log2_mono_of_le (Nat.ne_of_gt hypos) hs.2.2.2.2.1
    have hpowij : 2 ^ i ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hij
    have hpowjk : 2 ^ j ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hjk
    have hprodNat : 2 ^ i * 2 ^ j * 2 ^ k ≤ n := by
      calc
        2 ^ i * 2 ^ j * 2 ^ k ≤ x * y * w := by gcongr
        _ = d := by dsimp [x, y, w]; exact hs.2.2.2.2.2.symm
        _ ≤ n := hdle
    have hsimp := cubeExpression_le
      (X := ((2 ^ i : ℕ) : ℝ))
      (Y := ((2 ^ j : ℕ) : ℝ))
      (Z := ((2 ^ k : ℕ) : ℝ))
      (N := (n : ℝ))
      (by positivity) (by
        exact_mod_cast (show 1 ≤ 2 ^ j from
          pow_pos (by omega : 0 < (2 : ℕ)) j))
      (by exact_mod_cast hpowjk) (by exact_mod_cast hprodNat)
    exact (threeLargeDyadicBox_card_le A hA z i j k).trans hsimp

/-- If the threshold is the dyadic value `2^s`, every occupied box starts at
index at least `s`; hence the product-sensitive estimate has a uniform
threshold saving. -/
theorem threeLargeDyadicBox_card_le_threshold
    (A : Finset ℕ) (hA : HasRepBound 3 A) {n s i j k : ℕ}
    (hAint : A ⊆ Finset.Icc 1 n) :
    ((threeLargeDyadicBox A (2 ^ s) i j k).card : ℝ) ≤
      (n : ℝ) / (2 ^ s : ℕ) +
        2 * (n : ℝ) /
          Real.sqrt (Real.sqrt ((2 ^ s : ℕ) : ℝ)) := by
  classical
  by_cases hempty : threeLargeDyadicBox A (2 ^ s) i j k = ∅
  · rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  · rcases Finset.nonempty_iff_ne_empty.mpr hempty with ⟨d, hd⟩
    have hdf := Finset.mem_filter.mp hd
    have hdthree := (Finset.mem_filter.mp hdf.1).2
    have hs := sortedThreeFactors_spec hdthree
    have hxpos : 0 < (sortedThreeFactors (2 ^ s) d).1 :=
      (pow_pos (by omega : 0 < (2 : ℕ)) s).trans hs.1
    have hyle : (sortedThreeFactors (2 ^ s) d).1 ≤
        (sortedThreeFactors (2 ^ s) d).2.1 := hs.2.2.2.1
    have hsi : s ≤ i := by
      have hmono := log2_mono_of_le
        (show 2 ^ s ≠ 0 by positivity) (Nat.le_of_lt hs.1)
      rw [Nat.log2_two_pow, hdf.2.1] at hmono
      exact hmono
    have hij : i ≤ j := by
      rw [← hdf.2.1, ← hdf.2.2.1]
      exact log2_mono_of_le (Nat.ne_of_gt hxpos) hyle
    have hsj : s ≤ j := hsi.trans hij
    have hpowi : (2 ^ s : ℕ) ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by omega) hsi
    have hpowj : (2 ^ s : ℕ) ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by omega) hsj
    have hbase := threeLargeDyadicBox_card_le_product A hA hAint
      (z := 2 ^ s) (i := i) (j := j) (k := k)
    apply hbase.trans
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hpowiR : (((2 ^ s : ℕ) : ℝ)) ≤ (2 ^ i : ℕ) := by
      exact_mod_cast hpowi
    have hpowjR : (((2 ^ s : ℕ) : ℝ)) ≤ (2 ^ j : ℕ) := by
      exact_mod_cast hpowj
    have hden1 : (0 : ℝ) < (2 ^ s : ℕ) := by positivity
    have hden2 : (0 : ℝ) < (2 ^ i : ℕ) := by positivity
    have hdiv : (n : ℝ) / (2 ^ i : ℕ) ≤ (n : ℝ) / (2 ^ s : ℕ) :=
      div_le_div_of_nonneg_left hn0 hden1 hpowiR
    have hsqrt : Real.sqrt (Real.sqrt (((2 ^ s : ℕ) : ℝ))) ≤
        Real.sqrt (Real.sqrt (((2 ^ j : ℕ) : ℝ))) := by
      exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt hpowjR)
    have hsqrtPos : 0 < Real.sqrt (Real.sqrt (((2 ^ s : ℕ) : ℝ))) := by
      positivity
    have hsqrtPos' : 0 < Real.sqrt (Real.sqrt (((2 ^ j : ℕ) : ℝ))) := by
      positivity
    have hdivsqrt : 2 * (n : ℝ) /
          Real.sqrt (Real.sqrt (((2 ^ j : ℕ) : ℝ))) ≤
        2 * (n : ℝ) /
          Real.sqrt (Real.sqrt (((2 ^ s : ℕ) : ℝ))) := by
      exact div_le_div_of_nonneg_left (by positivity) hsqrtPos hsqrt
    linarith

/-- The cube of all dyadic indices that can occur for factors bounded by `n`. -/
def dyadicIndexCube (n : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  let I := Finset.range (Nat.log2 n + 1)
  I.product (I.product I)

@[simp] theorem dyadicIndexCube_card (n : ℕ) :
    (dyadicIndexCube n).card = (Nat.log2 n + 1) ^ 3 := by
  simp [dyadicIndexCube, pow_succ]
  ring

/-- Canonical dyadic boxes cover the entire three-large-factor part. -/
theorem threeLargePart_subset_dyadicBoxes
    {A : Finset ℕ} {n z : ℕ} (hAint : A ⊆ Finset.Icc 1 n) :
    threeLargePart A z ⊆
      (dyadicIndexCube n).biUnion fun e =>
        threeLargeDyadicBox A z e.1 e.2.1 e.2.2 := by
  classical
  intro d hd
  have hdf := Finset.mem_filter.mp hd
  have hdle : d ≤ n := (Finset.mem_Icc.mp (hAint hdf.1)).2
  have hlogs := sortedThreeFactors_log2_le hdf.2 hdle
  let e : ℕ × (ℕ × ℕ) :=
    (Nat.log2 (sortedThreeFactors z d).1,
      (Nat.log2 (sortedThreeFactors z d).2.1,
       Nat.log2 (sortedThreeFactors z d).2.2))
  apply Finset.mem_biUnion.mpr
  refine ⟨e, ?_, ?_⟩
  · unfold dyadicIndexCube
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hlogs.1)
    · apply Finset.mem_product.mpr
      exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hlogs.2.1),
        Finset.mem_range.mpr (Nat.lt_succ_of_le hlogs.2.2)⟩
  · unfold threeLargeDyadicBox
    apply Finset.mem_filter.mpr
    exact ⟨hd, rfl, rfl, rfl⟩

/-- Global quantitative bound for the part of an admissible set whose members
have three factors above a dyadic threshold. -/
theorem threeLargePart_card_le_dyadic
    (A : Finset ℕ) (hA : HasRepBound 3 A) {n s : ℕ}
    (hAint : A ⊆ Finset.Icc 1 n) :
    ((threeLargePart A (2 ^ s)).card : ℝ) ≤
      (((Nat.log2 n + 1) ^ 3 : ℕ) : ℝ) *
        ((n : ℝ) / (2 ^ s : ℕ) +
          2 * (n : ℝ) /
            Real.sqrt (Real.sqrt (((2 ^ s : ℕ) : ℝ)))) := by
  classical
  let U := (dyadicIndexCube n).biUnion fun e =>
    threeLargeDyadicBox A (2 ^ s) e.1 e.2.1 e.2.2
  have hsub : threeLargePart A (2 ^ s) ⊆ U :=
    threeLargePart_subset_dyadicBoxes hAint
  have hcard : (threeLargePart A (2 ^ s)).card ≤ U.card :=
    Finset.card_le_card hsub
  have hUnion : U.card ≤ ∑ e ∈ dyadicIndexCube n,
      (threeLargeDyadicBox A (2 ^ s) e.1 e.2.1 e.2.2).card := by
    dsimp [U]
    exact Finset.card_biUnion_le
  have hone : ∀ e ∈ dyadicIndexCube n,
      ((threeLargeDyadicBox A (2 ^ s) e.1 e.2.1 e.2.2).card : ℝ) ≤
        (n : ℝ) / (2 ^ s : ℕ) +
          2 * (n : ℝ) /
            Real.sqrt (Real.sqrt (((2 ^ s : ℕ) : ℝ))) := by
    intro e he
    exact threeLargeDyadicBox_card_le_threshold A hA hAint
  calc
    ((threeLargePart A (2 ^ s)).card : ℝ) ≤ (U.card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ (∑ e ∈ dyadicIndexCube n,
        (threeLargeDyadicBox A (2 ^ s) e.1 e.2.1 e.2.2).card : ℕ) := by
      exact_mod_cast hUnion
    _ = ∑ e ∈ dyadicIndexCube n,
        ((threeLargeDyadicBox A (2 ^ s) e.1 e.2.1 e.2.2).card : ℝ) := by
      push_cast
      rfl
    _ ≤ ∑ _e ∈ dyadicIndexCube n,
        ((n : ℝ) / (2 ^ s : ℕ) +
          2 * (n : ℝ) /
            Real.sqrt (Real.sqrt (((2 ^ s : ℕ) : ℝ)))) :=
      Finset.sum_le_sum hone
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, dyadicIndexCube_card]

/-- Primes in one half-open dyadic interval. -/
def dyadicPrimes (i : ℕ) : Finset ℕ :=
  (dyadicInterval i).filter Nat.Prime

lemma dyadicPrimes_subset_primesLE (i : ℕ) :
    dyadicPrimes i ⊆ Nat.primesLE (2 ^ (i + 1)) := by
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hpi := Finset.mem_Ico.mp hp'.1
  exact Nat.mem_primesLE.mpr ⟨hpi.2.le, hp'.2⟩

lemma dyadicPrimes_card_le_primeCounting (i : ℕ) :
    (dyadicPrimes i).card ≤ Nat.primeCounting (2 ^ (i + 1)) := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  exact Finset.card_le_card (dyadicPrimes_subset_primesLE i)

/-- A fixed harmless constant in the dyadic prime-counting bound. -/
noncomputable def dyadicPrimeConstant : ℝ :=
  2 * (Real.log 4 + 1) / Real.log 2

lemma dyadicPrimeConstant_pos : 0 < dyadicPrimeConstant := by
  unfold dyadicPrimeConstant
  positivity

/-- Chebyshev's theorem gives a uniform `2^i/i` upper bound in every
sufficiently high dyadic prime interval. -/
theorem eventually_dyadicPrimes_card_le :
    ∀ᶠ i : ℕ in Filter.atTop,
      ((dyadicPrimes i).card : ℝ) ≤
        dyadicPrimeConstant * ((2 ^ i : ℕ) : ℝ) / (i + 1) := by
  have hpow : Filter.Tendsto (fun i : ℕ => ((2 : ℝ) ^ (i + 1)))
      Filter.atTop Filter.atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp
      (Filter.tendsto_add_atTop_nat 1)
  have hcheb := hpow.eventually
    (Chebyshev.eventually_primeCounting_le (ε := (1 : ℝ)) one_pos)
  filter_upwards [hcheb] with i hi
  have hcard : ((dyadicPrimes i).card : ℝ) ≤
      (Nat.primeCounting (2 ^ (i + 1)) : ℝ) := by
    exact_mod_cast dyadicPrimes_card_le_primeCounting i
  apply hcard.trans
  have hpowcast : (2 : ℝ) ^ (i + 1) = ((2 ^ (i + 1) : ℕ) : ℝ) := by
    norm_num
  have hi' : (Nat.primeCounting (2 ^ (i + 1)) : ℝ) ≤
      (Real.log 4 + 1) * (2 : ℝ) ^ (i + 1) /
        Real.log ((2 : ℝ) ^ (i + 1)) := by
    rw [hpowcast, Nat.floor_natCast] at hi
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hi
  apply hi'.trans_eq
  unfold dyadicPrimeConstant
  rw [Real.log_pow, pow_succ]
  push_cast
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hi1 : ((i : ℝ) + 1) ≠ 0 := by positivity
  field_simp

end Erdos796
